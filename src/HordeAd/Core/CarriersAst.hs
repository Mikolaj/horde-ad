{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | AST of the code built using the @RankedTensor@ and related classes.
-- The AST is needed for handling second order operations (such as build
-- and map, via IET (vectorization), and for producing reusable reverse
-- derivative terms. However, it can also be used for other code
-- transformations, e.g., simplification.
module HordeAd.Core.CarriersAst
  ( AstRaw(..)
  , AstNoVectorize(..)
  , AstNoSimplify(..)
  ) where

import Prelude hiding (foldl')

import Data.Type.Equality (testEquality, (:~:) (Refl))

import Data.Array.Nested qualified as Nested

import HordeAd.Core.Ast
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Type family instances for AstTensor

type instance PrimalOf (AstTensor ms s) = AstTensor ms PrimalSpan
type instance DualOf (AstTensor ms s) = AstTensor ms DualSpan
type instance ShareOf (AstTensor ms s) = AstRaw s

-- This can't be just HFun, because they need to be vectorized
-- and vectorization applies such functions to the variable from build1
-- and the variable has to be eliminated via vectorization to preserve
-- the closed form of the function. Just applying a Haskell closure
-- to the build1 variable and then duplicating the result of the function
-- would not eliminate the variable and also would likely results
-- in more costly computations. Also, that would prevent simplification
-- of the instances, especially after applied to arguments that are terms.
type instance HFunOf (AstTensor AstMethodLet s) x z = AstHFun x z  -- TODO: PrimalSpan

type instance BoolOf (AstTensor ms s) = AstBool ms


-- * Unlawful numeric instances for AST scalars; they are lawful modulo evaluation

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstTensor ms s y) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstTensor ms s y) where
  (<=) = error "AST requires that OrdF be used instead"

instance (GoodScalar r, AstSpan s)
         => Num (AstTensor ms s (TKScalar r)) where
  -- The normal form has AstConcreteK, if any, as the first argument
  -- of the constructor. No flattening is performed beyond that.
  AstConcreteK 0 + u = u
  u + AstConcreteK 0 = u
  AstConcreteK n + AstConcreteK k = AstConcreteK (n + k)
  AstConcreteK n + AstPlusK (AstConcreteK k) u = AstConcreteK (n + k) + u
  AstPlusK (AstConcreteK n) u + AstConcreteK k = AstConcreteK (n + k) + u
  AstPlusK (AstConcreteK n) u + AstPlusK (AstConcreteK k) v =
    AstConcreteK (n + k) + AstPlusK u v  -- u and v can cancel, but unlikely

  -- Unfortunately, these only fire if the required subterms are at the top
  -- of the reduced term, which happens rarely except in small terms.
  -- We could keep variables at the top, but they'd compete with AstConcreteK.
  AstN1K NegateOp (AstVar _ var) + AstVar _ var'
    | var == var' = 0
  AstN1K NegateOp (AstVar _ var) + AstPlusK (AstVar _ var') u
    | var == var' = u
  AstVar _ var' + AstN1K NegateOp (AstVar _ var)
    | var == var' = 0
  AstVar _ var' + AstPlusK (AstN1K NegateOp (AstVar _ var)) u
    | var == var' = u

  AstI2K RemOp (AstN1K NegateOp (AstVar _ var)) (AstConcreteK n)
   + AstI2K RemOp (AstVar _ var') (AstConcreteK n')
     | var == var' && n == n' = 0
  AstI2K RemOp (AstN1K NegateOp (AstVar _ var)) (AstConcreteK n)
   + AstPlusK (AstI2K RemOp (AstVar _ var') (AstConcreteK n')) u
     | var == var' && n == n' = u
  AstI2K RemOp (AstVar _ var') (AstConcreteK n')
   + AstI2K RemOp (AstN1K NegateOp (AstVar _ var)) (AstConcreteK n)
     | var == var' && n == n' = 0
  AstI2K RemOp (AstVar _ var') (AstConcreteK n')
   + AstPlusK (AstI2K RemOp (AstN1K NegateOp (AstVar _ var)) (AstConcreteK n)) u
     | var == var' && n == n' = u

  AstPlusK u@AstConcreteK{} v + w = AstPlusK u (AstPlusK v w)  -- as above
  u + v@AstConcreteK{} = AstPlusK v u
  u + AstPlusK v@AstConcreteK{} w = AstPlusK v (AstPlusK u w)  -- as above
  u + v = AstPlusK u v

  AstConcreteK 0 * _ = 0
  _ * AstConcreteK 0 = 0
  AstConcreteK 1 * u = u
  u * AstConcreteK 1 = u
  AstConcreteK n * AstConcreteK k = AstConcreteK (n * k)
  AstConcreteK n * AstTimesK (AstConcreteK k) u = AstConcreteK (n * k) * u
  AstTimesK (AstConcreteK n) u * AstConcreteK k = AstConcreteK (n * k) * u
  AstTimesK (AstConcreteK n) u * AstTimesK (AstConcreteK k) v =
    AstConcreteK (n * k) * AstTimesK u v  -- u and v can cancel, but unlikely

  u@AstConcreteK{} * AstPlusK v w = AstPlusK (u * v) (u * w)
  AstTimesK u@AstConcreteK{} x * AstPlusK v w =
    AstTimesK x (AstPlusK (u * v) (u * w))
  AstPlusK v w * u@AstConcreteK{} = AstPlusK (v * u) (w * u)
  AstPlusK v w * AstTimesK u@AstConcreteK{} x =
    AstTimesK (AstPlusK (v * u) (w * u)) x

  AstN1K NegateOp u * AstN1K NegateOp v = AstTimesK u v

  -- With static shapes, the second argument to QuotOp and RemOp
  -- is often a constant, which makes such rules worth including,
  -- since they are likely to fire. To help them fire, we avoid changing
  -- that constant, if possible, e.g., in rules for NegateOp.
  AstConcreteK n * AstI2K QuotOp (AstVar ftk2 var) (AstConcreteK n')
    | n == n' =
      AstPlusK
        (AstVar ftk2 var)
        (negate (AstI2K RemOp (AstVar ftk2 var) (AstConcreteK n)))
  AstTimesK (AstConcreteK n) x * AstI2K QuotOp (AstVar ftk2 var)
                                               (AstConcreteK n')
    | n == n' =
      AstTimesK
        x
        (AstPlusK
           (AstVar ftk2 var)
           (negate (AstI2K RemOp (AstVar ftk2 var) (AstConcreteK n))))
  AstI2K QuotOp (AstVar ftk2 var) (AstConcreteK n') * AstConcreteK n
    | n == n' =
      AstPlusK
        (AstVar ftk2 var)
        (negate (AstI2K RemOp (AstVar ftk2 var) (AstConcreteK n)))
  AstI2K QuotOp (AstVar ftk2 var)
                (AstConcreteK n') * AstTimesK (AstConcreteK n) x
    | n == n' =
      AstTimesK
        (AstPlusK
           (AstVar ftk2 var)
           (negate (AstI2K RemOp (AstVar ftk2 var) (AstConcreteK n))))
        x

  AstTimesK u@AstConcreteK{} v * w = AstTimesK u (AstTimesK v w)  -- as above
  u * v@AstConcreteK{} = AstTimesK v u
  u * AstTimesK v@AstConcreteK{} w = AstTimesK v (AstTimesK u w)  -- as above
  u * v = AstTimesK u v

  negate (AstConcreteK n) = AstConcreteK (negate n)
  negate (AstPlusK u v) = AstPlusK (negate u) (negate v)
  negate (AstTimesK u v) = negate u * v
  negate (AstN1K NegateOp u) = u
  negate (AstN1K SignumOp u) = AstN1K SignumOp (negate u)
  negate (AstI2K QuotOp u v) = AstI2K QuotOp (negate u) v
    -- v is likely positive and let's keep it so
  negate (AstI2K RemOp u v) = AstI2K RemOp (negate u) v
    -- v is likely positive and let's keep it so
  negate u = AstN1K NegateOp u
  abs = AstN1K AbsOp
  signum = AstN1K SignumOp
  fromInteger i = fromPrimal $ AstConcreteK (fromInteger i)

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (GoodScalar r, IntegralF r, AstSpan s)
         => IntegralF (AstTensor ms s (TKScalar r)) where
  quotF = AstI2K QuotOp
  remF = AstI2K RemOp

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKScalar r)) where
  u / v = AstR2K DivideOp u v
  recip = AstR1K RecipOp
  fromRational r = fromPrimal $ AstConcreteK (fromRational r)

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKScalar r)) where
  pi = error "pi not defined for ranked tensors"
  exp = AstR1K ExpOp
  log = AstR1K LogOp
  sqrt = AstR1K SqrtOp
  (**) = AstR2K PowerOp
  logBase = AstR2K LogBaseOp
  sin = AstR1K SinOp
  cos = AstR1K CosOp
  tan = AstR1K TanOp
  asin = AstR1K AsinOp
  acos = AstR1K AcosOp
  atan = AstR1K AtanOp
  sinh = AstR1K SinhOp
  cosh = AstR1K CoshOp
  tanh = AstR1K TanhOp
  asinh = AstR1K AsinhOp
  acosh = AstR1K AcoshOp
  atanh = AstR1K AtanhOp

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => RealFloatF (AstTensor ms s (TKScalar r)) where
  atan2F = AstR2K Atan2Op


-- * Unlawful numeric instances for ranked AST; lawful modulo evaluation

instance GoodScalar r
         => Num (AstTensor ms s (TKR n r)) where
  (+) = liftRFromS2 (+)
  (-) = liftRFromS2 (-)
  (*) = liftRFromS2 (*)
  negate = liftRFromS1 negate
  abs = liftRFromS1 abs
  signum = liftRFromS1 signum
  fromInteger i = error $ "fromInteger not defined for ranked tensors: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (GoodScalar r, IntegralF r)
         => IntegralF (AstTensor ms s (TKR n r)) where
  quotF = liftRFromS2 quotF
  remF = liftRFromS2 remF

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r)
         => Fractional (AstTensor ms s (TKR n r)) where
  (/) = liftRFromS2 (/)
  recip = liftRFromS1 recip
  fromRational r = error $ "fromRational not defined for ranked tensors: "
                           ++ show r

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKR n r)) where
  pi = error "pi not defined for ranked tensors"
  exp = liftRFromS1 exp
  log = liftRFromS1 log
  sqrt = liftRFromS1 sqrt
  (**) = liftRFromS2 (**)
  logBase = liftRFromS2 logBase
  sin = liftRFromS1 sin
  cos = liftRFromS1 cos
  tan = liftRFromS1 tan
  asin = liftRFromS1 asin
  acos = liftRFromS1 acos
  atan = liftRFromS1 atan
  sinh = liftRFromS1 sinh
  cosh = liftRFromS1 cosh
  tanh = liftRFromS1 tanh
  asinh = liftRFromS1 asinh
  acosh = liftRFromS1 acosh
  atanh = liftRFromS1 atanh

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => RealFloatF (AstTensor ms s (TKR n r)) where
  atan2F = liftRFromS2 atan2F


-- * Unlawful numeric instances for shaped AST; lawful modulo evaluation

instance GoodScalar r
         => Num (AstTensor ms s (TKS sh r)) where
--  AstConcreteS 0 + u = u
--  u + AstConcreteS 0 = u
  AstConcreteS n + AstConcreteS k = AstConcreteS (n + k)
  AstConcreteS n + AstPlusS (AstConcreteS k) u =
    AstPlusS (AstConcreteS (n + k)) u
  AstPlusS (AstConcreteS n) u + AstConcreteS k =
    AstPlusS (AstConcreteS (n + k)) u
  AstPlusS (AstConcreteS n) u + AstPlusS (AstConcreteS k) v =
    AstPlusS (AstConcreteS (n + k)) (AstPlusS u v)

--  AstN1S NegateOp (AstVar _ var) + AstVar _ var'
--    | var == var' = 0
  AstN1S NegateOp (AstVar _ var) + AstPlusS (AstVar _ var') u
    | var == var' = u
--  AstVar _ var' + AstN1S NegateOp (AstVar _ var)
--    | var == var' = 0
  AstVar _ var' + AstPlusS (AstN1S NegateOp (AstVar _ var)) u
    | var == var' = u

  AstPlusS u@AstConcreteS{} v + w = AstPlusS u (AstPlusS v w)
  u + v@AstConcreteS{} = AstPlusS v u
  u + AstPlusS v@AstConcreteS{} w = AstPlusS v (AstPlusS u w)
  u + v = AstPlusS u v

  AstConcreteS n * AstConcreteS k = AstConcreteS (n * k)
  AstConcreteS n * AstTimesS (AstConcreteS k) u =
    AstTimesS (AstConcreteS (n * k)) u
  AstTimesS (AstConcreteS n) u * AstConcreteS k =
    AstTimesS (AstConcreteS (n * k)) u
  AstTimesS (AstConcreteS n) u * AstTimesS (AstConcreteS k) v =
    AstTimesS (AstConcreteS (n * k)) (AstTimesS u v)

  u@AstConcreteS{} * AstPlusS v w = AstPlusS (u * v) (u * w)
  AstTimesS u@AstConcreteS{} x * AstPlusS v w =
    AstTimesS x (AstPlusS (u * v) (u * w))
  AstPlusS v w * u@AstConcreteS{} = AstPlusS (v * u) (w * u)
  AstPlusS v w * AstTimesS u@AstConcreteS{} x =
    AstTimesS (AstPlusS (v * u) (w * u)) x

  AstN1S NegateOp u * AstN1S NegateOp v = AstTimesS u v

  AstTimesS u@AstConcreteS{} v * w = AstTimesS u (AstTimesS v w)
  u * v@AstConcreteS{} = AstTimesS v u
  u * AstTimesS v@AstConcreteS{} w = AstTimesS v (AstTimesS u w)
  u * v = AstTimesS u v

  negate (AstConcreteS n) = AstConcreteS (negate n)
  negate (AstPlusS u v) = AstPlusS (negate u) (negate v)
  negate (AstTimesS u v) = AstTimesS (negate u) v
  negate (AstN1S NegateOp u) = u
  negate (AstN1S SignumOp u) = AstN1S SignumOp (negate u)
  negate (AstI2S QuotOp u v) = AstI2S QuotOp (negate u) v
    -- v is likely positive and let's keep it so
  negate (AstI2S RemOp u v) = AstI2S RemOp (negate u) v
    -- v is likely positive and let's keep it so
  negate u = AstN1S NegateOp u
  abs = AstN1S AbsOp
  signum = AstN1S SignumOp
  fromInteger i = error $ "fromInteger not defined for shaped tensors: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (IntegralF r, GoodScalar r)
         => IntegralF (AstTensor ms s (TKS sh r)) where
  quotF = AstI2S QuotOp
  remF = AstI2S RemOp

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r)
         => Fractional (AstTensor ms s (TKS sh r)) where
  u / v = AstR2S DivideOp u v
  recip = AstR1S RecipOp
  fromRational r = error $ "fromRational not defined for shaped tensors: "
                           ++ show r

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKS sh r)) where
  pi = error "pi not defined for shaped tensors"
  exp = AstR1S ExpOp
  log = AstR1S LogOp
  sqrt = AstR1S SqrtOp
  (**) = AstR2S PowerOp
  logBase = AstR2S LogBaseOp
  sin = AstR1S SinOp
  cos = AstR1S CosOp
  tan = AstR1S TanOp
  asin = AstR1S AsinOp
  acos = AstR1S AcosOp
  atan = AstR1S AtanOp
  sinh = AstR1S SinhOp
  cosh = AstR1S CoshOp
  tanh = AstR1S TanhOp
  asinh = AstR1S AsinhOp
  acosh = AstR1S AcoshOp
  atanh = AstR1S AtanhOp

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => RealFloatF (AstTensor ms s (TKS sh r)) where
  atan2F = AstR2S Atan2Op


-- * Unlawful numeric instances for mixed AST; lawful modulo evaluation

instance GoodScalar r
         => Num (AstTensor ms s (TKX sh r)) where
  (+) = liftXFromS2 (+)
  (-) = liftXFromS2 (-)
  (*) = liftXFromS2 (*)
  negate = liftXFromS1 negate
  abs = liftXFromS1 abs
  signum = liftXFromS1 signum
  fromInteger i = error $ "fromInteger not defined for mixed tensors: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (IntegralF r, GoodScalar r)
         => IntegralF (AstTensor ms s (TKX sh r)) where
  quotF = liftXFromS2 quotF
  remF = liftXFromS2 remF

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r)
         => Fractional (AstTensor ms s (TKX sh r)) where
  (/) = liftXFromS2 (/)
  recip = liftXFromS1 recip
  fromRational r = error $ "fromRational not defined for mixed tensors: "
                           ++ show r

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKX sh r)) where
  pi = error "pi not defined for mixed tensors"
  exp = liftXFromS1 exp
  log = liftXFromS1 log
  sqrt = liftXFromS1 sqrt
  (**) = liftXFromS2 (**)
  logBase = liftXFromS2 logBase
  sin = liftXFromS1 sin
  cos = liftXFromS1 cos
  tan = liftXFromS1 tan
  asin = liftXFromS1 asin
  acos = liftXFromS1 acos
  atan = liftXFromS1 atan
  sinh = liftXFromS1 sinh
  cosh = liftXFromS1 cosh
  tanh = liftXFromS1 tanh
  asinh = liftXFromS1 asinh
  acosh = liftXFromS1 acosh
  atanh = liftXFromS1 atanh

instance (GoodScalar r, RealFloatF r, Nested.FloatElt r, AstSpan s)
         => RealFloatF (AstTensor ms s (TKX sh r)) where
  atan2F = liftXFromS2 atan2F


-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

instance Boolean (AstBool ms) where
  true = AstBoolConst True
  false = AstBoolConst False
  notB = AstBoolNot
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstB2 AndOp b c
  b ||* c = AstB2 OrOp b c

instance (AstSpan s, GoodScalar r) => EqF (AstTensor ms s) (TKR n r) where
  v ==. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withCastRS shv' $ \shv ->
          withCastRS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS EqOp (AstSFromR shu $ primalPart v)
                             (AstSFromR shv $ primalPart u)
              _ -> error $ "(==.): shapes don't match: "
                           ++ show (shu, shv)
  v /=. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withCastRS shv' $ \shv ->
          withCastRS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS NeqOp (AstSFromR shu $ primalPart v)
                             (AstSFromR shv $ primalPart u)
              _ -> error $ "(/=.): shapes don't match: "
                           ++ show (shu, shv)

instance (AstSpan s, GoodScalar r) => EqF (AstTensor ms s) (TKX sh r) where
  v ==. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withCastXS shv' $ \shv ->
          withCastXS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS EqOp (AstSFromX shu $ primalPart v)
                             (AstSFromX shv $ primalPart u)
              _ -> error $ "(==.): shapes don't match: "
                           ++ show (shu, shv)
  v /=. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withCastXS shv' $ \shv ->
          withCastXS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS NeqOp (AstSFromX shu $ primalPart v)
                             (AstSFromX shv $ primalPart u)
              _ -> error $ "(/=.): shapes don't match: "
                           ++ show (shu, shv)

instance (AstSpan s, GoodScalar r) => OrdF (AstTensor ms s) (TKR n r) where
  v <. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withCastRS shv' $ \shv ->
          withCastRS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS LsOp (AstSFromR shu $ primalPart v)
                             (AstSFromR shv $ primalPart u)
              _ -> error $ "(<.): shapes don't match: "
                           ++ show (shu, shv)
  v <=. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withCastRS shv' $ \shv ->
          withCastRS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS LeqOp (AstSFromR shu $ primalPart v)
                              (AstSFromR shv $ primalPart u)
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)
  v >. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withCastRS shv' $ \shv ->
          withCastRS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS GtOp (AstSFromR shu $ primalPart v)
                             (AstSFromR shv $ primalPart u)
              _ -> error $ "(>.): shapes don't match: "
                           ++ show (shu, shv)
  v >=. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withCastRS shv' $ \shv ->
          withCastRS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS GeqOp (AstSFromR shu $ primalPart v)
                              (AstSFromR shv $ primalPart u)
              _ -> error $ "(>=.): shapes don't match: "
                           ++ show (shu, shv)

instance (AstSpan s, GoodScalar r) => OrdF (AstTensor ms s) (TKX sh r) where
  v <. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withCastXS shv' $ \shv ->
          withCastXS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS LsOp (AstSFromX shu $ primalPart v)
                             (AstSFromX shv $ primalPart u)
              _ -> error $ "(<.): shapes don't match: "
                           ++ show (shu, shv)
  v <=. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withCastXS shv' $ \shv ->
          withCastXS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS LeqOp (AstSFromX shu $ primalPart v)
                              (AstSFromX shv $ primalPart u)
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)
  v >. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withCastXS shv' $ \shv ->
          withCastXS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS GtOp (AstSFromX shu $ primalPart v)
                             (AstSFromX shv $ primalPart u)
              _ -> error $ "(>.): shapes don't match: "
                           ++ show (shu, shv)
  v >=. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withCastXS shv' $ \shv ->
          withCastXS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstRelS GeqOp (AstSFromX shu $ primalPart v)
                              (AstSFromX shv $ primalPart u)
              _ -> error $ "(>=.): shapes don't match: "
                           ++ show (shu, shv)

-- These are common in indexing, so worth optimizing early via AstConcrete.
instance (AstSpan s, GoodScalar r)
         => EqF (AstTensor ms s) (TKScalar r) where
  AstConcreteK u ==. AstConcreteK v =
    AstBoolConst $ RepN @(TKScalar r) u ==. RepN v
  v ==. u = AstRelK EqOp (primalPart v) (primalPart u)
  AstConcreteK u /=. AstConcreteK v =
    AstBoolConst $ RepN @(TKScalar r) u /=. RepN v
  v /=. u = AstRelK NeqOp (primalPart v) (primalPart u)

instance (AstSpan s, GoodScalar r)
         => EqF (AstTensor ms s) (TKS sh r) where
  AstConcreteS u ==. AstConcreteS v =
    AstBoolConst $ RepN @(TKS sh r) u ==. RepN v
  v ==. u = AstRelS EqOp (primalPart v) (primalPart u)
  AstConcreteS u /=. AstConcreteS v =
    AstBoolConst $ RepN @(TKS sh r) u /=. RepN v
  v /=. u = AstRelS NeqOp (primalPart v) (primalPart u)

instance (AstSpan s, GoodScalar r)
         => OrdF (AstTensor ms s) (TKScalar r) where
  AstConcreteK u <. AstConcreteK v =
    AstBoolConst $ RepN  @(TKScalar r)u <. RepN v
  v <. u = AstRelK LsOp (primalPart v) (primalPart u)
  AstConcreteK u <=. AstConcreteK v =
    AstBoolConst $ RepN @(TKScalar r) u <=. RepN v
  v <=. u = AstRelK LeqOp (primalPart v) (primalPart u)
  AstConcreteK u >. AstConcreteK v =
    AstBoolConst $ RepN @(TKScalar r) u >. RepN v
  v >. u = AstRelK GtOp (primalPart v) (primalPart u)
  AstConcreteK u >=. AstConcreteK v =
    AstBoolConst $ RepN @(TKScalar r) u >=. RepN v
  v >=. u = AstRelK GeqOp (primalPart v) (primalPart u)

instance (AstSpan s, GoodScalar r)
         => OrdF (AstTensor ms s) (TKS sh r) where
  AstConcreteS u <. AstConcreteS v =
    AstBoolConst $ RepN @(TKS sh r) u <. RepN v
  v <. u = AstRelS LsOp (primalPart v) (primalPart u)
  AstConcreteS u <=. AstConcreteS v =
    AstBoolConst $ RepN @(TKS sh r) u <=. RepN v
  v <=. u = AstRelS LeqOp (primalPart v) (primalPart u)
  AstConcreteS u >. AstConcreteS v =
    AstBoolConst $ RepN @(TKS sh r) u >. RepN v
  v >. u = AstRelS GtOp (primalPart v) (primalPart u)
  AstConcreteS u >=. AstConcreteS v =
    AstBoolConst $ RepN @(TKS sh r) u >=. RepN v
  v >=. u = AstRelS GeqOp (primalPart v) (primalPart u)


-- * AstRaw, AstNoVectorize and AstNoSimplify definitions

type role AstRaw nominal nominal
newtype AstRaw s y =
  AstRaw {unAstRaw :: AstTensor AstMethodShare s y}
 deriving Show

type role AstNoVectorize nominal nominal
newtype AstNoVectorize s y =
  AstNoVectorize {unAstNoVectorize :: AstTensor AstMethodLet s y}
 deriving Show

type role AstNoSimplify nominal nominal
newtype AstNoSimplify s y =
  AstNoSimplify {unAstNoSimplify :: AstTensor AstMethodLet s y}
 deriving Show


-- * AstRaw, AstNoVectorize and AstNoSimplify type family instances

type instance PrimalOf (AstRaw s) = AstRaw PrimalSpan
type instance DualOf (AstRaw s) = AstTensor AstMethodShare DualSpan
type instance ShareOf (AstRaw s) = AstRaw s
type instance HFunOf (AstRaw s) x y = AstHFun x y
type instance BoolOf (AstRaw s) = AstBool AstMethodShare

type instance PrimalOf (AstNoVectorize s) = AstNoVectorize PrimalSpan
type instance DualOf (AstNoVectorize s) = AstTensor AstMethodLet DualSpan
type instance ShareOf (AstNoVectorize s) = AstRaw s
type instance HFunOf (AstNoVectorize s) x z = AstHFun x z
type instance BoolOf (AstNoVectorize s) = AstBool AstMethodLet

type instance PrimalOf (AstNoSimplify s) = AstNoSimplify PrimalSpan
type instance DualOf (AstNoSimplify s) = AstTensor AstMethodLet DualSpan
type instance ShareOf (AstNoSimplify s) = AstRaw s
type instance HFunOf (AstNoSimplify s) x z = AstHFun x z
type instance BoolOf (AstNoSimplify s) = AstBool AstMethodLet


-- * AstRaw, AstNoVectorize and AstNoSimplify other instances

instance EqF (AstTensor AstMethodShare s) y => EqF (AstRaw s) y where
  AstRaw v ==. AstRaw u = v ==. u
  AstRaw v /=. AstRaw u = v /=. u
instance OrdF (AstTensor AstMethodShare s) y => OrdF (AstRaw s) y where
  AstRaw v <. AstRaw u = v <. u
  AstRaw v <=. AstRaw u = v <=. u
  AstRaw v >. AstRaw u = v >. u
  AstRaw v >=. AstRaw u = v >=. u

deriving instance Eq (AstRaw s y)
deriving instance Ord (AstRaw s y)
deriving instance Num (AstTensor AstMethodShare s y) => Num (AstRaw s y)
deriving instance IntegralF (AstTensor AstMethodShare s y)
                  => IntegralF (AstRaw s y)
deriving instance Fractional (AstTensor AstMethodShare s y)
                  => Fractional (AstRaw s y)
deriving instance Floating (AstTensor AstMethodShare s y)
                  => Floating (AstRaw s y)
deriving instance RealFloatF (AstTensor AstMethodShare s y)
                  => RealFloatF (AstRaw s y)

instance EqF (AstTensor AstMethodLet s) y => EqF (AstNoVectorize s) y where
  AstNoVectorize v ==. AstNoVectorize u = v ==. u
  AstNoVectorize v /=. AstNoVectorize u = v /=. u
instance OrdF (AstTensor AstMethodLet s) y => OrdF (AstNoVectorize s) y where
  AstNoVectorize v <. AstNoVectorize u = v <. u
  AstNoVectorize v <=. AstNoVectorize u = v <=. u
  AstNoVectorize v >. AstNoVectorize u = v >. u
  AstNoVectorize v >=. AstNoVectorize u = v >=. u
deriving instance Eq (AstNoVectorize s y)
deriving instance Ord (AstNoVectorize s y)
deriving instance Num (AstTensor AstMethodLet s y) => Num (AstNoVectorize s y)
deriving instance (IntegralF (AstTensor AstMethodLet s y))
                  => IntegralF (AstNoVectorize s y)
deriving instance Fractional (AstTensor AstMethodLet s y)
                  => Fractional (AstNoVectorize s y)
deriving instance Floating (AstTensor AstMethodLet s y)
                  => Floating (AstNoVectorize s y)
deriving instance (RealFloatF (AstTensor AstMethodLet s y))
                  => RealFloatF (AstNoVectorize s y)

instance EqF (AstTensor AstMethodLet s) y => EqF (AstNoSimplify s) y where
  AstNoSimplify v ==. AstNoSimplify u = v ==. u
  AstNoSimplify v /=. AstNoSimplify u = v /=. u
instance OrdF (AstTensor AstMethodLet s) y => OrdF (AstNoSimplify s) y where
  AstNoSimplify v <. AstNoSimplify u = v <. u
  AstNoSimplify v <=. AstNoSimplify u = v <=. u
  AstNoSimplify v >. AstNoSimplify u = v >. u
  AstNoSimplify v >=. AstNoSimplify u = v >=. u
deriving instance Eq (AstNoSimplify s y)
deriving instance Ord (AstNoSimplify s y)
deriving instance Num (AstTensor AstMethodLet s y) => Num (AstNoSimplify s y)
deriving instance (IntegralF (AstTensor AstMethodLet s y))
                  => IntegralF (AstNoSimplify s y)
deriving instance Fractional (AstTensor AstMethodLet s y)
                  => Fractional (AstNoSimplify s y)
deriving instance Floating (AstTensor AstMethodLet s y)
                  => Floating (AstNoSimplify s y)
deriving instance (RealFloatF (AstTensor AstMethodLet s y))
                  => RealFloatF (AstNoSimplify s y)
