{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Definitions, mostly class instances, needed to make AST a valid
-- carrier for a tensor class algebra (instance) defined
-- in "HordeAd.Core.OpsAst".
-- This algebra permits user programs to be instantiated as AST terms,
-- as well as to be interpreted into AST terms and it also permits derivatives
-- to be expressed as AST terms.
module HordeAd.Core.CarriersAst
  ( AstRaw(..), AstNoVectorize(..), AstNoSimplify(..)
  ) where

import Prelude hiding (foldl')

import Data.Int (Int64)
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Foreign.C (CInt)
import Type.Reflection (typeRep)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
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
type instance HFunOf (AstTensor AstMethodLet s) x z = AstHFun s s x z

type instance BoolOf (AstTensor ms s) = AstBool ms


-- * Unlawful numeric instances for AST scalars; they are lawful modulo evaluation

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstTensor ms s y) where
  (==) = error "AST requires that EqH be used instead"
  (/=) = error "AST requires that EqH be used instead"

instance Ord (AstTensor ms s y) where
  (<=) = error "AST requires that OrdH be used instead"

-- TODO: perhaps aim for a polynomial normal form? but that requires global
-- inspection of the whole expression
-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right
-- and let's push negation down.
--
-- Not considered are rules that would require comparing non-constant terms
-- or that would duplicate a non-constant term, as well as most rules
-- informed by inequalities, expressed via max or min, such as
-- max n (signum (abs x)) | n <= 0 --> signum (abs x).
-- We could use sharing via @tlet@ if terms are duplicated, but it's
-- unclear if the term bloat is worth it and also we'd need to restrict
-- this extended simplification to AstMethodLet.
--
-- | Integer terms need to be simplified, because large ones are sometimes
-- created due to vectorization, e.g., via astTransposeAsGather
-- or astReshapeAsGather and can be a deciding factor in whether
-- the other tensor terms can be simplified in turn.
--
-- The normal form has AstConcreteK, if any, as the first argument
-- of the constructor. No flattening is performed beyond that.
instance (GoodScalar r, AstSpan s)
         => Num (AstTensor ms s (TKScalar r)) where
  AstFromPrimal u + AstFromPrimal v = AstFromPrimal $ u + v
  AstFromDual u + AstFromDual v = AstFromDual $ u + v
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
  AstN1K NegateOp (AstVar var) + AstVar var'
    | var == var' = 0
  AstN1K NegateOp (AstFromS STKScalar (AstVar var))
    + AstFromS STKScalar (AstVar var')
    | varNameToAstVarId var == varNameToAstVarId var' = 0
  AstN1K NegateOp (AstVar var) + AstPlusK (AstVar var') u
    | var == var' = u
  AstN1K NegateOp (AstFromS STKScalar (AstVar var))
    + AstPlusK (AstFromS STKScalar (AstVar var')) u
    | varNameToAstVarId var == varNameToAstVarId var' = u
  AstVar var' + AstN1K NegateOp (AstVar var)
    | var == var' = 0
  AstFromS STKScalar (AstVar var')
    + AstN1K NegateOp (AstFromS STKScalar (AstVar var))
    | varNameToAstVarId var == varNameToAstVarId var' = 0
  AstVar var' + AstPlusK (AstN1K NegateOp (AstVar var)) u
    | var == var' = u
  AstFromS STKScalar (AstVar var')
    + AstPlusK (AstN1K NegateOp (AstFromS STKScalar (AstVar var))) u
    | varNameToAstVarId var == varNameToAstVarId var' = u

  AstI2K RemOp (AstN1K NegateOp (AstVar var)) (AstConcreteK n)
   + AstI2K RemOp (AstVar var') (AstConcreteK n')
     | var == var' && n == n' = 0
  AstI2K RemOp (AstN1K NegateOp (AstFromS STKScalar (AstVar var)))
               (AstConcreteK n)
   + AstI2K RemOp (AstFromS STKScalar (AstVar var')) (AstConcreteK n')
     | varNameToAstVarId var == varNameToAstVarId var' && n == n' = 0
  AstI2K RemOp (AstN1K NegateOp (AstVar var)) (AstConcreteK n)
   + AstPlusK (AstI2K RemOp (AstVar var') (AstConcreteK n')) u
     | var == var' && n == n' = u
  AstI2K RemOp (AstN1K NegateOp (AstFromS STKScalar (AstVar var)))
               (AstConcreteK n)
   + AstPlusK (AstI2K RemOp (AstFromS STKScalar (AstVar var'))
                            (AstConcreteK n')) u
     | varNameToAstVarId var == varNameToAstVarId var' && n == n' = u
  AstI2K RemOp (AstVar var') (AstConcreteK n')
   + AstI2K RemOp (AstN1K NegateOp (AstVar var)) (AstConcreteK n)
     | var == var' && n == n' = 0
  AstI2K RemOp (AstFromS STKScalar (AstVar var')) (AstConcreteK n')
   + AstI2K RemOp (AstN1K NegateOp (AstFromS STKScalar (AstVar var)))
                                   (AstConcreteK n)
     | varNameToAstVarId var == varNameToAstVarId var' && n == n' = 0
  AstI2K RemOp (AstVar var') (AstConcreteK n')
   + AstPlusK (AstI2K RemOp (AstN1K NegateOp (AstVar var)) (AstConcreteK n)) u
     | var == var' && n == n' = u
  AstI2K RemOp (AstFromS STKScalar (AstVar var')) (AstConcreteK n')
   + AstPlusK (AstI2K RemOp (AstN1K NegateOp (AstFromS STKScalar (AstVar var)))
                            (AstConcreteK n)) u
     | varNameToAstVarId var == varNameToAstVarId var' && n == n' = u

  AstPlusK u@AstConcreteK{} v + w = AstPlusK u (AstPlusK v w)  -- as above
  u + v@AstConcreteK{} = AstPlusK v u
  u + AstPlusK v@AstConcreteK{} w = AstPlusK v (AstPlusK u w)  -- as above
  t1 + t2 | eqK t1 t2 = 2 * t1
  t1 + AstTimesK (AstConcreteK n) t2 | eqK t1 t2 = AstConcreteK (n + 1) * t1
  AstTimesK (AstConcreteK n) t2 + t1 | eqK t1 t2 = AstConcreteK (n + 1) * t1
  AstTimesK (AstConcreteK n1) t1 + AstTimesK (AstConcreteK n2) t2
    | eqK t1 t2 = AstConcreteK (n1 + n2) * t1
  u + v = AstPlusK u v

  AstFromPrimal u * AstFromPrimal v = AstFromPrimal $ u * v
    -- TODO: this is not mathematically correct for AstFromDual, right?
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

  {- TODO: these rules increase the number of occurrences of a variable
     and trade multiplication and quotient for an equally problematic remnant,
     so they are disabled until we find a way to profit from them.
  -- With static shapes, the second argument to QuotOp and RemOp
  -- is often a constant, which makes such rules worth including,
  -- since they are likely to fire. To help them fire, we avoid changing
  -- that constant, if possible, e.g., in rules for NegateOp.
  AstConcreteK n * AstI2K QuotOp (AstVar var) (AstConcreteK n')
    | n == n' =
      AstPlusK
        (AstVar var)
        (negate (AstI2K RemOp (AstVar var) (AstConcreteK n)))
  AstTimesK (AstConcreteK n) x * AstI2K QuotOp (AstVar var)
                                               (AstConcreteK n')
    | n == n' =
      AstTimesK
        x
        (AstPlusK
           (AstVar var)
           (negate (AstI2K RemOp (AstVar var) (AstConcreteK n))))
  AstI2K QuotOp (AstVar var) (AstConcreteK n') * AstConcreteK n
    | n == n' =
      AstPlusK
        (AstVar var)
        (negate (AstI2K RemOp (AstVar var) (AstConcreteK n)))
  AstI2K QuotOp (AstVar var)
                (AstConcreteK n') * AstTimesK (AstConcreteK n) x
    | n == n' =
      AstTimesK
        (AstPlusK
           (AstVar var)
           (negate (AstI2K RemOp (AstVar var) (AstConcreteK n))))
        x
  -}

  AstTimesK u@AstConcreteK{} v * w = AstTimesK u (AstTimesK v w)  -- as above
  u * v@AstConcreteK{} = AstTimesK v u
  u * AstTimesK v@AstConcreteK{} w = AstTimesK v (AstTimesK u w)  -- as above
  u * v = AstTimesK u v

  negate (AstFromPrimal n) = AstFromPrimal (negate n)
  negate (AstFromDual n) = AstFromDual (negate n)
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
  abs (AstFromPrimal n) = AstFromPrimal (abs n)
  abs (AstFromDual n) = AstFromDual (abs n)
  abs (AstConcreteK n) = AstConcreteK (abs n)
  abs (AstN1K AbsOp u) = AstN1K AbsOp u
  abs (AstN1K NegateOp u) = abs u
  abs u = AstN1K AbsOp u
  signum (AstFromPrimal n) = AstFromPrimal (signum n)
  signum (AstFromDual n) = AstFromDual (signum n)
  signum (AstConcreteK n) = AstConcreteK (signum n)
  signum (AstN1K SignumOp u) = AstN1K SignumOp u
  signum u = AstN1K SignumOp u
  fromInteger i = fromPrimal $ AstConcreteK (fromInteger i)
  {-# SPECIALIZE instance Num (AstTensor ms FullSpan (TKScalar Int64)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms PrimalSpan (TKScalar Int64)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms FullSpan (TKScalar CInt)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms PrimalSpan (TKScalar CInt)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms FullSpan (TKScalar Double)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms PrimalSpan (TKScalar Double)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms FullSpan (TKScalar Float)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms PrimalSpan (TKScalar Float)) #-}

-- An approximation. False doesn't imply terms have different semantics,
-- but True implies they have equal semantics.
eqK :: AstTensor ms s (TKScalar r) -> AstTensor ms s (TKScalar r) -> Bool
eqK (AstVar var1) (AstVar var2) = var1 == var2
eqK (AstLet @_ @_ @s1 var1 u1 v1) (AstLet @_ @_ @s2 var2 u2 v2)
  | FTKScalar @r1 <- ftkAst u1, FTKScalar @r2 <- ftkAst u2
  , Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameAstSpan @s1 @s2 =
    var1 == var2 && eqK u1 u2 && eqK v1 v2
eqK (AstPrimalPart u1) (AstPrimalPart u2) = eqK u1 u2
eqK (AstDualPart u1) (AstDualPart u2) = eqK u1 u2
eqK (AstFromPrimal u1) (AstFromPrimal u2) = eqK u1 u2
eqK (AstFromDual u1) (AstFromDual u2) = eqK u1 u2
eqK (AstPlusK u1 v1) (AstPlusK u2 v2) =
  eqK u1 u2 && eqK v1 v2 || eqK u1 v2 && eqK v1 u2
eqK (AstTimesK u1 v1) (AstTimesK u2 v2) =
  eqK u1 u2 && eqK v1 v2 || eqK u1 v2 && eqK v1 u2
eqK (AstN1K opCode1 u1) (AstN1K opCode2 u2) = opCode1 == opCode2 && eqK u1 u2
eqK (AstR1K opCode1 u1) (AstR1K opCode2 u2) = opCode1 == opCode2 && eqK u1 u2
eqK (AstR2K opCode1 u1 v1) (AstR2K opCode2 u2 v2) =
  opCode1 == opCode2 && eqK u1 u2 && eqK v1 v2
eqK (AstI2K opCode1 u1 v1) (AstI2K opCode2 u2 v2) =
  opCode1 == opCode2 && eqK u1 u2 && eqK v1 v2
eqK (AstConcreteK u1) (AstConcreteK u2) = u1 == u2
eqK (AstFloorK @r1 u1) (AstFloorK @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) = eqK u1 u2
eqK (AstFromIntegralK @r1 u1) (AstFromIntegralK @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) = eqK u1 u2
eqK (AstCastK @r1 u1) (AstCastK @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) = eqK u1 u2
eqK _ _ = False

-- Div and mod operations are very costly (simplifying them requires
-- constructing conditionals, etc), so they are not included in IntegralH.
instance (GoodScalar r, IntegralH r, Nested.IntElt r, AstSpan s)
         => IntegralH (AstTensor ms s (TKScalar r)) where
  quotH (AstFromPrimal n) (AstFromPrimal k) = AstFromPrimal (quotH n k)
  quotH (AstConcreteK n) (AstConcreteK k) = AstConcreteK (quotH n k)
  quotH (AstConcreteK 0) _ = AstConcreteK 0
  quotH u (AstConcreteK 1) = u
  quotH (AstI2K RemOp _ (AstConcreteK k)) (AstConcreteK k')
    | k' >= k && k >= 0 = 0
  quotH (AstI2K QuotOp u v) w = quotH u (v * w)
  quotH (AstTimesK (AstConcreteK n) v) (AstConcreteK n')
    | n == n' = v
  quotH u v =
    let t = AstI2K QuotOp u v
        (u1, u2) = bounds t
    in if u1 == u2 then fromPrimal $ AstConcreteK u1 else t

  remH (AstFromPrimal n) (AstFromPrimal k) = AstFromPrimal (remH n k)
  remH (AstConcreteK n) (AstConcreteK k) = AstConcreteK (remH n k)
  remH (AstConcreteK 0) _ = AstConcreteK 0
  remH _ (AstConcreteK 1) = AstConcreteK 0
  remH (AstI2K RemOp u (AstConcreteK k)) (AstConcreteK k')
    | k' >= k && k >= 0 = AstI2K RemOp u (AstConcreteK k)
  remH (AstI2K RemOp u (AstConcreteK k)) (AstConcreteK k')
    | remH k k' == 0 && k > 0 = remH u (AstConcreteK k')
  remH (AstTimesK (AstConcreteK n) _) (AstConcreteK n')
    | remH n n' == 0 = 0
  remH u v =
    let t = AstI2K RemOp u v
        (u1, u2) = bounds t
    in if u1 == u2 then fromPrimal $ AstConcreteK u1 else t
  {-# SPECIALIZE instance IntegralH (AstTensor ms FullSpan (TKScalar Int64)) #-}
  {-# SPECIALIZE instance IntegralH (AstTensor ms PrimalSpan (TKScalar Int64)) #-}
  {-# SPECIALIZE instance IntegralH (AstTensor ms FullSpan (TKScalar CInt)) #-}
  {-# SPECIALIZE instance IntegralH (AstTensor ms PrimalSpan (TKScalar CInt)) #-}

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKScalar r)) where
  AstFromPrimal u / AstFromPrimal v = AstFromPrimal $ u / v
  AstConcreteK u / AstConcreteK v = AstConcreteK $ u / v
  u / v = AstR2K DivideOp u v
  recip (AstFromPrimal u) = AstFromPrimal (recip u)
  recip (AstConcreteK u) = AstConcreteK (recip u)
  recip u = AstR1K RecipOp u
  fromRational r = fromPrimal $ AstConcreteK (fromRational r)

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKScalar r)) where
  pi = error "pi not defined for ranked tensors"
  exp (AstFromPrimal u) = AstFromPrimal $ exp u
  exp (AstConcreteK u) = AstConcreteK $ exp u
  exp u = AstR1K ExpOp u
  log (AstFromPrimal u) = AstFromPrimal $ log u
  log (AstConcreteK u) = AstConcreteK $ log u
  log u = AstR1K LogOp u
  sqrt (AstFromPrimal u) = AstFromPrimal $ sqrt u
  sqrt (AstConcreteK u) = AstConcreteK $ sqrt u
  sqrt u = AstR1K SqrtOp u
  (AstFromPrimal u) ** (AstFromPrimal v) = AstFromPrimal $ u ** v
  (AstConcreteK u) ** (AstConcreteK v) = AstConcreteK $ u ** v
  u ** v = AstR2K PowerOp u v
  logBase (AstFromPrimal u) (AstFromPrimal v) = AstFromPrimal $ logBase u v
  logBase (AstConcreteK u) (AstConcreteK v) = AstConcreteK $ logBase u v
  logBase u v = AstR2K LogBaseOp u v
  sin (AstFromPrimal u) = AstFromPrimal $ sin u
  sin (AstConcreteK u) = AstConcreteK $ sin u
  sin u = AstR1K SinOp u
  cos (AstFromPrimal u) = AstFromPrimal $ cos u
  cos (AstConcreteK u) = AstConcreteK $ cos u
  cos u = AstR1K CosOp u
  tan (AstFromPrimal u) = AstFromPrimal $ tan u
  tan (AstConcreteK u) = AstConcreteK $ tan u
  tan u = AstR1K TanOp u
  asin (AstFromPrimal u) = AstFromPrimal $ asin u
  asin (AstConcreteK u) = AstConcreteK $ asin u
  asin u = AstR1K AsinOp u
  acos (AstFromPrimal u) = AstFromPrimal $ acos u
  acos (AstConcreteK u) = AstConcreteK $ acos u
  acos u = AstR1K AcosOp u
  atan (AstFromPrimal u) = AstFromPrimal $ atan u
  atan (AstConcreteK u) = AstConcreteK $ atan u
  atan u = AstR1K AtanOp u
  sinh (AstFromPrimal u) = AstFromPrimal $ sinh u
  sinh (AstConcreteK u) = AstConcreteK $ sinh u
  sinh u = AstR1K SinhOp u
  cosh (AstFromPrimal u) = AstFromPrimal $ cosh u
  cosh (AstConcreteK u) = AstConcreteK $ cosh u
  cosh u = AstR1K CoshOp u
  tanh (AstFromPrimal u) = AstFromPrimal $ tanh u
  tanh (AstConcreteK u) = AstConcreteK $ tanh u
  tanh u = AstR1K TanhOp u
  asinh (AstFromPrimal u) = AstFromPrimal $ asinh u
  asinh (AstConcreteK u) = AstConcreteK $ asinh u
  asinh u = AstR1K AsinhOp u
  acosh (AstFromPrimal u) = AstFromPrimal $ acosh u
  acosh (AstConcreteK u) = AstConcreteK $ acosh u
  acosh u = AstR1K AcoshOp u
  atanh (AstFromPrimal u) = AstFromPrimal $ atanh u
  atanh (AstConcreteK u) = AstConcreteK $ atanh u
  atanh u = AstR1K AtanhOp u

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => RealFloatH (AstTensor ms s (TKScalar r)) where
  atan2H (AstFromPrimal u) (AstFromPrimal v) = AstFromPrimal $ atan2H u v
  atan2H (AstConcreteK u) (AstConcreteK v) = AstConcreteK $ atan2H u v
  atan2H u v = AstR2K Atan2Op u v


-- * Unlawful numeric instances for ranked AST; lawful modulo evaluation

instance (GoodScalar r, AstSpan s)
         => Num (AstTensor ms s (TKR n r)) where
  (+) = liftRFromS2 (+)
  (-) = liftRFromS2 (-)
  (*) = liftRFromS2 (*)
  negate = liftRFromS1 negate
  abs = liftRFromS1 abs
  signum = liftRFromS1 signum
  fromInteger i = error $ "fromInteger not defined for ranked tensors: "
                          ++ show i

instance (GoodScalar r, IntegralH r, Nested.IntElt r, AstSpan s)
         => IntegralH (AstTensor ms s (TKR n r)) where
  quotH = liftRFromS2 quotH
  remH = liftRFromS2 remH

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKR n r)) where
  (/) = liftRFromS2 (/)
  recip = liftRFromS1 recip
  fromRational r = error $ "fromRational not defined for ranked tensors: "
                           ++ show r

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
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

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => RealFloatH (AstTensor ms s (TKR n r)) where
  atan2H = liftRFromS2 atan2H


-- * Unlawful numeric instances for shaped AST; lawful modulo evaluation

instance (GoodScalar r, AstSpan s)
         => Num (AstTensor ms s (TKS sh r)) where
  AstReplicate snat stk@STKS{} u + AstReplicate _ STKS{} v =
    AstReplicate snat stk $ u + v
  AstFromPrimal u + AstFromPrimal v = AstFromPrimal $ u + v
  AstFromDual u + AstFromDual v = AstFromDual $ u + v
  AstSFromK u + AstSFromK v = AstSFromK $ u + v
--  AstConcreteS 0 + u = u
--  u + AstConcreteS 0 = u
  AstConcreteS n + AstConcreteS k = AstConcreteS (n + k)
  AstConcreteS n + AstPlusS (AstConcreteS k) u =
    AstPlusS (AstConcreteS (n + k)) u
  AstPlusS (AstConcreteS n) u + AstConcreteS k =
    AstPlusS (AstConcreteS (n + k)) u
  AstPlusS (AstConcreteS n) u + AstPlusS (AstConcreteS k) v =
    AstPlusS (AstConcreteS (n + k)) (AstPlusS u v)

--  AstN1S NegateOp (AstVar var) + AstVar var'
--    | var == var' = 0
  AstN1S NegateOp (AstVar var) + AstPlusS (AstVar var') u
    | var == var' = u
--  AstVar var' + AstN1S NegateOp (AstVar var)
--    | var == var' = 0
  AstVar var' + AstPlusS (AstN1S NegateOp (AstVar var)) u
    | var == var' = u

  AstPlusS u@AstConcreteS{} v + w = AstPlusS u (AstPlusS v w)
  u + v@AstConcreteS{} = AstPlusS v u
  u + AstPlusS v@AstConcreteS{} w = AstPlusS v (AstPlusS u w)
  u + v = AstPlusS u v

  AstReplicate snat stk@STKS{} u * AstReplicate _ STKS{} v =
    AstReplicate snat stk $ u * v
  AstFromPrimal u * AstFromPrimal v = AstFromPrimal $ u * v
  AstSFromK u * AstSFromK v = AstSFromK $ u * v
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

  negate (AstReplicate snat stk@STKS{} u) = AstReplicate snat stk (negate u)
  negate (AstFromPrimal n) = AstFromPrimal (negate n)
  negate (AstFromDual n) = AstFromDual (negate n)
  negate (AstSFromK n) = AstSFromK (negate n)
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
  abs (AstReplicate snat stk@STKS{} u) = AstReplicate snat stk (abs u)
  abs (AstFromPrimal n) = AstFromPrimal (abs n)
  abs (AstFromDual n) = AstFromDual (abs n)
  abs (AstSFromK n) = AstSFromK (abs n)
  abs (AstConcreteS u) = AstConcreteS (abs u)
  abs (AstN1S AbsOp u) = AstN1S AbsOp u
  abs (AstN1S NegateOp u) = abs u
  abs u = AstN1S AbsOp u
  signum (AstReplicate snat stk@STKS{} u) = AstReplicate snat stk (signum u)
  signum (AstFromPrimal n) = AstFromPrimal (signum n)
  signum (AstSFromK n) = AstSFromK (signum n)
  signum (AstFromDual n) = AstFromDual (signum n)
  signum (AstConcreteS u) = AstConcreteS (signum u)
  signum (AstN1S SignumOp u) = AstN1S SignumOp u
  signum u = AstN1S SignumOp u
  fromInteger i = error $ "fromInteger not defined for shaped tensors: "
                          ++ show i

instance (GoodScalar r, IntegralH r, Nested.IntElt r, AstSpan s)
         => IntegralH (AstTensor ms s (TKS sh r)) where
  quotH (AstReplicate snat stk@STKS{} u) (AstReplicate _ STKS{} v) =
    AstReplicate snat stk $ quotH u v
  quotH (AstFromPrimal n) (AstFromPrimal k) = AstFromPrimal (quotH n k)
  quotH (AstSFromK n) (AstSFromK k) = AstSFromK (quotH n k)
  quotH (AstConcreteS n) (AstConcreteS k) = AstConcreteS (quotH n k)
  quotH (AstI2S QuotOp u v) w = quotH u (v * w)
  quotH u v = AstI2S QuotOp u v
  remH (AstReplicate snat stk@STKS{} u) (AstReplicate _ STKS{} v) =
    AstReplicate snat stk $ remH u v
  remH (AstFromPrimal n) (AstFromPrimal k) = AstFromPrimal (remH n k)
  remH (AstSFromK n) (AstSFromK k) = AstSFromK (remH n k)
  remH (AstConcreteS n) (AstConcreteS k) = AstConcreteS (remH n k)
  remH u v = AstI2S RemOp u v

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKS sh r)) where
  AstFromPrimal u / AstFromPrimal v = AstFromPrimal $ u / v
  AstConcreteS u / AstConcreteS v = AstConcreteS $ u / v
  u / v = AstR2S DivideOp u v
  recip (AstFromPrimal u) = AstFromPrimal (recip u)
  recip (AstConcreteS u) = AstConcreteS (recip u)
  recip u = AstR1S RecipOp u
  fromRational r = error $ "fromRational not defined for shaped tensors: "
                           ++ show r

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKS sh r)) where
  pi = error "pi not defined for shaped tensors"
  exp (AstFromPrimal u) = AstFromPrimal $ exp u
  exp (AstConcreteS u) = AstConcreteS $ exp u
  exp u = AstR1S ExpOp u
  log (AstFromPrimal u) = AstFromPrimal $ log u
  log (AstConcreteS u) = AstConcreteS $ log u
  log u = AstR1S LogOp u
  sqrt (AstFromPrimal u) = AstFromPrimal $ sqrt u
  sqrt (AstConcreteS u) = AstConcreteS $ sqrt u
  sqrt u = AstR1S SqrtOp u
  (AstFromPrimal u) ** (AstFromPrimal v) = AstFromPrimal $ u ** v
  (AstConcreteS u) ** (AstConcreteS v) = AstConcreteS $ u ** v
  u ** v = AstR2S PowerOp u v
  logBase (AstFromPrimal u) (AstFromPrimal v) = AstFromPrimal $ logBase u v
  logBase (AstConcreteS u) (AstConcreteS v) = AstConcreteS $ logBase u v
  logBase u v = AstR2S LogBaseOp u v
  sin (AstFromPrimal u) = AstFromPrimal $ sin u
  sin (AstConcreteS u) = AstConcreteS $ sin u
  sin u = AstR1S SinOp u
  cos (AstFromPrimal u) = AstFromPrimal $ cos u
  cos (AstConcreteS u) = AstConcreteS $ cos u
  cos u = AstR1S CosOp u
  tan (AstFromPrimal u) = AstFromPrimal $ tan u
  tan (AstConcreteS u) = AstConcreteS $ tan u
  tan u = AstR1S TanOp u
  asin (AstFromPrimal u) = AstFromPrimal $ asin u
  asin (AstConcreteS u) = AstConcreteS $ asin u
  asin u = AstR1S AsinOp u
  acos (AstFromPrimal u) = AstFromPrimal $ acos u
  acos (AstConcreteS u) = AstConcreteS $ acos u
  acos u = AstR1S AcosOp u
  atan (AstFromPrimal u) = AstFromPrimal $ atan u
  atan (AstConcreteS u) = AstConcreteS $ atan u
  atan u = AstR1S AtanOp u
  sinh (AstFromPrimal u) = AstFromPrimal $ sinh u
  sinh (AstConcreteS u) = AstConcreteS $ sinh u
  sinh u = AstR1S SinhOp u
  cosh (AstFromPrimal u) = AstFromPrimal $ cosh u
  cosh (AstConcreteS u) = AstConcreteS $ cosh u
  cosh u = AstR1S CoshOp u
  tanh (AstFromPrimal u) = AstFromPrimal $ tanh u
  tanh (AstConcreteS u) = AstConcreteS $ tanh u
  tanh u = AstR1S TanhOp u
  asinh (AstFromPrimal u) = AstFromPrimal $ asinh u
  asinh (AstConcreteS u) = AstConcreteS $ asinh u
  asinh u = AstR1S AsinhOp u
  acosh (AstFromPrimal u) = AstFromPrimal $ acosh u
  acosh (AstConcreteS u) = AstConcreteS $ acosh u
  acosh u = AstR1S AcoshOp u
  atanh (AstFromPrimal u) = AstFromPrimal $ atanh u
  atanh (AstConcreteS u) = AstConcreteS $ atanh u
  atanh u = AstR1S AtanhOp u

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => RealFloatH (AstTensor ms s (TKS sh r)) where
  atan2H (AstFromPrimal u) (AstFromPrimal v) = AstFromPrimal $ atan2H u v
  atan2H (AstConcreteS u) (AstConcreteS v) = AstConcreteS $ atan2H u v
  atan2H u v = AstR2S Atan2Op u v


-- * Unlawful numeric instances for mixed AST; lawful modulo evaluation

instance (GoodScalar r, AstSpan s)
         => Num (AstTensor ms s (TKX sh r)) where
  (+) = liftXFromS2 (+)
  (-) = liftXFromS2 (-)
  (*) = liftXFromS2 (*)
  negate = liftXFromS1 negate
  abs = liftXFromS1 abs
  signum = liftXFromS1 signum
  fromInteger i = error $ "fromInteger not defined for mixed tensors: "
                          ++ show i

instance (GoodScalar r, IntegralH r, Nested.IntElt r, AstSpan s)
         => IntegralH (AstTensor ms s (TKX sh r)) where
  quotH = liftXFromS2 quotH
  remH = liftXFromS2 remH

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKX sh r)) where
  (/) = liftXFromS2 (/)
  recip = liftXFromS1 recip
  fromRational r = error $ "fromRational not defined for mixed tensors: "
                           ++ show r

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
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

instance (GoodScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => RealFloatH (AstTensor ms s (TKX sh r)) where
  atan2H = liftXFromS2 atan2H


-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

-- Simple variable comparisons, if any, come first.
instance Boolean (AstBool ms) where
  true = AstBoolConst True
  false = AstBoolConst False
  notB (AstBoolConst b) = AstBoolConst $ not b
  notB (AstBoolNot b) = b
  notB b = AstBoolNot b
  AstBoolConst True &&* b = b
  AstBoolConst False &&* _b = AstBoolConst False
  b &&* AstBoolConst True = b
  _b &&* AstBoolConst False = AstBoolConst False
  AstBoolAnd b c &&* d = b &&* (c &&* d)
  b@(AstLeqK AstConcreteK{} AstVar{}) &&* c = AstBoolAnd b c
  b@(AstLeqK AstConcreteK{} (AstN1K NegateOp
                                    AstVar{})) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstLeqK AstConcreteK{} AstVar{})) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstLeqK AstConcreteK{} (AstN1K NegateOp
                                       AstVar{}))) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstBoolAnd (AstLeqK AstConcreteK{} AstVar{}) _)) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstBoolAnd
          (AstLeqK AstConcreteK{}
                   (AstN1K NegateOp AstVar{})) _)) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstBoolAnd (AstBoolNot (AstLeqK AstConcreteK{}
                                        AstVar{})) _)) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstBoolAnd
          (AstBoolNot
             (AstLeqK AstConcreteK{}
                      (AstN1K NegateOp AstVar{}))) _)) &&* c = AstBoolAnd b c
  b &&* c@(AstLeqK AstConcreteK{} AstVar{}) = AstBoolAnd c b
  b &&* c@(AstLeqK AstConcreteK{} (AstN1K NegateOp
                                          AstVar{})) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstLeqK AstConcreteK{} AstVar{})) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstLeqK AstConcreteK{} (AstN1K NegateOp
                                             AstVar{}))) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstBoolAnd (AstLeqK AstConcreteK{} AstVar{}) _)) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstBoolAnd
                (AstLeqK AstConcreteK{}
                         (AstN1K NegateOp AstVar{})) _)) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstBoolAnd (AstBoolNot (AstLeqK AstConcreteK{}
                                              AstVar{})) _)) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstBoolAnd
                (AstBoolNot
                   (AstLeqK AstConcreteK{}
                            (AstN1K NegateOp AstVar{}))) _)) = AstBoolAnd c b
  b &&* AstBoolAnd
          c@(AstLeqK AstConcreteK{} AstVar{}) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstLeqK AstConcreteK{}
                     (AstN1K NegateOp AstVar{})) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot (AstLeqK AstConcreteK{}
                                 AstVar{})) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstLeqK AstConcreteK{}
                        (AstN1K NegateOp AstVar{}))) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstBoolAnd (AstLeqK AstConcreteK{}
                                    AstVar{}) _)) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstBoolAnd
                  (AstLeqK AstConcreteK{}
                           (AstN1K NegateOp
                                   AstVar{})) _)) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstBoolAnd
                  (AstBoolNot (AstLeqK AstConcreteK{}
                                       AstVar{})) _)) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstBoolAnd
                  (AstBoolNot
                     (AstLeqK AstConcreteK{}
                              (AstN1K NegateOp
                                      AstVar{}))) _)) d = AstBoolAnd c (b &&* d)
  b &&* c = AstBoolAnd b c
  b ||* c = notB (notB b &&* notB c)

-- TODO: refactor with something like liftRFromS2
instance (AstSpan s, GoodScalar r) => EqH (AstTensor ms s) (TKR n r) where
  v ==. u = v <=. u &&* u <=. v

instance (AstSpan s, GoodScalar r) => EqH (AstTensor ms s) (TKX sh r) where
  v ==. u = v <=. u &&* u <=. v

instance (AstSpan s, GoodScalar r) => OrdH (AstTensor ms s) (TKR n r) where
  v <=. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withCastRS shv' $ \shv ->
          withCastRS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstLeqS (AstSFromR shu $ primalPart v)
                        (AstSFromR shv $ primalPart u)
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)

instance (AstSpan s, GoodScalar r) => OrdH (AstTensor ms s) (TKX sh r) where
  v <=. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withCastXS shv' $ \shv ->
          withCastXS shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                AstLeqS (AstSFromX shu $ primalPart v)
                        (AstSFromX shv $ primalPart u)
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)

instance (AstSpan s, GoodScalar r)
         => EqH (AstTensor ms s) (TKScalar r) where
  v ==. u = v <=. u &&* u <=. v

instance (AstSpan s, GoodScalar r)
         => EqH (AstTensor ms s) (TKS sh r) where
  v ==. u = v <=. u &&* u <=. v

-- These are common in indexing, so worth optimizing early via AstConcrete.
-- We keep AstConcrete on the left, as with AstPlusK and others.
instance (AstSpan s, GoodScalar r)
         => OrdH (AstTensor ms s) (TKScalar r) where
  u <=. v | let (u1, u2) = bounds u
                (v1, v2) = bounds v
          , u2 <= v1 || u1 > v2 = AstBoolConst (u2 <= v1)
  AstFromPrimal u <=. AstFromPrimal v = u <=. v
  AstPrimalPart u <=. AstPrimalPart v = u <=. v
  AstFromDual u <=. AstFromDual v = u <=. v  -- TODO: correct?
  AstFromS STKScalar u <=. AstFromS STKScalar v
    | FTKS ZSS (FTKScalar @ru) <- ftkAst u
    , FTKS ZSS (FTKScalar @rv) <- ftkAst v
    , Just Refl <- testEquality (typeRep @ru) (typeRep @rv)
    = u <=. v
  AstConcreteK u <=. AstFromS STKScalar v
    | FTKS ZSS (FTKScalar @rv) <- ftkAst v
    , Just Refl <- testEquality (typeRep @rv) (typeRep @r)
    = AstConcreteS (unConcrete $ sfromK $ Concrete u) <=. v
  u <=. AstPlusK (AstConcreteK v) w =
    u - AstConcreteK v <=. w
  AstPlusK (AstConcreteK u) w <=. v =
    AstConcreteK u <=. v - w
  u <=. AstConcreteK v =
    AstConcreteK (negate v) <=. negate u
  AstConcreteK u <=. AstTimesK (AstConcreteK v) w
    | v > 0 && u >= 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstConcreteK ((u + v - 1) `quotH` v) <=. w -- 10 == 5 * 2, 11 > 5 * 2
  AstConcreteK u <=. AstTimesK (AstConcreteK v) w
    | v > 0 && u < 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstConcreteK (u `quotH` v) <=. w  -- -10 == 5 * -2, -9 > 5 * -2
  AstConcreteK u <=. AstTimesK (AstConcreteK v) w
    | v < 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstConcreteK u <=. AstTimesK (AstConcreteK $ negate v) (AstN1K NegateOp w)
  v@AstConcreteK{} <=. u =
    AstLeqK (primalPart v) (primalPart u)
  v <=. u =
    AstConcreteK 0 <=. primalPart u - primalPart v

instance (AstSpan s, GoodScalar r)
         => OrdH (AstTensor ms s) (TKS sh r) where
  AstFromPrimal u <=. AstFromPrimal v = u <=. v
  AstFromDual u <=. AstFromDual v = u <=. v  -- TODO: correct?
  AstPrimalPart u <=. AstPrimalPart v = u <=. v
  AstSFromK u <=. AstSFromK v = u <=. v
  AstConcreteS u <=. AstSFromK v =
    AstConcreteK (unConcrete $ kfromS $ Concrete u) <=. v
  AstConcreteS u <=. AstConcreteS v =
    AstBoolConst $ Concrete @(TKS sh r) u <=. Concrete v
  u <=. AstPlusS (AstConcreteS v) w =
    u - AstConcreteS v <=. w
  AstPlusS (AstConcreteS u) w <=. v =
    AstConcreteS u <=. v - w
  u <=. AstConcreteS v =
    AstConcreteS (negate v) <=. negate u
  AstVar u <=. AstVar v | u == v =
    AstBoolConst True
  AstSFromR _ (AstVar u) <=. AstSFromR _ (AstVar v) | u == v =
    AstBoolConst True
  AstSFromX _ (AstVar u) <=. AstSFromX _ (AstVar v)
    | varNameToAstVarId u == varNameToAstVarId v =
      AstBoolConst True
  v <=. u = AstLeqS (primalPart v) (primalPart u)


-- * AstRaw, AstNoVectorize and AstNoSimplify definitions

-- | An AST variant that doesn't vectorize terms and also builds them
-- with ordinary, non-simplifying constructors. It's based on sharing
-- rather than lets and commonly used as the instance for primals
-- inside ADVal and, consequently, used for evaluating delta expressions.
type role AstRaw nominal nominal
newtype AstRaw s y =
  AstRaw {unAstRaw :: AstTensor AstMethodShare s y}
 deriving Show

-- | An AST variant for testing that doesn't vectorize terms, but still
-- builds them using simplifying smart constructors.
type role AstNoVectorize nominal nominal
newtype AstNoVectorize s y =
  AstNoVectorize {unAstNoVectorize :: AstTensor AstMethodLet s y}
 deriving Show

-- | An AST variant for testing that vectorizes terms, but builds them
-- with ordinary, non-simplifying constructors.
type role AstNoSimplify nominal nominal
newtype AstNoSimplify s y =
  AstNoSimplify {unAstNoSimplify :: AstTensor AstMethodLet s y}
 deriving Show


-- * AstRaw, AstNoVectorize and AstNoSimplify type family instances

type instance PrimalOf (AstRaw s) = AstRaw PrimalSpan
type instance DualOf (AstRaw s) = AstTensor AstMethodShare DualSpan
type instance ShareOf (AstRaw s) = AstRaw s
type instance HFunOf (AstRaw s) x y = AstHFun s s x y
type instance BoolOf (AstRaw s) = AstBool AstMethodShare

type instance PrimalOf (AstNoVectorize s) = AstNoVectorize PrimalSpan
type instance DualOf (AstNoVectorize s) = AstTensor AstMethodLet DualSpan
type instance ShareOf (AstNoVectorize s) = AstRaw s
type instance HFunOf (AstNoVectorize s) x z = AstHFun s s x z
type instance BoolOf (AstNoVectorize s) = AstBool AstMethodLet

type instance PrimalOf (AstNoSimplify s) = AstNoSimplify PrimalSpan
type instance DualOf (AstNoSimplify s) = AstTensor AstMethodLet DualSpan
type instance ShareOf (AstNoSimplify s) = AstRaw s
type instance HFunOf (AstNoSimplify s) x z = AstHFun s s x z
type instance BoolOf (AstNoSimplify s) = AstBool AstMethodLet


-- * AstRaw, AstNoVectorize and AstNoSimplify other instances

instance EqH (AstTensor AstMethodShare s) y => EqH (AstRaw s) y where
  AstRaw v ==. AstRaw u = v ==. u
instance OrdH (AstTensor AstMethodShare s) y => OrdH (AstRaw s) y where
  AstRaw v <=. AstRaw u = v <=. u

deriving instance Eq (AstRaw s y)
deriving instance Ord (AstRaw s y)
deriving instance Num (AstTensor AstMethodShare s y) => Num (AstRaw s y)
deriving instance IntegralH (AstTensor AstMethodShare s y)
                  => IntegralH (AstRaw s y)
deriving instance Fractional (AstTensor AstMethodShare s y)
                  => Fractional (AstRaw s y)
deriving instance Floating (AstTensor AstMethodShare s y)
                  => Floating (AstRaw s y)
deriving instance RealFloatH (AstTensor AstMethodShare s y)
                  => RealFloatH (AstRaw s y)

instance EqH (AstTensor AstMethodLet s) y => EqH (AstNoVectorize s) y where
  AstNoVectorize v ==. AstNoVectorize u = v ==. u
instance OrdH (AstTensor AstMethodLet s) y => OrdH (AstNoVectorize s) y where
  AstNoVectorize v <=. AstNoVectorize u = v <=. u
deriving instance Eq (AstNoVectorize s y)
deriving instance Ord (AstNoVectorize s y)
deriving instance Num (AstTensor AstMethodLet s y) => Num (AstNoVectorize s y)
deriving instance (IntegralH (AstTensor AstMethodLet s y))
                  => IntegralH (AstNoVectorize s y)
deriving instance Fractional (AstTensor AstMethodLet s y)
                  => Fractional (AstNoVectorize s y)
deriving instance Floating (AstTensor AstMethodLet s y)
                  => Floating (AstNoVectorize s y)
deriving instance (RealFloatH (AstTensor AstMethodLet s y))
                  => RealFloatH (AstNoVectorize s y)

instance EqH (AstTensor AstMethodLet s) y => EqH (AstNoSimplify s) y where
  AstNoSimplify v ==. AstNoSimplify u = v ==. u
instance OrdH (AstTensor AstMethodLet s) y => OrdH (AstNoSimplify s) y where
  AstNoSimplify v <=. AstNoSimplify u = v <=. u
deriving instance Eq (AstNoSimplify s y)
deriving instance Ord (AstNoSimplify s y)
deriving instance Num (AstTensor AstMethodLet s y) => Num (AstNoSimplify s y)
deriving instance (IntegralH (AstTensor AstMethodLet s y))
                  => IntegralH (AstNoSimplify s y)
deriving instance Fractional (AstTensor AstMethodLet s y)
                  => Fractional (AstNoSimplify s y)
deriving instance Floating (AstTensor AstMethodLet s y)
                  => Floating (AstNoSimplify s y)
deriving instance (RealFloatH (AstTensor AstMethodLet s y))
                  => RealFloatH (AstNoSimplify s y)
