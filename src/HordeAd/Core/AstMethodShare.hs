{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Arithmetic instances for AST with sharing method AstMethodShare.
module HordeAd.Core.AstMethodShare
  ( cAstConvDownKFromS, cAstConvDownSFromR, cAstConvDownSFromX
  , cAstConvUpSFromK, cAstConvUpRFromS, cAstConvUpXFromS
  , astShareNoSimplify
  ) where

import Prelude

import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested (MapJust)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (withShsFromShR, withShsFromShX)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersAst
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Conversion
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

cAstConvDownKFromS :: forall r s.
                      AstTensor AstMethodShare s (TKS '[] r)
                   -> AstTensor AstMethodShare s (TKScalar r)
cAstConvDownKFromS = AstConvert (ConvCmp ConvX0 ConvSX)

cAstConvDownSFromR :: forall sh x s.
                      ShS sh -> FullShapeTK x
                   -> AstTensor AstMethodShare s (TKR2 (Rank sh) x)
                   -> AstTensor AstMethodShare s (TKS2 sh x)
cAstConvDownSFromR sh x t | Refl <- lemRankReplicate (Proxy @(Rank sh)) =
  AstConvert (ConvCmp (ConvXS' (FTKS sh x)) ConvRX) t

cAstConvDownSFromX :: forall sh sh' x s. Rank sh ~ Rank sh'
                   => ShS sh -> FullShapeTK x
                   -> AstTensor AstMethodShare s (TKX2 sh' x)
                   -> AstTensor AstMethodShare s (TKS2 sh x)
cAstConvDownSFromX sh x t = AstConvert (ConvXS' (FTKS sh x)) t

cAstConvUpSFromK :: forall r s. GoodScalar r
                 => AstTensor AstMethodShare s (TKScalar r)
                 -> AstTensor AstMethodShare s (TKS '[] r)
cAstConvUpSFromK = AstConvert (ConvCmp ConvXS (Conv0X STKScalar))

cAstConvUpRFromS :: forall sh x s.
                    ShS sh -> FullShapeTK x
                 -> AstTensor AstMethodShare s (TKS2 sh x)
                 -> AstTensor AstMethodShare s (TKR2 (Rank sh) x)
cAstConvUpRFromS sh x | Refl <- lemRankMapJust sh =
  AstConvert (ConvCmp (ConvXR (ftkToSTK x)) ConvSX)

cAstConvUpXFromS :: forall sh sh' x s. Rank sh ~ Rank sh'
                 => IShX sh' -> FullShapeTK x
                 -> AstTensor AstMethodShare s (TKS2 sh x)
                 -> AstTensor AstMethodShare s (TKX2 sh' x)
cAstConvUpXFromS sh' x =
  gcastWith (unsafeCoerceRefl :: Rank (MapJust sh) :~: Rank sh) $
  AstConvert (ConvCmp (ConvXX' (FTKX sh' x)) ConvSX)

liftRFromS1 :: forall n x s.
               (forall sh.
                   AstTensor AstMethodShare s (TKS2 sh x)
                -> AstTensor AstMethodShare s (TKS2 sh x))
            -> AstTensor AstMethodShare s (TKR2 n x)
            -> AstTensor AstMethodShare s (TKR2 n x)
{-# INLINE liftRFromS1 #-}
liftRFromS1 f a = case ftkAst a of
  FTKR sh' x ->
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      cAstConvUpRFromS sh x
      $ f (cAstConvDownSFromR sh x a)

liftRFromS2 :: forall n x s.
               (forall sh.
                   AstTensor AstMethodShare s (TKS2 sh x)
                -> AstTensor AstMethodShare s (TKS2 sh x)
                -> AstTensor AstMethodShare s (TKS2 sh x))
            -> AstTensor AstMethodShare s (TKR2 n x)
            -> AstTensor AstMethodShare s (TKR2 n x)
            -> AstTensor AstMethodShare s (TKR2 n x)
{-# INLINE liftRFromS2 #-}
liftRFromS2 f a b  = case ftkAst a of
  FTKR sh' x ->
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      cAstConvUpRFromS sh x
      $ f (cAstConvDownSFromR sh x a) (cAstConvDownSFromR sh x b)

liftXFromS1 :: forall sh' x s.
               (forall sh.
                   AstTensor AstMethodShare s (TKS2 sh x)
                -> AstTensor AstMethodShare s (TKS2 sh x))
            -> AstTensor AstMethodShare s (TKX2 sh' x)
            -> AstTensor AstMethodShare s (TKX2 sh' x)
{-# INLINE liftXFromS1 #-}
liftXFromS1 f a = case ftkAst a of
  FTKX sh' x ->
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      cAstConvUpXFromS sh' x
      $ f (cAstConvDownSFromX sh x a)

liftXFromS2 :: forall sh' x s.
               (forall sh.
                   AstTensor AstMethodShare s (TKS2 sh x)
                -> AstTensor AstMethodShare s (TKS2 sh x)
                -> AstTensor AstMethodShare s (TKS2 sh x))
            -> AstTensor AstMethodShare s (TKX2 sh' x)
            -> AstTensor AstMethodShare s (TKX2 sh' x)
            -> AstTensor AstMethodShare s (TKX2 sh' x)
{-# INLINE liftXFromS2 #-}
liftXFromS2 f a b = case ftkAst a of
  FTKX sh' x ->
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      cAstConvUpXFromS sh' x
      $ f (cAstConvDownSFromX sh x a) (cAstConvDownSFromX sh x b)


-- * Unlawful numeric instances for AST scalars; they are lawful modulo evaluation

-- The normal form has AstConcreteK or AstFromPlain (AstConcreteK),
-- if any, as the first argument of the constructor.
-- No flattening is performed beyond that.
instance (NumScalar r, KnownSpan s)
         => Num (AstTensor AstMethodShare s (TKScalar r)) where
  (+) = AstPlusK
  (*) = AstTimesK
  negate = AstN1K NegateOp
  abs = AstN1K AbsOp
  signum = AstN1K SignumOp
  {-# INLINE fromInteger #-}
  fromInteger i = fromPlain $ AstConcreteK (fromInteger i)

instance (NumScalar r, IntegralH r, Nested.IntElt r, KnownSpan s)
         => IntegralH (AstTensor AstMethodShare s (TKScalar r)) where
  quotH = AstI2K QuotOp
  remH = AstI2K RemOp

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Fractional (AstTensor AstMethodShare s (TKScalar r)) where
  (/) = AstR2K DivideOp
  recip = AstR1K RecipOp
  {-# INLINE fromRational #-}
  fromRational r = fromPlain $ AstConcreteK (fromRational r)

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Floating (AstTensor AstMethodShare s (TKScalar r)) where
  pi = error "pi is not defined for tensors"
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

instance (NumScalar r, Differentiable r, KnownSpan s)
         => RealFloatH (AstTensor AstMethodShare s (TKScalar r)) where
  atan2H = AstR2K Atan2Op


-- * Unlawful numeric instances for shaped AST; lawful modulo evaluation

instance NumScalar r
         => Num (AstTensor AstMethodShare s (TKS sh r)) where
  (+) = AstPlusS
  (*) = AstTimesS
  negate = AstN1S NegateOp
  abs = AstN1S AbsOp
  signum = AstN1S SignumOp
  fromInteger i = error $ "fromInteger is not defined for shaped tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r)
         => IntegralH (AstTensor AstMethodShare s (TKS sh r)) where
  quotH = AstI2S QuotOp
  remH = AstI2S RemOp

instance (NumScalar r, Differentiable r)
         => Fractional (AstTensor AstMethodShare s (TKS sh r)) where
  (/) = AstR2S DivideOp
  recip = AstR1S RecipOp
  fromRational r = error $ "fromRational is not defined for shaped tensors: "
                           ++ show r

instance (NumScalar r, Differentiable r)
         => Floating (AstTensor AstMethodShare s (TKS sh r)) where
  pi = error "pi is not defined for tensors"
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

instance (NumScalar r, Differentiable r)
         => RealFloatH (AstTensor AstMethodShare s (TKS sh r)) where
  atan2H = AstR2S Atan2Op


-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

instance Boolean (AstBool AstMethodShare) where
  true = AstConcreteK True
  false = AstConcreteK False
  notB = AstBoolNotK
  (&&*) = AstBoolAndK
  b ||* c = notB (notB b &&* notB c)

-- Since u and v are duplicated here, they need to be shared.
-- We share their difference, which would most likely appear in the
-- inequalities once they are rewritten, to ensure it's shared and whatever
-- vectorization substitutes into it is shared as well.
-- Otherwise, if u and v are variables, the sharing would vanish
-- before vectoriation complicates the expression a bit, making it
-- worth sharing.
instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodShare s) (TKScalar r) where
  vUnshared ==. uUnshared =
    let uv = astShareNoSimplify (uUnshared - vUnshared)
    in 0 <=. uv &&* uv <=. 0

instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodShare s) (TKS sh r) where
  vUnshared ==. uUnshared =
    let uv = astShareNoSimplify (uUnshared - vUnshared)
        zero = fromPlain $ AstConcreteS $ defTargetRep $ ftkAst vUnshared
    in zero <=. uv &&* uv <=. zero

instance (KnownSpan s, NumScalar r)
         => OrdH (AstTensor AstMethodShare s) (TKScalar r) where
  v <=. u = AstLeqK (plainPart v) (plainPart u)

instance (KnownSpan s, NumScalar r)
         => OrdH (AstTensor AstMethodShare s) (TKS sh r) where
  v <=. u = AstLeq (plainPart v) (plainPart u)


-- * Unlawful numeric instances for ranked AST; lawful modulo evaluation

instance NumScalar r
         => Num (AstTensor AstMethodShare s (TKR n r)) where
  (+) = liftRFromS2 (+)
  (-) = liftRFromS2 (-)
  (*) = liftRFromS2 (*)
  negate = liftRFromS1 negate
  abs = liftRFromS1 abs
  signum = liftRFromS1 signum
  fromInteger i = error $ "fromInteger is not defined for ranked tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r)
         => IntegralH (AstTensor AstMethodShare s (TKR n r)) where
  quotH = liftRFromS2 quotH
  remH = liftRFromS2 remH

instance (NumScalar r, Differentiable r)
         => Fractional (AstTensor AstMethodShare s (TKR n r)) where
  (/) = liftRFromS2 (/)
  recip = liftRFromS1 recip
  fromRational r = error $ "fromRational is not defined for ranked tensors: "
                           ++ show r

instance (NumScalar r, Differentiable r)
         => Floating (AstTensor AstMethodShare s (TKR n r)) where
  pi = error "pi is not defined for tensors"
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

instance (NumScalar r, Differentiable r)
         => RealFloatH (AstTensor AstMethodShare s (TKR n r)) where
  atan2H = liftRFromS2 atan2H

instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodShare s) (TKR n r) where
  v ==. u = case ftkAst v of
    FTKR shv' x -> case ftkAst u of
      FTKR shu' _ ->
        withShsFromShR shv' $ \shv ->
          withShsFromShR shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstConvDownSFromR shu x v ==. cAstConvDownSFromR shv x u
              _ -> error $ "(==.): shapes don't match: "
                           ++ show (shu, shv)

instance (KnownSpan s, NumScalar r)
         => OrdH (AstTensor AstMethodShare s) (TKR n r) where
  v <=. u = case ftkAst v of
    FTKR shv' x -> case ftkAst u of
      FTKR shu' _ ->
        withShsFromShR shv' $ \shv ->
          withShsFromShR shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstConvDownSFromR shu x v <=. cAstConvDownSFromR shv x u
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)


-- * Unlawful numeric instances for mixed AST; lawful modulo evaluation

instance NumScalar r
         => Num (AstTensor AstMethodShare s (TKX sh r)) where
  (+) = liftXFromS2 (+)
  (-) = liftXFromS2 (-)
  (*) = liftXFromS2 (*)
  negate = liftXFromS1 negate
  abs = liftXFromS1 abs
  signum = liftXFromS1 signum
  fromInteger i = error $ "fromInteger is not defined for mixed tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r)
         => IntegralH (AstTensor AstMethodShare s (TKX sh r)) where
  quotH = liftXFromS2 quotH
  remH = liftXFromS2 remH

instance (NumScalar r, Differentiable r)
         => Fractional (AstTensor AstMethodShare s (TKX sh r)) where
  (/) = liftXFromS2 (/)
  recip = liftXFromS1 recip
  fromRational r = error $ "fromRational is not defined for mixed tensors: "
                           ++ show r

instance (NumScalar r, Differentiable r)
         => Floating (AstTensor AstMethodShare s (TKX sh r)) where
  pi = error "pi is not defined for tensors"
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

instance (NumScalar r, Differentiable r)
         => RealFloatH (AstTensor AstMethodShare s (TKX sh r)) where
  atan2H = liftXFromS2 atan2H

instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodShare s) (TKX sh r) where
  v ==. u = case ftkAst v of
    FTKX shv' x -> case ftkAst u of
      FTKX shu' _ ->
        withShsFromShX shv' $ \shv ->
          withShsFromShX shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstConvDownSFromX shu x v ==. cAstConvDownSFromX shv x u
              _ -> error $ "(==.): shapes don't match: "
                           ++ show (shu, shv)

instance (KnownSpan s, NumScalar r)
         => OrdH (AstTensor AstMethodShare s) (TKX sh r) where
  v <=. u = case ftkAst v of
    FTKX shv' x -> case ftkAst u of
      FTKX shu' _ ->
        withShsFromShX shv' $ \shv ->
          withShsFromShX shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstConvDownSFromX shu x v <=. cAstConvDownSFromX shv x u
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)


-- * AstRaw instances

instance Boolean (AstRaw PlainSpan (TKScalar Bool)) where
  true = AstRaw true
  false = AstRaw false
  notB b = AstRaw (notB $ unAstRaw b)
  b &&* c = AstRaw (unAstRaw b &&* unAstRaw c)
  b ||* c = AstRaw (unAstRaw b ||* unAstRaw c)

instance (EqH (AstTensor AstMethodShare s) y)
         => EqH (AstRaw s) y where
  AstRaw v ==. AstRaw u = AstRaw $ v ==. u
instance (OrdH (AstTensor AstMethodShare s) y)
         => OrdH (AstRaw s) y where
  AstRaw v <=. AstRaw u = AstRaw $ v <=. u

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


-- * Misc

astShareNoSimplify :: KnownSpan s
                   => AstTensor AstMethodShare s y
                   -> AstTensor AstMethodShare s y
{-# NOINLINE astShareNoSimplify #-}
astShareNoSimplify a | astIsSmall True a = a
                         -- too important an optimization to skip
astShareNoSimplify a = case a of
  AstFromPrimal v -> fromPrimal $ astShareNoSimplify v
  AstFromDual v -> fromDual $ astShareNoSimplify v
  AstFromPlain v -> fromPlain $ astShareNoSimplify v
  _ -> unsafePerformIO $ case ftkAst a of
    ftk@FTKScalar -> do
        var <- funToAstAutoBoundsIO ftk a
        pure $! astShare var a
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> do
        let v = cAstConvDownSFromR sh x a
        var <- funToAstNoBoundsIO (FTKS sh x)
        pure $! cAstConvUpRFromS sh x $ astShare var v
    FTKX sh' x ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> do
        let v = cAstConvDownSFromX sh x a
        var <- funToAstNoBoundsIO (FTKS sh x)
        pure $! cAstConvUpXFromS sh' x $ astShare var v
    FTKS ZSS x@FTKScalar -> do
        let v = cAstConvDownKFromS a
        var <- funToAstAutoBoundsIO x v
        pure $! cAstConvUpSFromK $ astShare var v
    -- calling recursively for product may be not worth it
    ftk -> do
        var <- funToAstNoBoundsIO ftk
        pure $! astShare var a
