{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Arithmetic instances for AST with sharing method AstMethodLet.
-- The bulk of the instances is defined in 'AstSimplify`, the remaining
-- instances are here.
module HordeAd.Core.AstMethodLet
  (
  ) where

import Prelude

import Data.Type.Equality (testEquality, (:~:) (Refl))

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (withShsFromShR, withShsFromShX)
import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersAst
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

liftRFromS1 :: forall n x s. KnownSpan s
            => (forall sh.
                   AstTensor AstMethodLet s (TKS2 sh x)
                -> AstTensor AstMethodLet s (TKS2 sh x))
            -> AstTensor AstMethodLet s (TKR2 n x)
            -> AstTensor AstMethodLet s (TKR2 n x)
{-# INLINE liftRFromS1 #-}
liftRFromS1 f a = case ftkAst a of
  FTKR sh' x ->
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      astConvUpRFromS sh x $ f (astConvDownSFromR sh x a)

liftRFromS2 :: forall n x s. KnownSpan s
            => (forall sh.
                   AstTensor AstMethodLet s (TKS2 sh x)
                -> AstTensor AstMethodLet s (TKS2 sh x)
                -> AstTensor AstMethodLet s (TKS2 sh x))
            -> AstTensor AstMethodLet s (TKR2 n x)
            -> AstTensor AstMethodLet s (TKR2 n x)
            -> AstTensor AstMethodLet s (TKR2 n x)
{-# INLINE liftRFromS2 #-}
liftRFromS2 f a b  = case ftkAst a of
  FTKR sh' x ->
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      astConvUpRFromS sh x
      $ f (astConvDownSFromR sh x a) (astConvDownSFromR sh x b)

liftXFromS1 :: forall sh' x s. KnownSpan s
            => (forall sh.
                   AstTensor AstMethodLet s (TKS2 sh x)
                -> AstTensor AstMethodLet s (TKS2 sh x))
            -> AstTensor AstMethodLet s (TKX2 sh' x)
            -> AstTensor AstMethodLet s (TKX2 sh' x)
{-# INLINE liftXFromS1 #-}
liftXFromS1 f a = case ftkAst a of
  FTKX sh' x ->
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      astConvUpXFromS sh' x $ f (astConvDownSFromX sh x a)

liftXFromS2 :: forall sh' x s. KnownSpan s
            => (forall sh.
                   AstTensor AstMethodLet s (TKS2 sh x)
                -> AstTensor AstMethodLet s (TKS2 sh x)
                -> AstTensor AstMethodLet s (TKS2 sh x))
            -> AstTensor AstMethodLet s (TKX2 sh' x)
            -> AstTensor AstMethodLet s (TKX2 sh' x)
            -> AstTensor AstMethodLet s (TKX2 sh' x)
{-# INLINE liftXFromS2 #-}
liftXFromS2 f a b = case ftkAst a of
  FTKX sh' x ->
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      astConvUpXFromS sh' x
      $ f (astConvDownSFromX sh x a) (astConvDownSFromX sh x b)


-- * Unlawful numeric instances for ranked AST; lawful modulo evaluation

instance (NumScalar r, KnownSpan s)
         => Num (AstTensor AstMethodLet s (TKR n r)) where
  (+) = liftRFromS2 (+)
  (-) = liftRFromS2 (-)
  (*) = liftRFromS2 (*)
  negate = liftRFromS1 negate
  abs = liftRFromS1 abs
  signum = liftRFromS1 signum
  fromInteger i = error $ "fromInteger is not defined for ranked tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r, KnownSpan s)
         => IntegralH (AstTensor AstMethodLet s (TKR n r)) where
  quotH = liftRFromS2 quotH
  remH = liftRFromS2 remH

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Fractional (AstTensor AstMethodLet s (TKR n r)) where
  (/) = liftRFromS2 (/)
  recip = liftRFromS1 recip
  fromRational r = error $ "fromRational is not defined for ranked tensors: "
                           ++ show r

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Floating (AstTensor AstMethodLet s (TKR n r)) where
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

instance (NumScalar r, Differentiable r, KnownSpan s)
         => RealFloatH (AstTensor AstMethodLet s (TKR n r)) where
  atan2H = liftRFromS2 atan2H

-- TODO: refactor with something like liftRFromS2
instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodLet s) (TKR n r) where
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
         => OrdH (AstTensor AstMethodLet s) (TKR n r) where
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

instance (NumScalar r, KnownSpan s)
         => Num (AstTensor AstMethodLet s (TKX sh r)) where
  (+) = liftXFromS2 (+)
  (-) = liftXFromS2 (-)
  (*) = liftXFromS2 (*)
  negate = liftXFromS1 negate
  abs = liftXFromS1 abs
  signum = liftXFromS1 signum
  fromInteger i = error $ "fromInteger is not defined for mixed tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r, KnownSpan s)
         => IntegralH (AstTensor AstMethodLet s (TKX sh r)) where
  quotH = liftXFromS2 quotH
  remH = liftXFromS2 remH

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Fractional (AstTensor AstMethodLet s (TKX sh r)) where
  (/) = liftXFromS2 (/)
  recip = liftXFromS1 recip
  fromRational r = error $ "fromRational is not defined for mixed tensors: "
                           ++ show r

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Floating (AstTensor AstMethodLet s (TKX sh r)) where
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

instance (NumScalar r, Differentiable r, KnownSpan s)
         => RealFloatH (AstTensor AstMethodLet s (TKX sh r)) where
  atan2H = liftXFromS2 atan2H

instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodLet s) (TKX sh r) where
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
         => OrdH (AstTensor AstMethodLet s) (TKX sh r) where
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


--- * AstNoVectorize and AstNoSimplify instances

instance Boolean (AstNoVectorize PlainSpan (TKScalar Bool)) where
  true = AstNoVectorize true
  false = AstNoVectorize false
  notB b = AstNoVectorize (notB $ unAstNoVectorize b)
  b &&* c = AstNoVectorize (unAstNoVectorize b &&* unAstNoVectorize c)
  b ||* c = AstNoVectorize (unAstNoVectorize b ||* unAstNoVectorize c)

instance (EqH (AstTensor AstMethodLet s) y)
         => EqH (AstNoVectorize s) y where
  AstNoVectorize v ==. AstNoVectorize u = AstNoVectorize $ v ==. u
instance (OrdH (AstTensor AstMethodLet s) y)
         => OrdH (AstNoVectorize s) y where
  AstNoVectorize v <=. AstNoVectorize u = AstNoVectorize $ v <=. u

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

instance Boolean (AstNoSimplify PlainSpan (TKScalar Bool)) where
  true = AstNoSimplify true
  false = AstNoSimplify false
  notB b = AstNoSimplify (notB $ unAstNoSimplify b)
  b &&* c = AstNoSimplify (unAstNoSimplify b &&* unAstNoSimplify c)
  b ||* c = AstNoSimplify (unAstNoSimplify b ||* unAstNoSimplify c)

instance (EqH (AstTensor AstMethodLet s) y)
         => EqH (AstNoSimplify s) y where
  AstNoSimplify v ==. AstNoSimplify u = AstNoSimplify $ v ==. u
instance (OrdH (AstTensor AstMethodLet s) y)
         => OrdH (AstNoSimplify s) y where
  AstNoSimplify v <=. AstNoSimplify u = AstNoSimplify $ v <=. u

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
