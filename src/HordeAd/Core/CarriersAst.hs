{-# LANGUAGE AllowAmbiguousTypes #-}
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

import Data.Type.Equality ((:~:) (Refl))
import GHC.TypeLits (KnownNat)

import Data.Array.Nested (KnownShS (..), KnownShX)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.Ast
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.HVector
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.Types

-- * Basic type family instances

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

-- * Unlawful numeric instances of ranked AST; they are lawful modulo evaluation

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstTensor ms s y) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstTensor ms s y) where
  (<=) = error "AST requires that OrdF be used instead"

instance (Num (Nested.Ranked n r), GoodScalar r, KnownNat n)
         => Num (AstTensor ms s (TKR n r)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfListR (AstConcrete ftk u : lu) + AstSumOfListR (AstConcrete _ v : lv) =
    AstSumOfListR (AstConcrete ftk (u + v) : lu ++ lv)
  AstSumOfListR lu + AstSumOfListR (AstConcrete ftk v : lv) =
    AstSumOfListR (AstConcrete ftk v : lv ++ lu)
  AstSumOfListR lu + AstSumOfListR lv = AstSumOfListR (lu ++ lv)

  AstConcrete ftk u + AstSumOfListR (AstConcrete _ v : lv) =
    AstSumOfListR (AstConcrete ftk (u + v) : lv)
  u + AstSumOfListR (AstConcrete ftk v : lv) = AstSumOfListR (AstConcrete ftk v : u : lv)
  u + AstSumOfListR lv = AstSumOfListR (u : lv)

  AstSumOfListR (AstConcrete ftk u : lu) + AstConcrete _ v =
    AstSumOfListR (AstConcrete ftk (u + v) : lu)
  AstSumOfListR (AstConcrete ftk u : lu) + v = AstSumOfListR (AstConcrete ftk u : v : lu)
  AstSumOfListR lu + v = AstSumOfListR (v : lu)

  AstConcrete ftk u + AstConcrete _ v = AstConcrete ftk (u + v)
  u + AstConcrete ftk v = AstSumOfListR [AstConcrete ftk v, u]
  u + v = AstSumOfListR [u, v]

  AstConcrete ftk u - AstConcrete _ v =
    AstConcrete ftk (u - v)  -- common in indexing
  u - v = AstN2R MinusOp u v

  AstConcrete ftk u * AstConcrete _ v =
    AstConcrete ftk (u * v)  -- common in indexing
  u * v = AstN2R TimesOp u v

  negate (AstConcrete ftk u) = AstConcrete ftk $ negate u  -- common in indexing
  negate u = AstN1R NegateOp u
  abs = AstN1R AbsOp
  signum = AstN1R SignumOp
  fromInteger i = error $ "fromInteger not defined for ranked tensors: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (GoodScalar r, Integral r, KnownNat n)
         => IntegralF (AstTensor ms s (TKR n r)) where
  quotF = AstI2R QuotOp
  remF = AstI2R RemOp

instance (GoodScalar r, Differentiable r, Fractional (Nested.Ranked n r), KnownNat n)
         => Fractional (AstTensor ms s (TKR n r)) where
  u / v = AstR2R DivideOp u v
  recip = AstR1R RecipOp
  fromRational r = error $ "fromRational not defined for AST: "
                           ++ show r

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Floating (AstTensor ms s (TKR n r)) where
  pi = error "pi not defined for ranked tensors"
  exp = AstR1R ExpOp
  log = AstR1R LogOp
  sqrt = AstR1R SqrtOp
  (**) = AstR2R PowerOp
  logBase = AstR2R LogBaseOp
  sin = AstR1R SinOp
  cos = AstR1R CosOp
  tan = AstR1R TanOp
  asin = AstR1R AsinOp
  acos = AstR1R AcosOp
  atan = AstR1R AtanOp
  sinh = AstR1R SinhOp
  cosh = AstR1R CoshOp
  tanh = AstR1R TanhOp
  asinh = AstR1R AsinhOp
  acosh = AstR1R AcoshOp
  atanh = AstR1R AtanhOp

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => RealFloatF (AstTensor ms s (TKR n r)) where
  atan2F = AstR2R Atan2Op


-- * Unlawful numeric instances of shaped AST; they are lawful modulo evaluation

instance (GoodScalar r, Num (Nested.Shaped sh r), KnownShS sh, AstSpan s)
         => Num (AstTensor ms s (TKS sh r)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfListS (AstConcrete ftk u : lu) + AstSumOfListS (AstConcrete _ v : lv) =
    AstSumOfListS (AstConcrete ftk (u + v) : lu ++ lv)
  AstSumOfListS lu + AstSumOfListS (AstConcrete ftk v : lv) =
    AstSumOfListS (AstConcrete ftk v : lv ++ lu)
  AstSumOfListS lu + AstSumOfListS lv = AstSumOfListS (lu ++ lv)

  AstConcrete ftk u + AstSumOfListS (AstConcrete _ v : lv) =
    AstSumOfListS (AstConcrete ftk (u + v) : lv)
  u + AstSumOfListS (AstConcrete ftk v : lv) =
    AstSumOfListS (AstConcrete ftk v : u : lv)
  u + AstSumOfListS lv = AstSumOfListS (u : lv)

  AstSumOfListS (AstConcrete ftk u : lu) + AstConcrete _ v =
    AstSumOfListS (AstConcrete ftk (u + v) : lu)
  AstSumOfListS (AstConcrete ftk u : lu) + v =
    AstSumOfListS (AstConcrete ftk u : v : lu)
  AstSumOfListS lu + v = AstSumOfListS (v : lu)

  AstConcrete ftk u + AstConcrete _ v = AstConcrete ftk (u + v)
  u + AstConcrete ftk v = AstSumOfListS [AstConcrete ftk v, u]
  u + v = AstSumOfListS [u, v]

  AstConcrete ftk u - AstConcrete _ v =
    AstConcrete ftk (u - v)  -- common in indexing
  u - v = AstN2S MinusOp u v

  AstConcrete ftk u * AstConcrete _ v =
    AstConcrete ftk (u * v)  -- common in indexing
  u * v = AstN2S TimesOp u v

  negate = AstN1S NegateOp
  abs = AstN1S AbsOp
  signum = AstN1S SignumOp
  fromInteger :: Integer -> AstTensor ms s (TKS sh r)
  fromInteger i = case sameShape @sh @'[] of
    Just Refl ->
      fromPrimal . AstConcrete (FTKS knownShS FTKScalar) . fromInteger $ i
    Nothing -> error $ "fromInteger not defined for tensors of non-empty shapes: "
                       ++ show (i, knownShS @sh)
    -- it's crucial that there is no AstFromPrimal in fromInteger code
    -- so that we don't need 4 times the simplification rules

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, GoodScalar r, KnownShS sh)
         => IntegralF (AstTensor ms s (TKS sh r)) where
  quotF = AstI2S QuotOp
  remF = AstI2S RemOp

instance ( GoodScalar r, Differentiable r, Fractional (Nested.Shaped sh r)
         , KnownShS sh, AstSpan s )
         => Fractional (AstTensor ms s (TKS sh r)) where
  u / v = AstR2S DivideOp u v
  recip = AstR1S RecipOp
  fromRational r = error $ "fromRational not defined for AST: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShS sh, Floating (Nested.Shaped sh r), AstSpan s)
         => Floating (AstTensor ms s (TKS sh r)) where
  pi = fromPrimal $ AstConcrete (FTKS knownShS FTKScalar) (RepN pi)
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

instance (GoodScalar r, Differentiable r, KnownShS sh, Floating (Nested.Shaped sh r), AstSpan s)
         => RealFloatF (AstTensor ms s (TKS sh r)) where
  atan2F = AstR2S Atan2Op


-- mixed

instance (GoodScalar r, Num (Nested.Mixed sh r), KnownShX sh)
         => Num (AstTensor ms s (TKX sh r)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfListX (AstConcrete ftk u : lu) + AstSumOfListX (AstConcrete _ v : lv) =
    AstSumOfListX (AstConcrete ftk (u + v) : lu ++ lv)
  AstSumOfListX lu + AstSumOfListX (AstConcrete ftk v : lv) =
    AstSumOfListX (AstConcrete ftk v : lv ++ lu)
  AstSumOfListX lu + AstSumOfListX lv = AstSumOfListX (lu ++ lv)

  AstConcrete ftk u + AstSumOfListX (AstConcrete _ v : lv) =
    AstSumOfListX (AstConcrete ftk (u + v) : lv)
  u + AstSumOfListX (AstConcrete ftk v : lv) = AstSumOfListX (AstConcrete ftk v : u : lv)
  u + AstSumOfListX lv = AstSumOfListX (u : lv)

  AstSumOfListX (AstConcrete ftk u : lu) + AstConcrete _ v =
    AstSumOfListX (AstConcrete ftk (u + v) : lu)
  AstSumOfListX (AstConcrete ftk u : lu) + v = AstSumOfListX (AstConcrete ftk u : v : lu)
  AstSumOfListX lu + v = AstSumOfListX (v : lu)

  AstConcrete ftk u + AstConcrete _ v = AstConcrete ftk (u + v)
  u + AstConcrete ftk v = AstSumOfListX [AstConcrete ftk v, u]
  u + v = AstSumOfListX [u, v]

  AstConcrete ftk u - AstConcrete _ v =
    AstConcrete ftk (u - v)  -- common in indexing
  u - v = AstN2X MinusOp u v

  AstConcrete ftk u * AstConcrete _ v =
    AstConcrete ftk (u * v)  -- common in indexing
  u * v = AstN2X TimesOp u v

  negate = AstN1X NegateOp
  abs = AstN1X AbsOp
  signum = AstN1X SignumOp
  fromInteger i = error $ "fromInteger not defined for mixed tensors: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, GoodScalar r, KnownShX sh)
         => IntegralF (AstTensor ms s (TKX sh r)) where
  quotF = AstI2X QuotOp
  remF = AstI2X RemOp

instance ( GoodScalar r, Differentiable r, Fractional (Nested.Mixed sh r)
         , KnownShX sh )
         => Fractional (AstTensor ms s (TKX sh r)) where
  u / v = AstR2X DivideOp u v
  recip = AstR1X RecipOp
  fromRational r = error $ "fromRational not defined for AST: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShX sh, Floating (Nested.Mixed sh r), AstSpan s)
         => Floating (AstTensor ms s (TKX sh r)) where
  pi = error "pi not defined for mixed tensors"
  exp = AstR1X ExpOp
  log = AstR1X LogOp
  sqrt = AstR1X SqrtOp
  (**) = AstR2X PowerOp
  logBase = AstR2X LogBaseOp
  sin = AstR1X SinOp
  cos = AstR1X CosOp
  tan = AstR1X TanOp
  asin = AstR1X AsinOp
  acos = AstR1X AcosOp
  atan = AstR1X AtanOp
  sinh = AstR1X SinhOp
  cosh = AstR1X CoshOp
  tanh = AstR1X TanhOp
  asinh = AstR1X AsinhOp
  acosh = AstR1X AcoshOp
  atanh = AstR1X AtanhOp

instance (GoodScalar r, Differentiable r, KnownShX sh, Floating (Nested.Mixed sh r), AstSpan s)
         => RealFloatF (AstTensor ms s (TKX sh r)) where
  atan2F = AstR2X Atan2Op

-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

instance Boolean (AstBool ms) where
  true = AstBoolConst True
  false = AstBoolConst False
  notB = AstBoolNot
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstB2 AndOp b c
  b ||* c = AstB2 OrOp b c


-- * The AstRaw, AstNoVectorize and AstNoSimplify definitions

type instance PrimalOf (AstRaw s) = AstRaw PrimalSpan
type instance DualOf (AstRaw s) = AstTensor AstMethodShare DualSpan
type instance ShareOf (AstRaw s) = AstRaw s
type instance HFunOf (AstRaw s) x y = AstHFun x y

type instance PrimalOf (AstNoVectorize s) = AstNoVectorize PrimalSpan
type instance DualOf (AstNoVectorize s) = AstTensor AstMethodLet DualSpan
type instance ShareOf (AstNoVectorize s) = AstRaw s
type instance HFunOf (AstNoVectorize s) x z = AstHFun x z

type instance PrimalOf (AstNoSimplify s) = AstNoSimplify PrimalSpan
type instance DualOf (AstNoSimplify s) = AstTensor AstMethodLet DualSpan
type instance ShareOf (AstNoSimplify s) = AstRaw s
type instance HFunOf (AstNoSimplify s) x z = AstHFun x z

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
