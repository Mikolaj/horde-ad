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

import GHC.TypeLits (KnownNat)

import Data.Array.Nested (KnownShS (..))

import HordeAd.Core.Ast
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Basic type family instances

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

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstTensor ms s y) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstTensor ms s y) where
  (<=) = error "AST requires that OrdF be used instead"


-- * Unlawful numeric instances for AST scalars; they are lawful modulo evaluation

instance (GoodScalar r, AstSpan s)
         => Num (AstTensor ms s (TKScalar r)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfList stk (AstConcrete ftk u : lu)
    + AstSumOfList _ (AstConcrete _ v : lv) =
        AstSumOfList stk (AstConcrete ftk (u + v) : lu ++ lv)
  AstSumOfList stk lu + AstSumOfList _ (AstConcrete ftk v : lv) =
    AstSumOfList stk (AstConcrete ftk v : lv ++ lu)
  AstSumOfList stk lu + AstSumOfList _ lv = AstSumOfList stk (lu ++ lv)

  AstConcrete ftk u + AstSumOfList stk (AstConcrete _ v : lv) =
    AstSumOfList stk (AstConcrete ftk (u + v) : lv)
  u + AstSumOfList stk (AstConcrete ftk v : lv) =
    AstSumOfList stk (AstConcrete ftk v : u : lv)
  u + AstSumOfList stk lv = AstSumOfList stk (u : lv)

  AstSumOfList stk (AstConcrete ftk u : lu) + AstConcrete _ v =
    AstSumOfList stk (AstConcrete ftk (u + v) : lu)
  AstSumOfList stk (AstConcrete ftk u : lu) + v =
    AstSumOfList stk (AstConcrete ftk u : v : lu)
  AstSumOfList stk lu + v = AstSumOfList stk (v : lu)

  AstConcrete ftk u + AstConcrete _ v = AstConcrete ftk (u + v)
  u + AstConcrete ftk v = AstSumOfList stensorKind [AstConcrete ftk v, u]
  u + v = AstSumOfList stensorKind [u, v]

  AstConcrete ftk u - AstConcrete _ v =
    AstConcrete ftk (u - v)  -- common in indexing
  u - v = AstN2 MinusOp u v

  AstConcrete ftk u * AstConcrete _ v =
    AstConcrete ftk (u * v)  -- common in indexing
  u * v = AstN2 TimesOp u v

  negate (AstConcrete ftk u) = AstConcrete ftk $ negate u  -- common in indexing
  negate u = AstN1 NegateOp u
  abs = AstN1 AbsOp
  signum = AstN1 SignumOp
  fromInteger i = fromPrimal . AstConcrete FTKScalar . fromInteger $ i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (GoodScalar r, IntegralF r)
         => IntegralF (AstTensor ms s (TKScalar r)) where
  quotF = AstI2 QuotOp
  remF = AstI2 RemOp

instance (GoodScalar r, RealFloatF r, AstSpan s)
         => Fractional (AstTensor ms s (TKScalar r)) where
  u / v = AstR2 DivideOp u v
  recip = AstR1 RecipOp
  fromRational r = fromPrimal . AstConcrete FTKScalar . fromRational $ r

instance (GoodScalar r, RealFloatF r, AstSpan s)
         => Floating (AstTensor ms s (TKScalar r)) where
  pi = error "pi not defined for ranked tensors"
  exp = AstR1 ExpOp
  log = AstR1 LogOp
  sqrt = AstR1 SqrtOp
  (**) = AstR2 PowerOp
  logBase = AstR2 LogBaseOp
  sin = AstR1 SinOp
  cos = AstR1 CosOp
  tan = AstR1 TanOp
  asin = AstR1 AsinOp
  acos = AstR1 AcosOp
  atan = AstR1 AtanOp
  sinh = AstR1 SinhOp
  cosh = AstR1 CoshOp
  tanh = AstR1 TanhOp
  asinh = AstR1 AsinhOp
  acosh = AstR1 AcoshOp
  atanh = AstR1 AtanhOp

instance (GoodScalar r, RealFloatF r, AstSpan s)
         => RealFloatF (AstTensor ms s (TKScalar r)) where
  atan2F = AstR2 Atan2Op


-- * Unlawful numeric instances for ranked AST; they are lawful modulo evaluation

instance (GoodScalar r, KnownNat n)
         => Num (AstTensor ms s (TKR n r)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfList stk (AstConcrete ftk u : lu)
    + AstSumOfList _ (AstConcrete _ v : lv) =
        AstSumOfList stk (AstConcrete ftk (u + v) : lu ++ lv)
  AstSumOfList stk lu + AstSumOfList _ (AstConcrete ftk v : lv) =
    AstSumOfList stk (AstConcrete ftk v : lv ++ lu)
  AstSumOfList stk lu + AstSumOfList _ lv = AstSumOfList stk (lu ++ lv)

  AstConcrete ftk u + AstSumOfList stk (AstConcrete _ v : lv) =
    AstSumOfList stk (AstConcrete ftk (u + v) : lv)
  u + AstSumOfList stk (AstConcrete ftk v : lv) =
    AstSumOfList stk (AstConcrete ftk v : u : lv)
  u + AstSumOfList stk lv = AstSumOfList stk (u : lv)

  AstSumOfList stk (AstConcrete ftk u : lu) + AstConcrete _ v =
    AstSumOfList stk (AstConcrete ftk (u + v) : lu)
  AstSumOfList stk (AstConcrete ftk u : lu) + v =
    AstSumOfList stk (AstConcrete ftk u : v : lu)
  AstSumOfList stk lu + v = AstSumOfList stk (v : lu)

  AstConcrete ftk u + AstConcrete _ v = AstConcrete ftk (u + v)
  u + AstConcrete ftk v = AstSumOfList stensorKind [AstConcrete ftk v, u]
  u + v = AstSumOfList stensorKind [u, v]

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

instance (GoodScalar r, Differentiable r, KnownNat n)
         => Fractional (AstTensor ms s (TKR n r)) where
  u / v = AstR2R DivideOp u v
  recip = AstR1R RecipOp
  fromRational r = error $ "fromRational not defined for ranked tensors: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownNat n)
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

instance (GoodScalar r, Differentiable r, KnownNat n)
         => RealFloatF (AstTensor ms s (TKR n r)) where
  atan2F = AstR2R Atan2Op


-- * Unlawful numeric instances for shaped AST; they are lawful modulo evaluation

instance (GoodScalar r, KnownShS sh)
         => Num (AstTensor ms s (TKS sh r)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfList stk (AstConcrete ftk u : lu)
    + AstSumOfList _ (AstConcrete _ v : lv) =
        AstSumOfList stk (AstConcrete ftk (u + v) : lu ++ lv)
  AstSumOfList stk lu + AstSumOfList _ (AstConcrete ftk v : lv) =
    AstSumOfList stk (AstConcrete ftk v : lv ++ lu)
  AstSumOfList stk lu + AstSumOfList _ lv = AstSumOfList stk (lu ++ lv)

  AstConcrete ftk u + AstSumOfList stk (AstConcrete _ v : lv) =
    AstSumOfList stk (AstConcrete ftk (u + v) : lv)
  u + AstSumOfList stk (AstConcrete ftk v : lv) =
    AstSumOfList stk (AstConcrete ftk v : u : lv)
  u + AstSumOfList stk lv = AstSumOfList stk (u : lv)

  AstSumOfList stk (AstConcrete ftk u : lu) + AstConcrete _ v =
    AstSumOfList stk (AstConcrete ftk (u + v) : lu)
  AstSumOfList stk (AstConcrete ftk u : lu) + v =
    AstSumOfList stk (AstConcrete ftk u : v : lu)
  AstSumOfList stk lu + v = AstSumOfList stk (v : lu)

  AstConcrete ftk u + AstConcrete _ v = AstConcrete ftk (u + v)
  u + AstConcrete ftk v = AstSumOfList stensorKind [AstConcrete ftk v, u]
  u + v = AstSumOfList stensorKind [u, v]

  AstConcrete ftk u - AstConcrete _ v =
    AstConcrete ftk (u - v)  -- common in indexing
  u - v = AstN2S MinusOp u v

  AstConcrete ftk u * AstConcrete _ v =
    AstConcrete ftk (u * v)  -- common in indexing
  u * v = AstN2S TimesOp u v

  negate = AstN1S NegateOp
  abs = AstN1S AbsOp
  signum = AstN1S SignumOp
  fromInteger i = error $ "fromInteger not defined for shaped tensors: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, GoodScalar r, KnownShS sh)
         => IntegralF (AstTensor ms s (TKS sh r)) where
  quotF = AstI2S QuotOp
  remF = AstI2S RemOp

instance (GoodScalar r, Differentiable r, KnownShS sh)
         => Fractional (AstTensor ms s (TKS sh r)) where
  u / v = AstR2S DivideOp u v
  recip = AstR1S RecipOp
  fromRational r = error $ "fromRational not defined for shaped tensors: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShS sh, AstSpan s)
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

instance (GoodScalar r, Differentiable r, KnownShS sh, AstSpan s)
         => RealFloatF (AstTensor ms s (TKS sh r)) where
  atan2F = AstR2S Atan2Op


-- mixed

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
instance (Integral r, GoodScalar r)
         => IntegralF (AstTensor ms s (TKX sh r)) where
  quotF = liftXFromS2 quotF
  remF = liftXFromS2 remF

instance (GoodScalar r, Differentiable r)
         => Fractional (AstTensor ms s (TKX sh r)) where
  (/) = liftXFromS2 (/)
  recip = liftXFromS1 recip
  fromRational r = error $ "fromRational not defined for mixed tensors: "
                           ++ show r

instance (GoodScalar r, Differentiable r, AstSpan s)
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

instance (GoodScalar r, Differentiable r, AstSpan s)
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
