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
         => Num (AstTensor ms s (TKR r n)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfList (AstConcrete u : lu) + AstSumOfList (AstConcrete v : lv) =
    AstSumOfList (AstConcrete (u + v) : lu ++ lv)
  AstSumOfList lu + AstSumOfList (AstConcrete v : lv) =
    AstSumOfList (AstConcrete v : lv ++ lu)
  AstSumOfList lu + AstSumOfList lv = AstSumOfList (lu ++ lv)

  AstConcrete u + AstSumOfList (AstConcrete v : lv) =
    AstSumOfList (AstConcrete (u + v) : lv)
  u + AstSumOfList (AstConcrete v : lv) = AstSumOfList (AstConcrete v : u : lv)
  u + AstSumOfList lv = AstSumOfList (u : lv)

  AstSumOfList (AstConcrete u : lu) + AstConcrete v =
    AstSumOfList (AstConcrete (u + v) : lu)
  AstSumOfList (AstConcrete u : lu) + v = AstSumOfList (AstConcrete u : v : lu)
  AstSumOfList lu + v = AstSumOfList (v : lu)

  AstConcrete u + AstConcrete v = AstConcrete (u + v)
  u + AstConcrete v = AstSumOfList [AstConcrete v, u]
  u + v = AstSumOfList [u, v]

  AstConcrete u - AstConcrete v = AstConcrete (u - v)  -- common in indexing
  u - v = AstN2 MinusOp u v

  AstConcrete u * AstConcrete v = AstConcrete (u * v)  -- common in indexing
  u * v = AstN2 TimesOp u v

  negate (AstConcrete u) = AstConcrete $ negate u  -- common in indexing
  negate u = AstN1 NegateOp u
  abs = AstN1 AbsOp
  signum = AstN1 SignumOp
  fromInteger i = error $ "fromInteger not defined for ranked tensors: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (GoodScalar r, Integral r, KnownNat n)
         => IntegralF (AstTensor ms s (TKR r n)) where
  quotF = AstI2 QuotOp
  remF = AstI2 RemOp

instance (GoodScalar r, Differentiable r, Fractional (Nested.Ranked n r), KnownNat n)
         => Fractional (AstTensor ms s (TKR r n)) where
  u / v = AstR2 DivideOp u v
  recip = AstR1 RecipOp
  fromRational r = error $ "fromRational not defined for AST: "
                           ++ show r

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Floating (AstTensor ms s (TKR r n)) where
  pi = fromPrimal $ AstConcrete pi
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

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => RealFloatF (AstTensor ms s (TKR r n)) where
  atan2F = AstR2 Atan2Op


-- * Unlawful numeric instances of shaped AST; they are lawful modulo evaluation

instance (GoodScalar r, Num (Nested.Shaped sh r), KnownShS sh, AstSpan s)
         => Num (AstTensor ms s (TKS r sh)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfListS (AstConcreteS u : lu) + AstSumOfListS (AstConcreteS v : lv) =
    AstSumOfListS (AstConcreteS (u + v) : lu ++ lv)
  AstSumOfListS lu + AstSumOfListS (AstConcreteS v : lv) =
    AstSumOfListS (AstConcreteS v : lv ++ lu)
  AstSumOfListS lu + AstSumOfListS lv = AstSumOfListS (lu ++ lv)

  AstConcreteS u + AstSumOfListS (AstConcreteS v : lv) =
    AstSumOfListS (AstConcreteS (u + v) : lv)
  u + AstSumOfListS (AstConcreteS v : lv) = AstSumOfListS (AstConcreteS v : u : lv)
  u + AstSumOfListS lv = AstSumOfListS (u : lv)

  AstSumOfListS (AstConcreteS u : lu) + AstConcreteS v =
    AstSumOfListS (AstConcreteS (u + v) : lu)
  AstSumOfListS (AstConcreteS u : lu) + v = AstSumOfListS (AstConcreteS u : v : lu)
  AstSumOfListS lu + v = AstSumOfListS (v : lu)

  AstConcreteS u + AstConcreteS v = AstConcreteS (u + v)
  u + AstConcreteS v = AstSumOfListS [AstConcreteS v, u]
  u + v = AstSumOfListS [u, v]

  AstConcreteS u - AstConcreteS v = AstConcreteS (u - v)  -- common in indexing
  u - v = AstN2S MinusOp u v

  AstConcreteS u * AstConcreteS v = AstConcreteS (u * v)  -- common in indexing
  u * v = AstN2S TimesOp u v

  negate = AstN1S NegateOp
  abs = AstN1S AbsOp
  signum = AstN1S SignumOp
  fromInteger :: Integer -> AstTensor ms s (TKS r sh)
  fromInteger i = case sameShape @sh @'[] of
    Just Refl -> fromPrimal . AstConcreteS . fromInteger $ i
    Nothing -> error $ "fromInteger not defined for tensors of non-empty shapes: "
                       ++ show (i, knownShS @sh)
    -- it's crucial that there is no AstFromPrimal in fromInteger code
    -- so that we don't need 4 times the simplification rules

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, GoodScalar r, KnownShS sh)
         => IntegralF (AstTensor ms s (TKS r sh)) where
  quotF = AstI2S QuotOp
  remF = AstI2S RemOp

instance ( GoodScalar r, Differentiable r, Fractional (Nested.Shaped sh r)
         , KnownShS sh, AstSpan s )
         => Fractional (AstTensor ms s (TKS r sh)) where
  u / v = AstR2S DivideOp u v
  recip = AstR1S RecipOp
  fromRational r = error $ "fromRational not defined for AST: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShS sh, Floating (Nested.Shaped sh r), AstSpan s)
         => Floating (AstTensor ms s (TKS r sh)) where
  pi = fromPrimal $ AstConcreteS pi
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
         => RealFloatF (AstTensor ms s (TKS r sh)) where
  atan2F = AstR2S Atan2Op


-- mixed

instance (GoodScalar r, Num (Nested.Mixed sh r), KnownShX sh)
         => Num (AstTensor ms s (TKX r sh)) where
  -- The normal form has AstConcrete, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfListX (AstConcreteX u : lu) + AstSumOfListX (AstConcreteX v : lv) =
    AstSumOfListX (AstConcreteX (u + v) : lu ++ lv)
  AstSumOfListX lu + AstSumOfListX (AstConcreteX v : lv) =
    AstSumOfListX (AstConcreteX v : lv ++ lu)
  AstSumOfListX lu + AstSumOfListX lv = AstSumOfListX (lu ++ lv)

  AstConcreteX u + AstSumOfListX (AstConcreteX v : lv) =
    AstSumOfListX (AstConcreteX (u + v) : lv)
  u + AstSumOfListX (AstConcreteX v : lv) = AstSumOfListX (AstConcreteX v : u : lv)
  u + AstSumOfListX lv = AstSumOfListX (u : lv)

  AstSumOfListX (AstConcreteX u : lu) + AstConcreteX v =
    AstSumOfListX (AstConcreteX (u + v) : lu)
  AstSumOfListX (AstConcreteX u : lu) + v = AstSumOfListX (AstConcreteX u : v : lu)
  AstSumOfListX lu + v = AstSumOfListX (v : lu)

  AstConcreteX u + AstConcreteX v = AstConcreteX (u + v)
  u + AstConcreteX v = AstSumOfListX [AstConcreteX v, u]
  u + v = AstSumOfListX [u, v]

  AstConcreteX u - AstConcreteX v = AstConcreteX (u - v)  -- common in indexing
  u - v = AstN2X MinusOp u v

  AstConcreteX u * AstConcreteX v = AstConcreteX (u * v)  -- common in indexing
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
         => IntegralF (AstTensor ms s (TKX r sh)) where
  quotF = AstI2X QuotOp
  remF = AstI2X RemOp

instance ( GoodScalar r, Differentiable r, Fractional (Nested.Mixed sh r)
         , KnownShX sh )
         => Fractional (AstTensor ms s (TKX r sh)) where
  u / v = AstR2X DivideOp u v
  recip = AstR1X RecipOp
  fromRational r = error $ "fromRational not defined for AST: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShX sh, Floating (Nested.Mixed sh r), AstSpan s)
         => Floating (AstTensor ms s (TKX r sh)) where
  pi = fromPrimal $ AstConcreteX pi
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
         => RealFloatF (AstTensor ms s (TKX r sh)) where
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
