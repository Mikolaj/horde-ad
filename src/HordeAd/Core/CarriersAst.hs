{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
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
  , sunReplicate, sunReplicate1, sunReplicateN, unReplS, unReplK, eqK
  ) where

import Prelude

import Data.Type.Equality (testEquality, (:~:) (Refl))
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed qualified as Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
import HordeAd.Core.Conversion
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Type family instances for AstTensor

-- This can't be just HFun, because they need to be vectorized
-- and vectorization applies such functions to the variable from build1
-- and the variable has to be eliminated via vectorization to preserve
-- the closed form of the function. Just applying a Haskell closure
-- to the build1 variable and then duplicating the result of the function
-- would not eliminate the variable and also would likely results
-- in more costly computations. Also, that would prevent simplification
-- of the instances, especially after applied to arguments that are terms.
type instance HFunOf (AstTensor AstMethodLet s) = AstHFun s

-- This can't be defined only for FullSpan, because the BaseTensor instance
-- for @AstTensor ms PrimalSpan@ needs it and we need the instance
-- to satisfy ADReady constraints for AST.
type instance PrimalOf (AstTensor ms s) = AstTensor ms (PrimalStepSpan s)
type instance DualOf (AstTensor ms s) = AstTensor ms DualSpan
type instance PlainOf (AstTensor ms s) = AstTensor ms PlainSpan
type instance ShareOf (AstTensor ms s) = AstRaw s

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstTensor ms s y) where
  (==) = error "Eq is not defined for AST; please use EqH instead"
  (/=) = error "Eq is not defined for AST; please use EqH instead"

instance Ord (AstTensor ms s y) where
  (<=) = error "Ord is not defined for AST; please use OrdH instead"


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

type instance PrimalOf (AstRaw s) = AstRaw (PrimalStepSpan s)
type instance DualOf (AstRaw s) = AstTensor AstMethodShare DualSpan
type instance PlainOf (AstRaw s) = AstRaw PlainSpan
type instance ShareOf (AstRaw s) = AstRaw s
type instance HFunOf (AstRaw s) = AstHFun s

type instance PrimalOf (AstNoVectorize s) = AstNoVectorize (PrimalStepSpan s)
type instance DualOf (AstNoVectorize s) = AstTensor AstMethodLet DualSpan
type instance PlainOf (AstNoVectorize s) = AstNoVectorize PlainSpan
type instance ShareOf (AstNoVectorize s) = AstRaw s
type instance HFunOf (AstNoVectorize s) = AstHFun s

type instance PrimalOf (AstNoSimplify s) = AstNoSimplify (PrimalStepSpan s)
type instance DualOf (AstNoSimplify s) = AstTensor AstMethodLet DualSpan
type instance PlainOf (AstNoSimplify s) = AstNoSimplify PlainSpan
type instance ShareOf (AstNoSimplify s) = AstRaw s
type instance HFunOf (AstNoSimplify s) = AstHFun s


-- * Helper functions

sunReplicate :: Nested.Elt a
             => Nested.Shaped sh a -> Maybe a
{-# INLINE sunReplicate #-}
sunReplicate (Nested.Shaped arr)
  | all (all (== 0) . take (shxLength (Nested.mshape arr)))
        (Mixed.marrayStrides arr)
  , shxSize (Nested.mshape arr) /= 0 =
    Just $ Nested.mindex arr $ ixxZero' $ Nested.mshape arr
sunReplicate arr | ZSS <- Nested.sshape arr = Just $ Nested.sunScalar arr
sunReplicate _ = Nothing

sunReplicate1 :: Nested.Elt a
              => Nested.Shaped (n ': sh) a -> Maybe (Nested.Shaped sh a)
{-# INLINE sunReplicate1 #-}
sunReplicate1 a | (snat :$$ _) <- Nested.sshape a =
  sunReplicateN (snat :$$ ZSS) a

sunReplicateN :: Nested.Elt a
              => ShS shm -> Nested.Shaped (shm ++ shn) a
              -> Maybe (Nested.Shaped shn a)
{-# INLINE sunReplicateN #-}
sunReplicateN shm a@(Nested.Shaped arr)
  | all (all (== 0) . take (shsLength shm)) (Mixed.marrayStrides arr)
  , shsSize shm /= 0 =
    Just $ Nested.sindexPartial a $ ixsZero shm
sunReplicateN _ _ = Nothing

unReplS :: forall sh r s ms.
           AstTensor ms s (TKS sh r) -> Maybe r
unReplS (AstReplicate _ STKScalar a) = unReplK a
unReplS (AstReplicate _ STKS{} u) = unReplS u
unReplS (AstLet _ _ t) = unReplS t  -- we may be before inlining
unReplS (AstPrimalPart t) = unReplS t
unReplS (AstDualPart t) = unReplS t
unReplS (AstPlainPart t) = unReplS t
unReplS (AstFromPrimal t) = unReplS t
unReplS (AstFromDual t) = unReplS t
unReplS (AstFromPlain t) = unReplS t
unReplS (AstConcreteS a) = sunReplicate a
unReplS (AstConvert (ConvCmp ConvXS (Conv0X STKScalar)) (AstConcreteK a)) =
  Just a
unReplS _ = Nothing  -- e.g., a variable

-- No cases for, e.g., arithmetic, because it'd get simplified away beforehand.
unReplK :: forall r s ms.
           AstTensor ms s (TKScalar r) -> Maybe r
unReplK (AstLet _ _ t) = unReplK t  -- we may be before inlining
unReplK (AstPrimalPart t) = unReplK t
unReplK (AstDualPart t) = unReplK t
unReplK (AstPlainPart t) = unReplK t
unReplK (AstFromPrimal t) = unReplK t
unReplK (AstFromDual t) = unReplK t
unReplK (AstFromPlain t) = unReplK t
unReplK (AstConcreteK a) = Just a
unReplK (AstConvert (ConvCmp ConvX0 ConvSX) a) = unReplS a
unReplK _ = Nothing

-- An approximation. False doesn't imply terms have different semantics,
-- but True implies they have equal semantics.
eqK :: AstTensor ms s (TKScalar r) -> AstTensor ms s (TKScalar r) -> Bool
-- This is wrong for <=. but correct for this approximation:
eqK (AstVar var1) (AstVar var2) = var1 == var2
eqK (AstLet _ _  v1) (AstLet _ _ v2) = eqK v1 v2
eqK v1 (AstLet _ _ v2) = eqK v1 v2
eqK (AstLet _ _  v1) v2 = eqK v1 v2
eqK (AstPrimalPart u1) (AstPrimalPart u2) = eqK u1 u2
eqK (AstPlainPart @_ @s1 u1) (AstPlainPart @_ @s2 u2)
  | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
    eqK u1 u2
eqK (AstFromPrimal u1) (AstFromPrimal u2) = eqK u1 u2
eqK AstFromDual{} AstFromDual{} = True
eqK (AstFromPlain u1) (AstFromPlain u2) = eqK u1 u2
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
eqK (AstConvert _ (AstVar u)) (AstConvert _ (AstVar v)) =
  varNameToAstVarId u == varNameToAstVarId v
eqK (AstBoolNotK u1) (AstBoolNotK u2) = eqK u1 u2
eqK (AstBoolAndK u1 v1) (AstBoolAndK u2 v2) =
  eqK u1 u2 && eqK v1 v2 || eqK u1 v2 && eqK v1 u2
eqK _ _ = False
