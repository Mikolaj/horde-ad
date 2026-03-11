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
  , sunReplicate, sunReplicate1, sunReplicateN, unReplC, unAstK, unAstS
  , eqY, eqUnknownShapes
  ) where

import Prelude

import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed qualified as Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.Ast
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
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

unReplC :: forall sh x s ms.
           AstTensor ms s (TKS2 sh x) -> Maybe (RepConcrete x)
unReplC (AstReplicateK _ a) = unAstK a
unReplC (AstReplicateS _ u) = unReplC u
unReplC (AstLet _ _ t) = unReplC t  -- we may be before inlining
unReplC (AstPrimalPart t) = unReplC t
unReplC (AstDualPart t) = unReplC t
unReplC (AstPlainPart t) = unReplC t
unReplC (AstFromPrimal t) = unReplC t
unReplC (AstFromDual t) = unReplC t
unReplC (AstFromPlain t) = unReplC t
unReplC (AstConcreteS a) = sunReplicate a
unReplC (AstConvert (ConvCmp ConvXS (Conv0X STKScalar)) (AstConcreteK a)) =
  Just a
unReplC _ = Nothing  -- e.g., a variable

-- No cases for, e.g., arithmetic, because it'd get simplified away beforehand.
unAstK :: forall r s ms.
          AstTensor ms s (TKScalar r) -> Maybe r
unAstK (AstLet _ _ t) = unAstK t  -- we may be before inlining
unAstK (AstPrimalPart t) = unAstK t
unAstK (AstDualPart t) = unAstK t
unAstK (AstPlainPart t) = unAstK t
unAstK (AstFromPrimal t) = unAstK t
unAstK (AstFromDual t) = unAstK t
unAstK (AstFromPlain t) = unAstK t
unAstK (AstConcreteK a) = Just a
unAstK (AstConvert (ConvCmp ConvX0 ConvSX) a) = unReplC a
unAstK _ = Nothing

unAstS :: forall sh x s ms.
          AstTensor ms s (TKS2 sh x)
       -> Maybe (Nested.Shaped sh (RepConcrete x))
unAstS (AstReplicateS shm u) | Dict <- eltDictRep (stkAstX u) =
  Nested.sreplicate shm <$> unAstS u
unAstS (AstLet _ _ t) = unAstS t
unAstS (AstPrimalPart t) = unAstS t
unAstS (AstDualPart t) = unAstS t
unAstS (AstPlainPart t) = unAstS t
unAstS (AstFromPrimal t) = unAstS t
unAstS (AstFromDual t) = unAstS t
unAstS (AstFromPlain t) = unAstS t
unAstS (AstConcreteS a) = Just a
unAstS (AstConvert (ConvCmp ConvXS (Conv0X STKScalar)) (AstConcreteK r)) =
  gcastWith (unsafeCoerceRefl :: sh :~: '[]) $
  Just $ Nested.sscalar r
unAstS _ = Nothing

-- | An approximation of equality. `False` doesn't imply terms
-- have different semantics, but `True` implies they have equal semantics.
eqY :: AstTensor ms s y -> AstTensor ms s y -> Bool
eqY t1 t2 = case eqZ t1 t2 of
  Just Refl -> True
  Nothing -> False

-- | An approximation of equality, where `Just Refl` means that
-- the shapes of the terms are equal and the values denoted by them are equal.
eqUnknownShapes :: AstTensor ms s y -> AstTensor ms s z -> Maybe (y :~: z)
eqUnknownShapes = eqZ

-- | An approximation of equality, where `Just Refl` means that
-- the shapes of the terms are equal and if their spans are equal
-- then the values denoted by them are equal.
eqZ :: AstTensor ms s1 y -> AstTensor ms s2 z -> Maybe (y :~: z)
eqZ (AstPair u1 v1) (AstPair u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstProject1 u1) (AstProject1 u2) | Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstProject2 u1) (AstProject2 u2) | Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstVar u1) (AstVar u2)
  | varNameToAstVarId u1 == varNameToAstVarId u2
  , Just Refl <- matchingFTK (varNameToFTK u1) (varNameToFTK u2) = Just Refl
eqZ v1 (AstLet _ _ v2) = eqZ v1 v2
eqZ (AstLet _ _  v1) v2 = eqZ v1 v2
-- We can remove these wrappers from only one side, because if the spans
-- are equal, the values will be, thanks to the careful processing below.
eqZ u1 (AstPrimalPart u2) = eqZ u1 u2
eqZ (AstPrimalPart u1) u2 = eqZ u1 u2
eqZ u1 (AstDualPart u2) = eqZ u1 u2
eqZ (AstDualPart u1) u2 = eqZ u1 u2
eqZ u1 (AstPlainPart u2) = eqZ u1 u2
eqZ (AstPlainPart u1) u2 = eqZ u1 u2
-- We can't remove the following wrappers from only one side,
-- because taking a primal part above may result in a dual-number with zero
-- dual part and if AstFromPrimal would also be applied to only one side,
-- the empty dual part would no longer be reflected in the type (the span).
eqZ (AstFromPrimal u1) (AstFromPrimal u2) = eqZ u1 u2
eqZ (AstFromDual u1) (AstFromDual u2) = eqZ u1 u2
eqZ (AstFromPlain u1) (AstFromPlain u2) = eqZ u1 u2
eqZ (AstPlusK u1 v1) (AstPlusK u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstPlusK u1 v1) (AstPlusK u2 v2)
  | Just Refl <- eqZ u1 v2
  , Just Refl <- eqZ v1 u2 = Just Refl
eqZ (AstTimesK u1 v1) (AstTimesK u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstTimesK u1 v1) (AstTimesK u2 v2)
  | Just Refl <- eqZ u1 v2
  , Just Refl <- eqZ v1 u2 = Just Refl
eqZ (AstN1K opCode1 u1) (AstN1K opCode2 u2) | opCode1 == opCode2 = eqZ u1 u2
eqZ (AstR1K opCode1 u1) (AstR1K opCode2 u2) | opCode1 == opCode2 = eqZ u1 u2
eqZ (AstR2K opCode1 u1 v1) (AstR2K opCode2 u2 v2)
  | opCode1 == opCode2
  , Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstI2K opCode1 u1 v1) (AstI2K opCode2 u2 v2)
  | opCode1 == opCode2
  , Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstConcreteK @r1 u1) (AstConcreteK @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , u1 == u2 = Just Refl
eqZ (AstFloorK @_ @r1 u1) (AstFloorK @_ @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstFromIntegralK @_ @r1 u1) (AstFromIntegralK @_ @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstCastK @_ @r1 u1) (AstCastK @_ @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstPlusS u1 v1) (AstPlusS u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstPlusS u1 v1) (AstPlusS u2 v2)
  | Just Refl <- eqZ u1 v2
  , Just Refl <- eqZ v1 u2 = Just Refl
eqZ (AstTimesS u1 v1) (AstTimesS u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstTimesS u1 v1) (AstTimesS u2 v2)
  | Just Refl <- eqZ u1 v2
  , Just Refl <- eqZ v1 u2 = Just Refl
eqZ (AstN1S opCode1 u1) (AstN1S opCode2 u2) | opCode1 == opCode2 = eqZ u1 u2
eqZ (AstR1S opCode1 u1) (AstR1S opCode2 u2) | opCode1 == opCode2 = eqZ u1 u2
eqZ (AstR2S opCode1 u1 v1) (AstR2S opCode2 u2 v2)
  | opCode1 == opCode2
  , Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstI2S opCode1 u1 v1) (AstI2S opCode2 u2 v2)
  | opCode1 == opCode2
  , Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstFloorS @_ @r1 u1) (AstFloorS @_ @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstFromIntegralS @_ @r1 u1) (AstFromIntegralS @_ @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstCastS @_ @r1 u1) (AstCastS @_ @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstSumK u1) (AstSumK u2)
  | Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstSumS shm1 u1) (AstSumS shm2 u2)
  | Just Refl <- testEquality shm1 shm2
  , Just Refl <- eqZ u1 u2 = Just unsafeCoerceRefl
eqZ (AstReplicateK shm1 u1) (AstReplicateK shm2 u2)
  | Just Refl <- testEquality shm1 shm2
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstReplicateS shm1 u1) (AstReplicateS shm2 u2)
  | Just Refl <- testEquality shm1 shm2
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstIotaS @_ @r1 k1) (AstIotaS @_ @r2 k2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- testEquality k1 k2 = Just Refl
eqZ (AstReverseS u1) (AstReverseS u2) = eqZ u1 u2
eqZ (AstTransposeS perm1 u1) (AstTransposeS perm2 u2)
  | Just Refl <- testEquality perm1 perm2
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstReshapeS sh1 u1) (AstReshapeS sh2 u2)
  | Just Refl <- testEquality sh1 sh2
  , Just Refl <- eqZ u1 u2 = Just Refl
eqZ (AstConvert c1 u1) (AstConvert c2 u2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- testEquality c1 c2 = Just Refl
eqZ (AstBoolNotK u1) (AstBoolNotK u2) = eqZ u1 u2
eqZ (AstBoolNotS u1) (AstBoolNotS u2) = eqZ u1 u2
eqZ (AstBoolAndK u1 v1) (AstBoolAndK u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstBoolAndK u1 v1) (AstBoolAndK u2 v2)
  | Just Refl <- eqZ u1 v2
  , Just Refl <- eqZ v1 u2 = Just Refl
eqZ (AstBoolAndS u1 v1) (AstBoolAndS u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstBoolAndS u1 v1) (AstBoolAndS u2 v2)
  | Just Refl <- eqZ u1 v2
  , Just Refl <- eqZ v1 u2 = Just Refl
eqZ (AstLeqK u1 v1) (AstLeqK u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ (AstLeq u1 v1) (AstLeq u2 v2)
  | Just Refl <- eqZ u1 u2
  , Just Refl <- eqZ v1 v2 = Just Refl
eqZ _ _ = Nothing
