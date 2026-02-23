{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
-- | This module implements a few complete bottom-up simplifying passes
-- over any AST expression.
module HordeAd.Core.AstTraverse
  ( -- * The expansion (e.g., into gather expressions) bottom-up pass
    expandAst
    -- * The simplifying bottom-up pass
  , simplifyAst
    -- * The contraction (e.g., from gather expressions) bottom-up pass
  , contractAst
    -- * The let down (reducing the scope of lets cheaply) bottom-up pass
  , letDownAst
  ) where

import Prelude

import Data.Foldable qualified as Foldable
import Data.Int (Int16, Int32, Int64, Int8)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Foreign.C (CInt)
import Foreign.Storable (sizeOf)
import GHC.TypeLits (KnownNat)
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation (Perm (..))
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Shaped qualified as Shaped
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (fromSNat', unsafeCoerceRefl)

import HordeAd.Core.Ast
  ( AstTensor (AstConcreteK, AstConcreteS, AstPlusK, AstPlusS, AstTimesK, AstTimesS)
  )
import HordeAd.Core.Ast hiding (AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Conversion
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The expansion (e.g., into gather expressions) bottom-up pass

expandAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
expandAstIxS = fmap expandAst

-- | This pass expands terms, e.g., into @AstGather@ terms, in order
-- to expose redexes and enable fusion. It assumes that a contraction
-- pass follows that undoes some of the remaining expansion and applies
-- fusion rules that would be immediately counteracted by expansion rules
-- if applied earlier.
expandAst
  :: forall s y. KnownSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
expandAst t = case t of
  Ast.AstPair t1 t2 -> astPair (expandAst t1) (expandAst t2)
  Ast.AstProject1 v -> astProject1 (expandAst v)
  Ast.AstProject2 v -> astProject2 (expandAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map expandAst l)
  Ast.AstSum snat stk v -> astSum snat stk (expandAst v)
  Ast.AstReplicate snat stk v -> astReplicate snat stk (expandAst v)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (expandAstHFun f)
                    (expandAstHFun df)
                    (expandAstHFun rf)
                    (expandAst acc0)
                    (expandAst es)
  Ast.AstApply v ll -> astApply (expandAstHFun v) (expandAst ll)
  Ast.AstVar{} -> t
  Ast.AstCond b a2 a3 -> astCond (expandAst b) (expandAst a2) (expandAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = expandAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v ->
    astLetDown var (withKnownSpan (varNameToSpan var) $ expandAst u)
                   (expandAst v)

  Ast.AstPrimalPart v -> astPrimalPart (expandAst v)
  Ast.AstDualPart v -> astDualPart (expandAst v)
  Ast.AstPlainPart v -> astPlainPart (expandAst v)
  Ast.AstFromPrimal v -> fromPrimal (expandAst v)
  Ast.AstFromDual v -> fromDual (expandAst v)
  Ast.AstFromPlain v -> fromPlain (expandAst v)

  AstPlusK u v -> expandAst u + expandAst v
  AstTimesK u v -> expandAst u * expandAst v
  Ast.AstN1K opCode u -> astN1K opCode (expandAst u)
  Ast.AstR1K opCode u -> astR1K opCode (expandAst u)
  Ast.AstR2K opCode u v -> astR2K opCode (expandAst u) (expandAst v)
  Ast.AstI2K opCode u v -> astI2K opCode (expandAst u) (expandAst v)
  AstConcreteK{} -> t
  Ast.AstFloorK a -> astFloorK (expandAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ expandAst v
  Ast.AstCastK v -> astCastK $ expandAst v
  Ast.AstArgMinK v -> astArgMinK $ expandAst v
  Ast.AstArgMaxK v -> astArgMaxK $ expandAst v
  Ast.AstIndexK @shm v ix | Refl <- lemAppNil @shm ->
    kfromS
    $ astIndexKnobsS (defaultKnobs {knobPhase = PhaseExpansion})
                     ZSS (expandAst v) (expandAstIxS ix)

  AstPlusS u v -> expandAst u + expandAst v
  AstTimesS u v -> expandAst u * expandAst v
  Ast.AstN1S opCode u -> astN1S opCode (expandAst u)
  Ast.AstR1S opCode u -> astR1S opCode (expandAst u)
  Ast.AstR2S opCode u v -> astR2S opCode (expandAst u) (expandAst v)
  Ast.AstI2S opCode u v -> astI2S opCode (expandAst u) (expandAst v)
  AstConcreteS{} -> t
  Ast.AstFloorS a -> astFloorS (expandAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ expandAst v
  Ast.AstCastS v -> astCastS $ expandAst v
  Ast.AstArgMinS a -> Ast.AstArgMinS (expandAst a)
  Ast.AstArgMaxS a -> Ast.AstArgMaxS (expandAst a)
  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseExpansion})
                   shn (expandAst v) (expandAstIxS ix)

  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (expandAst v) (vars, expandAstIxS ix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherKnobsS (defaultKnobs {knobPhase = PhaseExpansion})
                    shm shn shp (expandAst v) (vars, expandAstIxS ix)
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> astAppendS (expandAst x) (expandAst y)
  Ast.AstSliceS i n k v -> astSliceS i n k (expandAst v)
  Ast.AstReverseS v -> astReverseS (expandAst v)
  Ast.AstTransposeS perm v -> {-
   -- disabled until we can reliably fuse back to transpose
   case expandAst v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstFromDual Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1{} -> t  -- normal form
    Ast.AstProject2{} -> t  -- normal form
    Ast.AstFromIntegralS{} -> t  -- normal form
    Ast.AstCastS{} -> t  -- normal form
    Ast.AstReplicate{} -> t  -- normal form
      -- TODO: this nf is silly, but right now transposes of replicates
      -- are small arrays and equivalent gathers are large terms and arrays,
      -- so this has to stay. Maybe we should contract gathers back
      -- to transposes of replicates (not only to replicates). Or maybe
      -- we should extend orthotope to any gather schemes, not only
      -- the simple ones.
      -- TODO: review also other nfs here and for AstReshapeS below
    Ast.AstScatterS _ _ (_, ix)
     | gcompare (Permutation.permRank perm) (ixsRank ix) == GGT -> t  -- nf
    v2 ->  -- not nf, let's express all as a gather
      astTransposeAsGatherS (defaultKnobs {knobExpand = True})
                            perm v2  -- TODO: (normalizePermutation perm)
        -- this is expensive but the only way to guarantee full simplification
    -} astTransposeS perm (expandAst v)
  Ast.AstReshapeS sh v -> {-  -- too hard to fuse back to reshape
   case expandAst v of
    Ast.AstVar{} -> t  -- normal form
    Ast.AstPrimalPart Ast.AstVar{} -> t  -- normal form
    Ast.AstDualPart Ast.AstVar{} -> t  -- normal form
    Ast.AstFromPrimal Ast.AstVar{} -> t  -- normal form
    Ast.AstFromDual Ast.AstVar{} -> t  -- normal form
    Ast.AstProject1{} -> t  -- normal form
    Ast.AstProject2{} -> t  -- normal form
    Ast.AstFromIntegralS{} -> t  -- normal form
    Ast.AstCastS{} -> t  -- normal form
    AstPlusS{} -> t  -- normal form
    AstTimesS{} -> t  -- normal form
    Ast.AstR2S{} -> t  -- normal form
    Ast.AstScatterS{} -> t  -- normal form
    v2 ->  -- not nf, let's express all as a gather
      astReshapeAsGatherS (defaultKnobs {knobExpand = True})
                          sh v2
        -- this is expensive but the only way to guarantee full simplification
    -} astReshapeS sh (expandAst v)

  Ast.AstConvert c v -> astConvert c $ expandAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstSum0{} -> t
  Ast.AstDot0{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatmul2S{} -> t

  Ast.AstBoolNotK arg -> notB $ expandAst arg
  Ast.AstBoolNotS arg -> astBoolNotS $ expandAst arg
  Ast.AstBoolAndK arg1 arg2 -> expandAst arg1 &&* expandAst arg2
  Ast.AstBoolAndS arg1 arg2 -> astBoolAndS (expandAst arg1) (expandAst arg2)
  Ast.AstLeqK arg1 arg2 -> fromPlain $ expandAst arg1 <=. expandAst arg2
  Ast.AstLeq arg1 arg2 -> fromPlain $ expandAst arg1 <=. expandAst arg2
  Ast.AstLeqS shb sh arg1 arg2 ->
    fromPlain $ astLeqS shb sh (expandAst arg1) (expandAst arg2)

expandAstHFun :: KnownSpan s
              => AstHFun s x y -> AstHFun s x y
expandAstHFun (AstLambda var l) = AstLambda var (expandAst l)


-- * The simplifying bottom-up pass

simplifyAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
simplifyAstIxS = fmap simplifyAst

-- | This function guarantees full simplification (unless redexes are obscured,
-- for which the expansion pass is sometimes a remedy): every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexR.
simplifyAst
  :: forall s y. KnownSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
simplifyAst t = case t of
  Ast.AstPair t1 t2 -> astPair (simplifyAst t1) (simplifyAst t2)
  Ast.AstProject1 v -> astProject1 (simplifyAst v)
  Ast.AstProject2 v -> astProject2 (simplifyAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map simplifyAst l)
  Ast.AstSum snat stk v -> astSum snat stk (simplifyAst v)
  Ast.AstReplicate snat stk v -> astReplicate snat stk (simplifyAst v)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (simplifyAstHFun f)
                    (simplifyAstHFun df)
                    (simplifyAstHFun rf)
                    (simplifyAst acc0)
                    (simplifyAst es)
  Ast.AstApply f a -> astApply (simplifyAstHFun f) (simplifyAst a)
  Ast.AstVar{} -> t
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAst b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = simplifyAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v ->
    astLet var (withKnownSpan (varNameToSpan var) $ simplifyAst u)
               (simplifyAst v)

  Ast.AstPrimalPart v -> astPrimalPart (simplifyAst v)
  Ast.AstDualPart v -> astDualPart (simplifyAst v)
  Ast.AstPlainPart v -> astPlainPart (simplifyAst v)
  Ast.AstFromPrimal v -> fromPrimal (simplifyAst v)
  Ast.AstFromDual v -> fromDual (simplifyAst v)
  Ast.AstFromPlain v -> fromPlain (simplifyAst v)

  AstPlusK u v -> simplifyAst u + simplifyAst v
  AstTimesK u v -> simplifyAst u * simplifyAst v
  Ast.AstN1K opCode u -> astN1K opCode (simplifyAst u)
  Ast.AstR1K opCode u -> astR1K opCode (simplifyAst u)
  Ast.AstR2K opCode u v -> astR2K opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2K opCode u v -> astI2K opCode (simplifyAst u) (simplifyAst v)
  AstConcreteK{} -> t
  Ast.AstFloorK a -> astFloorK (simplifyAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ simplifyAst v
  Ast.AstCastK v -> astCastK $ simplifyAst v
  Ast.AstArgMinK v -> astArgMinK $ simplifyAst v
  Ast.AstArgMaxK v -> astArgMaxK $ simplifyAst v
  Ast.AstIndexK @shm v ix | Refl <- lemAppNil @shm ->
    kfromS
    $ astIndexKnobsS (defaultKnobs {knobPhase = PhaseSimplification})
                     ZSS (simplifyAst v) (simplifyAstIxS ix)

  AstPlusS u v -> simplifyAst u + simplifyAst v
  AstTimesS u v -> simplifyAst u * simplifyAst v
  Ast.AstN1S opCode u -> astN1S opCode (simplifyAst u)
  Ast.AstR1S opCode u -> astR1S opCode (simplifyAst u)
  Ast.AstR2S opCode u v -> astR2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2S opCode u v -> astI2S opCode (simplifyAst u) (simplifyAst v)
  AstConcreteS{} -> t
  Ast.AstFloorS a -> astFloorS (simplifyAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ simplifyAst v
  Ast.AstCastS v -> astCastS $ simplifyAst v
  Ast.AstArgMinS a -> Ast.AstArgMinS (simplifyAst a)
  Ast.AstArgMaxS a -> Ast.AstArgMaxS (simplifyAst a)
  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseSimplification})
                   shn (simplifyAst v) (simplifyAstIxS ix)

  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherKnobsS (defaultKnobs {knobPhase = PhaseSimplification})
                    shm shn shp (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> astAppendS (simplifyAst x) (simplifyAst y)
  Ast.AstSliceS i n k v -> astSliceS i n k (simplifyAst v)
  Ast.AstReverseS v -> astReverseS (simplifyAst v)
  Ast.AstTransposeS perm v -> astTransposeS perm $ simplifyAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS sh v -> astReshapeS sh $ simplifyAst v

  Ast.AstConvert c v -> astConvert c $ simplifyAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstSum0{} -> t
  Ast.AstDot0{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatmul2S{} -> t

  Ast.AstBoolNotK arg -> notB $ simplifyAst arg
  Ast.AstBoolNotS arg -> astBoolNotS $ simplifyAst arg
  Ast.AstBoolAndK arg1 arg2 -> simplifyAst arg1 &&* simplifyAst arg2
  Ast.AstBoolAndS arg1 arg2 -> astBoolAndS (simplifyAst arg1) (simplifyAst arg2)
  Ast.AstLeqK arg1 arg2 -> fromPlain $ simplifyAst arg1 <=. simplifyAst arg2
  Ast.AstLeq arg1 arg2 -> fromPlain $ simplifyAst arg1 <=. simplifyAst arg2
  Ast.AstLeqS shb sh arg1 arg2 ->
    fromPlain $ astLeqS shb sh (simplifyAst arg1) (simplifyAst arg2)

simplifyAstHFun :: KnownSpan s
                => AstHFun s x y -> AstHFun s x y
simplifyAstHFun (AstLambda var l) = AstLambda var (simplifyAst l)


-- * The contraction (e.g., from gather expressions) bottom-up pass

contractAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
contractAstIxS = fmap contractAst

-- | When we have multiple backends, there should be one such pass
-- per backend that chooses a representation that is best for the backend.
-- The interpreter would interpret all of the backend-specific term
-- constructors, but the simplifier would ignore all and the user API
-- would not make them available.
--
-- Note that unlike all the other code in this module, this function
-- is not written in a compositional style nor close to it,
-- but it's instead defined in an ad-hoc way based on benchmarks.
contractAst
  :: forall s y. KnownSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
contractAst t0 = case t0 of
  Ast.AstPair t1 t2 -> astPair (contractAst t1) (contractAst t2)
  Ast.AstProject1 v -> astProject1 (contractAst v)
  Ast.AstProject2 v -> astProject2 (contractAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map contractAst l)
  Ast.AstSum _ (STKScalar @r) t2 | Dict0 <- numFromTKAllNum (Proxy @r) ->
    astSum0 (contractAst t2)
  Ast.AstSum
    snat@(SNat @m2)
    stk@(STKS (SNat @n2 :$$ SNat @p2 :$$ ZSS) STKScalar)
    v@(AstTimesS (Ast.AstTransposeS @permt permt
                    (Ast.AstReplicate (SNat @kt) (STKS @sht _ _) t2))
                 (Ast.AstTransposeS @permu permu
                    (Ast.AstReplicate (SNat @ku) (STKS @shu _ _) u2))) ->
    let perm10 = Permutation.makePerm @'[1, 0]
    in fromMaybe (astSum snat stk (contractAst v))
       $ case (permt, permu) of
      ( SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permt (kt ': sht)
                      :~: [m2, n2, p2]) $
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permu (ku ': shu)
                      :~: [m2, n2, p2]) $
        -- Sadly, the casts below, though implied by the permutations
        -- (as redundantly spelled out by the casts above) are required
        -- to make it type-check and they easily mask bugs, too.
        -- In the result, this is as type-unsafe as ranked code would be.
        gcastWith (unsafeCoerceRefl :: sht :~: [n2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, p2]) $
        attemptMatmul2 t2 u2
      ( SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, p2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [n2, m2]) $
        attemptMatmul2 u2 t2
      ( SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [n2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [p2, m2]) $
        attemptMatmul2 t2 (astTransposeS perm10 u2)
      ( SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [p2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [n2, m2]) $
        attemptMatmul2 u2 (astTransposeS perm10 t2)
      ( SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, n2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, p2]) $
        attemptMatmul2 (astTransposeS perm10 t2) u2
      ( SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, p2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, n2]) $
        attemptMatmul2 (astTransposeS perm10 u2) t2
      ( SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, n2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [p2, m2]) $
        attemptMatmul2 (astTransposeS perm10 t2)
                       (astTransposeS perm10 u2)
      ( SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [p2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, n2]) $
        attemptMatmul2 (astTransposeS perm10 u2)
                       (astTransposeS perm10 t2)
      _ -> Nothing
  Ast.AstSum
    snat@(SNat @m2)
    stk@(STKS (SNat @n2 :$$ SNat @p2 :$$ ZSS) STKScalar)
    v@(AstTimesS (Ast.AstFromPlain
                    (Ast.AstTransposeS @permt permt
                      (Ast.AstReplicate (SNat @kt) (STKS @sht _ _) t2')))
                 (Ast.AstTransposeS @permu permu
                    (Ast.AstReplicate (SNat @ku) (STKS @shu _ _) u2))) ->
    let perm10 = Permutation.makePerm @'[1, 0]
        t2 = fromPlain @s t2'
    in fromMaybe (astSum snat stk (contractAst v))
       $ case (permt, permu) of
      ( SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permt (kt ': sht)
                      :~: [m2, n2, p2]) $
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permu (ku ': shu)
                      :~: [m2, n2, p2]) $
        -- Sadly, the casts below, though implied by the permutations
        -- (as redundantly spelled out by the casts above) are required
        -- to make it type-check and they easily mask bugs, too.
        -- In the result, this is as type-unsafe as ranked code would be.
        gcastWith (unsafeCoerceRefl :: sht :~: [n2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, p2]) $
        attemptMatmul2 t2 u2
      ( SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, p2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [n2, m2]) $
        attemptMatmul2 u2 t2
      ( SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [n2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [p2, m2]) $
        attemptMatmul2 t2 (astTransposeS perm10 u2)
      ( SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [p2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [n2, m2]) $
        attemptMatmul2 u2 (astTransposeS perm10 t2)
      ( SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, n2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, p2]) $
        attemptMatmul2 (astTransposeS perm10 t2) u2
      ( SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, p2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, n2]) $
        attemptMatmul2 (astTransposeS perm10 u2) t2
      ( SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, n2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [p2, m2]) $
        attemptMatmul2 (astTransposeS perm10 t2)
                       (astTransposeS perm10 u2)
      ( SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [p2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, n2]) $
        attemptMatmul2 (astTransposeS perm10 u2)
                       (astTransposeS perm10 t2)
      _ -> Nothing
  Ast.AstSum
    snat@(SNat @m2)
    stk@(STKS (SNat @n2 :$$ SNat @p2 :$$ ZSS) STKScalar)
    v@(AstTimesS (Ast.AstTransposeS @permt permt
                    (Ast.AstReplicate (SNat @kt) (STKS @sht _ _) t2))
                 (Ast.AstFromPlain
                    (Ast.AstTransposeS @permu permu
                      (Ast.AstReplicate (SNat @ku) (STKS @shu _ _) u2')))) ->
    let perm10 = Permutation.makePerm @'[1, 0]
        u2 = fromPlain @s u2'
    in fromMaybe (astSum snat stk (contractAst v))
       $ case (permt, permu) of
      ( SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permt (kt ': sht)
                      :~: [m2, n2, p2]) $
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permu (ku ': shu)
                      :~: [m2, n2, p2]) $
        -- Sadly, the casts below, though implied by the permutations
        -- (as redundantly spelled out by the casts above) are required
        -- to make it type-check and they easily mask bugs, too.
        -- In the result, this is as type-unsafe as ranked code would be.
        gcastWith (unsafeCoerceRefl :: sht :~: [n2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, p2]) $
        attemptMatmul2 t2 u2
      ( SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, p2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [n2, m2]) $
        attemptMatmul2 u2 t2
      ( SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [n2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [p2, m2]) $
        attemptMatmul2 t2 (astTransposeS perm10 u2)
      ( SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [p2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [n2, m2]) $
        attemptMatmul2 u2 (astTransposeS perm10 t2)
      ( SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, n2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, p2]) $
        attemptMatmul2 (astTransposeS perm10 t2) u2
      ( SNat' @1 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, p2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, n2]) $
        attemptMatmul2 (astTransposeS perm10 u2) t2
      ( SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil
       ,SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [m2, n2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [p2, m2]) $
        attemptMatmul2 (astTransposeS perm10 t2)
                       (astTransposeS perm10 u2)
      ( SNat' @2 `PCons` SNat' @0 `PCons` SNat' @1 `PCons` PNil
       ,SNat' @1 `PCons` SNat' @2 `PCons` SNat' @0 `PCons` PNil ) ->
        gcastWith (unsafeCoerceRefl :: sht :~: [p2, m2]) $
        gcastWith (unsafeCoerceRefl :: shu :~: [m2, n2]) $
        attemptMatmul2 (astTransposeS perm10 u2)
                       (astTransposeS perm10 t2)
      _ -> Nothing
  Ast.AstSum n@(SNat @n) (STKS @sh sh _) (AstTimesS t2 u) ->
    let cpermR = backpermCycle $ 1 + shsLength sh
    in Permutation.permFromListCont cpermR $ \(cperm
                                               :: Permutation.Perm cperm) ->
         gcastWith (unsafeCoerceRefl :: Rank cperm :~: Rank (n : sh)) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix cperm (n : sh)
                       :~: sh ++ '[n]) $
         fromMaybe (error "contractAst: impossible non-permutation")
         $ Permutation.permCheckPermutation cperm
         $ astDot1InS sh n (contractAst $ Ast.AstTransposeS cperm t2)
                           (contractAst $ Ast.AstTransposeS cperm u)
  Ast.AstSum snat stk (AstTimesS (Ast.AstLet vart vt t2) u) ->
    {- TODO: do we really need this check?
    | not (varNameInAst vart u) ->
        -- The varNameInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
    -}
    astLet vart
           (withKnownSpan (varNameToSpan vart) $ contractAst vt)
           (contractAst $ Ast.AstSum snat stk  -- the crucial exposed redex
                                     (AstTimesS t2 u))
  Ast.AstSum snat stk (AstTimesS t2 (Ast.AstLet varu vu u)) ->
    astLet varu
           (withKnownSpan (varNameToSpan varu) $ contractAst vu)
           (contractAst $ Ast.AstSum snat stk (AstTimesS t2 u))
  Ast.AstSum snat stk (Ast.AstLet var v t2) ->
    astLet var (withKnownSpan (varNameToSpan var) $ contractAst v)
               (contractAst (Ast.AstSum snat stk t2))
  Ast.AstSum snat stk (Ast.AstSum snat2 stk2 (Ast.AstLet var v t2)) ->
    astLet var (withKnownSpan (varNameToSpan var) $ contractAst v)
               (contractAst (Ast.AstSum snat stk (Ast.AstSum snat2 stk2 t2)))
  Ast.AstSum snat stk v -> astSum snat stk (contractAst v)
  Ast.AstReplicate snat stk v -> astReplicate snat stk (contractAst v)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (contractAstHFun f)
                    (contractAstHFun df)
                    (contractAstHFun rf)
                    (contractAst acc0)
                    (contractAst es)
  Ast.AstApply v ll -> astApply (contractAstHFun v) (contractAst ll)
  Ast.AstVar{} -> t0
  Ast.AstCond b a2 a3 ->
    astCond (contractAst b) (contractAst a2) (contractAst a3)
  -- These are only needed for tests that don't vectorize Ast.
  Ast.AstBuild1 snat stk@(STKS ZSS _)  -- generalize
                (var, v@(Ast.AstSum n _
                           (AstTimesS
                              t2
                              (Ast.AstIndexS @shm @shn _shn
                                 u (ix@(AstIntVar var2 :.$ ZIS))))))
    | var == var2
    , not (varNameInAst var t2), not (varNameInAst var u)
    , FTKS shmshn _ <- ftkAst u ->
      withKnownShS (Shaped.shsTakeIx @shn @shm Proxy shmshn ix) $
      case knownShS @shm of
        snat2 :$$ _ | Just Refl <- testEquality snat snat2 ->
          astDot1InS (snat :$$ ZSS) n
                     (contractAst u)
                     (contractAst $ Ast.AstReplicate snat (ftkToSTK (ftkAst t2)) t2)
        _ ->
          let !v2 = contractAst v
          in Ast.AstBuild1 snat stk (var, v2)
  Ast.AstBuild1 snat stk@(STKS ZSS _)
                (var, v@(Ast.AstSum _ _
                           (Ast.AstReshapeS
                              _sh (AstTimesS
                                      t2
                                     (Ast.AstIndexS @shm @shn _shn
                                        u (ix@(AstIntVar var2 :.$ ZIS)))))))
    | ftk2@(FTKS (n :$$ ZSS) _) <- ftkAst t2
    , var == var2
    , not (varNameInAst var t2), not (varNameInAst var u)
    , FTKS shmshn _ <- ftkAst u ->
      withKnownShS (Shaped.shsTakeIx @shn @shm Proxy shmshn ix) $
      case knownShS @shm of
        snat2 :$$ _ | Just Refl <- testEquality snat snat2 ->
          astDot1InS (snat :$$ ZSS) n
                     (contractAst u)
                     (contractAst $ Ast.AstReplicate snat (ftkToSTK ftk2) t2)
        _ ->
          let !v2 = contractAst v
          in Ast.AstBuild1 snat stk (var, v2)
  Ast.AstBuild1 snat stk (var, v) ->
    let !v2 = contractAst v
    in Ast.AstBuild1 snat stk (var, v2)

  Ast.AstLet var u v ->
    astLet var (withKnownSpan (varNameToSpan var) $ contractAst u)
               (contractAst v)

  Ast.AstPrimalPart v -> astPrimalPart (contractAst v)
  Ast.AstDualPart v -> astDualPart (contractAst v)
  Ast.AstPlainPart v -> astPlainPart (contractAst v)
  Ast.AstFromPrimal v -> fromPrimal (contractAst v)
  Ast.AstFromDual v -> fromDual (contractAst v)
  Ast.AstFromPlain v -> fromPlain (contractAst v)

  AstPlusK u v -> contractAst u + contractAst v
  AstTimesK u v -> contractAst u * contractAst v
  Ast.AstN1K opCode u -> astN1K opCode (contractAst u)
  Ast.AstR1K opCode u -> astR1K opCode (contractAst u)
  Ast.AstR2K opCode u v -> astR2K opCode (contractAst u) (contractAst v)
  Ast.AstI2K opCode u v -> astI2K opCode (contractAst u) (contractAst v)
  AstConcreteK{} -> t0
  Ast.AstFloorK a -> astFloorK (contractAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ contractAst v
  Ast.AstCastK v -> astCastK $ contractAst v
  Ast.AstArgMinK v -> astArgMinK $ contractAst v
  Ast.AstArgMaxK v -> astArgMaxK $ contractAst v
  Ast.AstIndexK v ix -> astIndexK (contractAst v) (contractAstIxS ix)

  AstPlusS u v -> contractAst u + contractAst v
  AstTimesS u v -> contractAst u * contractAst v
  Ast.AstN1S opCode u -> astN1S opCode (contractAst u)
  Ast.AstR1S opCode u -> astR1S opCode (contractAst u)
  Ast.AstR2S opCode u v -> astR2S opCode (contractAst u) (contractAst v)
  Ast.AstI2S opCode u v -> astI2S opCode (contractAst u) (contractAst v)
  AstConcreteS{} -> t0
  Ast.AstFloorS @r1 @r2 t -> case contractAst t of
    AstConcreteS a | sizeOf (undefined :: r1) >= sizeOf (undefined :: r2) ->
      fromPlain $ astConcreteS $ tsfloor $ Concrete a
    t2 -> astFloorS t2
  Ast.AstFromIntegralS @r1 @r2 t -> case contractAst t of
    AstConcreteS a | sizeOf (undefined :: r1) >= sizeOf (undefined :: r2) ->
      fromPlain $ astConcreteS $ tsfromIntegral $ Concrete a
    t2 -> astFromIntegralS t2
  Ast.AstCastS @r1 @r2 t -> case contractAst t of
    AstConcreteS a | sizeOf (undefined :: r1) >= sizeOf (undefined :: r2) ->
      astConcreteS (tscast $ Concrete a)
    t2 -> astCastS t2
  Ast.AstArgMinS a -> Ast.AstArgMinS (contractAst a)
  Ast.AstArgMaxS a -> Ast.AstArgMaxS (contractAst a)
  Ast.AstConvert c (Ast.AstIndexS @sh1 ZSS v ix)
    | FTKS _ ftk2@FTKScalar <- ftkAst v
    , Just Refl <- matchingFTK (convertFTK c (FTKS ZSS ftk2)) ftk2
    , Refl <- lemAppNil @sh1 ->
      astIndexK (contractAst v) (contractAstIxS ix)
  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseContraction})
                   shn (contractAst v) (contractAstIxS ix)

  Ast.AstScatterS shm shn shp v (vars, ix) ->
    astScatterS shm shn shp (contractAst v) (vars, contractAstIxS ix)
  -- This rule is reverted in vectorization, so contraction phase may be fine.
  Ast.AstGatherS shm shn shp v (vars, Ast.AstCond b i1 i2 :.$ prest)
    | not $ Foldable.any ((`varInAst` b) . varNameToAstVarId) vars ->
      contractAst
      $ Ast.AstCond b (Ast.AstGatherS shm shn shp v (vars, i1 :.$ prest))
                      (Ast.AstGatherS shm shn shp v (vars, i2 :.$ prest))
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    astGatherKnobsS (defaultKnobs {knobPhase = PhaseContraction})
                    shm shn shp (contractAst v) (vars, contractAstIxS ix)
{- TODO, but sbuild is tricky, so only if benchmarks show it's worth it:
  AstGatherS @shm AstIotaS (vars, i :.$ ZIS) | Refl <- lemAppNil @shm ->
    gcastWith (unsafeCoerceRefl :: Drop (Rank shm) shm :~: '[]) $
    gcastWith (unsafeCoerceRefl :: Take (Rank shm) shm :~: shm) $
    sbuild @_ @_ @(Rank shm)
           (interpretLambdaIndexS
              interpretAst env
              (vars, fromPrimal @s $ AstFromIntegralS $ AstConvUpSFromK i)) -}
  Ast.AstIotaS snat@(SNat @n) | fromSNat' snat < 100 ->
    astConcreteS $ tsiota @_ @n  -- likely not to be O(data size)
  Ast.AstIotaS{} -> t0  -- tough trade-offs here
  Ast.AstAppendS x y -> astAppendS (contractAst x) (contractAst y)
  Ast.AstSliceS i n k t -> astSliceS i n k (contractAst t)
  Ast.AstReverseS t -> astReverseS (contractAst t)
  Ast.AstTransposeS perm v -> astTransposeS perm $ contractAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS sh2 t -> case contractAst t of
    AstConcreteS v -> astConcreteS (tsreshape sh2 $ Concrete v)
    t2 -> astReshapeS sh2 t2

  Ast.AstConvert c v -> astConvertConcrete c $ contractAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstSum0{} -> t0
  Ast.AstDot0{} -> t0
  Ast.AstDot1InS{} -> t0
  Ast.AstMatmul2S{} -> t0

  Ast.AstBoolNotK arg -> notB $ contractAst arg
  Ast.AstBoolNotS arg -> astBoolNotS $ contractAst arg
  Ast.AstBoolAndK arg1 arg2 -> contractAst arg1 &&* contractAst arg2
  Ast.AstBoolAndS arg1 arg2 -> astBoolAndS (contractAst arg1) (contractAst arg2)
  Ast.AstLeqK arg1 arg2 -> fromPlain $ contractAst arg1 <=. contractAst arg2
  Ast.AstLeq arg1 arg2 -> fromPlain $ contractAst arg1 <=. contractAst arg2
  Ast.AstLeqS shb sh arg1 arg2 ->
    fromPlain $ astLeqS shb sh (contractAst arg1) (contractAst arg2)

contractAstHFun :: KnownSpan s
                => AstHFun s x y -> AstHFun s x y
contractAstHFun (AstLambda var l) = AstLambda var (contractAst l)

astConvertConcrete :: forall y z s. KnownSpan s
                   => TKConversion y z
                   -> AstTensor AstMethodLet s y
                   -> AstTensor AstMethodLet s z
astConvertConcrete c a0 = case a0 of
  AstConcreteK a -> astConcreteKeepShaped (convertFTK c FTKScalar)
                    $ tconvert c STKScalar $ Concrete a
  AstConcreteS a -> let ftk = FTKS (Nested.sshape a) FTKScalar
                    in astConcreteKeepShaped (convertFTK c ftk)
                       $ tconvert c (ftkToSTK ftk) $ Concrete a
  Ast.AstPrimalPart a -> astPrimalPart $ astConvertConcrete c a
  Ast.AstDualPart a -> astDualPart $ astConvertConcrete c a
  Ast.AstPlainPart a -> astPlainPart $ astConvertConcrete c a
  Ast.AstFromPrimal a -> fromPrimal $ astConvertConcrete c a
  Ast.AstFromDual a -> fromDual $ astConvertConcrete c a
  Ast.AstFromPlain a -> fromPlain $ astConvertConcrete c a
  Ast.AstConvert c2 a2 -> astConvertConcrete (c `convCmp` c2) a2
  _ -> astConvert c a0

astConcreteKeepShaped :: FullShapeTK y -> Concrete y
                      -> AstTensor AstMethodLet PlainSpan y
astConcreteKeepShaped ftk v = case ftk of
  FTKS _ FTKScalar -> astConcreteS v
  _ -> astConcrete ftk v

attemptMatmul2
  :: forall m n p r s.
     (KnownNat m, KnownNat n, KnownNat p, GoodScalar r, KnownSpan s)
  => AstTensor AstMethodLet s (TKS '[m, n] r)
  -> AstTensor AstMethodLet s (TKS '[n, p] r)
  -> Maybe (AstTensor AstMethodLet s (TKS '[m, p] r))
attemptMatmul2 t3 u3 = Just $
  let t4 = contractAst t3
      u4 = contractAst u3
  in case typeRep @r of
    Is @Int -> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    Is @Double -> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    Is @Float -> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    Is @Z1 -> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    Is @Int64 -> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    Is @Int32-> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    Is @Int16 -> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    Is @Int8 -> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    Is @CInt -> astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    _ -> error "attemptMatmul2: unexpected scalar"


-- * The let down (reducing the scope of lets cheaply) bottom-up pass

letDownAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
letDownAstIxS = fmap letDownAst

letDownAst
  :: forall s y. KnownSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
letDownAst t = case t of
  Ast.AstPair t1 t2 -> Ast.AstPair (letDownAst t1) (letDownAst t2)
  Ast.AstProject1 v -> Ast.AstProject1 (letDownAst v)
  Ast.AstProject2 v -> Ast.AstProject2 (letDownAst v)
  Ast.AstFromVector snat stk l ->
    Ast.AstFromVector snat stk (V.map letDownAst l)
  Ast.AstSum snat stk v -> Ast.AstSum snat stk (letDownAst v)
  Ast.AstReplicate snat stk v -> Ast.AstReplicate snat stk (letDownAst v)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    Ast.AstMapAccumLDer k bftk eftk
                        (letDownAstHFun f)
                        (letDownAstHFun df)
                        (letDownAstHFun rf)
                        (letDownAst acc0)
                        (letDownAst es)
  Ast.AstApply v ll -> Ast.AstApply (letDownAstHFun v) (letDownAst ll)
  Ast.AstVar{} -> t
  Ast.AstCond b a2 a3 ->
    Ast.AstCond (letDownAst b) (letDownAst a2) (letDownAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = letDownAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v ->
    astLetDown var (withKnownSpan (varNameToSpan var) $ letDownAst u)
                   (letDownAst v)

  Ast.AstPrimalPart v -> Ast.AstPrimalPart (letDownAst v)
  Ast.AstDualPart v -> Ast.AstDualPart (letDownAst v)
  Ast.AstPlainPart v -> Ast.AstPlainPart (letDownAst v)
  Ast.AstFromPrimal v -> fromPrimal (letDownAst v)
  Ast.AstFromDual v -> fromDual (letDownAst v)
  Ast.AstFromPlain v -> fromPlain (letDownAst v)

  AstPlusK u v -> AstPlusK (letDownAst u) (letDownAst v)
  AstTimesK u v -> AstTimesK (letDownAst u) (letDownAst v)
  Ast.AstN1K op u -> Ast.AstN1K op (letDownAst u)
  Ast.AstR1K op u -> Ast.AstR1K op (letDownAst u)
  Ast.AstR2K op u v -> Ast.AstR2K op (letDownAst u) (letDownAst v)
  Ast.AstI2K op u v -> Ast.AstI2K op (letDownAst u) (letDownAst v)
  AstConcreteK{} -> t
  Ast.AstFloorK a -> Ast.AstFloorK (letDownAst a)
  Ast.AstFromIntegralK v -> Ast.AstFromIntegralK (letDownAst v)
  Ast.AstCastK v -> Ast.AstCastK (letDownAst v)
  Ast.AstArgMinK v -> Ast.AstArgMinK (letDownAst v)
  Ast.AstArgMaxK v -> Ast.AstArgMaxK (letDownAst v)
  Ast.AstIndexK v ix -> Ast.AstIndexK (letDownAst v) (letDownAstIxS ix)

  AstPlusS u v -> AstPlusS (letDownAst u) (letDownAst v)
  AstTimesS u v -> AstTimesS (letDownAst u) (letDownAst v)
  Ast.AstN1S op u -> Ast.AstN1S op (letDownAst u)
  Ast.AstR1S op u -> Ast.AstR1S op (letDownAst u)
  Ast.AstR2S op u v -> Ast.AstR2S op (letDownAst u) (letDownAst v)
  Ast.AstI2S op u v -> Ast.AstI2S op (letDownAst u) (letDownAst v)
  AstConcreteS{} -> t
  Ast.AstFloorS a -> Ast.AstFloorS (letDownAst a)
  Ast.AstFromIntegralS v -> Ast.AstFromIntegralS (letDownAst v)
  Ast.AstCastS v -> Ast.AstCastS (letDownAst v)
  Ast.AstArgMinS a -> Ast.AstArgMinS (letDownAst a)
  Ast.AstArgMaxS a -> Ast.AstArgMaxS (letDownAst a)
  Ast.AstIndexS shn v ix -> Ast.AstIndexS shn (letDownAst v) (letDownAstIxS ix)

  Ast.AstScatterS shm shn shp v (vars, ix) ->
    let !ix2 = letDownAstIxS ix
    in Ast.AstScatterS shm shn shp (letDownAst v) (vars, ix2)
  Ast.AstGatherS shm shn shp v (vars, ix) ->
    let !ix2 = letDownAstIxS ix
    in Ast.AstGatherS shm shn shp (letDownAst v) (vars, ix2)
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> Ast.AstAppendS (letDownAst x) (letDownAst y)
  Ast.AstSliceS i n k v -> Ast.AstSliceS i n k (letDownAst v)
  Ast.AstReverseS v -> Ast.AstReverseS (letDownAst v)
  Ast.AstTransposeS perm v -> Ast.AstTransposeS perm (letDownAst v)
  Ast.AstReshapeS sh v -> Ast.AstReshapeS sh (letDownAst v)

  Ast.AstConvert c v -> Ast.AstConvert c (letDownAst v)

  Ast.AstSum0 v -> Ast.AstSum0 (letDownAst v)
  Ast.AstDot0 u v -> Ast.AstDot0 (letDownAst u) (letDownAst v)
  Ast.AstDot1InS sh n u v -> Ast.AstDot1InS sh n (letDownAst u) (letDownAst v)
  Ast.AstMatmul2S m n p u v ->
    Ast.AstMatmul2S m n p (letDownAst u) (letDownAst v)

  Ast.AstBoolNotK arg -> Ast.AstBoolNotK (letDownAst arg)
  Ast.AstBoolNotS arg -> Ast.AstBoolNotS (letDownAst arg)
  Ast.AstBoolAndK arg1 arg2 ->
    Ast.AstBoolAndK (letDownAst arg1) (letDownAst arg2)
  Ast.AstBoolAndS arg1 arg2 ->
    Ast.AstBoolAndS (letDownAst arg1) (letDownAst arg2)
  Ast.AstLeqK arg1 arg2 -> Ast.AstLeqK (letDownAst arg1) (letDownAst arg2)
  Ast.AstLeq arg1 arg2 -> Ast.AstLeq (letDownAst arg1) (letDownAst arg2)
  Ast.AstLeqS shb sh arg1 arg2 ->
    Ast.AstLeqS shb sh (letDownAst arg1) (letDownAst arg2)

letDownAstHFun :: KnownSpan s
               => AstHFun s x y -> AstHFun s x y
letDownAstHFun (AstLambda var l) = AstLambda var (letDownAst l)
