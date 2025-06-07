-- | This module implements a few complete bottom-up simplifying passes
-- over any AST expression.
module HordeAd.Core.AstTraverse
  ( -- * The expansion (e.g., into gather expressions) bottom-up pass
    expandAst
    -- * The simplifying bottom-up pass
  , simplifyAst
    -- * The contraction (e.g., from gather expressions) bottom-up pass
  , contractAst
  ) where

import Prelude

import Data.Int (Int64)
import Data.Maybe (fromMaybe)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Foreign.C (CInt)
import GHC.TypeLits (KnownNat)
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation (Perm (..))
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.Ast
  ( AstBool (AstBoolConst)
  , AstTensor (AstConcreteK, AstConcreteS, AstPlusK, AstPlusS, AstTimesK, AstTimesS)
  )
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
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
  :: forall s y. AstSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
expandAst t = case t of
  Ast.AstPair t1 t2 -> astPair (expandAst t1) (expandAst t2)
  Ast.AstProject1 v -> astProject1 (expandAst v)
  Ast.AstProject2 v -> astProject2 (expandAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map expandAst l)
  Ast.AstSum snat stk v -> astSum snat stk (expandAst v)
  Ast.AstReplicate snat stk v -> astReplicate snat stk (expandAst v)
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    astMapAccumRDer k bftk eftk
                    (expandAstHFun f)
                    (expandAstHFun df)
                    (expandAstHFun rf)
                    (expandAst acc0)
                    (expandAst es)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (expandAstHFun f)
                    (expandAstHFun df)
                    (expandAstHFun rf)
                    (expandAst acc0)
                    (expandAst es)
  Ast.AstApply v ll -> astApply (expandAstHFun v) (expandAst ll)
  Ast.AstVar var -> astVar var
  Ast.AstCond b a2 a3 ->
    astCond (expandAstBool b) (expandAst a2) (expandAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = expandAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var (expandAst u) (expandAst v)

  Ast.AstPrimalPart v -> astPrimalPart (expandAst v)
  Ast.AstDualPart v -> astDualPart (expandAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (expandAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (expandAst v)

  AstPlusK u v -> expandAst u + expandAst v
  AstTimesK u v -> expandAst u * expandAst v
  Ast.AstN1K NegateOp u -> negate (expandAst u)
  Ast.AstN1K AbsOp u -> abs (expandAst u)
  Ast.AstN1K SignumOp u -> signum (expandAst u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (expandAst u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (expandAst u) (expandAst v)
  Ast.AstI2K QuotOp u v -> quotH (expandAst u) (expandAst v)
  Ast.AstI2K RemOp u v -> remH (expandAst u) (expandAst v)
  AstConcreteK k -> AstConcreteK k
  Ast.AstFloorK a -> astFloorK (expandAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ expandAst v
  Ast.AstCastK v -> astCastK $ expandAst v

  AstPlusS u v -> expandAst u + expandAst v
  AstTimesS u v -> expandAst u * expandAst v
  Ast.AstN1S NegateOp u -> negate (expandAst u)
  Ast.AstN1S AbsOp u -> abs (expandAst u)
  Ast.AstN1S SignumOp u -> signum (expandAst u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (expandAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (expandAst u) (expandAst v)
  Ast.AstI2S QuotOp u v -> quotH (expandAst u) (expandAst v)
  Ast.AstI2S RemOp u v -> remH (expandAst u) (expandAst v)
  AstConcreteS a -> AstConcreteS a
  Ast.AstFloorS a -> astFloorS (expandAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ expandAst v
  Ast.AstCastS v -> astCastS $ expandAst v

  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseExpansion})
                   shn (expandAst v) (expandAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (expandAst v) (vars, expandAstIxS ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherKnobsS @shm @shn @shp
                    (defaultKnobs {knobPhase = PhaseExpansion})
                    shn (expandAst v) (vars, expandAstIxS ix)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (expandAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (expandAst a)
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
    Ast.AstSFromR{} -> t  -- normal form
    Ast.AstSFromX{} -> t  -- normal form
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
    Ast.AstSFromR{} -> t  -- normal form
    Ast.AstSFromX{} -> t  -- normal form
    v2 ->  -- not nf, let's express all as a gather
      astReshapeAsGatherS (defaultKnobs {knobExpand = True})
                          sh v2
        -- this is expensive but the only way to guarantee full simplification
    -} astReshapeS sh (expandAst v)
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 $ expandAst v
  Ast.AstUnNestS v -> astUnNestS $ expandAst v

  Ast.AstFromS stkz v -> astFromS stkz $ expandAst v
  Ast.AstSFromK u -> astSFromK $ expandAst u
  Ast.AstSFromR sh v -> astSFromR sh $ expandAst v
  Ast.AstSFromX sh v -> astSFromX sh $ expandAst v
  Ast.AstCastCastable c bftk v ->
    Ast.AstCastCastable c bftk $ expandAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatmul2S{} -> t

expandAstHFun :: AstSpan s2
              => AstHFun s s2 x y -> AstHFun s s2 x y
expandAstHFun (AstLambda var l) = AstLambda var (expandAst l)

expandAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
expandAstBool t = case t of
  AstBoolConst{} -> t
  Ast.AstBoolNot arg -> notB $ expandAstBool arg
  Ast.AstBoolAnd arg1 arg2 -> expandAstBool arg1 &&* expandAstBool arg2
  Ast.AstLeqK arg1 arg2 -> expandAst arg1 <=. expandAst arg2
  Ast.AstLeqS arg1 arg2 -> expandAst arg1 <=. expandAst arg2


-- * The simplifying bottom-up pass

simplifyAstIxS :: AstIxS AstMethodLet sh -> AstIxS AstMethodLet sh
simplifyAstIxS = fmap simplifyAst

-- | This function guarantees full simplification (unless redexes are obscured,
-- for which the expansion pass is sometimes a remedy): every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexR.
simplifyAst
  :: forall s y. AstSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
simplifyAst t = case t of
  Ast.AstPair t1 t2 -> astPair (simplifyAst t1) (simplifyAst t2)
  Ast.AstProject1 v -> astProject1 (simplifyAst v)
  Ast.AstProject2 v -> astProject2 (simplifyAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map simplifyAst l)
  Ast.AstSum snat stk v -> astSum snat stk (simplifyAst v)
  Ast.AstReplicate snat stk v ->  astReplicate snat stk (simplifyAst v)
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    astMapAccumRDer k bftk eftk
                    (simplifyAstHFun f)
                    (simplifyAstHFun df)
                    (simplifyAstHFun rf)
                    (simplifyAst acc0)
                    (simplifyAst es)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (simplifyAstHFun f)
                    (simplifyAstHFun df)
                    (simplifyAstHFun rf)
                    (simplifyAst acc0)
                    (simplifyAst es)
  Ast.AstApply v ll -> astApply (simplifyAstHFun v) (simplifyAst ll)
  Ast.AstVar var -> astVar var
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAstBool b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = simplifyAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)

  Ast.AstPrimalPart v -> astPrimalPart (simplifyAst v)
  Ast.AstDualPart v -> astDualPart (simplifyAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (simplifyAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (simplifyAst v)

  AstPlusK u v -> simplifyAst u + simplifyAst v
  AstTimesK u v -> simplifyAst u * simplifyAst v
  Ast.AstN1K NegateOp u -> negate (simplifyAst u)
  Ast.AstN1K AbsOp u -> abs (simplifyAst u)
  Ast.AstN1K SignumOp u -> signum (simplifyAst u)
  Ast.AstR1K opCode u -> Ast.AstR1K opCode (simplifyAst u)
  Ast.AstR2K opCode u v -> Ast.AstR2K opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2K QuotOp u v -> quotH (simplifyAst u) (simplifyAst v)
  Ast.AstI2K RemOp u v -> remH (simplifyAst u) (simplifyAst v)
  AstConcreteK k -> AstConcreteK k
  Ast.AstFloorK a -> astFloorK (simplifyAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ simplifyAst v
  Ast.AstCastK v -> astCastK $ simplifyAst v

  AstPlusS u v -> simplifyAst u + simplifyAst v
  AstTimesS u v -> simplifyAst u * simplifyAst v
  Ast.AstN1S NegateOp u -> negate (simplifyAst u)
  Ast.AstN1S AbsOp u -> abs (simplifyAst u)
  Ast.AstN1S SignumOp u -> signum (simplifyAst u)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (simplifyAst u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (simplifyAst u) (simplifyAst v)
  Ast.AstI2S QuotOp u v -> quotH (simplifyAst u) (simplifyAst v)
  Ast.AstI2S RemOp u v -> remH (simplifyAst u) (simplifyAst v)
  AstConcreteS a -> AstConcreteS a
  Ast.AstFloorS a -> astFloorS (simplifyAst a)
  Ast.AstFromIntegralS v -> astFromIntegralS $ simplifyAst v
  Ast.AstCastS v -> astCastS $ simplifyAst v

  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseSimplification})
                   shn (simplifyAst v) (simplifyAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherKnobsS @shm @shn @shp
                    (defaultKnobs {knobPhase = PhaseSimplification})
                    shn (simplifyAst v) (vars, simplifyAstIxS ix)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (simplifyAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (simplifyAst a)
  Ast.AstIotaS{} -> t
  Ast.AstAppendS x y -> astAppendS (simplifyAst x) (simplifyAst y)
  Ast.AstSliceS i n k v -> astSliceS i n k (simplifyAst v)
  Ast.AstReverseS v -> astReverseS (simplifyAst v)
  Ast.AstTransposeS perm v -> astTransposeS perm $ simplifyAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS sh v -> astReshapeS sh $ simplifyAst v
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 $ simplifyAst v
  Ast.AstUnNestS v -> astUnNestS $ simplifyAst v

  Ast.AstFromS stkz v -> astFromS stkz $ simplifyAst v
  Ast.AstSFromK u -> astSFromK $ simplifyAst u
  Ast.AstSFromR sh v -> astSFromR sh $ simplifyAst v
  Ast.AstSFromX sh v -> astSFromX sh $ simplifyAst v
  Ast.AstCastCastable c bftk v ->
    Ast.AstCastCastable c bftk $ simplifyAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstSum0S{} -> t
  Ast.AstDot0S{} -> t
  Ast.AstDot1InS{} -> t
  Ast.AstMatmul2S{} -> t

simplifyAstHFun :: AstSpan s2
                => AstHFun s s2 x y -> AstHFun s s2 x y
simplifyAstHFun (AstLambda var l) = AstLambda var (simplifyAst l)

simplifyAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
simplifyAstBool t = case t of
  AstBoolConst{} -> t
  Ast.AstBoolNot arg -> notB $ simplifyAstBool arg
  Ast.AstBoolAnd arg1 arg2 -> simplifyAstBool arg1 &&* simplifyAstBool arg2
  Ast.AstLeqK arg1 arg2 -> simplifyAst arg1 <=. simplifyAst arg2
  Ast.AstLeqS arg1 arg2 -> simplifyAst arg1 <=. simplifyAst arg2


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
  :: forall s y. AstSpan s
  => AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
contractAst t0 = case t0 of
  Ast.AstPair t1 t2 -> astPair (contractAst t1) (contractAst t2)
  Ast.AstProject1 v -> astProject1 (contractAst v)
  Ast.AstProject2 v -> astProject2 (contractAst v)
  Ast.AstFromVector snat stk l -> astFromVector snat stk (V.map contractAst l)
  Ast.AstSum _ (STKS ZSS _) t2 -> astSum0S (contractAst t2)
  Ast.AstSum _ STKScalar t2 -> astFromS STKScalar $ astSum0S (contractAst t2)
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
  Ast.AstSum n@(SNat @n) (STKS @sh sh _) (AstTimesS t2 u) ->
    let cpermR = backpermCycle $ 1 + shsLength sh
    in Permutation.permFromList cpermR $ \(cperm :: Permutation.Perm cperm) ->
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
           (contractAst vt)
           (contractAst $ Ast.AstSum snat stk  -- the crucial exposed redex
                                     (AstTimesS t2 u))
  Ast.AstSum snat stk (AstTimesS t2 (Ast.AstLet varu vu u)) ->
    astLet varu
           (contractAst vu)
           (contractAst $ Ast.AstSum snat stk (AstTimesS t2 u))
  Ast.AstSum snat stk (Ast.AstLet var v t2) ->
    astLet var (contractAst v) (contractAst (Ast.AstSum snat stk t2))
  Ast.AstSum snat stk (Ast.AstSum snat2 stk2 (Ast.AstLet var v t2)) ->
    astLet var (contractAst v)
               (contractAst (Ast.AstSum snat stk (Ast.AstSum snat2 stk2 t2)))
  Ast.AstSum snat stk v -> astSum snat stk (contractAst v)
  Ast.AstReplicate snat stk v -> astReplicate snat stk (contractAst v)
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    astMapAccumRDer k bftk eftk
                    (contractAstHFun f)
                    (contractAstHFun df)
                    (contractAstHFun rf)
                    (contractAst acc0)
                    (contractAst es)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    astMapAccumLDer k bftk eftk
                    (contractAstHFun f)
                    (contractAstHFun df)
                    (contractAstHFun rf)
                    (contractAst acc0)
                    (contractAst es)
  Ast.AstApply v ll -> astApply (contractAstHFun v) (contractAst ll)
  Ast.AstVar var -> astVar var
  Ast.AstCond b a2 a3 ->
    astCond (contractAstBool b) (contractAst a2) (contractAst a3)
  -- These are only needed for tests that don't vectorize Ast.
  Ast.AstBuild1 snat (STKS ZSS _)  -- generalize
                (var, Ast.AstSum
                        n _
                        (AstTimesS
                           t2
                           (Ast.AstIndexS _shn
                              u (((:.$) @m (AstIntVar var2) ZIS)))))
    | Just Refl <- testEquality snat (SNat @m)
    , var == var2
    , not (varNameInAst var t2), not (varNameInAst var u) ->
        astDot1InS (snat :$$ ZSS) n
                   (contractAst u)
                   (contractAst
                    $ Ast.AstReplicate snat (ftkToSTK (ftkAst t2)) t2)
  Ast.AstBuild1 snat (STKS ZSS _)
                (var, Ast.AstSum _ _
                        (Ast.AstReshapeS
                           _sh (AstTimesS
                                  t2
                                  (Ast.AstIndexS _shn
                                     u (((:.$) @m (AstIntVar var2) ZIS))))))
    | ftk2@(FTKS (n :$$ ZSS) _) <- ftkAst t2
    , Just Refl <- testEquality snat (SNat @m)
    , var == var2
    , not (varNameInAst var t2), not (varNameInAst var u) ->
        astDot1InS (snat :$$ ZSS) n
                   (contractAst u)
                   (contractAst $ Ast.AstReplicate snat (ftkToSTK ftk2) t2)
  Ast.AstBuild1 k stk (var, v) ->
    let !v2 = contractAst v
    in Ast.AstBuild1 k stk (var, v2)

  Ast.AstLet var u v -> astLet var (contractAst u) (contractAst v)

  Ast.AstPrimalPart v -> astPrimalPart (contractAst v)
  Ast.AstDualPart v -> astDualPart (contractAst v)
  Ast.AstFromPrimal v -> Ast.AstFromPrimal (contractAst v)
  Ast.AstFromDual v -> Ast.AstFromDual (contractAst v)

  AstPlusK u v -> contractAst u + contractAst v
  AstTimesK u v -> contractAst u * contractAst v
  Ast.AstN1K NegateOp u -> negate (contractAst u)
  Ast.AstN1K AbsOp u -> abs (contractAst u)
  Ast.AstN1K SignumOp u -> signum (contractAst u)
  Ast.AstR1K RecipOp u -> recip (contractAst u)
  Ast.AstR1K ExpOp u -> exp (contractAst u)
  Ast.AstR1K LogOp u -> log (contractAst u)
  Ast.AstR1K SqrtOp u -> sqrt (contractAst u)
  Ast.AstR1K SinOp u -> sin (contractAst u)
  Ast.AstR1K CosOp u -> cos (contractAst u)
  Ast.AstR1K TanOp u -> tan (contractAst u)
  Ast.AstR1K AsinOp u -> asin (contractAst u)
  Ast.AstR1K AcosOp u -> acos (contractAst u)
  Ast.AstR1K AtanOp u -> atan (contractAst u)
  Ast.AstR1K SinhOp u -> sinh (contractAst u)
  Ast.AstR1K CoshOp u -> cosh (contractAst u)
  Ast.AstR1K TanhOp u -> tanh (contractAst u)
  Ast.AstR1K AsinhOp u -> asinh (contractAst u)
  Ast.AstR1K AcoshOp u -> acosh (contractAst u)
  Ast.AstR1K AtanhOp u -> atanh (contractAst u)
  Ast.AstR2K DivideOp u v -> contractAst u / contractAst v
  Ast.AstR2K PowerOp u v -> contractAst u ** contractAst v
  Ast.AstR2K LogBaseOp u v -> logBase (contractAst u) (contractAst v)
  Ast.AstR2K Atan2Op u v -> atan2H (contractAst u) (contractAst v)
  Ast.AstI2K QuotOp u v -> quotH (contractAst u) (contractAst v)
  Ast.AstI2K RemOp u v -> remH (contractAst u) (contractAst v)
  AstConcreteK k -> AstConcreteK k
  Ast.AstFloorK a -> astFloorK (contractAst a)
  Ast.AstFromIntegralK v -> astFromIntegralK $ contractAst v
  Ast.AstCastK v -> astCastK $ contractAst v

  AstPlusS u v -> contractAst u + contractAst v
  AstTimesS u v -> contractAst u * contractAst v
  Ast.AstN1S NegateOp u -> negate (contractAst u)
  Ast.AstN1S AbsOp u -> abs (contractAst u)
  Ast.AstN1S SignumOp u -> signum (contractAst u)
  Ast.AstR1S RecipOp u -> recip (contractAst u)
  Ast.AstR1S ExpOp u -> exp (contractAst u)
  Ast.AstR1S LogOp u -> log (contractAst u)
  Ast.AstR1S SqrtOp u -> sqrt (contractAst u)
  Ast.AstR1S SinOp u -> sin (contractAst u)
  Ast.AstR1S CosOp u -> cos (contractAst u)
  Ast.AstR1S TanOp u -> tan (contractAst u)
  Ast.AstR1S AsinOp u -> asin (contractAst u)
  Ast.AstR1S AcosOp u -> acos (contractAst u)
  Ast.AstR1S AtanOp u -> atan (contractAst u)
  Ast.AstR1S SinhOp u -> sinh (contractAst u)
  Ast.AstR1S CoshOp u -> cosh (contractAst u)
  Ast.AstR1S TanhOp u -> tanh (contractAst u)
  Ast.AstR1S AsinhOp u -> asinh (contractAst u)
  Ast.AstR1S AcoshOp u -> acosh (contractAst u)
  Ast.AstR1S AtanhOp u -> atanh (contractAst u)
  Ast.AstR2S DivideOp u v -> contractAst u / contractAst v
  Ast.AstR2S PowerOp u v -> contractAst u ** contractAst v
  Ast.AstR2S LogBaseOp u v -> logBase (contractAst u) (contractAst v)
  Ast.AstR2S Atan2Op u v -> atan2H (contractAst u) (contractAst v)
  Ast.AstI2S QuotOp u v -> quotH (contractAst u) (contractAst v)
  Ast.AstI2S RemOp u v -> remH (contractAst u) (contractAst v)
  AstConcreteS a -> AstConcreteS a
  Ast.AstFloorS t -> case contractAst t of
    AstConcreteS a -> astConcreteS (tsfloor $ Concrete a)
    t2 -> astFloorS t2
  Ast.AstFromIntegralS t -> case contractAst t of
    AstConcreteS a -> astConcreteS (tsfromIntegral $ Concrete a)
    t2 -> astFromIntegralS t2
  Ast.AstCastS t -> case contractAst t of
    AstConcreteS a -> astConcreteS (tscast $ Concrete a)
    t2 -> astCastS t2

  Ast.AstIndexS shn v ix ->
    astIndexKnobsS (defaultKnobs {knobPhase = PhaseContraction})
                   shn (contractAst v) (contractAstIxS ix)
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    astScatterS @shm @shn @shp shn (contractAst v) (vars, contractAstIxS ix)
  -- This rule is reverted in vectorization, so contraction phase may be fine.
  Ast.AstGatherS shn v (vars, Ast.AstCond b i1 i2 :.$ prest)
    | not $ any ((`varInAstBool` b) . varNameToAstVarId) (listsToList vars) ->
      contractAst
      $ Ast.AstCond b
                    (Ast.AstGatherS shn v (vars, i1 :.$ prest))
                    (Ast.AstGatherS shn v (vars, i2 :.$ prest))
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    astGatherKnobsS @shm @shn @shp
                    (defaultKnobs {knobPhase = PhaseContraction})
                    shn (contractAst v) (vars, contractAstIxS ix)
{- TODO, but sbuild is tricky, so only if benchmarks show it's worth it:
  AstGatherS @shm AstIotaS (vars, i :.$ ZIS) | Refl <- lemAppNil @shm ->
    gcastWith (unsafeCoerceRefl :: Drop (Rank shm) shm :~: '[]) $
    gcastWith (unsafeCoerceRefl :: Take (Rank shm) shm :~: shm) $
    sbuild @_ @_ @(Rank shm)
           (interpretLambdaIndexS
              interpretAst env
              (vars, fromPrimal @s $ AstFromIntegralS $ AstSFromK i)) -}
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (contractAst a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (contractAst a)
  Ast.AstIotaS (SNat @n) -> astConcreteS $ tsiota @_ @n
  Ast.AstAppendS x y -> astAppendS (contractAst x) (contractAst y)
  Ast.AstSliceS i n k t -> astSliceS i n k (contractAst t)
  Ast.AstReverseS t -> astReverseS (contractAst t)
  Ast.AstTransposeS perm v -> astTransposeS perm $ contractAst v  -- TODO:(normalizePermutation perm)
  Ast.AstReshapeS sh2 t -> case contractAst t of
    AstConcreteS v -> astConcreteS (tsreshape sh2 $ Concrete v)
    t2 -> astReshapeS sh2 t2
  Ast.AstNestS sh1 sh2 v ->
    astNestS sh1 sh2 $ contractAst v
  Ast.AstUnNestS v -> astUnNestS $ contractAst v

  Ast.AstFromS stkz v -> astFromS stkz $ contractAst v
  Ast.AstSFromK u -> astSFromK $ contractAst u
  Ast.AstSFromR sh v -> astSFromR sh $ contractAst v
  Ast.AstSFromX sh v -> astSFromX sh $ contractAst v
  Ast.AstCastCastable c bftk v ->
    Ast.AstCastCastable c bftk $ contractAst v

  -- These should not appear in this context unless via wacky tests.
  Ast.AstSum0S{} -> t0
  Ast.AstDot0S{} -> t0
  Ast.AstDot1InS{} -> t0
  Ast.AstMatmul2S{} -> t0

attemptMatmul2
  :: forall m n p r s.
     (KnownNat m, KnownNat n, KnownNat p, GoodScalar r, AstSpan s)
  => AstTensor AstMethodLet s (TKS '[m, n] r)
  -> AstTensor AstMethodLet s (TKS '[n, p] r)
  -> Maybe (AstTensor AstMethodLet s (TKS '[m, p] r))
attemptMatmul2 t3 u3 = Just $
  let t4 = contractAst t3
      u4 = contractAst u3
  in case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl ->
      astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl ->
        astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl ->
          astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl ->
            astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
          _ -> case testEquality (typeRep @r) (typeRep @Z1) of
            Just Refl ->
              astMatmul2S (SNat @m) (SNat @n) (SNat @p) t4 u4
            _ -> error "attemptMatmul2: unexpected scalar"

contractAstHFun :: AstSpan s2
                => AstHFun s s2 x y -> AstHFun s s2 x y
contractAstHFun (AstLambda var l) = AstLambda var (contractAst l)

contractAstBool :: AstBool AstMethodLet -> AstBool AstMethodLet
contractAstBool t = case t of
  AstBoolConst{} -> t
  Ast.AstBoolNot arg -> notB $ contractAstBool arg
  Ast.AstBoolAnd arg1 arg2 -> contractAstBool arg1 &&* contractAstBool arg2
  Ast.AstLeqK arg1 arg2 -> contractAst arg1 <=. contractAst arg2
  Ast.AstLeqS arg1 arg2 -> contractAst arg1 <=. contractAst arg2
