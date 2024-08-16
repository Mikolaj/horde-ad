{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Inlining and global sharing elimination.
module HordeAd.Core.AstInline
  ( -- * The joint inlining and simplification term transformation
    simplifyArtifact, simplifyArtifactGradient
  , simplifyInlineAst, simplifyInlineAstS
  , simplifyInlineHVector, simplifyInlineHVectorRaw
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty
    -- * The translates global sharing to normal lets
  , unshareAstRanked, unshareAstShaped, unshareAstHVector
  ) where

import Prelude

import Control.Arrow (second)
import Data.Array.Internal (valueOf)
import Data.EnumMap.Strict qualified as EM
import Data.IntMap.Strict (IntMap)
import Data.List (mapAccumR)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat, fromSNat)
import Type.Reflection (typeRep)

import HordeAd.Core.Ast (AstBool, AstTensor)
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * The joint inlining and simplification term transformation

simplifyArtifact :: AstArtifactRev TKUntyped TKUntyped -> AstArtifactRev TKUntyped TKUntyped
simplifyArtifact art =
  art { artDerivativeRev =
          HVectorPseudoTensor $ simplifyInlineHVectorRaw
          $ unHVectorPseudoTensor $ artDerivativeRev art
      , artPrimalRev =
          HVectorPseudoTensor $ simplifyInlineHVectorRaw
          $ unHVectorPseudoTensor $ artPrimalRev art
      }

simplifyArtifactGradient :: AstArtifactRev TKUntyped TKUntyped -> AstArtifactRev TKUntyped TKUntyped
simplifyArtifactGradient art =
  art { artDerivativeRev =
          HVectorPseudoTensor $ simplifyInlineHVectorRaw
          $ unHVectorPseudoTensor $ artDerivativeRev art
      }

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyInlineAst
  :: forall r n s. (KnownNat n, GoodScalar r, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
simplifyInlineAst =
  AstRanked . snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst . unAstRanked
{-# SPECIALIZE simplifyInlineAst
  :: (KnownNat n, AstSpan s)
  => AstRanked s Double n -> AstRanked s Double n #-}

simplifyInlineAstS
  :: forall r sh s. (GoodScalar r, KnownShS sh, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
simplifyInlineAstS =
  AstShaped . snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst . unAstShaped
{-# SPECIALIZE simplifyInlineAstS
  :: (KnownShS sh, AstSpan s)
  => AstShaped s Double sh -> AstShaped s Double sh #-}

-- TODO: rename, not longer just for HVector
simplifyInlineHVector
  :: (AstSpan s, TensorKind z) => AstTensor s z -> AstTensor s z
simplifyInlineHVector =
  snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst
    -- no specialization possible except for the tag type s

-- TODO: rename, not longer just for HVector
simplifyInlineHVectorRaw
  :: (AstSpan s, TensorKind z)
  => AstRawWrap (AstTensor s z) -> AstRawWrap (AstTensor s z)
simplifyInlineHVectorRaw =
  AstRawWrap . simplifyInlineHVector . unAstRawWrap

prettifyArtifactRev
  :: AstArtifactRev TKUntyped TKUntyped
  -> ( [AstDynamicVarName]
     , [AstDynamicVarName]
     , InterpretationTarget (AstRaw PrimalSpan) TKUntyped
     , InterpretationTarget (AstRaw PrimalSpan) TKUntyped )
prettifyArtifactRev AstArtifactRev{..} =
  let der = unAstRawWrap (unHVectorPseudoTensor artDerivativeRev)
      prim = unAstRawWrap (unHVectorPseudoTensor artPrimalRev)
  in fun1DToAst (shapeAstHVector prim) $ \ !varsDt !astsDt ->
       fun1DToAst (shapeAstHVector der) $ \ !vars1 !asts1 ->
       let idt = SubstitutionPayload $ Ast.AstMkHVector astsDt
           idom = SubstitutionPayload $ Ast.AstMkHVector asts1
           derivative = substituteAst idt artVarDtRev
                        $ substituteAst idom artVarDomainRev der
           primal = substituteAst idom artVarDomainRev prim
       in ( varsDt
          , vars1
          , HVectorPseudoTensor $ AstRawWrap derivative
          , HVectorPseudoTensor $ AstRawWrap primal )

printArtifactSimple
  :: IntMap String
  -> AstArtifactRev TKUntyped TKUntyped
  -> String
printArtifactSimple renames art =
  let (varsDt, vars1, derivative, _) = prettifyArtifactRev art
      varsPP = map (printAstDynamicVarNameBrief renames) $ varsDt ++ vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorSimple
                         renames (unAstRawWrap $ unHVectorPseudoTensor derivative)

printArtifactPretty
  :: IntMap String
  -> AstArtifactRev TKUntyped TKUntyped
  -> String
printArtifactPretty renames art =
  let (varsDt, vars1, derivative, _) = prettifyArtifactRev art
      varsPP = map (printAstDynamicVarNameBrief renames) $ varsDt ++ vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorPretty
                         renames (unAstRawWrap $ unHVectorPseudoTensor derivative)

printArtifactPrimalSimple
  :: IntMap String
  -> AstArtifactRev TKUntyped TKUntyped
  -> String
printArtifactPrimalSimple renames art =
  let (_, vars1, _, primal) = prettifyArtifactRev art
      varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorSimple
                         renames (unAstRawWrap $ unHVectorPseudoTensor primal)

printArtifactPrimalPretty
  :: IntMap String
  -> AstArtifactRev TKUntyped TKUntyped
  -> String
printArtifactPrimalPretty renames art =
  let (_, vars1, _, primal) = prettifyArtifactRev art
      varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorPretty
                         renames (unAstRawWrap $ unHVectorPseudoTensor primal)


-- * The pass that inlines lets with the bottom-up strategy

type AstMemo = EM.EnumMap AstVarId Double

inlineAst
  :: forall s y. AstSpan s
  => AstMemo -> AstTensor s y -> (AstMemo, AstTensor s y)
inlineAst memo v0 = case v0 of
  Ast.AstTuple t1 t2 ->
    let (memo2, v1) = inlineAst memo t1
        (memo3, v2) = inlineAst memo2 t2
    in (memo3, Ast.AstTuple v1 v2)
  -- TODO: these are correct only if each component appears once,
  -- as opposed to one appearing twice and ther other not at all
  -- (or if both components are similar enough)
  -- but without this we miss many other simplifications and simple
  -- examples become unreadable
  Ast.AstProject1 (Ast.AstVar _ var) ->
    let f Nothing = Just 0.5
        f (Just count) = Just $ count + 0.5
    in (EM.alter f (varNameToAstVarId var) memo, v0)
  Ast.AstProject2 (Ast.AstVar _ var) ->
    let f Nothing = Just 0.5
        f (Just count) = Just $ count + 0.5
    in (EM.alter f (varNameToAstVarId var) memo, v0)
  Ast.AstProject1 t -> second Ast.AstProject1 (inlineAst memo t)
  Ast.AstProject2 t -> second Ast.AstProject2 (inlineAst memo t)
  Ast.AstLetTupleIn var1 var2 p v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    -- TODO: check if we should do more, e.g., when p is AstTuple (but maybe
    -- simplification should rewrite that to normal lets instead?).
    let (memo1, p2) = inlineAst memo p
        (memo2, v2) = inlineAst memo1 v
    in (memo2, Ast.AstLetTupleIn var1 var2 p2 v2)

  Ast.AstVar _ var ->
    let f Nothing = Just 1
        f (Just count) = Just $ count + 1
    in (EM.alter f (varNameToAstVarId var) memo, v0)
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ inlineAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ inlineAst memo a
  Ast.AstConstant a -> second Ast.AstConstant $ inlineAst memo a
  Ast.AstD u u' ->
    let (memo1, t1) = inlineAst memo u
        (memo2, t2) = inlineAst memo1 u'
    in (memo2, Ast.AstD t1 t2)
  Ast.AstCond b a2 a3 ->
    -- This is a place where our inlining may increase code size
    -- by enlarging both branches due to not considering number of syntactic
    -- occurrences, but only dynamic occurrences. Tensor expressions
    -- in conditionals are problematic and special enough
    -- that we can let it be until problems are encountered in the wild.
    -- See https://github.com/VMatthijs/CHAD/blob/main/src/Count.hs#L88-L152.
    let (memo1, b1) = inlineAstBool memo b
        (memoA2, t2) = inlineAst EM.empty a2
        (memoA3, t3) = inlineAst EM.empty a3
        memo4 = EM.unionWith max memoA2 memoA3
        memo5 = EM.unionWith (+) memo1 memo4
    in (memo5, Ast.AstCond b1 t2 t3)
  Ast.AstReplicate k v -> second (Ast.AstReplicate k) (inlineAst memo v)
  Ast.AstBuild1 k (var, v) ->
    let (memoV0, v2) = inlineAst EM.empty v
        memo1 = EM.unionWith
                  (\c1 c0 -> c1 + fromInteger (fromSNat k) * c0) memo memoV0
    in (memo1, Ast.AstBuild1 k (var, v2))

  Ast.AstLet var u v ->
    -- We assume there are no nested lets with the same variable, hence
    -- the delete and hence var couldn't appear in memo, so we can make
    -- the recursive call for v with memo intact, to record extra occurences
    -- of other variables without the costly summing of maps.
    let vv = varNameToAstVarId var
        (memo1, v2) = inlineAst memo v
        memo1NoVar = EM.delete vv memo1
        (memo2, u2) = inlineAst memo1NoVar u
    in case EM.findWithDefault 0 vv memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substituteAst (SubstitutionPayload u2) var v2)
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
            memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
                      -- u is small, so the union is fast
        in (memo3, substituteAst (SubstitutionPayload u0) var v2)
      _ -> (memo2, Ast.AstLet var u2 v2)
  Ast.AstShare{} -> error "inlineAst: AstShare"
  Ast.AstMinIndex a -> second Ast.AstMinIndex $ inlineAst memo a
  Ast.AstMaxIndex a -> second Ast.AstMaxIndex $ inlineAst memo a
  Ast.AstFloor a -> second Ast.AstFloor $ inlineAst memo a
  Ast.AstIota -> (memo, v0)
  Ast.AstN1 opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstN1 opCode u2)
  Ast.AstN2 opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstN2 opCode u2 v3)
  Ast.AstR1 opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstR1 opCode u2)
  Ast.AstR2 opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstR2 opCode u2 v3)
  Ast.AstI2 opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstI2 opCode u2 v3)
  Ast.AstSumOfList args ->
    let (memo2, args2) = mapAccumR inlineAst memo args
    in (memo2, Ast.AstSumOfList args2)
  Ast.AstIndex v ix ->
    let (memo1, v2) = inlineAst memo v
        (memo2, ix2) = mapAccumR inlineAst memo1 (indexToList ix)
    in (memo2, Ast.AstIndex v2 (listToIndex ix2))
  Ast.AstSum v -> second Ast.AstSum (inlineAst memo v)
  Ast.AstScatter sh v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty (indexToList ix)
        count = fromIntegral $ sizeShape sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatter sh v2 (vars, listToIndex ix2))
  Ast.AstFromVector l ->
    let (memo2, l2) = mapAccumR inlineAst memo (V.toList l)
    in (memo2, Ast.AstFromVector $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstAppend x y ->
    let (memo1, t1) = inlineAst memo x
        (memo2, t2) = inlineAst memo1 y
    in (memo2, Ast.AstAppend t1 t2)
  Ast.AstSlice i k v -> second (Ast.AstSlice i k) (inlineAst memo v)
  Ast.AstReverse v -> second Ast.AstReverse (inlineAst memo v)
  Ast.AstTranspose perm v ->
    second (Ast.AstTranspose perm) $ inlineAst memo v
  Ast.AstReshape sh v -> second (Ast.AstReshape sh) (inlineAst memo v)
  Ast.AstGather sh v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty (indexToList ix)
        count = fromIntegral $ sizeShape sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGather sh v2 (vars, listToIndex ix2))
  Ast.AstCast v -> second Ast.AstCast $ inlineAst memo v
  Ast.AstFromIntegral v -> second Ast.AstFromIntegral $ inlineAst memo v
  Ast.AstConst{} -> (memo, v0)
  Ast.AstProjectR l p ->
    let (memo1, l2) = inlineAst memo l
    in (memo1, Ast.AstProjectR l2 p)
  Ast.AstLetHVectorIn vars l v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, l2) = inlineAst memo l
        (memo2, v2) = inlineAst memo1 v
    in (memo2, Ast.AstLetHVectorIn vars l2 v2)
  Ast.AstLetHFunIn var f v ->
    -- We assume there are no nested lets with the same variable.
    -- We assume functions are never small enough to justify inlining
    -- into more than one place.
    let (memo1, v2) = inlineAst memo v
        (memo2, f2) = inlineAstHFun memo1 f
    in case EM.findWithDefault 0 var memo2 of
      0 -> (memo1, v2)
      1 -> (memo2, fromMaybe v2 $ substitute1Ast
                                    (SubstitutionPayloadHFun f2) var v2)
      _ -> (memo2, Ast.AstLetHFunIn var f2 v2)
  Ast.AstLetHFunInTKNew var f v ->
    -- We assume there are no nested lets with the same variable.
    -- We assume functions are never small enough to justify inlining
    -- into more than one place.
    let (memo1, v2) = inlineAst memo v
        (memo2, f2) = inlineAstHFunTKNew memo1 f
    in case EM.findWithDefault 0 var memo2 of
      0 -> (memo1, v2)
      1 -> (memo2, fromMaybe v2 $ substitute1Ast
                                    (SubstitutionPayloadHFunTKNew f2) var v2)
      _ -> (memo2, Ast.AstLetHFunInTKNew var f2 v2)
  Ast.AstRFromS v -> second Ast.AstRFromS $ inlineAst memo v

  Ast.AstMinIndexS a -> second Ast.AstMinIndexS $ inlineAst memo a
  Ast.AstMaxIndexS a -> second Ast.AstMaxIndexS $ inlineAst memo a
  Ast.AstFloorS a -> second Ast.AstFloorS $ inlineAst memo a
  Ast.AstIotaS -> (memo, v0)
  Ast.AstN1S opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstN1S opCode u2)
  Ast.AstN2S opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstN2S opCode u2 v3)
  Ast.AstR1S opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstR1S opCode u2)
  Ast.AstR2S opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstR2S opCode u2 v3)
  Ast.AstI2S opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstI2S opCode u2 v3)
  Ast.AstSumOfListS args ->
    let (memo2, args2) = mapAccumR inlineAst memo args
    in (memo2, Ast.AstSumOfListS args2)
  Ast.AstIndexS @sh1 v ix ->
    let (memo1, v2) = inlineAst memo v
        (memo2, ix2) = mapAccumR inlineAst memo1
                                 (ShapedList.indexToList ix)
    in (memo2, Ast.AstIndexS @sh1 v2 (ShapedList.listToIndex ix2))
  Ast.AstSumS v -> second Ast.AstSumS (inlineAst memo v)
  Ast.AstScatterS @sh2 @p @sh v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty
                                  (ShapedList.indexToList ix)
        count = fromIntegral $ sizeT @sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatterS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstFromVectorS l ->
    let (memo2, l2) = mapAccumR inlineAst memo (V.toList l)
    in (memo2, Ast.AstFromVectorS $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstAppendS x y ->
    let (memo1, t1) = inlineAst memo x
        (memo2, t2) = inlineAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (inlineAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (inlineAst memo v)
  Ast.AstTransposeS perm v ->
    second (Ast.AstTransposeS perm) $ inlineAst memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (inlineAst memo v)
  Ast.AstGatherS @sh2 @p @sh v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty
                                  (ShapedList.indexToList ix)
        count = fromIntegral $ sizeT @sh2 + sizeT @sh - valueOf @p
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGatherS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ inlineAst memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ inlineAst memo v
  Ast.AstConstS{} -> (memo, v0)
  Ast.AstProjectS l p ->
    let (memo1, l2) = inlineAst memo l
    in (memo1, Ast.AstProjectS l2 p)
  Ast.AstLetHVectorInS vars l v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, l2) = inlineAst memo l
        (memo2, v2) = inlineAst memo1 v
    in (memo2, Ast.AstLetHVectorInS vars l2 v2)
  Ast.AstLetHFunInS var f v ->
    -- We assume there are no nested lets with the same variable.
    -- We assume functions are never small enough to justify inlining
    -- into more than one place.
    let (memo1, v2) = inlineAst memo v
        (memo2, f2) = inlineAstHFun memo1 f
    in case EM.findWithDefault 0 var memo2 of
      0 -> (memo1, v2)
      1 -> (memo2, fromMaybe v2 $ substitute1Ast
                                    (SubstitutionPayloadHFun f2) var v2)
      _ -> (memo2, Ast.AstLetHFunInS var f2 v2)
  Ast.AstLetHFunInSTKNew var f v ->
    -- We assume there are no nested lets with the same variable.
    -- We assume functions are never small enough to justify inlining
    -- into more than one place.
    let (memo1, v2) = inlineAst memo v
        (memo2, f2) = inlineAstHFunTKNew memo1 f
    in case EM.findWithDefault 0 var memo2 of
      0 -> (memo1, v2)
      1 -> (memo2, fromMaybe v2 $ substitute1Ast
                                    (SubstitutionPayloadHFunTKNew f2) var v2)
      _ -> (memo2, Ast.AstLetHFunInSTKNew var f2 v2)
  Ast.AstSFromR v -> second Ast.AstSFromR $ inlineAst memo v

  Ast.AstMkHVector l ->
    second Ast.AstMkHVector $ mapAccumR inlineAstDynamic memo l
  Ast.AstHApply t ll ->
    let (memo1, t2) = inlineAstHFun memo t
        (memo2, ll2) = mapAccumR (mapAccumR inlineAstDynamic) memo1 ll
    in (memo2, Ast.AstHApply t2 ll2)
  Ast.AstHApplyTKNew t ll ->
    let (memo1, t2) = inlineAstHFunTKNew memo t
        (memo2, ll2) = inlineAst memo1 ll
    in (memo2, Ast.AstHApplyTKNew t2 ll2)
  Ast.AstLetHVectorInHVector vars u v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, u2) = inlineAst memo u
        (memo2, v2) = inlineAst memo1 v
    in (memo2, Ast.AstLetHVectorInHVector vars u2 v2)
  Ast.AstLetHFunInHVector var f v ->
    -- We assume there are no nested lets with the same variable.
    -- We assume functions are never small enough to justify inlining
    -- into more than one place.
    let (memo1, v2) = inlineAst memo v
        (memo2, f2) = inlineAstHFun memo1 f
    in case EM.findWithDefault 0 var memo2 of
      0 -> (memo1, v2)
      1 -> (memo2, fromMaybe v2 $ substitute1Ast
                                    (SubstitutionPayloadHFun f2) var v2)
      _ -> (memo2, Ast.AstLetHFunInHVector var f2 v2)
  Ast.AstLetHFunInHVectorTKNew var f v ->
    -- We assume there are no nested lets with the same variable.
    -- We assume functions are never small enough to justify inlining
    -- into more than one place.
    let (memo1, v2) = inlineAst memo v
        (memo2, f2) = inlineAstHFunTKNew memo1 f
    in case EM.findWithDefault 0 var memo2 of
      0 -> (memo1, v2)
      1 -> (memo2, fromMaybe v2 $ substitute1Ast
                                    (SubstitutionPayloadHFunTKNew f2) var v2)
      _ -> (memo2, Ast.AstLetHFunInHVectorTKNew var f2 v2)
  Ast.AstShareHVector{} -> error "inlineAst: AstShareHVector"
  Ast.AstBuildHVector1 k (var, v) ->
    let (memoV0, v2) = inlineAst EM.empty v
        memo1 = EM.unionWith
                  (\c1 c0 -> c1 + fromInteger (fromSNat k) * c0) memo memoV0
    in (memo1, Ast.AstBuildHVector1 k (var, v2))
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFun memo f
        (memo2, df2) = inlineAstHFun memo1 df
        (memo3, rf2) = inlineAstHFun memo2 rf
        (memo4, acc02) = inlineAst memo3 acc0
        (memo5, es2) = inlineAst memo4 es
    in (memo5, Ast.AstMapAccumRDer k accShs bShs eShs f2 df2 rf2 acc02 es2)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFun memo f
        (memo2, df2) = inlineAstHFun memo1 df
        (memo3, rf2) = inlineAstHFun memo2 rf
        (memo4, acc02) = inlineAst memo3 acc0
        (memo5, es2) = inlineAst memo4 es
    in (memo5, Ast.AstMapAccumLDer k accShs bShs eShs f2 df2 rf2 acc02 es2)
  Ast.AstMapAccumRDerTKNew k accShs bShs eShs f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFunTKNew memo f
        (memo2, df2) = inlineAstHFunTKNew memo1 df
        (memo3, rf2) = inlineAstHFunTKNew memo2 rf
        (memo4, acc02) = inlineAst memo3 acc0
        (memo5, es2) = inlineAst memo4 es
    in (memo5, Ast.AstMapAccumRDerTKNew k accShs bShs eShs f2 df2 rf2 acc02 es2)
  Ast.AstMapAccumLDerTKNew k accShs bShs eShs f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFunTKNew memo f
        (memo2, df2) = inlineAstHFunTKNew memo1 df
        (memo3, rf2) = inlineAstHFunTKNew memo2 rf
        (memo4, acc02) = inlineAst memo3 acc0
        (memo5, es2) = inlineAst memo4 es
    in (memo5, Ast.AstMapAccumLDerTKNew k accShs bShs eShs f2 df2 rf2 acc02 es2)

inlineAstDynamic
  :: AstSpan s
  => AstMemo -> AstDynamic s
  -> (AstMemo, AstDynamic s)
inlineAstDynamic memo = \case
  DynamicRanked (AstRanked w) ->
    second (DynamicRanked . AstRanked) $ inlineAst memo w
  DynamicShaped (AstShaped w) ->
    second (DynamicShaped . AstShaped) $ inlineAst memo w
  u@DynamicRankedDummy{} -> (memo, u)
  u@DynamicShapedDummy{} -> (memo, u)

inlineAstHFun
  :: AstMemo -> AstHFun y -> (AstMemo, AstHFun y)
inlineAstHFun memo v0 = case v0 of
  Ast.AstLambda ~(vvars, l) ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards.
    (memo, Ast.AstLambda (vvars, snd $ inlineAst EM.empty l))
  Ast.AstVarHFun _shss _shs var ->
    let f Nothing = Just 1
        f (Just count) = Just $ count + 1
    in (EM.alter f var memo, v0)

inlineAstHFunTKNew
  :: AstMemo -> AstHFunTKNew x y -> (AstMemo, AstHFunTKNew x y)
inlineAstHFunTKNew memo v0 = case v0 of
  Ast.AstLambdaTKNew ~(var, ftk, l) ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards.
    (memo, Ast.AstLambdaTKNew (var, ftk, snd $ inlineAst EM.empty l))
  Ast.AstVarHFunTKNew _shss _shs var ->
    let f Nothing = Just 1
        f (Just count) = Just $ count + 1
    in (EM.alter f var memo, v0)

inlineAstBool :: AstMemo -> AstBool -> (AstMemo, AstBool)
inlineAstBool memo v0 = case v0 of
  Ast.AstBoolNot arg ->
    let (memo2, arg2) = inlineAstBool memo arg
    in (memo2, Ast.AstBoolNot arg2)
  Ast.AstB2 opCodeBool arg1 arg2 ->
    let (memo1, b1) = inlineAstBool memo arg1
        (memo2, b2) = inlineAstBool memo1 arg2
    in (memo2, Ast.AstB2 opCodeBool b1 b2)
  Ast.AstBoolConst{} -> (memo, v0)
  Ast.AstRel opCodeRel arg1 arg2 ->
    let (memo1, r1) = inlineAst memo arg1
        (memo2, r2) = inlineAst memo1 arg2
    in (memo2, Ast.AstRel opCodeRel r1 r2)
  Ast.AstRelS opCodeRel arg1 arg2 ->
    let (memo1, r1) = inlineAst memo arg1
        (memo2, r2) = inlineAst memo1 arg2
    in (memo2, Ast.AstRelS opCodeRel r1 r2)


-- * The translates global sharing to normal lets

unshareAstRanked :: (KnownNat n, GoodScalar r)
               => AstTensor PrimalSpan (TKR r n)
               -> AstTensor PrimalSpan (TKR r n)
unshareAstRanked t =
  let (memoOut, share) = shareAst EM.empty t
      bindingsOut = EM.toDescList memoOut
  in bindsToLet share bindingsOut

unshareAstShaped :: (KnownShS sh, GoodScalar r)
               => AstTensor PrimalSpan (TKS r sh)
               -> AstTensor PrimalSpan (TKS r sh)
unshareAstShaped t =
  let (memoOut, share) = shareAst EM.empty t
      bindingsOut = EM.toDescList memoOut
  in bindsToLetS share bindingsOut

unshareAstHVector :: AstTensor PrimalSpan TKUntyped -> AstTensor PrimalSpan TKUntyped
unshareAstHVector t =
  let (memoOut, share) = shareAst EM.empty t
      bindingsOut = EM.toDescList memoOut
  in bindsToHVectorLet share bindingsOut

type ShareMemo = EM.EnumMap AstVarId (AstBindingsCase PrimalSpan)

-- This works only because the other code never inserts the same rshare
-- into more than one index element, with the share containing
-- the gather/scatter/build variables corresponding to the index.
shareAstScoped
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => [IntVarName] -> ShareMemo -> AstTensor s (TKR r n)
  -> (ShareMemo, AstTensor s (TKR r n))
shareAstScoped vars0 memo0 v0 =
  let (memo1, v1) = shareAst memo0 v0
      memoDiff = EM.difference memo1 memo0
      varsOccur vs d = any (`varInAstBindingsCase` d) vs
      closeOccurs :: [AstVarId] -> ShareMemo -> (ShareMemo, ShareMemo)
      closeOccurs vars memo =
        let (memoLocal, memoGlobal) = EM.partition (varsOccur vars) memo
        in if EM.null memoLocal
           then (memoLocal, memoGlobal)
           else -- TODO: we probably need to include all variables from
                -- the HVector case, not only the first variable
                -- that represents them
                let vars2 = EM.keys memoLocal
                    (memoLocal2, memoGlobal2) = closeOccurs vars2 memoGlobal
                in (EM.union memoLocal memoLocal2, memoGlobal2)
      (memoLocal1, memoGlobal1) =
        closeOccurs (map varNameToAstVarId vars0) memoDiff
      bindingsLocal = EM.toDescList memoLocal1
  in (EM.union memo0 memoGlobal1, bindsToLet v1 bindingsLocal)

shareAst
  :: forall s y. AstSpan s
  => ShareMemo -> AstTensor s y -> (ShareMemo, AstTensor s y)
shareAst memo v0 = case v0 of
  Ast.AstTuple t1 t2 ->
    let (memo1, v1) = shareAst memo t1
        (memo2, v2) = shareAst memo1 t2
    in (memo2, Ast.AstTuple v1 v2)
  Ast.AstProject1 t -> second Ast.AstProject1 (shareAst memo t)
  Ast.AstProject2 t -> second Ast.AstProject2 (shareAst memo t)
  Ast.AstLetTupleIn{} -> error "shareAst: AstLetTupleIn"

  Ast.AstVar{} -> (memo, v0)
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ shareAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ shareAst memo a
  Ast.AstConstant a -> second Ast.AstConstant $ shareAst memo a
  Ast.AstD u u' ->
    let (memo1, t1) = shareAst memo u
        (memo2, t2) = shareAst memo1 u'
    in (memo2, Ast.AstD t1 t2)
  Ast.AstCond b a2 a3 ->
    let (memo1, b1) = shareAstBool memo b
        (memo2, t2) = shareAst memo1 a2
        (memo3, t3) = shareAst memo2 a3
    in (memo3, Ast.AstCond b1 t2 t3)
  Ast.AstReplicate k v -> second (Ast.AstReplicate k) (shareAst memo v)
  Ast.AstBuild1 @y2 snat (var, v) -> case stensorKind @y2 of
    STKR{} ->
      let (memo1, v2) = shareAstScoped [var] memo v
      in (memo1, Ast.AstBuild1 snat (var, v2))
    STKS{} -> error "WIP"
    STKProduct{} -> error "WIP"
    STKUntyped -> error "WIP"
  Ast.AstLet{} -> error "shareAst: AstLet"
    -- delta eval doesn't create lets and no lets
    -- survive instantiating in ADVal
  Ast.AstShare @y2 var v | Just Refl <- sameAstSpan @s @PrimalSpan ->
    -- We assume v is the same if var is the same.
    let varId = varNameToAstVarId var
        astVar = Ast.AstVar (shapeAstFull v) var
    in if varId `EM.member` memo
       then (memo, astVar)  -- TODO: memoize AstVar itself
       else let (memo1, v2) = shareAst memo v
                d = case stensorKind @y2 of
                  STKR{} -> AstBindingsSimple $ DynamicRanked $ AstRanked v2
                  STKS{} -> AstBindingsSimple $ DynamicShaped $ AstShaped v2
                  STKProduct{} -> error "TODO"
                  STKUntyped{} -> error "TODO"
            in (EM.insert varId d memo1, astVar)

  Ast.AstShare{} -> error "shareAst: AstShare not in PrimalSpan"
  Ast.AstMinIndex a -> second Ast.AstMinIndex $ shareAst memo a
  Ast.AstMaxIndex a -> second Ast.AstMaxIndex $ shareAst memo a
  Ast.AstFloor a -> second Ast.AstFloor $ shareAst memo a
  Ast.AstIota -> (memo, v0)
  Ast.AstN1 opCode u ->
    let (memo2, u2) = shareAst memo u
    in (memo2, Ast.AstN1 opCode u2)
  Ast.AstN2 opCode u v ->
    let (memo2, u2) = shareAst memo u
        (memo3, v3) = shareAst memo2 v
    in (memo3, Ast.AstN2 opCode u2 v3)
  Ast.AstR1 opCode u ->
    let (memo2, u2) = shareAst memo u
    in (memo2, Ast.AstR1 opCode u2)
  Ast.AstR2 opCode u v ->
    let (memo2, u2) = shareAst memo u
        (memo3, v3) = shareAst memo2 v
    in (memo3, Ast.AstR2 opCode u2 v3)
  Ast.AstI2 opCode u v ->
    let (memo2, u2) = shareAst memo u
        (memo3, v3) = shareAst memo2 v
    in (memo3, Ast.AstI2 opCode u2 v3)
  Ast.AstSumOfList args ->
    let (memo2, args2) = mapAccumR shareAst memo args
    in (memo2, Ast.AstSumOfList args2)
  Ast.AstIndex v ix ->
    let (memo1, v2) = shareAst memo v
        (memo2, ix2) = mapAccumR shareAst memo1 (indexToList ix)
    in (memo2, Ast.AstIndex v2 (listToIndex ix2))
  Ast.AstSum v -> second Ast.AstSum (shareAst memo v)
  Ast.AstScatter sh v (vars, ix) ->
    let (memo1, ix2) = mapAccumR (shareAstScoped $ sizedToList vars)
                                 memo (indexToList ix)
        (memo2, v2) = shareAst memo1 v
    in (memo2, Ast.AstScatter sh v2 (vars, listToIndex ix2))
  Ast.AstFromVector l ->
    let (memo2, l2) = mapAccumR shareAst memo (V.toList l)
    in (memo2, Ast.AstFromVector $ V.fromList l2)
  Ast.AstAppend x y ->
    let (memo1, t1) = shareAst memo x
        (memo2, t2) = shareAst memo1 y
    in (memo2, Ast.AstAppend t1 t2)
  Ast.AstSlice i k v -> second (Ast.AstSlice i k) (shareAst memo v)
  Ast.AstReverse v -> second Ast.AstReverse (shareAst memo v)
  Ast.AstTranspose perm v ->
    second (Ast.AstTranspose perm) $ shareAst memo v
  Ast.AstReshape sh v -> second (Ast.AstReshape sh) (shareAst memo v)
  Ast.AstGather sh v (vars, ix) ->
    let (memo1, ix2) = mapAccumR (shareAstScoped $ sizedToList vars)
                                 memo (indexToList ix)
        (memo2, v2) = shareAst memo1 v
    in (memo2, Ast.AstGather sh v2 (vars, listToIndex ix2))
  Ast.AstCast v -> second Ast.AstCast $ shareAst memo v
  Ast.AstFromIntegral v -> second Ast.AstFromIntegral $ shareAst memo v
  Ast.AstConst{} -> (memo, v0)
  Ast.AstProjectR l p ->
    -- This doesn't get simplified even if l is an HVector of vars freshly
    -- created by shareAst. However, then l is shared, so the cost
    -- per AstProjectR is only slightly (2 words? 1 indirection?)
    -- higher than if simplified.
    let (memo1, l2) = shareAst memo l
    in (memo1, Ast.AstProjectR l2 p)
  Ast.AstLetHVectorIn{} -> error "shareAst: AstLetHVectorIn"
  Ast.AstLetHFunIn{} -> error "shareAst: AstLetHFunIn"
  Ast.AstLetHFunInTKNew{} -> error "shareAst: AstLetHFunIn"
  Ast.AstRFromS v -> second Ast.AstRFromS $ shareAst memo v

  Ast.AstMinIndexS a -> second Ast.AstMinIndexS $ shareAst memo a
  Ast.AstMaxIndexS a -> second Ast.AstMaxIndexS $ shareAst memo a
  Ast.AstFloorS a -> second Ast.AstFloorS $ shareAst memo a
  Ast.AstIotaS -> (memo, v0)
  Ast.AstN1S opCode u ->
    let (memo2, u2) = shareAst memo u
    in (memo2, Ast.AstN1S opCode u2)
  Ast.AstN2S opCode u v ->
    let (memo2, u2) = shareAst memo u
        (memo3, v3) = shareAst memo2 v
    in (memo3, Ast.AstN2S opCode u2 v3)
  Ast.AstR1S opCode u ->
    let (memo2, u2) = shareAst memo u
    in (memo2, Ast.AstR1S opCode u2)
  Ast.AstR2S opCode u v ->
    let (memo2, u2) = shareAst memo u
        (memo3, v3) = shareAst memo2 v
    in (memo3, Ast.AstR2S opCode u2 v3)
  Ast.AstI2S opCode u v ->
    let (memo2, u2) = shareAst memo u
        (memo3, v3) = shareAst memo2 v
    in (memo3, Ast.AstI2S opCode u2 v3)
  Ast.AstSumOfListS args ->
    let (memo2, args2) = mapAccumR shareAst memo args
    in (memo2, Ast.AstSumOfListS args2)
  Ast.AstIndexS @sh1 v ix ->
    let (memo1, v2) = shareAst memo v
        (memo2, ix2) = mapAccumR shareAst memo1 (ShapedList.indexToList ix)
    in (memo2, Ast.AstIndexS @sh1 v2 (ShapedList.listToIndex ix2))
  Ast.AstSumS v -> second Ast.AstSumS (shareAst memo v)
  Ast.AstScatterS @sh2 @p v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (shareAstScoped $ ShapedList.sizedToList vars)
                    memo (ShapedList.indexToList ix)
        (memo2, v2) = shareAst memo1 v
    in (memo2, Ast.AstScatterS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstFromVectorS l ->
    let (memo2, l2) = mapAccumR shareAst memo (V.toList l)
    in (memo2, Ast.AstFromVectorS $ V.fromList l2)
  Ast.AstAppendS x y ->
    let (memo1, t1) = shareAst memo x
        (memo2, t2) = shareAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (shareAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (shareAst memo v)
  Ast.AstTransposeS perm v ->
    second (Ast.AstTransposeS perm) $ shareAst memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (shareAst memo v)
  Ast.AstGatherS @sh2 @p v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (shareAstScoped $ ShapedList.sizedToList vars)
                    memo (ShapedList.indexToList ix)
        (memo2, v2) = shareAst memo1 v
    in (memo2, Ast.AstGatherS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ shareAst memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ shareAst memo v
  Ast.AstConstS{} -> (memo, v0)
  Ast.AstProjectS l p ->
    let (memo1, l2) = shareAst memo l
    in (memo1, Ast.AstProjectS l2 p)
  Ast.AstLetHVectorInS{} -> error "shareAst: AstLetHVectorInS"
  Ast.AstLetHFunInS{} -> error "shareAst: AstLetHFunInS"
  Ast.AstLetHFunInSTKNew{} -> error "shareAst: AstLetHFunInS"
  Ast.AstSFromR v -> second Ast.AstSFromR $ shareAst memo v

  Ast.AstMkHVector l ->
    second Ast.AstMkHVector $ mapAccumR shareAstDynamic memo l
  Ast.AstHApply t ll ->
    let (memo1, t2) = shareAstHFun memo t
        (memo2, ll2) = mapAccumR (mapAccumR shareAstDynamic) memo1 ll
    in (memo2, Ast.AstHApply t2 ll2)
  Ast.AstHApplyTKNew t ll ->
    let (memo1, t2) = shareAstHFunTKNew memo t
        (memo2, ll2) = shareAst memo1 ll
    in (memo2, Ast.AstHApplyTKNew t2 ll2)
  Ast.AstLetHVectorInHVector{} -> error "shareAst: AstLetHVectorInHVector"
  Ast.AstLetHFunInHVector{} -> error "shareAst: AstLetHFunInHVector"
  Ast.AstLetHFunInHVectorTKNew{} -> error "shareAst: AstLetHFunInHVector"
  Ast.AstShareHVector [] l -> (memo, l)  -- no need to share an empty HVector
  Ast.AstShareHVector vars l | Just Refl <- sameAstSpan @s @PrimalSpan ->
    -- We assume l is the same if vars are the same.
    let var = vars !! 0  -- vars are fresh, so var uniquely represents vars
        varId = dynamicVarNameToAstVarId var
        f :: AstDynamicVarName -> DynamicTensor (AstRanked PrimalSpan)
        f (AstDynamicVarName @ty @rD @shD varIdD) =
          case testEquality (typeRep @ty) (typeRep @Nat) of
            Just Refl -> withListSh (Proxy @shD) $ \sh ->
              DynamicRanked @rD $ AstRanked $ Ast.AstVar (FTKR sh) (mkAstVarName varIdD)
            _ -> DynamicShaped @rD @shD $ AstShaped $ Ast.AstVar FTKS (mkAstVarName varIdD)
        astVars = Ast.AstMkHVector $ V.fromList $ map f vars
    in if varId `EM.member` memo
       then (memo, astVars)
       else let (memo1, l2) = shareAst memo l
                d = AstBindingsHVector vars l2
            in (EM.insert varId d memo1, astVars)
  Ast.AstShareHVector{} ->
    error "shareAst: AstShareHVector not in PrimalSpan"
  Ast.AstBuildHVector1{} -> error "shareAst: AstBuildHVector1"  -- not hard to add
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = shareAst memo acc0
        (memo2, es2) = shareAst memo1 es
    in (memo2, Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc02 es2)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = shareAst memo acc0
        (memo2, es2) = shareAst memo1 es
    in (memo2, Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc02 es2)
  Ast.AstMapAccumRDerTKNew k accShs bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = shareAst memo acc0
        (memo2, es2) = shareAst memo1 es
    in (memo2, Ast.AstMapAccumRDerTKNew k accShs bShs eShs f df rf acc02 es2)
  Ast.AstMapAccumLDerTKNew k accShs bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = shareAst memo acc0
        (memo2, es2) = shareAst memo1 es
    in (memo2, Ast.AstMapAccumLDerTKNew k accShs bShs eShs f df rf acc02 es2)

shareAstDynamic
  :: AstSpan s
  => ShareMemo -> AstDynamic s -> (ShareMemo, AstDynamic s)
shareAstDynamic memo = \case
  DynamicRanked (AstRanked w) ->
    second (DynamicRanked . AstRanked) $ shareAst memo w
  DynamicShaped (AstShaped w) ->
    second (DynamicShaped . AstShaped) $ shareAst memo w
  u@DynamicRankedDummy{} -> (memo, u)
  u@DynamicShapedDummy{} -> (memo, u)

shareAstHFun
  :: ShareMemo -> AstHFun y -> (ShareMemo, AstHFun y)
shareAstHFun memo v0 = case v0 of
  Ast.AstLambda{} ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards
    -- nor remove the Share constructors.
    (memo, v0)
  Ast.AstVarHFun{} -> (memo, v0)

shareAstHFunTKNew
  :: ShareMemo -> AstHFunTKNew x y -> (ShareMemo, AstHFunTKNew x y)
shareAstHFunTKNew memo v0 = case v0 of
  Ast.AstLambdaTKNew{} ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards
    -- nor remove the Share constructors.
    (memo, v0)
  Ast.AstVarHFunTKNew{} -> (memo, v0)

shareAstBool :: ShareMemo -> AstBool -> (ShareMemo, AstBool)
shareAstBool memo v0 = case v0 of
  Ast.AstBoolNot arg ->
    let (memo2, arg2) = shareAstBool memo arg
    in (memo2, Ast.AstBoolNot arg2)
  Ast.AstB2 opCodeBool arg1 arg2 ->
    let (memo1, b1) = shareAstBool memo arg1
        (memo2, b2) = shareAstBool memo1 arg2
    in (memo2, Ast.AstB2 opCodeBool b1 b2)
  Ast.AstBoolConst{} -> (memo, v0)
  Ast.AstRel opCodeRel arg1 arg2 ->
    let (memo1, r1) = shareAst memo arg1
        (memo2, r2) = shareAst memo1 arg2
    in (memo2, Ast.AstRel opCodeRel r1 r2)
  Ast.AstRelS opCodeRel arg1 arg2 ->
    let (memo1, r1) = shareAst memo arg1
        (memo2, r2) = shareAst memo1 arg2
    in (memo2, Ast.AstRelS opCodeRel r1 r2)
