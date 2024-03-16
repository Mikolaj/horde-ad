{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Inlining and other manipulations of the let-like constructors.
module HordeAd.Core.AstInline
  ( -- * Inlining and simplification pass operations to be applied after unlet
    simplifyArtifactRev
  , simplifyAst6, simplifyAst6S, simplifyAstHVector6
    -- * The unlet pass eliminating nested lets bottom-up
  , unletAstHVector6
  ) where

import Prelude

import           Control.Arrow (second)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import qualified Data.EnumMap.Strict as EM
import qualified Data.EnumSet as ES
import           Data.List (mapAccumR)
import           Data.Maybe (fromMaybe)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)

import           HordeAd.Core.Ast (AstBool, AstHVector, AstRanked, AstShaped)
import           HordeAd.Core.Ast hiding
  (AstBool (..), AstHVector (..), AstRanked (..), AstShaped (..))
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.HVector
import           HordeAd.Core.Types
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

-- * Inlining and simplification pass operations to be applied after unlet

simplifyArtifactRev
  :: AstArtifactRev (HVectorPseudoTensor (AstRanked PrimalSpan)) r y
  -> AstArtifactRev (HVectorPseudoTensor (AstRanked PrimalSpan)) r y
simplifyArtifactRev (vars, gradient, HVectorPseudoTensor primal) =
  ( vars, simplifyAstHVector6 gradient
  , HVectorPseudoTensor $ simplifyAstHVector6 primal)

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyAst6
  :: (GoodScalar r, KnownNat n, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
simplifyAst6 =
  snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst
{-# SPECIALIZE simplifyAst6
  :: (KnownNat n, AstSpan s)
  => AstRanked s Double n
  -> AstRanked s Double n #-}

simplifyAst6S
  :: (GoodScalar r, Sh.Shape sh, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
simplifyAst6S =
  snd . inlineAstS EM.empty
  . simplifyAstS . expandAstS
  . snd . inlineAstS EM.empty . simplifyAstS
{-# SPECIALIZE simplifyAst6S
  :: (Sh.Shape sh, AstSpan s)
  => AstShaped s Double sh
  -> AstShaped s Double sh #-}

simplifyAstHVector6
  :: AstSpan s => AstHVector s -> AstHVector s
simplifyAstHVector6 =
  snd . inlineAstHVector EM.empty
  . simplifyAstHVector . expandAstHVector
  . snd . inlineAstHVector EM.empty . simplifyAstHVector
    -- no specialization possible except for the tag type s


-- * The pass that inlines lets with the bottom-up strategy

type AstMemo = EM.EnumMap AstVarId Int

inlineAst
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => AstMemo
  -> AstRanked s r n -> (AstMemo, AstRanked s r n)
inlineAst memo v0 = case v0 of
  Ast.AstVar _ (AstVarName varId) ->
    let f Nothing = Just 1
        f (Just count) = Just $ succ count
    in (EM.alter f varId memo, v0)
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
      1 -> (memo2, substituteAst (SubstitutionPayloadRanked u2) var v2)
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
            memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
                      -- u is small, so the union is fast
        in (memo3, substituteAst (SubstitutionPayloadRanked u0) var v2)
      _ -> (memo2, Ast.AstLet var u2 v2)
  Ast.AstLetADShare{} -> error "inlineAst: AstLetADShare"
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
        count = sizeShape sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatter sh v2 (vars, listToIndex ix2))
  Ast.AstFromList l ->
    let (memo2, l2) = mapAccumR inlineAst memo l
    in (memo2, Ast.AstFromList l2)
  Ast.AstFromVector l ->
    let (memo2, l2) = mapAccumR inlineAst memo (V.toList l)
    in (memo2, Ast.AstFromVector $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstReplicate k v -> second (Ast.AstReplicate k) (inlineAst memo v)
  Ast.AstAppend x y ->
    let (memo1, t1) = inlineAst memo x
        (memo2, t2) = inlineAst memo1 y
    in (memo2, Ast.AstAppend t1 t2)
  Ast.AstSlice i k v -> second (Ast.AstSlice i k) (inlineAst memo v)
  Ast.AstReverse v -> second Ast.AstReverse (inlineAst memo v)
  Ast.AstTranspose perm v ->
    second (Ast.AstTranspose perm) $ inlineAst memo v
  Ast.AstReshape sh v -> second (Ast.AstReshape sh) (inlineAst memo v)
  Ast.AstBuild1 k (var, v) ->
    let (memoV0, v2) = inlineAst EM.empty v
        memo1 = EM.unionWith (\c1 c0 -> c1 + k * c0) memo memoV0
    in (memo1, Ast.AstBuild1 k (var, v2))
  Ast.AstGather sh v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty (indexToList ix)
        count = sizeShape sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGather sh v2 (vars, listToIndex ix2))
  Ast.AstCast v -> second Ast.AstCast $ inlineAst memo v
  Ast.AstFromIntegral v -> second Ast.AstFromIntegral $ inlineAst memo v
  Ast.AstConst{} -> (memo, v0)
  Ast.AstLetHVectorIn vars l v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, l2) = inlineAstHVector memo l
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
  Ast.AstRFromS v -> second Ast.AstRFromS $ inlineAstS memo v
  Ast.AstConstant a -> second Ast.AstConstant $ inlineAst memo a
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ inlineAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ inlineAst memo a
  Ast.AstD u u' ->
    let (memo1, t1) = inlineAst memo u
        (memo2, t2) = inlineAst memo1 u'
    in (memo2, Ast.AstD t1 t2)

inlineAstS
  :: forall sh s r. (GoodScalar r, Sh.Shape sh, AstSpan s)
  => AstMemo
  -> AstShaped s r sh -> (AstMemo, AstShaped s r sh)
inlineAstS memo v0 = case v0 of
  Ast.AstVarS (AstVarName varId) ->
    let f Nothing = Just 1
        f (Just count) = Just $ succ count
    in (EM.alter f varId memo, v0)
  Ast.AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let vv = varNameToAstVarId var
        (memo1, v2) = inlineAstS memo v
        memo1NoVar = EM.delete vv memo1
        (memo2, u2) = inlineAstS memo1NoVar u
    in case EM.findWithDefault 0 vv memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substituteAstS (SubstitutionPayloadShaped u2) var v2)
      count | astIsSmallS (count < 10) u ->
        let (memoU0, u0) = inlineAstS EM.empty u
            memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
                      -- u is small, so the union is fast
        in (memo3, substituteAstS (SubstitutionPayloadShaped u0) var v2)
      _ -> (memo2, Ast.AstLetS var u2 v2)
  Ast.AstLetADShareS{} -> error "inlineAstS: AstLetADShareS"
  Ast.AstCondS b a2 a3 ->
    -- This is a place where our inlining may increase code size
    -- by enlarging both branches due to not considering number of syntactic
    -- occurrences, but only dynamic occurrences. Tensor expressions
    -- in conditionals are problematic and special enough
    -- that we can let it be until problems are encountered in the wild.
    -- See https://github.com/VMatthijs/CHAD/blob/main/src/Count.hs#L88-L152.
    let (memo1, b1) = inlineAstBool memo b
        (memoA2, t2) = inlineAstS EM.empty a2
        (memoA3, t3) = inlineAstS EM.empty a3
        memo4 = EM.unionWith max memoA2 memoA3
        memo5 = EM.unionWith (+) memo1 memo4
    in (memo5, Ast.AstCondS b1 t2 t3)
  Ast.AstMinIndexS a -> second Ast.AstMinIndexS $ inlineAstS memo a
  Ast.AstMaxIndexS a -> second Ast.AstMaxIndexS $ inlineAstS memo a
  Ast.AstFloorS a -> second Ast.AstFloorS $ inlineAstS memo a
  Ast.AstIotaS -> (memo, v0)
  Ast.AstN1S opCode u ->
    let (memo2, u2) = inlineAstS memo u
    in (memo2, Ast.AstN1S opCode u2)
  Ast.AstN2S opCode u v ->
    let (memo2, u2) = inlineAstS memo u
        (memo3, v3) = inlineAstS memo2 v
    in (memo3, Ast.AstN2S opCode u2 v3)
  Ast.AstR1S opCode u ->
    let (memo2, u2) = inlineAstS memo u
    in (memo2, Ast.AstR1S opCode u2)
  Ast.AstR2S opCode u v ->
    let (memo2, u2) = inlineAstS memo u
        (memo3, v3) = inlineAstS memo2 v
    in (memo3, Ast.AstR2S opCode u2 v3)
  Ast.AstI2S opCode u v ->
    let (memo2, u2) = inlineAstS memo u
        (memo3, v3) = inlineAstS memo2 v
    in (memo3, Ast.AstI2S opCode u2 v3)
  Ast.AstSumOfListS args ->
    let (memo2, args2) = mapAccumR inlineAstS memo args
    in (memo2, Ast.AstSumOfListS args2)
  Ast.AstIndexS @sh1 v ix ->
    let (memo1, v2) = inlineAstS memo v
        (memo2, ix2) = mapAccumR inlineAst memo1
                                 (ShapedList.indexToList ix)
    in (memo2, Ast.AstIndexS @sh1 v2 (ShapedList.listToIndex ix2))
  Ast.AstSumS v -> second Ast.AstSumS (inlineAstS memo v)
  Ast.AstScatterS @sh2 @p v (vars, ix) ->
    let (memo1, v2) = inlineAstS memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty
                                  (ShapedList.indexToList ix)
        count = Sh.sizeT @sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatterS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstFromListS l ->
    let (memo2, l2) = mapAccumR inlineAstS memo l
    in (memo2, Ast.AstFromListS l2)
  Ast.AstFromVectorS l ->
    let (memo2, l2) = mapAccumR inlineAstS memo (V.toList l)
    in (memo2, Ast.AstFromVectorS $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstReplicateS v -> second Ast.AstReplicateS (inlineAstS memo v)
  Ast.AstAppendS x y ->
    let (memo1, t1) = inlineAstS memo x
        (memo2, t2) = inlineAstS memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (inlineAstS memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (inlineAstS memo v)
  Ast.AstTransposeS @perm v ->
    second (Ast.AstTransposeS @perm) $ inlineAstS memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (inlineAstS memo v)
  Ast.AstBuild1S @n (var, v) ->
    let (memoV0, v2) = inlineAstS EM.empty v
        memo1 = EM.unionWith (\c1 c0 -> c1 + valueOf @n * c0) memo memoV0
    in (memo1, Ast.AstBuild1S (var, v2))
  Ast.AstGatherS @sh2 @p v (vars, ix) ->
    let (memo1, v2) = inlineAstS memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty
                                  (ShapedList.indexToList ix)
        count = Sh.sizeT @sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGatherS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ inlineAstS memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ inlineAstS memo v
  Ast.AstConstS{} -> (memo, v0)
  Ast.AstLetHVectorInS vars l v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, l2) = inlineAstHVector memo l
        (memo2, v2) = inlineAstS memo1 v
    in (memo2, Ast.AstLetHVectorInS vars l2 v2)
  Ast.AstLetHFunInS var f v ->
    -- We assume there are no nested lets with the same variable.
    -- We assume functions are never small enough to justify inlining
    -- into more than one place.
    let (memo1, v2) = inlineAstS memo v
        (memo2, f2) = inlineAstHFun memo1 f
    in case EM.findWithDefault 0 var memo2 of
      0 -> (memo1, v2)
      1 -> (memo2, fromMaybe v2 $ substitute1AstS
                                    (SubstitutionPayloadHFun f2) var v2)
      _ -> (memo2, Ast.AstLetHFunInS var f2 v2)
  Ast.AstSFromR v -> second Ast.AstSFromR $ inlineAst memo v
  Ast.AstConstantS a -> second Ast.AstConstantS $ inlineAstS memo a
  Ast.AstPrimalPartS a -> second Ast.AstPrimalPartS $ inlineAstS memo a
  Ast.AstDualPartS a -> second Ast.AstDualPartS $ inlineAstS memo a
  Ast.AstDS u u' ->
    let (memo1, t1) = inlineAstS memo u
        (memo2, t2) = inlineAstS memo1 u'
    in (memo2, Ast.AstDS t1 t2)

inlineAstDynamic
  :: AstSpan s
  => AstMemo -> AstDynamic s
  -> (AstMemo, AstDynamic s)
inlineAstDynamic memo = \case
  DynamicRanked w -> second DynamicRanked $ inlineAst memo w
  DynamicShaped w -> second DynamicShaped $ inlineAstS memo w
  u@DynamicRankedDummy{} -> (memo, u)
  u@DynamicShapedDummy{} -> (memo, u)

inlineAstHVector
  :: forall s. AstSpan s
  => AstMemo -> AstHVector s -> (AstMemo, AstHVector s)
inlineAstHVector memo v0 = case v0 of
  Ast.AstMkHVector l ->
    second Ast.AstMkHVector $ mapAccumR inlineAstDynamic memo l
  Ast.AstHApply t ll ->
    let (memo1, t2) = inlineAstHFun memo t
        (memo2, ll2) = mapAccumR (mapAccumR inlineAstDynamic) memo1 ll
    in (memo2, Ast.AstHApply t2 ll2)
  Ast.AstLetHVectorInHVector vars u v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, u2) = inlineAstHVector memo u
        (memo2, v2) = inlineAstHVector memo1 v
    in (memo2, Ast.AstLetHVectorInHVector vars u2 v2)
  Ast.AstLetHFunInHVector var f v ->
    -- We assume there are no nested lets with the same variable.
    -- We assume functions are never small enough to justify inlining
    -- into more than one place.
    let (memo1, v2) = inlineAstHVector memo v
        (memo2, f2) = inlineAstHFun memo1 f
    in case EM.findWithDefault 0 var memo2 of
      0 -> (memo1, v2)
      1 -> (memo2, fromMaybe v2 $ substitute1AstHVector
                                    (SubstitutionPayloadHFun f2) var v2)
      _ -> (memo2, Ast.AstLetHFunInHVector var f2 v2)
  Ast.AstLetInHVector var u v ->
    -- We assume there are no nested lets with the same variable.
    let vv = varNameToAstVarId var
        (memo1, v2) = inlineAstHVector memo v
        memo1NoVar = EM.delete vv memo1
        (memo2, u2) = inlineAst memo1NoVar u
    in case EM.findWithDefault 0 vv memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substituteAstHVector (SubstitutionPayloadRanked u2) var v2)
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
        in ( EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
               -- u is small, so the union is fast
           , substituteAstHVector (SubstitutionPayloadRanked u0) var v2 )
      _ -> (memo2, Ast.AstLetInHVector var u2 v2)
  Ast.AstLetInHVectorS var u v ->
    -- We assume there are no nested lets with the same variable.
    let vv = varNameToAstVarId var
        (memo1, v2) = inlineAstHVector memo v
        memo1NoVar = EM.delete vv memo1
        (memo2, u2) = inlineAstS memo1NoVar u
    in case EM.findWithDefault 0 vv memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substituteAstHVector (SubstitutionPayloadShaped u2) var v2)
      count | astIsSmallS (count < 10) u ->
        let (memoU0, u0) = inlineAstS EM.empty u
        in ( EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
               -- u is small, so the union is fast
           , substituteAstHVector (SubstitutionPayloadShaped u0) var v2 )
      _ -> (memo2, Ast.AstLetInHVectorS var u2 v2)
  Ast.AstBuildHVector1 k (var, v) ->
    let (memoV0, v2) = inlineAstHVector EM.empty v
        memo1 = EM.unionWith (\c1 c0 -> c1 + sNatValue k * c0) memo memoV0
    in (memo1, Ast.AstBuildHVector1 k (var, v2))
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFun memo f
        (memo2, df2) = inlineAstHFun memo1 df
        (memo3, rf2) = inlineAstHFun memo2 rf
        (memo4, acc02) = inlineAstHVector memo3 acc0
        (memo5, es2) = inlineAstHVector memo4 es
    in (memo5, Ast.AstMapAccumRDer k accShs bShs eShs f2 df2 rf2 acc02 es2)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFun memo f
        (memo2, df2) = inlineAstHFun memo1 df
        (memo3, rf2) = inlineAstHFun memo2 rf
        (memo4, acc02) = inlineAstHVector memo3 acc0
        (memo5, es2) = inlineAstHVector memo4 es
    in (memo5, Ast.AstMapAccumLDer k accShs bShs eShs f2 df2 rf2 acc02 es2)

inlineAstHFun
  :: AstMemo -> AstHFun -> (AstMemo, AstHFun)
inlineAstHFun memo v0 = case v0 of
  Ast.AstLambda ~(vvars, l) ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards.
    (memo, Ast.AstLambda (vvars, snd $ inlineAstHVector EM.empty l))
  Ast.AstVarHFun _shss _shs var ->
    let f Nothing = Just 1
        f (Just count) = Just $ succ count
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
    let (memo1, r1) = inlineAstS memo arg1
        (memo2, r2) = inlineAstS memo1 arg2
    in (memo2, Ast.AstRelS opCodeRel r1 r2)


-- * The unlet pass eliminating nested duplicated lets bottom-up

data UnletEnv = UnletEnv
  { unletSet     :: ES.EnumSet AstVarId
  , unletADShare :: ADShare }

emptyUnletEnv :: ADShare -> UnletEnv
emptyUnletEnv = UnletEnv ES.empty

unletAstHVector6
  :: ADShare -> AstBindings -> AstHVector PrimalSpan
  -> AstHVector PrimalSpan
unletAstHVector6 l astBindings t =
  unletAstHVector (emptyUnletEnv l)
  $ bindsToHVectorLet (bindsToHVectorLet t astBindings) (assocsADShare l)

-- TODO: if a nested let is alone, eliminate the nesting let instead;
-- this probably requires many passes though
unletAst
  :: (GoodScalar r, KnownNat n, AstSpan s)
  => UnletEnv -> AstRanked s r n -> AstRanked s r n
unletAst env t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v ->
    -- This optimization is sound, because there is no mechanism
    -- that would nest lets with the same variable (e.g., our lets always
    -- bind fresh variables at creation time and we never substitute
    -- a term into the same term). If that changes, let's refresh
    -- let variables whenever substituting into let bodies.
    -- See the same assumption in AstInterpret.
    let vv = varNameToAstVarId var
    in if vv `ES.member` unletSet env
       then unletAst env v
       else let env2 = env {unletSet = ES.insert vv (unletSet env)}
            in Ast.AstLet var (unletAst env u) (unletAst env2 v)
  Ast.AstLetADShare l v ->
    let lassocs = subtractADShare l $ unletADShare env
          -- potentially prevents quadratic cost induced by rletWrap
          -- duplicating the global ADShare; may induce overhead when
          -- the same lets are verified for removal twice, in subtractADShare
          -- and via unletAst, but if many lets can be eliminated,
          -- subtractADShare does it much faster
    in unletAst env $ bindsToLet v lassocs
  Ast.AstCond b a1 a2 ->
    Ast.AstCond
      (unletAstBool env b) (unletAst env a1) (unletAst env a2)
  Ast.AstMinIndex a -> Ast.AstMinIndex $ unletAst env a
  Ast.AstMaxIndex a -> Ast.AstMaxIndex $ unletAst env a
  Ast.AstFloor a -> Ast.AstFloor $ unletAst env a
  Ast.AstIota -> t
  Ast.AstN1 opCode u -> Ast.AstN1 opCode (unletAst env u)
  Ast.AstN2 opCode u v -> Ast.AstN2 opCode (unletAst env u) (unletAst env v)
  Ast.AstR1 opCode u -> Ast.AstR1 opCode (unletAst env u)
  Ast.AstR2 opCode u v -> Ast.AstR2 opCode (unletAst env u) (unletAst env v)
  Ast.AstI2 opCode u v -> Ast.AstI2 opCode (unletAst env u) (unletAst env v)
  Ast.AstSumOfList args -> Ast.AstSumOfList (map (unletAst env) args)
  Ast.AstIndex v ix ->
    Ast.AstIndex (unletAst env v) (fmap (unletAst env) ix)
  Ast.AstSum v -> Ast.AstSum (unletAst env v)
  Ast.AstScatter sh v (var, ix) ->
    Ast.AstScatter sh (unletAst env v) (var, fmap (unletAst env) ix)
  Ast.AstFromList l -> Ast.AstFromList (map (unletAst env) l)
  Ast.AstFromVector l -> Ast.AstFromVector (V.map (unletAst env) l)
  Ast.AstReplicate k v -> Ast.AstReplicate k (unletAst env v)
  Ast.AstAppend x y -> Ast.AstAppend (unletAst env x) (unletAst env y)
  Ast.AstSlice i k v -> Ast.AstSlice i k (unletAst env v)
  Ast.AstReverse v -> Ast.AstReverse (unletAst env v)
  Ast.AstTranspose perm v -> Ast.AstTranspose perm (unletAst env v)
  Ast.AstReshape sh v -> Ast.AstReshape sh (unletAst env v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, unletAst env v)
  Ast.AstGather sh v (vars, ix) ->
    Ast.AstGather sh (unletAst env v) (vars, fmap (unletAst env) ix)
  Ast.AstCast v -> Ast.AstCast (unletAst env v)
  Ast.AstFromIntegral v -> Ast.AstFromIntegral (unletAst env v)
  Ast.AstConst{} -> t
  Ast.AstLetHVectorIn vars l v -> case vars of
    [] -> error "unletAst: empty hVector"
    var : _ ->  -- vars are fresh, so var uniquely represent vars
      let vv = dynamicVarNameToAstVarId var
      in if vv `ES.member` unletSet env
         then unletAst env v
         else let env2 = env {unletSet = ES.insert vv (unletSet env)}
              in Ast.AstLetHVectorIn
                   vars (unletAstHVector env l) (unletAst env2 v)
  Ast.AstLetHFunIn var f v ->
    if var `ES.member` unletSet env
    then unletAst env v
    else let env2 = env {unletSet = ES.insert var (unletSet env)}
         in Ast.AstLetHFunIn var (unletAstHFun f) (unletAst env2 v)
  Ast.AstRFromS v -> Ast.AstRFromS (unletAstS env v)
  Ast.AstConstant v -> Ast.AstConstant (unletAst env v)
  Ast.AstPrimalPart v -> Ast.AstPrimalPart (unletAst env v)
  Ast.AstDualPart v -> Ast.AstDualPart (unletAst env v)
  Ast.AstD u u' -> Ast.AstD (unletAst env u) (unletAst env u')

unletAstS
  :: (GoodScalar r, Sh.Shape sh, AstSpan s)
  => UnletEnv -> AstShaped s r sh -> AstShaped s r sh
unletAstS env t = case t of
  Ast.AstVarS{} -> t
  Ast.AstLetS var u v ->
    -- This optimization is sound, because there is no mechanism
    -- that would nest lets with the same variable (e.g., our lets always
    -- bind fresh variables at creation time and we never substitute
    -- a term into the same term). If that changes, let's refresh
    -- let variables whenever substituting into let bodies.
    -- See the same assumption in AstInterpret.
    let vv = varNameToAstVarId var
    in if vv `ES.member` unletSet env
       then unletAstS env v
       else let env2 = env {unletSet = ES.insert vv (unletSet env)}
            in Ast.AstLetS var (unletAstS env u) (unletAstS env2 v)
  Ast.AstLetADShareS l v ->
    let lassocs = subtractADShare l $ unletADShare env
          -- potentially prevents quadratic cost induced by rletWrap
          -- duplicating the global ADShare; may induce overhead when
          -- the same lets are verified for removal twice, in subtractADShare
          -- and via unletAst, but if many lets can be eliminated,
          -- subtractADShare does it much faster
    in unletAstS env $ bindsToLetS v lassocs
  Ast.AstCondS b a1 a2 ->
    Ast.AstCondS
      (unletAstBool env b) (unletAstS env a1) (unletAstS env a2)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS $ unletAstS env a
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS $ unletAstS env a
  Ast.AstFloorS a -> Ast.AstFloorS $ unletAstS env a
  Ast.AstIotaS -> t
  Ast.AstN1S opCode u -> Ast.AstN1S opCode (unletAstS env u)
  Ast.AstN2S opCode u v -> Ast.AstN2S opCode (unletAstS env u) (unletAstS env v)
  Ast.AstR1S opCode u -> Ast.AstR1S opCode (unletAstS env u)
  Ast.AstR2S opCode u v -> Ast.AstR2S opCode (unletAstS env u) (unletAstS env v)
  Ast.AstI2S opCode u v -> Ast.AstI2S opCode (unletAstS env u) (unletAstS env v)
  Ast.AstSumOfListS args -> Ast.AstSumOfListS (map (unletAstS env) args)
  Ast.AstIndexS v ix ->
    Ast.AstIndexS (unletAstS env v) (fmap (unletAst env) ix)
  Ast.AstSumS v -> Ast.AstSumS (unletAstS env v)
  Ast.AstScatterS v (var, ix) ->
    Ast.AstScatterS (unletAstS env v) (var, fmap (unletAst env) ix)
  Ast.AstFromListS l -> Ast.AstFromListS (map (unletAstS env) l)
  Ast.AstFromVectorS l -> Ast.AstFromVectorS (V.map (unletAstS env) l)
  Ast.AstReplicateS v -> Ast.AstReplicateS (unletAstS env v)
  Ast.AstAppendS x y -> Ast.AstAppendS (unletAstS env x) (unletAstS env y)
  Ast.AstSliceS @i v -> Ast.AstSliceS @i (unletAstS env v)
  Ast.AstReverseS v -> Ast.AstReverseS (unletAstS env v)
  Ast.AstTransposeS @perm v -> Ast.AstTransposeS @perm (unletAstS env v)
  Ast.AstReshapeS v -> Ast.AstReshapeS (unletAstS env v)
  Ast.AstBuild1S (var, v) -> Ast.AstBuild1S (var, unletAstS env v)
  Ast.AstGatherS v (vars, ix) ->
    Ast.AstGatherS (unletAstS env v) (vars, fmap (unletAst env) ix)
  Ast.AstCastS v -> Ast.AstCastS (unletAstS env v)
  Ast.AstFromIntegralS v -> Ast.AstFromIntegralS (unletAstS env v)
  Ast.AstConstS{} -> t
  Ast.AstLetHVectorInS vars l v -> case vars of
    [] -> error "unletAstS: empty hVector"
    var : _ ->  -- vars are fresh, so var uniquely represent vars
      let vv = dynamicVarNameToAstVarId var
      in if vv `ES.member` unletSet env
         then unletAstS env v
         else let env2 = env {unletSet = ES.insert vv (unletSet env)}
              in Ast.AstLetHVectorInS
                   vars (unletAstHVector env l) (unletAstS env2 v)
  Ast.AstLetHFunInS var f v ->
    if var `ES.member` unletSet env
    then unletAstS env v
    else let env2 = env {unletSet = ES.insert var (unletSet env)}
         in Ast.AstLetHFunInS var (unletAstHFun f) (unletAstS env2 v)
  Ast.AstSFromR v -> Ast.AstSFromR (unletAst env v)
  Ast.AstConstantS v -> Ast.AstConstantS (unletAstS env v)
  Ast.AstPrimalPartS v -> Ast.AstPrimalPartS (unletAstS env v)
  Ast.AstDualPartS v -> Ast.AstDualPartS (unletAstS env v)
  Ast.AstDS u u' -> Ast.AstDS (unletAstS env u) (unletAstS env u')

unletAstDynamic
  :: AstSpan s
  => UnletEnv -> AstDynamic s -> AstDynamic s
unletAstDynamic env = \case
  DynamicRanked u -> DynamicRanked $ unletAst env u
  DynamicShaped u -> DynamicShaped $ unletAstS env u
  u@DynamicRankedDummy{} -> u
  u@DynamicShapedDummy{} -> u

unletAstHVector
  :: AstSpan s => UnletEnv -> AstHVector s -> AstHVector s
unletAstHVector env = \case
  Ast.AstMkHVector l -> Ast.AstMkHVector $ V.map (unletAstDynamic env) l
  Ast.AstHApply t ll -> Ast.AstHApply (unletAstHFun t)
                                      (map (V.map (unletAstDynamic env)) ll)
  Ast.AstLetHVectorInHVector vars u v -> case vars of
    [] -> error "unletAstHVector: empty hVector"
    var : _ ->  -- vars are fresh, so var uniquely represent vars
      let vv = dynamicVarNameToAstVarId var
      in if vv `ES.member` unletSet env
         then unletAstHVector env v
         else let env2 = env {unletSet = ES.insert vv (unletSet env)}
              in Ast.AstLetHVectorInHVector
                   vars (unletAstHVector env u) (unletAstHVector env2 v)
  Ast.AstLetHFunInHVector var f v ->
    if var `ES.member` unletSet env
    then unletAstHVector env v
    else let env2 = env {unletSet = ES.insert var (unletSet env)}
         in Ast.AstLetHFunInHVector var (unletAstHFun f)
                                        (unletAstHVector env2 v)
  Ast.AstLetInHVector var u v ->
    let vv = varNameToAstVarId var
    in if vv `ES.member` unletSet env
      then unletAstHVector env v
      else let env2 = env {unletSet = ES.insert vv (unletSet env)}
           in Ast.AstLetInHVector var (unletAst env u)
                                      (unletAstHVector env2 v)
  Ast.AstLetInHVectorS var u v ->
    let vv = varNameToAstVarId var
    in if vv `ES.member` unletSet env
       then unletAstHVector env v
       else let env2 = env {unletSet = ES.insert vv (unletSet env)}
            in Ast.AstLetInHVectorS var (unletAstS env u)
                                        (unletAstHVector env2 v)
  Ast.AstBuildHVector1 k (var, v) ->
    Ast.AstBuildHVector1 k (var, unletAstHVector env v)
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    Ast.AstMapAccumRDer k accShs bShs eShs f df rf
                        (unletAstHVector env acc0)
                        (unletAstHVector env es)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    Ast.AstMapAccumLDer k accShs bShs eShs f df rf
                        (unletAstHVector env acc0)
                        (unletAstHVector env es)

unletAstHFun :: AstHFun -> AstHFun
unletAstHFun = \case
  Ast.AstLambda ~(vvars, l) ->
    Ast.AstLambda (vvars, unletAstHVector (emptyUnletEnv emptyADShare) l)
      -- No other free variables in l, so no outside lets can reach there.
  t@(Ast.AstVarHFun{}) -> t

unletAstBool :: UnletEnv -> AstBool -> AstBool
unletAstBool env t = case t of
  Ast.AstBoolNot arg -> Ast.AstBoolNot $ unletAstBool env arg
  Ast.AstB2 opCodeBool arg1 arg2 ->
    Ast.AstB2 opCodeBool (unletAstBool env arg1) (unletAstBool env arg2)
  Ast.AstBoolConst{} -> t
  Ast.AstRel opCodeRel arg1 arg2 ->
    Ast.AstRel opCodeRel (unletAst env arg1) (unletAst env arg2)
  Ast.AstRelS opCodeRel arg1 arg2 ->
    Ast.AstRelS opCodeRel (unletAstS env arg1) (unletAstS env arg2)
