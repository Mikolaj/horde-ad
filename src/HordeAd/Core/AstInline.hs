{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Inlining and global sharing elimination.
module HordeAd.Core.AstInline
  ( -- * The joint inlining and simplification term transformation
    simplifyArtifact, simplifyInlineAst, simplifyInlineAstS
  , simplifyInlineHVector, simplifyInlineHVectorRaw
    -- * The translates global sharing to normal lets
  , unletAstHVector
  ) where

import Prelude

import Control.Arrow (second)
import Data.Array.Internal (valueOf)
import Data.EnumMap.Strict qualified as EM
import Data.List (mapAccumR)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat)
import Type.Reflection (typeRep)

import HordeAd.Core.Ast hiding (AstBool (..), AstHVector (..), AstTensor (..))
import HordeAd.Core.Ast (AstBool, AstHVector, AstTensor)
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * The joint inlining and simplification term transformation

simplifyArtifact :: AstArtifact -> AstArtifact
simplifyArtifact art =
  art { artDerivative = simplifyInlineHVectorRaw $ artDerivative art
      , artPrimal = simplifyInlineHVectorRaw $ artPrimal art }

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyInlineAst
  :: forall r n s. AstSpan s
  => AstRanked s r n -> AstRanked s r n
simplifyInlineAst =
  AstRanked . snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst . unAstRanked
{-# SPECIALIZE simplifyInlineAst
  :: AstSpan s
  => AstRanked s Double n -> AstRanked s Double n #-}

simplifyInlineAstS
  :: forall r sh s. AstSpan s
  => AstShaped s r sh -> AstShaped s r sh
simplifyInlineAstS =
  AstShaped . snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst . unAstShaped
{-# SPECIALIZE simplifyInlineAstS
  :: AstSpan s
  => AstShaped s Double sh -> AstShaped s Double sh #-}

simplifyInlineHVector
  :: AstSpan s => AstHVector s -> AstHVector s
simplifyInlineHVector =
  snd . inlineAstHVector EM.empty
  . simplifyAstHVector . expandAstHVector
  . snd . inlineAstHVector EM.empty . simplifyAstHVector
    -- no specialization possible except for the tag type s

simplifyInlineHVectorRaw
  :: AstSpan s => AstRawWrap (AstHVector s) -> AstRawWrap (AstHVector s)
simplifyInlineHVectorRaw =
  AstRawWrap . simplifyInlineHVector . unAstRawWrap


-- * The pass that inlines lets with the bottom-up strategy

type AstMemo = EM.EnumMap AstVarId Int

inlineAst
  :: forall s y. AstSpan s
  => AstMemo -> AstTensor s y -> (AstMemo, AstTensor s y)
inlineAst memo v0 = case v0 of
  Ast.AstPair t1 t2 ->
    let (memo2, v1) = inlineAst memo t1
        (memo3, v2) = inlineAst memo2 t2
    in (memo3, Ast.AstPair v1 v2)
  Ast.AstLetPairIn var1 var2 p v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    -- TODO: check if we should do more, e.g., when p is AstPair (but maybe
    -- simplification should rewrite that to normal lets instead?).
    let (memo1, p2) = inlineAst memo p
        (memo2, v2) = inlineAst memo1 v
    in (memo2, Ast.AstLetPairIn var1 var2 p2 v2)

  Ast.AstVar _ var ->
    let f Nothing = Just 1
        f (Just count) = Just $ succ count
    in (EM.alter f (varNameToAstVarId var) memo, v0)
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
  Ast.AstShare{} -> error "inlineAst: AstShare"
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
  Ast.AstProject l p ->
    let (memo1, l2) = inlineAstHVector memo l
    in (memo1, Ast.AstProject l2 p)
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
  Ast.AstRFromS v -> second Ast.AstRFromS $ inlineAst memo v
  Ast.AstConstant a -> second Ast.AstConstant $ inlineAst memo a
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ inlineAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ inlineAst memo a
  Ast.AstD u u' ->
    let (memo1, t1) = inlineAst memo u
        (memo2, t2) = inlineAst memo1 u'
    in (memo2, Ast.AstD t1 t2)

  Ast.AstVarS var ->
    let f Nothing = Just 1
        f (Just count) = Just $ succ count
    in (EM.alter f (varNameToAstVarId var) memo, v0)
  Ast.AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let vv = varNameToAstVarId var
        (memo1, v2) = inlineAst memo v
        memo1NoVar = EM.delete vv memo1
        (memo2, u2) = inlineAst memo1NoVar u
    in case EM.findWithDefault 0 vv memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substituteAst (SubstitutionPayloadShaped u2) var v2)
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
            memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
                      -- u is small, so the union is fast
        in (memo3, substituteAst (SubstitutionPayloadShaped u0) var v2)
      _ -> (memo2, Ast.AstLetS var u2 v2)
  Ast.AstShareS{} -> error "inlineAst: AstShareS"
  Ast.AstCondS b a2 a3 ->
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
    in (memo5, Ast.AstCondS b1 t2 t3)
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
        count = sizeT @sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatterS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstFromVectorS l ->
    let (memo2, l2) = mapAccumR inlineAst memo (V.toList l)
    in (memo2, Ast.AstFromVectorS $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstReplicateS v -> second Ast.AstReplicateS (inlineAst memo v)
  Ast.AstAppendS x y ->
    let (memo1, t1) = inlineAst memo x
        (memo2, t2) = inlineAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (inlineAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (inlineAst memo v)
  Ast.AstTransposeS perm v ->
    second (Ast.AstTransposeS perm) $ inlineAst memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (inlineAst memo v)
  Ast.AstBuild1S @_ @n (var, v) ->
    let (memoV0, v2) = inlineAst EM.empty v
        memo1 = EM.unionWith (\c1 c0 -> c1 + valueOf @n * c0) memo memoV0
    in (memo1, Ast.AstBuild1S (var, v2))
  Ast.AstGatherS @sh2 @p @sh v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty
                                  (ShapedList.indexToList ix)
        count = sizeT @sh2 + sizeT @sh - valueOf @p
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGatherS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ inlineAst memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ inlineAst memo v
  Ast.AstConstS{} -> (memo, v0)
  Ast.AstProjectS l p ->
    let (memo1, l2) = inlineAstHVector memo l
    in (memo1, Ast.AstProjectS l2 p)
  Ast.AstLetHVectorInS vars l v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, l2) = inlineAstHVector memo l
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
  Ast.AstSFromR v -> second Ast.AstSFromR $ inlineAst memo v
  Ast.AstConstantS a -> second Ast.AstConstantS $ inlineAst memo a
  Ast.AstPrimalPartS a -> second Ast.AstPrimalPartS $ inlineAst memo a
  Ast.AstDualPartS a -> second Ast.AstDualPartS $ inlineAst memo a
  Ast.AstDS u u' ->
    let (memo1, t1) = inlineAst memo u
        (memo2, t2) = inlineAst memo1 u'
    in (memo2, Ast.AstDS t1 t2)

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
        (memo2, u2) = inlineAst memo1NoVar u
    in case EM.findWithDefault 0 vv memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substituteAstHVector (SubstitutionPayloadShaped u2) var v2)
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
        in ( EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
               -- u is small, so the union is fast
           , substituteAstHVector (SubstitutionPayloadShaped u0) var v2 )
      _ -> (memo2, Ast.AstLetInHVectorS var u2 v2)
  Ast.AstShareHVector{} -> error "inlineAstHVector: AstShareHVector"
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
    let (memo1, r1) = inlineAst memo arg1
        (memo2, r2) = inlineAst memo1 arg2
    in (memo2, Ast.AstRelS opCodeRel r1 r2)


-- * The translates global sharing to normal lets

unletAstHVector :: AstHVector PrimalSpan -> AstHVector PrimalSpan
unletAstHVector t =
  let (memoOut, share) = shareAstHVector EM.empty t
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
  in (EM.union memo0 memoGlobal1, unAstRanked $ bindsToLet (AstRanked v1) bindingsLocal)

shareAst
  :: forall s y. AstSpan s
  => ShareMemo -> AstTensor s y -> (ShareMemo, AstTensor s y)
shareAst memo v0 = case v0 of
  Ast.AstPair t1 t2 ->
    let (memo1, v1) = shareAst memo t1
        (memo2, v2) = shareAst memo1 t2
    in (memo2, Ast.AstPair v1 v2)
  Ast.AstLetPairIn{} -> (memo, v0)
    -- delta eval doesn't create lets and no lets
    -- survive instantiating in ADVal

  Ast.AstVar{} -> (memo, v0)
  Ast.AstLet{} -> (memo, v0)
  Ast.AstShare var v | Just Refl <- sameAstSpan @s @PrimalSpan ->
    -- We assume v is the same if var is the same.
    let varId = varNameToAstVarId var
        astVar = Ast.AstVar (shapeAst v) var
    in if varId `EM.member` memo
       then (memo, astVar)  -- TODO: memo AstVar
       else let (memo1, v2) = shareAst memo v
                d = AstBindingsSimple $ DynamicRanked $ AstRanked v2
            in (EM.insert varId d memo1, astVar)
  Ast.AstShare{} -> error "shareAst: AstShare not in PrimalSpan"
  Ast.AstCond b a2 a3 ->
    let (memo1, b1) = shareAstBool memo b
        (memo2, t2) = shareAst memo1 a2
        (memo3, t3) = shareAst memo2 a3
    in (memo3, Ast.AstCond b1 t2 t3)
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
  Ast.AstReplicate k v -> second (Ast.AstReplicate k) (shareAst memo v)
  Ast.AstAppend x y ->
    let (memo1, t1) = shareAst memo x
        (memo2, t2) = shareAst memo1 y
    in (memo2, Ast.AstAppend t1 t2)
  Ast.AstSlice i k v -> second (Ast.AstSlice i k) (shareAst memo v)
  Ast.AstReverse v -> second Ast.AstReverse (shareAst memo v)
  Ast.AstTranspose perm v ->
    second (Ast.AstTranspose perm) $ shareAst memo v
  Ast.AstReshape sh v -> second (Ast.AstReshape sh) (shareAst memo v)
  Ast.AstBuild1 k (var, v) ->
    let (memo1, v2) = shareAstScoped [var] memo v
    in (memo1, Ast.AstBuild1 k (var, v2))
  Ast.AstGather sh v (vars, ix) ->
    let (memo1, ix2) = mapAccumR (shareAstScoped $ sizedToList vars)
                                 memo (indexToList ix)
        (memo2, v2) = shareAst memo1 v
    in (memo2, Ast.AstGather sh v2 (vars, listToIndex ix2))
  Ast.AstCast v -> second Ast.AstCast $ shareAst memo v
  Ast.AstFromIntegral v -> second Ast.AstFromIntegral $ shareAst memo v
  Ast.AstConst{} -> (memo, v0)
  Ast.AstProject l p ->
    -- This doesn't get simplified even if l is an HVector of vars freshly
    -- created by shareAstHVector. However, then l is shared, so the cost
    -- per AstProject is only slightly (2 words? 1 indirection?)
    -- higher than if simplified.
    let (memo1, l2) = shareAstHVector memo l
    in (memo1, Ast.AstProject l2 p)
  Ast.AstLetHVectorIn{} -> (memo, v0)
  Ast.AstLetHFunIn{} -> (memo, v0)
  Ast.AstRFromS v -> second Ast.AstRFromS $ shareAst memo v
  Ast.AstConstant a -> second Ast.AstConstant $ shareAst memo a
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ shareAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ shareAst memo a
  Ast.AstD u u' ->
    let (memo1, t1) = shareAst memo u
        (memo2, t2) = shareAst memo1 u'
    in (memo2, Ast.AstD t1 t2)

  Ast.AstVarS{} -> (memo, v0)
  Ast.AstLetS{} -> (memo, v0)
  Ast.AstShareS var v | Just Refl <- sameAstSpan @s @PrimalSpan ->
    -- We assume v is the same if var is the same.
    let varId = varNameToAstVarId var
        astVar = Ast.AstVarS var
    in if varId `EM.member` memo
       then (memo, astVar)
       else let (memo1, v2) = shareAst memo v
                d = AstBindingsSimple $ DynamicShaped $ AstShaped v2
            in (EM.insert varId d memo1, astVar)
  Ast.AstShareS{} -> error "shareAst: AstShareS not in PrimalSpan"
  Ast.AstCondS b a2 a3 ->
    let (memo1, b1) = shareAstBool memo b
        (memo2, t2) = shareAst memo1 a2
        (memo3, t3) = shareAst memo2 a3
    in (memo3, Ast.AstCondS b1 t2 t3)
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
  Ast.AstReplicateS v -> second Ast.AstReplicateS (shareAst memo v)
  Ast.AstAppendS x y ->
    let (memo1, t1) = shareAst memo x
        (memo2, t2) = shareAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (shareAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (shareAst memo v)
  Ast.AstTransposeS perm v ->
    second (Ast.AstTransposeS perm) $ shareAst memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (shareAst memo v)
  Ast.AstBuild1S{} -> error "shareAst: AstBuild1S"  -- not hard to add
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
    let (memo1, l2) = shareAstHVector memo l
    in (memo1, Ast.AstProjectS l2 p)
  Ast.AstLetHVectorInS{} -> (memo, v0)
  Ast.AstLetHFunInS{} -> (memo, v0)
  Ast.AstSFromR v -> second Ast.AstSFromR $ shareAst memo v
  Ast.AstConstantS a -> second Ast.AstConstantS $ shareAst memo a
  Ast.AstPrimalPartS a -> second Ast.AstPrimalPartS $ shareAst memo a
  Ast.AstDualPartS a -> second Ast.AstDualPartS $ shareAst memo a
  Ast.AstDS u u' ->
    let (memo1, t1) = shareAst memo u
        (memo2, t2) = shareAst memo1 u'
    in (memo2, Ast.AstDS t1 t2)

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

shareAstHVector
  :: forall s. AstSpan s
  => ShareMemo -> AstHVector s -> (ShareMemo, AstHVector s)
shareAstHVector memo v0 = case v0 of
  Ast.AstMkHVector l ->
    second Ast.AstMkHVector $ mapAccumR shareAstDynamic memo l
  Ast.AstHApply t ll ->
    let (memo1, t2) = shareAstHFun memo t
        (memo2, ll2) = mapAccumR (mapAccumR shareAstDynamic) memo1 ll
    in (memo2, Ast.AstHApply t2 ll2)
  Ast.AstLetHVectorInHVector{} -> (memo, v0)
  Ast.AstLetHFunInHVector{} -> (memo, v0)
  Ast.AstLetInHVector{} -> (memo, v0)
  Ast.AstLetInHVectorS{} -> (memo, v0)
  Ast.AstShareHVector [] l -> (memo, l)  -- no need to share an empty HVector
  Ast.AstShareHVector vars l | Just Refl <- sameAstSpan @s @PrimalSpan ->
    -- We assume l is the same if vars are the same.
    let var = vars !! 0  -- vars are fresh, so var uniquely represents vars
        varId = dynamicVarNameToAstVarId var
        f :: AstDynamicVarName -> DynamicTensor (AstRanked PrimalSpan)
        f (AstDynamicVarName @ty @rD @shD varIdD) =
          case testEquality (typeRep @ty) (typeRep @Nat) of
            Just Refl -> withListSh (Proxy @shD) $ \sh ->
              DynamicRanked @rD $ AstRanked $ Ast.AstVar sh (mkAstVarName (length sh) varIdD)
            _ -> DynamicShaped @rD @shD $ AstShaped $ Ast.AstVarS (mkAstVarName (length (shapeT @shD)) varIdD)
        astVars = Ast.AstMkHVector $ V.fromList $ map f vars
    in if varId `EM.member` memo
       then (memo, astVars)
       else let (memo1, l2) = shareAstHVector memo l
                d = AstBindingsHVector vars l2
            in (EM.insert varId d memo1, astVars)
  Ast.AstShareHVector{} ->
    error "shareAstHVector: AstShareHVector not in PrimalSpan"
  Ast.AstBuildHVector1{} -> error "shareAst: AstBuild1S"  -- not hard to add
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = shareAstHVector memo acc0
        (memo2, es2) = shareAstHVector memo1 es
    in (memo2, Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc02 es2)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = shareAstHVector memo acc0
        (memo2, es2) = shareAstHVector memo1 es
    in (memo2, Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc02 es2)

shareAstHFun
  :: ShareMemo -> AstHFun -> (ShareMemo, AstHFun)
shareAstHFun memo v0 = case v0 of
  Ast.AstLambda{} ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards
    -- nor remove the Share constructors.
    (memo, v0)
  Ast.AstVarHFun{} -> (memo, v0)

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
