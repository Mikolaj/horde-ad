{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Inlining and global sharing elimination.
module HordeAd.Core.AstInline
  ( -- * The joint inlining and simplification term transformation
    simplifyArtifact, simplifyArtifactGradient
  , simplifyInlineAst
  , simplifyInline
    -- * The translates global sharing to normal lets
  , unshareAstTensor
  ) where

import Prelude

import Control.Arrow (second)
import Data.Array.Internal (valueOf)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.EnumMap.Strict qualified as EM
import Data.Foldable qualified as Foldable
import Data.List (mapAccumR)
import Data.Some
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, fromSNat)

import HordeAd.Core.Ast (AstBool, AstTensor)
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * The joint inlining and simplification term transformation

simplifyArtifact :: forall x z. (TensorKind x, TensorKind z)
                 => AstArtifactRev x z -> AstArtifactRev x z
simplifyArtifact art | Dict <- lemTensorKindOfAD (stensorKind @x) =
  let !der = simplifyInline $ artDerivativeRev art in
  let !prim = simplifyInline $ artPrimalRev art
  in art {artDerivativeRev = der, artPrimalRev = prim}

simplifyArtifactGradient :: forall x z. TensorKind x
                         => AstArtifactRev x z -> AstArtifactRev x z
simplifyArtifactGradient art | Dict <- lemTensorKindOfAD (stensorKind @x) =
  art { artDerivativeRev =
        simplifyInline $ artDerivativeRev art }

simplifyInlineAst
  :: forall r n s. (KnownNat n, GoodScalar r, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
simplifyInlineAst = AstRanked . simplifyInline . unAstRanked
{-# SPECIALIZE simplifyInlineAst
  :: (KnownNat n, AstSpan s)
  => AstRanked s Double n -> AstRanked s Double n #-}

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyInline
  :: (AstSpan s, TensorKind z) => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInline =
  snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst
    -- no specialization possible except for the tag type s


-- * The pass that inlines lets with the bottom-up strategy

type AstMemo = EM.EnumMap AstVarId Double

inlineAst
  :: forall s y. AstSpan s
  => AstMemo -> AstTensor AstMethodLet s y -> (AstMemo, AstTensor AstMethodLet s y)
inlineAst memo v0 = case v0 of
  Ast.AstScalar t -> second Ast.AstScalar (inlineAst memo t)
  Ast.AstUnScalar t -> second Ast.AstUnScalar (inlineAst memo t)
  Ast.AstPair t1 t2 ->
    let (memo2, v1) = inlineAst memo t1
        (memo3, v2) = inlineAst memo2 t2
    in (memo3, Ast.AstPair v1 v2)
  -- TODO: these are correct only if each component appears once,
  -- as opposed to one appearing twice and ther other not at all
  -- (or if both components are similar enough)
  -- but without this we miss many other simplifications and simple
  -- examples become unreadable
  -- TODO: these trigger variable capture and real duplication
{-
  Ast.AstProject1 (Ast.AstVar _ var) ->
    let f Nothing = Just 0.5
        f (Just count) = Just $ count + 0.5
    in (EM.alter f (varNameToAstVarId var) memo, v0)
  Ast.AstProject2 (Ast.AstVar _ var) ->
    let f Nothing = Just 0.5
        f (Just count) = Just $ count + 0.5
    in (EM.alter f (varNameToAstVarId var) memo, v0)
-}
  Ast.AstProject1 t -> second Ast.AstProject1 (inlineAst memo t)
  Ast.AstProject2 t -> second Ast.AstProject2 (inlineAst memo t)
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
  Ast.AstSFromR v -> second Ast.AstSFromR $ inlineAst memo v

  Ast.AstMinIndexX a -> second Ast.AstMinIndexX $ inlineAst memo a
  Ast.AstMaxIndexX a -> second Ast.AstMaxIndexX $ inlineAst memo a
  Ast.AstFloorX a -> second Ast.AstFloorX $ inlineAst memo a
  Ast.AstIotaX -> (memo, v0)
  Ast.AstN1X opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstN1X opCode u2)
  Ast.AstN2X opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstN2X opCode u2 v3)
  Ast.AstR1X opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstR1X opCode u2)
  Ast.AstR2X opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstR2X opCode u2 v3)
  Ast.AstI2X opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstI2X opCode u2 v3)
  Ast.AstSumOfListX args ->
    let (memo2, args2) = mapAccumR inlineAst memo args
    in (memo2, Ast.AstSumOfListX args2)
  Ast.AstIndexX @sh1 v ix ->
    let (memo1, v2) = inlineAst memo v
        (memo2, ix2) = mapAccumR inlineAst memo1
                                 (toList ix)
    in (memo2, Ast.AstIndexX @sh1 v2 (fromList ix2))
  Ast.AstSumX v -> second Ast.AstSumX (inlineAst memo v)
  Ast.AstScatterX{} -> error "TODO"
  Ast.AstFromVectorX l ->
    let (memo2, l2) = mapAccumR inlineAst memo (V.toList l)
    in (memo2, Ast.AstFromVectorX $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstAppendX x y ->
    let (memo1, t1) = inlineAst memo x
        (memo2, t2) = inlineAst memo1 y
    in (memo2, Ast.AstAppendX t1 t2)
  Ast.AstSliceX @i v -> second (Ast.AstSliceX @i) (inlineAst memo v)
  Ast.AstReverseX v -> second Ast.AstReverseX (inlineAst memo v)
  Ast.AstTransposeX perm v ->
    second (Ast.AstTransposeX perm) $ inlineAst memo v
  Ast.AstReshapeX sh v -> second (Ast.AstReshapeX sh) (inlineAst memo v)
  Ast.AstGatherX{} -> error "TODO"
  Ast.AstCastX v -> second Ast.AstCastX $ inlineAst memo v
  Ast.AstFromIntegralX v ->
    second Ast.AstFromIntegralX $ inlineAst memo v
  Ast.AstConstX{} -> (memo, v0)
  Ast.AstProjectX l p ->
    let (memo1, l2) = inlineAst memo l
    in (memo1, Ast.AstProjectX l2 p)
  Ast.AstXFromR v -> second Ast.AstXFromR $ inlineAst memo v

  Ast.AstMkHVector l ->
    second Ast.AstMkHVector $ mapAccumR inlineAstDynamic memo l
  Ast.AstHApply t ll ->
    let (memo1, t2) = inlineAstHFun memo t
        (memo2, ll2) = inlineAst memo1 ll
    in (memo2, Ast.AstHApply t2 ll2)
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

inlineAstDynamic
  :: AstSpan s
  => AstMemo -> AstDynamic AstMethodLet s
  -> (AstMemo, AstDynamic AstMethodLet s)
inlineAstDynamic memo = \case
  DynamicRanked (AstGeneric w) ->
    second (DynamicRanked . AstGeneric) $ inlineAst memo w
  DynamicShaped (AstGenericS w) ->
    second (DynamicShaped . AstGenericS) $ inlineAst memo w
  u@DynamicRankedDummy{} -> (memo, u)
  u@DynamicShapedDummy{} -> (memo, u)

inlineAstHFun
  :: AstMemo -> AstHFun x y -> (AstMemo, AstHFun x y)
inlineAstHFun memo v0 = case v0 of
  Ast.AstLambda ~(var, ftk, l) ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards.
    (memo, Ast.AstLambda (var, ftk, snd $ inlineAst EM.empty l))

inlineAstBool :: AstMemo -> AstBool AstMethodLet -> (AstMemo, AstBool AstMethodLet)
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
  Ast.AstRelX opCodeRel arg1 arg2 ->
    let (memo1, r1) = inlineAst memo arg1
        (memo2, r2) = inlineAst memo1 arg2
    in (memo2, Ast.AstRelX opCodeRel r1 r2)


-- * The translates global sharing to normal lets

unshareAstTensor :: TensorKind y
                 => AstTensor AstMethodShare PrimalSpan y
                 -> AstTensor AstMethodLet PrimalSpan y
unshareAstTensor tShare =
  let (memoOut, tLet) = unshareAst DMap.empty tShare
  in bindsToLet tLet memoOut

-- This works only because the other code never inserts the same rshare
-- into more than one index element, with the share containing
-- the gather/scatter/build variables corresponding to the index.
unshareAstScoped
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => [IntVarName] -> AstBindings -> AstTensor AstMethodShare s (TKR r n)
  -> (AstBindings, AstTensor AstMethodLet s (TKR r n))
unshareAstScoped vars0 memo0 v0 =
  let (memo1, v1) = unshareAst memo0 v0
      memoDiff = DMap.difference memo1 memo0
      varsOccur :: [AstVarId] -> AstTensor AstMethodLet PrimalSpan y
                -> Bool
      varsOccur vs d = any (`varInAst` d) vs
      closeOccurs :: [AstVarId] -> AstBindings -> (AstBindings, AstBindings)
      closeOccurs vars memo =
        let (memoLocal, memoGlobal) = DMap.partition (varsOccur vars) memo
        in if DMap.null memoLocal
           then (memoLocal, memoGlobal)
           else -- TODO: we probably need to include all variables from
                -- the HVector case, not only the first variable
                -- that represents them
                let vars2 = map (\(Some var) -> varNameToAstVarId var)
                                (DMap.keys memoLocal)
                    (memoLocal2, memoGlobal2) = closeOccurs vars2 memoGlobal
                in (DMap.union memoLocal memoLocal2, memoGlobal2)
      (memoLocal1, memoGlobal1) =
        closeOccurs (map varNameToAstVarId vars0) memoDiff
  in (DMap.union memo0 memoGlobal1, bindsToLet v1 memoLocal1)

-- So far, there are no lets in the resulting term, but we mark it as potentially
-- containing lets, because in the future we may optimize this by inserting
-- some lets not at the top-level.
unshareAst
  :: forall s y. AstSpan s
  => AstBindings -> AstTensor AstMethodShare s y
  -> (AstBindings, AstTensor AstMethodLet s y)
unshareAst memo = \case
  Ast.AstScalar t -> second Ast.AstScalar (unshareAst memo t)
  Ast.AstUnScalar t -> second Ast.AstUnScalar (unshareAst memo t)
  Ast.AstPair t1 t2 ->
    let (memo1, v1) = unshareAst memo t1
        (memo2, v2) = unshareAst memo1 t2
    in (memo2, Ast.AstPair v1 v2)
  Ast.AstProject1 t -> second Ast.AstProject1 (unshareAst memo t)
  Ast.AstProject2 t -> second Ast.AstProject2 (unshareAst memo t)
  Ast.AstVar sh v -> (memo, Ast.AstVar sh v)
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ unshareAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ unshareAst memo a
  Ast.AstConstant a -> second Ast.AstConstant $ unshareAst memo a
  Ast.AstD u u' ->
    let (memo1, t1) = unshareAst memo u
        (memo2, t2) = unshareAst memo1 u'
    in (memo2, Ast.AstD t1 t2)
  Ast.AstCond b a2 a3 ->
    let (memo1, b1) = unshareAstBool memo b
        (memo2, t2) = unshareAst memo1 a2
        (memo3, t3) = unshareAst memo2 a3
    in (memo3, Ast.AstCond b1 t2 t3)
  Ast.AstReplicate k v -> second (Ast.AstReplicate k) (unshareAst memo v)
  Ast.AstBuild1 @y2 snat (var, v) -> case stensorKind @y2 of
    STKScalar _ ->
      let (memo1, v2) = unshareAstScoped [var] memo $ Ast.AstScalar v
      in (memo1, Ast.AstBuild1 snat (var, v2))
    STKR STKScalar{} SNat ->
      let (memo1, v2) = unshareAstScoped [var] memo v
      in (memo1, Ast.AstBuild1 snat (var, v2))
    STKS STKScalar{} sh -> withKnownShS sh $ error "WIP"
    STKX STKScalar{} sh -> withKnownShX sh $ error "WIP"
    STKProduct{} -> error "WIP"
    STKUntyped -> error "WIP"
    _ -> error "TODO"
  Ast.AstShare var v | Just Refl <- sameAstSpan @s @PrimalSpan ->
    -- We assume v is the same if var is the same.
    let astVar = Ast.AstVar (shapeAstFull v) var
    in if var `DMap.member` memo
       then (memo, astVar)  -- TODO: memoize AstVar itself
       else let (memo1, v2) = unshareAst memo v
            in (DMap.insert var v2 memo1, astVar)
  Ast.AstShare{} -> error "unshareAst: AstShare not in PrimalSpan"
  Ast.AstToShare v -> (memo, v)  -- nothing to unshare in this subtree
  Ast.AstMinIndex a -> second Ast.AstMinIndex $ unshareAst memo a
  Ast.AstMaxIndex a -> second Ast.AstMaxIndex $ unshareAst memo a
  Ast.AstFloor a -> second Ast.AstFloor $ unshareAst memo a
  Ast.AstIota -> (memo, Ast.AstIota)
  Ast.AstN1 opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstN1 opCode u2)
  Ast.AstN2 opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstN2 opCode u2 v3)
  Ast.AstR1 opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstR1 opCode u2)
  Ast.AstR2 opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstR2 opCode u2 v3)
  Ast.AstI2 opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstI2 opCode u2 v3)
  Ast.AstSumOfList args ->
    let (memo2, args2) = mapAccumR unshareAst memo args
    in (memo2, Ast.AstSumOfList args2)
  Ast.AstIndex v ix ->
    let (memo1, v2) = unshareAst memo v
        (memo2, ix2) = mapAccumR unshareAst memo1 (indexToList ix)
    in (memo2, Ast.AstIndex v2 (listToIndex ix2))
  Ast.AstSum v -> second Ast.AstSum (unshareAst memo v)
  Ast.AstScatter sh v (vars, ix) ->
    let (memo1, ix2) = mapAccumR (unshareAstScoped $ sizedToList vars)
                                 memo (indexToList ix)
        (memo2, v2) = unshareAst memo1 v
    in (memo2, Ast.AstScatter sh v2 (vars, listToIndex ix2))
  Ast.AstFromVector l ->
    let (memo2, l2) = mapAccumR unshareAst memo (V.toList l)
    in (memo2, Ast.AstFromVector $ V.fromList l2)
  Ast.AstAppend x y ->
    let (memo1, t1) = unshareAst memo x
        (memo2, t2) = unshareAst memo1 y
    in (memo2, Ast.AstAppend t1 t2)
  Ast.AstSlice i k v -> second (Ast.AstSlice i k) (unshareAst memo v)
  Ast.AstReverse v -> second Ast.AstReverse (unshareAst memo v)
  Ast.AstTranspose perm v ->
    second (Ast.AstTranspose perm) $ unshareAst memo v
  Ast.AstReshape sh v -> second (Ast.AstReshape sh) (unshareAst memo v)
  Ast.AstGather sh v (vars, ix) ->
    let (memo1, ix2) = mapAccumR (unshareAstScoped $ sizedToList vars)
                                 memo (indexToList ix)
        (memo2, v2) = unshareAst memo1 v
    in (memo2, Ast.AstGather sh v2 (vars, listToIndex ix2))
  Ast.AstCast v -> second Ast.AstCast $ unshareAst memo v
  Ast.AstFromIntegral v -> second Ast.AstFromIntegral $ unshareAst memo v
  Ast.AstConst t -> (memo, Ast.AstConst t)
  Ast.AstProjectR l p ->
    -- This doesn't get simplified even if l is an HVector of vars freshly
    -- created by unshareAst. However, then l is shared, so the cost
    -- per AstProjectR is only slightly (2 words? 1 indirection?)
    -- higher than if simplified.
    let (memo1, l2) = unshareAst memo l
    in (memo1, Ast.AstProjectR l2 p)
  Ast.AstRFromS v -> second Ast.AstRFromS $ unshareAst memo v

  Ast.AstMinIndexS a -> second Ast.AstMinIndexS $ unshareAst memo a
  Ast.AstMaxIndexS a -> second Ast.AstMaxIndexS $ unshareAst memo a
  Ast.AstFloorS a -> second Ast.AstFloorS $ unshareAst memo a
  Ast.AstIotaS -> (memo, Ast.AstIotaS)
  Ast.AstN1S opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstN1S opCode u2)
  Ast.AstN2S opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstN2S opCode u2 v3)
  Ast.AstR1S opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstR1S opCode u2)
  Ast.AstR2S opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstR2S opCode u2 v3)
  Ast.AstI2S opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstI2S opCode u2 v3)
  Ast.AstSumOfListS args ->
    let (memo2, args2) = mapAccumR unshareAst memo args
    in (memo2, Ast.AstSumOfListS args2)
  Ast.AstIndexS @sh1 v ix ->
    let (memo1, v2) = unshareAst memo v
        (memo2, ix2) = mapAccumR unshareAst memo1 (ShapedList.indexToList ix)
    in (memo2, Ast.AstIndexS @sh1 v2 (ShapedList.listToIndex ix2))
  Ast.AstSumS v -> second Ast.AstSumS (unshareAst memo v)
  Ast.AstScatterS @sh2 @p v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (unshareAstScoped $ ShapedList.sizedToList vars)
                    memo (ShapedList.indexToList ix)
        (memo2, v2) = unshareAst memo1 v
    in (memo2, Ast.AstScatterS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstFromVectorS l ->
    let (memo2, l2) = mapAccumR unshareAst memo (V.toList l)
    in (memo2, Ast.AstFromVectorS $ V.fromList l2)
  Ast.AstAppendS x y ->
    let (memo1, t1) = unshareAst memo x
        (memo2, t2) = unshareAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (unshareAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (unshareAst memo v)
  Ast.AstTransposeS perm v ->
    second (Ast.AstTransposeS perm) $ unshareAst memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (unshareAst memo v)
  Ast.AstGatherS @sh2 @p v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (unshareAstScoped $ ShapedList.sizedToList vars)
                    memo (ShapedList.indexToList ix)
        (memo2, v2) = unshareAst memo1 v
    in (memo2, Ast.AstGatherS @sh2 @p v2 (vars, ShapedList.listToIndex ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ unshareAst memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ unshareAst memo v
  Ast.AstConstS t -> (memo, Ast.AstConstS t)
  Ast.AstProjectS l p ->
    let (memo1, l2) = unshareAst memo l
    in (memo1, Ast.AstProjectS l2 p)
  Ast.AstSFromR v -> second Ast.AstSFromR $ unshareAst memo v

  Ast.AstMinIndexX a -> second Ast.AstMinIndexX $ unshareAst memo a
  Ast.AstMaxIndexX a -> second Ast.AstMaxIndexX $ unshareAst memo a
  Ast.AstFloorX a -> second Ast.AstFloorX $ unshareAst memo a
  Ast.AstIotaX -> (memo, Ast.AstIotaX)
  Ast.AstN1X opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstN1X opCode u2)
  Ast.AstN2X opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstN2X opCode u2 v3)
  Ast.AstR1X opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstR1X opCode u2)
  Ast.AstR2X opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstR2X opCode u2 v3)
  Ast.AstI2X opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstI2X opCode u2 v3)
  Ast.AstSumOfListX args ->
    let (memo2, args2) = mapAccumR unshareAst memo args
    in (memo2, Ast.AstSumOfListX args2)
  Ast.AstIndexX @sh1 v ix ->
    let (memo1, v2) = unshareAst memo v
        (memo2, ix2) = mapAccumR unshareAst memo1 (Foldable.toList ix)
    in (memo2, Ast.AstIndexX @sh1 v2 (fromList ix2))
  Ast.AstSumX v -> second Ast.AstSumX (unshareAst memo v)
  Ast.AstScatterX @sh2 @p v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (unshareAstScoped $ toList vars)
                    memo (Foldable.toList ix)
        (memo2, v2) = unshareAst memo1 v
    in (memo2, Ast.AstScatterX @sh2 @p v2 (vars, fromList ix2))
  Ast.AstFromVectorX l ->
    let (memo2, l2) = mapAccumR unshareAst memo (V.toList l)
    in (memo2, Ast.AstFromVectorX $ V.fromList l2)
  Ast.AstAppendX x y ->
    let (memo1, t1) = unshareAst memo x
        (memo2, t2) = unshareAst memo1 y
    in (memo2, Ast.AstAppendX t1 t2)
  Ast.AstSliceX @i v -> second (Ast.AstSliceX @i) (unshareAst memo v)
  Ast.AstReverseX v -> second Ast.AstReverseX (unshareAst memo v)
  Ast.AstTransposeX perm v ->
    second (Ast.AstTransposeX perm) $ unshareAst memo v
  Ast.AstReshapeX sh v -> second (Ast.AstReshapeX sh) (unshareAst memo v)
  Ast.AstGatherX @sh2 @p v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (unshareAstScoped $ toList vars)
                    memo (Foldable.toList ix)
        (memo2, v2) = unshareAst memo1 v
    in (memo2, Ast.AstGatherX @sh2 @p v2 (vars, fromList ix2))
  Ast.AstCastX v -> second Ast.AstCastX $ unshareAst memo v
  Ast.AstFromIntegralX v ->
    second Ast.AstFromIntegralX $ unshareAst memo v
  Ast.AstConstX t -> (memo, Ast.AstConstX t)
  Ast.AstProjectX l p ->
    let (memo1, l2) = unshareAst memo l
    in (memo1, Ast.AstProjectX l2 p)
  Ast.AstXFromR v -> second Ast.AstXFromR $ unshareAst memo v

  Ast.AstMkHVector l ->
    second Ast.AstMkHVector $ mapAccumR unshareAstDynamic memo l
  Ast.AstHApply t ll ->
    let (memo1, t2) = unshareAstHFun memo t
        (memo2, ll2) = unshareAst memo1 ll
    in (memo2, Ast.AstHApply t2 ll2)
  Ast.AstBuildHVector1{} -> error "unshareAst: AstBuildHVector1"  -- not hard to add
  Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = unshareAst memo acc0
        (memo2, es2) = unshareAst memo1 es
    in (memo2, Ast.AstMapAccumRDer k accShs bShs eShs f df rf acc02 es2)
  Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = unshareAst memo acc0
        (memo2, es2) = unshareAst memo1 es
    in (memo2, Ast.AstMapAccumLDer k accShs bShs eShs f df rf acc02 es2)

unshareAstDynamic
  :: AstSpan s
  => AstBindings -> AstDynamic AstMethodShare s
  -> (AstBindings, AstDynamic AstMethodLet s)
unshareAstDynamic memo = \case
  DynamicRanked (AstGeneric w) ->
    second (DynamicRanked . AstGeneric) $ unshareAst memo w
  DynamicShaped (AstGenericS w) ->
    second (DynamicShaped . AstGenericS) $ unshareAst memo w
  DynamicRankedDummy p1 p2 -> (memo, DynamicRankedDummy p1 p2)
  DynamicShapedDummy p1 p2 -> (memo, DynamicShapedDummy p1 p2)

unshareAstHFun
  :: AstBindings -> AstHFun x y -> (AstBindings, AstHFun x y)
unshareAstHFun memo v0 = case v0 of
  Ast.AstLambda{} ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards
    -- nor remove the Share constructors.
    (memo, v0)

unshareAstBool :: AstBindings -> AstBool AstMethodShare
               -> (AstBindings, AstBool AstMethodLet)
unshareAstBool memo = \case
  Ast.AstBoolNot arg ->
    let (memo2, arg2) = unshareAstBool memo arg
    in (memo2, Ast.AstBoolNot arg2)
  Ast.AstB2 opCodeBool arg1 arg2 ->
    let (memo1, b1) = unshareAstBool memo arg1
        (memo2, b2) = unshareAstBool memo1 arg2
    in (memo2, Ast.AstB2 opCodeBool b1 b2)
  Ast.AstBoolConst t -> (memo, Ast.AstBoolConst t)
  Ast.AstRel opCodeRel arg1 arg2 ->
    let (memo1, r1) = unshareAst memo arg1
        (memo2, r2) = unshareAst memo1 arg2
    in (memo2, Ast.AstRel opCodeRel r1 r2)
  Ast.AstRelS opCodeRel arg1 arg2 ->
    let (memo1, r1) = unshareAst memo arg1
        (memo2, r2) = unshareAst memo1 arg2
    in (memo2, Ast.AstRelS opCodeRel r1 r2)
  Ast.AstRelX opCodeRel arg1 arg2 ->
    let (memo1, r1) = unshareAst memo arg1
        (memo2, r2) = unshareAst memo1 arg2
    in (memo2, Ast.AstRelX opCodeRel r1 r2)
