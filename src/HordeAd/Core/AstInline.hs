{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Inlining and other manipulations of the let-like constructors.
module HordeAd.Core.AstInline
  ( -- * Inlining and simplification pass operations to be applied after unlet
    simplifyArtifactRev, simplifyArtifactRevS
  , simplifyAst6, simplifyAst6S, simplifyAstHVector6
    -- * The unlet pass eliminating nested lets bottom-up
  , unletAst6, unletAst6S, unletAstHVector6
  ) where

import Prelude

import           Control.Arrow (second)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import qualified Data.EnumMap.Strict as EM
import qualified Data.EnumSet as ES
import           Data.List (mapAccumR)
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
import           HordeAd.Util.SizedIndex

-- * Inlining and simplification pass operations to be applied after unlet

simplifyArtifactRev :: (GoodScalar r, KnownNat n)
                    => AstArtifactRev (AstRanked PrimalSpan) r n
                    -> AstArtifactRev (AstRanked PrimalSpan) r n
simplifyArtifactRev (vars, gradient, primal, sh) =
  (vars, simplifyAstHVector6 gradient, simplifyAst6 primal, sh)
{-# SPECIALIZE simplifyArtifactRev
  :: KnownNat n
  => AstArtifactRev (AstRanked PrimalSpan) Double n
  -> AstArtifactRev (AstRanked PrimalSpan) Double n #-}

simplifyArtifactRevS :: (GoodScalar r, Sh.Shape sh)
                     => AstArtifactRev (AstShaped PrimalSpan) r sh
                     -> AstArtifactRev (AstShaped PrimalSpan) r sh
simplifyArtifactRevS (vars, gradient, primal, sh) =
  (vars, simplifyAstHVector6 gradient, simplifyAst6S primal, sh)
{-# SPECIALIZE simplifyArtifactRevS
  :: Sh.Shape sh
  => AstArtifactRev (AstShaped PrimalSpan) Double sh
  -> AstArtifactRev (AstShaped PrimalSpan) Double sh #-}

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyAst6
  :: (GoodScalar r, KnownNat n, AstSpan s)
  => AstRanked s r n -> AstRanked s r n
simplifyAst6 = simplifyAst . snd . inlineAst EM.empty . simplifyAst
{-# SPECIALIZE simplifyAst6
  :: (KnownNat n, AstSpan s)
  => AstRanked s Double n
  -> AstRanked s Double n #-}

simplifyAst6S
  :: (GoodScalar r, Sh.Shape sh, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
simplifyAst6S = simplifyAstS . snd . inlineAstS EM.empty . simplifyAstS
{-# SPECIALIZE simplifyAst6S
  :: (Sh.Shape sh, AstSpan s)
  => AstShaped s Double sh
  -> AstShaped s Double sh #-}

simplifyAstHVector6
  :: AstSpan s => AstHVector s -> AstHVector s
simplifyAstHVector6 =
  simplifyAstHVector . snd . inlineAstHVector EM.empty . simplifyAstHVector
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
  Ast.AstRFromS v -> second Ast.AstRFromS $ inlineAstS memo v
  Ast.AstConstant a -> second Ast.AstConstant $ inlineAst memo a
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ inlineAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ inlineAst memo a
  Ast.AstD u u' ->
    let (memo1, t1) = inlineAst memo u
        (memo2, t2) = inlineAst memo1 u'
    in (memo2, Ast.AstD t1 t2)
  Ast.AstFwd (vars, v) l ds ->
    let (_, v2) = inlineAst EM.empty v
        (memo1, l1) = mapAccumR inlineAstDynamic memo l
        (memo2, ds2) = mapAccumR inlineAstDynamic memo1 ds
    in (memo2, Ast.AstFwd (vars, v2) l1 ds2)
  Ast.AstFold (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAst EM.empty v
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = inlineAst memo1 as
    in (memo2, Ast.AstFold (nvar, mvar, v2) x02 as2)
  Ast.AstFoldDer (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                 (varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAst EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAst EM.empty ast1
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = inlineAst memo1 as
    in (memo2, Ast.AstFoldDer (nvar, mvar, v2)
                              (varDx, varDa, varn1, varm1, ast2)
                              (varDt2, nvar2, mvar2, doms2) x02 as2)
  Ast.AstFoldZip (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAst EM.empty v
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstFoldZip (nvar, mvar, v2) x02 as2)
  Ast.AstFoldZipDer (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                    (varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAst EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAst EM.empty ast1
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstFoldZipDer (nvar, mvar, v2)
                                 (varDx, varDa, varn1, varm1, ast2)
                                 (varDt2, nvar2, mvar2, doms2) x02 as2)
  Ast.AstScan (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAst EM.empty v
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = inlineAst memo1 as
    in (memo2, Ast.AstScan (nvar, mvar, v2) x02 as2)
  Ast.AstScanDer (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                 (varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAst EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAst EM.empty ast1
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = inlineAst memo1 as
    in (memo2, Ast.AstScanDer (nvar, mvar, v2)
                              (varDx, varDa, varn1, varm1, ast2)
                              (varDt2, nvar2, mvar2, doms2) x02 as2)
  Ast.AstScanZip (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAst EM.empty v
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstScanZip (nvar, mvar, v2) x02 as2)
  Ast.AstScanZipDer (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                    (varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAst EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAst EM.empty ast1
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstScanZipDer (nvar, mvar, v2)
                                 (varDx, varDa, varn1, varm1, ast2)
                                 (varDt2, nvar2, mvar2, doms2) x02 as2)

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
                                 (ShapedList.sizedListToList ix)
    in (memo2, Ast.AstIndexS @sh1 v2 (ShapedList.listToSized ix2))
  Ast.AstSumS v -> second Ast.AstSumS (inlineAstS memo v)
  Ast.AstScatterS @sh2 @p v (vars, ix) ->
    let (memo1, v2) = inlineAstS memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty
                                  (ShapedList.sizedListToList ix)
        count = Sh.sizeT @sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatterS @sh2 @p v2 (vars, ShapedList.listToSized ix2))
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
                                  (ShapedList.sizedListToList ix)
        count = Sh.sizeT @sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGatherS @sh2 @p v2 (vars, ShapedList.listToSized ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ inlineAstS memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ inlineAstS memo v
  Ast.AstConstS{} -> (memo, v0)
  Ast.AstLetHVectorInS vars l v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, l2) = inlineAstHVector memo l
        (memo2, v2) = inlineAstS memo1 v
    in (memo2, Ast.AstLetHVectorInS vars l2 v2)
  Ast.AstSFromR v -> second Ast.AstSFromR $ inlineAst memo v
  Ast.AstConstantS a -> second Ast.AstConstantS $ inlineAstS memo a
  Ast.AstPrimalPartS a -> second Ast.AstPrimalPartS $ inlineAstS memo a
  Ast.AstDualPartS a -> second Ast.AstDualPartS $ inlineAstS memo a
  Ast.AstDS u u' ->
    let (memo1, t1) = inlineAstS memo u
        (memo2, t2) = inlineAstS memo1 u'
    in (memo2, Ast.AstDS t1 t2)
  Ast.AstFwdS (vars, v) l ds ->
    let (_, v2) = inlineAstS EM.empty v
        (memo1, l1) = mapAccumR inlineAstDynamic memo l
        (memo2, ds2) = mapAccumR inlineAstDynamic memo1 ds
    in (memo2, Ast.AstFwdS (vars, v2) l1 ds2)
  Ast.AstFoldS (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAstS EM.empty v
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = inlineAstS memo1 as
    in (memo2, Ast.AstFoldS (nvar, mvar, v2) x02 as2)
  Ast.AstFoldDerS (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                  (varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAstS EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAstS EM.empty ast1
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = inlineAstS memo1 as
    in (memo2, Ast.AstFoldDerS (nvar, mvar, v2)
                               (varDx, varDa, varn1, varm1, ast2)
                               (varDt2, nvar2, mvar2, doms2) x02 as2)
  Ast.AstFoldZipS (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAstS EM.empty v
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstFoldZipS (nvar, mvar, v2) x02 as2)
  Ast.AstFoldZipDerS (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                     (varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAstS EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAstS EM.empty ast1
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstFoldZipDerS (nvar, mvar, v2)
                                  (varDx, varDa, varn1, varm1, ast2)
                                  (varDt2, nvar2, mvar2, doms2) x02 as2)
  Ast.AstScanS (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAstS EM.empty v
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = inlineAstS memo1 as
    in (memo2, Ast.AstScanS (nvar, mvar, v2) x02 as2)
  Ast.AstScanDerS (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                  (varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAstS EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAstS EM.empty ast1
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = inlineAstS memo1 as
    in (memo2, Ast.AstScanDerS (nvar, mvar, v2)
                               (varDx, varDa, varn1, varm1, ast2)
                               (varDt2, nvar2, mvar2, doms2) x02 as2)
  Ast.AstScanZipS (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAstS EM.empty v
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstScanZipS (nvar, mvar, v2) x02 as2)
  Ast.AstScanZipDerS (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                     (varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAstS EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAstS EM.empty ast1
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstScanZipDerS (nvar, mvar, v2)
                                  (varDx, varDa, varn1, varm1, ast2)
                                  (varDt2, nvar2, mvar2, doms2) x02 as2)

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
  :: AstSpan s
  => AstMemo -> AstHVector s -> (AstMemo, AstHVector s)
inlineAstHVector memo v0 = case v0 of
  Ast.AstHVector l ->
    second Ast.AstHVector $ mapAccumR inlineAstDynamic memo l
  Ast.AstLetHVectorInHVector vars u v ->
    -- We don't inline, but elsewhere try to reduce to constructors that we do.
    let (memo1, u2) = inlineAstHVector memo u
        (memo2, v2) = inlineAstHVector memo1 v
    in (memo2, Ast.AstLetHVectorInHVector vars u2 v2)
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
        memo1 = EM.unionWith (\c1 c0 -> c1 + k * c0) memo memoV0
    in (memo1, Ast.AstBuildHVector1 k (var, v2))
  Ast.AstRev (vars, v) l ->
    -- No other free variables in v, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards. Same below.
    let (_, v2) = inlineAst EM.empty v
    in second (Ast.AstRev (vars, v2)) (mapAccumR inlineAstDynamic memo l)
  Ast.AstRevDt (vars, v) l dt ->
    let (_, v2) = inlineAst EM.empty v
        (memo1, l1) = mapAccumR inlineAstDynamic memo l
        (memo2, dt2) = inlineAst memo1 dt
    in (memo2, Ast.AstRevDt (vars, v2) l1 dt2)
  Ast.AstRevS (vars, v) l ->
    let (_, v2) = inlineAstS EM.empty v
    in second (Ast.AstRevS (vars, v2)) (mapAccumR inlineAstDynamic memo l)
  Ast.AstRevDtS (vars, v) l dt ->
    let (_, v2) = inlineAstS EM.empty v
        (memo1, l1) = mapAccumR inlineAstDynamic memo l
        (memo2, dt2) = inlineAstS memo1 dt
    in (memo2, Ast.AstRevDtS (vars, v2) l1 dt2)
  Ast.AstMapAccumR k accShs bShs eShs (accvars, evars, v) acc0 es ->
    let (_, v2) = inlineAstHVector EM.empty v
        (memo1, acc02) = mapAccumR inlineAstDynamic memo acc0
        (memo2, es2) = mapAccumR inlineAstDynamic memo1 es
    in (memo2, Ast.AstMapAccumR k accShs bShs eShs
                                (accvars, evars, v2) acc02 es2)
  Ast.AstMapAccumRDer k accShs bShs eShs
                      (accvars, evars, v)
                      (vs1, vs2, vs3, vs4, ast)
                      (ws1, ws2, ws3, ws4, bst)
                      acc0 es ->
    let (_, v2) = inlineAstHVector EM.empty v
        (_, ast2) = inlineAstHVector EM.empty ast
        (_, bst2) = inlineAstHVector EM.empty bst
        (memo1, acc02) = mapAccumR inlineAstDynamic memo acc0
        (memo2, es2) = mapAccumR inlineAstDynamic memo1 es
    in (memo2, Ast.AstMapAccumRDer k accShs bShs eShs
                                   (accvars, evars, v2)
                                   (vs1, vs2, vs3, vs4, ast2)
                                   (ws1, ws2, ws3, ws4, bst2)
                                   acc02 es2)
  Ast.AstMapAccumRR domB (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAstHVector EM.empty v
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstMapAccumRR domB (nvar, mvar, v2) x02 as2)
  Ast.AstMapAccumRDerR domB (nvar, mvar, v)
                       (varDx, varDa, varn1, varm1, ast1)
                       (varDy, varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAstHVector EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAstHVector EM.empty ast1
        (memo1, x02) = inlineAst memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstMapAccumRDerR domB (nvar, mvar, v2)
                                    (varDx, varDa, varn1, varm1, ast2)
                                    (varDy, varDt2, nvar2, mvar2, doms2)
                                    x02 as2)
  Ast.AstMapAccumRS @k domB (nvar, mvar, v) x0 as ->
    let (_, v2) = inlineAstHVector EM.empty v
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstMapAccumRS @k domB (nvar, mvar, v2) x02 as2)
  Ast.AstMapAccumRDerS @k domB (nvar, mvar, v)
                       (varDx, varDa, varn1, varm1, ast1)
                       (varDy, varDt2, nvar2, mvar2, doms) x0 as ->
    let (_, v2) = inlineAstHVector EM.empty v
        (_, doms2) = inlineAstHVector EM.empty doms
        (_, ast2) = inlineAstHVector EM.empty ast1
        (memo1, x02) = inlineAstS memo x0
        (memo2, as2) = mapAccumR inlineAstDynamic memo1 as
    in (memo2, Ast.AstMapAccumRDerS @k domB (nvar, mvar, v2)
                                    (varDx, varDa, varn1, varm1, ast2)
                                    (varDy, varDt2, nvar2, mvar2, doms2)
                                    x02 as2)

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

unletAst6
  :: (GoodScalar r, KnownNat n)
  => ADShare -> AstBindings -> AstRanked PrimalSpan r n
  -> AstRanked PrimalSpan r n
unletAst6 l astBindings t =
  unletAst (emptyUnletEnv l)
  $ bindsToLet (bindsToLet t astBindings) (assocsADShare l)

unletAst6S
  :: (GoodScalar r, Sh.Shape sh)
  => ADShare -> AstBindings -> AstShaped PrimalSpan r sh
  -> AstShaped PrimalSpan r sh
unletAst6S l astBindings t =
  unletAstS (emptyUnletEnv l)
  $ bindsToLetS (bindsToLetS t astBindings) (assocsADShare l)

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
  Ast.AstRFromS v -> Ast.AstRFromS (unletAstS env v)
  Ast.AstConstant v -> Ast.AstConstant (unletAst env v)
  Ast.AstPrimalPart v -> Ast.AstPrimalPart (unletAst env v)
  Ast.AstDualPart v -> Ast.AstDualPart (unletAst env v)
  Ast.AstD u u' -> Ast.AstD (unletAst env u) (unletAst env u')
  Ast.AstFwd (vars, v) l ds ->
    -- No other free variables in v, so no outside lets can reach there.
    Ast.AstFwd (vars, unletAst (emptyUnletEnv emptyADShare) v)
               (V.map (unletAstDynamic env) l)
               (V.map (unletAstDynamic env) ds)
  Ast.AstFold (nvar, mvar, v) x0 as ->
    Ast.AstFold (nvar, mvar, unletAst (emptyUnletEnv emptyADShare) v)
                (unletAst env x0)
                (unletAst env as)
  Ast.AstFoldDer (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                 (varDt2, nvar2, mvar2, doms) x0 as ->
    Ast.AstFoldDer (nvar, mvar, unletAst (emptyUnletEnv emptyADShare) v)
                   ( varDx, varDa, varn1, varm1
                   , unletAst (emptyUnletEnv emptyADShare) ast1 )
                   ( varDt2, nvar2, mvar2
                   , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                   (unletAst env x0)
                   (unletAst env as)
  Ast.AstFoldZip (nvar, mvar, v) x0 as ->
    Ast.AstFoldZip (nvar, mvar, unletAst (emptyUnletEnv emptyADShare) v)
                   (unletAst env x0)
                   (V.map (unletAstDynamic env) as)
  Ast.AstFoldZipDer (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                    (varDt2, nvar2, mvar2, doms) x0 as ->
    Ast.AstFoldZipDer (nvar, mvar, unletAst (emptyUnletEnv emptyADShare) v)
                      ( varDx, varDa, varn1, varm1
                      , unletAst (emptyUnletEnv emptyADShare) ast1 )
                      ( varDt2, nvar2, mvar2
                      , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                      (unletAst env x0)
                      (V.map (unletAstDynamic env) as)
  Ast.AstScan (nvar, mvar, v) x0 as ->
    Ast.AstScan (nvar, mvar, unletAst (emptyUnletEnv emptyADShare) v)
                (unletAst env x0)
                (unletAst env as)
  Ast.AstScanDer (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                 (varDt2, nvar2, mvar2, doms) x0 as ->
    Ast.AstScanDer (nvar, mvar, unletAst (emptyUnletEnv emptyADShare) v)
                   ( varDx, varDa, varn1, varm1
                   , unletAst (emptyUnletEnv emptyADShare) ast1 )
                   ( varDt2, nvar2, mvar2
                   , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                   (unletAst env x0)
                   (unletAst env as)
  Ast.AstScanZip (nvar, mvar, v) x0 as ->
    Ast.AstScanZip (nvar, mvar, unletAst (emptyUnletEnv emptyADShare) v)
                   (unletAst env x0)
                   (V.map (unletAstDynamic env) as)
  Ast.AstScanZipDer (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                    (varDt2, nvar2, mvar2, doms) x0 as ->
    Ast.AstScanZipDer (nvar, mvar, unletAst (emptyUnletEnv emptyADShare) v)
                    ( varDx, varDa, varn1, varm1
                    , unletAst (emptyUnletEnv emptyADShare) ast1 )
                    ( varDt2, nvar2, mvar2
                    , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                    (unletAst env x0)
                    (V.map (unletAstDynamic env) as)

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
  Ast.AstSFromR v -> Ast.AstSFromR (unletAst env v)
  Ast.AstConstantS v -> Ast.AstConstantS (unletAstS env v)
  Ast.AstPrimalPartS v -> Ast.AstPrimalPartS (unletAstS env v)
  Ast.AstDualPartS v -> Ast.AstDualPartS (unletAstS env v)
  Ast.AstDS u u' -> Ast.AstDS (unletAstS env u) (unletAstS env u')
  Ast.AstFwdS (vars, v) l ds ->
    -- No other free variables in v, so no outside lets can reach there.
    Ast.AstFwdS (vars, unletAstS (emptyUnletEnv emptyADShare) v)
                (V.map (unletAstDynamic env) l)
                (V.map (unletAstDynamic env) ds)
  Ast.AstFoldS (nvar, mvar, v) x0 as ->
    Ast.AstFoldS (nvar, mvar, unletAstS (emptyUnletEnv emptyADShare) v)
                 (unletAstS env x0)
                 (unletAstS env as)
  Ast.AstFoldDerS (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                  (varDt2, nvar2, mvar2, doms) x0 as ->
    Ast.AstFoldDerS (nvar, mvar, unletAstS (emptyUnletEnv emptyADShare) v)
                    ( varDx, varDa, varn1, varm1
                    , unletAstS (emptyUnletEnv emptyADShare) ast1 )
                    ( varDt2, nvar2, mvar2
                    , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                    (unletAstS env x0)
                    (unletAstS env as)
  Ast.AstFoldZipS (nvar, mvar, v) x0 as ->
    Ast.AstFoldZipS (nvar, mvar, unletAstS (emptyUnletEnv emptyADShare) v)
                    (unletAstS env x0)
                    (V.map (unletAstDynamic env) as)
  Ast.AstFoldZipDerS (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                     (varDt2, nvar2, mvar2, doms) x0 as ->
    Ast.AstFoldZipDerS (nvar, mvar, unletAstS (emptyUnletEnv emptyADShare) v)
                       ( varDx, varDa, varn1, varm1
                       , unletAstS (emptyUnletEnv emptyADShare) ast1 )
                       ( varDt2, nvar2, mvar2
                       , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                       (unletAstS env x0)
                       (V.map (unletAstDynamic env) as)
  Ast.AstScanS (nvar, mvar, v) x0 as ->
    Ast.AstScanS (nvar, mvar, unletAstS (emptyUnletEnv emptyADShare) v)
                 (unletAstS env x0)
                 (unletAstS env as)
  Ast.AstScanDerS (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                  (varDt2, nvar2, mvar2, doms) x0 as ->
    Ast.AstScanDerS (nvar, mvar, unletAstS (emptyUnletEnv emptyADShare) v)
                    ( varDx, varDa, varn1, varm1
                    , unletAstS (emptyUnletEnv emptyADShare) ast1 )
                    ( varDt2, nvar2, mvar2
                    , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                    (unletAstS env x0)
                    (unletAstS env as)
  Ast.AstScanZipS (nvar, mvar, v) x0 as ->
    Ast.AstScanZipS (nvar, mvar, unletAstS (emptyUnletEnv emptyADShare) v)
                    (unletAstS env x0)
                    (V.map (unletAstDynamic env) as)
  Ast.AstScanZipDerS (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                   (varDt2, nvar2, mvar2, doms) x0 as ->
    Ast.AstScanZipDerS (nvar, mvar, unletAstS (emptyUnletEnv emptyADShare) v)
                       ( varDx, varDa, varn1, varm1
                       , unletAstS (emptyUnletEnv emptyADShare) ast1 )
                       ( varDt2, nvar2, mvar2
                       , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                       (unletAstS env x0)
                       (V.map (unletAstDynamic env) as)

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
  Ast.AstHVector l -> Ast.AstHVector $ V.map (unletAstDynamic env) l
  Ast.AstLetHVectorInHVector vars u v -> case vars of
    [] -> error "unletAstHVector: empty hVector"
    var : _ ->  -- vars are fresh, so var uniquely represent vars
      let vv = dynamicVarNameToAstVarId var
      in if vv `ES.member` unletSet env
         then unletAstHVector env v
         else let env2 = env {unletSet = ES.insert vv (unletSet env)}
              in Ast.AstLetHVectorInHVector
                   vars (unletAstHVector env u) (unletAstHVector env2 v)
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
  Ast.AstRev (vars, v) l ->
    -- No other free variables in v, so no outside lets can reach there.
    -- The same below.
    Ast.AstRev (vars, unletAst (emptyUnletEnv emptyADShare) v)
               (V.map (unletAstDynamic env) l)
  Ast.AstRevDt (vars, v) l dt ->
    Ast.AstRevDt (vars, unletAst (emptyUnletEnv emptyADShare) v)
                 (V.map (unletAstDynamic env) l)
                 (unletAst env dt)
  Ast.AstRevS (vars, v) l ->
    Ast.AstRevS (vars, unletAstS (emptyUnletEnv emptyADShare) v)
                (V.map (unletAstDynamic env) l)
  Ast.AstRevDtS (vars, v) l dt ->
    Ast.AstRevDtS (vars, unletAstS (emptyUnletEnv emptyADShare) v)
                  (V.map (unletAstDynamic env) l)
                  (unletAstS env dt)
  Ast.AstMapAccumR k accShs bShs eShs (accvars, evars, v) acc0 es ->
    Ast.AstMapAccumR k accShs bShs eShs
                     ( accvars, evars
                     , unletAstHVector (emptyUnletEnv emptyADShare) v )
                     (V.map (unletAstDynamic env) acc0)
                     (V.map (unletAstDynamic env) es)
  Ast.AstMapAccumRDer k accShs bShs eShs
                      (accvars, evars, v)
                      (vs1, vs2, vs3, vs4, ast)
                      (ws1, ws2, ws3, ws4, bst)
                      acc0 es ->
    Ast.AstMapAccumRDer k accShs bShs eShs
                        ( accvars, evars
                        , unletAstHVector (emptyUnletEnv emptyADShare) v )
                        ( vs1, vs2, vs3, vs4
                        , unletAstHVector (emptyUnletEnv emptyADShare) ast )
                        ( ws1, ws2, ws3, ws4
                        , unletAstHVector (emptyUnletEnv emptyADShare) bst )
                        (V.map (unletAstDynamic env) acc0)
                        (V.map (unletAstDynamic env) es)
  Ast.AstMapAccumRR domB (nvar, mvar, v) x0 as ->
    Ast.AstMapAccumRR domB
                      ( nvar, mvar
                      , unletAstHVector (emptyUnletEnv emptyADShare) v )
                      (unletAst env x0)
                      (V.map (unletAstDynamic env) as)
  Ast.AstMapAccumRDerR domB (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                            (varDy, varDt2, nvar2, mvar2, doms)
                                            x0 as ->
    Ast.AstMapAccumRDerR domB
                         ( nvar, mvar
                         , unletAstHVector (emptyUnletEnv emptyADShare) v )
                         ( varDx, varDa, varn1, varm1
                         , unletAstHVector (emptyUnletEnv emptyADShare) ast1 )
                         ( varDy, varDt2, nvar2, mvar2
                         , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                         (unletAst env x0)
                         (V.map (unletAstDynamic env) as)
  Ast.AstMapAccumRS @k domB (nvar, mvar, v) x0 as ->
    Ast.AstMapAccumRS @k domB
                      ( nvar, mvar
                      , unletAstHVector (emptyUnletEnv emptyADShare) v )
                      (unletAstS env x0)
                      (V.map (unletAstDynamic env) as)
  Ast.AstMapAccumRDerS @k domB
                       (nvar, mvar, v) (varDx, varDa, varn1, varm1, ast1)
                                       (varDy, varDt2, nvar2, mvar2, doms)
                                       x0 as ->
    Ast.AstMapAccumRDerS @k domB
                         ( nvar, mvar
                         , unletAstHVector (emptyUnletEnv emptyADShare) v )
                         ( varDx, varDa, varn1, varm1
                         , unletAstHVector (emptyUnletEnv emptyADShare) ast1 )
                         ( varDy, varDt2, nvar2, mvar2
                         , unletAstHVector (emptyUnletEnv emptyADShare) doms )
                         (unletAstS env x0)
                         (V.map (unletAstDynamic env) as)

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
