{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Inlining and global sharing elimination.
module HordeAd.Core.AstInline
  ( -- * The joint inlining and simplification term transformation
    simplifyArtifact, simplifyArtifactGradient
  , simplifyInline, simplifyInlineContract
    -- * The translates global sharing to normal lets
  , unshareAstTensor
  ) where

import Prelude

import Control.Arrow (second)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.EnumMap.Strict qualified as EM
import Data.List (mapAccumR)
import Data.Some
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (fromSNat)

import Data.Array.Mixed.Shape (ssxFromShape, withKnownShX)
import Data.Array.Nested (ShS (..))
import Data.Array.Nested.Internal.Shape (shrRank, withKnownShS)

import HordeAd.Core.Ast (AstBool, AstTensor)
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The joint inlining and simplification term transformation

simplifyArtifact :: forall x z. (TensorKind x, TensorKind z)
                 => AstArtifactRev x z -> AstArtifactRev x z
simplifyArtifact art | Dict <- lemTensorKindOfAD (stensorKind @x) =
  let !der = simplifyInlineContract $ artDerivativeRev art in
  let !prim = simplifyInlineContract $ artPrimalRev art
  in art {artDerivativeRev = der, artPrimalRev = prim}

simplifyArtifactGradient :: forall x z. TensorKind x
                         => AstArtifactRev x z -> AstArtifactRev x z
simplifyArtifactGradient art | Dict <- lemTensorKindOfAD (stensorKind @x) =
  art { artDerivativeRev =
        simplifyInlineContract $ artDerivativeRev art }

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyInline
  :: forall z s. (AstSpan s, TensorKind z)
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInline =
  snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst
    -- no specialization possible except for the tag type s

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyInlineContract
  :: forall z s. (AstSpan s, TensorKind z)
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInlineContract =
  snd . inlineAst EM.empty
  . contractAst . expandAst  -- TODO: when/if contractAst does less simplification, add simplifyAst in-between
  . snd . inlineAst EM.empty . simplifyAst
    -- no specialization possible except for the tag type s


-- * The pass that inlines lets with the bottom-up strategy

type AstMemo = EM.EnumMap AstVarId Double

inlineAst
  :: forall s y. AstSpan s
  => AstMemo -> AstTensor AstMethodLet s y -> (AstMemo, AstTensor AstMethodLet s y)
inlineAst memo v0 = case v0 of
  Ast.AstSFromK t -> second Ast.AstSFromK (inlineAst memo t)
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
  Ast.AstFromPrimal a -> second Ast.AstFromPrimal $ inlineAst memo a
  Ast.AstFromDual a -> second Ast.AstFromDual $ inlineAst memo a
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
  Ast.AstFromVector snat l ->
    let (memo2, l2) = mapAccumR inlineAst memo (V.toList l)
    in (memo2, Ast.AstFromVector snat $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstSum snat stk v ->
    second (Ast.AstSum snat stk) (inlineAst memo v)
  Ast.AstReplicate snat stk v ->
    second (Ast.AstReplicate snat stk) (inlineAst memo v)
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
      1 -> (memo2, substituteAst u2 var v2)
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
            memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
                      -- u is small, so the union is fast
        in (memo3, substituteAst u0 var v2)
      _ -> (memo2, Ast.AstLet var u2 v2)
  Ast.AstConcrete{} -> (memo, v0)

  Ast.AstSumOfList stk args ->
    let (memo2, args2) = mapAccumR inlineAst memo args
    in (memo2, Ast.AstSumOfList stk args2)

  Ast.AstN1K opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstN1K opCode u2)
  Ast.AstN2K opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstN2K opCode u2 v3)
  Ast.AstR1K opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstR1K opCode u2)
  Ast.AstR2K opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstR2K opCode u2 v3)
  Ast.AstI2K opCode u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstI2K opCode u2 v3)
  Ast.AstFloorK a -> second Ast.AstFloorK $ inlineAst memo a
  Ast.AstCastK a -> second Ast.AstCastK $ inlineAst memo a
  Ast.AstFromIntegralK a -> second Ast.AstFromIntegralK $ inlineAst memo a

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
  Ast.AstIndexS @sh1 v ix ->
    let (memo1, v2) = inlineAst memo v
        (memo2, ix2) = mapAccumR inlineAst memo1
                                 (toList ix)
    in (memo2, Ast.AstIndexS @sh1 v2 (fromList ix2))
  Ast.AstScatterS @shm @shn @shp v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty
                                  (toList ix)
        count = fromIntegral $ sizeT @shp * sizeT @shn
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatterS @shm @shn @shp v2 (vars, fromList ix2))
  Ast.AstAppendS x y ->
    let (memo1, t1) = inlineAst memo x
        (memo2, t2) = inlineAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (inlineAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (inlineAst memo v)
  Ast.AstTransposeS perm v ->
    second (Ast.AstTransposeS perm) $ inlineAst memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (inlineAst memo v)
  Ast.AstGatherS @shm @shn @shp v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty
                                  (toList ix)
        count = fromIntegral $ sizeT @shm * sizeT @shn
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGatherS @shm @shn @shp v2 (vars, fromList ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ inlineAst memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ inlineAst memo v
  Ast.AstZipS v -> second Ast.AstZipS (inlineAst memo v)
  Ast.AstUnzipS v -> second Ast.AstUnzipS (inlineAst memo v)

  Ast.AstFromS stkz v -> second (Ast.AstFromS stkz) $ inlineAst memo v
  Ast.AstSFromR v -> second Ast.AstSFromR $ inlineAst memo v
  Ast.AstSFromX v -> second Ast.AstSFromX $ inlineAst memo v

  Ast.AstXNestR v -> second Ast.AstXNestR $ inlineAst memo v
  Ast.AstXNestS v -> second Ast.AstXNestS $ inlineAst memo v
  Ast.AstXNest v -> second Ast.AstXNest $ inlineAst memo v
  Ast.AstXUnNestR v -> second Ast.AstXUnNestR $ inlineAst memo v
  Ast.AstXUnNestS v -> second Ast.AstXUnNestS $ inlineAst memo v
  Ast.AstXUnNest v -> second Ast.AstXUnNest $ inlineAst memo v

  Ast.AstApply t ll ->
    let (memo1, t2) = inlineAstHFun memo t
        (memo2, ll2) = inlineAst memo1 ll
    in (memo2, Ast.AstApply t2 ll2)
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFun memo f
        (memo2, df2) = inlineAstHFun memo1 df
        (memo3, rf2) = inlineAstHFun memo2 rf
        (memo4, acc02) = inlineAst memo3 acc0
        (memo5, es2) = inlineAst memo4 es
    in (memo5, Ast.AstMapAccumRDer k bShs eShs f2 df2 rf2 acc02 es2)
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFun memo f
        (memo2, df2) = inlineAstHFun memo1 df
        (memo3, rf2) = inlineAstHFun memo2 rf
        (memo4, acc02) = inlineAst memo3 acc0
        (memo5, es2) = inlineAst memo4 es
    in (memo5, Ast.AstMapAccumLDer k bShs eShs f2 df2 rf2 acc02 es2)

  Ast.AstReplicate0NS sh stk v ->
    second (Ast.AstReplicate0NS sh stk) (inlineAst memo v)
  Ast.AstSum0S sh stk v ->
    second (Ast.AstSum0S sh stk) (inlineAst memo v)
  Ast.AstDot0S sh u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstDot0S sh u2 v3)
  Ast.AstDot1InS m n u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstDot1InS m n u2 v3)
  Ast.AstMatvecmulS m n u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstMatvecmulS m n u2 v3)
  Ast.AstMatmul2S m n p u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstMatmul2S m n p u2 v3)

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
  :: forall z s. (TensorKind z, AstSpan s)
  => [IntVarName] -> AstBindings -> AstTensor AstMethodShare s z
  -> (AstBindings, AstTensor AstMethodLet s z)
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
           else let vars2 = map (\(Some var) -> varNameToAstVarId var)
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
  Ast.AstSFromK t -> second Ast.AstSFromK (unshareAst memo t)
  Ast.AstPair t1 t2 ->
    let (memo1, v1) = unshareAst memo t1
        (memo2, v2) = unshareAst memo1 t2
    in (memo2, Ast.AstPair v1 v2)
  Ast.AstProject1 t -> second Ast.AstProject1 (unshareAst memo t)
  Ast.AstProject2 t -> second Ast.AstProject2 (unshareAst memo t)
  Ast.AstVar sh v -> (memo, Ast.AstVar sh v)
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ unshareAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ unshareAst memo a
  Ast.AstFromPrimal a -> second Ast.AstFromPrimal $ unshareAst memo a
  Ast.AstFromDual a -> second Ast.AstFromDual $ unshareAst memo a
  Ast.AstCond b a2 a3 ->
    let (memo1, b1) = unshareAstBool memo b
        (memo2, t2) = unshareAst memo1 a2
        (memo3, t3) = unshareAst memo2 a3
    in (memo3, Ast.AstCond b1 t2 t3)
  Ast.AstFromVector snat l ->
    let (memo2, l2) = mapAccumR unshareAst memo (V.toList l)
    in (memo2, Ast.AstFromVector snat $ V.fromList l2)
  Ast.AstSum snat stk v ->
    second (Ast.AstSum snat stk) (unshareAst memo v)
  Ast.AstReplicate snat stk v ->
    second (Ast.AstReplicate snat stk) (unshareAst memo v)
  Ast.AstBuild1 snat (var, v) ->
    let (memo1, v2) = unshareAstScoped [var] memo v
    in (memo1, Ast.AstBuild1 snat (var, v2))
  -- We assume v is the same if var is the same.
  Ast.AstShare varRaw a | Just Refl <- sameAstSpan @s @PrimalSpan -> case a of
    Ast.AstFromS @y2 stkz v | Dict <- lemTensorKindOfSTK (ftkToStk (ftkAst v)) ->
      let var = mkAstVarName $ varNameToAstVarId varRaw
          astVar = Ast.AstFromS @y2 stkz
                   $ Ast.AstVar (ftkAst v) var
      in if var `DMap.member` memo
         then (memo, astVar)
         else let (memo1, a2) = unshareAst memo v
              in (DMap.insert var a2 memo1, astVar)
    -- The PrimalSpan check ensures there's no need to match for
    -- Ast.AstFromPrimal (Ast.AstFromS).
    _ -> case ftkAst a of
      ftk@(FTKR @_ @x sh' x) | SNat <- shrRank sh'
                             , Dict <- lemTensorKindOfSTK (ftkToStk x) ->
        withCastRS sh' $ \(sh :: ShS sh) ->
          withKnownShS sh $
          let var = mkAstVarName $ varNameToAstVarId varRaw
              astVar = Ast.AstFromS @(TKS2 sh x) (ftkToStk ftk)
                       $ Ast.AstVar (FTKS sh x) var
          in if var `DMap.member` memo
             then (memo, astVar)
             else let (memo1, a2) = unshareAst memo (Ast.AstSFromR @sh a)
                  in (DMap.insert var a2 memo1, astVar)
      ftk@(FTKX @_ @x sh' x) | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
        withCastXS sh' $ \(sh :: ShS sh) ->
          withKnownShX (ssxFromShape sh') $
          withKnownShS sh $
          let var = mkAstVarName $ varNameToAstVarId varRaw
              astVar = Ast.AstFromS @(TKS2 sh x) (ftkToStk ftk)
                       $ Ast.AstVar (FTKS sh x) var
          in if var `DMap.member` memo
             then (memo, astVar)
             else let (memo1, a2) = unshareAst memo (Ast.AstSFromX @sh a)
                  in (DMap.insert var a2 memo1, astVar)
      -- TODO: also recursively product
      ftk -> let var = varRaw
                 astVar = Ast.AstVar ftk var
             in if var `DMap.member` memo
                then (memo, astVar)  -- TODO: memoize AstVar itself
                else let (memo1, a2) = unshareAst memo a
                     in (DMap.insert var a2 memo1, astVar)
  Ast.AstShare{} -> error "unshareAst: AstShare not in PrimalSpan"
  Ast.AstToShare v -> (memo, v)  -- nothing to unshare in this subtree
  Ast.AstConcrete ftk t -> (memo, Ast.AstConcrete ftk t)

  Ast.AstSumOfList stk args ->
    let (memo2, args2) = mapAccumR unshareAst memo args
    in (memo2, Ast.AstSumOfList stk args2)

  Ast.AstN1K opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstN1K opCode u2)
  Ast.AstN2K opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstN2K opCode u2 v3)
  Ast.AstR1K opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstR1K opCode u2)
  Ast.AstR2K opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstR2K opCode u2 v3)
  Ast.AstI2K opCode u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstI2K opCode u2 v3)
  Ast.AstFloorK a -> second Ast.AstFloorK $ unshareAst memo a
  Ast.AstCastK v -> second Ast.AstCastK $ unshareAst memo v
  Ast.AstFromIntegralK v -> second Ast.AstFromIntegralK $ unshareAst memo v

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
  Ast.AstIndexS @sh1 v ix ->
    let (memo1, v2) = unshareAst memo v
        (memo2, ix2) = mapAccumR unshareAst memo1 (toList ix)
    in (memo2, Ast.AstIndexS @sh1 v2 (fromList ix2))
  Ast.AstScatterS @shm @shn @shp v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (unshareAstScoped $ toList vars)
                    memo (toList ix)
        (memo2, v2) = unshareAst memo1 v
    in (memo2, Ast.AstScatterS @shm @shn @shp v2 (vars, fromList ix2))
  Ast.AstAppendS x y ->
    let (memo1, t1) = unshareAst memo x
        (memo2, t2) = unshareAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (unshareAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (unshareAst memo v)
  Ast.AstTransposeS perm v ->
    second (Ast.AstTransposeS perm) $ unshareAst memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (unshareAst memo v)
  Ast.AstGatherS @shm @shn @shp v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (unshareAstScoped $ toList vars)
                    memo (toList ix)
        (memo2, v2) = unshareAst memo1 v
    in (memo2, Ast.AstGatherS @shm @shn @shp v2 (vars, fromList ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ unshareAst memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ unshareAst memo v
  Ast.AstZipS v -> second Ast.AstZipS (unshareAst memo v)
  Ast.AstUnzipS v -> second Ast.AstUnzipS (unshareAst memo v)

  Ast.AstFromS stkz v -> second (Ast.AstFromS stkz) $ unshareAst memo v
  Ast.AstSFromR v -> second Ast.AstSFromR $ unshareAst memo v
  Ast.AstSFromX v -> second Ast.AstSFromX $ unshareAst memo v

  Ast.AstXNestR v -> second Ast.AstXNestR $ unshareAst memo v
  Ast.AstXNestS v -> second Ast.AstXNestS $ unshareAst memo v
  Ast.AstXNest v -> second Ast.AstXNest $ unshareAst memo v
  Ast.AstXUnNestR v -> second Ast.AstXUnNestR $ unshareAst memo v
  Ast.AstXUnNestS v -> second Ast.AstXUnNestS $ unshareAst memo v
  Ast.AstXUnNest v -> second Ast.AstXUnNest $ unshareAst memo v

  Ast.AstApply t ll ->
    let (memo1, t2) = unshareAstHFun memo t
        (memo2, ll2) = unshareAst memo1 ll
    in (memo2, Ast.AstApply t2 ll2)
  Ast.AstMapAccumRDer k bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = unshareAst memo acc0
        (memo2, es2) = unshareAst memo1 es
    in (memo2, Ast.AstMapAccumRDer k bShs eShs f df rf acc02 es2)
  Ast.AstMapAccumLDer k bShs eShs f df rf acc0 es ->
    let (memo1, acc02) = unshareAst memo acc0
        (memo2, es2) = unshareAst memo1 es
    in (memo2, Ast.AstMapAccumLDer k bShs eShs f df rf acc02 es2)

  Ast.AstReplicate0NS sh stk v ->
    second (Ast.AstReplicate0NS sh stk) (unshareAst memo v)
  Ast.AstSum0S sh stk v ->
    second (Ast.AstSum0S sh stk) (unshareAst memo v)
  Ast.AstDot0S sh u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstDot0S sh u2 v3)
  Ast.AstDot1InS m n u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstDot1InS m n u2 v3)
  Ast.AstMatvecmulS m n u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstMatvecmulS m n u2 v3)
  Ast.AstMatmul2S m n p u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstMatmul2S m n p u2 v3)

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
