-- | Inlining and global sharing elimination.
module HordeAd.Core.AstInline
  ( -- * Inlining
    inlineAst
    -- * Translation of global sharing to local lets
  , unshareAstTensor
  ) where

import Prelude

import Control.Arrow (second)
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.EnumMap.Strict qualified as EM
import Data.Foldable qualified as Foldable
import Data.List (mapAccumR)
import Data.Some
import Data.Type.Equality ((:~:) (Refl))
import GHC.Exts (IsList (..))

import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast (AstBool, AstTensor)
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstSimplify (substituteAst)
import HordeAd.Core.AstTools
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The pass that inlines lets with the bottom-up strategy

type AstMemo = EM.EnumMap AstVarId Int

-- | This inlines 'AstLet', traversing the term bottom-up.
inlineAst
  :: forall s y. AstSpan s
  => AstMemo -> AstTensor AstMethodLet s y
  -> (AstMemo, AstTensor AstMethodLet s y)
inlineAst memo v0 = case v0 of
  Ast.AstPair t1 t2 ->
    let (memo2, v1) = inlineAst memo t1
        (memo3, v2) = inlineAst memo2 t2
    in (memo3, Ast.AstPair v1 v2)
  Ast.AstProject1 t -> second Ast.AstProject1 (inlineAst memo t)
  Ast.AstProject2 t -> second Ast.AstProject2 (inlineAst memo t)
  Ast.AstFromVector snat stk l ->
    let (memo2, l2) = mapAccumR inlineAst memo l
    in (memo2, Ast.AstFromVector snat stk l2)
  Ast.AstSum snat stk v -> second (Ast.AstSum snat stk) (inlineAst memo v)
  Ast.AstReplicate snat stk v ->
    second (Ast.AstReplicate snat stk) (inlineAst memo v)
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFun memo f
        (memo2, df2) = inlineAstHFun memo1 df
        (memo3, rf2) = inlineAstHFun memo2 rf
        (memo4, acc02) = inlineAst memo3 acc0
        (memo5, es2) = inlineAst memo4 es
    in (memo5, Ast.AstMapAccumRDer k bftk eftk f2 df2 rf2 acc02 es2)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    let (memo1, f2) = inlineAstHFun memo f
        (memo2, df2) = inlineAstHFun memo1 df
        (memo3, rf2) = inlineAstHFun memo2 rf
        (memo4, acc02) = inlineAst memo3 acc0
        (memo5, es2) = inlineAst memo4 es
    in (memo5, Ast.AstMapAccumLDer k bftk eftk f2 df2 rf2 acc02 es2)
  Ast.AstApply t ll ->
    let (memo1, t2) = inlineAstHFun memo t
        (memo2, ll2) = inlineAst memo1 ll
    in (memo2, Ast.AstApply t2 ll2)
  Ast.AstVar var ->
    let f Nothing = Just 1
        f (Just count) = Just $ count + 1
    in (EM.alter f (varNameToAstVarId var) memo, v0)
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
  Ast.AstBuild1 k stk (var, v) ->
    let (memoV0, !v2) = inlineAst EM.empty v
        memo1 = EM.unionWith
                  (\c1 c0 -> c1 + sNatValue k * c0) memo memoV0
    in (memo1, Ast.AstBuild1 k stk (var, v2))

  Ast.AstLet var u v ->
    -- We assume there are no nested lets with the same variable, hence
    -- the delete and hence var couldn't appear in memo, so we can make
    -- the recursive call for v with memo intact, to record extra occurrences
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

  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ inlineAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ inlineAst memo a
  Ast.AstFromPrimal a -> second Ast.AstFromPrimal $ inlineAst memo a
  Ast.AstFromDual a -> second Ast.AstFromDual $ inlineAst memo a

  Ast.AstPlusK u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstPlusK u2 v3)
  Ast.AstTimesK u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstTimesK u2 v3)
  Ast.AstN1K opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstN1K opCode u2)
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
  Ast.AstConcreteK{} -> (memo, v0)
  Ast.AstFloorK a -> second Ast.AstFloorK $ inlineAst memo a
  Ast.AstFromIntegralK a -> second Ast.AstFromIntegralK $ inlineAst memo a
  Ast.AstCastK a -> second Ast.AstCastK $ inlineAst memo a

  Ast.AstPlusS u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstPlusS u2 v3)
  Ast.AstTimesS u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstTimesS u2 v3)
  Ast.AstN1S opCode u ->
    let (memo2, u2) = inlineAst memo u
    in (memo2, Ast.AstN1S opCode u2)
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
  Ast.AstConcreteS{} -> (memo, v0)
  Ast.AstFloorS a -> second Ast.AstFloorS $ inlineAst memo a
  Ast.AstFromIntegralS v -> second Ast.AstFromIntegralS $ inlineAst memo v
  Ast.AstCastS v -> second Ast.AstCastS $ inlineAst memo v

  Ast.AstIndexS @sh1 shn v ix ->
    let (memo1, v2) = inlineAst memo v
        (memo2, ix2) = mapAccumR inlineAst memo1 (Foldable.toList ix)
    in withKnownShS (shsFromIxS ix)
       (memo2, Ast.AstIndexS @sh1 shn v2 (fromList ix2))
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty (Foldable.toList ix)
        count = shsSize (shsFromIxS ix) * shsSize shn
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
        !ix3 = withKnownShS (shsFromIxS ix) $ fromList ix2
    in (memo2, Ast.AstScatterS @shm @shn @shp shn v2 (vars, ix3))
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAst EM.empty (Foldable.toList ix)
        count = shsSize (shsFromListS vars) * shsSize shn
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
        !ix3 = withKnownShS (shsFromIxS ix) $ fromList ix2
    in (memo2, Ast.AstGatherS @shm @shn @shp shn v2 (vars, ix3))
  Ast.AstMinIndexS a -> second Ast.AstMinIndexS $ inlineAst memo a
  Ast.AstMaxIndexS a -> second Ast.AstMaxIndexS $ inlineAst memo a
  Ast.AstIotaS{} -> (memo, v0)
  Ast.AstAppendS x y ->
    let (memo1, t1) = inlineAst memo x
        (memo2, t2) = inlineAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS i n k v -> second (Ast.AstSliceS i n k) (inlineAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (inlineAst memo v)
  Ast.AstTransposeS perm v -> second (Ast.AstTransposeS perm) $ inlineAst memo v
  Ast.AstReshapeS sh v -> second (Ast.AstReshapeS sh) (inlineAst memo v)

  Ast.AstConvert c v -> second (Ast.AstConvert c) $ inlineAst memo v

  Ast.AstSum0S v -> second Ast.AstSum0S (inlineAst memo v)
  Ast.AstDot0S u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstDot0S u2 v3)
  Ast.AstDot1InS m n u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstDot1InS m n u2 v3)
  Ast.AstMatmul2S m n p u v ->
    let (memo2, u2) = inlineAst memo u
        (memo3, v3) = inlineAst memo2 v
    in (memo3, Ast.AstMatmul2S m n p u2 v3)

inlineAstHFun
  :: AstSpan s2
  => AstMemo -> AstHFun s s2 x y -> (AstMemo, AstHFun s s2 x y)
inlineAstHFun memo v0 = case v0 of
  Ast.AstLambda var l ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards.
    (memo, Ast.AstLambda var (snd $ inlineAst EM.empty l))

inlineAstBool :: AstMemo -> AstBool AstMethodLet
              -> (AstMemo, AstBool AstMethodLet)
inlineAstBool memo v0 = case v0 of
  Ast.AstBoolConst{} -> (memo, v0)
  Ast.AstBoolNot arg ->
    let (memo2, arg2) = inlineAstBool memo arg
    in (memo2, Ast.AstBoolNot arg2)
  Ast.AstBoolAnd arg1 arg2 ->
    let (memo1, b1) = inlineAstBool memo arg1
        (memo2, b2) = inlineAstBool memo1 arg2
    in (memo2, Ast.AstBoolAnd b1 b2)
  Ast.AstLeqK arg1 arg2 ->
    let (memo1, r1) = inlineAst memo arg1
        (memo2, r2) = inlineAst memo1 arg2
    in (memo2, Ast.AstLeqK r1 r2)
  Ast.AstLeqS arg1 arg2 ->
    let (memo1, r1) = inlineAst memo arg1
        (memo2, r2) = inlineAst memo1 arg2
    in (memo2, Ast.AstLeqS r1 r2)


-- * Translation of global sharing to normal lets

type AstBindings = DEnumMap (AstVarName PrimalSpan)
                            (AstTensor AstMethodLet PrimalSpan)

bindsToLet :: forall s y.
              AstTensor AstMethodLet s y -> AstBindings
           -> AstTensor AstMethodLet s y
{-# INLINE bindsToLet #-}  -- help list fusion
bindsToLet u0 bs = foldl' bindToLet u0 (DMap.toDescList bs)
 where
  bindToLet :: AstTensor AstMethodLet s y
            -> DSum (AstVarName PrimalSpan)
                    (AstTensor AstMethodLet PrimalSpan)
            -> AstTensor AstMethodLet s y
  bindToLet !u (var :=> w) = Ast.AstLet var w u

-- | This replaces 'AstShare' with 'AstLet', traversing the term bottom-up.
unshareAstTensor :: AstTensor AstMethodShare PrimalSpan y
                 -> AstTensor AstMethodLet PrimalSpan y
unshareAstTensor tShare =
  let (memoOut, tLet) = unshareAst DMap.empty tShare
  in bindsToLet tLet memoOut

-- This works only because the other code never inserts the same rshare
-- into more than one index element, with the share containing
-- the gather/scatter/build variables corresponding to the index.
unshareAstScoped
  :: forall z s. AstSpan s
  => [IntVarName] -> AstBindings -> AstTensor AstMethodShare s z
  -> (AstBindings, AstTensor AstMethodLet s z)
unshareAstScoped vars0 memo0 v0 =
  let (memo1, v1) = unshareAst memo0 v0
      memoDiff = DMap.difference memo1 memo0
      varsOccur :: [AstVarId] -> AstTensor AstMethodLet PrimalSpan y -> Bool
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

-- So far, there are no lets in the resulting term,
-- but we mark it as potentially containing lets, because in the future
-- we may optimize this by inserting some lets not at the top-level.
unshareAst
  :: forall s y. AstSpan s
  => AstBindings -> AstTensor AstMethodShare s y
  -> (AstBindings, AstTensor AstMethodLet s y)
unshareAst memo = \case
  Ast.AstPair t1 t2 ->
    let (memo1, v1) = unshareAst memo t1
        (memo2, v2) = unshareAst memo1 t2
    in (memo2, Ast.AstPair v1 v2)
  Ast.AstProject1 t -> second Ast.AstProject1 (unshareAst memo t)
  Ast.AstProject2 t -> second Ast.AstProject2 (unshareAst memo t)
  Ast.AstFromVector snat stk l ->
    let (memo2, l2) = mapAccumR unshareAst memo l
    in (memo2, Ast.AstFromVector snat stk l2)
  Ast.AstSum snat stk v -> second (Ast.AstSum snat stk) (unshareAst memo v)
  Ast.AstReplicate snat stk v ->
    second (Ast.AstReplicate snat stk) (unshareAst memo v)
  Ast.AstMapAccumRDer k bftk eftk f df rf acc0 es ->
    let (memo1, acc02) = unshareAst memo acc0
        (memo2, es2) = unshareAst memo1 es
    in (memo2, Ast.AstMapAccumRDer k bftk eftk f df rf acc02 es2)
  Ast.AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    let (memo1, acc02) = unshareAst memo acc0
        (memo2, es2) = unshareAst memo1 es
    in (memo2, Ast.AstMapAccumLDer k bftk eftk f df rf acc02 es2)
  Ast.AstApply t ll ->
    let (memo1, t2) = unshareAstHFun memo t
        (memo2, ll2) = unshareAst memo1 ll
    in (memo2, Ast.AstApply t2 ll2)
  Ast.AstVar v -> (memo, Ast.AstVar v)
  Ast.AstCond b a2 a3 ->
    let (memo1, b1) = unshareAstBool memo b
        (memo2, t2) = unshareAst memo1 a2
        (memo3, t3) = unshareAst memo2 a3
    in (memo3, Ast.AstCond b1 t2 t3)
  Ast.AstBuild1 snat stk (var, v) ->
    let (memo1, !v2) = unshareAstScoped [var] memo v
    in (memo1, Ast.AstBuild1 snat stk (var, v2))

  -- We assume v is the same if var is the same.
  Ast.AstShare varRaw a | Just Refl <- sameAstSpan @s @PrimalSpan -> case a of
    AstFromS' @y2 ftkz v ->
      let var = mkAstVarName
                  (ftkAst v) (varNameToBounds varRaw) (varNameToAstVarId varRaw)
          astVar0 = cAstFromS @y2 ftkz $ Ast.AstVar var
      in if var `DMap.member` memo
         then (memo, astVar0)
         else let (memo1, !a2) = unshareAst memo v
                    -- DMap is strict, but let's be paranoid
              in (DMap.insert var a2 memo1, astVar0)
    -- The PrimalSpan check ensures there's no need to match for
    -- Ast.AstFromPrimal (Ast.AstFromS).
    _ -> case varNameToFTK varRaw of
      ftk@(FTKR @_ @x sh' x) ->
        withCastRS sh' $ \(sh :: ShS sh) ->
          let var = mkAstVarName (FTKS sh x) (varNameToBounds varRaw)
                                 (varNameToAstVarId varRaw)
              astVar0 = cAstFromS @(TKS2 sh x) ftk $ Ast.AstVar var
          in if var `DMap.member` memo
             then (memo, astVar0)
             else let (memo1, !a2) = unshareAst memo (cAstSFromR @sh sh a)
                  in (DMap.insert var a2 memo1, astVar0)
      ftk@(FTKX @_ @x sh' x) ->
        withCastXS sh' $ \(sh :: ShS sh) ->
          let var = mkAstVarName (FTKS sh x) (varNameToBounds varRaw)
                                 (varNameToAstVarId varRaw)
              astVar0 = cAstFromS @(TKS2 sh x) ftk $ Ast.AstVar var
          in if var `DMap.member` memo
             then (memo, astVar0)
             else let (memo1, !a2) = unshareAst memo (cAstSFromX @sh sh a)
                  in (DMap.insert var a2 memo1, astVar0)
      -- it maybe not be worth it to recursively convert product
      -- so let's not do that until profiling shows we need it
      _ -> let var = varRaw
               astVar0 = Ast.AstVar var
           in if var `DMap.member` memo
              then (memo, astVar0)
              else let (memo1, !a2) = unshareAst memo a
                   in (DMap.insert var a2 memo1, astVar0)
  Ast.AstShare{} -> error "unshareAst: AstShare not in PrimalSpan"
  Ast.AstToShare v -> (memo, v)  -- nothing to unshare in this subtree

  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ unshareAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ unshareAst memo a
  Ast.AstFromPrimal a -> second Ast.AstFromPrimal $ unshareAst memo a
  Ast.AstFromDual a -> second Ast.AstFromDual $ unshareAst memo a

  Ast.AstPlusK u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstPlusK u2 v3)
  Ast.AstTimesK u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstTimesK u2 v3)
  Ast.AstN1K opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstN1K opCode u2)
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
  Ast.AstConcreteK k -> (memo, Ast.AstConcreteK k)
  Ast.AstFloorK a -> second Ast.AstFloorK $ unshareAst memo a
  Ast.AstFromIntegralK v -> second Ast.AstFromIntegralK $ unshareAst memo v
  Ast.AstCastK v -> second Ast.AstCastK $ unshareAst memo v

  Ast.AstPlusS u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstPlusS u2 v3)
  Ast.AstTimesS u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstTimesS u2 v3)
  Ast.AstN1S opCode u ->
    let (memo2, u2) = unshareAst memo u
    in (memo2, Ast.AstN1S opCode u2)
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
  Ast.AstConcreteS a -> (memo, Ast.AstConcreteS a)
  Ast.AstFloorS a -> second Ast.AstFloorS $ unshareAst memo a
  Ast.AstFromIntegralS v -> second Ast.AstFromIntegralS $ unshareAst memo v
  Ast.AstCastS v -> second Ast.AstCastS $ unshareAst memo v

  Ast.AstIndexS @sh1 shn v ix ->
    let (memo1, v2) = unshareAst memo v
        (memo2, ix2) = mapAccumR unshareAst memo1 (Foldable.toList ix)
    in withKnownShS (shsFromIxS ix)
       (memo2, Ast.AstIndexS @sh1 shn v2 (fromList ix2))
  Ast.AstScatterS @shm @shn @shp shn v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (unshareAstScoped $ listsToList vars)
                    memo (Foldable.toList ix)
        (memo2, v2) = unshareAst memo1 v
        !ix3 = withKnownShS (shsFromIxS ix) $ fromList ix2
    in (memo2, Ast.AstScatterS @shm @shn @shp shn v2 (vars, ix3))
  Ast.AstGatherS @shm @shn @shp shn v (vars, ix) ->
    let (memo1, ix2) =
          mapAccumR (unshareAstScoped $ listsToList vars)
                    memo (Foldable.toList ix)
        (memo2, v2) = unshareAst memo1 v
        !ix3 = withKnownShS (shsFromIxS ix) $ fromList ix2
    in (memo2, Ast.AstGatherS @shm @shn @shp shn v2 (vars, ix3))
  Ast.AstMinIndexS a -> second Ast.AstMinIndexS $ unshareAst memo a
  Ast.AstMaxIndexS a -> second Ast.AstMaxIndexS $ unshareAst memo a
  Ast.AstIotaS snat -> (memo, Ast.AstIotaS snat)
  Ast.AstAppendS x y ->
    let (memo1, t1) = unshareAst memo x
        (memo2, t2) = unshareAst memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS i n k v -> second (Ast.AstSliceS i n k) (unshareAst memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (unshareAst memo v)
  Ast.AstTransposeS perm v ->
    second (Ast.AstTransposeS perm) $ unshareAst memo v
  Ast.AstReshapeS sh v -> second (Ast.AstReshapeS sh) (unshareAst memo v)

  Ast.AstConvert c v -> second (Ast.AstConvert c) $ unshareAst memo v

  Ast.AstSum0S v -> second Ast.AstSum0S (unshareAst memo v)
  Ast.AstDot0S u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstDot0S u2 v3)
  Ast.AstDot1InS m n u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstDot1InS m n u2 v3)
  Ast.AstMatmul2S m n p u v ->
    let (memo2, u2) = unshareAst memo u
        (memo3, v3) = unshareAst memo2 v
    in (memo3, Ast.AstMatmul2S m n p u2 v3)

unshareAstHFun
  :: AstBindings -> AstHFun s s2 x y -> (AstBindings, AstHFun s s2 x y)
unshareAstHFun memo v0 = case v0 of
  Ast.AstLambda{} ->
    -- No other free variables in l, so no outside lets can reach there,
    -- so we don't need to pass the information from v upwards
    -- nor remove the Share constructors.
    (memo, v0)

unshareAstBool :: AstBindings -> AstBool AstMethodShare
               -> (AstBindings, AstBool AstMethodLet)
unshareAstBool memo = \case
  Ast.AstBoolConst t -> (memo, Ast.AstBoolConst t)
  Ast.AstBoolNot arg ->
    let (memo2, arg2) = unshareAstBool memo arg
    in (memo2, Ast.AstBoolNot arg2)
  Ast.AstBoolAnd arg1 arg2 ->
    let (memo1, b1) = unshareAstBool memo arg1
        (memo2, b2) = unshareAstBool memo1 arg2
    in (memo2, Ast.AstBoolAnd b1 b2)
  Ast.AstLeqK arg1 arg2 ->
    let (memo1, r1) = unshareAst memo arg1
        (memo2, r2) = unshareAst memo1 arg2
    in (memo2, Ast.AstLeqK r1 r2)
  Ast.AstLeqS arg1 arg2 ->
    let (memo1, r1) = unshareAst memo arg1
        (memo2, r2) = unshareAst memo1 arg2
    in (memo2, Ast.AstLeqS r1 r2)
