{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Inlining and other manipulations of the let-like constructors.
module HordeAd.Core.AstInline
  ( -- * Inlining and simplification pass operations to be applied after unlet
    simplifyArtifactRev, simplifyArtifactRevS
  , simplifyAst6, simplifyAst6S, simplifyAstDomains6
    -- * The unlet pass eliminating nested lets bottom-up
  , unletAst6, unletAst6S, unletAstDomains6
  ) where

import Prelude

import           Control.Arrow (second)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as OS
import qualified Data.EnumMap.Strict as EM
import qualified Data.EnumSet as ES
import           Data.List (mapAccumR)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)

import           HordeAd.Core.Ast (AstBool, AstDomains, AstRanked, AstShaped)
import           HordeAd.Core.Ast hiding
  (AstBool (..), AstDomains (..), AstRanked (..), AstShaped (..))
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.Types
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * Inlining and simplification pass operations to be applied after unlet

simplifyArtifactRev :: (GoodScalar r, KnownNat n)
                    => AstArtifactRev AstRanked r n
                    -> AstArtifactRev AstRanked r n
simplifyArtifactRev (vars, gradient, primal, sh) =
  (vars, simplifyAstDomains6 gradient, simplifyAst6 primal, sh)
{-# SPECIALIZE simplifyArtifactRev
  :: KnownNat n
  => AstArtifactRev AstRanked Double n
  -> AstArtifactRev AstRanked Double n #-}

simplifyArtifactRevS :: (GoodScalar r, OS.Shape sh)
                     => AstArtifactRev AstShaped r sh
                     -> AstArtifactRev AstShaped r sh
simplifyArtifactRevS (vars, gradient, primal, sh) =
  (vars, simplifyAstDomains6 gradient, simplifyAst6S primal, sh)
{-# SPECIALIZE simplifyArtifactRevS
  :: OS.Shape sh
  => AstArtifactRev AstShaped Double sh
  -> AstArtifactRev AstShaped Double sh #-}

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
  :: (GoodScalar r, OS.Shape sh, AstSpan s)
  => AstShaped s r sh -> AstShaped s r sh
simplifyAst6S = simplifyAstS . snd . inlineAstS EM.empty . simplifyAstS
{-# SPECIALIZE simplifyAst6S
  :: (OS.Shape sh, AstSpan s)
  => AstShaped s Double sh
  -> AstShaped s Double sh #-}

simplifyAstDomains6
  :: AstSpan s => AstDomains s -> AstDomains s
simplifyAstDomains6 =
  simplifyAstDomains . snd . inlineAstDomains EM.empty . simplifyAstDomains
    -- no specialization possible except for the tag type s

-- * The pass that inlines lets with the bottom-up strategy

type AstMemo = EM.EnumMap AstId Int

inlineAst
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => AstMemo
  -> AstRanked s r n -> (AstMemo, AstRanked s r n)
inlineAst memo v0 = case v0 of
  Ast.AstVar _ (AstVarName var) ->
    let f Nothing = Just 1
        f (Just count) = Just $ succ count
    in (EM.alter f (astVarIdToAstId var) memo, v0)
  Ast.AstLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let vv = varNameToAstId var
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
    -- occurences, but only dynamic occurences. Tensor expressions
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
  Ast.AstSToR v -> second Ast.AstSToR $ inlineAstS memo v
  Ast.AstConstant a -> second Ast.AstConstant $ inlineAst memo a
  Ast.AstPrimalPart a -> second Ast.AstPrimalPart $ inlineAst memo a
  Ast.AstDualPart a -> second Ast.AstDualPart $ inlineAst memo a
  Ast.AstD u u' ->
    let (memo1, t1) = inlineAst memo u
        (memo2, t2) = inlineAst memo1 u'
    in (memo2, Ast.AstD t1 t2)
  Ast.AstLetDomains vars l v ->  -- TODO: actually inline
    let (memo1, l2) = inlineAstDomains memo l
        (memo2, v2) = inlineAst memo1 v
    in (memo2, Ast.AstLetDomains vars l2 v2)

inlineAstDynamic
  :: AstSpan s
  => AstMemo -> DynamicExists (AstDynamic s)
  -> (AstMemo, DynamicExists (AstDynamic s))
inlineAstDynamic memo = \case
  DynamicExists (AstRToD w) ->
    second (DynamicExists . AstRToD) $ inlineAst memo w
  DynamicExists (AstSToD w) ->
    second (DynamicExists . AstSToD) $ inlineAstS memo w

inlineAstDomains
  :: AstSpan s
  => AstMemo -> AstDomains s -> (AstMemo, AstDomains s)
inlineAstDomains memo v0 = case v0 of
  Ast.AstDomains l ->
    second Ast.AstDomains $ mapAccumR inlineAstDynamic memo l
  Ast.AstDomainsLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let vv = varNameToAstId var
        (memo1, v2) = inlineAstDomains memo v
        memo1NoVar = EM.delete vv memo1
        (memo2, u2) = inlineAst memo1NoVar u
    in case EM.findWithDefault 0 vv memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substituteAstDomains (SubstitutionPayloadRanked u2) var v2)
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
        in ( EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
               -- u is small, so the union is fast
           , substituteAstDomains (SubstitutionPayloadRanked u0) var v2 )
      _ -> (memo2, Ast.AstDomainsLet var u2 v2)
  Ast.AstDomainsLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let vv = varNameToAstId var
        (memo1, v2) = inlineAstDomains memo v
        memo1NoVar = EM.delete vv memo1
        (memo2, u2) = inlineAstS memo1NoVar u
    in case EM.findWithDefault 0 vv memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substituteAstDomains (SubstitutionPayloadShaped u2) var v2)
      count | astIsSmallS (count < 10) u ->
        let (memoU0, u0) = inlineAstS EM.empty u
        in ( EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
               -- u is small, so the union is fast
           , substituteAstDomains (SubstitutionPayloadShaped u0) var v2 )
      _ -> (memo2, Ast.AstDomainsLetS var u2 v2)

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
  Ast.AstRel @n opCodeRel arg1 arg2 ->
    let (memo1, r1) = inlineAst memo arg1
        (memo2, r2) = inlineAst memo1 arg2
    in (memo2, Ast.AstRel opCodeRel r1 r2)
  Ast.AstRelS @n opCodeRel arg1 arg2 ->
    let (memo1, r1) = inlineAstS memo arg1
        (memo2, r2) = inlineAstS memo1 arg2
    in (memo2, Ast.AstRelS opCodeRel r1 r2)

inlineAstS
  :: forall sh s r. (GoodScalar r, OS.Shape sh, AstSpan s)
  => AstMemo
  -> AstShaped s r sh -> (AstMemo, AstShaped s r sh)
inlineAstS memo v0 = case v0 of
  Ast.AstVarS (AstVarName var) ->
    let f Nothing = Just 1
        f (Just count) = Just $ succ count
    in (EM.alter f (astVarIdToAstId var) memo, v0)
  Ast.AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let vv = varNameToAstId var
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
    -- occurences, but only dynamic occurences. Tensor expressions
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
        count = OS.sizeT @sh
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
        count = OS.sizeT @sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGatherS @sh2 @p v2 (vars, ShapedList.listToSized ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ inlineAstS memo v
  Ast.AstFromIntegralS v ->
    second Ast.AstFromIntegralS $ inlineAstS memo v
  Ast.AstConstS{} -> (memo, v0)
  Ast.AstRToS v -> second Ast.AstRToS $ inlineAst memo v
  Ast.AstConstantS a -> second Ast.AstConstantS $ inlineAstS memo a
  Ast.AstPrimalPartS a -> second Ast.AstPrimalPartS $ inlineAstS memo a
  Ast.AstDualPartS a -> second Ast.AstDualPartS $ inlineAstS memo a
  Ast.AstDS u u' ->
    let (memo1, t1) = inlineAstS memo u
        (memo2, t2) = inlineAstS memo1 u'
    in (memo2, Ast.AstDS t1 t2)
  Ast.AstLetDomainsS vars l v ->  -- TODO: actually inline
    let (memo1, l2) = inlineAstDomains memo l
        (memo2, v2) = inlineAstS memo1 v
    in (memo2, Ast.AstLetDomainsS vars l2 v2)


-- * The unlet pass eliminating nested lets bottom-up

data UnletEnv = UnletEnv
  { unletSet     :: ES.EnumSet AstId
  , unletADShare :: ADShare }

emptyUnletEnv :: ADShare -> UnletEnv
emptyUnletEnv = UnletEnv ES.empty

unletAstDomains6
  :: AstBindings (AstRanked PrimalSpan) -> ADShare
  -> AstDomains PrimalSpan
  -> AstDomains PrimalSpan
unletAstDomains6 astBindings l t =
  unletAstDomains (emptyUnletEnv l)
  $ bindsToDomainsLet (bindsToDomainsLet t astBindings) (assocsADShare l)

unletAst6
  :: (GoodScalar r, KnownNat n)
  => AstBindings (AstRanked PrimalSpan) -> ADShare
  -> AstRanked PrimalSpan r n
  -> AstRanked PrimalSpan r n
unletAst6 astBindings l t =
  unletAst (emptyUnletEnv l)
  $ bindsToLet (bindsToLet t astBindings) (assocsADShare l)

unletAst6S
  :: (GoodScalar r, OS.Shape sh)
  => AstBindings (AstRanked PrimalSpan) -> ADShare
  -> AstShaped PrimalSpan r sh
  -> AstShaped PrimalSpan r sh
unletAst6S astBindings l t =
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
    let vv = varNameToAstId var
    in if vv `ES.member` unletSet env
       then unletAst env v
       else let env2 = env {unletSet = ES.insert vv (unletSet env)}
            in Ast.AstLet var (unletAst env u) (unletAst env2 v)
  Ast.AstLetADShare l v ->
    let lassocs = subtractADShare l $ unletADShare env
          -- potentially prevents quadratic cost induced by tletWrap
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
  Ast.AstSToR v -> Ast.AstSToR (unletAstS env v)
  Ast.AstConstant v -> Ast.AstConstant (unletAst env v)
  Ast.AstPrimalPart v -> Ast.AstPrimalPart (unletAst env v)
  Ast.AstDualPart v -> Ast.AstDualPart (unletAst env v)
  Ast.AstD u u' -> Ast.AstD (unletAst env u) (unletAst env u')
  Ast.AstLetDomains vars l v ->
    let env2 = env {unletSet = unletSet env
                               `ES.union` ES.fromList (map astVarIdToAstId
                                                       $ V.toList vars)}
    in Ast.AstLetDomains vars (unletAstDomains env l) (unletAst env2 v)

unletAstDynamic
  :: AstSpan s
  => UnletEnv -> DynamicExists (AstDynamic s) -> DynamicExists (AstDynamic s)
unletAstDynamic env = \case
  DynamicExists (AstRToD u) -> DynamicExists $ AstRToD $ unletAst env u
  DynamicExists (AstSToD u) -> DynamicExists $ AstSToD $ unletAstS env u

unletAstDomains
  :: AstSpan s => UnletEnv -> AstDomains s -> AstDomains s
unletAstDomains env = \case
  Ast.AstDomains l -> Ast.AstDomains $ V.map (unletAstDynamic env) l
  Ast.AstDomainsLet var u v ->
    let vv = varNameToAstId var
    in if vv `ES.member` unletSet env
      then unletAstDomains env v
      else let env2 = env {unletSet = ES.insert vv (unletSet env)}
           in Ast.AstDomainsLet var (unletAst env u)
                                    (unletAstDomains env2 v)
  Ast.AstDomainsLetS var u v ->
    let vv = varNameToAstId var
    in if vv `ES.member` unletSet env
       then unletAstDomains env v
       else let env2 = env {unletSet = ES.insert vv (unletSet env)}
            in Ast.AstDomainsLetS var (unletAstS env u)
                                      (unletAstDomains env2 v)

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

unletAstS
  :: (GoodScalar r, OS.Shape sh, AstSpan s)
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
    let vv = varNameToAstId var
    in if vv `ES.member` unletSet env
       then unletAstS env v
       else let env2 = env {unletSet = ES.insert vv (unletSet env)}
            in Ast.AstLetS var (unletAstS env u) (unletAstS env2 v)
  Ast.AstLetADShareS l v ->
    let lassocs = subtractADShare l $ unletADShare env
          -- potentially prevents quadratic cost induced by tletWrap
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
  Ast.AstRToS v -> Ast.AstRToS (unletAst env v)
  Ast.AstConstantS v -> Ast.AstConstantS (unletAstS env v)
  Ast.AstPrimalPartS v -> Ast.AstPrimalPartS (unletAstS env v)
  Ast.AstDualPartS v -> Ast.AstDualPartS (unletAstS env v)
  Ast.AstDS u u' -> Ast.AstDS (unletAstS env u) (unletAstS env u')
  Ast.AstLetDomainsS vars l v ->
    let env2 = env {unletSet = unletSet env
                               `ES.union` ES.fromList (map astVarIdToAstId
                                                       $ V.toList vars)}
    in Ast.AstLetDomainsS vars (unletAstDomains env l) (unletAstS env2 v)
