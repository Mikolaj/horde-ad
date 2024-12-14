{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations working on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( -- * Shape calculation
    ftkAst, shapeAst
  , lengthAst, shapeAstHVector, shapeAstHFun
    -- * Variable occurrence detection
  , varInAst, varInAstBool, varInIndex
  , varInIndexS, varInAstDynamic, varNameInAst
    -- * Determining if a term is too small to require sharing
  , astIsSmall
    -- * Odds and ends
  , bindsToLet
  ) where

import Prelude hiding (foldl')

import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.List (foldl')
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (sameNat, type (+))
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  (KnownShX (..), shxAppend, shxDropSSX, shxSize, shxTakeSSX)
import Data.Array.Nested
  ( IShR
  , KnownShS (..)
  , MapJust
  , Replicate
  , ShR (..)
  , pattern (:$:)
  , pattern ZSR
  )
import Data.Array.Nested.Internal.Shape
  (shCvtRX, shCvtSX, shCvtXR', shrSize, shsSize)
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Ast
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Util.SizedList

-- * Shape calculation

ftkAst :: forall s y ms. AstTensor ms s y -> FullTensorKind y
ftkAst t = case t of
  AstFromScalar{} -> FTKS knownShS FTKScalar
  AstToScalar{} -> FTKScalar
  AstPair t1 t2 -> FTKProduct (ftkAst t1) (ftkAst t2)
  AstProject1 v -> case ftkAst v of
    FTKProduct ftk1 _ -> ftk1
  AstProject2 v -> case ftkAst v of
    FTKProduct _ ftk2 -> ftk2
  AstVar ftk _var -> ftk
  AstPrimalPart a -> ftkAst a
  AstDualPart a -> ftkAst a
  AstFromPrimal a -> ftkAst a
  AstD u _ -> ftkAst u
  AstCond _b v _w -> ftkAst v
  AstReplicate snat v -> buildFTK snat (ftkAst v)
  AstBuild1 snat (_var, v) -> buildFTK snat (ftkAst v)
  AstLet _ _ v -> ftkAst v
  AstShare _ v -> ftkAst v
  AstToShare v -> ftkAst v
  AstConcrete ftk _ -> ftk

  AstN1{} -> FTKScalar
  AstN2{} -> FTKScalar
  AstR1{} -> FTKScalar
  AstR2{} -> FTKScalar
  AstI2{} -> FTKScalar
  AstSumOfList{} -> FTKScalar
  AstFloor{} -> FTKScalar
  AstCast{} -> FTKScalar
  AstFromIntegral{} -> FTKScalar

  AstMinIndexR a -> FTKR (initShape $ shapeAst a) FTKScalar
  AstMaxIndexR a -> FTKR (initShape $ shapeAst a) FTKScalar
  AstFloorR a -> FTKR (shapeAst a) FTKScalar
  AstIotaR -> FTKR (singletonShape (maxBound :: Int)) FTKScalar  -- ought to be enough
  AstN1R _opCode v -> ftkAst v
  AstN2R _opCode v _ -> ftkAst v
  AstR1R _opCode v -> ftkAst v
  AstR2R _opCode v _ -> ftkAst v
  AstI2R _opCode v _ -> ftkAst v
  AstSumOfListR args -> case args of
    [] -> error "ftkAst: AstSumOfListR with no arguments"
    v : _ -> ftkAst v
  AstIndex v _ -> case ftkAst v of
    FTKR sh x -> FTKR (dropShape sh) x
  AstSum v -> FTKR (tailShape $ shapeAst v) FTKScalar
  AstScatter sh _ _ -> FTKR sh FTKScalar
  AstFromVector l -> case V.toList l of
    [] -> case stensorKind @y of
      STKR @n SNat STKScalar{} -> case sameNat (Proxy @n) (Proxy @1) of
        Just Refl -> FTKR (0 :$: ZSR) FTKScalar
        Nothing -> error "ftkAst: AstFromVector with no arguments"
      _ -> error "ftkAst: AstFromVector with no arguments"
    v : _ -> case ftkAst v of
      FTKR sh x -> FTKR (V.length l :$: sh) x
  AstAppend x y -> case shapeAst x of
    ZSR -> error "ftkAst: impossible pattern needlessly required"
    xi :$: xsh -> case shapeAst y of
      ZSR -> error "ftkAst: impossible pattern needlessly required"
      yi :$: _ -> FTKR (xi + yi :$: xsh) FTKScalar
  AstSlice _i n v -> FTKR (n :$: tailShape (shapeAst v)) FTKScalar
  AstReverse v -> ftkAst v
  AstTranspose perm v -> case ftkAst v of
    FTKR sh x -> FTKR (Nested.Internal.Shape.shrPermutePrefix perm sh) x
  AstReshape sh v -> case ftkAst v of
    FTKR _ x -> FTKR sh x
  AstGather sh _v (_vars, _ix) -> FTKR sh FTKScalar
  AstCastR v -> FTKR (shapeAst v) FTKScalar
  AstFromIntegralR a -> FTKR (shapeAst a) FTKScalar
  AstProjectR l p -> case shapeAstHVector l V.! p of
    DynamicRankedDummy @_ @sh _ _ -> FTKR (listToShape $ shapeT @sh) FTKScalar
    DynamicShapedDummy{} -> error "ftkAst: DynamicShapedDummy"
  AstLetHVectorIn _ _ v -> ftkAst v
  AstZipR v -> case ftkAst v of
    FTKProduct (FTKR sh y) (FTKR _ z) -> FTKR sh (FTKProduct y z)
  AstUnzipR v -> case ftkAst v of
    FTKR sh (FTKProduct y z) -> FTKProduct (FTKR sh y) (FTKR sh z)

  AstMinIndexS{} -> FTKS knownShS FTKScalar
  AstMaxIndexS{} -> FTKS knownShS FTKScalar
  AstFloorS{} -> FTKS knownShS FTKScalar
  AstIotaS{} -> FTKS knownShS FTKScalar
  AstN1S{} -> FTKS knownShS FTKScalar
  AstN2S{} -> FTKS knownShS FTKScalar
  AstR1S{} -> FTKS knownShS FTKScalar
  AstR2S{} -> FTKS knownShS FTKScalar
  AstI2S{} -> FTKS knownShS FTKScalar
  AstSumOfListS{} -> FTKS knownShS FTKScalar
  AstIndexS v _ix -> case ftkAst v of
    FTKS _sh1sh2 x -> FTKS knownShS x
  AstSumS{} -> FTKS knownShS FTKScalar
  AstScatterS{} -> FTKS knownShS FTKScalar
  AstFromVectorS l -> case V.toList l of
    [] -> case stensorKind @y of
      STKS _ STKScalar{} -> FTKS knownShS FTKScalar
        -- the only case where we can guess the x
      _ -> error "ftkAst: AstFromVectorS with no arguments"
    d : _ -> case ftkAst d of
      FTKS _ x -> FTKS knownShS x
  AstAppendS{} -> FTKS knownShS FTKScalar
  AstSliceS{} -> FTKS knownShS FTKScalar
  AstReverseS v -> ftkAst v
  AstTransposeS @perm @sh2 perm v -> case ftkAst v of
    FTKS _ x ->
      withShapeP
        (backpermutePrefixList (Permutation.permToList' perm)
                               (shapeT @sh2)) $ \(Proxy @sh2Perm) ->
          gcastWith (unsafeCoerce Refl :: sh2Perm :~: Permutation.PermutePrefix perm sh2) $
          FTKS knownShS x
  AstReshapeS v -> case ftkAst v of
    FTKS _ x -> FTKS knownShS x
  AstGatherS{} -> FTKS knownShS FTKScalar
  AstCastS{} -> FTKS knownShS FTKScalar
  AstFromIntegralS{} -> FTKS knownShS FTKScalar
  AstProjectS{} -> FTKS knownShS FTKScalar
  AstZipS v -> case ftkAst v of
    FTKProduct (FTKS sh y) (FTKS _ z) -> FTKS sh (FTKProduct y z)
  AstUnzipS v -> case ftkAst v of
    FTKS sh (FTKProduct y z) -> FTKProduct (FTKS sh y) (FTKS sh z)

  AstZipX v -> case ftkAst v of
    FTKProduct (FTKX sh y) (FTKX _ z) -> FTKX sh (FTKProduct y z)
  AstUnzipX v -> case ftkAst v of
    FTKX sh (FTKProduct y z) -> FTKProduct (FTKX sh y) (FTKX sh z)

  AstRFromS @sh v
   | Dict <- lemKnownNatRankS (knownShS @sh) -> case ftkAst v of
    FTKS _ x -> FTKR (fromList $ shapeT @sh) x
  AstRFromX @sh v
   | Dict <- lemKnownNatRankX (knownShX @sh) -> case ftkAst v of
    FTKX shx x -> FTKR (fromList $ toList shx) x
  AstSFromR v -> case ftkAst v of
    FTKR _ x -> FTKS knownShS x
  AstSFromX v -> case ftkAst v of
    FTKX _ x -> FTKS knownShS x
  AstXFromR @sh v
   | Dict <- lemKnownNatRankX (knownShX @sh) -> case ftkAst v of
    FTKR shr x -> FTKX (fromList $ toList shr) x
  AstXFromS v -> case ftkAst v of
    FTKS sh x -> FTKX (fromList $ toList sh) x

  AstXNestR @sh1 @m v -> case ftkAst v of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @(Replicate m Nothing))
                                  sh (knownShX @sh1))
                      (FTKR (shCvtXR' (shxDropSSX sh (knownShX @sh1))) x)
  AstXNestS @sh1 @sh2 v -> case ftkAst v of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @(MapJust sh2)) sh (knownShX @sh1))
                                  (FTKS knownShS x)
  AstXNest @sh1 @sh2 v -> case ftkAst v of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @sh2) sh (knownShX @sh1))
                      (FTKX (shxDropSSX sh (knownShX @sh1)) x)
  AstXUnNestR @_ @_ @m v -> case ftkAst v of
    FTKX sh1 (FTKR sh2 x) ->
      FTKX (sh1 `shxAppend` shCvtRX sh2) x
  AstXUnNestS v -> case ftkAst v of
    FTKX sh1 (FTKS sh2 x) ->
      FTKX (sh1 `shxAppend` shCvtSX sh2) x
  AstXUnNest v -> case ftkAst v of
    FTKX sh1 (FTKX sh2 x) ->
      FTKX (sh1 `shxAppend` sh2) x

  AstMkHVector v ->
    FTKUntyped
    $ V.map (voidFromDynamicF (shapeToList . shapeAst)) v
  AstApply v _ll -> shapeAstHFun v
  AstMapAccumRDer @accShs @bShs k accShs bShs _eShs _f _df _rf _acc0 _es
    | (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @accShs)
    , (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @bShs) ->
      FTKProduct accShs (buildFTK k bShs)
  AstMapAccumLDer @accShs @bShs k accShs bShs _eShs _f _df _rf _acc0 _es
    | (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @accShs)
    , (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @bShs) ->
      FTKProduct accShs (buildFTK k bShs)

  _ -> error "TODO"

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: forall n s x ms. AstTensor ms s (TKR2 n x) -> IShR n
shapeAst t = case ftkAst t of
  FTKR sh _ -> sh

-- Length of the outermost dimension.
lengthAst :: forall n s x ms. AstTensor ms s (TKR2 (1 + n) x) -> Int
{-# INLINE lengthAst #-}
lengthAst v1 = case shapeAst v1 of
  ZSR -> error "lengthAst: impossible pattern needlessly required"
  k :$: _ -> k

shapeAstHVector :: AstTensor ms s TKUntyped -> VoidHVector
shapeAstHVector t = case ftkAst t of
  FTKUntyped shs -> shs

shapeAstHFun :: AstHFun x y -> FullTensorKind y
shapeAstHFun = \case
  AstLambda ~(_vvars, _, l) -> ftkAst l


-- * Variable occurrence detection

-- We assume no variable is shared between a binding and its nested binding
-- and nobody asks about occurrences of variables that are bound.
-- This keeps the occurrence checking code simple, because we never need
-- to compare variables to any variable in the bindings.
varInAst :: AstVarId -> AstTensor ms s y -> Bool
varInAst var = \case
  AstFromScalar t -> varInAst var t
  AstToScalar t -> varInAst var t
  AstPair t1 t2 -> varInAst var t1 || varInAst var t2
  AstProject1 t -> varInAst var t
  AstProject2 t -> varInAst var t
  AstVar _ var2 -> var == varNameToAstVarId var2
  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstFromPrimal v -> varInAst var v
  AstD u u' -> varInAst var u || varInAst var u'
  AstCond b v w -> varInAstBool var b || varInAst var v || varInAst var w
  AstReplicate _ v -> varInAst var v
  AstBuild1 _ (_var2, v) -> varInAst var v
  AstLet _var2 u v -> varInAst var u || varInAst var v
  AstShare _ v -> varInAst var v
  AstToShare v -> varInAst var v
  AstConcrete{} -> False

  AstMinIndexR a -> varInAst var a
  AstMaxIndexR a -> varInAst var a
  AstFloorR a -> varInAst var a
  AstIotaR -> False
  AstN1 _ t -> varInAst var t
  AstN2 _ t u -> varInAst var t || varInAst var u
  AstR1 _ t -> varInAst var t
  AstR2 _ t u -> varInAst var t || varInAst var u
  AstI2 _ t u -> varInAst var t || varInAst var u
  AstFloor a -> varInAst var a
  AstCast t -> varInAst var t
  AstFromIntegral t -> varInAst var t
  AstSumOfList l -> any (varInAst var) l
  AstN1R _ t -> varInAst var t
  AstN2R _ t u -> varInAst var t || varInAst var u
  AstR1R _ t -> varInAst var t
  AstR2R _ t u -> varInAst var t || varInAst var u
  AstI2R _ t u -> varInAst var t || varInAst var u
  AstSumOfListR l -> any (varInAst var) l
  AstIndex v ix -> varInAst var v || varInIndex var ix
  AstSum v -> varInAst var v
  AstScatter _ v (_vars, ix) -> varInIndex var ix || varInAst var v
  AstFromVector vl -> any (varInAst var) $ V.toList vl
  AstAppend v u -> varInAst var v || varInAst var u
  AstSlice _ _ v -> varInAst var v
  AstReverse v -> varInAst var v
  AstTranspose _ v -> varInAst var v
  AstReshape _ v -> varInAst var v
  AstGather _ v (_vars, ix) -> varInIndex var ix || varInAst var v
  AstCastR t -> varInAst var t
  AstFromIntegralR t -> varInAst var t
  AstProjectR l _p -> varInAst var l
  AstLetHVectorIn _vars l v -> varInAst var l || varInAst var v
  AstZipR v -> varInAst var v
  AstUnzipR v -> varInAst var v

  AstMinIndexS a -> varInAst var a
  AstMaxIndexS a -> varInAst var a
  AstFloorS a -> varInAst var a
  AstIotaS -> False
  AstN1S _ t -> varInAst var t
  AstN2S _ t u -> varInAst var t || varInAst var u
  AstR1S _ t -> varInAst var t
  AstR2S _ t u -> varInAst var t || varInAst var u
  AstI2S _ t u -> varInAst var t || varInAst var u
  AstSumOfListS l -> any (varInAst var) l
  AstIndexS v ix -> varInAst var v || varInIndexS var ix
  AstSumS v -> varInAst var v
  AstScatterS v (_vars, ix) -> varInIndexS var ix || varInAst var v
  AstFromVectorS vl -> any (varInAst var) $ V.toList vl
  AstAppendS v u -> varInAst var v || varInAst var u
  AstSliceS v -> varInAst var v
  AstReverseS v -> varInAst var v
  AstTransposeS _perm v -> varInAst var v
  AstReshapeS v -> varInAst var v
  AstGatherS v (_vars, ix) -> varInIndexS var ix || varInAst var v
  AstCastS t -> varInAst var t
  AstFromIntegralS a -> varInAst var a
  AstProjectS l _p -> varInAst var l
  AstZipS v -> varInAst var v
  AstUnzipS v -> varInAst var v

  AstMinIndexX a -> varInAst var a
  AstMaxIndexX a -> varInAst var a
  AstFloorX a -> varInAst var a
  AstIotaX -> False
  AstN1X _ t -> varInAst var t
  AstN2X _ t u -> varInAst var t || varInAst var u
  AstR1X _ t -> varInAst var t
  AstR2X _ t u -> varInAst var t || varInAst var u
  AstI2X _ t u -> varInAst var t || varInAst var u
  AstSumOfListX l -> any (varInAst var) l
  AstIndexX v ix -> varInAst var v || varInIndexX var ix
  AstSumX v -> varInAst var v
  AstScatterX v (_vars, ix) -> varInIndexX var ix || varInAst var v
  AstFromVectorX vl -> any (varInAst var) $ V.toList vl
  AstAppendX v u -> varInAst var v || varInAst var u
  AstSliceX v -> varInAst var v
  AstReverseX v -> varInAst var v
  AstTransposeX _perm v -> varInAst var v
  AstReshapeX _ v -> varInAst var v
  AstGatherX v (_vars, ix) -> varInIndexX var ix || varInAst var v
  AstCastX t -> varInAst var t
  AstFromIntegralX a -> varInAst var a
  AstProjectX l _p -> varInAst var l
  AstZipX v -> varInAst var v
  AstUnzipX v -> varInAst var v

  AstRFromS v -> varInAst var v
  AstRFromX v -> varInAst var v
  AstSFromR v -> varInAst var v
  AstSFromX v -> varInAst var v
  AstXFromR v -> varInAst var v
  AstXFromS v -> varInAst var v

  AstXNestR v -> varInAst var v
  AstXNestS v -> varInAst var v
  AstXNest v -> varInAst var v
  AstXUnNestR v -> varInAst var v
  AstXUnNestS v -> varInAst var v
  AstXUnNest v -> varInAst var v

  AstMkHVector l -> any (varInAstDynamic var) l
  AstApply t ll -> varInAstHFun var t || varInAst var ll
  AstMapAccumRDer _k _accShs _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstMapAccumLDer _k _accShs _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es

varInIndex :: AstVarId -> AstIxR ms n -> Bool
varInIndex var = any (varInAst var)

varInIndexS :: AstVarId -> AstIxS ms sh -> Bool
varInIndexS var = any (varInAst var)

varInIndexX :: AstVarId -> AstIndexX ms sh -> Bool
varInIndexX var = any (varInAst var)

varInAstDynamic :: AstVarId -> AstDynamic ms s -> Bool
varInAstDynamic var = \case
  DynamicRanked t -> varInAst var t
  DynamicShaped t -> varInAst var t
  DynamicRankedDummy{} -> False
  DynamicShapedDummy{} -> False

varInAstHFun :: AstVarId -> AstHFun x y -> Bool
varInAstHFun _var = \case
  AstLambda{} -> False  -- we take advantage of the term being closed

varInAstBool :: AstVarId -> AstBool ms -> Bool
varInAstBool var = \case
  AstBoolNot b -> varInAstBool var b
  AstB2 _ arg1 arg2 -> varInAstBool var arg1 || varInAstBool var arg2
  AstBoolConst{} -> False
  AstRel _ arg1 arg2 -> varInAst var arg1 || varInAst var arg2

varNameInAst :: AstVarName f y -> AstTensor ms s2 y2 -> Bool
varNameInAst var = varInAst (varNameToAstVarId var)


-- * Determining if a term is too small to require sharing

astIsSmall :: Bool -> AstTensor ms s y -> Bool
astIsSmall relaxed = \case
  AstFromScalar{} -> True
  AstToScalar{} -> True
  AstPair t1 t2 -> astIsSmall relaxed t1 && astIsSmall relaxed t2
  AstProject1 t -> astIsSmall relaxed t
  AstProject2 t -> astIsSmall relaxed t
  AstVar{} -> True
  AstPrimalPart v -> astIsSmall relaxed v
  AstDualPart v -> astIsSmall relaxed v
  AstFromPrimal v -> astIsSmall relaxed v
  AstReplicate _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via tricks, so prob. safe
  AstConcrete FTKScalar _ -> True
  AstConcrete (FTKR sh FTKScalar) _ -> shrSize sh <= 1
  AstConcrete (FTKS sh FTKScalar) _ -> shsSize sh <= 1
  AstConcrete (FTKX sh FTKScalar) _ -> shxSize sh <= 1
  AstConcrete{} -> False

  AstIotaR -> True
  AstFromVector v | V.length v == 1 -> astIsSmall relaxed $ v V.! 0
  AstSlice _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTranspose _ v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstProjectR t _ -> astIsSmall relaxed t
  AstRFromS v -> astIsSmall relaxed v
  AstRFromX v -> astIsSmall relaxed v

  AstIotaS -> True
  AstFromVectorS v | V.length v == 1 -> astIsSmall relaxed $ v V.! 0
  AstSliceS v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTransposeS _perm v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstProjectS t _ -> astIsSmall relaxed t
  AstSFromR v -> astIsSmall relaxed v
  AstSFromX v -> astIsSmall relaxed v
  AstXFromR v -> astIsSmall relaxed v
  AstXFromS v -> astIsSmall relaxed v

  AstMkHVector v | V.length v == 1 -> case v V.! 0 of
    DynamicRanked t -> astIsSmall relaxed t
    DynamicShaped t -> astIsSmall relaxed t
    DynamicRankedDummy{} -> True
    DynamicShapedDummy{} -> True

  _ -> False


-- * Odds and ends

bindsToLet :: forall s y. TensorKind y
           => AstTensor AstMethodLet s y -> AstBindings
           -> AstTensor AstMethodLet s y
{-# INLINE bindsToLet #-}  -- help list fusion
bindsToLet u0 bs = foldl' bindToLet u0 (DMap.toDescList bs)
 where
  bindToLet :: AstTensor AstMethodLet s y
            -> DSum (AstVarName PrimalSpan)
                    (AstTensor AstMethodLet PrimalSpan)
            -> AstTensor AstMethodLet s y
  bindToLet !u (var :=> w)
    | Dict <- tensorKindFromAstVarName var =
      AstLet var w u
