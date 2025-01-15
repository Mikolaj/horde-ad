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
  , liftRFromS1, liftRFromS2, liftXFromS1, liftXFromS2
  ) where

import Prelude hiding (foldl')

import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.List (foldl')
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (sameNat, type (+))
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape
  ( KnownShX (..)
  , shxAppend
  , shxDropSSX
  , shxSize
  , shxTakeSSX
  , ssxFromShape
  , withKnownShX
  )
import Data.Array.Nested
  (IShR, KnownShS (..), MapJust, Rank, Replicate, ShR (..), ShS (..))
import Data.Array.Nested.Internal.Shape
  ( shCvtRX
  , shCvtSX
  , shCvtXR'
  , shrInit
  , shrRank
  , shrSize
  , shrTail
  , shsAppend
  , shsPermutePrefix
  , shsRank
  , shsSize
  , withKnownShS
  )
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Ast
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

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
  AstFromVector snat l -> case V.toList l of
    [] -> error "ftkAst: empty vector"
    v : _ -> buildFTK snat (ftkAst v)
  AstSum snat stk v -> razeFTK snat stk (ftkAst v)
  AstReplicate snat _ v -> buildFTK snat (ftkAst v)
  AstBuild1 snat (_var, v) -> buildFTK snat (ftkAst v)
  AstLet _ _ v -> ftkAst v
  AstShare _ v -> ftkAst v
  AstToShare v -> ftkAst v
  AstConcrete ftk _ -> ftk

  AstSumOfList _ args -> case args of
    [] -> error "ftkAst: AstSumOfList with no arguments"
    v : _ -> ftkAst v

  AstN1{} -> FTKScalar
  AstN2{} -> FTKScalar
  AstR1{} -> FTKScalar
  AstR2{} -> FTKScalar
  AstI2{} -> FTKScalar
  AstFloor{} -> FTKScalar
  AstCast{} -> FTKScalar
  AstFromIntegral{} -> FTKScalar

  AstMinIndexR a -> FTKR (shrInit $ shapeAst a) FTKScalar
  AstMaxIndexR a -> FTKR (shrInit $ shapeAst a) FTKScalar
  AstFloorR a -> FTKR (shapeAst a) FTKScalar
  AstIotaR n -> FTKR (n :$: ZSR) FTKScalar
  AstN1R _opCode v -> ftkAst v
  AstN2R _opCode v _ -> ftkAst v
  AstR1R _opCode v -> ftkAst v
  AstR2R _opCode v _ -> ftkAst v
  AstI2R _opCode v _ -> ftkAst v
  AstIndex v _ -> case ftkAst v of
    FTKR sh x -> FTKR (dropShape sh) x
  AstScatter sh v _ -> case ftkAst v of
    FTKR _ x -> FTKR sh x
  AstAppend a b -> case ftkAst a of
    FTKR ZSR _ -> error "ftkAst: impossible pattern needlessly required"
    FTKR (ai :$: ash) x -> case shapeAst b of
      ZSR -> error "ftkAst: impossible pattern needlessly required"
      bi :$: _ -> FTKR (ai + bi :$: ash) x
  AstSlice _i n v -> case ftkAst v of
    FTKR sh x -> FTKR (n :$: shrTail sh) x
  AstReverse v -> ftkAst v
  AstTranspose perm v -> case ftkAst v of
    FTKR sh x -> FTKR (Nested.Internal.Shape.shrPermutePrefix perm sh) x
  AstReshape sh v -> case ftkAst v of
    FTKR _ x -> FTKR sh x
  AstGather sh v _ -> case ftkAst v of
    FTKR _ x -> FTKR sh x
  AstCastR v -> FTKR (shapeAst v) FTKScalar
  AstFromIntegralR a -> FTKR (shapeAst a) FTKScalar
  AstProjectR @_ @n l p -> case shapeAstHVector l V.! p of
    DynamicRankedDummy @_ @sh _ _ | SNat <- shsRank (knownShS @sh) ->
      case sameNat (Proxy @(Rank sh)) (Proxy @n) of
        Just Refl -> FTKR (shCastSR $ knownShS @sh) FTKScalar
        Nothing -> error "ftkAst: AstProjectR ill-typed"
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
  AstIndexS v _ix -> case ftkAst v of
    FTKS _sh1sh2 x -> FTKS knownShS x
  AstScatterS @_ @shn @shp v _ -> case ftkAst v of
    FTKS _ x -> FTKS (knownShS @shp `shsAppend` knownShS @shn) x
  AstAppendS a _ -> case ftkAst a of
    FTKS _ x -> FTKS knownShS x
  AstSliceS a -> case ftkAst a of
    FTKS _ x -> FTKS knownShS x
  AstReverseS v -> ftkAst v
  AstTransposeS @_ @sh2 perm v -> case ftkAst v of
    FTKS _ x ->
      withKnownShS (shsPermutePrefix perm (knownShS @sh2)) $
      FTKS knownShS x
  AstReshapeS v -> case ftkAst v of
    FTKS _ x -> FTKS knownShS x
  AstGatherS @shm @shn v _ -> case ftkAst v of
    FTKS _ x -> FTKS (knownShS @shm `shsAppend` knownShS @shn) x
  AstCastS{} -> FTKS knownShS FTKScalar
  AstFromIntegralS{} -> FTKS knownShS FTKScalar
  AstProjectS{} -> FTKS knownShS FTKScalar
  AstZipS v -> case ftkAst v of
    FTKProduct (FTKS sh y) (FTKS _ z) -> FTKS sh (FTKProduct y z)
  AstUnzipS v -> case ftkAst v of
    FTKS sh (FTKProduct y z) -> FTKProduct (FTKS sh y) (FTKS sh z)

  AstFromS @_ @z v ->
    let fromS :: FullTensorKind y2 -> STensorKindType z2 -> FullTensorKind z2
        fromS ftk stk = case (ftk, stk) of
          _ | Just Refl <- sameSTK (ftkToStk ftk) stk -> ftk
          (FTKS ZSS (FTKScalar @r), STKScalar tr) ->
            case testEquality (typeRep @r) tr of
              Just Refl -> FTKScalar
              Nothing -> error "ftkAst: wrong tensor kinds for AstFromS"
          (FTKS sh x, STKR nx zx) ->
            case ( sameSTK (ftkToStk x) zx
                 , testEquality (shsRank sh) nx ) of
              (Just Refl, Just Refl) -> FTKR (shCastSR sh) x
              _ -> error $ "ftkAst: wrong tensor kinds for AstFromS: "
                           ++ show (ftkToStk x) ++ " vs " ++ show zx ++ " and "
                           ++ show sh ++ " vs " ++ show nx
          (FTKS sh x, STKX shx zx) ->
            case ( sameSTK (ftkToStk x) zx
                 , testEquality (shsRank sh) (ssxRank shx) ) of
              (Just Refl, Just Refl) -> FTKX (shCastSX shx sh) x
              _ -> error "ftkAst: wrong tensor kinds for AstFromS"
          (FTKProduct ftk1 ftk2, STKProduct stk1 stk2) ->
            FTKProduct (fromS ftk1 stk1) (fromS ftk2 stk2)
          _ -> error "ftkAst: wrong tensor kinds for AstFromS"
    in fromS (ftkAst v) (stensorKind @z)
  AstSFromR v -> case ftkAst v of
    FTKR _ x -> FTKS knownShS x
  AstSFromX v -> case ftkAst v of
    FTKX _ x -> FTKS knownShS x

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
  AstXUnNestR v -> case ftkAst v of
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
    $ V.map (voidFromDynamicF (toList . shapeAst)) v
  AstApply v _ll -> shapeAstHFun v
  AstMapAccumRDer @accShs @bShs k bShs _eShs _f _df _rf acc0 _es
    | Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct (ftkAst acc0) (buildFTK k bShs)
  AstMapAccumLDer @accShs @bShs k bShs _eShs _f _df _rf acc0 _es
    | Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct (ftkAst acc0) (buildFTK k bShs)

  AstReplicate0NR sh _ v -> case ftkAst v of
    FTKR _ x -> FTKR sh x
  AstSum0R _ _ v ->  case ftkAst v of
    FTKR _ x -> FTKR ZSR x
  AstDot0R _ _u _v -> FTKR ZSR FTKScalar
  AstDot1InR u _v -> case ftkAst u of
    FTKR (m :$: _) FTKScalar -> FTKR (m :$: ZSR) FTKScalar
  AstMatvecmulR u _v -> case ftkAst u of
    FTKR (m :$: _) FTKScalar -> FTKR (m :$: ZSR) FTKScalar
  AstMatmul2R u v -> case (ftkAst u, ftkAst v) of
    (FTKR (m :$: _ :$: ZSR) FTKScalar, FTKR (_ :$: p :$: ZSR) FTKScalar) ->
      FTKR (m :$: p :$: ZSR) FTKScalar
    _ -> error "ftkAst: impossible pattern needlessly required"
  AstReplicate0NS sh _ v -> case ftkAst v of
    FTKS _ x -> FTKS sh x
  AstSum0S _ _ v ->  case ftkAst v of
    FTKS _ x -> FTKS ZSS x
  AstDot0S _ _u _v -> FTKS ZSS FTKScalar
  AstDot1InS m@SNat _ _u _v -> FTKS (m :$$ ZSS) FTKScalar
  AstMatvecmulS m@SNat _ _u _v -> FTKS (m :$$ ZSS) FTKScalar
  AstMatmul2S m@SNat _ p@SNat _u _v -> FTKS (m :$$ p :$$ ZSS) FTKScalar

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
  AstFromVector _ vl -> any (varInAst var) $ V.toList vl
  AstSum _ _ v -> varInAst var v
  AstReplicate _ _ v -> varInAst var v
  AstBuild1 _ (var2, v) ->
    assert (varNameToAstVarId var2 /= var) $
    varInAst var v
  AstLet _var2 u v -> varInAst var u || varInAst var v
  AstShare _ v -> varInAst var v
  AstToShare v -> varInAst var v
  AstConcrete{} -> False

  AstSumOfList _ l -> any (varInAst var) l

  AstN1 _ t -> varInAst var t
  AstN2 _ t u -> varInAst var t || varInAst var u
  AstR1 _ t -> varInAst var t
  AstR2 _ t u -> varInAst var t || varInAst var u
  AstI2 _ t u -> varInAst var t || varInAst var u
  AstFloor a -> varInAst var a
  AstCast t -> varInAst var t
  AstFromIntegral t -> varInAst var t

  AstN1R _ t -> varInAst var t
  AstN2R _ t u -> varInAst var t || varInAst var u
  AstR1R _ t -> varInAst var t
  AstR2R _ t u -> varInAst var t || varInAst var u
  AstI2R _ t u -> varInAst var t || varInAst var u
  AstMinIndexR a -> varInAst var a
  AstMaxIndexR a -> varInAst var a
  AstFloorR a -> varInAst var a
  AstIotaR{} -> False
  AstIndex v ix -> varInAst var v || varInIndex var ix
  AstScatter _ v (_vars, ix) -> varInIndex var ix || varInAst var v
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
  AstIndexS v ix -> varInAst var v || varInIndexS var ix
  AstScatterS v (_vars, ix) -> varInIndexS var ix || varInAst var v
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

  AstFromS v -> varInAst var v
  AstSFromR v -> varInAst var v
  AstSFromX v -> varInAst var v

  AstXNestR v -> varInAst var v
  AstXNestS v -> varInAst var v
  AstXNest v -> varInAst var v
  AstXUnNestR v -> varInAst var v
  AstXUnNestS v -> varInAst var v
  AstXUnNest v -> varInAst var v

  AstMkHVector l -> any (varInAstDynamic var) l
  AstApply t ll -> varInAstHFun var t || varInAst var ll
  AstMapAccumRDer _k _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstMapAccumLDer _k _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es

  AstReplicate0NR _ _ v -> varInAst var v
  AstSum0R _ _ v -> varInAst var v
  AstDot0R _ u v -> varInAst var u || varInAst var v
  AstDot1InR u v -> varInAst var u || varInAst var v
  AstMatvecmulR u v -> varInAst var u || varInAst var v
  AstMatmul2R u v -> varInAst var u || varInAst var v
  AstReplicate0NS _ _ v -> varInAst var v
  AstSum0S _ _ v -> varInAst var v
  AstDot0S _ u v -> varInAst var u || varInAst var v
  AstDot1InS _ _ u v -> varInAst var u || varInAst var v
  AstMatvecmulS _ _ u v -> varInAst var u || varInAst var v
  AstMatmul2S _ _ _ u v -> varInAst var u || varInAst var v

varInIndex :: AstVarId -> AstIxR ms n -> Bool
varInIndex var = any (varInAst var)

varInIndexS :: AstVarId -> AstIxS ms sh -> Bool
varInIndexS var = any (varInAst var)

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
  AstReplicate _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via tricks, so prob. safe
  AstConcrete FTKScalar _ -> True
  AstConcrete (FTKR sh FTKScalar) _ -> shrSize sh <= 1
  AstConcrete (FTKS sh FTKScalar) _ -> shsSize sh <= 1
  AstConcrete (FTKX sh FTKScalar) _ -> shxSize sh <= 1
  AstConcrete{} -> False

  AstIotaR{} -> True
  AstFromVector snat v | sNatValue snat == 1 -> astIsSmall relaxed $ v V.! 0
  AstSlice _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTranspose _ v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstProjectR t _ -> astIsSmall relaxed t

  AstIotaS -> True
  AstSliceS v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTransposeS _perm v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstProjectS t _ -> astIsSmall relaxed t
  AstFromS v -> astIsSmall relaxed v
  AstSFromR v -> astIsSmall relaxed v
  AstSFromX v -> astIsSmall relaxed v

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

liftRFromS1 :: forall n x ms s. TensorKind x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
liftRFromS1 f (AstFromS @yu u) =
  case stensorKind @yu of
    STKS @shu shu xu ->
      withKnownShS shu $
      case sameSTK (stensorKind @x) xu of
        Just Refl -> AstFromS $ f u
        _ -> error $ "liftRFromS1: tensor kinds don't agree: "
                     ++ show (stensorKind @yu) ++ " "
                     ++ show (stensorKind @(TKS2 shu x))
    _ -> error "liftRFromS1: unexpected tensor kind"
liftRFromS1 f a = case ftkAst a of
  FTKR sh' x | Dict <- lemTensorKindOfSTK (ftkToStk x)
             , SNat <- shrRank sh' ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS @(TKS2 sh x) $ f (AstSFromR @sh a)

liftRFromS2 :: forall n x ms s. TensorKind x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x) -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
liftRFromS2 f (AstFromS @yu u) (AstFromS @yv v) =
  case (stensorKind @yu, stensorKind @yv) of
    (STKS @shu shu xu, STKS @shv shv xv) ->
      withKnownShS shu $
      withKnownShS shv $
      case ( sameShape @shu @shv
           , sameSTK (stensorKind @x) xu
           , sameSTK (stensorKind @x) xv ) of
      (Just Refl, Just Refl, Just Refl) ->
        AstFromS $ f u v
      _ -> error $ "liftRFromS2: tensor kinds don't agree: "
                   ++ show (stensorKind @yu) ++ " "
                   ++ show (stensorKind @yv) ++ " "
                   ++ show (stensorKind @(TKR2 n x))
    _ -> error "liftRFromS2: unexpected tensor kinds"
liftRFromS2 f a b  = case ftkAst a of
  FTKR sh' x | Dict <- lemTensorKindOfSTK (ftkToStk x)
             , SNat <- shrRank sh' ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS @(TKS2 sh x) $ f (AstSFromR @sh a) (AstSFromR @sh b)

liftXFromS1 :: forall sh' x ms s. TensorKind x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
liftXFromS1 f (AstFromS @yu u) =
  case stensorKind @yu of
    STKS @shu shu xu ->
      withKnownShS shu $
      case sameSTK (stensorKind @x) xu of
        Just Refl -> AstFromS $ f u
        _ -> error $ "liftXFromS1: tensor kinds don't agree: "
                     ++ show (stensorKind @yu) ++ " "
                     ++ show (stensorKind @(TKS2 shu x))
    _ -> error "liftXFromS1: unexpected tensor kind"
liftXFromS1 f a = case ftkAst a of
  FTKX sh' x | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
    withKnownShX (ssxFromShape sh') $
    withCastXS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS @(TKS2 sh x) @(TKX2 sh' x) $ f (AstSFromX @sh @sh' a)

liftXFromS2 :: forall sh' x ms s. TensorKind x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x) -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
liftXFromS2 f (AstFromS @yu u) (AstFromS @yv v) =
  case (stensorKind @yu, stensorKind @yv) of
    (STKS @shu shu xu, STKS @shv shv xv) ->
      withKnownShS shu $
      withKnownShS shv $
      case ( sameShape @shu @shv
           , sameSTK (stensorKind @x) xu
           , sameSTK (stensorKind @x) xv ) of
        (Just Refl, Just Refl, Just Refl) ->
          AstFromS $ f u v
        _ -> error $ "liftXFromS2: tensor kinds don't agree: "
                     ++ show (stensorKind @yu) ++ " "
                     ++ show (stensorKind @yv) ++ " "
                     ++ show (stensorKind @(TKS2 shu x))
    _ -> error "liftXFromS2: unexpected tensor kinds"
liftXFromS2 f a b  = case ftkAst a of
  FTKX sh' x | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
    withKnownShX (ssxFromShape sh') $
    withCastXS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS @(TKS2 sh x) @(TKX2 sh' x)
      $ f (AstSFromX @sh @sh' a) (AstSFromX @sh @sh' b)
