{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations working on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( -- * Full tensor kind derivation
    ftkAst
    -- * Variable occurrence detection
  , varInAst, varInAstBool, varInIndexS, varNameInAst
    -- * Determining if a term is too small to require sharing
  , astIsSmall
    -- * Odds and ends
  , liftRFromS1, liftRFromS2, liftXFromS1, liftXFromS2
  , cAstSFromR, cAstSFromX
  ) where

import Prelude hiding (foldl')

import Control.Exception.Assert.Sugar
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, sameNat)
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
import Data.Array.Nested (KnownShS (..), MapJust, Rank, Replicate, ShS (..))
import Data.Array.Nested.Internal.Shape
  ( shCvtRX
  , shCvtSX
  , shCvtXR'
  , shrRank
  , shrSize
  , shsAppend
  , shsInit
  , shsPermutePrefix
  , shsRank
  , shsSize
  , withKnownShS
  )

import HordeAd.Core.Ast
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Full tensor kind derivation

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
ftkAst :: forall s y ms. AstTensor ms s y -> FullTensorKind y
ftkAst t = case t of
  AstSFromK{} -> FTKS ZSS FTKScalar
  AstPair t1 t2 -> FTKProduct (ftkAst t1) (ftkAst t2)
  AstProject1 v -> case ftkAst v of
    FTKProduct ftk1 _ -> ftk1
  AstProject2 v -> case ftkAst v of
    FTKProduct _ ftk2 -> ftk2
  AstVar ftk _var -> ftk
  AstPrimalPart a -> ftkAst a
  AstDualPart a -> ftkAst a
  AstFromPrimal a -> ftkAst a
  AstFromDual a -> ftkAst a
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

  AstN1K{} -> FTKScalar
  AstN2K{} -> FTKScalar
  AstR1K{} -> FTKScalar
  AstR2K{} -> FTKScalar
  AstI2K{} -> FTKScalar
  AstFloorK{} -> FTKScalar
  AstCastK{} -> FTKScalar
  AstFromIntegralK{} -> FTKScalar

  AstMinIndexS @sh @n _ -> FTKS (shsInit (knownShS @(n ': sh))) FTKScalar
  AstMaxIndexS @sh @n _ -> FTKS (shsInit (knownShS @(n ': sh))) FTKScalar
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
  AstZipS v -> case ftkAst v of
    FTKProduct (FTKS sh y) (FTKS _ z) -> FTKS sh (FTKProduct y z)
  AstUnzipS v -> case ftkAst v of
    FTKS sh (FTKProduct y z) -> FTKProduct (FTKS sh y) (FTKS sh z)

  AstFromS stkz v ->
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
          _ -> error $ "ftkAst: wrong tensor kinds for AstFromS: "
                       ++ show (ftk, stk)
    in fromS (ftkAst v) stkz
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

  AstApply (AstLambda ~(_vvars, _, l)) _ll -> ftkAst l
  AstMapAccumRDer @accShs @bShs k bShs _eShs _f _df _rf acc0 _es
    | Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct (ftkAst acc0) (buildFTK k bShs)
  AstMapAccumLDer @accShs @bShs k bShs _eShs _f _df _rf acc0 _es
    | Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct (ftkAst acc0) (buildFTK k bShs)

  AstReplicate0NS sh _ v -> case ftkAst v of
    FTKS _ x -> FTKS sh x
  AstSum0S _ _ v ->  case ftkAst v of
    FTKS _ x -> FTKS ZSS x
  AstDot0S _ _u _v -> FTKS ZSS FTKScalar
  AstDot1InS m@SNat _ _u _v -> FTKS (m :$$ ZSS) FTKScalar
  AstMatvecmulS m@SNat _ _u _v -> FTKS (m :$$ ZSS) FTKScalar
  AstMatmul2S m@SNat _ p@SNat _u _v -> FTKS (m :$$ p :$$ ZSS) FTKScalar


-- * Variable occurrence detection

-- We assume no variable is shared between a binding and its nested binding
-- and nobody asks about occurrences of variables that are bound.
-- This keeps the occurrence checking code simple, because we never need
-- to compare variables to any variable in the bindings.
varInAst :: AstVarId -> AstTensor ms s y -> Bool
varInAst var = \case
  AstSFromK t -> varInAst var t
  AstPair t1 t2 -> varInAst var t1 || varInAst var t2
  AstProject1 t -> varInAst var t
  AstProject2 t -> varInAst var t
  AstVar _ var2 -> var == varNameToAstVarId var2
  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstFromPrimal v -> varInAst var v
  AstFromDual v -> varInAst var v
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

  AstN1K _ t -> varInAst var t
  AstN2K _ t u -> varInAst var t || varInAst var u
  AstR1K _ t -> varInAst var t
  AstR2K _ t u -> varInAst var t || varInAst var u
  AstI2K _ t u -> varInAst var t || varInAst var u
  AstFloorK a -> varInAst var a
  AstCastK t -> varInAst var t
  AstFromIntegralK t -> varInAst var t

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
  AstZipS v -> varInAst var v
  AstUnzipS v -> varInAst var v

  AstFromS _ v -> varInAst var v
  AstSFromR v -> varInAst var v
  AstSFromX v -> varInAst var v

  AstXNestR v -> varInAst var v
  AstXNestS v -> varInAst var v
  AstXNest v -> varInAst var v
  AstXUnNestR v -> varInAst var v
  AstXUnNestS v -> varInAst var v
  AstXUnNest v -> varInAst var v

  AstApply t ll -> varInAstHFun var t || varInAst var ll
  AstMapAccumRDer _k _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstMapAccumLDer _k _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es

  AstReplicate0NS _ _ v -> varInAst var v
  AstSum0S _ _ v -> varInAst var v
  AstDot0S _ u v -> varInAst var u || varInAst var v
  AstDot1InS _ _ u v -> varInAst var u || varInAst var v
  AstMatvecmulS _ _ u v -> varInAst var u || varInAst var v
  AstMatmul2S _ _ _ u v -> varInAst var u || varInAst var v

varInIndexS :: AstVarId -> AstIxS ms sh -> Bool
varInIndexS var = any (varInAst var)

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
  AstSFromK{} -> True
  AstPair t1 t2 -> astIsSmall relaxed t1 && astIsSmall relaxed t2
  AstProject1 t -> astIsSmall relaxed t
  AstProject2 t -> astIsSmall relaxed t
  AstVar{} -> True
  AstPrimalPart v -> astIsSmall relaxed v
  AstDualPart v -> astIsSmall relaxed v
  AstFromPrimal v -> astIsSmall relaxed v
  AstFromDual v -> astIsSmall relaxed v
  AstReplicate _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via tricks, so prob. safe
  AstConcrete FTKScalar _ -> True
  AstConcrete (FTKR sh FTKScalar) _ -> shrSize sh <= 1
  AstConcrete (FTKS sh FTKScalar) _ -> shsSize sh <= 1
  AstConcrete (FTKX sh FTKScalar) _ -> shxSize sh <= 1
  AstConcrete{} -> False
  AstFromVector snat v | sNatValue snat == 1 -> astIsSmall relaxed $ v V.! 0

  AstIotaS -> True
  AstSliceS v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTransposeS _perm v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstFromS _ v -> astIsSmall relaxed v
  AstSFromR v -> astIsSmall relaxed v
  AstSFromX v -> astIsSmall relaxed v

  _ -> False


-- * Odds and ends

liftRFromS1 :: forall n x ms s. TensorKind x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
-- The cheapest possible optimization to prevent trivial term buildup.
liftRFromS1 f (AstFromS stkz@(STKR snat@SNat x) u) = case ftkAst u of
  FTKS shu xu ->
    withKnownShS shu $
    case sameSTK x (ftkToStk xu) of
      Just Refl -> case f u of
        AstSFromR @sh a
          | Just Refl <- sameNat (SNat @(Rank sh)) snat -> a
        a -> AstFromS stkz a
      _ -> error $ "liftRFromS1: tensor kinds don't agree: "
                   ++ show x ++ " " ++ show xu
  _ -> error "liftRFromS1: unexpected tensor kind"
-- The pessimistic case, no optimization at all.
liftRFromS1 f a = case ftkAst a of
  ftk@(FTKR sh' _) | SNat <- shrRank sh' ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS @(TKS2 sh x) (ftkToStk ftk)
      $ f (AstSFromR @sh a)

-- We refrain from checking for AstFromPrimal (AstFromS), because that would
-- add three more cases for little gain (arithmetic expressions are unlikely
-- to have AstFromPrimal and especially a build-up of interspersed
-- conversions and AstFromPrimal).
liftRFromS2 :: forall n x ms s. TensorKind x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x) -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
liftRFromS2 f (AstFromS stkz@(STKR snat@SNat x) u) (AstFromS _ v) =
  case (ftkAst u, ftkAst v) of
    (ftku@(FTKS shu _), ftkv) ->
      withKnownShS shu $
      case ( sameSTK (ftkToStk ftku) (STKS shu x)
           , sameSTK (ftkToStk ftkv) (STKS shu x) ) of
      (Just Refl, Just Refl) -> case f u v of
        AstSFromR @sh a
          | Just Refl <- sameNat (SNat @(Rank sh)) snat -> a
        a -> AstFromS stkz a
      _ -> error $ "liftRFromS2: tensor kinds don't agree: "
                   ++ show ftku ++ " " ++ show ftkv ++ " "
                   ++ show (STKS shu x)
    _ -> error "liftRFromS2: unexpected tensor kinds"
liftRFromS2 f a b  = case ftkAst a of
  ftk@(FTKR sh' _) | SNat <- shrRank sh' ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS @(TKS2 sh x) (ftkToStk ftk)
      $ f (cAstSFromR @sh a) (cAstSFromR @sh b)
        -- both are not AstFromS, but one may be

liftXFromS1 :: forall sh' x ms s. TensorKind x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
liftXFromS1 f (AstFromS stkz@(STKX shx x) u) = case ftkAst u of
  FTKS shu xu ->
    withKnownShS shu $
    case sameSTK x (ftkToStk xu) of
      Just Refl -> case f u of
        AstSFromX @_ @shx2 a
          | Just Refl <- testEquality shx (knownShX @shx2) -> a
        a -> AstFromS stkz a
      _ -> error $ "liftXFromS1: tensor kinds don't agree: "
                   ++ show x ++ " " ++ show xu
  _ -> error "liftXFromS1: unexpected tensor kind"
liftXFromS1 f a = case ftkAst a of
  ftk@(FTKX sh' _) ->
    withKnownShX (ssxFromShape sh') $
    withCastXS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS @(TKS2 sh x) (ftkToStk ftk)
      $ f (AstSFromX @sh @sh' a)

liftXFromS2 :: forall sh' x ms s. TensorKind x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x) -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
liftXFromS2 f (AstFromS stkz@(STKX shx x) u) (AstFromS _ v) =
  case (ftkAst u, ftkAst v) of
    (ftku@(FTKS shu _), ftkv) ->
      withKnownShS shu $
      case ( sameSTK (ftkToStk ftku) (STKS shu x)
           , sameSTK (ftkToStk ftkv) (STKS shu x) ) of
        (Just Refl, Just Refl) -> case f u v of
          AstSFromX @_ @shx2 a
            | Just Refl <- testEquality shx (knownShX @shx2) -> a
          a -> AstFromS stkz a
        _ -> error $ "liftXFromS2: tensor kinds don't agree: "
                     ++ show ftku ++ " " ++ show ftkv ++ " "
                     ++ show (STKS shu x)
    _ -> error "liftXFromS2: unexpected tensor kinds"
liftXFromS2 f a b = case ftkAst a of
  ftk@(FTKX sh' _) ->
    withKnownShX (ssxFromShape sh') $
    withCastXS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS @(TKS2 sh x) (ftkToStk ftk)
      $ f (cAstSFromX @sh @sh' a) (cAstSFromX @sh @sh' b)

cAstSFromR :: forall sh ms s r.
              (KnownShS sh, KnownNat (Rank sh), TensorKind r)
           => AstTensor ms s (TKR2 (Rank sh) r) -> AstTensor ms s (TKS2 sh r)
cAstSFromR (AstFromS _ v)
           | Just Refl <- sameSTK (ftkToStk (ftkAst v))
                                  (stensorKind @(TKS2 sh r)) = v
cAstSFromR (AstFromPrimal (AstFromS _ v))
           | Just Refl <- sameSTK (ftkToStk (ftkAst v))
                                  (stensorKind @(TKS2 sh r)) = AstFromPrimal v
cAstSFromR v = AstSFromR v

cAstSFromX :: forall sh sh' ms s r.
              (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
           => AstTensor ms s (TKX2 sh' r) -> AstTensor ms s (TKS2 sh r)
cAstSFromX (AstFromS _ v)
           | Just Refl <- sameSTK (ftkToStk (ftkAst v))
                                  (stensorKind @(TKS2 sh r)) = v
cAstSFromX (AstFromPrimal (AstFromS _ v))
           | Just Refl <- sameSTK (ftkToStk (ftkAst v))
                                  (stensorKind @(TKS2 sh r)) = AstFromPrimal v
cAstSFromX v = AstSFromX v
