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
  , cAstSFromK, cAstSFromR, cAstSFromX
  ) where

import Prelude hiding (foldl')

import Control.Exception.Assert.Sugar
import Data.List.NonEmpty (NonEmpty (..))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, sameNat)
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape
  (KnownShX (..), shxSize, ssxFromShape, withKnownShX)
import Data.Array.Nested (KnownShS (..), Rank, ShS (..))
import Data.Array.Nested.Internal.Shape
  ( shrRank
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
  AstPair t1 t2 -> FTKProduct (ftkAst t1) (ftkAst t2)
  AstProject1 v -> case ftkAst v of
    FTKProduct ftk1 _ -> ftk1
  AstProject2 v -> case ftkAst v of
    FTKProduct _ ftk2 -> ftk2
  AstFromVector snat l -> case V.toList l of
    [] -> error "ftkAst: empty vector"
    v : _ -> buildFTK snat (ftkAst v)
  AstSum snat stk v -> razeFTK snat stk (ftkAst v)
  AstReplicate snat _ v -> buildFTK snat (ftkAst v)
  AstMapAccumRDer @accShs @bShs k bShs _eShs _f _df _rf acc0 _es
    | Dict <- lemKnownSTKOfBuild k (knownSTK @accShs)
    , Dict <- lemKnownSTKOfBuild k (knownSTK @bShs) ->
      FTKProduct (ftkAst acc0) (buildFTK k bShs)
  AstMapAccumLDer @accShs @bShs k bShs _eShs _f _df _rf acc0 _es
    | Dict <- lemKnownSTKOfBuild k (knownSTK @accShs)
    , Dict <- lemKnownSTKOfBuild k (knownSTK @bShs) ->
      FTKProduct (ftkAst acc0) (buildFTK k bShs)
  AstApply (AstLambda ~(_vvars, _, l)) _ll -> ftkAst l
  AstVar ftk _var -> ftk
  AstCond _b v _w -> ftkAst v
  AstBuild1 snat (_var, v) -> buildFTK snat (ftkAst v)
  AstConcrete ftk _ -> ftk

  AstLet _ _ v -> ftkAst v
  AstShare _ v -> ftkAst v
  AstToShare v -> ftkAst v

  AstPrimalPart a -> ftkAst a
  AstDualPart a -> ftkAst a
  AstFromPrimal a -> ftkAst a
  AstFromDual a -> ftkAst a

  AstSumOfList args -> case args of
    v :| _ -> ftkAst v

  AstN1K{} -> FTKScalar
  AstN2K{} -> FTKScalar
  AstR1K{} -> FTKScalar
  AstR2K{} -> FTKScalar
  AstI2K{} -> FTKScalar
  AstFloorK{} -> FTKScalar
  AstFromIntegralK{} -> FTKScalar
  AstCastK{} -> FTKScalar

  AstN1S{} -> FTKS knownShS FTKScalar
  AstN2S{} -> FTKS knownShS FTKScalar
  AstR1S{} -> FTKS knownShS FTKScalar
  AstR2S{} -> FTKS knownShS FTKScalar
  AstI2S{} -> FTKS knownShS FTKScalar
  AstFloorS{} -> FTKS knownShS FTKScalar
  AstFromIntegralS{} -> FTKS knownShS FTKScalar
  AstCastS{} -> FTKS knownShS FTKScalar

  AstIndexS v _ix -> case ftkAst v of
    FTKS _sh1sh2 x -> FTKS knownShS x
  AstScatterS @_ @shn @shp v _ -> case ftkAst v of
    FTKS _ x -> FTKS (knownShS @shp `shsAppend` knownShS @shn) x
  AstGatherS @shm @shn v _ -> case ftkAst v of
    FTKS _ x -> FTKS (knownShS @shm `shsAppend` knownShS @shn) x
  AstMinIndexS @sh @n _ -> FTKS (shsInit (knownShS @(n ': sh))) FTKScalar
  AstMaxIndexS @sh @n _ -> FTKS (shsInit (knownShS @(n ': sh))) FTKScalar
  AstIotaS{} -> FTKS knownShS FTKScalar
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
  AstZipS v -> case ftkAst v of
    FTKProduct (FTKS sh y) (FTKS _ z) -> FTKS sh (FTKProduct y z)
  AstUnzipS v -> case ftkAst v of
    FTKS sh (FTKProduct y z) -> FTKProduct (FTKS sh y) (FTKS sh z)
  AstNestS @sh1 @sh2 v -> case ftkAst v of
    FTKS _ x -> FTKS (knownShS @sh1) (FTKS (knownShS @sh2) x)
  AstUnNestS @sh1 @sh2 v -> case ftkAst v of
    FTKS _ (FTKS _ x) -> FTKS (knownShS @sh1 `shsAppend` knownShS @sh2) x

  AstFromS stkz v ->
    let fromS :: FullTensorKind y2 -> STensorKind z2 -> FullTensorKind z2
        fromS ftk stk = case (ftk, stk) of
          _ | Just Refl <- sameSTK (ftkToSTK ftk) stk -> ftk
          (FTKS ZSS (FTKScalar @r), STKScalar tr) ->
            case testEquality (typeRep @r) tr of
              Just Refl -> FTKScalar
              Nothing -> error "ftkAst: wrong tensor kinds for AstFromS"
          (FTKS sh x, STKR nx zx) ->
            case ( sameSTK (ftkToSTK x) zx
                 , testEquality (shsRank sh) nx ) of
              (Just Refl, Just Refl) -> FTKR (shCastSR sh) x
              _ -> error $ "ftkAst: wrong tensor kinds for AstFromS: "
                           ++ show (ftkToSTK x) ++ " vs " ++ show zx ++ " and "
                           ++ show sh ++ " vs " ++ show nx
          (FTKS sh x, STKX shx zx) ->
            case ( sameSTK (ftkToSTK x) zx
                 , testEquality (shsRank sh) (ssxRank shx) ) of
              (Just Refl, Just Refl) -> FTKX (shCastSX shx sh) x
              _ -> error "ftkAst: wrong tensor kinds for AstFromS"
          (FTKProduct ftk1 ftk2, STKProduct stk1 stk2) ->
            FTKProduct (fromS ftk1 stk1) (fromS ftk2 stk2)
          _ -> error $ "ftkAst: wrong tensor kinds for AstFromS: "
                       ++ show (ftk, stk)
    in fromS (ftkAst v) stkz
  AstSFromK{} -> FTKS ZSS FTKScalar
  AstSFromR v -> case ftkAst v of
    FTKR _ x -> FTKS knownShS x
  AstSFromX v -> case ftkAst v of
    FTKX _ x -> FTKS knownShS x

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
  AstPair t1 t2 -> varInAst var t1 || varInAst var t2
  AstProject1 t -> varInAst var t
  AstProject2 t -> varInAst var t
  AstFromVector _ vl -> any (varInAst var) $ V.toList vl
  AstSum _ _ v -> varInAst var v
  AstReplicate _ _ v -> varInAst var v
  AstMapAccumRDer _k _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstMapAccumLDer _k _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstApply t ll -> varInAstHFun var t || varInAst var ll
  AstVar _ var2 -> var == varNameToAstVarId var2
  AstCond b v w -> varInAstBool var b || varInAst var v || varInAst var w
  AstBuild1 _ (var2, v) ->
    assert (varNameToAstVarId var2 /= var) $
    varInAst var v
  AstConcrete{} -> False

  AstLet _var2 u v -> varInAst var u || varInAst var v
  AstShare _ v -> varInAst var v
  AstToShare v -> varInAst var v

  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstFromPrimal v -> varInAst var v
  AstFromDual v -> varInAst var v

  AstSumOfList l -> any (varInAst var) l

  AstN1K _ t -> varInAst var t
  AstN2K _ t u -> varInAst var t || varInAst var u
  AstR1K _ t -> varInAst var t
  AstR2K _ t u -> varInAst var t || varInAst var u
  AstI2K _ t u -> varInAst var t || varInAst var u
  AstFloorK a -> varInAst var a
  AstFromIntegralK t -> varInAst var t
  AstCastK t -> varInAst var t

  AstN1S _ t -> varInAst var t
  AstN2S _ t u -> varInAst var t || varInAst var u
  AstR1S _ t -> varInAst var t
  AstR2S _ t u -> varInAst var t || varInAst var u
  AstI2S _ t u -> varInAst var t || varInAst var u
  AstFloorS a -> varInAst var a
  AstFromIntegralS a -> varInAst var a
  AstCastS t -> varInAst var t

  AstIndexS v ix -> varInAst var v || varInIndexS var ix
  AstScatterS v (_vars, ix) -> varInIndexS var ix || varInAst var v
  AstGatherS v (_vars, ix) -> varInIndexS var ix || varInAst var v
  AstMinIndexS a -> varInAst var a
  AstMaxIndexS a -> varInAst var a
  AstIotaS -> False
  AstAppendS v u -> varInAst var v || varInAst var u
  AstSliceS v -> varInAst var v
  AstReverseS v -> varInAst var v
  AstTransposeS _perm v -> varInAst var v
  AstReshapeS v -> varInAst var v
  AstZipS v -> varInAst var v
  AstUnzipS v -> varInAst var v
  AstNestS v -> varInAst var v
  AstUnNestS v -> varInAst var v

  AstFromS _ v -> varInAst var v
  AstSFromK t -> varInAst var t
  AstSFromR v -> varInAst var v
  AstSFromX v -> varInAst var v

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
  AstPair t1 t2 -> astIsSmall relaxed t1 && astIsSmall relaxed t2
  AstProject1 t -> astIsSmall relaxed t
  AstProject2 t -> astIsSmall relaxed t
  AstFromVector snat v | sNatValue snat == 1 -> astIsSmall relaxed $ v V.! 0
  AstReplicate _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via tricks, so prob. safe
  AstVar{} -> True
  AstConcrete FTKScalar _ -> True
  AstConcrete (FTKR sh FTKScalar) _ -> shrSize sh <= 1
  AstConcrete (FTKS sh FTKScalar) _ -> shsSize sh <= 1
  AstConcrete (FTKX sh FTKScalar) _ -> shxSize sh <= 1
  AstConcrete{} -> False

  AstPrimalPart v -> astIsSmall relaxed v
  AstDualPart v -> astIsSmall relaxed v
  AstFromPrimal v -> astIsSmall relaxed v
  AstFromDual v -> astIsSmall relaxed v

  AstIotaS -> True
  AstSliceS v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTransposeS _perm v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses

  AstFromS _ v -> astIsSmall relaxed v
  AstSFromK{} -> True
  AstSFromR v -> astIsSmall relaxed v
  AstSFromX v -> astIsSmall relaxed v

  _ -> False


-- * Odds and ends

liftRFromS1 :: forall n x ms s. KnownSTK x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
-- The cheapest possible optimization to prevent trivial term buildup.
liftRFromS1 f (AstFromS stkz@(STKR snat@SNat x) u) = case ftkAst u of
  FTKS shu xu ->
    withKnownShS shu $
    case sameSTK x (ftkToSTK xu) of
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
      AstFromS @(TKS2 sh x) (ftkToSTK ftk)
      $ f (AstSFromR @sh a)

-- We refrain from checking for AstFromPrimal (AstFromS), because that would
-- add three more cases for little gain (arithmetic expressions are unlikely
-- to have AstFromPrimal and especially a build-up of interspersed
-- conversions and AstFromPrimal).
liftRFromS2 :: forall n x ms s. KnownSTK x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x) -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
liftRFromS2 f (AstFromS stkz@(STKR snat@SNat x) u) (AstFromS _ v) =
  case (ftkAst u, ftkAst v) of
    (ftku@(FTKS shu _), ftkv) ->
      withKnownShS shu $
      case ( sameSTK (ftkToSTK ftku) (STKS shu x)
           , sameSTK (ftkToSTK ftkv) (STKS shu x) ) of
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
      AstFromS @(TKS2 sh x) (ftkToSTK ftk)
      $ f (cAstSFromR @sh a) (cAstSFromR @sh b)
        -- both are not AstFromS, but one may be

liftXFromS1 :: forall sh' x ms s. KnownSTK x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
liftXFromS1 f (AstFromS stkz@(STKX shx x) u) = case ftkAst u of
  FTKS shu xu ->
    withKnownShS shu $
    case sameSTK x (ftkToSTK xu) of
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
      AstFromS @(TKS2 sh x) (ftkToSTK ftk)
      $ f (AstSFromX @sh @sh' a)

liftXFromS2 :: forall sh' x ms s. KnownSTK x
            => (forall sh. KnownShS sh
                => AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x) -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
liftXFromS2 f (AstFromS stkz@(STKX shx x) u) (AstFromS _ v) =
  case (ftkAst u, ftkAst v) of
    (ftku@(FTKS shu _), ftkv) ->
      withKnownShS shu $
      case ( sameSTK (ftkToSTK ftku) (STKS shu x)
           , sameSTK (ftkToSTK ftkv) (STKS shu x) ) of
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
      AstFromS @(TKS2 sh x) (ftkToSTK ftk)
      $ f (cAstSFromX @sh @sh' a) (cAstSFromX @sh @sh' b)

cAstSFromK :: forall r ms s. GoodScalar r
           => AstTensor ms s (TKScalar r) -> AstTensor ms s (TKS '[] r)
cAstSFromK (AstFromS _ v)
           | Just Refl <- sameSTK (ftkToSTK (ftkAst v))
                                  (knownSTK @(TKS '[] r)) = v
cAstSFromK (AstFromPrimal (AstFromS _ v))
           | Just Refl <- sameSTK (ftkToSTK (ftkAst v))
                                  (knownSTK @(TKS '[] r)) = AstFromPrimal v
cAstSFromK v = AstSFromK v

cAstSFromR :: forall sh r ms s.
              (KnownShS sh, KnownNat (Rank sh), KnownSTK r)
           => AstTensor ms s (TKR2 (Rank sh) r) -> AstTensor ms s (TKS2 sh r)
cAstSFromR (AstFromS _ v)
           | Just Refl <- sameSTK (ftkToSTK (ftkAst v))
                                  (knownSTK @(TKS2 sh r)) = v
cAstSFromR (AstFromPrimal (AstFromS _ v))
           | Just Refl <- sameSTK (ftkToSTK (ftkAst v))
                                  (knownSTK @(TKS2 sh r)) = AstFromPrimal v
cAstSFromR v = AstSFromR v

cAstSFromX :: forall sh sh' r ms s.
              (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', KnownSTK r)
           => AstTensor ms s (TKX2 sh' r) -> AstTensor ms s (TKS2 sh r)
cAstSFromX (AstFromS _ v)
           | Just Refl <- sameSTK (ftkToSTK (ftkAst v))
                                  (knownSTK @(TKS2 sh r)) = v
cAstSFromX (AstFromPrimal (AstFromS _ v))
           | Just Refl <- sameSTK (ftkToSTK (ftkAst v))
                                  (knownSTK @(TKS2 sh r)) = AstFromPrimal v
cAstSFromX v = AstSFromX v
