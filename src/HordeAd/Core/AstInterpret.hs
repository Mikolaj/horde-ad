{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
-- | Interpretation of AST terms in an aribtrary @RankedTensor@ & Co instance.
-- With the exception of the the interpretation of the sharing mechanisms,
-- the interpretation is the unique homorphism determined by the instance.
-- The sharing mechanisms are translated so as to preserve sharing in case
-- the instance is a term algebra as well.
module HordeAd.Core.AstInterpret
  ( interpretAstPrimal, interpretAst
  -- * Exported only to specialize elsewhere (because transitive specialization may not work, possibly)
  , interpretAstPrimalRuntimeSpecialized, interpretAstPrimalSRuntimeSpecialized
  , interpretAstDual
  , interpretAstRuntimeSpecialized, interpretAstSRuntimeSpecialized
  , interpretAstBool
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Int (Int64)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Foreign.C (CInt)
import GHC.TypeLits (KnownNat, sameNat)
import Type.Reflection (Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Shape (pattern (:.%), pattern ZIX)
import Data.Array.Nested
  ( IxR (..)
  , IxS (..)
  , KnownShS (..)
  , KnownShX (..)
  , ListR (..)
  , ListS (..)
  , Rank
  , ShR (..)
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shrRank)

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Util.SizedList

interpretAstPrimalRuntimeSpecialized
  :: forall target n r.
     (KnownNat n, ADReady target, Typeable r)
  => AstEnv target
  -> AstTensor AstMethodLet PrimalSpan (TKR n r) -> PrimalOf target (TKR n r)
interpretAstPrimalRuntimeSpecialized !env t =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable and RowSum instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
  -- TODO: revisit using TypeRepOf to pattern match
  -- instead of nesting conditionals
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAstPrimal @target @(TKR n Double) env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAstPrimal @target @(TKR n Float) env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAstPrimal @target @(TKR n Int64) env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAstPrimal @target @(TKR n CInt) env t
          _ -> error "an unexpected underlying scalar type"  -- catch absurd

interpretAstPrimalSRuntimeSpecialized
  :: forall target sh r.
     (KnownShS sh, ADReady target, Typeable r)
  => AstEnv target
  -> AstTensor AstMethodLet PrimalSpan (TKS sh r) -> PrimalOf target (TKS sh r)
interpretAstPrimalSRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAstPrimal @target @(TKS sh Double) env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAstPrimal @target @(TKS sh Float) env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAstPrimal @target @(TKS sh Int64) env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAstPrimal @target @(TKS sh CInt) env t
          _ -> error "an unexpected underlying scalar type"  -- catch absurd

-- Strict environment and strict ADVal and Delta make this is hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall target y. (ADReady target, TensorKind y)
  => AstEnv target
  -> AstTensor AstMethodLet PrimalSpan y
  -> PrimalOf target y
interpretAstPrimal !env v1 = case v1 of
  AstPrimalPart (AstD u _) -> interpretAstPrimal env u
  AstPrimalPart (AstFromPrimal u) -> interpretAstPrimal env u
  AstCond @y2 b a1 a2 ->
    -- This avoids multiple ifF expansions in ADVal.
    let c = interpretAstBool env b
    in tcond (stensorKind @y2) c
             (interpretAstPrimal env a1) (interpretAstPrimal env a2)
  _ ->
    tprimalPart (stensorKind @y) (interpretAst env v1)

interpretAstDual
  :: forall target y. (ADReady target, TensorKind y)
  => AstEnv target
  -> AstTensor AstMethodLet DualSpan y -> DualOf target y
interpretAstDual !env v1 = case v1 of
  AstDualPart (AstD _ u') -> interpretAstDual env u'
  _ ->
    tdualPart (stensorKind @y) (interpretAst env v1)

interpretAstRuntimeSpecialized
  :: forall target n s r.
     (ADReady target, Typeable r, AstSpan s)
  => AstEnv target
  -> AstTensor AstMethodLet s (TKR n r) -> target (TKR n r)
interpretAstRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAst @target @s @(TKR n Double) env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAst @target @s @(TKR n Float) env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAst @target @s @(TKR n Int64) env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAst @target @s @(TKR n CInt) env t
          _ -> case testEquality (typeRep @r) (typeRep @Z0) of
            Just Refl -> interpretAst @target @s @(TKR n Z0) env t
            _ -> error "an unexpected underlying scalar type"

interpretAstSRuntimeSpecialized
  :: forall target sh s r.
     (ADReady target, Typeable r, AstSpan s)
  => AstEnv target
  -> AstTensor AstMethodLet s (TKS sh r) -> target (TKS sh r)
interpretAstSRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAst @target @s @(TKS sh Double) env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAst @target @s @(TKS sh Float) env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAst @target @s @(TKS sh Int64) env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAst @target @s @(TKS sh CInt) env t
          _ -> case testEquality (typeRep @r) (typeRep @Z0) of
            Just Refl -> interpretAst @target @s @(TKS sh Z0) env t
            _ -> error "an unexpected underlying scalar type"

interpretAst
  :: forall target s y. (ADReady target, AstSpan s)
  => AstEnv target
  -> AstTensor AstMethodLet s y -> target y
interpretAst !env = \case
  AstFromScalar t -> sfromScalar $ interpretAst env t
  AstToScalar t -> stoScalar $ interpretAst env t
  AstPair t1 t2 -> tpair (interpretAst env t1) (interpretAst env t2)
  AstProject1 t -> tproject1 (interpretAst env t)
  AstProject2 t -> tproject2 (interpretAst env t)
  AstVar @y2 _sh var ->
   let var2 = mkAstVarName @FullSpan @y2 (varNameToAstVarId var)  -- TODO
   in case DMap.lookup var2 env of
    Just (AstEnvElemRep t) ->
      -- TODO: assert (rshape t == sh
      --         `blame` (sh, rshape t, var, t, env)) t
      t
    _ -> error $ "interpretAst: unknown AstVar " ++ show var
-- TODO:                 ++ " in environment " ++ showsPrecAstEnv 0 env ""
  AstPrimalPart a -> interpretAst env a
    -- This is correct, because @s@ must be @PrimalSpan@ and so @target@ must
    -- be morally the primal part of a dual numbers type that is the codomain
    -- of the interpretation of the same AST but marked with @FullSpan@.
    -- Consequently, the result is a primal part, despite the appearances.
    -- This whole notation abuse is for user comfort (less @PrimalOf@
    -- in the tensor classes) and to avoid repeating the @interpretAst@ code
    -- in @interpretAstPrimal@. TODO: make this sane.
    --
    -- For example, if I'm interpreting @AstRanked PrimalSpan@ in
    -- @AstRanked FullSpan@ (basically doing the forward pass
    -- via interpretation), then @target@ is a primal part
    -- of @ADVal (AstRanked FullSpan)@, even though @ADVal@ never appears
    -- and @a@ could even be returned as is (but @AstPrimalPart@ never occurs
    -- in terms created by AD, I think, so no point optimizing). What happens
    -- is that the term gets flattened and the @FullSpan@ terms inside
    -- @AstPrimalPart@ get merged with those created from @PrimalSpan@ terms
    -- via interpretation. Which is as good as any semantics of forward
    -- pass of a function that has dual numbers somewhere inside it.
    -- An alternative semantics would remove the dual parts and use
    -- the primal parts to reconstruct the dual in the simple way.
    -- Probably doesn't matter, because none of this can be created by AD.
    -- If we had an @AstRanked@ variant without the dual number constructors,
    -- instead of the spans, the mixup would vanish.
  AstDualPart a -> interpretAst env a
    -- This is correct, because @s@ must be @DualSpan@ and so @target@ must
    -- be morally the dual part of a dual numbers type that is the codomain
    -- of the interpretation of the same AST but marked with @FullSpan@.
    -- Consequently, the result is a dual part, despite the appearances.
  AstFromPrimal @y2 a -> tfromPrimal (stensorKind @y2) (interpretAstPrimal env a)
  AstD @y2 u u' ->
   tD (stensorKind @y2) (interpretAstPrimal env u) (interpretAstDual env u')
  AstCond @y2 b a1 a2 ->
    -- This avoids multiple ifF expansions in ADVal.
    let c = interpretAstBool env b
    in tcond (stensorKind @y2) c (interpretAst env a1) (interpretAst env a2)
  AstReplicate @y2 snat v ->
    treplicate snat (stensorKind @y2) (interpretAst env v)
  -- These are only needed for tests that don't vectorize Ast.
  AstBuild1 @y2
            snat (var, AstSum (AstN2R TimesOp t (AstIndex
                                                u (AstIntVar var2 :.: ZIR))))
    | Just Refl <- case stensorKind @y2 of
        STKR @n _ _ -> sameNat (Proxy @n) (Proxy @0)
    , var == var2, sNatValue snat == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 @y2
            snat (var, AstSum
                         (AstReshape @p
                            _sh (AstN2R TimesOp
                                         t
                                         (AstIndex
                                            u (AstIntVar var2 :.: ZIR)))))
    | Just Refl <- case stensorKind @y2 of
        STKR @n _ _ -> sameNat (Proxy @n) (Proxy @0)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, sNatValue snat == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 snat@(SNat @n) (_, v)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
      let emptyFromStk :: FullTensorKind z
                       -> target (BuildTensorKind n z)
          emptyFromStk ftk = case ftk of
            FTKR sh FTKScalar | SNat <- shrRank sh -> rfromList0N (0 :$: sh) []
            FTKS sh FTKScalar -> withKnownShS sh $ sfromList0N []
            FTKX{} -> error "TODO"
            FTKProduct @z1 @z2 ftk1 ftk2
              | Dict <- lemTensorKindOfFTK ftk1
              , Dict <- lemTensorKindOfFTK ftk2
              , (Dict, Dict) <- lemTensorKind1OfBuild snat (stensorKind @z1)
              , (Dict, Dict) <- lemTensorKind1OfBuild snat (stensorKind @z2) ->
                tpair (emptyFromStk ftk1) (emptyFromStk ftk2)
            FTKUntyped ssh -> dmkHVector $ replicate1HVector @target (SNat @0)
                              $ V.map dynamicFromVoid ssh
            _ -> error "TODO"
      in emptyFromStk (ftkAst v)
  -- The following can't be, in general, so partially evaluated, because v
  -- may contain variables that the evironment sends to terms,
  -- not to concrete numbers (and so Primal a is not equal to a).
  -- However, this matters only for POPL AD, not JAX AD and also it matters
  -- only with no vectorization of, at least, constant (primal-only) terms.
  -- AstBuild1 k (var, AstFromPrimal v) ->
  --   tconcrete
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env (var, v)
  AstBuild1 @y2 snat (var, v) ->
    let f i = interpretAst (extendEnvI var i env) v
    in tbuild1 snat f
  AstLet @y2 var u v -> case stensorKind @y2 of
    STKScalar{} ->
      -- We assume there are no nested lets with the same variable.
      let t = interpretAst env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)
    STKR _ STKScalar{} ->
      let t = interpretAstRuntimeSpecialized env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)
    STKS _ STKScalar{} ->
      let t = interpretAstSRuntimeSpecialized env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)
    STKX _ STKScalar{} ->
      let t = interpretAst env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)
    STKProduct{} ->
      let t = interpretAst env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)
    STKUntyped{} ->
      let t = interpretAst env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)
    _ -> error "TODO"

  AstMinIndexR v ->
    rminIndex $ rfromPrimal $ interpretAstPrimalRuntimeSpecialized env v
  AstMaxIndexR v ->
    rmaxIndex $ rfromPrimal $ interpretAstPrimalRuntimeSpecialized env v
  AstFloorR v ->
    rfloor $ rfromPrimal $ interpretAstPrimalRuntimeSpecialized env v
  AstIotaR -> error "interpretAst: bare AstIota, most likely a bug"
  AstN1 opCode u ->
    let u2 = interpretAst env u
    in interpretAstN1 opCode u2
  AstN2 opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstN2 opCode u2 v2
  AstR1 opCode u ->
    let u2 = interpretAst env u
    in interpretAstR1 opCode u2
  AstR2 opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstR2 opCode u2 v2
  AstI2 opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstI2F opCode u2 v2
  AstSumOfList args ->
    let args2 = interpretAst env <$> args
    in foldr1 (+) args2  -- avoid @fromInteger 0@ in @sum@
  AstFloor v ->
    kfloor $ tfromPrimal (STKScalar typeRep) $ interpretAstPrimal env v
  AstCast v -> kcast $ interpretAst env v
  AstFromIntegral v ->
    kfromIntegral $ tfromPrimal (STKScalar typeRep) $ interpretAstPrimal env v
  {- TODO: revise when we handle GPUs. For now, this is done in TensorOps
     instead and that's fine, because for one-element carriers,
     reshape and replicate are very cheap. OTOH, this was introducing
     ScalarR(UnScalar0 ...) into delta expressions by firing
     in an early phase.
  AstN2R TimesOp [v, AstReshape _ (AstReplicate @m _ s)]
   -- TODO: also handle nested AstReplicate to prevent executing them
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env v
            t2 = interpretAst env s
        in tscaleByScalar0 t2 t1
  AstN2R TimesOp [v, AstReplicate @m _ s]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env v
            t2 = interpretAst env s
        in tscaleByScalar0 t2 t1
  -}
  AstN2R TimesOp v (AstLet var u (AstReshape sh (AstReplicate (SNat @m) s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
        -- The varNameInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env
          (AstLet var u (AstN2R TimesOp v (AstReshape sh
                                            (AstReplicate (SNat @m) s))))
  AstN2R TimesOp v (AstReshape sh (AstLet var u (AstReplicate (SNat @m) s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
        interpretAst env
          (AstLet var u (AstN2R TimesOp v (AstReshape sh
                                            (AstReplicate (SNat @m) s))))
  AstN2R TimesOp v (AstLet var u (AstReplicate (SNat @m) s))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
        interpretAst env
          (AstLet var u (AstN2R TimesOp v (AstReplicate (SNat @m) s)))
  AstN1R opCode u ->
    let u2 = interpretAst env u
    in interpretAstN1 opCode u2
  AstN2R opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstN2 opCode u2 v2
  AstR1R opCode u ->
    let u2 = interpretAst env u
    in interpretAstR1 opCode u2
  AstR2R opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstR2 opCode u2 v2
  AstI2R opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstI2F opCode u2 v2
  AstSumOfListR args ->
    let args2 = interpretAst env <$> args
    in foldr1 (+) args2  -- avoid @fromInteger 0@ in @sum@
  AstIndex AstIotaR (i :.: ZIR) ->
    rfromIntegral . rfromPrimal . rfromScalar $ interpretAstPrimal env i
  AstIndex v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAstPrimal env <$> ix
    in rindex v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstSum (AstN2R TimesOp (AstLet vart vt (AstTranspose tperm t))
                        (AstTranspose uperm u)) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstN2R TimesOp (AstTranspose tperm t)
                                (AstTranspose uperm u))))
  AstSum (AstN2R TimesOp (AstTranspose tperm t)
                         (AstLet varu vu (AstTranspose uperm u))) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstN2R TimesOp (AstTranspose tperm t)
                                (AstTranspose uperm u))))
  AstSum (AstN2R TimesOp (AstLet vart vt (AstTranspose tperm t))
                         (AstLet varu vu (AstTranspose uperm u))) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstN2R TimesOp (AstTranspose tperm t)
                                 (AstTranspose uperm u)))))
  AstSum @n @r
         v@(AstN2R TimesOp (AstTranspose tperm (AstReplicate @yt _tk t))
                           (AstTranspose uperm (AstReplicate @yu _uk u)))
    | Just Refl <- sameNat (Proxy @n) (Proxy @2) ->
      case (stensorKind @yt, stensorKind @yu) of
       (STKR{}, STKR{}) ->
        let interpretMatmul2 t1 u1 =
              let t2 = interpretAst env t1
                  u2 = interpretAst env u1
              in case testEquality (typeRep @r) (typeRep @Double) of
                Just Refl -> rmatmul2 t2 u2
                _ -> case testEquality (typeRep @r) (typeRep @Float) of
                  Just Refl -> rmatmul2 t2 u2
                  _ -> case testEquality (typeRep @r) (typeRep @Int64) of
                    Just Refl -> rmatmul2 t2 u2
                    _ -> case testEquality (typeRep @r) (typeRep @CInt) of
                      Just Refl -> rmatmul2 t2 u2
                      _ -> case rshape u2 of
                        _ :$: width2 :$: ZSR -> rsum (rtranspose [2,1,0] (rreplicate width2 t2)
                                                    * rtranspose [1,0] (rreplicate (rlength t2) u2))
                        _ -> error "impossible pattern needlessly required"
        in case (tperm, uperm) of
          ([2, 1, 0], [1, 0]) ->  -- tk and uk are fine due to perms matching
            interpretMatmul2 t u
          ([1, 0], [2, 1, 0]) ->
            interpretMatmul2 u t
          ([2, 1, 0], [2, 0, 1]) ->
            interpretMatmul2 t (astTranspose [1, 0] u)
          ([2, 0, 1], [2, 1, 0]) ->
            interpretMatmul2 u (astTranspose [1, 0] t)
          ([1, 2, 0], [1, 0]) ->
            interpretMatmul2 (astTranspose [1, 0] t) u
          ([1, 0], [1, 2, 0]) ->
            interpretMatmul2 (astTranspose [1, 0] u) t
--          ([1, 2, 0], [2, 0, 1]) ->
--            interpretMatmul2 (AstTranspose [1, 0] t) (AstTranspose [1, 0] u)
--          ([2, 0, 1], [1, 2, 0]) ->
--            interpretMatmul2 (AstTranspose [1, 0] u) (AstTranspose [1, 0] t)
          -- The variants below emerge when the whole term is transposed.
          -- All overlap with variants above and the cheaper one is selected.
          ([2, 0, 1], [1, 2, 0]) ->
            rtr $ interpretMatmul2 t u
          ([1, 2, 0], [2, 0, 1]) ->
            rtr $ interpretMatmul2 u t
--          ([2, 0, 1], [2, 1, 0]) ->
--            rtr $ interpretMatmul2 t (AstTranspose [1, 0] u)
--          ([2, 1, 0], [2, 0, 1]) ->
--            rtr $ interpretMatmul2 u (AstTranspose [1, 0] t)
--          ([1, 2, 0], [1, 0]) ->
--            rtr $ interpretMatmul2 (AstTranspose [1, 0] u) t
--          ([1, 0], [2, 1, 0]) ->
--            ttr
--            $ interpretMatmul2 (AstTranspose [1, 0] t) (AstTranspose [1, 0] u)
--          ([2, 1, 0], [1, 0]) ->
--            ttr
--            $ interpretMatmul2 (AstTranspose [1, 0] u) (AstTranspose [1, 0] t)
          _ -> rsum $ interpretAst env v
  AstSum @n (AstN2R TimesOp t u)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum @n (AstReshape _sh (AstN2R TimesOp t u))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
  AstSum @n (AstTranspose [1, 0] (AstN2R TimesOp t u))  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot1In t1 t2
  AstSum @n (AstReshape sh (AstTranspose _ t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env (AstSum (AstReshape sh t))
  AstSum @n (AstReshape sh (AstReverse t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env (AstSum (AstReshape sh t))
  AstSum @n (AstReshape _sh (AstSum t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        rsum0 $ interpretAst env t
  AstSum @n (AstSum t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        rsum0 $ interpretAst env t
          -- more cases are needed so perhaps we need AstSum0
  AstSum (AstLet var v t) -> interpretAst env (AstLet var v (AstSum t))
  AstSum (AstReshape sh (AstLet var v t)) ->
    interpretAst env (AstLet var v (AstSum (AstReshape sh t)))
  AstSum @n (AstReshape _sh t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        rsum0 $ interpretAst env t
  AstSum v -> rsum $ interpretAst env v
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstScatter sh v (ZR, ix) ->
    roneHot (takeShape sh) (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstScatter sh v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndex interpretAstPrimal env (vars, ix)
    in rscatter sh t1 f2
  AstFromVector l ->
    let l2 = V.map (interpretAst env) l
    in rfromVector l2
  AstAppend x y ->
    let t1 = interpretAst env x
        t2 = interpretAst env y
    in rappend t1 t2
  AstSlice i n AstIotaR ->
    let u = Nested.rfromListPrimLinear (n :$: ZSR) $ map fromIntegral [i .. i + n - 1]
    in interpretAst env
       $ AstConcrete (FTKR (Nested.rshape u) FTKScalar) $ RepN u
  AstSlice i n v -> rslice i n (interpretAst env v)
  AstReverse v -> rreverse (interpretAst env v)
  AstTranspose perm v -> rtranspose perm $ interpretAst env v
  AstReshape sh v@(AstReplicate @y2 _ s) -> case stensorKind @y2 of
    STKR @m _ STKScalar{} | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
      let t1 = interpretAst env s
      in rreplicate0N sh t1
    _ -> rreshape sh (interpretAst env v)
  AstReshape sh (AstLet var v (AstReplicate k t)) ->
    interpretAst env (AstLet var v (AstReshape sh (AstReplicate k t)))
  AstReshape sh v -> rreshape sh (interpretAst env v)
  AstGather _ v (ZR, ix) ->
    rindex (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstGather sh AstIotaR (vars, i :.: ZIR) ->
    rbuild sh (interpretLambdaIndex interpretAst env
                                    (vars, fromPrimal @s $ AstFromIntegralR $ AstRFromS $ AstFromScalar i))
  AstGather sh v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndex interpretAstPrimal env (vars, ix)
    in rgather sh t1 f2
    -- the operation accepts out of bounds indexes,
    -- for the same reason ordinary indexing does, see above
    -- TODO: currently we store the function on tape, because it doesn't
    -- cause recomputation of the gradient per-cell, unlike storing the build
    -- function on tape; for GPUs and libraries that don't understand Haskell
    -- closures, we can check if the expressions involve tensor operations
    -- too hard for GPUs and, if not, we can store the AST expression
    -- on tape and translate it to whatever backend sooner or later;
    -- and if yes, fall back to POPL pre-computation that, unfortunately,
    -- leads to a tensor of deltas
  AstCastR v -> rcast $ interpretAstRuntimeSpecialized env v
  AstFromIntegralR v ->
    rfromIntegral $ rfromPrimal $ interpretAstPrimalRuntimeSpecialized env v
  AstConcrete ftk a -> tconcrete ftk a
  AstProjectR l p ->
    let lt = interpretAst env l
    in tlet @_ @TKUntyped lt
         (\lw -> rfromD $ dunHVector lw V.! p)
           -- This is awkward, but we don't need rproject nor sproject.
           -- Most likely, the term gets simplified before interpretation anyway.
  AstLetHVectorIn @_ @_ @z2 vars l v -> case stensorKind @z2 of
    STKScalar _ ->
      let lt = interpretAst env l
          env2 lw = assert (voidHVectorMatches (voidFromVars vars) lw
                            `blame` ( shapeVoidHVector (voidFromVars vars)
                                    , V.toList $ V.map shapeDynamic lw
                                    , ftkAst l
                                    , shapeVoidHVector (dshape @target lt) )) $
                   extendEnvHVector vars lw env
      in rtoScalar
         $ tlet @_ @TKUntyped lt
             (\lw -> rfromScalar $ interpretAst (env2 (dunHVector lw)) v)
    STKR SNat STKScalar{} ->
      let lt = interpretAst env l
          env2 lw = assert (voidHVectorMatches (voidFromVars vars) lw
                            `blame` ( shapeVoidHVector (voidFromVars vars)
                                    , V.toList $ V.map shapeDynamic lw
                                    , ftkAst l
                                    , shapeVoidHVector (dshape @target lt) )) $
                   extendEnvHVector vars lw env
      in tlet @_ @TKUntyped lt
           (\lw -> interpretAst (env2 (dunHVector lw)) v)
    STKS sh STKScalar{} -> withKnownShS sh $
      let lt = interpretAst env l
          env2 lw = assert (voidHVectorMatches (voidFromVars vars) lw
                            `blame` ( shapeVoidHVector (voidFromVars vars)
                                    , V.toList $ V.map shapeDynamic lw
                                    , ftkAst l
                                    , shapeVoidHVector (dshape @target lt) )) $
                    extendEnvHVector vars lw env
      in tlet @_ @TKUntyped lt
           (\lw -> interpretAst (env2 (dunHVector lw)) v)
    STKX sh STKScalar{} -> withKnownShX sh $ error "TODO"
    STKProduct{} -> error "TODO"
    STKUntyped ->
      let lt = interpretAst env l
          env2 lw = assert (voidHVectorMatches (voidFromVars vars) lw
                            `blame` ( shapeVoidHVector (voidFromVars vars)
                                    , V.toList $ V.map shapeDynamic lw
                                    , ftkAst l
                                    , shapeVoidHVector (dshape @target lt) )) $
                    extendEnvHVector vars lw env
      in tlet @_ @TKUntyped lt
           (\lw -> interpretAst (env2 (dunHVector lw)) v)
    _ -> error "TODO"

  AstMinIndexS v ->
    sminIndex $ sfromPrimal $ interpretAstPrimalSRuntimeSpecialized env v
  AstMaxIndexS v ->
    smaxIndex $ sfromPrimal $ interpretAstPrimalSRuntimeSpecialized env v
  AstFloorS v ->
    sfloor $ sfromPrimal $ interpretAstPrimalSRuntimeSpecialized env v
  AstIotaS -> siota
{- TODO:
  AstN2R TimesOp [v, AstLet var u (AstReshape sh (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varInAst var v) ->
        -- The varInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env
          (AstLet var u (AstN2R TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstN2R TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varInAst var v) ->
        interpretAst env
          (AstLet var u (AstN2R TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstN2R TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varInAst var v) ->
        interpretAst env
          (AstLet var u (AstN2R TimesOp [v, AstReplicate @m k s]))
-}
  AstN1S opCode u ->
    let u2 = interpretAst env u
    in interpretAstN1 opCode u2
  AstN2S opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstN2 opCode u2 v2
  AstR1S opCode u ->
    let u2 = interpretAst env u
    in interpretAstR1 opCode u2
  AstR2S opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstR2F opCode u2 v2
  AstI2S opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstI2F opCode u2 v2
  AstSumOfListS args ->
    let args2 = interpretAst env <$> args
    in foldl1 (+) (srepl 0 : args2)  -- backward compat vs @sum@
-- TODO: in foldr1 (+) args2  -- avoid @fromInteger 0@ in @sum@
  AstIndexS AstIotaS (i :.$ ZIS) ->
    sfromIntegral . sfromPrimal . sfromR . rfromScalar $ interpretAstPrimal env i
  AstIndexS @sh1 @_ @_ @r v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAstPrimal env <$> ix
    in sindex @target @r @sh1 v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
{- TODO:
  AstSum (AstN2R TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstTranspose uperm u ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstN2R TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstN2R TimesOp [ AstTranspose tperm t
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstN2R TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstN2R TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstN2R TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ]))))
  AstSum v@(AstN2R TimesOp [ AstTranspose tperm (AstReplicate _tk t)
                          , AstTranspose uperm (AstReplicate _uk u) ])
    | Just Refl <- sameNat (Proxy @n) (Proxy @2) ->
        let interpretMatmul2 t1 u1 =
              let t2 = interpretAst env t1
                  u2 = interpretAst env u1
              in rmatmul2 t2 u2
        in case (tperm, uperm) of
          ([2, 1, 0], [1, 0]) ->  -- tk and uk are fine due to perms matching
            interpretMatmul2 t u
          ([1, 0], [2, 1, 0]) ->
            interpretMatmul2 u t
          ([2, 1, 0], [2, 0, 1]) ->
            interpretMatmul2 t (astTranspose [1, 0] u)
          ([2, 0, 1], [2, 1, 0]) ->
            interpretMatmul2 u (astTranspose [1, 0] t)
          ([1, 2, 0], [1, 0]) ->
            interpretMatmul2 (astTranspose [1, 0] t) u
          ([1, 0], [1, 2, 0]) ->
            interpretMatmul2 (astTranspose [1, 0] u) t
          -- The variants below emerge when the whole term is transposed.
          -- All overlap with variants above and the cheaper one is selected.
          ([2, 0, 1], [1, 2, 0]) ->
            ttr
            $ interpretMatmul2 t u
          ([1, 2, 0], [2, 0, 1]) ->
            ttr
            $ interpretMatmul2 u t
          _ -> rsum $ interpretAst env v
  AstSum (AstN2R TimesOp [t, u])
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstN2R TimesOp [t, u]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstN2R TimesOp [t, u]))  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot1In t1 t2
  AstSum (AstReshape sh (AstTranspose _ t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env (AstSum (AstReshape sh t))
  AstSum (AstReshape sh (AstReverse t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env (AstSum (AstReshape sh t))
  AstSum (AstReshape _sh (AstSum t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        rsum0 $ interpretAst env t
  AstSum (AstSum t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        rsum0 $ interpretAst env t
          -- more cases are needed so perhaps we need AstSum0
  AstSum (AstLet var v t) -> interpretAst env (AstLet var v (AstSum t))
  AstSum (AstReshape sh (AstLet var v t)) ->
    interpretAst env (AstLet var v (AstSum (AstReshape sh t)))
  AstSum (AstReshape _sh t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        rsum0 $ interpretAst env t
-}
  AstSumS v -> ssum $ interpretAst env v
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstScatterS @_ @p @sh v (ZS, ix) ->
    gcastWith (unsafeCoerce Refl :: Take p sh ++ Drop p sh :~: sh)
    soneHot (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstScatterS v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndexS interpretAstPrimal env (vars, ix)
    in sscatter t1 f2
  AstFromVectorS l ->
    let l2 = V.map (interpretAst env) l
    in sfromVector l2
{- TODO:
  AstReshape sh (AstReplicate @m _ s)
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env s
        in rreplicate0N sh t1
  AstReshape sh (AstLet var v (AstReplicate k t)) ->
    interpretAst env (AstLet var v (AstReshape sh (AstReplicate k t)))
-}
  AstAppendS x y ->
    let t1 = interpretAst env x
        t2 = interpretAst env y
    in sappend t1 t2
  AstSliceS @i v -> sslice (Proxy @i) Proxy (interpretAst env v)
  AstReverseS v -> sreverse (interpretAst env v)
  AstTransposeS perm v -> stranspose perm $ interpretAst env v
  AstReshapeS v -> sreshape (interpretAst env v)
  AstGatherS @_ @p @sh v (ZS, ix) ->
    gcastWith (unsafeCoerce Refl :: Take p sh ++ Drop p sh :~: sh)
    sindex (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstGatherS @sh2 @p @sh @r AstIotaS (vars, i :.$ ZIS) ->
    gcastWith (unsafeCoerce Refl :: Take (Rank sh2) sh2 :~: sh2)
    $ gcastWith (unsafeCoerce Refl :: Drop (Rank sh2) sh2 :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Drop p sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: sh2 :~: sh2 ++ Drop p sh)
        -- transitivity of type equality doesn't work, by design,
        -- so this direct cast is needed instead of more basic laws
    $ sbuild @target @(TKScalar r) @(Rank sh2)
             (interpretLambdaIndexS
                interpretAst env
                (vars, fromPrimal @s $ AstFromIntegralS $ AstFromScalar i))
  AstGatherS v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndexS interpretAstPrimal env (vars, ix)
    in sgather t1 f2
    -- the operation accepts out of bounds indexes,
    -- for the same reason ordinary indexing does, see above
    -- TODO: currently we store the function on tape, because it doesn't
    -- cause recomputation of the gradient per-cell, unlike storing the build
    -- function on tape; for GPUs and libraries that don't understand Haskell
    -- closures, we can check if the expressions involve tensor operations
    -- too hard for GPUs and, if not, we can store the AST expression
    -- on tape and translate it to whatever backend sooner or later;
    -- and if yes, fall back to POPL pre-computation that, unfortunately,
    -- leads to a tensor of deltas
  AstCastS v -> scast $ interpretAstSRuntimeSpecialized env v
  AstFromIntegralS v ->
    sfromIntegral $ sfromPrimal $ interpretAstPrimalSRuntimeSpecialized env v
  AstProjectS l p ->
    let lt = interpretAst env l
    in tlet @_ @TKUntyped lt
         (\lw -> sfromD $ dunHVector lw V.! p)

  AstMinIndexX _v -> error "TODO"
  AstMaxIndexX _v -> error "TODO"
  AstFloorX _v -> error "TODO"
  AstIotaX -> error "TODO"
  AstN1X opCode u ->
    let u2 = interpretAst env u
    in interpretAstN1 opCode u2
  AstN2X opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstN2 opCode u2 v2
  AstR1X opCode u ->
    let u2 = interpretAst env u
    in interpretAstR1 opCode u2
  AstR2X opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstR2F opCode u2 v2
  AstI2X opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstI2F opCode u2 v2
  AstSumOfListX args ->
    let args2 = interpretAst env <$> args
    in foldr1 (+) args2  -- avoid @fromInteger 0@ in @sum@
  AstIndexX AstIotaX (_i :.% ZIX) -> error "TODO"
  AstIndexX @sh1 @_ @_ @r v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAstPrimal env <$> ix
    in xindex @target @r @sh1 v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstSumX _v -> error "TODO"
  AstScatterX _v (_vars, _ix) -> error "TODO"
  AstFromVectorX l ->
    let l2 = V.map (interpretAst env) l
    in xfromVector l2
  AstAppendX _x _y -> error "TODO"
  AstSliceX AstIotaX -> error "TODO"
  AstSliceX _v -> error "TODO"
  AstReverseX _v -> error "TODO"
  AstTransposeX _perm _v -> error "TODO"
  AstReshapeX _ _ -> error "TODO"
  AstGatherX AstIotaX (_vars, _i :.% ZIX) -> error "TODO"
  AstGatherX _v (_vars, _ix) -> error "TODO"
  AstCastX _v ->  error "TODO"
  AstFromIntegralX _v -> error "TODO"
  AstProjectX _l _p -> error "TODO"

  AstRFromS v -> rfromS $ interpretAst env v
  AstRFromX v -> rfromX $ interpretAst env v
  AstSFromR v -> sfromR $ interpretAst env v
  AstSFromX v -> sfromX $ interpretAst env v
  AstXFromR v -> xfromR $ interpretAst env v
  AstXFromS v -> xfromS $ interpretAst env v

  AstXNestR v -> xnestR knownShX $ interpretAst env v
  AstXNestS v -> xnestS knownShX $ interpretAst env v
  AstXNest v -> xnest knownShX $ interpretAst env v
  AstXUnNestR v -> xunNestR $ interpretAst env v
  AstXUnNestS v -> xunNestS $ interpretAst env v
  AstXUnNest v -> xunNest $ interpretAst env v

  AstMkHVector l -> dmkHVector $ interpretAstDynamic env <$> l
  AstApply t ll ->
    let t2 = interpretAstHFun env t
          -- this is a bunch of PrimalSpan terms interpreted in, perhaps,
          -- FullSpan terms
        ll2 = interpretAst env ll
          -- these are, perhaps, FullSpan terms, interpreted in the same
          -- as above so that the mixture becomes compatible; if the spans
          -- agreed, the AstApply would likely be simplified before
          -- getting interpreted
    in tApply t2 ll2
  AstMapAccumRDer @accShs @bShs @eShs k accShs bShs eShs f0 df0 rf0 acc0 es
    | (Dict, Dict) <- lemTensorKind1OfAD (stensorKind @accShs)
    , (Dict, Dict) <- lemTensorKind1OfAD (stensorKind @bShs)
    , (Dict, Dict) <- lemTensorKind1OfAD (stensorKind @eShs) ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in dmapAccumRDer (Proxy @target) k accShs bShs eShs f df rf acc02 es2
  AstMapAccumLDer @accShs @bShs @eShs k accShs bShs eShs f0 df0 rf0 acc0 es
    | (Dict, Dict) <- lemTensorKind1OfAD (stensorKind @accShs)
    , (Dict, Dict) <- lemTensorKind1OfAD (stensorKind @bShs)
    , (Dict, Dict) <- lemTensorKind1OfAD (stensorKind @eShs) ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in dmapAccumLDer (Proxy @target) k accShs bShs eShs f df rf acc02 es2

interpretAstDynamic
  :: forall target s. (ADReady target, AstSpan s)
  => AstEnv target
  -> AstDynamic AstMethodLet s -> DynamicTensor target
{-# INLINE interpretAstDynamic #-}
interpretAstDynamic !env = \case
  DynamicRanked w ->
    DynamicRanked $ interpretAstRuntimeSpecialized env w
  DynamicShaped w ->
    DynamicShaped $ interpretAstSRuntimeSpecialized env w
  DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
  DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2

interpretAstHFun
  :: forall target x y. (TensorKind x, TensorKind y)
  => BaseTensor target
  => AstEnv target -> AstHFun x y -> HFunOf target x y
interpretAstHFun _env = \case
  AstLambda ~(var, ftk, l) ->
    tlambda @target ftk $ interpretLambdaHsH interpretAst (var, l)
      -- interpretation in empty environment; makes sense here, because
      -- there are no free variables outside of those listed

interpretAstBool :: ADReady target
                 => AstEnv target -> AstBool AstMethodLet -> BoolOf target
interpretAstBool !env = \case
  AstBoolNot arg -> notB $ interpretAstBool env arg
  AstB2 opCodeBool arg1 arg2 ->
    let b1 = interpretAstBool env arg1
        b2 = interpretAstBool env arg2
    in interpretAstB2 opCodeBool b1 b2
  AstBoolConst a -> if a then true else false
  AstRel @y3 opCodeRel arg1 arg2 ->
    case stensorKind @y3 of
      STKScalar{} ->
        let r1 = interpretAstPrimal env arg1
            r2 = interpretAstPrimal env arg2
        in interpretAstRelOp opCodeRel r1 r2
      STKR SNat STKScalar{} ->
        let r1 = interpretAstPrimalRuntimeSpecialized env arg1
            r2 = interpretAstPrimalRuntimeSpecialized env arg2
        in interpretAstRelOp opCodeRel r1 r2
      STKS sh STKScalar{} -> withKnownShS sh $
        let r1 = interpretAstPrimalSRuntimeSpecialized env arg1
            r2 = interpretAstPrimalSRuntimeSpecialized env arg2
        in interpretAstRelOp opCodeRel r1 r2
      STKX sh STKScalar{} -> withKnownShX sh $
        let r1 = interpretAstPrimal env arg1
            r2 = interpretAstPrimal env arg2
        in interpretAstRelOp opCodeRel r1 r2
      _ -> error "TODO"
