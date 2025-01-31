{-# LANGUAGE CPP #-}
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

import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Int (Int64)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Foreign.C (CInt)
import GHC.TypeLits (KnownNat)
import Type.Reflection (Typeable, typeRep)

import Data.Array.Mixed.Shape (withKnownShX)
import Data.Array.Nested (KnownShS (..), ListS (..))
import Data.Array.Nested.Internal.Shape (shsAppend, shsProduct, withKnownShS)

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstTools
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

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
  :: forall target y. (ADReady target, KnownSTK y)
  => AstEnv target
  -> AstTensor AstMethodLet PrimalSpan y
  -> PrimalOf target y
interpretAstPrimal !env v1 = case v1 of
  AstPrimalPart (AstFromPrimal u) -> interpretAstPrimal env u
  AstPrimalPart (AstFromDual u) -> tconstantTarget 0 (ftkAst u)
  AstCond @y2 b a1 a2 ->
    -- This avoids multiple ifF expansions in ADVal.
    let c = interpretAstBool env b
    in tcond (knownSTK @y2) c
             (interpretAstPrimal env a1) (interpretAstPrimal env a2)
  _ ->
    tprimalPart (knownSTK @y) (interpretAst env v1)

interpretAstDual
  :: forall target y. (ADReady target, KnownSTK y)
  => AstEnv target
  -> AstTensor AstMethodLet DualSpan y -> DualOf target y
interpretAstDual !env v1 = case v1 of
  AstDualPart (AstFromDual u) -> interpretAstDual env u
  _ ->
    tdualPart (knownSTK @y) (interpretAst env v1)

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
  AstPair t1 t2 -> tpair (interpretAst env t1) (interpretAst env t2)
  AstProject1 t -> tproject1 (interpretAst env t)
  AstProject2 t -> tproject2 (interpretAst env t)
  AstFromVector snat l ->
    let l2 = V.map (interpretAst env) l
    in tfromVector snat knownSTK l2
  AstSum snat stk v -> tsum snat stk $ interpretAst env v
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstReplicate snat stk v ->
    treplicate snat stk (interpretAst env v)
  -- The following can't be, in general, so partially evaluated, because v
  -- may contain variables that the evironment sends to terms,
  -- not to concrete numbers (and so Primal a is not equal to a).
  -- However, this matters only for POPL AD, not JAX AD and also it matters
  -- only with no vectorization of, at least, constant (primal-only) terms.
  -- AstBuild1 k (var, AstFromPrimal v) ->
  --   tconcrete
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env (var, v)
  AstMapAccumRDer @accShs @bShs @eShs k bShs eShs f0 df0 rf0 acc0 es
    | Dict <- lemKnownSTKOfAD (knownSTK @accShs)
    , Dict <- lemKnownSTKOfAD (knownSTK @bShs)
    , Dict <- lemKnownSTKOfAD (knownSTK @eShs) ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in dmapAccumRDer (Proxy @target) k (ftkAst acc0) bShs eShs f df rf acc02 es2
  AstMapAccumLDer @accShs @bShs @eShs k bShs eShs f0 df0 rf0 acc0 es
    | Dict <- lemKnownSTKOfAD (knownSTK @accShs)
    , Dict <- lemKnownSTKOfAD (knownSTK @bShs)
    , Dict <- lemKnownSTKOfAD (knownSTK @eShs) ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in dmapAccumLDer (Proxy @target) k (ftkAst acc0) bShs eShs f df rf acc02 es2
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
  AstVar @y2 _sh var ->
   let var2 = mkAstVarName @FullSpan @y2 (varNameToAstVarId var)  -- TODO
   in case DMap.lookup var2 env of
    Just (AstEnvElemRep t) ->
#ifdef WITH_EXPENSIVE_ASSERTIONS
      assert (tftk (knownSTK @y2) t == _sh
              `blame` (_sh, tftk (knownSTK @y2) t, var, t))
#endif
      t
    _ -> error $ "interpretAst: unknown AstVar " ++ show var
-- TODO:                 ++ " in environment " ++ showsPrecAstEnv 0 env ""
  AstCond @y2 b a1 a2 ->
    let c = interpretAstBool env b
    in tcond (knownSTK @y2) c (interpretAst env a1) (interpretAst env a2)
  AstBuild1 snat (var, v) ->
    let f i = interpretAst (extendEnvI var i env) v
    in tbuild1 snat f
  AstConcrete ftk a -> tconcrete ftk a

  AstLet @y2 var u v -> case knownSTK @y2 of
    -- We assume there are no nested lets with the same variable.
    STKR _ STKScalar{} ->
      let t = interpretAstRuntimeSpecialized env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)
    STKS _ STKScalar{} ->
      let t = interpretAstSRuntimeSpecialized env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)
    _ ->
      let t = interpretAst env u
          env2 w = extendEnv var w env
      in tlet t (\w -> interpretAst (env2 w) v)

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
  AstFromPrimal @y2 a -> tfromPrimal (knownSTK @y2) (interpretAstPrimal env a)
  AstFromDual @y2 a -> tfromDual (knownSTK @y2) (interpretAstDual env a)

  AstSumOfList stk args ->
    let args2 = interpretAst env <$> args
    in case stk of
      STKScalar{} -> foldr1 (+) args2  -- @sum@ breaks and also reverses order
      STKR SNat STKScalar{} -> foldr1 (+) args2
      STKS sh STKScalar{} -> withKnownShS sh $ foldr1 (+) args2
      STKX sh STKScalar{} -> withKnownShX sh $ foldr1 (+) args2
      _ -> let v = V.fromList args2
           in withSNat (V.length v) $ \snat ->
                tsum snat stk $ tfromVector snat stk v

  AstN1K opCode u ->
    let u2 = interpretAst env u
    in interpretAstN1 opCode u2
  AstN2K opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstN2 opCode u2 v2
  AstR1K opCode u ->
    let u2 = interpretAst env u
    in interpretAstR1 opCode u2
  AstR2K opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstR2 opCode u2 v2
  AstI2K opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstI2F opCode u2 v2
  AstFloorK v ->
    kfloor $ tfromPrimal (STKScalar typeRep) $ interpretAstPrimal env v
  AstFromIntegralK v ->
    kfromIntegral $ tfromPrimal (STKScalar typeRep) $ interpretAstPrimal env v
  AstCastK v -> kcast $ interpretAst env v

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
  AstFloorS v ->
    sfloor $ sfromPrimal $ interpretAstPrimalSRuntimeSpecialized env v
  AstFromIntegralS v ->
    sfromIntegral $ sfromPrimal $ interpretAstPrimalSRuntimeSpecialized env v
  AstCastS v -> scast $ interpretAstSRuntimeSpecialized env v

  AstIndexS @sh1 @sh2 v ix ->
    withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
    let v2 = interpretAst env v
        ix3 = interpretAstPrimal env <$> ix
    in sindex @target @_ @sh1 v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstScatterS @_ @shn @shp v (ZS, ix) ->
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    soneHot (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstScatterS @shm @shn @shp v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndexS interpretAstPrimal env (vars, ix)
    in sscatter @_ @_ @shm @shn @shp t1 f2
  AstGatherS @_ @shn @shp v (ZS, ix) ->
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    sindex (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstGatherS @shm @shn @shp v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndexS interpretAstPrimal env (vars, ix)
    in sgather @_ @_ @shm @shn @shp t1 f2
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
  AstMinIndexS v ->
    sminIndex $ sfromPrimal $ interpretAstPrimalSRuntimeSpecialized env v
  AstMaxIndexS v ->
    smaxIndex $ sfromPrimal $ interpretAstPrimalSRuntimeSpecialized env v
  AstIotaS -> siota
  AstAppendS x y ->
    let t1 = interpretAst env x
        t2 = interpretAst env y
    in sappend t1 t2
  AstSliceS @i v -> sslice (Proxy @i) Proxy (interpretAst env v)
  AstReverseS v -> sreverse (interpretAst env v)
  AstTransposeS perm v -> stranspose perm $ interpretAst env v
  AstReshapeS v -> sreshape (interpretAst env v)
  AstZipS v -> szip $ interpretAst env v
  AstUnzipS v -> sunzip $ interpretAst env v
  AstNestS v -> snest knownShS $ interpretAst env v
  AstUnNestS v -> sunNest $ interpretAst env v

  AstFromS stkz v | Dict <- lemKnownSTK (ftkToSTK (ftkAst v))
                  , Dict <- lemKnownSTK stkz ->
    tfromS $ interpretAst env v
  AstSFromK t -> sfromK $ interpretAst env t
  AstSFromR v -> sfromR $ interpretAst env v
  AstSFromX v -> sfromX $ interpretAst env v

  AstReplicate0NS sh stk v | Dict <- lemKnownSTK stk
                           , SNat <- shsProduct sh ->
    withKnownShS sh $
    sreplicate0N (interpretAst env v)
  AstSum0S sh stk v | Dict <- lemKnownSTK stk
                    , SNat <- shsProduct sh ->
    withKnownShS sh $
    ssum0 (interpretAst env v)
  AstDot0S sh u v | SNat <- shsProduct sh ->
    withKnownShS sh $
    sdot0 (interpretAst env u) (interpretAst env v)
  AstDot1InS SNat n@SNat u v ->
    sdot1In n (interpretAst env u) (interpretAst env v)
  AstMatvecmulS SNat SNat u v ->
    smatvecmul (interpretAst env u) (interpretAst env v)
  AstMatmul2S SNat SNat SNat u v ->
    smatmul2 (interpretAst env u) (interpretAst env v)

interpretAstHFun
  :: forall target x y. (KnownSTK x, KnownSTK y)
  => BaseTensor target
  => AstEnv target -> AstHFun x y -> HFunOf target x y
interpretAstHFun _env = \case
  AstLambda ~(var, ftk, l) ->
    tlambda @target ftk $ interpretLambdaHFun interpretAst (var, l)
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
    case knownSTK @y3 of
      STKR SNat STKScalar{} ->
        let r1 = interpretAstPrimalRuntimeSpecialized env arg1
            r2 = interpretAstPrimalRuntimeSpecialized env arg2
        in interpretAstRelOp opCodeRel r1 r2
      STKS sh STKScalar{} -> withKnownShS sh $
        let r1 = interpretAstPrimalSRuntimeSpecialized env arg1
            r2 = interpretAstPrimalSRuntimeSpecialized env arg2
        in interpretAstRelOp opCodeRel r1 r2
      _ ->
        let r1 = interpretAstPrimal env arg1
            r2 = interpretAstPrimal env arg2
        in interpretAstRelOp opCodeRel r1 r2
