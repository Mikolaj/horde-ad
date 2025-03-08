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
  ( interpretAst
  ) where

import Prelude

import Data.Dependent.EnumMap.Strict.Unsafe qualified as DMap.Unsafe
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested.Internal.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstTools
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- Strict environment and strict ADVal and Delta make this is hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall target y. ADReady target
  => AstEnv target
  -> AstTensor AstMethodLet PrimalSpan y
  -> PrimalOf target y
interpretAstPrimal !env v1 = case v1 of
  AstPrimalPart (AstFromPrimal u) -> interpretAstPrimal env u
  AstPrimalPart (AstFromDual u) -> tconstantTarget 0 (ftkAst u)
  AstCond b a1 a2 ->
    -- This avoids multiple ifH expansions in ADVal.
    let c = interpretAstBool env b
    in tcond (ftkToSTK $ ftkAst a1) c
             (interpretAstPrimal env a1) (interpretAstPrimal env a2)
  _ ->
    tprimalPart (interpretAst env v1)

interpretAstDual
  :: forall target y. ADReady target
  => AstEnv target
  -> AstTensor AstMethodLet DualSpan y -> DualOf target y
interpretAstDual !env v1 = case v1 of
  AstDualPart (AstFromDual u) -> interpretAstDual env u
  _ ->
    tdualPart (ftkToSTK $ ftkAst v1) (interpretAst env v1)

interpretAst
  :: forall target s y. (ADReady target, AstSpan s)
  => AstEnv target
  -> AstTensor AstMethodLet s y -> target y
interpretAst !env = \case
  AstPair t1 t2 -> tpair (interpretAst env t1) (interpretAst env t2)
  AstProject1 t -> tproject1 (interpretAst env t)
  AstProject2 t -> tproject2 (interpretAst env t)
  AstFromVector snat stk l ->
    let l2 = V.map (interpretAst env) l
    in tfromVector snat stk l2
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
  AstMapAccumRDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in tmapAccumRDer (Proxy @target) k (ftkAst acc0) bftk eftk f df rf acc02 es2
  AstMapAccumLDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in tmapAccumLDer (Proxy @target) k (ftkAst acc0) bftk eftk f df rf acc02 es2
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
  AstVar var ->
   let var2 :: AstVarName FullSpan y
       var2 = unsafeCoerce var
-- TODO: this unsafe call is needed for benchmark VTO1.
-- Once VTO1 is fixed in another way, try to make it safe.
-- BTW, the old assertion tests the same thing and more.
   in case DMap.Unsafe.lookupUnsafe var2 env of
    Just (AstEnvElem t) ->
#ifdef WITH_EXPENSIVE_ASSERTIONS
      assert (tftk (ftkToSTK $ varNameToFTK var) t == varNameToFTK var
              `blame` ( tftk (ftkToSTK $ varNameToFTK var) t
                      , varNameToFTK var, var, t ))
#endif
      t
    _ -> error $ "interpretAst: unknown AstVar " ++ show var
-- TODO:                 ++ " in environment " ++ showsPrecAstEnv 0 env ""
  AstCond b a1 a2 ->
    let c = interpretAstBool env b
    in tcond (ftkToSTK (ftkAst a1))
             c (interpretAst env a1) (interpretAst env a2)
  AstBuild1 snat stk (var, v) ->
    let f i = interpretAst (extendEnvI var i env) v
    in tbuild1 snat stk f

  -- We assume there are no nested lets with the same variable.
  AstLet var u v ->
    let t = interpretAst env u
        env2 w = extendEnv var w env
    in ttlet t (\w -> interpretAst (env2 w) v)

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
  AstFromPrimal a ->
    tfromPrimal (ftkToSTK (ftkAst a)) (interpretAstPrimal env a)
  AstFromDual a -> tfromDual (interpretAstDual env a)

  AstPlusK u v -> interpretAst env u + interpretAst env v
  AstTimesK u v -> interpretAst env u * interpretAst env v
  AstN1K opCode u ->
    let u2 = interpretAst env u
    in interpretAstN1 opCode u2
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
  AstConcreteK k -> tkconcrete k
  AstFloorK v ->
    tkfloor $ tfromPrimal STKScalar $ interpretAstPrimal env v
  AstFromIntegralK v ->
    tkfromIntegral $ tfromPrimal STKScalar $ interpretAstPrimal env v
  AstCastK v -> tkcast $ interpretAst env v

  AstPlusS u v -> interpretAst env u + interpretAst env v
  AstTimesS u v -> interpretAst env u * interpretAst env v
  AstN1S opCode u -> interpretAstN1 opCode (interpretAst env u)
  AstR1S opCode u -> interpretAstR1 opCode (interpretAst env u)
  AstR2S opCode u v ->
    interpretAstR2F opCode (interpretAst env u) (interpretAst env v)
  AstI2S opCode u v ->
    interpretAstI2F opCode (interpretAst env u) (interpretAst env v)
  AstConcreteS a -> tsconcrete a
  AstFloorS v -> case ftkAst v of
    FTKS sh _ ->
      withKnownShS sh $
      tsfloor $ tfromPrimal knownSTK $ interpretAstPrimal env v
  AstFromIntegralS v -> case ftkAst v of
    FTKS sh _ ->
      withKnownShS sh $
      tsfromIntegral $ tfromPrimal knownSTK $ interpretAstPrimal env v
  AstCastS @r1 @r2 v ->
    -- Specializing for the cases covered by rules in GHC.Internal.Float.
    case testEquality (typeRep @r1) (typeRep @Double) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @Float) of
        Just Refl -> tscast @_ @Double @Float $ interpretAst env v
        _ -> tscast @_ @Double $ interpretAst env v
      _ -> case testEquality (typeRep @r1) (typeRep @Float) of
        Just Refl -> case testEquality (typeRep @r2) (typeRep @Double) of
          Just Refl -> tscast @_ @Float @Double $ interpretAst env v
          _ -> tscast @_ @Float $ interpretAst env v
        _ -> tscast $ interpretAst env v

  AstIndexS @sh1 sh2 v ix -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS (ixsToShS ix) $
      withKnownShS sh2 $
      withKnownSTK x $
      let v2 = interpretAst env v
          ix3 = interpretAstPrimal env <$> ix
      in tsindex @target @sh1 v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstScatterS shn v (ZS, ix) -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      withKnownSTK x $
      tsoneHot (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstScatterS @shm @shn @shp
              shn v (vars, ix) -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS (listsToShS vars) $
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      withKnownSTK x $
      let t1 = interpretAst env v
          f2 = interpretLambdaIndexToIndexS interpretAstPrimal env (vars, ix)
      in tsscatter @_ @shm @shn @shp t1 f2
  AstGatherS shn v (ZS, ix) -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      withKnownSTK x $
      tsindex (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstGatherS @shm @shn @shp
             shn v (vars, ix) -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS (listsToShS vars) $
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      withKnownSTK x $
      let t1 = interpretAst env v
          f2 = interpretLambdaIndexToIndexS interpretAstPrimal env (vars, ix)
      in tsgather @_ @shm @shn @shp t1 f2
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
  AstMinIndexS v -> case ftkToSTK (ftkAst v) of
    STKS (_ :$$ sh) x ->
      withKnownShS sh $
      withKnownSTK x $
      tsminIndex $ tfromPrimal knownSTK $ interpretAstPrimal env v
  AstMaxIndexS v -> case ftkToSTK (ftkAst v) of
    STKS (_ :$$ sh) x ->
      withKnownShS sh $
      withKnownSTK x $
      tsmaxIndex $ tfromPrimal knownSTK $ interpretAstPrimal env v
  AstIotaS SNat -> tsiota
  AstAppendS a b -> case ftkToSTK (ftkAst a) of
    STKS _ x ->
      withKnownSTK x $
      let t1 = interpretAst env a
          t2 = interpretAst env b
      in tsappend t1 t2
  AstSliceS i n k v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tsslice i n k $ interpretAst env v
  AstReverseS v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tsreverse (interpretAst env v)
  AstTransposeS perm v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tstranspose perm $ interpretAst env v
  AstReshapeS sh2 v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tsreshape sh2 (interpretAst env v)
  AstZipS v -> szip $ interpretAst env v
  AstUnzipS v -> sunzip $ interpretAst env v
  AstNestS sh1 sh2 v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS sh2 $
      withKnownSTK x $
      snest sh1 $ interpretAst env v
  AstUnNestS v -> case ftkToSTK (ftkAst v) of
    STKS sh1 (STKS sh2 x) ->
      withKnownShS sh1 $
      withKnownShS sh2 $
      withKnownSTK x $
      sunNest $ interpretAst env v

  AstFromS stkz v -> tfromS (ftkToSTK (ftkAst v)) stkz (interpretAst env v)
  AstSFromK t -> sfromK $ interpretAst env t
  AstSFromR sh v -> case ftkToSTK (ftkAst v) of
    STKR _ x ->
      withKnownShS sh $
      withKnownSTK x $
      sfromR $ interpretAst env v
  AstSFromX sh v -> case ftkToSTK (ftkAst v) of
    STKX _ x ->
      withKnownShS sh $
      withKnownSTK x $
      sfromX $ interpretAst env v

  AstReplicate0NS sh v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tsreplicate0N sh (interpretAst env v)
  AstSum0S v -> case ftkToSTK (ftkAst v) of
    STKS sh x ->
      withKnownShS sh $
      withKnownSTK x $
      tssum0 (interpretAst env v)
  AstDot0S u v -> case ftkAst u of
    FTKS sh _ ->
      withKnownShS sh $
      tsdot0 (interpretAst env u) (interpretAst env v)
  AstDot1InS SNat n@SNat u v ->
    tsdot1In n (interpretAst env u) (interpretAst env v)
  AstMatvecmulS @r SNat SNat u v ->
    case testEquality (typeRep @r) (typeRep @Double) of
      Just Refl ->
        tsmatvecmul @_ @_ @_ @Double (interpretAst env u) (interpretAst env v)
      _ -> case testEquality (typeRep @r) (typeRep @Float) of
        Just Refl ->
          tsmatvecmul @_ @_ @_ @Float (interpretAst env u) (interpretAst env v)
        _ -> tsmatvecmul (interpretAst env u) (interpretAst env v)
  AstMatmul2S SNat SNat SNat u v ->
    tsmatmul2 (interpretAst env u) (interpretAst env v)

interpretAstHFun
  :: forall target x y. BaseTensor target
  => AstEnv target -> AstHFun x y -> HFunOf target x y
interpretAstHFun _env = \case
  AstLambda var l ->
    tlambda @target (varNameToFTK var)
    $ HFun $ \ws -> interpretAst (extendEnv var ws emptyEnv) l
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
  AstRelK opCodeRel arg1 arg2 ->
    let r1 = interpretAstPrimal env arg1
        r2 = interpretAstPrimal env arg2
    in interpretAstRelOp opCodeRel r1 r2
  AstRelS opCodeRel arg1 arg2 ->
    let r1 = interpretAstPrimal env arg1
        r2 = interpretAstPrimal env arg2
    in interpretAstRelOp opCodeRel r1 r2
