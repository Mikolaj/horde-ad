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
  , interpretAstHVector
  -- * Exported only to specialize elsewhere (because transitive specialization may not work, possibly)
  , interpretAstPrimalRuntimeSpecialized, interpretAstPrimalSRuntimeSpecialized
  , interpretAstDual
  , interpretAstRuntimeSpecialized, interpretAstSRuntimeSpecialized
  , interpretAstBool
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Array.Internal (valueOf)
import Data.Array.Shape qualified as Sh
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Int (Int64)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Foreign.C (CInt)
import GHC.TypeLits (KnownNat, sameNat)
import Type.Reflection (Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Shape qualified as X
import Data.Array.Mixed.Types qualified as X
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.ShapedList (pattern (:.$), pattern ZIS)
import HordeAd.Util.SizedList

interpretAstPrimalRuntimeSpecialized
  :: forall ranked n r.
     (KnownNat n, ADReady ranked, Typeable r)
  => AstEnv ranked
  -> AstTensor PrimalSpan (TKR r n) -> PrimalOf ranked r n
interpretAstPrimalRuntimeSpecialized !env t =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable and RowSum instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
  -- TODO: revisit using TypeRepOf to pattern match
  -- instead of nesting conditionals
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAstPrimal @ranked @(TKR Double n) env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAstPrimal @ranked @(TKR Float n) env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAstPrimal @ranked @(TKR Int64 n) env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAstPrimal @ranked @(TKR CInt n) env t
          _ -> error "an unexpected underlying scalar type"  -- catch absurd

interpretAstPrimalSRuntimeSpecialized
  :: forall ranked sh r.
     (KnownShS sh, ADReady ranked, Typeable r)
  => AstEnv ranked
  -> AstTensor PrimalSpan (TKS r sh) -> PrimalOf (ShapedOf ranked) r sh
interpretAstPrimalSRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAstPrimal @ranked @(TKS Double sh) env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAstPrimal @ranked @(TKS Float sh) env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAstPrimal @ranked @(TKS Int64 sh) env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAstPrimal @ranked @(TKS CInt sh) env t
          _ -> error "an unexpected underlying scalar type"  -- catch absurd

-- Strict environment and strict ADVal and Delta make this is hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall ranked y. (ADReady ranked, TensorKind y)
  => AstEnv ranked
  -> AstTensor PrimalSpan y -> InterpretationTarget (PrimalOf ranked) y
interpretAstPrimal !env v1 = case v1 of
  AstPrimalPart (AstD u _) -> interpretAstPrimal env u
  AstPrimalPart (AstConstant u) -> interpretAstPrimal env u
  AstCond @y2 b a1 a2 ->
    -- This avoids multiple ifF expansions via ifB(ADVal)
    let c = interpretAstBool env b
    in mapInterpretationTarget2
        @(PrimalOf ranked) @(PrimalOf ranked) @(PrimalOf ranked)
        (ifF c) (ifF c)  -- this is ifF from PrimalOf ranked
        (stensorKind @y2)
        (interpretAstPrimal env a1) (interpretAstPrimal env a2)
  _ ->
    mapInterpretationTarget @ranked @(PrimalOf ranked)
      rprimalPart sprimalPart (stensorKind @y)
      (interpretAst env v1)

interpretAstDual
  :: forall ranked y. (ADReady ranked, TensorKind y)
  => AstEnv ranked
  -> AstTensor DualSpan y -> InterpretationTarget (DualOf ranked) y
interpretAstDual !env v1 = case v1 of
  AstDualPart (AstD _ u') -> interpretAstDual env u'
  _ ->
    mapInterpretationTarget @ranked @(DualOf ranked)
      rdualPart sdualPart (stensorKind @y)
      (interpretAst env v1)

interpretAstRuntimeSpecialized
  :: forall ranked n s r.
     (ADReady ranked, Typeable r, AstSpan s)
  => AstEnv ranked
  -> AstTensor s (TKR r n) -> ranked r n
interpretAstRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAst @ranked @s @(TKR Double n) env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAst @ranked @s @(TKR Float n) env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAst @ranked @s @(TKR Int64 n) env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAst @ranked @s @(TKR CInt n) env t
          _ -> error "an unexpected underlying scalar type"

interpretAstSRuntimeSpecialized
  :: forall ranked sh s r.
     (ADReady ranked, Typeable r, AstSpan s)
  => AstEnv ranked
  -> AstTensor s (TKS r sh) -> ShapedOf ranked r sh
interpretAstSRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAst @ranked @s @(TKS Double sh) env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAst @ranked @s @(TKS Float sh) env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAst @ranked @s @(TKS Int64 sh) env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAst @ranked @s @(TKS CInt sh) env t
          _ -> error "an unexpected underlying scalar type"

interpretAst
  :: forall ranked s y. (ADReady ranked, AstSpan s)
  => AstEnv ranked
  -> AstTensor s y -> InterpretationTarget ranked y
interpretAst !env = \case
  AstTuple t1 t2 -> (interpretAst env t1, interpretAst env t2)
  AstVar @y2 _sh var ->
   let var2 = mkAstVarName @FullSpan @y2 (varNameToAstVarId var)  -- TODO
   in case DMap.lookup var2 env of
    Just (AstEnvElemTuple @_ @y3 t) -> case sameTensorKind @y2 @y3 of
      Just Refl -> -- TODO: assert (rshape t == sh
                   --          `blame` (sh, rshape t, var, t, env)) t
                   t
      _ -> error $ "interpretAst: wrong kind in environment"
                   `showFailure`
                   (stensorKind @y2, stensorKind @y3, var) -- TODO: , t)
    _ -> error $ "interpretAst: unknown AstVar " ++ show var
      -- this is defeated by 'Undecidable instances and loopy superclasses':
      -- ++ " in environment " ++ show env
  AstPrimalPart a -> interpretAst env a
    -- This is correct, because @s@ must be @PrimalSpan@ and so @ranked@ must
    -- be morally the primal part of a dual numbers type that is the codomain
    -- of the interpretation of the same AST but marked with @FullSpan@.
    -- Consequently, the result is a primal part, despite the appearances.
    -- This whole notation abuse is for user comfort (less @PrimalOf@
    -- in the tensor classes) and to avoid repeating the @interpretAst@ code
    -- in @interpretAstPrimal@. TODO: make this sane.
    --
    -- For example, if I'm interpreting @AstRanked PrimalSpan@ in
    -- @AstRanked FullSpan@ (basically doing the forward pass
    -- via interpretation), then @ranked@ is a primal part
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
    -- This is correct, because @s@ must be @DualSpan@ and so @ranked@ must
    -- be morally the dual part of a dual numbers type that is the codomain
    -- of the interpretation of the same AST but marked with @FullSpan@.
    -- Consequently, the result is a dual part, despite the appearances.
  AstConstant @y2 a ->
    mapInterpretationTarget @(PrimalOf ranked) @ranked
      rconstant sconstant (stensorKind @y2)
      (interpretAstPrimal env a)
  AstD @y2 u u' ->
    let t1 = interpretAstPrimal env u
        t2 = interpretAstDual env u'
    in mapInterpretationTarget2 @(PrimalOf ranked) @(DualOf ranked) @ranked
         rD sD
         (stensorKind @y2)
         t1 t2
  AstCond @y2 b a1 a2 ->
    -- This avoids multiple ifF expansions via ifB(ADVal)
    let c = interpretAstBool env b
    in mapInterpretationTarget2 @ranked @ranked @ranked
         (ifF c) (ifF c)
         (stensorKind @y2)
         (interpretAst env a1) (interpretAst env a2)
  AstLetTupleIn @_ @z1 @z2 var1 var2 p v ->
    let (t1, t2) = interpretAst env p
        env2 w1 w2 = extendEnv var2 w2 $ extendEnv var1 w1 env
    in rletTKIn (stensorKind @z1) t1 $ \w1 ->
         rletTKIn (stensorKind @z2) t2 $ \w2 ->
           interpretAst (env2 w1 w2) v
  AstLet @_ @_ @y2 var u v -> case stensorKind @y2 of
    stk@STKR{} ->
      -- We assume there are no nested lets with the same variable.
      let t = interpretAstRuntimeSpecialized env u
          env2 w = extendEnv var w env
      in rletTKIn stk t (\w -> interpretAst (env2 w) v)
    stk@STKS{} ->
      let t = interpretAstSRuntimeSpecialized env u
          env2 w = extendEnv var w env
      in rletTKIn stk t (\w -> interpretAst (env2 w) v)
    stk@STKProduct{} ->
      let t = interpretAst env u
          env2 w = extendEnv var w env
      in rletTKIn stk t (\w -> interpretAst (env2 w) v)
  AstShare{} -> error "interpretAst: AstShare"
  AstMinIndex v ->
    rminIndex $ rconstant $ interpretAstPrimalRuntimeSpecialized env v
  AstMaxIndex v ->
    rmaxIndex $ rconstant $ interpretAstPrimalRuntimeSpecialized env v
  AstFloor v ->
    rfloor $ rconstant $ interpretAstPrimalRuntimeSpecialized env v
  AstIota -> error "interpretAst: bare AstIota, most likely a bug"
  {- TODO: revise when we handle GPUs. For now, this is done in TensorOps
     instead and that's fine, because for one-element carriers,
     reshape and replicate are very cheap. OTOH, this was introducing
     ScalarR(UnScalar0 ...) into delta expressions by firing
     in an early phase.
  AstN2 TimesOp [v, AstReshape _ (AstReplicate @m _ s)]
   -- TODO: also handle nested AstReplicate to prevent executing them
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env v
            t2 = interpretAst env s
        in tscaleByScalar0 t2 t1
  AstN2 TimesOp [v, AstReplicate @m _ s]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env v
            t2 = interpretAst env s
        in tscaleByScalar0 t2 t1
  -}
  AstN2 TimesOp v (AstLet var u (AstReshape sh (AstReplicate @m k s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
        -- The varNameInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env
          (AstLet var u (AstN2 TimesOp v (AstReshape sh
                                            (AstReplicate @m k s))))
  AstN2 TimesOp v (AstReshape sh (AstLet var u (AstReplicate @m k s)))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
        interpretAst env
          (AstLet var u (AstN2 TimesOp v (AstReshape sh
                                            (AstReplicate @m k s))))
  AstN2 TimesOp v (AstLet var u (AstReplicate @m k s))
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varNameInAst var v) ->
        interpretAst env
          (AstLet var u (AstN2 TimesOp v (AstReplicate @m k s)))
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
  AstIndex AstIota (i :.: ZIR) ->
    rfromIntegral $ rconstant $ interpretAstPrimal env i
  AstIndex v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAstPrimal env <$> ix
    in rindex v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstSum (AstN2 TimesOp (AstLet vart vt (AstTranspose tperm t))
                        (AstTranspose uperm u)) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstN2 TimesOp (AstTranspose tperm t)
                                (AstTranspose uperm u))))
  AstSum (AstN2 TimesOp (AstTranspose tperm t)
                        (AstLet varu vu (AstTranspose uperm u))) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstN2 TimesOp (AstTranspose tperm t)
                                (AstTranspose uperm u))))
  AstSum (AstN2 TimesOp (AstLet vart vt (AstTranspose tperm t))
                        (AstLet varu vu (AstTranspose uperm u))) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstN2 TimesOp (AstTranspose tperm t)
                                (AstTranspose uperm u)))))
  AstSum @n
         v@(AstN2 TimesOp (AstTranspose tperm (AstReplicate _tk t))
                          (AstTranspose uperm (AstReplicate _uk u)))
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
  AstSum @n (AstN2 TimesOp t u)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum @n (AstReshape _sh (AstN2 TimesOp t u))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
  AstSum @n (AstTranspose [1, 0] (AstN2 TimesOp t u))  -- TODO: generalize
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
  AstScatter sh v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndex interpretAstPrimal env (vars, ix)
    in rscatter sh t1 f2
  AstFromVector l ->
    let l2 = V.map (interpretAst env) l
    in rfromVector l2
  AstReshape sh (AstReplicate @m _ s)
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env s
        in rreplicate0N sh t1
  AstReshape sh (AstLet var v (AstReplicate k t)) ->
    interpretAst env (AstLet var v (AstReshape sh (AstReplicate k t)))
  AstReplicate k v -> rreplicate k (interpretAst env v)
  AstAppend x y ->
    let t1 = interpretAst env x
        t2 = interpretAst env y
    in rappend t1 t2
  AstSlice i n AstIota ->
    interpretAst env
    $ AstConst $ Nested.Internal.rfromListPrimLinear (n :$: ZSR) $ map fromIntegral [i .. i + n - 1]
  AstSlice i n v -> rslice i n (interpretAst env v)
  AstReverse v -> rreverse (interpretAst env v)
  AstTranspose perm v -> rtranspose perm $ interpretAst env v
  AstReshape sh v -> rreshape sh (interpretAst env v)
  -- These are only needed for tests that don't vectorize Ast.
  AstBuild1 @n
            k (var, AstSum (AstN2 TimesOp t (AstIndex
                                                u (AstIntVar var2 :.: ZIR))))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0)
    , var == var2, k == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 @n
            k (var, AstSum
                      (AstReshape @p
                         _sh (AstN2 TimesOp t (AstIndex
                                                 u (AstIntVar var2 :.: ZIR)))))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, k == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 0 (_, v) -> rfromList0N (0 :$: shapeAst v) []
  -- The following can't be, in general, so partially evaluated, because v
  -- may contain variables that the evironment sends to terms,
  -- not to concrete numbers (and so Primal a is not equal to a).
  -- However, this matters only for POPL AD, not JAX AD and also it matters
  -- only with no vectorization of, at least, constant (primal-only) terms.
  -- AstBuild1 k (var, AstConstant v) ->
  --   tconst
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env (var, v)
  AstBuild1 k (var, v) ->
    rbuild1 k (interpretLambdaI interpretAst env (var, v))
      -- to be used only in tests
  AstGather sh AstIota (vars, i :.: ZIR) ->
    rbuild sh (interpretLambdaIndex interpretAst env
                                    (vars, fromPrimal @s $ AstFromIntegral i))
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
  AstCast v -> rcast $ interpretAstRuntimeSpecialized env v
  AstFromIntegral v ->
    rfromIntegral $ rconstant $ interpretAstPrimalRuntimeSpecialized env v
  AstConst a -> rconst a
  AstProject l p ->
    let lt = interpretAstHVector env l
    in rletHVectorIn lt (\lw -> rfromD $ lw V.! p)
         -- This is weak, but we don't need rproject nor sproject.
         -- Most likely, the term gets simplified before interpretation anyway.
  AstLetHVectorIn vars l v ->
    let lt = interpretAstHVector env l
        env2 lw = assert (voidHVectorMatches (voidFromVars vars) lw
                          `blame` ( shapeVoidHVector (voidFromVars vars)
                                  , V.toList $ V.map shapeDynamic lw
                                  , shapeVoidHVector (shapeAstHVector l)
                                  , shapeVoidHVector (dshape lt) )) $
                 extendEnvHVector vars lw env
    in rletHVectorIn lt (\lw -> interpretAst (env2 lw) v)
  AstLetHFunIn var f v ->
    let g = interpretAstHFun env f
        env2 h = extendEnvHFun var h env
    in rletHFunIn g (\h -> interpretAst (env2 h) v)
  AstRFromS v -> rfromS $ interpretAst env v

  AstLetTupleInS @_ @z1 @z2 var1 var2 p v ->
    let (t1, t2) = interpretAst env p
        env2 w1 w2 = extendEnv var2 w2 $ extendEnv var1 w1 env
    in sletTKIn (stensorKind @z1) t1 $ \w1 ->
         sletTKIn (stensorKind @z2) t2 $ \w2 ->
           interpretAst (env2 w1 w2) v
  AstLetS @_ @_ @y2 var u v -> case stensorKind @y2 of
    stk@STKR{} ->
      -- We assume there are no nested lets with the same variable.
      let t = interpretAstRuntimeSpecialized env u
          env2 w = extendEnv var w env
      in sletTKIn stk t (\w -> interpretAst (env2 w) v)
    stk@STKS{} ->
      let t = interpretAstSRuntimeSpecialized env u
          env2 w = extendEnv var w env
      in sletTKIn stk t (\w -> interpretAst (env2 w) v)
    stk@STKProduct{} ->
      let t = interpretAst env u
          env2 w = extendEnv var w env
      in sletTKIn stk t (\w -> interpretAst (env2 w) v)
  AstShareS{} -> error "interpretAst: AstShareS"
  AstMinIndexS v ->
    sminIndex $ sconstant $ interpretAstPrimalSRuntimeSpecialized env v
  AstMaxIndexS v ->
    smaxIndex $ sconstant $ interpretAstPrimalSRuntimeSpecialized env v
  AstFloorS v ->
    sfloor $ sconstant $ interpretAstPrimalSRuntimeSpecialized env v
  AstIotaS -> siota
{- TODO:
  AstN2 TimesOp [v, AstLet var u (AstReshape sh (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varInAst var v) ->
        -- The varInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env
          (AstLet var u (AstN2 TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstN2 TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varInAst var v) ->
        interpretAst env
          (AstLet var u (AstN2 TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstN2 TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (varInAst var v) ->
        interpretAst env
          (AstLet var u (AstN2 TimesOp [v, AstReplicate @m k s]))
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
    sfromIntegral . sconstant . sfromR $ interpretAstPrimal env i
  AstIndexS @sh1 @_ @_ @r v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAstPrimal env <$> ix
    in sindex @(ShapedOf ranked) @r @sh1 v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
{- TODO:
  AstSum (AstN2 TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstTranspose uperm u ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstN2 TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstN2 TimesOp [ AstTranspose tperm t
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstN2 TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstN2 TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstN2 TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ]))))
  AstSum v@(AstN2 TimesOp [ AstTranspose tperm (AstReplicate _tk t)
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
  AstSum (AstN2 TimesOp [t, u])
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstN2 TimesOp [t, u]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstN2 TimesOp [t, u]))  -- TODO: generalize
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
  AstReplicateS v -> sreplicate (interpretAst env v)
  AstAppendS x y ->
    let t1 = interpretAst env x
        t2 = interpretAst env y
    in sappend t1 t2
  AstSliceS @i @n AstIotaS ->
    let i = valueOf @i
        n = valueOf @n
    in interpretAst env
       $ AstConstS $ Nested.Internal.sfromListPrimLinear Nested.knownShS
       $ map fromIntegral [i :: Int .. i + n - 1]
  AstSliceS @i v -> sslice (Proxy @i) Proxy (interpretAst env v)
  AstReverseS v -> sreverse (interpretAst env v)
  AstTransposeS perm v -> stranspose perm $ interpretAst env v
  AstReshapeS v -> sreshape (interpretAst env v)
  -- These are only needed for tests that don't vectorize Ast.
{- TODO:
  AstBuild1 k (var, AstSum (AstN2 TimesOp [t, AstIndex
                                                u (AstIntVar var2 :.: ZIR)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstN2 TimesOp [t, AstIndex
                                                  u (AstIntVar var2 :.: ZIR)])))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, k == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 0 (_, v) -> rfromList0N (0 :$: rshape v) []
  -- The following can't be, in general, so partially evaluated, because v
  -- may contain variables that the evironment sends to terms,
  -- not to concrete numbers (and so Primal a is not equal to a).
  -- However, this matters only for POPL AD, not JAX AD and also it matters
  -- only with no vectorization of, at least, constant (primal-only) terms.
  -- AstBuild1 k (var, AstConstant v) ->
  --   tconst
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env (var, v)
-}
  AstBuild1S (var, v) ->
    sbuild1 (interpretLambdaIS interpretAst env (var, v))
      -- to be used only in tests
  AstGatherS @sh2 @p @sh @r AstIotaS (vars, i :.$ ZIS) ->
    gcastWith (unsafeCoerce Refl :: Sh.Take (X.Rank sh2) sh2 :~: sh2)
    $ gcastWith (unsafeCoerce Refl :: Sh.Drop (X.Rank sh2) sh2 :~: '[])
    $ gcastWith (unsafeCoerce Refl :: sh2 :~: sh2 X.++ Sh.Drop p sh)
        -- transitivity of type equality doesn't work, by design,
        -- so this direct cast is needed instead of more basic laws
    $ sbuild @(ShapedOf ranked) @r @(X.Rank sh2)
             (interpretLambdaIndexS
                interpretAst env
                (vars, fromPrimal @s $ AstFromIntegralS $ AstSFromR i))
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
    sfromIntegral $ sconstant $ interpretAstPrimalSRuntimeSpecialized env v
  AstConstS a -> sconst a
  AstProjectS l p ->
    let lt = interpretAstHVector env l
    in sletHVectorIn lt (\lw -> sfromD $ lw V.! p)
  AstLetHVectorInS vars l v ->
    let lt = interpretAstHVector env l
        env2 lw = assert (voidHVectorMatches (voidFromVars vars) lw
                          `blame` ( shapeVoidHVector (voidFromVars vars)
                                  , V.toList $ V.map shapeDynamic lw
                                  , shapeVoidHVector (shapeAstHVector l)
                                  , shapeVoidHVector (dshape lt) )) $
                  extendEnvHVector vars lw env
    in sletHVectorIn lt (\lw -> interpretAst (env2 lw) v)
  AstLetHFunInS var f v ->
    let g = interpretAstHFun env f
        env2 h = extendEnvHFun var h env
    in sletHFunIn g (\h -> interpretAst (env2 h) v)
  AstSFromR v -> sfromR $ interpretAst env v

interpretAstDynamic
  :: forall ranked s. (ADReady ranked, AstSpan s)
  => AstEnv ranked
  -> AstDynamic s -> DynamicTensor ranked
{-# INLINE interpretAstDynamic #-}
interpretAstDynamic !env = \case
  DynamicRanked (AstRanked w) ->
    DynamicRanked $ interpretAstRuntimeSpecialized env w
  DynamicShaped (AstShaped w) ->
    DynamicShaped $ interpretAstSRuntimeSpecialized env w
  DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
  DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2

interpretAstHVector
  :: forall ranked s. (ADReady ranked, AstSpan s)
  => AstEnv ranked -> AstHVector s -> HVectorOf ranked
interpretAstHVector !env = \case
  AstMkHVector l -> dmkHVector $ interpretAstDynamic env <$> l
  AstHApply t ll ->
    let t2 = interpretAstHFun env t
          -- this is a bunch of PrimalSpan terms interpreted in, perhaps,
          -- FullSpan terms
        ll2 = (interpretAstDynamic env <$>) <$> ll
          -- these are, perhaps, FullSpan terms, interpreted in the same
          -- as above so that the mixture becomes compatible; if the spans
          -- agreed, the AstHApply would likely be simplified before
          -- getting interpreted
    in dHApply t2 ll2
  AstLetHVectorInHVector vars l v ->
    let lt = interpretAstHVector env l
        env2 lw = assert (voidHVectorMatches (voidFromVars vars) lw
                          `blame` ( shapeVoidHVector (voidFromVars vars)
                                  , V.toList $ V.map shapeDynamic lw
                                  , shapeVoidHVector (shapeAstHVector l)
                                  , shapeVoidHVector (dshape lt) )) $
                  extendEnvHVector vars lw env
    in dletHVectorInHVector lt (\lw -> interpretAstHVector (env2 lw) v)
  AstLetHFunInHVector var f v ->
    let g = interpretAstHFun env f
        env2 h = extendEnvHFun var h env
    in dletHFunInHVector g (\h -> interpretAstHVector (env2 h) v)
  AstLetInHVector var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstRuntimeSpecialized env u
        env2 w = extendEnv var w env
    in rletInHVector t (\w -> interpretAstHVector (env2 w) v)
  AstLetInHVectorS var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstSRuntimeSpecialized env u
        env2 w = extendEnv var w env
    in sletInHVector t (\w -> interpretAstHVector (env2 w) v)
  AstShareHVector{} -> error "interpretAstHVector: AstShareHVector"
  AstBuildHVector1 k (var, v) ->
    dbuild1 k (interpretLambdaIHVector interpretAstHVector env (var, v))
  AstMapAccumRDer k accShs bShs eShs f0 df0 rf0 acc0 es ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAstHVector env acc0
        es2 = interpretAstHVector env es
    in dmapAccumRDer (Proxy @ranked) k accShs bShs eShs f df rf acc02 es2
  AstMapAccumLDer k accShs bShs eShs f0 df0 rf0 acc0 es ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAstHVector env acc0
        es2 = interpretAstHVector env es
    in dmapAccumLDer (Proxy @ranked) k accShs bShs eShs f df rf acc02 es2

interpretAstHFun
  :: forall ranked. HVectorTensor ranked (ShapedOf ranked)
  => AstEnv ranked -> AstHFun -> HFunOf ranked
interpretAstHFun !env = \case
  AstLambda ~(vvars, l) ->
    dlambda @ranked (map voidFromVars vvars)
    $ interpretLambdaHsH interpretAstHVector (vvars, l)
      -- interpretation in empty environment; makes sense here, because
      -- there are no free variables outside of those listed
  AstVarHFun _shss _shs varId -> case DMap.lookup (mkAstVarName @_ @(TKR Float 0) varId) env of
    Just (AstEnvElemHFun f) -> f
    _ -> error $ "interpretAstHFun: unknown variable " ++ show varId

interpretAstBool :: ADReady ranked
                 => AstEnv ranked -> AstBool -> BoolOf ranked
interpretAstBool !env = \case
  AstBoolNot arg -> notB $ interpretAstBool env arg
  AstB2 opCodeBool arg1 arg2 ->
    let b1 = interpretAstBool env arg1
        b2 = interpretAstBool env arg2
    in interpretAstB2 opCodeBool b1 b2
  AstBoolConst a -> if a then true else false
  AstRel opCodeRel arg1 arg2 ->
    let r1 = interpretAstPrimalRuntimeSpecialized env arg1
        r2 = interpretAstPrimalRuntimeSpecialized env arg2
    in interpretAstRelOp opCodeRel r1 r2
  AstRelS opCodeRel arg1 arg2 ->
    let r1 = interpretAstPrimalSRuntimeSpecialized env arg1
        r2 = interpretAstPrimalSRuntimeSpecialized env arg2
    in interpretAstRelOp opCodeRel r1 r2
