{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
-- | Interpretation of AST terms in an aribtrary @RankedTensor@
-- and/or @ShapedTensor@ class instance.
module HordeAd.Core.AstInterpret
  ( interpretAstPrimal, interpretAst
  , interpretAstPrimalS, interpretAstS
  -- * Exported only to specialize elsewhere (because transitive specialization may not work, possibly)
  , interpretAstPrimalRuntimeSpecialized, interpretAstPrimalSRuntimeSpecialized
  , interpretAstDual, interpretAstDualS
  , interpretAstRuntimeSpecialized, interpretAstSRuntimeSpecialized
  , interpretAstDomains, interpretAstBool
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import qualified Data.EnumMap.Strict as EM
import           Data.Int (Int64)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, Nat, sameNat)
import           Type.Reflection (Typeable, typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (matchingRank, sameShape)
import HordeAd.Util.ShapedList (ShapedList (..))
import HordeAd.Util.SizedIndex

interpretAstPrimalRuntimeSpecialized
  :: forall ranked shaped n r.
     (KnownNat n, ADReadyBoth ranked shaped, Typeable r)
  => AstEnv ranked shaped
  -> AstRanked PrimalSpan r n -> PrimalOf ranked r n
interpretAstPrimalRuntimeSpecialized !env t =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable and RowSum instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
  -- TODO: once we drop GHC <= 9.4, use TypeRepOf to pattern match
  -- instead of nesting conditionals
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAstPrimal @ranked @shaped @n @Double env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAstPrimal @ranked @shaped @n @Float env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAstPrimal @ranked @shaped @n @Int64 env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAstPrimal @ranked @shaped @n @CInt env t
          _ -> error "an unexpected underlying scalar type"  -- catch absurd

-- Strict environment and strict ADVal and Delta make this is hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall ranked shaped n r.
     (KnownNat n, ADReadyBoth ranked shaped, GoodScalar r)
  => AstEnv ranked shaped
  -> AstRanked PrimalSpan r n -> PrimalOf ranked r n
interpretAstPrimal !env v1 = case v1 of
  AstPrimalPart (AstD u _) -> interpretAstPrimal env u
  AstPrimalPart (AstConstant u) -> interpretAstPrimal env u
  AstPrimalPart t -> rprimalPart $ interpretAst env t
  AstCond b a1 a2 ->  -- this avoids multiple ifF expansions via ifB(ADVal)
    let b1 = interpretAstBool env b
        t2 = interpretAstPrimal env a1
        t3 = interpretAstPrimal env a2
    in ifF b1 t2 t3  -- this is ifF from PrimalOf ranked
  _ -> rprimalPart $ interpretAst env v1

interpretAstDual
  :: forall ranked shaped n r.
     (KnownNat n, ADReadyBoth ranked shaped, GoodScalar r)
  => AstEnv ranked shaped
  -> AstRanked DualSpan r n -> DualOf ranked r n
interpretAstDual !env v1 = case v1 of
  AstDualPart (AstD _ u') -> interpretAstDual env u'
  AstDualPart t -> rdualPart $ interpretAst env t
  _ -> rdualPart $ interpretAst env v1

interpretAstRuntimeSpecialized
  :: forall ranked shaped n s r.
     (KnownNat n, ADReadyBoth ranked shaped, Typeable r, AstSpan s)
  => AstEnv ranked shaped
  -> AstRanked s r n -> ranked r n
interpretAstRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAst @ranked @shaped @n @s @Double env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAst @ranked @shaped @n @s @Float env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAst @ranked @shaped @n @s @Int64 env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAst @ranked @shaped @n @s @CInt env t
          _ -> error "an unexpected underlying scalar type"

interpretAst
  :: forall ranked shaped n s r.
     (KnownNat n, ADReadyBoth ranked shaped, GoodScalar r, AstSpan s)
  => AstEnv ranked shaped
  -> AstRanked s r n -> ranked r n
interpretAst !env = \case
  AstVar sh (AstVarName varId) -> case EM.lookup varId env of
    Just (AstEnvElemR @n2 @r2 t) -> case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> assert (rshape t == sh
                             `blame` (sh, rshape t, varId, t, env)) t
        _ -> error "interpretAst: scalar mismatch"
      _ -> error $ "interpretAst: wrong rank in environment"
                   `showFailure`
                   (valueOf @n :: Int, valueOf @n2 :: Int, varId, t, env)
    -- To impose such checks, we'd need to switch from OD tensors
    -- to existential OR/OS tensors so that we can inspect
    -- which it is and then seed Delta evaluation maps with that.
    -- Just{} -> error "interpretAst: wrong tensor type in environment"
    Just (AstEnvElemS @sh2 @r2 t) -> case shapeToList sh == Sh.shapeT @sh2 of
      True -> case matchingRank @sh2 @n of
        Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> rfromS @_ @r2 @sh2 t
          _ -> error "interpretAst: scalar mismatch"
        _ -> error "interpretAst: wrong rank"
      False -> error $ "interpretAst: wrong shape in environment"
                         `showFailure`
                         (sh, Sh.shapeT @sh2, varId, t, env)
    Nothing -> error $ "interpretAst: unknown variable " ++ show varId
                       ++ " in environment " ++ show env
  AstLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstRuntimeSpecialized env u
        env2 w = extendEnvR var w env
    in rlet t (\w -> interpretAst (env2 w) v)
  AstLetADShare{} -> error "interpretAst: AstLetADShare"
  AstCond b a1 a2 ->
    let b1 = interpretAstBool env b
        t2 = interpretAst env a1
        t3 = interpretAst env a2
    in ifF b1 t2 t3
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
    in interpretAstI2 opCode u2 v2
  AstSumOfList args ->
    let args2 = interpretAst env <$> args
    in foldr1 (+) args2  -- avoid unknown shape of @0@ in @sum@
  AstIndex AstIota (i :. ZI) ->
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
  AstSum (AstN2 TimesOp (AstTranspose tperm (AstLet vart vt
                                                    (AstReplicate tk t)))
                        (AstTranspose uperm (AstReplicate uk u))) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstN2 TimesOp (AstTranspose tperm (AstReplicate tk t))
                                (AstTranspose uperm (AstReplicate uk u)))))
  AstSum (AstN2 TimesOp (AstTranspose tperm (AstReplicate tk t))
                        (AstTranspose uperm (AstLet varu vu
                                                    (AstReplicate uk u)))) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstN2 TimesOp (AstTranspose tperm (AstReplicate tk t))
                                (AstTranspose uperm (AstReplicate uk u)))))
  AstSum (AstN2 TimesOp (AstTranspose tperm (AstLet vart vt
                                                    (AstReplicate tk t)))
                        (AstTranspose uperm (AstLet varu vu
                                                    (AstReplicate uk u)))) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstN2 TimesOp (AstTranspose tperm (AstReplicate tk t))
                                (AstTranspose uperm (AstReplicate uk u))))))
  AstSum v@(AstN2 TimesOp (AstTranspose tperm (AstReplicate _tk t))
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
  AstSum (AstN2 TimesOp t u)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstN2 TimesOp t u))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstN2 TimesOp t u))  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rdot1In t1 t2
  AstSum (AstTranspose [1, 0] t)  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        rsumIn $ interpretAst env t
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
  AstSum (AstReplicate k v) ->
    rscaleByScalar (fromIntegral k) $ interpretAst env v
  AstSum (AstLet var v t) -> interpretAst env (AstLet var v (AstSum t))
  AstSum (AstReshape sh (AstLet var v t)) ->
    interpretAst env (AstLet var v (AstSum (AstReshape sh t)))
  AstSum (AstReshape _sh t)
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
  AstFromList l ->
    let l2 = interpretAst env <$> l
    in rfromList l2
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
    $ AstConst $ OR.fromList [n] $ map fromIntegral [i .. i + n - 1]
  AstSlice i n v -> rslice i n (interpretAst env v)
  AstReverse v -> rreverse (interpretAst env v)
  AstTranspose perm v -> rtranspose perm $ interpretAst env v
  AstReshape sh v -> rreshape sh (interpretAst env v)
  -- These are only needed for tests that don't vectorize Ast.
  AstBuild1 k (var, AstSum (AstN2 TimesOp t (AstIndex
                                               u (AstIntVar var2 :. ZI))))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstN2 TimesOp t (AstIndex
                                                 u (AstIntVar var2 :. ZI)))))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, k == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 0 (_, v) -> rfromList0N (0 :$ shapeAst v) []
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
  AstGather sh AstIota (vars, i :. ZI) ->
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
  AstLetDomainsIn vars l v ->
    let lt0 = V.fromList $ map odFromVar vars
        lt = interpretAstDomains env l
        -- We don't need to manually pick a specialization for the existential
        -- variable r2, because the operations do not depend on r2.
        f :: (AstDynamicVarName, DynamicTensor ranked)
          -> AstEnv ranked shaped -> AstEnv ranked shaped
        f vd@(AstDynamicVarName @ty @r2 @sh2 varId, d) = case d of
          DynamicRanked @r3 @n3 u
            | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
            , Just Refl <- matchingRank @sh2 @n3
            , Just Refl <- testEquality (typeRep @r2) (typeRep @r3) ->
              extendEnvR (AstVarName varId) u
          DynamicShaped @r3 @sh3 u
            | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
            , Just Refl <- sameShape @sh3 @sh2
            , Just Refl <- testEquality (typeRep @r2) (typeRep @r3) ->
              extendEnvS (AstVarName varId) u
          DynamicRankedDummy @r3 @sh3 _ _
            | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
            , Just Refl <- sameShape @sh3 @sh2
            , Just Refl <- testEquality (typeRep @r2) (typeRep @r3) ->
              withListShape (Sh.shapeT @sh2) $ \sh4 ->
              extendEnvR @ranked @shaped @r2 (AstVarName varId) $ rzero sh4
          DynamicShapedDummy @r3 @sh3 _ _
            | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
            , Just Refl <- sameShape @sh3 @sh2
            , Just Refl <- testEquality (typeRep @r2) (typeRep @r3) ->
              extendEnvS @ranked @shaped @r2 @sh2 (AstVarName varId) 0
          _ -> error $ "interpretAst: impossible type"
                       `showFailure`
                       ( vd, typeRep @ty, typeRep @r2, Sh.shapeT @sh2
                       , scalarDynamic d, shapeDynamic d )
        env2 lw = foldr f env (zip vars (V.toList lw))
    in rletDomainsIn lt0 lt (\lw -> interpretAst (env2 lw) v)
  AstSToR v -> rfromS $ interpretAstS env v
  AstConstant a -> rconstant $ interpretAstPrimal env a
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
  AstD u u' ->
    let t1 = interpretAstPrimal env u
        t2 = interpretAstDual env u'
    in rD t1 t2
  AstFwd (vars, ast) parameters ds ->
    let g :: forall f. ADReady f => Domains f -> f r n
        g = interpretLambdaDomains interpretAst EM.empty (vars, ast)
          -- interpretation in empty environment makes sense only
          -- if there are no free variables outside of those listed
        parameters0 = V.fromList $ map odFromVar vars
        pars = interpretAstDynamic @ranked env <$> parameters
        d = interpretAstDynamic @ranked env <$> ds
    in rfwd @ranked g parameters0 pars d
  AstFold @_ @rm @_ @m f x0 as ->
    let g :: forall f. ADReady f => f r n -> f rm m -> f r n
        g = interpretLambda2 interpretAst EM.empty f
          -- Interpretation in empty environment --- makes sense only
          -- if there are no free variables outside of those listed.
          -- Note that @f@ is in @PrimalSpan@, but this does not affect
          -- the interpretation, only what term can be built.
        x0i = interpretAst @ranked env x0
        asi = interpretAst @ranked env as
    in rfold @ranked g x0i asi
  AstFoldDer @_ @rm @_ @m f0 df0 rf0 x0 as ->
    let f :: forall f. ADReady f => f r n -> f rm m -> f r n
        f = interpretLambda2 interpretAst EM.empty f0
        df :: forall f. ADReady f
           => f r n -> f rm m -> f r n -> f rm m -> f r n
        df = interpretLambda4 interpretAst EM.empty df0
        rf :: forall f. ADReady f
           => f r n -> f r n -> f rm m -> DomainsOf f
        rf = interpretLambda3 interpretAstDomains EM.empty rf0
        x0i = interpretAst @ranked env x0
        asi = interpretAst @ranked env as
    in rfoldDer @ranked f df rf x0i asi
  AstFoldZip @_ @n1 f@(_, vars, _) x0 as ->
    let g :: forall f. ADReady f => f r n1 -> DomainsOf f -> f r n1
        g = interpretLambda2D interpretAst EM.empty f
          -- TODO: interpretLambda2D, and others, breaks sharing!
        od = V.fromList $ map odFromVar vars
        x0i = interpretAst env x0
        asi = interpretAstDynamic env <$> as
    in rfoldZip g od x0i asi
  AstFoldZipDer @_ @n1 f0@(_, vars, _) df0 rf0 x0 as ->
    let f :: forall f. ADReady f => f r n1 -> DomainsOf f -> f r n1
        f = interpretLambda2D interpretAst EM.empty f0
        df :: forall f. ADReady f
           => f r n1 -> DomainsOf f -> f r n1 -> DomainsOf f -> f r n1
        df = interpretLambda4D interpretAst EM.empty df0
        rf :: forall f. ADReady f
           => f r n1 -> f r n1 -> DomainsOf f -> DomainsOf f
        rf = interpretLambda3D interpretAstDomains EM.empty rf0
        od = V.fromList $ map odFromVar vars
        x0i = interpretAst env x0
        asi = interpretAstDynamic env <$> as
    in rfoldZipDer f df rf od x0i asi
  AstScan @_ @rm @n1 @m f x0 as ->
    let g :: forall f. ADReady f => f r n1 -> f rm m -> f r n1
        g = interpretLambda2 interpretAst EM.empty f
        x0i = interpretAst env x0
        asi = interpretAst env as
    in rscan g x0i asi
  AstScanDer @_ @rm @n1 @m f0 df0 rf0 x0 as ->
    let f :: forall f. ADReady f => f r n1 -> f rm m -> f r n1
        f = interpretLambda2 interpretAst EM.empty f0
        df :: forall f. ADReady f
           => f r n1 -> f rm m -> f r n1 -> f rm m -> f r n1
        df = interpretLambda4 interpretAst EM.empty df0
        rf :: forall f. ADReady f
           => f r n1 -> f r n1 -> f rm m -> DomainsOf f
        rf = interpretLambda3 interpretAstDomains EM.empty rf0
        x0i = interpretAst env x0
        asi = interpretAst env as
    in rscanDer f df rf x0i asi
  AstScanZip @_ @n1 f@(_, vars, _) x0 as ->
    let g :: forall f. ADReady f => f r n1 -> DomainsOf f -> f r n1
        g = interpretLambda2D interpretAst EM.empty f
          -- TODO: interpretLambda2D, and others, breaks sharing!
        od = V.fromList $ map odFromVar vars
        x0i = interpretAst env x0
        asi = interpretAstDynamic env <$> as
    in rscanZip g od x0i asi
  AstScanZipDer @_ @n1 f0@(_, vars, _) df0 rf0 x0 as ->
    let f :: forall f. ADReady f => f r n1 -> DomainsOf f -> f r n1
        f = interpretLambda2D interpretAst EM.empty f0
        df :: forall f. ADReady f
           => f r n1 -> DomainsOf f -> f r n1 -> DomainsOf f -> f r n1
        df = interpretLambda4D interpretAst EM.empty df0
        rf :: forall f. ADReady f
           => f r n1 -> f r n1 -> DomainsOf f -> DomainsOf f
        rf = interpretLambda3D interpretAstDomains EM.empty rf0
        od = V.fromList $ map odFromVar vars
        x0i = interpretAst env x0
        asi = interpretAstDynamic env <$> as
    in rscanZipDer f df rf od x0i asi

interpretAstDynamic
  :: forall ranked shaped s. (ADReadyBoth ranked shaped, AstSpan s)
  => AstEnv ranked shaped
  -> AstDynamic s -> DynamicTensor ranked
{-# INLINE interpretAstDynamic #-}
interpretAstDynamic !env = \case
  DynamicRanked w ->
    DynamicRanked $ interpretAstRuntimeSpecialized env w
  DynamicShaped w ->
    DynamicShaped $ interpretAstSRuntimeSpecialized env w
  DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
  DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2

interpretAstDomains
  :: forall ranked shaped s. (ADReadyBoth ranked shaped, AstSpan s)
  => AstEnv ranked shaped -> AstDomains s -> DomainsOf ranked
interpretAstDomains !env = \case
  AstDomains l ->
    dmkDomains @ranked @shaped $ interpretAstDynamic @ranked env <$> l
  AstLetInDomains var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstRuntimeSpecialized env u
        env2 w = extendEnvR var w env
    in rletInDomains t (\w -> interpretAstDomains (env2 w) v)
  AstLetInDomainsS var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstSRuntimeSpecialized env u
        env2 w = extendEnvS var w env
    in sletInDomains t (\w -> interpretAstDomains (env2 w) v)
  AstRev @r @n (vars, ast) parameters ->
    let g :: forall f. ADReady f => Domains f -> f r n
        g = interpretLambdaDomains interpretAst EM.empty (vars, ast)
          -- interpretation in empty environment; makes sense only
          -- if there are no free variables outside of those listed;
          -- the same below
        parameters0 = V.fromList $ map odFromVar vars
        pars = interpretAstDynamic @ranked env <$> parameters
    in rrev @ranked g parameters0 pars
  AstRevDt @r @n (vars, ast) parameters dt ->
    let g :: forall f. ADReady f => Domains f -> f r n
        g = interpretLambdaDomains interpretAst EM.empty (vars, ast)
        parameters0 = V.fromList $ map odFromVar vars
        pars = interpretAstDynamic @ranked env <$> parameters
        d = interpretAst env dt
    in rrevDt @ranked g parameters0 pars d
  AstRevS @r @sh (vars, ast) parameters ->
    let g :: forall f. ADReadyS f => Domains (RankedOf f) -> f r sh
        g = interpretLambdaDomainsS interpretAstS EM.empty (vars, ast)
        parameters0 = V.fromList $ map odFromVar vars
        pars = interpretAstDynamic @ranked env <$> parameters
    in srev @ranked g parameters0 pars
  AstRevDtS @r @sh (vars, ast) parameters dt ->
    let g :: forall f. ADReadyS f => Domains (RankedOf f) -> f r sh
        g = interpretLambdaDomainsS interpretAstS EM.empty (vars, ast)
        parameters0 = V.fromList $ map odFromVar vars
        pars = interpretAstDynamic @ranked env <$> parameters
        d = interpretAstS env dt
    in srevDt @ranked g parameters0 pars d

interpretAstBool :: ADReadyBoth ranked shaped
                 => AstEnv ranked shaped -> AstBool -> BoolOf ranked
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

interpretAstPrimalSRuntimeSpecialized
  :: forall ranked shaped sh r.
     (Sh.Shape sh, ADReadyBoth ranked shaped, Typeable r)
  => AstEnv ranked shaped
  -> AstShaped PrimalSpan r sh -> PrimalOf shaped r sh
interpretAstPrimalSRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAstPrimalS @ranked @shaped @sh @Double env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAstPrimalS @ranked @shaped @sh @Float env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAstPrimalS @ranked @shaped @sh @Int64 env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAstPrimalS @ranked @shaped @sh @CInt env t
          _ -> error "an unexpected underlying scalar type"

interpretAstPrimalS
  :: forall ranked shaped sh r.
     (Sh.Shape sh, ADReadyBoth ranked shaped, GoodScalar r)
  => AstEnv ranked shaped
  -> AstShaped PrimalSpan r sh -> PrimalOf shaped r sh
interpretAstPrimalS !env v1 = case v1 of
  AstPrimalPartS (AstDS u _) -> interpretAstPrimalS env u
  AstPrimalPartS (AstConstantS u) -> interpretAstPrimalS env u
  AstPrimalPartS t -> sprimalPart $ interpretAstS env t
  AstCondS b a1 a2 ->  -- this avoids multiple ifF expansions via ifB(ADVal)
    let b1 = interpretAstBool env b
        t2 = interpretAstPrimalS env a1
        t3 = interpretAstPrimalS env a2
    in ifF b1 t2 t3  -- this is ifF from PrimalOf ranked
  _ -> sprimalPart $ interpretAstS env v1

interpretAstDualS
  :: forall ranked shaped sh r.
     (Sh.Shape sh, ADReadyBoth ranked shaped, GoodScalar r)
  => AstEnv ranked shaped
  -> AstShaped DualSpan r sh -> DualOf shaped r sh
interpretAstDualS !env v1 = case v1 of
  AstDualPartS (AstDS _ u') -> interpretAstDualS env u'
  AstDualPartS t -> sdualPart $ interpretAstS env t
  _ -> sdualPart $ interpretAstS env v1

interpretAstSRuntimeSpecialized
  :: forall ranked shaped sh s r.
     (Sh.Shape sh, ADReadyBoth ranked shaped, Typeable r, AstSpan s)
  => AstEnv ranked shaped
  -> AstShaped s r sh -> shaped r sh
interpretAstSRuntimeSpecialized !env t =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> interpretAstS @ranked @shaped @sh @s @Double env t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> interpretAstS @ranked @shaped @sh @s @Float env t
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> interpretAstS @ranked @shaped @sh @s @Int64 env t
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> interpretAstS @ranked @shaped @sh @s @CInt env t
          _ -> error "an unexpected underlying scalar type"

interpretAstS
  :: forall ranked shaped sh s r.
     (Sh.Shape sh, ADReadyBoth ranked shaped, GoodScalar r, AstSpan s)
  => AstEnv ranked shaped
  -> AstShaped s r sh -> shaped r sh
interpretAstS !env = \case
  AstVarS (AstVarName varId) -> case EM.lookup varId env of
    Just (AstEnvElemS @sh2 @r2 t) -> case sameShape @sh2 @sh of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> t
        _ -> error "interpretAstS: scalar mismatch"
      Nothing -> error $ "interpretAstS: wrong shape in environment"
                         `showFailure`
                         (Sh.shapeT @sh, Sh.shapeT @sh2, varId, t, env)
    -- To impose such checks, we'd need to switch from OD tensors
    -- to existential OR/OS tensors so that we can inspect
    -- which it is and then seed Delta evaluation maps with that.
    -- Just{} -> error "interpretAstS: wrong tensor type in environment"
    Just (AstEnvElemR @n2 @r2 t) -> case matchingRank @sh @n2 of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> assert (Sh.shapeT @sh == shapeToList (rshape t)
                             `blame` (Sh.shapeT @sh, rshape t, varId, t, env))
                     $ sfromR @_ @r2 @sh t
        _ -> error "interpretAstS: scalar mismatch"
      _ -> error "interpretAstS: wrong shape in environment"
    Nothing -> error $ "interpretAstS: unknown variable " ++ show varId
  AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstSRuntimeSpecialized env u
        env2 w = extendEnvS var w env
    in slet t (\w -> interpretAstS (env2 w) v)
  AstLetADShareS{} -> error "interpretAstS: AstLetADShare"
  AstCondS b a1 a2 ->
    let b1 = interpretAstBool env b
        t2 = interpretAstS env a1
        t3 = interpretAstS env a2
    in ifF b1 t2 t3
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
    let u2 = interpretAstS env u
    in interpretAstN1 opCode u2
  AstN2S opCode u v ->
    let u2 = interpretAstS env u
        v2 = interpretAstS env v
    in interpretAstN2 opCode u2 v2
  AstR1S opCode u ->
    let u2 = interpretAstS env u
    in interpretAstR1 opCode u2
  AstR2S opCode u v ->
    let u2 = interpretAstS env u
        v2 = interpretAstS env v
    in interpretAstR2 opCode u2 v2
  AstI2S opCode u v ->
    let u2 = interpretAstS env u
        v2 = interpretAstS env v
    in interpretAstI2 opCode u2 v2
  AstSumOfListS args ->
    let args2 = interpretAstS env <$> args
    in sum args2
  AstIndexS AstIotaS (i :$: ZSH) ->
    sfromIntegral . sconstant . sfromR $ interpretAstPrimal env i
  AstIndexS @sh1 v ix ->
    let v2 = interpretAstS env v
        ix3 = interpretAstPrimal env <$> ix
    in sindex @shaped @r @sh1 v2 ix3
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
  AstSum (AstN2 TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstReplicate uk u) ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstN2 TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstN2 TimesOp [ AstTranspose tperm (AstReplicate tk t)
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstN2 TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstN2 TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstN2 TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ]))))
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
  AstSum (AstTranspose [1, 0] t)  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        rsumIn $ interpretAst env t
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
  AstSum (AstReplicate k v) ->
    rscaleByScalar (fromIntegral k) $ interpretAst env v
  AstSum (AstLet var v t) -> interpretAst env (AstLet var v (AstSum t))
  AstSum (AstReshape sh (AstLet var v t)) ->
    interpretAst env (AstLet var v (AstSum (AstReshape sh t)))
  AstSum (AstReshape _sh t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        rsum0 $ interpretAst env t
-}
  AstSumS v -> ssum $ interpretAstS env v
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstScatterS v (vars, ix) ->
    let t1 = interpretAstS env v
        f2 = interpretLambdaIndexToIndexS interpretAstPrimal env (vars, ix)
    in sscatter t1 f2
  AstFromListS l ->
    let l2 = interpretAstS env <$> l
    in sfromList l2
  AstFromVectorS l ->
    let l2 = V.map (interpretAstS env) l
    in sfromVector l2
{- TODO:
  AstReshape sh (AstReplicate @m _ s)
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env s
        in rreplicate0N sh t1
  AstReshape sh (AstLet var v (AstReplicate k t)) ->
    interpretAst env (AstLet var v (AstReshape sh (AstReplicate k t)))
-}
  AstReplicateS v -> sreplicate (interpretAstS env v)
  AstAppendS x y ->
    let t1 = interpretAstS env x
        t2 = interpretAstS env y
    in sappend t1 t2
  AstSliceS @i @n AstIotaS ->
    let i = valueOf @i
        n = valueOf @n
    in interpretAstS env
       $ AstConstS $ OS.fromList $ map fromIntegral [i :: Int .. i + n - 1]
  AstSliceS @i v -> sslice (Proxy @i) Proxy (interpretAstS env v)
  AstReverseS v -> sreverse (interpretAstS env v)
  AstTransposeS @perm v -> stranspose (Proxy @perm) $ interpretAstS env v
  AstReshapeS v -> sreshape (interpretAstS env v)
  -- These are only needed for tests that don't vectorize Ast.
{- TODO:
  AstBuild1 k (var, AstSum (AstN2 TimesOp [t, AstIndex
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstN2 TimesOp [t, AstIndex
                                                  u (AstIntVar var2 :. ZI)])))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, k == lengthAst u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in rmatvecmul t2 t1
  AstBuild1 0 (_, v) -> rfromList0N (0 :$ rshape v) []
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
    sbuild1 (interpretLambdaIS interpretAstS env (var, v))
      -- to be used only in tests
  AstGatherS @sh2 AstIotaS (vars, i :$: ZSH) ->
    gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh)
    $ gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: sh2 :~: sh)
        -- transitivity of type equality doesn't work, by design,
        -- so this direct cast is needed instead of more basic laws
    $ sbuild @shaped @r @(Sh.Rank sh)
             (interpretLambdaIndexS
                interpretAstS env
                (vars, fromPrimalS @s $ AstFromIntegralS $ AstRToS i))
  AstGatherS v (vars, ix) ->
    let t1 = interpretAstS env v
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
  AstLetDomainsInS vars l v ->
    let lt0 = V.fromList $ map odFromVar vars
        lt = interpretAstDomains env l
        -- We don't need to manually pick a specialization for the existential
        -- variable r2, because the operations do not depend on r2.
        f :: (AstDynamicVarName, DynamicTensor ranked)
          -> AstEnv ranked shaped -> AstEnv ranked shaped
        f vd@(AstDynamicVarName @ty @r2 @sh2 varId, d) = case d of
          DynamicRanked @r3 @n3 u
            | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
            , Just Refl <- matchingRank @sh2 @n3
            , Just Refl <- testEquality (typeRep @r2) (typeRep @r3) ->
              extendEnvR (AstVarName varId) u
          DynamicShaped @r3 @sh3 u
            | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
            , Just Refl <- sameShape @sh3 @sh2
            , Just Refl <- testEquality (typeRep @r2) (typeRep @r3) ->
              extendEnvS (AstVarName varId) u
          DynamicRankedDummy @r3 @sh3 _ _
            | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
            , Just Refl <- sameShape @sh3 @sh2
            , Just Refl <- testEquality (typeRep @r2) (typeRep @r3) ->
              withListShape (Sh.shapeT @sh2) $ \sh4 ->
              extendEnvR @ranked @shaped @r2 (AstVarName varId) $ rzero sh4
          DynamicShapedDummy @r3 @sh3 _ _
            | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
            , Just Refl <- sameShape @sh3 @sh2
            , Just Refl <- testEquality (typeRep @r2) (typeRep @r3) ->
              extendEnvS @ranked @shaped @r2 @sh2 (AstVarName varId) 0
          _ -> error $ "interpretAstS: impossible type"
                       `showFailure`
                       ( vd, typeRep @ty, typeRep @r2, Sh.shapeT @sh2
                       , scalarDynamic d, shapeDynamic d )
        env2 lw = foldr f env (zip vars (V.toList lw))
    in sletDomainsIn lt0 lt (\lw -> interpretAstS (env2 lw) v)
  AstRToS v -> sfromR $ interpretAst env v
  AstConstantS a -> sconstant $ interpretAstPrimalS env a
  AstPrimalPartS a -> interpretAstS env a
  AstDualPartS a -> interpretAstS env a
  AstDS u u' ->
    let t1 = interpretAstPrimalS env u
        t2 = interpretAstDualS env u'
    in sD t1 t2
  AstFwdS (vars, ast) parameters ds ->
    let g :: forall f. ADReadyS f => Domains (RankedOf f) -> f r sh
        g = interpretLambdaDomainsS interpretAstS EM.empty (vars, ast)
          -- interpretation in empty environment makes sense only
          -- if there are no free variables outside of those listed
        parameters0 = V.fromList $ map odFromVar vars
        pars = interpretAstDynamic @ranked env <$> parameters
        d = interpretAstDynamic @ranked env <$> ds
    in sfwd @ranked g parameters0 pars d
  AstFoldS @_ @rm @_ @shm f x0 as ->
    let g :: forall f. ADReadyS f => f r sh -> f rm shm -> f r sh
        g = interpretLambda2S interpretAstS EM.empty f
          -- Interpretation in empty environment --- makes sense only
          -- if there are no free variables outside of those listed.
          -- Note that @f@ is in @PrimalSpan@, but this does not affect
          -- the interpretation, only what term can be built.
        x0i = interpretAstS @ranked env x0
        asi = interpretAstS @ranked env as
    in sfold @ranked g x0i asi
  AstFoldDerS @_ @rm @_ @shm f0 df0 rf0 x0 as ->
    let f :: forall f. ADReadyS f => f r sh -> f rm shm -> f r sh
        f = interpretLambda2S interpretAstS EM.empty f0
        df :: forall f. ADReadyS f
           => f r sh -> f rm shm -> f r sh -> f rm shm -> f r sh
        df = interpretLambda4S interpretAstS EM.empty df0
        rf :: forall f. ADReadyS f
           => f r sh -> f r sh -> f rm shm -> DomainsOf (RankedOf f)
        rf = interpretLambda3S interpretAstDomains EM.empty rf0
        x0i = interpretAstS @ranked env x0
        asi = interpretAstS @ranked env as
    in sfoldDer @ranked f df rf x0i asi
  AstFoldZipS @_ @n1 f@(_, vars, _) x0 as ->
    let g :: forall f. ADReadyS f => f r n1 -> DomainsOf (RankedOf f) -> f r n1
        g = interpretLambda2DS interpretAstS EM.empty f
          -- TODO: interpretLambda2DS, and others, breaks sharing!
        od = V.fromList $ map odFromVar vars
        x0i = interpretAstS env x0
        asi = interpretAstDynamic env <$> as
    in sfoldZip g od x0i asi
  AstFoldZipDerS @_ @n1 f0@(_, vars, _) df0 rf0 x0 as ->
    let f :: forall f. ADReadyS f => f r n1 -> DomainsOf (RankedOf f) -> f r n1
        f = interpretLambda2DS interpretAstS EM.empty f0
        df :: forall f. ADReadyS f
           => f r n1 -> DomainsOf (RankedOf f) -> f r n1
           -> DomainsOf (RankedOf f)
           -> f r n1
        df = interpretLambda4DS interpretAstS EM.empty df0
        rf :: forall f. ADReadyS f
           => f r n1 -> f r n1 -> DomainsOf (RankedOf f)
           -> DomainsOf (RankedOf f)
        rf = interpretLambda3DS interpretAstDomains EM.empty rf0
        od = V.fromList $ map odFromVar vars
        x0i = interpretAstS env x0
        asi = interpretAstDynamic env <$> as
    in sfoldZipDer f df rf od x0i asi
  AstScanS @_ @rm @n1 @m f x0 as ->
    let g :: forall f. ADReadyS f => f r n1 -> f rm m -> f r n1
        g = interpretLambda2S interpretAstS EM.empty f
        x0i = interpretAstS env x0
        asi = interpretAstS env as
    in sscan g x0i asi
  AstScanDerS @_ @rm @n1 @m f0 df0 rf0 x0 as ->
    let f :: forall f. ADReadyS f => f r n1 -> f rm m -> f r n1
        f = interpretLambda2S interpretAstS EM.empty f0
        df :: forall f. ADReadyS f
           => f r n1 -> f rm m -> f r n1 -> f rm m -> f r n1
        df = interpretLambda4S interpretAstS EM.empty df0
        rf :: forall f. ADReadyS f
           => f r n1 -> f r n1 -> f rm m -> DomainsOf (RankedOf f)
        rf = interpretLambda3S interpretAstDomains EM.empty rf0
        x0i = interpretAstS env x0
        asi = interpretAstS env as
    in sscanDer f df rf x0i asi
  AstScanZipS @_ @n1 f@(_, vars, _) x0 as ->
    let g :: forall f. ADReadyS f => f r n1 -> DomainsOf (RankedOf f) -> f r n1
        g = interpretLambda2DS interpretAstS EM.empty f
          -- TODO: interpretLambda2DS, and others, breaks sharing!
        od = V.fromList $ map odFromVar vars
        x0i = interpretAstS env x0
        asi = interpretAstDynamic env <$> as
    in sscanZip g od x0i asi
  AstScanZipDerS @_ @n1 f0@(_, vars, _) df0 rf0 x0 as ->
    let f :: forall f. ADReadyS f => f r n1 -> DomainsOf (RankedOf f) -> f r n1
        f = interpretLambda2DS interpretAstS EM.empty f0
        df :: forall f. ADReadyS f
           => f r n1 -> DomainsOf (RankedOf f) -> f r n1
           -> DomainsOf (RankedOf f)
           -> f r n1
        df = interpretLambda4DS interpretAstS EM.empty df0
        rf :: forall f. ADReadyS f
           => f r n1 -> f r n1 -> DomainsOf (RankedOf f)
           -> DomainsOf (RankedOf f)
        rf = interpretLambda3DS interpretAstDomains EM.empty rf0
        od = V.fromList $ map odFromVar vars
        x0i = interpretAstS env x0
        asi = interpretAstDynamic env <$> as
    in sscanZipDer f df rf od x0i asi
