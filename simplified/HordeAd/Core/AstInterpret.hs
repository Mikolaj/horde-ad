{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Interpretation of @Ast@ terms in an aribtrary @Tensor@ class instance..
module HordeAd.Core.AstInterpret
  ( InterpretAst, interpretAst, interpretAstDomainsDummy
  , AstEnv, extendEnvR, extendEnvD, AstMemo, emptyMemo
  , AstEnvElem(AstVarR)  -- for a test only
  ) where

import Prelude hiding ((<*))

import           Control.Arrow (second)
import           Control.Exception.Assert.Sugar
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.EnumMap.Strict as EM
import           Data.List (foldl1', mapAccumR)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, sameNat)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.Domains
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal ()
import HordeAd.Core.TensorClass
import HordeAd.Internal.SizedList

type AstEnv a = EM.EnumMap AstVarId (AstEnvElem a)

data AstEnvElem a =
    AstVarR (DTensorOf a)
  | AstVarI (IntOf a)
deriving instance (Show (DTensorOf a), Show (IntOf a))
                  => Show (AstEnvElem a)

extendEnvR :: forall n a. (ConvertTensor a, KnownNat n)
           => AstVarName (OR.Array n (Value a)) -> TensorOf n a
           -> AstEnv a -> AstEnv a
extendEnvR v@(AstVarName var) d =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show v)
                   var (AstVarR $ dfromR d)

extendEnvD :: ConvertTensor a
           => (AstDynamicVarName (Value a), DTensorOf a) -> AstEnv a
           -> AstEnv a
extendEnvD (AstDynamicVarName var, d) = extendEnvR var (tfromD d)

extendEnvDId :: AstVarId -> DTensorOf a -> AstEnv a
             -> AstEnv a
extendEnvDId var d =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvDId: duplicate " ++ show var)
                   var (AstVarR d)

extendEnvI :: AstVarId -> IntOf a -> AstEnv a -> AstEnv a
extendEnvI var i =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvI: duplicate " ++ show var)
                   var (AstVarI i)

extendEnvVars :: AstVarList m -> IndexOf m a -> AstEnv a -> AstEnv a
extendEnvVars vars ix env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

-- Extensions to @memo@, one created for each iteration of the function,
-- are forgotten instead of returned, because they would differ
-- for each iteration, with differently extended environment,
-- and also because the created function is not expected to return a @memo@.
interpretLambdaI
  :: (AstEnv a -> AstMemo a -> Ast n (Value a)
  -> (AstMemo a, TensorOf n a))
  -> AstEnv a -> AstMemo a -> (AstVarId, Ast n (Value a)) -> IntOf a
  -> TensorOf n a
{-# INLINE interpretLambdaI #-}
interpretLambdaI f env memo (var, ast) =
  \i -> snd $ f (extendEnvI var i env) memo ast

interpretLambdaIndex
  :: (AstEnv a -> AstMemo a -> Ast n (Value a)
  -> (AstMemo a, TensorOf n a))
  -> AstEnv a -> AstMemo a
  -> (AstVarList m, Ast n (Value a)) -> IndexOf m a
  -> TensorOf n a
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f env memo (vars, ast) =
  \ix -> snd $ f (extendEnvVars vars ix env) memo ast

interpretLambdaIndexToIndex
  :: KnownNat p
  => (AstEnv a -> AstMemo a -> AstInt q -> (AstMemo a, IntOf a))
  -> AstEnv a -> AstMemo a -> (AstVarList m, AstIndex p q) -> IndexOf m a
  -> IndexOf p a
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f env memo (vars, asts) =
  \ix -> listToIndex $ snd
         $ mapAccumR (f (extendEnvVars vars ix env)) memo (indexToList asts)

class (BooleanOf r ~ b) => BooleanOfMatches b r where
instance (BooleanOf r ~ b) => BooleanOfMatches b r where

type InterpretAst a =
  ( Tensor a, ConvertTensor a, Tensor (Primal a)
  , ShowAstSimplify (Value a), Underlying a ~ Value a
  , EqB (IntOf a), OrdB (IntOf a), IfB (IntOf a)
  , IntOf (Primal a) ~ IntOf a, BooleanOf (Primal a) ~ BooleanOf (IntOf a)
  , CRanked EqB (Primal a)
  , CRanked OrdB (Primal a)
  , CRanked (BooleanOfMatches (BooleanOf (Primal a))) (Primal a)
  )

type AstMemo a = ()  -- unused for now, but likely to be used in the future,
                     -- though probably not for memoization

emptyMemo :: AstMemo a
emptyMemo = ()

-- Strict environment and strict ADVal and Delta make this is hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall n a. (KnownNat n, InterpretAst a)
  => AstEnv a -> AstMemo a
  -> AstPrimalPart n (Value a) -> (AstMemo a, TensorOf n (Primal a))
interpretAstPrimal env memo (AstPrimalPart v1) = case v1 of
  AstD u _-> interpretAstPrimal env memo u
  _ -> second tprimalPart $ interpretAst env memo v1

interpretAstDual
  :: forall n a. (KnownNat n, InterpretAst a)
  => AstEnv a -> AstMemo a
  -> AstDualPart n (Value a) -> (AstMemo a, DualOf n a)
interpretAstDual env memo (AstDualPart v1) = case v1 of
  AstD _ u'-> interpretAstDual env memo u'
  _ -> second tdualPart $ interpretAst env memo v1

interpretAst
  :: forall n a. (KnownNat n, InterpretAst a)
  => AstEnv a -> AstMemo a
  -> Ast n (Value a) -> (AstMemo a, TensorOf n a)
interpretAst env memo = \case
  AstVar sh var -> case EM.lookup var env of
    Just (AstVarR d) -> let t = tfromD d
                        in assert (sh == tshape t) $ (memo, t)
    Just AstVarI{} ->
      error $ "interpretAst: type mismatch for " ++ show var
    Nothing -> error $ "interpretAst: unknown variable " ++ show var
  AstLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let (memo1, t) = interpretAst env memo u
        env2 w = extendEnvR (AstVarName var) w env
    in (memo1, tlet t (\w -> snd $ interpretAst (env2 w) memo1 v))
         -- TODO: snd; env/state?
  AstLetADShare{} -> error "interpretAst: AstLetADShare"
  {- TODO: revise when we handle GPUs. For now, this is done in TensorOps
     instead and that's fine, because for one-element carriers,
     reshape and replicate are very cheap. OTOH, this was introducing
     ScalarR(UnScalar0 ...) into delta expressions by firing
     in an early phase.
  AstOp TimesOp [v, AstReshape _ (AstReplicate @m _ s)]
   -- TODO: also handle nested AstReplicate to prevent executing them
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let (memo1, t1) = interpretAst env memo v
            (memo2, t2) = interpretAst env memo1 s
        in (memo2, tscaleByScalar0 t2 t1)
  AstOp TimesOp [v, AstReplicate @m _ s]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let (memo1, t1) = interpretAst env memo v
            (memo2, t2) = interpretAst env memo1 s
        in (memo2, tscaleByScalar0 t2 t1)
  -}
  AstOp TimesOp [v, AstLet var u (AstReshape sh (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        -- The intVarInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env memo
          (AstLet var u (AstOp TimesOp [v, AstReshape sh (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env memo
          (AstLet var u (AstOp TimesOp [v, AstReshape sh (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env memo
          (AstLet var u (AstOp TimesOp [v, AstReplicate @m k s]))
  AstOp opCode args ->
    let (memo2, args2) = mapAccumR (interpretAst env) memo args
    in (memo2, interpretAstOp opCode args2)
  AstSumOfList args ->
    let (memo2, args2) = mapAccumR (interpretAst env) memo args
    in (memo2, tsumOfList args2)
  AstIota -> error "interpretAst: bare AstIota, most likely a bug"
  AstIndexZ AstIota (i :. ZI) -> second tfromIndex0 $ interpretAstInt env memo i
  AstIndexZ v ix ->
    let (memo2, v2) = interpretAst env memo v
        (memo3, ix3) = mapAccumR (interpretAstInt env) memo2 (indexToList ix)
    in (memo3, tindex v2 $ listToIndex ix3)
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstSum (AstOp TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstTranspose uperm u ]) ->
    interpretAst env memo
      (AstLet vart vt
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm t
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env memo
      (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstOp TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env memo
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ]))))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt (AstReplicate tk t))
                        , AstTranspose uperm (AstReplicate uk u) ]) ->
    interpretAst env memo
      (AstLet vart vt
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env memo
      (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt (AstReplicate tk t))
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env memo
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ]))))
  AstSum v@(AstOp TimesOp [ AstTranspose tperm (AstReplicate _tk t)
                          , AstTranspose uperm (AstReplicate _uk u) ])
    | Just Refl <- sameNat (Proxy @n) (Proxy @2) ->
        let interpretMatmul2 t1 u1 =
              let (memo1, t2) = interpretAst env memo t1
                  (memo2, u2) = interpretAst env memo1 u1
              in (memo2, tmatmul2 t2 u2)
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
            second (ttranspose [1, 0])
            $ interpretMatmul2 t u
          ([1, 2, 0], [2, 0, 1]) ->
            second (ttranspose [1, 0])
            $ interpretMatmul2 u t
--          ([2, 0, 1], [2, 1, 0]) ->
--            second (ttranspose [1, 0])
--            $ interpretMatmul2 t (AstTranspose [1, 0] u)
--          ([2, 1, 0], [2, 0, 1]) ->
--            second (ttranspose [1, 0])
--            $ interpretMatmul2 u (AstTranspose [1, 0] t)
--          ([1, 2, 0], [1, 0]) ->
--            second (ttranspose [1, 0])
--            $ interpretMatmul2 (AstTranspose [1, 0] u) t
--          ([1, 0], [2, 1, 0]) ->
--            second (ttranspose [1, 0])
--            $ interpretMatmul2 (AstTranspose [1, 0] t) (AstTranspose [1, 0] u)
--          ([2, 1, 0], [1, 0]) ->
--            second (ttranspose [1, 0])
--            $ interpretMatmul2 (AstTranspose [1, 0] u) (AstTranspose [1, 0] t)
          _ -> second tsum $ interpretAst env memo v
  AstSum (AstOp TimesOp [t, u])
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let (memo1, t1) = interpretAst env memo t
            (memo2, t2) = interpretAst env memo1 u
        in (memo2, tdot0 t1 t2)
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstOp TimesOp [t, u]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let (memo1, t1) = interpretAst env memo t
            (memo2, t2) = interpretAst env memo1 u
        in (memo2, tdot0 t1 t2)
  AstSum (AstTranspose [1, 0] (AstOp TimesOp [t, u]))  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        let (memo1, t1) = interpretAst env memo t
            (memo2, t2) = interpretAst env memo1 u
        in (memo2, tdot1In t1 t2)
  AstSum (AstTranspose [1, 0] t)  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        second tsumIn $ interpretAst env memo t
  AstSum (AstReshape sh (AstTranspose _ t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env memo (AstSum (AstReshape sh t))
  AstSum (AstReshape sh (AstReverse t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env memo (AstSum (AstReshape sh t))
  AstSum (AstReshape _sh (AstSum t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        second tsum0 $ interpretAst env memo t
  AstSum (AstSum t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        second tsum0 $ interpretAst env memo t
          -- more cases are needed so perhaps we need AstSum0
  AstSum (AstReplicate k v) ->
    second (tscaleByScalar (fromIntegral k)) $ interpretAst env memo v
  AstSum (AstLet var v t) -> interpretAst env memo (AstLet var v (AstSum t))
  AstSum (AstReshape sh (AstLet var v t)) ->
    interpretAst env memo (AstLet var v (AstSum (AstReshape sh t)))
  AstSum (AstReshape _sh t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        second tsum0 $ interpretAst env memo t
  AstSum v -> second tsum $ interpretAst env memo v
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstScatter sh v (vars, ix) ->
    let (memo1, t1) = interpretAst env memo v
        f2 = interpretLambdaIndexToIndex interpretAstInt env memo (vars, ix)
    in (memo1, tscatter sh t1 f2)
  AstFromList l ->
    let (memo2, l2) = mapAccumR (interpretAst env) memo l
    in (memo2, tfromList l2)
  AstFromVector l ->
    let (memo2, l2) = mapAccumR (interpretAst env) memo (V.toList l)
    in (memo2, tfromVector $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  AstReshape sh (AstReplicate @m _ s)
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let (memo1, t1) = interpretAst env memo s
        in (memo1, treplicate0N sh t1)
  AstReshape sh (AstLet var v (AstReplicate k t)) ->
    interpretAst env memo (AstLet var v (AstReshape sh (AstReplicate k t)))
  AstReplicate k v -> second (treplicate k) (interpretAst env memo v)
  AstAppend x y ->
    let (memo1, t1) = interpretAst env memo x
        (memo2, t2) = interpretAst env memo1 y
    in (memo2, tappend t1 t2)
  AstSlice i k AstIota ->
    interpretAst env memo
    $ AstConst $ OR.fromList [k] $ map fromIntegral [i .. i + k - 1]
  AstSlice i k v -> second (tslice i k) (interpretAst env memo v)
  AstReverse v -> second treverse (interpretAst env memo v)
  AstTranspose perm v -> second (ttranspose perm) $ interpretAst env memo v
  AstReshape sh v -> second (treshape sh) (interpretAst env memo v)
  -- These two are only needed for tests that don't vectorize Ast.
  AstBuild1 k (var, AstSum (AstOp TimesOp [t, AstIndexZ
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let (memo1, t1) = interpretAst env memo t
            (memo2, t2) = interpretAst env memo1 u
        in (memo2, tmatvecmul t2 t1)
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstOp TimesOp [t, AstIndexZ
                                                  u (AstIntVar var2 :. ZI)])))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, k == tlength u ->
        let (memo1, t1) = interpretAst env memo t
            (memo2, t2) = interpretAst env memo1 u
        in (memo2, tmatvecmul t2 t1)
  AstBuild1 0 (_, v) -> (memo, tfromList0N (0 :$ tshape v) [])
  -- The following can't be, in general, so partially evaluated, because v
  -- may contain variables that the evironment sends to terms,
  -- not to concrete numbers (and so Primal a is not equal to Value a).
  -- However, this matters only for POPL AD, not JAX AD and also it matters
  -- only with no vectorization of, at least, constant (primal-only) terms.
  -- AstBuild1 k (var, AstConstant v) ->
  --   tconst
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env memo (var, v)
  AstBuild1 k (var, v) ->
    (memo, tbuild1 k (interpretLambdaI interpretAst env memo (var, v)))
      -- to be used only in tests
  AstGatherZ sh AstIota (vars, (i :. ZI)) ->
    ( memo
    , tbuild sh (interpretLambdaIndex interpretAst env memo
                                      (vars, tfromIndex0 i)) )
  AstGatherZ sh v (vars, ix) ->
    let (memo1, t1) = interpretAst env memo v
        f2 = interpretLambdaIndexToIndex interpretAstInt env memo (vars, ix)
    in (memo1, tgather sh t1 f2)
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
  AstConst a -> (memo, tconstBare a)
  AstConstant a -> second tconstant $ interpretAstPrimal env memo a
  AstD u u' ->
    let (memo1, t1) = interpretAstPrimal env memo u
        (memo2, t2) = interpretAstDual env memo1 u'
    in (memo2, tD t1 t2)
  AstLetDomains vars l v ->
    let (memo2, l2) = interpretAstDomains env memo l
        env2 = V.foldr (\(var, d) -> extendEnvDId var d) env (V.zip vars l2)
    in interpretAst env2 memo2 v

interpretAstDynamic
  :: InterpretAst a
  => AstEnv a -> AstMemo a
  -> AstDynamic (Value a) -> (AstMemo a, DTensorOf a)
interpretAstDynamic env memo = \case
  AstDynamic w -> second dfromR $ interpretAst env memo w

interpretAstDomains
  :: InterpretAst a
  => AstEnv a -> AstMemo a
  -> AstDomains (Value a) -> (AstMemo a, Data.Vector.Vector (DTensorOf a))
interpretAstDomains env memo = \case
  AstDomains l -> mapAccumR (interpretAstDynamic env) memo l
  AstDomainsLet var u v ->
    let (memo2, t) = interpretAst env memo u
        env2 = extendEnvR (AstVarName var) t env
    in interpretAstDomains env2 memo2 v
      -- TODO: preserve let, as in AstLet case

interpretAstInt :: InterpretAst a
                => AstEnv a -> AstMemo a
                -> AstInt (Value a) -> (AstMemo a, IntOf (Primal a))
interpretAstInt env memo = \case
  AstIntVar var -> case EM.lookup var env of
    Just AstVarR{} ->
      error $ "interpretAstInt: type mismatch for " ++ show var
    Just (AstVarI i) -> (memo, i)
    Nothing -> error $ "interpretAstInt: unknown variable " ++ show var
  AstIntOp opCodeInt args ->
    let (memo2, args2) = mapAccumR (interpretAstInt env) memo args
    in (memo2, interpretAstIntOp opCodeInt args2)
  AstIntConst a -> (memo, fromIntegral a)
  AstIntFloor v -> second tfloor $ interpretAstPrimal env memo v
  AstIntCond b a1 a2 ->
    let (memo1, b1) = interpretAstBool env memo b
        (memo2, t2) = interpretAstInt env memo1 a1
        (memo3, t3) = interpretAstInt env memo2 a2
    in (memo3, ifB b1 t2 t3)
  AstMinIndex1 v -> second tminIndex0 $ interpretAstPrimal env memo v
  AstMaxIndex1 v -> second tmaxIndex0 $ interpretAstPrimal env memo v

interpretAstBool :: forall a. InterpretAst a
                 => AstEnv a -> AstMemo a
                 -> AstBool (Value a) -> (AstMemo a, BooleanOf (Primal a))
interpretAstBool env memo = \case
  AstBoolOp opCodeBool args ->
    let (memo2, args2) = mapAccumR (interpretAstBool env) memo args
    in (memo2, interpretAstBoolOp opCodeBool args2)
  AstBoolConst a -> (memo, if a then true else false)
  AstRel opCodeRel args ->
    let (memo2, args2) = mapAccumR (interpretAstPrimal env) memo args
    in (memo2, interpretAstRelOp opCodeRel args2)
  AstRelInt opCodeRel args ->
    let (memo2, args2) = mapAccumR (interpretAstInt env) memo args
    in (memo2, interpretAstRelOp opCodeRel args2)

interpretAstDynamicDummy
  :: (InterpretAst a, DynamicTensor a)
  => AstEnv a -> AstMemo a
  -> AstDynamic (Value a) -> (AstMemo a, DTensorOf a)
interpretAstDynamicDummy env memo = \case
  AstDynamic AstIota -> (memo, ddummy)
  AstDynamic w -> second dfromR $ interpretAst env memo w

interpretAstDomainsDummy
  :: (InterpretAst a, DynamicTensor a)
  => AstEnv a -> AstMemo a
  -> AstDomains (Value a) -> (AstMemo a, Data.Vector.Vector (DTensorOf a))
interpretAstDomainsDummy env memo = \case
  AstDomains l -> mapAccumR (interpretAstDynamicDummy env) memo l
  AstDomainsLet var u v ->
    let (memo2, t) = interpretAst env memo u
        env2 = extendEnvR (AstVarName var) t env
    in interpretAstDomainsDummy env2 memo2 v
      -- TODO: preserve let, as in AstLet case

-- TODO: when the code again compiles with GHC >= 9.6, check whether
-- these INLINEs are still needed (removal causes 10% slowdown ATM).
interpretAstOp :: (Tensor r, KnownNat n)
               => OpCode -> [TensorOf n r] -> TensorOf n r
{-# INLINE interpretAstOp #-}
interpretAstOp MinusOp [u, v] = u - v
interpretAstOp TimesOp [u, v] = u `tmult` v
interpretAstOp NegateOp [u] = negate u
interpretAstOp AbsOp [u] = abs u
interpretAstOp SignumOp [u] = signum u
interpretAstOp DivideOp [u, v] = u / v
interpretAstOp RecipOp [u] = recip u
interpretAstOp ExpOp [u] = exp u
interpretAstOp LogOp [u] = log u
interpretAstOp SqrtOp [u] = sqrt u
interpretAstOp PowerOp [u, v] = u ** v
interpretAstOp LogBaseOp [u, v] = logBase u v
interpretAstOp SinOp [u] = sin u
interpretAstOp CosOp [u] = cos u
interpretAstOp TanOp [u] = tan u
interpretAstOp AsinOp [u] = asin u
interpretAstOp AcosOp [u] = acos u
interpretAstOp AtanOp [u] = atan u
interpretAstOp SinhOp [u] = sinh u
interpretAstOp CoshOp [u] = cosh u
interpretAstOp TanhOp [u] = tanh u
interpretAstOp AsinhOp [u] = asinh u
interpretAstOp AcoshOp [u] = acosh u
interpretAstOp AtanhOp [u] = atanh u
interpretAstOp Atan2Op [u, v] = atan2 u v
interpretAstOp MaxOp [u, v] = max u v
interpretAstOp MinOp [u, v] = min u v
interpretAstOp opCode args =
  error $ "interpretAstOp: wrong number of arguments"
          ++ show (opCode, length args)

interpretAstIntOp :: Integral a
                  => OpCodeInt -> [a] -> a
{-# INLINE interpretAstIntOp #-}
interpretAstIntOp PlusIntOp l = foldl1' (+) l  -- TODO: use or remove
interpretAstIntOp MinusIntOp [u, v] = u - v
interpretAstIntOp TimesIntOp l = foldl1' (*) l  -- TODO: use or remove
interpretAstIntOp NegateIntOp [u] = negate u
interpretAstIntOp AbsIntOp [u] = abs u
interpretAstIntOp SignumIntOp [u] = signum u
interpretAstIntOp MaxIntOp [u, v] = max u v
interpretAstIntOp MinIntOp [u, v] = min u v
interpretAstIntOp QuotIntOp [u, v] = quot u v
interpretAstIntOp RemIntOp [u, v] = rem u v
interpretAstIntOp opCodeInt args =
  error $ "interpretAstIntOp: wrong number of arguments"
          ++ show (opCodeInt, length args)

interpretAstBoolOp :: Boolean b
                   => OpCodeBool -> [b] -> b
{-# INLINE interpretAstBoolOp #-}
interpretAstBoolOp NotOp [u] = notB u
interpretAstBoolOp AndOp [u, v] = u &&* v
interpretAstBoolOp OrOp [u, v] = u ||* v
interpretAstBoolOp opCodeBool args =
  error $ "interpretAstBoolOp: wrong number of arguments"
          ++ show (opCodeBool, length args)

interpretAstRelOp :: (EqB b, OrdB b)
                  => OpCodeRel -> [b] -> BooleanOf b
interpretAstRelOp EqOp [u, v] = u ==* v
interpretAstRelOp NeqOp [u, v] = u /=* v
interpretAstRelOp LeqOp [u, v] = u <=* v
interpretAstRelOp GeqOp [u, v] = u >=* v
interpretAstRelOp LsOp [u, v] = u <* v
interpretAstRelOp GtOp [u, v] = u >* v
interpretAstRelOp opCodeRel args =
  error $ "interpretAstRelOp: wrong number of arguments"
          ++ show (opCodeRel, length args)



{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal Double) -> AstMemo (ADVal Double)
  -> AstPrimalPart n Double -> (AstMemo (ADVal Double), TensorOf n Double) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal Float) -> AstMemo (ADVal Float)
  -> AstPrimalPart n Float -> (AstMemo (ADVal Float), TensorOf n Float) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Double)) -> AstMemo (ADVal (Ast0 Double))
  -> AstPrimalPart n Double -> (AstMemo (ADVal (Ast0 Double)), TensorOf n (Ast0 Double)) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Float)) -> AstMemo (ADVal (Ast0 Float))
  -> AstPrimalPart n Float -> (AstMemo (ADVal (Ast0 Float)), TensorOf n (Ast0 Float)) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv Double -> AstMemo Double
  -> AstPrimalPart n Double -> (AstMemo Double, TensorOf n Double) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv Float -> AstMemo Float
  -> AstPrimalPart n Float -> (AstMemo Float, TensorOf n Float) #-}

{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal Double) -> AstMemo (ADVal Double)
  -> AstDualPart n Double -> (AstMemo (ADVal Double), DualOf n (ADVal Double)) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal Float) -> AstMemo (ADVal Float)
  -> AstDualPart n Float -> (AstMemo (ADVal Float), DualOf n (ADVal Float)) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Double)) -> AstMemo (ADVal (Ast0 Double))
  -> AstDualPart n Double -> (AstMemo (ADVal (Ast0 Double)), DualOf n (ADVal (Ast0 Double))) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Float)) -> AstMemo (ADVal (Ast0 Float))
  -> AstDualPart n Float -> (AstMemo (ADVal (Ast0 Float)), DualOf n (ADVal (Ast0 Float))) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv Double -> AstMemo Double
  -> AstDualPart n Double -> (AstMemo Double, DualOf n Double) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv Float -> AstMemo Float
  -> AstDualPart n Float -> (AstMemo Float, DualOf n Float) #-}

{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal Double) -> AstMemo (ADVal Double)
  -> Ast n Double -> (AstMemo (ADVal Double), TensorOf n (ADVal Double)) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal Float) -> AstMemo (ADVal Float)
  -> Ast n Float -> (AstMemo (ADVal Float), TensorOf n (ADVal Float)) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Double)) -> AstMemo (ADVal (Ast0 Double))
  -> Ast n Double -> (AstMemo (ADVal (Ast0 Double)), TensorOf n (ADVal (Ast0 Double))) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Float)) -> AstMemo (ADVal (Ast0 Float))
  -> Ast n Float -> (AstMemo (ADVal (Ast0 Float)), TensorOf n (ADVal (Ast0 Float))) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv Double -> AstMemo Double
  -> Ast n Double -> (AstMemo Double, TensorOf n Double) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv Float -> AstMemo Float
  -> Ast n Float -> (AstMemo Float, TensorOf n Float) #-}

{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal Double) -> AstMemo (ADVal Double)
  -> AstDynamic Double -> (AstMemo (ADVal Double), DTensorOf (ADVal Double)) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal Float) -> AstMemo (ADVal Float)
  -> AstDynamic Float -> (AstMemo (ADVal Float), DTensorOf (ADVal Float)) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Ast0 Double)) -> AstMemo (ADVal (Ast0 Double))
  -> AstDynamic Double -> (AstMemo (ADVal (Ast0 Double)), DTensorOf (ADVal (Ast0 Double))) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Ast0 Float)) -> AstMemo (ADVal (Ast0 Float))
  -> AstDynamic Float -> (AstMemo (ADVal (Ast0 Float)), DTensorOf (ADVal (Ast0 Float))) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv Double -> AstMemo Double
  -> AstDynamic Double -> (AstMemo Double, DTensorOf Double) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv Float -> AstMemo Float
  -> AstDynamic Float -> (AstMemo Float, DTensorOf Float) #-}

{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal Double) -> AstMemo (ADVal Double)
  -> AstDomains Double -> (AstMemo (ADVal Double), Data.Vector.Vector (DTensorOf (ADVal Double))) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal Float) -> AstMemo (ADVal Float)
  -> AstDomains Float -> (AstMemo (ADVal Float), Data.Vector.Vector (DTensorOf (ADVal Float))) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Ast0 Double)) -> AstMemo (ADVal (Ast0 Double))
  -> AstDomains Double -> (AstMemo (ADVal (Ast0 Double)), Data.Vector.Vector (DTensorOf (ADVal (Ast0 Double)))) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Ast0 Float)) -> AstMemo (ADVal (Ast0 Float))
  -> AstDomains Float -> (AstMemo (ADVal (Ast0 Float)), Data.Vector.Vector (DTensorOf (ADVal (Ast0 Float)))) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv Double -> AstMemo Double
  -> AstDomains Double -> (AstMemo Double, Data.Vector.Vector (DTensorOf Double)) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv Float -> AstMemo Float
  -> AstDomains Float -> (AstMemo Float, Data.Vector.Vector (DTensorOf Float)) #-}

{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal Double) -> AstMemo (ADVal Double)
  -> AstInt Double -> (AstMemo (ADVal Double), CInt) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal Float) -> AstMemo (ADVal Float)
  -> AstInt Float -> (AstMemo (ADVal Float), CInt) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Ast0 Double)) -> AstMemo (ADVal (Ast0 Double))
  -> AstInt Double -> (AstMemo (ADVal (Ast0 Double)), AstInt Double) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Ast0 Float)) -> AstMemo (ADVal (Ast0 Float))
  -> AstInt Float -> (AstMemo (ADVal (Ast0 Float)), AstInt Float) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv Double -> AstMemo Double
  -> AstInt Double -> (AstMemo Double, CInt) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv Float -> AstMemo Float
  -> AstInt Float -> (AstMemo Float, CInt) #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal Double) -> AstMemo (ADVal Double)
  -> AstBool Double -> (AstMemo (ADVal Double), Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal Float) -> AstMemo (ADVal Float)
  -> AstBool Float -> (AstMemo (ADVal Float), Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Ast0 Double)) -> AstMemo (ADVal (Ast0 Double))
  -> AstBool Double -> (AstMemo (ADVal (Ast0 Double)), AstBool Double) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Ast0 Float)) -> AstMemo (ADVal (Ast0 Float))
  -> AstBool Float -> (AstMemo (ADVal (Ast0 Float)), AstBool Float) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv Double -> AstMemo Double
  -> AstBool Double -> (AstMemo Double, Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv Float -> AstMemo Float
  -> AstBool Float -> (AstMemo Float, Bool) #-}

{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv Double -> AstMemo Double
  -> AstDynamic Double -> (AstMemo Double, DTensorOf Double) #-}
{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv Float -> AstMemo Float
  -> AstDynamic Float -> (AstMemo Float, DTensorOf Float) #-}

{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv Double -> AstMemo Double
  -> AstDomains Double -> (AstMemo Double, Data.Vector.Vector (DTensorOf Double)) #-}
{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv Float -> AstMemo Float
  -> AstDomains Float -> (AstMemo Float, Data.Vector.Vector (DTensorOf Float)) #-}

{- outdated and inlined anyway:
{-# SPECIALIZE interpretAstOp
  :: OpCode -> [(ADVal Double)] -> (ADVal Double) #-}
{-# SPECIALIZE interpretAstOp
  :: OpCode -> [(ADVal Float)] -> (ADVal Float) #-}
{-# SPECIALIZE interpretAstOp
  :: OpCode -> [(ADVal (Ast0 Double))] -> (ADVal (Ast0 Double)) #-}
{-# SPECIALIZE interpretAstOp
  :: OpCode -> [(ADVal (Ast0 Float))] -> (ADVal (Ast0 Float)) #-}
{-# SPECIALIZE interpretAstOp
  :: OpCode -> [Double] -> Double #-}
{-# SPECIALIZE interpretAstOp
  :: OpCode -> [Float] -> Float #-}
-}

{- make compilation even longer and inlined anyway:
{-# SPECIALIZE interpretAstIntOp
  :: OpCodeInt -> [Int] -> Int #-}
{-# SPECIALIZE interpretAstIntOp
  :: OpCodeInt -> [AstInt Double] -> AstInt Double #-}
{-# SPECIALIZE interpretAstIntOp
  :: OpCodeInt -> [AstInt Float] -> AstInt Float #-}

{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [Bool] -> Bool #-}
{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [AstBool Double] -> AstBool Double #-}
{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [AstBool Float] -> AstBool Float #-}
-}

{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [ADVal Double] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [ADVal Float] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [ADVal (Ast0 Double)] -> AstBool Double #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [ADVal (Ast0 Float)] -> AstBool Float #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [Double] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [Float] -> Bool #-}

{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [CInt] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [AstInt Double] -> AstBool Double #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [AstInt Float] -> AstBool Float #-}
