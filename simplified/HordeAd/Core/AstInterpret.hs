{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
-- | Interpretation of @Ast@ terms in an aribtrary @Tensor@ class instance..
module HordeAd.Core.AstInterpret
  ( InterpretAstR, InterpretAstS
  , interpretAst, interpretAstDomainsDummy, interpretAstS
  , AstEnv, extendEnvS, extendEnvR, extendEnvDR, extendEnvD
  , AstEnvElem(AstEnvElemR)  -- for a test only
  ) where

import Prelude hiding ((<*))

import           Control.Exception.Assert.Sugar
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Boolean
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Const
import           Data.List (foldl1')
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, sameNat)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.Delta
import           HordeAd.Core.DualNumber
import           HordeAd.Core.ShapedList (ShapedList (..))
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.SizedList
import           HordeAd.Core.TensorADVal
import           HordeAd.Core.TensorClass
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)

type AstEnv ranked = EM.EnumMap AstVarId (AstEnvElem ranked)

data AstEnvElem ranked =
    forall r. AstEnvElemD (DynamicOf ranked r)
  | forall n r. KnownNat n => AstEnvElemR (ranked r n)
  | forall sh r. OS.Shape sh => AstEnvElemS (ShapedOf ranked r sh)
  | forall r. AstEnvElemI (IntOf ranked r)
deriving instance ( forall r. ShowDynamicOf ranked r
                  , forall n r. Show (ranked r n)
                  , forall sh r. ShowShapedOf ranked r sh
                  , forall r. ShowIntOf ranked r )
                  => Show (AstEnvElem ranked)

class Show (DynamicOf ranked r) => ShowDynamicOf ranked r

class Show (ShapedOf ranked r sh) => ShowShapedOf ranked r sh

class Show (IntOf ranked r) => ShowIntOf ranked r

extendEnvS :: forall ranked shaped r sh.
              (OS.Shape sh, shaped ~ ShapedOf ranked, RankedOf shaped ~ ranked)
           => AstVarName (Flip OS.Array r sh) -> shaped r sh
           -> AstEnv ranked -> AstEnv ranked
extendEnvS v@(AstVarName var) t =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvS: duplicate " ++ show v)
                   var (AstEnvElemS t)

extendEnvR :: forall ranked r n. KnownNat n
           => AstVarName (Flip OR.Array r n) -> ranked r n
           -> AstEnv ranked -> AstEnv ranked
extendEnvR v@(AstVarName var) t =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show v)
                   var (AstEnvElemR t)

extendEnvDR :: (ConvertTensor ranked shaped, GoodScalar r)
            => (AstDynamicVarName r, DynamicOf ranked r)
            -> AstEnv ranked
            -> AstEnv ranked
extendEnvDR (AstDynamicVarName var, d) = extendEnvR var (tfromD d)
extendEnvDR (AstDynamicVarNameS var, d) = extendEnvS var (sfromD d)

extendEnvD :: AstVarId -> DynamicOf ranked r -> AstEnv ranked
           -> AstEnv ranked
extendEnvD var d =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvD: duplicate " ++ show var)
                   var (AstEnvElemD d)

extendEnvI :: forall r ranked.
              AstVarId -> IntOf ranked r -> AstEnv ranked
           -> AstEnv ranked
extendEnvI var i =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvI: duplicate " ++ show var)
                   var (AstEnvElemI @ranked @r i)

extendEnvVars :: forall r ranked m.
                 AstVarList m -> IndexOf ranked r m
              -> AstEnv ranked
              -> AstEnv ranked
extendEnvVars vars ix env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry (extendEnvI @r)) env assocs

extendEnvVarsS :: forall r ranked sh.
                  AstVarListS sh -> IndexSh ranked r sh
               -> AstEnv ranked
               -> AstEnv ranked
extendEnvVarsS vars ix env =
  let assocs = zip (ShapedList.sizedListToList vars)
                   (ShapedList.sizedListToList ix)
  in foldr (uncurry (extendEnvI @r)) env assocs

interpretLambdaI
  :: forall ranked n r.
     (AstEnv ranked -> AstRanked r n -> ranked r n)
  -> AstEnv ranked -> (AstVarId, AstRanked r n)
  -> IntOf ranked r
  -> ranked r n
{-# INLINE interpretLambdaI #-}
interpretLambdaI f env (var, ast) =
  \i -> f (extendEnvI @r var i env) ast

interpretLambdaIS
  :: forall ranked shaped sh n r.
     (AstEnv ranked -> AstShaped r sh -> shaped r sh)
  -> AstEnv ranked -> (AstVarId, AstShaped r sh)
  -> IntSh ranked r n
  -> shaped r sh
{-# INLINE interpretLambdaIS #-}
interpretLambdaIS f env (var, ast) =
  \i -> f (extendEnvI @r var (ShapedList.unShapedNat i) env) ast

interpretLambdaIndex
  :: forall ranked r m n.
     (AstEnv ranked -> AstRanked r n -> ranked r n)
  -> AstEnv ranked -> (AstVarList m, AstRanked r n)
  -> IndexOf ranked r m
  -> ranked r n
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f env (vars, ast) =
  \ix -> f (extendEnvVars @r vars ix env) ast

interpretLambdaIndexS
  :: forall sh sh2 ranked shaped r.
     (shaped ~ ShapedOf ranked, RankedOf shaped ~ ranked)
  => (AstEnv ranked -> AstShaped r sh -> shaped r sh)
  -> AstEnv ranked -> (AstVarListS sh2, AstShaped r sh)
  -> IndexSh ranked r sh2
  -> shaped r sh
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f env (vars, ast) =
  \ix -> f (extendEnvVarsS @r vars ix env) ast

interpretLambdaIndexToIndex
  :: forall ranked r m n.
     (AstEnv ranked -> AstInt r -> IntOf ranked r)
  -> AstEnv ranked -> (AstVarList m, AstIndex r n)
  -> IndexOf ranked r m
  -> IndexOf ranked r n
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f env (vars, asts) =
  \ix -> f (extendEnvVars @r vars ix env) <$> asts

interpretLambdaIndexToIndexS
  :: forall ranked r sh sh2.
     (AstEnv ranked -> AstInt r -> IntOf ranked r)
  -> AstEnv ranked -> (AstVarListS sh, AstIndexS r sh2)
  -> IndexSh ranked r sh
  -> IndexSh ranked r sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f env (vars, asts) =
  \ix -> f (extendEnvVarsS @r vars ix env) <$> asts

class (BooleanOf r ~ b, b ~ BooleanOf r) => BooleanOfMatches b r where
instance (BooleanOf r ~ b, b ~ BooleanOf r) => BooleanOfMatches b r where

class (forall y41. KnownNat y41 => c (ranked r y41))
      => CRanked ranked r c where
instance
      (forall y41. KnownNat y41 => c (ranked r y41))
      => CRanked ranked r c where

class (forall y41. OS.Shape y41 => c (shaped r y41))
      => CShaped shaped r c where
instance
      (forall y41. OS.Shape y41 => c (shaped r y41))
      => CShaped shaped r c where

type InterpretAstR ranked r =
  ( GoodScalar r
  , Integral (IntOf (PrimalOf ranked) r), EqB (IntOf ranked r)
  , OrdB (IntOf ranked r), IfB (IntOf ranked r)
  , IntOf (PrimalOf ranked) r ~ IntOf ranked r
  , CRanked (PrimalOf ranked) r EqB
  , CRanked (PrimalOf ranked) r OrdB
  , CRanked ranked r RealFloat
  , CRanked (PrimalOf ranked) r
            (BooleanOfMatches (BooleanOf (IntOf ranked r)))
  , BooleanOf (ranked r 0) ~ BooleanOf (IntOf ranked r)
  , BooleanOf (IntOf ranked r) ~ BooleanOf (ranked r 0)
  )

type InterpretAstS shaped r =
  ( GoodScalar r
  , Integral (IntOf (PrimalOf shaped) r), EqB (IntOf shaped r)
  , OrdB (IntOf shaped r), IfB (IntOf shaped r)
  , IntOf (PrimalOf shaped) r ~ IntOf shaped r
  , CShaped (PrimalOf shaped) r EqB
  , CShaped (PrimalOf shaped) r OrdB
  , CShaped shaped r RealFloat
  , CShaped (PrimalOf shaped) r
            (BooleanOfMatches (BooleanOf (IntOf shaped r)))
  , BooleanOf (shaped r '[]) ~ BooleanOf (IntOf shaped r)
  , BooleanOf (IntOf shaped r) ~ BooleanOf (shaped r '[])
  )

type InterpretAst ranked r =
  ( Tensor ranked, Tensor (PrimalOf ranked)
  , ShapedTensor (ShapedOf ranked), ShapedTensor (PrimalOf (ShapedOf ranked))
  , ConvertTensor ranked (ShapedOf ranked)
  , InterpretAstR ranked r
  , InterpretAstS (ShapedOf ranked) r
  , IntOf ranked r ~ IntOf (ShapedOf ranked) r
  )

-- Strict environment and strict ADVal and Delta make this is hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall ranked n r.
     (KnownNat n, InterpretAst ranked r)
  => AstEnv ranked
  -> AstPrimalPart r n -> PrimalOf ranked r n
interpretAstPrimal env (AstPrimalPart v1) = case v1 of
  AstD u _-> interpretAstPrimal env u
  _ -> tprimalPart $ interpretAst env v1

interpretAstDual
  :: forall ranked n r.
     (KnownNat n, InterpretAst ranked r)
  => AstEnv ranked
  -> AstDualPart r n -> DualOf ranked r n
interpretAstDual env (AstDualPart v1) = case v1 of
  AstD _ u'-> interpretAstDual env u'
  _ -> tdualPart $ interpretAst env v1

interpretAst
  :: forall ranked n r.
     (KnownNat n, InterpretAst ranked r)
  => AstEnv ranked
  -> AstRanked r n -> ranked r n
interpretAst env = \case
  AstVar sh var -> case EM.lookup var env of
    Just (AstEnvElemR @_ @n2 @r2 t) -> case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> gcastWith (unsafeCoerce Refl :: r :~: r2) $ assert (sh == tshape t) t  -- TODO
      Nothing -> error "interpretAst: wrong rank in environment"
    Just _  ->
      error $ "interpretAst: type mismatch for " ++ show var
    Nothing -> error $ "interpretAst: unknown variable " ++ show var
  AstLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAst env u
        env2 w = extendEnvR (AstVarName var) w env
    in tlet t (\w -> interpretAst (env2 w) v)
  AstLetADShare{} -> error "interpretAst: AstLetADShare"
  {- TODO: revise when we handle GPUs. For now, this is done in TensorOps
     instead and that's fine, because for one-element carriers,
     reshape and replicate are very cheap. OTOH, this was introducing
     ScalarR(UnScalar0 ...) into delta expressions by firing
     in an early phase.
  AstOp TimesOp [v, AstReshape _ (AstReplicate @m _ s)]
   -- TODO: also handle nested AstReplicate to prevent executing them
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env v
            t2 = interpretAst env s
        in tscaleByScalar0 t2 t1
  AstOp TimesOp [v, AstReplicate @m _ s]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env v
            t2 = interpretAst env s
        in tscaleByScalar0 t2 t1
  -}
  AstOp TimesOp [v, AstLet var u (AstReshape sh (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        -- The intVarInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env
          (AstLet var u (AstOp TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env
          (AstLet var u (AstOp TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env
          (AstLet var u (AstOp TimesOp [v, AstReplicate @m k s]))
  AstOp TimesOp [v, u] ->
    let v5 = interpretAst env v
        u5 = interpretAst env u
    in v5 `tmult` u5
  AstOp opCode args ->
    let args2 = interpretAst env <$> args
    in interpretAstOp opCode args2
  AstSumOfList args ->
    let args2 = interpretAst env <$> args
    in tsumOfList args2
  AstIota -> error "interpretAst: bare AstIota, most likely a bug"
  AstIndex AstIota (i :. ZI) -> tfromIndex0 $ interpretAstInt env i
  AstIndex v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAstInt env <$> ix
    in tindex v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstSum (AstOp TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstTranspose uperm u ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm t
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstOp TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ]))))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstReplicate uk u) ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ]))))
  AstSum v@(AstOp TimesOp [ AstTranspose tperm (AstReplicate _tk t)
                          , AstTranspose uperm (AstReplicate _uk u) ])
    | Just Refl <- sameNat (Proxy @n) (Proxy @2) ->
        let interpretMatmul2 t1 u1 =
              let t2 = interpretAst env t1
                  u2 = interpretAst env u1
              in tmatmul2 t2 u2
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
            ttr $ interpretMatmul2 t u
          ([1, 2, 0], [2, 0, 1]) ->
            ttr $ interpretMatmul2 u t
--          ([2, 0, 1], [2, 1, 0]) ->
--            ttr $ interpretMatmul2 t (AstTranspose [1, 0] u)
--          ([2, 1, 0], [2, 0, 1]) ->
--            ttr $ interpretMatmul2 u (AstTranspose [1, 0] t)
--          ([1, 2, 0], [1, 0]) ->
--            ttr $ interpretMatmul2 (AstTranspose [1, 0] u) t
--          ([1, 0], [2, 1, 0]) ->
--            ttr
--            $ interpretMatmul2 (AstTranspose [1, 0] t) (AstTranspose [1, 0] u)
--          ([2, 1, 0], [1, 0]) ->
--            ttr
--            $ interpretMatmul2 (AstTranspose [1, 0] u) (AstTranspose [1, 0] t)
          _ -> tsum $ interpretAst env v
  AstSum (AstOp TimesOp [t, u])
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstOp TimesOp [t, u]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstOp TimesOp [t, u]))  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot1In t1 t2
  AstSum (AstTranspose [1, 0] t)  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        tsumIn $ interpretAst env t
  AstSum (AstReshape sh (AstTranspose _ t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env (AstSum (AstReshape sh t))
  AstSum (AstReshape sh (AstReverse t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env (AstSum (AstReshape sh t))
  AstSum (AstReshape _sh (AstSum t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        tsum0 $ interpretAst env t
  AstSum (AstSum t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        tsum0 $ interpretAst env t
          -- more cases are needed so perhaps we need AstSum0
  AstSum (AstReplicate k v) ->
    tscaleByScalar (fromIntegral k) $ interpretAst env v
  AstSum (AstLet var v t) -> interpretAst env (AstLet var v (AstSum t))
  AstSum (AstReshape sh (AstLet var v t)) ->
    interpretAst env (AstLet var v (AstSum (AstReshape sh t)))
  AstSum (AstReshape _sh t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        tsum0 $ interpretAst env t
  AstSum v -> tsum $ interpretAst env v
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstScatter sh v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndex interpretAstInt env (vars, ix)
    in tscatter sh t1 f2
  AstFromList l ->
    let l2 = interpretAst env <$> l
    in tfromList l2
  AstFromVector l ->
    let l2 = V.map (interpretAst env) l
    in tfromVector l2
      -- TODO: emulate mapAccum using mapM?
  AstReshape sh (AstReplicate @m _ s)
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env s
        in treplicate0N sh t1
  AstReshape sh (AstLet var v (AstReplicate k t)) ->
    interpretAst env (AstLet var v (AstReshape sh (AstReplicate k t)))
  AstReplicate k v -> treplicate k (interpretAst env v)
  AstAppend x y ->
    let t1 = interpretAst env x
        t2 = interpretAst env y
    in tappend t1 t2
  AstSlice i n AstIota ->
    interpretAst env
    $ AstConst $ OR.fromList [n] $ map fromIntegral [i .. i + n - 1]
  AstSlice i n v -> tslice i n (interpretAst env v)
  AstReverse v -> treverse (interpretAst env v)
  AstTranspose perm v -> ttranspose perm $ interpretAst env v
  AstReshape sh v -> treshape sh (interpretAst env v)
  -- These are only needed for tests that don't vectorize Ast.
  AstBuild1 k (var, AstSum (AstOp TimesOp [t, AstIndex
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstOp TimesOp [t, AstIndex
                                                  u (AstIntVar var2 :. ZI)])))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, k == tlength u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tmatvecmul t2 t1
  AstBuild1 0 (_, v) -> tfromList0N (0 :$ tshape v) []
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
    tbuild1 k (interpretLambdaI interpretAst env (var, v))
      -- to be used only in tests
  AstGather sh AstIota (vars, (i :. ZI)) ->
    tbuild sh (interpretLambdaIndex interpretAst env
                                    (vars, tfromIndex0 i))
  AstGather sh v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndex interpretAstInt env (vars, ix)
    in tgather sh t1 f2
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
  AstSToR v -> tfromS $ interpretAstS env v
  AstConst a -> tconstBare a
  AstConstant a -> tconstant $ interpretAstPrimal env a
  AstD u u' ->
    let t1 = interpretAstPrimal env u
        t2 = interpretAstDual env u'
    in tD t1 t2
  AstLetDomains vars l v ->
    let l2 = interpretAstDomains env l
        env2 = V.foldr (\(var, d) -> extendEnvD var d) env (V.zip vars l2)
    in interpretAst env2 v

interpretAstDynamic
  :: forall ranked r.
     InterpretAst ranked r
  => AstEnv ranked
  -> AstDynamic r -> DynamicOf ranked r
interpretAstDynamic env = \case
  AstRToD w -> dfromR $ interpretAst env w
  AstSToD w -> dfromS $ interpretAstS env w

interpretAstDomains
  :: forall ranked r.
     InterpretAst ranked r
  => AstEnv ranked
  -> AstDomains r -> Domains (DynamicOf ranked) r
interpretAstDomains env = \case
  AstDomains l -> interpretAstDynamic env <$> l
  AstDomainsLet var u v ->
    let t = interpretAst env u
        env2 = extendEnvR (AstVarName var) t env
    in interpretAstDomains env2 v
      -- TODO: preserve let, as in AstLet case
  AstDomainsLetS var u v ->
    let t = interpretAstS env u
        env2 = extendEnvS (AstVarName var) t env
    in interpretAstDomains env2 v
      -- TODO: preserve let, as in AstLet case

interpretAstInt :: forall ranked r.
                   InterpretAst ranked r
                => AstEnv ranked
                -> AstInt r -> IntOf ranked r
interpretAstInt env = \case
  AstIntVar var -> case EM.lookup var env of
    Just (AstEnvElemI @_ @r2 i) -> gcastWith (unsafeCoerce Refl :: r :~: r2) $ i  -- TODO
    Just _ ->
      error $ "interpretAstInt: type mismatch for " ++ show var
    Nothing -> error $ "interpretAstInt: unknown variable " ++ show var
  AstIntOp opCodeInt args ->
    let args2 = interpretAstInt env <$> args
    in interpretAstIntOp opCodeInt args2
  AstIntConst a -> fromIntegral a
  AstIntFloor v -> tfloor $ interpretAstPrimal env v
  AstIntFloorS v -> sfloor $ interpretAstPrimalS env v
  AstIntCond b a1 a2 ->
    let b1 = interpretAstBool env b
        t2 = interpretAstInt env a1
        t3 = interpretAstInt env a2
    in ifB b1 t2 t3
  AstMinIndex1 v -> tminIndex0 $ interpretAstPrimal env v
  AstMaxIndex1 v -> tmaxIndex0 $ interpretAstPrimal env v
  AstMinIndex1S v -> ShapedList.unShapedNat . sminIndex0
                     $ interpretAstPrimalS env v
  AstMaxIndex1S v -> ShapedList.unShapedNat . smaxIndex0
                     $ interpretAstPrimalS env v

interpretAstBool :: forall ranked r.
                    InterpretAst ranked r
                 => AstEnv ranked
                 -> AstBool r -> BooleanOf (ranked r 0)
interpretAstBool env = \case
  AstBoolOp opCodeBool args ->
    let args2 = interpretAstBool env <$> args
    in interpretAstBoolOp opCodeBool args2
  AstBoolConst a -> if a then true else false
  AstRel opCodeRel args ->
    let args2 = interpretAstPrimal env <$> args
    in interpretAstRelOp opCodeRel args2
  AstRelS opCodeRel args ->
    let args2 = interpretAstPrimalS env <$> args
    in interpretAstRelOp opCodeRel args2
  AstRelInt opCodeRel args ->
    let args2 = interpretAstInt env <$> args
    in interpretAstRelOp opCodeRel args2

interpretAstDynamicDummy
  :: forall ranked r.
     InterpretAst ranked r
  => AstEnv ranked
  -> AstDynamic r -> DynamicOf ranked r
interpretAstDynamicDummy env = \case
  AstRToD AstIota -> ddummy @ranked
  AstRToD w -> dfromR $ interpretAst env w
  AstSToD AstIotaS -> ddummy @ranked
  AstSToD w -> dfromS $ interpretAstS env w

interpretAstDomainsDummy
  :: forall ranked r.
     InterpretAst ranked r
  => AstEnv ranked
  -> AstDomains r -> Domains (DynamicOf ranked) r
interpretAstDomainsDummy env = \case
  AstDomains l -> interpretAstDynamicDummy env <$> l
  AstDomainsLet var u v ->
    let t = interpretAst env u
        env2 = extendEnvR (AstVarName var) t env
    in interpretAstDomainsDummy env2 v
      -- TODO: preserve let, as in AstLet case
  AstDomainsLetS var u v ->
    let t = interpretAstS env u
        env2 = extendEnvS (AstVarName var) t env
    in interpretAstDomainsDummy env2 v
      -- TODO: preserve let, as in AstLet case

-- TODO: when the code again tests with GHC >= 9.6, check whether
-- these INLINEs are still needed (removal causes 10% slowdown ATM).
interpretAstOp :: RealFloat a
               => OpCode -> [a] -> a
{-# INLINE interpretAstOp #-}
interpretAstOp MinusOp [u, v] = u - v
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

interpretAstPrimalS
  :: forall ranked shaped sh r.
     (OS.Shape sh, shaped ~ ShapedOf ranked, RankedOf shaped ~ ranked)
  => InterpretAst ranked r
  => AstEnv ranked
  -> AstPrimalPartS r sh -> PrimalOf shaped r sh
interpretAstPrimalS env (AstPrimalPartS v1) = case v1 of
  AstDS u _-> interpretAstPrimalS env u
  _ -> sprimalPart $ interpretAstS env v1

interpretAstDualS
  :: forall ranked shaped sh r.
     (OS.Shape sh, shaped ~ ShapedOf ranked, RankedOf shaped ~ ranked)
  => InterpretAst ranked r
  => AstEnv ranked
  -> AstDualPartS r sh -> DualOf shaped r sh
interpretAstDualS env (AstDualPartS v1) = case v1 of
  AstDS _ u'-> interpretAstDualS env u'
  _ -> sdualPart $ interpretAstS env v1

interpretAstS
  :: forall ranked shaped sh r.
     (OS.Shape sh, shaped ~ ShapedOf ranked, RankedOf shaped ~ ranked)
  => InterpretAst ranked r
  => AstEnv ranked
  -> AstShaped r sh -> shaped r sh
interpretAstS env = \case
  AstVarS var -> case EM.lookup var env of
    Just (AstEnvElemS @_ @sh2 @r2 t) -> case sameShape @sh2 @sh of
      Just Refl -> gcastWith (unsafeCoerce Refl :: r :~: r2) $ t  -- TODO
      Nothing -> error "interpretAstS: wrong shape in environment"
    Just _ ->
      error $ "interpretAstS: type mismatch for " ++ show var
    Nothing -> error $ "interpretAstS: unknown variable " ++ show var
  AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstS env u
        env2 w = extendEnvS (AstVarName var) w env
    in slet t (\w -> interpretAstS (env2 w) v)
  AstLetADShareS{} -> error "interpretAst: AstLetADShare"
{- TODO:
  AstOp TimesOp [v, AstLet var u (AstReshape sh (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        -- The intVarInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env
          (AstLet var u (AstOp TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env
          (AstLet var u (AstOp TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env
          (AstLet var u (AstOp TimesOp [v, AstReplicate @m k s]))
-}
  AstOpS TimesOp [v, u] ->
    let v5 = interpretAstS env v
        u5 = interpretAstS env u
    in v5 `smult` u5
  AstOpS opCode args ->
    let args2 = interpretAstS env <$> args
    in interpretAstOp opCode args2
  AstSumOfListS args ->
    let args2 = interpretAstS env <$> args
    in ssumOfList args2
  AstIotaS -> error "interpretAstS: bare AstIotaS, most likely a bug"
  AstIndexS (AstIotaS @n) (i :$: ZSH) ->
    sfromIndex0 . ShapedList.shapedNat @n $ interpretAstInt env i
  AstIndexS @sh1 v ix ->
    let v2 = interpretAstS env v
        ix3 = interpretAstInt env <$> ix
    in sindex @shaped @r @sh1 v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
{- TODO:
  AstSum (AstOp TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstTranspose uperm u ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm t
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstOp TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ]))))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstReplicate uk u) ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstOp TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ]))))
  AstSum v@(AstOp TimesOp [ AstTranspose tperm (AstReplicate _tk t)
                          , AstTranspose uperm (AstReplicate _uk u) ])
    | Just Refl <- sameNat (Proxy @n) (Proxy @2) ->
        let interpretMatmul2 t1 u1 =
              let t2 = interpretAst env t1
                  u2 = interpretAst env u1
              in tmatmul2 t2 u2
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
          _ -> tsum $ interpretAst env v
  AstSum (AstOp TimesOp [t, u])
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstOp TimesOp [t, u]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstOp TimesOp [t, u]))  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot1In t1 t2
  AstSum (AstTranspose [1, 0] t)  -- TODO: generalize
    | Just Refl <- sameNat (Proxy @n) (Proxy @1) ->
        tsumIn $ interpretAst env t
  AstSum (AstReshape sh (AstTranspose _ t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env (AstSum (AstReshape sh t))
  AstSum (AstReshape sh (AstReverse t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        interpretAst env (AstSum (AstReshape sh t))
  AstSum (AstReshape _sh (AstSum t))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        tsum0 $ interpretAst env t
  AstSum (AstSum t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        tsum0 $ interpretAst env t
          -- more cases are needed so perhaps we need AstSum0
  AstSum (AstReplicate k v) ->
    tscaleByScalar (fromIntegral k) $ interpretAst env v
  AstSum (AstLet var v t) -> interpretAst env (AstLet var v (AstSum t))
  AstSum (AstReshape sh (AstLet var v t)) ->
    interpretAst env (AstLet var v (AstSum (AstReshape sh t)))
  AstSum (AstReshape _sh t)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        tsum0 $ interpretAst env t
-}
  AstSumS v -> ssum $ interpretAstS env v
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstScatterS v (vars, ix) ->
    let t1 = interpretAstS env v
        f2 = interpretLambdaIndexToIndexS interpretAstInt env (vars, ix)
    in sscatter t1 f2
  AstFromListS l ->
    let l2 = interpretAstS env <$> l
    in sfromList l2
  AstFromVectorS l ->
    let l2 = V.map (interpretAstS env) l
    in sfromVector l2
      -- TODO: emulate mapAccum using mapM?
{- TODO:
  AstReshape sh (AstReplicate @m _ s)
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env s
        in treplicate0N sh t1
  AstReshape sh (AstLet var v (AstReplicate k t)) ->
    interpretAst env (AstLet var v (AstReshape sh (AstReplicate k t)))
-}
  AstReplicateS v -> sreplicate (interpretAstS env v)
  AstAppendS x y ->
    let t1 = interpretAstS env x
        t2 = interpretAstS env y
    in sappend t1 t2
  AstSliceS @i @k AstIotaS ->
    let i = valueOf @i
        k = valueOf @k
    in interpretAstS env
       $ AstConstS $ OS.fromList $ map fromIntegral [i :: Int .. i + k - 1]
  AstSliceS @i v -> sslice (Proxy @i) Proxy (interpretAstS env v)
  AstReverseS v -> sreverse (interpretAstS env v)
  AstTransposeS @perm v -> stranspose (Proxy @perm) $ interpretAstS env v
  AstReshapeS v -> sreshape (interpretAstS env v)
  -- These are only needed for tests that don't vectorize Ast.
{- TODO:
  AstBuild1 k (var, AstSum (AstOp TimesOp [t, AstIndex
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstOp TimesOp [t, AstIndex
                                                  u (AstIntVar var2 :. ZI)])))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , Just Refl <- sameNat (Proxy @p) (Proxy @1)
    , var == var2, k == tlength u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tmatvecmul t2 t1
  AstBuild1 0 (_, v) -> tfromList0N (0 :$ tshape v) []
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
  AstGatherS @sh2 (AstIotaS @n) (vars, (i :$: ZSH)) ->
    gcastWith (unsafeCoerce Refl :: OS.Take (OS.Rank sh) sh :~: sh)
    $ gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: sh2 :~: sh)
        -- transitivity of type equality doesn't work, by design,
        -- so this direct cast is needed instead of more basic laws
    $ sbuild @shaped @r @(OS.Rank sh)
             (interpretLambdaIndexS
                interpretAstS env
                (vars, sfromIndex0 (ShapedList.shapedNat @n i)))
  AstGatherS v (vars, ix) ->
    let t1 = interpretAstS env v
        f2 = interpretLambdaIndexToIndexS interpretAstInt env (vars, ix)
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
  AstRToS v -> sfromR $ interpretAst env v
  AstConstS a -> sconstBare a
  AstConstantS a -> sconstant $ interpretAstPrimalS env a
  AstDS u u' ->
    let t1 = interpretAstPrimalS env u
        t2 = interpretAstDualS env u'
    in sD t1 t2
  AstLetDomainsS vars l v ->
    let l2 = interpretAstDomains env l
        env2 = V.foldr (\(var, d) -> extendEnvD var d) env (V.zip vars l2)
    in interpretAstS env2 v



{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstPrimalPart Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstPrimalPart Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal AstRanked)
  -> AstPrimalPart Double n
  -> AstRanked Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal AstRanked)
  -> AstPrimalPart Float n
  -> AstRanked Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstPrimalPart Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstPrimalPart Float n
  -> Flip OR.Array Float n #-}

{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstDualPart Double n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstDualPart Float n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal AstRanked)
  -> AstDualPart Double n
  -> Product (Clown (Const ADShare)) (DeltaR AstRanked AstShaped) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal AstRanked)
  -> AstDualPart Float n
  -> Product (Clown (Const ADShare)) (DeltaR AstRanked AstShaped) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstDualPart Double n
  -> DummyDual Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstDualPart Float n
  -> DummyDual Float n #-}

{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked Double n
  -> ADVal (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked Float n
  -> ADVal (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal AstRanked)
  -> AstRanked Double n
  -> ADVal AstRanked Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal AstRanked)
  -> AstRanked Float n
  -> ADVal AstRanked Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked Float n
  -> Flip OR.Array Float n #-}

{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstDynamic Double
  -> ADValClown OD.Array Double #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstDynamic Float
  -> ADValClown OD.Array Float #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal AstRanked)
  -> AstDynamic Double
  -> ADValClown AstDynamic Double #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal AstRanked)
  -> AstDynamic Float
  -> ADValClown AstDynamic Float #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array)
  -> AstDynamic Double
  -> OD.Array Double #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array)
  -> AstDynamic Float
  -> OD.Array Float #-}

{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstDomains Double
  -> Domains (ADValClown OD.Array) Double #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstDomains Float
  -> Domains (ADValClown OD.Array) Float #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal AstRanked)
  -> AstDomains Double
  -> Domains (ADValClown AstDynamic) Double #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal AstRanked)
  -> AstDomains Float
  -> Domains (ADValClown AstDynamic) Float #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (Flip OR.Array)
  -> AstDomains Double
  -> Domains OD.Array Double #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv  (Flip OR.Array)
  -> AstDomains Float
  -> Domains OD.Array Float #-}

{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstInt Double
  -> CInt #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstInt Float
  -> CInt #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal AstRanked)
  -> AstInt Double
  -> AstInt Double #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal AstRanked)
  -> AstInt Float
  -> AstInt Float #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (Flip OR.Array)
  -> AstInt Double
  -> CInt #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (Flip OR.Array)
  -> AstInt Float
  -> CInt #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstBool Double
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstBool Float
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal AstRanked)
  -> AstBool Double
  -> AstBool Double #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal AstRanked)
  -> AstBool Float
  -> AstBool Float #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array)
  -> AstBool Double
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array)
  -> AstBool Float
  -> Bool #-}

{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array)
  -> AstDynamic Double
  -> OD.Array Double #-}
{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array)
  -> AstDynamic Float
  -> OD.Array Float #-}

{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array)
  -> AstDomains Double
  -> Domains OD.Array Double #-}
{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array)
  -> AstDomains Float
  -> Domains OD.Array Float #-}

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
  :: OpCodeRel -> [Flip OR.Array Double n] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [Flip OR.Array Float n] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked Double n] -> AstBool Double #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked Float n] -> AstBool Float #-}

{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [CInt] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [AstInt Double] -> AstBool Double #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [AstInt Float] -> AstBool Float #-}
