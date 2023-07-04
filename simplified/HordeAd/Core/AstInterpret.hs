{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
-- | Interpretation of @Ast@ terms in an aribtrary @Tensor@ class instance..
module HordeAd.Core.AstInterpret
  ( InterpretAstR, InterpretAstS
  , interpretAst, interpretAstDomainsDummy, interpretAstS
  , AstEnv, extendEnvS, extendEnvR, extendEnvDR
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
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, sameNat)
import           Type.Reflection (typeRep)
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
    forall n r. (KnownNat n, GoodScalar r) => AstEnvElemR (ranked r n)
  | forall sh r. (OS.Shape sh, GoodScalar r)
                 => AstEnvElemS (ShapedOf ranked r sh)
  | AstEnvElemI (IntOf ranked)
deriving instance (forall r n sh. ShowDynamicOf ranked r n sh)
                  => Show (AstEnvElem ranked)

class ( Show (DynamicOf ranked r)
      , Show (ranked r n)
      , Show (ShapedOf ranked r sh)
      , Show (IntOf ranked) ) => ShowDynamicOf ranked r n sh

extendEnvS :: forall ranked shaped r sh.
              (OS.Shape sh, shaped ~ ShapedOf ranked, GoodScalar r)
           => AstVarName (Flip OS.Array r sh) -> shaped r sh
           -> AstEnv ranked -> AstEnv ranked
extendEnvS v@(AstVarName var) t =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvS: duplicate " ++ show v)
                   var (AstEnvElemS t)

extendEnvR :: forall ranked r n. (KnownNat n, GoodScalar r)
           => AstVarName (Flip OR.Array r n) -> ranked r n
           -> AstEnv ranked -> AstEnv ranked
extendEnvR v@(AstVarName var) t =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show v)
                   var (AstEnvElemR t)

extendEnvDR :: ConvertTensor ranked shaped
            => (AstDynamicVarName, DynamicExists (DynamicOf ranked))
            -> AstEnv ranked
            -> AstEnv ranked
extendEnvDR (AstDynamicVarName @_ @r var, DynamicExists @_ @r2 d) =
  case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> extendEnvR var (tfromD d)
    _ -> error "extendEnvDR: type mismatch"
extendEnvDR (AstDynamicVarNameS @_ @r var, DynamicExists @_ @r2 d) =
  case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> extendEnvS var (sfromD d)
    _ -> error "extendEnvDR: type mismatch"

extendEnvI :: AstVarId -> IntOf ranked -> AstEnv ranked
           -> AstEnv ranked
extendEnvI var i =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvI: duplicate " ++ show var)
                   var (AstEnvElemI i)

extendEnvVars :: forall ranked m.
                 AstVarList m -> IndexOf ranked m
              -> AstEnv ranked
              -> AstEnv ranked
extendEnvVars vars ix env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvVarsS :: forall ranked sh.
                  AstVarListS sh -> IndexSh ranked sh
               -> AstEnv ranked
               -> AstEnv ranked
extendEnvVarsS vars ix env =
  let assocs = zip (ShapedList.sizedListToList vars)
                   (ShapedList.sizedListToList ix)
  in foldr (uncurry extendEnvI) env assocs

interpretLambdaI
  :: forall ranked n r.
     (AstEnv ranked -> AstRanked r n -> ranked r n)
  -> AstEnv ranked -> (AstVarId, AstRanked r n)
  -> IntOf ranked
  -> ranked r n
{-# INLINE interpretLambdaI #-}
interpretLambdaI f env (var, ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIS
  :: forall ranked shaped sh n r.
     (AstEnv ranked -> AstShaped r sh -> shaped r sh)
  -> AstEnv ranked -> (AstVarId, AstShaped r sh)
  -> IntSh ranked n
  -> shaped r sh
{-# INLINE interpretLambdaIS #-}
interpretLambdaIS f env (var, ast) =
  \i -> f (extendEnvI var (ShapedList.unShapedNat i) env) ast

interpretLambdaIndex
  :: forall ranked r m n.
     (AstEnv ranked -> AstRanked r n -> ranked r n)
  -> AstEnv ranked -> (AstVarList m, AstRanked r n)
  -> IndexOf ranked m
  -> ranked r n
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f env (vars, ast) =
  \ix -> f (extendEnvVars vars ix env) ast

interpretLambdaIndexS
  :: forall sh sh2 ranked shaped r.
     (AstEnv ranked -> AstShaped r sh -> shaped r sh)
  -> AstEnv ranked -> (AstVarListS sh2, AstShaped r sh)
  -> IndexSh ranked sh2
  -> shaped r sh
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f env (vars, ast) =
  \ix -> f (extendEnvVarsS vars ix env) ast

interpretLambdaIndexToIndex
  :: forall ranked m n.
     (AstEnv ranked -> AstInt -> IntOf ranked)
  -> AstEnv ranked -> (AstVarList m, AstIndex n)
  -> IndexOf ranked m
  -> IndexOf ranked n
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f env (vars, asts) =
  \ix -> f (extendEnvVars vars ix env) <$> asts

interpretLambdaIndexToIndexS
  :: forall ranked sh sh2.
     (AstEnv ranked -> AstInt -> IntOf ranked)
  -> AstEnv ranked -> (AstVarListS sh, AstIndexS sh2)
  -> IndexSh ranked sh
  -> IndexSh ranked sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f env (vars, asts) =
  \ix -> f (extendEnvVarsS vars ix env) <$> asts

class ( BooleanOf (ranked r 0)
        ~ BooleanOf (IntOf (PrimalOf (ShapedOf ranked)))
      , BooleanOf (IntOf (PrimalOf (ShapedOf ranked)))
        ~ BooleanOf (ranked r 0) )
      => BooleanMatchesR ranked r where
instance
      ( BooleanOf (ranked r 0)
        ~ BooleanOf (IntOf (PrimalOf (ShapedOf ranked)))
      , BooleanOf (IntOf (PrimalOf (ShapedOf ranked)))
        ~ BooleanOf (ranked r 0) )
      => BooleanMatchesR ranked r where

class ( BooleanOf (ranked () 0)
        ~ BooleanOf (PrimalOf (ShapedOf ranked) r y)
      , BooleanOf (PrimalOf (ShapedOf ranked) r y)
        ~ BooleanOf (ranked () 0) )
      => BooleanMatchesR2 ranked r y where
instance
      ( BooleanOf (ranked () 0)
        ~ BooleanOf (PrimalOf (ShapedOf ranked) r y)
      , BooleanOf (PrimalOf (ShapedOf ranked) r y)
        ~ BooleanOf (ranked () 0) )
      => BooleanMatchesR2 ranked r y where

class ( EqB (PrimalOf ranked r y)
      , OrdB (PrimalOf ranked r y) )
      => BooleanMatchesYR ranked r y where
instance
      ( EqB (PrimalOf ranked r y)
      , OrdB (PrimalOf ranked r y) )
      => BooleanMatchesYR ranked r y where

class ( EqB (PrimalOf shaped r y)
      , OrdB (PrimalOf shaped r y) )
      => BooleanMatchesYS shaped r y where
instance
      ( EqB (PrimalOf shaped r y)
      , OrdB (PrimalOf shaped r y) )
      => BooleanMatchesYS shaped r y where

class ( Boolean (BooleanOf (ranked r y)) )
      => BooleanMatchesXR ranked r y where
instance
      ( Boolean (BooleanOf (ranked r y)) )
      => BooleanMatchesXR ranked r y where

class ( BooleanOf (PrimalOf ranked r y) ~ BooleanOf (ranked r2 0)
      , BooleanOf (ranked r2 0) ~ BooleanOf (PrimalOf ranked r y) )
      => BooleanMatchesXR8 ranked r r2 y where
instance
      ( BooleanOf (PrimalOf ranked r y) ~ BooleanOf (ranked r2 0)
      , BooleanOf (ranked r2 0) ~ BooleanOf (PrimalOf ranked r y) )
      => BooleanMatchesXR8 ranked r r2 y where

class (forall rc yc. (GoodScalar rc, KnownNat yc) => c ranked rc yc)
      => CRankedY2 ranked c where
instance
      (forall rc yc. (GoodScalar rc, KnownNat yc) => c ranked rc yc)
      => CRankedY2 ranked c where

class (forall re. c ranked re)
      => CRanked ranked c where
instance
      (forall re. c ranked re)
      => CRanked ranked c where

class (forall re ye. c ranked re ye)
      => CRankedX2 ranked c where
instance
      (forall re ye. c ranked re ye)
      => CRankedX2 ranked c where

class (forall re re2. c ranked re re2)
      => CRankedX4 ranked c where
instance
      (forall re re2. c ranked re re2)
      => CRankedX4 ranked c where

class (forall re re2 ye. c ranked re re2 ye)
      => CRankedX8 ranked c where
instance
      (forall re re2 ye. c ranked re re2 ye)
      => CRankedX8 ranked c where

class (forall rd yd. (GoodScalar rd, OS.Shape yd) => c shaped rd yd)
      => CShapedY2 shaped c where
instance
      (forall rd yd. (GoodScalar rd, OS.Shape yd) => c shaped rd yd)
      => CShapedY2 shaped c where

type InterpretAstR ranked =
  ( EqB (IntOf ranked)
  , OrdB (IntOf ranked)
  , IfB (IntOf ranked)
  , IntOf ranked ~ IntOf (ShapedOf ranked)
  , IntOf (ShapedOf ranked) ~ IntOf ranked
  , IntOf ranked ~ IntOf (PrimalOf ranked)
  , IntOf (PrimalOf ranked) ~ IntOf ranked
  , CRankedY2 ranked BooleanMatchesYR
  , CRankedX2 ranked BooleanMatchesXR
  , CRankedX2 ranked BooleanMatchesR2
  , CRankedX8 ranked BooleanMatchesXR8
  , CRanked ranked BooleanMatchesR
  )

type InterpretAstS shaped =
  ( EqB (IntOf shaped)
  , OrdB (IntOf shaped)
  , IfB (IntOf shaped)
  , IntOf shaped ~ IntOf (PrimalOf shaped)
  , IntOf (PrimalOf shaped) ~ IntOf shaped
  , CShapedY2 shaped BooleanMatchesYS
  )

type InterpretAst ranked =
  ( Tensor ranked, Tensor (PrimalOf ranked)
  , ShapedTensor (ShapedOf ranked), ShapedTensor (PrimalOf (ShapedOf ranked))
  , ConvertTensor ranked (ShapedOf ranked)
  , InterpretAstR ranked
  , InterpretAstS (ShapedOf ranked)
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
     (KnownNat n, InterpretAst ranked, GoodScalar r)
  => AstEnv ranked
  -> AstPrimalPart r n -> PrimalOf ranked r n
interpretAstPrimal env (AstPrimalPart v1) = case v1 of
  AstD u _-> interpretAstPrimal env u
  _ -> tprimalPart $ interpretAst env v1

interpretAstDual
  :: forall ranked n r.
     (KnownNat n, InterpretAst ranked, GoodScalar r)
  => AstEnv ranked
  -> AstDualPart r n -> DualOf ranked r n
interpretAstDual env (AstDualPart v1) = case v1 of
  AstD _ u'-> interpretAstDual env u'
  _ -> tdualPart $ interpretAst env v1

interpretAst
  :: forall ranked n r.
     (KnownNat n, InterpretAst ranked, GoodScalar r)
  => AstEnv ranked
  -> AstRanked r n -> ranked r n
interpretAst env = \case
  AstVar sh var -> case EM.lookup var env of
    Just (AstEnvElemR @_ @n2 @r2 t) -> case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> assert (sh == tshape t) t
        _ -> error "interpretAst: type mismatch"
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
  AstCast v -> tcast $ interpretAst env v
  AstSToR v -> tfromS $ interpretAstS env v
  AstConst a -> tconstBare a
  AstConstant a -> tconstant $ interpretAstPrimal env a
  AstD u u' ->
    let t1 = interpretAstPrimal env u
        t2 = interpretAstDual env u'
    in tD t1 t2
  AstLetDomains vars l v ->
    let l2 = interpretAstDomains env l
        f (varId, DynamicExists @_ @r2 d) =
          let sh2 = dshape @ranked d
          in OS.withShapeP sh2 $ \(Proxy @sh2) ->
            extendEnvS @ranked @(ShapedOf ranked) @r2 @sh2
                       (AstVarName varId) (sfromD d)
        env2 = V.foldr f env (V.zip vars l2)
    in interpretAst env2 v

interpretAstDynamic
  :: forall ranked. InterpretAst ranked
  => AstEnv ranked -> DynamicExists AstDynamic
  -> DynamicExists (DynamicOf ranked)
interpretAstDynamic env = \case
  DynamicExists (AstRToD w) -> DynamicExists $ dfromR $ interpretAst env w
  DynamicExists (AstSToD w) -> DynamicExists $ dfromS $ interpretAstS env w

interpretAstDomains
  :: forall ranked . InterpretAst ranked
  => AstEnv ranked -> AstDomains -> Domains (DynamicOf ranked)
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

interpretAstInt :: InterpretAst ranked
                => AstEnv ranked -> AstInt -> IntOf ranked
interpretAstInt env = \case
  AstIntVar var -> case EM.lookup var env of
    Just (AstEnvElemI i) -> i
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

interpretAstBool :: InterpretAst ranked
                 => AstEnv ranked -> AstBool -> BooleanOf (ranked () 0)
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
  :: forall ranked. InterpretAst ranked
  => AstEnv ranked
  -> DynamicExists AstDynamic -> DynamicExists (DynamicOf ranked)
interpretAstDynamicDummy env = \case
  DynamicExists @_ @r (AstRToD AstIota) ->
    DynamicExists $ ddummy @ranked @(ShapedOf ranked) @r
  DynamicExists (AstRToD w) -> DynamicExists $ dfromR $ interpretAst env w
  DynamicExists @_ @r (AstSToD AstIotaS) ->
    DynamicExists $ ddummy @ranked @(ShapedOf ranked) @r
  DynamicExists (AstSToD w) -> DynamicExists $ dfromS $ interpretAstS env w

interpretAstDomainsDummy
  :: forall ranked . InterpretAst ranked
  => AstEnv ranked -> AstDomains -> Domains (DynamicOf ranked)
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
     ( OS.Shape sh, shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped, InterpretAst ranked, GoodScalar r )
  => AstEnv ranked
  -> AstPrimalPartS r sh -> PrimalOf shaped r sh
interpretAstPrimalS env (AstPrimalPartS v1) = case v1 of
  AstDS u _-> interpretAstPrimalS env u
  _ -> sprimalPart $ interpretAstS env v1

interpretAstDualS
  :: forall ranked shaped sh r.
     ( OS.Shape sh, shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped, InterpretAst ranked, GoodScalar r )
  => AstEnv ranked
  -> AstDualPartS r sh -> DualOf shaped r sh
interpretAstDualS env (AstDualPartS v1) = case v1 of
  AstDS _ u'-> interpretAstDualS env u'
  _ -> sdualPart $ interpretAstS env v1

interpretAstS
  :: forall ranked shaped sh r.
     ( OS.Shape sh, shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped, InterpretAst ranked, GoodScalar r )
  => AstEnv ranked
  -> AstShaped r sh -> shaped r sh
interpretAstS env = \case
  AstVarS var -> case EM.lookup var env of
    Just (AstEnvElemS @_ @sh2 @r2 t) -> case sameShape @sh2 @sh of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> t
        _ -> error "interpretAstS: type mismatch"
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
  AstCastS v -> scast $ interpretAstS env v
  AstRToS v -> sfromR $ interpretAst env v
  AstConstS a -> sconstBare a
  AstConstantS a -> sconstant $ interpretAstPrimalS env a
  AstDS u u' ->
    let t1 = interpretAstPrimalS env u
        t2 = interpretAstDualS env u'
    in sD t1 t2
  AstLetDomainsS vars l v ->
    let l2 = interpretAstDomains env l
        f (varId, DynamicExists @_ @r2 d) =
          let sh2 = dshape @ranked d
          in OS.withShapeP sh2 $ \(Proxy @sh2) ->
            extendEnvS @ranked @(ShapedOf ranked) @r2 @sh2
                       (AstVarName varId) (sfromD d)
        env2 = V.foldr f env (V.zip vars l2)
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
  -> DynamicExists AstDynamic
  -> DynamicExists (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal AstRanked)
  -> DynamicExists AstDynamic
  -> DynamicExists (ADValClown AstDynamic) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array)
  -> DynamicExists AstDynamic
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstDomains
  -> Domains (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal AstRanked)
  -> AstDomains
  -> Domains (ADValClown AstDynamic) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (Flip OR.Array)
  -> AstDomains
  -> Domains OD.Array #-}

{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstInt
  -> CInt #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal AstRanked)
  -> AstInt
  -> AstInt #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (Flip OR.Array)
  -> AstInt
  -> CInt #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstBool
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal AstRanked)
  -> AstBool
  -> AstBool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array)
  -> AstBool
  -> Bool #-}

{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array)
  -> DynamicExists AstDynamic
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array)
  -> AstDomains
  -> Domains OD.Array #-}

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
  :: OpCodeInt -> [AstInt] -> AstInt #-}

{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [Bool] -> Bool #-}
{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [AstBool Double] -> AstBool #-}
{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [AstBool Float] -> AstBool #-}
-}

{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [Flip OR.Array Double n] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [Flip OR.Array Float n] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked Double n] -> AstBool #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked Float n] -> AstBool #-}

{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [CInt] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: OpCodeRel -> [AstInt] -> AstBool #-}
