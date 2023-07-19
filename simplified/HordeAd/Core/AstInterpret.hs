{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
-- | Interpretation of @Ast@ terms in an aribtrary @RankedTensor@ class instance..
module HordeAd.Core.AstInterpret
  ( InterpretAstR, InterpretAstS
  , interpretAstPrimal, interpretAst, interpretAstDomainsDummy
  , interpretAstPrimalS, interpretAstS
  , AstEnv, extendEnvS, extendEnvR, extendEnvDR
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Const
import           Data.Int (Int64)
import           Data.Kind (Type)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat)
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

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
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)

type AstEnv ranked = EM.EnumMap AstVarId (AstEnvElem ranked)

data AstEnvElem :: RankedTensorKind -> Type where
  AstEnvElemS :: (OS.Shape sh, GoodScalar r)
              => ShapedOf ranked r sh -> AstEnvElem ranked
deriving instance CRankedRNS ranked ShowDynamicOf
                  => Show (AstEnvElem ranked)

class (forall re ne she. (GoodScalar re, OS.Shape she)
       => c ranked re ne she)
      => CRankedRNS ranked c where
instance
      (forall re ne she. (GoodScalar re, OS.Shape she)
       => c ranked re ne she)
      => CRankedRNS ranked c where

class ( Show (DynamicOf ranked r)
      , Show (ranked r n)
      , Show (ShapedOf ranked r sh)
      , Show (IntOf ranked) ) => ShowDynamicOf ranked r n sh
instance
      ( Show (DynamicOf ranked r)
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

extendEnvR :: forall ranked r n.
              ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
              , KnownNat n, GoodScalar r )
           => AstVarName (Flip OR.Array r n) -> ranked r n
           -> AstEnv ranked -> AstEnv ranked
extendEnvR (AstVarName var) t =
  let sh2 = tshape t
  in OS.withShapeP (shapeToList sh2) $ \(Proxy :: Proxy sh2) ->
    gcastWith (unsafeCoerce Refl :: OS.Rank sh2 :~: n)
    $ extendEnvS (AstVarName var)
                 (sfromR @ranked @(ShapedOf ranked) @r @sh2 t)

extendEnvDR :: ConvertTensor ranked shaped
            => (AstDynamicVarName, DynamicExists (DynamicOf ranked))
            -> AstEnv ranked
            -> AstEnv ranked
extendEnvDR (AstDynamicVarName @sh @r var, DynamicExists @r2 d) =
  case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> extendEnvS (AstVarName @(Flip OS.Array r sh) var) (sfromD d)
    _ -> error "extendEnvDR: type mismatch"

extendEnvI :: ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => AstVarId -> IntOf ranked -> AstEnv ranked
           -> AstEnv ranked
extendEnvI var i = extendEnvR (AstVarName var) (tconstant i)

extendEnvVars :: forall ranked m.
                 ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
                 , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
              => AstVarList m -> IndexOf ranked m
              -> AstEnv ranked
              -> AstEnv ranked
extendEnvVars vars ix env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvVarsS :: forall ranked sh.
                  ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
                  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
               => AstVarListS sh -> IndexSh ranked sh
               -> AstEnv ranked
               -> AstEnv ranked
extendEnvVarsS vars ix env =
  let assocs = zip (ShapedList.sizedListToList vars)
                   (ShapedList.sizedListToList ix)
  in foldr (uncurry extendEnvI) env assocs

interpretLambdaI
  :: forall ranked n s r.
     ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked -> (AstVarId, AstRanked s r n)
  -> IntOf ranked
  -> ranked r n
{-# INLINE interpretLambdaI #-}
interpretLambdaI f env (var, ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIS
  :: forall ranked shaped sh n s r.
     ( RankedTensor ranked, ConvertTensor ranked shaped
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked -> AstShaped s r sh -> shaped r sh)
  -> AstEnv ranked -> (AstVarId, AstShaped s r sh)
  -> IntSh ranked n
  -> shaped r sh
{-# INLINE interpretLambdaIS #-}
interpretLambdaIS f env (var, ast) =
  \i -> f (extendEnvI var (ShapedList.unShapedNat i) env) ast

interpretLambdaIndex
  :: forall ranked s r m n.
     ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked -> (AstVarList m, AstRanked s r n)
  -> IndexOf ranked m
  -> ranked r n
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f env (vars, ast) =
  \ix -> f (extendEnvVars vars ix env) ast

interpretLambdaIndexS
  :: forall sh sh2 ranked shaped s r.
     ( RankedTensor ranked, ConvertTensor ranked shaped
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked -> AstShaped s r sh -> shaped r sh)
  -> AstEnv ranked -> (AstVarListS sh2, AstShaped s r sh)
  -> IndexSh ranked sh2
  -> shaped r sh
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f env (vars, ast) =
  \ix -> f (extendEnvVarsS vars ix env) ast

interpretLambdaIndexToIndex
  :: forall ranked m n.
     ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked -> AstInt -> IntOf ranked)
  -> AstEnv ranked -> (AstVarList m, AstIndex n)
  -> IndexOf ranked m
  -> IndexOf ranked n
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f env (vars, asts) =
  \ix -> f (extendEnvVars vars ix env) <$> asts

interpretLambdaIndexToIndexS
  :: forall ranked sh sh2.
     ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked -> AstInt -> IntOf ranked)
  -> AstEnv ranked -> (AstVarListS sh, AstIndexS sh2)
  -> IndexSh ranked sh
  -> IndexSh ranked sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f env (vars, asts) =
  \ix -> f (extendEnvVarsS vars ix env) <$> asts

class ( Integral (ShapedOf ranked r y) )
      => IsIntegralShapedOf ranked r y where
instance
      ( Integral (ShapedOf ranked r y) )
      => IsIntegralShapedOf ranked r y where

class (forall y. KnownNat y => c (ranked r y))
      => IRanked ranked r c where
instance
      (forall y. KnownNat y => c (ranked r y))
      => IRanked ranked r c where

class (forall y. OS.Shape y => c ranked r y)
      => YRanked ranked r c where
instance
      (forall y. OS.Shape y => c ranked r y)
      => YRanked ranked r c where

type InterpretAstR ranked =
  ( RankedOf (PrimalOf ranked) ~ PrimalOf ranked
  , PrimalOf ranked ~ RankedOf (PrimalOf ranked)
  , CRankedRNS ranked ShowDynamicOf
  , IfF ranked, IfF (ShapedOf ranked), IfF (PrimalOf ranked)
  , EqF ranked, EqF (ShapedOf ranked), EqF (PrimalOf ranked)
  , OrdF ranked, OrdF (ShapedOf ranked), OrdF (PrimalOf ranked)
  , Boolean (BoolOf ranked)
  , BoolOf ranked ~ BoolOf (ShapedOf ranked)
  , BoolOf ranked ~ BoolOf (PrimalOf ranked)
  , BoolOf ranked ~ BoolOf (PrimalOf (ShapedOf ranked))
  )

type InterpretAstS shaped =
  ( RankedOf (PrimalOf shaped) ~ PrimalOf (RankedOf shaped)
  , PrimalOf (RankedOf shaped) ~ RankedOf (PrimalOf shaped)
  , IfF shaped, IfF (RankedOf shaped), IfF (PrimalOf shaped)
  , EqF shaped, EqF (RankedOf shaped), EqF (PrimalOf shaped)
  , OrdF shaped, OrdF (RankedOf shaped), OrdF (PrimalOf shaped)
  , Boolean (BoolOf shaped)
  , BoolOf shaped ~ BoolOf (RankedOf shaped)
  , BoolOf shaped ~ BoolOf (PrimalOf shaped)
  )

type InterpretAst ranked shaped =
  ( shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped
  , RankedTensor ranked, RankedTensor (PrimalOf ranked)
  , ShapedTensor shaped, ShapedTensor (PrimalOf shaped)
  , ConvertTensor ranked shaped
  , ConvertTensor (PrimalOf ranked) (PrimalOf shaped)
  , InterpretAstR ranked
  , InterpretAstS shaped
  , IRanked ranked Int64 Integral
  , YRanked ranked Int64 IsIntegralShapedOf
  )

-- Strict environment and strict ADVal and Delta make this is hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall ranked shaped n r.
     (KnownNat n, InterpretAst ranked shaped, GoodScalar r)
  => AstEnv ranked
  -> AstRanked AstPrimal r n -> PrimalOf ranked r n
interpretAstPrimal env v1 = case v1 of
  AstPrimalPart (AstD u _) -> interpretAstPrimal env u
  AstCond b a1 a2 ->  -- this avoids multiple ifF expansions via ifB(ADVal)
    let b1 = interpretAstBool env b
        t2 = interpretAstPrimal env a1
        t3 = interpretAstPrimal env a2
    in ifF b1 t2 t3  -- this is ifF from PrimalOf ranked
  _ -> tprimalPart $ interpretAst env v1

interpretAstDual
  :: forall ranked shaped n r.
     (KnownNat n, InterpretAst ranked shaped, GoodScalar r)
  => AstEnv ranked
  -> AstRanked AstDual r n -> DualOf ranked r n
interpretAstDual env v1 = case v1 of
  AstDualPart (AstD _ u') -> interpretAstDual env u'
  _ -> tdualPart $ interpretAst env v1

interpretAst
  :: forall ranked shaped n s r.
     (KnownNat n, InterpretAst ranked shaped, GoodScalar r, AstSpan s)
  => AstEnv ranked
  -> AstRanked s r n -> ranked r n
interpretAst env = \case
  AstVar sh var -> case EM.lookup var env of
    Just (AstEnvElemS @sh2 @r2 t) ->
      if shapeToList sh == OS.shapeT @sh2 then
        gcastWith (unsafeCoerce Refl :: OS.Rank sh2 :~: n)
        $ case testEquality (typeRep @r) (typeRep @r2) of
            Just Refl -> tfromS t
            _ -> error "interpretAst: type mismatch"
      else error "interpretAst: wrong shape in environment"
    Nothing -> error $ "interpretAst: unknown variable " ++ show var
                       ++ " in environment " ++ show env
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
  AstNm TimesOp [v, AstReshape _ (AstReplicate @m _ s)]
   -- TODO: also handle nested AstReplicate to prevent executing them
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env v
            t2 = interpretAst env s
        in tscaleByScalar0 t2 t1
  AstNm TimesOp [v, AstReplicate @m _ s]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let t1 = interpretAst env v
            t2 = interpretAst env s
        in tscaleByScalar0 t2 t1
  -}
  AstNm TimesOp [v, AstLet var u (AstReshape sh (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        -- The intVarInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env
          (AstLet var u (AstNm TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstNm TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env
          (AstLet var u (AstNm TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstNm TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env
          (AstLet var u (AstNm TimesOp [v, AstReplicate @m k s]))
  AstNm TimesOp [v, u] ->
    let v5 = interpretAst env v
        u5 = interpretAst env u
    in v5 `tmult` u5
  AstNm opCode args ->
    let args2 = interpretAst env <$> args
    in interpretAstNm opCode args2
  AstOp opCode args ->
    let args2 = interpretAst env <$> args
    in interpretAstOp opCode args2
  AstOpIntegral opCode args ->
    let args2 = interpretAst env <$> args
    in interpretAstOpIntegral opCode args2
  AstSumOfList args ->
    let args2 = interpretAst env <$> args
    in tsumOfList args2
  AstIota -> error "interpretAst: bare AstIota, most likely a bug"
  AstIndex AstIota (i :. ZI) ->
    tfromIntegral $ tconstant $ interpretAstPrimal env i
  AstIndex v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAstPrimal env <$> ix
    in tindex v2 ix3
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstSum (AstNm TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstTranspose uperm u ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstNm TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstNm TimesOp [ AstTranspose tperm t
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstNm TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstNm TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstNm TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ]))))
  AstSum (AstNm TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstReplicate uk u) ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstNm TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstNm TimesOp [ AstTranspose tperm (AstReplicate tk t)
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstNm TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstNm TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstNm TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ]))))
  AstSum v@(AstNm TimesOp [ AstTranspose tperm (AstReplicate _tk t)
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
  AstSum (AstNm TimesOp [t, u])
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstNm TimesOp [t, u]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstNm TimesOp [t, u]))  -- TODO: generalize
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
        f2 = interpretLambdaIndexToIndex interpretAstPrimal env (vars, ix)
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
    -- AstConstant not needed, because when AstIota is introduced
    -- by the user, AstConstant is wrapped over it.
    interpretAst env
    $ AstConst $ OR.fromList [n] $ map fromIntegral [i .. i + n - 1]
  AstSlice i n v -> tslice i n (interpretAst env v)
  AstReverse v -> treverse (interpretAst env v)
  AstTranspose perm v -> ttranspose perm $ interpretAst env v
  AstReshape sh v -> treshape sh (interpretAst env v)
  -- These are only needed for tests that don't vectorize Ast.
  AstBuild1 k (var, AstSum (AstNm TimesOp [t, AstIndex
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstNm TimesOp [t, AstIndex
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
                                    (vars, tfromIntegral i))
  AstGather sh v (vars, ix) ->
    let t1 = interpretAst env v
        f2 = interpretLambdaIndexToIndex interpretAstPrimal env (vars, ix)
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
  AstFromIntegral v -> tfromIntegral $ tconstant $ interpretAstPrimal env v
  AstSToR v -> tfromS $ interpretAstS env v
  AstConst a -> tconstBare a
  AstConstant a -> tconstant $ interpretAstPrimal env a
  AstPrimalPart a -> interpretAst env a  -- TODO
  AstDualPart a -> interpretAst env a  -- TODO
  AstD u u' ->
    let t1 = interpretAstPrimal env u
        t2 = interpretAstDual env u'
    in tD t1 t2
  AstLetDomains vars l v ->
    let l2 = interpretAstDomains env l
        f (varId, DynamicExists @r2 d) =
          let sh2 = dshape @ranked d
          in OS.withShapeP sh2 $ \(Proxy :: Proxy sh2) ->
            extendEnvS @ranked @shaped @r2 @sh2
                       (AstVarName varId) (sfromD d)
        env2 = V.foldr f env (V.zip vars l2)
    in interpretAst env2 v
  AstCond b a1 a2 ->
    let b1 = interpretAstBool env b
        t2 = interpretAst env a1
        t3 = interpretAst env a2
    in ifF b1 t2 t3
  AstFloor v -> tfloor $ tconstant $ interpretAstPrimal env v
  AstMinIndex v -> tminIndex $ tconstant $ interpretAstPrimal env v
  AstMaxIndex v -> tmaxIndex $ tconstant $ interpretAstPrimal env v

interpretAstDynamic
  :: forall ranked shaped s. (InterpretAst ranked shaped, AstSpan s)
  => AstEnv ranked -> DynamicExists (AstDynamic s)
  -> DynamicExists (DynamicOf ranked)
interpretAstDynamic env = \case
  DynamicExists (AstRToD w) -> DynamicExists $ dfromR $ interpretAst env w
  DynamicExists (AstSToD w) -> DynamicExists $ dfromS $ interpretAstS env w

interpretAstDomains
  :: forall ranked shaped s. (InterpretAst ranked shaped, AstSpan s)
  => AstEnv ranked -> AstDomains s -> Domains (DynamicOf ranked)
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

interpretAstBool :: InterpretAst ranked shaped
                 => AstEnv ranked -> AstBool -> BoolOf ranked
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

interpretAstDynamicDummy
  :: forall ranked shaped s. (InterpretAst ranked shaped, AstSpan s)
  => AstEnv ranked
  -> DynamicExists (AstDynamic s) -> DynamicExists (DynamicOf ranked)
interpretAstDynamicDummy env = \case
  DynamicExists @r (AstRToD AstIota) ->
    DynamicExists $ ddummy @ranked @shaped @r
  DynamicExists (AstRToD w) -> DynamicExists $ dfromR $ interpretAst env w
  DynamicExists @r (AstSToD AstIotaS) ->
    DynamicExists $ ddummy @ranked @shaped @r
  DynamicExists (AstSToD w) -> DynamicExists $ dfromS $ interpretAstS env w

interpretAstDomainsDummy
  :: forall ranked shaped s. (InterpretAst ranked shaped, AstSpan s)
  => AstEnv ranked -> AstDomains s -> Domains (DynamicOf ranked)
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
interpretAstNm :: Num a
               => OpCodeNum -> [a] -> a
{-# INLINE interpretAstNm #-}
interpretAstNm MinusOp [u, v] = u - v
interpretAstNm NegateOp [u] = negate u
interpretAstNm AbsOp [u] = abs u
interpretAstNm SignumOp [u] = signum u
interpretAstNm opCode args =
  error $ "interpretAstNm: wrong number of arguments"
          ++ show (opCode, length args)

interpretAstOp :: RealFloat a
               => OpCode -> [a] -> a
{-# INLINE interpretAstOp #-}
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
interpretAstOp opCode args =
  error $ "interpretAstOp: wrong number of arguments"
          ++ show (opCode, length args)

interpretAstOpIntegral :: Integral a
                       => OpCodeIntegral -> [a] -> a
{-# INLINE interpretAstOpIntegral #-}
interpretAstOpIntegral QuotOp [u, v] = quot u v
interpretAstOpIntegral RemOp [u, v] = rem u v
interpretAstOpIntegral opCode args =
  error $ "interpretAstOpIntegral: wrong number of arguments"
          ++ show (opCode, length args)

interpretAstBoolOp :: Boolean b
                   => OpCodeBool -> [b] -> b
{-# INLINE interpretAstBoolOp #-}
interpretAstBoolOp NotOp [u] = notB u
interpretAstBoolOp AndOp [u, v] = u &&* v
interpretAstBoolOp OrOp [u, v] = u ||* v
interpretAstBoolOp opCodeBool args =
  error $ "interpretAstBoolOp: wrong number of arguments"
          ++ show (opCodeBool, length args)

interpretAstRelOp :: (EqF f, OrdF f, GoodScalar r, HasSingletonDict y)
                  => OpCodeRel -> [f r y] -> BoolOf f
interpretAstRelOp EqOp [u, v] = u ==. v
interpretAstRelOp NeqOp [u, v] = u /=. v
interpretAstRelOp LeqOp [u, v] = u <=. v
interpretAstRelOp GeqOp [u, v] = u >=. v
interpretAstRelOp LsOp [u, v] = u <. v
interpretAstRelOp GtOp [u, v] = u >. v
interpretAstRelOp opCodeRel args =
  error $ "interpretAstRelOp: wrong number of arguments"
          ++ show (opCodeRel, length args)

interpretAstPrimalS
  :: forall ranked shaped sh r.
     (OS.Shape sh, InterpretAst ranked shaped, GoodScalar r)
  => AstEnv ranked
  -> AstShaped AstPrimal r sh -> PrimalOf shaped r sh
interpretAstPrimalS env v1 = case v1 of
  AstPrimalPartS (AstDS u _) -> interpretAstPrimalS env u
  AstCondS b a1 a2 ->  -- this avoids multiple ifF expansions via ifB(ADVal)
    let b1 = interpretAstBool env b
        t2 = interpretAstPrimalS env a1
        t3 = interpretAstPrimalS env a2
    in ifF b1 t2 t3  -- this is ifF from PrimalOf ranked
  _ -> sprimalPart $ interpretAstS env v1

interpretAstDualS
  :: forall ranked shaped sh r.
     (OS.Shape sh, InterpretAst ranked shaped, GoodScalar r)
  => AstEnv ranked
  -> AstShaped AstDual r sh -> DualOf shaped r sh
interpretAstDualS env v1 = case v1 of
  AstDualPartS (AstDS _ u') -> interpretAstDualS env u'
  _ -> sdualPart $ interpretAstS env v1

interpretAstS
  :: forall ranked shaped sh s r.
     (OS.Shape sh, InterpretAst ranked shaped, GoodScalar r, AstSpan s)
  => AstEnv ranked
  -> AstShaped s r sh -> shaped r sh
interpretAstS env = \case
  AstVarS var -> case EM.lookup var env of
    Just (AstEnvElemS @sh2 @r2 t) -> case sameShape @sh2 @sh of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> t
        _ -> error "interpretAstS: type mismatch"
      Nothing -> error "interpretAstS: wrong shape in environment"
    Nothing -> error $ "interpretAstS: unknown variable " ++ show var
  AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstS env u
        env2 w = extendEnvS (AstVarName var) w env
    in slet t (\w -> interpretAstS (env2 w) v)
  AstLetADShareS{} -> error "interpretAst: AstLetADShare"
{- TODO:
  AstNm TimesOp [v, AstLet var u (AstReshape sh (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        -- The intVarInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env
          (AstLet var u (AstNm TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstNm TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env
          (AstLet var u (AstNm TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstNm TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env
          (AstLet var u (AstNm TimesOp [v, AstReplicate @m k s]))
-}
  AstNmS TimesOp [v, u] ->
    let v5 = interpretAstS env v
        u5 = interpretAstS env u
    in v5 `smult` u5
  AstNmS opCode args ->
    let args2 = interpretAstS env <$> args
    in interpretAstNm opCode args2
  AstOpS opCode args ->
    let args2 = interpretAstS env <$> args
    in interpretAstOp opCode args2
  AstOpIntegralS opCode args ->
    let args2 = interpretAstS env <$> args
    in interpretAstOpIntegral opCode args2
  AstSumOfListS args ->
    let args2 = interpretAstS env <$> args
    in ssumOfList args2
  AstIotaS -> siota  -- TODO: siotaBare might be needed to avoid AstConstant
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
  AstSum (AstNm TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstTranspose uperm u ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstNm TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstNm TimesOp [ AstTranspose tperm t
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstNm TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ])))
  AstSum (AstNm TimesOp [ AstLet vart vt (AstTranspose tperm t)
                        , AstLet varu vu (AstTranspose uperm u) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstNm TimesOp [ AstTranspose tperm t
                                , AstTranspose uperm u ]))))
  AstSum (AstNm TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstReplicate uk u) ]) ->
    interpretAst env
      (AstLet vart vt
         (AstSum (AstNm TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstNm TimesOp [ AstTranspose tperm (AstReplicate tk t)
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet varu vu
         (AstSum (AstNm TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ])))
  AstSum (AstNm TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
                        , AstTranspose uperm (AstLet varu vu
                                               (AstReplicate uk u)) ]) ->
    interpretAst env
      (AstLet vart vt (AstLet varu vu
         (AstSum (AstNm TimesOp [ AstTranspose tperm (AstReplicate tk t)
                                , AstTranspose uperm (AstReplicate uk u) ]))))
  AstSum v@(AstNm TimesOp [ AstTranspose tperm (AstReplicate _tk t)
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
  AstSum (AstNm TimesOp [t, u])
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstNm TimesOp [t, u]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstNm TimesOp [t, u]))  -- TODO: generalize
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
        f2 = interpretLambdaIndexToIndexS interpretAstPrimal env (vars, ix)
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
  AstBuild1 k (var, AstSum (AstNm TimesOp [t, AstIndex
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstNm TimesOp [t, AstIndex
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
  AstGatherS @sh2 AstIotaS (vars, (i :$: ZSH)) ->
    gcastWith (unsafeCoerce Refl :: OS.Take (OS.Rank sh) sh :~: sh)
    $ gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: sh2 :~: sh)
        -- transitivity of type equality doesn't work, by design,
        -- so this direct cast is needed instead of more basic laws
    $ sbuild @shaped @r @(OS.Rank sh)
             (interpretLambdaIndexS
                interpretAstS env
                (vars, sfromIntegral $ sfromR i))
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
  AstCastS v -> scast $ interpretAstS env v
  AstFromIntegralS v -> sfromIntegral $ sconstant $ interpretAstPrimalS env v
  AstRToS v -> sfromR $ interpretAst env v
  AstConstS a -> sconstBare a
  AstConstantS a -> sconstant $ interpretAstPrimalS env a
  AstPrimalPartS a -> interpretAstS env a  -- TODO
  AstDualPartS a -> interpretAstS env a  -- TODO
  AstDS u u' ->
    let t1 = interpretAstPrimalS env u
        t2 = interpretAstDualS env u'
    in sD t1 t2
  AstLetDomainsS vars l v ->
    let l2 = interpretAstDomains env l
        f (varId, DynamicExists @r2 d) =
          let sh2 = dshape @ranked d
          in OS.withShapeP sh2 $ \(Proxy :: Proxy sh2) ->
            extendEnvS @ranked @shaped @r2 @sh2
                       (AstVarName varId) (sfromD d)
        env2 = V.foldr f env (V.zip vars l2)
    in interpretAstS env2 v
  AstCondS b a1 a2 ->
    let b1 = interpretAstBool env b
        t2 = interpretAstS env a1
        t3 = interpretAstS env a2
    in ifF b1 t2 t3
  AstFloorS v -> sfloor $ sconstant $ interpretAstPrimalS env v
  AstMinIndexS v -> sminIndex $ sconstant $ interpretAstPrimalS env v
  AstMaxIndexS v -> smaxIndex $ sconstant $ interpretAstPrimalS env v




{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked AstPrimal Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked AstPrimal Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked AstPrimal))
  -> AstRanked AstPrimal Double n
  -> AstRanked AstPrimal Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked AstPrimal))
  -> AstRanked AstPrimal Float n
  -> AstRanked AstPrimal Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked AstPrimal Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked AstPrimal Float n
  -> Flip OR.Array Float n #-}

{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked AstDual Double n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked AstDual Float n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked AstPrimal))
  -> AstRanked AstDual Double n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked AstPrimal) (AstShaped AstPrimal)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked AstPrimal))
  -> AstRanked AstDual Float n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked AstPrimal) (AstShaped AstPrimal)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked AstDual Double n
  -> DummyDual Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked AstDual Float n
  -> DummyDual Float n #-}

{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked AstPrimal Double n
  -> ADVal (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked AstPrimal Float n
  -> ADVal (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked AstPrimal))
  -> AstRanked AstPrimal Double n
  -> ADVal (AstRanked AstPrimal) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked AstPrimal))
  -> AstRanked AstPrimal Float n
  -> ADVal (AstRanked AstPrimal) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked AstPrimal Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked AstPrimal Float n
  -> Flip OR.Array Float n #-}

{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked AstFull Double n
  -> ADVal (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked AstFull Float n
  -> ADVal (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked AstPrimal))
  -> AstRanked AstFull Double n
  -> ADVal (AstRanked AstPrimal) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked AstPrimal))
  -> AstRanked AstFull Float n
  -> ADVal (AstRanked AstPrimal) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked AstFull Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked AstFull Float n
  -> Flip OR.Array Float n #-}

{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Flip OR.Array))
  -> DynamicExists (AstDynamic AstPrimal)
  -> DynamicExists (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (AstRanked AstPrimal))
  -> DynamicExists (AstDynamic AstPrimal)
  -> DynamicExists (ADValClown (AstDynamic AstPrimal)) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array)
  -> DynamicExists (AstDynamic AstPrimal)
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Flip OR.Array))
  -> DynamicExists (AstDynamic AstFull)
  -> DynamicExists (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (AstRanked AstPrimal))
  -> DynamicExists (AstDynamic AstFull)
  -> DynamicExists (ADValClown (AstDynamic AstPrimal)) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array)
  -> DynamicExists (AstDynamic AstFull)
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstDomains AstPrimal
  -> Domains (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (AstRanked AstPrimal))
  -> AstDomains AstPrimal
  -> Domains (ADValClown (AstDynamic AstPrimal)) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (Flip OR.Array)
  -> AstDomains AstPrimal
  -> Domains OD.Array #-}

{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstDomains AstFull
  -> Domains (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (AstRanked AstPrimal))
  -> AstDomains AstFull
  -> Domains (ADValClown (AstDynamic AstPrimal)) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (Flip OR.Array)
  -> AstDomains AstFull
  -> Domains OD.Array #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstBool
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRanked AstPrimal))
  -> AstBool
  -> AstBool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array)
  -> AstBool
  -> Bool #-}

{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array)
  -> DynamicExists (AstDynamic AstPrimal)
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array)
  -> AstDomains AstPrimal
  -> Domains OD.Array #-}

{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array)
  -> DynamicExists (AstDynamic AstFull)
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array)
  -> AstDomains AstFull
  -> Domains OD.Array #-}

{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n => OpCodeRel -> [Flip OR.Array Double n] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n => OpCodeRel -> [Flip OR.Array Float n] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n => OpCodeRel -> [Flip OR.Array Int64 n] -> Bool #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked AstPrimal Double n] -> AstBool #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked AstPrimal Float n] -> AstBool #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked AstPrimal Int64 n] -> AstBool #-}
-- AstFull not needed, because relations are computed on primal parts

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
{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [Bool] -> Bool #-}
{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [AstBool Double] -> AstBool #-}
{-# SPECIALIZE interpretAstBoolOp
  :: OpCodeBool -> [AstBool Float] -> AstBool #-}
-}
