{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
-- | Interpretation of AST terms in an aribtrary @RankedTensor@
-- and/or @ShapedTensor@ class instance.
module HordeAd.Core.AstInterpret
  ( -- * The environment and operations for extending it
    AstEnv, extendEnvS, extendEnvR, extendEnvDR, extendEnvDS
    -- * AST interpretation functions
  , interpretAstPrimal, interpretAst, interpretAstDomainsDummy
  , interpretAstPrimalS, interpretAstS
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
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
import           GHC.TypeLits (KnownNat, SomeNat (..), sameNat, someNatVal)
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.Delta
import           HordeAd.Core.DualNumber
import           HordeAd.Core.TensorADVal
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)
import           HordeAd.Util.ShapedList (ShapedList (..))
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex
import           HordeAd.Util.SizedList

-- * The environment and operations for extending it

-- | The environment that keeps variables values during interpretation
type AstEnv ranked shaped = EM.EnumMap AstId (AstEnvElem ranked shaped)

data AstEnvElem :: RankedTensorKind -> ShapedTensorKind -> Type where
  AstEnvElemR :: (KnownNat n, GoodScalar r)
              => ranked r n -> AstEnvElem ranked shaped
  AstEnvElemS :: (OS.Shape sh, GoodScalar r)
              => shaped r sh -> AstEnvElem ranked shaped
deriving instance (CRanked ranked Show, CShaped shaped Show)
                  => Show (AstEnvElem ranked shaped)

-- An informal invariant: if s is FullSpan, ranked is dual numbers,
-- and if s is PrimalSpan, ranked is their primal part.
-- The same for all the function below.
extendEnvR :: forall ranked shaped r n s.
              (KnownNat n, GoodScalar r)
           => AstVarName s AstRanked r n -> ranked r n
           -> AstEnv ranked shaped -> AstEnv ranked shaped
extendEnvR (AstVarName var) t =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show var)
                   (astVarIdToAstId var) (AstEnvElemR t)

extendEnvS :: forall ranked shaped r sh s.
              (OS.Shape sh, GoodScalar r)
           => AstVarName s AstShaped r sh -> shaped r sh
           -> AstEnv ranked shaped -> AstEnv ranked shaped
extendEnvS (AstVarName var) t =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvS: duplicate " ++ show var)
                   (astVarIdToAstId var) (AstEnvElemS t)

extendEnvDR :: forall ranked shaped s. ConvertTensor ranked shaped
            => ( AstDynamicVarName s AstRanked
               , DynamicExists (DynamicOf ranked) )
            -> AstEnv ranked shaped
            -> AstEnv ranked shaped
extendEnvDR (AstDynamicVarName @_ @sh @r @y var, DynamicExists @r2 d) =
  case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl ->
      let n = length $ OS.shapeT @sh
      in case someNatVal $ toInteger n of
        Just (SomeNat @n _) -> gcastWith (unsafeCoerce Refl :: n :~: y) $
                               extendEnvR var (tfromD d)
        Nothing -> error "extendEnvDR: impossible someNatVal error"
    _ -> error "extendEnvDR: type mismatch"

extendEnvDS :: ConvertTensor ranked shaped
            => ( AstDynamicVarName s AstShaped
               , DynamicExists (DynamicOf ranked) )
            -> AstEnv ranked shaped
            -> AstEnv ranked shaped
extendEnvDS (AstDynamicVarName @_ @sh @r @y var, DynamicExists @r2 d) =
  case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> gcastWith (unsafeCoerce Refl :: sh :~: y) $
                 extendEnvS var (sfromD d)
    _ -> error "extendEnvDS: type mismatch"

extendEnvI :: ( RankedTensor ranked
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => IntVarName -> IntOf ranked -> AstEnv ranked shaped
           -> AstEnv ranked shaped
extendEnvI var i = extendEnvR var (tconstant i)

extendEnvVars :: forall ranked shaped m.
                 ( RankedTensor ranked
                 , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
              => AstVarList m -> IndexOf ranked m
              -> AstEnv ranked shaped
              -> AstEnv ranked shaped
extendEnvVars vars ix env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvVarsS :: forall ranked shaped sh.
                  ( RankedTensor ranked
                  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
               => AstVarListS sh -> IndexSh ranked sh
               -> AstEnv ranked shaped
               -> AstEnv ranked shaped
extendEnvVarsS vars ix env =
  let assocs = zip (ShapedList.sizedListToList vars)
                   (ShapedList.sizedListToList ix)
  in foldr (uncurry extendEnvI) env assocs


-- * Interpretation of bindings

interpretLambdaI
  :: forall ranked shaped n s r.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked shaped -> (IntVarName, AstRanked s r n)
  -> IntOf ranked
  -> ranked r n
{-# INLINE interpretLambdaI #-}
interpretLambdaI f env (var, ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIS
  :: forall ranked shaped sh n s r.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstShaped s r sh -> shaped r sh)
  -> AstEnv ranked shaped -> (IntVarName, AstShaped s r sh)
  -> IntSh ranked n
  -> shaped r sh
{-# INLINE interpretLambdaIS #-}
interpretLambdaIS f env (var, ast) =
  \i -> f (extendEnvI var (ShapedList.unShapedNat i) env) ast

interpretLambdaIndex
  :: forall ranked shaped s r m n.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked shaped -> (AstVarList m, AstRanked s r n)
  -> IndexOf ranked m
  -> ranked r n
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f env (vars, ast) =
  \ix -> f (extendEnvVars vars ix env) ast

interpretLambdaIndexS
  :: forall sh sh2 ranked shaped s r.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstShaped s r sh -> shaped r sh)
  -> AstEnv ranked shaped -> (AstVarListS sh2, AstShaped s r sh)
  -> IndexSh ranked sh2
  -> shaped r sh
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f env (vars, ast) =
  \ix -> f (extendEnvVarsS vars ix env) ast

interpretLambdaIndexToIndex
  :: forall ranked shaped m n.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstInt -> IntOf ranked)
  -> AstEnv ranked shaped -> (AstVarList m, AstIndex n)
  -> IndexOf ranked m
  -> IndexOf ranked n
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f env (vars, asts) =
  \ix -> f (extendEnvVars vars ix env) <$> asts

interpretLambdaIndexToIndexS
  :: forall ranked shaped sh sh2.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstInt -> IntOf ranked)
  -> AstEnv ranked shaped -> (AstVarListS sh, AstIndexS sh2)
  -> IndexSh ranked sh
  -> IndexSh ranked sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f env (vars, asts) =
  \ix -> f (extendEnvVarsS vars ix env) <$> asts


-- * AST interpretation functions

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
interpretAstPrimal env v1 = case v1 of
  AstPrimalPart (AstD u _) -> interpretAstPrimal env u
  AstPrimalPart (AstConstant u) -> interpretAstPrimal env u
  AstPrimalPart t -> tprimalPart $ interpretAst env t
  AstCond b a1 a2 ->  -- this avoids multiple ifF expansions via ifB(ADVal)
    let b1 = interpretAstBool env b
        t2 = interpretAstPrimal env a1
        t3 = interpretAstPrimal env a2
    in ifF b1 t2 t3  -- this is ifF from PrimalOf ranked
  _ -> tprimalPart $ interpretAst env v1

interpretAstDual
  :: forall ranked shaped n r.
     (KnownNat n, ADReadyBoth ranked shaped, GoodScalar r)
  => AstEnv ranked shaped
  -> AstRanked DualSpan r n -> DualOf ranked r n
interpretAstDual env v1 = case v1 of
  AstDualPart (AstD _ u') -> interpretAstDual env u'
  AstDualPart t -> tdualPart $ interpretAst env t
  _ -> tdualPart $ interpretAst env v1

interpretAst
  :: forall ranked shaped n s r.
     (KnownNat n, ADReadyBoth ranked shaped, GoodScalar r, AstSpan s)
  => AstEnv ranked shaped
  -> AstRanked s r n -> ranked r n
interpretAst env = \case
  AstVar sh (AstVarName var) -> case EM.lookup (astVarIdToAstId var) env of
    Just (AstEnvElemR @n2 @r2 t) -> case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> assert (tshape t == sh) t
        _ -> error "interpretAst: type mismatch"
      _ -> error "interpretAst: wrong shape in environment"
    Just{} -> error "interpretAst: wrong tensor kind in environment"
    Nothing -> error $ "interpretAst: unknown variable " ++ show var
                       ++ " in environment " ++ show env
  AstLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAst env u
        env2 w = extendEnvR var w env
    in tlet t (\w -> interpretAst (env2 w) v)
  AstLetADShare{} -> error "interpretAst: AstLetADShare"
  AstCond b a1 a2 ->
    let b1 = interpretAstBool env b
        t2 = interpretAst env a1
        t3 = interpretAst env a2
    in ifF b1 t2 t3
  AstMinIndex v -> tminIndex $ tconstant $ interpretAstPrimal env v
  AstMaxIndex v -> tmaxIndex $ tconstant $ interpretAstPrimal env v
  AstFloor v -> tfloor $ tconstant $ interpretAstPrimal env v
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
    tfromIntegral $ tconstant $ interpretAstPrimal env i
  AstIndex v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAstPrimal env <$> ix
    in tindex v2 ix3
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
  AstSum (AstN2 TimesOp t u)
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstN2 TimesOp t u))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstN2 TimesOp t u))  -- TODO: generalize
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
  AstBuild1 k (var, AstSum (AstN2 TimesOp t (AstIndex
                                               u (AstIntVar var2 :. ZI))))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstN2 TimesOp t (AstIndex
                                                 u (AstIntVar var2 :. ZI)))))
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
  AstGather sh AstIota (vars, i :. ZI) ->
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
  AstConst a -> tconst a
  AstSToR v -> tfromS $ interpretAstS env v
  AstConstant a -> tconstant $ interpretAstPrimal env a
  AstPrimalPart a -> interpretAst env a
    -- This is correct, because @s@ must be @PrimalSpan@ and so @ranked@ must
    -- be morally a primal part of the same AST interpreted with @FullSpan@
    -- and so the result is a primal part, despite the appearances.
    -- This whole notation abuse is for user comfort (less @PrimalOf@
    -- in the tensor classes) and to avoid repeating the @interpretAst@ code
    -- in @interpretAstPrimal@. TODO: make this sane.
  AstDualPart a -> interpretAst env a
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

interpretAstDynamic
  :: forall ranked shaped s. (ADReadyBoth ranked shaped, AstSpan s)
  => AstEnv ranked shaped -> DynamicExists (AstDynamic s)
  -> DynamicExists (DynamicOf ranked)
interpretAstDynamic env = \case
  DynamicExists (AstRToD w) -> DynamicExists $ dfromR $ interpretAst env w
  DynamicExists (AstSToD w) -> DynamicExists $ dfromS $ interpretAstS env w

interpretAstDomains
  :: forall ranked shaped s. (ADReadyBoth ranked shaped, AstSpan s)
  => AstEnv ranked shaped -> AstDomains s -> Domains (DynamicOf ranked)
interpretAstDomains env = \case
  AstDomains l -> interpretAstDynamic env <$> l
  AstDomainsLet var u v ->
    let t = interpretAst env u
        env2 = extendEnvR var t env
    in interpretAstDomains env2 v
      -- TODO: preserve let, as in AstLet case
  AstDomainsLetS var u v ->
    let t = interpretAstS env u
        env2 = extendEnvS var t env
    in interpretAstDomains env2 v
      -- TODO: preserve let, as in AstLet case

interpretAstBool :: ADReadyBoth ranked shaped
                 => AstEnv ranked shaped -> AstBool -> BoolOf ranked
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
  :: forall ranked shaped s. (ADReadyBoth ranked shaped, AstSpan s)
  => AstEnv ranked shaped
  -> DynamicExists (AstDynamic s) -> DynamicExists (DynamicOf ranked)
interpretAstDynamicDummy env = \case
  DynamicExists @r (AstRToD AstIota) ->
    DynamicExists $ ddummy @ranked @shaped @r
  DynamicExists (AstRToD w) -> DynamicExists $ dfromR $ interpretAst env w
  DynamicExists @r (AstSToD AstIotaS) ->
    DynamicExists $ ddummy @ranked @shaped @r
  DynamicExists (AstSToD w) -> DynamicExists $ dfromS $ interpretAstS env w

interpretAstDomainsDummy
  :: forall ranked shaped s. (ADReadyBoth ranked shaped, AstSpan s)
  => AstEnv ranked shaped -> AstDomains s -> Domains (DynamicOf ranked)
interpretAstDomainsDummy env = \case
  AstDomains l -> interpretAstDynamicDummy env <$> l
  AstDomainsLet var u v ->
    let t = interpretAst env u
        env2 = extendEnvR var t env
    in interpretAstDomainsDummy env2 v
      -- TODO: preserve let, as in AstLet case
  AstDomainsLetS var u v ->
    let t = interpretAstS env u
        env2 = extendEnvS var t env
    in interpretAstDomainsDummy env2 v
      -- TODO: preserve let, as in AstLet case

-- TODO: when the code again tests with GHC >= 9.6, check whether
-- these INLINEs are still needed (removal causes 10% slowdown ATM).
interpretAstN1 :: Num a
               => OpCodeNum1 -> a -> a
{-# INLINE interpretAstN1 #-}
interpretAstN1 NegateOp u = negate u
interpretAstN1 AbsOp u = abs u
interpretAstN1 SignumOp u = signum u

interpretAstN2 :: Num a
               => OpCodeNum2 -> a -> a -> a
{-# INLINE interpretAstN2 #-}
interpretAstN2 MinusOp u v = u - v
interpretAstN2 TimesOp u v = u * v

interpretAstR1 :: RealFloat a
               => OpCode1 -> a -> a
{-# INLINE interpretAstR1 #-}
interpretAstR1 RecipOp u = recip u
interpretAstR1 ExpOp u = exp u
interpretAstR1 LogOp u = log u
interpretAstR1 SqrtOp u = sqrt u
interpretAstR1 SinOp u = sin u
interpretAstR1 CosOp u = cos u
interpretAstR1 TanOp u = tan u
interpretAstR1 AsinOp u = asin u
interpretAstR1 AcosOp u = acos u
interpretAstR1 AtanOp u = atan u
interpretAstR1 SinhOp u = sinh u
interpretAstR1 CoshOp u = cosh u
interpretAstR1 TanhOp u = tanh u
interpretAstR1 AsinhOp u = asinh u
interpretAstR1 AcoshOp u = acosh u
interpretAstR1 AtanhOp u = atanh u

interpretAstR2 :: RealFloat a
               => OpCode2 -> a -> a -> a
{-# INLINE interpretAstR2 #-}
interpretAstR2 DivideOp u v = u / v
interpretAstR2 PowerOp u v = u ** v
interpretAstR2 LogBaseOp u v = logBase u v
interpretAstR2 Atan2Op u v = atan2 u v

interpretAstI2 :: Integral a
               => OpCodeIntegral2 -> a -> a -> a
{-# INLINE interpretAstI2 #-}
interpretAstI2 QuotOp u v = quot u v
interpretAstI2 RemOp u v = rem u v

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
     (OS.Shape sh, ADReadyBoth ranked shaped, GoodScalar r)
  => AstEnv ranked shaped
  -> AstShaped PrimalSpan r sh -> PrimalOf shaped r sh
interpretAstPrimalS env v1 = case v1 of
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
     (OS.Shape sh, ADReadyBoth ranked shaped, GoodScalar r)
  => AstEnv ranked shaped
  -> AstShaped DualSpan r sh -> DualOf shaped r sh
interpretAstDualS env v1 = case v1 of
  AstDualPartS (AstDS _ u') -> interpretAstDualS env u'
  AstDualPartS t -> sdualPart $ interpretAstS env t
  _ -> sdualPart $ interpretAstS env v1

interpretAstS
  :: forall ranked shaped sh s r.
     (OS.Shape sh, ADReadyBoth ranked shaped, GoodScalar r, AstSpan s)
  => AstEnv ranked shaped
  -> AstShaped s r sh -> shaped r sh
interpretAstS env = \case
  AstVarS (AstVarName var) -> case EM.lookup (astVarIdToAstId var) env of
    Just (AstEnvElemS @sh2 @r2 t) -> case sameShape @sh2 @sh of
      Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> t
        _ -> error "interpretAstS: type mismatch"
      Nothing -> error "interpretAstS: wrong shape in environment"
    Just{} -> error "interpretAstS: wrong tensor kind in environment"
    Nothing -> error $ "interpretAstS: unknown variable " ++ show var
  AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let t = interpretAstS env u
        env2 w = extendEnvS var w env
    in slet t (\w -> interpretAstS (env2 w) v)
  AstLetADShareS{} -> error "interpretAstS: AstLetADShare"
  AstCondS b a1 a2 ->
    let b1 = interpretAstBool env b
        t2 = interpretAstS env a1
        t3 = interpretAstS env a2
    in ifF b1 t2 t3
  AstMinIndexS v -> sminIndex $ sconstant $ interpretAstPrimalS env v
  AstMaxIndexS v -> smaxIndex $ sconstant $ interpretAstPrimalS env v
  AstFloorS v -> sfloor $ sconstant $ interpretAstPrimalS env v
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
  AstSum (AstN2 TimesOp [t, u])
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
          -- TODO: do as a term rewrite using an extended set of terms?
  AstSum (AstReshape _sh (AstN2 TimesOp [t, u]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @0) ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tdot0 t1 t2
  AstSum (AstTranspose [1, 0] (AstN2 TimesOp [t, u]))  -- TODO: generalize
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
  AstBuild1 k (var, AstSum (AstN2 TimesOp [t, AstIndex
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let t1 = interpretAst env t
            t2 = interpretAst env u
        in tmatvecmul t2 t1
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstN2 TimesOp [t, AstIndex
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
  AstGatherS @sh2 AstIotaS (vars, i :$: ZSH) ->
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
  AstConstS a -> sconst a
  AstRToS v -> sfromR $ interpretAst env v
  AstConstantS a -> sconstant $ interpretAstPrimalS env a
  AstPrimalPartS a -> interpretAstS env a
  AstDualPartS a -> interpretAstS env a
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



{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Double n
  -> AstRanked PrimalSpan Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Float n
  -> AstRanked PrimalSpan Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Int64 n
  -> AstRanked PrimalSpan Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Double n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Float n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Int64 n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Double n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Float n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Int64 n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Double n
  -> DummyDual Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Float n
  -> DummyDual Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Int64 n
  -> DummyDual Int64 n #-}

{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Double n
  -> ADVal (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Float n
  -> ADVal (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Int64 n
  -> ADVal (Flip OR.Array) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Double n
  -> ADVal (AstRanked PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Float n
  -> ADVal (AstRanked PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Int64 n
  -> ADVal (AstRanked PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked FullSpan Double n
  -> ADVal (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked FullSpan Float n
  -> ADVal (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked FullSpan Int64 n
  -> ADVal (Flip OR.Array) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked FullSpan Double n
  -> ADVal (AstRanked PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked FullSpan Float n
  -> ADVal (AstRanked PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked FullSpan Int64 n
  -> ADVal (AstRanked PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked FullSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked FullSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked FullSpan Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> DynamicExists (AstDynamic PrimalSpan)
  -> DynamicExists (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> DynamicExists (AstDynamic PrimalSpan)
  -> DynamicExists (ADValClown (AstDynamic PrimalSpan)) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> DynamicExists (AstDynamic PrimalSpan)
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> DynamicExists (AstDynamic FullSpan)
  -> DynamicExists (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> DynamicExists (AstDynamic FullSpan)
  -> DynamicExists (ADValClown (AstDynamic PrimalSpan)) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> DynamicExists (AstDynamic FullSpan)
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstDomains PrimalSpan
  -> Domains (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstDomains PrimalSpan
  -> Domains (ADValClown (AstDynamic PrimalSpan)) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstDomains PrimalSpan
  -> DomainsOD #-}

{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstDomains FullSpan
  -> Domains (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstDomains FullSpan
  -> Domains (ADValClown (AstDynamic PrimalSpan)) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstDomains FullSpan
  -> DomainsOD #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstBool
  -> (ADShare, Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstBool
  -> (ADShare, AstBool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstBool
  -> (ADShare, Bool) #-}

{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> DynamicExists (AstDynamic PrimalSpan)
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstDomains PrimalSpan
  -> DomainsOD #-}

{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> DynamicExists (AstDynamic FullSpan)
  -> DynamicExists OD.Array #-}

{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstDomains FullSpan
  -> DomainsOD #-}

{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n => OpCodeRel -> [Flip OR.Array Double n] -> (ADShare, Bool) #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n => OpCodeRel -> [Flip OR.Array Float n] -> (ADShare, Bool) #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n => OpCodeRel -> [Flip OR.Array Int64 n] -> (ADShare, Bool) #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked PrimalSpan Double n] -> (ADShare, AstBool) #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked PrimalSpan Float n] -> (ADShare, AstBool) #-}
{-# SPECIALIZE interpretAstRelOp
  :: KnownNat n
  => OpCodeRel -> [AstRanked PrimalSpan Int64 n] -> (ADShare, AstBool) #-}
-- FullSpan not needed, because relations are computed on primal parts
