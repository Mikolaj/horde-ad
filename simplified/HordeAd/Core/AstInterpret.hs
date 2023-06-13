{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
-- | Interpretation of @Ast@ terms in an aribtrary @Tensor@ class instance..
module HordeAd.Core.AstInterpret
  ( InterpretAstR, InterpretAstS
  , interpretAst, interpretAstDomainsDummy, interpretAstS
  , AstEnv, extendEnvS, extendEnvR, extendEnvD, AstMemo, emptyMemo
  , AstEnvElem(AstVarR)  -- for a test only
  ) where

import Prelude hiding ((<*))

import           Control.Arrow (second)
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
import           Data.List (foldl1', mapAccumR)
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

type AstEnv ranked r = EM.EnumMap AstVarId (AstEnvElem ranked r)

data AstEnvElem ranked r =
    AstVarR (DynamicOf ranked r)
  | AstVarI (IntOf (ranked r 0))
deriving instance (Show (DynamicOf ranked r), Show (IntOf (ranked r 0)))
                  => Show (AstEnvElem ranked r)

extendEnvS :: forall ranked shaped r sh.
              (OS.Shape sh, ConvertTensor ranked shaped, GoodScalar r)
           => AstVarName (OS.Array sh r) -> shaped r sh
           -> AstEnv ranked r -> AstEnv ranked r
extendEnvS v@(AstVarName var) d =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvS: duplicate " ++ show v)
                   var (AstVarR $ dfromS d)

extendEnvR :: forall ranked shaped r n.
              (ConvertTensor ranked shaped, KnownNat n, GoodScalar r)
           => AstVarName (OR.Array n r) -> ranked r n
           -> AstEnv ranked r -> AstEnv ranked r
extendEnvR v@(AstVarName var) d =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show v)
                   var (AstVarR $ dfromR d)

extendEnvD :: (ConvertTensor ranked shaped, GoodScalar r)
           => (AstDynamicVarName r, DynamicOf ranked r)
           -> AstEnv ranked r
           -> AstEnv ranked r
extendEnvD (AstDynamicVarName var, d) = extendEnvR var (tfromD d)

extendEnvDId :: AstVarId -> DynamicOf ranked r -> AstEnv ranked r
             -> AstEnv ranked r
extendEnvDId var d =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvDId: duplicate " ++ show var)
                   var (AstVarR d)

extendEnvI :: AstVarId -> IntOf (ranked r 0) -> AstEnv ranked r
           -> AstEnv ranked r
extendEnvI var i =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvI: duplicate " ++ show var)
                   var (AstVarI i)

extendEnvVars :: AstVarList m -> IndexOf (ranked r 0) m
              -> AstEnv ranked r
              -> AstEnv ranked r
extendEnvVars vars ix env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvVarsS :: AstVarListS sh -> IndexSh (ranked r 0) sh
               -> AstEnv ranked r
               -> AstEnv ranked r
extendEnvVarsS vars ix env =
  let assocs = zip (ShapedList.sizedListToList vars)
                   (ShapedList.sizedListToList ix)
  in foldr (uncurry extendEnvI) env assocs

-- Extensions to @memo@, one created for each iteration of the function,
-- are forgotten instead of returned, because they would differ
-- for each iteration, with differently extended environment,
-- and also because the created function is not expected to return a @memo@.
interpretLambdaI
  :: (AstEnv ranked r -> AstMemo r -> AstRanked r n
      -> (AstMemo r, ranked r n))
  -> AstEnv ranked r -> AstMemo r -> (AstVarId, AstRanked r n)
  -> IntOf (ranked r 0)
  -> ranked r n
{-# INLINE interpretLambdaI #-}
interpretLambdaI f env memo (var, ast) =
  \i -> snd $ f (extendEnvI var i env) memo ast

interpretLambdaIS
  :: (AstEnv ranked r -> AstMemo r -> AstShaped r sh
      -> (AstMemo r, shaped r sh))
  -> AstEnv ranked r -> AstMemo r -> (AstVarId, AstShaped r sh)
  -> IntSh (ranked r 0) n
  -> shaped r sh
{-# INLINE interpretLambdaIS #-}
interpretLambdaIS f env memo (var, ast) =
  \i -> snd $ f (extendEnvI var (ShapedList.unShapedNat i) env) memo ast

interpretLambdaIndex
  :: (AstEnv ranked r -> AstMemo r -> AstRanked r n
      -> (AstMemo r, ranked r n))
  -> AstEnv ranked r -> AstMemo r
  -> (AstVarList m, AstRanked r n) -> IndexOf (ranked r 0) m
  -> ranked r n
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f env memo (vars, ast) =
  \ix -> snd $ f (extendEnvVars vars ix env) memo ast

interpretLambdaIndexS
  :: forall sh sh2 ranked shaped r.
     (AstEnv ranked r -> AstMemo r -> AstShaped r sh
      -> (AstMemo r, shaped r sh))
  -> AstEnv ranked r -> AstMemo r
  -> (AstVarListS sh2, AstShaped r sh) -> IndexSh (ranked r 0) sh2
  -> shaped r sh
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f env memo (vars, ast) =
  \ix -> snd $ f (extendEnvVarsS vars ix env) memo ast

interpretLambdaIndexToIndex
  :: KnownNat p
  => (AstEnv ranked r -> AstMemo r -> AstInt q
      -> (AstMemo r, IntOf (ranked r 0))) -> AstEnv ranked r
  -> AstMemo r -> (AstVarList m, AstIndex q p)
  -> IndexOf (ranked r 0) m
  -> IndexOf (ranked r 0) p
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f env memo (vars, asts) =
  \ix -> listToIndex $ snd
         $ mapAccumR (f (extendEnvVars vars ix env)) memo (indexToList asts)

interpretLambdaIndexToIndexS
  :: OS.Shape sh2
  => (AstEnv ranked r -> AstMemo r -> AstInt q
      -> (AstMemo r, IntOf (ranked r 0))) -> AstEnv ranked r
  -> AstMemo r -> (AstVarListS sh, AstIndexS q sh2)
  -> IndexSh (ranked r 0) sh
  -> IndexSh (ranked r 0) sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f env memo (vars, asts) =
  \ix -> ShapedList.listToSized $ snd
         $ mapAccumR (f (extendEnvVarsS vars ix env)) memo
                     (ShapedList.sizedListToList asts)

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
  , Integral (IntOf (PrimalOf ranked r 0)), EqB (IntOf (ranked r 0))
  , OrdB (IntOf (ranked r 0)), IfB (IntOf (ranked r 0))
  , IntOf (PrimalOf ranked r 0) ~ IntOf (ranked r 0)
  , CRanked (PrimalOf ranked) r EqB
  , CRanked (PrimalOf ranked) r OrdB
  , CRanked ranked r RealFloat
  , CRanked (PrimalOf ranked) r
            (BooleanOfMatches (BooleanOf (IntOf (ranked r 0))))
  , BooleanOf (ranked r 0) ~ BooleanOf (IntOf (ranked r 0))
  , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 0)
  )

type InterpretAstS shaped r =
  ( GoodScalar r
  , Integral (IntOf (PrimalOf shaped r '[])), EqB (IntOf (shaped r '[]))
  , OrdB (IntOf (shaped r '[])), IfB (IntOf (shaped r '[]))
  , IntOf (PrimalOf shaped r '[]) ~ IntOf (shaped r '[])
  , CShaped (PrimalOf shaped) r EqB
  , CShaped (PrimalOf shaped) r OrdB
  , CShaped shaped r RealFloat
  , CShaped (PrimalOf shaped) r
            (BooleanOfMatches (BooleanOf (IntOf (shaped r '[]))))
  , BooleanOf (shaped r '[]) ~ BooleanOf (IntOf (shaped r '[]))
  , BooleanOf (IntOf (shaped r '[])) ~ BooleanOf (shaped r '[])
  )

type InterpretAst ranked shaped r =
  ( Tensor ranked, Tensor (PrimalOf ranked)
  , ShapedTensor shaped, ShapedTensor (PrimalOf shaped)
  , ConvertTensor ranked shaped
  , InterpretAstR ranked r
  , InterpretAstS shaped r
  , IntOf (ranked r 0) ~ IntOf (shaped r '[])
  )

type AstMemo r = ()  -- unused for now, but likely to be used in the future,
                     -- though probably not for memoization

emptyMemo :: AstMemo r
emptyMemo = ()

-- Strict environment and strict ADVal and Delta make this is hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall ranked shaped n r.
     (KnownNat n, InterpretAst ranked shaped r)
  => AstEnv ranked r -> AstMemo r
  -> AstPrimalPart r n -> (AstMemo r, PrimalOf ranked r n)
interpretAstPrimal env memo (AstPrimalPart v1) = case v1 of
  AstD u _-> interpretAstPrimal env memo u
  _ -> second (tprimalPart) $ interpretAst env memo v1

interpretAstDual
  :: forall ranked shaped n r.
     (KnownNat n, InterpretAst ranked shaped r)
  => AstEnv ranked r -> AstMemo r
  -> AstDualPart r n -> (AstMemo r, DualOf ranked r n)
interpretAstDual env memo (AstDualPart v1) = case v1 of
  AstD _ u'-> interpretAstDual env memo u'
  _ -> second (tdualPart) $ interpretAst env memo v1

interpretAst
  :: forall ranked shaped n r.
     (KnownNat n, InterpretAst ranked shaped r)
  => AstEnv ranked r -> AstMemo r
  -> AstRanked r n -> (AstMemo r, ranked r n)
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
          (AstLet var u (AstOp TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env memo
          (AstLet var u (AstOp TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env memo
          (AstLet var u (AstOp TimesOp [v, AstReplicate @m k s]))
  AstOp TimesOp [v, u] ->
    let (memo2, v5) = interpretAst env memo v
        (memo3, u5) = interpretAst env memo2 u
    in (memo3, v5 `tmult` u5)
  AstOp opCode args ->
    let (memo2, args2) = mapAccumR (interpretAst env) memo args
    in (memo2, interpretAstOp opCode args2)
  AstSumOfList args ->
    let (memo2, args2) = mapAccumR (interpretAst env) memo args
    in (memo2, tsumOfList args2)
  AstIota -> error "interpretAst: bare AstIota, most likely a bug"
  AstIndex AstIota (i :. ZI) -> second tfromIndex0 $ interpretAstInt env memo i
  AstIndex v ix ->
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
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
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
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
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
  -- These are only needed for tests that don't vectorize Ast.
  AstBuild1 k (var, AstSum (AstOp TimesOp [t, AstIndex
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let (memo1, t1) = interpretAst env memo t
            (memo2, t2) = interpretAst env memo1 u
        in (memo2, tmatvecmul t2 t1)
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstOp TimesOp [t, AstIndex
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
  -- not to concrete numbers (and so Primal a is not equal to a).
  -- However, this matters only for POPL AD, not JAX AD and also it matters
  -- only with no vectorization of, at least, constant (primal-only) terms.
  -- AstBuild1 k (var, AstConstant v) ->
  --   tconst
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env memo (var, v)
  AstBuild1 k (var, v) ->
    (memo, tbuild1 k (interpretLambdaI interpretAst env memo (var, v)))
      -- to be used only in tests
  AstGather sh AstIota (vars, (i :. ZI)) ->
    ( memo
    , tbuild sh (interpretLambdaIndex interpretAst env memo
                                      (vars, tfromIndex0 i)) )
  AstGather sh v (vars, ix) ->
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
  AstSToR v -> second tfromS $ interpretAstS env memo v
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
  :: forall ranked shaped r.
     InterpretAst ranked shaped r
  => AstEnv ranked r -> AstMemo r
  -> AstDynamic r -> (AstMemo r, DynamicOf ranked r)
interpretAstDynamic env memo = \case
  AstRToD w -> second dfromR $ interpretAst env memo w
  AstSToD w -> second dfromS $ interpretAstS env memo w

interpretAstDomains
  :: forall ranked shaped r.
     InterpretAst ranked shaped r
  => AstEnv  ranked r -> AstMemo r
  -> AstDomains r -> (AstMemo r, Domains (DynamicOf ranked) r)
interpretAstDomains env memo = \case
  AstDomains l -> mapAccumR (interpretAstDynamic env) memo l
  AstDomainsLet var u v ->
    let (memo2, t) = interpretAst env memo u
        env2 = extendEnvR (AstVarName var) t env
    in interpretAstDomains env2 memo2 v
      -- TODO: preserve let, as in AstLet case
  AstDomainsLetS var u v ->
    let (memo2, t) = interpretAstS env memo u
        env2 = extendEnvS (AstVarName var) t env
    in interpretAstDomains env2 memo2 v
      -- TODO: preserve let, as in AstLet case

interpretAstInt :: forall ranked shaped r.
                   InterpretAst ranked shaped r
                => AstEnv ranked r -> AstMemo r
                -> AstInt r -> (AstMemo r, IntOf (ranked r 0))
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
  AstIntFloorS v -> second sfloor $ interpretAstPrimalS env memo v
  AstIntCond b a1 a2 ->
    let (memo1, b1) = interpretAstBool env memo b
        (memo2, t2) = interpretAstInt env memo1 a1
        (memo3, t3) = interpretAstInt env memo2 a2
    in (memo3, ifB b1 t2 t3)
  AstMinIndex1 v -> second tminIndex0 $ interpretAstPrimal env memo v
  AstMaxIndex1 v -> second tmaxIndex0 $ interpretAstPrimal env memo v
  AstMinIndex1S v -> second (ShapedList.unShapedNat . sminIndex0)
                     $ interpretAstPrimalS env memo v
  AstMaxIndex1S v -> second (ShapedList.unShapedNat . smaxIndex0)
                     $ interpretAstPrimalS env memo v

interpretAstBool :: forall ranked shaped r.
                    InterpretAst ranked shaped r
                 => AstEnv ranked r -> AstMemo r
                 -> AstBool r -> (AstMemo r, BooleanOf (ranked r 0))
interpretAstBool env memo = \case
  AstBoolOp opCodeBool args ->
    let (memo2, args2) = mapAccumR (interpretAstBool env) memo args
    in (memo2, interpretAstBoolOp opCodeBool args2)
  AstBoolConst a -> (memo, if a then true else false)
  AstRel opCodeRel args ->
    let (memo2, args2) = mapAccumR (interpretAstPrimal env) memo args
    in (memo2, interpretAstRelOp opCodeRel args2)
  AstRelS opCodeRel args ->
    let (memo2, args2) = mapAccumR (interpretAstPrimalS env) memo args
    in (memo2, interpretAstRelOp opCodeRel args2)
  AstRelInt opCodeRel args ->
    let (memo2, args2) = mapAccumR (interpretAstInt env) memo args
    in (memo2, interpretAstRelOp opCodeRel args2)

interpretAstDynamicDummy
  :: forall ranked shaped r.
     InterpretAst ranked shaped r
  => AstEnv ranked r -> AstMemo r
  -> AstDynamic r -> (AstMemo r, DynamicOf ranked r)
interpretAstDynamicDummy env memo = \case
  AstRToD AstIota -> (memo, ddummy @ranked)
  AstRToD w -> second dfromR $ interpretAst env memo w
  AstSToD AstIotaS -> (memo, ddummy @ranked)
  AstSToD w -> second dfromS $ interpretAstS env memo w

interpretAstDomainsDummy
  :: forall ranked shaped r.
     InterpretAst ranked shaped r
  => AstEnv ranked r -> AstMemo r
  -> AstDomains r -> (AstMemo r, Domains (DynamicOf ranked) r)
interpretAstDomainsDummy env memo = \case
  AstDomains l -> mapAccumR (interpretAstDynamicDummy env) memo l
  AstDomainsLet var u v ->
    let (memo2, t) = interpretAst env memo u
        env2 = extendEnvR (AstVarName var) t env
    in interpretAstDomainsDummy env2 memo2 v
      -- TODO: preserve let, as in AstLet case
  AstDomainsLetS var u v ->
    let (memo2, t) = interpretAstS env memo u
        env2 = extendEnvS (AstVarName var) t env
    in interpretAstDomainsDummy env2 memo2 v
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
  :: forall ranked shaped sh r. OS.Shape sh
  => InterpretAst ranked shaped r
  => AstEnv ranked r -> AstMemo r
  -> AstPrimalPartS r sh -> (AstMemo r, PrimalOf shaped r sh)
interpretAstPrimalS env memo (AstPrimalPartS v1) = case v1 of
  AstDS u _-> interpretAstPrimalS env memo u
  _ -> second (sprimalPart) $ interpretAstS env memo v1

interpretAstDualS
  :: forall ranked shaped sh r. OS.Shape sh
  => InterpretAst ranked shaped r
  => AstEnv ranked r -> AstMemo r
  -> AstDualPartS r sh -> (AstMemo r, DualOf shaped r sh)
interpretAstDualS env memo (AstDualPartS v1) = case v1 of
  AstDS _ u'-> interpretAstDualS env memo u'
  _ -> second (sdualPart) $ interpretAstS env memo v1

interpretAstS
  :: forall ranked shaped sh r. OS.Shape sh
  => InterpretAst ranked shaped r
  => AstEnv ranked r -> AstMemo r
  -> AstShaped r sh -> (AstMemo r, shaped r sh)
interpretAstS env memo = \case
  AstVarS var -> case EM.lookup var env of
    Just (AstVarR d) -> let t = sfromD d
                        in (memo, t)
    Just AstVarI{} ->
      error $ "interpretAstS: type mismatch for " ++ show var
    Nothing -> error $ "interpretAstS: unknown variable " ++ show var
  AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let (memo1, t) = interpretAstS env memo u
        env2 w = extendEnvS (AstVarName var) w env
    in (memo1, slet t (\w -> snd $ interpretAstS (env2 w) memo1 v))
         -- TODO: snd; env/state?
  AstLetADShareS{} -> error "interpretAst: AstLetADShare"
{- TODO:
  AstOp TimesOp [v, AstLet var u (AstReshape sh (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        -- The intVarInAst check is needed, because although variable
        -- capture is impossible, because we don't create nested lets
        -- with the same variable, we could create such nested lets
        -- if we omitted this check.
        interpretAst env memo
          (AstLet var u (AstOp TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstReshape sh (AstLet var u (AstReplicate @m k s))]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env memo
          (AstLet var u (AstOp TimesOp [v, AstReshape sh
                                             (AstReplicate @m k s)]))
  AstOp TimesOp [v, AstLet var u (AstReplicate @m k s)]
    | Just Refl <- sameNat (Proxy @m) (Proxy @0), not (intVarInAst var v) ->
        interpretAst env memo
          (AstLet var u (AstOp TimesOp [v, AstReplicate @m k s]))
-}
  AstOpS TimesOp [v, u] ->
    let (memo2, v5) = interpretAstS env memo v
        (memo3, u5) = interpretAstS env memo2 u
    in (memo3, v5 `smult` u5)
  AstOpS opCode args ->
    let (memo2, args2) = mapAccumR (interpretAstS env) memo args
    in (memo2, interpretAstOp opCode args2)
  AstSumOfListS args ->
    let (memo2, args2) = mapAccumR (interpretAstS env) memo args
    in (memo2, ssumOfList args2)
  AstIotaS -> error "interpretAstS: bare AstIotaS, most likely a bug"
  AstIndexS (AstIotaS @n) (i :$: ZSH) ->
    second (sfromIndex0 . ShapedList.shapedNat @n) $ interpretAstInt env memo i
  AstIndexS @sh1 v ix ->
    let (memo2, v2) = interpretAstS env memo v
        (memo3, ix3) = mapAccumR (interpretAstInt env) memo2
                                 (ShapedList.sizedListToList ix)
    in (memo3, sindex @shaped @r @sh1 v2 $ ShapedList.listToSized ix3)
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
{- TODO:
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
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
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
  AstSum (AstOp TimesOp [ AstTranspose tperm (AstLet vart vt
                                                (AstReplicate tk t))
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
          -- The variants below emerge when the whole term is transposed.
          -- All overlap with variants above and the cheaper one is selected.
          ([2, 0, 1], [1, 2, 0]) ->
            second (ttranspose [1, 0])
            $ interpretMatmul2 t u
          ([1, 2, 0], [2, 0, 1]) ->
            second (ttranspose [1, 0])
            $ interpretMatmul2 u t
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
-}
  AstSumS v -> second ssum $ interpretAstS env memo v
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstScatterS v (vars, ix) ->
    let (memo1, t1) = interpretAstS env memo v
        f2 = interpretLambdaIndexToIndexS interpretAstInt env memo (vars, ix)
    in (memo1, sscatter t1 f2)
  AstFromListS l ->
    let (memo2, l2) = mapAccumR (interpretAstS env) memo l
    in (memo2, sfromList l2)
  AstFromVectorS l ->
    let (memo2, l2) = mapAccumR (interpretAstS env) memo (V.toList l)
    in (memo2, sfromVector $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
{- TODO:
  AstReshape sh (AstReplicate @m _ s)
    | Just Refl <- sameNat (Proxy @m) (Proxy @0) ->
        let (memo1, t1) = interpretAst env memo s
        in (memo1, treplicate0N sh t1)
  AstReshape sh (AstLet var v (AstReplicate k t)) ->
    interpretAst env memo (AstLet var v (AstReshape sh (AstReplicate k t)))
-}
  AstReplicateS v -> second sreplicate (interpretAstS env memo v)
  AstAppendS x y ->
    let (memo1, t1) = interpretAstS env memo x
        (memo2, t2) = interpretAstS env memo1 y
    in (memo2, sappend t1 t2)
  AstSliceS @i @k AstIotaS ->
    let i = valueOf @i
        k = valueOf @k
    in interpretAstS env memo
       $ AstConstS $ OS.fromList $ map fromIntegral [i :: Int .. i + k - 1]
  AstSliceS @i v -> second (sslice (Proxy @i) Proxy) (interpretAstS env memo v)
  AstReverseS v -> second sreverse (interpretAstS env memo v)
  AstTransposeS @perm v -> second (stranspose (Proxy @perm))
                           $ interpretAstS env memo v
  AstReshapeS v -> second sreshape (interpretAstS env memo v)
  -- These are only needed for tests that don't vectorize Ast.
{- TODO:
  AstBuild1 k (var, AstSum (AstOp TimesOp [t, AstIndex
                                                u (AstIntVar var2 :. ZI)]))
    | Just Refl <- sameNat (Proxy @n) (Proxy @1)
    , var == var2, k == tlength u ->
        let (memo1, t1) = interpretAst env memo t
            (memo2, t2) = interpretAst env memo1 u
        in (memo2, tmatvecmul t2 t1)
  AstBuild1 k (var, AstSum
                      (AstReshape @p
                         _sh (AstOp TimesOp [t, AstIndex
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
  -- not to concrete numbers (and so Primal a is not equal to a).
  -- However, this matters only for POPL AD, not JAX AD and also it matters
  -- only with no vectorization of, at least, constant (primal-only) terms.
  -- AstBuild1 k (var, AstConstant v) ->
  --   tconst
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env memo (var, v)
-}
  AstBuild1S (var, v) ->
    (memo, sbuild1 (interpretLambdaIS interpretAstS env memo (var, v)))
      -- to be used only in tests
  AstGatherS @sh2 (AstIotaS @n) (vars, (i :$: ZSH)) ->
    ( memo
    , gcastWith (unsafeCoerce Refl :: OS.Take (OS.Rank sh) sh :~: sh)
      $ gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
      $ gcastWith (unsafeCoerce Refl :: sh2 :~: sh)
          -- transitivity of type equality doesn't work, by design,
          -- so this direct cast is needed instead of more basic laws
      $ sbuild @shaped @r @(OS.Rank sh)
               (interpretLambdaIndexS
                  interpretAstS env memo
                  (vars, sfromIndex0 (ShapedList.shapedNat @n i))) )
  AstGatherS v (vars, ix) ->
    let (memo1, t1) = interpretAstS env memo v
        f2 = interpretLambdaIndexToIndexS interpretAstInt env memo (vars, ix)
    in (memo1, sgather t1 f2)
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
  AstRToS v -> second sfromR $ interpretAst env memo v
  AstConstS a -> (memo, sconstBare a)
  AstConstantS a -> second sconstant $ interpretAstPrimalS env memo a
  AstDS u u' ->
    let (memo1, t1) = interpretAstPrimalS env memo u
        (memo2, t2) = interpretAstDualS env memo1 u'
    in (memo2, sD t1 t2)
  AstLetDomainsS vars l v ->
    let (memo2, l2) = interpretAstDomains env memo l
        env2 = V.foldr (\(var, d) -> extendEnvDId var d) env (V.zip vars l2)
    in interpretAstS env2 memo2 v



{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) Double
  -> AstMemo Double
  -> AstPrimalPart Double n
  -> (AstMemo Double, Flip OR.Array Double n) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) Float
  -> AstMemo Float
  -> AstPrimalPart Float n
  -> (AstMemo Float, Flip OR.Array Float n) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal AstRanked) Double
  -> AstMemo Double
  -> AstPrimalPart Double n
  -> (AstMemo Double, AstRanked Double n) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal AstRanked) Float
  -> AstMemo Float
  -> AstPrimalPart Float n
  -> (AstMemo Float, AstRanked Float n) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstPrimalPart Double n
  -> (AstMemo Double, Flip OR.Array Double n) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) Float
  -> AstMemo Float
  -> AstPrimalPart Float n
  -> (AstMemo Float, Flip OR.Array Float n) #-}

{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) Double
  -> AstMemo Double
  -> AstDualPart Double n
  -> (AstMemo Double, Product (Clown ADShare) (DeltaR (Flip OR.Array) (Flip OS.Array)) Double n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) Float
  -> AstMemo Float
  -> AstDualPart Float n
  -> (AstMemo Float, Product (Clown ADShare) (DeltaR (Flip OR.Array) (Flip OS.Array)) Float n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal AstRanked) Double
  -> AstMemo Double
  -> AstDualPart Double n
  -> (AstMemo Double, Product (Clown ADShare) (DeltaR AstRanked AstShaped) Double n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal AstRanked) Float
  -> AstMemo Float
  -> AstDualPart Float n
  -> (AstMemo Float, Product (Clown ADShare) (DeltaR AstRanked AstShaped) Float n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstDualPart Double n
  -> (AstMemo Double, DummyDual Double n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) Float
  -> AstMemo Float
  -> AstDualPart Float n
  -> (AstMemo Float, DummyDual Float n) #-}

{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) Double
  -> AstMemo Double
  -> AstRanked Double n
  -> (AstMemo Double, ADVal (Flip OR.Array) Double n) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) Float
  -> AstMemo Float
  -> AstRanked Float n
  -> (AstMemo Float, ADVal (Flip OR.Array) Float n) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal AstRanked) Double
  -> AstMemo Double
  -> AstRanked Double n
  -> (AstMemo Double, ADVal AstRanked Double n) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal AstRanked) Float
  -> AstMemo Float
  -> AstRanked Float n
  -> (AstMemo Float, ADVal AstRanked Float n) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstRanked Double n
  -> (AstMemo Double, Flip OR.Array Double n) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (Flip OR.Array) Float
  -> AstMemo Float
  -> AstRanked Float n
  -> (AstMemo Float, Flip OR.Array Float n) #-}

{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Flip OR.Array)) Double
  -> AstMemo Double
  -> AstDynamic Double
  -> (AstMemo Double, ADValClown OD.Array Double) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Flip OR.Array)) Float
  -> AstMemo Float
  -> AstDynamic Float
  -> (AstMemo Float, ADValClown OD.Array Float) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal AstRanked) Double
  -> AstMemo Double
  -> AstDynamic Double
  -> (AstMemo Double, ADValClown AstDynamic Double) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal AstRanked) Float
  -> AstMemo Float
  -> AstDynamic Float
  -> (AstMemo Float, ADValClown AstDynamic Float) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstDynamic Double
  -> (AstMemo Double, OD.Array Double) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (Flip OR.Array) Float
  -> AstMemo Float
  -> AstDynamic Float
  -> (AstMemo Float, OD.Array Float) #-}

{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array)) Double
  -> AstMemo Double
  -> AstDomains Double
  -> (AstMemo Double, Domains (ADValClown OD.Array) Double) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal (Flip OR.Array)) Float
  -> AstMemo Float
  -> AstDomains Float
  -> (AstMemo Float, Domains (ADValClown OD.Array) Float) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal AstRanked) Double
  -> AstMemo Double
  -> AstDomains Double
  -> (AstMemo Double, Domains (ADValClown AstDynamic) Double) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (ADVal AstRanked) Float
  -> AstMemo Float
  -> AstDomains Float
  -> (AstMemo Float, Domains (ADValClown AstDynamic) Float) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstDomains Double
  -> (AstMemo Double, Domains OD.Array Double) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstEnv  (Flip OR.Array) Float
  -> AstMemo Float
  -> AstDomains Float
  -> (AstMemo Float, Domains OD.Array Float) #-}

{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Flip OR.Array)) Double
  -> AstMemo Double
  -> AstInt Double
  -> (AstMemo Double, CInt) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Flip OR.Array)) Float
  -> AstMemo Float
  -> AstInt Float
  -> (AstMemo Float, CInt) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal AstRanked) Double
  -> AstMemo Double
  -> AstInt Double
  -> (AstMemo Double, AstInt Double) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal AstRanked) Float
  -> AstMemo Float
  -> AstInt Float
  -> (AstMemo Float, AstInt Float) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstInt Double
  -> (AstMemo Double, CInt) #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (Flip OR.Array) Float
  -> AstMemo Float
  -> AstInt Float
  -> (AstMemo Float, CInt) #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array)) Double
  -> AstMemo Double
  -> AstBool Double
  -> (AstMemo Double, Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array)) Float
  -> AstMemo Float
  -> AstBool Float
  -> (AstMemo Float, Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal AstRanked) Double
  -> AstMemo Double
  -> AstBool Double
  -> (AstMemo Double, AstBool Double) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal AstRanked) Float
  -> AstMemo Float
  -> AstBool Float
  -> (AstMemo Float, AstBool Float) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstBool Double
  -> (AstMemo Double, Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array) Float
  -> AstMemo Float
  -> AstBool Float
  -> (AstMemo Float, Bool) #-}

{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstDynamic Double
  -> (AstMemo Double, OD.Array Double) #-}
{-# SPECIALIZE interpretAstDynamicDummy
  :: AstEnv (Flip OR.Array) Float
  -> AstMemo Float
  -> AstDynamic Float
  -> (AstMemo Float, OD.Array Float) #-}

{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array) Double
  -> AstMemo Double
  -> AstDomains Double
  -> (AstMemo Double, Domains OD.Array Double) #-}
{-# SPECIALIZE interpretAstDomainsDummy
  :: AstEnv (Flip OR.Array) Float
  -> AstMemo Float
  -> AstDomains Float
  -> (AstMemo Float, Domains OD.Array Float) #-}

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
