{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.AstInterpret
  ( InterpretAst, interpretAst, interpretAstDynamic
  , AstEnv, extendEnvR
  , AstEnvElem(AstVarR)  -- for a test only
  ) where

import Prelude hiding ((<*))

import           Control.Exception.Assert.Sugar
import           Data.Boolean
import qualified Data.EnumMap.Strict as EM
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, sameNat)
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Ast
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal ()
import HordeAd.Core.TensorClass
import HordeAd.Internal.SizedList

-- * Interpretation of Ast in ADVal

type AstEnv a = EM.EnumMap AstVarId (AstEnvElem a)

data AstEnvElem a =
    AstVarR (DynamicTensor a)
  | AstVarI (IntOf a)

deriving instance (Show (DynamicTensor a), Show (IntOf a))
                  => Show (AstEnvElem a)

extendEnvR :: forall n a. (Tensor a, KnownNat n)
           => AstVarName (TensorOf n (ScalarOf a)) -> TensorOf n a
           -> AstEnv a -> AstEnv a
extendEnvR v@(AstVarName var) d =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show v)
                   var (AstVarR $ tfromR d)

extendEnvI :: AstVarId -> IntOf a -> AstEnv a -> AstEnv a
extendEnvI var i =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvI: duplicate " ++ show var)
                   var (AstVarI i)

extendEnvVars :: AstVarList m -> IndexOf m a
              -> AstEnv a -> AstEnv a
extendEnvVars vars ix env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

interpretLambdaI
  :: (AstEnv c -> a -> b) -> AstEnv c -> (AstVarId, a) -> IntOf c -> b
{-# INLINE interpretLambdaI #-}
interpretLambdaI f env (var, ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIndexToIndex
  :: (AstEnv a -> AstInt q -> IntOf a)
  -> AstEnv a -> (AstVarList m, AstIndex p q) -> IndexOf m a
  -> IndexOf p a
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f env (vars, asts) =
  \ix -> fmap (f (extendEnvVars vars ix env)) asts

-- This horror (and some lesser horrors elsewhere) are required due
-- to the inability to quantify constraints containing type families, see
-- https://gitlab.haskell.org/ghc/ghc/-/issues/14860 and
-- https://gitlab.haskell.org/ghc/ghc/-/issues/16365.
data Dict c a where
  Dict :: c a => Dict c a

class ( Tensor a, Tensor (Primal a)
      , EqB (IntOf a), OrdB (IntOf a), IfB (IntOf a)
      , Numeric (ScalarOf a), Show (ScalarOf a), RealFloat (Primal a)
      , Num (Vector (ScalarOf a)), IntOf (Primal a) ~ IntOf a
      , BooleanOf (Primal a) ~ BooleanOf (IntOf a) )
      => Evidence a where
  ev :: forall n. KnownNat n
     => Proxy a
     -> ( BooleanOf (TensorOf n (Primal a)) :~: BooleanOf (IntOf a)
        , Dict RealFloat (TensorOf n a)
        , Dict EqB (TensorOf n (Primal a))
        , Dict OrdB (TensorOf n (Primal a)) )

instance Evidence (ADVal Double) where
  ev _ = (Refl, Dict, Dict, Dict)
instance Evidence (ADVal Float) where
  ev _ = (Refl, Dict, Dict, Dict)
instance (Numeric r, Show r, RealFloat r, Floating (Vector r))
         => Evidence (ADVal (Ast0 r)) where
  ev _ = (Refl, Dict, Dict, Dict)
instance Evidence Double where
  ev _ = (Refl, Dict, Dict, Dict)
instance Evidence Float where
  ev _ = (Refl, Dict, Dict, Dict)

type InterpretAst a = Evidence a

-- TODO: the following is false. Make it true.
-- Note that this uses the @Primal a@ instance of @InterpretAst@,
-- which makes this simpler and more performant than projecting
-- the result from an @a@ instance.
interpretAstPrimal
  :: (KnownNat n, Evidence a)
  => AstEnv a
  -> AstPrimalPart n (ScalarOf a) -> TensorOf n (Primal a)
interpretAstPrimal env (AstPrimalPart v) =
  tprimalPart $ interpretAst env v
-- interpretAst @n @(Primal a) (EM.map tprimalPart env) v
-- TODO: but both Dual and AstEnv are strict, so in both cases
-- we can't avoid wasted computation. Benchmark lazy AstEnv
-- once we have tests with many vars.
-- TODO: constrain types (we are down one level here) and then special case
   -- AstBuild1 k (var, AstConstant v) ->

interpretAst
  :: forall n a. (KnownNat n, Evidence a)
  => AstEnv a
  -> Ast n (ScalarOf a) -> TensorOf n a
interpretAst env | (_, Dict, _, _) <- ev @a @n Proxy = \case
  AstVar _sh var -> case EM.lookup var env of
    Just (AstVarR d) -> tfromD d
    Just AstVarI{} ->
      error $ "interpretAst: type mismatch for Var" ++ show var
    Nothing -> error $ "interpretAst: unknown variable Var" ++ show var
  AstLet var u v ->
    interpretAst (EM.insert var (AstVarR $ tfromR $ interpretAst env u) env) v
  AstOp opCode args ->
    interpretAstOp (interpretAst env) opCode args
  AstConst a -> tconst a
  AstConstant a -> tconstant $ interpretAstPrimal env a
  AstConstInt0 i -> tfromIndex0 $ interpretAstInt env i
  AstIndexZ v is ->
    tindex (interpretAst env v) (fmap (interpretAstInt env) is)
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
  AstSum v@(AstOp TimesOp [t, u]) ->
    case sameNat (Proxy @n) (Proxy @0) of
      Just Refl -> tdot0 (interpretAst env t) (interpretAst env u)
        -- TODO: do as a term rewrite using an extended set of terms?
      _ -> tsum (interpretAst env v)
  AstSum v -> tsum (interpretAst env v)
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R
    -- is cheaper, too
  AstScatter sh v (vars, ix) ->
    tscatter sh (interpretAst env v)
                (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
  AstFromList l -> tfromList (map (interpretAst env) l)
  AstFromVector l -> tfromVector (V.map (interpretAst env) l)
  AstKonst k v -> tkonst k (interpretAst env v)
  AstAppend x y -> tappend (interpretAst env x) (interpretAst env y)
  AstSlice i k v -> tslice i k (interpretAst env v)
  AstReverse v -> treverse (interpretAst env v)
  AstTranspose perm v -> ttranspose perm $ interpretAst env v
  AstReshape sh v -> treshape sh (interpretAst env v)
  AstBuild1 0 (_, v) -> tfromList0N (0 :$ tshape v) []
  -- The following can't be, in general, so partially evaluated, because v
  -- may contain variables that the evironment sends to terms,
  -- not to concrete numbers (and so Primal a is not equal to ScalarOf a).
  -- However, this matters only for POPL AD, not JAX AD.
  -- AstBuild1 k (var, AstConstant v) ->
  --   tconst
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env (var, v)
  AstBuild1 k (var, v) ->
    tbuild1 k (interpretLambdaI interpretAst env (var, v))
    -- to be used only in tests
  AstGatherZ sh v (vars, ix) ->
    tgather sh (interpretAst env v)
               (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
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
  AstD u (AstDualPart u') -> tD (interpretAstPrimal env u)
                                (tdualPart $ interpretAst env u')

interpretAstInt :: Evidence a
                => AstEnv a
                -> AstInt (ScalarOf a) -> IntOf (Primal a)
interpretAstInt env = \case
  AstIntVar var -> case EM.lookup var env of
    Just AstVarR{} ->
      error $ "interpretAstInt: type mismatch for Var" ++ show var
    Just (AstVarI i) -> i
    Nothing -> error $ "interpretAstInt: unknown variable Var" ++ show var
  AstIntOp opCodeInt args ->
    interpretAstIntOp (interpretAstInt env) opCodeInt args
  AstIntConst a -> fromIntegral a
  AstIntFloor v -> tfloor $ interpretAstPrimal env v
  AstIntCond b a1 a2 -> ifB (interpretAstBool env b)
                            (interpretAstInt env a1)
                            (interpretAstInt env a2)
  AstMinIndex1 v -> tminIndex0 $ interpretAstPrimal env v
  AstMaxIndex1 v -> tmaxIndex0 $ interpretAstPrimal env v

interpretAstBool :: forall a. Evidence a
                 => AstEnv a
                 -> AstBool (ScalarOf a) -> BooleanOf (Primal a)
interpretAstBool env = \case
  AstBoolOp opCodeBool args ->
    interpretAstBoolOp (interpretAstBool env) opCodeBool args
  AstBoolConst a -> if a then true else false
  AstRel @n opCodeRel args | (Refl, _, Dict, Dict) <- ev @a @n Proxy ->
    let f v = interpretAstPrimal env v
    in interpretAstRelOp f opCodeRel args
  AstRelInt opCodeRel args ->
    let f = interpretAstInt env
    in interpretAstRelOp f opCodeRel args

interpretAstDynamic
  :: Evidence a
  => AstEnv a
  -> AstDynamic (ScalarOf a) -> DynamicTensor a
interpretAstDynamic env = \case
  AstDynamicDummy -> error "interpretAstDynamic: AstDynamicDummy"
  AstDynamicPlus v u ->
    interpretAstDynamic env v `taddD` interpretAstDynamic env u
  AstDynamicFrom w -> tfromR $ interpretAst env w
  AstDynamicVar sh var -> case EM.lookup var env of
    Just (AstVarR d) -> assert (shapeToList sh == tshapeD d) $ d
    Just AstVarI{} ->
      error $ "interpretAstDynamic: type mismatch for Var" ++ show var
    Nothing -> error $ "interpretAstDynamic: unknown variable Var" ++ show var

interpretAstOp :: RealFloat b
               => (c -> b) -> OpCode -> [c] -> b
{-# INLINE interpretAstOp #-}
interpretAstOp f PlusOp [u, v] = f u + f v
interpretAstOp f MinusOp [u, v] = f u - f v
interpretAstOp f TimesOp [u, v] = f u * f v
interpretAstOp f NegateOp [u] = negate $ f u
interpretAstOp f AbsOp [u] = abs $ f u
interpretAstOp f SignumOp [u] = signum $ f u
interpretAstOp f DivideOp [u, v] = f u / f v
interpretAstOp f RecipOp [u] = recip $ f u
interpretAstOp f ExpOp [u] = exp $ f u
interpretAstOp f LogOp [u] = log $ f u
interpretAstOp f SqrtOp [u] = sqrt $ f u
interpretAstOp f PowerOp [u, v] = f u ** f v
interpretAstOp f LogBaseOp [u, v] = logBase (f u) (f v)
interpretAstOp f SinOp [u] = sin $ f u
interpretAstOp f CosOp [u] = cos $ f u
interpretAstOp f TanOp [u] = tan $ f u
interpretAstOp f AsinOp [u] = asin $ f u
interpretAstOp f AcosOp [u] = acos $ f u
interpretAstOp f AtanOp [u] = atan $ f u
interpretAstOp f SinhOp [u] = sinh $ f u
interpretAstOp f CoshOp [u] = cosh $ f u
interpretAstOp f TanhOp [u] = tanh $ f u
interpretAstOp f AsinhOp [u] = asinh $ f u
interpretAstOp f AcoshOp [u] = acosh $ f u
interpretAstOp f AtanhOp [u] = atanh $ f u
interpretAstOp f Atan2Op [u, v] = atan2 (f u) (f v)
interpretAstOp f MaxOp [u, v] = max (f u) (f v)
interpretAstOp f MinOp [u, v] = min (f u) (f v)
interpretAstOp _ opCode args =
  error $ "interpretAstOp: wrong number of arguments"
          ++ show (opCode, length args)

interpretAstIntOp :: Integral b
                  => (c -> b) -> OpCodeInt -> [c] -> b
{-# INLINE interpretAstIntOp #-}
interpretAstIntOp f PlusIntOp [u, v] = f u + f v
interpretAstIntOp f MinusIntOp [u, v] = f u - f v
interpretAstIntOp f TimesIntOp [u, v] = f u * f v
interpretAstIntOp f NegateIntOp [u] = negate $ f u
interpretAstIntOp f AbsIntOp [u] = abs $ f u
interpretAstIntOp f SignumIntOp [u] = signum $ f u
interpretAstIntOp f MaxIntOp [u, v] = max (f u) (f v)
interpretAstIntOp f MinIntOp [u, v] = min (f u) (f v)
interpretAstIntOp f QuotIntOp [u, v] = quot (f u) (f v)
interpretAstIntOp f RemIntOp [u, v] = rem (f u) (f v)
interpretAstIntOp _ opCodeInt args =
  error $ "interpretAstIntOp: wrong number of arguments"
          ++ show (opCodeInt, length args)

interpretAstBoolOp :: Boolean b
                   => (c -> b) -> OpCodeBool -> [c] -> b
{-# INLINE interpretAstBoolOp #-}
interpretAstBoolOp f NotOp [u] = notB $ f u
interpretAstBoolOp f AndOp [u, v] = f u &&* f v
interpretAstBoolOp f OrOp [u, v] = f u ||* f v
interpretAstBoolOp _ opCodeBool args =
  error $ "interpretAstBoolOp: wrong number of arguments"
          ++ show (opCodeBool, length args)

interpretAstRelOp :: (EqB b, OrdB b)
                  => (a -> b) -> OpCodeRel -> [a] -> BooleanOf b
{-# INLINE interpretAstRelOp #-}
interpretAstRelOp f EqOp [u, v] = f u ==* f v
interpretAstRelOp f NeqOp [u, v] = f u /=* f v
interpretAstRelOp f LeqOp [u, v] = f u <=* f v
interpretAstRelOp f GeqOp [u, v] = f u >=* f v
interpretAstRelOp f LsOp [u, v] = f u <* f v
interpretAstRelOp f GtOp [u, v] = f u >* f v
interpretAstRelOp _ opCodeRel args =
  error $ "interpretAstRelOp: wrong number of arguments"
          ++ show (opCodeRel, length args)



{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal Double)
  -> AstPrimalPart n Double -> TensorOf n Double #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal Float)
  -> AstPrimalPart n Float -> TensorOf n Float #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Double))
  -> AstPrimalPart n Double -> TensorOf n (Ast0 Double) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Float))
  -> AstPrimalPart n Float -> TensorOf n (Ast0 Float) #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv Double
  -> AstPrimalPart n Double -> TensorOf n Double #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv Float
  -> AstPrimalPart n Float -> TensorOf n Float #-}

{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal Double)
  -> Ast n Double -> TensorOf n (ADVal Double) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal Float)
  -> Ast n Float -> TensorOf n (ADVal Float) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Double))
  -> Ast n Double -> TensorOf n (ADVal (Ast0 Double)) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv (ADVal (Ast0 Float))
  -> Ast n Float -> TensorOf n (ADVal (Ast0 Float)) #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv Double
  -> Ast n Double -> TensorOf n Double #-}
{-# SPECIALIZE interpretAst
  :: KnownNat n
  => AstEnv Float
  -> Ast n Float -> TensorOf n Float #-}

{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal Double)
  -> AstInt Double -> CInt #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal Float)
  -> AstInt Float -> CInt #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Ast0 Double))
  -> AstInt Double -> AstInt Double #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv (ADVal (Ast0 Float))
  -> AstInt Float -> AstInt Float #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv Double
  -> AstInt Double -> CInt #-}
{-# SPECIALIZE interpretAstInt
  :: AstEnv Float
  -> AstInt Float -> CInt #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal Double)
  -> AstBool Double -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal Float)
  -> AstBool Float -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Ast0 Double))
  -> AstBool Double -> AstBool Double #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Ast0 Float))
  -> AstBool Float -> AstBool Float #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv Double
  -> AstBool Double -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv Float
  -> AstBool Float -> Bool #-}

{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal Double)
  -> AstDynamic Double -> DynamicTensor (ADVal Double) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal Float)
  -> AstDynamic Float -> DynamicTensor (ADVal Float) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Ast0 Double))
  -> AstDynamic Double -> DynamicTensor (ADVal (Ast0 Double)) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv (ADVal (Ast0 Float))
  -> AstDynamic Float -> DynamicTensor (ADVal (Ast0 Float)) #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv Double
  -> AstDynamic Double -> DynamicTensor Double #-}
{-# SPECIALIZE interpretAstDynamic
  :: AstEnv Float
  -> AstDynamic Float -> DynamicTensor Float #-}
