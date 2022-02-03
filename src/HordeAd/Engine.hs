{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-orphans #-}
-- | Two implementations of the monad in which our dual numbers live,
-- an implementation of deriving a gradient and several gradient descent
-- schemes.
module HordeAd.Engine where

import Prelude

import           Control.Monad.Trans.State.Strict
import           Data.Functor.Identity
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector, rows)
import qualified Numeric.LinearAlgebra

import HordeAd.Delta
import HordeAd.DualNumber (DeltaMonad (..), DualNumber (..))
import HordeAd.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- import Debug.Trace

type Domain r = Vector r

type Domain' r = Domain r

type DomainV r = Data.Vector.Vector (Vector r)

type DomainV' r = DomainV r

type DomainL r = Data.Vector.Vector (Matrix r)

type DomainL' r = DomainL r

type Domains r = (Domain r, DomainV r, DomainL r)

type Domains' r = (Domain' r, DomainV' r, DomainL' r)

-- * First comes the dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

type DeltaMonadValue r = Identity

instance DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = Identity $ D u Zero
  returnLetV (D u _u') = Identity $ D u Zero
  returnLetL (D u _u') = Identity $ D u Zero

-- The general case, needed for old, hacky tests before 'Delta' extension.
--
-- Small enough that inline won't hurt.
primalValueGeneric :: Numeric r
                   => (DualNumberVariables r -> DeltaMonadValue r a)
                   -> Domains r
                   -> a
{-# INLINE primalValueGeneric #-}
primalValueGeneric f (params, paramsV, paramsL) =
  let vec = makeDualNumberVariables
              (params, paramsV, paramsL)
              ( V.replicate (V.length params) Zero  -- dummy
              , V.replicate (V.length paramsV) Zero
              , V.replicate (V.length paramsL) Zero )
  in runIdentity $ f vec

-- Small enough that inline won't hurt.
primalValue :: Numeric r
            => (DualNumberVariables r -> DeltaMonadValue r (DualNumber a))
            -> Domains r
            -> a
{-# INLINE primalValue #-}
primalValue f parameters =
  let D value _ = primalValueGeneric f parameters
  in value

-- * Here's the fully-fledged monad implementation for gradients
-- and the code that uses it to compute single gradients and to do
-- gradient descent.

newtype DeltaMonadGradient r a = DeltaMonadGradient
  { runDeltaMonadGradient :: State (DeltaState r) a }
  deriving (Monad, Functor, Applicative)

instance DeltaMonad r (DeltaMonadGradient r) where
  returnLet (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DScalar u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetV (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DVector u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetL (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DMatrix u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)

-- The functions in which it inlines and which are used in client code
-- are not inlined there, so the bloat is limited.
generalDf :: (Eq r, Numeric r, Num (Vector r))
          => DualNumberVariables r
          -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
          -> (Domains' r, r)
{-# INLINE generalDf #-}
generalDf vec@(params, _, paramsV, _, paramsL, _) f =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      initialState = DeltaState
        { deltaCounter = DeltaId $ dim + dimV + dimL
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaMonadGradient (f vec)) initialState
      gradient = evalBindings dim dimV dimL st d
  in (gradient, value)

df :: forall r. (Eq r, Numeric r, Num (Vector r))
   => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
   -> Domains r
   -> (Domains' r, r)
df f (params, paramsV, paramsL) =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      vVar = V.generate dim (Var . DeltaId)
      vVarV = V.generate dimV (Var . DeltaId . (+ dim))
      vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
      varDeltas = (vVar, vVarV, vVarL)
      variables = makeDualNumberVariables (params, paramsV, paramsL) varDeltas
  in generalDf variables f

updateWithGradient :: (Numeric r, Num (Vector r))
                   => r
                   -> Domains' r
                   -> Domains' r
                   -> Domains' r
updateWithGradient gamma (params, paramsV, paramsL)
                         (gradient, gradientV, gradientL) =
  let paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
      paramsVNew = V.zipWith (\i r -> i - Numeric.LinearAlgebra.scale gamma r)
                             paramsV gradientV
      paramsLNew = V.zipWith (\i r -> i - Numeric.LinearAlgebra.scale gamma r)
                             paramsL gradientL
  in (paramsNew, paramsVNew, paramsLNew)

-- | Simple Gradient Descent.
gdSimple :: forall r. (Eq r, Numeric r, Num (Vector r))
         => r
         -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
         -> Int  -- ^ requested number of iterations
         -> Domains r  -- ^ initial parameters
         -> Domains' r
gdSimple gamma f n0 parameters0@(params0, paramsV0, paramsL0) =
  go n0 parameters0
 where
  dim = V.length params0
  dimV = V.length paramsV0
  dimL = V.length paramsL0
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
  varDeltas = (vVar, vVarV, vVarL)
  go :: Int -> Domains r -> Domains' r
  go 0 parameters = parameters
  go n parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        gradients = fst $ generalDf variables f
        parametersNew = updateWithGradient gamma parameters gradients
    in go (pred n) parametersNew

-- | Stochastic Gradient Descent.
sgd :: forall r a. (Eq r, Numeric r, Num (Vector r))
    => r
    -> (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
    -> [a]  -- ^ training data
    -> Domains r  -- ^ initial parameters
    -> Domains' r
sgd gamma f trainingData parameters0@(params0, paramsV0, paramsL0) =
  go trainingData parameters0
 where
  dim = V.length params0
  dimV = V.length paramsV0
  dimL = V.length paramsL0
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
  varDeltas = (vVar, vVarV, vVarL)
  go :: [a] -> Domains r -> Domains' r
  go [] parameters = parameters
  go (a : rest) parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        gradients = fst $ generalDf variables (f a)
        parametersNew = updateWithGradient gamma parameters gradients
    in go rest parametersNew

-- | Relatively Smart Gradient Descent.
-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gdSmart :: forall r. (
--                     Show r,
                       Ord r, Fractional r, Numeric r
                     , Num (Vector r)
                     )
        => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
        -> Int  -- ^ requested number of iterations
        -> Domains r  -- ^ initial parameters
        -> (Domains' r, r)
gdSmart f n0 parameters0@(params0, paramsV0, paramsL0) =
  go n0 parameters0 0.1 gradients0 value0 0
 where
  dim = V.length params0
  dimV = V.length paramsV0
  dimL = V.length paramsL0
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
  varDeltas = (vVar, vVarV, vVarL)
  variables0 = makeDualNumberVariables parameters0 varDeltas
  (gradients0, value0) = generalDf variables0 f
  go :: Int -> Domains r -> r -> Domains' r -> r -> Int -> (Domains' r, r)
  go 0 parameters !gamma _gradientsPrev _valuePrev !_i = (parameters, gamma)
  go _ parameters 0 _ _ _ = (parameters, 0)
  go n parameters gamma gradientsPrev valuePrev i =
--    traceShow (n, gamma, valuePrev, i) $
--    traceShow ("parameters" :: String, parameters) $
--    traceShow ("gradients" :: String, gradientsPrev) $
    --
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let parametersNew = updateWithGradient gamma parameters gradientsPrev
        variables = makeDualNumberVariables parametersNew varDeltas
        (gradients, value) = generalDf variables f
    in if | gradientIsNil gradientsPrev -> (parameters, gamma)
          | value > valuePrev ->
--              traceShow ("value > valuePrev" :: String, value, valuePrev) $
              go n parameters (gamma / 2) gradientsPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) parametersNew gamma gradients value 0
          | otherwise -> go (pred n) parametersNew gamma gradients value (i + 1)

gradientIsNil :: (Ord r, Numeric r) => Domains' r -> Bool
gradientIsNil (gradient, gradientV, gradientL) =
  V.all (== 0) gradient
  && V.all (== V.empty) gradientV
  && V.all (\r -> rows r <= 0) gradientL
