{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -fno-full-laziness -fno-cse #-}
-- | A couple of gradient descent scheme implementations.
module HordeAd.Core.Optimizer
  ( gdSimple
  , sgd
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  ) where

import Prelude

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.OptimizerTools
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- | Simple Gradient Descent.
gdSimple :: forall r. HasDelta r
         => r
         -> (DualNumberVariables 'DModeGradient r -> DualMonadGradient r (DualNumber 'DModeGradient r))
         -> Int  -- ^ requested number of iterations
         -> Domains r  -- ^ initial parameters
         -> IO (Domains r)
gdSimple gamma f n0 parameters0 = go n0 parameters0 where
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  varDeltas = generateDeltaVars parameters0
  go :: Int -> Domains r -> IO (Domains r)
  go 0 parameters = return parameters
  go n parameters = do
    let variables = makeDualNumberVariables parameters varDeltas
    gradients <- fst <$> dReverseGeneral 1 variables f
    let !parametersNew = updateWithGradient gamma parameters gradients
    go (pred n) parametersNew

-- | Stochastic Gradient Descent.
sgd :: forall r a. HasDelta r
    => r
    -> (a -> DualNumberVariables 'DModeGradient r -> DualMonadGradient r (DualNumber 'DModeGradient r))
    -> [a]  -- ^ training data
    -> Domains r  -- ^ initial parameters
    -> IO (Domains r, r)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r -> IO (Domains r, r)
  go [] parameters = return (parameters, 0)
  go (a : rest) parameters = do
    let variables = makeDualNumberVariables parameters varDeltas
    (gradients, valueNew) <- dReverseGeneral 1 variables (f a)
    let !parametersNew = updateWithGradient gamma parameters gradients
    if null rest
    then return (parametersNew, valueNew)
    else go rest parametersNew
{-
{-# SPECIALIZE sgd
  :: Double
  -> ((Vector Double, Vector Double) -> DualNumberVariables 'DModeGradient Double -> DualMonadGradient Double (DualNumber 'DModeGradient Double))
  -> [(Vector Double, Vector Double)]
  -> Domains Double
  -> (Domains Double, Double) #-}
-}

sgdAdam :: forall r a. HasDelta r
        => (a -> DualNumberVariables 'DModeGradient r -> DualMonadGradient r (DualNumber 'DModeGradient r))
        -> [a]
        -> Domains r
        -> StateAdam r
        -> IO (Domains r, StateAdam r)
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs :: forall r a. HasDelta r
            => ArgsAdam r
            -> (a -> DualNumberVariables 'DModeGradient r
                -> DualMonadGradient r (DualNumber 'DModeGradient r))
            -> [a]
            -> Domains r
            -> StateAdam r
            -> IO (Domains r, StateAdam r)
sgdAdamArgs argsAdam f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r-> StateAdam r -> IO (Domains r, StateAdam r)
  go [] parameters stateAdam = return (parameters, stateAdam)
  go (a : rest) parameters stateAdam = do
    let variables = makeDualNumberVariables parameters varDeltas
    gradients <- fst <$> dReverseGeneral 1 variables (f a)
    let (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    go rest parametersNew stateAdamNew
