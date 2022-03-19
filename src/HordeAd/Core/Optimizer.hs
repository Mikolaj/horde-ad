{-# LANGUAGE TypeFamilies #-}
-- | A couple of gradient descent scheme implementations.
module HordeAd.Core.Optimizer
  ( gdSimple
  , sgd
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  ) where

import Prelude

import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber (DualNumber (..))
import HordeAd.Core.Engine
import HordeAd.Core.OptimizerTools
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- | Simple Gradient Descent.
gdSimple :: forall r. HasDelta r
         => Primal r
         -> (DualNumberVariables r -> DualMonadGradient r (DualNumber r))
         -> Int  -- ^ requested number of iterations
         -> Domains r  -- ^ initial parameters
         -> Domains r
gdSimple gamma f n0 parameters0 = go n0 parameters0 where
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  varDeltas = generateDeltaVars parameters0
  go :: Int -> Domains r -> Domains r
  go 0 parameters = parameters
  go n parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        gradients = fst $ generalDf variables f
        parametersNew = updateWithGradient @r gamma parameters gradients
    in go (pred n) parametersNew

-- | Stochastic Gradient Descent.
sgd :: forall r a. HasDelta r
    => Primal r
    -> (a -> DualNumberVariables r -> DualMonadGradient r (DualNumber r))
    -> [a]  -- ^ training data
    -> Domains r  -- ^ initial parameters
    -> (Domains r, Primal r)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r -> (Domains r, Primal r)
  go [] parameters = (parameters, 0)
  go (a : rest) parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        (gradients, valueNew) = generalDf variables (f a)
        !parametersNew = updateWithGradient @r gamma parameters gradients
    in if null rest
       then (parametersNew, valueNew)
       else go rest parametersNew

sgdAdam :: forall r a.
           (HasDelta r, Floating (Primal r), Floating (Primal (Tensor1 r)))
        => (a -> DualNumberVariables r -> DualMonadGradient r (DualNumber r))
        -> [a]
        -> Domains r
        -> StateAdam r
        -> (Domains r, StateAdam r)
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs :: forall r a.
               (HasDelta r, Floating (Primal r), Floating (Primal (Tensor1 r)))
            => ArgsAdam r
            -> (a -> DualNumberVariables r
                -> DualMonadGradient r (DualNumber r))
            -> [a]
            -> Domains r
            -> StateAdam r
            -> (Domains r, StateAdam r)
sgdAdamArgs argsAdam f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r-> StateAdam r -> (Domains r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) parameters stateAdam =
    let variables = makeDualNumberVariables parameters varDeltas
        gradients = fst $ generalDf variables (f a)
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
