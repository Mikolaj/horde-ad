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

import System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.OptimizerTools
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- TODO: change the type to IO, but this requires a rewrite of all
-- test glue code; also remove NOINLINE
-- | Simple Gradient Descent.
gdSimple :: forall r. HasDelta r
         => r
         -> (DualNumberVariables 'DModeGradient r -> DualMonadGradient r (DualNumber 'DModeGradient r))
         -> Int  -- ^ requested number of iterations
         -> Domains r  -- ^ initial parameters
         -> Domains r
{-# NOINLINE gdSimple #-}
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
        gradients = unsafePerformIO $ fst <$> dReverseGeneral 1 variables f
        parametersNew = updateWithGradient gamma parameters gradients
    in go (pred n) parametersNew

-- TODO: change the type to IO, but this requires a rewrite of all
-- test glue code; also remove NOINLINE
-- | Stochastic Gradient Descent.
sgd :: forall r a. HasDelta r
    => r
    -> (a -> DualNumberVariables 'DModeGradient r -> DualMonadGradient r (DualNumber 'DModeGradient r))
    -> [a]  -- ^ training data
    -> Domains r  -- ^ initial parameters
    -> (Domains r, r)
{-# NOINLINE sgd #-}
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r -> (Domains r, r)
  go [] parameters = (parameters, 0)
  go (a : rest) parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        (gradients, valueNew) =
          unsafePerformIO $ dReverseGeneral 1 variables (f a)
        !parametersNew = updateWithGradient gamma parameters gradients
    in if null rest
       then (parametersNew, valueNew)
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
        -> (Domains r, StateAdam r)
sgdAdam = sgdAdamArgs defaultArgsAdam

-- TODO: change the type to IO, but this requires a rewrite of all
-- test glue code; also remove NOINLINE
sgdAdamArgs :: forall r a. HasDelta r
            => ArgsAdam r
            -> (a -> DualNumberVariables 'DModeGradient r
                -> DualMonadGradient r (DualNumber 'DModeGradient r))
            -> [a]
            -> Domains r
            -> StateAdam r
            -> (Domains r, StateAdam r)
{-# NOINLINE sgdAdamArgs #-}
sgdAdamArgs argsAdam f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r-> StateAdam r -> (Domains r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) parameters stateAdam =
    let variables = makeDualNumberVariables parameters varDeltas
        gradients = unsafePerformIO $ fst <$> dReverseGeneral 1 variables (f a)
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
