{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Outdated and/or superseded implementations of gradient descent.
-- They are used only for special tests and for comparison with the recommended
-- optimizers to make sure the latter are superior in all contexts.
module HordeAd.Core.OutdatedOptimizer where

import Prelude

import Control.Monad (foldM)
import Numeric.LinearAlgebra (Vector)

import HordeAd.Core.DualNumber (DualNumber (..))
import HordeAd.Core.Engine
import HordeAd.Core.OptimizerTools
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- | Stochastic Gradient Descent with mini-batches, taking the mean
-- of the results from each mini-batch.
--
-- An option: vectorize and only then take the mean of the vector of results
-- and also parallelize taking advantage of vectorization (but currently
-- we have a global state, so that's tricky).
sgdBatch :: forall r a. (Ord r, IsScalar r, Fractional r)
         => Int  -- ^ batch size
         -> r  -- ^ gamma (learning_rate?)
         -> (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
         -> [a]  -- ^ training data
         -> Domains r  -- ^ initial parameters
         -> Domains r
sgdBatch batchSize gamma f trainingData parameters0 =
  go trainingData parameters0
 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r -> Domains' r
  go [] parameters = parameters
  go l parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        (batch, rest) = splitAt batchSize l
        fAdd :: DualNumberVariables r -> DualNumber r -> a
             -> DeltaMonadGradient r (DualNumber r)
        fAdd vars !acc a = do
          res <- f a vars
          return $! acc + res
        fBatch :: DualNumberVariables r
               -> DeltaMonadGradient r (DualNumber r)
        fBatch vars = do
          resBatch <- foldM (fAdd vars) 0 batch
          return $! resBatch / fromIntegral (length batch)
        gradients = fst $ generalDf variables fBatch
        parametersNew = updateWithGradient gamma parameters gradients
    in go rest parametersNew

sgdAdamBatch
  :: forall r a. (Eq r, Floating r, IsScalar r, Floating (Vector r))
  => Int  -- ^ batch size
  -> (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
  -> [a]
  -> Domains r
  -> StateAdam r
  -> (Domains r, StateAdam r)
sgdAdamBatch = sgdAdamBatchArgs defaultArgsAdam

sgdAdamBatchArgs
  :: forall r a. (Eq r, Floating r, IsScalar r, Floating (Vector r))
  => ArgsAdam r
  -> Int  -- ^ batch size
  -> (a -> DualNumberVariables r
      -> DeltaMonadGradient r (DualNumber r))
  -> [a]
  -> Domains r
  -> StateAdam r
  -> (Domains r, StateAdam r)
sgdAdamBatchArgs argsAdam batchSize f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r-> StateAdam r -> (Domains r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go l parameters stateAdam =
    let variables = makeDualNumberVariables parameters varDeltas
        (batch, rest) = splitAt batchSize l
        fAdd :: DualNumberVariables r -> DualNumber r -> a
             -> DeltaMonadGradient r (DualNumber r)
        fAdd vars !acc a = do
          res <- f a vars
          return $! acc + res
        fBatch :: DualNumberVariables r
               -> DeltaMonadGradient r (DualNumber r)
        fBatch vars = do
          resBatch <- foldM (fAdd vars) 0 batch
          return $! resBatch / fromIntegral (length batch)
        gradients = fst $ generalDf variables fBatch
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew

-- | Relatively Smart Gradient Descent.
-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gdSmart :: forall r. (Ord r, Fractional r, IsScalar r)
        => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
        -> Int  -- ^ requested number of iterations
        -> Domains r  -- ^ initial parameters
        -> (Domains r, r)
gdSmart f n0 parameters0 = go n0 parameters0 0.1 gradients0 value0 0 where
  varDeltas = generateDeltaVars parameters0
  variables0 = makeDualNumberVariables parameters0 varDeltas
  (gradients0, value0) = generalDf variables0 f
  go :: Int -> Domains r -> r -> Domains' r -> r -> Int -> (Domains' r, r)
  go 0 parameters !gamma _gradientsPrev _valuePrev !_i = (parameters, gamma)
  go _ parameters 0 _ _ _ = (parameters, 0)
  go n parameters gamma gradientsPrev valuePrev i =
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let parametersNew = updateWithGradient gamma parameters gradientsPrev
        variables = makeDualNumberVariables parametersNew varDeltas
        (gradients, value) = generalDf variables f
    in if | gradientIsNil gradientsPrev -> (parameters, gamma)
          | value > valuePrev ->
              go n parameters (gamma / 2) gradientsPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) parametersNew (gamma * 2) gradients value 0
          | otherwise -> go (pred n) parametersNew gamma gradients value (i + 1)
