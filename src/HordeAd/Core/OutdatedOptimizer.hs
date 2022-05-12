{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Outdated and/or superseded implementations of gradient descent.
-- They are used only for special tests and for comparison with the recommended
-- optimizers to make sure the latter are superior in all contexts.
module HordeAd.Core.OutdatedOptimizer where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import           Data.Coerce (coerce)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.DualClass (DifferentiationScheme (..))
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.OptimizerTools
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- | Stochastic Gradient Descent with mini-batches, taking the mean
-- of the results from each mini-batch. Additionally, it uses
-- "forward gradient" from "Gradients without Backpropagation"
-- by Atilim Gunes Baydin, Barak A. Pearlmutter, Don Syme, Frank Wood,
-- Philip Torr.
--
-- Note that we can't generalize this to use either
-- @dForwardGeneral@ or @dReverseGeneral@, because the optimized call
-- to @updateWithGradient@ below would not be possible with the common API
-- for obtaining gradients and at least twice more allocations would
-- be done there. With small mini-batch sizes this matters,
-- especially for optimal forward gradient implementation
-- @dFastForwardGeneral@, where there's no overhead from storing
-- and evaluating delta-expressions.
--
-- An option: vectorize and only then take the mean of the vector of results
-- and also parallelize taking advantage of vectorization (but currently
-- we have a global state, so that's tricky).
sgdBatchForward
  :: forall a.
     Int
  -> Int  -- ^ batch size
  -> Double  -- ^ gamma (learning_rate?)
  -> (a -> DualNumberVariables 'DifferentiationSchemeGradient Double
      -> DualMonadGradient Double (DualNumber 'DifferentiationSchemeGradient Double))
  -> [a]  -- ^ training data
  -> Domains Double  -- ^ initial parameters
  -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
  -> (Domains Double, Double)
sgdBatchForward seed0 batchSize gamma f trainingData parameters0 nParameters =
  go seed0 trainingData parameters0 0
 where
  varDeltas = generateDeltaVars parameters0
  go :: Int -> [a] -> Domains Double -> Double -> (Domains Double, Double)
  go _ [] parameters value = (parameters, value)
  go seed l parameters _ =
    let (batch, rest) = splitAt batchSize l
        fAdd :: DualNumberVariables 'DifferentiationSchemeGradient Double
             -> DualNumber 'DifferentiationSchemeGradient Double -> a
             -> DualMonadGradient Double (DualNumber 'DifferentiationSchemeGradient Double)
        fAdd vars !acc a = do
          res <- f a vars
          return $! acc + res
        fBatch :: DualNumberVariables 'DifferentiationSchemeGradient Double
               -> DualMonadGradient Double (DualNumber 'DifferentiationSchemeGradient Double)
        fBatch vars = do
          resBatch <- foldM (fAdd vars) 0 batch
          return $! resBatch / fromIntegral (length batch)
        unitVarianceRange = sqrt 12 / 2
        (g1, g2) = (seed + 5, seed + 13)
        (_, _, _, direction) = initializerFixed g1 unitVarianceRange nParameters
        variables = makeDualNumberVariables parameters varDeltas
        (directionalDerivative, valueNew) =
          dForwardGeneral variables fBatch direction
        gammaDirectional = gamma * directionalDerivative
        parametersNew = updateWithGradient gammaDirectional parameters direction
    in go g2 rest parametersNew valueNew

-- | A variant with fast forward derivative computation.
sgdBatchFastForward
  :: forall a.
     Int
  -> Int  -- ^ batch size
  -> Double  -- ^ gamma (learning_rate?)
  -> (a -> DualNumberVariables 'DifferentiationSchemeDerivative Double
      -> DualMonadForward Double (DualNumber 'DifferentiationSchemeDerivative Double))
  -> [a]  -- ^ training data
  -> Domains Double  -- ^ initial parameters
  -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
  -> (Domains Double, Double)
sgdBatchFastForward seed0 batchSize gamma f trainingData
                    parameters0 nParameters =
  go seed0 trainingData parameters0 0
 where
  go :: Int -> [a] -> Domains Double -> Double -> (Domains Double, Double)
  go _ [] parameters value = (parameters, value)
  go seed l parameters@(params0, params1, params2, paramsX) _ =
    let (batch, rest) = splitAt batchSize l
        fAdd :: DualNumberVariables 'DifferentiationSchemeDerivative Double
             -> DualNumber 'DifferentiationSchemeDerivative Double -> a
             -> DualMonadForward Double (DualNumber 'DifferentiationSchemeDerivative Double)
        fAdd vars !acc a = do
          res <- f a vars
          return $! acc + res
        fBatch :: DualNumberVariables 'DifferentiationSchemeDerivative Double
               -> DualMonadForward Double (DualNumber 'DifferentiationSchemeDerivative Double)
        fBatch vars = do
          resBatch <- foldM (fAdd vars) 0 batch
          return $! resBatch / fromIntegral (length batch)
        unitVarianceRange = sqrt 12 / 2
        (g1, g2) = (seed + 5, seed + 13)
        (_, _, _, direction@(dparams0, dparams1, dparams2, dparamsX)) =
          initializerFixed g1 unitVarianceRange nParameters
        variables =
          makeDualNumberVariables
            ( coerce params0, coerce params1, coerce params2
            , unsafeCoerce paramsX )
            (V.convert dparams0, dparams1, dparams2, dparamsX)
        (directionalDerivative, valueNew) =
          dFastForwardGeneral variables fBatch
        gammaDirectional = gamma * directionalDerivative
        parametersNew = updateWithGradient gammaDirectional parameters direction
    in go g2 rest parametersNew valueNew

sgdAdamBatch
  :: forall r a. (HasDelta r, Floating (Data.Vector.Storable.Vector r))
  => Int  -- ^ batch size
  -> (a -> DualNumberVariables 'DifferentiationSchemeGradient r -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
  -> [a]
  -> Domains r
  -> StateAdam r
  -> (Domains r, StateAdam r)
sgdAdamBatch = sgdAdamBatchArgs defaultArgsAdam

sgdAdamBatchArgs
  :: forall r a. (HasDelta r, Floating (Data.Vector.Storable.Vector r))
  => ArgsAdam r
  -> Int  -- ^ batch size
  -> (a -> DualNumberVariables 'DifferentiationSchemeGradient r
      -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
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
        fAdd :: DualNumberVariables 'DifferentiationSchemeGradient r -> DualNumber 'DifferentiationSchemeGradient r -> a
             -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r)
        fAdd vars !acc a = do
          res <- f a vars
          return $! acc + res
        fBatch :: DualNumberVariables 'DifferentiationSchemeGradient r
               -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r)
        fBatch vars = do
          resBatch <- foldM (fAdd vars) 0 batch
          return $! resBatch / fromIntegral (length batch)
        gradients = fst $ dReverseGeneral 1 variables fBatch
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew

-- | Relatively Smart Gradient Descent.
-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gdSmart :: forall r. (HasDelta r, Floating (Data.Vector.Storable.Vector r))
        => (DualNumberVariables 'DifferentiationSchemeGradient r -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
        -> Int  -- ^ requested number of iterations
        -> Domains r  -- ^ initial parameters
        -> (Domains r, r)
gdSmart f n0 parameters0 = go n0 parameters0 0.1 gradients0 value0 0 where
  varDeltas = generateDeltaVars parameters0
  variables0 = makeDualNumberVariables parameters0 varDeltas
  (gradients0, value0) = dReverseGeneral 1 variables0 f
  go :: Int -> Domains r -> r -> Domains r -> r -> Int
     -> (Domains r, r)
  go 0 parameters !gamma _gradientsPrev _valuePrev !_i = (parameters, gamma)
  go _ parameters 0 _ _ _ = (parameters, 0)
  go n parameters gamma gradientsPrev valuePrev i =
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let parametersNew = updateWithGradient gamma parameters gradientsPrev
        variables = makeDualNumberVariables parametersNew varDeltas
        (gradients, value) = dReverseGeneral 1 variables f
    in if | gradientIsNil gradientsPrev ->
              (parameters, gamma)
          | value > valuePrev ->
              go n parameters (gamma / 2) gradientsPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) parametersNew (gamma * 2) gradients value 0
          | otherwise -> go (pred n) parametersNew gamma gradients value (i + 1)
