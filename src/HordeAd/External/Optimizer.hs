-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  , defaultArgsAdam
  ) where

import Prelude

import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.Ops
import HordeAd.Core.OpsADVal
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.External.OptimizerTools

-- These functions have their SPECIALIZE pragmas in MnistData.

-- | Stochastic Gradient Descent.
sgd :: forall a x z. (KnownSTK x, KnownSTK z)
    => Double
    -> (a -> ADVal RepN x -> ADVal RepN z)
    -> [a]  -- ^ training data
    -> RepN x  -- ^ initial parameters
    -> (RepN x, RepN z)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  ftk = tftk knownSTK parameters0
  deltaInputs :: Delta RepN x
  deltaInputs = generateDeltaInputs ftk
  go :: [a] -> RepN x -> (RepN x, RepN z)
  go [] parameters = (parameters, undefined)
  go (a : rest) !parameters =
    let inputs :: ADVal RepN x
        inputs = dDnotShared parameters deltaInputs
        (gradients, valueNew) = crevOnADInputs Nothing (f a) inputs
        parametersNew = updateWithGradient gamma parameters gradients
    in if null rest
       then (parametersNew, valueNew)
       else go rest parametersNew

-- We inline (possibly causing a binary blowup) until we are able to work around
-- https://gitlab.haskell.org/ghc/ghc/-/issues/23798
-- and specialize.
-- | An implementation of the Adam gradient descent.
sgdAdam
  :: forall a x z . (KnownSTK x, KnownSTK z)
  => (a -> ADVal RepN x -> ADVal RepN z)
  -> [a]
  -> RepN x
  -> StateAdam x
  -> (RepN x, StateAdam x)
{-# INLINE sgdAdam #-}
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs
  :: forall a x z. (KnownSTK x, KnownSTK z)
  => ArgsAdam
  -> (a -> ADVal RepN x -> ADVal RepN z)
  -> [a]
  -> RepN x
  -> StateAdam x
  -> (RepN x, StateAdam x)
{-# INLINE sgdAdamArgs #-}
sgdAdamArgs argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  ftk = tftk knownSTK parameters0
  deltaInputs :: Delta RepN x
  deltaInputs = generateDeltaInputs ftk
  go :: [a] -> RepN x -> StateAdam x -> (RepN x, StateAdam x)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs :: ADVal RepN x
        inputs = dDnotShared parameters deltaInputs
        gradients = fst $ crevOnADInputs Nothing (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
