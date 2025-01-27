-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdamDeep, sgdAdamArgsDeep
  , StateAdamDeep, initialStateAdamDeep
  , defaultArgsAdam
  ) where

import Prelude

import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.OpsADVal
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.External.OptimizerTools

-- These functions have their SPECIALIZE pragmas in MnistData.

-- | Stochastic Gradient Descent.
sgd :: forall a x z. (TensorKind x, TensorKind z)
    => Double
    -> (a -> ADVal RepN x -> ADVal RepN z)
    -> [a]  -- ^ training data
    -> RepN x  -- ^ initial parameters
    -> (RepN x, RepN z)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  ftk = tftk stensorKind parameters0
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
sgdAdamDeep
  :: forall a x z . (TensorKind x, TensorKind z)
  => (a -> ADVal RepN x -> ADVal RepN z)
  -> [a]
  -> RepN x
  -> StateAdamDeep x
  -> (RepN x, StateAdamDeep x)
{-# INLINE sgdAdamDeep #-}
sgdAdamDeep = sgdAdamArgsDeep defaultArgsAdam

sgdAdamArgsDeep
  :: forall a x z. (TensorKind x, TensorKind z)
  => ArgsAdam
  -> (a -> ADVal RepN x -> ADVal RepN z)
  -> [a]
  -> RepN x
  -> StateAdamDeep x
  -> (RepN x, StateAdamDeep x)
{-# INLINE sgdAdamArgsDeep #-}
sgdAdamArgsDeep argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  ftk = tftk stensorKind parameters0
  deltaInputs :: Delta RepN x
  deltaInputs = generateDeltaInputs ftk
  go :: [a] -> RepN x -> StateAdamDeep x -> (RepN x, StateAdamDeep x)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam
   | Dict <- lemTensorKindOfAD (stensorKind @x) =
    let inputs :: ADVal RepN x
        inputs = dDnotShared parameters deltaInputs
        gradients = fst $ crevOnADInputs Nothing (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdamDeep argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
