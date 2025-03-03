-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd, sgdSTK
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  , defaultArgsAdam
  ) where

import Prelude

import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.OpsADVal
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.External.OptimizerTools

-- | Stochastic Gradient Descent.
sgdSTK :: forall a x z.
          STensorKind x
       -> Double  -- ^ gamma (learning_rate?)
       -> (a -> ADVal RepN x -> ADVal RepN z)
       -> [a]  -- ^ training data
       -> RepN x  -- ^ initial parameters
       -> (RepN x, RepN z)
sgdSTK stk gamma f trainingData parameters0 = go trainingData parameters0 where
  zftk = tftkG stk $ unRepN parameters0
  deltaInputs :: Delta RepN x
  deltaInputs = generateDeltaInputs zftk
  go :: [a] -> RepN x -> (RepN x, RepN z)
  go [] parameters = (parameters, undefined)
  go (a : rest) !parameters =
    let inputs :: ADVal RepN x
        inputs = dDnotShared parameters deltaInputs
        (gradients, valueNew) = crevOnADInputs Nothing (f a) zftk inputs
        parametersNew = updateWithGradient gamma stk parameters gradients
    in if null rest
       then (parametersNew, valueNew)
       else go rest parametersNew

sgd :: forall a x z. KnownSTK x
    => Double  -- ^ gamma (learning_rate?)
    -> (a -> ADVal RepN x -> ADVal RepN z)
    -> [a]  -- ^ training data
    -> RepN x  -- ^ initial parameters
    -> (RepN x, RepN z)
sgd = sgdSTK knownSTK

-- We inline (possibly causing a binary blowup) until we are able to work around
-- https://gitlab.haskell.org/ghc/ghc/-/issues/23798
-- and specialize.
-- | An implementation of the Adam gradient descent.
sgdAdam
  :: forall a x z . KnownSTK x
  => (a -> ADVal RepN x -> ADVal RepN z)
  -> [a]
  -> RepN x
  -> StateAdam x
  -> (RepN x, StateAdam x)
{-# INLINE sgdAdam #-}
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs
  :: forall a x z. KnownSTK x
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
  zftk = tftkG knownSTK $ unRepN parameters0
  deltaInputs :: Delta RepN x
  deltaInputs = generateDeltaInputs zftk
  go :: [a] -> RepN x -> StateAdam x -> (RepN x, StateAdam x)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs :: ADVal RepN x
        inputs = dDnotShared parameters deltaInputs
        gradients = fst $ crevOnADInputs Nothing (f a) zftk inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam
            argsAdam stateAdam knownSTK parameters gradients
    in go rest parametersNew stateAdamNew
