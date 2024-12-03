-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdamDeep, sgdAdamArgsDeep
  , StateAdamDeep, initialStateAdamDeep
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  , defaultArgsAdam
  ) where

import Prelude

import HordeAd.Core.CarriersADVal
import HordeAd.Core.Delta
import HordeAd.Core.HVectorOps
import HordeAd.Core.OpsADVal
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.External.OptimizerTools

-- These functions have their SPECIALIZE pragmas in MnistData.

-- | Stochastic Gradient Descent.
sgd :: forall a z. TensorKind z
    => Double
    -> (a -> HVector (ADVal RepN) -> ADVal RepN z)
    -> [a]  -- ^ training data
    -> HVector RepN  -- ^ initial parameters
    -> (HVector RepN, RepN z)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  g :: a -> ADVal RepN TKUntyped -> ADVal RepN z
  g a = f a . tunvector
  ftk = FTKUntyped $ voidFromHVector parameters0
  deltaInputs :: Delta RepN TKUntyped
  deltaInputs = generateDeltaInputs ftk
  go :: [a] -> HVector RepN
     -> (HVector RepN, RepN z)
  go [] parameters = (parameters, undefined)
  go (a : rest) !parameters =
    let inputs :: ADVal RepN TKUntyped
        inputs = makeADInputs (RepN parameters) deltaInputs
        (gradients, valueNew) = crevOnADInputs Nothing (g a) inputs
        parametersNew = updateWithGradient gamma parameters
                        $ unRepN gradients
    in if null rest
       then (parametersNew, valueNew)
       else go rest parametersNew

-- We inline (possibly causing a binary blowup) until we are able to work around
-- https://gitlab.haskell.org/ghc/ghc/-/issues/23798
-- and specialize.
-- | An implementation of the Adam gradient descent.
sgdAdamDeep
  :: forall a x z .(TensorKind x, TensorKind z)
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
  go :: [a] -> RepN x -> StateAdamDeep x
     -> (RepN x, StateAdamDeep x)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam
   | Dict <- lemTensorKindOfAD (stensorKind @x) =
    let inputs :: ADVal RepN x
        inputs = makeADInputs parameters deltaInputs
        gradients = fst $ crevOnADInputs Nothing (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdamDeep argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew

-- We inline (possibly causing a binary blowup) until we are able to work around
-- https://gitlab.haskell.org/ghc/ghc/-/issues/23798
-- and specialize.
-- | An implementation of the Adam gradient descent.
sgdAdam
  :: forall a z. TensorKind z
  => (a -> HVector (ADVal RepN) -> ADVal RepN z)
  -> [a]
  -> HVector RepN
  -> StateAdam
  -> (HVector RepN, StateAdam)
{-# INLINE sgdAdam #-}
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs
  :: forall a z. TensorKind z
  => ArgsAdam
  -> (a -> HVector (ADVal RepN) -> ADVal RepN z)
  -> [a]
  -> HVector RepN
  -> StateAdam
  -> (HVector RepN, StateAdam)
{-# INLINE sgdAdamArgs #-}
sgdAdamArgs argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  g :: a -> ADVal RepN TKUntyped -> ADVal RepN z
  g a = f a . tunvector
  ftk = FTKUntyped $ voidFromHVector parameters0
  deltaInputs :: Delta RepN TKUntyped
  deltaInputs = generateDeltaInputs ftk
  go :: [a] -> HVector RepN -> StateAdam
     -> (HVector RepN, StateAdam)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs :: ADVal RepN TKUntyped
        inputs = makeADInputs (RepN parameters) deltaInputs
        gradients = unRepN $ fst
                    $ crevOnADInputs Nothing (g a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
