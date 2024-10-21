{-# LANGUAGE AllowAmbiguousTypes #-}
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

import Data.Proxy (Proxy (Proxy))

import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorConcrete ()
import HordeAd.Core.Types
import HordeAd.External.OptimizerTools
import HordeAd.Internal.BackendOX (ORArray)

-- These functions have their SPECIALIZE pragmas in MnistData.

-- | Stochastic Gradient Descent.
sgd :: forall a z. TensorKind z
    => Double
    -> (a -> HVector (ADVal ORArray) -> Rep (ADVal ORArray) z)
    -> [a]  -- ^ training data
    -> HVector ORArray  -- ^ initial parameters
    -> (HVector ORArray, Rep ORArray z)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  g :: a -> Rep (ADVal ORArray) TKUntyped -> Rep (ADVal ORArray) z
  g a = f a . unHVectorPseudoTensor
  ftk = tshapeFull stensorKind $ HVectorPseudoTensor parameters0
  deltaInputs :: Delta ORArray TKUntyped
  deltaInputs = generateDeltaInputs ftk
  go :: [a] -> HVector ORArray
     -> (HVector ORArray, Rep ORArray z)
  go [] parameters = (parameters, undefined)
  go (a : rest) !parameters =
    let inputs :: Rep (ADVal ORArray) TKUntyped
        inputs = makeADInputs (HVectorPseudoTensor parameters) deltaInputs
        (gradients, valueNew) =
          crevOnADInputs
            (Proxy @ORArray) (stensorKind @TKUntyped) (stensorKind @z)
            Nothing (g a) inputs
        parametersNew = updateWithGradient gamma parameters
                        $ unHVectorPseudoTensor gradients
    in if null rest
       then (parametersNew, valueNew)
       else go rest parametersNew

-- We inline (possibly causing a binary blowup) until we are able to work around
-- https://gitlab.haskell.org/ghc/ghc/-/issues/23798
-- and specialize.
-- | An implementation of the Adam gradient descent.
sgdAdamDeep
  :: forall a x z .(TensorKind x, TensorKind z)
  => (a -> Rep (ADVal ORArray) x -> Rep (ADVal ORArray) z)
  -> [a]
  -> Rep ORArray x
  -> StateAdamDeep x
  -> (Rep ORArray x, StateAdamDeep x)
{-# INLINE sgdAdamDeep #-}
sgdAdamDeep = sgdAdamArgsDeep @a @x @z defaultArgsAdam

sgdAdamArgsDeep
  :: forall a x z. (TensorKind x, TensorKind z)
  => ArgsAdam
  -> (a -> Rep (ADVal ORArray) x -> Rep (ADVal ORArray) z)
  -> [a]
  -> Rep ORArray x
  -> StateAdamDeep x
  -> (Rep ORArray x, StateAdamDeep x)
{-# INLINE sgdAdamArgsDeep #-}
sgdAdamArgsDeep argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  ftk = tshapeFull @ORArray stensorKind parameters0
  deltaInputs :: Delta ORArray x
  deltaInputs = generateDeltaInputs ftk
  go :: [a] -> Rep ORArray x -> StateAdamDeep x
     -> (Rep ORArray x, StateAdamDeep x)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam
   | Dict <- lemTensorKindOfAD (stensorKind @x) =
    let inputs :: Rep (ADVal ORArray) x
        inputs = makeADInputs parameters deltaInputs
        gradients = fst $ crevOnADInputs
                            (Proxy @ORArray) (stensorKind @x) (stensorKind @z)
                            Nothing (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdamDeep @x argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew

-- We inline (possibly causing a binary blowup) until we are able to work around
-- https://gitlab.haskell.org/ghc/ghc/-/issues/23798
-- and specialize.
-- | An implementation of the Adam gradient descent.
sgdAdam
  :: forall a z. TensorKind z
  => (a -> HVector (ADVal ORArray) -> Rep (ADVal ORArray) z)
  -> [a]
  -> HVector ORArray
  -> StateAdam
  -> (HVector ORArray, StateAdam)
{-# INLINE sgdAdam #-}
sgdAdam = sgdAdamArgs @a @z defaultArgsAdam

sgdAdamArgs
  :: forall a z. TensorKind z
  => ArgsAdam
  -> (a -> HVector (ADVal ORArray) -> Rep (ADVal ORArray) z)
  -> [a]
  -> HVector ORArray
  -> StateAdam
  -> (HVector ORArray, StateAdam)
{-# INLINE sgdAdamArgs #-}
sgdAdamArgs argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  g :: a -> Rep (ADVal ORArray) TKUntyped -> Rep (ADVal ORArray) z
  g a = f a . unHVectorPseudoTensor
  ftk = tshapeFull stensorKind $ HVectorPseudoTensor parameters0
  deltaInputs :: Delta ORArray TKUntyped
  deltaInputs = generateDeltaInputs ftk
  go :: [a] -> HVector ORArray -> StateAdam
     -> (HVector ORArray, StateAdam)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs :: Rep (ADVal ORArray) TKUntyped
        inputs = makeADInputs (HVectorPseudoTensor parameters) deltaInputs
        gradients = unHVectorPseudoTensor $ fst
                    $ crevOnADInputs
                        (Proxy @ORArray) (stensorKind @TKUntyped)
                                         (stensorKind @z)
                        Nothing (g a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
