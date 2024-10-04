-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdam, sgdAdamArgs, defaultArgsAdam
  , StateAdam, initialStateAdam
  ) where

import Prelude

import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat)

import HordeAd.Core.Adaptor
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
sgd :: forall n r a. (KnownNat n, GoodScalar r)
    => Double
    -> (a
        -> HVector (ADVal ORArray)
        -> ADVal ORArray r n)
    -> [a]  -- ^ training data
    -> HVector ORArray  -- ^ initial parameters
    -> (HVector ORArray, ORArray r n)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  g :: a -> Rep (ADVal ORArray) TKUntyped -> Rep (ADVal ORArray) TKUntyped
  g a hVector = HVectorPseudoTensor
                $ V.singleton
                $ DynamicRanked
                $ f a
                $ parseHVector (fromDValue parameters0)
                $ unHVectorPseudoTensor hVector
  deltaInputs = generateDeltaInputs @TKUntyped @ORArray (tshapeFull (stensorKind @TKUntyped) $ HVectorPseudoTensor $ dmkHVector parameters0)
  go :: [a] -> HVector ORArray
     -> (HVector ORArray, ORArray r n)
  go [] parameters = (parameters, 0)
  go (a : rest) !parameters =
    let inputs = makeADInputs (HVectorPseudoTensor $ dmkHVector parameters) deltaInputs
        (gradients, valueNew) =
          crevOnADInputs @_ @TKUntyped Nothing (g a) inputs
        parametersNew = updateWithGradient gamma parameters
                        $ unHVectorPseudoTensor gradients
    in if null rest
       then (parametersNew, rfromD $ unHVectorPseudoTensor valueNew V.! 0)
       else go rest parametersNew

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
sgdAdam = sgdAdamArgs defaultArgsAdam

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
  deltaInputs :: Delta ORArray TKUntyped
  deltaInputs = generateDeltaInputs
                  (tshapeFull stensorKind
                   $ HVectorPseudoTensor parameters0)
  go :: [a] -> HVector ORArray -> StateAdam
     -> (HVector ORArray, StateAdam)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs :: Rep (ADVal ORArray) TKUntyped
        inputs = makeADInputs (HVectorPseudoTensor parameters) deltaInputs
        gradients = unHVectorPseudoTensor $ fst
                    $ crevOnADInputs Nothing (g a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
