-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  ) where

import Prelude

import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat)

import HordeAd.Core.Adaptor
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
  g a hVector = HVectorPseudoTensor
                $ toHVector
                $ f a $ parseHVector (fromDValue parameters0)
                $ unHVectorPseudoTensor hVector
  deltaInputs = generateDeltaInputs @ORArray parameters0
  go :: [a] -> HVector ORArray
     -> (HVector ORArray, ORArray r n)
  go [] parameters = (parameters, 0)
  go (a : rest) !parameters =
    let inputs = makeADInputs parameters deltaInputs
        (gradients, valueNew) =
          crevOnADInputs @_ @TKUntyped Nothing (g a)
          $ HVectorPseudoTensor inputs
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
  :: forall f r a y.
     ( RankedOf f ~ ORArray
     , AdaptableHVector (ADVal ORArray) (ADVal f r y) )
  => (a -> HVector (ADVal ORArray) -> ADVal f r y)
  -> [a]
  -> HVector ORArray
  -> StateAdam
  -> (HVector ORArray, StateAdam)
{-# INLINE sgdAdam #-}
sgdAdam = sgdAdamArgs updateWithGradientAdam defaultArgsAdam

sgdAdamArgs
  :: forall f r a y.
     ( RankedOf f ~ ORArray
     , AdaptableHVector (ADVal ORArray) (ADVal f r y) )
  => (ArgsAdam -> StateAdam -> HVector (RankedOf f) -> HVectorOf (RankedOf f)
      -> (HVector (RankedOf f), StateAdam))
  -> ArgsAdam
  -> (a -> HVector (ADVal (RankedOf f)) -> ADVal f r y)
  -> [a]
  -> HVector (RankedOf f)
  -> StateAdam
  -> (HVector (RankedOf f), StateAdam)
{-# INLINE sgdAdamArgs #-}
sgdAdamArgs updateWith argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  g a hVector = HVectorPseudoTensor
                $ toHVector
                $ f a
                $ parseHVector (fromDValue parameters0)
                $ unHVectorPseudoTensor hVector
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> HVector (RankedOf f) -> StateAdam
     -> (HVector (RankedOf f), StateAdam)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs = makeADInputs parameters deltaInputs
        gradients = unHVectorPseudoTensor $ fst
                    $ crevOnADInputs @_ @TKUntyped Nothing (g a)
                    $ HVectorPseudoTensor inputs
        (parametersNew, stateAdamNew) =
          updateWith argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
