-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)

import HordeAd.Core.Adaptor
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorConcrete ()
import HordeAd.Core.Types
import HordeAd.External.OptimizerTools
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))

-- These functions have their SPECIALIZE pragmas in MnistData.

-- | Stochastic Gradient Descent.
sgd :: forall n r a. (KnownNat n, GoodScalar r)
    => Double
    -> (a
        -> HVector (ADVal (FlipR OR.Array))
        -> ADVal (FlipR OR.Array) r n)
    -> [a]  -- ^ training data
    -> HVector (FlipR OR.Array)  -- ^ initial parameters
    -> (HVector (FlipR OR.Array), FlipR OR.Array r n)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  g a hVector = hVectorADValToADVal
                $ toHVector
                $ f a $ parseHVector (fromDValue parameters0) hVector
  deltaInputs = generateDeltaInputs @(FlipR OR.Array) parameters0
  go :: [a] -> HVector (FlipR OR.Array)
     -> (HVector (FlipR OR.Array), FlipR OR.Array r n)
  go [] parameters = (parameters, 0)
  go (a : rest) !parameters =
    let inputs = makeADInputs parameters deltaInputs
        (gradients, valueNew) =
          crevOnADInputs Nothing (g a) inputs
        parametersNew = updateWithGradient gamma parameters gradients
    in if null rest
       then (parametersNew, rfromD $ valueNew V.! 0)
       else go rest parametersNew

-- We inline (possibly causing a binary blowup) until we are able to work around
-- https://gitlab.haskell.org/ghc/ghc/-/issues/23798
-- and specialize.
-- | An implementation of the Adam gradient descent.
sgdAdam
  :: forall f r a y.
     ( RankedOf f ~ FlipR OR.Array
     , AdaptableHVector (ADVal (FlipR OR.Array)) (ADVal f r y) )
  => (a -> HVector (ADVal (FlipR OR.Array)) -> ADVal f r y)
  -> [a]
  -> HVector (FlipR OR.Array)
  -> StateAdam
  -> (HVector (FlipR OR.Array), StateAdam)
{-# INLINE sgdAdam #-}
sgdAdam = sgdAdamArgs updateWithGradientAdam defaultArgsAdam

sgdAdamArgs
  :: forall f r a y.
     ( RankedOf f ~ FlipR OR.Array
     , AdaptableHVector (ADVal (FlipR OR.Array)) (ADVal f r y) )
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
  g a hVector = hVectorADValToADVal
                $ toHVector
                $ f a $ parseHVector (fromDValue parameters0) hVector
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> HVector (RankedOf f) -> StateAdam
     -> (HVector (RankedOf f), StateAdam)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs = makeADInputs parameters deltaInputs
        gradients = fst $ crevOnADInputs Nothing (g a) inputs
        (parametersNew, stateAdamNew) =
          updateWith argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
