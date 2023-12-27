-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           GHC.TypeLits (KnownNat)

import HordeAd.Core.Delta (DualPart (..))
import HordeAd.Core.DualNumber
import HordeAd.Core.TensorADVal ()
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.OptimizerTools

-- These functions have their SPECIALIZE pragmas in MnistData.

-- | Stochastic Gradient Descent.
sgd :: forall n r a. (KnownNat n, GoodScalar r)
    => Double
    -> (a
        -> Domains (ADVal (Flip OR.Array))
        -> ADVal (Flip OR.Array) r n)
    -> [a]  -- ^ training data
    -> DomainsOD  -- ^ initial parameters
    -> (DomainsOD, Flip OR.Array r n)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  deltaInputs = generateDeltaInputs @(Flip OR.Array) parameters0
  go :: [a] -> DomainsOD -> (DomainsOD, Flip OR.Array r n)
  go [] parameters = (parameters, 0)
  go (a : rest) !parameters =
    let inputs = makeADInputs parameters deltaInputs
        (gradients, valueNew) = crevOnADInputs (Just 1) (f a) inputs
        parametersNew = updateWithGradient gamma parameters gradients
    in if null rest
       then (parametersNew, valueNew)
       else go rest parametersNew

-- | An implementation of the Adam gradient descent.
sgdAdam
  :: forall f r a y.
     ( RankedTensor (ADVal (RankedOf f))
     , DualPart f, UnletGradient f, HasSingletonDict y, GoodScalar r
     , RankedOf f ~ Flip OR.Array, Num (f r y))
  => (a -> Domains (ADVal (RankedOf f)) -> ADVal f r y)
  -> [a]
  -> DomainsOD
  -> StateAdam
  -> (DomainsOD, StateAdam)
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs
  :: forall f r a y.
     ( RankedTensor (ADVal (RankedOf f))
     , DualPart f, UnletGradient f, GoodScalar r, HasSingletonDict y
     , RankedOf f ~ Flip OR.Array, Num (f r y) )
  => ArgsAdam
  -> (a -> Domains (ADVal (RankedOf f)) -> ADVal f r y)
  -> [a]
  -> DomainsOD
  -> StateAdam
  -> (DomainsOD, StateAdam)
sgdAdamArgs argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> DomainsOD -> StateAdam -> (DomainsOD, StateAdam)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs = makeADInputs parameters deltaInputs
        gradients = fst $ crevOnADInputs (Just 1) (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
