-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Domains
import HordeAd.Core.DualNumber (ADTensor, ADVal, IsPrimalR)
import HordeAd.Core.Engine
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.External.OptimizerTools

-- | Stochastic Gradient Descent.
sgd :: forall n r a.
       ( KnownNat n, Numeric r, Show r, Floating (Vector r), ADTensor r
       , IsPrimalR r
       , DTensorOf r ~ OD.Array r, Ranked r ~ Flip OR.Array r )
    => r
    -> (a -> Domains (ADVal r) -> ADVal (TensorOf n r))
    -> [a]  -- ^ training data
    -> Domains r  -- ^ initial parameters
    -> (Domains r, TensorOf n r)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> Domains r -> (Domains r, TensorOf n r)
  go [] parameters = (parameters, 0)
  go (a : rest) !parameters =
    let inputs = makeADInputs parameters deltaInputs
        (gradients, valueNew) = revOnADInputs (Just 1) (f a) inputs
        parametersNew = updateWithGradient gamma parameters gradients
    in if null rest
       then (parametersNew, valueNew)
       else go rest parametersNew
{-# SPECIALIZE sgd
  :: Double
  -> ((Vector Double, Vector Double)
      -> ADInputs Double
      -> ADVal (TensorOf 0 Double))
  -> [(Vector Double, Vector Double)]
  -> Domains Double
  -> (Domains Double, TensorOf 0 Double) #-}

sgdAdam :: forall r a n.
           ( KnownNat n, Numeric r, Floating (Vector r), ADTensor r
           , IsPrimalR r
           , DTensorOf r ~ OD.Array r, Ranked r ~ Flip OR.Array r )
        => (a -> Domains (ADVal r) -> ADVal (TensorOf n r))
        -> [a]
        -> Domains r
        -> StateAdam r
        -> (Domains r, StateAdam r)
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs :: forall r a n.
               ( KnownNat n, Numeric r, Floating (Vector r), ADTensor r
               , IsPrimalR r
               , DTensorOf r ~ OD.Array r, Ranked r ~ Flip OR.Array r )
            => ArgsAdam r
            -> (a -> Domains (ADVal r) -> ADVal (TensorOf n r))
            -> [a]
            -> Domains r
            -> StateAdam r
            -> (Domains r, StateAdam r)
sgdAdamArgs argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> Domains r -> StateAdam r -> (Domains r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs = makeADInputs parameters deltaInputs
        gradients = fst $ revOnADInputs (Just 1) (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
