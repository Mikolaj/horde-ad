-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( sgd
  , sgdAdam, sgdAdamArgs
  , sgdAdamS, sgdAdamArgsS
  , StateAdam, initialStateAdam
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.Adaptor
import HordeAd.Core.DualNumber (ADVal)
import HordeAd.Core.Engine
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.External.OptimizerTools

-- | Stochastic Gradient Descent.
sgd :: forall n r a. (KnownNat n, GoodScalar r)
    => r
    -> (a -> Domains (ADValClown OD.Array) r -> ADVal (Flip OR.Array) r n)
    -> [a]  -- ^ training data
    -> DomainsOD r  -- ^ initial parameters
    -> (DomainsOD r, Flip OR.Array r n)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  deltaInputs = generateDeltaInputs @(Flip OR.Array) parameters0
  go :: [a] -> DomainsOD r -> (DomainsOD r, Flip OR.Array r n)
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
      -> Domains (ADValClown OD.Array) Double
      -> ADVal (Flip OR.Array) Double 0)
  -> [(Vector Double, Vector Double)]
  -> DomainsOD Double
  -> (DomainsOD Double, Flip OR.Array Double 0) #-}

sgdAdam :: forall r a n. (KnownNat n, GoodScalar r)
        => (a -> Domains (ADValClown OD.Array) r -> ADVal (Flip OR.Array) r n)
        -> [a]
        -> DomainsOD r
        -> StateAdam r
        -> (DomainsOD r, StateAdam r)
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs :: forall r a n. (KnownNat n, GoodScalar r)
            => ArgsAdam r
            -> (a -> Domains (ADValClown OD.Array) r
                -> ADVal (Flip OR.Array) r n)
            -> [a]
            -> DomainsOD r
            -> StateAdam r
            -> (DomainsOD r, StateAdam r)
sgdAdamArgs argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  deltaInputs = generateDeltaInputs @(Flip OR.Array) parameters0
  go :: [a] -> DomainsOD r -> StateAdam r -> (DomainsOD r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs = makeADInputs parameters deltaInputs
        gradients = fst $ revOnADInputs (Just 1) (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew

sgdAdamS :: forall r a sh. (OS.Shape sh, KnownNat (OS.Size sh), GoodScalar r)
         => (a -> Domains (ADValClown OD.Array) r -> ADVal (Flip OS.Array) r sh)
         -> [a]
         -> DomainsOD r
         -> StateAdam r
         -> (DomainsOD r, StateAdam r)
sgdAdamS = sgdAdamArgsS defaultArgsAdam

sgdAdamArgsS :: forall r a sh.
                (OS.Shape sh, KnownNat (OS.Size sh), GoodScalar r)
             => ArgsAdam r
             -> (a -> Domains (ADValClown OD.Array) r
                 -> ADVal (Flip OS.Array) r sh)
             -> [a]
             -> DomainsOD r
             -> StateAdam r
             -> (DomainsOD r, StateAdam r)
sgdAdamArgsS argsAdam f trainingData !parameters0 !stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  deltaInputs = generateDeltaInputs @(Flip OR.Array) @(Flip OS.Array)
                                    parameters0
  go :: [a] -> DomainsOD r -> StateAdam r -> (DomainsOD r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) !parameters !stateAdam =
    let inputs = makeADInputs parameters deltaInputs
        gradients = fst $ revOnADInputsS (Just 1) (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
