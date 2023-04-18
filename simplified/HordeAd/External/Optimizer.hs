-- | A couple of gradient descent scheme implementations.
module HordeAd.External.Optimizer
  ( gdSimple
  , sgd
  , sgdAdam, sgdAdamArgs
  , StateAdam, initialStateAdam
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.MonoTraversable (Element)
import qualified Data.Strict.Vector as Data.Vector
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.DualNumber (ADNum, ADVal)
import HordeAd.Core.Engine
import HordeAd.Core.TensorADVal (ADTensor)
import HordeAd.Core.TensorClass
import HordeAd.External.OptimizerTools

-- | Simple Gradient Descent.
gdSimple :: forall r. ADNum r
         => r
         -> (ADInputs r -> ADVal r)
         -> Int  -- ^ requested number of iterations
         -> Domains r  -- ^ initial parameters
         -> Domains r
gdSimple gamma f n0 parameters0 = go n0 parameters0 where
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  deltaInputs = generateDeltaInputs parameters0
  go :: Int -> Domains r -> Domains r
  go 0 parameters = parameters
  go n parameters =
    let inputs = makeADInputs parameters deltaInputs
        gradients = fst $ revOnADInputs (Just 1) f inputs
        !parametersNew = updateWithGradient gamma parameters gradients
    in go (pred n) parametersNew

-- | Stochastic Gradient Descent.
sgd :: forall r a.
       ( Numeric r, Floating (Vector r), ADTensor r
       , DynamicTensor r, DomainsTensor r, Element r ~ r
       , DTensorOf r ~ OD.Array r, TensorOf 1 r ~ OR.Array 1 r
       , DomainsOf r ~ Data.Vector.Vector (OD.Array r) )
    => r
    -> (a -> ADInputs r -> ADVal r)
    -> [a]  -- ^ training data
    -> Domains r  -- ^ initial parameters
    -> (Domains r, r)
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> Domains r -> (Domains r, r)
  go [] parameters = (parameters, 0)
  go (a : rest) parameters =
    let inputs = makeADInputs parameters deltaInputs
        (gradients, valueNew) = revOnADInputs (Just 1) (f a) inputs
        !parametersNew = updateWithGradient gamma parameters gradients
    in if null rest
       then (parametersNew, valueNew)
       else go rest parametersNew
{-# SPECIALIZE sgd
  :: Double
  -> ((Vector Double, Vector Double)
      -> ADInputs Double
      -> ADVal Double)
  -> [(Vector Double, Vector Double)]
  -> Domains Double
  -> (Domains Double, Double) #-}

sgdAdam :: forall r a.
           ( Numeric r, Floating r, Floating (Vector r), ADTensor r
           , DynamicTensor r, DomainsTensor r, Element r ~ r
           , DTensorOf r ~ OD.Array r, TensorOf 1 r ~ OR.Array 1 r
           , DomainsOf r ~ Data.Vector.Vector (OD.Array r) )
       => (a -> ADInputs r -> ADVal r)
        -> [a]
        -> Domains r
        -> StateAdam r
        -> (Domains r, StateAdam r)
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs :: forall r a.
               ( Numeric r, Floating r, Floating (Vector r), ADTensor r
               , DynamicTensor r, DomainsTensor r, Element r ~ r
               , DTensorOf r ~ OD.Array r, TensorOf 1 r ~ OR.Array 1 r
               , DomainsOf r ~ Data.Vector.Vector (OD.Array r) )
            => ArgsAdam r
            -> (a -> ADInputs r -> ADVal r)
            -> [a]
            -> Domains r
            -> StateAdam r
            -> (Domains r, StateAdam r)
sgdAdamArgs argsAdam f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> Domains r -> StateAdam r -> (Domains r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) parameters stateAdam =
    let inputs = makeADInputs parameters deltaInputs
        gradients = fst $ revOnADInputs (Just 1) (f a) inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew
