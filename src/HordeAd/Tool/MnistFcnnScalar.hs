{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Scalar-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers.
module HordeAd.Tool.MnistFcnnScalar where

import Prelude

import           Control.Exception (assert)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (ADValInputs, at0)
import HordeAd.Tool.MnistData

-- | Compute the output of a neuron, without applying activation function,
-- from trainable inputs in @xs@ and parameters (the bias and weights)
-- at @inputs@ starting at @offset@. Useful for neurons in the middle
-- of the network, receiving inputs from other neurons.
sumTrainableInputs
  :: forall d r. ADModeAndNum d r
  => Data.Vector.Vector (ADVal d r) -> Int -> ADValInputs d r
  -> ADVal d r
sumTrainableInputs xs offset inputs =
  let bias = at0 inputs offset
      f :: ADVal d r -> Int -> ADVal d r -> ADVal d r
      f !acc i u =
        let v = at0 inputs (offset + 1 + i)
        in acc + u * v
  in V.ifoldl' f bias xs
{-# SPECIALIZE sumTrainableInputs :: Data.Vector.Vector (ADVal 'ADModeGradient Double) -> Int -> ADValInputs 'ADModeGradient Double -> ADVal 'ADModeGradient Double #-}

-- | Compute the output of a neuron, without applying activation function,
-- from constant data in @xs@ and parameters (the bias and weights)
-- at @inputs@ starting at @offset@. Useful for neurons at the bottom
-- of the network, tasked with ingesting the data.
sumConstantData
  :: forall d r. ADModeAndNum d r
  => Vector r -> Int -> ADValInputs d r -> ADVal d r
sumConstantData xs offset inputs =
  let bias = at0 inputs offset
      f :: ADVal d r -> Int -> r -> ADVal d r
      f !acc i r =
        let v = at0 inputs (offset + 1 + i)
        in acc + scale r v
  in V.ifoldl' f bias xs
{-# SPECIALIZE sumConstantData :: Vector Double -> Int -> ADValInputs 'ADModeGradient Double -> ADVal 'ADModeGradient Double #-}

hiddenLayerMnist
  :: forall d r. ADModeAndNum d r
  => (ADVal d r -> ADVal d r)
  -> Vector r
  -> ADValInputs d r -> Int
  -> Data.Vector.Vector (ADVal d r)
hiddenLayerMnist factivation datum inputs width =
  let nWeightsAndBias = V.length datum + 1
      f :: Int -> ADVal d r
      f i =
        let outSum = sumConstantData datum (i * nWeightsAndBias) inputs
        in factivation outSum
  in V.generate width f

middleLayerMnist
  :: forall d r. ADModeAndNum d r
  => (ADVal d r -> ADVal d r)
  -> Data.Vector.Vector (ADVal d r)
  -> Int -> ADValInputs d r -> Int
  -> Data.Vector.Vector (ADVal d r)
middleLayerMnist factivation hiddenVec offset inputs width =
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> ADVal d r
      f i =
        let outSum = sumTrainableInputs hiddenVec
                                        (offset + i * nWeightsAndBias)
                                        inputs
        in factivation outSum
  in V.generate width f

outputLayerMnist
  :: forall d r. ADModeAndNum d r
  => (Data.Vector.Vector (ADVal d r)
      -> Data.Vector.Vector (ADVal d r))
  -> Data.Vector.Vector (ADVal d r) -> Int
  -> ADValInputs d r -> Int
  -> Data.Vector.Vector (ADVal d r)
outputLayerMnist factivation hiddenVec offset inputs width =
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> ADVal d r
      f i = sumTrainableInputs hiddenVec
                               (offset + i * nWeightsAndBias)
                               inputs
      vOfSums = V.generate width f
  in factivation vOfSums

fcnnMnistLen0 :: Int -> Int -> Int
fcnnMnistLen0 widthHidden widthHidden2 =
  widthHidden * (sizeMnistGlyphInt + 1)
  + widthHidden2 * (widthHidden + 1)
  + sizeMnistLabelInt * (widthHidden2 + 1)

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @fcnnMnistLen2@ function computes the number
-- of scalar dual number parameters (inputs) to be given to the program.
fcnnMnist0 :: forall d r. ADModeAndNum d r
           => (ADVal d r -> ADVal d r)
           -> (Data.Vector.Vector (ADVal d r)
               -> Data.Vector.Vector (ADVal d r))
           -> Int
           -> Int
           -> Vector r
           -> ADValInputs d r
           -> Data.Vector.Vector (ADVal d r)
fcnnMnist0 factivationHidden factivationOutput widthHidden widthHidden2
           datum inputs =
  let !_A = assert (sizeMnistGlyphInt == V.length datum) ()
      layer1 = inline hiddenLayerMnist factivationHidden datum
                                       inputs widthHidden
      offsetMiddle = widthHidden * (sizeMnistGlyphInt + 1)
      layer2 = inline middleLayerMnist factivationHidden layer1
                                       offsetMiddle inputs widthHidden2
      offsetOutput = offsetMiddle + widthHidden2 * (widthHidden + 1)
  in inline outputLayerMnist factivationOutput layer2
                             offsetOutput inputs sizeMnistLabelInt

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
fcnnMnistLoss0
  :: ADModeAndNum d r
  => Int -> Int -> MnistData r -> ADValInputs d r
  -> ADVal d r
fcnnMnistLoss0 widthHidden widthHidden2 (datum, target) inputs =
  let result = inline fcnnMnist0 logistic softMax
                                 widthHidden widthHidden2 datum inputs
  in lossCrossEntropy target result
{-# SPECIALIZE fcnnMnistLoss0 :: Int -> Int -> MnistData Double -> ADValInputs 'ADModeGradient Double -> ADVal 'ADModeGradient Double #-}

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
fcnnMnistTest0 :: forall r. ADModeAndNum 'ADModeValue r
               => Int -> Int -> [MnistData r] -> Domain0 r
               -> r
fcnnMnistTest0 widthHidden widthHidden2 inputs params0 =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let nn = inline (fcnnMnist0 @'ADModeValue)
                        logistic softMax
                        widthHidden widthHidden2 glyph
            value = V.map (\(D r _) -> r)
                    $ primalValueGeneral nn (params0, V.empty, V.empty, V.empty)
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE fcnnMnistTest0 :: Int -> Int -> [MnistData Double] -> Domain0 Double -> Double #-}
