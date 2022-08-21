{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- Needed due to unsafePerformIO:
{-# OPTIONS_GHC -fno-full-laziness -fno-cse #-}
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
import HordeAd.Core.PairOfVectors (DualNumberVariables, var0)
import HordeAd.Tool.MnistData

-- | Compute the output of a neuron, without applying activation function,
-- from trainable inputs in @xs@ and parameters (the bias and weights)
-- at @variables@ starting at @offset@. Useful for neurons in the middle
-- of the network, receiving inputs from other neurons.
sumTrainableInputs
  :: forall d r m. DualMonad d r m
  => Data.Vector.Vector (DualNumber d r) -> Int -> DualNumberVariables d r
  -> m (DualNumber d r)
sumTrainableInputs xs offset variables = do
  let bias = var0 variables offset
      f :: DualNumber d r -> Int -> DualNumber d r -> DualNumber d r
      f !acc i u =
        let v = var0 variables (offset + 1 + i)
        in acc + u * v
  returnLet $ V.ifoldl' f bias xs
{-# SPECIALIZE sumTrainableInputs :: Data.Vector.Vector (DualNumber 'DModeGradient Double) -> Int -> DualNumberVariables 'DModeGradient Double -> DualMonadGradient Double (DualNumber 'DModeGradient Double) #-}

-- | Compute the output of a neuron, without applying activation function,
-- from constant data in @xs@ and parameters (the bias and weights)
-- at @variables@ starting at @offset@. Useful for neurons at the bottom
-- of the network, tasked with ingesting the data.
sumConstantData
  :: forall d r m. DualMonad d r m
  => Vector r -> Int -> DualNumberVariables d r -> m (DualNumber d r)
sumConstantData xs offset variables = do
  let bias = var0 variables offset
      f :: DualNumber d r -> Int -> r -> DualNumber d r
      f !acc i r =
        let v = var0 variables (offset + 1 + i)
        in acc + scale r v
  returnLet $ V.ifoldl' f bias xs
{-# SPECIALIZE sumConstantData :: Vector Double -> Int -> DualNumberVariables 'DModeGradient Double -> DualMonadGradient Double (DualNumber 'DModeGradient Double) #-}

hiddenLayerMnist
  :: forall d r m. DualMonad d r m
  => (DualNumber d r -> m (DualNumber d r)) -> Vector r
  -> DualNumberVariables d r -> Int
  -> m (Data.Vector.Vector (DualNumber d r))
hiddenLayerMnist factivation input variables width = do
  let nWeightsAndBias = V.length input + 1
      f :: Int -> m (DualNumber d r)
      f i = do
        outSum <- sumConstantData input (i * nWeightsAndBias) variables
        factivation outSum
  V.generateM width f

middleLayerMnist
  :: forall d r m. DualMonad d r m
  => (DualNumber d r -> m (DualNumber d r))
  -> Data.Vector.Vector (DualNumber d r)
  -> Int -> DualNumberVariables d r -> Int
  -> m (Data.Vector.Vector (DualNumber d r))
middleLayerMnist factivation hiddenVec offset variables width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m (DualNumber d r)
      f i = do
        outSum <- sumTrainableInputs hiddenVec
                                     (offset + i * nWeightsAndBias)
                                     variables
        factivation outSum
  V.generateM width f

outputLayerMnist
  :: forall d r m. DualMonad d r m
  => (Data.Vector.Vector (DualNumber d r)
      -> m (Data.Vector.Vector (DualNumber d r)))
  -> Data.Vector.Vector (DualNumber d r) -> Int
  -> DualNumberVariables d r -> Int
  -> m (Data.Vector.Vector (DualNumber d r))
outputLayerMnist factivation hiddenVec offset variables width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m (DualNumber d r)
      f i = sumTrainableInputs hiddenVec
                               (offset + i * nWeightsAndBias)
                               variables
  vOfSums <- V.generateM width f
  factivation vOfSums

fcnnMnistLen0 :: Int -> Int -> Int
fcnnMnistLen0 widthHidden widthHidden2 =
  widthHidden * (sizeMnistGlyph + 1)
  + widthHidden2 * (widthHidden + 1)
  + sizeMnistLabel * (widthHidden2 + 1)

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @fcnnMnistLen2@ function computes the number
-- of scalar dual number parameters (variables) to be given to the program.
fcnnMnist0 :: forall d r m. DualMonad d r m
           => (DualNumber d r -> m (DualNumber d r))
           -> (Data.Vector.Vector (DualNumber d r)
               -> m (Data.Vector.Vector (DualNumber d r)))
           -> Int
           -> Int
           -> Vector r
           -> DualNumberVariables d r
           -> m (Data.Vector.Vector (DualNumber d r))
fcnnMnist0 factivationHidden factivationOutput widthHidden widthHidden2
           input variables = do
  let !_A = assert (sizeMnistGlyph == V.length input) ()
  layer1 <- inline hiddenLayerMnist factivationHidden input
                                    variables widthHidden
  let offsetMiddle = widthHidden * (sizeMnistGlyph + 1)
  layer2 <- inline middleLayerMnist factivationHidden layer1
                                    offsetMiddle variables widthHidden2
  let offsetOutput = offsetMiddle + widthHidden2 * (widthHidden + 1)
  inline outputLayerMnist factivationOutput layer2
                          offsetOutput variables sizeMnistLabel

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
fcnnMnistLoss0
  :: DualMonad d r m
  => Int -> Int -> MnistData r -> DualNumberVariables d r
  -> m (DualNumber d r)
fcnnMnistLoss0 widthHidden widthHidden2 (input, target) variables = do
  result <- inline fcnnMnist0 logisticAct softMaxAct
                              widthHidden widthHidden2 input variables
  lossCrossEntropy target result
{-# SPECIALIZE fcnnMnistLoss0 :: Int -> Int -> MnistData Double -> DualNumberVariables 'DModeGradient Double -> DualMonadGradient Double (DualNumber 'DModeGradient Double) #-}

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
fcnnMnistTest0 :: forall r. IsScalar 'DModeValue r
               => Int -> Int -> [MnistData r] -> Domain0 r
               -> r
fcnnMnistTest0 widthHidden widthHidden2 inputs params0 =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let nn = inline (fcnnMnist0 @'DModeValue)
                        logisticAct softMaxAct
                        widthHidden widthHidden2 glyph
            value = V.map (\(D r _) -> r)
                    $ primalValueGeneral nn (params0, V.empty, V.empty, V.empty)
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE fcnnMnistTest0 :: Int -> Int -> [MnistData Double] -> Domain0 Double -> Double #-}
