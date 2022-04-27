{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Scalar-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers.
module HordeAd.Tool.MnistFcnnScalar where

import Prelude

import           Control.Exception (assert)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)

import HordeAd.Core.DualClass (Delta0)
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (DualNumberVariables, var0)
import HordeAd.Tool.MnistData

-- | Compute the output of a neuron, without applying activation function,
-- from trainable inputs in @xs@ and parameters (the bias and weights)
-- at @variables@ starting at @offset@. Useful for neurons in the middle
-- of the network, receiving inputs from other neurons.
sumTrainableInputs
  :: forall r m. DualMonad r m
  => Data.Vector.Vector (DualNumber r) -> Int -> DualNumberVariables r
  -> m (DualNumber r)
sumTrainableInputs xs offset variables = do
  let bias = var0 variables offset
      f :: DualNumber r -> Int -> DualNumber r -> DualNumber r
      f !acc i u =
        let v = var0 variables (offset + 1 + i)
        in acc + u * v
  returnLet $ V.ifoldl' f bias xs

-- | Compute the output of a neuron, without applying activation function,
-- from constant data in @xs@ and parameters (the bias and weights)
-- at @variables@ starting at @offset@. Useful for neurons at the bottom
-- of the network, tasked with ingesting the data.
sumConstantData
  :: forall r m. DualMonad r m
  => Primal (Tensor1 r) -> Int -> DualNumberVariables r -> m (DualNumber r)
sumConstantData xs offset variables = do
  let bias = var0 variables offset
      f :: DualNumber r -> Int -> Primal r -> DualNumber r
      f !acc i r =
        let v = var0 variables (offset + 1 + i)
        in acc + scale r v
  returnLet $ V.ifoldl' f bias xs

hiddenLayerMnist
  :: forall r m. DualMonad r m
  => (DualNumber r -> m (DualNumber r)) -> Primal (Tensor1 r)
  -> DualNumberVariables r -> Int
  -> m (Data.Vector.Vector (DualNumber r))
hiddenLayerMnist factivation input variables width = do
  let nWeightsAndBias = V.length input + 1
      f :: Int -> m (DualNumber r)
      f i = do
        outSum <- sumConstantData input (i * nWeightsAndBias) variables
        factivation outSum
  V.generateM width f

middleLayerMnist
  :: forall r m. DualMonad r m
  => (DualNumber r -> m (DualNumber r)) -> Data.Vector.Vector (DualNumber r)
  -> Int -> DualNumberVariables r -> Int
  -> m (Data.Vector.Vector (DualNumber r))
middleLayerMnist factivation hiddenVec offset variables width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m (DualNumber r)
      f i = do
        outSum <- sumTrainableInputs hiddenVec
                                     (offset + i * nWeightsAndBias)
                                     variables
        factivation outSum
  V.generateM width f

outputLayerMnist
  :: forall r m. DualMonad r m
  => (Data.Vector.Vector (DualNumber r)
      -> m (Data.Vector.Vector (DualNumber r)))
  -> Data.Vector.Vector (DualNumber r) -> Int -> DualNumberVariables r -> Int
  -> m (Data.Vector.Vector (DualNumber r))
outputLayerMnist factivation hiddenVec offset variables width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m (DualNumber r)
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
fcnnMnist0 :: forall r m. DualMonad r m
           => (DualNumber r -> m (DualNumber r))
           -> (Data.Vector.Vector (DualNumber r)
               -> m (Data.Vector.Vector (DualNumber r)))
           -> Int
           -> Int
           -> Primal (Tensor1 r)
           -> DualNumberVariables r
           -> m (Data.Vector.Vector (DualNumber r))
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
  :: DualMonad r m
  => Int -> Int -> MnistData (Primal r) -> DualNumberVariables r
  -> m (DualNumber r)
fcnnMnistLoss0 widthHidden widthHidden2 (input, target) variables = do
  result <- inline fcnnMnist0 logisticAct softMaxAct
                              widthHidden widthHidden2 input variables
  lossCrossEntropy target result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
--
-- The proxy argument is needed only for the (spurious) SPECIALIZE pragma,
-- becuase I can't write @SPECIALIZE fcnnMnistTest0 \@(Delta0 Double)@.
fcnnMnistTest0 :: forall r. IsScalar r
           => Proxy r -> Int -> Int -> [MnistData (Primal r)] -> Domain0 r
           -> Primal r
fcnnMnistTest0 _ widthHidden widthHidden2 inputs params0 =
  let matchesLabels :: MnistData (Primal r) -> Bool
      matchesLabels (glyph, label) =
        let nn = inline (fcnnMnist0 @r) logisticAct softMaxAct
                                        widthHidden widthHidden2 glyph
            value = V.map (\(D r _) -> r)
                    $ primalValueGeneral @r nn
                                         (params0, V.empty, V.empty, V.empty)
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE fcnnMnistTest0 :: Proxy (Delta0 Double) -> Int -> Int -> [MnistData Double] -> Domain0 (Delta0 Double) -> Double #-}
