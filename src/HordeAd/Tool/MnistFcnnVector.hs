{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Vector-based (meaning that dual numbers for gradient computation
-- consider vectors, not scalars, as the primitive differentiable type)
-- implementation of fully connected neutral network for classification
-- of MNIST digits. Sports 2 hidden layers.
module HordeAd.Tool.MnistFcnnVector where

import Prelude

import           Control.Exception (assert)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.IsTensor
import HordeAd.Core.PairOfVectors (DualNumberVariables, varV)
import HordeAd.Tool.MnistData

sumTrainableInputsV :: IsScalar r
                    => DualNumber (Vector r)
                    -> Int
                    -> DualNumberVariables r
                    -> DualNumber r
sumTrainableInputsV x offset variables =
  let v = varV variables offset
  in v <.>! x

sumTrainableInputsL :: forall r. IsScalar r
                    => DualNumber (Vector r)
                    -> Int
                    -> DualNumberVariables r
                    -> Int
                    -> DualNumber (Vector r)
sumTrainableInputsL x offset variables width =
  let f :: Int -> DualNumber r
      f i = sumTrainableInputsV x (offset + i) variables
  in deltaSeq1 $ V.generate width f

sumConstantDataV :: IsScalar r
                 => Vector r
                 -> Int
                 -> DualNumberVariables r
                 -> DualNumber r
sumConstantDataV x offset variables =
  let v = varV variables offset
  in v <.>!! x

sumConstantDataL :: forall r. IsScalar r
                 => Vector r
                 -> Int
                 -> DualNumberVariables r
                 -> Int
                 -> DualNumber (Vector r)
sumConstantDataL x offset variables width =
  let f :: Int -> DualNumber r
      f i = sumConstantDataV x (offset + i) variables
  in deltaSeq1 $ V.generate width f

lenMnist2V :: Int -> Int -> Int
lenMnist2V _widthHidden _widthHidden2 = 0

lenVectorsMnist2V :: Int -> Int -> Data.Vector.Vector Int
lenVectorsMnist2V widthHidden widthHidden2 =
  V.fromList $ replicate widthHidden sizeMnistGlyph ++ [widthHidden]
               ++ replicate widthHidden2 widthHidden ++ [widthHidden2]
               ++ replicate sizeMnistLabel widthHidden2 ++ [sizeMnistLabel]

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @len*@ functions compute the number and dimensions
-- of scalars (none in this case) and vectors of dual number parameters
-- (variables) to be given to the program.
nnMnist2V :: DeltaMonad r m
          => (DualNumber (Vector r) -> m (DualNumber (Vector r)))
          -> (DualNumber (Vector r) -> m (DualNumber (Vector r)))
          -> Int
          -> Int
          -> Vector r
          -> DualNumberVariables r
          -> m (DualNumber (Vector r))
nnMnist2V factivationHidden factivationOutput widthHidden widthHidden2
          input variables = do
  let !_A = assert (sizeMnistGlyph == V.length input) ()
  let hiddenLayer1 = sumConstantDataL input 0 variables widthHidden
                     + varV variables widthHidden  -- bias
  nonlinearLayer1 <- factivationHidden hiddenLayer1
  let offsetMiddle = widthHidden + 1
      hiddenLayer2 = sumTrainableInputsL nonlinearLayer1 offsetMiddle
                                         variables widthHidden2
                     + varV variables (offsetMiddle + widthHidden2)  -- bias
  nonlinearLayer2 <- factivationHidden hiddenLayer2
  let offsetOutput = offsetMiddle + widthHidden2 + 1
      outputLayer = sumTrainableInputsL nonlinearLayer2 offsetOutput
                                        variables sizeMnistLabel
                    + varV variables (offsetOutput + sizeMnistLabel)  -- bias
  factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
nnMnistLoss2V :: (DeltaMonad r m, Floating r, Floating (Vector r))
              => Int
              -> Int
              -> MnistData r
              -> DualNumberVariables r
              -> m (DualNumber r)
nnMnistLoss2V widthHidden widthHidden2 (input, target) variables = do
  result <- inline nnMnist2V logisticAct softMaxActV
                             widthHidden widthHidden2 input variables
  lossCrossEntropyV target result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
testMnist2V :: forall r. (Ord r, Floating r, IsScalar r, Floating (Vector r))
            => Int -> Int -> [MnistData r] -> (Domain r, DomainV r) -> r
testMnist2V widthHidden widthHidden2 inputs (params, paramsV) =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let nn = inline nnMnist2V logisticAct softMaxActV
                                  widthHidden widthHidden2 glyph
            value = primalValue nn (params, paramsV, V.empty, V.empty)
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
