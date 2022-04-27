{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
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

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (DualNumberVariables, var1)
import HordeAd.Tool.MnistData

sumTrainableInputsV
  :: IsScalar r
  => DualNumber (Tensor1 r) -> Int -> DualNumberVariables r -> DualNumber r
sumTrainableInputsV x offset variables =
  let v = var1 variables offset
  in v <.>! x

sumTrainableInputsL
  :: forall r. IsScalar r
  => DualNumber (Tensor1 r) -> Int -> DualNumberVariables r -> Int
  -> DualNumber (Tensor1 r)
sumTrainableInputsL x offset variables width =
  let f :: Int -> DualNumber r
      f i = sumTrainableInputsV x (offset + i) variables
  in seq1 $ V.generate width f

sumConstantDataV
  :: IsScalar r
  => Primal (Tensor1 r) -> Int -> DualNumberVariables r -> DualNumber r
sumConstantDataV x offset variables =
  let v = var1 variables offset
  in v <.>!! x

sumConstantDataL
  :: forall r. IsScalar r
  => Primal (Tensor1 r) -> Int -> DualNumberVariables r -> Int
  -> DualNumber (Tensor1 r)
sumConstantDataL x offset variables width =
  let f :: Int -> DualNumber r
      f i = sumConstantDataV x (offset + i) variables
  in seq1 $ V.generate width f

fcnnMnistLen1 :: Int -> Int -> Int
fcnnMnistLen1 _widthHidden _widthHidden2 = 0

lenVectorsMnist1 :: Int -> Int -> Data.Vector.Vector Int
lenVectorsMnist1 widthHidden widthHidden2 =
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
fcnnMnist1 :: forall r m. DualMonad r m
          => (DualNumber (Tensor1 r) -> m (DualNumber (Tensor1 r)))
          -> (DualNumber (Tensor1 r) -> m (DualNumber (Tensor1 r)))
          -> Int
          -> Int
          -> Primal (Tensor1 r)
          -> DualNumberVariables r
          -> m (DualNumber (Tensor1 r))
fcnnMnist1 factivationHidden factivationOutput widthHidden widthHidden2
          input variables = do
  let !_A = assert (sizeMnistGlyph == V.length input) ()
  let hiddenLayer1 = sumConstantDataL input 0 variables widthHidden
                     + var1 variables widthHidden  -- bias
  nonlinearLayer1 <- factivationHidden hiddenLayer1
  let offsetMiddle = widthHidden + 1
      hiddenLayer2 = sumTrainableInputsL nonlinearLayer1 offsetMiddle
                                         variables widthHidden2
                     + var1 variables (offsetMiddle + widthHidden2)  -- bias
  nonlinearLayer2 <- factivationHidden hiddenLayer2
  let offsetOutput = offsetMiddle + widthHidden2 + 1
      outputLayer = sumTrainableInputsL nonlinearLayer2 offsetOutput
                                        variables sizeMnistLabel
                    + var1 variables (offsetOutput + sizeMnistLabel)  -- bias
  factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
fcnnMnistLoss1
  :: DualMonad r m
  => Int -> Int -> MnistData (Primal r) -> DualNumberVariables r
  -> m (DualNumber r)
fcnnMnistLoss1 widthHidden widthHidden2 (input, target) variables = do
  result <- inline fcnnMnist1 logisticAct softMaxActV
                            widthHidden widthHidden2 input variables
  lossCrossEntropyV target result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
fcnnMnistTest1
  :: forall r. IsScalar r
  => Int -> Int -> [MnistData (Primal r)] -> (Domain0 r, Domain1 r) -> Primal r
fcnnMnistTest1 widthHidden widthHidden2 inputs (params0, params1) =
  let matchesLabels :: MnistData (Primal r) -> Bool
      matchesLabels (glyph, label) =
        let nn = inline (fcnnMnist1 @r) logisticAct softMaxActV
                                      widthHidden widthHidden2 glyph
            value = primalValue nn (params0, params1, V.empty, V.empty)
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
