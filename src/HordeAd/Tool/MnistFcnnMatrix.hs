{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Matrix-based (meaning that dual numbers for gradient computation
-- consider matrices, not scalars, as the primitive differentiable type)
-- implementation of fully connected neutral network for classification
-- of MNIST digits. Sports 2 hidden layers.
module HordeAd.Tool.MnistFcnnMatrix where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OT
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (DualNumberVariables, var1, var2)
import HordeAd.Tool.MnistData

fcnnMnistLen2 :: Int -> Int -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
fcnnMnistLen2 widthHidden widthHidden2 =
  ( 0
  , [widthHidden, widthHidden2, sizeMnistLabel]
  , [ (widthHidden, sizeMnistGlyph)
    , (widthHidden2, widthHidden)
    , (sizeMnistLabel, widthHidden2) ]
  , []
  )

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The width of the layers is determined by the dimensions of the matrices
-- and vectors given as dual number parameters (variables).
-- The dimensions, in turn, can be computed by the @len*@ functions
-- on the basis of the requested widths, see above.
fcnnMnist2 :: forall d r m. DualMonad d r m
           => (DualNumber d (Vector r) -> m (DualNumber d (Vector r)))
           -> (DualNumber d (Vector r) -> m (DualNumber d (Vector r)))
           -> Vector r
           -> DualNumberVariables d r
           -> m (DualNumber d (Vector r))
fcnnMnist2 factivationHidden factivationOutput input variables = do
  let !_A = assert (sizeMnistGlyph == V.length input) ()
      weightsL0 = var2 variables 0
      biasesV0 = var1 variables 0
      weightsL1 = var2 variables 1
      biasesV1 = var1 variables 1
      weightsL2 = var2 variables 2
      biasesV2 = var1 variables 2
  let hiddenLayer1 = weightsL0 #>!! input + biasesV0
  nonlinearLayer1 <- factivationHidden hiddenLayer1
  let hiddenLayer2 = weightsL1 #>! nonlinearLayer1 + biasesV1
  nonlinearLayer2 <- factivationHidden hiddenLayer2
  let outputLayer = weightsL2 #>! nonlinearLayer2 + biasesV2
  factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
fcnnMnistLoss2
  :: DualMonad d r m
  => MnistData r -> DualNumberVariables d r -> m (DualNumber d r)
fcnnMnistLoss2 (input, target) variables = do
  result <- inline fcnnMnist2 logisticAct softMaxActV input variables
  lossCrossEntropyV target result

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function, using fused
-- softMax and cross entropy as the loss function.
fcnnMnistLossFused2
  :: DualMonad d r m
  => MnistData r -> DualNumberVariables d r -> m (DualNumber d r)
fcnnMnistLossFused2 (input, target) variables = do
  result <- inline fcnnMnist2 logisticAct return input variables
  lossSoftMaxCrossEntropyV target result

fcnnMnistLossFusedRelu2
  :: DualMonad d r m
  => MnistData r -> DualNumberVariables d r -> m (DualNumber d r)
fcnnMnistLossFusedRelu2 (input, target) variables = do
  result <- inline fcnnMnist2 reluAct return input variables
  lossSoftMaxCrossEntropyV target result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
fcnnMnistTest2
  :: forall r. IsScalar 'DModeGradient r
  => [MnistData r] -> Domains r -> r
fcnnMnistTest2 inputs parameters =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let nn = inline (fcnnMnist2 @'DModeGradient) logisticAct softMaxActV glyph
            value = primalValue nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
