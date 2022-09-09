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
import HordeAd.Core.PairOfVectors (DualNumberInputs, at1, at2)
import HordeAd.Tool.MnistData

fcnnMnistLen2 :: Int -> Int -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
fcnnMnistLen2 widthHidden widthHidden2 =
  ( 0
  , [widthHidden, widthHidden2, sizeMnistLabelInt]
  , [ (widthHidden, sizeMnistGlyphInt)
    , (widthHidden2, widthHidden)
    , (sizeMnistLabelInt, widthHidden2) ]
  , []
  )

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The width of the layers is determined by the dimensions of the matrices
-- and vectors given as dual number parameters (inputs).
-- The dimensions, in turn, can be computed by the @len*@ functions
-- on the basis of the requested widths, see above.
fcnnMnist2 :: forall d r. IsScalar d r
           => (DualNumber d (Vector r) -> DualNumber d (Vector r))
           -> (DualNumber d (Vector r) -> DualNumber d (Vector r))
           -> Vector r
           -> DualNumberInputs d r
           -> DualNumber d (Vector r)
fcnnMnist2 factivationHidden factivationOutput datum inputs =
  let !_A = assert (sizeMnistGlyphInt == V.length datum) ()
      weightsL0 = at2 inputs 0
      biasesV0 = at1 inputs 0
      weightsL1 = at2 inputs 1
      biasesV1 = at1 inputs 1
      weightsL2 = at2 inputs 2
      biasesV2 = at1 inputs 2
      hiddenLayer1 = weightsL0 #>!! datum + biasesV0
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = weightsL1 #>! nonlinearLayer1 + biasesV1
      nonlinearLayer2 =factivationHidden hiddenLayer2
      outputLayer = weightsL2 #>! nonlinearLayer2 + biasesV2
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
fcnnMnistLoss2
  :: IsScalar d r
  => MnistData r -> DualNumberInputs d r -> DualNumber d r
fcnnMnistLoss2 (datum, target) inputs =
  let result = inline fcnnMnist2 logistic softMaxV datum inputs
  in lossCrossEntropyV target result

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function, using fused
-- softMax and cross entropy as the loss function.
fcnnMnistLossFused2
  :: IsScalar d r
  => MnistData r -> DualNumberInputs d r -> DualNumber d r
fcnnMnistLossFused2 (datum, target) inputs =
  let result = inline fcnnMnist2 logistic id datum inputs
  in lossSoftMaxCrossEntropyV target result

fcnnMnistLossFusedRelu2
  :: IsScalar d r
  => MnistData r -> DualNumberInputs d r -> DualNumber d r
fcnnMnistLossFusedRelu2 (datum, target) inputs =
  let result = inline fcnnMnist2 relu id datum inputs
  in lossSoftMaxCrossEntropyV target result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
fcnnMnistTest2
  :: forall r. IsScalar 'DModeValue r
  => [MnistData r] -> Domains r -> r
fcnnMnistTest2 inputs parameters =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let nn = inline (fcnnMnist2 @'DModeValue) logistic softMaxV glyph
            value = primalValue nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
