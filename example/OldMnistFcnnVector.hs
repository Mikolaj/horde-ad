{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Vector-based (meaning that dual numbers for gradient computation
-- consider vectors, not scalars, as the primitive differentiable type)
-- implementation of fully connected neutral network for classification
-- of MNIST digits. Sports 2 hidden layers.
-- Written in the old style without adaptors and instead directly
-- specyfing the layout of trainable parameter chunks in ADInputs.
module OldMnistFcnnVector where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OD
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Vector)

import HordeAd
import MnistData

sumTrainableInputsV
  :: ADModeAndNum d r
  => ADVal d (Vec r) -> Int -> ADInputs d r -> ADVal d r
sumTrainableInputsV x offset inputs =
  let v = at1 inputs offset
  in v <.>! x

sumTrainableInputsL
  :: forall d r. ADModeAndNum d r
  => ADVal d (Vec r) -> Int -> ADInputs d r -> Int
  -> ADVal d (Vec r)
sumTrainableInputsL x offset inputs width =
  let f :: Int -> ADVal d r
      f i = sumTrainableInputsV x (offset + i) inputs
  in fromVector1 $ V.generate width f

sumConstantDataV
  :: ADModeAndNum d r
  => Vector r -> Int -> ADInputs d r -> ADVal d r
sumConstantDataV x offset inputs =
  let v = at1 inputs offset
  in v <.>!! vToVec x

sumConstantDataL
  :: forall d r. ADModeAndNum d r
  => Vector r -> Int -> ADInputs d r -> Int
  -> ADVal d (Vec r)
sumConstantDataL x offset inputs width =
  let f :: Int -> ADVal d r
      f i = sumConstantDataV x (offset + i) inputs
  in fromVector1 $ V.generate width f

fcnnMnistLen1 :: Int -> Int -> (Int, [Int], [(Int, Int)], [OD.ShapeL])
fcnnMnistLen1 widthHidden widthHidden2 =
  ( 0
  , replicate widthHidden sizeMnistGlyphInt ++ [widthHidden]
    ++ replicate widthHidden2 widthHidden ++ [widthHidden2]
    ++ replicate sizeMnistLabelInt widthHidden2 ++ [sizeMnistLabelInt]
  , []
  , []
  )

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @len*@ functions compute the number and dimensions
-- of scalars (none in this case) and vectors of dual number parameters
-- (inputs) to be given to the program.
fcnnMnist1 :: forall d r. ADModeAndNum d r
           => (ADVal d (Vec r) -> ADVal d (Vec r))
           -> (ADVal d (Vec r) -> ADVal d (Vec r))
           -> Int
           -> Int
           -> Vector r
           -> ADInputs d r
           -> ADVal d (Vec r)
fcnnMnist1 factivationHidden factivationOutput widthHidden widthHidden2
          datum inputs =
  let !_A = assert (sizeMnistGlyphInt == V.length datum) ()
      hiddenLayer1 = sumConstantDataL datum 0 inputs widthHidden
                     + at1 inputs widthHidden  -- bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      offsetMiddle = widthHidden + 1
      hiddenLayer2 = sumTrainableInputsL nonlinearLayer1 offsetMiddle
                                         inputs widthHidden2
                     + at1 inputs (offsetMiddle + widthHidden2)  -- bias
      nonlinearLayer2 = factivationHidden hiddenLayer2
      offsetOutput = offsetMiddle + widthHidden2 + 1
      outputLayer = sumTrainableInputsL nonlinearLayer2 offsetOutput
                                        inputs sizeMnistLabelInt
                    + at1 inputs (offsetOutput + sizeMnistLabelInt)  -- bias
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
fcnnMnistLoss1
  :: ADModeAndNum d r
  => Int -> Int -> MnistData r -> ADInputs d r
  -> ADVal d r
fcnnMnistLoss1 widthHidden widthHidden2 (datum, target) inputs =
  let result = inline fcnnMnist1 logistic softMaxV
                                 widthHidden widthHidden2 datum inputs
  in lossCrossEntropyV (constant $ vToVec target) result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
fcnnMnistTest1
  :: forall r. ADModeAndNum 'ADModeValue r
  => Int -> Int -> [MnistData r] -> (Vector r, Domain1 r) -> r
fcnnMnistTest1 widthHidden widthHidden2 dataList (params0, params1) =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let nn = inline fcnnMnist1 logistic softMaxV
                                   widthHidden widthHidden2 glyph
            v = valueOnDomains nn (domainsFrom01 params0 params1)
        in V.maxIndex (vecToV v) == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
