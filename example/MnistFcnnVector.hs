{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Vector-based (meaning that dual numbers for gradient computation
-- consider vectors, not scalars, as the primitive differentiable type)
-- implementation of fully connected neutral network for classification
-- of MNIST digits. Sports 2 hidden layers. Adaptors-based version.
module MnistFcnnVector where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OD
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Vector)

import HordeAd
import MnistData

sumTrainableInputsL
  :: forall d r. ADModeAndNum d r
  => ADVal d (Vec r) -> [ADVal d (Vec r)]
  -> ADVal d (Vec r)
sumTrainableInputsL x weights =
  let f :: ADVal d (Vec r) -> ADVal d r
      f v = v <.>! x
  in fromList1 $ map f weights

sumConstantDataL
  :: forall d r. ADModeAndNum d r
  => Vector r -> [ADVal d (Vec r)]
  -> ADVal d (Vec r)
sumConstantDataL x weights =
  let f :: ADVal d (Vec r) -> ADVal d r
      f v = v <.>!! vToVec x
  in fromList1 $ map f weights

afcnnMnistLen1 :: Int -> Int -> (Int, [Int], [(Int, Int)], [OD.ShapeL])
afcnnMnistLen1 widthHidden widthHidden2 =
  ( 0
  , replicate widthHidden sizeMnistGlyphInt ++ [widthHidden]
    ++ replicate widthHidden2 widthHidden ++ [widthHidden2]
    ++ replicate sizeMnistLabelInt widthHidden2 ++ [sizeMnistLabelInt]
  , []
  , []
  )

-- The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist1Parameters d r =
  ( ( [ADVal d (Vec r)]  -- @widthHidden@ copies, length @sizeMnistGlyphInt@
    , ADVal d (Vec r) )  -- length @widthHidden@
  , ( [ADVal d (Vec r)]  -- @widthHidden2@ copies, length @widthHidden@
    , ADVal d (Vec r) )  -- length @widthHidden2@
  , ( [ADVal d (Vec r)]  -- @sizeMnistLabelInt@ copies, length @widthHidden2@
    , ADVal d (Vec r) )  -- length @sizeMnistLabelInt@
  )

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @len*@ functions compute the number and dimensions
-- of scalars (none in this case) and vectors of dual number parameters
-- (inputs) to be given to the program.
afcnnMnist1 :: forall d r. ADModeAndNum d r
            => (ADVal d (Vec r) -> ADVal d (Vec r))
            -> (ADVal d (Vec r) -> ADVal d (Vec r))
            -> Int
            -> Int
            -> Vector r
            -> ADFcnnMnist1Parameters d r
            -> ADVal d (Vec r)
afcnnMnist1 factivationHidden factivationOutput widthHidden widthHidden2
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let !_A = assert (sizeMnistGlyphInt == V.length datum
                    && length hidden == widthHidden
                    && length hidden2 == widthHidden2
                    && length readout == sizeMnistLabelInt) ()
      hiddenLayer1 = sumConstantDataL datum hidden + bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = sumTrainableInputsL nonlinearLayer1 hidden2 + bias2
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = sumTrainableInputsL nonlinearLayer2 readout + biasr
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss1
  :: ADModeAndNum d r
  => Int -> Int -> MnistData r -> ADFcnnMnist1Parameters d r
  -> ADVal d r
afcnnMnistLoss1 widthHidden widthHidden2 (datum, target) adparams =
  let result = inline afcnnMnist1 logistic softMaxV
                                  widthHidden widthHidden2 datum adparams
  in lossCrossEntropyV (vToVec target) result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest1
  :: forall r. ADModeAndNum 'ADModeValue r
  => Int -> Int -> [MnistData r]
  -> ((ADFcnnMnist1Parameters 'ADModeValue r
       -> ADVal 'ADModeValue (Vec r))
      -> Vector r)
  -> r
afcnnMnistTest1 widthHidden widthHidden2 dataList evalAtTestParams =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let nn :: ADFcnnMnist1Parameters 'ADModeValue r
               -> ADVal 'ADModeValue (Vec r)
            nn = inline afcnnMnist1 logistic softMaxV
                                    widthHidden widthHidden2 glyph
            v = evalAtTestParams nn
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
