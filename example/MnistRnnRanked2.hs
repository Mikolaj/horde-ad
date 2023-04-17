{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistRnnRanked2 where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.RankedS as OR
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.TensorClass
import HordeAd.External.CommonRankedOps
import MnistData

sumTrainableInputsL
  :: forall r. Tensor r
  => TensorOf 1 r -> [TensorOf 1 r]
  -> TensorOf 1 r
sumTrainableInputsL x0 weights = tlet x0 $ \x ->
  let f :: TensorOf 1 r -> TensorOf 0 r
      f v = v `tdot0` x
  in tfromList $ map f weights

afcnnMnistLen1 :: Int -> Int -> [Int]
afcnnMnistLen1 widthHidden widthHidden2 =
  replicate widthHidden sizeMnistGlyphInt ++ [widthHidden]
  ++ replicate widthHidden2 widthHidden ++ [widthHidden2]
  ++ replicate sizeMnistLabelInt widthHidden2 ++ [sizeMnistLabelInt]

-- The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist1Parameters r =
  ( ( [TensorOf 1 r]  -- @widthHidden@ copies, length @sizeMnistGlyphInt@
    , TensorOf 1 r )  -- length @widthHidden@
  , ( [TensorOf 1 r]  -- @widthHidden2@ copies, length @widthHidden@
    , TensorOf 1 r )  -- length @widthHidden2@
  , ( [TensorOf 1 r]  -- @sizeMnistLabelInt@ copies, length @widthHidden2@
    , TensorOf 1 r )  -- length @sizeMnistLabelInt@
  )

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @len*@ functions compute the number and dimensions
-- of scalars (none in this case) and vectors of dual number parameters
-- (inputs) to be given to the program.
afcnnMnist1 :: ADReady r
            => (TensorOf 1 r -> TensorOf 1 r)
            -> (TensorOf 1 r -> TensorOf 1 r)
            -> Int
            -> Int
            -> TensorOf 1 r
            -> ADFcnnMnist1Parameters r
            -> TensorOf 1 r
afcnnMnist1 factivationHidden factivationOutput widthHidden widthHidden2
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let !_A = assert (sizeMnistGlyphInt == tlength datum
                    && length hidden == widthHidden
                    && length hidden2 == widthHidden2
                    && length readout == sizeMnistLabelInt) ()
      hiddenLayer1 = sumTrainableInputsL datum hidden + bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = sumTrainableInputsL nonlinearLayer1 hidden2 + bias2
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = sumTrainableInputsL nonlinearLayer2 readout + biasr
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss1
  :: ADReady r
  => Int -> Int -> MnistData (ScalarOf r) -> ADFcnnMnist1Parameters r
  -> r
afcnnMnistLoss1 widthHidden widthHidden2 (datum, target) =
  let datum1 = tconst $ OR.fromVector [sizeMnistGlyphInt] datum
      target1 = tconst $ OR.fromVector [sizeMnistLabelInt] target
  in afcnnMnistLoss1TensorData widthHidden widthHidden2 (datum1, target1)

afcnnMnistLoss1TensorData
  :: ADReady r
  => Int -> Int -> (TensorOf 1 r, TensorOf 1 r) -> ADFcnnMnist1Parameters r
  -> r
afcnnMnistLoss1TensorData widthHidden widthHidden2 (datum, target) adparams =
  let result = inline afcnnMnist1 logistic softMaxV
                                  widthHidden widthHidden2 datum adparams
  in lossCrossEntropyV target result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest1
  :: forall r. (ADReady r, Numeric r)
  => Int -> Int -> [MnistData (ScalarOf r)]
  -> ((ADFcnnMnist1Parameters r
       -> TensorOf 1 r)
      -> Vector r)
  -> r
afcnnMnistTest1 widthHidden widthHidden2 dataList evalAtTestParams =
  let matchesLabels :: MnistData (ScalarOf r) -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = tconst $ OR.fromVector [sizeMnistGlyphInt] glyph
            nn :: ADFcnnMnist1Parameters r
               -> TensorOf 1 r
            nn = inline afcnnMnist1 logistic softMaxV
                                    widthHidden widthHidden2 glyph1
            v = evalAtTestParams nn
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
