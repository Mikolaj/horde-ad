{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistFcnnRanked2 where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.RankedS as OR
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.Domains
import HordeAd.Core.TensorClass
import HordeAd.External.CommonRankedOps
import MnistData

afcnnMnistLen2 :: Int -> Int -> [[Int]]
afcnnMnistLen2 widthHidden widthHidden2 =
  [ [widthHidden, sizeMnistGlyphInt], [widthHidden]
  , [widthHidden2, widthHidden], [widthHidden2]
  , [sizeMnistLabelInt, widthHidden2], [sizeMnistLabelInt] ]

-- The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist2Parameters r =
  ( ( TensorOf 2 r  -- @widthHidden@ copies, length @sizeMnistGlyphInt@
    , TensorOf 1 r )  -- length @widthHidden@
  , ( TensorOf 2 r  -- @widthHidden2@ copies, length @widthHidden@
    , TensorOf 1 r )  -- length @widthHidden2@
  , ( TensorOf 2 r  -- @sizeMnistLabelInt@ copies, length @widthHidden2@
    , TensorOf 1 r )  -- length @sizeMnistLabelInt@
  )

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @len*@ functions compute the number and dimensions
-- of scalars (none in this case) and vectors of dual number parameters
-- (inputs) to be given to the program.
afcnnMnist2 :: ADReady r
            => (TensorOf 1 r -> TensorOf 1 r)
            -> (TensorOf 1 r -> TensorOf 1 r)
            -> TensorOf 1 r
            -> ADFcnnMnist2Parameters r
            -> TensorOf 1 r
afcnnMnist2 factivationHidden factivationOutput
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let !_A = assert (sizeMnistGlyphInt == tlength datum) ()
      hiddenLayer1 = tmatvecmul hidden datum + bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = tmatvecmul hidden2 nonlinearLayer1 + bias2
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = tmatvecmul readout nonlinearLayer2 + biasr
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss2
  :: ADReady r
  => MnistData (Value r) -> ADFcnnMnist2Parameters r
  -> r
afcnnMnistLoss2 (datum, target) =
  let datum1 = tconst $ OR.fromVector [sizeMnistGlyphInt] datum
      target1 = tconst $ OR.fromVector [sizeMnistLabelInt] target
  in afcnnMnistLoss2TensorData (datum1, target1)

afcnnMnistLoss2TensorData
  :: ADReady r
  => (TensorOf 1 r, TensorOf 1 r) -> ADFcnnMnist2Parameters r
  -> r
afcnnMnistLoss2TensorData (datum, target) adparams =
  let result = inline afcnnMnist2 logistic softMax1 datum adparams
  in lossCrossEntropyV target result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest2
  :: forall r. (ADReady r, r ~ Value r)
  => [MnistData r]
  -> ((ADFcnnMnist2Parameters r
       -> TensorOf 1 r)
      -> Vector r)
  -> r
{-# INLINE afcnnMnistTest2 #-}
afcnnMnistTest2 [] _ = 0
afcnnMnistTest2 dataList evalAtTestParams =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = tconst $ OR.fromVector [sizeMnistGlyphInt] glyph
            nn :: ADFcnnMnist2Parameters r
               -> TensorOf 1 r
            nn = inline afcnnMnist2 logistic softMax1 glyph1
            v = evalAtTestParams nn
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
