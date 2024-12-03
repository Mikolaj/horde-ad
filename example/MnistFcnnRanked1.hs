{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Implementation of fully connected neutral network for classification
-- of MNIST digits with lists of rank 1 tensors (vectors)
-- as the trainable parameters. Sports 2 hidden layers. No mini-batches.
module MnistFcnnRanked1 where

import Prelude

import Control.Exception (assert)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..), inline)

import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorKind
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import MnistData

afcnnMnistLen1 :: Int -> Int -> [Int]
afcnnMnistLen1 widthHidden widthHidden2 =
  replicate widthHidden sizeMnistGlyphInt ++ [widthHidden]
  ++ replicate widthHidden2 widthHidden ++ [widthHidden2]
  ++ replicate sizeMnistLabelInt widthHidden2 ++ [sizeMnistLabelInt]

-- | The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist1Parameters (target :: Target) r =
  ( ( [target (TKR 1 r)]  -- ^ @widthHidden@ copies, length @sizeMnistGlyphInt@
    , target (TKR 1 r) )  -- ^ length @widthHidden@
  , ( [target (TKR 1 r)]  -- ^ @widthHidden2@ copies, length @widthHidden@
    , target (TKR 1 r) )  -- ^ length @widthHidden2@
  , ( [target (TKR 1 r)]  -- ^ @sizeMnistLabelInt@ copies, length @widthHidden2@
    , target (TKR 1 r) )  -- ^ length @sizeMnistLabelInt@
  )

listMatmul1
  :: forall target r.
     (BaseTensor target, LetTensor target, GoodScalar r)
  => target (TKR 1 r) -> [target (TKR 1 r)]
  -> target (TKR 1 r)
listMatmul1 x0 weights = tlet x0 $ \x ->
  let f :: target (TKR 1 r) -> target (TKR 0 r)
      f v = v `rdot0` x
  in rfromList $ NonEmpty.fromList $ map f weights

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @len*@ functions compute the number and dimensions
-- of scalars (none in this case) and vectors of dual number parameters
-- (inputs) to be given to the program.
afcnnMnist1 :: (ADReady target, GoodScalar r)
            => (target (TKR 1 r) -> target (TKR 1 r))
            -> (target (TKR 1 r) -> target (TKR 1 r))
            -> Int -> Int
            -> target (TKR 1 r)
            -> ADFcnnMnist1Parameters target r
            -> target (TKR 1 r)
afcnnMnist1 factivationHidden factivationOutput widthHidden widthHidden2
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let !_A = assert (sizeMnistGlyphInt == rlength datum
                    && length hidden == widthHidden
                    && length hidden2 == widthHidden2) ()
-- TODO: disabled for tests:  && length readout == sizeMnistLabelInt) ()
      hiddenLayer1 = listMatmul1 datum hidden + bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = listMatmul1 nonlinearLayer1 hidden2 + bias2
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = listMatmul1 nonlinearLayer2 readout + biasr
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss1TensorData
  :: (ADReady target, GoodScalar r, Differentiable r)
  => Int -> Int -> (target (TKR 1 r), target (TKR 1 r)) -> ADFcnnMnist1Parameters target r
  -> target (TKR 0 r)
afcnnMnistLoss1TensorData widthHidden widthHidden2 (datum, target) adparams =
  let result = inline afcnnMnist1 logistic softMax1
                                  widthHidden widthHidden2 datum adparams
  in lossCrossEntropyV target result

afcnnMnistLoss1
  :: (ADReady target, GoodScalar r, Differentiable r)
  => Int -> Int -> MnistData r -> ADFcnnMnist1Parameters target r
  -> target (TKR 0 r)
afcnnMnistLoss1 widthHidden widthHidden2 (datum, target) =
  let datum1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) datum
      target1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistLabelInt]) target
  in afcnnMnistLoss1TensorData widthHidden widthHidden2 (datum1, target1)

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest1
  :: forall target r.
     (target ~ RepN, GoodScalar r, Differentiable r)
  => ADFcnnMnist1Parameters target r
  -> Int -> Int
  -> [MnistData r]
  -> HVector RepN
  -> r
afcnnMnistTest1 _ _ _ [] _ = 0
afcnnMnistTest1 valsInit widthHidden widthHidden2 dataList testParams =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) glyph
            nn :: ADFcnnMnist1Parameters target r
               -> target (TKR 1 r)
            nn = inline afcnnMnist1 logistic softMax1
                                    widthHidden widthHidden2 glyph1
            v = Nested.rtoVector $ unRepN $ nn $ unAsHVector $ parseHVector (AsHVector valsInit) (dmkHVector testParams)
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
