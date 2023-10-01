{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers. No mini-batches,
-- so the maximum rank of the tensors is 2.
module MnistFcnnRanked2 where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.Kind (Type)
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           GHC.TypeLits (Nat)

import HordeAd.Core.Adaptor
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
type ADFcnnMnist2ParametersShaped (shaped :: ShapedTensorKind)
                                  (widthHidden :: Nat)
                                  (widthHidden2 :: Nat)
                                  (r :: Type) =
  ( ( shaped r '[widthHidden, SizeMnistGlyph]
    , shaped r '[widthHidden] )
  , ( shaped Float '[widthHidden2, widthHidden]
    , shaped r '[widthHidden2] )
  , ( shaped r '[SizeMnistLabel, widthHidden2]
    , shaped r '[SizeMnistLabel] )
  )

-- | The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist2Parameters (ranked :: RankedTensorKind) r =
  ( ( ranked r 2
    , ranked r 1 )
  , ( ranked Float 2
    , ranked r 1 )
  , ( ranked r 2
    , ranked r 1 )
  )

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @len*@ functions compute the number and dimensions
-- of scalars (none in this case) and vectors of dual number parameters
-- (inputs) to be given to the program.
afcnnMnist2 :: (ADReady ranked, GoodScalar r, Differentiable r)
            => (ranked r 1 -> ranked r 1)
            -> (ranked r 1 -> ranked r 1)
            -> ranked r 1
            -> ADFcnnMnist2Parameters ranked r
            -> ranked r 1
afcnnMnist2 factivationHidden factivationOutput
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let !_A = assert (sizeMnistGlyphInt == rlength datum) ()
      hiddenLayer1 = rmatvecmul hidden datum + bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = rcast (rmatvecmul hidden2 (rcast nonlinearLayer1)) + bias2
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = rmatvecmul readout nonlinearLayer2 + biasr
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss2TensorData
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => (ranked r 1, ranked r 1) -> ADFcnnMnist2Parameters ranked r
  -> ranked r 0
afcnnMnistLoss2TensorData (datum, target) adparams =
  let result = inline afcnnMnist2 logistic softMax1 datum adparams
  in lossCrossEntropyV target result

afcnnMnistLoss2
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => MnistData r -> ADFcnnMnist2Parameters ranked r
  -> ranked r 0
afcnnMnistLoss2 (datum, target) =
  let datum1 = rconst $ OR.fromVector [sizeMnistGlyphInt] datum
      target1 = rconst $ OR.fromVector [sizeMnistLabelInt] target
  in afcnnMnistLoss2TensorData (datum1, target1)

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest2
  :: forall ranked r.
     (ranked ~ Flip OR.Array, GoodScalar r, Differentiable r)
  => ADFcnnMnist2Parameters ranked r
  -> [MnistData r]
  -> DomainsOD
  -> r
afcnnMnistTest2 _ [] _ = 0
afcnnMnistTest2 valsInit dataList testParams =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = rconst $ OR.fromVector [sizeMnistGlyphInt] glyph
            nn :: ADFcnnMnist2Parameters ranked r
               -> ranked r 1
            nn = inline afcnnMnist2 logistic softMax1 glyph1
            v = OR.toVector $ runFlip $ nn $ parseDomains valsInit testParams
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
