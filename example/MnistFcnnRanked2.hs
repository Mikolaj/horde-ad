{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers. No mini-batches,
-- so the maximum rank of the tensors is 2.
module MnistFcnnRanked2 where

import Prelude

import Data.Array.RankedS qualified as OR
import Data.Kind (Type)
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..), inline)
import GHC.TypeLits (Nat)

import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.Internal.BackendOX (RepN (..))
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
type ADFcnnMnist2ParametersShaped (target :: Target)
                                  (widthHidden :: Nat)
                                  (widthHidden2 :: Nat)
                                  (r :: Type) =
  ( ( target (TKS r '[widthHidden, SizeMnistGlyph])
    , target (TKS r '[widthHidden]) )
  , ( target (TKS Float '[widthHidden2, widthHidden])
    , target (TKS r '[widthHidden2]) )
  , ( target (TKS r '[SizeMnistLabel, widthHidden2])
    , target (TKS r '[SizeMnistLabel]) )
  )

-- | The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist2Parameters (target :: Target) r =
  ( ( target (TKR r 2)
    , target (TKR r 1) )
  , ( target (TKR Float 2)
    , target (TKR r 1) )
  , ( target (TKR r 2)
    , target (TKR r 1) )
  )

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the hidden layers are @widthHidden@ and @widthHidden2@
-- and from these, the @len*@ functions compute the number and dimensions
-- of scalars (none in this case) and vectors of dual number parameters
-- (inputs) to be given to the program.
afcnnMnist2 :: (ADReady target, GoodScalar r, Differentiable r)
            => (target (TKR r 1) -> target (TKR r 1))
            -> (target (TKR r 1) -> target (TKR r 1))
            -> target (TKR r 1)
            -> ADFcnnMnist2Parameters target r
            -> target (TKR r 1)
afcnnMnist2 factivationHidden factivationOutput
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let hiddenLayer1 = rmatvecmul hidden datum + bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = rcast (rmatvecmul hidden2 (rcast nonlinearLayer1)) + bias2
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = rmatvecmul readout nonlinearLayer2 + biasr
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss2TensorData
  :: (ADReady target, GoodScalar r, Differentiable r)
  => (target (TKR r 1), target (TKR r 1)) -> ADFcnnMnist2Parameters target r
  -> target (TKR r 0)
afcnnMnistLoss2TensorData (datum, target) adparams =
  let result = inline afcnnMnist2 logistic softMax1 datum adparams
  in lossCrossEntropyV target result

afcnnMnistLoss2
  :: (ADReady target, GoodScalar r, Differentiable r)
  => MnistData r -> ADFcnnMnist2Parameters target r
  -> target (TKR r 0)
afcnnMnistLoss2 (datum, target) =
  let datum1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) datum
      target1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistLabelInt]) target
  in afcnnMnistLoss2TensorData (datum1, target1)

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest2
  :: forall target r.
     (target ~ RepN, GoodScalar r, Differentiable r)
  => ADFcnnMnist2Parameters target r
  -> [MnistData r]
  -> HVector RepN
  -> r
afcnnMnistTest2 _ [] _ = 0
afcnnMnistTest2 valsInit dataList testParams =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) glyph
            nn :: ADFcnnMnist2Parameters target r
               -> target (TKR r 1)
            nn = inline afcnnMnist2 logistic softMax1 glyph1
            v = OR.toVector $ Nested.rtoOrthotope $ runFlipR $ unRepN $ nn $ unAsHVector $ parseHVector (AsHVector valsInit) (dmkHVector testParams)
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
