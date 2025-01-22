{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Implementation of fully connected neutral network for classification
-- of MNIST digits with lists of rank 1 tensors (vectors)
-- as the trainable parameters. Sports 2 hidden layers. No mini-batches.
module MnistFcnnRanked1 where

import Prelude

import Data.List.NonEmpty qualified as NonEmpty
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..), inline)
import GHC.TypeLits (KnownNat, Nat)

import Data.Array.Nested (ListR (..))
import Data.Array.Nested qualified as Nested

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist1Parameters
       (target :: Target) (widthHidden :: Nat) (widthHidden2 :: Nat) r =
  ( ( ListR widthHidden (target (TKS '[SizeMnistGlyph] r))
    , target (TKS '[widthHidden] r) )
  , ( ListR widthHidden2 (target (TKS '[widthHidden] r))
    , target (TKS '[widthHidden2] r) )
  , ( ListR SizeMnistLabel (target (TKS '[widthHidden2] r))
    , target (TKS '[SizeMnistLabel] r) )
  )

listMatmul1
  :: forall target r w1 w2.
     ( BaseTensor target, LetTensor target, GoodScalar r
     , KnownNat w1, KnownNat w2 )
  => target (TKS '[w1] r) -> [target (TKS '[w1] r)]
  -> target (TKS '[w2] r)
listMatmul1 x0 weights = tlet x0 $ \x ->
  let f :: target (TKS '[w1] r) -> target (TKS '[] r)
      f v = v `sdot0` x
  in sfromList $ NonEmpty.fromList $ map f weights

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
            -> SNat widthHidden -> SNat widthHidden2
            -> target (TKS '[SizeMnistGlyph] r)
            -> ADFcnnMnist1Parameters target widthHidden widthHidden2 r
            -> target (TKR 1 r)
afcnnMnist1 factivationHidden factivationOutput SNat SNat
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let hiddenLayer1 = listMatmul1 datum (toList hidden) + bias
      nonlinearLayer1 = sfromR $ factivationHidden $ rfromS hiddenLayer1
      hiddenLayer2 = listMatmul1 nonlinearLayer1 (toList hidden2) + bias2
      nonlinearLayer2 = sfromR $ factivationHidden $ rfromS hiddenLayer2
      outputLayer = listMatmul1 nonlinearLayer2 (toList readout) + biasr
  in factivationOutput $ rfromS outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss1TensorData
  :: (ADReady target, GoodScalar r, Differentiable r)
  => SNat widthHidden -> SNat widthHidden2
  -> (target (TKR 1 r), target (TKR 1 r))
  -> ADFcnnMnist1Parameters target widthHidden widthHidden2 r
  -> target (TKR 0 r)
afcnnMnistLoss1TensorData widthHidden widthHidden2 (datum, target) adparams =
  let result = inline afcnnMnist1 logistic softMax1
                                  widthHidden widthHidden2 (sfromR datum) adparams
  in lossCrossEntropyV target result

afcnnMnistLoss1
  :: (ADReady target, GoodScalar r, Differentiable r)
  => SNat widthHidden -> SNat widthHidden2
  -> MnistData r
  -> ADFcnnMnist1Parameters target widthHidden widthHidden2 r
  -> target (TKR 0 r)
afcnnMnistLoss1 widthHidden widthHidden2 (datum, target) =
  let datum1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) datum
      target1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistLabelInt]) target
  in afcnnMnistLoss1TensorData widthHidden widthHidden2 (datum1, target1)

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest1
  :: forall target widthHidden widthHidden2 r.
     (target ~ RepN, GoodScalar r, Differentiable r)
  => SNat widthHidden -> SNat widthHidden2
  -> [MnistData r]
  -> ADFcnnMnist1Parameters target widthHidden widthHidden2 r
  -> r
afcnnMnistTest1 _ _ [] _ = 0
afcnnMnistTest1 widthHidden widthHidden2 dataList testParams =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = rconcrete $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) glyph
            nn :: ADFcnnMnist1Parameters target widthHidden widthHidden2 r
               -> target (TKR 1 r)
            nn = inline afcnnMnist1 logistic softMax1
                                    widthHidden widthHidden2 (sfromR glyph1)
            v = Nested.rtoVector $ unRepN $ nn testParams
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
