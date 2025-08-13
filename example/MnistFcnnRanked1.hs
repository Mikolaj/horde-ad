{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Implementation of fully connected neutral network for classification
-- of MNIST digits with sized lists of rank 1 tensors (vectors)
-- as the trainable parameters. Sports 2 hidden layers. No mini-batches.
-- This is an exotic and fundamentally inefficient way of implementing nns,
-- but it's valuable for comparative benchmarking.
module MnistFcnnRanked1 where

import Prelude

import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Ranked.Shape

import HordeAd
import HordeAd.Core.Ops (tfromListR)
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist1Parameters
       (target :: Target) (widthHidden :: Nat) (widthHidden2 :: Nat) r =
  ( ( ListR widthHidden (target (TKS '[SizeMnistGlyph] r))
    , target (TKS '[widthHidden] r) )
  , ( ListR widthHidden2 (target (TKS '[widthHidden] Float))
    , target (TKS '[widthHidden2] r) )
  , ( ListR SizeMnistLabel (target (TKS '[widthHidden2] r))
    , target (TKS '[SizeMnistLabel] r) )
  )

-- | An ad-hoc matrix multiplication analogue for matrices represented
-- as lists of vectors.
listMatmul1
  :: forall target r w1 w2.
     (ADReady target, NumScalar r, KnownNat w1)
  => target (TKS '[w1] r) -> ListR w2 (target (TKS '[w1] r))
  -> target (TKS '[w2] r)
{-# INLINE listMatmul1 #-}  -- this doesn't want to specialize
listMatmul1 x0 weights = tlet x0 $ \x ->
  let f :: target (TKS '[w1] r) -> target (TKS '[] r)
      f v = v `sdot0` x
  in tfromListR knownSTK $ f <$> weights

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the two hidden layers are @widthHidden@ and @widthHidden2@,
-- respectively.
afcnnMnist1 :: forall target r widthHidden widthHidden2.
               (ADReady target, NumScalar r, Differentiable r)
            => (forall n. KnownNat n
                => target (TKS '[n] r) -> target (TKS '[n] r))
            -> (target (TKS '[SizeMnistLabel] r)
                -> target (TKS '[SizeMnistLabel] r))
            -> SNat widthHidden -> SNat widthHidden2
            -> target (TKS '[SizeMnistGlyph] r)
            -> ADFcnnMnist1Parameters target widthHidden widthHidden2 r
            -> target (TKR 1 r)
afcnnMnist1 factivationHidden factivationOutput SNat SNat
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let hiddenLayer1 = listMatmul1 datum hidden + bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = scast (listMatmul1 (scast nonlinearLayer1) hidden2) + bias2
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = listMatmul1 nonlinearLayer2 readout + biasr
      result :: target (TKS '[SizeMnistLabel] r)
      result = factivationOutput outputLayer
  in rfromS result

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss1
  :: (ADReady target, NumScalar r, Differentiable r)
  => SNat widthHidden -> SNat widthHidden2
  -> (target (TKR 1 r), target (TKR 1 r))
  -> ADFcnnMnist1Parameters target widthHidden widthHidden2 r
  -> target (TKScalar r)
afcnnMnistLoss1 widthHidden widthHidden2 (datum, target) adparams =
  let result = afcnnMnist1 logisticS softMax1S
                           widthHidden widthHidden2 (sfromR datum) adparams
  in lossCrossEntropyV target result
-- {-# SPECIALIZE afcnnMnistLoss1 :: (NumScalar r, Differentiable r) => SNat widthHidden -> SNat widthHidden2 -> (AstTensor AstMethodLet FullSpan (TKR 1 r), AstTensor AstMethodLet FullSpan (TKR 1 r)) -> ADFcnnMnist1Parameters (AstTensor AstMethodLet FullSpan) widthHidden widthHidden2 r -> AstTensor AstMethodLet FullSpan (TKScalar r) #-}

-- TODO: RULE left-hand side too complicated to desugar:
-- {-# SPECIALIZE afcnnMnistLoss1 :: SNat widthHidden -> SNat widthHidden2 -> (AstTensor AstMethodLet FullSpan (TKR 1 Double), AstTensor AstMethodLet FullSpan (TKR 1 Double)) -> ADFcnnMnist1Parameters (AstTensor AstMethodLet FullSpan) widthHidden widthHidden2 Double -> AstTensor AstMethodLet FullSpan (TKScalar Double) #-}
-- {-# SPECIALIZE afcnnMnistLoss1 :: SNat widthHidden -> SNat widthHidden2 -> (AstTensor AstMethodLet FullSpan (TKR 1 Float), AstTensor AstMethodLet FullSpan (TKR 1 Float)) -> ADFcnnMnist1Parameters (AstTensor AstMethodLet FullSpan) widthHidden widthHidden2 Float -> AstTensor AstMethodLet FullSpan (TKScalar Float) #-}
-- {-# SPECIALIZE afcnnMnistLoss1 :: SNat widthHidden -> SNat widthHidden2 -> (ADVal Concrete (TKR 1 Double), ADVal Concrete (TKR 1 Double)) -> ADFcnnMnist1Parameters (ADVal Concrete) widthHidden widthHidden2 Double -> ADVal Concrete (TKScalar Double) #-}
-- {-# SPECIALIZE afcnnMnistLoss1 :: SNat widthHidden -> SNat widthHidden2 -> (ADVal Concrete (TKR 1 Float), ADVal Concrete (TKR 1 Float)) -> ADFcnnMnist1Parameters (ADVal Concrete) widthHidden widthHidden2 Float -> ADVal Concrete (TKScalar Float) #-}

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest1
  :: forall target widthHidden widthHidden2 r.
     (target ~ Concrete, NumScalar r, Differentiable r)
  => SNat widthHidden -> SNat widthHidden2
  -> [MnistDataLinearR r]
  -> ADFcnnMnist1Parameters target widthHidden widthHidden2 r
  -> r
afcnnMnistTest1 _ _ [] _ = 0
afcnnMnistTest1 widthHidden widthHidden2 dataList testParams =
  let matchesLabels :: MnistDataLinearR r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = rconcrete glyph
            nn :: ADFcnnMnist1Parameters target widthHidden widthHidden2 r
               -> target (TKR 1 r)
            nn = afcnnMnist1 logisticS softMax1S
                             widthHidden widthHidden2 (sfromR glyph1)
            v = rtoVector $ nn testParams
        in V.maxIndex v == V.maxIndex (Nested.rtoVector label)
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
