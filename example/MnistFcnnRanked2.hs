{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers. No mini-batches,
-- so the maximum rank tensors being used is 2.
module MnistFcnnRanked2 where

import Prelude

import Data.Vector.Generic qualified as V
import GHC.Exts (inline)
import GHC.TypeLits (Nat)
import System.Random

import Data.Array.Nested (ShR (..))
import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Engine
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
type ADFcnnMnist2ParametersShaped
       (target :: Target) (widthHidden :: Nat) (widthHidden2 :: Nat) r =
  ( ( target (TKS '[widthHidden, SizeMnistGlyph] r)
    , target (TKS '[widthHidden] r) )
  , ( target (TKS '[widthHidden2, widthHidden] Float)
    , target (TKS '[widthHidden2] r) )
  , ( target (TKS '[SizeMnistLabel, widthHidden2] r)
    , target (TKS '[SizeMnistLabel] r) )
  )

-- | The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist2Parameters (target :: Target) r =
  ( ( target (TKR 2 r)
    , target (TKR 1 r) )
  , ( target (TKR 2 Float)
    , target (TKR 1 r) )
  , ( target (TKR 2 r)
    , target (TKR 1 r) )
  )

type XParams2 r = X (MnistFcnnRanked2.ADFcnnMnist2Parameters RepN r)

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the two hidden layers are @widthHidden@ and @widthHidden2@,
-- respectively.
afcnnMnist2 :: (ADReady target, GoodScalar r, Differentiable r)
            => (target (TKR 1 r) -> target (TKR 1 r))
            -> (target (TKR 1 r) -> target (TKR 1 r))
            -> target (TKR 1 r)
            -> ADFcnnMnist2Parameters target r
            -> target (TKR 1 r)
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
afcnnMnistLoss2
  :: (ADReady target, GoodScalar r, Differentiable r)
  => (target (TKR 1 r), target (TKR 1 r)) -> ADFcnnMnist2Parameters target r
  -> target (TKScalar r)
afcnnMnistLoss2 (datum, target) adparams =
  let result = inline afcnnMnist2 logistic softMax1 datum adparams
  in lossCrossEntropyV target result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest2
  :: forall target r.
     (target ~ RepN, GoodScalar r, Differentiable r)
  => [MnistDataLinearR r]
  -> ADFcnnMnist2Parameters target r
  -> r
afcnnMnistTest2 [] _ = 0
afcnnMnistTest2 dataList testParams =
  let matchesLabels :: MnistDataLinearR r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = rconcrete glyph
            nn :: ADFcnnMnist2Parameters target r
               -> target (TKR 1 r)
            nn = inline afcnnMnist2 logistic softMax1 glyph1
            v = Nested.rtoVector $ unRepN $ nn testParams
        in V.maxIndex v == V.maxIndex (Nested.rtoVector label)
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)

mnistTrainBench2VTOGradient
  :: forall r. (GoodScalar r, Differentiable r, Random r)
  => Double -> StdGen -> Int -> Int
  -> ( RepN (XParams2 r)
     , AstArtifactRev
         (TKProduct
            (XParams2 r)
            (TKProduct (TKR2 1 (TKScalar r))
                       (TKR2 1 (TKScalar r))))
         (TKScalar r) )
mnistTrainBench2VTOGradient range seed widthHidden widthHidden2 =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  -- Initial parameter generation is counted as part of compilation time.
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                                   RepN widthHidden widthHidden2 r)))
                      range seed
      ftk = tftk @RepN (knownSTK @(XParams2 r)) targetInit
      ftkData = FTKProduct (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar)
                           (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar)
      f :: ( MnistFcnnRanked2.ADFcnnMnist2Parameters
               (AstTensor AstMethodLet FullSpan) r
           , ( AstTensor AstMethodLet FullSpan (TKR 1 r)
             , AstTensor AstMethodLet FullSpan (TKR 1 r) ) )
        -> AstTensor AstMethodLet FullSpan (TKScalar r)
      f (pars, (glyphR, labelR)) =
        afcnnMnistLoss2 (glyphR, labelR) pars
      (artRaw, _) = revArtifactAdapt False f (FTKProduct ftk ftkData)
  in (targetInit, artRaw)
