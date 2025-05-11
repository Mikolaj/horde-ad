{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of Convolutional Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
--
-- With the current CPU backend it's slow enough that it's hard to see
-- if it trains.
module MnistCnnRanked2 where

import Prelude

import Data.Vector.Generic qualified as V
import Data.Vector.Storable (Vector)
import GHC.TypeLits (type (*), type (+), type Div)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
--
-- Due to subtraction complicating posititive number type inference,
-- @kh@ denotes kernel height minus one and analogously @kw@ is kernel
-- width minus one.
type ADCnnMnistParametersShaped
       (target :: Target) h w kh kw c_out n_hidden r =
  ( ( target (TKS '[c_out, 1, kh + 1, kw + 1] r)
    , target (TKS '[c_out] r) )
  , ( target (TKS '[c_out, c_out, kh + 1, kw + 1] r)
    , target (TKS '[c_out] r) )
  , ( target (TKS '[n_hidden, c_out * (h `Div` 4) * (w `Div` 4)] r)
    , target (TKS '[n_hidden] r) )
  , ( target (TKS '[SizeMnistLabel, n_hidden] r)
    , target (TKS '[SizeMnistLabel] r) )
  )

-- | The differentiable type of all trainable parameters of this nn.
-- Ranked version.
type ADCnnMnistParameters (target :: Target) r =
  ( ( target (TKR 4 r)
    , target (TKR 1 r) )
  , ( target (TKR 4 r)
    , target (TKR 1 r) )
  , ( target (TKR 2 r)
    , target (TKR 1 r) )
  , ( target (TKR 2 r)
    , target (TKR 1 r) ) )

-- | A single convolutional layer with @relu@ and @maxPool@.
convMnistLayerR
  :: (ADReady target, GoodScalar r, Differentiable r)
  => target (TKR 4 r)  -- ^ @[c_out, c_in, kh + 1, kw + 1]@
  -> target (TKR 4 r)  -- ^ @[batch_size, c_in, h, w]@
  -> target (TKR 1 r)  -- ^ @[c_out]@
  -> target (TKR 4 r)  -- ^ @[batch_size, c_out, h \`Div\` 2, w \`Div\` 2]@
convMnistLayerR ker input bias =
  let (batch_size :$: _ :$: h :$: w :$: ZSR) = rshape input
      yConv = conv2dUnpadded ker input
      biasStretched = rtranspose [0, 3, 1, 2]
                      $ rreplicate batch_size $ rreplicate h $ rreplicate w bias
      yRelu = relu $ yConv + biasStretched
  in maxPool2dUnpadded 2 2 yRelu

-- | Composition of two convolutional layers.
convMnistTwoR
  :: (ADReady target, GoodScalar r, Differentiable r)
  => Int -> Int -> Int
  -> PrimalOf target (TKR 4 r)
       -- ^ input images @[batch_size, 1, SizeMnistHeight, SizeMnistWidth]@
  -> ADCnnMnistParameters target r  -- ^ parameters
  -> target (TKR 2 r)  -- ^ output classification @[SizeMnistLabel, batch_size]@
convMnistTwoR sizeMnistHeightI sizeMnistWidthI batch_size input
              ( (ker1, bias1), (ker2, bias2)
              , (weightsDense, biasesDense), (weightsReadout, biasesReadout) ) =
  let t1 = convMnistLayerR ker1 (rfromPrimal input) bias1
      t2 = convMnistLayerR ker2 t1 bias2
             -- [ batch_size, c_out
             -- , SizeMnistHeight `Div` 4, SizeMnistWidth `Div` 2 ]
      c_out = rwidth bias1
      m1 = rreshape (batch_size
                     :$: c_out * (sizeMnistHeightI `div` 4)
                               * (sizeMnistWidthI `div` 4)
                     :$: ZSR)
                    t2
      m2 = rtr m1
      denseLayer = weightsDense `rmatmul2` m2
                   + rtr (rreplicate batch_size biasesDense)
      denseRelu = relu denseLayer
  in weightsReadout `rmatmul2` denseRelu
     + rtr (rreplicate batch_size biasesReadout)

-- | The neural network composed with the SoftMax-CrossEntropy loss function.
convMnistLossFusedR
  :: (ADReady target, ADReady (PrimalOf target), GoodScalar r, Differentiable r)
  => Int  -- ^ batch_size
  -> ( PrimalOf target (TKR 3 r)
         -- ^ @[batch_size, SizeMnistHeight, SizeMnistWidth]@
     , PrimalOf target (TKR 2 r) )  -- ^ @[batch_size, SizeMnistLabel]@
  -> ADCnnMnistParameters target r  -- kh kw c_out n_hidden
  -> target (TKScalar r)
convMnistLossFusedR batch_size (glyphR, labelR) adparameters =
  let input = rreshape (batch_size
                        :$: 1
                        :$: sizeMnistHeightInt
                        :$: sizeMnistWidthInt
                        :$: ZSR)
                       glyphR
      result = convMnistTwoR sizeMnistHeightInt sizeMnistWidthInt
                             batch_size input adparameters
      targets = rtr labelR
      loss = lossSoftMaxCrossEntropyR targets result
  in kfromPrimal (recip $ kconcrete $ fromIntegral batch_size) * loss

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
convMnistTestR
  :: forall target r.
     (target ~ Concrete, GoodScalar r, Differentiable r)
  => Int
  -> MnistDataBatchR r
  -> ADCnnMnistParameters Concrete r
  -> r
convMnistTestR 0 _ _ = 0
convMnistTestR batch_size (glyphR, labelR) testParams =
  let input :: target (TKR 4 r)
      input =
        rconcrete $ Nested.rreshape [ batch_size, 1
                                    , sizeMnistHeightInt, sizeMnistWidthInt ]
                                    glyphR
      outputR :: Concrete (TKR 2 r)
      outputR =
        let nn :: ADCnnMnistParameters target r
               -> target (TKR 2 r)  -- [SizeMnistLabel, batch_size]
            nn = convMnistTwoR sizeMnistHeightInt sizeMnistWidthInt
                               batch_size input
        in nn testParams
      outputs = map rtoVector $ runravelToList
                $ rtranspose [1, 0] outputR
      labels = map rtoVector
               $ runravelToList @_ @(TKScalar r)
               $ rconcrete labelR
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral batch_size
