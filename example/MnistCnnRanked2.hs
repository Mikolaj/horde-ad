{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of Convolutional Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistCnnRanked2 where

import Prelude

import Data.Vector.Generic qualified as V
import Data.Vector.Storable (Vector)
import GHC.TypeLits (type (*), type (+), type Div)
import Numeric.LinearAlgebra (Numeric)

import Data.Array.Nested (pattern (:$:), pattern ZSR)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
--
-- Due to subtraction complicating posititive number type inference,
-- @kh@ denotes kernel height minus one and analogously @kw@ is kernel
-- width minus one.
type ADCnnMnistParametersShaped
       (target :: Target) h w kh kw c_out n_hidden r =
  ( ( target (TKS r '[c_out, 1, kh + 1, kw + 1])
    , target (TKS r '[c_out]) )
  , ( target (TKS r '[c_out, c_out, kh + 1, kw + 1])
    , target (TKS r '[c_out]) )
  , ( target (TKS r '[n_hidden, c_out * (h `Div` 4) * (w `Div` 4) ])
    , target (TKS r '[n_hidden]) )
  , ( target (TKS r '[SizeMnistLabel, n_hidden])
    , target (TKS r '[SizeMnistLabel]) )
  )

-- | The differentiable type of all trainable parameters of this nn.
type ADCnnMnistParameters (target :: Target) r =
  ( ( target (TKR r 4)
    , target (TKR r 1) )
  , ( target (TKR r 4)
    , target (TKR r 1) )
  , ( target (TKR r 2)
    , target (TKR r 1) )
  , ( target (TKR r 2)
    , target (TKR r 1) ) )

convMnistLayerR
  :: (ADReady target, GoodScalar r, Differentiable r)
  => target (TKR r 4)  -- [c_out, c_in, kh + 1, kw + 1]
  -> target (TKR r 4)  -- [batch_size, c_in, h, w]
  -> target (TKR r 1)  -- [c_out]
  -> target (TKR r 4)  -- [batch_size, c_out, h `Div` 2, w `Div` 2]
convMnistLayerR ker input bias =
  let (batch_size :$: _ :$: h :$: w :$: ZSR) = rshape input
      yConv = conv2dUnpadded ker input
      biasStretched = rtranspose [0, 3, 1, 2]
                      $ rreplicate batch_size $ rreplicate h $ rreplicate w bias
      yRelu = relu $ yConv + biasStretched
  in maxPool2dUnpadded 2 2 yRelu

convMnistTwoR
  :: (ADReady target, GoodScalar r, Numeric r, Differentiable r)
  => Int -> Int -> Int
  -> PrimalOf target (TKR r 4)  -- [batch_size, 1, SizeMnistHeight, SizeMnistWidth]
                          -- ^ input images
  -> ADCnnMnistParameters target r
  -> target (TKR r 2)  -- [SizeMnistLabel, batch_size]
                 -- ^ classification
convMnistTwoR sizeMnistHeightI sizeMnistWidthI batch_size input
              ( (ker1, bias1), (ker2, bias2)
              , (weightsDense, biasesDense), (weightsReadout, biasesReadout) ) =
  let t1 = convMnistLayerR ker1 (rfromPrimal input) bias1
      t2 = convMnistLayerR ker2 t1 bias2
             -- [ batch_size, c_out
             -- , SizeMnistHeight `Div` 4, SizeMnistWidth `Div` 2 ]
      c_out = rlength bias1
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

convMnistLossFusedR
  :: (ADReady target, ADReady (PrimalOf target), GoodScalar r, Numeric r, Differentiable r)
  => Int
  -> ( PrimalOf target (TKR r 3)  -- [batch_size, SizeMnistHeight, SizeMnistWidth]
     , PrimalOf target (TKR r 2) )  -- [batch_size, SizeMnistLabel]
  -> ADCnnMnistParameters target r  -- kh kw c_out n_hidden
  -> target (TKR r 0)
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
  in rfromPrimal (recip $ rscalar $ fromIntegral batch_size) * loss

convMnistTestR
  :: forall target r.
     (target ~ RepN, GoodScalar r, Numeric r, Differentiable r)
  => ADCnnMnistParameters target r
  -> Int
  -> MnistDataBatchR r
  -> HVector RepN
  -> r
convMnistTestR _ 0 _ _ = 0
convMnistTestR valsInit batch_size (glyphR, labelR) testParams =
  let input :: target (TKR r 4)
      input =
        rconcrete $ Nested.rreshape [batch_size, 1, sizeMnistHeightInt, sizeMnistWidthInt]
                                glyphR
      outputR :: RepN (TKR r 2)
      outputR =
        let nn :: ADCnnMnistParameters target r
               -> target (TKR r 2)  -- [SizeMnistLabel, batch_size]
            nn = convMnistTwoR sizeMnistHeightInt sizeMnistWidthInt
                               batch_size input
        in nn $ unAsHVector $ parseHVector (AsHVector valsInit) (dmkHVector testParams)
      outputs = map (Nested.rtoVector . unRepN) $ runravelToList
                $ rtranspose [1, 0] outputR
      labels = map (Nested.rtoVector . unRepN) $ runravelToList
               $ RepN labelR
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral batch_size
