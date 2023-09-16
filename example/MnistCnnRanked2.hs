{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of Convolutional Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistCnnRanked2 where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (type (*), type (+), type Div)
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.Adaptor
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.Internal.TensorOps
import HordeAd.Util.SizedIndex
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
--
-- Due to subtraction complicating posititive number type inference,
-- @kh@ denotes kernel height minus one and analogously @kw@ is kernel
-- width minus one.
type ADCnnMnistParametersShaped
       (shaped :: ShapedTensorKind) h w kh kw c_out n_hidden r =
  ( ( shaped r '[c_out, 1, kh + 1, kw + 1]
    , shaped r '[c_out] )
  , ( shaped r '[c_out, c_out, kh + 1, kw + 1]
    , shaped r '[c_out] )
  , ( shaped r '[n_hidden, c_out * (h `Div` 4) * (w `Div` 4) ]
    , shaped r '[n_hidden] )
  , ( shaped r '[SizeMnistLabel, n_hidden]
    , shaped r '[SizeMnistLabel] )
  )

-- | The differentiable type of all trainable parameters of this nn.
type ADCnnMnistParameters (ranked :: RankedTensorKind) r =
  ( ( ranked r 4
    , ranked r 1 )
  , ( ranked r 4
    , ranked r 1 )
  , ( ranked r 2
    , ranked r 1 )
  , ( ranked r 2
    , ranked r 1 ) )

convMnistLayerR
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => ranked r 4  -- [c_out, c_in, kh + 1, kw + 1]
  -> ranked r 4  -- [batch_size, c_in, h, w]
  -> ranked r 1  -- [c_out]
  -> ranked r 4  -- [batch_size, c_out, h `Div` 2, w `Div` 2]
convMnistLayerR ker input bias =
  let (batch_size :$ _ :$ h :$ w :$ ZS) = tshape input
      yConv = conv2dUnpadded ker input
      biasStretched = ttranspose [0, 3, 1, 2]
                      $ treplicate batch_size $ treplicate h $ treplicate w bias
      yRelu = relu $ yConv + biasStretched
  in maxPool2dUnpadded 2 2 yRelu

convMnistTwoR
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => Int -> Int -> Int
  -> PrimalOf ranked r 4  -- [batch_size, 1, SizeMnistHeight, SizeMnistWidth]
                          -- ^ input images
  -> ADCnnMnistParameters ranked r
  -> ranked r 2  -- [SizeMnistLabel, batch_size]
                 -- ^ classification
convMnistTwoR sizeMnistHeightI sizeMnistWidthI batch_size input
              ( (ker1, bias1), (ker2, bias2)
              , (weightsDense, biasesDense), (weightsReadout, biasesReadout) ) =
  let t1 = convMnistLayerR ker1 (tconstant input) bias1
      t2 = convMnistLayerR ker2 t1 bias2
             -- [ batch_size, c_out
             -- , SizeMnistHeight `Div` 4, SizeMnistWidth `Div` 2 ]
      c_out = tlength bias1
      m1 = treshape (batch_size
                     :$ c_out * (sizeMnistHeightI `div` 4)
                              * (sizeMnistWidthI `div` 4)
                     :$ ZS)
                    t2
      m2 = ttr m1
      denseLayer = weightsDense `tmatmul2` m2
                   + ttr (treplicate batch_size biasesDense)
      denseRelu = relu denseLayer
  in weightsReadout `tmatmul2` denseRelu
     + ttr (treplicate batch_size biasesReadout)

convMnistLossFusedR
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => Int
  -> ( PrimalOf ranked r 3  -- [batch_size, SizeMnistHeight, SizeMnistWidth]
     , PrimalOf ranked r 2 )  -- [batch_size, SizeMnistLabel]
  -> ADCnnMnistParameters ranked r  -- kh kw c_out n_hidden
  -> ranked r 0
convMnistLossFusedR batch_size (glyphR, labelR) adparameters =
  let input = treshape (batch_size
                        :$ 1
                        :$ sizeMnistHeightInt
                        :$ sizeMnistWidthInt
                        :$ ZS)
                       glyphR
      result = convMnistTwoR sizeMnistHeightInt sizeMnistWidthInt
                             batch_size input adparameters
      targets = ttr labelR
      loss = lossSoftMaxCrossEntropyR targets result
  in tconstant (recip $ fromIntegral batch_size) * loss

convMnistTestR
  :: forall ranked r.
     (ranked ~ Flip OR.Array, GoodScalar r, Differentiable r)
  => ADCnnMnistParameters ranked r
  -> Int
  -> MnistDataBatchR r
  -> DomainsOD
  -> r
convMnistTestR _ 0 _ _ = 0
convMnistTestR valsInit batch_size (glyphR, labelR) testParams =
  let input =
        Flip $ OR.reshape [batch_size, 1, sizeMnistHeightInt, sizeMnistWidthInt]
                          glyphR
      outputR =
        let nn :: ADCnnMnistParameters ranked r
               -> ranked r 2  -- [SizeMnistLabel, batch_size]
            nn = convMnistTwoR sizeMnistHeightInt sizeMnistWidthInt
                               batch_size input
        in runFlip $ nn $ parseDomains valsInit testParams
      outputs = map OR.toVector $ tunravelToListR $ OR.transpose [1, 0] outputR
      labels = map OR.toVector $ tunravelToListR labelR
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral batch_size
