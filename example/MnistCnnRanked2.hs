{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistCnnRanked2 where

import Prelude

import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (type (*), type (+), type Div)
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.CommonRankedOps
import MnistData

type ADCnnMnistParametersShaped kh kw c_out n_hidden r =
  ( ( Shaped r '[c_out, 1, kh + 1, kw + 1]
    , Shaped r '[c_out] )
  , ( Shaped r '[c_out, c_out, kh + 1, kw + 1]
    , Shaped r '[c_out] )
  , ( Shaped r '[n_hidden, c_out * SizeMnistHeight `Div` 4
                                 * SizeMnistWidth `Div` 4 ]
    , Shaped r '[n_hidden] )
  , ( Shaped r '[SizeMnistLabel, n_hidden]
    , Shaped r '[SizeMnistLabel] )
  )

-- The differentiable type of all trainable parameters of this nn.
type ADCnnMnistParameters r =
  ( ( Ranked r 4
    , Ranked r 1 )
  , ( Ranked r 4
    , Ranked r 1 )
  , ( Ranked r 2
    , Ranked r 1 )
  , ( Ranked r 2
    , Ranked r 1 ) )

convMnistLayerR
  :: ADReady r
  => Ranked r 4  -- [c_out, c_in, kh + 1, kw + 1]
  -> Ranked r 4  -- [batch_size, c_in, h, w]
  -> Ranked r 1  -- [c_out]
  -> Ranked r 4  -- [batch_size, c_out, h `Div` 2, w `Div` 2]
convMnistLayerR ker input bias =
  let (batch_size :$ _ :$ h :$ w :$ ZS) = tshape input
      yConv = conv2dUnpadded ker input
      biasStretched = ttranspose [0, 3, 1, 2]
                      $ treplicate batch_size $ treplicate h $ treplicate w bias
      yRelu = relu $ yConv + biasStretched
  in maxPool2dUnpadded 2 2 yRelu

convMnistTwoR
  :: ADReady r
  => Int
  -> Ranked (Primal r) 4  -- [batch_size, 1, SizeMnistHeight, SizeMnistWidth]
                          -- ^ input images
  -> ADCnnMnistParameters r
  -> Ranked r 2  -- [SizeMnistLabel, batch_size]
                 -- ^ classification
convMnistTwoR batch_size input
              ( (ker1, bias1), (ker2, bias2)
              , (weightsDense, biasesDense), (weightsReadout, biasesReadout) ) =
  let t1 = convMnistLayerR ker1 (constant input) bias1
      t2 = convMnistLayerR ker2 t1 bias2
             -- [ batch_size, c_out
             -- , SizeMnistHeight `Div` 4, SizeMnistWidth `Div` 2 ]
      c_out = tlength bias1
      m1 = treshape (batch_size
                     :$ c_out * sizeMnistHeightInt `div` 4
                              * sizeMnistWidthInt `div` 4
                     :$ ZS)
                    t2
      m2 = ttranspose [1, 0] m1
      denseLayer = weightsDense `tmatmul2` m2
                   + ttranspose [1, 0] (treplicate batch_size biasesDense)
      denseRelu = relu denseLayer
  in weightsReadout `tmatmul2` denseRelu
     + ttranspose [1, 0] (treplicate batch_size biasesReadout)

convMnistLossFusedR
  :: ADReady r
  => Int
  -> ( Ranked (Primal r) 3  -- [batch_size, SizeMnistHeight, SizeMnistWidth]
     , Ranked (Primal r) 2 )  -- [batch_size, SizeMnistLabel]
  -> ADCnnMnistParameters r  -- kh kw c_out n_hidden
  -> r
convMnistLossFusedR batch_size (glyphR, labelR) adparameters =
  let input = treshape (batch_size
                        :$ 1
                        :$ sizeMnistHeightInt
                        :$ sizeMnistWidthInt
                        :$ ZS)
                       glyphR
      result = convMnistTwoR batch_size input adparameters
      targets = ttranspose [1, 0] labelR
      loss = lossSoftMaxCrossEntropyR targets result
  in tscale0 (recip $ fromIntegral batch_size) loss

convMnistTestR
  :: forall r. (ADReady r, r ~ Primal r, Numeric r, Ranked r ~ Flip OR.Array r)
  => Int
  -> MnistDataBatchR r
  -> ((ADCnnMnistParameters r
       -> Ranked r 2)  -- [SizeMnistLabel, batch_size]
      -> OR.Array 2 r)  -- [SizeMnistLabel, batch_size]
  -> r
convMnistTestR batch_size (glyphR, labelR) evalAtTestParams =
  let input =
        Flip $ OR.reshape [batch_size, 1, sizeMnistHeightInt, sizeMnistWidthInt]
                          glyphR
      outputR =
        let nn :: ADCnnMnistParameters r
               -> Ranked r 2  -- [SizeMnistLabel, batch_size]
            nn = convMnistTwoR batch_size input
        in evalAtTestParams nn
      outputs = map OR.toVector $ ORB.toList $ OR.unravel
                $ OR.transpose [1, 0] $ outputR
      labels = map OR.toVector $ ORB.toList $ OR.unravel labelR
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral batch_size