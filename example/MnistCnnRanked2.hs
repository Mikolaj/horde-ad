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

import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.Internal.BackendOX (RepN (..))
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))
import HordeAd.Util.SizedList
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
--
-- Due to subtraction complicating posititive number type inference,
-- @kh@ denotes kernel height minus one and analogously @kw@ is kernel
-- width minus one.
type ADCnnMnistParametersShaped
       (target :: Target) h w kh kw c_out n_hidden r =
  ( ( target (TKS r '[c_out, 1, kh + 1, kw + 1]) )
  , ( target (TKS r '[c_out, c_out, kh + 1, kw + 1]) )
  , ( target (TKS r '[n_hidden, c_out * (h `Div` 4) * (w `Div` 4) ])
    )
  , ( target (TKS r '[SizeMnistLabel, n_hidden])
    )
  )

-- | The differentiable type of all trainable parameters of this nn.
type ADCnnMnistParameters (target :: Target) r =
  ( ( target (TKR r 4) )
  , ( target (TKR r 4) )
  , ( target (TKR r 2) )
  , ( target (TKR r 2) ) )

convMnistLayerR
  :: (ADReady target, GoodScalar r, Differentiable r)
  => target (TKR r 4)  -- [c_out, c_in, kh + 1, kw + 1]
  -> target (TKR r 4)  -- [batch_size, c_in, h, w]
  -> target (TKR r 4)  -- [batch_size, c_out, h `Div` 2, w `Div` 2]
convMnistLayerR ker input =
  let yConv = conv2dUnpadded ker input
  in maxPool2dUnpadded 2 2 yConv

convMnistTwoR
  :: (ADReady target, GoodScalar r, Numeric r, Differentiable r)
  => PrimalOf target (TKR r 4)  -- [batch_size, 1, SizeMnistHeight, SizeMnistWidth]
                          -- ^ input images
  -> ADCnnMnistParameters target r
  -> target (TKR r 2)  -- [SizeMnistLabel, batch_size]
                 -- ^ classification
convMnistTwoR input
              ( (ker1), (ker2)
              , (weightsDense), (weightsReadout) ) =
  let t1 = convMnistLayerR ker1 (rfromPrimal input)
      t2 = convMnistLayerR ker2 t1
             -- [ batch_size, c_out
             -- , SizeMnistHeight `Div` 4, SizeMnistWidth `Div` 2 ]
      m1 = rreshape (1 :$: 1 :$: ZSR) t2
      m2 = rtr m1
      denseLayer = weightsDense `rmatmul2` m2
  in weightsReadout `rmatmul2` denseLayer
