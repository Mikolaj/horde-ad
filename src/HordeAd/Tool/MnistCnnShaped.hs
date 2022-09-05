{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes, TypeFamilies,
             TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Shaped tensor-based implementation of Convolutional Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module HordeAd.Tool.MnistCnnShaped where

import Prelude

import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape
import qualified Data.Array.ShapedS as OS
import           Data.Proxy (Proxy)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+), type (<=), type Div)
import qualified Numeric.LinearAlgebra as HM

-- until stylish-haskell accepts NoStarIsType
import qualified GHC.TypeLits

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (DualNumberInputs, atS)
import HordeAd.Tool.MnistData

convMnistLayerS
  :: forall kheight_minus_1 kwidth_minus_1 out_channels
            in_height in_width in_channels batch_size d r.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width
     , KnownNat in_channels, KnownNat batch_size
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1  -- wrongly reported as redundant
     , IsScalar d r )
  => DualNumber d (OS.Array '[ out_channels, in_channels
                             , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
  -> DualNumber d (OS.Array '[batch_size, in_channels, in_height, in_width] r)
  -> DualNumber d (OS.Array '[out_channels] r)
  -> DualNumber d (OS.Array '[ batch_size, out_channels
                             , (in_height + kheight_minus_1) `Div` 2
                             , (in_width + kwidth_minus_1) `Div` 2 ] r)
convMnistLayerS ker x bias =
  let yConv = conv24 ker x
      replicateBias
        :: DualNumber d (OS.Array '[] r)
        -> DualNumber d (OS.Array '[ in_height + kheight_minus_1
                                   , in_width + kwidth_minus_1 ] r)
      replicateBias = konstS . fromS0
      biasStretched = ravelFromListS
                      $ replicate (valueOf @batch_size)
                      $ mapS replicateBias bias
        -- TODO: this is weakly typed; add and use replicateS instead
        -- or broadcastS or stretchS, possibly with transposeS?
      yRelu = relu $ yConv + biasStretched
  in maxPool24 @1 @2 yRelu

convMnistTwoS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width in_channels batch_size d r.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width, KnownNat batch_size
     , in_channels ~ 1
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , IsScalar d r )
  => OS.Array '[batch_size, in_channels, in_height, in_width] r
  -- All below is the type of all paramters of this nn. The same is reflected
  -- in the length function below and read from inputs further down.
  -> DualNumber d (OS.Array '[ out_channels, in_channels
                             , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
  -> DualNumber d (OS.Array '[out_channels] r)
  -> DualNumber d (OS.Array '[ out_channels, out_channels
                             , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
  -> DualNumber d (OS.Array '[out_channels] r)
  -> DualNumber d (OS.Array '[ num_hidden
                             , out_channels
                                 GHC.TypeLits.*
                                   (((in_height + kheight_minus_1) `Div` 2
                                     + kheight_minus_1) `Div` 2)
                                 GHC.TypeLits.*
                                   (((in_width + kwidth_minus_1) `Div` 2
                                     + kwidth_minus_1) `Div` 2)
                             ] r)
  -> DualNumber d (OS.Array '[num_hidden] r)
  -> DualNumber d (OS.Array '[SizeMnistLabel, num_hidden] r)
  -> DualNumber d (OS.Array '[SizeMnistLabel] r)
  -> DualNumber d (OS.Array '[SizeMnistLabel, batch_size] r)
convMnistTwoS x ker1 bias1 ker2 bias2
              weigthsDense biasesDense weigthsReadout biasesReadout =
  let t1 = convMnistLayerS ker1 (constant x) bias1
      t2 = convMnistLayerS ker2 t1 bias2
      m1 = mapS reshapeS t2
      m2 = transpose2S m1
      denseLayer = weigthsDense <>$ m2 + asColumnS biasesDense
      denseRelu = relu denseLayer
  in weigthsReadout <>$ denseRelu + asColumnS biasesReadout

convMnistLenS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width )
  => Proxy kheight_minus_1
  -> Proxy kwidth_minus_1
  -> Proxy num_hidden
  -> Proxy out_channels
  -> Proxy in_height
  -> Proxy in_width
  -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
convMnistLenS _ _ _ _ _ _ =
  ( 0
  , []
  , []
  , [ Data.Array.Shape.shapeT @'[ out_channels, 1
                                , kheight_minus_1 + 1, kwidth_minus_1 + 1 ]
    , Data.Array.Shape.shapeT @'[out_channels]
    , Data.Array.Shape.shapeT @'[ out_channels, out_channels
                                , kheight_minus_1 + 1, kwidth_minus_1 + 1 ]
    , Data.Array.Shape.shapeT @'[out_channels]
    , Data.Array.Shape.shapeT @'[ num_hidden
                                , out_channels
                                    GHC.TypeLits.*
                                      ((in_height + kheight_minus_1) `Div` 2
                                       + kheight_minus_1) `Div` 2
                                    GHC.TypeLits.*
                                      ((in_width + kwidth_minus_1) `Div` 2
                                       + kheight_minus_1) `Div` 2
                                ]
    , Data.Array.Shape.shapeT @'[num_hidden]
    , Data.Array.Shape.shapeT @'[SizeMnistLabel, num_hidden]
    , Data.Array.Shape.shapeT @'[SizeMnistLabel]
    ]
  )

convMnistS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width batch_size d r.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width, KnownNat batch_size
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , IsScalar d r )
  => OS.Array '[batch_size, 1, in_height, in_width] r
  -> DualNumberInputs d r
  -> DualNumber d (OS.Array '[SizeMnistLabel, batch_size] r)
convMnistS x inputs =
  let ker1 = atS inputs 0
      bias1 = atS inputs 1
      ker2 = atS inputs 2
      bias2 = atS inputs 3
      weigthsDense = atS inputs 4
      biasesDense = atS inputs 5
      weigthsReadout = atS inputs 6
      biasesReadout = atS inputs 7
  in convMnistTwoS @kheight_minus_1 @kwidth_minus_1 @num_hidden @out_channels
                   x ker1 bias1 ker2 bias2
                   weigthsDense biasesDense weigthsReadout biasesReadout

convMnistLossFusedS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width batch_size d r.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width, KnownNat batch_size
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , IsScalar d r )
  => Proxy kheight_minus_1
  -> Proxy kwidth_minus_1
  -> Proxy num_hidden
  -> Proxy out_channels
  -> ( OS.Array '[batch_size, in_height, in_width] r
     , OS.Array '[batch_size, SizeMnistLabel] r )
  -> DualNumberInputs d r
  -> DualNumber d r
convMnistLossFusedS _ _ _ _ (glyphS, labelS) inputs =
  let xs :: OS.Array '[batch_size, 1, in_height, in_width] r
      xs = OS.reshape glyphS
      result = convMnistS @kheight_minus_1 @kwidth_minus_1
                          @num_hidden @out_channels
                          xs inputs
      targets2 = HM.tr $ HM.reshape (valueOf @SizeMnistLabel)
                       $ OS.toVector labelS
      vec = lossSoftMaxCrossEntropyL targets2 (fromS2 result)
  in scale (recip $ fromIntegral (valueOf @batch_size :: Int))
     $ sumElements0 vec

-- For simplicity, testing is performed in mini-batches of 1.
-- See RNN for testing done in batches.
convMnistTestS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width r.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , IsScalar 'DModeValue r )
  => Proxy kheight_minus_1
  -> Proxy kwidth_minus_1
  -> Proxy num_hidden
  -> Proxy out_channels
  -> [( OS.Array '[in_height, in_width] r
      , OS.Array '[SizeMnistLabel] r )]
  -> Domains r
  -> r
convMnistTestS _ _ _ _ inputs parameters =
  let matchesLabels :: ( OS.Array '[in_height, in_width] r
                       , OS.Array '[SizeMnistLabel] r )
                    -> Bool
      matchesLabels (glyph, label) =
        let tx :: OS.Array '[1, 1, in_height, in_width] r
            tx = OS.reshape glyph
            nn :: DualNumberInputs 'DModeValue r
               -> DualNumber 'DModeValue (OS.Array '[SizeMnistLabel, 1] r)
            nn = convMnistS @kheight_minus_1 @kwidth_minus_1
                            @num_hidden @out_channels
                            tx
            value = primalValue nn parameters
        in V.maxIndex (OS.toVector value) == V.maxIndex (OS.toVector label)
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
