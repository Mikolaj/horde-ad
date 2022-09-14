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
import qualified Data.Array.Shape
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (type (+), type (<=), type Div)
import qualified Numeric.LinearAlgebra as HM

-- until stylish-haskell accepts NoStarIsType
import qualified GHC.TypeLits

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (ADValInputs, atS)
import HordeAd.Tool.MnistData

convMnistLayerS
  :: forall kheight_minus_1 kwidth_minus_1 out_channels
            in_height in_width in_channels batch_size d r.
     ( 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1  -- wrongly reported as redundant
     , ADModeAndNum d r )
  => StaticNat kheight_minus_1 -> StaticNat kwidth_minus_1
  -> StaticNat out_channels
  -> StaticNat in_height -> StaticNat in_width
  -> StaticNat in_channels
  -> StaticNat batch_size
  -> ADVal d (OS.Array '[ out_channels, in_channels
                             , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
  -> ADVal d (OS.Array '[batch_size, in_channels, in_height, in_width] r)
  -> ADVal d (OS.Array '[out_channels] r)
  -> ADVal d (OS.Array '[ batch_size, out_channels
                             , (in_height + kheight_minus_1) `Div` 2
                             , (in_width + kwidth_minus_1) `Div` 2 ] r)
convMnistLayerS MkSN MkSN MkSN MkSN MkSN MkSN
                batch_size@MkSN
                ker x bias =
  let yConv = conv24 ker x
      replicateBias
        :: ADVal d (OS.Array '[] r)
        -> ADVal d (OS.Array '[ in_height + kheight_minus_1
                                   , in_width + kwidth_minus_1 ] r)
      replicateBias = konstS . fromS0
      biasStretched = ravelFromListS
                      $ replicate (staticNatValue batch_size)
                      $ mapS replicateBias bias
        -- TODO: this is weakly typed; add and use replicateS instead
        -- or broadcastS or stretchS, possibly with transposeS?
      yRelu = relu $ yConv + biasStretched
  in maxPool24 @1 @2 yRelu

convMnistTwoS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width in_channels batch_size d r.
     ( in_channels ~ 1
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , ADModeAndNum d r )
  => StaticNat kheight_minus_1 -> StaticNat kwidth_minus_1
  -> StaticNat num_hidden
  -> StaticNat out_channels
  -> StaticNat in_height -> StaticNat in_width
  -> StaticNat batch_size
  -> OS.Array '[batch_size, in_channels, in_height, in_width] r
  -- All below is the type of all paramters of this nn. The same is reflected
  -- in the length function below and read from inputs further down.
  -> ADVal d (OS.Array '[ out_channels, in_channels
                             , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
  -> ADVal d (OS.Array '[out_channels] r)
  -> ADVal d (OS.Array '[ out_channels, out_channels
                             , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
  -> ADVal d (OS.Array '[out_channels] r)
  -> ADVal d (OS.Array '[ num_hidden
                             , out_channels
                                 GHC.TypeLits.*
                                   (((in_height + kheight_minus_1) `Div` 2
                                     + kheight_minus_1) `Div` 2)
                                 GHC.TypeLits.*
                                   (((in_width + kwidth_minus_1) `Div` 2
                                     + kwidth_minus_1) `Div` 2)
                             ] r)
  -> ADVal d (OS.Array '[num_hidden] r)
  -> ADVal d (OS.Array '[SizeMnistLabel, num_hidden] r)
  -> ADVal d (OS.Array '[SizeMnistLabel] r)
  -> ADVal d (OS.Array '[SizeMnistLabel, batch_size] r)
convMnistTwoS kheight_minus_1@MkSN kwidth_minus_1@MkSN
              _num_hidden@MkSN
              out_channels@MkSN
              in_height@MkSN in_width@MkSN
              batch_size@MkSN
              x ker1 bias1 ker2 bias2
              weigthsDense biasesDense weigthsReadout biasesReadout =
  let t1 = convMnistLayerS kheight_minus_1 kwidth_minus_1
                           out_channels
                           in_height in_width
                           (MkSN @in_channels) batch_size
                           ker1 (constant x) bias1
      t2 = convMnistLayerS kheight_minus_1 kwidth_minus_1
                           out_channels
                           (MkSN @((in_height + kheight_minus_1) `Div` 2))
                           (MkSN @((in_width + kwidth_minus_1) `Div` 2))
                           out_channels batch_size
                           ker2 t1 bias2
      m1 = mapS reshapeS t2
      m2 = transpose2S m1
      denseLayer = weigthsDense <>$ m2 + asColumnS biasesDense
      denseRelu = relu denseLayer
  in weigthsReadout <>$ denseRelu + asColumnS biasesReadout

convMnistLenS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width.
     StaticNat kheight_minus_1 -> StaticNat kwidth_minus_1
  -> StaticNat num_hidden
  -> StaticNat out_channels
  -> StaticNat in_height -> StaticNat in_width
  -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
convMnistLenS MkSN MkSN MkSN MkSN MkSN MkSN =
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
     ( 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , ADModeAndNum d r )
  => StaticNat kheight_minus_1 -> StaticNat kwidth_minus_1
  -> StaticNat num_hidden
  -> StaticNat out_channels
  -> StaticNat in_height -> StaticNat in_width
  -> StaticNat batch_size
  -> OS.Array '[batch_size, 1, in_height, in_width] r
  -> ADValInputs d r
  -> ADVal d (OS.Array '[SizeMnistLabel, batch_size] r)
convMnistS kheight_minus_1@MkSN kwidth_minus_1@MkSN
           num_hidden@MkSN
           out_channels@MkSN
           in_height@MkSN in_width@MkSN
           batch_size@MkSN
           x inputs =
  let ker1 = atS inputs 0
      bias1 = atS inputs 1
      ker2 = atS inputs 2
      bias2 = atS inputs 3
      weigthsDense = atS inputs 4
      biasesDense = atS inputs 5
      weigthsReadout = atS inputs 6
      biasesReadout = atS inputs 7
  in convMnistTwoS kheight_minus_1 kwidth_minus_1 num_hidden out_channels
                   in_height in_width batch_size
                   x ker1 bias1 ker2 bias2
                   weigthsDense biasesDense weigthsReadout biasesReadout

convMnistLossFusedS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width batch_size d r.
     ( 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , ADModeAndNum d r )
  => StaticNat kheight_minus_1 -> StaticNat kwidth_minus_1
  -> StaticNat num_hidden
  -> StaticNat out_channels
  -> StaticNat in_height -> StaticNat in_width
  -> StaticNat batch_size
  -> ( OS.Array '[batch_size, in_height, in_width] r
     , OS.Array '[batch_size, SizeMnistLabel] r )
  -> ADValInputs d r
  -> ADVal d r
convMnistLossFusedS
    kheight_minus_1@MkSN kwidth_minus_1@MkSN
    num_hidden@MkSN
    out_channels@MkSN
    in_height@MkSN in_width@MkSN
    batch_size@MkSN
    (glyphS, labelS) inputs =
  let xs :: OS.Array '[batch_size, 1, in_height, in_width] r
      xs = OS.reshape glyphS
      result = convMnistS kheight_minus_1 kwidth_minus_1 num_hidden out_channels
                          in_height in_width batch_size
                          xs inputs
      targets2 = HM.tr $ HM.reshape (staticNatValue sizeMnistLabel :: Int)
                       $ OS.toVector labelS
      vec = lossSoftMaxCrossEntropyL targets2 (fromS2 result)
  in scale (recip $ fromIntegral (staticNatValue batch_size :: Int))
     $ sumElements0 vec

-- For simplicity, testing is performed in mini-batches of 1.
-- See RNN for testing done in batches.
convMnistTestS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width r.
     ( 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , ADModeAndNum 'DModeValue r )
  => StaticNat kheight_minus_1 -> StaticNat kwidth_minus_1
  -> StaticNat num_hidden
  -> StaticNat out_channels
  -> StaticNat in_height -> StaticNat in_width
  -> [( OS.Array '[in_height, in_width] r
      , OS.Array '[SizeMnistLabel] r )]
  -> Domains r
  -> r
convMnistTestS kheight_minus_1@MkSN kwidth_minus_1@MkSN
               num_hidden@MkSN
               out_channels@MkSN
               in_height@MkSN in_width@MkSN
               inputs parameters =
  let matchesLabels :: ( OS.Array '[in_height, in_width] r
                       , OS.Array '[SizeMnistLabel] r )
                    -> Bool
      matchesLabels (glyph, label) =
        let tx :: OS.Array '[1, 1, in_height, in_width] r
            tx = OS.reshape glyph
            batch_size_1 = MkSN @1
            nn :: ADValInputs 'DModeValue r
               -> ADVal 'DModeValue (OS.Array '[SizeMnistLabel, 1] r)
            nn = convMnistS kheight_minus_1 kwidth_minus_1
                            num_hidden out_channels
                            in_height in_width batch_size_1
                            tx
            value = primalValue nn parameters
        in V.maxIndex (OS.toVector value) == V.maxIndex (OS.toVector label)
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
