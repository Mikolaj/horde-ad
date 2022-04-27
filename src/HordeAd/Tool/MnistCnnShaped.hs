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

import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (DualNumberVariables, varS)
import HordeAd.Tool.MnistData

convMnistLayerS
  :: forall kheight_minus_1 kwidth_minus_1 out_channels
            in_height in_width in_channels batch_size r m.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width
     , KnownNat in_channels, KnownNat batch_size
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1  -- wrongly reported as redundant
     , DualMonad r m )
  => DualNumber (TensorS r '[ out_channels, in_channels
                            , kheight_minus_1 + 1, kwidth_minus_1 + 1 ])
  -> DualNumber (TensorS r '[batch_size, in_channels, in_height, in_width])
  -> DualNumber (TensorS r '[out_channels])
  -> m (DualNumber (TensorS r '[ batch_size, out_channels
                               , (in_height + kheight_minus_1) `Div` 2
                               , (in_width + kwidth_minus_1) `Div` 2 ]))
convMnistLayerS ker x bias = do
  let yConv = conv24 ker x
      replicateBias
        :: DualNumber (TensorS r '[])
           -> DualNumber (TensorS r '[ in_height + kheight_minus_1
                                     , in_width + kwidth_minus_1 ])
      replicateBias = konstS . fromS0
      biasStretched = ravelFromListS
                      $ replicate (valueOf @batch_size)
                      $ mapS replicateBias bias
        -- TODO: this is weakly typed; add and use replicateS instead
        -- or broadcastS or stretchS, possibly with transposeS?
  yRelu <- reluAct $ yConv + biasStretched
  maxPool24 @1 @2 yRelu

convMnistTwoS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width in_channels batch_size r m.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width, KnownNat batch_size
     , in_channels ~ 1
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , DualMonad r m )
  => Primal (TensorS r '[batch_size, in_channels, in_height, in_width])
  -> DualNumber (TensorS r '[ out_channels, in_channels
                            , kheight_minus_1 + 1, kwidth_minus_1 + 1 ])
  -> DualNumber (TensorS r '[out_channels])
  -> DualNumber (TensorS r '[ out_channels, out_channels
                            , kheight_minus_1 + 1, kwidth_minus_1 + 1 ])
  -> DualNumber (TensorS r '[out_channels])
  -> DualNumber (TensorS r '[ num_hidden
                            , out_channels
                                GHC.TypeLits.*
                                  ((in_height + kheight_minus_1) `Div` 2
                                   + kheight_minus_1) `Div` 2
                                GHC.TypeLits.*
                                  ((in_width + kwidth_minus_1) `Div` 2
                                   + kheight_minus_1) `Div` 2
                            ])
  -> DualNumber (TensorS r '[num_hidden])
  -> DualNumber (TensorS r '[SizeMnistLabel, num_hidden])
  -> DualNumber (TensorS r '[SizeMnistLabel])
  -> m (DualNumber (TensorS r '[SizeMnistLabel, batch_size]))
convMnistTwoS x ker1 bias1 ker2 bias2
              weigthsDense biasesDense weigthsReadout biasesReadout = do
  t1 <- convMnistLayerS ker1 (scalar x) bias1
  t2 <- convMnistLayerS ker2 t1 bias2
  let m1 = mapS reshapeS t2
      m2 = from2S (transpose2 (fromS2 m1))  -- TODO: add permuation transposeS
      denseLayer = weigthsDense <>$ m2 + asColumnS biasesDense
  denseRelu <- reluAct denseLayer
  returnLet $ weigthsReadout <>$ denseRelu + asColumnS biasesReadout

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
            in_height in_width batch_size r m.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width, KnownNat batch_size
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , DualMonad r m )
  => Primal (TensorS r '[batch_size, 1, in_height, in_width])
  -> DualNumberVariables r
  -> m (DualNumber (TensorS r '[SizeMnistLabel, batch_size]))
convMnistS x variables = do
  let ker1 = varS variables 0
      bias1 = varS variables 1
      ker2 = varS variables 2
      bias2 = varS variables 3
      weigthsDense = varS variables 4
      biasesDense = varS variables 5
      weigthsReadout = varS variables 6
      biasesReadout = varS variables 7
  convMnistTwoS @kheight_minus_1 @kwidth_minus_1 @num_hidden @out_channels
                x ker1 bias1 ker2 bias2
                weigthsDense biasesDense weigthsReadout biasesReadout

convMnistLossFusedS
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width batch_size r m.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width, KnownNat batch_size
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , DualMonad r m )
  => Proxy kheight_minus_1
  -> Proxy kwidth_minus_1
  -> Proxy num_hidden
  -> Proxy out_channels
  -> Proxy in_height
  -> Proxy in_width
  -> Proxy batch_size
  -> ( OS.Array '[batch_size, in_height, in_width] (Primal r)
     , OS.Array '[batch_size, SizeMnistLabel] (Primal r) )
  -> DualNumberVariables r
  -> m (DualNumber r)
convMnistLossFusedS _ _ _ _ _ _ _ (glyphS, labelS) variables = do
  let xs :: Primal (TensorS r '[batch_size, 1, in_height, in_width])
      xs = OS.reshape glyphS
  result <- convMnistS @kheight_minus_1 @kwidth_minus_1
                       @num_hidden @out_channels
                       xs variables
  let targets2 = HM.tr $ HM.reshape (valueOf @SizeMnistLabel)
                       $ OS.toVector labelS
  vec@(D u _) <-
    lossSoftMaxCrossEntropyL targets2 (fromS2 result)
  returnLet $ scale (recip $ fromIntegral $ V.length u) $ sumElements0 vec

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
     , IsScalar r )
  => Proxy r
  -> Proxy kheight_minus_1
  -> Proxy kwidth_minus_1
  -> Proxy num_hidden
  -> Proxy out_channels
  -> Proxy in_height
  -> Proxy in_width
  -> [( OS.Array '[in_height, in_width] (Primal r)
      , OS.Array '[SizeMnistLabel] (Primal r) )]
  -> Domains r
  -> Primal r
convMnistTestS _ _ _ _ _ _ _ inputs parameters =
  let matchesLabels :: ( OS.Array '[in_height, in_width] (Primal r)
                       , OS.Array '[SizeMnistLabel] (Primal r) )
                    -> Bool
      matchesLabels (glyph, label) =
        let tx :: Primal (TensorS r '[1, 1, in_height, in_width])
            tx = OS.reshape glyph
            nn :: DualNumberVariables r
               -> DualMonadValue r (DualNumber (TensorS r '[SizeMnistLabel, 1]))
            nn variables =
              convMnistS @kheight_minus_1 @kwidth_minus_1
                         @num_hidden @out_channels
                         tx variables
            value = primalValue @r nn parameters
        in V.maxIndex (OS.toVector value) == V.maxIndex (OS.toVector label)
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
