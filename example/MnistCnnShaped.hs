{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Shaped tensor-based implementation of Convolutional Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistCnnShaped where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Shape
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (ADInputs, atS)
import MnistData

-- Due to subtraction complicating posititive number type inference,
-- @kh@ denotes kernel height minus one and analogously @kw@ is kernel
-- width minus one.
convMnistLayerS
  :: forall kh kw h w c_in c_out batch_size d r.
     ( 1 <= kh
     , 1 <= kw  -- wrongly reported as redundant
     , ADModeAndNum d r )
  => StaticNat kh -> StaticNat kw
  -> StaticNat h -> StaticNat w
  -> StaticNat c_in -> StaticNat c_out
  -> StaticNat batch_size
  -> ADVal d (OS.Array '[c_out, c_in, kh + 1, kw + 1] r)
  -> ADVal d (OS.Array '[batch_size, c_in, h, w] r)
  -> ADVal d (OS.Array '[c_out] r)
  -> ADVal d (OS.Array '[ batch_size, c_out
                        , (h + kh) `Div` 2
                        , (w + kw) `Div` 2 ] r)
convMnistLayerS MkSN MkSN MkSN MkSN MkSN MkSN batch_size@MkSN
                ker x bias =
  let yConv = conv24 ker x
      replicateBias
        :: ADVal d (OS.Array '[] r)
        -> ADVal d (OS.Array '[h + kh, w + kw] r)
      replicateBias = konstS . fromS0
      biasStretched = ravelFromListS
                      $ replicate (staticNatValue batch_size)
                      $ mapOuterS replicateBias bias
        -- TODO: this is weakly typed; add and use replicateS instead
        -- or broadcastS or stretchS, possibly with transposeS?
      yRelu = relu $ yConv + biasStretched
  in maxPool24 @1 @2 yRelu

convMnistTwoS
  :: forall kh kw h w c_in c_out n_hidden batch_size d r.
     ( c_in ~ 1
     , 1 <= kh
     , 1 <= kw
     , ADModeAndNum d r )
  => StaticNat kh -> StaticNat kw
  -> StaticNat h -> StaticNat w
  -> StaticNat c_out
  -> StaticNat n_hidden -> StaticNat batch_size
  -> OS.Array '[batch_size, c_in, h, w] r
  -- All below is the type of all parameters of this nn. The same is reflected
  -- in the length function below and read from inputs further down.
  -> ADVal d (OS.Array '[c_out, c_in, kh + 1, kw + 1] r)
  -> ADVal d (OS.Array '[c_out] r)
  -> ADVal d (OS.Array '[c_out, c_out, kh + 1, kw + 1] r)
  -> ADVal d (OS.Array '[c_out] r)
  -> ADVal d (OS.Array '[ n_hidden
                        , c_out * (((h + kh) `Div` 2 + kh) `Div` 2)
                                * (((w + kw) `Div` 2 + kw) `Div` 2)
                        ] r)
  -> ADVal d (OS.Array '[n_hidden] r)
  -> ADVal d (OS.Array '[SizeMnistLabel, n_hidden] r)
  -> ADVal d (OS.Array '[SizeMnistLabel] r)
  -> ADVal d (OS.Array '[SizeMnistLabel, batch_size] r)
convMnistTwoS kh@MkSN kw@MkSN
              h@MkSN w@MkSN
              c_out@MkSN
              _n_hidden@MkSN batch_size@MkSN
              x ker1 bias1 ker2 bias2
              weigthsDense biasesDense weigthsReadout biasesReadout =
  let t1 = convMnistLayerS kh kw
                           h w
                           (MkSN @c_in) c_out
                           batch_size
                           ker1 (constant x) bias1
      t2 = convMnistLayerS kh kw
                           (MkSN @((h + kh) `Div` 2)) (MkSN @((w + kw) `Div` 2))
                           c_out c_out
                           batch_size
                           ker2 t1 bias2
      m1 = mapOuterS reshapeS t2
      m2 = transpose2S m1
      denseLayer = weigthsDense <>$ m2 + asColumnS biasesDense
      denseRelu = relu denseLayer
  in weigthsReadout <>$ denseRelu + asColumnS biasesReadout

convMnistLenS
  :: forall kh kw h w c_out n_hidden.
     StaticNat kh -> StaticNat kw
  -> StaticNat h -> StaticNat w
  -> StaticNat c_out
  -> StaticNat n_hidden
  -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
convMnistLenS MkSN MkSN MkSN MkSN MkSN MkSN =
  ( 0
  , []
  , []
  , [ Data.Array.Shape.shapeT @'[c_out, 1, kh + 1, kw + 1]
    , Data.Array.Shape.shapeT @'[c_out]
    , Data.Array.Shape.shapeT @'[c_out, c_out, kh + 1, kw + 1]
    , Data.Array.Shape.shapeT @'[c_out]
    , Data.Array.Shape.shapeT @'[ n_hidden
                                , c_out
                                  * ((h + kh) `Div` 2 + kh) `Div` 2
                                  * ((w + kw) `Div` 2 + kh) `Div` 2
                                ]
    , Data.Array.Shape.shapeT @'[n_hidden]
    , Data.Array.Shape.shapeT @'[SizeMnistLabel, n_hidden]
    , Data.Array.Shape.shapeT @'[SizeMnistLabel]
    ]
  )

convMnistS
  :: forall kh kw h w c_out batch_size n_hidden d r.
     ( 1 <= kh
     , 1 <= kw
     , ADModeAndNum d r )
  => StaticNat kh -> StaticNat kw
  -> StaticNat h -> StaticNat w
  -> StaticNat c_out
  -> StaticNat batch_size -> StaticNat n_hidden
  -> OS.Array '[batch_size, 1, h, w] r
  -> ADInputs d r
  -> ADVal d (OS.Array '[SizeMnistLabel, batch_size] r)
convMnistS kh@MkSN kw@MkSN
           h@MkSN w@MkSN
           c_out@MkSN
           batch_size@MkSN n_hidden@MkSN
           x inputs =
  let ker1 = atS inputs 0
      bias1 = atS inputs 1
      ker2 = atS inputs 2
      bias2 = atS inputs 3
      weigthsDense = atS inputs 4
      biasesDense = atS inputs 5
      weigthsReadout = atS inputs 6
      biasesReadout = atS inputs 7
  in convMnistTwoS kh kw h w c_out n_hidden batch_size
                   x ker1 bias1 ker2 bias2
                   weigthsDense biasesDense weigthsReadout biasesReadout

convMnistLossFusedS
  :: forall kh kw h w c_out n_hidden batch_size d r.
     ( 1 <= kh
     , 1 <= kw
     , ADModeAndNum d r )
  => StaticNat kh -> StaticNat kw
  -> StaticNat h -> StaticNat w
  -> StaticNat c_out
  -> StaticNat n_hidden -> StaticNat batch_size
  -> ( OS.Array '[batch_size, h, w] r
     , OS.Array '[batch_size, SizeMnistLabel] r )
  -> ADInputs d r
  -> ADVal d r
convMnistLossFusedS kh@MkSN kw@MkSN
                    h@MkSN w@MkSN
                    c_out@MkSN
                    n_hidden@MkSN batch_size@MkSN
                    (glyphS, labelS) inputs =
  let xs :: OS.Array '[batch_size, 1, h, w] r
      xs = OS.reshape glyphS
      result = convMnistS kh kw h w c_out batch_size n_hidden
                          xs inputs
      targets2 = LA.tr $ LA.reshape (staticNatValue sizeMnistLabel :: Int)
                       $ OS.toVector labelS
      vec = lossSoftMaxCrossEntropyL targets2 (fromS2 result)
  in scale (recip $ fromIntegral (staticNatValue batch_size :: Int))
     $ sumElements0 vec

-- For simplicity, testing is performed in mini-batches of 1.
-- See RNN for testing done in batches.
convMnistTestS
  :: forall kh kw h w c_out n_hidden r.
     ( 1 <= kh
     , 1 <= kw
     , ADModeAndNum 'ADModeValue r )
  => StaticNat kh -> StaticNat kw
  -> StaticNat h -> StaticNat w
  -> StaticNat c_out
  -> StaticNat n_hidden
  -> [( OS.Array '[h, w] r
      , OS.Array '[SizeMnistLabel] r )]
  -> Domains r
  -> r
convMnistTestS kh@MkSN kw@MkSN
               h@MkSN w@MkSN
               c_out@MkSN
               n_hidden@MkSN
               inputs parameters =
  let matchesLabels :: ( OS.Array '[h, w] r
                       , OS.Array '[SizeMnistLabel] r )
                    -> Bool
      matchesLabels (glyph, label) =
        let tx :: OS.Array '[1, 1, h, w] r
            tx = OS.reshape glyph
            batch_size_1 = MkSN @1
            nn :: ADInputs 'ADModeValue r
               -> ADVal 'ADModeValue (OS.Array '[SizeMnistLabel, 1] r)
            nn = convMnistS kh kw h w c_out
                            batch_size_1 n_hidden
                            tx
            v = valueFun nn parameters
        in V.maxIndex (OS.toVector v) == V.maxIndex (OS.toVector label)
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
