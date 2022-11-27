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

import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.DualNumber
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
                        , (h + kh) `Div` 2, (w + kw) `Div` 2 ] r)
convMnistLayerS MkSN MkSN MkSN MkSN MkSN MkSN batch_size@MkSN
                ker input bias =
  let yConv = conv24 ker input
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
     -- @c_in@ will be alwayst 1, grayscale, but this function works for any;
     -- similarly, @h@ and @w@ are fixed for MNIST
     ( 1 <= kh             -- kernel height is large enough
     , 1 <= kw             -- kernel width is large enough
     , ADModeAndNum d r )  -- differentiation mode and scalar type are legal
  => StaticNat kh -> StaticNat kw
  -> StaticNat h -> StaticNat w
  -> StaticNat c_in -> StaticNat c_out
  -> StaticNat n_hidden -> StaticNat batch_size
       -- ^ these boilerplate lines tie type parameters to the corresponding
       -- value parameters (@MkSN@ below) denoting basic dimensions

  -> OS.Array '[batch_size, c_in, h, w] r  -- ^ input images

  -- All the pairs below form the set of all parameters of this nn,
  -- slightly generalized (arbitrary @c_in@). Compare with
  -- @ADConvMnistParameters@.
  -> ( ADVal d (OS.Array '[c_out, c_in, kh + 1, kw + 1] r)
     , ADVal d (OS.Array '[c_out] r ) )
  -> ( ADVal d (OS.Array '[c_out, c_out, kh + 1, kw + 1] r)
     , ADVal d (OS.Array '[c_out] r) )
  -> ( ADVal d (OS.Array '[ n_hidden
                          , c_out * (((h + kh) `Div` 2 + kh) `Div` 2)
                                  * (((w + kw) `Div` 2 + kw) `Div` 2)
                          ] r)
     , ADVal d (OS.Array '[n_hidden] r) )
  -> ( ADVal d (OS.Array '[SizeMnistLabel, n_hidden] r)
     , ADVal d (OS.Array '[SizeMnistLabel] r) )

  -> ADVal d (OS.Array '[SizeMnistLabel, batch_size] r)  -- classification
convMnistTwoS kh@MkSN kw@MkSN
              h@MkSN w@MkSN
              c_in@MkSN c_out@MkSN
              _n_hidden@MkSN batch_size@MkSN
              input
              (ker1, bias1) (ker2, bias2)
              (weigthsDense, biasesDense) (weigthsReadout, biasesReadout) =
  let t1 = convMnistLayerS kh kw
                           h w
                           c_in c_out
                           batch_size
                           ker1 (constant input) bias1
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

-- The differentiable type of all trainable parameters of this nn.
type ADConvMnistParameters kh kw c_out n_hidden d r =
  ( ( ADVal d (OS.Array '[c_out, 1, kh + 1, kw + 1] r)
    , ADVal d (OS.Array '[c_out] r) )
  , ( ADVal d (OS.Array '[c_out, c_out, kh + 1, kw + 1] r)
    , ADVal d (OS.Array '[c_out] r) )
  , ( ADVal d (OS.Array '[ n_hidden
                         , c_out
                           * (((SizeMnistHeight + kh) `Div` 2 + kh) `Div` 2)
                           * (((SizeMnistWidth + kw) `Div` 2 + kw) `Div` 2)
                         ] r)
    , ADVal d (OS.Array '[n_hidden] r) )
  , ( ADVal d (OS.Array '[SizeMnistLabel, n_hidden] r)
    , ADVal d (OS.Array '[SizeMnistLabel] r) )
  )

convMnistLossFusedS
  :: forall kh kw h w c_in c_out n_hidden batch_size d r.
     ( c_in ~ 1
     , h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , 1 <= kh
     , 1 <= kw
     , ADModeAndNum d r )
  => StaticNat kh -> StaticNat kw
  -> StaticNat c_out
  -> StaticNat n_hidden -> StaticNat batch_size
  -> ( OS.Array '[batch_size, h, w] r
     , OS.Array '[batch_size, SizeMnistLabel] r )
  -> ADConvMnistParameters kh kw c_out n_hidden d r
  -> ADVal d r
convMnistLossFusedS kh@MkSN kw@MkSN
                    c_out@MkSN
                    n_hidden@MkSN batch_size@MkSN
                    (glyphS, labelS) _adparameters@(a1, a2, a3, a4) =
  let input :: OS.Array '[batch_size, c_in, h, w] r
      input = OS.reshape glyphS
      result = convMnistTwoS kh kw (MkSN @h) (MkSN @w) (MkSN @c_in)
                             c_out n_hidden batch_size
                             input a1 a2 a3 a4
      targets2 = LA.tr $ LA.reshape (staticNatValue sizeMnistLabel :: Int)
                       $ OS.toVector labelS
      vec = lossSoftMaxCrossEntropyL targets2 (fromS2 result)
  in scale (recip $ fromIntegral (staticNatValue batch_size :: Int))
     $ sumElements0 vec

convMnistTestS
  :: forall kh kw h w c_in c_out n_hidden batch_size r.
     ( c_in ~ 1
     , h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , 1 <= kh
     , 1 <= kw
     , ADModeAndNum 'ADModeValue r )
  => StaticNat kh -> StaticNat kw
  -> StaticNat c_out
  -> StaticNat n_hidden -> StaticNat batch_size
  -> MnistDataBatchS batch_size r
  -> ((ADConvMnistParameters kh kw c_out n_hidden 'ADModeValue r
       -> ADVal 'ADModeValue (OS.Array '[SizeMnistLabel, batch_size] r))
      -> (OS.Array '[SizeMnistLabel, batch_size] r))
  -> r
convMnistTestS kh@MkSN kw@MkSN
               c_out@MkSN
               n_hidden@MkSN batch_size@MkSN
               (glyphS, labelS) evalAtFixedParams =
  let input :: OS.Array '[batch_size, c_in, h, w] r
      input = OS.reshape glyphS
      outputS =
        let nn :: ADConvMnistParameters kh kw c_out n_hidden 'ADModeValue r
               -> ADVal 'ADModeValue (OS.Array '[SizeMnistLabel, batch_size] r)
            nn _adparameters@(a1, a2, a3, a4) =
              convMnistTwoS kh kw (MkSN @h) (MkSN @w) (MkSN @c_in) c_out
                            n_hidden batch_size
                            input a1 a2 a3 a4
        in evalAtFixedParams nn
      outputs = map OS.toVector $ OSB.toList $ OS.unravel
                $ OS.transpose @'[1, 0] $ outputS
      labels = map OS.toVector $ OSB.toList $ OS.unravel labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral (valueOf @batch_size :: Int)
