{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Shaped tensor-based implementation of Convolutional Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistCnnShaped2 where

import Prelude

import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (type (*), type (+), type (<=), type Div)
import           Numeric.LinearAlgebra (Vector)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Adaptor
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonShapedOps
import HordeAd.Internal.TensorOps
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
--
-- Due to subtraction complicating posititive number type inference,
-- @kh@ denotes kernel height minus one and analogously @kw@ is kernel
-- width minus one.
type ADCnnMnistParametersShaped
       (shaped :: ShapedTensorType) h w kh kw c_out n_hidden r =
  ( ( shaped r '[c_out, 1, kh + 1, kw + 1]
    , shaped r '[c_out] )
  , ( shaped r '[c_out, c_out, kh + 1, kw + 1]
    , shaped r '[c_out] )
  , ( shaped r '[n_hidden, c_out * (h `Div` 4) * (w `Div` 4) ]
    , shaped r '[n_hidden] )
  , ( shaped r '[SizeMnistLabel, n_hidden]
    , shaped r '[SizeMnistLabel] )
  )

convMnistLayerS
  :: forall kh kw h w c_in c_out batch_size shaped r.
     -- @c_in@ will be alwayst 1, grayscale, but this function works for any
     ( 1 <= kh
     , 1 <= kw  -- wrongly reported as redundant due to plugins
     , ADReadyS shaped, GoodScalar r, Differentiable r )
  => SNat kh -> SNat kw
  -> SNat h -> SNat w
  -> SNat c_in -> SNat c_out
  -> SNat batch_size
  -> shaped r '[c_out, c_in, kh + 1, kw + 1]
  -> shaped r '[batch_size, c_in, h, w]
  -> shaped r '[c_out]
  -> shaped r '[batch_size, c_out, h `Div` 2, w `Div` 2]
convMnistLayerS SNat SNat SNat SNat SNat SNat SNat
                ker input bias =
  let yConv = conv2dUnpaddedS ker input
      biasStretched = stranspose (Proxy @'[0, 3, 1, 2])
                      $ sreplicate {-@batch_size-}
                      $ sreplicate {-@h-}
                      $ sreplicate {-@w-} bias
      yRelu = reluS $ yConv + biasStretched
  in maxPool2dUnpaddedS @2 @2 yRelu

convMnistTwoS
  :: forall kh kw h w c_out n_hidden batch_size shaped r.
       -- @h@ and @w@ are fixed for MNIST, but may be different, e.g., in tests
     ( 1 <= kh             -- kernel height is large enough
     , 1 <= kw             -- kernel width is large enough
     , ADReadyS shaped, GoodScalar r, Differentiable r )
  => SNat kh -> SNat kw
  -> SNat h -> SNat w
  -> SNat c_out -> SNat n_hidden -> SNat batch_size
       -- ^ these boilerplate lines tie type parameters to the corresponding
       -- value parameters (@SNat@ below) denoting basic dimensions
  -> PrimalOf shaped r '[batch_size, 1, h, w]  -- ^ input images
  -> ADCnnMnistParametersShaped shaped h w kh kw c_out n_hidden r
  -> shaped r '[SizeMnistLabel, batch_size]  -- ^ classification
convMnistTwoS kh@SNat kw@SNat
              h@SNat w@SNat
              c_out@SNat _n_hidden@SNat batch_size@SNat
              input
              ( (ker1, bias1), (ker2, bias2)
              , (weightsDense, biasesDense), (weightsReadout, biasesReadout) ) =
  gcastWith (unsafeCoerce Refl :: Div (Div w 2) 2 :~: Div w 4) $
  gcastWith (unsafeCoerce Refl :: Div (Div h 2) 2 :~: Div h 4) $
  let t1 = convMnistLayerS kh kw
                           h w
                           (SNat @1) c_out batch_size
                           ker1 (sconstant input) bias1
      t2 :: shaped r '[batch_size, c_out, h `Div` 4, w `Div` 4]
      t2 = convMnistLayerS kh kw
                           (SNat @(h `Div` 2)) (SNat @(w `Div` 2))
                           c_out c_out batch_size
                           ker2 t1 bias2
      m1 :: shaped r '[batch_size, c_out * (h `Div` 4) * (w `Div` 4)]
      m1 = sreshape t2
      m2 = str m1
      denseLayer = weightsDense `smatmul2` m2
                   + str (sreplicate {-@batch_size-} biasesDense)
      denseRelu = reluS denseLayer
  in weightsReadout `smatmul2` denseRelu
     + str (sreplicate {-@batch_size-} biasesReadout)

convMnistLossFusedS
  :: forall kh kw h w c_out n_hidden batch_size shaped r.
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , 1 <= kh
     , 1 <= kw
     , ADReadyS shaped, ADReadyS (PrimalOf shaped)
     , GoodScalar r, Differentiable r )
  => SNat kh -> SNat kw
  -> SNat c_out
  -> SNat n_hidden -> SNat batch_size
  -> ( PrimalOf shaped r '[batch_size, h, w]
     , PrimalOf shaped r '[batch_size, SizeMnistLabel] )
  -> ADCnnMnistParametersShaped shaped h w kh kw c_out n_hidden r
  -> shaped r '[]
convMnistLossFusedS kh@SNat kw@SNat
                    c_out@SNat n_hidden@SNat batch_size@SNat
                    (glyphS, labelS) adparameters =
  let input :: PrimalOf shaped r '[batch_size, 1, h, w]
      input = sreshape glyphS
      result = convMnistTwoS kh kw (SNat @h) (SNat @w)
                             c_out n_hidden batch_size
                             input adparameters
      targets = str labelS
      loss = lossSoftMaxCrossEntropyS targets result
  in sconstant (recip $ sNatValue batch_size) * loss

convMnistTestS
  :: forall kh kw h w c_out n_hidden batch_size shaped r.
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , 1 <= kh
     , 1 <= kw
     , shaped ~ Flip OS.Array
     , GoodScalar r, Differentiable r )
  => SNat kh -> SNat kw
  -> SNat c_out
  -> SNat n_hidden -> SNat batch_size
  -> ADCnnMnistParametersShaped shaped h w kh kw c_out n_hidden r
  -> MnistDataBatchS batch_size r
  -> DomainsOD
  -> r
convMnistTestS  _ _ _ _ batch_size@SNat _ _ _
  | sNatValue batch_size == (0 :: Int) = 0
convMnistTestS kh@SNat kw@SNat
               c_out@SNat n_hidden@SNat batch_size@SNat
               valsInit (glyphS, labelS) testParams =
  let input :: shaped r '[batch_size, 1, h, w]
      input = Flip $ OS.reshape glyphS
      outputS =
        let nn :: ADCnnMnistParametersShaped shaped h w kh kw c_out n_hidden r
               -> shaped r '[SizeMnistLabel, batch_size]
            nn = convMnistTwoS kh kw (SNat @h) (SNat @w)
                               c_out n_hidden batch_size
                               input
        in runFlip $ nn $ parseDomains valsInit testParams
      outputs = map OS.toVector $ tunravelToListS
                $ OS.transpose @'[1, 0] $ outputS
      labels = map OS.toVector $ tunravelToListS labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / sNatValue batch_size
