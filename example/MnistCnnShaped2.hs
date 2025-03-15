{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Shaped tensor-based implementation of Convolutional Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistCnnShaped2 where

import Prelude

import Data.Type.Equality (gcastWith, (:~:))
import Data.Vector.Generic qualified as V
import Data.Vector.Storable (Vector)
import GHC.TypeLits (fromSNat, type (*), type (+), type (<=), type Div)

import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
--
-- Due to subtraction complicating posititive number type inference,
-- @kh@ denotes kernel height minus one and analogously @kw@ is kernel
-- width minus one.
type ADCnnMnistParametersShaped
       (target :: Target) h w kh kw c_out n_hidden r =
  ( ( target (TKS '[c_out, 1, kh + 1, kw + 1] r)
    , target (TKS '[c_out] r) )
  , ( target (TKS '[c_out, c_out, kh + 1, kw + 1] r)
    , target (TKS '[c_out] r) )
  , ( target (TKS '[n_hidden, c_out * (h `Div` 4) * (w `Div` 4) ] r)
    , target (TKS '[n_hidden] r) )
  , ( target (TKS '[SizeMnistLabel, n_hidden] r)
    , target (TKS '[SizeMnistLabel] r) )
  )

convMnistLayerS
  :: forall kh kw h w c_in c_out batch_size target r.
     -- @c_in@ will be alwayst 1, grayscale, but this function works for any
     ( 1 <= kh
     , 1 <= kw  -- wrongly reported as redundant due to plugins
     , ADReady target, GoodScalar r, Differentiable r )
  => SNat kh -> SNat kw -> SNat h -> SNat w
  -> SNat c_in -> SNat c_out -> SNat batch_size
  -> target (TKS '[c_out, c_in, kh + 1, kw + 1] r)
  -> target (TKS '[batch_size, c_in, h, w] r)
  -> target (TKS '[c_out] r)
  -> target (TKS '[batch_size, c_out, h `Div` 2, w `Div` 2] r)
convMnistLayerS SNat SNat SNat SNat SNat SNat SNat
                ker input bias =
  let yConv = conv2dUnpaddedS ker input
      biasStretched = stranspose @'[0, 3, 1, 2]
                      $ sreplicate {-@batch_size-}
                      $ sreplicate {-@h-}
                      $ sreplicate {-@w-} bias
      yRelu = reluS $ yConv + biasStretched
  in maxPool2dUnpaddedS @2 @2 yRelu

convMnistTwoS
  :: forall kh kw h w c_out n_hidden batch_size target r.
       -- @h@ and @w@ are fixed with MNIST data, but not with test data
     ( 1 <= kh  -- kernel height is large enough
     , 1 <= kw  -- kernel width is large enough
     , ADReady target, GoodScalar r, Differentiable r )
  => SNat kh -> SNat kw -> SNat h -> SNat w
  -> SNat c_out -> SNat n_hidden -> SNat batch_size
       -- ^ these boilerplate lines tie type parameters to the corresponding
       -- SNat value parameters denoting basic dimensions
  -> PrimalOf target (TKS '[batch_size, 1, h, w] r)  -- ^ input images
  -> ADCnnMnistParametersShaped target h w kh kw c_out n_hidden r
       -- ^ parameters
  -> target (TKS '[SizeMnistLabel, batch_size] r)  -- ^ output classification
convMnistTwoS kh@SNat kw@SNat h@SNat w@SNat
              c_out@SNat _n_hidden@SNat batch_size@SNat
              input
              ( (ker1, bias1), (ker2, bias2)
              , (weightsDense, biasesDense), (weightsReadout, biasesReadout) ) =
  gcastWith (unsafeCoerceRefl :: Div (Div w 2) 2 :~: Div w 4) $
  gcastWith (unsafeCoerceRefl :: Div (Div h 2) 2 :~: Div h 4) $
  let t1 = convMnistLayerS kh kw h w
                           (SNat @1) c_out batch_size
                           ker1 (sfromPrimal input) bias1
--      t2 :: target (TKS '[batch_size, c_out, h `Div` 4, w `Div` 4] r)
      t2 = convMnistLayerS kh kw (SNat @(h `Div` 2)) (SNat @(w `Div` 2))
                           c_out c_out batch_size
                           ker2 t1 bias2
--      m1 :: target (TKS '[batch_size, c_out * (h `Div` 4) * (w `Div` 4)] r)
      m1 = sreshape t2
      denseLayer = weightsDense `smatmul2` str m1
                   + str (sreplicate biasesDense)
  in weightsReadout `smatmul2` reluS denseLayer
     + str (sreplicate biasesReadout)

convMnistLossFusedS
  :: forall kh kw h w c_out n_hidden batch_size target r.
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , 1 <= kh
     , 1 <= kw
     , ADReady target, ADReady (PrimalOf target)
     , GoodScalar r, Differentiable r )
  => SNat kh -> SNat kw
  -> SNat c_out
  -> SNat n_hidden -> SNat batch_size
  -> ( PrimalOf target (TKS '[batch_size, h, w] r)
     , PrimalOf target (TKS '[batch_size, SizeMnistLabel] r) )
  -> ADCnnMnistParametersShaped target h w kh kw c_out n_hidden r
  -> target (TKScalar r)
convMnistLossFusedS kh@SNat kw@SNat
                    c_out@SNat n_hidden@SNat batch_size@SNat
                    (glyphS, labelS) adparameters =
  let input :: PrimalOf target (TKS '[batch_size, 1, h, w] r)
      input = sreshape glyphS
      result = convMnistTwoS kh kw (SNat @h) (SNat @w)
                             c_out n_hidden batch_size
                             input adparameters
      targets = str labelS
      loss = lossSoftMaxCrossEntropyS targets result
  in kfromPrimal (recip $ kconcrete $ fromInteger $ fromSNat batch_size) * loss

convMnistTestS
  :: forall kh kw h w c_out n_hidden batch_size target r.
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , 1 <= kh
     , 1 <= kw
     , target ~ Concrete
     , GoodScalar r, Differentiable r )
  => SNat kh -> SNat kw
  -> SNat c_out
  -> SNat n_hidden -> SNat batch_size
  -> MnistDataBatchS batch_size r
  -> ADCnnMnistParametersShaped target h w kh kw c_out n_hidden r
  -> r
convMnistTestS _ _ _ batch_size@SNat _ _ _
  | sNatValue batch_size == 0 = 0
convMnistTestS kh@SNat kw@SNat
               c_out@SNat n_hidden@SNat batch_size@SNat
               (glyphS, labelS) testParams =
  let input :: target (TKS '[batch_size, 1, h, w] r)
      input = sconcrete $ Nested.sreshape knownShS glyphS
      outputS :: Concrete (TKS '[SizeMnistLabel, batch_size] r)
      outputS =
        let nn :: ADCnnMnistParametersShaped target h w kh kw c_out n_hidden r
               -> target (TKS '[SizeMnistLabel, batch_size] r)
            nn = convMnistTwoS kh kw (SNat @h) (SNat @w)
                               c_out n_hidden batch_size
                               input
        in nn testParams
      outputs = map stoVector $ sunravelToList
                $ stranspose @'[1, 0] outputS
      labels = map stoVector
               $ sunravelToList @_ @_ @(TKScalar r)
               $ sconcrete labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromInteger (fromSNat batch_size)
