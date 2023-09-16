{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Shaped tensor-based implementation of Recurrent Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistRnnShaped2 where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (*))
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.Adaptor
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonShapedOps (lossSoftMaxCrossEntropyS)
import HordeAd.Internal.TensorOps
import HordeAd.Util.ShapedList (ShapedList (..))
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
type ADRnnMnistParametersShaped
       (shaped :: ShapedTensorKind) sizeMnistHeight width r =
  ( LayerWeigthsRNNShaped shaped sizeMnistHeight width r
  , LayerWeigthsRNNShaped shaped width width r
  , ( shaped r '[SizeMnistLabel, width]
    , shaped r '[SizeMnistLabel] ) )

type LayerWeigthsRNNShaped shaped in_width out_width r =
  ( shaped r '[out_width, in_width]   -- input weight
  , shaped r '[out_width, out_width]  -- state weight
  , shaped r '[out_width] )           -- bias

zeroStateS
  :: (ShapedTensor shaped, OS.Shape sh, GoodScalar r)
  => (shaped r sh  -- state
      -> a)
  -> a
zeroStateS f = f 0

unrollLastS :: forall shaped state c w r n sh.
               (ShapedTensor shaped, KnownNat n, OS.Shape sh, GoodScalar r)
            => (state -> shaped r sh -> w -> (c, state))
            -> (state -> shaped r (n ': sh) -> w -> (c, state))
unrollLastS f s0 xs w =
  let g :: (c, state) -> shaped r sh -> (c, state)
      g (_, !s) x = f s x w
      projections :: [shaped r sh]
      projections = map (\i -> sindex xs (fromIntegral i :$: ZSH))
                        [0 .. (valueOf @n :: Int)- 1]
  in foldl' g (undefined, s0) projections

rnnMnistLayerS
  :: (ADReadyS shaped, GoodScalar r, Differentiable r)
  => SNat in_width -> SNat out_width -> SNat batch_size
       -- ^ these boilerplate lines tie type parameters to the corresponding
       -- value parameters (@SNat@ below) denoting basic dimensions
  -> shaped r '[out_width, batch_size]  -- state
  -> shaped r '[in_width, batch_size]  -- input
  -> LayerWeigthsRNNShaped shaped in_width out_width r
  -> shaped r '[out_width, batch_size]  -- output state
rnnMnistLayerS SNat SNat SNat
               s x (wX, wS, b) =
    let y = wX `smatmul2` x + wS `smatmul2` s
            + str (sreplicate {-@batch_size-} b)
    in tanh y

rnnMnistTwoS
  :: (ADReadyS shaped, GoodScalar r, Differentiable r)
  => SNat out_width -> SNat batch_size -> SNat sizeMnistHeight
  -> shaped r '[2 * out_width, batch_size]  -- initial state
  -> PrimalOf shaped r '[sizeMnistHeight, batch_size]
  -> ( LayerWeigthsRNNShaped shaped sizeMnistHeight out_width r
     , LayerWeigthsRNNShaped shaped out_width out_width r )
  -> ( shaped r '[out_width, batch_size]
     , shaped r '[2 * out_width, batch_size] )  -- final state
rnnMnistTwoS out_width@SNat
             batch_size@SNat
             sizeMnistHeightHere@SNat
             s' x ((wX, wS, b), (wX2, wS2, b2)) =
    let s3 = slet s' $ \s ->
          let s1 = sslice (Proxy @0) (proxyFromSNat out_width) s
              s2 = sslice (proxyFromSNat out_width) (proxyFromSNat out_width) s
              vec1 = rnnMnistLayerS sizeMnistHeightHere
                                    out_width
                                    batch_size
                                    s1 (sconstant x) (wX, wS, b)
              vec2 = rnnMnistLayerS out_width
                                    out_width
                                    batch_size
                                    s2 vec1 (wX2, wS2, b2)
          in sappend vec1 vec2
    in (sslice (proxyFromSNat out_width) (proxyFromSNat out_width) s3, s3)

rnnMnistZeroS
  :: (ADReadyS shaped, GoodScalar r, Differentiable r)
  => SNat out_width
  -> SNat batch_size
  -> SNat sizeMnistHeight -> SNat sizeMnistWidth
  -> PrimalOf shaped r '[sizeMnistWidth, sizeMnistHeight, batch_size]
  -> ADRnnMnistParametersShaped shaped sizeMnistHeight out_width r
  -> shaped r '[SizeMnistLabel, batch_size]
rnnMnistZeroS out_width@SNat
              batch_size@SNat
              sizeMnistHeightHere@SNat _sizeMnistWidthHere@SNat
              xs ((wX, wS, b), (wX2, wS2, b2), (w3, b3)) =
    let rnnMnistTwo = rnnMnistTwoS out_width batch_size sizeMnistHeightHere
        (out, _s) = zeroStateS (unrollLastS rnnMnistTwo) xs
                               ((wX, wS, b), (wX2, wS2, b2))
    in w3 `smatmul2` out + str (sreplicate {-@batch_size-} b3)

rnnMnistLossFusedS
  :: forall shaped h w out_width batch_size r.
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth, Differentiable r
     , ADReadyS shaped, GoodScalar r )
  => SNat out_width
  -> SNat batch_size
  -> ( PrimalOf shaped r '[batch_size, h, w]
     , PrimalOf shaped r '[batch_size, SizeMnistLabel] )
  -> ADRnnMnistParametersShaped shaped h out_width r
  -> shaped r '[]
rnnMnistLossFusedS out_width@SNat
                   batch_size@SNat
                   (glyphS, labelS) adparameters =
  let xs = stranspose (Proxy @'[2, 1, 0]) glyphS
      result = rnnMnistZeroS out_width
                             batch_size
                             (SNat @h) (SNat @w)
                             xs adparameters
      targets = str labelS
      loss = lossSoftMaxCrossEntropyS targets result
  in sconstant (recip $ sNatValue batch_size) * loss

rnnMnistTestS
  :: forall shaped h w out_width batch_size r.
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , shaped ~ Flip OS.Array, Differentiable r
     , GoodScalar r )
  => SNat out_width
  -> SNat batch_size
  -> ADRnnMnistParametersShaped shaped h out_width r
  -> MnistDataBatchS batch_size r
  -> DomainsOD
  -> r
rnnMnistTestS out_width@SNat batch_size@SNat
              valsInit (glyphS, labelS) testParams =
  let xs = Flip $ OS.transpose @'[2, 1, 0] glyphS
      outputS =
        let nn :: ADRnnMnistParametersShaped shaped h out_width r
               -> shaped r '[SizeMnistLabel, batch_size]
            nn = rnnMnistZeroS out_width
                               batch_size
                               (SNat @h) (SNat @w)
                               xs
        in runFlip $ nn $ parseDomains valsInit testParams
      outputs = map OS.toVector $ tunravelToListS
                $ OS.transpose @'[1, 0] outputS
      labels = map OS.toVector $ tunravelToListS labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / sNatValue batch_size
