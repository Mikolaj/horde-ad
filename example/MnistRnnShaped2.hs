{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistRnnShaped2 where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (*))
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.DualNumber
import HordeAd.Core.ShapedList (ShapedList (..))
import HordeAd.Core.TensorClass
import HordeAd.External.CommonShapedOps (lossSoftMaxCrossEntropyS)
import MnistData

type LayerWeigthsRNNShaped shaped in_width out_width r =
  ( shaped r '[out_width, in_width]   -- input weight
  , shaped r '[out_width, out_width]  -- state weight
  , shaped r '[out_width] )           -- bias

type ADRnnMnistParametersShaped shaped sizeMnistHeight width r =
  ( LayerWeigthsRNNShaped shaped sizeMnistHeight width r
  , LayerWeigthsRNNShaped shaped width width r
  , ( shaped r '[SizeMnistLabel, width]
    , shaped r '[SizeMnistLabel] ) )

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
      g (_, s) x = f s x w
      projections :: [shaped r sh]
      projections = map (\i -> sindex xs (fromIntegral i :$: ZSH))
                        [0 .. (valueOf @n :: Int)- 1]
  in foldl' g (undefined, s0) projections

rnnMnistLayerS
  :: ADReadyS shaped r
  => SNat in_width -> SNat out_width -> SNat batch_size
  -> shaped r '[out_width, batch_size]  -- in state
  -> shaped r '[in_width, batch_size]  -- in
  -> LayerWeigthsRNNShaped shaped in_width out_width r
  -> shaped r '[out_width, batch_size]  -- out
rnnMnistLayerS SNat SNat SNat
               s x (wX, wS, b) =
    let y = wX `smatmul2` x + wS `smatmul2` s
            + str (sreplicate {-@batch_size-} b)
    in tanh y

rnnMnistTwoS
  :: ADReadyS shaped r
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
  :: ADReadyS shaped r
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
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , ADReadyS shaped r )
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
     , shaped ~ Flip OS.Array
     , ADReadyS shaped r )
  => SNat out_width
  -> SNat batch_size
  -> MnistDataBatchS batch_size r
  -> ((ADRnnMnistParametersShaped shaped h out_width r
       -> shaped r '[SizeMnistLabel, batch_size])
      -> OS.Array '[SizeMnistLabel, batch_size] r)
  -> r
{-# INLINE rnnMnistTestS #-}
rnnMnistTestS out_width@SNat
              batch_size@SNat
              (glyphS, labelS) evalAtTestParams =
  let xs = Flip $ OS.transpose @'[2, 1, 0] glyphS
      outputS =
        let nn :: ADRnnMnistParametersShaped shaped h out_width r
               -> shaped r '[SizeMnistLabel, batch_size]
            nn = rnnMnistZeroS out_width
                               batch_size
                               (SNat @h) (SNat @w)
                               xs
        in evalAtTestParams nn
      outputs = map OS.toVector $ OSB.toList $ OS.unravel
                $ OS.transpose @'[1, 0] outputS
      labels = map OS.toVector $ OSB.toList $ OS.unravel labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / sNatValue batch_size