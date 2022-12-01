{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Shaped tensor-based implementation of Recurrent Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
-- Written in the old style without adaptors and with @rnnMnistLenS@
-- and the @atS@ function instead.
module OldMnistRnnShaped where

import Prelude

import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl')
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (ADInputs, atS)
import MnistData

zeroStateS
  :: (ADModeAndNum d r, OS.Shape sh)
  => (ADVal d (OS.Array sh r)  -- state
      -> a)
  -> a
zeroStateS f = f (konstS 0)

unrollLastS :: forall d state c w r k rest.
               (ADModeAndNum d r, OS.Shape rest)
            => StaticNat k
            -> (state -> OS.Array rest r -> w -> (c, state))
            -> (state -> OS.Array (k : rest) r -> w -> (c, state))
unrollLastS MkSN f s0 xs w =
  let g :: (c, state) -> OS.Array rest r -> (c, state)
      g (_, s) x = f s x w
  in foldl' g (undefined, s0) $ OSB.toList $ OS.unravel xs

type LayerWeigthsRNN in_width out_width d r =
  ( ADVal d (OS.Array '[out_width, in_width] r)   -- input weight
  , ADVal d (OS.Array '[out_width, out_width] r)  -- state weight
  , ADVal d (OS.Array '[out_width] r) )           -- bias

rnnMnistLayerS
  :: forall in_width out_width batch_size d r. ADModeAndNum d r
  => StaticNat in_width -> StaticNat out_width
  -> StaticNat batch_size
  -> ADVal d (OS.Array '[out_width, batch_size] r)  -- in state
  -> ADVal d (OS.Array '[in_width, batch_size] r)  -- in
  -> LayerWeigthsRNN in_width out_width d r
  -> ( ADVal d (OS.Array '[out_width, batch_size] r)  -- out
     , ADVal d (OS.Array '[out_width, batch_size] r) ) -- out state
rnnMnistLayerS MkSN MkSN MkSN
               s x (wX, wS, b) =
  let y = wX <>$ x + wS <>$ s + asColumnS b
      yTanh = tanh y
  in (yTanh, yTanh)

rnnMnistTwoS
  :: forall out_width batch_size sizeMnistHeight d r. ADModeAndNum d r
  => StaticNat out_width
  -> StaticNat batch_size
  -> StaticNat sizeMnistHeight
  -> ADVal d (OS.Array '[2 * out_width, batch_size] r)
       -- initial state
  -> OS.Array '[sizeMnistHeight, batch_size] r
  -> ( LayerWeigthsRNN sizeMnistHeight out_width d r
     , LayerWeigthsRNN out_width out_width d r )
  -> ( ADVal d (OS.Array '[out_width, batch_size] r)
     , ADVal d (OS.Array '[2 * out_width, batch_size] r) )
           -- final state
rnnMnistTwoS out_width@MkSN
             batch_size@MkSN
             sizeMnistHeightHere@MkSN
             s x ((wX, wS, b), (wX2, wS2, b2)) =
  let s1 = sliceS @0 @out_width s
      s2 = sliceS @out_width @out_width s
      (vec1, s1') = rnnMnistLayerS sizeMnistHeightHere
                                   out_width
                                   batch_size
                                   s1 (constant x) (wX, wS, b)
      (vec2, s2') = rnnMnistLayerS out_width
                                   out_width
                                   batch_size
                                   s2 vec1 (wX2, wS2, b2)
      s3 = appendS s1' s2'
  in (vec2, s3)

rnnMnistZeroS
  :: forall out_width batch_size sizeMnistWidth sizeMnistHeight d r.
     ADModeAndNum d r
  => StaticNat out_width
  -> StaticNat batch_size
  -> StaticNat sizeMnistWidth -> StaticNat sizeMnistHeight
  -> OS.Array '[sizeMnistWidth, sizeMnistHeight, batch_size] r
  -- All below is the type of all parameters of this nn. The same is reflected
  -- in the length function below and read from inputs further down.
  -> ( LayerWeigthsRNN sizeMnistHeight out_width d r
     , LayerWeigthsRNN out_width out_width d r )
  -> ADVal d (OS.Array '[SizeMnistLabel, out_width] r)
  -> ADVal d (OS.Array '[SizeMnistLabel] r)
  -> ADVal d (OS.Array '[SizeMnistLabel, batch_size] r)
rnnMnistZeroS out_width@MkSN
              batch_size@MkSN
              sizeMnistWidthHere@MkSN sizeMnistHeightHere@MkSN
              xs ((wX, wS, b), (wX2, wS2, b2)) w3 b3 =
  let rnnMnistTwo = rnnMnistTwoS out_width batch_size sizeMnistHeightHere
      (out, _s) = zeroStateS (unrollLastS @d sizeMnistWidthHere rnnMnistTwo) xs
                             ((wX, wS, b), (wX2, wS2, b2))
  in w3 <>$ out + asColumnS b3

rnnMnistLenS
  :: forall out_width sizeMnistWidth.
     StaticNat out_width -> StaticNat sizeMnistWidth
  -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
rnnMnistLenS MkSN MkSN =
  ( 0
  , []
  , []
  , [ Data.Array.Shape.shapeT @'[out_width, sizeMnistWidth]
    , Data.Array.Shape.shapeT @'[out_width, out_width]
    , Data.Array.Shape.shapeT @'[out_width]
    , Data.Array.Shape.shapeT @'[out_width, out_width]
    , Data.Array.Shape.shapeT @'[out_width, out_width]
    , Data.Array.Shape.shapeT @'[out_width]
    , Data.Array.Shape.shapeT @'[SizeMnistLabel, out_width]
    , Data.Array.Shape.shapeT @'[SizeMnistLabel]
    ]
  )

rnnMnistS
  :: forall out_width batch_size sizeMnistWidth sizeMnistHeight d r.
     ADModeAndNum d r
  => StaticNat out_width
  -> StaticNat batch_size
  -> StaticNat sizeMnistWidth -> StaticNat sizeMnistHeight
  -> OS.Array '[sizeMnistWidth, sizeMnistHeight, batch_size] r
  -> ADInputs d r
  -> ADVal d (OS.Array '[SizeMnistLabel, batch_size] r)
rnnMnistS out_width@MkSN
          batch_size@MkSN
          sizeMnistWidthHere@MkSN sizeMnistHeightHere@MkSN
          xs inputs =
  let wX = atS inputs 0
      wS = atS inputs 1
      b = atS inputs 2
      wX2 = atS inputs 3
      wS2 = atS inputs 4
      b2 = atS inputs 5
      w3 = atS inputs 6
      b3 = atS inputs 7
  in rnnMnistZeroS out_width
                   batch_size
                   sizeMnistWidthHere sizeMnistHeightHere
                   xs ((wX, wS, b), (wX2, wS2, b2)) w3 b3

rnnMnistLossFusedS
  :: forall out_width batch_size d r. ADModeAndNum d r
  => StaticNat out_width
  -> StaticNat batch_size
  -> MnistDataBatchS batch_size r
  -> ADInputs d r
  -> ADVal d r
rnnMnistLossFusedS out_width@MkSN
                   batch_size@MkSN
                   (glyphS, labelS) inputs =
  let xs = OS.transpose @'[2, 1, 0] glyphS
      result = rnnMnistS out_width
                         batch_size
                         sizeMnistWidth sizeMnistHeight
                         xs inputs
      targets2 = LA.tr $ LA.reshape (valueOf @SizeMnistLabel)
                       $ OS.toVector labelS
      vec = lossSoftMaxCrossEntropyL targets2 (fromS2 result)
  in scale (recip $ fromIntegral (valueOf @batch_size :: Int))
     $ sumElements0 vec

rnnMnistTestS
  :: forall out_width batch_size r. ADModeAndNum 'ADModeValue r
  => StaticNat out_width
  -> StaticNat batch_size
  -> MnistDataBatchS batch_size r
  -> Domains r
  -> r
rnnMnistTestS out_width@MkSN
              batch_size@MkSN
              (glyphS, labelS) parameters =
  let xs = OS.transpose @'[2, 1, 0] glyphS
      outputS = valueOnDomains (rnnMnistS out_width
                                    batch_size
                                    sizeMnistWidth sizeMnistHeight
                                    xs) parameters
      outputs = map OS.toVector $ OSB.toList $ OS.unravel
                $ OS.transpose @'[1, 0] $ outputS
      labels = map OS.toVector $ OSB.toList $ OS.unravel labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral (valueOf @batch_size :: Int)
