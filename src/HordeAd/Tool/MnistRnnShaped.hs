{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes, TypeFamilies,
             TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- Needed due to unsafePerformIO:
{-# OPTIONS_GHC -fno-full-laziness #-}
-- | Shaped tensor-based implementation of Recurrent Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module HordeAd.Tool.MnistRnnShaped where

import Prelude

import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl')
import           Data.Proxy (Proxy)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM

-- until stylish-haskell accepts NoStarIsType
import qualified GHC.TypeLits

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (DualNumberVariables, varS)
import HordeAd.Tool.MnistData

zeroStateS
  :: (IsScalar d r, OS.Shape sh)
  => (DualNumber d (OS.Array sh r)  -- state
      -> a)
  -> a
zeroStateS f = f (konstS 0)

unrollLastS :: forall d state c w r k rest.
               (IsScalar d r, KnownNat k, OS.Shape rest)
            => (state -> OS.Array rest r -> w -> (c, state))
            -> (state -> OS.Array (k : rest) r -> w -> (c, state))
unrollLastS f s0 xs w =
  let g :: (c, state) -> OS.Array rest r -> (c, state)
      g (_, s) x = f s x w
  in foldl' g (undefined, s0) $ OSB.toList $ OS.unravel xs

type LayerWeigthsRNN in_width out_width d r =
  ( DualNumber d (OS.Array '[out_width, in_width] r)   -- input weight
  , DualNumber d (OS.Array '[out_width, out_width] r)  -- state weight
  , DualNumber d (OS.Array '[out_width] r) )           -- bias

rnnMnistLayerS
  :: forall in_width out_width batch_size d r.
     ( IsScalar d r
     , KnownNat in_width, KnownNat out_width, KnownNat batch_size )
  => DualNumber d (OS.Array '[out_width, batch_size] r)  -- in state
  -> DualNumber d (OS.Array '[in_width, batch_size] r)  -- in
  -> LayerWeigthsRNN in_width out_width d r
  -> ( DualNumber d (OS.Array '[out_width, batch_size] r)  -- out
     , DualNumber d (OS.Array '[out_width, batch_size] r) ) -- out state
rnnMnistLayerS s x (wX, wS, b) =
  let y = wX <>$ x + wS <>$ s + asColumnS b
      yTanh = tanh y
  in (yTanh, yTanh)

rnnMnistTwoS
  :: forall out_width batch_size sizeMnistHeight d r.
     ( IsScalar d r, KnownNat out_width, KnownNat batch_size
     , KnownNat sizeMnistHeight )
  => DualNumber d (OS.Array '[2 GHC.TypeLits.* out_width, batch_size] r)
       -- initial state
  -> OS.Array '[sizeMnistHeight, batch_size] r
  -> ( LayerWeigthsRNN sizeMnistHeight out_width d r
     , LayerWeigthsRNN out_width out_width d r )
  -> ( DualNumber d (OS.Array '[out_width, batch_size] r)
     , DualNumber d (OS.Array '[2 GHC.TypeLits.* out_width, batch_size] r) )
           -- final state
rnnMnistTwoS s x ((wX, wS, b), (wX2, wS2, b2)) =
  let s1 = sliceS @0 @out_width s
      s2 = sliceS @out_width @out_width s
      (vec1, s1') = rnnMnistLayerS s1 (constant x) (wX, wS, b)
      (vec2, s2') = rnnMnistLayerS s2 vec1 (wX2, wS2, b2)
      s3 = appendS s1' s2'
  in (vec2, s3)

rnnMnistZeroS
  :: forall out_width batch_size sizeMnistWidth sizeMnistHeight d r.
     ( IsScalar d r, KnownNat out_width, KnownNat batch_size
     , KnownNat sizeMnistWidth, KnownNat sizeMnistHeight )
  => OS.Array '[sizeMnistWidth, sizeMnistHeight, batch_size] r
  -- All below is the type of all parameters of this nn. The same is reflected
  -- in the length function below and read from variables further down.
  -> ( LayerWeigthsRNN sizeMnistHeight out_width d r
     , LayerWeigthsRNN out_width out_width d r )
  -> DualNumber d (OS.Array '[SizeMnistLabel, out_width] r)
  -> DualNumber d (OS.Array '[SizeMnistLabel] r)
  -> DualNumber d (OS.Array '[SizeMnistLabel, batch_size] r)
rnnMnistZeroS xs ((wX, wS, b), (wX2, wS2, b2)) w3 b3 =
  let (out, _s) = zeroStateS (unrollLastS @d rnnMnistTwoS) xs
                             ((wX, wS, b), (wX2, wS2, b2))
  in w3 <>$ out + asColumnS b3

rnnMnistLenS
  :: forall out_width sizeMnistWidth.
     (KnownNat out_width, KnownNat sizeMnistWidth)
  => Proxy out_width -> Proxy sizeMnistWidth
  -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
rnnMnistLenS _ _ =
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
     ( IsScalar d r, KnownNat out_width, KnownNat batch_size
     , KnownNat sizeMnistWidth, KnownNat sizeMnistHeight )
  => OS.Array '[sizeMnistWidth, sizeMnistHeight, batch_size] r
  -> DualNumberVariables d r
  -> DualNumber d (OS.Array '[SizeMnistLabel, batch_size] r)
rnnMnistS xs variables =
  let wX = varS variables 0
      wS = varS variables 1
      b = varS variables 2
      wX2 = varS variables 3
      wS2 = varS variables 4
      b2 = varS variables 5
      w3 = varS variables 6
      b3 = varS variables 7
  in rnnMnistZeroS @out_width xs ((wX, wS, b), (wX2, wS2, b2)) w3 b3

rnnMnistLossFusedS
  :: forall out_width batch_size d r.
     (IsScalar d r, KnownNat out_width, KnownNat batch_size)
  => Proxy out_width
  -> MnistDataBatchS batch_size r
  -> DualNumberVariables d r
  -> DualNumber d r
rnnMnistLossFusedS _ (glyphS, labelS) variables =
  let xs = OS.transpose @'[2, 1, 0] glyphS
      result = rnnMnistS @out_width xs variables
      targets2 = HM.tr $ HM.reshape (valueOf @SizeMnistLabel)
                       $ OS.toVector labelS
      vec = lossSoftMaxCrossEntropyL targets2 (fromS2 result)
  in scale (recip $ fromIntegral (valueOf @batch_size :: Int))
     $ sumElements0 vec

rnnMnistTestS
  :: forall out_width batch_size r.
     (IsScalar 'DModeValue r, KnownNat out_width, KnownNat batch_size)
  => Proxy out_width
  -> MnistDataBatchS batch_size r
  -> Domains r
  -> r
rnnMnistTestS _ (glyphS, labelS) parameters =
  let xs = OS.transpose @'[2, 1, 0] glyphS
      outputS = primalValue (rnnMnistS @out_width xs) parameters
      outputs = map OS.toVector $ OSB.toList $ OS.unravel
                $ OS.transpose @'[1, 0] $ outputS
      labels = map OS.toVector $ OSB.toList $ OS.unravel labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral (valueOf @batch_size :: Int)
