{-# LANGUAGE FlexibleContexts, RankNTypes #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistAdTools where

import Prelude

import           Control.Arrow ((***))
import           Control.Exception (assert)
import           Criterion.Main
import           Data.Reflection (Reifies)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           GHC.Exts (inline)
import           Numeric.AD.Internal.Reverse.Double (Tape)
import           Numeric.AD.Mode.Reverse.Double hiding (diff)
import           System.Random

type Domain r = Data.Vector.Vector r

type Domain' r = Domain r

gradDescStochastic
  :: forall a.
     Double
  -> (a -> (forall s. Reifies s Tape
             => Data.Vector.Vector (ReverseDouble s) -> ReverseDouble s))
  -> [a]  -- ^ training data
  -> Domain Double  -- ^ initial parameters
  -> Domain' Double
gradDescStochastic gamma f = go where
  go :: [a] -> Domain Double -> Domain' Double
  go [] !params = params
  go (a : rest) params =
    let combine i r = i - gamma * r
        v = gradWith combine (f a) params
    in go rest v

var :: Int -> Domain r -> r
var i vec = vec V.! i

sumDual :: forall r. Num r
        => Data.Vector.Vector r
        -> r
sumDual = V.foldl' (+) 0

sumConstantData, sumTrainableInputs
                :: forall r. Num r
                => Domain r
                -> Int
                -> Data.Vector.Vector r
                -> r
sumConstantData xs offset vec =
  let bias = var offset vec
      f :: r -> Int -> r -> r
      f !acc i r =
        let v = var (offset + 1 + i) vec
        in acc + r * v
  in V.ifoldl' f bias xs

sumTrainableInputs = sumConstantData

logisticAct :: Floating r => r -> r
logisticAct u = recip (1 + exp (- u))

softMaxAct :: Floating r
           => Data.Vector.Vector r
           -> Data.Vector.Vector r
softMaxAct us =
  let expUs = V.map exp us
      sumExpUs = sumDual expUs
  in V.map (/ sumExpUs) expUs

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy
  :: forall r. Floating r
  => Data.Vector.Vector r
  -> Data.Vector.Vector r
  -> r
lossCrossEntropy targ res =
  let f :: r -> Int -> r -> r
      f !acc i d = acc + (targ V.! i) * log d
  in negate $ V.ifoldl' f 0 res

sizeMnistGlyph :: Int
sizeMnistGlyph = 784

sizeMnistLabel :: Int
sizeMnistLabel = 10

type MnistData = ( Data.Vector.Vector Double
                 , Data.Vector.Vector Double )

hiddenLayerMnist :: forall r. Num r
                 => (r -> r)
                 -> Domain r
                 -> Data.Vector.Vector r
                 -> Int
                 -> Data.Vector.Vector r
hiddenLayerMnist factivation xs vec width =
  let nWeightsAndBias = V.length xs + 1
      f :: Int -> r
      f i =
        let outSum = sumConstantData xs (i * nWeightsAndBias) vec
        in factivation outSum
  in V.generate width f

middleLayerMnist :: forall r. Num r
                 => (r -> r)
                 -> Data.Vector.Vector r
                 -> Int
                 -> Data.Vector.Vector r
                 -> Int
                 -> Data.Vector.Vector r
middleLayerMnist factivation hiddenVec offset vec width =
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> r
      f i =
        let outSum = sumTrainableInputs hiddenVec
                                     (offset + i * nWeightsAndBias)
                                     vec
        in factivation outSum
  in V.generate width f

outputLayerMnist :: forall r. Num r
                 => (Data.Vector.Vector r
                     -> Data.Vector.Vector r)
                 -> Data.Vector.Vector r
                 -> Int
                 -> Data.Vector.Vector r
                 -> Int
                 -> Data.Vector.Vector r
outputLayerMnist factivation hiddenVec offset vec width =
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> r
      f i = sumTrainableInputs hiddenVec (offset + i * nWeightsAndBias) vec
      vOfSums = V.generate width f
  in factivation vOfSums

lenMnist2 :: Int -> Int -> Int
lenMnist2 widthHidden widthHidden2 =
  widthHidden * (sizeMnistGlyph + 1)
  + widthHidden2 * (widthHidden + 1)
  + sizeMnistLabel * (widthHidden2 + 1)

-- Two hidden layers of width @widthHidden@ and (the middle one) @widthHidden2@.
-- Both hidden layers use the same activation function.
nnMnist2 :: forall r. Num r
         => (r -> r)
         -> (Data.Vector.Vector r
             -> Data.Vector.Vector r)
         -> Int
         -> Int
         -> Domain r
         -> Data.Vector.Vector r
         -> Data.Vector.Vector r
nnMnist2 factivationHidden factivationOutput widthHidden widthHidden2
         xs vec =
  let !_A = assert (sizeMnistGlyph == V.length xs) ()
      hiddenVec = inline hiddenLayerMnist factivationHidden xs vec widthHidden
      offsetMiddle = widthHidden * (sizeMnistGlyph + 1)
      middleVec = inline middleLayerMnist factivationHidden hiddenVec
                                       offsetMiddle vec widthHidden2
      offsetOutput = offsetMiddle + widthHidden2 * (widthHidden + 1)
  in inline outputLayerMnist factivationOutput middleVec
                          offsetOutput vec sizeMnistLabel

nnMnistLoss2 :: forall s. Reifies s Tape
             => Int
             -> Int
             -> MnistData
             -> Data.Vector.Vector (ReverseDouble s)
             -> ReverseDouble s
nnMnistLoss2 widthHidden widthHidden2 (x, targ) vec =
  let res = inline nnMnist2 logisticAct softMaxAct widthHidden widthHidden2
                            (V.map auto x) vec
  in lossCrossEntropy (V.map auto targ) res

generalTestMnist :: (Domain Double
                     -> Data.Vector.Vector Double
                     -> Data.Vector.Vector Double)
                 -> [MnistData] -> Domain Double
                 -> Double
{-# INLINE generalTestMnist #-}
generalTestMnist nn xs res =
  let matchesLabels :: MnistData -> Bool
      matchesLabels (glyph, label) =
        let value = nn glyph res
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels xs)) / fromIntegral (length xs)

testMnist2 :: Int -> Int -> [MnistData] -> Domain Double -> Double
testMnist2 widthHidden widthHidden2 xs res =
  generalTestMnist (inline nnMnist2 logisticAct softMaxAct
                                    widthHidden widthHidden2)
                   xs res

type MnistDataUnboxed = ( Data.Vector.Unboxed.Vector Double
                        , Data.Vector.Unboxed.Vector Double )

mnistTrainBench2 :: Int -> [MnistData] -> Int -> Int -> Double -> Benchmark
mnistTrainBench2 chunkLength xs widthHidden widthHidden2 gamma = do
  let nParams = lenMnist2 widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      f :: MnistData
        -> (forall s. Reifies s Tape
            => Data.Vector.Vector (ReverseDouble s) -> ReverseDouble s)
      f = nnMnistLoss2 widthHidden widthHidden2
      chunk = take chunkLength xs
      gradd c = gradDescStochastic gamma f c params0
      name = "train2 "
             ++ unwords [show widthHidden, show widthHidden2, show nParams]
  bench name $ whnf gradd chunk

mnistTestBench2 :: Int -> [MnistData] -> Int -> Int -> Benchmark
mnistTestBench2 chunkLength xs widthHidden widthHidden2 = do
  let nParams = lenMnist2 widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      chunk = take chunkLength xs
      score c = testMnist2 widthHidden widthHidden2 c params0
      name = "test2 "
             ++ unwords [show widthHidden, show widthHidden2, show nParams ]
  bench name $ whnf score chunk

mnistTrainBGroup2 :: [MnistDataUnboxed] -> Int -> Benchmark
mnistTrainBGroup2 xs0 chunkLength =
  env (return $ map (V.convert *** V.convert) xs0) $
  \ ~xs ->
  bgroup ("2-hidden-layer MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2 chunkLength xs 30 10  -- toy width
    , mnistTrainBench2 chunkLength xs 30 10 0.02
    , mnistTestBench2 chunkLength xs 300 100  -- ordinary width
    , mnistTrainBench2 chunkLength xs 300 100 0.02
    , mnistTestBench2 chunkLength xs 500 150  -- another common size
    , mnistTrainBench2 chunkLength xs 500 150 0.02
    ]
