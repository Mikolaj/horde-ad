{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistMostlyHarmlessTools where

import Prelude

import           Criterion.Main
import qualified Data.Vector.Generic as V
import           System.Random

import AD
import MnistTools

mnistTrainBench :: Int -> [MnistData] -> Int -> Double -> Benchmark
mnistTrainBench chunkLength xs widthHidden gamma = do
  let nParams = lenMnist widthHidden
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      f = nnMnistLoss widthHidden
      chunk = take chunkLength xs
      grad c = gradDescStochastic gamma f c params0
      name = "train a 1-hidden-layer MNIST nn "
             ++ unwords [ show chunkLength, show widthHidden, show nParams
                        , show gamma ]
  bench name $ whnf grad chunk

mnistTestBench :: Int -> [MnistData] -> Int -> Benchmark
mnistTestBench chunkLength xs widthHidden = do
  let nParams = lenMnist widthHidden
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      chunk = take chunkLength xs
      score c = testMnist widthHidden c params0
      name = "test a 1-hidden-layer MNIST nn "
             ++ unwords [show chunkLength, show widthHidden, show nParams]
  bench name $ whnf score chunk

mnistTrainBGroup :: [MnistData] -> Int -> Benchmark
mnistTrainBGroup xs0 chunkLength =
  env (return xs0) $
  \ ~xs ->
  bgroup ("1-hidden-layer MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench chunkLength xs 25  -- toy width
    , mnistTrainBench chunkLength xs 25 0.02
    , mnistTestBench chunkLength xs 250  -- ordinary width
    , mnistTrainBench chunkLength xs 250 0.02
    , mnistTestBench chunkLength xs 2500  -- probably mostly wasted
    , mnistTrainBench chunkLength xs 2500 0.02
    ]

mnistTrainBench2 :: Int -> [MnistData] -> Int -> Int -> Double -> Benchmark
mnistTrainBench2 chunkLength xs widthHidden widthHidden2 gamma = do
  let nParams = lenMnist2 widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      f = nnMnistLoss2 widthHidden widthHidden2
      chunk = take chunkLength xs
      grad c = gradDescStochastic gamma f c params0
      name = "train a 2-hidden-layer MNIST nn "
             ++ unwords [ show chunkLength, show widthHidden, show widthHidden2
                        , show nParams, show gamma ]
  bench name $ whnf grad chunk

mnistTestBench2 :: Int -> [MnistData] -> Int -> Int -> Benchmark
mnistTestBench2 chunkLength xs widthHidden widthHidden2 = do
  let nParams = lenMnist2 widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      chunk = take chunkLength xs
      score c = testMnist2 widthHidden widthHidden2 c params0
      name = "test a 2-hidden-layer MNIST nn "
             ++ unwords [ show chunkLength, show widthHidden, show widthHidden2
                        , show nParams ]
  bench name $ whnf score chunk

mnistTrainBGroup2 :: [MnistData] -> Int -> Benchmark
mnistTrainBGroup2 xs0 chunkLength =
  env (return xs0) $
  \ ~xs ->
  bgroup ("2-hidden-layer MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2 chunkLength xs 30 10  -- toy width
    , mnistTrainBench2 chunkLength xs 30 10 0.02
    , mnistTestBench2 chunkLength xs 300 100  -- ordinary width
    , mnistTrainBench2 chunkLength xs 300 100 0.02
    , mnistTestBench2 chunkLength xs 500 150  -- another common size
    , mnistTrainBench2 chunkLength xs 500 150 0.02
    ]
