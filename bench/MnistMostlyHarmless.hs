module Main (main) where

import Prelude

import           Criterion.Main
import qualified Data.Vector.Generic as V
import           System.Random

import AD
import MnistTools

main :: IO ()
main = do
  testData <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
  defaultMain
    [ mnistTrainBGroup testData 500
--    , mnistTrainBGroup testData 5000  -- ordinary chunk size, takes too long
    ]

mnistTrainBench :: Int -> [MnistData] -> Int -> Double -> Benchmark
mnistTrainBench chunkLength xs widthHidden gamma = do
  let nParams = lenMnist widthHidden
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      f = nnMnistLoss logisticAct softMaxActUnfused widthHidden
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
      score c = testMnist c params0 widthHidden
      name = "test a 1-hidden-layer MNIST nn "
             ++ unwords [show chunkLength, show widthHidden, show nParams]
  bench name $ whnf score chunk

mnistTrainBGroup :: [MnistData] -> Int -> Benchmark
mnistTrainBGroup xs chunkLength =
  bgroup (show chunkLength)
    [ mnistTestBench chunkLength xs 25
    , mnistTrainBench chunkLength xs 25 0.02  -- toy width
    , mnistTestBench chunkLength xs 250
    , mnistTrainBench chunkLength xs 250 0.02  -- ordinary width
    , mnistTestBench chunkLength xs 2500
    , mnistTrainBench chunkLength xs 2500 0.02  -- probably mostly wasted
    ]
