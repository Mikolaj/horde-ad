module Main (main) where

import Prelude

import Criterion.Main
import System.Random

import MnistData

import BenchMnistTools

main :: IO ()
main = do
  testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
  let testData = shuffle (mkStdGen 42) testData0
  defaultMain
    [ mnistTrainBGroup2 testData 400
--    , mnistTrainBGroup2 testData 5000  -- ordinary chunk size, takes too long
    , mnistTrainBGroup2000 testData 40
    , mnistTrainBGroup2V testData 400
    , mnistTrainBGroup2VA testData 400
    , mnistTrainBGroup2L testData 400
    ]
