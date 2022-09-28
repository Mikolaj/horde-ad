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
    [ mnistTrainBGroup2 testData 40
    , mnistTrainBGroup2000 testData 4
    , mnistTrainBGroup2V testData 40
    , mnistTrainBGroup2L testData 40
    ]
