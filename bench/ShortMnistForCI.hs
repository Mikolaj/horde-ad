module Main (main) where

import Prelude

import Criterion.Main
import System.Random

import HordeAd.Tool.MnistTools

import BenchMnistTools

main :: IO ()
main = do
  testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
  let testData = shuffle (mkStdGen 42) testData0
  defaultMain
    [ mnistTrainBGroup2 testData 50
    , mnistTrainBGroup2500 testData 5
    , mnistTrainBGroup2V testData 50
    , mnistTrainBGroup2L testData 50
    ]
