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
    [ mnistBGroup1VTA testData 400
    , mnistBGroup1VTO testData 400
    , mnistBGroup2VTA testData 400
    , mnistBGroup2VTO testData 400
    ]
