module Main (main) where

import Prelude

import Criterion.Main

import MnistMostlyHarmlessTools
import MnistTools

main :: IO ()
main = do
  testData <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
  defaultMain
    [ mnistTrainBGroup testData 500
--    , mnistTrainBGroup testData 5000  -- ordinary chunk size, takes too long
      , mnistTrainBGroup2 testData 500
--    , mnistTrainBGroup2 testData 5000  -- ordinary chunk size, takes too long
    ]
