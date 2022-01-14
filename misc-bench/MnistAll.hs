module Main (main) where

import Prelude

import Control.DeepSeq
import Criterion.Main
import System.Random

import qualified MnistBackpropTools
import qualified MnistMostlyHarmlessTools
import           MnistTools

main :: IO ()
main = do
  testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
  let testData1 = shuffle (mkStdGen 42) testData0
      !testData = deepseq testData1 testData1
  defaultMain
    [ bgroup "50"
        [ bgroup "ours"
            [ MnistMostlyHarmlessTools.mnistTestBench2 50 testData 300 100
            , MnistMostlyHarmlessTools.mnistTrainBench2 50 testData 300 100
                                                        0.02
            ]
        , MnistBackpropTools.backpropBgroupUnboxed testData 50
        ]
    , bgroup "500"
        [ bgroup "ours"
            [ MnistMostlyHarmlessTools.mnistTestBench2 500 testData 300 100
            , MnistMostlyHarmlessTools.mnistTrainBench2 500 testData 300 100
                                                        0.02
            ]
        , MnistBackpropTools.backpropBgroupUnboxed testData 500
        ]
    ]
