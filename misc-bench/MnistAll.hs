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
    [ bgroup "30 10"
        [ bgroup "ours"
            [ MnistMostlyHarmlessTools.mnistTrainBench2 500 testData 30 10
                                                        0.02
            , MnistMostlyHarmlessTools.mnistTestBench2 500 testData 30 10
            ]
        , MnistBackpropTools.backpropBgroupUnboxed3010 testData 500
        ]
    , bgroup "300 100"
        [ bgroup "ours"
            [ MnistMostlyHarmlessTools.mnistTrainBench2 500 testData 300 100
                                                        0.02
            , MnistMostlyHarmlessTools.mnistTestBench2 500 testData 300 100
            ]
        , MnistBackpropTools.backpropBgroupUnboxed testData 500
        ]
    , bgroup "500 150"
        [ bgroup "ours"
            [ MnistMostlyHarmlessTools.mnistTrainBench2 500 testData 500 150
                                                        0.02
            , MnistMostlyHarmlessTools.mnistTestBench2 500 testData 500 150
            ]
        , MnistBackpropTools.backpropBgroupUnboxed500150 testData 500
        ]
    ]
