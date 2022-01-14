module Main (main) where

import Prelude

import           Control.DeepSeq
import           Criterion.Main
import qualified Data.Vector.Generic as V
import           System.Random

import qualified MnistAdTools
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
        [ env (return testData) $
          \ ~xs ->
          bgroup "ours"
            [ MnistMostlyHarmlessTools.mnistTrainBench2 500 xs 30 10 0.02
            , MnistMostlyHarmlessTools.mnistTestBench2 500 xs 30 10
            ]
        , env (return $ map (\(x, y) -> (V.convert x, V.convert y)) testData) $
          \ ~xs ->
          bgroup "ad"
            [ MnistAdTools.mnistTrainBench2 500 xs 30 10 0.02
            , MnistAdTools.mnistTestBench2 500 xs 30 10
            ]
        , MnistBackpropTools.backpropBgroupUnboxed3010 testData 500
        ]
    , bgroup "300 100"
        [ env (return testData) $
          \ ~xs ->
          bgroup "ours"
            [ MnistMostlyHarmlessTools.mnistTrainBench2 500 xs 300 100 0.02
            , MnistMostlyHarmlessTools.mnistTestBench2 500 xs 300 100
            ]
        , env (return $ map (\(x, y) -> (V.convert x, V.convert y)) testData) $
          \ ~xs ->
          bgroup "ad"
            [ MnistAdTools.mnistTrainBench2 500 xs 300 100 0.02
            , MnistAdTools.mnistTestBench2 500 xs 300 100
            ]
        , MnistBackpropTools.backpropBgroupUnboxed testData 500
        ]
    , bgroup "500 150"
        [ env (return testData) $
          \ ~xs ->
          bgroup "ours"
            [ MnistMostlyHarmlessTools.mnistTrainBench2 500 xs 500 150  0.02
            , MnistMostlyHarmlessTools.mnistTestBench2 500 xs 500 150
            ]
-- too slow
--        , env (return $ map (\(x, y) -> (V.convert x, V.convert y)) testData) $
--          \ ~xs ->
--          bgroup "ad"
--            [ MnistAdTools.mnistTrainBench2 500 testData 500 150
--                                            0.02
--            , MnistAdTools.mnistTestBench2 500 testData 500 150
--            ]
        , MnistBackpropTools.backpropBgroupUnboxed500150 testData 500
        ]
    ]
