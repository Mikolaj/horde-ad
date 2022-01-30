{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module BenchMnistTools where

import Prelude

import           Control.Arrow ((***))
import           Criterion.Main
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Numeric.LinearAlgebra (Numeric)
import           System.Random

import HordeAd
import HordeAd.MnistTools

mnistTrainBench2 :: ( Eq r, Floating r, UniformRange r
                    , Numeric r, Num (Data.Vector.Storable.Vector r) )
                 => String -> Int -> [MnistData r] -> Int -> Int -> r
                 -> Benchmark
mnistTrainBench2 extraPrefix chunkLength xs widthHidden widthHidden2 gamma = do
  let nParams = lenMnist2 widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      f = nnMnistLoss2 widthHidden widthHidden2
      chunk = take chunkLength xs
      grad c = sgd gamma f c (params0, V.empty)
      name = "train2 " ++ extraPrefix
             ++ unwords [show widthHidden, show widthHidden2, show nParams]
  bench name $ whnf grad chunk

mnistTestBench2 :: (Ord r, Floating r, UniformRange r, Numeric r)
                => String -> Int -> [MnistData r] -> Int -> Int -> Benchmark
mnistTestBench2 extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let nParams = lenMnist2 widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      chunk = take chunkLength xs
      score c = testMnist2 widthHidden widthHidden2 c params0
      name = "test2 " ++ extraPrefix
             ++ unwords [show widthHidden, show widthHidden2, show nParams ]
  bench name $ whnf score chunk

mnistTrainBGroup2 :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2 xs0 chunkLength =
  env (return (xs0, map (V.map realToFrac *** V.map realToFrac)
                    $ take chunkLength xs0)) $
  \ ~(xs, xsFloat) ->
  bgroup ("2-hidden-layer MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2 "" chunkLength xs 30 10  -- toy width
    , mnistTrainBench2 "" chunkLength xs 30 10 0.02
    , mnistTestBench2 "" chunkLength xs 300 100  -- ordinary width
    , mnistTrainBench2 "" chunkLength xs 300 100 0.02
    , mnistTestBench2 "" chunkLength xs 500 150  -- another common size
    , mnistTrainBench2 "" chunkLength xs 500 150 0.02
    , mnistTestBench2 "(Float) " chunkLength xsFloat 500 150  -- Float test
    , mnistTrainBench2 "(Float) " chunkLength xsFloat 500 150 (0.02 :: Float)
    ]

mnistTrainBGroup2500 :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2500 xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("huge 2-hidden-layer MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2 "" chunkLength xs 2500 750  -- probably mostly wasted
    , mnistTrainBench2 "" chunkLength xs 2500 750 0.02
    ]

mnistTrainBench2V :: ( Eq r, Floating r, Numeric r, UniformRange r
                     , Floating (Data.Vector.Storable.Vector r) )
                  => String -> Int -> [MnistData r] -> Int -> Int -> r
                  -> Benchmark
mnistTrainBench2V extraPrefix chunkLength xs widthHidden widthHidden2 gamma = do
  let nParams = lenMnist2V widthHidden widthHidden2
      nParamsV = lenVectorsMnist2V widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      paramsV0 =
        V.imap (\i nPV -> V.unfoldrExactN nPV (uniformR (-0.5, 0.5))
                                          (mkStdGen $ 33 + nPV + i))
               nParamsV
      f = nnMnistLoss2V widthHidden widthHidden2
      chunk = take chunkLength xs
      grad c = sgd gamma f c (params0, paramsV0)
      name = "train2 " ++ extraPrefix
             ++ unwords [show widthHidden, show widthHidden2, show nParams]
  bench name $ whnf grad chunk

mnistTestBench2V :: ( Ord r, Floating r, Numeric r, UniformRange r
                    , Floating (Data.Vector.Storable.Vector r) )
                 => String -> Int -> [MnistData r] -> Int -> Int -> Benchmark
mnistTestBench2V extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let nParams = lenMnist2V widthHidden widthHidden2
      nParamsV = lenVectorsMnist2V widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      paramsV0 =
        V.imap (\i nPV -> V.unfoldrExactN nPV (uniformR (-0.5, 0.5))
                                          (mkStdGen $ 33 + nPV + i))
               nParamsV
      chunk = take chunkLength xs
      score c = testMnist2V widthHidden widthHidden2 c (params0, paramsV0)
      name = "test2 " ++ extraPrefix
             ++ unwords [show widthHidden, show widthHidden2, show nParams ]
  bench name $ whnf score chunk

mnistTrainBGroup2V :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2V xs0 chunkLength =
  env (return (xs0, map (V.map realToFrac *** V.map realToFrac)
                    $ take chunkLength xs0)) $
  \ ~(xs, xsFloat) ->
  bgroup ("2-hidden-layer V MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2V "" chunkLength xs 30 10  -- toy width
    , mnistTrainBench2V "" chunkLength xs 30 10 0.02
    , mnistTestBench2V "" chunkLength xs 300 100  -- ordinary width
    , mnistTrainBench2V "" chunkLength xs 300 100 0.02
    , mnistTestBench2V "" chunkLength xs 500 150  -- another common size
    , mnistTrainBench2V "" chunkLength xs 500 150 0.02
    , mnistTestBench2V "(Float) " chunkLength xsFloat 500 150  -- Float test
    , mnistTrainBench2V "(Float) " chunkLength xsFloat 500 150 (0.02 :: Float)
    ]
