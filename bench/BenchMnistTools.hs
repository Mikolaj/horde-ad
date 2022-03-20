{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module BenchMnistTools where

import Prelude

import           Control.Arrow ((***))
import           Control.DeepSeq (NFData)
import           Criterion.Main
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM
import           System.Random

import HordeAd
import HordeAd.Tool.MnistTools

mnistTrainBench2 :: forall r. ( NFData (Primal r), HasDelta r
                              , Floating (Primal r), UniformRange (Primal r) )
                 => String -> Int -> [MnistData (Primal r)] -> Int -> Int
                 -> Primal r
                 -> Benchmark
mnistTrainBench2 extraPrefix chunkLength xs widthHidden widthHidden2 gamma = do
  let nParams0 = lenMnist0 widthHidden widthHidden2
      params0Init = V.unfoldrExactN nParams0 (uniformR (-0.5, 0.5))
                    $ mkStdGen 33
      f = nnMnistLoss0 widthHidden widthHidden2
      chunk = take chunkLength xs
      grad c = fst $ sgd gamma f c (params0Init, V.empty, V.empty, V.empty)
      name = "" ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v0"
                        , "m0" ++ "=" ++ show nParams0 ]
  bench name $ nf grad chunk

mnistTestBench2
  :: forall r. (Floating (Primal r), UniformRange (Primal r), HasDelta r)
  => Proxy r -> String -> Int -> [MnistData (Primal r)] -> Int -> Int -> Benchmark
mnistTestBench2 proxy extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let nParams0 = lenMnist0 widthHidden widthHidden2
      params0Init = V.unfoldrExactN nParams0 (uniformR (-0.5, 0.5))
                    $ mkStdGen 33
      chunk = take chunkLength xs
      score c = testMnist0 proxy widthHidden widthHidden2 c params0Init
      name = "test " ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v0"
                        , "m0" ++ "=" ++ show nParams0 ]
  bench name $ whnf score chunk
{-# SPECIALIZE mnistTestBench2 :: Proxy (Delta0 Double) -> String -> Int -> [MnistData Double] -> Int -> Int -> Benchmark #-}

mnistTrainBGroup2 :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2 xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2 (Proxy :: Proxy (Delta0 Double)) "30|10 " chunkLength xs 30 10  -- toy width
    , mnistTrainBench2 "30|10 " chunkLength xs 30 10 0.02
    , mnistTestBench2 (Proxy :: Proxy (Delta0 Double)) "300|100 " chunkLength xs 300 100  -- ordinary width
    , mnistTrainBench2 "300|100 " chunkLength xs 300 100 0.02
    , mnistTestBench2 (Proxy :: Proxy (Delta0 Double)) "500|150 " chunkLength xs 500 150  -- another common size
    , mnistTrainBench2 "500|150 " chunkLength xs 500 150 0.02
    ]

mnistTrainBGroup2500 :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2500 xs0 chunkLength =
  env (return (xs0, map (V.map realToFrac *** V.map realToFrac)
                    $ take chunkLength xs0)) $
  \ ~(xs, xsFloat) ->
  bgroup ("huge 2-hidden-layer MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2 (Proxy :: Proxy (Delta0 Double)) "2500|750 " chunkLength xs 2500 750
        -- probably mostly wasted
    , mnistTrainBench2 "2500|750 " chunkLength xs 2500 750 0.02
    , mnistTestBench2 (Proxy :: Proxy (Delta0 Float)) "(Float) 2500|750 " chunkLength xsFloat 2500 750
        -- Float test
    , mnistTrainBench2 "(Float) 2500|750 " chunkLength xsFloat 2500 750
                       (0.02 :: Float)
    ]

mnistTrainBench2V :: String -> Int -> [MnistData Double]
                  -> Int -> Int -> Double
                  -> Benchmark
mnistTrainBench2V extraPrefix chunkLength xs widthHidden widthHidden2 gamma = do
  let nParams0 = lenMnist1 widthHidden widthHidden2
      nParams1 = lenVectorsMnist1 widthHidden widthHidden2
      params0Init = HM.randomVector 33 HM.Uniform nParams0 - HM.scalar 0.5
      params1Init =
        V.imap (\i nPV -> HM.randomVector (33 + nPV + i) HM.Uniform nPV
                          - HM.scalar 0.5)
               nParams1
      f = nnMnistLoss1 widthHidden widthHidden2
      chunk = take chunkLength xs
      grad c = fst $ sgd gamma f c (params0Init, params1Init, V.empty, V.empty)
      totalParams = nParams0 + V.sum nParams1
      name = "" ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v" ++ show (V.length nParams1)
                        , "m0" ++ "=" ++ show totalParams ]
  bench name $ nf grad chunk

mnistTestBench2V :: String -> Int -> [MnistData Double] -> Int -> Int
                 -> Benchmark
mnistTestBench2V extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let nParams0 = lenMnist1 widthHidden widthHidden2
      nParams1 = lenVectorsMnist1 widthHidden widthHidden2
      params0Init = HM.randomVector 33 HM.Uniform nParams0 - HM.scalar 0.5
      params1Init =
        V.imap (\i nPV -> HM.randomVector (33 + nPV + i) HM.Uniform nPV
                          - HM.scalar 0.5)
               nParams1
      chunk = take chunkLength xs
      score c = testMnist1 @(Delta0 Double) widthHidden widthHidden2 c
                           (params0Init, params1Init)
      totalParams = nParams0 + V.sum nParams1
      name = "test " ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v" ++ show (V.length nParams1)
                        , "m0" ++ "=" ++ show totalParams ]
  bench name $ whnf score chunk

mnistTrainBGroup2V :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2V xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer V MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2V "30|10 " chunkLength xs 30 10  -- toy width
    , mnistTrainBench2V "30|10 " chunkLength xs 30 10 0.02
    , mnistTestBench2V "300|100 " chunkLength xs 300 100  -- ordinary width
    , mnistTrainBench2V "300|100 " chunkLength xs 300 100 0.02
    , mnistTestBench2V "500|150 " chunkLength xs 500 150  -- another common size
    , mnistTrainBench2V "500|150 " chunkLength xs 500 150 0.02
    ]

mnistTrainBench2L :: String -> Int -> [MnistData Double] -> Int -> Int
                  -> Double
                  -> Benchmark
mnistTrainBench2L extraPrefix chunkLength xs widthHidden widthHidden2 gamma = do
  let ((nParams0, nParams1, nParams2), totalParams, _reach, parameters0) =
        initializerFixed 33 0.5 (lenMnistFcnn2 widthHidden widthHidden2)
      -- Using the fused version to benchmark against the manual gradient
      -- from backprop that uses it at least in its forward pass,
      -- not againts the derived gradients that are definitively slower.
      f = nnMnistLossFused2
      chunk = take chunkLength xs
      grad c = fst $ sgd gamma f c parameters0
      name = "" ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v" ++ show nParams1
                        , "m" ++ show nParams2
                          ++ "=" ++ show totalParams ]
  bench name $ nf grad chunk

mnistTestBench2L :: String -> Int -> [MnistData Double] -> Int -> Int
                 -> Benchmark
mnistTestBench2L extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let ((nParams0, nParams1, nParams2), totalParams, _reach, parameters0) =
        initializerFixed 33 0.5 (lenMnistFcnn2 widthHidden widthHidden2)
      chunk = take chunkLength xs
      score c = testMnist2 @(Delta0 Double) c parameters0
      name = "test " ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v" ++ show nParams1
                        , "m" ++ show nParams2
                          ++ "=" ++ show totalParams ]
  bench name $ whnf score chunk

mnistTrainBGroup2L :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2L xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer L MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2L "30|10 " chunkLength xs 30 10  -- toy width
    , mnistTrainBench2L "30|10 " chunkLength xs 30 10 0.02
    , mnistTestBench2L "300|100 " chunkLength xs 300 100  -- ordinary width
    , mnistTrainBench2L "300|100 " chunkLength xs 300 100 0.02
    , mnistTestBench2L "500|150 " chunkLength xs 500 150  -- another common size
    , mnistTrainBench2L "500|150 " chunkLength xs 500 150 0.02
    ]
