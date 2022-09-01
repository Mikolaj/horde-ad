{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module BenchMnistTools where

import Prelude

import           Control.Arrow ((***))
import           Control.DeepSeq (NFData)
import           Criterion.Main
import           Data.List.Index (imap)
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM
import           System.Random

-- import           System.IO (hPutStrLn, stderr)

import HordeAd
import HordeAd.Core.DualClass (unsafeGetFreshId)
import HordeAd.Tool.MnistData
import HordeAd.Tool.MnistFcnnMatrix
import HordeAd.Tool.MnistFcnnScalar
import HordeAd.Tool.MnistFcnnVector

mnistTrainBench2 :: forall r. (NFData r, UniformRange r, HasDelta r)
                 => String -> Int -> [MnistData r] -> Int -> Int
                 -> r
                 -> Benchmark
mnistTrainBench2 extraPrefix chunkLength xs widthHidden widthHidden2 gamma = do
  let nParams0 = fcnnMnistLen0 widthHidden widthHidden2
      params0Init = V.unfoldrExactN nParams0 (uniformR (-0.5, 0.5))
                    $ mkStdGen 33
      f = fcnnMnistLoss0 widthHidden widthHidden2
      chunk = take chunkLength xs
      grad c = fst <$> sgd gamma f c (params0Init, V.empty, V.empty, V.empty)
      name = "" ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v0"
                        , "m0" ++ "=" ++ show nParams0 ]
  bench name $ nfIO $ do
    grad chunk
    counter <- unsafeGetFreshId
    if counter > 2 ^ (62 :: Int)
    then error $ "Counter is dangerously high: " ++ show counter
    else return ()  -- hPutStrLn stderr $ "Counter value: " ++ show counter
{-# SPECIALIZE mnistTrainBench2 :: String -> Int -> [MnistData Double] -> Int -> Int -> Double -> Benchmark #-}

mnistTestBench2
  :: forall r. (UniformRange r, IsScalar 'DModeValue r)
  => String -> Int -> [MnistData r] -> Int -> Int -> Benchmark
mnistTestBench2 extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let nParams0 = fcnnMnistLen0 widthHidden widthHidden2
      params0Init = V.unfoldrExactN nParams0 (uniformR (-0.5, 0.5))
                    $ mkStdGen 33
      chunk = take chunkLength xs
      score c = fcnnMnistTest0 widthHidden widthHidden2 c params0Init
      name = "test " ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v0"
                        , "m0" ++ "=" ++ show nParams0 ]
  bench name $ whnf score chunk
{-# SPECIALIZE mnistTestBench2 :: String -> Int -> [MnistData Double] -> Int -> Int -> Benchmark #-}

mnistTrainBGroup2 :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2 xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer MNIST nn with samples: " ++ show chunkLength) $
    (if chunkLength <= 1000
     then
       [ mnistTestBench2 "30|10 " chunkLength xs 30 10  -- toy width
       , mnistTrainBench2 "30|10 " chunkLength xs 30 10 0.02
       , mnistTestBench2 "300|100 " chunkLength xs 300 100  -- ordinary width
       , mnistTrainBench2 "300|100 " chunkLength xs 300 100 0.02
       ]
     else
       [])
    ++ [ mnistTestBench2 "500|150 " chunkLength xs 500 150
                                                     -- another common size
       , mnistTrainBench2 "500|150 " chunkLength xs 500 150 0.02
       ]

mnistTrainBGroup2000 :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2000 xs0 chunkLength =
  env (return (xs0, map (V.map realToFrac *** V.map realToFrac)
                    $ take chunkLength xs0)) $
  \ ~(xs, xsFloat) ->
  bgroup ("huge 2-hidden-layer MNIST nn with samples: " ++ show chunkLength)
    [ mnistTestBench2 "2000|600 " chunkLength xs 2000 600
        -- probably mostly wasted
    , mnistTrainBench2 "2000|600 " chunkLength xs 2000 600 0.02
    , mnistTestBench2 "(Float) 2000|600 " chunkLength xsFloat 2000 600
        -- Float test
    , mnistTrainBench2 "(Float) 2000|600 " chunkLength xsFloat 2000 600
                       (0.02 :: Float)
    ]

mnistTrainBench2V :: String -> Int -> [MnistData Double]
                  -> Int -> Int -> Double
                  -> Benchmark
mnistTrainBench2V extraPrefix chunkLength xs widthHidden widthHidden2 gamma = do
  let (nParams0, nParams1, _, _) = fcnnMnistLen1 widthHidden widthHidden2
      params0Init = HM.randomVector 33 HM.Uniform nParams0 - HM.scalar 0.5
      params1Init = V.fromList $
        imap (\i nPV -> HM.randomVector (33 + nPV + i) HM.Uniform nPV
                        - HM.scalar 0.5)
             nParams1
      f = fcnnMnistLoss1 widthHidden widthHidden2
      chunk = take chunkLength xs
      grad c =
        fst <$> sgd gamma f c (params0Init, params1Init, V.empty, V.empty)
      totalParams = nParams0 + sum nParams1
      name = "" ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v" ++ show (length nParams1)
                        , "m0" ++ "=" ++ show totalParams ]
  bench name $ nfIO $ grad chunk

mnistTestBench2V :: String -> Int -> [MnistData Double] -> Int -> Int
                 -> Benchmark
mnistTestBench2V extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let (nParams0, nParams1, _, _) = fcnnMnistLen1 widthHidden widthHidden2
      params0Init = HM.randomVector 33 HM.Uniform nParams0 - HM.scalar 0.5
      params1Init = V.fromList $
        imap (\i nPV -> HM.randomVector (33 + nPV + i) HM.Uniform nPV
                        - HM.scalar 0.5)
             nParams1
      chunk = take chunkLength xs
      score c = fcnnMnistTest1 widthHidden widthHidden2 c
                           (params0Init, params1Init)
      totalParams = nParams0 + sum nParams1
      name = "test " ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v" ++ show (length nParams1)
                        , "m0" ++ "=" ++ show totalParams ]
  bench name $ whnf score chunk

mnistTrainBGroup2V :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2V xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer V MNIST nn with samples: " ++ show chunkLength) $
    (if chunkLength <= 1000
     then
       [ mnistTestBench2V "30|10 " chunkLength xs 30 10  -- toy width
       , mnistTrainBench2V "30|10 " chunkLength xs 30 10 0.02
       , mnistTestBench2V "300|100 " chunkLength xs 300 100  -- ordinary width
       , mnistTrainBench2V "300|100 " chunkLength xs 300 100 0.02
       ]
     else
       [])
    ++ [ mnistTestBench2V "500|150 " chunkLength xs 500 150
                                                    -- another common size
       , mnistTrainBench2V "500|150 " chunkLength xs 500 150 0.02
       ]

mnistTrainBench2L :: String -> Int -> [MnistData Double] -> Int -> Int
                  -> Double
                  -> Benchmark
mnistTrainBench2L extraPrefix chunkLength xs widthHidden widthHidden2 gamma = do
  let ((nParams0, nParams1, nParams2, _), totalParams, _reach, parameters0) =
        initializerFixed 33 0.5 (fcnnMnistLen2 widthHidden widthHidden2)
      -- Using the fused version to benchmark against the manual gradient
      -- from backprop that uses it at least in its forward pass,
      -- not againts the derived gradients that are definitively slower.
      f = fcnnMnistLossFused2
      chunk = take chunkLength xs
      grad c = fst <$> sgd gamma f c parameters0
      name = "" ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v" ++ show nParams1
                        , "m" ++ show nParams2
                          ++ "=" ++ show totalParams ]
  bench name $ nfIO $ grad chunk

mnistTestBench2L :: String -> Int -> [MnistData Double] -> Int -> Int
                 -> Benchmark
mnistTestBench2L extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let ((nParams0, nParams1, nParams2, _), totalParams, _reach, parameters0) =
        initializerFixed 33 0.5 (fcnnMnistLen2 widthHidden widthHidden2)
      chunk = take chunkLength xs
      score c = fcnnMnistTest2 c parameters0
      name = "test " ++ extraPrefix
             ++ unwords [ "s" ++ show nParams0, "v" ++ show nParams1
                        , "m" ++ show nParams2
                          ++ "=" ++ show totalParams ]
  bench name $ whnf score chunk

mnistTrainBGroup2L :: [MnistData Double] -> Int -> Benchmark
mnistTrainBGroup2L xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer L MNIST nn with samples: " ++ show chunkLength) $
    (if chunkLength <= 1000
     then
       [ mnistTestBench2L "30|10 " chunkLength xs 30 10  -- toy width
       , mnistTrainBench2L "30|10 " chunkLength xs 30 10 0.02
       , mnistTestBench2L "300|100 " chunkLength xs 300 100  -- ordinary width
       , mnistTrainBench2L "300|100 " chunkLength xs 300 100 0.02
       ]
    else
       [])
    ++ [ mnistTestBench2L "500|150 " chunkLength xs 500 150
                                                    -- another common size
       , mnistTrainBench2L "500|150 " chunkLength xs 500 150 0.02
       ]
