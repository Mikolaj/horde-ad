-- | TODO: outdated, uses the old API, but has some features we may want to copy, such as 'writeFile "walltimeLoss.txt"', decay, unitVarianceRange and maybe "Gradients without Backpropagation"
module TestMnistFCNN
  ( testTrees, shortTestForCITrees, mnistTestCase2T, mnistTestCase2D
  ) where

import Prelude

import Control.Arrow ((&&&))
import Control.DeepSeq
import Control.Monad (foldM, when)
import Data.Array.DynamicS qualified as OD
import Data.Coerce (coerce)
import Data.List (foldl')
import Data.List.Index (imap)
import Data.Time.Clock.POSIX (POSIXTime, getPOSIXTime)
import Data.Vector.Generic qualified as V
import Numeric.LinearAlgebra qualified as LA
import System.IO (hFlush, hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.QuickCheck hiding (label, shuffle)
import Text.Printf
import Unsafe.Coerce (unsafeCoerce)

import HordeAd
import HordeAd.External.OptimizerTools
import MnistData
import MnistFcnnMatrix
import MnistFcnnShaped
import MnistFcnnVector
import OldMnistFcnnShaped

import EqEpsilon
import Prop

mnistTestCase2T
  :: Bool
  -> String
  -> Int
  -> Int
  -> (MnistData Double
      -> ADInputs 'ADModeGradient Double
      -> ADVal 'ADModeGradient Double)
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2T reallyWriteFile
                prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let ((nParams0, nParams1, nParams2, _), totalParams, range, !parameters0) =
        initializerFixed 44 0.5 (fcnnMnistLen2 widthHidden widthHidden2)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show gamma, show range]
  in testCase name $ do
       hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
              prefix epochs maxBatches
       trainData0 <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       let !trainData = force $ shuffle (mkStdGen 6) trainData0
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (HVector Double, [(POSIXTime, Double)])
                    -> (Int, [MnistData Double])
                    -> IO (HVector Double, [(POSIXTime, Double)])
           runBatch (!domains, !times)
                    (k, chunk) = do
             when (k `mod` 100 == 0) $ do
               hPutStrLn stderr $ printf "%s: %d " prefix k
               hFlush stderr
             let f = trainWithLoss
                 (!params0New, !v) = sgd gamma f chunk domains
             time <- getPOSIXTime
             return (params0New, (time, v) : times)
       let runEpoch :: Int
                    -> (HVector Double, [(POSIXTime, Double)])
                    -> IO (HVector Double, [(POSIXTime, Double)])
           runEpoch n params2times | n > epochs = return params2times
           runEpoch n (!params2, !times2) = do
             hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let !trainDataShuffled =
                   if n > 1
                   then shuffle (mkStdGen $ n + 5) trainData
                   else trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 1 trainDataShuffled
             res <- foldM runBatch (params2, times2) chunks
             runEpoch (succ n) res
       timeBefore <- getPOSIXTime
       (res, times) <- runEpoch 1 (parameters0, [])
       let ppTime (t, l) = init (show (t - timeBefore)) ++ " " ++ show l
       when reallyWriteFile $
         writeFile "walltimeLoss.txt" $ unlines $ map ppTime times
       let testErrorFinal = 1 - fcnnMnistTest2 testData res
       testErrorFinal @?~ expected


mnistTestCase2D
  :: Bool
  -> Int
  -> Bool
  -> String
  -> Int
  -> Int
  -> (MnistData Double
      -> ADInputs 'ADModeGradient Double
      -> ADVal 'ADModeGradient Double)
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2D reallyWriteFile miniBatchSize decay
                prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma0 expected =
  let np = fcnnMnistLen2 widthHidden widthHidden2
      ((nParams0, nParams1, nParams2, _), totalParams, range, !parameters0) =
        initializerFixed 44 0.5 np
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show gamma0, show range]
  in testCase name $ do
       hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
              prefix epochs maxBatches
       trainData0 <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       let !trainData = force $ shuffle (mkStdGen 6) trainData0
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (HVector Double, [(POSIXTime, Double)])
                    -> (Int, [MnistData Double])
                    -> IO (HVector Double, [(POSIXTime, Double)])
           runBatch (!domains, !times)
                    (k, chunk) = do
             when (k `mod` 100 == 0) $ do
               hPutStrLn stderr $ printf "%s: %d " prefix k
               hFlush stderr
             let f = trainWithLoss
                 gamma = if decay
                         then gamma0 * exp ((- fromIntegral k) * 1e-4)
                         else gamma0
                 (!params0New, !v) =
                   sgdBatchForward (33 + k * 7) miniBatchSize gamma f chunk
                                   domains np
             time <- getPOSIXTime
             return (params0New, (time, v) : times)
       let runEpoch :: Int
                    -> (HVector Double, [(POSIXTime, Double)])
                    -> IO (HVector Double, [(POSIXTime, Double)])
           runEpoch n params2times | n > epochs = return params2times
           runEpoch n (!params2, !times2) = do
             hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let !trainDataShuffled =
                   if n > 1
                   then shuffle (mkStdGen $ n + 5) trainData
                   else trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf miniBatchSize trainDataShuffled
             res <- foldM runBatch (params2, times2) chunks
             runEpoch (succ n) res
       timeBefore <- getPOSIXTime
       (res, times) <- runEpoch 1 (parameters0, [])
       let ppTime (t, l) = init (show (t - timeBefore)) ++ " " ++ show l
       when reallyWriteFile $
         writeFile "walltimeLoss.txt" $ unlines $ map ppTime times
       let testErrorFinal = 1 - fcnnMnistTest2 testData res
       testErrorFinal @?~ expected

-- | Stochastic Gradient Descent with mini-batches, taking the mean
-- of the results from each mini-batch. Additionally, it uses
-- "forward gradient" from "Gradients without Backpropagation"
-- by Atilim Gunes Baydin, Barak A. Pearlmutter, Don Syme, Frank Wood,
-- Philip Torr.
--
-- Note that we can't generalize this to use either
-- @slowFwdGeneral@ or @revGeneral@, because the optimized call
-- to @updateWithGradient@ below would not be possible with the common API
-- for obtaining gradients and at least twice more allocations would
-- be done there. With small mini-batch sizes this matters,
-- especially for optimal forward gradient implementation
-- @fwdOnADInputs@, where there's no overhead from storing
-- and evaluating delta-expressions.
--
-- An option: vectorize and only then take the mean of the vector of results
-- and also parallelize taking advantage of vectorization (but currently
-- we have a global state, so that's tricky).
sgdBatchForward
  :: forall a.
     Int
  -> Int  -- ^ batch size
  -> Double  -- ^ gamma (learning_rate?)
  -> (a -> ADInputs 'ADModeGradient Double -> ADVal 'ADModeGradient Double)
  -> [a]  -- ^ training data
  -> HVector Double  -- ^ initial parameters
  -> (Int, [Int], [(Int, Int)], [OD.ShapeL])
  -> (HVector Double, Double)
sgdBatchForward seed0 batchSize gamma f trainingData parameters0 nParameters =
  go seed0 trainingData parameters0 0
 where
  deltaInputs = generateDeltaInputs parameters0
  go :: Int -> [a] -> HVector Double -> Double -> (HVector Double, Double)
  go _ [] parameters v = (parameters, v)
  go seed l parameters _ =
    let (batch, rest) = splitAt batchSize l
        fAdd :: ADInputs 'ADModeGradient Double
             -> ADVal 'ADModeGradient Double -> a
             -> ADVal 'ADModeGradient Double
        fAdd vars !acc a = acc + f a vars
        fBatch :: ADInputs 'ADModeGradient Double
               -> ADVal 'ADModeGradient Double
        fBatch vars =
          let resBatch = foldl' (fAdd vars) 0 batch
          in resBatch / fromIntegral (length batch)
        unitVarianceRange = sqrt 12 / 2
        (g1, g2) = (seed + 5, seed + 13)
        (_, _, _, direction) = initializerFixed g1 unitVarianceRange nParameters
        inputs = dDnotShared parameters deltaInputs
        (directionalDerivative, valueNew) =
          slowFwdOnADInputs inputs fBatch direction
        gammaDirectional = gamma * directionalDerivative
        parametersNew = updateWithGradient gammaDirectional parameters direction
    in go g2 rest parametersNew valueNew
