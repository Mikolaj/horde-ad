{-# LANGUAGE FlexibleContexts #-}
module TestConditionalSynth (testTrees) where

import Prelude

import           Data.List (nub, sort, unfoldr)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Foreign.Storable.Tuple ()
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.MnistTools

testTrees :: [TestTree]
testTrees = [ conditionalSynthTests
            ]

-- Pair samples sorted and made unique wrt first element of the pair.
integerPairSamples :: (Int, Int) -> Int -> Int
                   -> Data.Vector.Storable.Vector (Double, Double)
integerPairSamples range seed k =
  let rolls :: RandomGen g => g -> [Int]
      rolls = unfoldr (Just . uniformR range)
      (g1, g2) = split $ mkStdGen seed
      nubInputs :: [Int] -> [Int] -> [Int]
      nubInputs candidates rest =
        let len = length candidates
        in if len == k
           then candidates
           else let (candidatesExtra, restExtra) = splitAt (k - len) rest
                    candidatesUniq = nub $ sort $ candidates ++ candidatesExtra
                in nubInputs candidatesUniq restExtra
      inputs = nubInputs [] (rolls g1)
  in V.zip (V.fromListN k $ map fromIntegral inputs)
           (V.fromListN k $ map fromIntegral $ rolls g2)

gdSmartShow :: (VecDualDelta Double
                -> DeltaMonadGradient Double (DualDelta Double))
            -> Domain Double
            -> Int
            -> ([Double], (Double, Double))
gdSmartShow f initVec n =
  let ((res, _), gamma) = gdSmart f n (initVec, V.empty)
      (_, value) = df f (res, V.empty)
  in (V.toList res, (value, gamma))

gradSmartTestCase
  :: String
  -> ((DualDelta Double -> DeltaMonadGradient Double (DualDelta Double))
      -> (DualDelta Double -> DeltaMonadGradient Double (DualDelta Double))
      -> (DualDelta Double -> DeltaMonadGradient Double (DualDelta Double))
      -> Data.Vector.Storable.Vector (Double, Double)
      -> Int
      -> VecDualDelta Double
      -> DeltaMonadGradient Double (DualDelta Double))
  -> Int -> Int -> Int -> Int -> (Double, Double)
  -> TestTree
gradSmartTestCase prefix lossFunction seedSamples
                  nSamples width nIterations expected =
  let samples = integerPairSamples (-1000, 1000) seedSamples nSamples
      nParams = lenSynth width nSamples
      vec = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      name = prefix ++ " "
             ++ unwords [ show seedSamples, show nSamples, show width
                        , show nParams, show nIterations ]
  in testCase name $
       snd (gdSmartShow
              (lossFunction reluAct tanhAct tanhAct samples width)
              vec nIterations)
       @?= expected

a :: Int
a = 1

lenSynth :: Int -> Int -> Int
lenSynth width nSamples = width * (nSamples * 2 + 1)
                          + a * nSamples * 4 * (width + 1)

-- To reproduce the samples, divide argument and multiply result;
-- see @synthLossSquared@.
synthValue :: forall m. DeltaMonad Double m
           => (DualDelta Double -> m (DualDelta Double))
           -> Double
           -> Data.Vector.Vector (DualDelta Double)
           -> m (DualDelta Double)
synthValue factivation x ys = go 0 (V.length ys `div` 4 - 1)
 where
  go :: DualDelta Double -> Int -> m (DualDelta Double)
  go !acc (-1) = return acc
  go acc i = do
    let weight = ys V.! (4 * i)
        bias = ys V.! (4 * i + 1)
    activated <- factivation $ scale x weight + bias
    let weightAfter = ys V.! (4 * i + 2)
        biasAfter = ys V.! (4 * i + 3)
    go (acc + activated * weightAfter + biasAfter) (pred i)

synthLossSquared :: DeltaMonad Double m
                 => (DualDelta Double -> m (DualDelta Double))
                 -> Double
                 -> Data.Vector.Vector (DualDelta Double)
                 -> Double
                 -> m (DualDelta Double)
synthLossSquared factivation x ys targ = do
  res <- synthValue factivation (x / 1000) ys
  lossSquared (targ / 10000) res  -- smaller target to overcome @tanh@ clamping

synthLossAll
  :: forall m. DeltaMonad Double m
  => (DualDelta Double -> m (DualDelta Double))
  -> Data.Vector.Storable.Vector (Double, Double)
  -> Data.Vector.Vector (DualDelta Double)
  -> m (DualDelta Double)
synthLossAll factivation samples ys = do
  let f :: (Double, Double) -> m (DualDelta Double)
      f (x, res) = synthLossSquared factivation x ys res
  sumResultsDual f samples

synthLossBareTotal
  :: DeltaMonad Double m
  => (DualDelta Double -> m (DualDelta Double))
  -> (DualDelta Double -> m (DualDelta Double))
  -> (DualDelta Double -> m (DualDelta Double))
  -> Data.Vector.Storable.Vector (Double, Double)
  -> Int
  -> VecDualDelta Double
  -> m (DualDelta Double)
synthLossBareTotal factivation factivationHidden factivationMiddle
                   samples width vec = do
  let (inputs, outputs) = V.unzip samples
      nSamples = V.length samples
      sampleData = V.convert inputs <> V.convert outputs
  hiddenVec <- hiddenLayerMnist factivationHidden sampleData vec width
  ys <- middleLayerMnist factivationMiddle hiddenVec
                         (width * (nSamples * 2 + 1)) vec (a * nSamples * 4)
  synthLossAll factivation samples ys

conditionalSynthTests:: TestTree
conditionalSynthTests =
 testGroup "reluAct: synthesizing a sum of linear conditionals matching samples"
  [ gradSmartTestCase "reluAct"
      synthLossBareTotal 42 1 10 100000
      (6.291648505851797e-3,6.25e-3)
  , gradSmartTestCase "reluAct"
      synthLossBareTotal 42 2 10 100000
      (6.291648505851797e-3,6.25e-3)
  , gradSmartTestCase "reluAct"
      synthLossBareTotal 42 3 10 100000
      (6.291648505851797e-3,6.25e-3)
  , gradSmartTestCase "reluAct"
      synthLossBareTotal 42 4 20 100000
      (6.291648505851797e-3,6.25e-3)
  , gradSmartTestCase "reluAct"
      synthLossBareTotal 42 8 40 100000
      (4.34890234424764e-7,6.25e-3)
  , gradSmartTestCase "reluAct"
      synthLossBareTotal 42 16 80 100000
      (0.3434691592146121,1.5625e-3)
  , gradSmartTestCase "reluAct"
      synthLossBareTotal 42 24 120 100000
      (1.665065359469462,9.765625e-5)
  ]
