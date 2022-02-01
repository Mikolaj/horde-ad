{-# LANGUAGE FlexibleContexts #-}
module TestConditionalSynth (testTrees) where

import Prelude

import           Data.List (nub, sort, unfoldr)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Foreign.Storable (Storable)
import           Foreign.Storable.Tuple ()
import           Numeric.LinearAlgebra (Vector, konst)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.MnistTools

testTrees :: [TestTree]
testTrees = [ conditionalSynthTests
            ]

-- Inlined to avoid the tiny overhead of calling an unknown function.
-- This operation is needed, because @sumListDual@ doesn't (always) fuse.
sumResultsDual :: forall m a r. (DeltaMonad r m, Num r, Storable a)
               => (a -> m (DualNumber r))
               -> Vector a
               -> m (DualNumber r)
{-# INLINE sumResultsDual #-}
sumResultsDual f as = do
  let g :: DualNumber r -> a -> m (DualNumber r)
      g !acc a = do
        u <- f a
        return $! acc + u
  sumUs <- V.foldM g (scalar 0) as
  returnLet sumUs

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

gdSmartShow :: (VecDualNumber Double
                -> DeltaMonadGradient Double (DualNumber Double))
            -> DomainV Double
            -> Int
            -> ([Data.Vector.Storable.Vector Double], (Double, Double))
gdSmartShow f initVec n =
  let ((_, res, _), gamma) = gdSmart f n (V.empty, initVec, V.empty)
      (_, value) = df f (V.empty, res, V.empty)
  in (V.toList res, (value, gamma))

gradSmartTestCase
  :: String
  -> ((DualNumber (Vector Double)
       -> DeltaMonadGradient Double (DualNumber (Vector Double)))
      -> (DualNumber (Vector Double)
          -> DeltaMonadGradient Double (DualNumber (Vector Double)))
      -> (DualNumber (Vector Double)
          -> DeltaMonadGradient Double (DualNumber (Vector Double)))
      -> Data.Vector.Storable.Vector (Double, Double)
      -> Int
      -> VecDualNumber Double
      -> DeltaMonadGradient Double (DualNumber Double))
  -> Int -> Int -> Int -> Int -> (Double, Double)
  -> TestTree
gradSmartTestCase prefix lossFunction seedSamples
                  nSamples width nIterations expected =
  let samples = integerPairSamples (-1000, 1000) seedSamples nSamples
      nParamsV = lenSynthV width nSamples
      paramsV0 =
        V.imap (\i nPV -> V.unfoldrExactN nPV (uniformR (-0.5, 0.5))
                                          (mkStdGen $ 33 + nPV + i))
               nParamsV
      name = prefix ++ " "
             ++ unwords [ show seedSamples, show nSamples, show width
                        , show (V.length nParamsV), show (V.sum nParamsV)
                        , show nIterations ]
  in testCase name $
       snd (gdSmartShow
              (lossFunction {-reluActV-} tanhActV tanhActV tanhActV samples width)
              paramsV0 nIterations)
       @?= expected

bloat :: Int
bloat = 1

lenSynthV :: Int -> Int -> Data.Vector.Vector Int
lenSynthV width nSamples =
  V.fromList $ replicate width (nSamples * 2) ++ [width]
               ++ replicate (bloat * nSamples * 4) width
               ++ replicate 4 (bloat * nSamples)

-- To reproduce the samples, divide argument and multiply result;
-- see @synthLossSquared@.
synthValue :: forall m. DeltaMonad Double m
           => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
           -> Double
           -> DualNumber (Vector Double)
           -> DualNumber (Vector Double)
           -> DualNumber (Vector Double)
           -> DualNumber (Vector Double)
           -> m (DualNumber Double)
synthValue factivation x ys1@(D u _) ys2 ys3 ys4 = do
  activated <- factivation $ scale (konst x (V.length u)) ys1 + ys2
  returnLet $ sumElements' $ activated * ys3 + ys4

synthLossSquared :: DeltaMonad Double m
                 => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
                 -> Double
                 -> DualNumber (Vector Double)
                 -> DualNumber (Vector Double)
                 -> DualNumber (Vector Double)
                 -> DualNumber (Vector Double)
                 -> Double
                 -> m (DualNumber Double)
synthLossSquared factivation x ys1 ys2 ys3 ys4 targ = do
  res <- synthValue factivation (x / 1000) ys1 ys2 ys3 ys4
  lossSquared (targ / 10000) res  -- smaller target to overcome @tanh@ clamping

synthLossAll
  :: forall m. DeltaMonad Double m
  => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
  -> Data.Vector.Storable.Vector (Double, Double)
  -> DualNumber (Vector Double)
  -> DualNumber (Vector Double)
  -> DualNumber (Vector Double)
  -> DualNumber (Vector Double)
  -> m (DualNumber Double)
synthLossAll factivation samples ys1 ys2 ys3 ys4 = do
  let f :: (Double, Double) -> m (DualNumber Double)
      f (x, res) = synthLossSquared factivation x ys1 ys2 ys3 ys4 res
  sumResultsDual f samples

sumTrainableInputsS :: DualNumber (Vector Double)
                    -> Int
                    -> VecDualNumber Double
                    -> Int
                    -> Data.Vector.Vector (DualNumber Double)
sumTrainableInputsS x offset vec width =
  let f :: Int -> DualNumber Double
      f i = sumTrainableInputsV x (offset + i) vec
  in V.generate width f

splitLayerV :: forall m. DeltaMonad Double m
            => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
            -> DualNumber (Vector Double)
            -> Int
            -> VecDualNumber Double
            -> Int
            -> m ( DualNumber (Vector Double)
                 , DualNumber (Vector Double)
                 , DualNumber (Vector Double)
                 , DualNumber (Vector Double) )
splitLayerV factivation hiddenVec offset vec width = do
  let multiplied = sumTrainableInputsS hiddenVec offset vec width
      chunkWidth = width `div` 4
      activate :: Int -> m (DualNumber (Vector Double))
      activate n = do
        let v = V.slice (n * chunkWidth) chunkWidth multiplied
        factivation $ deltaSeq v + varV vec (offset + width + n)
  a0 <- activate 0
  a1 <- activate 1
  a2 <- activate 2
  a3 <- activate 3
  return (a0, a1, a2, a3)

synthLossBareTotal
  :: DeltaMonad Double m
  => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
  -> (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
  -> (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
  -> Data.Vector.Storable.Vector (Double, Double)
  -> Int
  -> VecDualNumber Double
  -> m (DualNumber Double)
synthLossBareTotal factivation factivationHidden factivationMiddle
                   samples width vec = do
  let (inputs, outputs) = V.unzip samples
      nSamples = V.length samples
      sampleData = inputs <> outputs
  hiddenVec <- initialLayerMnistV factivationHidden sampleData vec width
  let offsetMiddle = width + 1
  (ys1, ys2, ys3, ys4) <- splitLayerV factivationMiddle hiddenVec
                                      offsetMiddle vec (bloat * nSamples * 4)
  synthLossAll factivation samples ys1 ys2 ys3 ys4

conditionalSynthTests:: TestTree
conditionalSynthTests =
 testGroup "reluAct: synthesizing a sum of linear conditionals matching samples"
  [ gradSmartTestCase "reluAct"
      synthLossBareTotal 42 1 10 100000
      (1.925929944387236e-34,0.2)
{-
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
-}
  ]
