module TestConditionalSynth (testTrees) where

import Prelude

import           Data.List (nub, sort, unfoldr)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Foreign.Storable (Storable)
import           Foreign.Storable.Tuple ()
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.OutdatedOptimizer
import HordeAd.Tool.MnistTools

testTrees :: [TestTree]
testTrees = [ conditionalSynthTests
            ]


-- * A neural net that learns to represent a list of input and result pairs
-- as a function that is a sum of conditionals with linear conditions
-- and linear or zero results.
--
-- The samples are easy: inputs and results are integers and inputs
-- are sorted and not repeating (with input repetition it would not be
-- a function or the output would need to be repeated as well).

bloat :: Int
bloat = 1

lenSynthV :: Int -> Int -> Data.Vector.Vector Int
lenSynthV width nSamples =
  V.fromList $ replicate width (nSamples * 2) ++ [width]
               ++ replicate (bloat * nSamples * 3) width
               ++ replicate 3 (bloat * nSamples)

-- If ai ranges over ps1, bi over ps2 and ci over ps4,
-- the value of the function on input x is
-- the sum of if x * ai + bi > 0 then (x * ai + bi) * ci else 0, which is
-- the sum of if x * ai + bi > 0 then x * ai * ci + bi * ci else 0
-- so each condition depends in a linear way on x and each result,
-- if not 0, depends in a linear way on input x.
--
-- To approximate the samples (a list of input and result pairs on which
-- parameters are trained or tested) using this code, divide the input
-- and multiply result appropriately, see @synthLossSquared@.
synthValue :: forall m. DeltaMonad Double m
           => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
           -> Double
           -> DualNumber (Vector Double)
           -> DualNumber (Vector Double)
           -> DualNumber (Vector Double)
           -> m (DualNumber Double)
synthValue factivation x ps1@(D u _) ps2 ps3 = do
  activated <- factivation $ scale (HM.konst x (V.length u)) ps1 + ps2
  returnLet $ activated <.>! ps3

synthLossSquared :: DeltaMonad Double m
                 => (DualNumber (Vector Double)
                     -> m (DualNumber (Vector Double)))
                 -> Double
                 -> DualNumber (Vector Double)
                 -> DualNumber (Vector Double)
                 -> DualNumber (Vector Double)
                 -> Double
                 -> m (DualNumber Double)
synthLossSquared factivation x ps1 ps2 ps3 targ = do
  y <- synthValue factivation (x / 1000) ps1 ps2 ps3
  lossSquared (targ / 10000) y  -- smaller target to overcome @tanh@ clamping

-- Inlined to avoid the tiny overhead of calling an unknown function.
sumResultsDual :: forall m a r. (DeltaMonad r m, Storable a)
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

synthLossAll
  :: forall m. DeltaMonad Double m
  => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
  -> Data.Vector.Storable.Vector (Double, Double)
  -> DualNumber (Vector Double)
  -> DualNumber (Vector Double)
  -> DualNumber (Vector Double)
  -> m (DualNumber Double)
synthLossAll factivation samples ps1 ps2 ps3 = do
  let f :: (Double, Double) -> m (DualNumber Double)
      f (x, y) = synthLossSquared factivation x ps1 ps2 ps3 y
  sumResultsDual f samples

sumTrainableInputsS :: DualNumber (Vector Double)
                    -> Int
                    -> DualNumberVariables Double
                    -> Int
                    -> Data.Vector.Vector (DualNumber Double)
sumTrainableInputsS x offset variables width =
  let f :: Int -> DualNumber Double
      f i = sumTrainableInputsV x (offset + i) variables
  in V.generate width f

splitLayerV :: forall m. DeltaMonad Double m
            => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
            -> DualNumber (Vector Double)
            -> Int
            -> DualNumberVariables Double
            -> Int
            -> m ( DualNumber (Vector Double)
                 , DualNumber (Vector Double)
                 , DualNumber (Vector Double) )
splitLayerV factivation hiddenVec offset variables width = do
  let multiplied = sumTrainableInputsS hiddenVec offset variables width
      chunkWidth = width `div` 3
      activate :: Int -> m (DualNumber (Vector Double))
      activate n = do
        let v = V.slice (n * chunkWidth) chunkWidth multiplied
        factivation $ deltaSeq1 v + varV variables (offset + width + n)
  a0 <- activate 0
  a1 <- activate 1
  a2 <- activate 2
  return (a0, a1, a2)

synthLossBareTotal
  :: DeltaMonad Double m
  => (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
  -> (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
  -> (DualNumber (Vector Double) -> m (DualNumber (Vector Double)))
  -> Data.Vector.Storable.Vector (Double, Double)
  -> Int
  -> DualNumberVariables Double
  -> m (DualNumber Double)
synthLossBareTotal factivation factivationHidden factivationMiddle
                   samples width variables = do
  let (inputs, outputs) = V.unzip samples
      nSamples = V.length samples
      sampleData = inputs <> outputs
      hiddenLayer1 = sumConstantDataL sampleData 0 variables width
                     + varV variables width  -- bias
  nonlinearLayer1 <- factivationHidden hiddenLayer1
  let offsetMiddle = width + 1
  (ps1, ps2, ps3) <- splitLayerV factivationMiddle nonlinearLayer1
                                 offsetMiddle variables (bloat * nSamples * 3)
  synthLossAll factivation samples ps1 ps2 ps3


-- * Tests and generation of random data

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

gdSmartShow :: (DualNumberVariables Double
                -> DeltaMonadGradient Double (DualNumber Double))
            -> DomainV Double
            -> Int
            -> ([Data.Vector.Storable.Vector Double], (Double, Double))
gdSmartShow f paramsV0 n =
  let ((_, paramsV, _), gamma) = gdSmart f n (V.empty, paramsV0, V.empty)
      (_, value) = df f (V.empty, paramsV, V.empty)
  in (V.toList paramsV, (value, gamma))

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
      -> DualNumberVariables Double
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
              (lossFunction reluActV tanhActV tanhActV samples width)
              paramsV0 nIterations)
       @?= expected

conditionalSynthTests:: TestTree
conditionalSynthTests =
 testGroup "reluAct: synthesizing a sum of linear conditionals matching samples"
  [ gradSmartTestCase "reluAct"
      synthLossBareTotal 42 1 10 1
      (5.58009e-3,0.1)
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
