{-# LANGUAGE DataKinds, TypeFamilies #-}
module TestOutdated (testTrees) where

import Prelude

import           Control.Arrow (first)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Foreign.Storable (Storable)
import           Foreign.Storable.Tuple ()
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.External.OutdatedOptimizer
import MnistData
import MnistFcnnScalar
import Tool.EqEpsilon

type ADValD = ADVal 'ADModeGradient Double

type ADInputsD = ADInputs 'ADModeGradient Double

testTrees :: [TestTree]
testTrees = [ fitTests
            , fit2Tests
            , fit2TestsL
            , smartFitTests
            , smartFit2Tests
            , smartFit2TestsL
            , smartFit3Tests
            , smartFit3TestsL
            , stochasticFit3Tests
            ]

-- Inlined to avoid the tiny overhead of calling an unknown function.
-- This operation is needed, because @sumListDual@ doesn't (always) fuse.
sumResultsDual :: forall d a r. (ADModeAndNum d r, Storable a)
               => (a -> ADVal d r)
               -> Vector a
               -> ADVal d r
{-# INLINE sumResultsDual #-}
sumResultsDual f as =
  let g :: ADVal d r -> a -> ADVal d r
      g !acc a = acc + f a
      sumUs = V.foldl' g 0 as
  in sumUs

lengthADVal :: Storable r => ADInputs d r -> Int
lengthADVal ADInputs{inputPrimal0} = V.length inputPrimal0

-- This, and other Fit and Fit2 nn operations, have unfused Delta let-bindings
-- (one binding per each subexpression, even when not needed), which is fine,
-- just not enough for comprehensive benchmarks.
hiddenLayerFit :: (ADValD -> ADValD)
               -> Double
               -> ADInputsD
               -> Int
               -> Data.Vector.Vector ADValD
hiddenLayerFit factivation x vec width =
  let f :: Int -> ADValD
      f i =
        let weight = at0 vec (2 * i)
            bias = at0 vec (2 * i + 1)
            sx = scale x weight
            sxBias = sx + bias
        in factivation sxBias
  in V.generate width f

outputLayerFit :: (ADValD -> ADValD)
               -> Data.Vector.Vector ADValD
               -> Int
               -> ADInputsD
               -> ADValD
outputLayerFit factivation hiddenVec offset vec =
  let outSum = sumTrainableInputs hiddenVec offset vec
  in factivation outSum

nnFit :: (ADValD -> ADValD)
      -> (ADValD -> ADValD)
      -> Double -> ADInputsD -> ADValD
nnFit factivationHidden factivationOutput x vec =
  -- One bias of the outer layer, a list of weights of the outer layer,
  -- a list of the same length of weights and biases of the hidden layer.
  let width = (lengthADVal vec - 1) `div` 3
      hiddenVec = hiddenLayerFit factivationHidden x vec width
  in outputLayerFit factivationOutput hiddenVec (2 * width) vec

nnFitLoss :: (ADValD -> ADValD)
          -> (ADValD -> ADValD)
          -> Double -> Double -> ADInputsD -> ADValD
nnFitLoss factivationHidden factivationOutput x targ vec =
  let res = nnFit factivationHidden factivationOutput x vec
  in squaredDifference targ res

nnFitLossTotal :: (ADValD -> ADValD)
               -> (ADValD -> ADValD)
               -> Vector (Double, Double)
               -> ADInputsD
               -> ADValD
nnFitLossTotal factivationHidden factivationOutput samples vec =
  let f :: (Double, Double) -> ADValD
      f (x, res) = nnFitLoss factivationHidden factivationOutput x res vec
  in sumResultsDual f samples
    -- an implementation that doesn't delve into implementation details
    -- of dual numbers, but uses @sumListDual@ instead is up to twice slower,
    -- due to no list fusion happening across monadic operations

-- We will use the samples with fixed known good seeds, so we don't care
-- whether any first element of the pair (nearly) repeats,
-- creating (nearly) unsatisfiable samples.
--
-- Alas, this happens too often and is hard to pinpoint,
-- so instead let's generate floats and covert to doubles,
-- to ensure at least minimal separation. Without this,
-- many tests that worked with floats, don't work with doubles,
-- and now more old tests pass and new tests pass with more CPU
-- usage that couldn't pass with floats no matter what, due to numeric errors.
wsFit :: (Float, Float) -> Int -> Int
      -> Vector (Double, Double)
wsFit range seed k =
  let rolls :: RandomGen g => g -> Vector Double
      rolls = V.unfoldrExactN k (first realToFrac . uniformR range)
      (g1, g2) = split $ mkStdGen seed
  in V.zip (rolls g1) (rolls g2)

-- Here a huge separation is ensured.
wsFitSeparated :: (Double, Double) -> Int -> Int
               -> Vector (Double, Double)
wsFitSeparated range@(low, hi) seed k =
  let rolls :: RandomGen g => g -> Vector Double
      rolls = V.unfoldrExactN k (uniformR range)
      width = hi - low
      steps = V.generate k (\n ->
        low + fromIntegral n * width / (fromIntegral k - 1))
      g = mkStdGen seed
  in V.zip steps (rolls g)

gdSimpleShow :: HasDelta r
             => r
             -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
             -> Domain0 r
             -> Int
             -> IO ([r], r)
gdSimpleShow gamma f initVec n = do
  (res, _, _, _) <- gdSimple gamma f n (initVec, V.empty, V.empty, V.empty)
  (_, v) <- revIO 1 f (res, V.empty, V.empty, V.empty)
  return (V.toList res, v)

gdSimpleTestCase
  :: Num a
  => String
  -> ((a, a) -> Int -> Int
      -> Vector (Double, Double))
  -> ((ADValD -> ADValD)
      -> (ADValD -> ADValD)
      -> Vector (Double, Double)
      -> ADInputsD
      -> ADValD)
  -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree
gdSimpleTestCase prefix sampleFunction lossFunction
                 seedSamples nSamples nParams0 gamma nIterations expected =
  let samples = sampleFunction (-1, 1) seedSamples nSamples
      vec = V.unfoldrExactN nParams0 (uniformR (-1, 1)) $ mkStdGen 33
      name = prefix ++ " "
             ++ unwords [ show seedSamples, show nSamples
                        , show nParams0, show gamma, show nIterations ]
  in testCase name $ do
       res <- snd <$> gdSimpleShow gamma (lossFunction tanh tanh samples)
                                   vec nIterations
       res @?~ expected

gdSimpleWsTestCase
  :: ((ADValD -> ADValD)
      -> (ADValD -> ADValD)
      -> Vector (Double, Double)
      -> ADInputsD
      -> ADValD)
  -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree
gdSimpleWsTestCase = gdSimpleTestCase "gdSimple Ws" wsFit

gdSimpleSeparatedTestCase
  :: ((ADValD -> ADValD)
      -> (ADValD -> ADValD)
      -> Vector (Double, Double)
      -> ADInputsD
      -> ADValD)
  -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree
gdSimpleSeparatedTestCase = gdSimpleTestCase "gdSimple Separated" wsFitSeparated

lenP :: Int -> Int
lenP width = 3 * width + 1

-- Some tests here fail due to not smart enough gradient descent
-- (overshooting, mostly).
fitTests :: TestTree
fitTests = testGroup "Sample fitting fully connected neural net tests"
  [ testCase "wsFit (-1, 1) 42 20" $
      V.toList (wsFit (-1, 1) 42 20) @?~ [(-0.22217941284179688,-0.5148218870162964),(0.25622618198394775,0.42662060260772705),(7.794177532196045e-2,-0.5301129817962646),(0.384537935256958,0.8958269357681274),(-0.6027946472167969,-0.5425337553024292),(0.4734766483306885,0.19495820999145508),(0.3921601474285126,0.8963258266448975),(-2.679157257080078e-2,-0.43389952182769775),(-8.326125144958496e-2,-0.17110145092010498),(-6.933605670928955e-2,-0.6602561473846436),(-0.7554467916488647,0.9077622890472412),(-0.17885446548461914,0.14958932995796204),(-0.49340176582336426,0.13965561985969543),(0.4703446626663208,-0.487585186958313),(-0.37681376934051514,-0.39065873622894287),(-0.9820539951324463,-0.10905027389526367),(0.6628230810165405,0.11808493733406067),(4.337519407272339e-3,-7.50422477722168e-3),(-0.270332932472229,0.9103447198867798),(2.815529704093933e-2,-0.9941539764404297)]
  , gdSimpleWsTestCase
      nnFitLossTotal 42 8 (lenP 10) 0.1 10000 1.6225349272445413e-2
  , gdSimpleWsTestCase
      nnFitLossTotal 42 10 (lenP 10) 0.01 100000 0.11821681957239855
      -- failed; even 61 1000000 was not enough
  , testCase "wsFitSeparated (-1, 1) 42 20" $
      V.toList (wsFitSeparated (-1, 1) 42 20) @?~ [(-1.0,0.8617048050432681),(-0.8947368421052632,-0.12944690839124995),(-0.7894736842105263,0.7709385349363602),(-0.6842105263157895,0.7043981517795999),(-0.5789473684210527,0.5002907568304664),(-0.4736842105263158,-0.20067467322001753),(-0.368421052631579,-5.526582421799997e-2),(-0.26315789473684215,0.3006213813725571),(-0.1578947368421053,0.12350686811659489),(-5.2631578947368474e-2,-0.7621608299731257),(5.263157894736836e-2,-3.550743010902346e-2),(0.1578947368421053,-0.32868601453242263),(0.26315789473684204,0.7784360517385773),(0.368421052631579,-0.6715107907491862),(0.4736842105263157,-0.41971965075782536),(0.5789473684210527,-0.4920995297212283),(0.6842105263157894,-0.8809132509345221),(0.7894736842105263,-7.615997455596313e-2),(0.894736842105263,0.36412224491658224),(1.0,-0.31352088018219515)]
  , gdSimpleSeparatedTestCase
      nnFitLossTotal 42 8 (lenP 10) 0.1 10000 0.3884360171054549
  , gdSimpleSeparatedTestCase
      nnFitLossTotal 42 10 (lenP 10) 0.01 100000 1.9817301995554423e-2
  , gdSimpleSeparatedTestCase
      nnFitLossTotal 42 16 (lenP 10) 0.01 100000 6.88603932297595e-2
  ]

-- This connects with only one neuron from the first hidden layer.
-- No wonder the extra hidden layer was not particulary effective
-- compared to wider single hidden layer.
middleLayerFit2 :: (ADValD -> ADValD)
                -> Data.Vector.Vector ADValD
                -> Int
                -> ADInputsD
                -> Data.Vector.Vector ADValD
middleLayerFit2 factivation hiddenVec offset vec =
  let f :: Int -> ADValD -> ADValD
      f i x =
        let weight = at0 vec (offset + 2 * i)
            bias = at0 vec (offset + 1 + 2 * i)
            sx = x * weight
            sxBias = sx + bias
        in factivation sxBias
  in V.imap f hiddenVec

nnFit2 :: (ADValD -> ADValD)
       -> (ADValD -> ADValD)
       -> (ADValD -> ADValD)
       -> Double -> ADInputsD -> ADValD
nnFit2 factivationHidden factivationMiddle factivationOutput x vec =
  -- Due to not being fully connected, the parameters are only:
  -- one bias of the outer layer, a list of weights of the outer layer,
  -- a list of the same length of weights and biases of the first hidden layer
  -- and of the middle hidden layer.
  let width = (lengthADVal vec - 1) `div` 5
      hiddenVec = hiddenLayerFit factivationHidden x vec width
      middleVec = middleLayerFit2 factivationMiddle hiddenVec (2 * width) vec
  in outputLayerFit factivationOutput middleVec (4 * width) vec

nnFit2Loss :: (ADValD -> ADValD)
           -> (ADValD -> ADValD)
           -> (ADValD -> ADValD)
           -> Double -> Double -> ADInputsD -> ADValD
nnFit2Loss factivationHidden factivationMiddle factivationOutput x targ vec =
  let res = nnFit2 factivationHidden factivationMiddle factivationOutput x vec
  in squaredDifference targ res

nnFit2LossTotal :: (ADValD -> ADValD)
                -> (ADValD -> ADValD)
                -> (ADValD -> ADValD)
                -> Vector (Double, Double)
                -> ADInputsD
                -> ADValD
nnFit2LossTotal factivationHidden factivationMiddle factivationOutput
                samples vec =
  let f :: (Double, Double) -> ADValD
      f (x, res) =
        nnFit2Loss factivationHidden factivationMiddle factivationOutput
                   x res vec
  in sumResultsDual f samples

lenP2 :: Int -> Int
lenP2 width = 5 * width + 1

-- Two layers seem to be an advantage for data with points very close
-- together. Otherwise, having all neurons on one layer is more effective.
fit2Tests :: TestTree
fit2Tests = testGroup "Sample fitting 2 hidden layer not fully connected nn tests"
  [ gdSimpleWsTestCase
      (nnFit2LossTotal tanh) 42 8 (lenP2 6) 0.1 10000
      1.2856619684390336e-2
  , gdSimpleWsTestCase
      (nnFit2LossTotal tanh) 42 10 (lenP2 6) 0.01 400000
      3.835053990072211e-2
  , gdSimpleSeparatedTestCase
      (nnFit2LossTotal tanh) 42 8 (lenP2 6) 0.1 10000
      0.31692351465375723
  , gdSimpleSeparatedTestCase
      (nnFit2LossTotal tanh) 42 10 (lenP2 6) 0.01 100000
      1.2308485318049472e-3
  , gdSimpleSeparatedTestCase
      (nnFit2LossTotal tanh) 42 16 (lenP2 12) 0.01 100000
      1.9398514673723763e-2
  ]

-- The same tests, but with logistic for the first hidden layer instead
-- of tanh. Usually worse results.
fit2TestsL :: TestTree
fit2TestsL = testGroup "logistic: Sample fitting 2 hidden layer not fully connected nn tests"
  [ gdSimpleWsTestCase
      (nnFit2LossTotal logistic) 42 8 (lenP2 6) 0.1 10000
      9.323867115794165e-3
  , gdSimpleWsTestCase
      (nnFit2LossTotal logistic) 42 10 (lenP2 6) 0.01 400000
      0.12307345215742066
  , gdSimpleSeparatedTestCase
      (nnFit2LossTotal logistic) 42 8 (lenP2 6) 0.1 10000
      0.2978076625110597
  , gdSimpleSeparatedTestCase
      (nnFit2LossTotal logistic) 42 10 (lenP2 6) 0.01 100000
      8.707658552473477e-2
  , gdSimpleSeparatedTestCase
      (nnFit2LossTotal logistic) 42 16 (lenP2 12) 0.01 100000
      1.2453082870396885
  ]

gdSmartShow :: (ADInputsD -> ADValD)
            -> Domain0 Double
            -> Int
            -> IO ([Double], (Double, Double))
gdSmartShow f initVec n = do
  ((res, _, _, _), gamma) <- gdSmart f n (initVec, V.empty, V.empty, V.empty)
  (_, v) <- revIO 1 f (res, V.empty, V.empty, V.empty)
  return (V.toList res, (v, gamma))

gradSmartTestCase :: Num a
                  => String
                  -> ((a, a) -> Int -> Int
                      -> Vector (Double, Double))
                  -> ((ADValD -> ADValD)
                      -> (ADValD -> ADValD)
                      -> Vector (Double, Double)
                      -> ADInputsD
                      -> ADValD)
                  -> Int -> Int -> Int -> Int -> (Double, Double)
                  -> TestTree
gradSmartTestCase prefix sampleFunction lossFunction
                  seedSamples nSamples nParams0 nIterations expected =
  let samples = sampleFunction (-1, 1) seedSamples nSamples
      vec = V.unfoldrExactN nParams0 (uniformR (-1, 1)) $ mkStdGen 33
      name = prefix ++ " "
             ++ unwords [ show seedSamples, show nSamples
                        , show nParams0, show nIterations ]
  in testCase name $ do
       res <- snd <$> gdSmartShow (lossFunction tanh tanh samples) vec nIterations
       res @?~ expected

gradSmartWsTestCase
  :: ((ADValD -> ADValD)
      -> (ADValD -> ADValD)
      -> Vector (Double, Double)
      -> ADInputsD
      -> ADValD)
  -> Int -> Int -> Int -> Int -> (Double, Double)
  -> TestTree
gradSmartWsTestCase = gradSmartTestCase "gradSmart Ws" wsFit

gradSmartSeparatedTestCase
  :: ((ADValD -> ADValD)
      -> (ADValD -> ADValD)
      -> Vector (Double, Double)
      -> ADInputsD
      -> ADValD)
  -> Int -> Int -> Int -> Int -> (Double, Double)
  -> TestTree
gradSmartSeparatedTestCase =
  gradSmartTestCase "gradSmart Separated" wsFitSeparated

-- With Float, the approximation overshoots all the time and makes smaller
-- and smaller steps, getting nowhere. This probably means
-- approximation with this number of neurons is not possible.
-- However, adding neurons doesn't help (without huge increases of iterations).
-- The fact that results are better when freely overshooting
-- suggests there are local minima, which confirms too low dimensionality.
-- The experiments with separated samples seem to confirm both hypotheses.
--
-- With Double, it scales well to twice as many samples or even more,
-- but it takes too long to verify if/when errors crop in again.
smartFitTests :: TestTree
smartFitTests = testGroup "Smart descent sample fitting fully connected nn tests"
  [ gradSmartWsTestCase
      nnFitLossTotal 42 8 (lenP 10) 10000
      (2.0585450568797953e-3,1.25e-2)
  , gradSmartWsTestCase
      nnFitLossTotal 42 10 (lenP 20) 1000000
      (9.072288039580448e-2,6.25e-3)
        -- 31 not enough, 700000 not enough
  , gradSmartWsTestCase
      nnFitLossTotal 42 16 (lenP 20) 1700000
      (4.8336260347113275e-2,1.5625e-3)
  , gradSmartSeparatedTestCase
      nnFitLossTotal 42 8 (lenP 10) 10000
      (1.5742022677967708e-2,2.5e-2)
  , gradSmartSeparatedTestCase
      nnFitLossTotal 42 10 (lenP 10) 100000
      (4.506881373306206e-10,2.5e-2)
  , gradSmartSeparatedTestCase
      nnFitLossTotal 42 16 (lenP 10) 100000
      (5.197706771219677e-2,6.25e-3)
  , gradSmartSeparatedTestCase
      nnFitLossTotal 42 24 (lenP 33) 700000
      (2.967249104936791e-2,6.25e-3)
        -- 61 1300000 not enough
  , gradSmartSeparatedTestCase
      nnFitLossTotal 42 32 (lenP 20) 1700000
      (3.828456463288314e-2,6.25e-3)
        -- 151 1000000 not enough, despite taking twice longer
  ]

smartFit2Tests :: TestTree
smartFit2Tests =
 testGroup "Smart descent sample fitting 2 hidden layer not fully connected nn tests"
  [ gradSmartWsTestCase
      (nnFit2LossTotal tanh) 42 8 (lenP2 6) 10000
      (4.896924209457198e-3,2.5e-2)
  , gradSmartWsTestCase
      (nnFit2LossTotal tanh) 42 10 (lenP2 6) 400000
      (8.470989419560765e-2,2.5e-2)
  , gradSmartWsTestCase
      (nnFit2LossTotal tanh) 42 16 (lenP2 12) 700000
      (5.149610997592684e-2,3.90625e-4)
        -- 61 1000000 not enough for 20, 101 700000 enough
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal tanh) 42 8 (lenP2 6) 10000
      (1.832621758590325e-2,1.25e-2)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal tanh) 42 10 (lenP2 6) 100000
      (2.6495249749522148e-2,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal tanh) 42 16 (lenP2 12) 100000
      (1.8617700399788891e-3,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal tanh) 42 24 (lenP2 12) 1300000
      (1.0411445668840221e-2,3.125e-3)
        -- this is faster but less accurate than 101 1000000
        -- 151 700000 is not enough
  ]

-- The same tests, but with logistic for the first hidden layer instead
-- of tanh. Usually worse results.
smartFit2TestsL :: TestTree
smartFit2TestsL =
 testGroup "logistic: Smart descent sample fitting 2 hidden layer not fully connected nn tests"
  [ gradSmartWsTestCase
      (nnFit2LossTotal logistic) 42 8 (lenP2 6) 10000
      (5.277048486983709e-3,5.0e-2)
  , gradSmartWsTestCase
      (nnFit2LossTotal logistic) 42 10 (lenP2 6) 400000
      (0.12231013820426907,2.5e-2)
  , gradSmartWsTestCase
      (nnFit2LossTotal logistic) 42 16 (lenP2 12) 700000
      (0.625388101609215,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal logistic) 42 8 (lenP2 6) 10000
      (0.486980368199192,2.5e-2)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal logistic) 42 10 (lenP2 6) 100000
      (2.9673291826644015e-2,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal logistic) 42 16 (lenP2 12) 100000
      (2.1703256232095827,1.25e-2)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal logistic) 42 24 (lenP2 12) 1300000
      (2.225663713307959,3.90625e-4)
  ]

-- This is really fully connected.
middleLayerFit3 :: (ADValD -> ADValD)
                -> Data.Vector.Vector ADValD
                -> Int
                -> ADInputsD
                -> Data.Vector.Vector ADValD
middleLayerFit3 factivation hiddenVec offset vec =
  middleLayerMnist factivation hiddenVec offset vec $ V.length hiddenVec

nnFit3 :: (ADValD -> ADValD)
       -> (ADValD -> ADValD)
       -> (ADValD -> ADValD)
       -> Double -> ADInputsD -> ADValD
nnFit3 factivationHidden factivationMiddle factivationOutput x vec =
  -- This is fully connected, so given width w, the number of parameters is:
  -- one bias of the outer layer, a list of weights of the outer layer
  -- of length w, a list of the same length of weights and biases of the first
  -- hidden layer, w * w weigths in the middle hidden layer and w biases.
  -- In total, #params0 == 1 + w + 2 * w + w^2 + w == w^2 + 4 * w + 1,
  -- so the equation to solve is w^2 + 4 * w + (1 - #params0) = 0.
  -- Length 31 gives almost 3. Length 61 gives exactly 6.
  let len :: Double
      len = fromIntegral $ lengthADVal vec  -- #params
      width = floor $ (-4 + sqrt (12 + 4 * len)) / 2
      hiddenVec = hiddenLayerFit factivationHidden x vec width
      middleVec = middleLayerFit3 factivationMiddle hiddenVec (2 * width) vec
  in outputLayerFit factivationOutput middleVec ((3 + width) * width) vec

nnFit3Loss :: (ADValD -> ADValD)
           -> (ADValD -> ADValD)
           -> (ADValD -> ADValD)
           -> Double -> Double -> ADInputsD -> ADValD
nnFit3Loss factivationHidden factivationMiddle factivationOutput x targ vec =
  let res = nnFit3 factivationHidden factivationMiddle factivationOutput x vec
  in squaredDifference targ res

nnFit3LossTotal :: (ADValD -> ADValD)
                -> (ADValD -> ADValD)
                -> (ADValD -> ADValD)
                -> Vector (Double, Double)
                -> ADInputsD
                -> ADValD
nnFit3LossTotal factivationHidden factivationMiddle factivationOutput
                samples vec =
  let f :: (Double, Double) -> ADValD
      f (x, res) =
        nnFit3Loss factivationHidden factivationMiddle factivationOutput
                   x res vec
  in sumResultsDual f samples

lenP3 :: Int -> Int
lenP3 width = (4 + width) * width + 1

smartFit3Tests :: TestTree
smartFit3Tests =
 testGroup "Smart descent sample fitting 2 hidden layer really fully connected nn tests"
  -- The same (or slightly lower) number of parameters, but on many layers
  -- gives much worse results, except if there are few samples.
  -- It is also less costly for some reason.
  [ gradSmartWsTestCase
      (nnFit3LossTotal tanh) 42 8 (lenP3 4) 10000
      (3.5604072240265575e-3,2.5e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotal tanh) 42 10 (lenP3 4) 400000
      (0.10126792765437645,3.125e-3)
        -- failed, because too narrow (4 neurons in each hidden layer)
  , gradSmartWsTestCase
      (nnFit3LossTotal tanh) 42 16 (lenP3 6) 700000
      (0.19318876323310907,1.5625e-3)
        -- failed, because too narrow (6 neurons in each hidden layer)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanh) 42 8 (lenP3 4) 10000
      (6.291648505851797e-3,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanh) 42 10 (lenP3 4) 100000
      (4.34890234424764e-7,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanh) 42 16 (lenP3 6) 100000
      (0.3434691592146121,1.5625e-3)
        -- failed, because too narrow (6 neurons in each hidden layer)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanh) 42 24 (lenP3 6) 1300000
      (1.665065359469462,9.765625e-5)
        -- failed, because too narrow (6 neurons in each hidden layer)
  -- The same width of fully connected nn, but with 2 instead of 1 hidden
  -- layer has many more parameters and is usually more costly,
  -- but also much more powerful given enough training:
  , gradSmartWsTestCase
      (nnFit3LossTotal tanh) 42 8 (lenP3 6) 10000
      (2.1767148242940303e-3,1.25e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotal tanh) 42 10 (lenP3 6) 400000
      (1.3871923964300112e-4,6.25e-3)
  , gradSmartWsTestCase
      (nnFit3LossTotal tanh) 42 16 (lenP3 12) 700000
      (2.131955325962636e-5,7.8125e-4)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanh) 42 8 (lenP3 6) 10000
      (2.0369556559640215e-4,5.0e-2)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanh) 42 10 (lenP3 6) 100000
      (4.0282344474667426e-16,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanh) 42 16 (lenP3 12) 100000
      (1.5819824634756573e-5,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanh) 42 24 (lenP3 12) 1300000
      (1.1354796858869852e-6,1.5625e-3)
  ]

-- The same tests, but with logistic for the first hidden layer instead
-- of tanh. Usually worse results.
smartFit3TestsL :: TestTree
smartFit3TestsL =
 testGroup "logistic: Smart descent sample fitting 2 hidden layer really fully connected nn tests"
  [ gradSmartWsTestCase
      (nnFit3LossTotal logistic) 42 8 (lenP3 4) 10000
      (4.262690053475572e-3,2.5e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotal logistic) 42 10 (lenP3 4) 400000
      (8.133312854575311e-2,0.1)
  , gradSmartWsTestCase
      (nnFit3LossTotal logistic) 42 16 (lenP3 6) 700000
      (0.35607225062502207,1.5625e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal logistic) 42 8 (lenP3 4) 10000
      (8.041780516044969e-2,1.25e-2)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal logistic) 42 10 (lenP3 4) 100000
      (1.0877770623826884e-2,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal logistic) 42 16 (lenP3 6) 100000
      (1.444649714852858,1.25e-2)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal logistic) 42 24 (lenP3 6) 1300000
      (1.7847189651694308,1.953125e-4)
  , gradSmartWsTestCase
      (nnFit3LossTotal logistic) 42 8 (lenP3 6) 10000
      (5.436829414964154e-3,2.5e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotal logistic) 42 10 (lenP3 6) 400000
      (0.11938665766915235,1.25e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotal logistic) 42 16 (lenP3 12) 700000
      (0.24271694671964975,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal logistic) 42 8 (lenP3 6) 10000
      (8.700033031145113e-2,1.25e-2)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal logistic) 42 10 (lenP3 6) 100000
      (7.225917500882556e-6,1.25e-2)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal logistic) 42 16 (lenP3 12) 100000
      (2.3379235156826658e-2,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal logistic) 42 24 (lenP3 12) 1300000
      (0.6440964543158452,3.125e-3)
  ]

{-
nnFit3LossTotalOutput :: (ADValD -> ADValD)
                      -> (ADValD -> ADValD)
                      -> (ADValD -> ADValD)
                      -> Vector (Double, Double)
                      -> ADInputsD
                      -> ADValD
nnFit3LossTotalOutput f1 f2 f3 samples vec =
  nnFit3LossTotal f2 f3 f1 samples vec

-- The same tests, but with logistic for the output layer instead of tanh.
-- Somewhat better results than with tanh, but not worth recording.
-- OTOH, with reluAct (understandable, it rules out any negative values)
-- and with reluLeakyAct (gradient explosion for positive values?)
-- the results are disastrous. Also they are disastrous with either relu
-- in any other position (no idea why, there is one more layer to recover
-- anything that's lost; perhaps the sums overflow due to no normalization?)
-- and mediocre with logistic in other positions.
smartFit3TestsL3 :: TestTree
smartFit3TestsL3 =
 testGroup "logistic3: Smart descent sample fitting 2 hidden layer really fully connected nn tests"
  [ gradSmartWsTestCase
      (nnFit3LossTotalOutput logistic) 42 8 (lenP3 4) 10000
      (3.5604072240265575e-3,2.5e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotalOutput logistic) 42 10 (lenP3 4) 400000
      (0.10126792765437645,3.125e-3)
  , gradSmartWsTestCase
      (nnFit3LossTotalOutput logistic) 42 16 (lenP3 6) 700000
      (0.19318876323310907,1.5625e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotalOutput logistic) 42 8 (lenP3 4) 10000
      (6.291648505851797e-3,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotalOutput logistic) 42 10 (lenP3 4) 100000
      (4.34890234424764e-7,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotalOutput logistic) 42 16 (lenP3 6) 100000
      (0.3434691592146121,1.5625e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotalOutput logistic) 42 24 (lenP3 6) 1300000
      (1.665065359469462,9.765625e-5)
  , gradSmartWsTestCase
      (nnFit3LossTotalOutput logistic) 42 8 (lenP3 6) 10000
      (2.1767148242940303e-3,1.25e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotalOutput logistic) 42 10 (lenP3 6) 400000
      (1.3871923964300112e-4,6.25e-3)
  , gradSmartWsTestCase
      (nnFit3LossTotalOutput logistic) 42 16 (lenP3 12) 700000
      (2.131955325962636e-5,7.8125e-4)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotalOutput logistic) 42 8 (lenP3 6) 10000
      (2.0369556559640215e-4,5.0e-2)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotalOutput logistic) 42 10 (lenP3 6) 100000
      (4.0282344474667426e-16,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotalOutput logistic) 42 16 (lenP3 12) 100000
      (1.5819824634756573e-5,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotalOutput logistic) 42 24 (lenP3 12) 1300000
      (1.1354796858869852e-6,1.5625e-3)
  ]
-}

sgdShow :: HasDelta r
        => r
        -> (a -> ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
        -> [a]  -- ^ training data
        -> Domain0 r  -- ^ initial parameters
        -> IO ([r], r)
sgdShow gamma f trainData params0Init = do
  (res, _, _, _) <-
    fst <$> sgd gamma f trainData (params0Init, V.empty, V.empty, V.empty)
  (_, v) <- revIO 1 (f $ head trainData) (res, V.empty, V.empty, V.empty)
  return (V.toList res, v)

sgdTestCase
  :: String
  -> IO [a]
  -> (Int
      -> a
      -> ADInputsD
      -> ADValD)
  -> Double
  -> Double
  -> TestTree
sgdTestCase prefix trainDataIO trainWithLoss gamma expected =
  let widthHidden = 250
      nParams0 = lenMnist widthHidden
      vec = HM.randomVector 33 HM.Uniform nParams0 - HM.scalar 0.5
      name = prefix ++ " "
             ++ unwords [show widthHidden, show nParams0, show gamma]
  in testCase name $ do
       trainData <- trainDataIO
       res <- snd <$> sgdShow gamma (trainWithLoss widthHidden) trainData vec
       res @?~ expected

lenMnist :: Int -> Int
lenMnist widthHidden =
  widthHidden * (sizeMnistGlyphInt + 1) + sizeMnistLabelInt * (widthHidden + 1)

nnFit3ForStochastic :: Int
                    -> (Double, Double)
                    -> ADInputsD
                    -> ADValD
nnFit3ForStochastic _ (x, res) = nnFit3Loss tanh tanh tanh x res

stochasticFit3Tests :: TestTree
stochasticFit3Tests =
 testGroup "Stochastic gradient descent sample fitting 2 hidden layer really fully connected nn tests"
  [ let trainData = V.toList $ wsFit (-1, 1) 42 2
    in sgdTestCase "Ws 42 2"
         (return trainData) nnFit3ForStochastic 0.1 0.23539780131842747
  , let trainData = take 200 $ cycle $ V.toList $ wsFit (-1, 1) 42 2
    in sgdTestCase "Ws 42 2(200)"
         (return trainData) nnFit3ForStochastic 0.1 0.23539780131842747
  , let trainData = V.toList $ wsFitSeparated (-1, 1) 42 128
    in sgdTestCase "separated 42 128"
         (return trainData) nnFit3ForStochastic 0.1 3.465944781121193
  , let trainData = V.toList $ wsFitSeparated (-1, 1) 42 256
    in sgdTestCase "separated 42 256"
         (return trainData) nnFit3ForStochastic 0.1 1.912556094812049e-2
  , let trainData = take 1280 $ cycle $ V.toList $ wsFitSeparated (-1, 1) 42 128
    in sgdTestCase "separated 42 128(1280)"
         (return trainData) nnFit3ForStochastic 0.1 3.465944781121193
  ]
