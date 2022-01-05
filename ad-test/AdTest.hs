{-# LANGUAGE FlexibleContexts, RankNTypes #-}
module Main (main) where

import Prelude

import           Control.Arrow (first)
import           Data.Reflection (Reifies)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           Numeric.AD.Internal.Reverse.Double (Tape)
import           Numeric.AD.Mode.Reverse.Double hiding (diff)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Ad Tests" [ adXorTests
                             , fitTests
                             , fit2Tests
                             , smartFitTests
                             , smartFit2Tests
                             ]

type Domain r = Data.Vector.Vector r
-- Bummer. Unboxed vectors can't be Traversable due to their constraint.
-- type Domain r = Data.Vector.Unboxed.Vector r

type Domain' r = Domain r

gradDesc :: Double
         -> (forall s. Reifies s Tape => Domain (ReverseDouble s) -> ReverseDouble s)
         -> Int
         -> Domain Double
         -> Domain' Double
gradDesc gamma f = go where
  go :: Int -> Domain Double -> Domain' Double
  go 0 !vecInitial = vecInitial
  go n vecInitial =
    let combine i r = i - gamma * r
        v = gradWith combine f vecInitial
    in go (pred n) v

gradDescShow :: Double
             -> (forall s. Reifies s Tape
                 => Domain (ReverseDouble s) -> ReverseDouble s)
             -> Domain Double
             -> Int
             -> ([Double], Double)
gradDescShow gamma f initVec n =
  let res = gradDesc gamma f n initVec
      (value, _) = grad' f res
  in (V.toList res, value)

var :: Int -> Domain r -> r
var i vec = vec V.! i

tanhAct :: Floating r
        => r -> r
tanhAct = tanh

reluAct :: (Num r, Ord r)
        => r -> r
reluAct = max 0

scaleAddWithBias :: Num r
                 => r -> r -> Int
                 -> Domain r
                 -> r
scaleAddWithBias x y ixWeight vec =
  let wx = var ixWeight vec
      wy = var (ixWeight + 1) vec
      bias = var (ixWeight + 2) vec
      sx = x * wx
      sy = y * wy
      sxy = sx + sy
  in sxy + bias

neuron :: Num r
       => (r -> r)
       -> r -> r -> Int -> Domain r
       -> r
neuron factivation x y ixWeight vec =
  let sc = scaleAddWithBias x y ixWeight vec
  in factivation sc

nnXor :: Num r
      => (r -> r)
      -> r -> r -> Domain r
      -> r
nnXor factivation x y vec =
  let n1 = neuron factivation x y 0 vec
      n2 = neuron factivation x y 3 vec
  in neuron factivation n1 n2 6 vec

lossSquared :: Num r
            => r -> r -> r
lossSquared u v =
  let diff = u - v
  in diff * diff

nnXorLoss :: Num r
       => (r -> r)
       -> r -> r -> r -> Domain r
       -> r
nnXorLoss factivation x y res vec =
  let r = nnXor factivation x y vec
  in lossSquared r res

nnXorLossTotal :: Num r
        => (r -> r)
        -> Domain r
        -> r
nnXorLossTotal factivation vec =
  let n1 = nnXorLoss factivation 0 0 0 vec
      n2 = nnXorLoss factivation 0 1 1 vec
      n3 = nnXorLoss factivation 1 0 1 vec
      n4 = nnXorLoss factivation 1 1 0 vec
      n12 = n1 + n2
      n34 = n3 + n4
  in n12 + n34

-- These tests work on @Float@ in mostly-harmless-test, but here they can't
-- because I can't share polymorphic code between @Float@ and @Double@
-- if I want to use @ReverseDouble@, which is require to plug memory leaks.
ws, ws2 :: Domain Double
ws = let w = [0.37, 0.28, 0.19] in V.fromList $ w ++ w ++ w
ws2 = let w = [-1.37, 2.28, -0.19] in V.fromList $ w ++ w ++ w

-- The values below are copied from the other tests to compare results
-- They seem to be pretty close.
adXorTests :: TestTree
adXorTests = testGroup "XOR neural net tests (errors are expected here and in all latter tests, because expected results come from the main library (the difference is usually tiny, due to floating point arithmetics))"
  [ testCase "0.1 tanhAct ws 500"
    $ gradDescShow 0.1 (nnXorLossTotal tanhAct) ws 500
      @?= ([2.256964,2.255974,-0.6184606,0.943269,0.9431414,-1.2784432,1.805072,-1.9925138,-0.704399],1.20509565e-2)
  , testCase "0.1 tanhAct ws 5000"
    $ gradDescShow 0.1 (nnXorLossTotal tanhAct) ws 5000
      @?= ([2.4474504,2.4467778,-0.8350617,1.3046894,1.3045748,-1.8912042,2.3819275,-2.5550227,-0.8139653],1.8524402e-4)
  , testCase "0.01 tanhAct ws2 50000"
    $ gradDescShow 0.01 (nnXorLossTotal tanhAct) ws2 50000
      @?= ([-1.9872262,2.576039,0.66793317,-1.7813873,2.2283037,-0.9866766,-2.1694322,2.1973324,2.9272876],2.1781659e-4)
  , testCase "0.01 reluAct ws 5000"
    $ gradDescShow 0.01 (nnXorLossTotal reluAct) ws 5000  -- no cookie
      @?= ([0.18997861,0.14774871,0.25415534,0.28254044,0.21788013,0.22178599,8.981165e-2,-6.05783e-2,0.49060053],1.0)
  , testCase "0.1 reluAct ws2 50000"
    $ gradDescShow 0.1 (nnXorLossTotal reluAct) ws2 50000  -- no cookie
      @?= ([-1.2425352,2.6025252,0.13252532,-1.5821311,1.7432425,-0.72675747,-1.7345629,1.9154371,-0.42541993],2.0)
  ]

scaleAddVecWithBias :: Num r
                    => Domain r
                    -> Int
                    -> Domain r
                    -> r
scaleAddVecWithBias xs offset vec =
  let bias = var offset vec
      f !acc i u =
        let v = var (offset + 1 + i) vec
        in acc + u * v
  in V.ifoldl' f bias xs

hiddenLayerFit :: forall r. Num r
               => (r -> r)
               -> r
               -> Domain r
               -> Int
               -> Domain r
hiddenLayerFit factivation x vec width =
  let f :: Int -> r
      f i =
        let weight = var (2 * i) vec
            bias = var (2 * i + 1) vec
            sx = x * weight
            sxBias = sx + bias
        in factivation sxBias
  in V.generate width f

outputLayerFit :: Num r
               => (r -> r)
               -> Domain r
               -> Int
               -> Domain r
               -> r
outputLayerFit factivation hiddenVec offset vec =
  let outSum = scaleAddVecWithBias hiddenVec offset vec
  in factivation outSum

nnFit :: Num r
      => (r -> r)
      -> (r -> r)
      -> r -> Domain r -> r
nnFit factivationHidden factivationOutput x vec =
  -- One bias of the outer layer, a list of weights of the outer layer,
  -- a list of the same length of weights and biases of the hidden layer.
  let width = (V.length vec - 1) `div` 3
      hiddenVec = hiddenLayerFit factivationHidden x vec width
  in outputLayerFit factivationOutput hiddenVec (2 * width) vec

nnFitLoss :: Num r
          => (r -> r)
          -> (r -> r)
          -> r -> r -> Domain r -> r
nnFitLoss factivationHidden factivationOutput x res vec =
  let r = nnFit factivationHidden factivationOutput x vec
  in lossSquared r res

nnFitLossTotal :: forall s. Reifies s Tape
               => (ReverseDouble s -> ReverseDouble s)
               -> (ReverseDouble s -> ReverseDouble s)
               -> Data.Vector.Unboxed.Vector (Double, Double)
               -> Domain (ReverseDouble s)
               -> ReverseDouble s
nnFitLossTotal factivationHidden factivationOutput samples vec =
  let f :: ReverseDouble s -> (Double, Double) -> ReverseDouble s
      f !acc (x, res) =
        let fl = nnFitLoss factivationHidden factivationOutput
                           (auto x) (auto res) vec
        in acc + fl
  in V.foldl' f 0 samples

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
      -> Data.Vector.Unboxed.Vector (Double, Double)
wsFit range seed k =
  let rolls :: RandomGen g => g -> Data.Vector.Unboxed.Vector Double
      rolls = V.unfoldrExactN k (first realToFrac . uniformR range)
      (g1, g2) = split $ mkStdGen seed
  in V.zip (rolls g1) (rolls g2)

-- Here a huge separation is ensured.
wsFitSeparated :: (Double, Double) -> Int -> Int
               -> Data.Vector.Unboxed.Vector (Double, Double)
wsFitSeparated range@(low, hi) seed k =
  let rolls :: RandomGen g => g -> Data.Vector.Unboxed.Vector Double
      rolls = V.unfoldrExactN k (uniformR range)
      width = hi - low
      steps = V.generate k (\n ->
        low + fromIntegral n * width / (fromIntegral k - 1))
      g = mkStdGen seed
  in V.zip steps (rolls g)

-- Some tests here fail due to not smart enough gradient descent
-- (overshooting, mostly).
fitTests :: TestTree
fitTests = testGroup "Sample fitting fully connected neural net tests"
  [ testCase "wsFit (-1, 1) 42 10" $
      V.toList (wsFit (-1, 1) 42 20) @?= [(-0.22217941284179688,-0.5148218870162964),(0.25622618198394775,0.42662060260772705),(7.794177532196045e-2,-0.5301129817962646),(0.384537935256958,0.8958269357681274),(-0.6027946472167969,-0.5425337553024292),(0.4734766483306885,0.19495820999145508),(0.3921601474285126,0.8963258266448975),(-2.679157257080078e-2,-0.43389952182769775),(-8.326125144958496e-2,-0.17110145092010498),(-6.933605670928955e-2,-0.6602561473846436),(-0.7554467916488647,0.9077622890472412),(-0.17885446548461914,0.14958932995796204),(-0.49340176582336426,0.13965561985969543),(0.4703446626663208,-0.487585186958313),(-0.37681376934051514,-0.39065873622894287),(-0.9820539951324463,-0.10905027389526367),(0.6628230810165405,0.11808493733406067),(4.337519407272339e-3,-7.50422477722168e-3),(-0.270332932472229,0.9103447198867798),(2.815529704093933e-2,-0.9941539764404297)]
  , testCase "tanhAct tanhAct (-1, 1) 42 8 31 0.1 10000" $ do
      let samples = wsFit (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.1 (nnFitLossTotal tanhAct tanhAct samples)
                        vec 10000)
        @?= 1.6225349272445413e-2
  , testCase "tanhAct tanhAct (-1, 1) 42 10 31 0.01 100000 failed" $ do
      let samples = wsFit (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFitLossTotal tanhAct tanhAct samples)
                        vec 100000)  -- even 61 1000000 was not enough
        @?= 0.11821681957239855
  , testCase "wsFitSeparated (-1, 1) 42 10" $
      V.toList (wsFitSeparated (-1, 1) 42 20) @?= [(-1.0,0.8617048050432681),(-0.8947368421052632,-0.12944690839124995),(-0.7894736842105263,0.7709385349363602),(-0.6842105263157895,0.7043981517795999),(-0.5789473684210527,0.5002907568304664),(-0.4736842105263158,-0.20067467322001753),(-0.368421052631579,-5.526582421799997e-2),(-0.26315789473684215,0.3006213813725571),(-0.1578947368421053,0.12350686811659489),(-5.2631578947368474e-2,-0.7621608299731257),(5.263157894736836e-2,-3.550743010902346e-2),(0.1578947368421053,-0.32868601453242263),(0.26315789473684204,0.7784360517385773),(0.368421052631579,-0.6715107907491862),(0.4736842105263157,-0.41971965075782536),(0.5789473684210527,-0.4920995297212283),(0.6842105263157894,-0.8809132509345221),(0.7894736842105263,-7.615997455596313e-2),(0.894736842105263,0.36412224491658224),(1.0,-0.31352088018219515)]
  , testCase "Separated (-1, 1) 42 8 31 0.1 10000 failed" $ do
      let samples = wsFitSeparated (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.1 (nnFitLossTotal tanhAct tanhAct samples)
                        vec 10000)
        @?= 0.3884360171054549
  , testCase "Separated (-1, 1) 42 10 31 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFitLossTotal tanhAct tanhAct samples)
                        vec 100000)
        @?= 1.9817301995554423e-2
  , testCase "Separated (-1, 1) 42 16 31 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 16
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFitLossTotal tanhAct tanhAct samples)
                        vec 100000)
        @?= 6.88603932297595e-2
  ]

middleLayerFit2 :: forall r. Num r
                => (r -> r)
                -> Domain r
                -> Int
                -> Domain r
                -> Domain r
middleLayerFit2 factivation hiddenVec offset vec =
  let f :: Int -> r -> r
      f i x =
        let weight = var (offset + 2 * i) vec
            bias = var (offset + 1 + 2 * i) vec
            sx = x * weight
            sxBias = sx + bias
        in factivation sxBias
  in V.imap f hiddenVec

nnFit2 :: Num r
       => (r -> r)
       -> (r -> r)
       -> (r -> r)
       -> r -> Domain r -> r
nnFit2 factivationHidden factivationMiddle factivationOutput x vec =
  -- One bias of the outer layer, a list of weights of the outer layer,
  -- a list of the same length of weights and biases of the hidden layer.
  let width = (V.length vec - 1) `div` 5
      hiddenVec = hiddenLayerFit factivationHidden x vec width
      middleVec = middleLayerFit2 factivationMiddle hiddenVec (2 * width) vec
  in outputLayerFit factivationOutput middleVec (4 * width) vec

nnFit2Loss :: Num r
           => (r -> r)
           -> (r -> r)
           -> (r -> r)
           -> r -> r -> Domain r -> r
nnFit2Loss factivationHidden factivationMiddle factivationOutput x res vec =
  let r = nnFit2 factivationHidden factivationMiddle factivationOutput x vec
  in lossSquared r res

nnFit2LossTotal :: forall s. Reifies s Tape
                => (ReverseDouble s -> ReverseDouble s)
                -> (ReverseDouble s -> ReverseDouble s)
                -> (ReverseDouble s -> ReverseDouble s)
                -> Data.Vector.Unboxed.Vector (Double, Double)
                -> Domain (ReverseDouble s)
                -> (ReverseDouble s)
nnFit2LossTotal factivationHidden factivationMiddle factivationOutput
                samples vec =
  let f :: ReverseDouble s -> (Double, Double) -> ReverseDouble s
      f !acc (x, res) =
        let fl =
              nnFit2Loss factivationHidden factivationMiddle factivationOutput
                         (auto x) (auto res) vec
        in acc + fl
  in V.foldl' f 0 samples

-- Two layers seem to be an advantage for data with points very close
-- together. Otherwise, have all neurons on one layer is more effective.
fit2Tests :: TestTree
fit2Tests = testGroup "Sample fitting 2 hidden layer fc nn tests"
  [ testCase "tanhAct tanhAct (-1, 1) 42 8 31 0.1 10000" $ do
      let samples = wsFit (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.1 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 10000)
        @?= 1.2856619684390336e-2
  , testCase "tanhAct tanhAct (-1, 1) 42 10 31 0.01 400000" $ do
      let samples = wsFit (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 400000)
        @?= 3.835053990072211e-2
  , testCase "Separated (-1, 1) 42 8 31 0.1 10000 failed" $ do
      let samples = wsFitSeparated (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.1 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 10000)
        @?= 0.31692351465375723
  , testCase "Separated (-1, 1) 42 10 31 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 100000)
        @?= 1.2308485318049472e-3
  , testCase "Separated (-1, 1) 42 16 61 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 16
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 100000)
        @?= 1.9398514673723763e-2
  ]

-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
--
-- The ad package tests took 4 to 12 times more runtime that corresponding
-- main tests, which is mysterious and prompted a trade-off optimization.
-- Namely, loosing polymorphism and make Float test impossible,
-- this code is rewritten from @Reverse@ (that leaks memory and/or
-- doesn't unbox) to @ReverseDouble@.
--
-- The below had to be coded, because @gradientDescent@ from ad doesn't work
-- with @ReverseDouble@. Also, the original @gradientDescent@ allocates
-- lots of thunks so is leak suspect, too.
-- Even after switching to @ReverseDouble@ and coding this @gradDescSmart@,
-- the ad tests GC a lot and also use gigabytes of RAM at a time,
-- while the non-ad tests GC less (but still a lot) and use megabytes
-- in analogous code. Perhaps it's just the allocation of lots of symbols
-- in ad, compared to only tiny deltas in main code.
gradDescSmart :: (forall s. Reifies s Tape
                  => Domain (ReverseDouble s) -> ReverseDouble s)
              -> Int
              -> Domain Double
              -> (Domain' Double, Double)
gradDescSmart f n0 params0 = go n0 params0 0.1 gradient0 value0 0 where
  (value0, gradient0) = grad' f params0
  go :: Int -> Domain Double -> Double -> Domain Double -> Double -> Int
     -> (Domain' Double, Double)
  go 0 !params !gamma _gradientPrev _valuePrev !_i = (params, gamma)
  go _ params 0 _ _ _ = (params, 0)
  go n params gamma gradientPrev valuePrev i =
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let paramsNew = V.zipWith (\p r -> p - gamma * r) params gradientPrev
        (value, gradient) = grad' f paramsNew
    in if | V.all (== 0) gradientPrev -> (params, gamma)
          | value > valuePrev ->
              go n params (gamma / 2) gradientPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) paramsNew (gamma * 2) gradient value 0
          | otherwise -> go (pred n) paramsNew gamma gradient value (i + 1)

gradDescSmartShow :: (forall s. Reifies s Tape
                      => Domain (ReverseDouble s) -> ReverseDouble s)
                  -> Domain Double
                  -> Int
                  -> ([Double], (Double, Double))
gradDescSmartShow f initVec n =
  let (res, gamma) = gradDescSmart f n initVec
      (value, _) = grad' f res
  in (V.toList res, (value, gamma))

-- With Float, the approximation overshoots all the time and makes smaller
-- and smaller steps, getting nowhere. This probably means
-- approximation with this number of neurons is not possible.
-- However, adding neurons doesn't help (without huge increases of iterations).
-- The fact that results are better when freely overshooting
-- suggests there are local minima, which confirms too low dimensionality.
-- The experiments with separated samples seem to confirm both hypotheses.
--
-- With Double, it scales well to twice as many samples or even more,
-- but it takes too long to verify when errors crop in again.
smartFitTests :: TestTree
smartFitTests = testGroup "Smart descent sample fitting fc nn tests"
  [ testCase "tanhAct tanhAct (-1, 1) 42 8 31 10000" $ do
      let samples = wsFit (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 10000)
        @?= (2.0585450568797953e-3,1.25e-2)
  , testCase "tanhAct tanhAct (-1, 1) 42 10 61 1000000" $ do
      let samples = wsFit (-1, 1) 42 10
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 1000000)  -- 31 not enough, 700000 not enough
        @?= (9.072288039580448e-2,6.25e-3)
  , testCase "tanhAct tanhAct (-1, 1) 42 16 61 1700000" $ do
      let samples = wsFit (-1, 1) 42 16
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 1700000)
        @?= (4.8336260347113275e-2,1.5625e-3)
  , testCase "Separated (-1, 1) 42 8 31 10000" $ do
      let samples = wsFitSeparated (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 10000)
        @?= (1.5742022677967708e-2,2.5e-2)
  , testCase "Separated (-1, 1) 42 10 31 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 100000)
        @?= (4.506881373306206e-10,2.5e-2)
  , testCase "Separated (-1, 1) 42 16 31 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 16
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 100000)
        @?= (5.197706771219677e-2,6.25e-3)
  , testCase "Separated (-1, 1) 42 24 101 700000" $ do
      let samples = wsFitSeparated (-1, 1) 42 24
          vec = V.unfoldrExactN 101 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 700000)  -- 61 1300000 not enough
        @?= (2.967249104936791e-2,6.25e-3)
  , testCase "Separated (-1, 1) 42 32 61 1700000" $ do
      let samples = wsFitSeparated (-1, 1) 42 32
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 1700000)
        @?= (3.828456463288314e-2,6.25e-3)
        -- 151 1000000 not enough, despite taking twice longer
  ]

smartFit2Tests :: TestTree
smartFit2Tests =
 testGroup "Smart descent sample fitting 2 hidden layer fc nn tests"
  [ testCase "tanhAct tanhAct (-1, 1) 42 8 31 10000" $ do
      let samples = wsFit (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 10000)
        @?= (4.896924209457198e-3,2.5e-2)
  , testCase "tanhAct tanhAct (-1, 1) 42 10 31 400000" $ do
      let samples = wsFit (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 400000)
        @?= (8.470989419560765e-2,2.5e-2)
  , testCase "tanhAct tanhAct (-1, 1) 42 16 61 700000" $ do
      let samples = wsFit (-1, 1) 42 16
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 700000)
        @?= (5.149610997592684e-2,3.90625e-4)
        -- 61 1000000 not enough for 20, 101 700000 enough
  , testCase "Separated (-1, 1) 42 8 31 10000" $ do
      let samples = wsFitSeparated (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 10000)
        @?= (1.832621758590325e-2,1.25e-2)
  , testCase "Separated (-1, 1) 42 10 31 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 100000)
        @?= (2.6495249749522148e-2,3.125e-3)
  , testCase "Separated (-1, 1) 42 16 61 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 16
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 100000)
        @?= (1.8617700399788891e-3,3.125e-3)
  , testCase "Separated (-1, 1) 42 24 61 1300000" $ do
      let samples = wsFitSeparated (-1, 1) 42 24
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 1300000)
        @?= (1.0411445668840221e-2,3.125e-3)
        -- this faster, but less accurate than 101 1000000
        -- 151 700000 is not enough
  ]
