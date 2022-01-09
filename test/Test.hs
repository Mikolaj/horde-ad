module Main (main) where

import Prelude

import           Control.Arrow (first)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit

import AD

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [ dfTests
                          , gradDescTests
                          , xorTests
                          , fitTests
                          , fit2Tests
                          , smartFitTests
                          , smartFit2Tests
                          , smartFit3Tests
                          ]

dfShow :: (VecDualDeltaF -> DeltaMonadF DualDeltaF)
       -> [Float]
       -> ([Float], Float)
dfShow f deltaInput =
  let (results, value) = df f (V.fromList deltaInput)
  in (V.toList results, value)

gradDescShow :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
             => r
             -> (VecDualDelta r -> DeltaMonad r (DualDelta r))
             -> Domain r
             -> Int
             -> ([r], r)
gradDescShow gamma f initVec n =
  let res = gradDesc gamma f n initVec
      (_, value) = df f res
  in (V.toList res, value)

fX :: VecDualDeltaF -> DeltaMonadF DualDeltaF
fX vec = do
  let x = var 0 vec
  return x

fX1Y :: VecDualDeltaF -> DeltaMonadF DualDeltaF
fX1Y vec = do
  let x = var 0 vec
      y = var 1 vec
  x1 <- x +\ scalar 1
  x1 *\ y

fXXY :: VecDualDeltaF -> DeltaMonadF DualDeltaF
fXXY vec = do
  let x = var 0 vec
      y = var 1 vec
  xy <- x *\ y
  x *\ xy

fXYplusZ :: VecDualDeltaF -> DeltaMonadF DualDeltaF
fXYplusZ vec = do
  let x = var 0 vec
      y = var 1 vec
      z = var 2 vec
  xy <- x *\ y
  xy +\ z

fXtoY :: VecDualDeltaF -> DeltaMonadF DualDeltaF
fXtoY vec = do
  let x = var 0 vec
      y = var 1 vec
  x **\ y

freluX :: VecDualDeltaF -> DeltaMonadF DualDeltaF
freluX vec = do
  let x = var 0 vec
  reluAct x

fquad :: VecDualDeltaF -> DeltaMonadF DualDeltaF
fquad vec = do
  let x = var 0 vec
      y = var 1 vec
  x2 <- x *\ x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ scalar 5

fblowup :: VecDualDeltaF -> DeltaMonadF DualDeltaF
fblowup vec = do
  let blowup :: Int -> DualDeltaF -> DeltaMonadF DualDeltaF
      blowup 0 y = return y
      blowup n y = do
        ysum <- y +\ y
        yscaled <- scale 0.499999985 ysum  -- otherwise, we'd get NaN at once
        blowup (pred n) yscaled
  y0 <- fquad vec
  blowup 100 y0

dfTests :: TestTree
dfTests = testGroup "Simple df application tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ dfShow f v @?= expected)
    [ ("fX", fX, [99], ([1.0],99.0))
    , ("fX1Y", fX1Y, [3, 2], ([2.0,4.0],8.0))
    , ("fXXY", fXXY, [3, 2], ([12.0,9.0],18.0))
    , ("fXYplusZ", fXYplusZ, [1, 2, 3], ([2.0,1.0,1.0],5.0))
    , ( "fXtoY", fXtoY, [0.00000000000001, 2]
      , ([2.0e-14,-3.2236188e-27],9.9999994e-29) )
    , ("fXtoY2", fXtoY, [1, 2], ([2.0,0.0],1.0))
    , ("freluX", freluX, [-1], ([0.0],0.0))
    , ("freluX2", freluX, [0], ([0.0],0.0))
    , ("freluX3", freluX, [0.0001], ([1.0],1.0e-4))
    , ("freluX4", freluX, [99], ([1.0],99.0))
    , ("fquad", fquad, [2, 3], ([4.0,6.0],18.0))
    ]

gradDescTests :: TestTree
gradDescTests = testGroup "Simple gradient descent tests"
  [ testCase "0.1 30"
    $ gradDescShow 0.1 fquad (V.fromList [2, 3]) 30
      @?= ([2.47588e-3,3.7138206e-3],5.00002)
  , testCase "0.01 30"
    $ gradDescShow 0.01 fquad (V.fromList [2, 3]) 30
      @?= ([1.0909687,1.6364527],8.86819)
  , testCase "0.01 300"
    $ gradDescShow 0.01 fquad (V.fromList [2, 3]) 300
      @?= ([4.665013e-3,6.9975173e-3],5.0000706)
  , testCase "0.01 300000"
    $ gradDescShow 0.01 fquad (V.fromList [2, 3]) 300000
      @?= ([3.5e-44,3.5e-44],5.0)
  -- The (no) blowup tests.
  , testCase "blowup 0.1 30"
    $ gradDescShow 0.1 fblowup (V.fromList [2, 3]) 30
      @?= ([2.475991e-3,3.7139843e-3],4.9999723)
  , testCase "blowup 0.01 30"
    $ gradDescShow 0.01 fblowup (V.fromList [2, 3]) 30
      @?= ([1.0909724,1.6364591],8.868124)
  , testCase "blowup 0.01 300"
    $ gradDescShow 0.01 fblowup (V.fromList [2, 3]) 300
      @?= ([4.665179e-3,6.9977706e-3],5.000023)
  , testCase "blowup 0.01 300000"
    $ gradDescShow 0.01 fblowup (V.fromList [2, 3]) 300000
      @?= ([3.5e-44,3.5e-44],4.9999523)
  , testCase "blowup 0.01 3000000"
    $ gradDescShow 0.01 fblowup (V.fromList [2, 3]) 3000000
      @?= ([3.5e-44,3.5e-44],4.9999523)
  ]

scaleAddWithBias :: DualDeltaF -> DualDeltaF -> Int -> VecDualDeltaF
                 -> DeltaMonadF DualDeltaF
scaleAddWithBias x y ixWeight vec = do
  let wx = var ixWeight vec
      wy = var (ixWeight + 1) vec
      bias = var (ixWeight + 2) vec
  sx <- x *\ wx
  sy <- y *\ wy
  sxy <- sx +\ sy
  sxy +\ bias

neuron :: (DualDeltaF -> DeltaMonadF DualDeltaF)
       -> DualDeltaF -> DualDeltaF -> Int -> VecDualDeltaF
       -> DeltaMonadF DualDeltaF
neuron factivation x y ixWeight vec = do
  sc <- scaleAddWithBias x y ixWeight vec
  factivation sc

nnXor :: (DualDeltaF -> DeltaMonadF DualDeltaF)
      -> DualDeltaF -> DualDeltaF -> VecDualDeltaF
      -> DeltaMonadF DualDeltaF
nnXor factivation x y vec = do
  n1 <- neuron factivation x y 0 vec
  n2 <- neuron factivation x y 3 vec
  neuron factivation n1 n2 6 vec

lossSquared :: Num r => DualDelta r -> r -> DeltaMonad r (DualDelta r)
lossSquared u res = do
  diff <- u -\ scalar res
  diff *\ diff

nnXorLoss :: (DualDeltaF -> DeltaMonadF DualDeltaF)
          -> Float -> Float -> Float -> VecDualDeltaF
          -> DeltaMonadF DualDeltaF
nnXorLoss factivation x y res vec = do
  r <- nnXor factivation (scalar x) (scalar y) vec
  lossSquared r res

nnXorLossTotal :: (DualDeltaF -> DeltaMonadF DualDeltaF)
               -> VecDualDeltaF
               -> DeltaMonadF DualDeltaF
nnXorLossTotal factivation vec = do
  n1 <- nnXorLoss factivation 0 0 0 vec
  n2 <- nnXorLoss factivation 0 1 1 vec
  n3 <- nnXorLoss factivation 1 0 1 vec
  n4 <- nnXorLoss factivation 1 1 0 vec
  n12 <- n1 +\ n2
  n34 <- n3 +\ n4
  n12 +\ n34

ws, ws2 :: Domain Float
ws = let w = [0.37, 0.28, 0.19] in V.fromList $ w ++ w ++ w
ws2 = let w = [-1.37, 2.28, -0.19] in V.fromList $ w ++ w ++ w

xorTests :: TestTree
xorTests = testGroup "XOR neural net tests"
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

hiddenLayerFit :: (DualDeltaD -> DeltaMonadD DualDeltaD)
               -> Double
               -> VecDualDeltaD
               -> Int
               -> DeltaMonadD (Data.Vector.Vector DualDeltaD)
hiddenLayerFit factivation x vec width = do
  let f :: Int -> DeltaMonadD DualDeltaD
      f i = do
        let weight = var (2 * i) vec
            bias = var (2 * i + 1) vec
        sx <- scale x weight
        sxBias <- sx +\ bias
        factivation sxBias
  V.generateM width f

outputLayerFit :: (DualDeltaD -> DeltaMonadD DualDeltaD)
               -> Data.Vector.Vector DualDeltaD
               -> Int
               -> VecDualDeltaD
               -> DeltaMonadD DualDeltaD
outputLayerFit factivation hiddenVec offset vec = do
  outSum <- scaleAddVecWithBias hiddenVec offset vec
  factivation outSum

nnFit :: (DualDeltaD -> DeltaMonadD DualDeltaD)
      -> (DualDeltaD -> DeltaMonadD DualDeltaD)
      -> Double -> VecDualDeltaD -> DeltaMonadD DualDeltaD
nnFit factivationHidden factivationOutput x vec = do
  -- One bias of the outer layer, a list of weights of the outer layer,
  -- a list of the same length of weights and biases of the hidden layer.
  let width = (V.length (fst vec) - 1) `div` 3
  hiddenVec <- hiddenLayerFit factivationHidden x vec width
  outputLayerFit factivationOutput hiddenVec (2 * width) vec

nnFitLoss :: (DualDeltaD -> DeltaMonadD DualDeltaD)
          -> (DualDeltaD -> DeltaMonadD DualDeltaD)
          -> Double -> Double -> VecDualDeltaD -> DeltaMonadD DualDeltaD
nnFitLoss factivationHidden factivationOutput x res vec = do
  r <- nnFit factivationHidden factivationOutput x vec
  lossSquared r res

nnFitLossTotal :: (DualDeltaD -> DeltaMonadD DualDeltaD)
               -> (DualDeltaD -> DeltaMonadD DualDeltaD)
               -> Data.Vector.Unboxed.Vector (Double, Double)
               -> VecDualDeltaD
               -> DeltaMonadD DualDeltaD
nnFitLossTotal factivationHidden factivationOutput samples vec = do
  let f :: DualDeltaD -> (Double, Double) -> DeltaMonadD DualDeltaD
      f (D acc acc') (x, res) = do
        D fl fl' <- nnFitLoss factivationHidden factivationOutput x res vec
        return $! D (acc + fl) (Add acc' fl')
  V.foldM' f (scalar 0) samples

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

gradDescTestCase :: Num a
                 => String
                 -> ((a, a) -> Int -> Int
                     -> Data.Vector.Unboxed.Vector (Double, Double))
                 -> ((DualDeltaD -> DeltaMonadD DualDeltaD)
                     -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                     -> Data.Vector.Unboxed.Vector (Double, Double)
                     -> VecDualDeltaD
                     -> DeltaMonadD DualDeltaD)
                 -> Int -> Int -> Int -> Double -> Int -> Double
                 -> TestTree
gradDescTestCase prefix sampleFunction lossFunction
                 seedSamples nSamples nParams gamma nIterations expected =
  let samples = sampleFunction (-1, 1) seedSamples nSamples
      vec = V.unfoldrExactN nParams (uniformR (-1, 1)) $ mkStdGen 33
      name = prefix ++ " "
             ++ unwords [ show seedSamples, show nSamples
                        , show nParams, show gamma, show nIterations ]
  in testCase name $
       snd (gradDescShow gamma (lossFunction tanhAct tanhAct samples)
                         vec nIterations)
       @?= expected

gradDescWsTestCase :: ((DualDeltaD -> DeltaMonadD DualDeltaD)
                       -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                       -> Data.Vector.Unboxed.Vector (Double, Double)
                       -> VecDualDeltaD
                       -> DeltaMonadD DualDeltaD)
                   -> Int -> Int -> Int -> Double -> Int -> Double
                   -> TestTree
gradDescWsTestCase = gradDescTestCase "gradDesc Ws" wsFit

gradDescSeparatedTestCase :: ((DualDeltaD -> DeltaMonadD DualDeltaD)
                              -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                              -> Data.Vector.Unboxed.Vector (Double, Double)
                              -> VecDualDeltaD
                              -> DeltaMonadD DualDeltaD)
                          -> Int -> Int -> Int -> Double -> Int -> Double
                          -> TestTree
gradDescSeparatedTestCase = gradDescTestCase "gradDesc Separated" wsFitSeparated

lenP :: Int -> Int
lenP width = 3 * width + 1

-- Some tests here fail due to not smart enough gradient descent
-- (overshooting, mostly).
fitTests :: TestTree
fitTests = testGroup "Sample fitting fully connected neural net tests"
  [ testCase "wsFit (-1, 1) 42 10" $
      V.toList (wsFit (-1, 1) 42 20) @?= [(-0.22217941284179688,-0.5148218870162964),(0.25622618198394775,0.42662060260772705),(7.794177532196045e-2,-0.5301129817962646),(0.384537935256958,0.8958269357681274),(-0.6027946472167969,-0.5425337553024292),(0.4734766483306885,0.19495820999145508),(0.3921601474285126,0.8963258266448975),(-2.679157257080078e-2,-0.43389952182769775),(-8.326125144958496e-2,-0.17110145092010498),(-6.933605670928955e-2,-0.6602561473846436),(-0.7554467916488647,0.9077622890472412),(-0.17885446548461914,0.14958932995796204),(-0.49340176582336426,0.13965561985969543),(0.4703446626663208,-0.487585186958313),(-0.37681376934051514,-0.39065873622894287),(-0.9820539951324463,-0.10905027389526367),(0.6628230810165405,0.11808493733406067),(4.337519407272339e-3,-7.50422477722168e-3),(-0.270332932472229,0.9103447198867798),(2.815529704093933e-2,-0.9941539764404297)]
  , gradDescWsTestCase
      nnFitLossTotal 42 8 (lenP 10) 0.1 10000 1.6225349272445413e-2
  , gradDescWsTestCase
      nnFitLossTotal 42 10 (lenP 10) 0.01 100000 0.11821681957239855
      -- failed; even 61 1000000 was not enough
  , testCase "wsFitSeparated (-1, 1) 42 10" $
      V.toList (wsFitSeparated (-1, 1) 42 20) @?= [(-1.0,0.8617048050432681),(-0.8947368421052632,-0.12944690839124995),(-0.7894736842105263,0.7709385349363602),(-0.6842105263157895,0.7043981517795999),(-0.5789473684210527,0.5002907568304664),(-0.4736842105263158,-0.20067467322001753),(-0.368421052631579,-5.526582421799997e-2),(-0.26315789473684215,0.3006213813725571),(-0.1578947368421053,0.12350686811659489),(-5.2631578947368474e-2,-0.7621608299731257),(5.263157894736836e-2,-3.550743010902346e-2),(0.1578947368421053,-0.32868601453242263),(0.26315789473684204,0.7784360517385773),(0.368421052631579,-0.6715107907491862),(0.4736842105263157,-0.41971965075782536),(0.5789473684210527,-0.4920995297212283),(0.6842105263157894,-0.8809132509345221),(0.7894736842105263,-7.615997455596313e-2),(0.894736842105263,0.36412224491658224),(1.0,-0.31352088018219515)]
  , gradDescSeparatedTestCase
      nnFitLossTotal 42 8 (lenP 10) 0.1 10000 0.3884360171054549
  , gradDescSeparatedTestCase
      nnFitLossTotal 42 10 (lenP 10) 0.01 100000 1.9817301995554423e-2
  , gradDescSeparatedTestCase
      nnFitLossTotal 42 16 (lenP 10) 0.01 100000 6.88603932297595e-2
  ]

-- This connects with only one neuron from the first hidden layer.
-- No wonder the extra hidden layer was not particulary effective
-- compared to wider single hidden layer.
middleLayerFit2 :: (DualDeltaD -> DeltaMonadD DualDeltaD)
                -> Data.Vector.Vector DualDeltaD
                -> Int
                -> VecDualDeltaD
                -> DeltaMonadD (Data.Vector.Vector DualDeltaD)
middleLayerFit2 factivation hiddenVec offset vec = do
  let f :: Int -> DualDeltaD -> DeltaMonadD DualDeltaD
      f i x = do
        let weight = var (offset + 2 * i) vec
            bias = var (offset + 1 + 2 * i) vec
        sx <- x *\ weight
        sxBias <- sx +\ bias
        factivation sxBias
  V.imapM f hiddenVec

nnFit2 :: (DualDeltaD -> DeltaMonadD DualDeltaD)
       -> (DualDeltaD -> DeltaMonadD DualDeltaD)
       -> (DualDeltaD -> DeltaMonadD DualDeltaD)
       -> Double -> VecDualDeltaD -> DeltaMonadD DualDeltaD
nnFit2 factivationHidden factivationMiddle factivationOutput x vec = do
  -- Due to not being fully connected, the parameters are only:
  -- one bias of the outer layer, a list of weights of the outer layer,
  -- a list of the same length of weights and biases of the first hidden layer
  -- and of the middle hidden layer.
  let width = (V.length (fst vec) - 1) `div` 5
  hiddenVec <- hiddenLayerFit factivationHidden x vec width
  middleVec <- middleLayerFit2 factivationMiddle hiddenVec (2 * width) vec
  outputLayerFit factivationOutput middleVec (4 * width) vec

nnFit2Loss :: (DualDeltaD -> DeltaMonadD DualDeltaD)
           -> (DualDeltaD -> DeltaMonadD DualDeltaD)
           -> (DualDeltaD -> DeltaMonadD DualDeltaD)
           -> Double -> Double -> VecDualDeltaD -> DeltaMonadD DualDeltaD
nnFit2Loss factivationHidden factivationMiddle factivationOutput x res vec = do
  r <- nnFit2 factivationHidden factivationMiddle factivationOutput x vec
  lossSquared r res

nnFit2LossTotal :: (DualDeltaD -> DeltaMonadD DualDeltaD)
                -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                -> Data.Vector.Unboxed.Vector (Double, Double)
                -> VecDualDeltaD
                -> DeltaMonadD DualDeltaD
nnFit2LossTotal factivationHidden factivationMiddle factivationOutput
                samples vec = do
  let f :: DualDeltaD -> (Double, Double) -> DeltaMonadD DualDeltaD
      f (D acc acc') (x, res) = do
        D fl fl' <-
          nnFit2Loss factivationHidden factivationMiddle factivationOutput
                     x res vec
        return $! D (acc + fl) (Add acc' fl')
  V.foldM' f (scalar 0) samples

lenP2 :: Int -> Int
lenP2 width = 5 * width + 1

-- Two layers seem to be an advantage for data with points very close
-- together. Otherwise, having all neurons on one layer is more effective.
fit2Tests :: TestTree
fit2Tests = testGroup "Sample fitting 2 hidden layer not fully connected nn tests"
  [ gradDescWsTestCase
      (nnFit2LossTotal tanhAct) 42 8 (lenP2 6) 0.1 10000
      1.2856619684390336e-2
  , gradDescWsTestCase
      (nnFit2LossTotal tanhAct) 42 10 (lenP2 6) 0.01 400000
      3.835053990072211e-2
  , gradDescSeparatedTestCase
      (nnFit2LossTotal tanhAct) 42 8 (lenP2 6) 0.1 10000
      0.31692351465375723
  , gradDescSeparatedTestCase
      (nnFit2LossTotal tanhAct) 42 10 (lenP2 6) 0.01 100000
      1.2308485318049472e-3
  , gradDescSeparatedTestCase
      (nnFit2LossTotal tanhAct) 42 16 (lenP2 12) 0.01 100000
      1.9398514673723763e-2
  ]

gradDescSmartShow :: (VecDualDeltaD -> DeltaMonadD DualDeltaD)
                  -> Domain Double
                  -> Int
                  -> ([Double], (Double, Double))
gradDescSmartShow f initVec n =
  let (res, gamma) = gradDescSmart f n initVec
      (_, value) = df f res
  in (V.toList res, (value, gamma))

gradSmartTestCase :: Num a
                  => String
                  -> ((a, a) -> Int -> Int
                      -> Data.Vector.Unboxed.Vector (Double, Double))
                  -> ((DualDeltaD -> DeltaMonadD DualDeltaD)
                      -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                      -> Data.Vector.Unboxed.Vector (Double, Double)
                      -> VecDualDeltaD
                      -> DeltaMonadD DualDeltaD)
                  -> Int -> Int -> Int -> Int -> (Double, Double)
                  -> TestTree
gradSmartTestCase prefix sampleFunction lossFunction
                  seedSamples nSamples nParams nIterations expected =
  let samples = sampleFunction (-1, 1) seedSamples nSamples
      vec = V.unfoldrExactN nParams (uniformR (-1, 1)) $ mkStdGen 33
      name = prefix ++ " "
             ++ unwords [ show seedSamples, show nSamples
                        , show nParams, show nIterations ]
  in testCase name $
       snd (gradDescSmartShow (lossFunction tanhAct tanhAct samples)
                              vec nIterations)
       @?= expected

gradSmartWsTestCase :: ((DualDeltaD -> DeltaMonadD DualDeltaD)
                        -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                        -> Data.Vector.Unboxed.Vector (Double, Double)
                        -> VecDualDeltaD
                        -> DeltaMonadD DualDeltaD)
                    -> Int -> Int -> Int -> Int -> (Double, Double)
                    -> TestTree
gradSmartWsTestCase = gradSmartTestCase "gradSmart Ws" wsFit

gradSmartSeparatedTestCase :: ((DualDeltaD -> DeltaMonadD DualDeltaD)
                               -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                               -> Data.Vector.Unboxed.Vector (Double, Double)
                               -> VecDualDeltaD
                               -> DeltaMonadD DualDeltaD)
                           -> Int -> Int -> Int -> Int
                           -> (Double, Double)
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
      (nnFit2LossTotal tanhAct) 42 8 (lenP2 6) 10000
      (4.896924209457198e-3,2.5e-2)
  , gradSmartWsTestCase
      (nnFit2LossTotal tanhAct) 42 10 (lenP2 6) 400000
      (8.470989419560765e-2,2.5e-2)
  , gradSmartWsTestCase
      (nnFit2LossTotal tanhAct) 42 16 (lenP2 12) 700000
      (5.149610997592684e-2,3.90625e-4)
        -- 61 1000000 not enough for 20, 101 700000 enough
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal tanhAct) 42 8 (lenP2 6) 10000
      (1.832621758590325e-2,1.25e-2)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal tanhAct) 42 10 (lenP2 6) 100000
      (2.6495249749522148e-2,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal tanhAct) 42 16 (lenP2 12) 100000
      (1.8617700399788891e-3,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit2LossTotal tanhAct) 42 24 (lenP2 12) 1300000
      (1.0411445668840221e-2,3.125e-3)
        -- this is faster but less accurate than 101 1000000
        -- 151 700000 is not enough
  ]

-- This is really fully connected.
middleLayerFit3 :: (DualDeltaD -> DeltaMonadD DualDeltaD)
                -> Data.Vector.Vector DualDeltaD
                -> Int
                -> VecDualDeltaD
                -> DeltaMonadD (Data.Vector.Vector DualDeltaD)
middleLayerFit3 factivation hiddenVec offset vec = do
  let width = V.length hiddenVec
      nWeightsAndBias = width + 1
      f :: Int -> DeltaMonadD DualDeltaD
      f i = do
        outSum <- scaleAddVecWithBias hiddenVec
                                      (offset + i * nWeightsAndBias)
                                      vec
        factivation outSum
  V.generateM width f

nnFit3 :: (DualDeltaD -> DeltaMonadD DualDeltaD)
       -> (DualDeltaD -> DeltaMonadD DualDeltaD)
       -> (DualDeltaD -> DeltaMonadD DualDeltaD)
       -> Double -> VecDualDeltaD -> DeltaMonadD DualDeltaD
nnFit3 factivationHidden factivationMiddle factivationOutput x vec = do
  -- This is fully connected, so given width w, the number of parameters is:
  -- one bias of the outer layer, a list of weights of the outer layer
  -- of length w, a list of the same length of weights and biases of the first
  -- hidden layer, w * w weigths in the middle hidden layer and w biases.
  -- In total, #params == 1 + w + 2 * w + w^2 + w == w^2 + 4 * w + 1,
  -- so the equation to solve is w^2 + 4 * w + (1 - #params) = 0.
  -- Length 31 gives almost 3. Length 61 gives exactly 6.
  let len :: Double
      len = fromIntegral $ V.length (fst vec)  -- #params
      width = floor $ (-4 + sqrt (12 + 4 * len)) / 2
  hiddenVec <- hiddenLayerFit factivationHidden x vec width
  middleVec <- middleLayerFit3 factivationMiddle hiddenVec (2 * width) vec
  outputLayerFit factivationOutput middleVec ((3 + width) * width) vec

nnFit3Loss :: (DualDeltaD -> DeltaMonadD DualDeltaD)
           -> (DualDeltaD -> DeltaMonadD DualDeltaD)
           -> (DualDeltaD -> DeltaMonadD DualDeltaD)
           -> Double -> Double -> VecDualDeltaD -> DeltaMonadD DualDeltaD
nnFit3Loss factivationHidden factivationMiddle factivationOutput x res vec = do
  r <- nnFit3 factivationHidden factivationMiddle factivationOutput x vec
  lossSquared r res

nnFit3LossTotal :: (DualDeltaD -> DeltaMonadD DualDeltaD)
                -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                -> (DualDeltaD -> DeltaMonadD DualDeltaD)
                -> Data.Vector.Unboxed.Vector (Double, Double)
                -> VecDualDeltaD
                -> DeltaMonadD DualDeltaD
nnFit3LossTotal factivationHidden factivationMiddle factivationOutput
                samples vec = do
  let f :: DualDeltaD -> (Double, Double) -> DeltaMonadD DualDeltaD
      f (D acc acc') (x, res) = do
        D fl fl' <-
          nnFit3Loss factivationHidden factivationMiddle factivationOutput
                     x res vec
        return $! D (acc + fl) (Add acc' fl')
  V.foldM' f (scalar 0) samples

lenP3 :: Int -> Int
lenP3 width = (4 + width) * width + 1

smartFit3Tests :: TestTree
smartFit3Tests =
 testGroup "Smart descent sample fitting 2 hidden layer really fully connected nn tests"
  -- The same (or slightly lower) number of parameters, but on many layers
  -- gives much worse results, except if there are few samples.
  -- It is also less costly for some reason.
  [ gradSmartWsTestCase
      (nnFit3LossTotal tanhAct) 42 8 (lenP3 4) 10000
      (3.5604072240265575e-3,2.5e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotal tanhAct) 42 10 (lenP3 4) 400000
      (0.10126792765437645,3.125e-3)
        -- failed, because too narrow (4 neurons in each hidden layer)
  , gradSmartWsTestCase
      (nnFit3LossTotal tanhAct) 42 16 (lenP3 6) 700000
      (0.19318876323310907,1.5625e-3)
        -- failed, because too narrow (6 neurons in each hidden layer)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanhAct) 42 8 (lenP3 4) 10000
      (6.291648505851797e-3,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanhAct) 42 10 (lenP3 4) 100000
      (4.34890234424764e-7,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanhAct) 42 16 (lenP3 6) 100000
      (0.3434691592146121,1.5625e-3)
        -- failed, because too narrow (6 neurons in each hidden layer)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanhAct) 42 24 (lenP3 6) 1300000
      (1.665065359469462,9.765625e-5)
        -- failed, because too narrow (6 neurons in each hidden layer)
  -- The same width of fully connected nn, but with 2 instead of 1 hidden
  -- layer has many more parameters and is usually more costly,
  -- but also much more powerful given enough training:
  , gradSmartWsTestCase
      (nnFit3LossTotal tanhAct) 42 8 (lenP3 6) 10000
      (2.1767148242940303e-3,1.25e-2)
  , gradSmartWsTestCase
      (nnFit3LossTotal tanhAct) 42 10 (lenP3 6) 400000
      (1.3871923964300112e-4,6.25e-3)
  , gradSmartWsTestCase
      (nnFit3LossTotal tanhAct) 42 16 (lenP3 12) 700000
      (2.131955325962636e-5,7.8125e-4)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanhAct) 42 8 (lenP3 6) 10000
      (2.0369556559640215e-4,5.0e-2)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanhAct) 42 10 (lenP3 6) 100000
      (4.0282344474667426e-16,6.25e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanhAct) 42 16 (lenP3 12) 100000
      (1.5819824634756573e-5,3.125e-3)
  , gradSmartSeparatedTestCase
      (nnFit3LossTotal tanhAct) 42 24 (lenP3 12) 1300000
      (1.1354796858869852e-6,1.5625e-3)
  ]
