module Main (main) where

import Prelude

import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit

import AD

main :: IO ()
main = defaultMain tests

dfShow :: (VecDualDelta -> DeltaMonad DualDelta)
       -> [Float]
       -> ([Float], Float)
dfShow f deltaInput =
  let (results, value) = df f (V.fromList deltaInput)
  in (V.toList results, value)

gradDescShow :: Float
             -> (VecDualDelta -> DeltaMonad DualDelta)
             -> Domain Float
             -> Int
             -> ([Float], Float)
gradDescShow gamma f initVec n =
  let res = V.toList $ gradDesc gamma f n initVec
  in (res, snd $ dfShow f res)

tests :: TestTree
tests = testGroup "Tests" [ dfTests
                          , gradDescTests
                          , xorTests
                          , fitTests
                          , fit2Tests
                          , smartFitTests
                          , smartFit2Tests
                          ]

fX :: VecDualDelta -> DeltaMonad DualDelta
fX vec = do
  let x = var 0 vec
  return x

fX1Y :: VecDualDelta -> DeltaMonad DualDelta
fX1Y vec = do
  let x = var 0 vec
      y = var 1 vec
  x1 <- x +\ scalar 1
  x1 *\ y

fXXY :: VecDualDelta -> DeltaMonad DualDelta
fXXY vec = do
  let x = var 0 vec
      y = var 1 vec
  xy <- x *\ y
  x *\ xy

fXYplusZ :: VecDualDelta -> DeltaMonad DualDelta
fXYplusZ vec = do
  let x = var 0 vec
      y = var 1 vec
      z = var 2 vec
  xy <- x *\ y
  xy +\ z

fXtoY :: VecDualDelta -> DeltaMonad DualDelta
fXtoY vec = do
  let x = var 0 vec
      y = var 1 vec
  x **\ y

freluX :: VecDualDelta -> DeltaMonad DualDelta
freluX vec = do
  let x = var 0 vec
  reluAct x

fquad :: VecDualDelta -> DeltaMonad DualDelta
fquad vec = do
  let x = var 0 vec
      y = var 1 vec
  x2 <- x *\ x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ scalar 5

dfTests :: TestTree
dfTests = testGroup "df application tests" $
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
gradDescTests = testGroup "simple gradDesc tests"
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
  ]

scaleAddWithBias :: DualDelta -> DualDelta -> Int -> VecDualDelta
                 -> DeltaMonad DualDelta
scaleAddWithBias x y ixWeight vec = do
  let wx = var ixWeight vec
      wy = var (ixWeight + 1) vec
      bias = var (ixWeight + 2) vec
  sx <- x *\ wx
  sy <- y *\ wy
  sxy <- sx +\ sy
  sxy +\ bias

neuron :: (DualDelta -> DeltaMonad DualDelta)
       -> DualDelta -> DualDelta -> Int -> VecDualDelta
       -> DeltaMonad DualDelta
neuron factivation x y ixWeight vec = do
  sc <- scaleAddWithBias x y ixWeight vec
  factivation sc

nnXor :: (DualDelta -> DeltaMonad DualDelta)
      -> DualDelta -> DualDelta -> VecDualDelta
      -> DeltaMonad DualDelta
nnXor factivation x y vec = do
  n1 <- neuron factivation x y 0 vec
  n2 <- neuron factivation x y 3 vec
  neuron factivation n1 n2 6 vec

lossSquared :: DualDelta -> Float -> DeltaMonad DualDelta
lossSquared u res = do
  diff <- u -\ (scalar res)
  diff *\ diff

nnXorLoss :: (DualDelta -> DeltaMonad DualDelta)
          -> Float -> Float -> Float -> VecDualDelta
          -> DeltaMonad DualDelta
nnXorLoss factivation x y res vec = do
  r <- nnXor factivation (scalar x) (scalar y) vec
  lossSquared r res

nnXorLossTotal :: (DualDelta -> DeltaMonad DualDelta)
               -> VecDualDelta
               -> DeltaMonad DualDelta
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

hiddenLayerFit :: (DualDelta -> DeltaMonad DualDelta)
               -> Float
               -> VecDualDelta
               -> Int
               -> DeltaMonad (Data.Vector.Vector DualDelta)
hiddenLayerFit factivation x vec width = do
  let f :: Int -> DeltaMonad DualDelta
      f i = do
        let weight = var (2 * i) vec
            bias = var (2 * i + 1) vec
        sx <- scale x weight
        sxBias <- sx +\ bias
        factivation sxBias
  V.generateM width f

outputLayerFit :: (DualDelta -> DeltaMonad DualDelta)
               -> Data.Vector.Vector DualDelta
               -> Int
               -> VecDualDelta
               -> DeltaMonad DualDelta
outputLayerFit factivation hiddenVec offset vec = do
  outSum <- scaleAddVecWithBias hiddenVec offset vec
  factivation outSum

nnFit :: (DualDelta -> DeltaMonad DualDelta)
      -> (DualDelta -> DeltaMonad DualDelta)
      -> Float -> VecDualDelta -> DeltaMonad DualDelta
nnFit factivationHidden factivationOutput x vec = do
  -- One bias of the outer layer, a list of weights of the outer layer,
  -- a list of the same length of weights and biases of the hidden layer.
  let width = (V.length (fst vec) - 1) `div` 3
  hiddenVec <- hiddenLayerFit factivationHidden x vec width
  outputLayerFit factivationOutput hiddenVec (2 * width) vec

nnFitLoss :: (DualDelta -> DeltaMonad DualDelta)
          -> (DualDelta -> DeltaMonad DualDelta)
          -> Float -> Float -> VecDualDelta -> DeltaMonad DualDelta
nnFitLoss factivationHidden factivationOutput x res vec = do
  r <- nnFit factivationHidden factivationOutput x vec
  lossSquared r res

nnFitLossTotal :: (DualDelta -> DeltaMonad DualDelta)
               -> (DualDelta -> DeltaMonad DualDelta)
               -> Data.Vector.Unboxed.Vector (Float, Float)
               -> VecDualDelta
               -> DeltaMonad DualDelta
nnFitLossTotal factivationHidden factivationOutput samples vec = do
  let f :: DualDelta -> (Float, Float) -> DeltaMonad DualDelta
      f (D acc acc') (x, res) = do
        D fl fl' <- nnFitLoss factivationHidden factivationOutput x res vec
        return $! D (acc + fl) (Add acc' fl')
  V.foldM' f (scalar 0) samples

-- We will use this with fixes known good seeds, so we don't care
-- whether any first element of the pair (nearly) repeats,
-- creating (nearly) unsatisfiable samples.
--
-- Alas, this happens too often and is hard to pinpoint
wsFit :: (Float, Float) -> Int -> Int
      -> Data.Vector.Unboxed.Vector (Float, Float)
wsFit range seed k =
  let rolls :: RandomGen g => g -> Data.Vector.Unboxed.Vector Float
      rolls = V.unfoldrExactN k (uniformR range)
      (g1, g2) = split $ mkStdGen seed
  in V.zip (rolls g1) (rolls g2)

wsFitSeparated :: (Float, Float) -> Int -> Int
               -> Data.Vector.Unboxed.Vector (Float, Float)
wsFitSeparated range@(low, hi) seed k =
  let rolls :: RandomGen g => g -> Data.Vector.Unboxed.Vector Float
      rolls = V.unfoldrExactN k (uniformR range)
      width = hi - low
      steps = V.generate k (\n ->
        low + fromIntegral n * width / (fromIntegral k - 1))
      g = mkStdGen seed
  in V.zip steps (rolls g)

fitTests :: TestTree
fitTests = testGroup "Sample fitting fully connected neural net tests"
  [ testCase "wsFit (-1, 1) 42 10" $
      V.toList (wsFit (-1, 1) 42 20) @?= [(-0.22217941,-0.5148219),(0.25622618,0.4266206),(7.7941775e-2,-0.530113),(0.38453794,0.89582694),(-0.60279465,-0.54253376),(0.47347665,0.19495821),(0.39216015,0.8963258),(-2.6791573e-2,-0.43389952),(-8.326125e-2,-0.17110145),(-6.933606e-2,-0.66025615),(-0.7554468,0.9077623),(-0.17885447,0.14958933),(-0.49340177,0.13965562),(0.47034466,-0.4875852),(-0.37681377,-0.39065874),(-0.982054,-0.109050274),(0.6628231,0.11808494),(4.3375194e-3,-7.504225e-3),(-0.27033293,0.9103447),(2.8155297e-2,-0.994154)]
  , testCase "tanhAct tanhAct (-1, 1) 42 7 31 0.1 10000" $ do
      let samples = wsFit (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.1 (nnFitLossTotal tanhAct tanhAct samples) vec 10000)
        @?= 8.1257485e-3
  , testCase "tanhAct tanhAct (-1, 1) 42 9 31 0.01 100000" $ do
      let samples = wsFit (-1, 1) 42 9
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFitLossTotal tanhAct tanhAct samples) vec 100000)
        @?= 1.6422749e-2
  , testCase "tanhAct tanhAct (-1, 1) 42 10 31 0.01 100000" $ do
      -- It seems that more hidden layer neurons that samples doesn't help,
      -- regardless of how long it runs.
      let samples = wsFit (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFitLossTotal tanhAct tanhAct samples) vec 100000)
        @?= 0.11910388  -- 10 seems to be the limit for this data
  , testCase "wsFitSeparated (-1, 1) 42 10" $
      V.toList (wsFitSeparated (-1, 1) 42 20) @?= [(-1.0,-0.533108),(-0.8947368,0.89127314),(-0.78947365,-0.22217941),(-0.68421054,0.25622618),(-0.57894737,7.7941775e-2),(-0.4736842,0.38453794),(-0.36842108,-0.60279465),(-0.2631579,0.47347665),(-0.15789473,0.39216015),(-5.2631557e-2,-2.6791573e-2),(5.2631617e-2,-8.326125e-2),(0.15789473,-6.933606e-2),(0.26315784,-0.7554468),(0.36842108,-0.17885447),(0.4736842,-0.49340177),(0.5789474,0.47034466),(0.68421054,-0.37681377),(0.78947365,-0.982054),(0.8947369,0.6628231),(1.0,4.3375194e-3)]
  , testCase "Separated (-1, 1) 42 7 31 0.1 10000" $ do
      let samples = wsFitSeparated (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.1 (nnFitLossTotal tanhAct tanhAct samples) vec 10000)
        @?= 1.8856211
  , testCase "Separated (-1, 1) 42 9 31 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 9
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFitLossTotal tanhAct tanhAct samples) vec 100000)
        @?= 8.3821e-9
  , testCase "Separated (-1, 1) 42 10 31 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFitLossTotal tanhAct tanhAct samples) vec 100000)
        @?= 1.6819966e-8
  , testCase "Separated (-1, 1) 42 16 31 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 16
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFitLossTotal tanhAct tanhAct samples) vec 100000)
        @?= 0.3413926
  ]

middleLayerFit2 :: (DualDelta -> DeltaMonad DualDelta)
                -> Data.Vector.Vector DualDelta
                -> Int
                -> VecDualDelta
                -> DeltaMonad (Data.Vector.Vector DualDelta)
middleLayerFit2 factivation hiddenVec offset vec = do
  let f :: Int -> DualDelta -> DeltaMonad DualDelta
      f i x = do
        let weight = var (offset + 2 * i) vec
            bias = var (offset + 1 + 2 * i) vec
        sx <- x *\ weight
        sxBias <- sx +\ bias
        factivation sxBias
  V.imapM f hiddenVec

nnFit2 :: (DualDelta -> DeltaMonad DualDelta)
       -> (DualDelta -> DeltaMonad DualDelta)
       -> (DualDelta -> DeltaMonad DualDelta)
       -> Float -> VecDualDelta -> DeltaMonad DualDelta
nnFit2 factivationHidden factivationMiddle factivationOutput x vec = do
  -- One bias of the outer layer, a list of weights of the outer layer,
  -- a list of the same length of weights and biases of the hidden layer.
  let width = (V.length (fst vec) - 1) `div` 5
  hiddenVec <- hiddenLayerFit factivationHidden x vec width
  middleVec <- middleLayerFit2 factivationMiddle hiddenVec (2 * width) vec
  outputLayerFit factivationOutput middleVec (4 * width) vec

nnFit2Loss :: (DualDelta -> DeltaMonad DualDelta)
           -> (DualDelta -> DeltaMonad DualDelta)
           -> (DualDelta -> DeltaMonad DualDelta)
           -> Float -> Float -> VecDualDelta -> DeltaMonad DualDelta
nnFit2Loss factivationHidden factivationMiddle factivationOutput x res vec = do
  r <- nnFit2 factivationHidden factivationMiddle factivationOutput x vec
  lossSquared r res

nnFit2LossTotal :: (DualDelta -> DeltaMonad DualDelta)
                -> (DualDelta -> DeltaMonad DualDelta)
                -> (DualDelta -> DeltaMonad DualDelta)
                -> Data.Vector.Unboxed.Vector (Float, Float)
                -> VecDualDelta
                -> DeltaMonad DualDelta
nnFit2LossTotal factivationHidden factivationMiddle factivationOutput
                samples vec = do
  let f :: DualDelta -> (Float, Float) -> DeltaMonad DualDelta
      f (D acc acc') (x, res) = do
        D fl fl' <-
          nnFit2Loss factivationHidden factivationMiddle factivationOutput
                    x res vec
        return $! D (acc + fl) (Add acc' fl')
  V.foldM' f (scalar 0) samples

fit2Tests :: TestTree
fit2Tests = testGroup "Sample fitting 2 hidden layer fc nn tests"
  [ testCase "tanhAct tanhAct (-1, 1) 42 7 31 0.1 10000" $ do
      let samples = wsFit (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.1 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 10000)
        @?= 1.2184165e-2
  , testCase "tanhAct tanhAct (-1, 1) 42 9 31 0.01 100000" $ do
      let samples = wsFit (-1, 1) 42 9
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 100000)
        @?= 3.8852803e-2
  , testCase "tanhAct tanhAct (-1, 1) 42 16 61 0.01 100000" $ do
      -- With 1 layer, adding hidden layer neurons above the number
      -- of samples didn't help. Here it helps to an extent,
      -- if iterations go up as well, considerably but not yet outrageously
      -- (here 7 times per twice more neurons).
      let samples = wsFit (-1, 1) 42 16
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 100000)  -- 700000 needed to get close
        @?= 0.28223497  -- 16 seems to be the limit for this data
  , testCase "Separated (-1, 1) 42 7 31 0.1 10000" $ do
      let samples = wsFitSeparated (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.1 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 10000)
        @?= 1.4805155
  , testCase "Separated (-1, 1) 42 9 31 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 9
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 100000)
        @?= 1.6218979e-2
  , testCase "Separated (-1, 1) 42 16 61 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 16
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 100000)
        @?= 2.2715058e-3
  , testCase "Separated (-1, 1) 42 20 61 0.01 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 20
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescShow 0.01 (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                        vec 100000)
        @?= 0.8966881
  ]

-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gradDescSmart :: forall r . (Ord r, Fractional r, Data.Vector.Unboxed.Unbox r)
              => (VecDualDeltaR r -> DeltaMonadR r (DualDeltaR r))
              -> Int
              -> Domain r
              -> (Domain' r, r)
gradDescSmart f n0 params0 = go n0 params0 0.1 gradient0 value0 0 where
  dim = V.length params0
  vVar = V.generate dim (Var . DeltaId)
  initVars0 :: (VecDualDeltaR r, Int)
  initVars0 = ((params0, vVar), dim)
  (gradient0, value0) = generalDf (const initVars0) evalBindingsV f params0
  go :: Int -> Domain r -> r -> Domain r -> r -> Int -> (Domain' r, r)
  go 0 !params !gamma _gradientPrev _valuePrev !_i = (params, gamma)
  go _ params 0 _ _ _ = (params, 0)
  go n params gamma gradientPrev valuePrev i =
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let paramsNew = V.zipWith (\p r -> p - gamma * r) params gradientPrev
        initVars = ((paramsNew, vVar), dim)
        (gradient, value) = generalDf (const initVars) evalBindingsV f paramsNew
    in if | V.all (== 0) gradientPrev -> (params, gamma)
          | value > valuePrev ->
              go n params (gamma / 2) gradientPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) paramsNew (gamma * 2) gradient value 0
          | otherwise -> go (pred n) paramsNew gamma gradient value (i + 1)

gradDescSmartShow :: (VecDualDelta -> DeltaMonad DualDelta)
                  -> Domain Float
                  -> Int
                  -> ([Float], (Float, Float))
gradDescSmartShow f initVec n =
  let (res, gamma) = gradDescSmart f n initVec
      l = V.toList $ res
  in (l, (snd $ dfShow f l, gamma))

-- It seems the approximation overshoots all the time and makes smaller
-- and smaller steps, getting nowhere. This probably means
-- approximation with this number of neurons is not possible.
-- However, adding neurons doesn't help (without huge increases of iterations).
-- The fact that results are worse than when freely overshooting
-- suggests there are local minima, which confirms too low dimensionality.
--
-- The experiments with separated samples seem to confirm both hypotheses.
smartFitTests :: TestTree
smartFitTests = testGroup "Sample fitting smart descent fc nn tests"
  [ testCase "tanhAct tanhAct (-1, 1) 42 7 31 10000" $ do
      let samples = wsFit (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 10000)
        @?= (2.3912373e-3,2.5e-2)
  , testCase "tanhAct tanhAct (-1, 1) 42 9 31 100000" $ do
      let samples = wsFit (-1, 1) 42 9
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 100000)
        @?= (2.7362056e-2,4.7683717e-8)
  , testCase "tanhAct tanhAct (-1, 1) 42 10 31 100000" $ do
      let samples = wsFit (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 100000)
        @?= (0.12360282,3.0517579e-6)
  , testCase "Separated (-1, 1) 42 7 31 10000" $ do
      let samples = wsFitSeparated (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 10000)
        @?= (0.1171444,5.0e-2)
  , testCase "Separated (-1, 1) 42 9 31 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 9
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 100000)
        @?= (3.2441253e-6,1.953125e-4)
  , testCase "Separated (-1, 1) 42 10 31 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 10
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 100000)
        @?= (3.2457123e-5,2.4414063e-5)
  , testCase "Separated (-1, 1) 42 16 31 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 16
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFitLossTotal tanhAct tanhAct samples)
                             vec 100000)
        @?= (0.40494907,6.1035157e-6)
  ]

smartFit2Tests :: TestTree
smartFit2Tests =
 testGroup "Sample fitting smart descent 2 hidden layer fc nn tests"
  [ testCase "tanhAct tanhAct (-1, 1) 42 7 31 10000" $ do
      let samples = wsFit (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 10000)
        @?= (5.270035e-3,1.25e-2)
  , testCase "tanhAct tanhAct (-1, 1) 42 9 31 100000" $ do
      let samples = wsFit (-1, 1) 42 9
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 100000)
        @?= (5.852994e-2,3.0517579e-6)
  , testCase "tanhAct tanhAct (-1, 1) 42 16 61 100000" $ do
      let samples = wsFit (-1, 1) 42 16
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 100000)  -- 700000 needed to get close
        @?= (1.8046868,3.8146973e-7)
  , testCase "Separated (-1, 1) 42 7 31 10000" $ do
      let samples = wsFitSeparated (-1, 1) 42 8
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 10000)
        @?= (5.3525884e-2,5.0e-2)
  , testCase "Separated (-1, 1) 42 9 31 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 9
          vec = V.unfoldrExactN 31 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 100000)
        @?= (1.450565e-7,2.4414063e-5)
  , testCase "Separated (-1, 1) 42 16 61 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 16
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 100000)
        @?= (1.789534e-4,1.2207031e-5)
  , testCase "Separated (-1, 1) 42 20 61 100000" $ do
      let samples = wsFitSeparated (-1, 1) 42 20
          vec = V.unfoldrExactN 61 (uniformR (-1, 1)) $ mkStdGen 33
      snd (gradDescSmartShow (nnFit2LossTotal tanhAct tanhAct tanhAct samples)
                             vec 100000)
        @?= (1.0836166,1.5258789e-6)
  ]
