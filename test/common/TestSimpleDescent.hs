{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
module TestSimpleDescent (testTrees) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Internal.Delta (toShapedOrDummy)
import Tool.Shared (fquad, quad)
import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees = [ gdSimpleTests
            , gdTestsRecord
            , xorTests ]

gdSimpleShow :: HasDelta r
             => r
             -> (ADInputs 'ADModeGradient r
                 -> ADVal 'ADModeGradient r)
             -> Domain0 r
             -> Int
             -> IO ([r], r)
gdSimpleShow gamma f initVec n = do
  (res, _, _, _) <- gdSimple gamma f n (initVec, V.empty, V.empty, V.empty)
  (_, v) <- revIO 1 f (res, V.empty, V.empty, V.empty)
  return (V.toList res, v)

-- Catastrophic loss of sharing prevented via the monad.
fblowup :: forall d. ADModeAndNum d Float
        => ADInputs d Float -> ADVal d Float
fblowup inputs =
  let blowup :: Int -> ADVal d Float -> ADVal d Float
      blowup 0 y = y
      blowup n y =
        let ysum = y + y
            yscaled = 0.499999985 * ysum
          -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = fquad inputs
  in blowup 100 y0

gdSimpleTests :: TestTree
gdSimpleTests = testGroup "Simple gradient descent tests"
  [ testCase "0.1 30" $ do
      res <- gdSimpleShow 0.1 fquad (V.fromList [2, 3]) 30
      res @?~ ([2.47588e-3,3.7138206e-3],5.00002 :: Float)
  , testCase "0.01 30" $ do
      res <- gdSimpleShow 0.01 fquad (V.fromList [2, 3]) 30
      res @?~ ([1.0909687,1.6364527],8.86819 :: Float)
  , testCase "0.01 300" $ do
      res <- gdSimpleShow 0.01 fquad (V.fromList [2, 3]) 300
      res @?~ ([4.665013e-3,6.9975173e-3],5.0000706 :: Float)
  , testCase "0.01 300000" $ do
      res <- gdSimpleShow 0.01 fquad (V.fromList [2, 3]) 300000
      res @?~ ([3.5e-44,3.5e-44],5.0 :: Float)
  -- The (no) blowup tests.
  , testCase "blowup 0.1 100" $ do
      res <- gdSimpleShow 0.1 fblowup (V.fromList [2, 3]) 100
      res @?~ ([4.0746778e-10,6.1120126e-10],4.9999523)
  , testCase "blowup 0.01 100" $ do
      res <- gdSimpleShow 0.01 fblowup (V.fromList [2, 3]) 100
      res @?~ ([0.2652423,0.39786342],5.228601)
  , testCase "blowup 0.01 10000" $ do
      res <- gdSimpleShow 0.01 fblowup (V.fromList [2, 3]) 10000
      res @?~ ([3.5e-44,3.5e-44],4.9999523)
  , testCase "blowup 0.01 1000000" $ do
      res <- gdSimpleShow 0.01 fblowup (V.fromList [2, 3]) 1000000
      res @?~ ([3.5e-44,3.5e-44],4.9999523)
  ]

data ARecord a b = ARecord a b

type ARecordAA sh r = ARecord (OS.Array sh r)
                              (OS.Array sh r)

type ARecordDD sh d r = ARecord (ADVal d (OS.Array sh r))
                                (ADVal d (OS.Array sh r))

adaptFunctionRecord
  :: forall sh r d. (ADModeAndNum d r, OS.Shape sh)
  => (ARecordDD sh d r -> ADVal d r)
  -> (ADInputs d r -> ADVal d r)
adaptFunctionRecord f inputs =
  let a = atS inputs 0
      b = atS inputs 1
  in f $ ARecord a b

adaptDReverseRecord
  :: forall sh r. (HasDelta r, OS.Shape sh)
  => r
  -> (forall d. ADModeAndNum d r
      => ARecordDD sh d r -> ADVal d r)
  -> ARecordAA sh r
  -> IO (ARecordAA sh r, r)
adaptDReverseRecord dt f (ARecord a b) = do
  let initVec = V.fromList $ map Data.Array.Convert.convert [a, b]
      g = adaptFunctionRecord f
  ((_, _, _, gradient), v) <-
    revIO dt g (V.empty, V.empty, V.empty, initVec)
  let gradientRecord = case V.toList gradient of
        [a2, b2] -> ARecord (toShapedOrDummy a2)
                            (toShapedOrDummy b2)
        _ -> error "adaptDReverseRecord"
  return (gradientRecord, v)

adaptGdSimpleRecord
  :: forall sh r. (HasDelta r, OS.Shape sh)
  => r
  -> (forall d. ADModeAndNum d r
      => ARecordDD sh d r -> ADVal d r)
  -> Int
  -> ARecordAA sh r
  -> IO (ARecordAA sh r)
adaptGdSimpleRecord gamma f n0 (ARecord a b) = do
  let initVec = V.fromList $ map Data.Array.Convert.convert [a, b]
      g = adaptFunctionRecord f
  (_, _, _, gradient) <-
    gdSimple gamma g n0 (V.empty, V.empty, V.empty, initVec)
  case V.toList gradient of
    [a2, b2] -> return $! ARecord (toShapedOrDummy a2)
                                  (toShapedOrDummy b2)
    _ -> error "adaptGdSimpleRecord"

gdShowRecord
  :: forall sh r. (HasDelta r, OS.Shape sh)
  => r
  -> (forall d. ADModeAndNum d r
      => ARecordDD sh d r -> ADVal d r)
  -> [[r]]
  -> Int
  -> IO ([r], r)
gdShowRecord gamma f initList n = do
  let initRecord = case initList of
        [a, b] -> ARecord (OS.fromList a)
                          (OS.fromList b)
        _ -> error "gdShowRecord"
  gradient <- adaptGdSimpleRecord gamma f n initRecord
  (_, v) <- adaptDReverseRecord 1 f gradient
  let ppARecord :: ARecordAA sh r -> [r]
      ppARecord (ARecord a b) = OS.toList a ++ OS.toList b
  return (ppARecord gradient, v)

fquadRecord :: forall k d r. (ADModeAndNum d r, KnownNat k)
            => ARecordDD '[k] d r -> ADVal d r
fquadRecord (ARecord x y) = quad (fromS0 (head (unravelToListS x)))
                                 (fromS0 (head (unravelToListS y)))

gdTestsRecord :: TestTree
gdTestsRecord = testGroup "Record of shaped tensors tests"
  [ testCase "0.1 30" $ do
      res <- gdShowRecord 0.1 (fquadRecord @1) [[2], [3]] 30
      res @?~ ([2.47588e-3,3.7138206e-3],5.00002 :: Float)
  , testCase "0.01 30" $ do
      res <- gdShowRecord 0.01 (fquadRecord @1) [[2], [3]] 30
      res @?~ ([1.0909687,1.6364527],8.86819 :: Float)
  , testCase "0.01 300" $ do
      res <- gdShowRecord 0.01 (fquadRecord @1) [[2], [3]] 300
      res @?~ ([4.665013e-3,6.9975173e-3],5.0000706 :: Float)
  , testCase "0.01 300000" $ do
      res <- gdShowRecord 0.01 (fquadRecord @1) [[2], [3]] 300000
      res @?~ ([3.5e-44,3.5e-44],5.0 :: Float)
  , testCase "0.1 30" $ do
      res <- gdShowRecord 0.1 (fquadRecord @2) [[2, 42], [3, 42]] 30
      res @?~ ([2.47588e-3,42,3.7138206e-3,42],5.00002 :: Float)
  , testCase "0.01 30" $ do
      res <- gdShowRecord 0.01 (fquadRecord @2) [[2, 42], [3, 42]] 30
      res @?~ ([1.0909687,42,1.6364527,42],8.86819 :: Float)
  , testCase "0.01 300" $ do
      res <- gdShowRecord 0.01 (fquadRecord @2) [[2, 42], [3, 42]] 300
      res @?~ ([4.665013e-3,42,6.9975173e-3,42],5.0000706 :: Float)
  , testCase "0.01 300000" $ do
      res <- gdShowRecord 0.01 (fquadRecord @2) [[2, 42], [3, 42]] 300000
      res @?~ ([3.5e-44,42,3.5e-44,42],5.0 :: Float)
  ]

-- This, and other XOR nn operations, have unfused Delta let-bindings
-- (one binding per each subexpression, even when not needed), which is fine,
-- just not enough for comprehensive benchmarks.
scaleAddWithBias :: ADModeAndNum d Float
                 => ADVal d Float -> ADVal d Float -> Int -> ADInputs d Float
                 -> ADVal d Float
scaleAddWithBias x y ixWeight inputs =
  let wx = at0 inputs ixWeight
      wy = at0 inputs (ixWeight + 1)
      bias = at0 inputs (ixWeight + 2)
      sx = x * wx
      sy = y * wy
      sxy = sx + sy
  in sxy + bias

neuron :: ADModeAndNum d Float
       => (ADVal d Float -> ADVal d Float)
       -> ADVal d Float -> ADVal d Float -> Int
       -> ADInputs d Float
       -> ADVal d Float
neuron factivation x y ixWeight inputs =
  let sc = scaleAddWithBias x y ixWeight inputs
  in factivation sc

nnXor :: ADModeAndNum d Float
      => (ADVal d Float -> ADVal d Float)
      -> ADVal d Float -> ADVal d Float -> ADInputs d Float
      -> ADVal d Float
nnXor factivation x y inputs =
  let n1 = neuron factivation x y 0 inputs
      n2 = neuron factivation x y 3 inputs
  in neuron factivation n1 n2 6 inputs

nnXorLoss :: ADModeAndNum d Float
          => (ADVal d Float -> ADVal d Float)
          -> Float -> Float -> Float -> ADInputs d Float
          -> ADVal d Float
nnXorLoss factivation x y targ inputs =
  let res = nnXor factivation (constant x) (constant y) inputs
  in squaredDifference targ res

nnXorLossTotal :: ADModeAndNum d Float
               => (ADVal d Float -> ADVal d Float)
               -> ADInputs d Float
               -> ADVal d Float
nnXorLossTotal factivation inputs =
  let n1 = nnXorLoss factivation 0 0 0 inputs
      n2 = nnXorLoss factivation 0 1 1 inputs
      n3 = nnXorLoss factivation 1 0 1 inputs
      n4 = nnXorLoss factivation 1 1 0 inputs
      n12 = n1 + n2
      n34 = n3 + n4
  in n12 + n34

ws, ws2 :: Domain0 Float
ws = let w = [0.37, 0.28, 0.19] in V.fromList $ w ++ w ++ w
ws2 = let w = [-1.37, 2.28, -0.19] in V.fromList $ w ++ w ++ w

xorTests :: TestTree
xorTests = testGroup "XOR neural net tests"
  [ testCase "0.1 tanh ws 500" $ do
      res <- gdSimpleShow 0.1 (nnXorLossTotal tanh) ws 500
      res @?~ ([2.256964,2.255974,-0.6184606,0.943269,0.9431414,-1.2784432,1.805072,-1.9925138,-0.704399],1.20509565e-2)
  , testCase "0.1 tanh ws 5000" $ do
      res <- gdSimpleShow 0.1 (nnXorLossTotal tanh) ws 5000
      res @?~ ([2.4474504,2.4467778,-0.8350617,1.3046894,1.3045748,-1.8912042,2.3819275,-2.5550227,-0.8139653],1.8524402e-4)
  , testCase "0.01 tanh ws2 50000" $ do
      res <- gdSimpleShow 0.01 (nnXorLossTotal tanh) ws2 50000
      res @?~ ([-1.9872262,2.576039,0.66793317,-1.7813873,2.2283037,-0.9866766,-2.1694322,2.1973324,2.9272876],2.1781659e-4)
  -- the same, but logistic for the first hidden layer instead of tanh
  , testCase "0.1 logistic ws 5000" $ do
      res <- gdSimpleShow 0.1 (nnXorLossTotal logistic) ws 5000
      assertBool "test case 0.1 logistic ws 5000 did not produce any of the known good results (one only seen on CI)" $
        res `elem` [ ([5.5609226,5.553409,-2.2246428,3.4135451,3.4121408,-5.2069902,6.8810863,-7.41155,-3.086779],2.4756126e-2)
                   , ([5.560923,5.553408,-2.2246423,3.4135454,3.412141,-5.2069907,6.881085,-7.411549,-3.0867786],2.4756145e-2) ]
  , testCase "0.01 logistic ws2 50000" $ do
      res <- gdSimpleShow 0.01 (nnXorLossTotal logistic) ws2 50000
      res @?~ ([-5.276363,5.5221853,2.641188,-5.2796497,5.2037635,-2.8858855,-7.5792775,7.997162,3.5127592],6.759104e-3)
  -- the same, but relu for the first hidden layer instead of tanh
  , testCase "0.1 relu ws 5000" $ do
      res <- gdSimpleShow 0.1 (nnXorLossTotal relu) ws 5000  -- no cookie
      res @?~ ([0.18908867,0.14627013,0.25409937,0.2798127,0.21643773,0.22213355,8.865212e-2,-5.99097e-2,0.4907815],0.9999999)
  , testCase "0.01 relu ws2 50000" $ do
      res <- gdSimpleShow 0.01 (nnXorLossTotal relu) ws2 50000  -- no cookie
      res @?~ ([-1.3572536,2.3245132,-0.14548694,-1.3912132,2.2069085,-0.2630923,-1.4252249,2.2264564,-0.22221938],1.0)
  ]
