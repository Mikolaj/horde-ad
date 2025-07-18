-- | TODO: outdated, uses the old API
module TestDescentSimple (testTrees) where

import Prelude

import Data.Vector.Generic qualified as V
import Numeric.LinearAlgebra (Vector)
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import EqEpsilon
import HordeAd
import Prop (fquad)

testTrees :: [TestTree]
testTrees = [ xorTests ]

-- TODO: keep here the nn, move tests to the tests directory
-- and test with all kinds of activation functions and loss functions,
-- e.g., harmonic loss



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
  let res = nnXor factivation (fromPrimal0 x) (fromPrimal0 y) inputs
  in squaredDifference0 targ res

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

ws, ws2 :: Vector Float
ws = let w = [0.37, 0.28, 0.19] in V.fromList $ w ++ w ++ w
ws2 = let w = [-1.37, 2.28, -0.19] in V.fromList $ w ++ w ++ w

xorTests :: TestTree
xorTests = testGroup "XOR neural net tests"
  [ testCase "0.1 tanh ws 500" $ do
      let res = gdSimpleShow 0.1 (nnXorLossTotal tanh) ws 500
      res @?~ ([2.256964,2.255974,-0.6184606,0.943269,0.9431414,-1.2784432,1.805072,-1.9925138,-0.704399],1.20509565e-2)
  , testCase "0.1 tanh ws 5000" $ do
      let res = gdSimpleShow 0.1 (nnXorLossTotal tanh) ws 5000
      res @?~ ([2.4474504,2.4467778,-0.8350617,1.3046894,1.3045748,-1.8912042,2.3819275,-2.5550227,-0.8139653],1.8524402e-4)
  , testCase "0.01 tanh ws2 50000" $ do
      let res = gdSimpleShow 0.01 (nnXorLossTotal tanh) ws2 50000
      res @?~ ([-1.9872262,2.576039,0.66793317,-1.7813873,2.2283037,-0.9866766,-2.1694322,2.1973324,2.9272876],2.1781659e-4)
  -- the same, but logistic for the first hidden layer instead of tanh
  , testCase "0.1 logistic ws 5000" $ do
      let res = gdSimpleShow 0.1 (nnXorLossTotal logistic) ws 5000
      assertBool "test case 0.1 logistic ws 5000 did not produce any of the known good results (one only seen on CI)" $
        res `elem` [ ([5.5609226,5.553409,-2.2246428,3.4135451,3.4121408,-5.2069902,6.8810863,-7.41155,-3.086779],2.4756126e-2)
                   , ([5.560923,5.553408,-2.2246423,3.4135454,3.412141,-5.2069907,6.881085,-7.411549,-3.0867786],2.4756145e-2) ]
  , testCase "0.01 logistic ws2 50000" $ do
      let res = gdSimpleShow 0.01 (nnXorLossTotal logistic) ws2 50000
      res @?~ ([-5.276363,5.5221853,2.641188,-5.2796497,5.2037635,-2.8858855,-7.5792775,7.997162,3.5127592],6.759104e-3)
  -- the same, but relu for the first hidden layer instead of tanh
  , testCase "0.1 relu0 ws 5000" $ do
      let res = gdSimpleShow 0.1 (nnXorLossTotal relu0) ws 5000  -- no cookie
      res @?~ ([0.18908867,0.14627013,0.25409937,0.2798127,0.21643773,0.22213355,8.865212e-2,-5.99097e-2,0.4907815],0.9999999)
  , testCase "0.01 relu0 ws2 50000" $ do
      let res = gdSimpleShow 0.01 (nnXorLossTotal relu0) ws2 50000  -- no cookie
      res @?~ ([-1.3572536,2.3245132,-0.14548694,-1.3912132,2.2069085,-0.2630923,-1.4252249,2.2264564,-0.22221938],1.0)
  ]
