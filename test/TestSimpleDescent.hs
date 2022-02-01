{-# LANGUAGE FlexibleContexts #-}
module TestSimpleDescent (testTrees) where

import Prelude

import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Numeric.LinearAlgebra (Numeric)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

type DualNumberF = DualNumber Float

type VecDualNumberF = VecDualNumber Float

testTrees :: [TestTree]
testTrees = [ gdSimpleTests
            , xorTests ]

-- Unfortunately, monadic versions of the operations below are not
-- polymorphic over whether they operate on scalars, vectors or other types,
-- so we should probably abandon them.

(+\) :: (DeltaMonad r m, Num r)
     => DualNumber r -> DualNumber r -> m (DualNumber r)
(+\) u v = returnLet $ u + v

(*\) :: (DeltaMonad r m, Num r)
     => DualNumber r -> DualNumber r -> m (DualNumber r)
(*\) u v = returnLet $ u * v

scaleDual :: (DeltaMonad r m, Num r) => r -> DualNumber r -> m (DualNumber r)
scaleDual r u = returnLet $ scale r u

squareDual :: (DeltaMonad r m, Num r) => DualNumber r -> m (DualNumber r)
squareDual = returnLet . square

gdSimpleShow :: (Eq r, Numeric r, Num (Data.Vector.Storable.Vector r))
             => r
             -> (VecDualNumber r -> DeltaMonadGradient r (DualNumber r))
             -> Domain r
             -> Int
             -> ([r], r)
gdSimpleShow gamma f initVec n =
  let (res, _, _) = gdSimple gamma f n (initVec, V.empty, V.empty)
      (_, value) = df f (res, V.empty, V.empty)
  in (V.toList res, value)

fquad :: DeltaMonad Float m => VecDualNumberF -> m DualNumberF
fquad vec = do
  let x = var vec 0
      y = var vec 1
  x2 <- squareDual x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ scalar 5

fblowup :: forall m. DeltaMonad Float m => VecDualNumberF -> m DualNumberF
fblowup vec = do
  let blowup :: Int -> DualNumberF -> m DualNumberF
      blowup 0 y = return y
      blowup n y = do
        ysum <- y +\ y
        yscaled <- scaleDual 0.499999985 ysum  -- otherwise we'd get NaN at once
        blowup (pred n) yscaled
  y0 <- fquad vec
  blowup 100 y0

gdSimpleTests :: TestTree
gdSimpleTests = testGroup "Simple gradient descent tests"
  [ testCase "0.1 30"
    $ gdSimpleShow 0.1 fquad (V.fromList [2, 3]) 30
      @?= ([2.47588e-3,3.7138206e-3],5.00002)
  , testCase "0.01 30"
    $ gdSimpleShow 0.01 fquad (V.fromList [2, 3]) 30
      @?= ([1.0909687,1.6364527],8.86819)
  , testCase "0.01 300"
    $ gdSimpleShow 0.01 fquad (V.fromList [2, 3]) 300
      @?= ([4.665013e-3,6.9975173e-3],5.0000706)
  , testCase "0.01 300000"
    $ gdSimpleShow 0.01 fquad (V.fromList [2, 3]) 300000
      @?= ([3.5e-44,3.5e-44],5.0)
  -- The (no) blowup tests.
  , testCase "blowup 0.1 30"
    $ gdSimpleShow 0.1 fblowup (V.fromList [2, 3]) 30
      @?= ([2.475991e-3,3.7139843e-3],4.9999723)
  , testCase "blowup 0.01 30"
    $ gdSimpleShow 0.01 fblowup (V.fromList [2, 3]) 30
      @?= ([1.0909724,1.6364591],8.868124)
  , testCase "blowup 0.01 300"
    $ gdSimpleShow 0.01 fblowup (V.fromList [2, 3]) 300
      @?= ([4.665179e-3,6.9977706e-3],5.000023)
  , testCase "blowup 0.01 300000"
    $ gdSimpleShow 0.01 fblowup (V.fromList [2, 3]) 300000
      @?= ([3.5e-44,3.5e-44],4.9999523)
  , testCase "blowup 0.01 3000000"
    $ gdSimpleShow 0.01 fblowup (V.fromList [2, 3]) 3000000
      @?= ([3.5e-44,3.5e-44],4.9999523)
  ]

-- This, and other XOR nn operations, have unfused Delta let-bindings
-- (one binding per each subexpression, even when not needed), which is fine,
-- just not enough for comprehensive benchmarks.
scaleAddWithBias :: DeltaMonad Float m
                 => DualNumberF -> DualNumberF -> Int -> VecDualNumberF
                 -> m DualNumberF
scaleAddWithBias x y ixWeight vec = do
  let wx = var vec ixWeight
      wy = var vec (ixWeight + 1)
      bias = var vec (ixWeight + 2)
  sx <- x *\ wx
  sy <- y *\ wy
  sxy <- sx +\ sy
  sxy +\ bias

neuron :: DeltaMonad Float m
       => (DualNumberF -> m DualNumberF)
       -> DualNumberF -> DualNumberF -> Int -> VecDualNumberF
       -> m DualNumberF
neuron factivation x y ixWeight vec = do
  sc <- scaleAddWithBias x y ixWeight vec
  factivation sc

nnXor :: DeltaMonad Float m
      => (DualNumberF -> m DualNumberF)
      -> DualNumberF -> DualNumberF -> VecDualNumberF
      -> m DualNumberF
nnXor factivation x y vec = do
  n1 <- neuron factivation x y 0 vec
  n2 <- neuron factivation x y 3 vec
  neuron factivation n1 n2 6 vec

nnXorLoss :: DeltaMonad Float m
          => (DualNumberF -> m DualNumberF)
          -> Float -> Float -> Float -> VecDualNumberF
          -> m DualNumberF
nnXorLoss factivation x y targ vec = do
  res <- nnXor factivation (scalar x) (scalar y) vec
  lossSquared targ res

nnXorLossTotal :: DeltaMonad Float m
               => (DualNumberF -> m DualNumberF)
               -> VecDualNumberF
               -> m DualNumberF
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
    $ gdSimpleShow 0.1 (nnXorLossTotal tanhAct) ws 500
      @?= ([2.256964,2.255974,-0.6184606,0.943269,0.9431414,-1.2784432,1.805072,-1.9925138,-0.704399],1.20509565e-2)
  , testCase "0.1 tanhAct ws 5000"
    $ gdSimpleShow 0.1 (nnXorLossTotal tanhAct) ws 5000
      @?= ([2.4474504,2.4467778,-0.8350617,1.3046894,1.3045748,-1.8912042,2.3819275,-2.5550227,-0.8139653],1.8524402e-4)
  , testCase "0.01 tanhAct ws2 50000"
    $ gdSimpleShow 0.01 (nnXorLossTotal tanhAct) ws2 50000
      @?= ([-1.9872262,2.576039,0.66793317,-1.7813873,2.2283037,-0.9866766,-2.1694322,2.1973324,2.9272876],2.1781659e-4)
  -- the same, but logisticAct for the first hidden layer instead of tanhAct
  , testCase "0.1 logisticAct ws 5000"
    $ assertBool "test case 0.1 logisticAct ws 5000 did not produce any of the known good results (one only seen on CI)"
      $ gdSimpleShow 0.1 (nnXorLossTotal logisticAct) ws 5000
        `elem` [ ([5.5609226,5.553409,-2.2246428,3.4135451,3.4121408,-5.2069902,6.8810863,-7.41155,-3.086779],2.4756126e-2)
               , ([5.560923,5.553408,-2.2246423,3.4135454,3.412141,-5.2069907,6.881085,-7.411549,-3.0867786],2.4756145e-2) ]
  , testCase "0.01 logisticAct ws2 50000"
    $ gdSimpleShow 0.01 (nnXorLossTotal logisticAct) ws2 50000
      @?= ([-5.276363,5.5221853,2.641188,-5.2796497,5.2037635,-2.8858855,-7.5792775,7.997162,3.5127592],6.759104e-3)
  -- the same, but reluAct for the first hidden layer instead of tanhAct
  , testCase "0.1 reluAct ws 5000"
    $ gdSimpleShow 0.1 (nnXorLossTotal reluAct) ws 5000  -- no cookie
      @?= ([0.18908867,0.14627013,0.25409937,0.2798127,0.21643773,0.22213355,8.865212e-2,-5.99097e-2,0.4907815],0.9999999)
  , testCase "0.01 reluAct ws2 50000"
    $ gdSimpleShow 0.01 (nnXorLossTotal reluAct) ws2 50000  -- no cookie
      @?= ([-1.3572536,2.3245132,-0.14548694,-1.3912132,2.2069085,-0.2630923,-1.4252249,2.2264564,-0.22221938],1.0)
  ]
