{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
module TestSimplified (testTrees) where

import Prelude

import qualified Data.Vector.Generic as V
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd hiding (sumElementsVectorOfDual)

import Tool.EqEpsilon
import Tool.Shared

testTrees :: [TestTree]
testTrees = [ simple0Tests
            , quickCheck0Tests
            ]

baseline1
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
baseline1 x = 6 * x

testBaseline1 :: Assertion
testBaseline1 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 baseline1 1.5)
    (6, 9)

build1SeqSimple1
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
build1SeqSimple1 x =
  sumElements0 (build1Seq 4 $ \i -> fromInteger (toInteger i) * x)

testBuild1SeqSimple1 :: Assertion
testBuild1SeqSimple1 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 build1SeqSimple1 1.5)
    (6, 9)

build1Simple1
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
build1Simple1 x =
  sumElements0 (build1 4 $ \i -> fromInteger (toInteger i) * x)

testBuild1Simple1 :: Assertion
testBuild1Simple1 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 build1Simple1 1.5)
    (6, 9)


baseline2
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
baseline2 x = x * x + x + 6 * x * x + 4 * x

testBaseline2 :: Assertion
testBaseline2 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 baseline2 1.5)
    (26.0,23.25)

build1SeqSimple2
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
build1SeqSimple2 x =
  let !x2 = x * x
  in x2 + x
     + sumElements0 (build1Seq 4 $ \i -> fromInteger (toInteger i) * x2 + x)

testBuild1SeqSimple2 :: Assertion
testBuild1SeqSimple2 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 build1SeqSimple2 1.5)
    (26.0,23.25)

build1Simple2
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
build1Simple2 x =
  let !x2 = x * x
  in x2 + x
     + sumElements0 (build1 4 $ \i -> fromInteger (toInteger i) * x2 + x)

testBuild1Simple2 :: Assertion
testBuild1Simple2 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 build1Simple2 1.5)
    (26.0,23.25)


baseline3
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
baseline3 x = 5 * (x * x + x)

testBaseline3 :: Assertion
testBaseline3 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 baseline3 1.5)
    (20.0,18.75)

build1SeqSimple3
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
build1SeqSimple3 x =
  let !x2 = x * x
      !v = build1Seq 1 $ \i -> fromInteger (toInteger i) * x2 + x * x + x
  in sumElements0
     $ v
       + build1Seq 1 (const $ sumElements0 v)
       + v
       + build1Seq 1
           (const $ sumElements0
            $ build1Seq 1 $ \i -> fromInteger (toInteger i) * x2 + x2 + x)
       + v

testBuild1SeqSimple3 :: Assertion
testBuild1SeqSimple3 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 build1SeqSimple3 1.5)
    (20.0,18.75)

build1Simple3
  :: ADModeAndNum d r
  => ADVal d r -> ADVal d r
build1Simple3 x =
  let !x2 = x * x
      !v = build1 1 $ \i -> fromInteger (toInteger i) * x2 + x * x + x
  in sumElements0
     $ v
       + build1 1 (const $ sumElements0 v)
       + v
       + build1 1
           (const $ sumElements0
            $ build1 1 $ \i -> fromInteger (toInteger i) * x2 + x2 + x)
       + v

testBuild1Simple3 :: Assertion
testBuild1Simple3 =
  assertEqualUpToEpsilon 1e-7
    (dRev0 build1Simple3 1.5)
    (20.0,18.75)

simple0Tests :: TestTree
simple0Tests = testGroup "Simple0Tests of build1"
  [ testCase "testBaseline1" testBaseline1
  , testCase "testBuild1SeqSimple1" testBuild1SeqSimple1
  , testCase "testBuild1Simple1" testBuild1Simple1
  , testCase "testBaseline2" testBaseline2
  , testCase "testBuild1SeqSimple2" testBuild1SeqSimple2
  , testCase "testBuild1Simple2" testBuild1Simple2
  , testCase "testBaseline3" testBaseline3
  , testCase "testBuild1SeqSimple3" testBuild1SeqSimple3
  , testCase "testBuild1Simple3" testBuild1Simple3
  ]

quickCheck0Tests :: TestTree
quickCheck0Tests =
 testGroup
  "TuickCheck tests of build1's gradient vs derivative vs perturbation"
  [ quickCheckTestBuild "testBaseline1" baseline1
  , quickCheckTestBuild "testBuild1SeqSimple1" build1SeqSimple1
  , quickCheckTestBuild "testBuild1Simple1" build1Simple1
  , quickCheckTestBuild "testBaseline2" baseline2
  , quickCheckTestBuild "testBuild1SeqSimple2" build1SeqSimple2
  , quickCheckTestBuild "testBuild1Simple2" build1Simple2
  , quickCheckTestBuild "testBaseline3" baseline3
  , quickCheckTestBuild "testBuild1SeqSimple3" build1SeqSimple3
  , quickCheckTestBuild "testBuild1Simple3" build1Simple3
  ]

dRev0
  :: (r ~ Double, d ~ 'ADModeGradient)
  => (ADVal d r -> ADVal d r)
  -> r
  -> (r, r)
dRev0 f x =
  let g adInputs = f $ adInputs `at0` 0
      ((gradient0, _), value) = revFun 1 g (V.singleton x, V.empty)
  in (gradient0 V.! 0, value)

quickCheckTestBuild
  :: TestName
  -> (forall d r. ADModeAndNum d r => ADVal d r -> ADVal d r)
  -> TestTree
quickCheckTestBuild txt f =
  let g :: (forall d r. ADModeAndNum d r => ADInputs d r -> ADVal d r)
      g adInputs = f $ adInputs `at0` 0
  in quickCheckTest0 txt g (\(x, _, _) -> ([x], [], [], []))
