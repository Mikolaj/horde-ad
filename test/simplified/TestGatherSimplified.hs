{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, OverloadedLists,
             RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestGatherSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           GHC.TypeLits (KnownNat, type (+), type (-), type (<=))
import           Numeric.LinearAlgebra (Numeric)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import TestAdaptorSimplified
  (assertEqualUpToEpsilon', assertEqualUpToEpsilonShorter, rev')
import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "gatherNested1" testGatherNested1
  , testCase "gather1" testGather1
  , testCase "gatherSimp1" testGatherSimp1
  , testCase "gatherNested2" testGatherNested2
  , testCase "gather2" testGather2
  , testCase "gatherSimp2" testGatherSimp2
  ]

gatherNested1 :: forall r. ADReady r
              => TensorOf 2 r -> TensorOf 1 r
gatherNested1 t =
  tgather @r @1
          (2 :$ ZS)
          (tgather @r @1
                   (4 :$ 2 :$ ZS) t
                   (\(k3 :. ZI) -> k3 :. ZI))
          (\(i2 :. ZI) -> i2 + i2 :. i2 :. ZI)

testGatherNested1 :: Assertion
testGatherNested1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @(OR.Array 1 Double) gatherNested1
                               (tkonst 7 $ tfromList [0, 1]))

gather1 :: forall r. ADReady r
        => TensorOf 2 r -> TensorOf 1 r
gather1 t =
  tgather @r @1
          (2 :$ ZS)
          t
          (\(i2 :. ZI) -> i2 + i2 :. i2 :. ZI)

testGather1 :: Assertion
testGather1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @(OR.Array 1 Double) gather1
                               (tkonst 7 $ tfromList [0, 1]))

testGatherSimp1 :: Assertion
testGatherSimp1 = do
  length (show (simplifyAst @Float
                $ gatherNested1 $ AstVar [7, 2] (AstVarName 0)))
    @?= length (show (simplifyAst @Float
                      $ gather1 $ AstVar [7, 2] (AstVarName 0)))

gatherNested2 :: forall r. ADReady r
              => TensorOf 2 r -> TensorOf 2 r
gatherNested2 t =
  tgather @r @2
          (2 :$ 3 :$ ZS)
          (tgather @r @3
                   (2 :$ 3 :$ 4 :$ 2 :$ ZS) t
                   (\(k1 :. k2 :. k3 :. ZI) -> k1 + k2 + k3 :. ZI))
          (\(i1 :. i2 :. ZI) -> i1 :. i2 :. i1 + i2 :. i1 :. ZI)

testGatherNested2 :: Assertion
testGatherNested2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,1.0])
    (rev' @(OR.Array 2 Double) gatherNested2
                               (tkonst 7 $ tfromList [0, 1]))

gather2 :: forall r. ADReady r
        => TensorOf 2 r -> TensorOf 2 r
gather2 t =
  tgather @r @2
          (2 :$ 3 :$ ZS)
          t
          (\(i1 :. i2 :. ZI) -> i1 + i2 + i1 + i2 :. i1 :. ZI)

testGather2 :: Assertion
testGather2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,1.0])
    (rev' @(OR.Array 2 Double) gather2
                               (tkonst 7 $ tfromList [0, 1]))

testGatherSimp2 :: Assertion
testGatherSimp2 = do
  length (show (simplifyAst @Float
                $ gatherNested2 $ AstVar [7, 2] (AstVarName 0)))
    @?= length (show (simplifyAst @Float
                      $ gather2 $ AstVar [7, 2] (AstVarName 0)))
