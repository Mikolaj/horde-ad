{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, OverloadedLists,
             RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestGatherSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import TestAdaptorSimplified (assertEqualUpToEpsilon', rev')

testTrees :: [TestTree]
testTrees =
  [ testCase "gatherNested1" testGatherNested1
  , testCase "gather1" testGather1
  , testCase "gatherSimp1" testGatherSimp1
  , testCase "gatherNested2" testGatherNested2
  , testCase "gather2" testGather2
  , testCase "gatherSimp2" testGatherSimp2
  , testCase "gatherNested12" testGatherNested12
  , testCase "gather12" testGather12
  , testCase "gatherSimp12" testGatherSimp12
  , testCase "gatherReshape22" testGatherReshape22
  , testCase "gatherSimp22" testGatherSimp22
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

gatherNested12 :: forall r. ADReady r
               => TensorOf 2 r -> TensorOf 2 r
gatherNested12 t =
  tgather @r @1
          (2 :$ 4 :$ ZS)
          (tgather @r @3
                   (2 :$ 3 :$ 4 :$ ZS) t
                   (\(k1 :. k2 :. k3 :. ZI) -> k1 + k2 + k3 :. k1 :. ZI))
          (\(i1 :. ZI) -> i1 :. i1 + i1 :. ZI)

testGatherNested12 :: Assertion
testGatherNested12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @(OR.Array 2 Double) gatherNested12
                               (tkonst 7 $ tfromList [0, 1]))

gather12 :: forall r. ADReady r
         => TensorOf 2 r -> TensorOf 2 r
gather12 t =
  tgather @r @2
          (2 :$ 4 :$ ZS)
          t
          (\(i1 :. k3 :. ZI) -> i1 + i1 + i1 + k3 :. i1 :. ZI)

testGather12 :: Assertion
testGather12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @(OR.Array 2 Double) gather12
                               (tkonst 7 $ tfromList [0, 1]))

testGatherSimp12 :: Assertion
testGatherSimp12 = do
  length (show (simplifyAst @Float
                $ gatherNested12 $ AstVar [7, 2] (AstVarName 0)))
    @?= length (show (simplifyAst @Float
                      $ gather12 $ AstVar [7, 2] (AstVarName 0)))

gatherReshape22 :: forall r. ADReady r
                => TensorOf 2 r -> TensorOf 2 r
gatherReshape22 t =
  treshape @r @2 [2, 6]
  $ treshape @r @6 [3, 1, 2, 1, 1, 2]
  $ treshape (1 :$ 12 :$ 1 :$ ZS)
  $ treshape @r @4 [3, 1, 1, 4]
  $ treshape @r @3 [2, 2, 3] t

testGatherReshape22 :: Assertion
testGatherReshape22 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [6,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @(OR.Array 2 Double) gatherReshape22
                               (tkonst 6 $ tfromList [0, 1]))

-- TODO: try to get this down to equality by simplifying better
testGatherSimp22 :: Assertion
testGatherSimp22 = do
  assertBool "reshape as gather is not simplified" $
    length (show (simplifyAst @Float
                  $ gatherReshape22 $ AstVar [6, 2] (AstVarName 0)))
      >= length (show (simplifyAst @Float
                       $ treshape @(Ast 0 Float) @2 @2 [2, 6]
                       $ AstVar [6, 2] (AstVarName 0)))
