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

import TestAdaptorSimplified (assertEqualUpToEpsilon', rev', t128, t48)

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
  , testCase "gatherTranspose33" testGatherTranspose33
  , testCase "gatherSimp33" testGatherSimp33
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
  resetVarCOunter
  let !t1 = simplifyAst @Float
            $ gatherNested1 $ AstVar [7, 2] (AstVarName 0)
  resetVarCOunter
  let !t2 = simplifyAst @Float
            $ gather1 $ AstVar [7, 2] (AstVarName 0)
  length (show t1) @?= length (show t2)

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
  resetVarCOunter
  let !t1 = simplifyAst @Float
                $ gatherNested2 $ AstVar [7, 2] (AstVarName 0)
  resetVarCOunter
  let !t2 = simplifyAst @Float
                      $ gather2 $ AstVar [7, 2] (AstVarName 0)
  length (show t1) @?= length (show t2)

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
  resetVarCOunter
  let !t1 = simplifyAst @Float
                $ gatherNested12 $ AstVar [7, 2] (AstVarName 0)
  resetVarCOunter
  let !t2 = simplifyAst @Float
            $ gather12 $ AstVar [7, 2] (AstVarName 0)
  length (show t1) @?= length (show t2)

gatherReshape22 :: forall r. ADReady r
                => TensorOf 2 r -> TensorOf 2 r
gatherReshape22 t =
  treshape @r @6 [2, 6]
  $ treshape [3, 1, 2, 1, 1, 2]
  $ treshape @r @4 (1 :$ 12 :$ 1 :$ ZS)
  $ treshape @r @3 [3, 1, 1, 4]
  $ treshape [2, 2, 3] t

testGatherReshape22 :: Assertion
testGatherReshape22 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [6,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @(OR.Array 2 Double) gatherReshape22
                               (tkonst 6 $ tfromList [0, 1]))

-- TODO: try to lower the gap down to zero
testGatherSimp22 :: Assertion
testGatherSimp22 = do
  resetVarCOunter
  let !t1 = simplifyAst @Float
            $ gatherReshape22 $ AstVar [6, 2] (AstVarName 0)
  resetVarCOunter
  let !t2 = simplifyAst @Float
            $ treshape @(Ast 0 Float) @2 @2 [2, 6]
            $ AstVar [6, 2] (AstVarName 0)
  (length (show t1) - length (show t2)) @?= 8200

-- Depending on if and how transpose it desugared, this may or may not result
-- in dozens of nested gathers that should vanish after simplification.
gatherTranspose33 :: forall r. ADReady r
                  => TensorOf 10 r -> TensorOf 2 r
gatherTranspose33 t =
  tmatmul2 (treshape [6, 8] (tconst t48))
    (ttr
     $ treshape @r @4 [16, 8]
     $ ttranspose [0, 1, 2]
     $ ttranspose [2, 0, 1]
     $ ttranspose [1, 2, 0]
     $ ttranspose [1, 0, 2]
     $ ttranspose [1, 0]
     $ ttranspose [0, 1, 2, 3]
     $ ttranspose [1, 2, 3, 0]
     $ ttranspose [3, 0, 2, 1]
     $ treshape [2, 2, 8, 4]
     $ ttranspose [0, 1, 2, 3]
     $ ttranspose [1, 2, 3, 0]
     $ ttranspose [1, 0, 3, 2]
     $ ttranspose [0, 1, 2, 3, 4, 5, 6, 7, 9, 8]
     $ ttranspose [0, 1, 2, 3, 7, 5, 6, 4]
     $ ttranspose [0, 1, 2, 3, 4, 5, 6]
     $ ttranspose [5, 0, 1, 2, 3, 4]
     $ ttranspose [0, 1, 2, 4, 3, 5, 6, 7, 9, 8]
     $ ttranspose []
     $ ttranspose [0]
     $ ttranspose [0, 1]
     $ ttranspose [1, 0]
     $ ttranspose [0, 1, 7, 4, 5, 3, 6, 2, 8]
     $ t)

testGatherTranspose33 :: Assertion
testGatherTranspose33 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,2,2,1,2,2,2,2,2,1] [81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002])
    (rev' @(OR.Array 2 Double) gatherTranspose33 t128)

-- These are different terms, but they should have similar lengths,
-- because they differ only by single transpose and reshape, most probably,
-- and all the rest of the element reordering should cancel out.
-- Still, probably impossible to lower the gap to zero.
testGatherSimp33 :: Assertion
testGatherSimp33 = do
  resetVarCOunter
  let !t1 = simplifyAst @Float
                 $ gatherTranspose33
                 $ AstVar [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (AstVarName 0)
  resetVarCOunter
  let !t2 = simplifyAst @Float
                   $ (\t -> tmatmul2 (treshape [6, 8] (tconst t48))
                              (treshape @(Ast 0 Float) @10 [8, 16] t))
                   $ AstVar [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (AstVarName 0)
  (length (show t1) - length (show t2)) @?= 4729
