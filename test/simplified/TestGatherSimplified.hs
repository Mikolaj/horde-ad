{-# LANGUAGE ImpredicativeTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestGatherSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstSimplify
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps

import CrossTesting

testTrees :: [TestTree]
testTrees =
  [ testCase "gatherNested1" testGatherNested1
  , testCase "gatherNestedBuild1" testGatherNestedBuild1
  , testCase "gather1" testGather1
  , testCase "gatherBuild1" testGatherBuild1
  , testCase "gatherSimp1" testGatherSimp1
  , testCase "gatherNested2" testGatherNested2
  , testCase "gatherNestedBuild2" testGatherNestedBuild2
  , testCase "gather2" testGather2
  , testCase "gatherBuild2" testGatherBuild2
  , testCase "gatherSimp2" testGatherSimp2
  , testCase "gatherNested12" testGatherNested12
  , testCase "gatherNestedBuild12" testGatherNestedBuild12
  , testCase "gather12" testGather12
  , testCase "gatherBuild12" testGatherBuild12
  , testCase "gatherSimp12" testGatherSimp12
  , testCase "gatherReshape22" testGatherReshape22
  , testCase "gatherReshapeBuild22" testGatherReshapeBuild22
  , testCase "gatherSimp22" testGatherSimp22
  , testCase "gatherSimp23" testGatherSimp23
  , testCase "gatherTranspose33" testGatherTranspose33
  , testCase "gatherTransposeBuild33" testGatherTransposeBuild33
  , testCase "gatherSimp33" testGatherSimp33
  , testCase "gatherSimp34" testGatherSimp34

  , testCase "scatterNested1" testScatterNested1
  , testCase "scatterNestedBuild1" testScatterNestedBuild1
  , testCase "scatter1" testScatter1
  , testCase "scatterBuild1" testScatterBuild1
  , testCase "scatterSimp1" testScatterSimp1
  , testCase "scatterNested2" testScatterNested2
  , testCase "scatterNestedBuild2" testScatterNestedBuild2
  , testCase "scatter2" testScatter2
  , testCase "scatterBuild2" testScatterBuild2
  , testCase "scatterSimp2" testScatterSimp2
  , testCase "scatterNested12" testScatterNested12
  , testCase "scatterNestedBuild12" testScatterNestedBuild12
  , testCase "scatter12" testScatter12
  , testCase "scatterBuild12" testScatterBuild12
  , testCase "scatterSimp12" testScatterSimp12
  ]

gatherNested1 :: forall ranked r. ADReady ranked r
              => ranked r 2 -> ranked r 1
gatherNested1 t =
  tgather @ranked @r @1
          (2 :$ ZS)
          (tgather @ranked @r @1
                   (4 :$ 2 :$ ZS) t
                   (\(k3 :. ZI) -> k3 :. ZI))
          (\(i2 :. ZI) -> i2 + i2 :. i2 :. ZI)

testGatherNested1 :: Assertion
testGatherNested1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @1 gatherNested1
                               (treplicate 7 $ tfromList [0, 1]))

testGatherNestedBuild1 :: Assertion
testGatherNestedBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [3.0,1.0,1.0,1.0,1.0,3.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> tbuild1 5 (\i ->
             ifF (i >. 2) (gatherNested1 t) (t ! [i])))
          (treplicate 7 $ tfromList [0, 1]))

gather1 :: forall ranked r. ADReady ranked r
        => ranked r 2 -> ranked r 1
gather1 t =
  tgather @ranked @r @1
          (2 :$ ZS)
          t
          (\(i2 :. ZI) -> i2 + i2 :. i2 :. ZI)

testGather1 :: Assertion
testGather1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @1 gather1
                               (treplicate 7 $ tfromList [0, 1]))

testGatherBuild1 :: Assertion
testGatherBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [3.0,1.0,1.0,1.0,1.0,3.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> tbuild1 5 (\i ->
             ifF (i >. 2) (gather1 t) (t ! [i])))
          (treplicate 7 $ tfromList [0, 1]))

testGatherSimp1 :: Assertion
testGatherSimp1 = do
  resetVarCounter
  let !t1 = gatherNested1 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t1) @?= 358
  resetVarCounter
  let !t2 = gather1 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t2) @?= 250
  length (show (simplifyAst6 @Float t1))
    @?= length (show (simplifyAst6 @Float t2))

gatherNested2 :: forall ranked r. ADReady ranked r
              => ranked r 2 -> ranked r 2
gatherNested2 t =
  tgather @ranked @r @2
          (2 :$ 3 :$ ZS)
          (tgather @ranked @r @3
                   (2 :$ 3 :$ 4 :$ 2 :$ ZS) t
                   (\(k1 :. k2 :. k3 :. ZI) -> k1 + k2 + k3 :. ZI))
          (\(i1 :. i2 :. ZI) -> i1 :. i2 :. i1 + i2 :. i1 :. ZI)

testGatherNested2 :: Assertion
testGatherNested2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,1.0])
    (rev' @Double @2 gatherNested2
                               (treplicate 7 $ tfromList [0, 1]))

testGatherNestedBuild2 :: Assertion
testGatherNestedBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [6.0,0.0,0.0,0.0,6.0,6.0,0.0,0.0,6.0,6.0,0.0,0.0,0.0,6.0])
    (rev' @Double @3
          (\t -> tbuild1 4 (\i ->
             gatherNested2 (t * treplicate0N [7, 2] (tfromIndex0 i))))
          (treplicate 7 $ tfromList [0, 1]))

gather2 :: forall ranked r. ADReady ranked r
        => ranked r 2 -> ranked r 2
gather2 t =
  tgather @ranked @r @2
          (2 :$ 3 :$ ZS)
          t
          (\(i1 :. i2 :. ZI) -> i1 + i2 + i1 + i2 :. i1 :. ZI)

testGather2 :: Assertion
testGather2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,1.0])
    (rev' @Double @2 gather2
                               (treplicate 7 $ tfromList [0, 1]))

testGatherBuild2 :: Assertion
testGatherBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [6.0,0.0,0.0,0.0,6.0,6.0,0.0,0.0,6.0,6.0,0.0,0.0,0.0,6.0])
    (rev' @Double @3
          (\t -> tbuild1 4 (\i ->
             gather2 (t * treplicate0N [7, 2] (tfromIndex0 i))))
          (treplicate 7 $ tfromList [0, 1]))

testGatherSimp2 :: Assertion
testGatherSimp2 = do
  resetVarCounter
  let !t1 = gatherNested2 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t1) @?= 628
  resetVarCounter
  let !t2 = gather2 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t2) @?= 333
  length (show (simplifyAst6 @Float t1)) @?= 333
  length (show (simplifyAst6 @Float t2)) @?= 333

gatherNested12 :: forall ranked r. ADReady ranked r
               => ranked r 2 -> ranked r 2
gatherNested12 t =
  tgather @ranked @r @1
          (2 :$ 4 :$ ZS)
          (tgather @ranked @r @3
                   (2 :$ 3 :$ 4 :$ ZS) t
                   (\(k1 :. k2 :. k3 :. ZI) -> k1 + k2 + k3 :. k1 :. ZI))
          (\(i1 :. ZI) -> i1 :. i1 + i1 :. ZI)

testGatherNested12 :: Assertion
testGatherNested12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @Double @2 gatherNested12
                               (treplicate 7 $ tfromList [0, 1]))

testGatherNestedBuild12 :: Assertion
testGatherNestedBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> tindex (tbuild1 5 (\i ->
             ifF (i >. 2) (gatherNested12 t)
                          (ttranspose [1, 0] $ treplicate 4 $ t ! [i]))) [1])
          (treplicate 7 $ tfromList [0, 1]))

gather12 :: forall ranked r. ADReady ranked r
         => ranked r 2 -> ranked r 2
gather12 t =
  tgather @ranked @r @2
          (2 :$ 4 :$ ZS)
          t
          (\(i1 :. k3 :. ZI) -> i1 + i1 + i1 + k3 :. i1 :. ZI)

testGather12 :: Assertion
testGather12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @Double @2 gather12
                               (treplicate 7 $ tfromList [0, 1]))

testGatherBuild12 :: Assertion
testGatherBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> tindex (tbuild1 5 (\i ->
             ifF (i >. 2) (gather12 t)
                          (ttranspose [1, 0] $ treplicate 4 $ t ! [i]))) [1])
          (treplicate 7 $ tfromList [0, 1]))

testGatherSimp12 :: Assertion
testGatherSimp12 = do
  resetVarCounter
  let !t1 = gatherNested12 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t1) @?= 542
  resetVarCounter
  let !t2 = gather12 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t2) @?= 333
  length (show (simplifyAst6 @Float t1)) @?= 333
  length (show (simplifyAst6 @Float t2)) @?= 333

gatherReshape22 :: forall ranked r. ADReady ranked r
                => ranked r 2 -> ranked r 2
gatherReshape22 t =
  treshape @ranked @r @6 [2, 6]
  $ treshape [3, 1, 2, 1, 1, 2]
  $ treshape @ranked @r @4 (1 :$ 12 :$ 1 :$ ZS)
  $ treshape @ranked @r @3 [3, 1, 1, 4]
  $ treshape [2, 2, 3] t

testGatherReshape22 :: Assertion
testGatherReshape22 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [6,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 gatherReshape22
                               (treplicate 6 $ tfromList [0, 1]))

testGatherReshapeBuild22 :: Assertion
testGatherReshapeBuild22 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [6,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> tbuild1 4 (\i ->
             gatherReshape22 (t * treplicate0N [6, 2] (tfromIndex0 i))))
          (treplicate 6 $ tfromList [0, 1]))

testGatherSimp22 :: Assertion
testGatherSimp22 = do
  resetVarCounter
  let !t1 = gatherReshape22 $ AstVar [6, 2] (intToAstVarId 100000000)
  length (show t1) @?= 52
  length (show (simplifyAst6 @Float t1)) @?= 52
  resetVarCounter
  let !t2 = treshape @AstRanked @Float @2 @2 [2, 6]
            $ AstVar [6, 2] (intToAstVarId 100000000)
  length (show t2) @?= 52
  length (show (simplifyAst6 @Float t2)) @?= 52

testGatherSimp23 :: Assertion
testGatherSimp23 = do
  resetVarCounter
  let !t1 = (\t -> tbuild1 4 (\i ->
              gatherReshape22
                (t * treplicate0N [6, 2] (tfromIndex0 i))))
            $ AstVar [6, 2] (intToAstVarId 100000000)
  length (show t1) @?= 224
  length (show (simplifyAst6 @Float t1)) @?= 576
  resetVarCounter
  let !t2 = (\t -> tbuild1 4 (\i ->
              treshape @AstRanked @Float @2 @2 [2, 6]
                (t * treplicate0N [6, 2] (tfromIndex0 i))))
            $ AstVar [6, 2] (intToAstVarId 100000000)
  length (show t2) @?= 224
  length (show (simplifyAst6 @Float t2)) @?= 576

-- Depending on if and how transpose it desugared, this may or may not result
-- in dozens of nested gathers that should vanish after simplification.
gatherTranspose33 :: forall ranked r. ADReady ranked r
                  => ranked r 10 -> ranked r 2
gatherTranspose33 t =
  tmatmul2 (treshape [6, 8] (tconst $ runFlip t48))
    (ttr
     $ treshape @ranked @r @4 [16, 8]
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
       t)

testGatherTranspose33 :: Assertion
testGatherTranspose33 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,2,2,1,2,2,2,2,2,1] [81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002])
    (rev' @Double @2 gatherTranspose33 t128)

testGatherTransposeBuild33 :: Assertion
testGatherTransposeBuild33 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,2,2,1,2,2,2,2,2,1] [487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012])
    (rev' @Double @3
          (\t -> tbuild1 4 (\i ->
             gatherTranspose33 (t * treplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (tfromIndex0 i))))
          t128)

-- These are different terms, but they should have similar lengths,
-- because they differ only by single transpose and reshape, most probably,
-- and all the rest of the element reordering should cancel out.
-- Still, probably impossible to lower the gap to zero.
testGatherSimp33 :: Assertion
testGatherSimp33 = do
  resetVarCounter
  let !t1 = gatherTranspose33
            $ AstVar [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (intToAstVarId 100000000)
  length (show t1) @?= 613
  length (show (simplifyAst6 @Float t1)) @?= 8447
  resetVarCounter
  let !t2 = (\t -> tmatmul2 (treshape [6, 8] (tconst $ runFlip t48))
                            (treshape @AstRanked @Float @10 [8, 16] t))
            $ AstVar [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (intToAstVarId 100000000)
  length (show t2) @?= 513
  length (show (simplifyAst6 @Float t2)) @?= 513

testGatherSimp34 :: Assertion
testGatherSimp34 = do
  resetVarCounter
  let !t1 = (\t -> tbuild1 4 (\i ->
             gatherTranspose33 (t * treplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (tfromIndex0 i))))
            $ AstVar [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (intToAstVarId 100000000)
  length (show t1) @?= 812
  length (show (simplifyAst6 @Float t1)) @?= 16003
  resetVarCounter
  let !t2 = (\t -> tbuild1 4 (\i ->
              (\t' -> tmatmul2 (treshape [6, 8] (tconst $ runFlip t48))
                               (treshape @AstRanked @Float @10 [8, 16] t'))
                (t * treplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (tfromIndex0 i))))
            $ AstVar [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (intToAstVarId 100000000)
  length (show t2) @?= 708
  length (show (simplifyAst6 @Float t2)) @?= 1062

-- scatters instead of gathers

scatterNested1 :: forall ranked r. ADReady ranked r
               => ranked r 2 -> ranked r 1
scatterNested1 t =
  tscatter @ranked @r @2
          (2 :$ ZS)
          (tscatter @ranked @r @1
                   (7 :$ 2 :$ ZS) t
                   (\(k3 :. ZI) -> k3 :. ZI))
          (\(i1 :. i2 :. ZI) -> i2 `quot` (1 + i1) :. ZI)

testScatterNested1 :: Assertion
testScatterNested1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @1 scatterNested1 (treplicate 7 $ tfromList [0, 1]))

testScatterNestedBuild1 :: Assertion
testScatterNestedBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [3.0,3.0,3.0,3.0,3.0,3.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0])
    (rev' @Double @2
          (\t -> tbuild1 5 (\i ->
             ifF (i >. 2) (scatterNested1 t) (t ! [i])))
          (treplicate 7 $ tfromList [0, 1]))

scatter1 :: forall ranked r. ADReady ranked r
         => ranked r 2 -> ranked r 1
scatter1 t =
  tscatter @ranked @r @2
          (2 :$ ZS)
          t
          (\(i1 :. i2 :. ZI) -> minF (i2 + 2 * i1) 1 :. ZI)

testScatter1 :: Assertion
testScatter1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @1 scatter1 (treplicate 7 $ tfromList [0, 1]))

testScatterBuild1 :: Assertion
testScatterBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [3.0,3.0,3.0,3.0,3.0,3.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0])
    (rev' @Double @2
          (\t -> tbuild1 5 (\i ->
             ifF (i >. 2) (scatter1 t) (t ! [i])))
          (treplicate 7 $ tfromList [0, 1]))

testScatterSimp1 :: Assertion
testScatterSimp1 = do
  resetVarCounter
  let !t1 = scatterNested1 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t1) @?= 364
  resetVarCounter
  let !t2 = scatter1 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t2) @?= 519
  length (show (simplifyAst6 @Float t1)) @?= 364
  length (show (simplifyAst6 @Float t2)) @?= 519

scatterNested2 :: forall ranked r. ADReady ranked r
              => ranked r 2 -> ranked r 2
scatterNested2 t =
  tscatter @ranked @r @4
          (2 :$ 3 :$ ZS)
          (tscatter @ranked @r @1
                   (2 :$ 3 :$ 4 :$ 2 :$ ZS) t
                   (\(k1 :. ZI) -> minF k1 1 :. minF k1 2  :. minF k1 3 :. ZI))
          (\(i1 :. i2 :. _i3 :. i4 :. ZI) ->
            minF (i1 + i2) 1 :. minF (i4 + i1) 2 :. ZI)

testScatterNested2 :: Assertion
testScatterNested2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatterNested2
                               (treplicate 7 $ tfromList [0, 1]))

testScatterNestedBuild2 :: Assertion
testScatterNestedBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> tbuild1 4 (\i ->
             scatterNested2 (t * treplicate0N [7, 2] (tfromIndex0 i))))
          (treplicate 7 $ tfromList [0, 1]))

scatter2 :: forall ranked r. ADReady ranked r
        => ranked r 2 -> ranked r 2
scatter2 t =
  tscatter @ranked @r @2
          (2 :$ 3 :$ ZS)
          t
          (\(i1 :. i2 :. ZI) -> minF (i1 + i2 + i1 + i2) 1 :. minF i1 2 :. ZI)

testScatter2 :: Assertion
testScatter2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatter2
                               (treplicate 7 $ tfromList [0, 1]))

testScatterBuild2 :: Assertion
testScatterBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> tbuild1 4 (\i ->
             scatter2 (t * treplicate0N [7, 2] (tfromIndex0 i))))
          (treplicate 7 $ tfromList [0, 1]))

testScatterSimp2 :: Assertion
testScatterSimp2 = do
  resetVarCounter
  let !t1 = scatterNested2 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t1) @?= 1601
  resetVarCounter
  let !t2 = scatter2 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t2) @?= 806
  length (show (simplifyAst6 @Float t1)) @?= 1601
  length (show (simplifyAst6 @Float t2)) @?= 806

scatterNested12 :: forall ranked r. ADReady ranked r
               => ranked r 2 -> ranked r 2
scatterNested12 t =
  tscatter @ranked @r @2
          (2 :$ 4 :$ ZS)
          (tscatter @ranked @r @2
                   (2 :$ 3 :$ 4 :$ ZS) t
                   (\(k1 :. k2 :. ZI) ->
                     minF k1 1 :. minF (k2 + k1) 2 :. minF k1 3 :. ZI))
          (\(i1 :. _i2 :. ZI) -> minF (i1 + i1) 1 :. ZI)

testScatterNested12 :: Assertion
testScatterNested12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatterNested12
                               (treplicate 7 $ tfromList [0, 1]))

testScatterNestedBuild12 :: Assertion
testScatterNestedBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> tindex (tbuild1 5 (\i ->
             ifF (i >. 2) (scatterNested12 t)
                          (ttranspose [1, 0] $ treplicate 4 $ t ! [i]))) [1])
          (treplicate 7 $ tfromList [0, 1]))

scatter12 :: forall ranked r. ADReady ranked r
         => ranked r 2 -> ranked r 2
scatter12 t =
  tscatter @ranked @r @2
          (2 :$ 4 :$ ZS)
          t
          (\(i1 :. k3 :. ZI) -> minF (i1 + i1 + i1 + k3) 1 :. minF i1 3 :. ZI)

testScatter12 :: Assertion
testScatter12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatter12
                               (treplicate 7 $ tfromList [0, 1]))

testScatterBuild12 :: Assertion
testScatterBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> tindex (tbuild1 5 (\i ->
             ifF (i >. 2) (scatter12 t)
                          (ttranspose [1, 0] $ treplicate 4 $ t ! [i]))) [1])
          (treplicate 7 $ tfromList [0, 1]))

testScatterSimp12 :: Assertion
testScatterSimp12 = do
  resetVarCounter
  let !t1 = scatterNested12 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t1) @?= 1333
  resetVarCounter
  let !t2 = scatter12 $ AstVar [7, 2] (intToAstVarId 100000000)
  length (show t2) @?= 806
  length (show (simplifyAst6 @Float t1)) @?= 1333
  length (show (simplifyAst6 @Float t2)) @?= 806
