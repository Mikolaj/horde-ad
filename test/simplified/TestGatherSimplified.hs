{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Tests of the gather and scatter operations, operations that expand
-- to gather and fusion of all of these.
module TestGatherSimplified (testTrees) where

import Prelude

import Data.Int (Int64)
import GHC.Exts (IsList (..))
import Numeric.LinearAlgebra (Numeric)
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.AstFreshId (resetVarCounter)
import HordeAd.Internal.BackendOX (RepN (..))
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..), IntegralF (..))

import CrossTesting

testTrees :: [TestTree]
testTrees =
  [ testCase "gatherNested1" testGatherNested1
  , testCase "gatherNestedBuild1" testGatherNestedBuild1
  , testCase "gather1" testGather1
  , testCase "gatherBuild1" testGatherBuild1
  , testCase "gatherSimpPP1" testGatherSimpPP1
  , testCase "gatherNested02" testGatherNested02
  , testCase "gatherNested2" testGatherNested2
  , testCase "gatherNestedBuild2" testGatherNestedBuild2
  , testCase "gather2" testGather2
  , testCase "gatherBuild2" testGatherBuild2
  , testCase "gatherSimpPP2" testGatherSimpPP2
  , testCase "gatherNested12" testGatherNested12
  , testCase "gatherNestedBuild12" testGatherNestedBuild12
  , testCase "gather12" testGather12
  , testCase "gatherBuild12" testGatherBuild12
  , testCase "gatherSimpPP12" testGatherSimpPP12
  , testCase "gatherReshape22" testGatherReshape22
  , testCase "gatherReshapeBuild22" testGatherReshapeBuild22
  , testCase "gatherSimpPP22" testGatherSimpPP22
  , testCase "gatherSimpPP23" testGatherSimpPP23
  , testCase "gatherTranspose33" testGatherTranspose33
  , testCase "gatherTransposeBuild33" testGatherTransposeBuild33
  , testCase "gatherTransposeBuild331" testGatherTransposeBuild331
  , testCase "gatherTransposeBuild332" testGatherTransposeBuild332
  , testCase "gatherTransposeBuild333" testGatherTransposeBuild333
  , testCase "gatherTransposeBuild334" testGatherTransposeBuild334
  , testCase "gatherTransposeBuild335" testGatherTransposeBuild335
  , testCase "gatherTransposeBuild336" testGatherTransposeBuild336
  , testCase "gatherSimpPP33" testGatherSimpPP33
  , testCase "gatherSimpPP34" testGatherSimpPP34

  , testCase "scatterNested1" testScatterNested1
  , testCase "scatterNestedBuild1" testScatterNestedBuild1
  , testCase "scatter1" testScatter1
  , testCase "scatterBuild1" testScatterBuild1
  , testCase "scatterSimpPP1" testScatterSimpPP1
  , testCase "scatterNested2" testScatterNested2
  , testCase "scatterNestedBuild2" testScatterNestedBuild2
  , testCase "scatter2" testScatter2
  , testCase "scatterBuild2" testScatterBuild2
  , testCase "scatterSimpPP2" testScatterSimpPP2
  , testCase "scatterNested12" testScatterNested12
  , testCase "scatterNestedBuild12" testScatterNestedBuild12
  , testCase "scatter12" testScatter12
  , testCase "scatterBuild12" testScatterBuild12
  , testCase "scatterSimpPP12" testScatterSimpPP12
  ]

gatherNested1 :: forall target r. (ADReady target, GoodScalar r)
              => target (TKR r 2) -> target (TKR r 1)
gatherNested1 t =
  rgather @target @r @1
          (2 :$: ZSR)
          (rgather @target @r @1
                   (4 :$: 2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 :.: ZIR))
          (\(i2 :.: ZIR) -> i2 + i2 :.: i2 :.: ZIR)

testGatherNested1 :: Assertion
testGatherNested1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @1 gatherNested1
                               (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherNestedBuild1 :: Assertion
testGatherNestedBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [3.0,1.0,1.0,1.0,1.0,3.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifF (i >. 2) (gatherNested1 t) (t ! [i])))
          (rreplicate 7 $ ringestData [2] [0, 1]))

gather1 :: forall target r. (ADReady target, GoodScalar r)
        => target (TKR r 2) -> target (TKR r 1)
gather1 t =
  rgather @target @r @1
          (2 :$: ZSR)
          t
          (\(i2 :.: ZIR) -> i2 + i2 :.: i2 :.: ZIR)

testGather1 :: Assertion
testGather1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @1 gather1
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherBuild1 :: Assertion
testGatherBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [3.0,1.0,1.0,1.0,1.0,3.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifF (i >. 2) (gather1 t) (t ! [i])))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherSimpPP1 :: Assertion
testGatherSimpPP1 = do
  resetVarCounter
  let !t1 = gatherNested1 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 210
  resetVarCounter
  let !t2 = gather1 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 210
  length (show (simplifyInline @(TKR Float 1) t1))
    @?= length (show (simplifyInline @(TKR Float 1) t2))

gatherNested02 :: forall target r. (ADReady target, GoodScalar r)
               => target (TKR r 1) -> target (TKR r 1)
gatherNested02 t =
  rgather @target @r @1
          (1 :$: ZSR)
          (rgather @target @r @1
                   (2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 + k3 :.: ZIR))
          (\(i1 :.: ZIR) -> i1 + i1 + i1 :.: ZIR)

testGatherNested02 :: Assertion
testGatherNested02 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [4] [1.0,0.0,0.0,0.0])
    (rev' @Double @1 gatherNested02 (rreplicate 4 (rscalar 0.1)))

gatherNested2 :: forall target r. (ADReady target, GoodScalar r)
              => target (TKR r 2) -> target (TKR r 2)
gatherNested2 t =
  rgather @target @r @2
          (2 :$: 3 :$: ZSR)
          (rgather @target @r @3
                   (2 :$: 3 :$: 4 :$: 2 :$: ZSR) t
                   (\(k1 :.: k2 :.: k3 :.: ZIR) -> k1 + k2 + k3 :.: ZIR))
          (\(i1 :.: i2 :.: ZIR) -> i1 :.: i2 :.: i1 + i2 :.: i1 :.: ZIR)

testGatherNested2 :: Assertion
testGatherNested2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,1.0])
    (rev' @Double @2 gatherNested2
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherNestedBuild2 :: Assertion
testGatherNestedBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,0.0,0.0,0.0,6.0,6.0,0.0,0.0,6.0,6.0,0.0,0.0,0.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherNested2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

gather2 :: forall target r. (ADReady target, GoodScalar r)
        => target (TKR r 2) -> target (TKR r 2)
gather2 t =
  rgather @target @r @2
          (2 :$: 3 :$: ZSR)
          t
          (\(i1 :.: i2 :.: ZIR) -> i1 + i2 + i1 + i2 :.: i1 :.: ZIR)

testGather2 :: Assertion
testGather2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,1.0])
    (rev' @Double @2 gather2 (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherBuild2 :: Assertion
testGatherBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,0.0,0.0,0.0,6.0,6.0,0.0,0.0,6.0,6.0,0.0,0.0,0.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gather2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherSimpPP2 :: Assertion
testGatherSimpPP2 = do
  resetVarCounter
  let !t1 = gatherNested2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 392
  resetVarCounter
  let !t2 = gather2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 307
  length (show (simplifyInline @(TKR Float 2) t1)) @?= 307
  length (show (simplifyInline @(TKR Float 2) t2)) @?= 307

gatherNested12 :: forall target r. (ADReady target, GoodScalar r)
               => target (TKR r 2) -> target (TKR r 2)
gatherNested12 t =
  rgather @target @r @1
          (2 :$: 4 :$: ZSR)
          (rgather @target @r @3
                   (2 :$: 3 :$: 4 :$: ZSR) t
                   (\(k1 :.: k2 :.: k3 :.: ZIR) -> k1 + k2 + k3 :.: k1 :.: ZIR))
          (\(i1 :.: ZIR) -> i1 :.: i1 + i1 :.: ZIR)

testGatherNested12 :: Assertion
testGatherNested12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @Double @2 gatherNested12
                               (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherNestedBuild12 :: Assertion
testGatherNestedBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifF (i >. 2) (gatherNested12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

gather12 :: forall target r. (ADReady target, GoodScalar r)
         => target (TKR r 2) -> target (TKR r 2)
gather12 t =
  rgather @target @r @2
          (2 :$: 4 :$: ZSR)
          t
          (\(i1 :.: k3 :.: ZIR) -> i1 + i1 + i1 + k3 :.: i1 :.: ZIR)

testGather12 :: Assertion
testGather12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @Double @2 gather12
                               (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherBuild12 :: Assertion
testGatherBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifF (i >. 2) (gather12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherSimpPP12 :: Assertion
testGatherSimpPP12 = do
  resetVarCounter
  let !t1 = gatherNested12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 392
  resetVarCounter
  let !t2 = gather12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 307
  length (show (simplifyInline @(TKR Float 2) t1)) @?= 307
  length (show (simplifyInline @(TKR Float 2) t2)) @?= 307

gatherReshape22 :: forall target r. (ADReady target, GoodScalar r)
                => target (TKR r 2) -> target (TKR r 2)
gatherReshape22 t =
  rreshape @target @r @6 [2, 6]
  $ rreshape [3, 1, 2, 1, 1, 2]
  $ rreshape @target @r @4 (1 :$: 12 :$: 1 :$: ZSR)
  $ rreshape @target @r @3 [3, 1, 1, 4]
  $ rreshape [2, 2, 3] t

testGatherReshape22 :: Assertion
testGatherReshape22 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [6,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 gatherReshape22
                               (rreplicate 6 $ ringestData [2] [0, 1]))

testGatherReshapeBuild22 :: Assertion
testGatherReshapeBuild22 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [6,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherReshape22 (t * rreplicate0N [6, 2] (rfromIndex0 i))))
          (rreplicate 6 $ ringestData [2] [0, 1]))

testGatherSimpPP22 :: Assertion
testGatherSimpPP22 = do
  resetVarCounter
  let !t1 = gatherReshape22 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [6, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 59
  length (show (simplifyInline @(TKR Float 2) t1)) @?= 59
  resetVarCounter
  let !t2 = rreshape @(AstTensor AstMethodLet PrimalSpan) @Float @2 @2 [2, 6]
            $ AstVar (FTKR [6, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 59
  length (show (simplifyInline @(TKR Float 2) t2)) @?= 59

testGatherSimpPP23 :: Assertion
testGatherSimpPP23 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
              gatherReshape22 @(AstTensor AstMethodLet PrimalSpan)
                (t * rreplicate0N [6, 2] (rfromIndex0 i))))
            $ AstVar (FTKR [6, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 209
  length (show (simplifyInline @(TKR Float 3) t1)) @?= 545
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @(AstTensor AstMethodLet PrimalSpan) @Float @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (rfromIndex0 i))))
            $ AstVar (FTKR [6, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 209
  length (show (simplifyInline @(TKR Float 3) t2)) @?= 545

-- Depending on if and how transpose it desugared, this may or may not result
-- in dozens of nested gathers that should vanish after simplification.
gatherTranspose33 :: forall target r. (ADReady target, GoodScalar r, Numeric r, RealFloat r)
                  => target (TKR r 10) -> target (TKR r 2)
gatherTranspose33 t =
  rmatmul2 (rreshape [6, 8] (rconst $ runFlipR $ unRepN t48))
    (rtr
     $ rreshape @target @r @4 [16, 8]
     $ rtranspose [0, 1, 2]
     $ rtranspose [2, 0, 1]
     $ rtranspose [1, 2, 0]
     $ rtranspose [1, 0, 2]
     $ rtranspose [1, 0]
     $ rtranspose [0, 1, 2, 3]
     $ rtranspose [1, 2, 3, 0]
     $ rtranspose [3, 0, 2, 1]
     $ rreshape [2, 2, 8, 4]
     $ rtranspose [0, 1, 2, 3]
     $ rtranspose [1, 2, 3, 0]
     $ rtranspose [1, 0, 3, 2]
     $ rtranspose [0, 1, 2, 3, 4, 5, 6, 7, 9, 8]
     $ rtranspose [0, 1, 2, 3, 7, 5, 6, 4]
     $ rtranspose [0, 1, 2, 3, 4, 5, 6]
     $ rtranspose [5, 0, 1, 2, 3, 4]
     $ rtranspose [0, 1, 2, 4, 3, 5, 6, 7, 9, 8]
     $ rtranspose []
     $ rtranspose [0]
     $ rtranspose [0, 1]
     $ rtranspose [1, 0]
     $ rtranspose [0, 1, 7, 4, 5, 3, 6, 2, 8]
       t)

testGatherTranspose33 :: Assertion
testGatherTranspose33 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,2,2,1,2,2,2,2,2,1] [81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002])
    (rev' @Double @2 gatherTranspose33 t128)

testGatherTransposeBuild33 :: Assertion
testGatherTransposeBuild33 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,2,2,1,2,2,2,2,2,1] [487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherTranspose33 (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
          t128)

testGatherTransposeBuild331 :: Assertion
testGatherTransposeBuild331 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 3] [1,1,1,1,1,1])
    (rev' @Double @3
          (\t -> rbuild1 2 (\i ->
             rtranspose [1, 0] (t * rreplicate0N [2, 3] (rfromIndex0 i))))
          (ringestData [2, 3] [1,2,3,4,5,6]))

testGatherTransposeBuild332 :: Assertion
testGatherTransposeBuild332 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 3] [1,1,1,1,1,1])
    (rev' @Double @3
          (\t -> rbuild1 2 (\i ->
             rtranspose [1, 0] (t * rreplicate0N [2, 3] (rfromIndex0 i))))
          (ringestData [2, 3] [1,2,3,4,5,6]))

testGatherTransposeBuild333 :: Assertion
testGatherTransposeBuild333 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2] [1,1])
    (rev' @Double @2
          (\t -> rbuild1 2 (\i ->
             t * rreplicate0N [2] (rfromIndex0 i)))
          (ringestData [2] [0,0]))

testGatherTransposeBuild334 :: Assertion
testGatherTransposeBuild334 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 1] [1,1])
    (rev' @Double @3
          (\t -> rbuild1 2 (\i ->
             t * rreplicate 2 (rreplicate 1 (rfromIntegral (rfromPrimal i)))))
         (ringestData [2, 1] [1,2]))

testGatherTransposeBuild335 :: Assertion
testGatherTransposeBuild335 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 1] [1,1])
    (rev' @Double @3
          (\t ->
             rreplicate 2 t * rtranspose [2,0,1] (rreplicate 2 (rreplicate 1 (rfromIntegral @_ @Int64 (rconst $ Nested.rfromListPrimLinear (fromList [2]) [0, 1])))))
         (ringestData [2, 1] [1,2]))

testGatherTransposeBuild336 :: Assertion
testGatherTransposeBuild336 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 1] [1,1])
    (rev' @Double @3
          (\t ->
             rreplicate 2 t * rtranspose [2,0,1] (rreplicate 2 (rreplicate 1 (rfromList [0, 1]))))
         (ringestData [2, 1] [1,2]))

-- These are different terms, but they should have similar lengths,
-- because they differ only by single transpose and reshape, most probably,
-- and all the rest of the element reordering should cancel out.
-- Still, probably impossible to lower the gap to zero.
testGatherSimpPP33 :: Assertion
testGatherSimpPP33 = do
  resetVarCounter
  let !t1 = gatherTranspose33 @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 578
  length (show (simplifyInline @(TKR Float 2) t1)) @?= 578
  resetVarCounter
  let !t2 = (\t -> rmatmul2 (rreshape [6, 8] (rconst $ runFlipR $ unRepN t48))
                            (rreshape @(AstTensor AstMethodLet PrimalSpan) @Float @10 [8, 16] t))
            $ AstVar (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 497
  length (show (simplifyInline @(TKR Float 2) t2)) @?= 497

testGatherSimpPP34 :: Assertion
testGatherSimpPP34 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
             gatherTranspose33 @(AstTensor AstMethodLet PrimalSpan) (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstVar (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 925
  length (show (simplifyInline @(TKR Float 3) t1)) @?= 925
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              (\t' -> rmatmul2 (rreshape [6, 8] (rconst $ runFlipR $ unRepN t48))
                               (rreshape @(AstTensor AstMethodLet PrimalSpan) @Float @10 [8, 16] t'))
                (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstVar (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 678
  length (show (simplifyInline @(TKR Float 3) t2)) @?= 678

-- scatters instead of gathers

scatterNested1 :: forall target r. (ADReady target, GoodScalar r)
               => target (TKR r 2) -> target (TKR r 1)
scatterNested1 t =
  rscatter @target @r @2
          (2 :$: ZSR)
          (rscatter @target @r @1
                   (7 :$: 2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 :.: ZIR))
          (\(i1 :.: i2 :.: ZIR) -> i2 `quotF` (1 + i1) :.: ZIR)

testScatterNested1 :: Assertion
testScatterNested1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @1 scatterNested1 (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterNestedBuild1 :: Assertion
testScatterNestedBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [3.0,3.0,3.0,3.0,3.0,3.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifF (i >. 2) (scatterNested1 t) (t ! [i])))
          (rreplicate 7 $ ringestData [2] [0, 1]))

scatter1 :: forall target r. (ADReady target, GoodScalar r)
         => target (TKR r 2) -> target (TKR r 1)
scatter1 t =
  rscatter @target @r @2
          (2 :$: ZSR)
          t
          (\(i1 :.: i2 :.: ZIR) -> minF (i2 + 2 * i1) 1 :.: ZIR)

testScatter1 :: Assertion
testScatter1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @1 scatter1 (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterBuild1 :: Assertion
testScatterBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [3.0,3.0,3.0,3.0,3.0,3.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifF (i >. 2) (scatter1 t) (t ! [i])))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterSimpPP1 :: Assertion
testScatterSimpPP1 = do
  resetVarCounter
  let !t1 = scatterNested1 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 325
  resetVarCounter
  let !t2 = scatter1 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 486
  length (show (simplifyInline @(TKR Float 1) t1)) @?= 325
  length (show (simplifyInline @(TKR Float 1) t2)) @?= 486

scatterNested2 :: forall target r. (ADReady target, GoodScalar r)
              => target (TKR r 2) -> target (TKR r 2)
scatterNested2 t =
  rscatter @target @r @4
          (2 :$: 3 :$: ZSR)
          (rscatter @target @r @1
                   (2 :$: 3 :$: 4 :$: 2 :$: ZSR) t
                   (\(k1 :.: ZIR) -> minF k1 1 :.: minF k1 2  :.: minF k1 3 :.: ZIR))
          (\(i1 :.: i2 :.: _i3 :.: i4 :.: ZIR) ->
            minF (i1 + i2) 1 :.: minF (i4 + i1) 2 :.: ZIR)

testScatterNested2 :: Assertion
testScatterNested2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatterNested2
                               (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterNestedBuild2 :: Assertion
testScatterNestedBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             scatterNested2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

scatter2 :: forall target r. (ADReady target, GoodScalar r)
        => target (TKR r 2) -> target (TKR r 2)
scatter2 t =
  rscatter @target @r @2
          (2 :$: 3 :$: ZSR)
          t
          (\(i1 :.: i2 :.: ZIR) -> minF (i1 + i2 + i1 + i2) 1 :.: minF i1 2 :.: ZIR)

testScatter2 :: Assertion
testScatter2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatter2
                               (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterBuild2 :: Assertion
testScatterBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             scatter2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterSimpPP2 :: Assertion
testScatterSimpPP2 = do
  resetVarCounter
  let !t1 = scatterNested2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 1276
  resetVarCounter
  let !t2 = scatter2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 711
  length (show (simplifyInline @(TKR Float 2) t1)) @?= 1276
  length (show (simplifyInline @(TKR Float 2) t2)) @?= 711

scatterNested12 :: forall target r. (ADReady target, GoodScalar r)
               => target (TKR r 2) -> target (TKR r 2)
scatterNested12 t =
  rscatter @target @r @2
          (2 :$: 4 :$: ZSR)
          (rscatter @target @r @2
                   (2 :$: 3 :$: 4 :$: ZSR) t
                   (\(k1 :.: k2 :.: ZIR) ->
                     minF k1 1 :.: minF (k2 + k1) 2 :.: minF k1 3 :.: ZIR))
          (\(i1 :.: _i2 :.: ZIR) -> minF (i1 + i1) 1 :.: ZIR)

testScatterNested12 :: Assertion
testScatterNested12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatterNested12
                               (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterNestedBuild12 :: Assertion
testScatterNestedBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifF (i >. 2) (scatterNested12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

scatter12 :: forall target r. (ADReady target, GoodScalar r)
         => target (TKR r 2) -> target (TKR r 2)
scatter12 t =
  rscatter @target @r @2
          (2 :$: 4 :$: ZSR)
          t
          (\(i1 :.: k3 :.: ZIR) -> minF (i1 + i1 + i1 + k3) 1 :.: minF i1 3 :.: ZIR)

testScatter12 :: Assertion
testScatter12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatter12
                               (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterBuild12 :: Assertion
testScatterBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifF (i >. 2) (scatter12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterSimpPP12 :: Assertion
testScatterSimpPP12 = do
  resetVarCounter
  let !t1 = scatterNested12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 1080
  resetVarCounter
  let !t2 = scatter12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 711
  length (show (simplifyInline @(TKR Float 2) t1)) @?= 1080
  length (show (simplifyInline @(TKR Float 2) t2)) @?= 711
