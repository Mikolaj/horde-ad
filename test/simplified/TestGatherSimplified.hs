{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Tests of the gather and scatter operations, operations that expand
-- to gather and fusion of all of these.
module TestGatherSimplified (testTrees) where

import Prelude

import Data.Array.RankedS qualified as OR
import Data.Int (Int64)
import GHC.Exts (IsList (..))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal

import HordeAd
import HordeAd.Core.AstFreshId (resetVarCounter)
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

gatherNested1 :: forall ranked r. (ADReady ranked, GoodScalar r)
              => ranked r 2 -> ranked r 1
gatherNested1 t =
  rgather @ranked @r @1
          (2 :$: ZSR)
          (rgather @ranked @r @1
                   (4 :$: 2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 :.: ZIR))
          (\(i2 :.: ZIR) -> i2 + i2 :.: i2 :.: ZIR)

testGatherNested1 :: Assertion
testGatherNested1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @1 gatherNested1
                               (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherNestedBuild1 :: Assertion
testGatherNestedBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [3.0,1.0,1.0,1.0,1.0,3.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifF (i >. 2) (gatherNested1 t) (t ! [i])))
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

gather1 :: forall ranked r. (ADReady ranked, GoodScalar r)
        => ranked r 2 -> ranked r 1
gather1 t =
  rgather @ranked @r @1
          (2 :$: ZSR)
          t
          (\(i2 :.: ZIR) -> i2 + i2 :.: i2 :.: ZIR)

testGather1 :: Assertion
testGather1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @1 gather1
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherBuild1 :: Assertion
testGatherBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [3.0,1.0,1.0,1.0,1.0,3.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifF (i >. 2) (gather1 t) (t ! [i])))
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherSimpPP1 :: Assertion
testGatherSimpPP1 = do
  resetVarCounter
  let !t1 = gatherNested1 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 210
  resetVarCounter
  let !t2 = gather1 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 210
  length (show (simplifyInlineAst @Float t1))
    @?= length (show (simplifyInlineAst @Float t2))

gatherNested02 :: forall ranked r. (ADReady ranked, GoodScalar r)
               => ranked r 1 -> ranked r 1
gatherNested02 t =
  rgather @ranked @r @1
          (1 :$: ZSR)
          (rgather @ranked @r @1
                   (2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 + k3 :.: ZIR))
          (\(i1 :.: ZIR) -> i1 + i1 + i1 :.: ZIR)

testGatherNested02 :: Assertion
testGatherNested02 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [4] [1.0,0.0,0.0,0.0])
    (rev' @Double @1 gatherNested02 (FlipR $ treplicateR 4 0.1))

gatherNested2 :: forall ranked r. (ADReady ranked, GoodScalar r)
              => ranked r 2 -> ranked r 2
gatherNested2 t =
  rgather @ranked @r @2
          (2 :$: 3 :$: ZSR)
          (rgather @ranked @r @3
                   (2 :$: 3 :$: 4 :$: 2 :$: ZSR) t
                   (\(k1 :.: k2 :.: k3 :.: ZIR) -> k1 + k2 + k3 :.: ZIR))
          (\(i1 :.: i2 :.: ZIR) -> i1 :.: i2 :.: i1 + i2 :.: i1 :.: ZIR)

testGatherNested2 :: Assertion
testGatherNested2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,1.0])
    (rev' @Double @2 gatherNested2
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherNestedBuild2 :: Assertion
testGatherNestedBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [6.0,0.0,0.0,0.0,6.0,6.0,0.0,0.0,6.0,6.0,0.0,0.0,0.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherNested2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

gather2 :: forall ranked r. (ADReady ranked, GoodScalar r)
        => ranked r 2 -> ranked r 2
gather2 t =
  rgather @ranked @r @2
          (2 :$: 3 :$: ZSR)
          t
          (\(i1 :.: i2 :.: ZIR) -> i1 + i2 + i1 + i2 :.: i1 :.: ZIR)

testGather2 :: Assertion
testGather2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,1.0])
    (rev' @Double @2 gather2 (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherBuild2 :: Assertion
testGatherBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [6.0,0.0,0.0,0.0,6.0,6.0,0.0,0.0,6.0,6.0,0.0,0.0,0.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gather2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherSimpPP2 :: Assertion
testGatherSimpPP2 = do
  resetVarCounter
  let !t1 = gatherNested2 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 392
  resetVarCounter
  let !t2 = gather2 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 307
  length (show (simplifyInlineAst @Float t1)) @?= 307
  length (show (simplifyInlineAst @Float t2)) @?= 307

gatherNested12 :: forall ranked r. (ADReady ranked, GoodScalar r)
               => ranked r 2 -> ranked r 2
gatherNested12 t =
  rgather @ranked @r @1
          (2 :$: 4 :$: ZSR)
          (rgather @ranked @r @3
                   (2 :$: 3 :$: 4 :$: ZSR) t
                   (\(k1 :.: k2 :.: k3 :.: ZIR) -> k1 + k2 + k3 :.: k1 :.: ZIR))
          (\(i1 :.: ZIR) -> i1 :.: i1 + i1 :.: ZIR)

testGatherNested12 :: Assertion
testGatherNested12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @Double @2 gatherNested12
                               (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherNestedBuild12 :: Assertion
testGatherNestedBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifF (i >. 2) (gatherNested12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

gather12 :: forall ranked r. (ADReady ranked, GoodScalar r)
         => ranked r 2 -> ranked r 2
gather12 t =
  rgather @ranked @r @2
          (2 :$: 4 :$: ZSR)
          t
          (\(i1 :.: k3 :.: ZIR) -> i1 + i1 + i1 + k3 :.: i1 :.: ZIR)

testGather12 :: Assertion
testGather12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @Double @2 gather12
                               (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherBuild12 :: Assertion
testGatherBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifF (i >. 2) (gather12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testGatherSimpPP12 :: Assertion
testGatherSimpPP12 = do
  resetVarCounter
  let !t1 = gatherNested12 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 392
  resetVarCounter
  let !t2 = gather12 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 307
  length (show (simplifyInlineAst @Float t1)) @?= 307
  length (show (simplifyInlineAst @Float t2)) @?= 307

gatherReshape22 :: forall ranked r. (ADReady ranked, GoodScalar r)
                => ranked r 2 -> ranked r 2
gatherReshape22 t =
  rreshape @ranked @r @6 [2, 6]
  $ rreshape [3, 1, 2, 1, 1, 2]
  $ rreshape @ranked @r @4 (1 :$: 12 :$: 1 :$: ZSR)
  $ rreshape @ranked @r @3 [3, 1, 1, 4]
  $ rreshape [2, 2, 3] t

testGatherReshape22 :: Assertion
testGatherReshape22 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [6,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 gatherReshape22
                               (FlipR $ treplicateR 6 $ tfromListR [0, 1]))

testGatherReshapeBuild22 :: Assertion
testGatherReshapeBuild22 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [6,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherReshape22 (t * rreplicate0N [6, 2] (rfromIndex0 i))))
          (FlipR $ treplicateR 6 $ tfromListR [0, 1]))

testGatherSimpPP22 :: Assertion
testGatherSimpPP22 = do
  resetVarCounter
  let !t1 = gatherReshape22 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [6, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 59
  length (show (simplifyInlineAst @Float t1)) @?= 59
  resetVarCounter
  let !t2 = rreshape @(AstRanked PrimalSpan) @Float @2 @2 [2, 6]
            $ AstRanked $ AstVar (FTKR [6, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 59
  length (show (simplifyInlineAst @Float t2)) @?= 59

testGatherSimpPP23 :: Assertion
testGatherSimpPP23 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
              gatherReshape22 @(AstRanked PrimalSpan)
                (t * rreplicate0N [6, 2] (rfromIndex0 i))))
            $ AstRanked $ AstVar (FTKR [6, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 209
  length (show (simplifyInlineAst @Float t1)) @?= 209
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @(AstRanked PrimalSpan) @Float @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (rfromIndex0 i))))
            $ AstRanked $ AstVar (FTKR [6, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 209
  length (show (simplifyInlineAst @Float t2)) @?= 209

-- Depending on if and how transpose it desugared, this may or may not result
-- in dozens of nested gathers that should vanish after simplification.
gatherTranspose33 :: forall ranked r. (ADReady ranked, GoodScalar r, RealFloat r)
                  => ranked r 10 -> ranked r 2
gatherTranspose33 t =
  rmatmul2 (rreshape [6, 8] (rconst $ Nested.rfromOrthotope SNat $ runFlipR t48OR))
    (rtr
     $ rreshape @ranked @r @4 [16, 8]
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
    (OR.fromList [1,2,2,1,2,2,2,2,2,1] [81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,81.3003,71.0,80.0,79.0,80.0,79.0,80.0,79.0,80.0,79.0,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,166.8003,137.70326,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002,186.1003,162.3889400002])
    (rev' @Double @2 gatherTranspose33 t128OR)

testGatherTransposeBuild33 :: Assertion
testGatherTransposeBuild33 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,2,2,1,2,2,2,2,2,1] [487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,487.80179999999996,426.0,480.0,474.0,480.0,474.0,480.0,474.0,480.0,474.0,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1000.8018,826.21956,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012,1116.6018,974.3336400012])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherTranspose33 (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
          t128OR)

testGatherTransposeBuild331 :: Assertion
testGatherTransposeBuild331 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 3] [1,1,1,1,1,1])
    (rev' @Double @3
          (\t -> rbuild1 2 (\i ->
             rtranspose [1, 0] (t * rreplicate0N [2, 3] (rfromIndex0 i))))
          (FlipR $ OR.fromList [2, 3] [1,2,3,4,5,6]))

testGatherTransposeBuild332 :: Assertion
testGatherTransposeBuild332 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 3] [1,1,1,1,1,1])
    (rev' @Double @3
          (\t -> rbuild1 2 (\i ->
             rtranspose [1, 0] (t * rreplicate0N [2, 3] (rfromIndex0 i))))
          (FlipR $ OR.fromList [2, 3] [1,2,3,4,5,6]))

testGatherTransposeBuild333 :: Assertion
testGatherTransposeBuild333 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2] [1,1])
    (rev' @Double @2
          (\t -> rbuild1 2 (\i ->
             (t * rreplicate0N [2] (rfromIndex0 i))))
          (FlipR $ OR.fromList [2] [0,0]))

testGatherTransposeBuild334 :: Assertion
testGatherTransposeBuild334 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1] [1,1])
    (rev' @Double @3
          (\t -> rbuild1 2 (\i ->
             t * rreplicate 2 (rreplicate 1 (rfromIntegral (rconstant i)))))
         (FlipR $ OR.fromList [2, 1] [1,2]))

testGatherTransposeBuild335 :: Assertion
testGatherTransposeBuild335 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1] [1,1])
    (rev' @Double @3
          (\t ->
             rreplicate 2 t * rtranspose [2,0,1] (rreplicate 2 (rreplicate 1 (rfromIntegral @_ @Int64 (rconst $ Nested.Internal.rfromListPrimLinear (fromList [2]) [0, 1])))))
         (FlipR $ OR.fromList [2, 1] [1,2]))

testGatherTransposeBuild336 :: Assertion
testGatherTransposeBuild336 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1] [1,1])
    (rev' @Double @3
          (\t ->
             rreplicate 2 t * rtranspose [2,0,1] (rreplicate 2 (rreplicate 1 (rfromList [0, 1]))))
         (FlipR $ OR.fromList [2, 1] [1,2]))

-- These are different terms, but they should have similar lengths,
-- because they differ only by single transpose and reshape, most probably,
-- and all the rest of the element reordering should cancel out.
-- Still, probably impossible to lower the gap to zero.
testGatherSimpPP33 :: Assertion
testGatherSimpPP33 = do
  resetVarCounter
  let !t1 = gatherTranspose33 @(AstRanked PrimalSpan)
            $ AstRanked $ AstVar (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 578
  length (show (simplifyInlineAst @Float t1)) @?= 578
  resetVarCounter
  let !t2 = (\t -> rmatmul2 (rreshape [6, 8] (rconst $ Nested.rfromOrthotope SNat $ runFlipR t48OR))
                            (rreshape @(AstRanked PrimalSpan) @Float @10 [8, 16] t))
            $ AstRanked $ AstVar (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 497
  length (show (simplifyInlineAst @Float t2)) @?= 497

testGatherSimpPP34 :: Assertion
testGatherSimpPP34 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
             gatherTranspose33 @(AstRanked PrimalSpan) (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstRanked $ AstVar (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 925
  length (show (simplifyInlineAst @Float t1)) @?= 925
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              (\t' -> rmatmul2 (rreshape [6, 8] (rconst $ Nested.rfromOrthotope SNat $ runFlipR t48OR))
                               (rreshape @(AstRanked PrimalSpan) @Float @10 [8, 16] t'))
                (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstRanked $ AstVar (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 678
  length (show (simplifyInlineAst @Float t2)) @?= 678

-- scatters instead of gathers

scatterNested1 :: forall ranked r. (ADReady ranked, GoodScalar r)
               => ranked r 2 -> ranked r 1
scatterNested1 t =
  rscatter @ranked @r @2
          (2 :$: ZSR)
          (rscatter @ranked @r @1
                   (7 :$: 2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 :.: ZIR))
          (\(i1 :.: i2 :.: ZIR) -> i2 `quotF` (1 + i1) :.: ZIR)

testScatterNested1 :: Assertion
testScatterNested1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @1 scatterNested1 (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterNestedBuild1 :: Assertion
testScatterNestedBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [3.0,3.0,3.0,3.0,3.0,3.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifF (i >. 2) (scatterNested1 t) (t ! [i])))
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

scatter1 :: forall ranked r. (ADReady ranked, GoodScalar r)
         => ranked r 2 -> ranked r 1
scatter1 t =
  rscatter @ranked @r @2
          (2 :$: ZSR)
          t
          (\(i1 :.: i2 :.: ZIR) -> minF (i2 + 2 * i1) 1 :.: ZIR)

testScatter1 :: Assertion
testScatter1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @1 scatter1 (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterBuild1 :: Assertion
testScatterBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [3.0,3.0,3.0,3.0,3.0,3.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifF (i >. 2) (scatter1 t) (t ! [i])))
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterSimpPP1 :: Assertion
testScatterSimpPP1 = do
  resetVarCounter
  let !t1 = scatterNested1 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 325
  resetVarCounter
  let !t2 = scatter1 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 486
  length (show (simplifyInlineAst @Float t1)) @?= 325
  length (show (simplifyInlineAst @Float t2)) @?= 486

scatterNested2 :: forall ranked r. (ADReady ranked, GoodScalar r)
              => ranked r 2 -> ranked r 2
scatterNested2 t =
  rscatter @ranked @r @4
          (2 :$: 3 :$: ZSR)
          (rscatter @ranked @r @1
                   (2 :$: 3 :$: 4 :$: 2 :$: ZSR) t
                   (\(k1 :.: ZIR) -> minF k1 1 :.: minF k1 2  :.: minF k1 3 :.: ZIR))
          (\(i1 :.: i2 :.: _i3 :.: i4 :.: ZIR) ->
            minF (i1 + i2) 1 :.: minF (i4 + i1) 2 :.: ZIR)

testScatterNested2 :: Assertion
testScatterNested2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatterNested2
                               (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterNestedBuild2 :: Assertion
testScatterNestedBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             scatterNested2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

scatter2 :: forall ranked r. (ADReady ranked, GoodScalar r)
        => ranked r 2 -> ranked r 2
scatter2 t =
  rscatter @ranked @r @2
          (2 :$: 3 :$: ZSR)
          t
          (\(i1 :.: i2 :.: ZIR) -> minF (i1 + i2 + i1 + i2) 1 :.: minF i1 2 :.: ZIR)

testScatter2 :: Assertion
testScatter2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatter2
                               (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterBuild2 :: Assertion
testScatterBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             scatter2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterSimpPP2 :: Assertion
testScatterSimpPP2 = do
  resetVarCounter
  let !t1 = scatterNested2 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 1276
  resetVarCounter
  let !t2 = scatter2 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 711
  length (show (simplifyInlineAst @Float t1)) @?= 1276
  length (show (simplifyInlineAst @Float t2)) @?= 711

scatterNested12 :: forall ranked r. (ADReady ranked, GoodScalar r)
               => ranked r 2 -> ranked r 2
scatterNested12 t =
  rscatter @ranked @r @2
          (2 :$: 4 :$: ZSR)
          (rscatter @ranked @r @2
                   (2 :$: 3 :$: 4 :$: ZSR) t
                   (\(k1 :.: k2 :.: ZIR) ->
                     minF k1 1 :.: minF (k2 + k1) 2 :.: minF k1 3 :.: ZIR))
          (\(i1 :.: _i2 :.: ZIR) -> minF (i1 + i1) 1 :.: ZIR)

testScatterNested12 :: Assertion
testScatterNested12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatterNested12
                               (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterNestedBuild12 :: Assertion
testScatterNestedBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifF (i >. 2) (scatterNested12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

scatter12 :: forall ranked r. (ADReady ranked, GoodScalar r)
         => ranked r 2 -> ranked r 2
scatter12 t =
  rscatter @ranked @r @2
          (2 :$: 4 :$: ZSR)
          t
          (\(i1 :.: k3 :.: ZIR) -> minF (i1 + i1 + i1 + k3) 1 :.: minF i1 3 :.: ZIR)

testScatter12 :: Assertion
testScatter12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatter12
                               (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterBuild12 :: Assertion
testScatterBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifF (i >. 2) (scatter12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (FlipR $ treplicateR 7 $ tfromListR [0, 1]))

testScatterSimpPP12 :: Assertion
testScatterSimpPP12 = do
  resetVarCounter
  let !t1 = scatterNested12 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t1) @?= 1080
  resetVarCounter
  let !t2 = scatter12 @(AstRanked PrimalSpan) $ AstRanked $ AstVar (FTKR [7, 2]) (mkAstVarName . intToAstVarId $ 100000000)
  length (show t2) @?= 711
  length (show (simplifyInlineAst @Float t1)) @?= 1080
  length (show (simplifyInlineAst @Float t2)) @?= 711
