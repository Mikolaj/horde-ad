{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Tests of the gather and scatter operations and of operations that expand
-- to gather and of fusion of all of them.
module TestGatherSimplified (testTrees) where

import Prelude

import Data.Int (Int64)
import GHC.Exts (IsList (..))
import GHC.TypeLits (Div, KnownNat, type (<=))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape

import HordeAd
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (resetVarCounter)
import HordeAd.Core.AstInterpret
import HordeAd.Core.CarriersAst
import HordeAd.Core.Ops

import CrossTesting
import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "gatherNested1" testGatherNested1
  , testCase "gatherNestedBuild1" testGatherNestedBuild1
  , testCase "gather1" testGather1
  , testCase "gatherBuild1" testGatherBuild1
  , testCase "gatherSimpPP1" testGatherSimpPP1
  , testCase "gatherSimp1" testGatherSimp1
  , testCase "gatherNested02" testGatherNested02
  , testCase "gatherNested2" testGatherNested2
  , testCase "gatherNestedBuild2" testGatherNestedBuild2
  , testCase "gather2" testGather2
  , testCase "gatherBuild2" testGatherBuild2
  , testCase "gatherSimpPP2" testGatherSimpPP2
  , testCase "gatherSimp2" testGatherSimp2
  , testCase "gatherNested12" testGatherNested12
  , testCase "gatherNestedBuild12" testGatherNestedBuild12
  , testCase "gather12" testGather12
  , testCase "gatherBuild12" testGatherBuild12
  , testCase "gatherSimpPP12" testGatherSimpPP12
  , testCase "gatherSimp12" testGatherSimp12
  , testCase "gatherReshape22" testGatherReshape22
  , testCase "gatherReshapeBuild22" testGatherReshapeBuild22
  , testCase "gatherSimpPP22" testGatherSimpPP22
  , testCase "gatherSimp22" testGatherSimp22
  , testCase "gatherSimpPP23" testGatherSimpPP23
  , testCase "gatherSimp23" testGatherSimp23
  , testCase "gatherTranspose33" testGatherTranspose33
  , testCase "gatherTransposeBuild33" testGatherTransposeBuild33
  , testCase "gatherTransposeBuild33PP" testGatherTransposeBuild33PP
  , testCase "gatherTransposeBuild331" testGatherTransposeBuild331
  , testCase "gatherTransposeBuild332" testGatherTransposeBuild332
  , testCase "gatherTransposeBuild333" testGatherTransposeBuild333
  , testCase "gatherTransposeBuild334" testGatherTransposeBuild334
  , testCase "gatherTransposeBuild335" testGatherTransposeBuild335
  , testCase "gatherTransposeBuild336" testGatherTransposeBuild336
  , testCase "gatherSimpPP33" testGatherSimpPP33
  , testCase "gatherSimpPP34" testGatherSimpPP34
{- TODO: re-enable the tests once we drop GHC 9.10
   (they don't type-check with 9.10)
  , testCase "gatherCond" testGatherCond
  , testCase "gatherCondBuild" testGatherCondBuild
  , testCase "gatherCond2" testGatherCond2
  , testCase "gatherCondBuild2" testGatherCondBuild2
  , testCase "gatherSimpCond" testGatherSimpCond
  , testCase "gatherCond3" testGatherCond3
  , testCase "gatherCondBuild3" testGatherCondBuild3
  , testCase "gatherCond4" testGatherCond4
  , testCase "gatherCondBuild4" testGatherCondBuild4
  , testCase "gatherSimpCond3" testGatherSimpCond3
  , testCase "gatherCond5" testGatherCond5
  , testCase "gatherCondBuild5" testGatherCondBuild5
  , testCase "gatherCond6" testGatherCond6
  , testCase "gatherCondBuild6" testGatherCondBuild6
  , testCase "gatherSimpCond5" testGatherSimpCond5
-}

  , testCase "scatterNested1" testScatterNested1
  , testCase "scatterNestedBuild1" testScatterNestedBuild1
  , testCase "scatter1" testScatter1
  , testCase "scatterBuild1" testScatterBuild1
  , testCase "scatterSimpPP1" testScatterSimpPP1
  , testCase "scatterSimp1" testScatterSimp1
  , testCase "scatterNested2" testScatterNested2
  , testCase "scatterNestedBuild2" testScatterNestedBuild2
  , testCase "scatter2" testScatter2
  , testCase "scatterBuild2" testScatterBuild2
  , testCase "scatterSimpPP2" testScatterSimpPP2
  , testCase "scatterSimp2" testScatterSimp2
  , testCase "scatterNested12" testScatterNested12
  , testCase "scatterNestedBuild12" testScatterNestedBuild12
  , testCase "scatter12" testScatter12
  , testCase "scatterBuild12" testScatterBuild12
  , testCase "scatterBuild12b" testScatterBuild12b
  , testCase "scatterSimpPP12" testScatterSimpPP12
  , testCase "scatterSimp12" testScatterSimp12

  , testCase "shmatterBarReluADVal320" testBarReluADVal320
  , testCase "shmatterReluSimpPP" testReluSimpPP

  , testCase "sminimizedCNNOPP2" testCNNOPP2
  , testCase "sminimizedCNNOPP2b" testCNNOPP2b
--  , testCase "sminimizedCNNOPP3" testCNNOPP3
  , testCase "sminimizedCNNOPP3b" testCNNOPP3b
  , testCase "sminimizedCNNOPP4" testCNNOPP4
  , testCase "sminimizedCNNOPP4b" testCNNOPP4b
  , testCase "sminimizedCNNOPP5" testCNNOPP5
  , testCase "sminimizedCNNOPP5b" testCNNOPP5b
  , testCase "sminimizedCNNOPP6" testCNNOPP6
  , testCase "sminimizedCNNOPP6b" testCNNOPP6b
  , testCase "sminimizedCNNOPP7" testCNNOPP7
  , testCase "sminimizedCNNOPP7b" testCNNOPP7b
  , testCase "minimizedCNNOPP4bU" testCNNOPP4bU
  ]


-- * Gathers

gatherNested1 :: forall target r. (ADReady target, GoodScalar r)
              => target (TKR 2 r) -> target (TKR 1 r)
gatherNested1 t =
  rgather @1
          (2 :$: ZSR)
          (rgather @1
                   (4 :$: 2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 :.: ZIR))
          (\(i2 :.: ZIR) -> i2 + i2 :.: i2 :.: ZIR)

testGatherNested1 :: Assertion
testGatherNested1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @1 gatherNested1 (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherNestedBuild1 :: Assertion
testGatherNestedBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [3.0,1.0,1.0,1.0,1.0,3.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rbuild1 5 (\i ->
             ifH (i >. 2) (gatherNested1 t) (t ! [i])))
          (rreplicate 7 $ ringestData [2] [0, 1]))

gather1 :: forall target r. (ADReady target, GoodScalar r)
        => target (TKR 2 r) -> target (TKR 1 r)
gather1 t =
  rgather @1
          (2 :$: ZSR)
          (rslice 0 4 t)
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
             ifH (i >. 2) (gather1 t) (t ! [i])))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherSimpPP1 :: Assertion
testGatherSimpPP1 = do
  resetVarCounter
  let !t1 = gatherNested1 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 315
  resetVarCounter
  let !t2 = gather1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 315
  length (show (simplifyInlineContract @(TKR 1 Float) t1))
    @?= length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t2))

testGatherSimp1 :: Assertion
testGatherSimp1 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0, 0.1, 0.007]
      env = extendEnv varName (ringestData [7, 2] vals) emptyEnv
  let !t1 = gatherNested1 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = gather1 (ringestData [7, 2] vals)
  let !t1n = unAstNoSimplify $ gatherNested1 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ gather1 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 1 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 1 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 1 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 1 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

gatherNested02 :: forall target r. (ADReady target, GoodScalar r)
               => target (TKR 1 r) -> target (TKR 1 r)
gatherNested02 t =
  rgather @1
          (1 :$: ZSR)
          (rgather @1
                   (2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 + k3 :.: ZIR))
          (\(i1 :.: ZIR) -> i1 + i1 + i1 :.: ZIR)

testGatherNested02 :: Assertion
testGatherNested02 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [4] [1.0,0.0,0.0,0.0])
    (rev' @Double @1 gatherNested02 (rreplicate 4 (rscalar 0.1)))

gatherNested2 :: forall target r. (ADReady target, GoodScalar r)
              => target (TKR 2 r) -> target (TKR 2 r)
gatherNested2 t =
  rgather @2
          (2 :$: 3 :$: ZSR)
          (rgather @3
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
        => target (TKR 2 r) -> target (TKR 2 r)
gather2 t =
  rgather @2
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
  let !t1 = gatherNested2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 582
  resetVarCounter
  let !t2 = gather2 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 394
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t1)) @?= 582
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 394

testGatherSimp2 :: Assertion
testGatherSimp2 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0, 0.1, 0.007]
      env = extendEnv varName (ringestData [7, 2] vals) emptyEnv
  let !t1 = gatherNested2 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = gather2 (ringestData [7, 2] vals)
  let !t1n = unAstNoSimplify $ gatherNested2 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ gather2 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 2 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

gatherNested12 :: forall target r. (ADReady target, GoodScalar r)
               => target (TKR 2 r) -> target (TKR 2 r)
gatherNested12 t =
  rgather @1
          (2 :$: 4 :$: ZSR)
          (rgather @3
                   (2 :$: 3 :$: 4 :$: ZSR) t
                   (\(k1 :.: k2 :.: k3 :.: ZIR) -> k1 + k2 + k3 :.: k1 :.: ZIR))
          (\(i1 :.: ZIR) -> i1 :.: i1 + i1 :.: ZIR)

testGatherNested12 :: Assertion
testGatherNested12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @Double @2 gatherNested12 (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherNestedBuild12 :: Assertion
testGatherNestedBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifH (i >. 2) (gatherNested12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

gather12 :: forall target r. (ADReady target, GoodScalar r)
         => target (TKR 2 r) -> target (TKR 2 r)
gather12 t =
  rgather @2
          (2 :$: 4 :$: ZSR)
          t
          (\(i1 :.: k3 :.: ZIR) -> i1 + i1 + i1 + k3 :.: i1 :.: ZIR)

testGather12 :: Assertion
testGather12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,1.0,0.0,1.0,0.0,1.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0])
    (rev' @Double @2 gather12 (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherBuild12 :: Assertion
testGatherBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifH (i >. 2) (gather12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherSimpPP12 :: Assertion
testGatherSimpPP12 = do
  resetVarCounter
  let !t1 = gatherNested12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 515
  resetVarCounter
  let !t2 = gather12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 341
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 515
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 341

testGatherSimp12 :: Assertion
testGatherSimp12 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0, 0.1, 0.007]
      env = extendEnv varName (ringestData [7, 2] vals) emptyEnv
  let !t1 = gatherNested12 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = gather12 (ringestData [7, 2] vals)
  let !t1n = unAstNoSimplify $ gatherNested12 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ gather12 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 2 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

gatherReshape22 :: forall target r. (ADReady target, GoodScalar r)
                => target (TKR 2 r) -> target (TKR 2 r)
gatherReshape22 t =
  rreshape @6 [2, 6]
  $ rreshape [3, 1, 2, 1, 1, 2]
  $ rreshape @4 (1 :$: 12 :$: 1 :$: ZSR)
  $ rreshape @3 [3, 1, 1, 4]
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
  let !t1 = gatherReshape22 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 159
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 159
  resetVarCounter
  let !t2 = rreshape @2 @2 [2, 6]
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 159
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 159

testGatherSimp22 :: Assertion
testGatherSimp22 = do
  let varName = mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0]
      env = extendEnv varName (ringestData [6, 2] vals) emptyEnv
  let !t1 = gatherReshape22 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = rreshape @2 @2 [2, 6] (ringestData [6, 2] vals)
  let !t1n = unAstNoSimplify $ gatherReshape22 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ rreshape @2 @2 [2, 6] $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 2 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

testGatherSimpPP23 :: Assertion
testGatherSimpPP23 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
              gatherReshape22 @(AstTensor AstMethodLet PrimalSpan)
                (t * rreplicate0N [6, 2] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 465
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 471
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 465
  length (show (simplifyInlineContract @(TKR 3 Float) @PrimalSpan t2)) @?= 471

testGatherSimp23 :: Assertion
testGatherSimp23 = do
  let varName = mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0]
      env = extendEnv varName (ringestData [6, 2] vals) emptyEnv
  let !t1 = (\t -> rbuild1 4 (\i ->
              gatherReshape22 @(AstTensor AstMethodLet PrimalSpan)
                (t * rreplicate0N [6, 2] (rfromIndex0 i)))) var
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (rfromIndex0 i)))) (ringestData [6, 2] vals)
  let !t1n = unAstNoSimplify $ (\t -> rbuild1 4 (\i ->
              gatherReshape22
                (t * rreplicate0N [6, 2] (rfromIndex0 i)))) $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (rfromIndex0 i)))) $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 3 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 3 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 3 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 3 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

-- Depending on if and how transpose it desugared, this may or may not result
-- in dozens of nested gathers that should vanish after simplification.
gatherTranspose33 :: forall target r. (ADReady target, NumScalar r, RealFloat r)
                  => target (TKR 10 r) -> target (TKR 2 r)
gatherTranspose33 t =
  rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
    (rtr
     $ rreshape @4 [16, 8]
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

testGatherTransposeBuild33PP :: Assertion
testGatherTransposeBuild33PP = do
  resetVarCounter
  let artifactRev =
        revArtifactAdapt
          UseIncomingCotangent
          (\t -> rbuild1 4 (\i ->
             gatherTranspose33
               (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]
                                 (rfromIndex0 i))))
          (FTKR @10 [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]
                (FTKScalar @Double))
  printArtifactPrimalSimple (simplifyArtifact artifactRev)
    @?= "\\w1 -> rfromS (sdot1In (tfromPlain (STKS [4,6,16,8] STKScalar) (sconcrete (sfromListLinear [4,6,16,8] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]))) (ttranspose (makePerm @[1,0,3,2]) (sreplicate @6 (ttranspose (makePerm @[0,2,1]) (sreshape @[4,16,8] (ttranspose (makePerm @[0,1,3,2]) (sreshape @[4,2,2,8,4] (tfromPlain (STKS [4,1,2,1,2,2,2,2,2,2,1] STKScalar) (sconcrete (sfromListLinear [4,1,2,1,2,2,2,2,2,2,1] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0])) * sreplicate @4 (ttranspose (makePerm @[3,7,0,1,2,4,6,5]) (sfromR w1))))))))))"

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
             t * rreplicate 2 (rreplicate 1 (rfromIndex0 i))))
         (ringestData [2, 1] [1,2]))

testGatherTransposeBuild335 :: Assertion
testGatherTransposeBuild335 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 1] [1,1])
    (rev' @Double @3
          (\t ->
             rreplicate 2 t * rtranspose [2,0,1] (rreplicate 2 (rreplicate 1 (rfromIntegral @Int64 (rconcrete $ Nested.rfromListPrimLinear (fromList [2]) [0, 1])))))
         (ringestData [2, 1] [1,2]))

testGatherTransposeBuild336 :: Assertion
testGatherTransposeBuild336 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 1] [1,1])
    (rev' @Double @3
          (\t ->
             rreplicate 2 t * rtranspose [2,0,1] (rreplicate 2 (rreplicate 1 (rfromList [rscalar 0, rscalar 1]))))
         (ringestData [2, 1] [1,2]))

-- These are different terms, but they should have similar lengths,
-- because they differ only by single transpose and reshape, most probably,
-- and all the rest of the element reordering should cancel out.
-- Still, probably impossible to lower the gap to zero.
testGatherSimpPP33 :: Assertion
testGatherSimpPP33 = do
  resetVarCounter
  let !t1 = gatherTranspose33 @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 1132
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 862
  printAstSimple (simplifyInlineContract @(TKR 2 Float) t1)
    @?= "rfromS (smatmul2 (tfromPlain (STKS [6,8] STKScalar) (sconcrete (sfromListLinear [6,8] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.89432,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.89432,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]))) (str (sreshape @[16,8] (ttranspose (makePerm @[0,2,1]) (sreshape @[2,2,8,4] (ttranspose (makePerm @[3,7,0,1,2,4,6,5]) (sfromR w0)))))))"
  resetVarCounter
  let !t2 = (\t -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                            (rreshape @10 [8, 16] t))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 811
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 541

testGatherSimpPP34 :: Assertion
testGatherSimpPP34 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
             gatherTranspose33 @(AstTensor AstMethodLet PrimalSpan) (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 2534
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 19868
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              (\t' -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                               (rreshape @10 [8, 16] t'))
                (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 2175
  length (show (simplifyInlineContract @(TKR 3 Float) @PrimalSpan t2)) @?= 19509

{- TODO: re-enable the tests once we drop GHC 9.10
   (they don't type-check with 9.10)
gatherCond :: forall target r. (ADReady target, GoodScalar r)
           => target (TKR 2 r) -> target (TKR 2 r)
gatherCond u =
  let v = rtranspose [2, 0, 1] $ rreplicate (2 * rwidth u) u
  in rgather [rwidth u, 2] v (\(i :.: j :.: ZIR) ->
                                ifH (i ==. 3) 0 j :.: 2 * i :.: i :.: ZIR)

testGatherCond :: Assertion
testGatherCond =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,2.0,0.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 gatherCond (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherCondBuild :: Assertion
testGatherCondBuild =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,12.0,0.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherCond (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

gatherCond2 :: forall target r. (ADReady target, GoodScalar r)
            => target (TKR 2 r) -> target (TKR 2 r)
gatherCond2 u =
  let v = rreplicate (2 * rwidth u) u
  in rtr $ rgather [2, rwidth u] v (\(j :.: i :.: ZIR) ->
                                      2 * i :.: i :.: ifH (i ==. 3) 0 j :.: ZIR)

testGatherCond2 :: Assertion
testGatherCond2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,2.0,0.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 gatherCond2 (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherCondBuild2 :: Assertion
testGatherCondBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,12.0,0.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherCond2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherSimpCond :: Assertion
testGatherSimpCond = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0, 0.1, 0.007]
      env = extendEnv varName (ringestData [7, 2] vals) emptyEnv
  let !t1 = gatherCond @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = gatherCond2 (ringestData [7, 2] vals)
  let !t1n = unAstNoSimplify $ gatherCond $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ gatherCond2 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 2 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

gatherCond3 :: forall target r. (ADReady target, GoodScalar r)
            => target (TKR 2 r) -> target (TKR 2 r)
gatherCond3 u =
  let v = rtranspose [2, 0, 1] $ rreplicate (2 * rwidth u) u
  in rgather [rwidth u, 2] v (\(i :.: j :.: ZIR) ->
                                2 * i :.: i :.: ifH (i ==. 3) 0 j :.: ZIR)

testGatherCond3 :: Assertion
testGatherCond3 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2 gatherCond3 (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherCondBuild3 :: Assertion
testGatherCondBuild3 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,0.0,6.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherCond3 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

gatherCond4 :: forall target r. (ADReady target, GoodScalar r)
            => target (TKR 2 r) -> target (TKR 2 r)
gatherCond4 u =
  let v = rreplicate (2 * rwidth u) u
  in rtr $ rgather [2, rwidth u] v (\(j :.: i :.: ZIR) ->
                                      i :.: ifH (i ==. 3) 0 j :.: 2 * i :.: ZIR)

testGatherCond4 :: Assertion
testGatherCond4 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2 gatherCond4 (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherCondBuild4 :: Assertion
testGatherCondBuild4 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,0.0,6.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherCond4 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherSimpCond3 :: Assertion
testGatherSimpCond3 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0, 0.1, 0.007]
      env = extendEnv varName (ringestData [7, 2] vals) emptyEnv
  let !t1 = gatherCond3 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = gatherCond4 (ringestData [7, 2] vals)
  let !t1n = unAstNoSimplify $ gatherCond3 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ gatherCond4 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 2 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

gatherCond5 :: forall target r. (ADReady target, GoodScalar r)
            => target (TKR 3 r) -> target (TKR 2 r)
gatherCond5 v =
  rgather [rwidth v, 2] v (\(i :.: j :.: ZIR) ->
                             ifH (i ==. 1) 0 j :.: 2 * i :.: i :.: ZIR)

testGatherCond5 :: Assertion
testGatherCond5 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2,4,2]
                 [1.0,0.0,0.0,0.0,0.0,2.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2 gatherCond5 (rreplicate 2 $ rreplicate 4 $ ringestData [2] [0, 1]))

testGatherCondBuild5 :: Assertion
testGatherCondBuild5 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2,4,2]
                 [6.0,0.0,0.0,0.0,0.0,12.0,0.0,0.0,6.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherCond5 (t * rreplicate0N [2,4,2] (rfromIndex0 i))))
          (rreplicate 2 $ rreplicate 4 $ ringestData [2] [0, 1]))

gatherCond6 :: forall target r. (ADReady target, GoodScalar r)
            => target (TKR 3 r) -> target (TKR 2 r)
gatherCond6 u =
  let v = rtranspose [2, 0, 1] u
  in rtr $ rgather [2, rwidth v] v (\(j :.: i :.: ZIR) ->
                                      i :.: ifH (i ==. 1) 0 j :.: 2 * i :.: ZIR)

testGatherCond6 :: Assertion
testGatherCond6 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2,4,2]
                 [1.0,0.0,0.0,0.0,0.0,2.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2 gatherCond6 (rreplicate 2 $ rreplicate 4 $ ringestData [2] [0, 1]))

testGatherCondBuild6 :: Assertion
testGatherCondBuild6 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2,4,2]
                 [6.0,0.0,0.0,0.0,0.0,12.0,0.0,0.0,6.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             gatherCond6 (t * rreplicate0N [2,4,2] (rfromIndex0 i))))
          (rreplicate 2 $ rreplicate 4 $ ringestData [2] [0, 1]))

testGatherSimpCond5 :: Assertion
testGatherSimpCond5 = do
  let varName = mkAstVarName (FTKR [2,4,2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1,0,2.0,2.13,0.2,11.0,-17.0,23.0,29.0,-35.0,41.0,1.4,-0.33,33.0,0.1,0.007]
      env = extendEnv varName (ringestData [2,4,2] vals) emptyEnv
  let !t1 = gatherCond5 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = gatherCond6 (ringestData [2,4,2] vals)
  let !t1n = unAstNoSimplify $ gatherCond5 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ gatherCond6 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 2 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n
-}


-- * Scatters instead of gathers

scatterNested1 :: forall target r. (ADReady target, NumScalar r)
               => target (TKR 2 r) -> target (TKR 1 r)
scatterNested1 t =
  rscatter @2
          (2 :$: ZSR)
          (rscatter @1
                   (7 :$: 2 :$: ZSR) t
                   (\(k3 :.: ZIR) -> k3 :.: ZIR))
          (\(i1 :.: i2 :.: ZIR) -> i2 `quotH` (1 + i1) :.: ZIR)

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
             ifH (i >. 2) (scatterNested1 t) (t ! [i])))
          (rreplicate 7 $ ringestData [2] [0, 1]))

scatter1 :: forall target r. (ADReady target, NumScalar r)
         => target (TKR 2 r) -> target (TKR 1 r)
scatter1 t =
  rscatter @2
          (2 :$: ZSR)
          t
          (\(i1 :.: i2 :.: ZIR) -> minH (i2 + 2 * i1) 1 :.: ZIR)

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
             ifH (i >. 2) (scatter1 t) (t ! [i])))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterSimpPP1 :: Assertion
testScatterSimpPP1 = do
  resetVarCounter
  let !t1 = scatterNested1 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 397
  resetVarCounter
  let !t2 = scatter1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 492
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t1)) @?= 397
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t2)) @?= 492

testScatterSimp1 :: Assertion
testScatterSimp1 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0, 0.1, 0.007]
      env = extendEnv varName (ringestData [7, 2] vals) emptyEnv
  let !t1 = scatterNested1 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = scatter1 (ringestData [7, 2] vals)
  let !t1n = unAstNoSimplify $ scatterNested1 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ scatter1 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  -- TODO: scatter fusion isn't sound? or just incorrectly manually done here?
  -- interpretAstPrimal @Concrete env t1n
  --   @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 1 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 1 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 1 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 1 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

scatterNested2 :: forall target r. (ADReady target, NumScalar r)
              => target (TKR 2 r) -> target (TKR 2 r)
scatterNested2 t =
  rscatter @4
          (2 :$: 3 :$: ZSR)
          (rscatter @1
                   (2 :$: 3 :$: 4 :$: 2 :$: ZSR) t
                   (\(k1 :.: ZIR) -> minH k1 1 :.: minH k1 2  :.: minH k1 3 :.: ZIR))
          (\(i1 :.: i2 :.: _i3 :.: i4 :.: ZIR) ->
            minH (i1 + i2) 1 :.: minH (i4 + i1) 2 :.: ZIR)

testScatterNested2 :: Assertion
testScatterNested2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatterNested2 (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterNestedBuild2 :: Assertion
testScatterNestedBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0])
    (rev' @Double @3
          (\t -> rbuild1 4 (\i ->
             scatterNested2 (t * rreplicate0N [7, 2] (rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

scatter2 :: forall target r. (ADReady target, NumScalar r)
        => target (TKR 2 r) -> target (TKR 2 r)
scatter2 t =
  rscatter @2
          (2 :$: 3 :$: ZSR)
          t
          (\(i1 :.: i2 :.: ZIR) -> minH (i1 + i2 + i1 + i2) 1 :.: minH i1 2 :.: ZIR)

testScatter2 :: Assertion
testScatter2 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatter2 (rreplicate 7 $ ringestData [2] [0, 1]))

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
  let !t1 = scatterNested2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 1022
  resetVarCounter
  let !t2 = scatter2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 782
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 1022
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 782

testScatterSimp2 :: Assertion
testScatterSimp2 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0, 0.1, 0.007]
      env = extendEnv varName (ringestData [7, 2] vals) emptyEnv
  let !t1 = scatterNested2 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = scatter2 (ringestData [7, 2] vals)
  let !t1n = unAstNoSimplify $ scatterNested2 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ scatter2 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  -- TODO: scatter fusion isn't sound? or just incorrectly manually done here?
  -- interpretAstPrimal @Concrete env t1n
  --  @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 2 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

scatterNested12 :: forall target r. (ADReady target, NumScalar r)
               => target (TKR 2 r) -> target (TKR 2 r)
scatterNested12 t =
  rscatter @2
          (2 :$: 4 :$: ZSR)
          (rscatter @2
                   (2 :$: 3 :$: 4 :$: ZSR) t
                   (\(k1 :.: k2 :.: ZIR) ->
                     minH k1 1 :.: minH (k2 + k1) 2 :.: minH k1 3 :.: ZIR))
          (\(i1 :.: _i2 :.: ZIR) -> minH (i1 + i1) 1 :.: ZIR)

testScatterNested12 :: Assertion
testScatterNested12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatterNested12 (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterNestedBuild12 :: Assertion
testScatterNestedBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifH (i >. 2) (scatterNested12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

scatter12 :: forall target r. (ADReady target, NumScalar r)
         => target (TKR 2 r) -> target (TKR 2 r)
scatter12 t =
  rscatter @2
          (2 :$: 4 :$: ZSR)
          t
          (\(i1 :.: k3 :.: ZIR) -> minH (i1 + i1 + i1 + k3) 1 :.: minH i1 3 :.: ZIR)

testScatter12 :: Assertion
testScatter12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @2 scatter12 (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterBuild12 :: Assertion
testScatterBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             ifH (i >. 2) (scatter12 t)
                          (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterBuild12b :: Assertion
testScatterBuild12b =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             tlet (tfromPlain STKScalar $ i >. 2) $ \b ->
               ifH (tplainPart b &&* tplainPart b)
                   (scatter12 t)
                   (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))
                        ) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterSimpPP12 :: Assertion
testScatterSimpPP12 = do
  resetVarCounter
  let !t1 = scatterNested12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 952
  resetVarCounter
  let !t2 = scatter12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 625
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 952
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 625

testScatterSimp12 :: Assertion
testScatterSimp12 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000
      var = AstVar varName
      vals = [-1, 0, 2.0,5.0,11.0,-17.0,23.0,29.0,-35.0,41.0,47.0,33.0, 0.1, 0.007]
      env = extendEnv varName (ringestData [7, 2] vals) emptyEnv
  let !t1 = scatterNested12 @(AstTensor AstMethodLet PrimalSpan) var
  let !t2 = scatter12 (ringestData [7, 2] vals)
  let !t1n = unAstNoSimplify $ scatterNested12 $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ scatter12 $ AstNoSimplify var
  interpretAstPrimal @Concrete env t1
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete env t1n
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete emptyEnv t2
    @?= interpretAstPrimal @Concrete env t2n
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1)
    @?= interpretAstPrimal @Concrete env t1
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t1n)
    @?= interpretAstPrimal @Concrete env t1n
  interpretAstPrimal @Concrete emptyEnv
                     (simplifyInlineContract @(TKR 2 Float) t2)
    @?= interpretAstPrimal @Concrete emptyEnv t2
  interpretAstPrimal @Concrete env
                     (simplifyInlineContract @(TKR 2 Float) t2n)
    @?= interpretAstPrimal @Concrete env t2n

foo :: RealFloatH a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2H z w + z * w

bar :: forall a. RealFloatH a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2H x w + y * w

barRelu
  :: ( ADReady target, NumScalar r, KnownNat n, Differentiable r )
  => target (TKR n r) -> target (TKR n r)
barRelu x = let t = rreplicate0N (rshape x) (rscalar 0.001) * x
            in relu $ bar (t, relu t)

barRelu10xSlower
  :: ( ADReady target, NumScalar r, KnownNat n, Differentiable r )
  => target (TKR n r) -> target (TKR n r)
barRelu10xSlower x = let t = rmap0N (* rscalar 0.001) x
                     in relu $ bar (t, relu t)

testBarReluADVal320 :: Assertion
testBarReluADVal320 =
  assertEqualUpToEpsilon 1e-10
    (ringestData [1,2,2,1,2,2,2,2,2,1] [2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885034988157713e-4,2.885923176600045e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.8851415976532735e-4,2.885923176600045e-4,2.887454843457817e-4,2.8849246223035154e-4,2.884182085399516e-4,2.884075468755327e-4,2.8842176240868867e-4,2.8840399312321096e-4,0.0,2.887454843457817e-4,2.886097295122454e-4,2.887454843457817e-4,2.88599069218435e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.885145151321922e-4,2.8854294397024206e-4,2.8858878438222746e-4,2.885923176600045e-4,0.0,2.884007943794131e-4,0.0,2.884469945274759e-4,2.8843242392031246e-4,2.884288700806792e-4,0.0,2.885034988157713e-4,2.884110805753153e-4,0.0,2.8849283778617973e-4,2.884075468755327e-4,2.884075468755327e-4,2.884075468755327e-4,2.884075468755327e-4,0.0,0.0,0.0,0.0,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,0.0,0.0,0.0,0.0,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.8854294397024206e-4,2.884288700806792e-4,2.884395315486472e-4,0.0,2.8849246223035154e-4,2.8850276789489724e-4,0.0,2.8849212704517413e-4,2.8854294397024206e-4,2.884288700806792e-4,2.884395315486472e-4,0.0,2.8849246223035154e-4,2.8850276789489724e-4,0.0,2.8849212704517413e-4,2.8842922547482884e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.894378297730782e-4,2.885923176600045e-4,2.887454843457817e-4,2.88599069218435e-4,2.887454843457817e-4,2.887056688523444e-4,2.887454843457817e-4,2.887056688523444e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.884786229769816e-4,2.885923176600045e-4,2.887454843457817e-4,2.886950092188272e-4,2.887454843457817e-4,2.884818011261814e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.887167039107226e-4,2.885923176600045e-4,2.887454843457817e-4,2.8860262265516213e-4,2.887454843457817e-4,2.885884088500461e-4,2.887454843457817e-4,2.88599069218435e-4])
    (grad (kfromR . rsum0 @10 @(TKScalar Double) . barRelu10xSlower)
          (rmap0N (* rscalar 0.001) t128))

testReluSimpPP :: Assertion
testReluSimpPP = do
  resetVarCounter
  let !t1 = barRelu10xSlower @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 23589
  length (show (simplifyInlineContract @(TKR 10 Float) t1)) @?= 23589
  resetVarCounter
  let !t2 = barRelu @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 12708
  length (show (simplifyInlineContract @(TKR 10 Float) t2)) @?= 12708

testCNNOPP2 :: Assertion
testCNNOPP2 = do
  resetVarCounter
  let t = maxPool2dUnpadded2
            (rconcrete $ Nested.rreplicateScal (1 :$: 1 :$: 2 :$: 2 :$: ZSR) 1)
  printAstPretty (simplifyInlineContract t)
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty t
    @?= "rfromS (sreplicate @2 (sreplicate @2 (let u37 = let u42 = sgather (sgather (sreplicate @1 (let w32 = sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sfromListLinear [2,3,2] [1.0,1.0,0.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,0.0])) (\\[i26, i15] -> [i26 + i15]))) (\\[i22, i16] -> [i22 + i16]) in stranspose @[1,2,3,0] (sappend (sconcrete (sreplicate [1,2,2,2,2] 0.0)) (sappend (sreplicate @1 (stranspose @[2,0,4,1,3] w32 !$ [1])) (sconcrete (sreplicate [1,2,2,2,2] 0.0)))))) (\\[i20] -> [i20, i20, i20, 0])) (\\[i45, i40, i36, i8] -> [2 * i40 + i8, i40, 2 * i45 + i36]) in str (sappend (sconcrete (sreplicate [1,2,2,2] 0.0)) (sreplicate @1 (str u42 !$ [1]))) in stranspose @[2,3,0,1] u37 !$ [0, 0])))"

testCNNOPP2b :: Assertion
testCNNOPP2b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded2 (FTKR [1, 1, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (sconcrete (sreplicate [1,1,2,2] 0.0))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sconcrete (sreplicate [1,1,2,2] 0.0))"

maxPool2dUnpadded2
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded2 a =
  rbuild [2, 2, 2, 2] $ \case
    [_, _, iBh, iBw] ->
      let arrt = slicez2 (conv2dSame2 a) [iBw, 1, 2 * iBh, 2 * iBw]
      in rmaximum2 arrt
    _ -> error "maxPool2dUnpadded2: impossible pattern needlessly required"

conv2dSame2
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dSame2 a =
  rbuild [3, 3, 2, 2] $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez2 a [iImg, 0, iBh, iBw]
      in rindex0 arrAt [0, iBw, iBw, 0]
    _ -> error "conv2dSame2: impossible pattern needlessly required"

slicez2
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double, n ~ 4)
  => target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez2 d ixBase =
  rbuild [1, 1, 2, 2] $ \ixResult -> indexz02 d (ixrZipWith (+) ixBase ixResult)

indexz02
  :: forall target r n.
     (target ~ AstTensor AstMethodLet FullSpan, r ~ Double, n ~ 4)
  => target (TKR n r) -> IxROf target n -> target (TKR 0 r)
indexz02 d ix = ifH (1 ==. (toList ix !! 0)) (d ! ix) (rscalar 0)

rmaximum2 :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
         => target (TKR 4 r) -> target (TKR 0 r)
rmaximum2 t0 = tlet t0 $ \t -> rindex0 t [0, 0, 0, 0]

{- TODO: divergent result; bring back when GHC 9.10 dropped:
testCNNOPP3 :: Assertion
testCNNOPP3 = do
  resetVarCounter
  let blackGlyph :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      blackGlyph = AstFromPrimal $ AstReplicate (SNat @3) knownSTK
                   $ AstReplicate (SNat @3) knownSTK
                   $ AstReplicate (SNat @3) knownSTK
                   $ AstReplicate (SNat @3) knownSTK
                       (rconcrete $ Nested.rscalar 7
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      afcnn2T = maxPool2dUnpadded3 $ conv2dSame3 blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [14.0,0.0,14.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (stranspose @[1,2,0] (sreplicate @2 (let w32 = stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (let t44 = sreplicate @2 (sgather (sappend (stranspose @[4,1,2,3,5,0] (sappend (sreplicate @1 (stranspose @[0,1,2,4,3] (sgather (str (sreplicate @1 (sconcrete (sfromListLinear [2] [7.0,0.0])))) (\\[i31, i25, i20, i17] -> [ifH (notB (notB (0 <=. negate i31 + negate i20) &&* notB (1 <=. i31 + i20 &&* (-1) <=. negate i31 + negate i20)) &&* notB (notB (0 <=. negate i25 + negate i17) &&* notB (1 <=. i25 + i17 &&* (-1) <=. negate i25 + negate i17))) 0 1])))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sscalar 0.0))))))))) (stranspose @[4,1,2,3,5,0] (sappend (sreplicate @1 (stranspose @[0,1,2,4,3] (sgather (str (sreplicate @1 (sconcrete (sfromListLinear [2] [7.0,0.0])))) (\\[i30, i24, i19, i17] -> [ifH (notB (notB (0 <=. negate i30 + negate i19) &&* notB (1 <=. i30 + i19 &&* (-1) <=. negate i30 + negate i19)) &&* notB (notB (0 <=. negate i24 + negate i17) &&* notB (1 <=. i24 + i17 &&* (-1) <=. negate i24 + negate i17))) 0 1])))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sscalar 0.0)))))))))) (\\[i39, i4] -> [2 * i4, 0, 2 * i4, 0, 0, 2 * i39]) + sgather (sappend (sreplicate @1 (sgather (stranspose @[1,2,3,4,5,0] (sappend (sreplicate @1 (stranspose @[0,2,4,3,1] (sgather (str (sreplicate @1 (sconcrete (sfromListLinear [2] [7.0,0.0])))) (\\[i28, i22, i19, i17] -> [ifH (notB (notB (0 <=. negate i28 + negate i19) &&* notB (1 <=. i28 + i19 &&* (-1) <=. negate i28 + negate i19)) &&* notB (notB (0 <=. negate i22 + negate i17) &&* notB (1 <=. i22 + i17 &&* (-1) <=. negate i22 + negate i17))) 0 1])))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))))) (\\[i27] -> [i27, i27, 0, 1, 0]))) (str (sreplicate @2 (str (sreplicate @2 (sconcrete (sfromListLinear [1] [0.0]))))))) (\\[i38, i4] -> [2 * i4, 0, 2 * i38])) in sappend (str (sappend (stranspose @[1,2,0] (sappend (sgather t44 (\\[i34, i37, i42] -> [i42, i37, i34])) (sreplicate @1 (sreplicate @1 (sreplicate @1 (sscalar 0.0)))))) (sreplicate @1 (sreplicate @1 (sreplicate @2 (sscalar 0.0)))))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))))))))) in stranspose @[3,4,5,6,0,1,2] w32 !$ [0, 0, 0, 0])))"
-}

testCNNOPP3b :: Assertion
testCNNOPP3b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dSame3) (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (let t123 = sgather (stranspose @[1,2,3,0] (sslice (SNat @1) (SNat @2) (str (sslice (SNat @0) (SNat @2) (stranspose @[0,3,2,1] (sfromR u1)))))) (\\[i121, i122] -> [i121, i122 + i121, i122]) in stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (stranspose @[2,0,1] (sgather (sreplicate @2 (str (sappend (sreplicate @1 (sgather (stranspose @[3,2,1,0] (sfromVector (fromList [stranspose @[0,2,1] t123, sconcrete (sreplicate [2,2,2] 0.0)])) !$ [0]) (\\[i124, i125] -> [i125, i124, let x126 = 1 + i125 ; x127 = 1 + i125 ; x128 = 1 + i125 ; x129 = 1 + i125 in ifH (0 <=. negate i124) (ifH (notB (notB (0 <=. negate i124) &&* notB (1 <=. i124)) &&* notB (notB (0 <=. tplainPart x126 &&* 0 <=. tplainPart (negate x126)) &&* notB (1 <=. tplainPart x127 &&* (-1) <=. tplainPart (negate x127)))) 0 1) (ifH (1 <=. i124) (ifH (notB (notB (0 <=. negate i124) &&* notB (1 <=. i124)) &&* notB (notB (0 <=. tplainPart x128 &&* 0 <=. tplainPart (negate x128)) &&* notB (1 <=. tplainPart x129 &&* (-1) <=. tplainPart (negate x129)))) 0 1) 1)]))) (sreplicate @1 (sgather (stranspose @[3,2,1,0] (sfromVector (fromList [stranspose @[0,2,1] t123, sconcrete (sreplicate [2,2,2] 0.0)])) !$ [1]) (\\[i130, i131] -> [i131, i130, let x132 = 1 + i130 ; x133 = 1 + i130 ; x134 = 1 + i131 ; x135 = 1 + i131 ; x136 = 1 + i130 ; x137 = 1 + i130 ; x138 = 1 + i131 ; x139 = 1 + i131 in ifH (0 <=. negate i130) (ifH (notB (notB (0 <=. tplainPart x132 &&* 0 <=. tplainPart (negate x132)) &&* notB (1 <=. tplainPart x133 &&* (-1) <=. tplainPart (negate x133))) &&* notB (notB (0 <=. tplainPart x134 &&* 0 <=. tplainPart (negate x134)) &&* notB (1 <=. tplainPart x135 &&* (-1) <=. tplainPart (negate x135)))) 0 1) (ifH (1 <=. i130) (ifH (notB (notB (0 <=. tplainPart x136 &&* 0 <=. tplainPart (negate x136)) &&* notB (1 <=. tplainPart x137 &&* (-1) <=. tplainPart (negate x137))) &&* notB (notB (0 <=. tplainPart x138 &&* 0 <=. tplainPart (negate x138)) &&* notB (1 <=. tplainPart x139 &&* (-1) <=. tplainPart (negate x139)))) 0 1) 1)])))) !$ [0] + sgather (sreplicate @1 (sgather (stranspose @[1,3,4,5,2,0] (sfromVector (fromList [stranspose @[1,2,3,4,5,0] (sslice (SNat @1) (SNat @2) (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[1,2,3,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,3,0,1] (sgather (sfromR u1) (\\[i140, i141] -> [i140 + i141]))))) (\\[i142, i143] -> [i142 + i143])))), sconcrete (sreplicate [2,2,2,2,2,2] 0.0)])) !$ [0, 0, 1, 1]) (\\[i144, i145] -> [i144, let x146 = 1 + i144 ; x147 = 1 + i144 ; x148 = 1 + i145 ; x149 = 1 + i145 in ifH (notB (notB (0 <=. tplainPart x146 &&* 0 <=. tplainPart (negate x146)) &&* notB (1 <=. tplainPart x147 &&* (-1) <=. tplainPart (negate x147))) &&* notB (notB (0 <=. tplainPart x148 &&* 0 <=. tplainPart (negate x148)) &&* notB (1 <=. tplainPart x149 &&* (-1) <=. tplainPart (negate x149)))) 0 1, i145]))) (\\[i150] -> [i150, i150]))) (\\[i302] -> [2 * i302]))) (\\[i305] -> [2 * i305]))) (\\[i153] -> [2 * i153])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i154, i155, i156] -> [let x157 = 2 * i154 ; x158 = 2 * i154 ; x159 = 2 * i155 ; x160 = 2 * i155 ; x161 = 2 * i156 ; x162 = 2 * i156 in ifH (notB (notB (0 <=. tplainPart x157 &&* 0 <=. tplainPart (negate x157)) &&* notB (0 <=. tplainPart x158 &&* 0 <=. tplainPart (negate x158))) &&* (notB (notB (0 <=. tplainPart x159 &&* 0 <=. tplainPart (negate x159)) &&* notB (0 <=. tplainPart x160 &&* 0 <=. tplainPart (negate x160))) &&* notB (notB (0 <=. tplainPart x161 &&* 0 <=. tplainPart (negate x161)) &&* notB (0 <=. tplainPart x162 &&* 0 <=. tplainPart (negate x162))))) 0 1, i154, i155, i156]))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let t123 = sgather (stranspose @[1,2,3,0] (sslice (SNat @1) (SNat @2) (str (sslice (SNat @0) (SNat @2) (stranspose @[0,3,2,1] (sfromR u1)))))) (\\[i121, i122] -> [i121, i122 + i121, i122]) in rfromS (stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (stranspose @[2,0,1] (sgather (sreplicate @2 (str (sappend (sreplicate @1 (sgather (stranspose @[3,2,1,0] (sfromVector (fromList [stranspose @[0,2,1] t123, sconcrete (sreplicate [2,2,2] 0.0)])) !$ [0]) (\\[i124, i125] -> [i125, i124, let x126 = 1 + i125 ; x127 = 1 + i125 ; x128 = 1 + i125 ; x129 = 1 + i125 in ifH (0 <=. negate i124) (ifH (notB (notB (0 <=. negate i124) &&* notB (1 <=. i124)) &&* notB (notB (0 <=. tplainPart x126 &&* 0 <=. tplainPart (negate x126)) &&* notB (1 <=. tplainPart x127 &&* (-1) <=. tplainPart (negate x127)))) 0 1) (ifH (1 <=. i124) (ifH (notB (notB (0 <=. negate i124) &&* notB (1 <=. i124)) &&* notB (notB (0 <=. tplainPart x128 &&* 0 <=. tplainPart (negate x128)) &&* notB (1 <=. tplainPart x129 &&* (-1) <=. tplainPart (negate x129)))) 0 1) 1)]))) (sreplicate @1 (sgather (stranspose @[3,2,1,0] (sfromVector (fromList [stranspose @[0,2,1] t123, sconcrete (sreplicate [2,2,2] 0.0)])) !$ [1]) (\\[i130, i131] -> [i131, i130, let x132 = 1 + i130 ; x133 = 1 + i130 ; x134 = 1 + i131 ; x135 = 1 + i131 ; x136 = 1 + i130 ; x137 = 1 + i130 ; x138 = 1 + i131 ; x139 = 1 + i131 in ifH (0 <=. negate i130) (ifH (notB (notB (0 <=. tplainPart x132 &&* 0 <=. tplainPart (negate x132)) &&* notB (1 <=. tplainPart x133 &&* (-1) <=. tplainPart (negate x133))) &&* notB (notB (0 <=. tplainPart x134 &&* 0 <=. tplainPart (negate x134)) &&* notB (1 <=. tplainPart x135 &&* (-1) <=. tplainPart (negate x135)))) 0 1) (ifH (1 <=. i130) (ifH (notB (notB (0 <=. tplainPart x136 &&* 0 <=. tplainPart (negate x136)) &&* notB (1 <=. tplainPart x137 &&* (-1) <=. tplainPart (negate x137))) &&* notB (notB (0 <=. tplainPart x138 &&* 0 <=. tplainPart (negate x138)) &&* notB (1 <=. tplainPart x139 &&* (-1) <=. tplainPart (negate x139)))) 0 1) 1)])))) !$ [0] + sgather (sreplicate @1 (sgather (stranspose @[4,5,1,3,2,0] (sfromVector (fromList [stranspose @[1,2,3,4,5,0] (sslice (SNat @1) (SNat @2) (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[1,2,3,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,3,0,1] (sgather (sfromR u1) (\\[i140, i141] -> [i140 + i141]))))) (\\[i142, i143] -> [i142 + i143])))), sconcrete (sreplicate [2,2,2,2,2,2] 0.0)])) !$ [1, 1, 0, 0]) (\\[i144, i145] -> [i144, let x146 = 1 + i144 ; x147 = 1 + i144 ; x148 = 1 + i145 ; x149 = 1 + i145 in ifH (notB (notB (0 <=. tplainPart x146 &&* 0 <=. tplainPart (negate x146)) &&* notB (1 <=. tplainPart x147 &&* (-1) <=. tplainPart (negate x147))) &&* notB (notB (0 <=. tplainPart x148 &&* 0 <=. tplainPart (negate x148)) &&* notB (1 <=. tplainPart x149 &&* (-1) <=. tplainPart (negate x149)))) 0 1, i145]))) (\\[i150] -> [i150, i150]))) (\\[i151] -> [2 * i151]))) (\\[i152] -> [2 * i152]))) (\\[i153] -> [2 * i153])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i154, i155, i156] -> [let x157 = 2 * i154 ; x158 = 2 * i154 ; x159 = 2 * i155 ; x160 = 2 * i155 ; x161 = 2 * i156 ; x162 = 2 * i156 in ifH (notB (notB (0 <=. tplainPart x157 &&* 0 <=. tplainPart (negate x157)) &&* notB (0 <=. tplainPart x158 &&* 0 <=. tplainPart (negate x158))) &&* (notB (notB (0 <=. tplainPart x159 &&* 0 <=. tplainPart (negate x159)) &&* notB (0 <=. tplainPart x160 &&* 0 <=. tplainPart (negate x160))) &&* notB (notB (0 <=. tplainPart x161 &&* 0 <=. tplainPart (negate x161)) &&* notB (0 <=. tplainPart x162 &&* 0 <=. tplainPart (negate x162))))) 0 1, i154, i155, i156]))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let u173 = sscatter (ssum @2 (stranspose @[2,0,1] (sfromR dret))) (\\[i164, i165, i166] -> [let x167 = 2 * i164 ; x168 = 2 * i164 ; x169 = 2 * i165 ; x170 = 2 * i165 ; x171 = 2 * i166 ; x172 = 2 * i166 in ifH (notB (notB (0 <=. tplainPart x167 &&* 0 <=. tplainPart (negate x167)) &&* notB (0 <=. tplainPart x168 &&* 0 <=. tplainPart (negate x168))) &&* (notB (notB (0 <=. tplainPart x169 &&* 0 <=. tplainPart (negate x169)) &&* notB (0 <=. tplainPart x170 &&* 0 <=. tplainPart (negate x170))) &&* notB (notB (0 <=. tplainPart x171 &&* 0 <=. tplainPart (negate x171)) &&* notB (0 <=. tplainPart x172 &&* 0 <=. tplainPart (negate x172))))) 0 1, i164, i165, i166]) ; m177 = ssum @2 (sscatter (stranspose @[1,2,0] (sscatter (stranspose @[2,1,0] (sscatter (stranspose @[2,0,1] (u173 !$ [0])) (\\[i174] -> [2 * i174]))) (\\[i175] -> [2 * i175]))) (\\[i176] -> [2 * i176])) ; w185 = stranspose @[5,2,4,3,0,1] (soneHot (sscatter (ssum @1 (sscatter m177 (\\[i178] -> [i178, i178]))) (\\[i179, i180] -> [i179, let x181 = 1 + i179 ; x182 = 1 + i179 ; x183 = 1 + i180 ; x184 = 1 + i180 in ifH (notB (notB (0 <=. tplainPart x181 &&* 0 <=. tplainPart (negate x181)) &&* notB (1 <=. tplainPart x182 &&* (-1) <=. tplainPart (negate x182))) &&* notB (notB (0 <=. tplainPart x183 &&* 0 <=. tplainPart (negate x183)) &&* notB (1 <=. tplainPart x184 &&* (-1) <=. tplainPart (negate x184)))) 0 1, i180])) [1, 1, 0, 0]) ; t190 = str (soneHot m177 [0]) ; u201 = stranspose @[3,2,1,0] (soneHot (sscatter (ssum @1 (sslice (SNat @1) (SNat @1) t190)) (\\[i191, i192] -> [i192, i191, let x193 = 1 + i191 ; x194 = 1 + i191 ; x195 = 1 + i192 ; x196 = 1 + i192 ; x197 = 1 + i191 ; x198 = 1 + i191 ; x199 = 1 + i192 ; x200 = 1 + i192 in ifH (0 <=. negate i191) (ifH (notB (notB (0 <=. tplainPart x193 &&* 0 <=. tplainPart (negate x193)) &&* notB (1 <=. tplainPart x194 &&* (-1) <=. tplainPart (negate x194))) &&* notB (notB (0 <=. tplainPart x195 &&* 0 <=. tplainPart (negate x195)) &&* notB (1 <=. tplainPart x196 &&* (-1) <=. tplainPart (negate x196)))) 0 1) (ifH (1 <=. i191) (ifH (notB (notB (0 <=. tplainPart x197 &&* 0 <=. tplainPart (negate x197)) &&* notB (1 <=. tplainPart x198 &&* (-1) <=. tplainPart (negate x198))) &&* notB (notB (0 <=. tplainPart x199 &&* 0 <=. tplainPart (negate x199)) &&* notB (1 <=. tplainPart x200 &&* (-1) <=. tplainPart (negate x200)))) 0 1) 1)])) [1]) ; u208 = stranspose @[3,2,1,0] (soneHot (sscatter (ssum @1 (sslice (SNat @0) (SNat @1) t190)) (\\[i202, i203] -> [i203, i202, let x204 = 1 + i203 ; x205 = 1 + i203 ; x206 = 1 + i203 ; x207 = 1 + i203 in ifH (0 <=. negate i202) (ifH (notB (notB (0 <=. negate i202) &&* notB (1 <=. i202)) &&* notB (notB (0 <=. tplainPart x204 &&* 0 <=. tplainPart (negate x204)) &&* notB (1 <=. tplainPart x205 &&* (-1) <=. tplainPart (negate x205)))) 0 1) (ifH (1 <=. i202) (ifH (notB (notB (0 <=. negate i202) &&* notB (1 <=. i202)) &&* notB (notB (0 <=. tplainPart x206 &&* 0 <=. tplainPart (negate x206)) &&* notB (1 <=. tplainPart x207 &&* (-1) <=. tplainPart (negate x207)))) 0 1) 1)])) [0]) in rfromS (stranspose @[0,3,2,1] (sappend (sconcrete (sfromListLinear [0,3,3,3] [])) (sappend (str (sappend (sconcrete (sreplicate [1,2,3,3] 0.0)) (sappend (stranspose @[3,0,1,2] (sscatter (stranspose @[0,2,1] (u208 !$ [0]) + stranspose @[0,2,1] (u201 !$ [0])) (\\[i209, i210] -> [i209, i210 + i209, i210]))) (sconcrete (sfromListLinear [0,2,3,3] []))))) (sconcrete (sreplicate [1,3,3,3] 0.0)))) + sscatter (stranspose @[2,3,0,1] (sappend (sconcrete (sfromListLinear [0,3,2,2,3] [])) (sappend (stranspose @[3,0,1,2] (sscatter (stranspose @[2,5,1,3,4,0] (sappend (sconcrete (sreplicate [1,2,2,2,2,2] 0.0)) (sappend (stranspose @[5,0,1,2,3,4] (w185 !$ [0])) (sconcrete (sfromListLinear [0,2,2,2,2,2] []))))) (\\[i186, i187] -> [i186 + i187]))) (sconcrete (sreplicate [1,3,2,2,3] 0.0))))) (\\[i188, i189] -> [i188 + i189]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (let m177 = ssum @2 (sscatter (stranspose @[1,2,0] (sscatter (stranspose @[2,1,0] (sscatter (sscatter (ssum @2 (stranspose @[2,0,1] (sfromR dret))) (\\[i164, i165, i166] -> [let x167 = 2 * i164 ; x168 = 2 * i164 ; x169 = 2 * i165 ; x170 = 2 * i165 ; x171 = 2 * i166 ; x172 = 2 * i166 in ifH (notB (notB (0 <=. tplainPart x167 &&* 0 <=. tplainPart (negate x167)) &&* notB (0 <=. tplainPart x168 &&* 0 <=. tplainPart (negate x168))) &&* (notB (notB (0 <=. tplainPart x169 &&* 0 <=. tplainPart (negate x169)) &&* notB (0 <=. tplainPart x170 &&* 0 <=. tplainPart (negate x170))) &&* notB (notB (0 <=. tplainPart x171 &&* 0 <=. tplainPart (negate x171)) &&* notB (0 <=. tplainPart x172 &&* 0 <=. tplainPart (negate x172))))) 0 1, i166, i164, i165]) !$ [0]) (\\[i174] -> [2 * i174]))) (\\[i175] -> [2 * i175]))) (\\[i176] -> [2 * i176])) ; t190 = soneHot m177 [0] in sappend (stranspose @[1,3,2,0] (sappend (sconcrete (sreplicate [1,2,3,3] 0.0)) (stranspose @[3,0,1,2] (sscatter (stranspose @[3,2,0,1] (soneHot (sscatter (str t190 !$ [0]) (\\[i202, i203] -> [i203, i202, let x204 = 1 + i203 ; x205 = 1 + i203 ; x206 = 1 + i203 ; x207 = 1 + i203 in ifH (0 <=. negate i202) (ifH (notB (notB (0 <=. negate i202) &&* notB (1 <=. i202)) &&* notB (notB (0 <=. tplainPart x204 &&* 0 <=. tplainPart (negate x204)) &&* notB (1 <=. tplainPart x205 &&* (-1) <=. tplainPart (negate x205)))) 0 1) (ifH (1 <=. i202) (ifH (notB (notB (0 <=. negate i202) &&* notB (1 <=. i202)) &&* notB (notB (0 <=. tplainPart x206 &&* 0 <=. tplainPart (negate x206)) &&* notB (1 <=. tplainPart x207 &&* (-1) <=. tplainPart (negate x207)))) 0 1) 1)])) [0]) !$ [0] + stranspose @[3,2,0,1] (soneHot (sscatter (str t190 !$ [1]) (\\[i191, i192] -> [i192, i191, let x193 = 1 + i191 ; x194 = 1 + i191 ; x195 = 1 + i192 ; x196 = 1 + i192 ; x197 = 1 + i191 ; x198 = 1 + i191 ; x199 = 1 + i192 ; x200 = 1 + i192 in ifH (0 <=. negate i191) (ifH (notB (notB (0 <=. tplainPart x193 &&* 0 <=. tplainPart (negate x193)) &&* notB (1 <=. tplainPart x194 &&* (-1) <=. tplainPart (negate x194))) &&* notB (notB (0 <=. tplainPart x195 &&* 0 <=. tplainPart (negate x195)) &&* notB (1 <=. tplainPart x196 &&* (-1) <=. tplainPart (negate x196)))) 0 1) (ifH (1 <=. i191) (ifH (notB (notB (0 <=. tplainPart x197 &&* 0 <=. tplainPart (negate x197)) &&* notB (1 <=. tplainPart x198 &&* (-1) <=. tplainPart (negate x198))) &&* notB (notB (0 <=. tplainPart x199 &&* 0 <=. tplainPart (negate x199)) &&* notB (1 <=. tplainPart x200 &&* (-1) <=. tplainPart (negate x200)))) 0 1) 1)])) [1]) !$ [0]) (\\[i209, i210] -> [i209, i210 + i209, i210]))))) (sconcrete (sreplicate [1,3,3,3] 0.0)) + sscatter (stranspose @[2,3,0,1] (sappend (stranspose @[3,0,1,2] (sscatter (stranspose @[2,5,1,3,4,0] (sappend (sconcrete (sreplicate [1,2,2,2,2,2] 0.0)) (stranspose @[5,6,2,4,3,0,1] (soneHot (sscatter (sscatter m177 (\\[i178] -> [i178, i178]) !$ [0]) (\\[i179, i180] -> [i179, let x181 = 1 + i179 ; x182 = 1 + i179 ; x183 = 1 + i180 ; x184 = 1 + i180 in ifH (notB (notB (0 <=. tplainPart x181 &&* 0 <=. tplainPart (negate x181)) &&* notB (1 <=. tplainPart x182 &&* (-1) <=. tplainPart (negate x182))) &&* notB (notB (0 <=. tplainPart x183 &&* 0 <=. tplainPart (negate x183)) &&* notB (1 <=. tplainPart x184 &&* (-1) <=. tplainPart (negate x184)))) 0 1, i180])) [1, 1, 0, 0]) !$ [0]))) (\\[i186, i187] -> [i186 + i187]))) (sconcrete (sreplicate [1,3,2,2,3] 0.0)))) (\\[i188, i189] -> [i188 + i189]))"

maxPool2dUnpadded3
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded3 arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez3 [2, 2, 2, 2] arr [iBh `quotH` 2, aa, bb, iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded3: impossible pattern needlessly required"

conv2dSame3
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dSame3 arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez4 shB arrA [iImg, 0, iBw, 1]
      in rindex0 arrAt [0, iBw, iImg, iBh] + rindex0 arrAt [iImg, 1, iBw + 1, iBh]
    _ -> error "conv2dSame3: impossible pattern needlessly required"

slicez3
  :: (ADReady target, NumScalar r, KnownNat n)
  => IShR n -> target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez3 shOut d ixBase =
  rbuild shOut $ \_ -> indexz03 d (ixrZipWith (+) ixBase ixBase)

indexz03
  :: forall target r n. (ADReady target, NumScalar r, KnownNat n)
  => target (TKR n r) -> IxROf target n -> target (TKR 0 r)
indexz03 d ix = ifH (within3 @target (rshape @target d) ix) (d ! ix) (rscalar 0)

within3
  :: forall target n. (ADReady target, KnownNat n)
  => IShR n -> IxROf target n -> BoolOf target
within3 sh ix =
  let within :: IntOf target -> IntOf target -> BoolOf target
      within i dim = 0 ==. i ||* dim - 2 ==. i
  in foldr (&&*) true
     $ zipWith within (toList ix) (map fromIntegral $ toList sh)

rmaximum3 :: (BaseTensor target, LetTensor target, KnownNat n, GoodScalar r)
         => target (TKR n r) -> target (TKR 0 r)
rmaximum3 t0 = tlet t0 $ \t -> rindex0 t [0, 0, 0, 0]

testCNNOPP4 :: Assertion
testCNNOPP4 = do
  resetVarCounter
  let blackGlyph :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      blackGlyph = AstFromPrimal $ AstReplicate (SNat @3) knownSTK
                   $ AstReplicate (SNat @3) knownSTK
                   $ AstReplicate (SNat @3) knownSTK
                   $ AstReplicate (SNat @3) knownSTK
                       (rconcrete $ Nested.rscalar 7
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      afcnn2T = maxPool2dUnpadded4 blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sgather (stranspose @[5,6,7,8,0,1,2,3,4] (sfromVector (fromList [stranspose @[2,3,4,0,5,6,7,1] (sgather (stranspose @[6,0,3,1,4,5,2] (sgather (stranspose @[4,1,3,0,2] (sgather (stranspose @[3,0,4,1,2] (sgather (sconcrete (sreplicate [2,3,3,3] 7.0)) (\\[i59, i62] -> [i59 + i62]))) (\\[i65, i67] -> [2 + (negate i67 + i65), i67]))) (\\[i69, i71, i74] -> [i69 * i71 + i74]))) (\\[i30, i8] -> [2 * i30 + i8])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0]) (\\[i42, i36, i32, i29] -> [ifH (notB (notB (let i9 = 1 + i36 in 0 <=. i9 &&* 0 <=. negate i9) &&* notB (let i10 = 1 + i36 in 1 <=. i10 &&* (-1) <=. negate i10)) &&* (notB (notB (let i11 = 2 + negate i36 in 0 <=. i11 &&* 0 <=. negate i11) &&* notB (let i12 = 2 + negate i36 in 1 <=. i12 &&* (-1) <=. negate i12)) &&* (notB (notB (let i13 = i42 * i32 in 0 <=. i13 &&* 0 <=. negate i13) &&* notB (let i14 = i42 * i32 in 1 <=. i14 &&* (-1) <=. negate i14)) &&* notB (notB (let i15 = 2 * i29 in 0 <=. i15 &&* 0 <=. negate i15) &&* notB (let i16 = 2 * i29 in 1 <=. i16 &&* (-1) <=. negate i16))))) 0 1, i42, i36, i32, i29]))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (let w27 = sgather (sfromVector (fromList [stranspose @[2,3,4,0,5,6,7,1] (sgather (stranspose @[6,0,3,1,4,5,2] (sgather (stranspose @[3,0,2,1] (sgather (stranspose @[0,2,1] (sgather (sconcrete (sreplicate [2,3,3,3] 7.0)) (\\[i40, i5] -> [i40 + i5]))) (\\[i39, i6] -> [i39, 2 + (negate i39 + i6)]))) (\\[i44, i34, i7] -> [i44 * i34 + i7]))) (\\[i30, i8] -> [2 * i30 + i8])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) (\\[i42, i36, i32, i29, i23, i20, i18, i17] -> [ifH (notB (notB (let i9 = 1 + (i36 + i23) in 0 <=. i9 &&* 0 <=. negate i9) &&* notB (let i10 = 1 + (i36 + i23) in 1 <=. i10 &&* (-1) <=. negate i10)) &&* (notB (notB (let i11 = 2 + (negate i36 + i20) in 0 <=. i11 &&* 0 <=. negate i11) &&* notB (let i12 = 2 + (negate i36 + i20) in 1 <=. i12 &&* (-1) <=. negate i12)) &&* (notB (notB (let i13 = i42 * i32 + i18 in 0 <=. i13 &&* 0 <=. negate i13) &&* notB (let i14 = i42 * i32 + i18 in 1 <=. i14 &&* (-1) <=. negate i14)) &&* notB (notB (let i15 = 2 * i29 + i17 in 0 <=. i15 &&* 0 <=. negate i15) &&* notB (let i16 = 2 * i29 + i17 in 1 <=. i16 &&* (-1) <=. negate i16))))) 0 1, i42, i36, i32, i29, i23, i20, i18, i17]) in stranspose @[4,5,6,7,0,1,2,3] w27 !$ [0, 0, 0, 0])"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP4b :: Assertion
testCNNOPP4b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded4 (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sgather (stranspose @[5,6,7,8,0,1,2,3,4] (sfromVector (fromList [stranspose @[2,3,4,0,5,6,7,1] (sgather (stranspose @[4,7,0,3,1,5,6,2] (sgather (stranspose @[3,4,7,1,5,6,0,2] (sgather (stranspose @[6,0,7,4,3,2,1,5] (sgather (sslice (SNat @1) (SNat @2) (stranspose @[0,2,1] (sfromR u1))) (\\[i216, i218, i219, i220, i221] -> [i216 + i218]))) (\\[i227, i230] -> [2 + (negate i230 + i227), i230]))) (\\[i233, i235, i238] -> [i233, i235, i233 * i235 + i238]))) (\\[i124, i125] -> [i124, 2 * i124 + i125])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0]) (\\[i126, i127, i128, i129] -> [let x130 = 1 + i127 ; x131 = 1 + i127 ; x132 = 2 + negate i127 ; x133 = 2 + negate i127 ; x134 = i126 * i128 ; x135 = i126 * i128 ; x136 = 2 * i129 ; x137 = 2 * i129 in ifH (notB (notB (0 <=. tplainPart x130 &&* 0 <=. tplainPart (negate x130)) &&* notB (1 <=. tplainPart x131 &&* (-1) <=. tplainPart (negate x131))) &&* (notB (notB (0 <=. tplainPart x132 &&* 0 <=. tplainPart (negate x132)) &&* notB (1 <=. tplainPart x133 &&* (-1) <=. tplainPart (negate x133))) &&* (notB (notB (0 <=. tplainPart x134 &&* 0 <=. tplainPart (negate x134)) &&* notB (1 <=. tplainPart x135 &&* (-1) <=. tplainPart (negate x135))) &&* notB (notB (0 <=. tplainPart x136 &&* 0 <=. tplainPart (negate x136)) &&* notB (1 <=. tplainPart x137 &&* (-1) <=. tplainPart (negate x137)))))) 0 1, i126, i127, i128, i129]))"
      -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sgather (stranspose @[5,6,7,8,0,1,2,3,4] (sfromVector (fromList [stranspose @[2,3,4,0,5,6,7,1] (sgather (stranspose @[4,7,0,3,1,5,6,2] (sgather (stranspose @[3,4,7,1,5,6,0,2] (sgather (stranspose @[6,0,7,4,3,2,1,5] (sgather (sslice (SNat @1) (SNat @2) (stranspose @[0,2,1] (sfromR u1))) (\\[i114, i115, i116, i117, i118] -> [i114 + i115]))) (\\[i119, i120] -> [2 + (negate i120 + i119), i120]))) (\\[i121, i122, i123] -> [i121, i122, i121 * i122 + i123]))) (\\[i124, i125] -> [i124, 2 * i124 + i125])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0]) (\\[i126, i127, i128, i129] -> [let x130 = 1 + i127 ; x131 = 1 + i127 ; x132 = 2 + negate i127 ; x133 = 2 + negate i127 ; x134 = i126 * i128 ; x135 = i126 * i128 ; x136 = 2 * i129 ; x137 = 2 * i129 in ifH (notB (notB (0 <=. tplainPart x130 &&* 0 <=. tplainPart (negate x130)) &&* notB (1 <=. tplainPart x131 &&* (-1) <=. tplainPart (negate x131))) &&* (notB (notB (0 <=. tplainPart x132 &&* 0 <=. tplainPart (negate x132)) &&* notB (1 <=. tplainPart x133 &&* (-1) <=. tplainPart (negate x133))) &&* (notB (notB (0 <=. tplainPart x134 &&* 0 <=. tplainPart (negate x134)) &&* notB (1 <=. tplainPart x135 &&* (-1) <=. tplainPart (negate x135))) &&* notB (notB (0 <=. tplainPart x136 &&* 0 <=. tplainPart (negate x136)) &&* notB (1 <=. tplainPart x137 &&* (-1) <=. tplainPart (negate x137)))))) 0 1, i126, i127, i128, i129]))"
      -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w151 = stranspose @[4,5,6,7,8,0,1,2,3] (soneHot (sscatter (sfromR dret) (\\[i139, i140, i141, i142] -> [let x143 = 1 + i140 ; x144 = 1 + i140 ; x145 = 2 + negate i140 ; x146 = 2 + negate i140 ; x147 = i139 * i141 ; x148 = i139 * i141 ; x149 = 2 * i142 ; x150 = 2 * i142 in ifH (notB (notB (0 <=. tplainPart x143 &&* 0 <=. tplainPart (negate x143)) &&* notB (1 <=. tplainPart x144 &&* (-1) <=. tplainPart (negate x144))) &&* (notB (notB (0 <=. tplainPart x145 &&* 0 <=. tplainPart (negate x145)) &&* notB (1 <=. tplainPart x146 &&* (-1) <=. tplainPart (negate x146))) &&* (notB (notB (0 <=. tplainPart x147 &&* 0 <=. tplainPart (negate x147)) &&* notB (1 <=. tplainPart x148 &&* (-1) <=. tplainPart (negate x148))) &&* notB (notB (0 <=. tplainPart x149 &&* 0 <=. tplainPart (negate x149)) &&* notB (1 <=. tplainPart x150 &&* (-1) <=. tplainPart (negate x150)))))) 0 1, i139, i140, i141, i142])) [0, 0, 0, 0]) in rfromS (stranspose @[0,2,1] (sappend (sconcrete (sreplicate [1,3,3,3] 0.0)) (sappend (sscatter (stranspose @[1,6,5,4,3,7,0,2] (sscatter (stranspose @[6,3,7,0,1,4,5,2] (sscatter (stranspose @[2,4,7,3,0,5,6,1] (sscatter (stranspose @[3,7,0,1,2,4,5,6] (w151 !$ [0])) (\\[i152, i153] -> [i152, 2 * i152 + i153]))) (\\[i154, i155, i156] -> [i154, i155, i154 * i155 + i156]))) (\\[i157, i158] -> [2 + (negate i158 + i157), i158]))) (\\[i159, i160, i161, i162, i163] -> [i159 + i160])) (sconcrete (sfromListLinear [0,3,3,3] [])))))"
      -- TODO: was once "\\dret u1 -> rfromS (sconcrete (sreplicate [3,3,3,3] 0.0))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sappend (sconcrete (sreplicate [1,3,3,3] 0.0)) (stranspose @[0,2,1] (sscatter (stranspose @[1,6,5,4,3,7,0,2] (sscatter (stranspose @[6,3,7,0,1,4,5,2] (sscatter (stranspose @[2,4,7,3,0,5,6,1] (sscatter (stranspose @[4,8,3,5,6,7,0,1,2] (soneHot (sscatter (sfromR dret) (\\[i139, i140, i141, i142] -> [let x143 = 1 + i140 ; x144 = 1 + i140 ; x145 = 2 + negate i140 ; x146 = 2 + negate i140 ; x147 = i139 * i141 ; x148 = i139 * i141 ; x149 = 2 * i142 ; x150 = 2 * i142 in ifH (notB (notB (0 <=. tplainPart x143 &&* 0 <=. tplainPart (negate x143)) &&* notB (1 <=. tplainPart x144 &&* (-1) <=. tplainPart (negate x144))) &&* (notB (notB (0 <=. tplainPart x145 &&* 0 <=. tplainPart (negate x145)) &&* notB (1 <=. tplainPart x146 &&* (-1) <=. tplainPart (negate x146))) &&* (notB (notB (0 <=. tplainPart x147 &&* 0 <=. tplainPart (negate x147)) &&* notB (1 <=. tplainPart x148 &&* (-1) <=. tplainPart (negate x148))) &&* notB (notB (0 <=. tplainPart x149 &&* 0 <=. tplainPart (negate x149)) &&* notB (1 <=. tplainPart x150 &&* (-1) <=. tplainPart (negate x150)))))) 0 1, i139, i140, i141, i142])) [0, 0, 0, 0]) !$ [0]) (\\[i152, i153] -> [i152, 2 * i152 + i153]))) (\\[i154, i155, i156] -> [i154, i155, i154 * i155 + i156]))) (\\[i157, i158] -> [2 + (negate i158 + i157), i158]))) (\\[i159, i160, i161, i162, i163] -> [i159 + i160]))))"
      -- TODO: was once "\\dret u1 -> rfromS (sconcrete (sreplicate [3,3,3,3] 0.0))"

testCNNOPP5 :: Assertion
testCNNOPP5 = do
  resetVarCounter
  let blackGlyph :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      blackGlyph = AstFromPrimal $ AstReplicate (SNat @6) knownSTK
                   $ AstReplicate (SNat @6) knownSTK
                   $ AstReplicate (SNat @6) knownSTK
                   $ AstReplicate (SNat @6) knownSTK
                       (rconcrete $ Nested.rscalar 7
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      afcnn2T = conv2dSame4 blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [1,1,2,2] [7.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (sconcrete (sfromListLinear [1,1,2,2] [7.0,0.0,0.0,0.0]))"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP5b :: Assertion
testCNNOPP5b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent conv2dSame4 (FTKR [5, 5, 5, 5] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) (str (ssum @1 (ssum @1 (sfromR dret)))))))) [0, 0, 0, 0])"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (sfromR dret !$ [0, 0, 0, 0]) [0, 0, 0, 0])"

maxPool2dUnpadded4
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded4 arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez4 [2, 2, 2, 2] arr [bb + 1, 2 - bb, aa * iBh, 2 * iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded4: impossible pattern needlessly required"

conv2dSame4
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dSame4 arrA =
  let shB = [1, 1, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez4 shB arrA [iImg, 0, iBh, iBw]
      in rindex0 arrAt [0, 0, 0, 0]
    _ -> error "conv2dSame4: impossible pattern needlessly required"

slicez4
  :: (ADReady target, NumScalar r, KnownNat n)
  => IShR n -> target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez4 shOut d ixBase =
  rbuild shOut $ \ixResult -> indexz03 d (ixrZipWith (+) ixBase ixResult)

testCNNOPP6 :: Assertion
testCNNOPP6 = do
  resetVarCounter
  let blackGlyph :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      blackGlyph = AstFromPrimal $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                       (rconcrete $ Nested.rscalar 7
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      afcnn2T = maxPool2dUnpadded3 $ conv2dSame3z blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (stranspose @[2,0,1] (sgather (stranspose @[1,2,0] (sreplicate @2 (sreplicate @2 (sgather (str (sfromVector (fromList [str (sgather (str (sgather (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\[i53] -> [2 * i53, 2 * i53, 2 * i53]))) (\\[i12] -> [2 * i12])), sconcrete (sreplicate [2,2] 0.0)])) !$ [0]) (\\[i25] -> [ifH (notB (let i23 = 2 * i25 in 0 <=. i23 &&* 0 <=. negate i23) &&* notB (let i24 = 2 * i25 in 0 <=. i24 &&* 0 <=. negate i24)) 1 0, i25]))))) (\\[i58] -> [2 * i58]))) (\\[i61] -> [2 * i61]))) (\\[i4] -> [2 * i4])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i38, i36, i35] -> [ifH (notB (notB (let i28 = 2 * i38 in 0 <=. i28 &&* 0 <=. negate i28) &&* notB (let i29 = 2 * i38 in 0 <=. i29 &&* 0 <=. negate i29)) &&* (notB (notB (let i30 = 2 * i36 in 0 <=. i30 &&* 0 <=. negate i30) &&* notB (let i31 = 2 * i36 in 0 <=. i31 &&* 0 <=. negate i31)) &&* notB (notB (let i32 = 2 * i35 in 0 <=. i32 &&* 0 <=. negate i32) &&* notB (let i33 = 2 * i35 in 0 <=. i33 &&* 0 <=. negate i33)))) 0 1, i38, i36, i35]))))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (str (sgather (sreplicate @2 (str (sreplicate @2 (sgather (sfromVector (fromList [str (sgather (str (sgather (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\[i9] -> [2 * i9, 2 * i9, 2 * i9]))) (\\[i12] -> [2 * i12])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i26, i25] -> [ifH (notB (notB (let i17 = 2 * i26 in 0 <=. i17 &&* 0 <=. negate i17) &&* notB (let i18 = 2 * i26 in 0 <=. i18 &&* 0 <=. negate i18)) &&* (notB (notB (let i19 = 2 * i26 in 0 <=. i19 &&* 0 <=. negate i19) &&* notB (let i20 = 2 * i26 in 0 <=. i20 &&* 0 <=. negate i20)) &&* (notB (notB (let i21 = 2 * i26 in 0 <=. i21 &&* 0 <=. negate i21) &&* notB (let i22 = 2 * i26 in 0 <=. i22 &&* 0 <=. negate i22)) &&* notB (notB (let i23 = 2 * i25 in 0 <=. i23 &&* 0 <=. negate i23) &&* notB (let i24 = 2 * i25 in 0 <=. i24 &&* 0 <=. negate i24))))) 0 1, i26, i25]))))) (\\[i1] -> [2 * i1, 0]))) (\\[i2] -> [2 * i2]))) (\\[i4] -> [2 * i4])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i38, i36, i35] -> [ifH (notB (notB (let i28 = 2 * i38 in 0 <=. i28 &&* 0 <=. negate i28) &&* notB (let i29 = 2 * i38 in 0 <=. i29 &&* 0 <=. negate i29)) &&* (notB (notB (let i30 = 2 * i36 in 0 <=. i30 &&* 0 <=. negate i30) &&* notB (let i31 = 2 * i36 in 0 <=. i31 &&* 0 <=. negate i31)) &&* notB (notB (let i32 = 2 * i35 in 0 <=. i32 &&* 0 <=. negate i32) &&* notB (let i33 = 2 * i35 in 0 <=. i33 &&* 0 <=. negate i33)))) 0 1, i38, i36, i35]))))"

testCNNOPP6b :: Assertion
testCNNOPP6b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dSame3z) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (stranspose @[2,0,1] (sgather (stranspose @[1,2,0] (sreplicate @2 (sreplicate @2 (sgather (str (sfromVector (fromList [str (sgather (str (sgather (sfromR u1) (\\[i120] -> [2 * i120, 2 * i120, 2 * i120]))) (\\[i64] -> [2 * i64])), sconcrete (sreplicate [2,2] 0.0)])) !$ [0]) (\\[i111] -> [let x66 = 2 * i111 ; x67 = 2 * i111 in ifH (notB (0 <=. tplainPart x66 &&* 0 <=. tplainPart (negate x66)) &&* notB (0 <=. tplainPart x67 &&* 0 <=. tplainPart (negate x67))) 1 0, i111]))))) (\\[i125] -> [2 * i125]))) (\\[i128] -> [2 * i128]))) (\\[i70] -> [2 * i70])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i71, i72, i73] -> [let x74 = 2 * i71 ; x75 = 2 * i71 ; x76 = 2 * i72 ; x77 = 2 * i72 ; x78 = 2 * i73 ; x79 = 2 * i73 in ifH (notB (notB (0 <=. tplainPart x74 &&* 0 <=. tplainPart (negate x74)) &&* notB (0 <=. tplainPart x75 &&* 0 <=. tplainPart (negate x75))) &&* (notB (notB (0 <=. tplainPart x76 &&* 0 <=. tplainPart (negate x76)) &&* notB (0 <=. tplainPart x77 &&* 0 <=. tplainPart (negate x77))) &&* notB (notB (0 <=. tplainPart x78 &&* 0 <=. tplainPart (negate x78)) &&* notB (0 <=. tplainPart x79 &&* 0 <=. tplainPart (negate x79))))) 0 1, i71, i72, i73]))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (stranspose @[2,0,1] (sgather (stranspose @[1,2,0] (sreplicate @2 (sreplicate @2 (sgather (str (sfromVector (fromList [str (sgather (str (sgather (sfromR u1) (\\[i63] -> [2 * i63, 2 * i63, 2 * i63]))) (\\[i64] -> [2 * i64])), sconcrete (sreplicate [2,2] 0.0)])) !$ [0]) (\\[i65] -> [let x66 = 2 * i65 ; x67 = 2 * i65 in ifH (notB (0 <=. tplainPart x66 &&* 0 <=. tplainPart (negate x66)) &&* notB (0 <=. tplainPart x67 &&* 0 <=. tplainPart (negate x67))) 1 0, i65]))))) (\\[i68] -> [2 * i68]))) (\\[i69] -> [2 * i69]))) (\\[i70] -> [2 * i70])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i71, i72, i73] -> [let x74 = 2 * i71 ; x75 = 2 * i71 ; x76 = 2 * i72 ; x77 = 2 * i72 ; x78 = 2 * i73 ; x79 = 2 * i73 in ifH (notB (notB (0 <=. tplainPart x74 &&* 0 <=. tplainPart (negate x74)) &&* notB (0 <=. tplainPart x75 &&* 0 <=. tplainPart (negate x75))) &&* (notB (notB (0 <=. tplainPart x76 &&* 0 <=. tplainPart (negate x76)) &&* notB (0 <=. tplainPart x77 &&* 0 <=. tplainPart (negate x77))) &&* notB (notB (0 <=. tplainPart x78 &&* 0 <=. tplainPart (negate x78)) &&* notB (0 <=. tplainPart x79 &&* 0 <=. tplainPart (negate x79))))) 0 1, i71, i72, i73]))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let u90 = sscatter (ssum @2 (stranspose @[2,0,1] (sfromR dret))) (\\[i81, i82, i83] -> [let x84 = 2 * i81 ; x85 = 2 * i81 ; x86 = 2 * i82 ; x87 = 2 * i82 ; x88 = 2 * i83 ; x89 = 2 * i83 in ifH (notB (notB (0 <=. tplainPart x84 &&* 0 <=. tplainPart (negate x84)) &&* notB (0 <=. tplainPart x85 &&* 0 <=. tplainPart (negate x85))) &&* (notB (notB (0 <=. tplainPart x86 &&* 0 <=. tplainPart (negate x86)) &&* notB (0 <=. tplainPart x87 &&* 0 <=. tplainPart (negate x87))) &&* notB (notB (0 <=. tplainPart x88 &&* 0 <=. tplainPart (negate x88)) &&* notB (0 <=. tplainPart x89 &&* 0 <=. tplainPart (negate x89))))) 0 1, i81, i82, i83]) ; t97 = str (soneHot (sscatter (ssum @2 (ssum @2 (stranspose @[2,0,1] (sscatter (stranspose @[1,2,0] (sscatter (stranspose @[2,1,0] (sscatter (stranspose @[2,0,1] (u90 !$ [0])) (\\[i91] -> [2 * i91]))) (\\[i92] -> [2 * i92]))) (\\[i93] -> [2 * i93]))))) (\\[i94] -> [let x95 = 2 * i94 ; x96 = 2 * i94 in ifH (notB (0 <=. tplainPart x95 &&* 0 <=. tplainPart (negate x95)) &&* notB (0 <=. tplainPart x96 &&* 0 <=. tplainPart (negate x96))) 1 0, i94])) [0]) in rfromS (sscatter (str (sscatter (str (t97 !$ [0])) (\\[i98] -> [2 * i98]))) (\\[i99] -> [2 * i99, 2 * i99, 2 * i99]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter (str (sscatter (stranspose @[1,2,0] (soneHot (sscatter (ssum @2 (ssum @2 (stranspose @[2,0,1] (sscatter (stranspose @[1,2,0] (sscatter (stranspose @[2,1,0] (sscatter (sscatter (ssum @2 (stranspose @[2,0,1] (sfromR dret))) (\\[i81, i82, i83] -> [let x84 = 2 * i81 ; x85 = 2 * i81 ; x86 = 2 * i82 ; x87 = 2 * i82 ; x88 = 2 * i83 ; x89 = 2 * i83 in ifH (notB (notB (0 <=. tplainPart x84 &&* 0 <=. tplainPart (negate x84)) &&* notB (0 <=. tplainPart x85 &&* 0 <=. tplainPart (negate x85))) &&* (notB (notB (0 <=. tplainPart x86 &&* 0 <=. tplainPart (negate x86)) &&* notB (0 <=. tplainPart x87 &&* 0 <=. tplainPart (negate x87))) &&* notB (notB (0 <=. tplainPart x88 &&* 0 <=. tplainPart (negate x88)) &&* notB (0 <=. tplainPart x89 &&* 0 <=. tplainPart (negate x89))))) 0 1, i83, i81, i82]) !$ [0]) (\\[i91] -> [2 * i91]))) (\\[i92] -> [2 * i92]))) (\\[i93] -> [2 * i93]))))) (\\[i94] -> [let x95 = 2 * i94 ; x96 = 2 * i94 in ifH (notB (0 <=. tplainPart x95 &&* 0 <=. tplainPart (negate x95)) &&* notB (0 <=. tplainPart x96 &&* 0 <=. tplainPart (negate x96))) 1 0, i94])) [0]) !$ [0]) (\\[i98] -> [2 * i98]))) (\\[i99] -> [2 * i99, 2 * i99, 2 * i99]))"
      -- TODO: was once "\\dret u1 -> rfromS (soneHot (ssum0 (stranspose @[0,1,3,2] (sfromR dret) !$ [0, 0, 0])) [0, 0, 0, 0])"

conv2dSame3z
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dSame3z arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez3 shB arrA [iImg, iImg, iImg, iBw]
      in rindex0 arrAt [iBh, iBw, iImg, iBh]
    _ -> error "conv2dSame3z: impossible pattern needlessly required"

testCNNOPP7 :: Assertion
testCNNOPP7 = do
  resetVarCounter
  let blackGlyph :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      blackGlyph = AstFromPrimal $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                       (rconcrete $ Nested.rscalar 7
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      afcnn2T = maxPool2dUnpadded3y $ conv2dSame3y blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sgather (sfromVector (fromList [stranspose @[1,2,3,0] (sgather (stranspose @[3,2,0,1] (sgather (stranspose @[2,3,0,1] (sgather (sreplicate @2 (sreplicate @2 (sgather (sfromVector (fromList [str (sgather (str (sgather (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\[i56] -> [2 * i56, 2 * i56, 2 * i56]))) (\\[i11] -> [2 * i11])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i26, i25] -> [ifH (notB (notB (let i17 = 2 * i26 in 0 <=. i17 &&* 0 <=. negate i17) &&* notB (let i18 = 2 * i26 in 0 <=. i18 &&* 0 <=. negate i18)) &&* (notB (notB (let i19 = 2 * i26 in 0 <=. i19 &&* 0 <=. negate i19) &&* notB (let i20 = 2 * i26 in 0 <=. i20 &&* 0 <=. negate i20)) &&* (notB (notB (let i21 = 2 * i26 in 0 <=. i21 &&* 0 <=. negate i21) &&* notB (let i22 = 2 * i26 in 0 <=. i22 &&* 0 <=. negate i22)) &&* notB (notB (let i23 = 2 * i25 in 0 <=. i23 &&* 0 <=. negate i23) &&* notB (let i24 = 2 * i25 in 0 <=. i24 &&* 0 <=. negate i24))))) 0 1, i26, i25])))) (\\[i60] -> [2 * i60]))) (\\[i63, i64] -> [2 * i64, 2 * i63]))) (\\[i4] -> [2 * i4])), sconcrete (sreplicate [2,2,2,2] 0.0)])) (\\[i43, i40, i38, i37] -> [ifH (notB (notB (let i28 = 2 * i38 in 0 <=. i28 &&* 0 <=. negate i28) &&* notB (let i29 = 2 * i38 in 0 <=. i29 &&* 0 <=. negate i29)) &&* (notB (notB (let i30 = 2 * i43 in 0 <=. i30 &&* 0 <=. negate i30) &&* notB (let i31 = 2 * i43 in 0 <=. i31 &&* 0 <=. negate i31)) &&* (notB (notB (let i32 = 2 * i40 in 0 <=. i32 &&* 0 <=. negate i32) &&* notB (let i33 = 2 * i40 in 0 <=. i33 &&* 0 <=. negate i33)) &&* notB (notB (let i34 = 2 * i37 in 0 <=. i34 &&* 0 <=. negate i34) &&* notB (let i35 = 2 * i37 in 0 <=. i35 &&* 0 <=. negate i35))))) 0 1, i43, i40, i38, i37]))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (sgather (sfromVector (fromList [stranspose @[1,2,3,0] (sgather (stranspose @[3,2,0,1] (sgather (stranspose @[1,2,0] (sgather (sreplicate @2 (stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [str (sgather (str (sgather (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\[i9] -> [2 * i9, 2 * i9, 2 * i9]))) (\\[i11] -> [2 * i11])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i26, i25] -> [ifH (notB (notB (let i17 = 2 * i26 in 0 <=. i17 &&* 0 <=. negate i17) &&* notB (let i18 = 2 * i26 in 0 <=. i18 &&* 0 <=. negate i18)) &&* (notB (notB (let i19 = 2 * i26 in 0 <=. i19 &&* 0 <=. negate i19) &&* notB (let i20 = 2 * i26 in 0 <=. i20 &&* 0 <=. negate i20)) &&* (notB (notB (let i21 = 2 * i26 in 0 <=. i21 &&* 0 <=. negate i21) &&* notB (let i22 = 2 * i26 in 0 <=. i22 &&* 0 <=. negate i22)) &&* notB (notB (let i23 = 2 * i25 in 0 <=. i23 &&* 0 <=. negate i23) &&* notB (let i24 = 2 * i25 in 0 <=. i24 &&* 0 <=. negate i24))))) 0 1, i26, i25]))))) (\\[i1] -> [2 * i1]))) (\\[i42, i3] -> [2 * i3, 2 * i42]))) (\\[i4] -> [2 * i4])), sconcrete (sreplicate [2,2,2,2] 0.0)])) (\\[i43, i40, i38, i37] -> [ifH (notB (notB (let i28 = 2 * i38 in 0 <=. i28 &&* 0 <=. negate i28) &&* notB (let i29 = 2 * i38 in 0 <=. i29 &&* 0 <=. negate i29)) &&* (notB (notB (let i30 = 2 * i43 in 0 <=. i30 &&* 0 <=. negate i30) &&* notB (let i31 = 2 * i43 in 0 <=. i31 &&* 0 <=. negate i31)) &&* (notB (notB (let i32 = 2 * i40 in 0 <=. i32 &&* 0 <=. negate i32) &&* notB (let i33 = 2 * i40 in 0 <=. i33 &&* 0 <=. negate i33)) &&* notB (notB (let i34 = 2 * i37 in 0 <=. i34 &&* 0 <=. negate i34) &&* notB (let i35 = 2 * i37 in 0 <=. i35 &&* 0 <=. negate i35))))) 0 1, i43, i40, i38, i37]))"

testCNNOPP7b :: Assertion
testCNNOPP7b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3y . conv2dSame3y) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sgather (sfromVector (fromList [stranspose @[1,2,3,0] (sgather (stranspose @[3,2,0,1] (sgather (stranspose @[2,3,0,1] (sgather (sreplicate @2 (sreplicate @2 (sgather (sfromVector (fromList [str (sgather (str (sgather (sfromR u1) (\\[i136] -> [2 * i136, 2 * i136, 2 * i136]))) (\\[i67] -> [2 * i67])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i139, i138] -> [let x70 = 2 * i139 ; x71 = 2 * i139 ; x72 = 2 * i139 ; x73 = 2 * i139 ; x74 = 2 * i139 ; x75 = 2 * i139 ; x76 = 2 * i138 ; x77 = 2 * i138 in ifH (notB (notB (0 <=. tplainPart x70 &&* 0 <=. tplainPart (negate x70)) &&* notB (0 <=. tplainPart x71 &&* 0 <=. tplainPart (negate x71))) &&* (notB (notB (0 <=. tplainPart x72 &&* 0 <=. tplainPart (negate x72)) &&* notB (0 <=. tplainPart x73 &&* 0 <=. tplainPart (negate x73))) &&* (notB (notB (0 <=. tplainPart x74 &&* 0 <=. tplainPart (negate x74)) &&* notB (0 <=. tplainPart x75 &&* 0 <=. tplainPart (negate x75))) &&* notB (notB (0 <=. tplainPart x76 &&* 0 <=. tplainPart (negate x76)) &&* notB (0 <=. tplainPart x77 &&* 0 <=. tplainPart (negate x77)))))) 0 1, i139, i138])))) (\\[i144] -> [2 * i144]))) (\\[i147, i148] -> [2 * i148, 2 * i147]))) (\\[i81] -> [2 * i81])), sconcrete (sreplicate [2,2,2,2] 0.0)])) (\\[i82, i83, i84, i85] -> [let x86 = 2 * i84 ; x87 = 2 * i84 ; x88 = 2 * i82 ; x89 = 2 * i82 ; x90 = 2 * i83 ; x91 = 2 * i83 ; x92 = 2 * i85 ; x93 = 2 * i85 in ifH (notB (notB (0 <=. tplainPart x86 &&* 0 <=. tplainPart (negate x86)) &&* notB (0 <=. tplainPart x87 &&* 0 <=. tplainPart (negate x87))) &&* (notB (notB (0 <=. tplainPart x88 &&* 0 <=. tplainPart (negate x88)) &&* notB (0 <=. tplainPart x89 &&* 0 <=. tplainPart (negate x89))) &&* (notB (notB (0 <=. tplainPart x90 &&* 0 <=. tplainPart (negate x90)) &&* notB (0 <=. tplainPart x91 &&* 0 <=. tplainPart (negate x91))) &&* notB (notB (0 <=. tplainPart x92 &&* 0 <=. tplainPart (negate x92)) &&* notB (0 <=. tplainPart x93 &&* 0 <=. tplainPart (negate x93)))))) 0 1, i82, i83, i84, i85]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sgather (sfromVector (fromList [stranspose @[1,2,3,0] (sgather (stranspose @[3,2,0,1] (sgather (stranspose @[2,3,0,1] (sgather (sreplicate @2 (sreplicate @2 (sgather (sfromVector (fromList [str (sgather (str (sgather (sfromR u1) (\\[i66] -> [2 * i66, 2 * i66, 2 * i66]))) (\\[i67] -> [2 * i67])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i68, i69] -> [let x70 = 2 * i68 ; x71 = 2 * i68 ; x72 = 2 * i68 ; x73 = 2 * i68 ; x74 = 2 * i68 ; x75 = 2 * i68 ; x76 = 2 * i69 ; x77 = 2 * i69 in ifH (notB (notB (0 <=. tplainPart x70 &&* 0 <=. tplainPart (negate x70)) &&* notB (0 <=. tplainPart x71 &&* 0 <=. tplainPart (negate x71))) &&* (notB (notB (0 <=. tplainPart x72 &&* 0 <=. tplainPart (negate x72)) &&* notB (0 <=. tplainPart x73 &&* 0 <=. tplainPart (negate x73))) &&* (notB (notB (0 <=. tplainPart x74 &&* 0 <=. tplainPart (negate x74)) &&* notB (0 <=. tplainPart x75 &&* 0 <=. tplainPart (negate x75))) &&* notB (notB (0 <=. tplainPart x76 &&* 0 <=. tplainPart (negate x76)) &&* notB (0 <=. tplainPart x77 &&* 0 <=. tplainPart (negate x77)))))) 0 1, i68, i69])))) (\\[i78] -> [2 * i78]))) (\\[i79, i80] -> [2 * i80, 2 * i79]))) (\\[i81] -> [2 * i81])), sconcrete (sreplicate [2,2,2,2] 0.0)])) (\\[i82, i83, i84, i85] -> [let x86 = 2 * i84 ; x87 = 2 * i84 ; x88 = 2 * i82 ; x89 = 2 * i82 ; x90 = 2 * i83 ; x91 = 2 * i83 ; x92 = 2 * i85 ; x93 = 2 * i85 in ifH (notB (notB (0 <=. tplainPart x86 &&* 0 <=. tplainPart (negate x86)) &&* notB (0 <=. tplainPart x87 &&* 0 <=. tplainPart (negate x87))) &&* (notB (notB (0 <=. tplainPart x88 &&* 0 <=. tplainPart (negate x88)) &&* notB (0 <=. tplainPart x89 &&* 0 <=. tplainPart (negate x89))) &&* (notB (notB (0 <=. tplainPart x90 &&* 0 <=. tplainPart (negate x90)) &&* notB (0 <=. tplainPart x91 &&* 0 <=. tplainPart (negate x91))) &&* notB (notB (0 <=. tplainPart x92 &&* 0 <=. tplainPart (negate x92)) &&* notB (0 <=. tplainPart x93 &&* 0 <=. tplainPart (negate x93)))))) 0 1, i82, i83, i84, i85]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w107 = sscatter (sfromR dret) (\\[i95, i96, i97, i98] -> [let x99 = 2 * i97 ; x100 = 2 * i97 ; x101 = 2 * i95 ; x102 = 2 * i95 ; x103 = 2 * i96 ; x104 = 2 * i96 ; x105 = 2 * i98 ; x106 = 2 * i98 in ifH (notB (notB (0 <=. tplainPart x99 &&* 0 <=. tplainPart (negate x99)) &&* notB (0 <=. tplainPart x100 &&* 0 <=. tplainPart (negate x100))) &&* (notB (notB (0 <=. tplainPart x101 &&* 0 <=. tplainPart (negate x101)) &&* notB (0 <=. tplainPart x102 &&* 0 <=. tplainPart (negate x102))) &&* (notB (notB (0 <=. tplainPart x103 &&* 0 <=. tplainPart (negate x103)) &&* notB (0 <=. tplainPart x104 &&* 0 <=. tplainPart (negate x104))) &&* notB (notB (0 <=. tplainPart x105 &&* 0 <=. tplainPart (negate x105)) &&* notB (0 <=. tplainPart x106 &&* 0 <=. tplainPart (negate x106)))))) 0 1, i95, i96, i97, i98]) ; t122 = sscatter (ssum @2 (ssum @2 (sscatter (stranspose @[2,3,0,1] (sscatter (stranspose @[2,3,1,0] (sscatter (stranspose @[3,0,1,2] (w107 !$ [0])) (\\[i108] -> [2 * i108]))) (\\[i109, i110] -> [2 * i110, 2 * i109]))) (\\[i111] -> [2 * i111])))) (\\[i112, i113] -> [let x114 = 2 * i112 ; x115 = 2 * i112 ; x116 = 2 * i112 ; x117 = 2 * i112 ; x118 = 2 * i112 ; x119 = 2 * i112 ; x120 = 2 * i113 ; x121 = 2 * i113 in ifH (notB (notB (0 <=. tplainPart x114 &&* 0 <=. tplainPart (negate x114)) &&* notB (0 <=. tplainPart x115 &&* 0 <=. tplainPart (negate x115))) &&* (notB (notB (0 <=. tplainPart x116 &&* 0 <=. tplainPart (negate x116)) &&* notB (0 <=. tplainPart x117 &&* 0 <=. tplainPart (negate x117))) &&* (notB (notB (0 <=. tplainPart x118 &&* 0 <=. tplainPart (negate x118)) &&* notB (0 <=. tplainPart x119 &&* 0 <=. tplainPart (negate x119))) &&* notB (notB (0 <=. tplainPart x120 &&* 0 <=. tplainPart (negate x120)) &&* notB (0 <=. tplainPart x121 &&* 0 <=. tplainPart (negate x121)))))) 0 1, i112, i113]) in rfromS (sscatter (str (sscatter (str (t122 !$ [0])) (\\[i123] -> [2 * i123]))) (\\[i124] -> [2 * i124, 2 * i124, 2 * i124]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter (str (sscatter (sscatter (ssum @2 (ssum @2 (sscatter (stranspose @[2,3,0,1] (sscatter (stranspose @[2,3,1,0] (sscatter (sscatter (sfromR dret) (\\[i95, i96, i97, i98] -> [let x99 = 2 * i97 ; x100 = 2 * i97 ; x101 = 2 * i95 ; x102 = 2 * i95 ; x103 = 2 * i96 ; x104 = 2 * i96 ; x105 = 2 * i98 ; x106 = 2 * i98 in ifH (notB (notB (0 <=. tplainPart x99 &&* 0 <=. tplainPart (negate x99)) &&* notB (0 <=. tplainPart x100 &&* 0 <=. tplainPart (negate x100))) &&* (notB (notB (0 <=. tplainPart x101 &&* 0 <=. tplainPart (negate x101)) &&* notB (0 <=. tplainPart x102 &&* 0 <=. tplainPart (negate x102))) &&* (notB (notB (0 <=. tplainPart x103 &&* 0 <=. tplainPart (negate x103)) &&* notB (0 <=. tplainPart x104 &&* 0 <=. tplainPart (negate x104))) &&* notB (notB (0 <=. tplainPart x105 &&* 0 <=. tplainPart (negate x105)) &&* notB (0 <=. tplainPart x106 &&* 0 <=. tplainPart (negate x106)))))) 0 1, i98, i95, i96, i97]) !$ [0]) (\\[i108] -> [2 * i108]))) (\\[i109, i110] -> [2 * i110, 2 * i109]))) (\\[i111] -> [2 * i111])))) (\\[i112, i113] -> [let x114 = 2 * i112 ; x115 = 2 * i112 ; x116 = 2 * i112 ; x117 = 2 * i112 ; x118 = 2 * i112 ; x119 = 2 * i112 ; x120 = 2 * i113 ; x121 = 2 * i113 in ifH (notB (notB (0 <=. tplainPart x114 &&* 0 <=. tplainPart (negate x114)) &&* notB (0 <=. tplainPart x115 &&* 0 <=. tplainPart (negate x115))) &&* (notB (notB (0 <=. tplainPart x116 &&* 0 <=. tplainPart (negate x116)) &&* notB (0 <=. tplainPart x117 &&* 0 <=. tplainPart (negate x117))) &&* (notB (notB (0 <=. tplainPart x118 &&* 0 <=. tplainPart (negate x118)) &&* notB (0 <=. tplainPart x119 &&* 0 <=. tplainPart (negate x119))) &&* notB (notB (0 <=. tplainPart x120 &&* 0 <=. tplainPart (negate x120)) &&* notB (0 <=. tplainPart x121 &&* 0 <=. tplainPart (negate x121)))))) 0 1, i113, i112]) !$ [0]) (\\[i123] -> [2 * i123]))) (\\[i124] -> [2 * i124, 2 * i124, 2 * i124]))"
      -- TODO: was once "\\dret u1 -> rfromS (soneHot (sfromR dret !$ [0, 0, 0, 0]) [0, 0, 0, 0])"

maxPool2dUnpadded3y
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded3y arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez3 [2, 2, 2, 2] arr [iBh, aa, bb, iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded3y: impossible pattern needlessly required"

conv2dSame3y
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dSame3y arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez3 shB arrA [iImg, iImg, iImg, iBh]
      in rindex0 arrAt [iBh, iBw, iImg, iBh]
    _ -> error "conv2dSame3y: impossible pattern needlessly required"

-- This test uses a disastrous version of smaximum, but shows how
-- smaxIndex gets non-trivially vectorized, preserving sharing, too.
testCNNOPP4bU :: Assertion
testCNNOPP4bU = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpaddedS4 @4 @2) (FTKS (SNat @31 :$$ SNat @31 :$$ SNat @31 :$$ SNat @31 :$$ ZSS) (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> let w52 = sgather (stranspose @[4,2,3,0,1] (sgather (stranspose @[2,0,1] u1) (\\[i99, i100] -> [2 * i99 + i100]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (sreshape @[31,31,15,15,16] (stranspose @[2,3,4,0,5,1] (splainPart w52))) in sgather w52 (\\[i54, i55, i56, i57] -> [i57, remH (tplainPart (kfromS (u53 !$ [i54, i55, i56, i57]))) 4, i54, i55, i56, remH (quotH (tplainPart (kfromS (u53 !$ [i54, i55, i56, i57]))) 4) 4])"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w52 = sgather (stranspose @[4,2,3,0,1] (sgather (stranspose @[2,0,1] u1) (\\[i48, i49] -> [2 * i48 + i49]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (splainPart (sreshape @[31,31,15,15,16] (stranspose @[2,3,4,0,5,1] (splainPart w52)))) in sgather w52 (\\[i54, i55, i56, i57] -> [i57, remH (tplainPart (kfromS (u53 !$ [i54, i55, i56, i57]))) 4, i54, i55, i56, remH (quotH (tplainPart (kfromS (u53 !$ [i54, i55, i56, i57]))) 4) 4])"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w52 = sgather (stranspose @[4,2,3,0,1] (sgather (stranspose @[2,0,1] u1) (\\[i48, i49] -> [2 * i48 + i49]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (splainPart (sreshape @[31,31,15,15,16] (stranspose @[2,3,4,0,5,1] (splainPart w52)))) in stranspose @[1,2,0] (sscatter (stranspose @[3,4,1,2,0] (sscatter (sscatter dret (\\[i59, i60, i61, i62] -> [i62, remH (tplainPart (kfromS (u53 !$ [i59, i60, i61, i62]))) 4, i59, i60, i61, remH (quotH (tplainPart (kfromS (u53 !$ [i59, i60, i61, i62]))) 4) 4])) (\\[i63, i64] -> [2 * i63 + i64]))) (\\[i65, i66] -> [2 * i65 + i66]))"
-- TODO: different test result with GHC 9.10:   printArtifactPretty (simplifyArtifact artifactRev)
--    @?= "\\dret u1 -> let u53 = smaxIndex (sreshape @[31,31,15,15,16] (stranspose @[2,3,4,0,5,1] (sgather (stranspose @[4,2,3,0,1] (sgather (stranspose @[2,0,1] u1) (\\[i82, i83] -> [2 * i82 + i83]))) (\\[i50, i51] -> [2 * i50 + i51])))) in stranspose @[1,2,0] (sscatter (stranspose @[3,4,1,2,0] (sscatter (sscatter dret (\\[i59, i60, i61, i62] -> [i62, remH (kfromS (u53 !$ [i59, i60, i61, i62])) 4, i59, i60, i61, remH (quotH (kfromS (u53 !$ [i59, i60, i61, i62])) 4) 4])) (\\[i63, i64] -> [2 * i63 + i64]))) (\\[i65, i66] -> [2 * i65 + i66]))"

smaximum4 :: forall r sh target. (ADReady target, NumScalar r, KnownShS sh)
          => target (TKS sh r) -> target (TKS '[] r)
smaximum4 t0 =
  tlet t0 $ \t ->
  ttletPrimal (tprimalPart $ kfromS $ smaxIndex (sflatten t)) $ \maxIndex ->
    sindex0 t
    $ fromLinearIdxS (kplainPart @target . kconcrete . fromIntegral)
                     (sshape t)
                     (kplainPart $ kfromPrimal @target maxIndex)

maxPool2dUnpaddedS4
  :: forall ksize stride batch_size channels h w target r shOut shK1.
     ( KnownNat ksize, KnownNat stride, KnownNat batch_size, KnownNat channels
     , KnownNat h, KnownNat w
     , 1 <= stride  -- wrongly reported as redundant due to plugins
     , ADReady target, NumScalar r
     , shOut ~ '[batch_size, channels, h `Div` stride, w `Div` stride]
     , shK1 ~ '[1, 1, ksize, ksize]
     )
  => target (TKS '[batch_size, channels, h, w] r)
  -> target (TKS shOut r)
maxPool2dUnpaddedS4 arr =
  let stride = valueOf @stride :: Int
  in sbuild @(Rank shOut) $ \case
    [iImg, iChan, iBh, iBw] ->
      smaximum4 $ slicezS @shK1 arr [ iImg, iChan
                                    , fromIntegral stride * iBh
                                    , fromIntegral stride * iBw ]
    _ -> error "maxPool2dUnpaddedS4: impossible pattern needlessly required"
