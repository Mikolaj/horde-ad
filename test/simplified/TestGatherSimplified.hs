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
  , testCase "scatterSimpPP12" testScatterSimpPP12
  , testCase "scatterSimp12" testScatterSimp12

  , testCase "shmatterBarReluADVal320" testBarReluADVal320
  , testCase "shmatterReluSimpPP" testReluSimpPP

  , testCase "sminimizedCNNOPP2" testCNNOPP2
  , testCase "sminimizedCNNOPP2b" testCNNOPP2b
--  , testCase "sminimizedCNNOPP3" testCNNOPP3
--  , testCase "sminimizedCNNOPP3b" testCNNOPP3b
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
  length (show t1) @?= 450
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 456
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 450
  length (show (simplifyInlineContract @(TKR 3 Float) @PrimalSpan t2)) @?= 456

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
gatherTranspose33 :: forall target r. (ADReady target, GoodScalar r, RealFloat r)
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
  length (show t1) @?= 1117
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 847
  resetVarCounter
  let !t2 = (\t -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                            (rreshape @10 [8, 16] t))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 796
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 526

testGatherSimpPP34 :: Assertion
testGatherSimpPP34 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
             gatherTranspose33 @(AstTensor AstMethodLet PrimalSpan) (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 2504
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 19838
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              (\t' -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                               (rreshape @10 [8, 16] t'))
                (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 2145
  length (show (simplifyInlineContract @(TKR 3 Float) @PrimalSpan t2)) @?= 19479

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

scatterNested1 :: forall target r. (ADReady target, GoodScalar r)
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

scatter1 :: forall target r. (ADReady target, GoodScalar r)
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

scatterNested2 :: forall target r. (ADReady target, GoodScalar r)
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

scatter2 :: forall target r. (ADReady target, GoodScalar r)
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

scatterNested12 :: forall target r. (ADReady target, GoodScalar r)
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

scatter12 :: forall target r. (ADReady target, GoodScalar r)
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
  :: ( ADReady target, GoodScalar r, KnownNat n, Differentiable r )
  => target (TKR n r) -> target (TKR n r)
barRelu x = let t = rreplicate0N (rshape x) (rscalar 0.001) * x
            in relu $ bar (t, relu t)

barRelu10xSlower
  :: ( ADReady target, GoodScalar r, KnownNat n, Differentiable r )
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
  length (show t1) @?= 22675
  length (show (simplifyInlineContract @(TKR 10 Float) t1)) @?= 22675
  resetVarCounter
  let !t2 = barRelu @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 12258
  length (show (simplifyInlineContract @(TKR 10 Float) t2)) @?= 12258

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
      let arrt = slicez2 (conv2dUnpadded2 a) [iBw, 1, 2 * iBh, 2 * iBw]
      in rmaximum2 arrt
    _ -> error "maxPool2dUnpadded2: impossible pattern needlessly required"

conv2dUnpadded2
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded2 a =
  rbuild [3, 3, 2, 2] $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez2 a [iImg, 0, iBh, iBw]
      in rindex0 arrAt [0, iBw, iBw, 0]
    _ -> error "conv2dUnpadded2: impossible pattern needlessly required"

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
      afcnn2T = maxPool2dUnpadded3 $ conv2dUnpadded3 blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [14.0,0.0,14.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (stranspose @[1,2,0] (sreplicate @2 (let w32 = stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (let t44 = sreplicate @2 (sgather (sappend (stranspose @[4,1,2,3,5,0] (sappend (sreplicate @1 (stranspose @[0,1,2,4,3] (sgather (str (sreplicate @1 (sconcrete (sfromListLinear [2] [7.0,0.0])))) (\\[i31, i25, i20, i17] -> [ifH (notB (notB (0 <=. negate i31 + negate i20) &&* notB (1 <=. i31 + i20 &&* (-1) <=. negate i31 + negate i20)) &&* notB (notB (0 <=. negate i25 + negate i17) &&* notB (1 <=. i25 + i17 &&* (-1) <=. negate i25 + negate i17))) 0 1])))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sscalar 0.0))))))))) (stranspose @[4,1,2,3,5,0] (sappend (sreplicate @1 (stranspose @[0,1,2,4,3] (sgather (str (sreplicate @1 (sconcrete (sfromListLinear [2] [7.0,0.0])))) (\\[i30, i24, i19, i17] -> [ifH (notB (notB (0 <=. negate i30 + negate i19) &&* notB (1 <=. i30 + i19 &&* (-1) <=. negate i30 + negate i19)) &&* notB (notB (0 <=. negate i24 + negate i17) &&* notB (1 <=. i24 + i17 &&* (-1) <=. negate i24 + negate i17))) 0 1])))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sscalar 0.0)))))))))) (\\[i39, i4] -> [2 * i4, 0, 2 * i4, 0, 0, 2 * i39]) + sgather (sappend (sreplicate @1 (sgather (stranspose @[1,2,3,4,5,0] (sappend (sreplicate @1 (stranspose @[0,2,4,3,1] (sgather (str (sreplicate @1 (sconcrete (sfromListLinear [2] [7.0,0.0])))) (\\[i28, i22, i19, i17] -> [ifH (notB (notB (0 <=. negate i28 + negate i19) &&* notB (1 <=. i28 + i19 &&* (-1) <=. negate i28 + negate i19)) &&* notB (notB (0 <=. negate i22 + negate i17) &&* notB (1 <=. i22 + i17 &&* (-1) <=. negate i22 + negate i17))) 0 1])))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))))) (\\[i27] -> [i27, i27, 0, 1, 0]))) (str (sreplicate @2 (str (sreplicate @2 (sconcrete (sfromListLinear [1] [0.0]))))))) (\\[i38, i4] -> [2 * i4, 0, 2 * i38])) in sappend (str (sappend (stranspose @[1,2,0] (sappend (sgather t44 (\\[i34, i37, i42] -> [i42, i37, i34])) (sreplicate @1 (sreplicate @1 (sreplicate @1 (sscalar 0.0)))))) (sreplicate @1 (sreplicate @1 (sreplicate @2 (sscalar 0.0)))))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))))))))) in stranspose @[3,4,5,6,0,1,2] w32 !$ [0, 0, 0, 0])))"
-}

-- TODO: OOMs
_testCNNOPP3b :: Assertion
_testCNNOPP3b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dUnpadded3) (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1,2,0] (sreplicate @2 (sappend (sreplicate @1 (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 1] + sfromR u1 !$ [0, 1, 1, 1])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0)))) (sconcrete (sreplicate [1,2,2] 0.0)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (stranspose @[1,2,0] (sreplicate @2 (sappend (sreplicate @1 (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 1] + sfromR u1 !$ [0, 1, 1, 1])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0)))) (sconcrete (sreplicate [1,2,2] 0.0)))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let t80 = ssum @2 (stranspose @[2,0,1] (sfromR dret)) in rfromS (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) t80)))))) [0, 0, 0, 1] + soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) t80)))))) [0, 1, 1, 1])"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (let t80 = ssum @2 (stranspose @[2,0,1] (sfromR dret)) in soneHot (t80 !$ [0, 0, 0]) [0, 0, 0, 1] + soneHot (t80 !$ [0, 0, 0]) [0, 1, 1, 1])"

maxPool2dUnpadded3
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded3 arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez3 [2, 2, 2, 2] arr [iBh `quotH` 2, aa, bb, iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded3: impossible pattern needlessly required"

conv2dUnpadded3
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded3 arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez4 shB arrA [iImg, 0, iBw, 1]
      in rindex0 arrAt [0, iBw, iImg, iBh] + rindex0 arrAt [iImg, 1, iBw + 1, iBh]
    _ -> error "conv2dUnpadded3: impossible pattern needlessly required"

slicez3
  :: (ADReady target, GoodScalar r, KnownNat n)
  => IShR n -> target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez3 shOut d ixBase =
  rbuild shOut $ \_ -> indexz03 d (ixrZipWith (+) ixBase ixBase)

indexz03
  :: forall target r n. (ADReady target, GoodScalar r, KnownNat n)
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
    @?= "rfromS (let w77 = stranspose @[5,6,7,8,0,1,2,3,4] (sfromVector (fromList [stranspose @[2,3,4,0,5,6,7,1] (sgather (stranspose @[6,0,3,1,4,5,2] (sgather (stranspose @[4,1,3,0,2] (sgather (stranspose @[3,0,4,1,2] (sgather (sconcrete (sreplicate [2,3,3,3] 7.0)) (\\[i52, i55] -> [i52 + i55]))) (\\[i58, i60] -> [2 + (negate i60 + i58), i60]))) (\\[i62, i64, i67] -> [i62 * i64 + i67]))) (\\[i22, i8] -> [2 * i22 + i8])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0] in stranspose @[1,2,3,0] (sappend (sreplicate @1 (str (sappend (sreplicate @1 (stranspose @[0,2,4,1,3] w77 !$ [1, 0, 0])) (sreplicate @1 (stranspose @[0,2,4,1,3] w77 !$ [1, 1, 0]))))) (sreplicate @1 (stranspose @[0,4,1,2,3] w77 !$ [1, 1]))))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (let w19 = sgather (sfromVector (fromList [stranspose @[2,3,4,0,5,6,7,1] (sgather (stranspose @[6,0,3,1,4,5,2] (sgather (stranspose @[3,0,2,1] (sgather (stranspose @[0,2,1] (sgather (sconcrete (sreplicate [2,3,3,3] 7.0)) (\\[i32, i5] -> [i32 + i5]))) (\\[i31, i6] -> [i31, 2 + (negate i31 + i6)]))) (\\[i36, i26, i7] -> [i36 * i26 + i7]))) (\\[i22, i8] -> [2 * i22 + i8])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) (\\[i34, i28, i24, i21, i15, i12, i10, i9] -> [ifH (0 <=. negate i28 + negate i15 &&* (1 <=. i28 + negate i12 &&* (notB (notB (0 <=. negate i34 * i24 + negate i10) &&* notB (1 <=. i34 * i24 + i10 &&* (-1) <=. negate i34 * i24 + negate i10)) &&* notB (notB (0 <=. (-2) * i21 + negate i9) &&* notB (1 <=. 2 * i21 + i9 &&* (-1) <=. (-2) * i21 + negate i9))))) 0 1, i34, i28, i24, i21, i15, i12, i10, i9]) in stranspose @[4,5,6,7,0,1,2,3] w19 !$ [0, 0, 0, 0])"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP4b :: Assertion
testCNNOPP4b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded4 (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (let w120 = stranspose @[5,6,7,8,0,1,2,3,4] (sfromVector (fromList [stranspose @[2,3,4,0,5,6,7,1] (sgather (stranspose @[4,7,0,3,1,5,6,2] (sgather (stranspose @[3,4,7,1,5,6,0,2] (sgather (stranspose @[6,0,7,4,3,2,1,5] (sgather (sslice (SNat @1) (SNat @2) (stranspose @[0,2,1] (sfromR u1))) (\\[i241, i243, i244, i245, i246] -> [i241 + i243]))) (\\[i252, i255] -> [2 + (negate i255 + i252), i255]))) (\\[i258, i260, i263] -> [i258, i260, i258 * i260 + i263]))) (\\[i118, i119] -> [i118, 2 * i118 + i119])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0] in stranspose @[1,2,3,0] (sappend (sreplicate @1 (str (sappend (sreplicate @1 (stranspose @[0,2,4,1,3] w120 !$ [1, 0, 0])) (sreplicate @1 (stranspose @[0,2,4,1,3] w120 !$ [1, 1, 0]))))) (sreplicate @1 (stranspose @[0,4,1,2,3] w120 !$ [1, 1]))))"
      -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w120 = stranspose @[5,6,7,8,0,1,2,3,4] (sfromVector (fromList [stranspose @[2,3,4,0,5,6,7,1] (sgather (stranspose @[4,7,0,3,1,5,6,2] (sgather (stranspose @[3,4,7,1,5,6,0,2] (sgather (stranspose @[6,0,7,4,3,2,1,5] (sgather (sslice (SNat @1) (SNat @2) (stranspose @[0,2,1] (sfromR u1))) (\\[i108, i109, i110, i111, i112] -> [i108 + i109]))) (\\[i113, i114] -> [2 + (negate i114 + i113), i114]))) (\\[i115, i116, i117] -> [i115, i116, i115 * i116 + i117]))) (\\[i118, i119] -> [i118, 2 * i118 + i119])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0] in rfromS (stranspose @[1,2,3,0] (sappend (sreplicate @1 (str (sappend (sreplicate @1 (stranspose @[0,2,4,1,3] w120 !$ [1, 0, 0])) (sreplicate @1 (stranspose @[0,2,4,1,3] w120 !$ [1, 1, 0]))))) (sreplicate @1 (stranspose @[0,4,1,2,3] w120 !$ [1, 1]))))"
      -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w122 = stranspose @[4,5,6,7,8,0,1,2,3] (soneHot (stranspose @[0,3,1,4,2] (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (str (ssum @1 (sslice (SNat @0) (SNat @1) (stranspose @[3,0,1,2] (sfromR dret))))))) [1, 0, 0]) + (stranspose @[0,3,1,4,2] (soneHot (ssum @1 (sslice (SNat @1) (SNat @1) (str (ssum @1 (sslice (SNat @0) (SNat @1) (stranspose @[3,0,1,2] (sfromR dret))))))) [1, 1, 0]) + stranspose @[0,2,3,4,1] (soneHot (ssum @1 (sslice (SNat @1) (SNat @1) (stranspose @[3,0,1,2] (sfromR dret)))) [1, 1]))) [0, 0, 0, 0]) in rfromS (stranspose @[0,2,1] (sappend (sconcrete (sreplicate [1,3,3,3] 0.0)) (sappend (sscatter (stranspose @[1,6,5,4,3,7,0,2] (sscatter (stranspose @[6,3,7,0,1,4,5,2] (sscatter (stranspose @[2,4,7,3,0,5,6,1] (sscatter (stranspose @[3,7,0,1,2,4,5,6] (w122 !$ [0])) (\\[i123, i124] -> [i123, 2 * i123 + i124]))) (\\[i125, i126, i127] -> [i125, i126, i125 * i126 + i127]))) (\\[i128, i129] -> [2 + (negate i129 + i128), i129]))) (\\[i130, i131, i132, i133, i134] -> [i130 + i131])) (sconcrete (sfromListLinear [0,3,3,3] [])))))"
      -- TODO: was once "\\dret u1 -> rfromS (sconcrete (sreplicate [3,3,3,3] 0.0))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sappend (sconcrete (sreplicate [1,3,3,3] 0.0)) (stranspose @[0,2,1] (sscatter (stranspose @[1,6,5,4,3,7,0,2] (sscatter (stranspose @[6,3,7,0,1,4,5,2] (sscatter (stranspose @[2,4,7,3,0,5,6,1] (sscatter (stranspose @[4,8,3,5,6,7,0,1,2] (soneHot (stranspose @[0,3,1,4,2] (soneHot (stranspose @[1,3,0,2] (sfromR dret) !$ [0, 0]) [1, 0, 0]) + (stranspose @[0,3,1,4,2] (soneHot (stranspose @[1,3,0,2] (sfromR dret) !$ [1, 0]) [1, 1, 0]) + stranspose @[0,2,3,4,1] (soneHot (stranspose @[3,0,1,2] (sfromR dret) !$ [1]) [1, 1]))) [0, 0, 0, 0]) !$ [0]) (\\[i123, i124] -> [i123, 2 * i123 + i124]))) (\\[i125, i126, i127] -> [i125, i126, i125 * i126 + i127]))) (\\[i128, i129] -> [2 + (negate i129 + i128), i129]))) (\\[i130, i131, i132, i133, i134] -> [i130 + i131]))))"
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
      afcnn2T = conv2dUnpadded4 blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [1,1,2,2] [7.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (sconcrete (sfromListLinear [1,1,2,2] [7.0,0.0,0.0,0.0]))"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP5b :: Assertion
testCNNOPP5b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent conv2dUnpadded4 (FTKR [5, 5, 5, 5] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) (str (ssum @1 (ssum @1 (sfromR dret)))))))) [0, 0, 0, 0])"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (sfromR dret !$ [0, 0, 0, 0]) [0, 0, 0, 0])"

maxPool2dUnpadded4
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded4 arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez4 [2, 2, 2, 2] arr [bb + 1, 2 - bb, aa * iBh, 2 * iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded4: impossible pattern needlessly required"

conv2dUnpadded4
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded4 arrA =
  let shB = [1, 1, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez4 shB arrA [iImg, 0, iBh, iBw]
      in rindex0 arrAt [0, 0, 0, 0]
    _ -> error "conv2dUnpadded4: impossible pattern needlessly required"

slicez4
  :: (ADReady target, GoodScalar r, KnownNat n)
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
      afcnn2T = maxPool2dUnpadded3 $ conv2dUnpadded3z blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (stranspose @[1,2,0] (sreplicate @2 (sappend (sreplicate @1 (let t45 = str (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sfromListLinear [2,2,2] [7.0,7.0,0.0,0.0,7.0,7.0,0.0,0.0])) (\\[i48] -> [2 * i48]))) (\\[i51] -> [2 * i51]))) (\\[i4] -> [2 * i4])), sconcrete (sreplicate [2,2,2] 0.0)])) !$ [0] in sappend (sreplicate @1 (sappend (sreplicate @1 (t45 !$ [0, 0, 0])) (sreplicate @1 (t45 !$ [1, 0, 1])))) (sreplicate @1 (t45 !$ [1, 1])))) (sconcrete (sreplicate [1,2,2] 0.0)))))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (str (sgather (sreplicate @2 (str (sreplicate @2 (sgather (sfromVector (fromList [str (sgather (str (sgather (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\[i9] -> [2 * i9, 2 * i9, 2 * i9]))) (\\[i12] -> [2 * i12])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i19, i17] -> [let i18 = ifH (notB (notB (0 <=. negate i19) &&* notB (0 <=. negate i19)) &&* (notB (notB (0 <=. negate i19) &&* notB (0 <=. negate i19)) &&* notB (notB (0 <=. negate i17) &&* notB (0 <=. negate i17)))) 0 1 in ifH (0 <=. negate i19) i18 (ifH (0 <=. negate i19) i18 1), i19, i17]))))) (\\[i1] -> [2 * i1, 0]))) (\\[i2] -> [2 * i2]))) (\\[i4] -> [2 * i4])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i26, i24, i22] -> [let i23 = ifH (notB (notB (0 <=. negate i24) &&* notB (0 <=. negate i24)) &&* notB (notB (0 <=. negate i22) &&* notB (0 <=. negate i22))) 0 1 in ifH (0 <=. negate i26) i23 (ifH (0 <=. negate i26) i23 1), i26, i24, i22]))))"

testCNNOPP6b :: Assertion
testCNNOPP6b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dUnpadded3z) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (let t58 = str (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (stranspose @[2,0,1] (sgather (stranspose @[1,2,0] (sreplicate @2 (sreplicate @2 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))))) (\\[i93] -> [2 * i93]))) (\\[i96] -> [2 * i96]))) (\\[i57] -> [2 * i57])), sconcrete (sreplicate [2,2,2] 0.0)])) !$ [0] in stranspose @[1,2,0] (sreplicate @2 (sappend (sreplicate @1 (sappend (sreplicate @1 (sappend (sreplicate @1 (t58 !$ [0, 0, 0])) (sreplicate @1 (t58 !$ [1, 0, 1])))) (sreplicate @1 (t58 !$ [1, 1])))) (sconcrete (sreplicate [1,2,2] 0.0)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let t58 = str (sfromVector (fromList [stranspose @[1,2,0] (sgather (stranspose @[2,1,0] (sgather (stranspose @[2,0,1] (sgather (stranspose @[1,2,0] (sreplicate @2 (sreplicate @2 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))))) (\\[i55] -> [2 * i55]))) (\\[i56] -> [2 * i56]))) (\\[i57] -> [2 * i57])), sconcrete (sreplicate [2,2,2] 0.0)])) !$ [0] in rfromS (stranspose @[1,2,0] (sreplicate @2 (sappend (sreplicate @1 (sappend (sreplicate @1 (sappend (sreplicate @1 (t58 !$ [0, 0, 0])) (sreplicate @1 (t58 !$ [1, 0, 1])))) (sreplicate @1 (t58 !$ [1, 1])))) (sconcrete (sreplicate [1,2,2] 0.0)))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let t60 = ssum @2 (stranspose @[2,0,1] (sfromR dret)) ; u61 = str (soneHot (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) t60)))))) [0, 0, 0] + (soneHot (ssum @1 (sslice (SNat @1) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) t60)))))) [1, 0, 1] + soneHot (ssum @1 (sslice (SNat @1) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) t60)))) [1, 1])) [0]) ; v65 = ssum @2 (ssum @2 (stranspose @[2,0,1] (sscatter (stranspose @[1,2,0] (sscatter (stranspose @[2,1,0] (sscatter (stranspose @[2,0,1] (u61 !$ [0])) (\\[i62] -> [2 * i62]))) (\\[i63] -> [2 * i63]))) (\\[i64] -> [2 * i64])))) in rfromS (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) v65)) [0, 0, 0, 0])"

  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (let t60 = ssum @2 (stranspose @[2,0,1] (sfromR dret)) in soneHot (ssum0 (stranspose @[1,2,0] (sscatter (stranspose @[1,2,0] (sscatter (stranspose @[2,1,0] (sscatter (stranspose @[1,3,0,2] (soneHot (soneHot (t60 !$ [0, 0, 0]) [0, 0, 0] + (soneHot (t60 !$ [0, 0, 1]) [1, 0, 1] + soneHot (t60 !$ [0, 1]) [1, 1])) [0]) !$ [0]) (\\[i62] -> [2 * i62]))) (\\[i63] -> [2 * i63]))) (\\[i64] -> [2 * i64])) !$ [0])) [0, 0, 0, 0])"
      -- TODO: was once "\\dret u1 -> rfromS (soneHot (ssum0 (stranspose @[0,1,3,2] (sfromR dret) !$ [0, 0, 0])) [0, 0, 0, 0])"

conv2dUnpadded3z
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded3z arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez3 shB arrA [iImg, iImg, iImg, iBw]
      in rindex0 arrAt [iBh, iBw, iImg, iBh]
    _ -> error "conv2dUnpadded3z: impossible pattern needlessly required"

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
      afcnn2T = maxPool2dUnpadded3y $ conv2dUnpadded3y blackGlyph
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (stranspose @[1,2,0] (sappend (sreplicate @1 (sgather (stranspose @[3,2,1,0] (sfromVector (fromList [stranspose @[1,2,3,0] (sgather (stranspose @[3,2,0,1] (sgather (stranspose @[2,3,0,1] (sgather (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,0.0,0.0,7.0,0.0,0.0,0.0,7.0,0.0,0.0,0.0,7.0,0.0,0.0,0.0])) (\\[i49] -> [2 * i49]))) (\\[i52, i53] -> [2 * i53, 2 * i52]))) (\\[i4] -> [2 * i4])), sconcrete (sreplicate [2,2,2,2] 0.0)])) !$ [0]) (\\[i29, i26, i22] -> [i26, i29, ifH (0 <=. negate i29) (ifH (notB (notB (0 <=. negate i26) &&* notB (0 <=. negate i26)) &&* notB (notB (0 <=. negate i22) &&* notB (0 <=. negate i22))) 0 1) (ifH (0 <=. negate i29) (ifH (notB (notB (0 <=. negate i26) &&* notB (0 <=. negate i26)) &&* notB (notB (0 <=. negate i22) &&* notB (0 <=. negate i22))) 0 1) 1), i22]))) (sconcrete (sreplicate [1,2,2,2] 0.0))))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (sgather (sfromVector (fromList [stranspose @[1,2,3,0] (sgather (stranspose @[3,2,0,1] (sgather (stranspose @[1,2,0] (sgather (sreplicate @2 (stranspose @[1,2,0] (sreplicate @2 (sgather (sfromVector (fromList [str (sgather (str (sgather (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\[i9] -> [2 * i9, 2 * i9, 2 * i9]))) (\\[i11] -> [2 * i11])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i19, i17] -> [let i18 = ifH (notB (notB (0 <=. negate i19) &&* notB (0 <=. negate i19)) &&* (notB (notB (0 <=. negate i19) &&* notB (0 <=. negate i19)) &&* notB (notB (0 <=. negate i17) &&* notB (0 <=. negate i17)))) 0 1 in ifH (0 <=. negate i19) i18 (ifH (0 <=. negate i19) i18 1), i19, i17]))))) (\\[i1] -> [2 * i1]))) (\\[i28, i3] -> [2 * i3, 2 * i28]))) (\\[i4] -> [2 * i4])), sconcrete (sreplicate [2,2,2,2] 0.0)])) (\\[i29, i26, i24, i22] -> [let i23 = ifH (notB (notB (0 <=. negate i29) &&* notB (0 <=. negate i29)) &&* (notB (notB (0 <=. negate i26) &&* notB (0 <=. negate i26)) &&* notB (notB (0 <=. negate i22) &&* notB (0 <=. negate i22)))) 0 1 in ifH (0 <=. negate i24) i23 (ifH (0 <=. negate i24) i23 1), i29, i26, i24, i22]))"

testCNNOPP7b :: Assertion
testCNNOPP7b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3y . conv2dUnpadded3y) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1,2,0] (sappend (sreplicate @1 (sgather (stranspose @[3,2,1,0] (sfromVector (fromList [stranspose @[1,2,3,0] (sgather (stranspose @[3,2,0,1] (sgather (stranspose @[2,3,0,1] (sgather (sreplicate @2 (sreplicate @2 (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0))))) (\\[i119] -> [2 * i119]))) (\\[i122, i123] -> [2 * i123, 2 * i122]))) (\\[i62] -> [2 * i62])), sconcrete (sreplicate [2,2,2,2] 0.0)])) !$ [0]) (\\[i63, i64, i65] -> [i64, i63, ifH (0 <=. negate i63) (ifH (notB (notB (0 <=. negate i64) &&* notB (0 <=. negate i64)) &&* notB (notB (0 <=. negate i65) &&* notB (0 <=. negate i65))) 0 1) (ifH (0 <=. negate i63) (ifH (notB (notB (0 <=. negate i64) &&* notB (0 <=. negate i64)) &&* notB (notB (0 <=. negate i65) &&* notB (0 <=. negate i65))) 0 1) 1), i65]))) (sconcrete (sreplicate [1,2,2,2] 0.0))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (stranspose @[1,2,0] (sappend (sreplicate @1 (sgather (stranspose @[3,2,1,0] (sfromVector (fromList [stranspose @[1,2,3,0] (sgather (stranspose @[3,2,0,1] (sgather (stranspose @[2,3,0,1] (sgather (sreplicate @2 (sreplicate @2 (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0))))) (\\[i59] -> [2 * i59]))) (\\[i60, i61] -> [2 * i61, 2 * i60]))) (\\[i62] -> [2 * i62])), sconcrete (sreplicate [2,2,2,2] 0.0)])) !$ [0]) (\\[i63, i64, i65] -> [i64, i63, ifH (0 <=. negate i63) (ifH (notB (notB (0 <=. negate i64) &&* notB (0 <=. negate i64)) &&* notB (notB (0 <=. negate i65) &&* notB (0 <=. negate i65))) 0 1) (ifH (0 <=. negate i63) (ifH (notB (notB (0 <=. negate i64) &&* notB (0 <=. negate i64)) &&* notB (notB (0 <=. negate i65) &&* notB (0 <=. negate i65))) 0 1) 1), i65]))) (sconcrete (sreplicate [1,2,2,2] 0.0))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w70 = stranspose @[3,2,1,0] (soneHot (sscatter (ssum @1 (sslice (SNat @0) (SNat @1) (stranspose @[2,0,1] (sfromR dret)))) (\\[i67, i68, i69] -> [i68, i67, ifH (0 <=. negate i67) (ifH (notB (notB (0 <=. negate i68) &&* notB (0 <=. negate i68)) &&* notB (notB (0 <=. negate i69) &&* notB (0 <=. negate i69))) 0 1) (ifH (0 <=. negate i67) (ifH (notB (notB (0 <=. negate i68) &&* notB (0 <=. negate i68)) &&* notB (notB (0 <=. negate i69) &&* notB (0 <=. negate i69))) 0 1) 1), i69])) [0]) ; m75 = ssum @2 (ssum @2 (sscatter (stranspose @[2,3,0,1] (sscatter (stranspose @[2,3,1,0] (sscatter (stranspose @[3,0,1,2] (w70 !$ [0])) (\\[i71] -> [2 * i71]))) (\\[i72, i73] -> [2 * i73, 2 * i72]))) (\\[i74] -> [2 * i74]))) in rfromS (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) m75)))) [0, 0, 0, 0])"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (ssum0 (stranspose @[2,3,0,1] (sscatter (stranspose @[2,3,0,1] (sscatter (stranspose @[2,3,1,0] (sscatter (stranspose @[3,4,2,1,0] (soneHot (sscatter (stranspose @[2,0,1] (sfromR dret) !$ [0]) (\\[i67, i68, i69] -> [i68, i67, ifH (0 <=. negate i67) (ifH (notB (notB (0 <=. negate i68) &&* notB (0 <=. negate i68)) &&* notB (notB (0 <=. negate i69) &&* notB (0 <=. negate i69))) 0 1) (ifH (0 <=. negate i67) (ifH (notB (notB (0 <=. negate i68) &&* notB (0 <=. negate i68)) &&* notB (notB (0 <=. negate i69) &&* notB (0 <=. negate i69))) 0 1) 1), i69])) [0]) !$ [0]) (\\[i71] -> [2 * i71]))) (\\[i72, i73] -> [2 * i73, 2 * i72]))) (\\[i74] -> [2 * i74])) !$ [0, 0])) [0, 0, 0, 0])"
      -- TODO: was once "\\dret u1 -> rfromS (soneHot (sfromR dret !$ [0, 0, 0, 0]) [0, 0, 0, 0])"

maxPool2dUnpadded3y
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded3y arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez3 [2, 2, 2, 2] arr [iBh, aa, bb, iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded3y: impossible pattern needlessly required"

conv2dUnpadded3y
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded3y arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez3 shB arrA [iImg, iImg, iImg, iBh]
      in rindex0 arrAt [iBh, iBw, iImg, iBh]
    _ -> error "conv2dUnpadded3y: impossible pattern needlessly required"

-- This test uses a disastrous version of smaximum, but shows how
-- smaxIndex gets non-trivially vectorized, preserving sharing, too.
testCNNOPP4bU :: Assertion
testCNNOPP4bU = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpaddedS4 @4 @2) (FTKS (SNat @31 :$$ SNat @31 :$$ SNat @31 :$$ SNat @31 :$$ ZSS) (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> let w52 = sgather (stranspose @[4,2,3,0,1] (sgather (stranspose @[2,0,1] u1) (\\[i99, i100] -> [2 * i99 + i100]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (sreshape @[31,31,15,15,16] (stranspose @[2,3,4,0,5,1] w52)) in sgather w52 (\\[i54, i55, i56, i57] -> [i57, remH (kfromS (u53 !$ [i54, i55, i56, i57])) 4, i54, i55, i56, remH (quotH (kfromS (u53 !$ [i54, i55, i56, i57])) 4) 4])"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w52 = sgather (stranspose @[4,2,3,0,1] (sgather (stranspose @[2,0,1] u1) (\\[i48, i49] -> [2 * i48 + i49]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (sreshape @[31,31,15,15,16] (stranspose @[2,3,4,0,5,1] w52)) in sgather w52 (\\[i54, i55, i56, i57] -> [i57, remH (kfromS (u53 !$ [i54, i55, i56, i57])) 4, i54, i55, i56, remH (quotH (kfromS (u53 !$ [i54, i55, i56, i57])) 4) 4])"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w52 = sgather (stranspose @[4,2,3,0,1] (sgather (stranspose @[2,0,1] u1) (\\[i48, i49] -> [2 * i48 + i49]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (sreshape @[31,31,15,15,16] (stranspose @[2,3,4,0,5,1] w52)) in stranspose @[1,2,0] (sscatter (stranspose @[3,4,1,2,0] (sscatter (sscatter dret (\\[i59, i60, i61, i62] -> [i62, remH (kfromS (u53 !$ [i59, i60, i61, i62])) 4, i59, i60, i61, remH (quotH (kfromS (u53 !$ [i59, i60, i61, i62])) 4) 4])) (\\[i63, i64] -> [2 * i63 + i64]))) (\\[i65, i66] -> [2 * i65 + i66]))"
-- TODO: different test result with GHC 9.10:   printArtifactPretty (simplifyArtifact artifactRev)
--    @?= "\\dret u1 -> let u53 = smaxIndex (sreshape @[31,31,15,15,16] (stranspose @[2,3,4,0,5,1] (sgather (stranspose @[4,2,3,0,1] (sgather (stranspose @[2,0,1] u1) (\\[i82, i83] -> [2 * i82 + i83]))) (\\[i50, i51] -> [2 * i50 + i51])))) in stranspose @[1,2,0] (sscatter (stranspose @[3,4,1,2,0] (sscatter (sscatter dret (\\[i59, i60, i61, i62] -> [i62, remH (kfromS (u53 !$ [i59, i60, i61, i62])) 4, i59, i60, i61, remH (quotH (kfromS (u53 !$ [i59, i60, i61, i62])) 4) 4])) (\\[i63, i64] -> [2 * i63 + i64]))) (\\[i65, i66] -> [2 * i65 + i66]))"

smaximum4 :: forall r sh target. (ADReady target, GoodScalar r, KnownShS sh)
          => target (TKS sh r) -> target (TKS '[] r)
smaximum4 t0 =
  tlet t0 $ \t ->
  ttletPrimal (tprimalPart $ kfromS $ smaxIndex (sflatten t)) $ \maxIndex ->
    sindex0 t
    $ fromLinearIdxS (tprimalPart @target . kconcrete . fromIntegral)
                     (sshape t)
                     maxIndex

maxPool2dUnpaddedS4
  :: forall ksize stride batch_size channels h w target r shOut shK1.
     ( KnownNat ksize, KnownNat stride, KnownNat batch_size, KnownNat channels
     , KnownNat h, KnownNat w
     , 1 <= stride  -- wrongly reported as redundant due to plugins
     , ADReady target, GoodScalar r
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
