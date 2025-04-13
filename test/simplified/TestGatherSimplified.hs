{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
-- | Tests of the gather and scatter operations and of operations that expand
-- to gather and of fusion of all of them.
module TestGatherSimplified (testTrees) where

import Prelude

import Data.Int (Int64)
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (resetVarCounter)
import HordeAd.Core.AstInterpret
import HordeAd.Core.CarriersAst

import CrossTesting

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
  , testCase "sminimizedCNNOPP3" testCNNOPP3
  , testCase "sminimizedCNNOPP3b" testCNNOPP3b
  , testCase "sminimizedCNNOPP4" testCNNOPP4
  , testCase "sminimizedCNNOPP4b" testCNNOPP4b
  , testCase "sminimizedCNNOPP5" testCNNOPP5
  , testCase "sminimizedCNNOPP5b" testCNNOPP5b
  , testCase "sminimizedCNNOPP6" testCNNOPP6
  , testCase "sminimizedCNNOPP6b" testCNNOPP6b
  , testCase "sminimizedCNNOPP7" testCNNOPP7
  , testCase "sminimizedCNNOPP7b" testCNNOPP7b
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
  length (show t1) @?= 259
  resetVarCounter
  let !t2 = gather1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 259
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
  length (show t1) @?= 314
  resetVarCounter
  let !t2 = gather2 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 338
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t1)) @?= 314
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 338

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
  length (show t1) @?= 285
  resetVarCounter
  let !t2 = gather12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 285
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 285
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 285

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
  length (show t1) @?= 103
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 103
  resetVarCounter
  let !t2 = rreshape @2 @2 [2, 6]
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 103
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 103

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
  length (show t1) @?= 394
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 400
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 394
  length (show (simplifyInlineContract @(TKR 3 Float) @PrimalSpan t2)) @?= 400

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
  length (show t1) @?= 2473
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 2199
  resetVarCounter
  let !t2 = (\t -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                            (rreshape @10 [8, 16] t))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 1609
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 1335

testGatherSimpPP34 :: Assertion
testGatherSimpPP34 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
             gatherTranspose33 @(AstTensor AstMethodLet PrimalSpan) (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 3877
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 4970
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              (\t' -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                               (rreshape @10 [8, 16] t'))
                (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 2958
  length (show (simplifyInlineContract @(TKR 3 Float) @PrimalSpan t2)) @?= 3919

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
  length (show t1) @?= 341
  resetVarCounter
  let !t2 = scatter1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 436
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t1)) @?= 341
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t2)) @?= 436

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
  length (show t1) @?= 966
  resetVarCounter
  let !t2 = scatter2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 726
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 966
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 726

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
  length (show t1) @?= 896
  resetVarCounter
  let !t2 = scatter12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 569
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 896
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 569

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
  assertEqualUpToEpsilonShort 1e-10
    (ringestData [1,2,2,1,2,2,2,2,2,1] [2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885034988157713e-4,2.885923176600045e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.8851415976532735e-4,2.885923176600045e-4,2.887454843457817e-4,2.8849246223035154e-4,2.884182085399516e-4,2.884075468755327e-4,2.8842176240868867e-4,2.8840399312321096e-4,0.0,2.887454843457817e-4,2.886097295122454e-4,2.887454843457817e-4,2.88599069218435e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.885145151321922e-4,2.8854294397024206e-4,2.8858878438222746e-4,2.885923176600045e-4,0.0,2.884007943794131e-4,0.0,2.884469945274759e-4,2.8843242392031246e-4,2.884288700806792e-4,0.0,2.885034988157713e-4,2.884110805753153e-4,0.0,2.8849283778617973e-4,2.884075468755327e-4,2.884075468755327e-4,2.884075468755327e-4,2.884075468755327e-4,0.0,0.0,0.0,0.0,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,0.0,0.0,0.0,0.0,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.8854294397024206e-4,2.884288700806792e-4,2.884395315486472e-4,0.0,2.8849246223035154e-4,2.8850276789489724e-4,0.0,2.8849212704517413e-4,2.8854294397024206e-4,2.884288700806792e-4,2.884395315486472e-4,0.0,2.8849246223035154e-4,2.8850276789489724e-4,0.0,2.8849212704517413e-4,2.8842922547482884e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.894378297730782e-4,2.885923176600045e-4,2.887454843457817e-4,2.88599069218435e-4,2.887454843457817e-4,2.887056688523444e-4,2.887454843457817e-4,2.887056688523444e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.884786229769816e-4,2.885923176600045e-4,2.887454843457817e-4,2.886950092188272e-4,2.887454843457817e-4,2.884818011261814e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.887167039107226e-4,2.885923176600045e-4,2.887454843457817e-4,2.8860262265516213e-4,2.887454843457817e-4,2.885884088500461e-4,2.887454843457817e-4,2.88599069218435e-4])
    (rev' @Double @10 barRelu10xSlower
          (rmap0N (* rscalar 0.001) t128))

testReluSimpPP :: Assertion
testReluSimpPP = do
  resetVarCounter
  let !t1 = barRelu10xSlower @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 17830
  length (show (simplifyInlineContract @(TKR 10 Float) t1)) @?= 23196
  resetVarCounter
  let !t2 = barRelu @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 17830
  length (show (simplifyInlineContract @(TKR 10 Float) t2)) @?= 23196

testCNNOPP2 :: Assertion
testCNNOPP2 = do
  resetVarCounter
  let t = maxPool2dUnpadded2
            (rconcrete $ Nested.rreplicateScal (1 :$: 1 :$: 2 :$: 2 :$: ZSR) 1)
  printAstPretty t
    @?= "rfromS (sreplicate @2 (sreplicate @2 (let w42 = stranspose @[1,2,3,0] (sreplicate @1 (sgather (sfromVector (fromList [let w30 = sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (stranspose @[1,2,0] (sappend (sgather (sappend (sconcrete (sfromListLinear [1,1,2,2] [1.0,1.0,1.0,1.0])) (sconcrete (sfromListLinear [2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) (\\[i12, i28, i26] -> [i28, i12, i26 + i12, i12])) (str (sreplicate @3 (str (sreplicate @2 (sconcrete (sfromListLinear [1] [0.0])))))))))))) in sgather (sfromVector (fromList [sgather w30 (\\[i53, i47, i41, i37, i32] -> [i53, i47, i41, i37, i32, 1, 2 * i53 + i37, 2 * i47 + i32]), sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i52, i46, i40] -> [ifH (1 <=. i46 + i40) 0 1, i52, i46, i40]), sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i50, i44, i38] -> [ifH (1 <=. i44 + i38) 0 1, i50, i44, i38]))) in sgather w42 (\\[i49, i43] -> [i49, i43, 0, 0, 0, 0]))))"
  printAstPretty (simplifyInlineContract t)
    @?= "rfromS (sreplicate @2 (sreplicate @2 (str (sappend (sconcrete (sfromListLinear [1,2] [0.0,0.0])) (sreplicate @1 (stranspose @[1,2,3,0] (stranspose @[0,2,1] (sgather (stranspose @[0,2,3,1] (sfromVector (fromList [sgather (str (sappend (stranspose @[0,2,1] (sgather (sconcrete (sfromListLinear [1,2,2,3] [1.0,0.0,0.0,1.0,0.0,0.0,1.0,0.0,0.0,1.0,0.0,0.0])) (\\[i12, i26] -> [i12, i26 + i12, i12]))) (sconcrete (sfromListLinear [1,3,2] [0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [1]) (\\[i53, i47, i61, i37, i32] -> [2 * i47 + i32, 2 * i53 + i37]), sconcrete (sfromListLinear [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]))) (\\[i46, i40] -> [ifH (1 <=. i46 + i40) 0 1, i46, i40])) !$ [1]) !$ [0, 0, 0]))))))"

testCNNOPP2b :: Assertion
testCNNOPP2b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded2 (FTKR [1, 1, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w58 = sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (stranspose @[1,2,0] (sappend (sgather (sappend (sfromR u1) (sconcrete (sfromListLinear [2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) (\\[i55, i56, i57] -> [i56, i55, i57 + i55, i55])) (str (sreplicate @3 (str (sreplicate @2 (sconcrete (sfromListLinear [1] [0.0])))))))))))) ; w70 = stranspose @[1,2,3,0] (sreplicate @1 (sgather (sfromVector (fromList [sgather (sfromVector (fromList [sgather w58 (\\[i59, i60, i61, i62, i63] -> [i59, i60, i61, i62, i63, 1, 2 * i59 + i62, 2 * i60 + i63]), sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i64, i65, i66] -> [ifH (1 <=. i65 + i66) 0 1, i64, i65, i66]), sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i67, i68, i69] -> [ifH (1 <=. i68 + i69) 0 1, i67, i68, i69]))) in rfromS (sreplicate @2 (sreplicate @2 (sgather w70 (\\[i71, i72] -> [i71, i72, 0, 0, 0, 0]))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sreplicate @2 (sreplicate @2 (str (sappend (sconcrete (sfromListLinear [1,2] [0.0,0.0])) (sreplicate @1 (stranspose @[1,2,3,0] (stranspose @[0,2,1] (sgather (stranspose @[0,2,3,1] (sfromVector (fromList [sgather (str (sappend (stranspose @[0,2,1] (sgather (stranspose @[1,2,3,0] (sappend (sfromR u1) (sconcrete (sfromListLinear [2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) (\\[i55, i57] -> [i55, i57 + i55, i55]))) (sconcrete (sfromListLinear [1,3,2] [0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [1]) (\\[i59, i60, i108, i62, i63] -> [2 * i60 + i63, 2 * i59 + i62]), sconcrete (sfromListLinear [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]))) (\\[i65, i66] -> [ifH (1 <=. i65 + i66) 0 1, i65, i66])) !$ [1]) !$ [0, 0, 0]))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w79 = sscatter (ssum @1 (stranspose @[3,0,1,2] (sscatter (ssum @2 (ssum @2 (sfromR dret))) (\\[i74, i75] -> [i74, i75, 0, 0, 0, 0])))) (\\[i76, i77, i78] -> [ifH (1 <=. i77 + i78) 0 1, i76, i77, i78]) ; w83 = sscatter (w79 !$ [0]) (\\[i80, i81, i82] -> [ifH (1 <=. i81 + i82) 0 1, i80, i81, i82]) ; t89 = stranspose @[2,0,1] (ssum @2 (ssum @2 (ssum @1 (ssum @2 (ssum @2 (sscatter (w83 !$ [0]) (\\[i84, i85, i86, i87, i88] -> [i84, i85, i86, i87, i88, 1, 2 * i84 + i87, 2 * i85 + i88]))))))) ; u93 = sscatter (sslice (SNat @0) (SNat @1) t89) (\\[i90, i91, i92] -> [i91, i90, i92 + i90, i90]) in rfromS (sslice (SNat @0) (SNat @1) u93)"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sreplicate @1 (sscatter (sreplicate @1 (ssum @2 (ssum @2 (ssum @2 (ssum @2 (stranspose @[5,4,3,2,1,0] (stranspose @[6,5,4,3,2,1,0] (sscatter (sscatter (sscatter (sscatter (ssum @2 (ssum @2 (sfromR dret))) (\\[i74, i75] -> [i74, i75, 0, 0, 0])) (\\[i76, i77, i78] -> [ifH (1 <=. i77 + i78) 0 1, i76, i77, i78]) !$ [0]) (\\[i80, i81, i82] -> [ifH (1 <=. i81 + i82) 0 1, i80, i81, i82]) !$ [0]) (\\[i84, i85, i86, i87, i88] -> [i86, i84, i85, i87, i88, 1, 2 * i84 + i87, 2 * i85 + i88]) !$ [0]) !$ [0]))))))) (\\[i90, i91, i92] -> [i91, i90, i92 + i90, i90]) !$ [0]))"

maxPool2dUnpadded2
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded2 a =
  rbuild [2, 2, 2, 2] $ \case
    [_, _, iBh, iBw] ->
      let arrt = slicez2 (conv2dUnpadded2 a) [iBw, 1, 2 * iBh, 2 * iBw]
      in rmaximum2 arrt
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"

conv2dUnpadded2
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded2 a =
  rbuild [3, 3, 2, 2] $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez2 a [iImg, 0, iBh, iBw]
      in rindex0 arrAt [0, iBw, iBw, 0]
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

slicez2
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double, n ~ 4)
  => target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez2 d ixBase =
  rbuild [1, 1, 2, 2] $ \ixResult -> indexz02 d (zipWith_Index (+) ixBase ixResult)

indexz02
  :: forall target r n.
     (target ~ AstTensor AstMethodLet FullSpan, r ~ Double, n ~ 4)
  => target (TKR n r) -> IxROf target n -> target (TKR 0 r)
indexz02 d ix = ifH (1 ==. (toList ix !! 0)) (d ! ix) (rscalar 0)

rmaximum2 :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
         => target (TKR 4 r) -> target (TKR 0 r)
rmaximum2 t0 = tlet t0 $ \t -> rindex0 t [0, 0, 0, 0]

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
  printAstPretty afcnn2T
    @?= "rfromS (let w59 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (let w98 = str (sreplicate @2 (sfromVector (fromList [(let w30 = sreplicate @2 (sreplicate @2 (let m41 = sgather (sappend (sconcrete (sfromListLinear [1,2] [0.0,0.0])) (sreplicate @1 (sreplicate @2 (sscalar 0.0)))) (\\[i58, i12] -> [i12, i58]) ; m42 = sappend (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i57, i12] -> [ifH (notB (0 <=. negate i12 + negate i57) &&* notB (1 <=. i12 + i57 &&* (-1) <=. negate i12 + negate i57)) 1 0])) (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i57, i12] -> [ifH (0 <=. negate i12 + negate i57) 0 1])) in str (sappend (sreplicate @1 m42) (sreplicate @1 m41)))) ; w31 = sreplicate @2 (sreplicate @2 (let m38 = sreplicate @2 (sappend (sreplicate @1 (sscalar 0.0)) (sconcrete (sfromListLinear [1] [0.0]))) ; m39 = sappend (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i54, i12] -> [ifH (notB (0 <=. negate i12 + negate i54) &&* notB (1 <=. i12 + i54 &&* (-1) <=. negate i12 + negate i54)) 1 0])) (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i54, i12] -> [ifH (0 <=. negate i12 + negate i54) 0 1])) in str (sappend (sreplicate @1 m39) (sreplicate @1 m38)))) in sgather (sappend (sreplicate @1 (sgather w31 (\\[i94, i78, i51, i36] -> [i94, i78, i51, i36, 0]))) (sreplicate @1 (sgather w30 (\\[i93, i77, i50, i36] -> [i93, i77, i50, i36, 1])))) (\\[i92, i72, i4] -> [2 * i4, i92, i72, 2 * quotH i72 2, 2 * i92])) + (let u33 = sreplicate @2 (sreplicate @2 (sreplicate @2 (sappend (sreplicate @1 (sscalar 0.0)) (sconcrete (sfromListLinear [1] [0.0]))))) ; u34 = sreplicate @2 (sreplicate @2 (sappend (sreplicate @1 (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i12] -> [ifH (0 <=. negate i12 + negate i12) 0 1]))) (sreplicate @1 (sreplicate @2 (sscalar 0.0))))) ; t88 = sgather u33 (\\[i85, i68, i4] -> [i85, i68, 2 * quotH i68 2, 2 * i4]) ; t89 = sgather u34 (\\[i86, i69, i4] -> [i86, i69, 2 * quotH i69 2, 2 * i4]) in sappend (sreplicate @1 (t89 !$ [0])) (sreplicate @1 (t88 !$ [1]))), sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))]))) in sappend (str (sappend (stranspose @[1,2,3,0] (sappend (sgather (w98 !$ [0]) (\\[i61, i81, i97, i64] -> [i97, i81, i64, i61])) (sreplicate @1 (sgather (stranspose @[3,2,1,0] (w98 !$ [1]) !$ [1]) (\\[i81, i97, i64] -> [i64, i81, i97]))))) (sreplicate @1 (sreplicate @1 (w98 !$ [1, 0, 1]))))) (sreplicate @1 (w98 !$ [1, 1])))))))))) in sgather w59 (\\[i96, i80, i63, i60] -> [i96, i80, i63, i60, 0, 0, 0, 0]))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (let w98 = str (sreplicate @2 (sfromVector (fromList [sgather (sappend (sreplicate @1 (sreplicate @2 (sreplicate @2 (stranspose @[2,1,0] (sappend (sreplicate @1 (sappend (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i54, i12] -> [ifH (notB (0 <=. negate i12 + negate i54) &&* notB (1 <=. i12 + i54 &&* (-1) <=. negate i12 + negate i54)) 1 0])) (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i54, i12] -> [ifH (0 <=. negate i12 + negate i54) 0 1])))) (sconcrete (sfromListLinear [1,2,2] [0.0,0.0,0.0,0.0]))) !$ [0])))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (stranspose @[2,1,0] (sappend (sreplicate @1 (sappend (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i57, i12] -> [ifH (notB (0 <=. negate i12 + negate i57) &&* notB (1 <=. i12 + i57 &&* (-1) <=. negate i12 + negate i57)) 1 0])) (sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i57, i12] -> [ifH (0 <=. negate i12 + negate i57) 0 1])))) (sconcrete (sfromListLinear [1,2,2] [0.0,0.0,0.0,0.0]))) !$ [1]))))) (\\[i92, i72, i4] -> [2 * i4, i92, i72, 2 * quotH i72 2, 2 * i92]) + sappend (sreplicate @1 (sgather (sconcrete (sfromListLinear [2,2] [7.0,0.0,0.0,0.0])) (\\[i116, i117] -> [2 * quotH i116 2, 2 * i117]))) (sreplicate @1 (sreplicate @2 (sgather (sconcrete (sfromListLinear [2] [0.0,0.0])) (\\[i114] -> [2 * i114])))), sconcrete (sfromListLinear [2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]))) in sappend (str (sappend (stranspose @[1,2,3,0] (sappend (stranspose @[0,2,3,1] (sreplicate @1 (stranspose @[2,0,1] (sreplicate @1 (sreplicate @1 (str (w98 !$ [0, 0, 0]) !$ [0])))))) (sreplicate @1 (sreplicate @1 (sreplicate @1 (str (w98 !$ [1, 0, 0]) !$ [1])))))) (sreplicate @1 (sreplicate @1 (w98 !$ [1, 0, 1]))))) (sreplicate @1 (w98 !$ [1, 1])))"

testCNNOPP3b :: Assertion
testCNNOPP3b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dUnpadded3) (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w174 = sreplicate @2 (sreplicate @2 (str (sreplicate @2 (stranspose @[1,2,3,4,5,0] (sslice (SNat @1) (SNat @2) (stranspose @[5,0,1,2,3,4] (sgather (sslice (SNat @0) (SNat @2) (stranspose @[2,0,1] (sgather (sfromR u1) (\\[i167, i168] -> [i167 + i168])))) (\\[i169, i170, i171, i172, i173] -> [i172, i169, i171, i170 + i173])))))))) ; w180 = sgather w174 (\\[i175, i176, i177, i178, i179] -> [i175, i176, i177, i178, i179, 0, 1, i177, i178]) ; w191 = stranspose @[1,2,0] (sappend (sgather (sfromVector (fromList [w180, sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i181, i182, i183, i184, i185] -> [ifH (notB (0 <=. negate i185 + negate i181) &&* notB (1 <=. i185 + i181)) 1 0, i182, i183, i181, i184, i185])) (sgather (sfromVector (fromList [w180, sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i186, i187, i188, i189, i190] -> [ifH (0 <=. negate i190 + negate i186) 0 1, i187, i188, 1, i189, i190]))) ; w195 = stranspose @[1,2,3,0] (sappend (sreplicate @1 (sgather w191 (\\[i192, i193, i194] -> [i192, i193, i194, 0]))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))) ; w201 = sgather w174 (\\[i196, i197, i198, i199, i200] -> [i196, i197, i198, i199, i200, 0, i200, i198, i199]) ; w212 = stranspose @[1,2,0] (sappend (sgather (sfromVector (fromList [w201, sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i202, i203, i204, i205, i206] -> [ifH (notB (0 <=. negate i206 + negate i202) &&* notB (1 <=. i206 + i202)) 1 0, i203, i204, i202, i205, i206])) (sgather (sfromVector (fromList [w201, sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i207, i208, i209, i210, i211] -> [ifH (0 <=. negate i211 + negate i207) 0 1, i208, i209, 1, i210, i211]))) ; w216 = stranspose @[1,2,3,0] (sappend (sreplicate @1 (sgather w212 (\\[i213, i214, i215] -> [i213, i214, i215, 0]))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))) ; w235 = sreplicate @2 (sreplicate @2 (str (sreplicate @2 (stranspose @[1,2,3,4,5,0] (sslice (SNat @1) (SNat @2) (stranspose @[5,0,1,2,3,4] (sgather (sslice (SNat @0) (SNat @2) (stranspose @[2,0,1] (sgather (sfromR u1) (\\[i228, i229] -> [i228 + i229])))) (\\[i230, i231, i232, i233, i234] -> [i233, i230, i232, i231 + i234])))))))) ; w240 = stranspose @[1,2,3,4,0] (sappend (sreplicate @1 (sgather w235 (\\[i236, i237, i238, i239] -> [i236, i237, i238, i239, 0, i238, 1, 1, i239]))) (str (sreplicate @2 (str (sreplicate @2 (str (sreplicate @2 (str (sreplicate @2 (sconcrete (sfromListLinear [1] [0.0]))))))))))) ; w246 = stranspose @[1,2,0] (sappend (stranspose @[3,1,2,4,0] (sappend (sgather w240 (\\[i241, i242, i243, i244, i245] -> [i242, i243, i244, i245, i241])) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sscalar 0.0)))))))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))) ; t250 = sgather w246 (\\[i247, i248, i249] -> [i247, i248, 2 * quotH i248 2, 0, 2 * i249]) ; w251 = str (sreplicate @2 (sfromVector (fromList [sgather (sappend (sreplicate @1 (sgather w216 (\\[i217, i218, i219, i220] -> [i217, i218, i219, i220, 0]))) (sreplicate @1 (sgather w195 (\\[i221, i222, i223, i224] -> [i221, i222, i223, i224, 1])))) (\\[i225, i226, i227] -> [2 * i227, i225, i226, 2 * quotH i226 2, 2 * i225]) + sappend (sreplicate @1 (t250 !$ [0])) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))), sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))]))) ; w259 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (sappend (str (sappend (stranspose @[1,2,3,0] (sappend (sgather (w251 !$ [0]) (\\[i252, i253, i254, i255] -> [i254, i253, i255, i252])) (sreplicate @1 (sgather (stranspose @[3,2,1,0] (w251 !$ [1]) !$ [1]) (\\[i256, i257, i258] -> [i258, i256, i257]))))) (sreplicate @1 (sreplicate @1 (w251 !$ [1, 0, 1]))))) (sreplicate @1 (w251 !$ [1, 1])))))))))) in rfromS (sgather w259 (\\[i260, i261, i262, i263] -> [i260, i261, i262, i263, 0, 0, 0, 0]))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (let w174 = sreplicate @2 (sreplicate @2 (str (sreplicate @2 (stranspose @[1,2,3,4,5,0] (sslice (SNat @1) (SNat @2) (stranspose @[5,3,0,2,4,1] (sgather (stranspose @[3,2,1,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,0,1] (sgather (sfromR u1) (\\[i167, i168] -> [i167 + i168]))))) (\\[i170, i173] -> [i170 + i173])))))))) ; w180 = stranspose @[4,3,0,1,2] (sgather (stranspose @[2,1,0] (stranspose @[5,2,3,6,7,8,4,1,0] w174 !$ [0]) !$ [1]) (\\[i177, i178] -> [i178, i177, i177, i178])) ; w201 = stranspose @[4,3,0,1,2] (sgather (stranspose @[5,4,3,2,6,7,8,1,0] w174 !$ [0]) (\\[i198, i199, i200] -> [i200, i199, i198, i200, i198, i199])) ; w251 = str (sreplicate @2 (sfromVector (fromList [sgather (sappend (sreplicate @1 (stranspose @[2,1,0] (stranspose @[4,3,2,1,0] (sappend (sreplicate @1 (str (stranspose @[3,2,1,0] (sappend (stranspose @[0,4,3,2,1] (sgather (stranspose @[0,2,3,1] (sreplicate @1 (stranspose @[1,4,2,0,3] (stranspose @[3,2,4,5,1,0] (sfromVector (fromList [w201, sconcrete (sfromListLinear [2,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])])) !$ [0])))) (\\[i202, i206] -> [i202, ifH (notB (0 <=. negate i206 + negate i202) &&* notB (1 <=. i206 + i202)) 1 0, i206]))) (stranspose @[0,4,3,2,1] (sgather (stranspose @[0,2,1] (stranspose @[3,0,4,5,2,1] (sfromVector (fromList [w201, sconcrete (sfromListLinear [2,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])])) !$ [1])) (\\[i207, i211] -> [ifH (0 <=. negate i211 + negate i207) 0 1, i211])))) !$ [0]))) (sconcrete (sfromListLinear [1,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [0]))) (sreplicate @1 (stranspose @[2,1,0] (stranspose @[4,3,2,1,0] (sappend (sreplicate @1 (str (stranspose @[3,2,1,0] (sappend (stranspose @[0,4,3,2,1] (sgather (stranspose @[0,2,3,1] (sreplicate @1 (stranspose @[1,4,2,0,3] (stranspose @[3,2,4,5,1,0] (sfromVector (fromList [w180, sconcrete (sfromListLinear [2,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])])) !$ [0])))) (\\[i181, i185] -> [i181, ifH (notB (0 <=. negate i185 + negate i181) &&* notB (1 <=. i185 + i181)) 1 0, i185]))) (stranspose @[0,4,3,2,1] (sgather (stranspose @[0,2,1] (stranspose @[3,0,4,5,2,1] (sfromVector (fromList [w180, sconcrete (sfromListLinear [2,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])])) !$ [1])) (\\[i186, i190] -> [ifH (0 <=. negate i190 + negate i186) 0 1, i190])))) !$ [0]))) (sconcrete (sfromListLinear [1,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [1])))) (\\[i225, i226, i227] -> [2 * i227, i225, i226, 2 * quotH i226 2, 2 * i225]) + sappend (sreplicate @1 (sgather (stranspose @[2,1,0] (str (sappend (stranspose @[3,1,2,4,0] (sappend (stranspose @[0,4,3,2,1] (sreplicate @1 (stranspose @[3,0,1,2] (sreplicate @1 (sreplicate @2 (sreplicate @2 (stranspose @[1,2,3,4,5,0] (sslice (SNat @1) (SNat @2) (stranspose @[5,3,0,2,4,1] (sgather (stranspose @[3,2,1,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,0,1] (sgather (sfromR u1) (\\[i228, i229] -> [i228 + i229]))))) (\\[i231, i234] -> [i231 + i234])))) !$ [0, 0, 0, 1, 1]))))))) (sconcrete (sfromListLinear [1,2,2,1,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) (sconcrete (sfromListLinear [1,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [0]) !$ [0]) (\\[i248, i249] -> [i248, 2 * quotH i248 2, 2 * i249]))) (sconcrete (sfromListLinear [1,2,2] [0.0,0.0,0.0,0.0])), sconcrete (sfromListLinear [2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]))) in sappend (str (sappend (stranspose @[1,2,3,0] (sappend (stranspose @[0,2,3,1] (sreplicate @1 (stranspose @[2,0,1] (sreplicate @1 (sreplicate @1 (str (w251 !$ [0, 0, 0]) !$ [0])))))) (sreplicate @1 (sreplicate @1 (sreplicate @1 (str (w251 !$ [1, 0, 0]) !$ [1])))))) (sreplicate @1 (sreplicate @1 (w251 !$ [1, 0, 1]))))) (sreplicate @1 (w251 !$ [1, 1])))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let u269 = ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (sscatter (sfromR dret) (\\[i265, i266, i267, i268] -> [i265, i266, i267, i268, 0, 0, 0, 0]))))))))) ; u270 = str (sslice (SNat @0) (SNat @1) u269) ; u271 = stranspose @[3,0,1,2] (sslice (SNat @0) (SNat @1) u270) ; u279 = ssum @2 (str (soneHot (sscatter (sslice (SNat @0) (SNat @1) u271) (\\[i275, i276, i277, i278] -> [i277, i276, i278, i275])) [0] + (soneHot (stranspose @[3,2,1,0] (soneHot (sscatter (ssum @1 (sslice (SNat @1) (SNat @1) u271)) (\\[i272, i273, i274] -> [i274, i272, i273])) [1])) [1] + (soneHot (ssum @1 (ssum @1 (sslice (SNat @1) (SNat @1) u270))) [1, 0, 1] + soneHot (ssum @1 (sslice (SNat @1) (SNat @1) u269)) [1, 1])))) ; t280 = u279 !$ [0] ; w284 = stranspose @[2,0,1] (sscatter (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) t280)) [0]) (\\[i281, i282, i283] -> [i281, i282, 2 * quotH i282 2, 0, 2 * i283])) ; w285 = stranspose @[4,1,2,0,3] (sslice (SNat @0) (SNat @1) w284) ; w291 = stranspose @[4,0,1,2,3] (sscatter (sslice (SNat @0) (SNat @1) w285) (\\[i286, i287, i288, i289, i290] -> [i287, i288, i289, i290, i286])) ; w306 = sscatter t280 (\\[i303, i304, i305] -> [2 * i305, i303, i304, 2 * quotH i304 2, 2 * i303]) ; w315 = stranspose @[3,0,1,2] (sscatter (ssum @1 (sslice (SNat @0) (SNat @1) w306)) (\\[i311, i312, i313, i314] -> [i311, i312, i313, i314, 0])) ; w319 = stranspose @[2,0,1] (sscatter (ssum @1 (sslice (SNat @0) (SNat @1) w315)) (\\[i316, i317, i318] -> [i316, i317, i318, 0])) ; w325 = sscatter (sslice (SNat @1) (SNat @1) w319) (\\[i320, i321, i322, i323, i324] -> [ifH (0 <=. negate i324 + negate i320) 0 1, i321, i322, 1, i323, i324]) ; w331 = sscatter (sslice (SNat @0) (SNat @1) w319) (\\[i326, i327, i328, i329, i330] -> [ifH (notB (0 <=. negate i330 + negate i326) &&* notB (1 <=. i330 + i326)) 1 0, i327, i328, i326, i329, i330]) ; w337 = stranspose @[3,0,1,2] (sscatter (ssum @1 (sslice (SNat @1) (SNat @1) w306)) (\\[i307, i308, i309, i310] -> [i307, i308, i309, i310, 1])) ; w341 = stranspose @[2,0,1] (sscatter (ssum @1 (sslice (SNat @0) (SNat @1) w337)) (\\[i338, i339, i340] -> [i338, i339, i340, 0])) ; w347 = sscatter (sslice (SNat @1) (SNat @1) w341) (\\[i342, i343, i344, i345, i346] -> [ifH (0 <=. negate i346 + negate i342) 0 1, i343, i344, 1, i345, i346]) ; w353 = sscatter (sslice (SNat @0) (SNat @1) w341) (\\[i348, i349, i350, i351, i352] -> [ifH (notB (0 <=. negate i352 + negate i348) &&* notB (1 <=. i352 + i348)) 1 0, i349, i350, i348, i351, i352]) in rfromS (sscatter (stranspose @[1,2,0] (sappend (sconcrete (sfromListLinear [0,2,2,3,3] [])) (sappend (sscatter (stranspose @[1,2,3,4,5,0] (sappend (sconcrete (sfromListLinear [1,2,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (sappend (stranspose @[5,0,1,2,3,4] (ssum @2 (str (ssum @2 (ssum @2 (sscatter (w353 !$ [0] + w347 !$ [0]) (\\[i354, i355, i356, i357, i358] -> [i354, i355, i356, i357, i358, 0, 1, i356, i357]) + sscatter (w331 !$ [0] + w325 !$ [0]) (\\[i332, i333, i334, i335, i336] -> [i332, i333, i334, i335, i336, 0, i336, i334, i335]))))))) (sconcrete (sfromListLinear [0,2,2,2,2,2] []))))) (\\[i359, i360, i361, i362, i363] -> [i362, i359, i361, i360 + i363])) (sconcrete (sfromListLinear [1,2,2,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))))) (\\[i364, i365] -> [i364 + i365]) + sscatter (stranspose @[1,2,0] (sappend (sconcrete (sfromListLinear [0,2,2,3,3] [])) (sappend (sscatter (stranspose @[1,2,3,4,5,0] (sappend (sconcrete (sfromListLinear [1,2,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (sappend (stranspose @[5,0,1,2,3,4] (ssum @2 (str (ssum @2 (ssum @2 (sscatter (ssum @1 (sslice (SNat @0) (SNat @1) w291)) (\\[i292, i293, i294, i295] -> [i292, i293, i294, i295, 0, i294, 1, 1, i295]))))))) (sconcrete (sfromListLinear [0,2,2,2,2,2] []))))) (\\[i296, i297, i298, i299, i300] -> [i299, i296, i298, i297 + i300])) (sconcrete (sfromListLinear [1,2,2,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))))) (\\[i301, i302] -> [i301 + i302]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (let t280 = ssum @2 (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) + sscatter (sreplicate @1 (stranspose @[3,0,1,2] (sreplicate @1 (str (sreplicate @1 (ssum @2 (ssum @2 (ssum @2 (ssum @2 (sscatter (sfromR dret) (\\[i265, i266, i267, i268] -> [i265, 0, 0, 0, 0, i266, i267, i268]) !$ [0])))))) !$ [0])) !$ [0])) (\\[i275, i276, i277, i278] -> [i277, i276, i278, i275])) ; w306 = sscatter t280 (\\[i303, i304, i305] -> [2 * i305, i303, i304, 2 * quotH i304 2, 2 * i303]) ; w319 = sscatter (sscatter (w306 !$ [0]) (\\[i311, i312, i313, i314] -> [i314, i311, i312, i313, 0]) !$ [0]) (\\[i316, i317, i318] -> [i318, i316, i317, 0]) ; w341 = sscatter (sscatter (w306 !$ [1]) (\\[i307, i308, i309, i310] -> [i310, i307, i308, i309, 1]) !$ [0]) (\\[i338, i339, i340] -> [i340, i338, i339, 0]) in sscatter (stranspose @[1,2,0] (sappend (sscatter (stranspose @[1,2,3,4,5,0] (sappend (sconcrete (sfromListLinear [1,2,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (ssum @2 (ssum @2 (ssum @2 (sscatter (sscatter (sreplicate @1 (w341 !$ [0])) (\\[i348, i349, i350, i351, i352] -> [ifH (notB (0 <=. negate i352 + negate i348) &&* notB (1 <=. i352 + i348)) 1 0, i349, i350, i348, i351, i352]) !$ [0] + sscatter (sreplicate @1 (w341 !$ [1])) (\\[i342, i343, i344, i345, i346] -> [ifH (0 <=. negate i346 + negate i342) 0 1, i343, i344, 1, i345, i346]) !$ [0]) (\\[i354, i355, i356, i357, i358] -> [i354, i355, i357, i357, i356, i358, 0, 1, i356]) + sscatter (sscatter (sreplicate @1 (w319 !$ [0])) (\\[i326, i327, i328, i329, i330] -> [ifH (notB (0 <=. negate i330 + negate i326) &&* notB (1 <=. i330 + i326)) 1 0, i327, i328, i326, i329, i330]) !$ [0] + sscatter (sreplicate @1 (w319 !$ [1])) (\\[i320, i321, i322, i323, i324] -> [ifH (0 <=. negate i324 + negate i320) 0 1, i321, i322, 1, i323, i324]) !$ [0]) (\\[i332, i333, i334, i335, i336] -> [i332, i333, i335, i335, i334, i336, 0, i336, i334]))))))) (\\[i359, i360, i361, i362, i363] -> [i362, i359, i361, i360 + i363])) (sconcrete (sfromListLinear [1,2,2,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) (\\[i364, i365] -> [i364 + i365]) + sscatter (stranspose @[1,2,0] (sappend (sscatter (stranspose @[1,2,3,4,5,0] (sappend (sconcrete (sfromListLinear [1,2,2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (ssum @2 (ssum @2 (ssum @2 (sscatter (sscatter (sreplicate @1 (stranspose @[3,2,0,1] (sreplicate @1 (stranspose @[3,2,1,0] (sscatter (soneHot (t280 !$ [0]) [0]) (\\[i281, i282, i283] -> [2 * quotH i282 2, i281, i282, 0, 2 * i283]) !$ [0]) !$ [0])))) (\\[i286, i287, i288, i289, i290] -> [i286, i287, i288, i289, i290]) !$ [0]) (\\[i292, i293, i294, i295] -> [i292, i293, i295, i295, i294, 0, i294, 1, 1]))))))) (\\[i296, i297, i298, i299, i300] -> [i299, i296, i298, i297 + i300])) (sconcrete (sfromListLinear [1,2,2,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) (\\[i301, i302] -> [i301 + i302]))"

maxPool2dUnpadded3
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded3 arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez3 [2, 2, 2, 2] arr [iBh `quotH` 2, aa, bb, iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"

conv2dUnpadded3
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded3 arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez4 shB arrA [iImg, 0, iBw, 1]
      in rindex0 arrAt [0, iBw, iImg, iBh] + rindex0 arrAt [iImg, 1, iBw + 1, iBh]
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

slicez3
  :: (ADReady target, GoodScalar r, KnownNat n)
  => IShR n -> target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez3 shOut d ixBase =
  rbuild shOut $ \_ -> indexz03 d (zipWith_Index (+) ixBase ixBase)

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
  printAstPretty afcnn2T
    @?= "rfromS (let w12 = sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i23, i20, i17, i14, i11, i10, i9, i8] -> [ifH (0 <=. negate i20 + negate i11 &&* (1 <=. i20 + negate i10 &&* (notB (notB (0 <=. negate i23 * i17 + negate i9) &&* notB (1 <=. i23 * i17 + i9 &&* (-1) <=. negate i23 * i17 + negate i9)) &&* notB (notB (0 <=. (-2) * i14 + negate i8) &&* notB (1 <=. 2 * i14 + i8 &&* (-1) <=. (-2) * i14 + negate i8))))) 0 1]) in sgather w12 (\\[i22, i19, i16, i13] -> [i22, i19, i16, i13, 0, 0, 0, 0]))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP4b :: Assertion
testCNNOPP4b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded4 (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w48 = sgather (sfromVector (fromList [stranspose @[1,2,3,4,5,0] (sreplicate @2 (sgather (sslice (SNat @1) (SNat @2) (sfromR u1)) (\\[i33, i34, i35, i36, i37, i38, i39] -> [i34 + i37, 2, i33 * i35 + i38, 2 * i36 + i39]))), sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))))])) (\\[i40, i41, i42, i43, i44, i45, i46, i47] -> [ifH (0 <=. negate i41 + negate i44 &&* (1 <=. i41 + negate i45 &&* (notB (notB (0 <=. negate i40 * i42 + negate i46) &&* notB (1 <=. i40 * i42 + i46 &&* (-1) <=. negate i40 * i42 + negate i46)) &&* notB (notB (0 <=. (-2) * i43 + negate i47) &&* notB (1 <=. 2 * i43 + i47 &&* (-1) <=. (-2) * i43 + negate i47))))) 0 1, i40, i41, i42, i43, i44, i45, i46, i47]) in rfromS (sgather w48 (\\[i49, i50, i51, i52] -> [i49, i50, i51, i52, 0, 0, 0, 0]))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w66 = sscatter (sscatter (sfromR dret) (\\[i54, i55, i56, i57] -> [i54, i55, i56, i57, 0, 0, 0, 0])) (\\[i58, i59, i60, i61, i62, i63, i64, i65] -> [ifH (0 <=. negate i59 + negate i62 &&* (1 <=. i59 + negate i63 &&* (notB (notB (0 <=. negate i58 * i60 + negate i64) &&* notB (1 <=. i58 * i60 + i64 &&* (-1) <=. negate i58 * i60 + negate i64)) &&* notB (notB (0 <=. (-2) * i61 + negate i65) &&* notB (1 <=. 2 * i61 + i65 &&* (-1) <=. (-2) * i61 + negate i65))))) 0 1, i58, i59, i60, i61, i62, i63, i64, i65]) in rfromS (sappend (sconcrete (sfromListLinear [1,3,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (sappend (sscatter (ssum @2 (stranspose @[5,0,1,2,3,4] (w66 !$ [0]))) (\\[i67, i68, i69, i70, i71, i72, i73] -> [i68 + i71, 2, i67 * i69 + i72, 2 * i70 + i73])) (sconcrete (sfromListLinear [0,3,3,3] []))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sappend (sconcrete (sfromListLinear [1,3,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (sscatter (ssum @2 (stranspose @[5,0,1,2,3,4] (sscatter (sscatter (sfromR dret) (\\[i54, i55, i56, i57] -> [i54, i55, i56, i57, 0, 0, 0, 0])) (\\[i58, i59, i60, i61, i62, i63, i64, i65] -> [ifH (0 <=. negate i59 + negate i62 &&* (1 <=. i59 + negate i63 &&* (notB (notB (0 <=. negate i58 * i60 + negate i64) &&* notB (1 <=. i58 * i60 + i64 &&* (-1) <=. negate i58 * i60 + negate i64)) &&* notB (notB (0 <=. (-2) * i61 + negate i65) &&* notB (1 <=. 2 * i61 + i65 &&* (-1) <=. (-2) * i61 + negate i65))))) 0 1, i58, i59, i60, i61, i62, i63, i64, i65]) !$ [0]))) (\\[i67, i68, i69, i70, i71, i72, i73] -> [i68 + i71, 2, i67 * i69 + i72, 2 * i70 + i73])))"

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
  printAstPretty afcnn2T
    @?= "rfromS (sreplicate @1 (sreplicate @1 (str (sappend (sreplicate @1 (sappend (sreplicate @1 (sscalar 7.0)) (sreplicate @1 (sscalar 0.0)))) (sreplicate @1 (sreplicate @2 (sscalar 0.0)))))))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [1,1,2,2] [7.0,0.0,0.0,0.0]))"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP5b :: Assertion
testCNNOPP5b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent conv2dUnpadded4 (FTKR [5, 5, 5, 5] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let t27 = stranspose @[1,2,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,1,0] (sslice (SNat @0) (SNat @2) (str (sreplicate @1 (sfromR u1 !$ [0, 0])))))) ; m30 = sgather t27 (\\[i28, i29] -> [i28, i29, 0]) in rfromS (str (sreplicate @1 (stranspose @[1,2,0] (sappend (sreplicate @1 (str (sappend (sreplicate @1 (sgather m30 (\\[i31] -> [i31, 0]))) (sreplicate @1 (sreplicate @1 (sscalar 0.0)))))) (sreplicate @1 (sreplicate @1 (sreplicate @2 (sscalar 0.0))))))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (str (sreplicate @1 (stranspose @[1,2,0] (sappend (sreplicate @1 (str (sappend (sreplicate @1 (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0]))) (sconcrete (sfromListLinear [1,1] [0.0]))))) (sconcrete (sfromListLinear [1,1,2] [0.0,0.0]))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (ssum @1 (str (sappend (sconcrete (sfromListLinear [0,1,5] [])) (sappend (stranspose @[2,1,0] (sappend (sconcrete (sfromListLinear [0,1,2] [])) (sappend (stranspose @[2,0,1] (sscatter (sscatter (ssum @1 (sslice (SNat @0) (SNat @1) (str (ssum @1 (sslice (SNat @0) (SNat @1) (stranspose @[2,0,1] (ssum @1 (str (sfromR dret))))))))) (\\[i33] -> [i33, 0])) (\\[i34, i35] -> [i34, i35, 0]))) (sconcrete (sfromListLinear [3,1,2] [0.0,0.0,0.0,0.0,0.0,0.0]))))) (sconcrete (sfromListLinear [3,1,5] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))))) [0, 0])"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (str (sappend (stranspose @[2,1,0] (sappend (sscatter (sscatter (stranspose @[1,2,3,0] (sfromR dret) !$ [0, 0, 0]) (\\[i33] -> [i33, 0])) (\\[i34, i35] -> [0, i34, i35])) (sconcrete (sfromListLinear [3,1,2] [0.0,0.0,0.0,0.0,0.0,0.0])))) (sconcrete (sfromListLinear [3,1,5] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [0]) [0, 0])"

maxPool2dUnpadded4
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded4 arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez4 [2, 2, 2, 2] arr [bb + 1, 2 - bb, aa * iBh, 2 * iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"

conv2dUnpadded4
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded4 arrA =
  let shB = [1, 1, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez4 shB arrA [iImg, 0, iBh, iBw]
      in rindex0 arrAt [0, 0, 0, 0]
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

slicez4
  :: (ADReady target, GoodScalar r, KnownNat n)
  => IShR n -> target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez4 shOut d ixBase =
  rbuild shOut $ \ixResult -> indexz03 d (zipWith_Index (+) ixBase ixResult)

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
  printAstPretty afcnn2T
    @?= "rfromS (let w24 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (let u41 = str (sreplicate @2 (sfromVector (fromList [let m29 = sgather (sappend (sconcrete (sfromListLinear [1,1] [0.0])) (sreplicate @1 (sreplicate @1 (sscalar 0.0)))) (\\[i34, i4] -> [2 * i4, 2 * quotH i34 2]) in str (sappend (sreplicate @1 (sreplicate @2 (sscalar 7.0))) (sreplicate @1 (sgather m29 (\\[i33] -> [i33, 1])))), sreplicate @2 (sreplicate @2 (sscalar 0.0))]))) in sappend (str (sappend (sreplicate @1 (stranspose @[1,2,0] (sappend (sgather (u41 !$ [0]) (\\[i26, i40, i32] -> [i40, i32, i26])) (sreplicate @1 (sgather (stranspose @[2,1,0] (u41 !$ [1]) !$ [1]) (\\[i40, i32] -> [i32, i40])))))) (sreplicate @1 (sreplicate @1 (u41 !$ [1, 0]))))) (sreplicate @1 (sreplicate @2 (u41 !$ [1, 1]))))))))))) in sgather w24 (\\[i39, i36, i31, i25] -> [i39, i36, i31, i25, 0, 0, 0, 0]))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sappend (str (sappend (sreplicate @1 (stranspose @[1,2,0] (sappend (stranspose @[0,2,1] (sreplicate @1 (str (sreplicate @1 (sconcrete (sfromListLinear [2] [7.0,7.0])))))) (sreplicate @1 (sreplicate @1 (sconcrete (sfromListLinear [2] [0.0,0.0]))))))) (sreplicate @1 (sreplicate @1 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])))))) (sreplicate @1 (sreplicate @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])))))"
  printAstPretty (simplifyInlineContract $ simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"

testCNNOPP6b :: Assertion
testCNNOPP6b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dUnpadded3z) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let t39 = sreplicate @2 (sgather (sfromR u1) (\\[i37, i38] -> [2 * i37, 2 * i37, 2 * i37, 2 * i38])) ; v41 = sgather t39 (\\[i40] -> [i40, 0, 2 * i40]) ; t42 = str (sreplicate @2 (sfromVector (fromList [sappend (sreplicate @1 (v41 !$ [0])) (sreplicate @1 (sscalar 0.0)), sreplicate @2 (sscalar 0.0)]))) ; w45 = stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (stranspose @[1,2,3,0] (sreplicate @2 (sappend (str (sappend (sreplicate @1 (str (sappend (sgather (t42 !$ [0]) (\\[i43, i44] -> [i44, i43])) (sreplicate @1 (sreplicate @1 (t42 !$ [1, 0, 1])))))) (sreplicate @1 (sreplicate @1 (t42 !$ [1, 0]))))) (sreplicate @1 (sreplicate @2 (t42 !$ [1, 1]))))))))))) in rfromS (stranspose @[1,2,0] (sreplicate @2 (sgather w45 (\\[i46, i47, i48] -> [i46, i47, i48, 0, 0, 0, 0]))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (let t42 = str (sreplicate @2 (sfromVector (fromList [sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])), sconcrete (sfromListLinear [2] [0.0,0.0])]))) in stranspose @[1,2,0] (sreplicate @2 (sappend (str (sappend (sreplicate @1 (str (sappend (sreplicate @1 (sreplicate @1 (t42 !$ [0, 0, 0]))) (sreplicate @1 (sreplicate @1 (t42 !$ [1, 0, 1])))))) (sreplicate @1 (sreplicate @1 (t42 !$ [1, 0]))))) (sreplicate @1 (sreplicate @2 (t42 !$ [1, 1]))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let t53 = ssum @2 (stranspose @[3,0,1,2] (ssum @2 (stranspose @[3,0,1,2] (ssum @2 (stranspose @[3,0,1,2] (ssum @2 (stranspose @[3,0,1,2] (sscatter (ssum @2 (stranspose @[2,0,1] (sfromR dret))) (\\[i50, i51, i52] -> [i50, i51, i52, 0, 0, 0, 0]))))))))) ; t54 = str (sslice (SNat @0) (SNat @1) t53) ; m55 = str (ssum @1 (sslice (SNat @0) (SNat @1) t54)) ; m58 = ssum @2 (str (soneHot (sscatter (sslice (SNat @0) (SNat @1) m55) (\\[i56, i57] -> [i57, i56])) [0] + (soneHot (ssum @1 (ssum @1 (sslice (SNat @1) (SNat @1) m55))) [1, 0, 1] + (soneHot (ssum @1 (ssum @1 (sslice (SNat @1) (SNat @1) t54))) [1, 0] + soneHot (ssum @2 (ssum @1 (sslice (SNat @1) (SNat @1) t53))) [1, 1])))) ; v59 = m58 !$ [0] in rfromS (sscatter (ssum @2 (sscatter (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) v59)) [0]) (\\[i60] -> [i60, 0, 2 * i60]))) (\\[i61, i62] -> [2 * i61, 2 * i61, 2 * i61, 2 * i62]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (let t53 = ssum @2 (ssum @2 (ssum @2 (ssum @2 (sscatter (ssum @2 (stranspose @[2,0,1] (sfromR dret))) (\\[i50, i51, i52] -> [0, 0, 0, 0, i50, i51, i52]))))) ; t54 = str (sreplicate @1 (t53 !$ [0])) in sscatter (ssum @2 (sscatter (soneHot (ssum0 (sconcrete (sfromListLinear [2] [0.0,0.0]) + (sscatter (sreplicate @1 (str (t54 !$ [0]) !$ [0])) (\\[i56, i57] -> [i56, i57]) !$ [0] + (stranspose @[1,2,0] (soneHot (t54 !$ [1, 0]) [0, 1]) !$ [0, 0] + stranspose @[1,2,0] (soneHot (ssum @2 (t53 !$ [1])) [1, 1]) !$ [0, 0])))) [0]) (\\[i60] -> [i60, 0, 2 * i60]))) (\\[i61, i62] -> [2 * i61, 2 * i61, 2 * i61, 2 * i62]))"

conv2dUnpadded3z
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded3z arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez3 shB arrA [iImg, iImg, iImg, iBw]
      in rindex0 arrAt [iBh, iBw, iImg, iBh]
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

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
  printAstPretty afcnn2T
    @?= "rfromS (let w24 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (let t34 = sreplicate @2 (let m31 = sgather (sappend (sconcrete (sfromListLinear [1,2] [0.0,0.0])) (sreplicate @1 (sreplicate @2 (sscalar 0.0)))) (\\[i40, i3] -> [2 * i3, 2 * i40]) in str (sappend (sreplicate @1 (sappend (sreplicate @1 (sscalar 7.0)) (sreplicate @1 (sscalar 0.0)))) (sreplicate @1 (sgather m31 (\\[i39] -> [i39, 1]))))) in stranspose @[1,2,0] (sappend (str (sappend (stranspose @[1,2,0] (sappend (stranspose @[1,2,3,0] (sappend (sreplicate @1 (sgather t34 (\\[i38, i44, i28] -> [i44, i38, i28]))) (sreplicate @1 (sreplicate @1 (sreplicate @1 (sreplicate @1 (sscalar 0.0))))))) (sreplicate @1 (sreplicate @1 (sreplicate @1 (sreplicate @2 (sscalar 0.0))))))) (sreplicate @1 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))))))))))) in sgather w24 (\\[i42, i36, i27, i25] -> [i42, i36, i27, i25, 0, 0, 0, 0]))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"

testCNNOPP7b :: Assertion
testCNNOPP7b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3y . conv2dUnpadded3y) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let u52 = sreplicate @2 (sreplicate @2 (sgather (sfromR u1) (\\[i50, i51] -> [2 * i50, 2 * i50, 2 * i50, 2 * i51]))) ; m55 = sgather u52 (\\[i53, i54] -> [i53, i54, 0, 2 * i53]) ; m56 = sappend (sreplicate @1 (m55 !$ [0])) (sreplicate @1 (sreplicate @2 (sscalar 0.0))) ; t58 = sreplicate @2 (str (sappend (sreplicate @1 (sgather m56 (\\[i57] -> [i57, 0]))) (sreplicate @1 (sreplicate @2 (sscalar 0.0))))) ; w62 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,0] (sappend (str (sappend (stranspose @[1,2,0] (sappend (stranspose @[1,2,3,0] (sappend (sreplicate @1 (sgather t58 (\\[i59, i60, i61] -> [i60, i59, i61]))) (sreplicate @1 (sreplicate @1 (sreplicate @1 (sreplicate @1 (sscalar 0.0))))))) (sreplicate @1 (sreplicate @1 (sreplicate @1 (sreplicate @2 (sscalar 0.0))))))) (sreplicate @1 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))) (sreplicate @1 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))))))))))) in rfromS (sgather w62 (\\[i63, i64, i65, i66] -> [i63, i64, i65, i66, 0, 0, 0, 0]))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1,2,0] (sappend (str (sappend (stranspose @[1,2,0] (sappend (stranspose @[1,2,3,0] (sappend (sreplicate @1 (sreplicate @1 (sreplicate @1 (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0]))))) (sconcrete (sfromListLinear [1,1,1,1] [0.0])))) (sconcrete (sfromListLinear [1,1,1,2] [0.0,0.0])))) (sconcrete (sfromListLinear [1,1,2,2] [0.0,0.0,0.0,0.0])))) (sconcrete (sfromListLinear [1,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let u72 = stranspose @[2,0,1] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (sscatter (sfromR dret) (\\[i68, i69, i70, i71] -> [i68, i69, i70, i71, 0, 0, 0, 0])))))))))) ; u73 = str (sslice (SNat @0) (SNat @1) u72) ; u74 = stranspose @[2,0,1] (sslice (SNat @0) (SNat @1) u73) ; u75 = stranspose @[3,0,1,2] (sslice (SNat @0) (SNat @1) u74) ; m79 = str (ssum @2 (sscatter (ssum @1 (sslice (SNat @0) (SNat @1) u75)) (\\[i76, i77, i78] -> [i77, i76, i78]))) ; m81 = sscatter (ssum @1 (sslice (SNat @0) (SNat @1) m79)) (\\[i80] -> [i80, 0]) in rfromS (sscatter (ssum @2 (ssum @2 (sscatter (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) m81)) [0]) (\\[i82, i83] -> [i82, i83, 0, 2 * i82])))) (\\[i84, i85] -> [2 * i84, 2 * i84, 2 * i84, 2 * i85]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter (ssum @2 (ssum @2 (sscatter (soneHot (sscatter (ssum @2 (sscatter (ssum @2 (ssum @2 (ssum @2 (ssum @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @1 (sreplicate @1 (sreplicate @1 (stranspose @[4,5,6,3,2,1,0] (sscatter (sfromR dret) (\\[i68, i69, i70, i71] -> [i70, 0, 0, 0, 0, i68, i69, i71]) !$ [0]) !$ [0, 0, 0]))))))))) (\\[i76, i77, i78] -> [i78, i77, i76]) !$ [0])) (\\[i80] -> [i80, 0]) !$ [0]) [0]) (\\[i82, i83] -> [i82, i83, 0, 2 * i82])))) (\\[i84, i85] -> [2 * i84, 2 * i84, 2 * i84, 2 * i85]))"

maxPool2dUnpadded3y
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded3y arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez3 [2, 2, 2, 2] arr [iBh, aa, bb, iBw]
      in rmaximum3 arrt
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"

conv2dUnpadded3y
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded3y arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez3 shB arrA [iImg, iImg, iImg, iBh]
      in rindex0 arrAt [iBh, iBw, iImg, iBh]
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"
