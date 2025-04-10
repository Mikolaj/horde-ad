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
  length (show t1) @?= 271
  resetVarCounter
  let !t2 = gather1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 271
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
  length (show t1) @?= 398
  resetVarCounter
  let !t2 = gather2 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 338
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t1)) @?= 338
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
  length (show t1) @?= 398
  resetVarCounter
  let !t2 = gather12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 338
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 338
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 338

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
  length (show t2) @?= 442
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t1)) @?= 341
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t2)) @?= 442

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
  length (show t1) @?= 1160
  resetVarCounter
  let !t2 = scatter2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 738
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 1160
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 738

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
  length (show t1) @?= 994
  resetVarCounter
  let !t2 = scatter12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 738
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 994
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 738

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
  length (show t1) @?= 17606
  length (show (simplifyInlineContract @(TKR 10 Float) t1)) @?= 23244
  resetVarCounter
  let !t2 = barRelu @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 17606
  length (show (simplifyInlineContract @(TKR 10 Float) t2)) @?= 23244

testCNNOPP2 :: Assertion
testCNNOPP2 = do
  resetVarCounter
  let t = maxPool2dUnpadded2
            (rconcrete $ Nested.rreplicateScal (1 :$: 1 :$: 2 :$: 2 :$: ZSR) 1)
  printAstPretty t
    @?= "rfromS (sreplicate @2 (sreplicate @2 (let w45 = stranspose @[1,2,3,0] (sreplicate @1 (sgather (sfromVector (fromList [let w30 = sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (stranspose @[1,2,0] (sappend (sgather (sappend (sconcrete (sfromListLinear [1,1,2,2] [1.0,1.0,1.0,1.0])) (sconcrete (sfromListLinear [2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) (\\[i12, i28, i26] -> [i28, i12, i26 + i12, i12])) (str (sreplicate @3 (str (sreplicate @2 (sconcrete (sfromListLinear [1] [0.0])))))))))))) in sgather (sfromVector (fromList [sgather (sfromVector (fromList [sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))), sgather w30 (\\[i58, i51, i44, i39, i32] -> [i58, i51, i44, i39, i32, 1, 2 * i58 + i39, 2 * i51 + i32])])) (\\[i57, i50, i43] -> [ifH (2 <=. i50 + i43) 0 1, i57, i50, i43]), sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i56, i49, i42] -> [ifH (1 <=. i49 + i42) 0 1, i56, i49, i42]), sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i54, i47, i40] -> [ifH (1 <=. i47 + i40) (ifH ((-1) <=. negate i47 + negate i40) 0 1) 1, i54, i47, i40]))) in sgather w45 (\\[i53, i46] -> [i53, i46, 0, 0, 0, 0]))))"
  printAstPretty (simplifyInlineContract t)
    @?= "rfromS (sreplicate @2 (sreplicate @2 (str (sappend (sconcrete (sfromListLinear [1,2] [0.0,0.0])) (sreplicate @1 (stranspose @[1,2,3,0] (stranspose @[0,2,1] (sgather (stranspose @[0,2,3,1] (sfromVector (fromList [stranspose @[2,0,1] (sgather (stranspose @[0,2,3,1] (sfromVector (fromList [sconcrete (sfromListLinear [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sgather (str (sappend (stranspose @[0,2,1] (sgather (sconcrete (sfromListLinear [1,2,2,3] [1.0,0.0,0.0,1.0,0.0,0.0,1.0,0.0,0.0,1.0,0.0,0.0])) (\\[i12, i26] -> [i12, i26 + i12, i12]))) (sconcrete (sfromListLinear [1,3,2] [0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [1]) (\\[i58, i51, i66, i39, i32] -> [2 * i51 + i32, 2 * i58 + i39])]))) (\\[i50, i43] -> [ifH (2 <=. i50 + i43) 0 1, i50, i43])), sconcrete (sfromListLinear [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]))) (\\[i49, i42] -> [ifH (1 <=. i49 + i42) 0 1, i49, i42])) !$ [1]) !$ [0, 0, 0]))))))"

testCNNOPP2b :: Assertion
testCNNOPP2b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded2 (FTKR [1, 1, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w63 = sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (stranspose @[1,2,0] (sappend (sgather (sappend (sfromR u1) (sconcrete (sfromListLinear [2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) (\\[i60, i61, i62] -> [i61, i60, i62 + i60, i60])) (str (sreplicate @3 (str (sreplicate @2 (sconcrete (sfromListLinear [1] [0.0])))))))))))) ; w78 = stranspose @[1,2,3,0] (sreplicate @1 (sgather (sfromVector (fromList [sgather (sfromVector (fromList [sgather (sfromVector (fromList [sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))), sgather w63 (\\[i64, i65, i66, i67, i68] -> [i64, i65, i66, i67, i68, 1, 2 * i64 + i67, 2 * i65 + i68])])) (\\[i69, i70, i71] -> [ifH (2 <=. i70 + i71) 0 1, i69, i70, i71]), sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i72, i73, i74] -> [ifH (1 <=. i73 + i74) 0 1, i72, i73, i74]), sreplicate @2 (sreplicate @2 (sreplicate @1 (sreplicate @2 (sreplicate @2 (sscalar 0.0)))))])) (\\[i75, i76, i77] -> [ifH (1 <=. i76 + i77) (ifH ((-1) <=. negate i76 + negate i77) 0 1) 1, i75, i76, i77]))) in rfromS (sreplicate @2 (sreplicate @2 (sgather w78 (\\[i79, i80] -> [i79, i80, 0, 0, 0, 0]))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sreplicate @2 (sreplicate @2 (str (sappend (sconcrete (sfromListLinear [1,2] [0.0,0.0])) (sreplicate @1 (stranspose @[1,2,3,0] (stranspose @[0,2,1] (sgather (stranspose @[0,2,3,1] (sfromVector (fromList [stranspose @[2,0,1] (sgather (stranspose @[0,2,3,1] (sfromVector (fromList [sconcrete (sfromListLinear [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sgather (str (sappend (stranspose @[0,2,1] (sgather (stranspose @[1,2,3,0] (sappend (sfromR u1) (sconcrete (sfromListLinear [2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) (\\[i60, i62] -> [i60, i62 + i60, i60]))) (sconcrete (sfromListLinear [1,3,2] [0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [1]) (\\[i64, i65, i120, i67, i68] -> [2 * i65 + i68, 2 * i64 + i67])]))) (\\[i70, i71] -> [ifH (2 <=. i70 + i71) 0 1, i70, i71])), sconcrete (sfromListLinear [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]))) (\\[i73, i74] -> [ifH (1 <=. i73 + i74) 0 1, i73, i74])) !$ [1]) !$ [0, 0, 0]))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w87 = sscatter (ssum @1 (stranspose @[3,0,1,2] (sscatter (ssum @2 (ssum @2 (sfromR dret))) (\\[i82, i83] -> [i82, i83, 0, 0, 0, 0])))) (\\[i84, i85, i86] -> [ifH (1 <=. i85 + i86) (ifH ((-1) <=. negate i85 + negate i86) 0 1) 1, i84, i85, i86]) ; w91 = sscatter (w87 !$ [0]) (\\[i88, i89, i90] -> [ifH (1 <=. i89 + i90) 0 1, i88, i89, i90]) ; w95 = sscatter (w91 !$ [0]) (\\[i92, i93, i94] -> [ifH (2 <=. i93 + i94) 0 1, i92, i93, i94]) ; t101 = stranspose @[2,0,1] (ssum @2 (ssum @2 (ssum @1 (ssum @2 (ssum @2 (sscatter (w95 !$ [1]) (\\[i96, i97, i98, i99, i100] -> [i96, i97, i98, i99, i100, 1, 2 * i96 + i99, 2 * i97 + i100]))))))) ; u105 = sscatter (sslice (SNat @0) (SNat @1) t101) (\\[i102, i103, i104] -> [i103, i102, i104 + i102, i102]) in rfromS (sslice (SNat @0) (SNat @1) u105)"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sreplicate @1 (sscatter (sreplicate @1 (ssum @2 (ssum @2 (ssum @2 (ssum @2 (stranspose @[5,4,3,2,1,0] (stranspose @[6,5,4,3,2,1,0] (sscatter (sscatter (sscatter (sscatter (sscatter (ssum @2 (ssum @2 (sfromR dret))) (\\[i82, i83] -> [i82, i83, 0, 0, 0])) (\\[i84, i85, i86] -> [ifH (1 <=. i85 + i86) (ifH ((-1) <=. negate i85 + negate i86) 0 1) 1, i84, i85, i86]) !$ [0]) (\\[i88, i89, i90] -> [ifH (1 <=. i89 + i90) 0 1, i88, i89, i90]) !$ [0]) (\\[i92, i93, i94] -> [ifH (2 <=. i93 + i94) 0 1, i92, i93, i94]) !$ [1]) (\\[i96, i97, i98, i99, i100] -> [i98, i96, i97, i99, i100, 1, 2 * i96 + i99, 2 * i97 + i100]) !$ [0]) !$ [0]))))))) (\\[i102, i103, i104] -> [i103, i102, i104 + i102, i102]) !$ [0]))"

maxPool2dUnpadded2
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded2 a =
  rbuild [2, 2, 2, 2] $ \case
    [_, _, iBh, iBw] ->
      let arrt = slicez2 (conv2dUnpadded2 a) [iBw, 3, 2 * iBh, 2 * iBw]
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
      blackGlyph = AstFromPrimal $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                       (rconcrete $ Nested.rscalar 7
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: AstTensor AstMethodLet FullSpan (TKR 4 Double)
      afcnn2T = maxPool2dUnpadded3 $ conv2dUnpadded3 blackGlyph
  printAstPretty afcnn2T
    @?= "rfromS (let w17 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (sgather (sconcrete (sfromListLinear [2] [0.0,0.0])) (\\[i28, i25, i22, i4] -> [let i19 = ifH (notB (notB (0 <=. negate i28 + negate i28) &&* notB (0 <=. negate i28 + negate i28)) &&* (notB (notB (0 <=. negate i25 + negate i25) &&* notB (0 <=. negate i25 + negate i25)) &&* notB (notB (0 <=. negate i4 + negate i4) &&* notB (0 <=. negate i4 + negate i4)))) 0 1 in ifH (0 <=. quotH (negate i22) 2 + quotH (negate i22) 2) i19 (ifH (0 <=. quotH (negate i22) 2 + quotH (negate i22) 2) i19 1)]))))))))) in sgather w17 (\\[i27, i24, i21, i18] -> [i27, i24, i21, i18, 0, 0, 0, 0]))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sgather (sconcrete (sfromListLinear [2] [0.0,0.0])) (\\[i36, i35, i34, i33] -> [ifH (0 <=. quotH (negate i34) 2 + quotH (negate i34) 2) (ifH (notB (notB (0 <=. negate i36 + negate i36) &&* notB (0 <=. negate i36 + negate i36)) &&* (notB (notB (0 <=. negate i35 + negate i35) &&* notB (0 <=. negate i35 + negate i35)) &&* notB (notB (0 <=. negate i33 + negate i33) &&* notB (0 <=. negate i33 + negate i33)))) 0 1) (ifH (0 <=. quotH (negate i34) 2 + quotH (negate i34) 2) (ifH (notB (notB (0 <=. negate i36 + negate i36) &&* notB (0 <=. negate i36 + negate i36)) &&* (notB (notB (0 <=. negate i35 + negate i35) &&* notB (0 <=. negate i35 + negate i35)) &&* notB (notB (0 <=. negate i33 + negate i33) &&* notB (0 <=. negate i33 + negate i33)))) 0 1) 1)]))"

testCNNOPP3b :: Assertion
testCNNOPP3b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dUnpadded3) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w35 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (sgather (sconcrete (sfromListLinear [2] [0.0,0.0])) (\\[i30, i31, i32, i33] -> [let x34 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (0 <=. negate i30 + negate i30) &&* notB (0 <=. negate i30 + negate i30)) &&* (notB (notB (0 <=. negate i31 + negate i31) &&* notB (0 <=. negate i31 + negate i31)) &&* notB (notB (0 <=. negate i33 + negate i33) &&* notB (0 <=. negate i33 + negate i33)))) 0 1] in kfromS (tfromVector (fromList [kfromS x34, kfromS (tfromVector (fromList [kfromS x34, 1]) !$ [ifH (0 <=. quotH (negate i32) 2 + quotH (negate i32) 2) 0 1])]) !$ [ifH (0 <=. quotH (negate i32) 2 + quotH (negate i32) 2) 0 1])]))))))))) in rfromS (sgather w35 (\\[i36, i37, i38, i39] -> [i36, i37, i38, i39, 0, 0, 0, 0]))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sgather (sconcrete (sfromListLinear [2] [0.0,0.0])) (\\[i52, i51, i50, i49] -> [kfromS (let x34 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (0 <=. negate i52 + negate i52) &&* notB (0 <=. negate i52 + negate i52)) &&* (notB (notB (0 <=. negate i51 + negate i51) &&* notB (0 <=. negate i51 + negate i51)) &&* notB (notB (0 <=. negate i49 + negate i49) &&* notB (0 <=. negate i49 + negate i49)))) 0 1] in sfromVector (fromList [x34, tfromVector (fromList [kfromS x34, 1]) !$ [ifH (0 <=. quotH (negate i50) 2 + quotH (negate i50) 2) 0 1]]) !$ [ifH (0 <=. quotH (negate i50) 2 + quotH (negate i50) 2) 0 1])]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"

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
      let arrAt = slicez3 shB arrA [iImg `remH` 2, iImg, iImg, 2]
      in rindex0 arrAt [iBh, iBw, iImg, iBh]
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

slicez3
  :: (ADReady target, GoodScalar r, KnownNat n)
  => IShR n -> target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez3 shOut d ixBase =
  rbuild shOut $ \_ixResult -> indexz03 d (zipWith_Index (+) ixBase ixBase) -- ixResult)

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
    @?= "rfromS (let w12 = sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i23, i20, i17, i14, i11, i10, i9, i8] -> [ifH (0 <=. negate i20 + negate i11) (ifH (2 <=. i20 + negate i10 &&* (notB (notB (0 <=. negate i23 * i17 + negate i9) &&* notB (1 <=. i23 * i17 + i9 &&* (-1) <=. negate i23 * i17 + negate i9)) &&* notB (notB (0 <=. (-2) * i14 + negate i8) &&* notB (1 <=. 2 * i14 + i8 &&* (-1) <=. (-2) * i14 + negate i8)))) 0 1) 1]) in sgather w12 (\\[i22, i19, i16, i13] -> [i22, i19, i16, i13, 0, 0, 0, 0]))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"

testCNNOPP4b :: Assertion
testCNNOPP4b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded4 (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w54 = sgather (sfromVector (fromList [sgather (sslice (SNat @3) (SNat @0) (stranspose @[2,0,1] (sgather (sslice (SNat @1) (SNat @2) (sfromR u1)) (\\[i34, i35] -> [i34 + i35])))) (\\[i36, i37, i38, i39, i40, i41, i42, i43] -> [negate i37 + i41, i37, i40, i36 * i38 + i42, 2 * i39 + i43]), sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))))))])) (\\[i44, i45, i46, i47, i48, i49, i50, i51] -> [let i52 = negate i44 ; i53 = negate i44 in ifH (0 <=. negate i45 + negate i48) (ifH (2 <=. i45 + negate i49 &&* (notB (notB (0 <=. i52 * i46 + negate i50) &&* notB (1 <=. i44 * i46 + i50 &&* (-1) <=. i53 * i46 + negate i50)) &&* notB (notB (0 <=. (-2) * i47 + negate i51) &&* notB (1 <=. 2 * i47 + i51 &&* (-1) <=. (-2) * i47 + negate i51)))) 0 1) 1, i44, i45, i46, i47, i48, i49, i50, i51]) in rfromS (sgather w54 (\\[i55, i56, i57, i58] -> [i55, i56, i57, i58, 0, 0, 0, 0]))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w74 = sscatter (sscatter (sfromR dret) (\\[i60, i61, i62, i63] -> [i60, i61, i62, i63, 0, 0, 0, 0])) (\\[i64, i65, i66, i67, i68, i69, i70, i71] -> [let i72 = negate i64 ; i73 = negate i64 in ifH (0 <=. negate i65 + negate i68) (ifH (2 <=. i65 + negate i69 &&* (notB (notB (0 <=. i72 * i66 + negate i70) &&* notB (1 <=. i64 * i66 + i70 &&* (-1) <=. i73 * i66 + negate i70)) &&* notB (notB (0 <=. (-2) * i67 + negate i71) &&* notB (1 <=. 2 * i67 + i71 &&* (-1) <=. (-2) * i67 + negate i71)))) 0 1) 1, i64, i65, i66, i67, i68, i69, i70, i71]) in rfromS (sappend (sconcrete (sfromListLinear [1,3,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (sappend (sscatter (stranspose @[1,2,0] (sappend (sconcrete (sfromListLinear [3,2,2,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (sappend (sscatter (w74 !$ [0]) (\\[i75, i76, i77, i78, i79, i80, i81, i82] -> [negate i76 + i80, i76, i79, i75 * i77 + i81, 2 * i78 + i82])) (sconcrete (sfromListLinear [0,2,2,3,3] []))))) (\\[i83, i84] -> [i83 + i84])) (sconcrete (sfromListLinear [0,3,3,3] []))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sappend (sconcrete (sfromListLinear [1,3,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (sscatter (sconcrete (sfromListLinear [2,2,3,3,3] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])) (\\[i83, i84] -> [i83 + i84])))"

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
    @?= "rfromS (str (sreplicate @1 (stranspose @[1,2,0] (sappend (sreplicate @1 (str (sappend (sreplicate @1 (sreplicate @1 (sscalar 7.0))) (sreplicate @1 (sreplicate @1 (sscalar 0.0)))))) (sreplicate @1 (sreplicate @1 (sreplicate @2 (sscalar 0.0))))))))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sconcrete (sfromListLinear [1,1,2,2] [7.0,0.0,0.0,0.0]))"

testCNNOPP5b :: Assertion
testCNNOPP5b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent conv2dUnpadded4 (FTKR [5, 5, 5, 5] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let t22 = stranspose @[1,2,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,1,0] (sslice (SNat @0) (SNat @2) (str (sreplicate @1 (sfromR u1 !$ [0, 0])))))) in rfromS (str (sreplicate @1 (stranspose @[1,2,0] (sappend (stranspose @[1,2,0] (sappend (sgather t22 (\\[i23, i24, i25] -> [i25, i23, i24])) (sreplicate @1 (sreplicate @1 (sreplicate @1 (sscalar 0.0)))))) (sreplicate @1 (sreplicate @1 (sreplicate @2 (sscalar 0.0))))))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (str (sreplicate @1 (stranspose @[1,2,0] (sappend (stranspose @[1,2,0] (sappend (sreplicate @1 (sreplicate @1 (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])))) (sconcrete (sfromListLinear [1,1,1] [0.0])))) (sconcrete (sfromListLinear [1,1,2] [0.0,0.0]))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let t27 = stranspose @[2,0,1] (ssum @1 (str (sfromR dret))) ; t28 = stranspose @[2,0,1] (sslice (SNat @0) (SNat @1) t27) in rfromS (soneHot (ssum @1 (str (sappend (sconcrete (sfromListLinear [0,1,5] [])) (sappend (stranspose @[2,1,0] (sappend (sconcrete (sfromListLinear [0,1,2] [])) (sappend (stranspose @[2,0,1] (sscatter (sslice (SNat @0) (SNat @1) t28) (\\[i29, i30, i31] -> [i31, i29, i30]))) (sconcrete (sfromListLinear [3,1,2] [0.0,0.0,0.0,0.0,0.0,0.0]))))) (sconcrete (sfromListLinear [3,1,5] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))))) [0, 0])"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (str (sappend (stranspose @[2,1,0] (sappend (sscatter (sreplicate @1 (sreplicate @1 (stranspose @[1,2,3,0] (sfromR dret) !$ [0, 0, 0]))) (\\[i29, i30, i31] -> [i30, i31, i29])) (sconcrete (sfromListLinear [3,1,2] [0.0,0.0,0.0,0.0,0.0,0.0])))) (sconcrete (sfromListLinear [3,1,5] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) !$ [0]) [0, 0])"

maxPool2dUnpadded4
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded4 arr =
  rbuild [2, 2, 2, 2] $ \case
    [aa, bb, iBh, iBw] ->
      let arrt = slicez4 [2, 2, 2, 2] arr [bb + 1, 3 - bb, aa * iBh, 2 * iBw]
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
    @?= "rfromS (let w19 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (sgather (sfromVector (fromList [let m18 = str (sreplicate @2 (quotH (siota (SNat @2)) (treplicate (SNat @2) (STKScalar) 2) + quotH (siota (SNat @2)) (treplicate (SNat @2) (STKScalar) 2))) ; m12 = sreplicate @2 (siota (SNat @2) + siota (SNat @2)) in sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i30, i23] -> [let i17 = ifH (notB (notB (sscalar 0 <=. negate (m18 !$ [i30, i23]) + negate (m18 !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (m18 !$ [i30, i23]) + negate (m18 !$ [i30, i23]))) &&* (notB (notB (sscalar 0 <=. negate (m18 !$ [i30, i23]) + negate (m18 !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (m18 !$ [i30, i23]) + negate (m18 !$ [i30, i23]))) &&* notB (notB (sscalar 0 <=. negate (m12 !$ [i30, i23]) + negate (m12 !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (m12 !$ [i30, i23]) + negate (m12 !$ [i30, i23]))))) 0 1 in ifH (sscalar 0 <=. negate (m18 !$ [i30, i23]) + negate (m18 !$ [i30, i23])) i17 (ifH (sscalar 0 <=. negate (m18 !$ [i30, i23]) + negate (m18 !$ [i30, i23])) i17 1)]), sreplicate @2 (sreplicate @2 (sscalar 0.0))])) (\\[i36, i33, i27, i21] -> [let i24 = ifH (notB (notB (0 <=. negate i36 + negate i36) &&* notB (0 <=. negate i36 + negate i36)) &&* (notB (notB (0 <=. negate i33 + negate i33) &&* notB (0 <=. negate i33 + negate i33)) &&* notB (notB (0 <=. negate i21 + negate i21) &&* notB (0 <=. negate i21 + negate i21)))) 0 1 in ifH (0 <=. quotH (negate i27) 2 + quotH (negate i27) 2) i24 (ifH (0 <=. quotH (negate i27) 2 + quotH (negate i27) 2) i24 1), i27, i21]))))))))) in sgather w19 (\\[i35, i32, i26, i20] -> [i35, i32, i26, i20, 0, 0, 0, 0]))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sgather (sfromVector (fromList [sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i30, i23] -> [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23])) (ifH (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]))) &&* (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]))) &&* notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i30, i23]))))) 0 1) (ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23])) (ifH (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]))) &&* (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i30, i23]))) &&* notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i30, i23])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i30, i23]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i30, i23]))))) 0 1) 1)]), sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])])) (\\[i44, i43, i42, i41] -> [ifH (0 <=. quotH (negate i42) 2 + quotH (negate i42) 2) (ifH (notB (notB (0 <=. negate i44 + negate i44) &&* notB (0 <=. negate i44 + negate i44)) &&* (notB (notB (0 <=. negate i43 + negate i43) &&* notB (0 <=. negate i43 + negate i43)) &&* notB (notB (0 <=. negate i41 + negate i41) &&* notB (0 <=. negate i41 + negate i41)))) 0 1) (ifH (0 <=. quotH (negate i42) 2 + quotH (negate i42) 2) (ifH (notB (notB (0 <=. negate i44 + negate i44) &&* notB (0 <=. negate i44 + negate i44)) &&* (notB (notB (0 <=. negate i43 + negate i43) &&* notB (0 <=. negate i43 + negate i43)) &&* notB (notB (0 <=. negate i41 + negate i41) &&* notB (0 <=. negate i41 + negate i41)))) 0 1) 1), i42, i41]))"

testCNNOPP6b :: Assertion
testCNNOPP6b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dUnpadded3z) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let m43 = str (sreplicate @2 (quotH (siota (SNat @2)) (sreplicate @2 (sfromK 2)) + quotH (siota (SNat @2)) (sreplicate @2 (sfromK 2)))) ; m44 = sreplicate @2 (siota (SNat @2) + siota (SNat @2)) ; w55 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (sgather (sfromVector (fromList [sgather (sfromVector (fromList [sgather (sfromR u1) (\\[i45, i46] -> [kfromS (m43 !$ [i45, i46] + m43 !$ [i45, i46]), kfromS (m43 !$ [i45, i46] + m43 !$ [i45, i46]), kfromS (m43 !$ [i45, i46] + m43 !$ [i45, i46]), kfromS (m44 !$ [i45, i46] + m44 !$ [i45, i46])]), sreplicate @2 (sreplicate @2 (sscalar 0.0))])) (\\[i47, i48] -> [let x49 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (sscalar 0 <=. negate (m43 !$ [i47, i48]) + negate (m43 !$ [i47, i48])) &&* notB (sscalar 0 <=. negate (m43 !$ [i47, i48]) + negate (m43 !$ [i47, i48]))) &&* (notB (notB (sscalar 0 <=. negate (m43 !$ [i47, i48]) + negate (m43 !$ [i47, i48])) &&* notB (sscalar 0 <=. negate (m43 !$ [i47, i48]) + negate (m43 !$ [i47, i48]))) &&* notB (notB (sscalar 0 <=. negate (m44 !$ [i47, i48]) + negate (m44 !$ [i47, i48])) &&* notB (sscalar 0 <=. negate (m44 !$ [i47, i48]) + negate (m44 !$ [i47, i48]))))) 0 1] in kfromS (tfromVector (fromList [kfromS x49, kfromS (tfromVector (fromList [kfromS x49, 1]) !$ [ifH (sscalar 0 <=. negate (m43 !$ [i47, i48]) + negate (m43 !$ [i47, i48])) 0 1])]) !$ [ifH (sscalar 0 <=. negate (m43 !$ [i47, i48]) + negate (m43 !$ [i47, i48])) 0 1]), i47, i48]), sreplicate @2 (sreplicate @2 (sscalar 0.0))])) (\\[i50, i51, i52, i53] -> [let x54 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (0 <=. negate i50 + negate i50) &&* notB (0 <=. negate i50 + negate i50)) &&* (notB (notB (0 <=. negate i51 + negate i51) &&* notB (0 <=. negate i51 + negate i51)) &&* notB (notB (0 <=. negate i53 + negate i53) &&* notB (0 <=. negate i53 + negate i53)))) 0 1] in kfromS (tfromVector (fromList [kfromS x54, kfromS (tfromVector (fromList [kfromS x54, 1]) !$ [ifH (0 <=. quotH (negate i52) 2 + quotH (negate i52) 2) 0 1])]) !$ [ifH (0 <=. quotH (negate i52) 2 + quotH (negate i52) 2) 0 1]), i52, i53]))))))))) in rfromS (sgather w55 (\\[i56, i57, i58, i59] -> [i56, i57, i58, i59, 0, 0, 0, 0]))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sgather (sfromVector (fromList [sgather (sfromVector (fromList [sgather (sfromR u1) (\\[i45, i46] -> [kfromS (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i45, i46] + sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i45, i46]), kfromS (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i45, i46] + sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i45, i46]), kfromS (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i45, i46] + sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i45, i46]), kfromS (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i45, i46] + sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i45, i46])]), sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])])) (\\[i47, i48] -> [kfromS (let x49 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48]))) &&* (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48]))) &&* notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i47, i48]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i47, i48])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i47, i48]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i47, i48]))))) 0 1] in sfromVector (fromList [x49, tfromVector (fromList [kfromS x49, 1]) !$ [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48])) 0 1]]) !$ [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i47, i48])) 0 1]), i47, i48]), sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])])) (\\[i84, i83, i82, i81] -> [kfromS (let x54 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (0 <=. negate i84 + negate i84) &&* notB (0 <=. negate i84 + negate i84)) &&* (notB (notB (0 <=. negate i83 + negate i83) &&* notB (0 <=. negate i83 + negate i83)) &&* notB (notB (0 <=. negate i81 + negate i81) &&* notB (0 <=. negate i81 + negate i81)))) 0 1] in sfromVector (fromList [x54, tfromVector (fromList [kfromS x54, 1]) !$ [ifH (0 <=. quotH (negate i82) 2 + quotH (negate i82) 2) 0 1]]) !$ [ifH (0 <=. quotH (negate i82) 2 + quotH (negate i82) 2) 0 1]), i82, i81]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let m43 = str (sreplicate @2 (quotH (siota (SNat @2)) (sreplicate @2 (sfromK 2)) + quotH (siota (SNat @2)) (sreplicate @2 (sfromK 2)))) ; m44 = sreplicate @2 (siota (SNat @2) + siota (SNat @2)) ; t70 = sscatter (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (sscatter (sfromR dret) (\\[i61, i62, i63, i64] -> [i61, i62, i63, i64, 0, 0, 0, 0])))))))))) (\\[i65, i66, i67, i68] -> [let x69 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (0 <=. negate i65 + negate i65) &&* notB (0 <=. negate i65 + negate i65)) &&* (notB (notB (0 <=. negate i66 + negate i66) &&* notB (0 <=. negate i66 + negate i66)) &&* notB (notB (0 <=. negate i68 + negate i68) &&* notB (0 <=. negate i68 + negate i68)))) 0 1] in kfromS (tfromVector (fromList [kfromS x69, kfromS (tfromVector (fromList [kfromS x69, 1]) !$ [ifH (0 <=. quotH (negate i67) 2 + quotH (negate i67) 2) 0 1])]) !$ [ifH (0 <=. quotH (negate i67) 2 + quotH (negate i67) 2) 0 1]), i67, i68]) ; t74 = sscatter (t70 !$ [0]) (\\[i71, i72] -> [let x73 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (sscalar 0 <=. negate (m43 !$ [i71, i72]) + negate (m43 !$ [i71, i72])) &&* notB (sscalar 0 <=. negate (m43 !$ [i71, i72]) + negate (m43 !$ [i71, i72]))) &&* (notB (notB (sscalar 0 <=. negate (m43 !$ [i71, i72]) + negate (m43 !$ [i71, i72])) &&* notB (sscalar 0 <=. negate (m43 !$ [i71, i72]) + negate (m43 !$ [i71, i72]))) &&* notB (notB (sscalar 0 <=. negate (m44 !$ [i71, i72]) + negate (m44 !$ [i71, i72])) &&* notB (sscalar 0 <=. negate (m44 !$ [i71, i72]) + negate (m44 !$ [i71, i72]))))) 0 1] in kfromS (tfromVector (fromList [kfromS x73, kfromS (tfromVector (fromList [kfromS x73, 1]) !$ [ifH (sscalar 0 <=. negate (m43 !$ [i71, i72]) + negate (m43 !$ [i71, i72])) 0 1])]) !$ [ifH (sscalar 0 <=. negate (m43 !$ [i71, i72]) + negate (m43 !$ [i71, i72])) 0 1]), i71, i72]) in rfromS (sscatter (t74 !$ [0]) (\\[i75, i76] -> [kfromS (m43 !$ [i75, i76] + m43 !$ [i75, i76]), kfromS (m43 !$ [i75, i76] + m43 !$ [i75, i76]), kfromS (m43 !$ [i75, i76] + m43 !$ [i75, i76]), kfromS (m44 !$ [i75, i76] + m44 !$ [i75, i76])]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter (sscatter (sscatter (ssum @2 (ssum @2 (ssum @2 (ssum @2 (sscatter (sfromR dret) (\\[i61, i62, i63, i64] -> [0, 0, 0, 0, i61, i62, i63, i64])))))) (\\[i65, i66, i67, i68] -> [kfromS (let x69 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (0 <=. negate i65 + negate i65) &&* notB (0 <=. negate i65 + negate i65)) &&* (notB (notB (0 <=. negate i66 + negate i66) &&* notB (0 <=. negate i66 + negate i66)) &&* notB (notB (0 <=. negate i68 + negate i68) &&* notB (0 <=. negate i68 + negate i68)))) 0 1] in sfromVector (fromList [x69, tfromVector (fromList [kfromS x69, 1]) !$ [ifH (0 <=. quotH (negate i67) 2 + quotH (negate i67) 2) 0 1]]) !$ [ifH (0 <=. quotH (negate i67) 2 + quotH (negate i67) 2) 0 1]), i67, i68]) !$ [0]) (\\[i71, i72] -> [kfromS (let x73 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72]))) &&* (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72]))) &&* notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i71, i72]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i71, i72])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i71, i72]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i71, i72]))))) 0 1] in sfromVector (fromList [x73, tfromVector (fromList [kfromS x73, 1]) !$ [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72])) 0 1]]) !$ [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72]) + negate (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i71, i72])) 0 1]), i71, i72]) !$ [0]) (\\[i75, i76] -> [kfromS (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i75, i76] + sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i75, i76]), kfromS (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i75, i76] + sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i75, i76]), kfromS (sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i75, i76] + sconcrete (sfromListLinear [2,2] [0,0,0,0]) !$ [i75, i76]), kfromS (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i75, i76] + sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i75, i76])]))"

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
    @?= "rfromS (let w19 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (sgather (sfromVector (fromList [let m18 = sreplicate @2 (siota (SNat @2) + siota (SNat @2)) ; m11 = str (sreplicate @2 (siota (SNat @2) + siota (SNat @2))) in sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i32, i26] -> [let i17 = ifH (notB (notB (sscalar 0 <=. negate (m18 !$ [i32, i26]) + negate (m18 !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (m18 !$ [i32, i26]) + negate (m18 !$ [i32, i26]))) &&* (notB (notB (sscalar 0 <=. negate (m18 !$ [i32, i26]) + negate (m18 !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (m18 !$ [i32, i26]) + negate (m18 !$ [i32, i26]))) &&* notB (notB (sscalar 0 <=. negate (m11 !$ [i32, i26]) + negate (m11 !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (m11 !$ [i32, i26]) + negate (m11 !$ [i32, i26]))))) 0 1 in ifH (sscalar 0 <=. negate (m18 !$ [i32, i26]) + negate (m18 !$ [i32, i26])) i17 (ifH (sscalar 0 <=. negate (m18 !$ [i32, i26]) + negate (m18 !$ [i32, i26])) i17 1)]), sreplicate @2 (sreplicate @2 (sscalar 0.0))])) (\\[i35, i29, i24, i4] -> [let i21 = ifH (notB (notB (0 <=. negate i35 + negate i35) &&* notB (0 <=. negate i35 + negate i35)) &&* (notB (notB (0 <=. negate i29 + negate i29) &&* notB (0 <=. negate i29 + negate i29)) &&* notB (notB (0 <=. negate i4 + negate i4) &&* notB (0 <=. negate i4 + negate i4)))) 0 1 in ifH (0 <=. negate i24 + negate i24) i21 (ifH (0 <=. negate i24 + negate i24) i21 1), i29, i24]))))))))) in sgather w19 (\\[i34, i28, i23, i20] -> [i34, i28, i23, i20, 0, 0, 0, 0]))"
  printAstPretty (simplifyInlineContract afcnn2T)
    @?= "rfromS (sgather (sfromVector (fromList [sgather (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i32, i26] -> [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26])) (ifH (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]))) &&* (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]))) &&* notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i32, i26]))))) 0 1) (ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26])) (ifH (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]))) &&* (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i32, i26]))) &&* notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i32, i26])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i32, i26]) + negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i32, i26]))))) 0 1) 1)]), sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])])) (\\[i43, i42, i41, i40] -> [ifH (0 <=. negate i41 + negate i41) (ifH (notB (notB (0 <=. negate i43 + negate i43) &&* notB (0 <=. negate i43 + negate i43)) &&* (notB (notB (0 <=. negate i42 + negate i42) &&* notB (0 <=. negate i42 + negate i42)) &&* notB (notB (0 <=. negate i40 + negate i40) &&* notB (0 <=. negate i40 + negate i40)))) 0 1) (ifH (0 <=. negate i41 + negate i41) (ifH (notB (notB (0 <=. negate i43 + negate i43) &&* notB (0 <=. negate i43 + negate i43)) &&* (notB (notB (0 <=. negate i42 + negate i42) &&* notB (0 <=. negate i42 + negate i42)) &&* notB (notB (0 <=. negate i40 + negate i40) &&* notB (0 <=. negate i40 + negate i40)))) 0 1) 1), i42, i41]))"

testCNNOPP7b :: Assertion
testCNNOPP7b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3y . conv2dUnpadded3y) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let m42 = sreplicate @2 (siota (SNat @2) + siota (SNat @2)) ; m43 = str (sreplicate @2 (siota (SNat @2) + siota (SNat @2))) ; w54 = stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (stranspose @[1,2,3,4,0] (sreplicate @2 (sgather (sfromVector (fromList [sgather (sfromVector (fromList [sgather (sfromR u1) (\\[i44, i45] -> [kfromS (m42 !$ [i44, i45] + m42 !$ [i44, i45]), kfromS (m42 !$ [i44, i45] + m42 !$ [i44, i45]), kfromS (m42 !$ [i44, i45] + m42 !$ [i44, i45]), kfromS (m43 !$ [i44, i45] + m43 !$ [i44, i45])]), sreplicate @2 (sreplicate @2 (sscalar 0.0))])) (\\[i46, i47] -> [let x48 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (sscalar 0 <=. negate (m42 !$ [i46, i47]) + negate (m42 !$ [i46, i47])) &&* notB (sscalar 0 <=. negate (m42 !$ [i46, i47]) + negate (m42 !$ [i46, i47]))) &&* (notB (notB (sscalar 0 <=. negate (m42 !$ [i46, i47]) + negate (m42 !$ [i46, i47])) &&* notB (sscalar 0 <=. negate (m42 !$ [i46, i47]) + negate (m42 !$ [i46, i47]))) &&* notB (notB (sscalar 0 <=. negate (m43 !$ [i46, i47]) + negate (m43 !$ [i46, i47])) &&* notB (sscalar 0 <=. negate (m43 !$ [i46, i47]) + negate (m43 !$ [i46, i47]))))) 0 1] in kfromS (tfromVector (fromList [kfromS x48, kfromS (tfromVector (fromList [kfromS x48, 1]) !$ [ifH (sscalar 0 <=. negate (m42 !$ [i46, i47]) + negate (m42 !$ [i46, i47])) 0 1])]) !$ [ifH (sscalar 0 <=. negate (m42 !$ [i46, i47]) + negate (m42 !$ [i46, i47])) 0 1]), i46, i47]), sreplicate @2 (sreplicate @2 (sscalar 0.0))])) (\\[i49, i50, i51, i52] -> [let x53 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (0 <=. negate i49 + negate i49) &&* notB (0 <=. negate i49 + negate i49)) &&* (notB (notB (0 <=. negate i50 + negate i50) &&* notB (0 <=. negate i50 + negate i50)) &&* notB (notB (0 <=. negate i52 + negate i52) &&* notB (0 <=. negate i52 + negate i52)))) 0 1] in kfromS (tfromVector (fromList [kfromS x53, kfromS (tfromVector (fromList [kfromS x53, 1]) !$ [ifH (0 <=. negate i51 + negate i51) 0 1])]) !$ [ifH (0 <=. negate i51 + negate i51) 0 1]), i50, i51]))))))))) in rfromS (sgather w54 (\\[i55, i56, i57, i58] -> [i55, i56, i57, i58, 0, 0, 0, 0]))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (sgather (sfromVector (fromList [sgather (sfromVector (fromList [sgather (sfromR u1) (\\[i44, i45] -> [kfromS (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i44, i45] + sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i44, i45]), kfromS (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i44, i45] + sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i44, i45]), kfromS (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i44, i45] + sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i44, i45]), kfromS (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i44, i45] + sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i44, i45])]), sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])])) (\\[i46, i47] -> [kfromS (let x48 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47]))) &&* (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47]))) &&* notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i46, i47]) + negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i46, i47])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i46, i47]) + negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i46, i47]))))) 0 1] in sfromVector (fromList [x48, tfromVector (fromList [kfromS x48, 1]) !$ [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47])) 0 1]]) !$ [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i46, i47])) 0 1]), i46, i47]), sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])])) (\\[i83, i82, i81, i80] -> [kfromS (let x53 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (0 <=. negate i83 + negate i83) &&* notB (0 <=. negate i83 + negate i83)) &&* (notB (notB (0 <=. negate i82 + negate i82) &&* notB (0 <=. negate i82 + negate i82)) &&* notB (notB (0 <=. negate i80 + negate i80) &&* notB (0 <=. negate i80 + negate i80)))) 0 1] in sfromVector (fromList [x53, tfromVector (fromList [kfromS x53, 1]) !$ [ifH (0 <=. negate i81 + negate i81) 0 1]]) !$ [ifH (0 <=. negate i81 + negate i81) 0 1]), i82, i81]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let m42 = sreplicate @2 (siota (SNat @2) + siota (SNat @2)) ; m43 = str (sreplicate @2 (siota (SNat @2) + siota (SNat @2))) ; t69 = sscatter (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (ssum @2 (stranspose @[4,0,1,2,3] (sscatter (sfromR dret) (\\[i60, i61, i62, i63] -> [i60, i61, i62, i63, 0, 0, 0, 0])))))))))) (\\[i64, i65, i66, i67] -> [let x68 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (0 <=. negate i64 + negate i64) &&* notB (0 <=. negate i64 + negate i64)) &&* (notB (notB (0 <=. negate i65 + negate i65) &&* notB (0 <=. negate i65 + negate i65)) &&* notB (notB (0 <=. negate i67 + negate i67) &&* notB (0 <=. negate i67 + negate i67)))) 0 1] in kfromS (tfromVector (fromList [kfromS x68, kfromS (tfromVector (fromList [kfromS x68, 1]) !$ [ifH (0 <=. negate i66 + negate i66) 0 1])]) !$ [ifH (0 <=. negate i66 + negate i66) 0 1]), i65, i66]) ; t73 = sscatter (t69 !$ [0]) (\\[i70, i71] -> [let x72 = tfromVector (fromList [0, 1]) !$ [ifH (notB (notB (sscalar 0 <=. negate (m42 !$ [i70, i71]) + negate (m42 !$ [i70, i71])) &&* notB (sscalar 0 <=. negate (m42 !$ [i70, i71]) + negate (m42 !$ [i70, i71]))) &&* (notB (notB (sscalar 0 <=. negate (m42 !$ [i70, i71]) + negate (m42 !$ [i70, i71])) &&* notB (sscalar 0 <=. negate (m42 !$ [i70, i71]) + negate (m42 !$ [i70, i71]))) &&* notB (notB (sscalar 0 <=. negate (m43 !$ [i70, i71]) + negate (m43 !$ [i70, i71])) &&* notB (sscalar 0 <=. negate (m43 !$ [i70, i71]) + negate (m43 !$ [i70, i71]))))) 0 1] in kfromS (tfromVector (fromList [kfromS x72, kfromS (tfromVector (fromList [kfromS x72, 1]) !$ [ifH (sscalar 0 <=. negate (m42 !$ [i70, i71]) + negate (m42 !$ [i70, i71])) 0 1])]) !$ [ifH (sscalar 0 <=. negate (m42 !$ [i70, i71]) + negate (m42 !$ [i70, i71])) 0 1]), i70, i71]) in rfromS (sscatter (t73 !$ [0]) (\\[i74, i75] -> [kfromS (m42 !$ [i74, i75] + m42 !$ [i74, i75]), kfromS (m42 !$ [i74, i75] + m42 !$ [i74, i75]), kfromS (m42 !$ [i74, i75] + m42 !$ [i74, i75]), kfromS (m43 !$ [i74, i75] + m43 !$ [i74, i75])]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter (sscatter (sscatter (ssum @2 (ssum @2 (ssum @2 (ssum @2 (sscatter (sfromR dret) (\\[i60, i61, i62, i63] -> [0, 0, 0, 0, i60, i61, i62, i63])))))) (\\[i64, i65, i66, i67] -> [kfromS (let x68 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (0 <=. negate i64 + negate i64) &&* notB (0 <=. negate i64 + negate i64)) &&* (notB (notB (0 <=. negate i65 + negate i65) &&* notB (0 <=. negate i65 + negate i65)) &&* notB (notB (0 <=. negate i67 + negate i67) &&* notB (0 <=. negate i67 + negate i67)))) 0 1] in sfromVector (fromList [x68, tfromVector (fromList [kfromS x68, 1]) !$ [ifH (0 <=. negate i66 + negate i66) 0 1]]) !$ [ifH (0 <=. negate i66 + negate i66) 0 1]), i65, i66]) !$ [0]) (\\[i70, i71] -> [kfromS (let x72 = sconcrete (sfromListLinear [2] [0,1]) !$ [ifH (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71]))) &&* (notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71]))) &&* notB (notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i70, i71]) + negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i70, i71])) &&* notB (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i70, i71]) + negate (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i70, i71]))))) 0 1] in sfromVector (fromList [x72, tfromVector (fromList [kfromS x72, 1]) !$ [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71])) 0 1]]) !$ [ifH (sscalar 0 <=. negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71]) + negate (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i70, i71])) 0 1]), i70, i71]) !$ [0]) (\\[i74, i75] -> [kfromS (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i74, i75] + sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i74, i75]), kfromS (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i74, i75] + sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i74, i75]), kfromS (sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i74, i75] + sconcrete (sfromListLinear [2,2] [0,2,0,2]) !$ [i74, i75]), kfromS (sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i74, i75] + sconcrete (sfromListLinear [2,2] [0,0,2,2]) !$ [i74, i75])]))"

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
