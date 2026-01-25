{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Tests of the gather and scatter operations and of operations that expand
-- to gather and of fusion of all of them.
module TestGatherSimplified (testTrees) where

import Prelude

import Control.Monad.ST.Strict (ST, runST)
import Data.Int (Int64, Int8)
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import GHC.Exts (IsList (..))
import GHC.TypeLits (Div, KnownNat, type (<=))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (fromSNat')

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
  , testCase "scatterBuild12c" testScatterBuild12c
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
  , testCase "minimizedCNNOPP4bU" testCNNOPP4bU
  , testCase "detSquarePP" testDetSquarePP
  , testCase "detSquare3" testDetSquare3
  , testCase "detSquare9" testDetSquare9
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
  length (show t1) @?= 307
  resetVarCounter
  let !t2 = gather1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 307
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
             gatherNested2 (t * rreplicate0N [7, 2] (kfromR $ rfromIndex0 i))))
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
             gather2 (t * rreplicate0N [7, 2] (kfromR $ rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testGatherSimpPP2 :: Assertion
testGatherSimpPP2 = do
  resetVarCounter
  let !t1 = gatherNested2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 542
  resetVarCounter
  let !t2 = gather2 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 378
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t1)) @?= 542
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 378

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
  length (show t1) @?= 483
  resetVarCounter
  let !t2 = gather12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 325
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 483
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 325

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
             gatherReshape22 (t * rreplicate0N [6, 2] (kfromR $ rfromIndex0 i))))
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
                (t * rreplicate0N [6, 2] (kfromR $ rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 465
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 471
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (kfromR $ rfromIndex0 i))))
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
                (t * rreplicate0N [6, 2] (kfromR $ rfromIndex0 i)))) var
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (kfromR $ rfromIndex0 i)))) (ringestData [6, 2] vals)
  let !t1n = unAstNoSimplify $ (\t -> rbuild1 4 (\i ->
              gatherReshape22
                (t * rreplicate0N [6, 2] (kfromR $ rfromIndex0 i)))) $ AstNoSimplify var
  let !t2n = unAstNoSimplify $ (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (kfromR $ rfromIndex0 i)))) $ AstNoSimplify var
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
             gatherTranspose33 (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (kfromR $ rfromIndex0 i))))
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
                                 (kfromR $ rfromIndex0 i))))
          (FTKR @10 [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]
                (FTKScalar @Double))
  printArtifactPrimalSimple (simplifyArtifactRev artifactRev)
    @?= "\\w1 -> rfromS (sdot1In (tfromPlain (STKS [4,6,16,8] STKScalar) (sconcrete (sfromListLinear [4,6,16,8] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]))) (ttranspose (makePerm @[1, 0, 3, 2]) (sreplicate @6 (ttranspose (makePerm @[0, 2, 1]) (sreshape @[4, 16, 8] (ttranspose (makePerm @[0, 1, 3, 2]) (sreshape @[4, 2, 2, 8, 4] (tfromPlain (STKS [4,1,2,1,2,2,2,2,2,2,1] STKScalar) (sconcrete (sfromListLinear [4,1,2,1,2,2,2,2,2,2,1] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0])) * sreplicate @4 (ttranspose (makePerm @[3, 7, 0, 1, 2, 4, 6, 5]) (sfromR w1))))))))))"

testGatherTransposeBuild331 :: Assertion
testGatherTransposeBuild331 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 3] [1,1,1,1,1,1])
    (rev' @Double @3
          (\t -> rbuild1 2 (\i ->
             rtranspose [1, 0] (t * rreplicate0N [2, 3] (kfromR $ rfromIndex0 i))))
          (ringestData [2, 3] [1,2,3,4,5,6]))

testGatherTransposeBuild332 :: Assertion
testGatherTransposeBuild332 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 3] [1,1,1,1,1,1])
    (rev' @Double @3
          (\t -> rbuild1 2 (\i ->
             rtranspose [1, 0] (t * rreplicate0N [2, 3] (kfromR $ rfromIndex0 i))))
          (ringestData [2, 3] [1,2,3,4,5,6]))

testGatherTransposeBuild333 :: Assertion
testGatherTransposeBuild333 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2] [1,1])
    (rev' @Double @2
          (\t -> rbuild1 2 (\i ->
             t * rreplicate0N [2] (kfromR $ rfromIndex0 i)))
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
    @?= "rfromS (smatmul2 (tfromPlain (STKS [6,8] STKScalar) (sconcrete (sfromListLinear [6,8] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.89432,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.89432,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]))) (str (sreshape @[16, 8] (ttranspose (makePerm @[0, 2, 1]) (sreshape @[2, 2, 8, 4] (ttranspose (makePerm @[3, 7, 0, 1, 2, 4, 6, 5]) (sfromR w0)))))))"
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
             gatherTranspose33 @(AstTensor AstMethodLet PrimalSpan) (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (kfromR $ rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 2534
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 19868
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              (\t' -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                               (rreshape @10 [8, 16] t'))
                (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (kfromR $ rfromIndex0 i))))
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
             gatherCond (t * rreplicate0N [7, 2] (kfromR $ rfromIndex0 i))))
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
             gatherCond2 (t * rreplicate0N [7, 2] (kfromR $ rfromIndex0 i))))
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
             gatherCond3 (t * rreplicate0N [7, 2] (kfromR $ rfromIndex0 i))))
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
             gatherCond4 (t * rreplicate0N [7, 2] (kfromR $ rfromIndex0 i))))
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
             gatherCond5 (t * rreplicate0N [2,4,2] (kfromR $ rfromIndex0 i))))
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
             gatherCond6 (t * rreplicate0N [2,4,2] (kfromR $ rfromIndex0 i))))
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
  length (show t1) @?= 373
  resetVarCounter
  let !t2 = scatter1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 476
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t1)) @?= 373
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t2)) @?= 476

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
             scatterNested2 (t * rreplicate0N [7, 2] (kfromR $ rfromIndex0 i))))
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
             scatter2 (t * rreplicate0N [7, 2] (kfromR $ rfromIndex0 i))))
          (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterSimpPP2 :: Assertion
testScatterSimpPP2 = do
  resetVarCounter
  let !t1 = scatterNested2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 982
  resetVarCounter
  let !t2 = scatter2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 766
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 982
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 766

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

testScatterBuild12c :: Assertion
testScatterBuild12c =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [7,2]
                 [0.0,0.0,4.0,4.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (rev' @Double @2
          (\t -> rindex (rbuild1 5 (\i ->
             tletPlain (i >. 2) $ \b ->
               ifH (b &&* b)
                   (scatter12 t)
                   (rtranspose [1, 0] $ rreplicate 4 $ t ! [i]))
                       ) [1])
          (rreplicate 7 $ ringestData [2] [0, 1]))

testScatterSimpPP12 :: Assertion
testScatterSimpPP12 = do
  resetVarCounter
  let !t1 = scatterNested12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 920
  resetVarCounter
  let !t2 = scatter12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 609
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 920
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 609

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
barRelu x = let t = rreplicate0N (rshape x) 0.001 * x
            in relu $ bar (t, relu t)

barRelu10xSlower
  :: ( ADReady target, NumScalar r, KnownNat n, Differentiable r )
  => target (TKR n r) -> target (TKR n r)
barRelu10xSlower x = let t = rmap0N (* 0.001) x
                     in relu $ bar (t, relu t)

testBarReluADVal320 :: Assertion
testBarReluADVal320 =
  assertEqualUpToEpsilon 1e-10
    (ringestData [1,2,2,1,2,2,2,2,2,1] [2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885034988157713e-4,2.885923176600045e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.8851415976532735e-4,2.885923176600045e-4,2.887454843457817e-4,2.8849246223035154e-4,2.884182085399516e-4,2.884075468755327e-4,2.8842176240868867e-4,2.8840399312321096e-4,0.0,2.887454843457817e-4,2.886097295122454e-4,2.887454843457817e-4,2.88599069218435e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.885145151321922e-4,2.8854294397024206e-4,2.8858878438222746e-4,2.885923176600045e-4,0.0,2.884007943794131e-4,0.0,2.884469945274759e-4,2.8843242392031246e-4,2.884288700806792e-4,0.0,2.885034988157713e-4,2.884110805753153e-4,0.0,2.8849283778617973e-4,2.884075468755327e-4,2.884075468755327e-4,2.884075468755327e-4,2.884075468755327e-4,0.0,0.0,0.0,0.0,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,0.0,0.0,0.0,0.0,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.884892851579934e-4,2.8854294397024206e-4,2.884288700806792e-4,2.884395315486472e-4,0.0,2.8849246223035154e-4,2.8850276789489724e-4,0.0,2.8849212704517413e-4,2.8854294397024206e-4,2.884288700806792e-4,2.884395315486472e-4,0.0,2.8849246223035154e-4,2.8850276789489724e-4,0.0,2.8849212704517413e-4,2.8842922547482884e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.894378297730782e-4,2.885923176600045e-4,2.887454843457817e-4,2.88599069218435e-4,2.887454843457817e-4,2.887056688523444e-4,2.887454843457817e-4,2.887056688523444e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.884786229769816e-4,2.885923176600045e-4,2.887454843457817e-4,2.886950092188272e-4,2.887454843457817e-4,2.884818011261814e-4,2.887454843457817e-4,2.886097295122454e-4,2.8846476339094805e-4,2.885038541771792e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.885145151321922e-4,2.8854294397024206e-4,2.887167039107226e-4,2.885923176600045e-4,2.887454843457817e-4,2.8860262265516213e-4,2.887454843457817e-4,2.885884088500461e-4,2.887454843457817e-4,2.88599069218435e-4])
    (grad (rsum0 @10 @Double . barRelu10xSlower)
          (rmap0N (* 0.001) t128))

testReluSimpPP :: Assertion
testReluSimpPP = do
  resetVarCounter
  let !t1 = barRelu10xSlower @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t1) @?= 23245
  length (show (simplifyInlineContract @(TKR 10 Float) t1)) @?= 22933
  resetVarCounter
  let !t2 = barRelu @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) Nothing . intToAstVarId $ 100000000)
  length (show t2) @?= 12364
  length (show (simplifyInlineContract @(TKR 10 Float) t2)) @?= 12052

testCNNOPP2 :: Assertion
testCNNOPP2 = do
  resetVarCounter
  let t = maxPool2dUnpadded2
            (rconcrete $ Nested.rreplicatePrim (1 :$: 1 :$: 2 :$: 2 :$: ZSR) 1)
  printAstPretty (simplifyInlineContract t)
    @?= "rfromS (sreplicate @2 (sreplicate @2 (str (sgather1 @2 (stranspose @[2, 3, 0, 1] (sfromVector (fromList [sgather @[2, 2, 2, 2] (sgather1 @2 (stranspose @[3, 0, 1, 2] (sreplicate @1 (str (sgather1 @3 (stranspose @[1, 0, 2, 4, 3] (sfromVector (fromList [stranspose @[1, 2, 4, 0, 3] (sgather @[2, 2] (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (sconcrete (sfromListLinear [2,3,2] [1.0,1.0,0.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,0.0])) (\\[i65, i66] -> [i65 + i66]))) (\\[i22, i17] -> [i22 + i17])), sconcrete (sreplicate [2,3,2,2,2] 0.0)])) !$ [0]) (\\i72 -> [ifH (let i18 = (-1) + i72 in 0 <=. i18 &&* 0 <=. negate i18) 0 1, i72]))))) (\\i24 -> [i24, i24, i24])) (\\[i40, i34, i8, i43] -> [2 * i40 + i8, i40, 2 * i43 + i34]), sconcrete (sreplicate [2,2,2,2] 0.0)])) !$ [0, 0]) (\\i62 -> [ifH (let i9 = (-1) + i62 in 0 <=. i9 &&* 0 <=. negate i9) 0 1, i62])))))"
    -- TODO: was "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty t
    @?= "rfromS (sreplicate @2 (sreplicate @2 (let u37 = sgather1 @2 (stranspose @[2, 0, 1] (sfromVector (fromList [sgather @[2, 2, 2, 2] (sgather1 @2 (stranspose @[3, 0, 4, 5, 1, 2] (sreplicate @1 (sgather1 @3 (str (sfromVector (fromList [stranspose @[2, 3, 0, 4, 1] (sgather @[2, 2] (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (sconcrete (sfromListLinear [2,3,2] [1.0,1.0,0.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,0.0])) (\\[i27, i16] -> [i27 + i16]))) (\\[i22, i17] -> [i22 + i17])), sconcrete (sreplicate [3,2,2,2,2] 0.0)]))) (\\i32 -> [i32, ifH (let i18 = (-1) + i32 in 0 <=. i18 &&* 0 <=. negate i18) 0 1])))) (\\i24 -> [i24, i24, i24, 0])) (\\[i43, i40, i34, i8] -> [2 * i40 + i8, i40, 2 * i43 + i34]), sconcrete (sreplicate [2,2,2,2] 0.0)]))) (\\i39 -> [i39, ifH (let i9 = (-1) + i39 in 0 <=. i9 &&* 0 <=. negate i9) 0 1]) in stranspose @[2, 3, 1, 0] u37 !$ [0, 0])))"

testCNNOPP2b :: Assertion
testCNNOPP2b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded2 (FTKR [1, 1, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (sreplicate @2 (sreplicate @2 (str (sgather1 @2 (stranspose @[2, 3, 0, 1] (sfromVector (fromList [sgather @[2, 2, 2, 2] (sgather1 @2 (stranspose @[3, 0, 1, 2] (sreplicate @1 (str (sgather1 @3 (stranspose @[1, 0, 2, 4, 3] (sfromVector (fromList [stranspose @[1, 2, 4, 0, 3] (sgather @[2, 2] (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (str (sappend (sreplicate @1 (sfromR u1 !$ [0, 0])) (sconcrete (sreplicate [2,2,2] 0.0)))) (\\[i174, i175] -> [i174 + i175]))) (\\[i86, i87] -> [i86 + i87])), sconcrete (sreplicate [2,3,2,2,2] 0.0)])) !$ [0]) (\\i181 -> [let i89 = (-1) + i181 in ifH (0 <=. i89) (ifH (0 <=. negate i89) 0 1) 1, i181]))))) (\\i90 -> [i90, i90, i90])) (\\[i91, i92, i93, i94] -> [2 * i91 + i93, i91, 2 * i94 + i92]), sconcrete (sreplicate [2,2,2,2] 0.0)])) !$ [0, 0]) (\\i95 -> [let i96 = (-1) + i95 in ifH (0 <=. i96) (ifH (0 <=. negate i96) 0 1) 1, i95])))))"
    -- TODO: was "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sreplicate @2 (sreplicate @2 (str (sgather1 @2 (stranspose @[2, 3, 0, 1] (sfromVector (fromList [sgather @[2, 2, 2, 2] (sgather1 @2 (stranspose @[3, 0, 1, 2] (sreplicate @1 (str (sgather1 @3 (stranspose @[1, 0, 2, 4, 3] (sfromVector (fromList [stranspose @[1, 2, 4, 0, 3] (sgather @[2, 2] (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (str (sappend (sreplicate @1 (sfromR u1 !$ [0, 0])) (sconcrete (sreplicate [2,2,2] 0.0)))) (\\[i84, i85] -> [i84 + i85]))) (\\[i86, i87] -> [i86 + i87])), sconcrete (sreplicate [2,3,2,2,2] 0.0)])) !$ [0]) (\\i88 -> [let i89 = (-1) + i88 in ifH (0 <=. i89 &&* 0 <=. negate i89) 0 1, i88]))))) (\\i90 -> [i90, i90, i90])) (\\[i91, i92, i93, i94] -> [2 * i91 + i93, i91, 2 * i94 + i92]), sconcrete (sreplicate [2,2,2,2] 0.0)])) !$ [0, 0]) (\\i95 -> [let i96 = (-1) + i95 in ifH (0 <=. i96 &&* 0 <=. negate i96) 0 1, i95])))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (str (sscatter @[2, 2] (stranspose @[2, 3, 1, 0] (sscatter @[2, 2] (stranspose @[3, 0, 1, 4, 2] (stranspose @[1, 0, 2, 4, 3] (soneHot (sscatter1 @3 (str (ssum @1 (stranspose @[1, 2, 3, 0] (sscatter1 @2 (sscatter @[2, 2, 2, 2] (stranspose @[2, 3, 0, 1] (soneHot (sscatter1 @2 (str (ssum @2 (ssum @2 (sfromR dret)))) (\\i98 -> [let i99 = (-1) + i98 in ifH (0 <=. i99 &&* 0 <=. negate i99) 0 1, i98])) [0, 0]) !$ [0]) (\\[i101, i102, i103, i104] -> [2 * i101 + i103, i101, 2 * i104 + i102])) (\\i105 -> [i105, i105, i105]))))) (\\i106 -> [let i107 = (-1) + i106 in ifH (0 <=. i107 &&* 0 <=. negate i107) 0 1, i106])) [0]) !$ [0])) (\\[i109, i110] -> [i109 + i110]))) (\\[i111, i112] -> [i111 + i112]))))) [0, 0])"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (sscatter @[2, 2] (stranspose @[2, 3, 1, 0] (sscatter @[2, 2] (stranspose @[1, 3, 0, 2, 5, 4] (soneHot (sscatter1 @3 (stranspose @[1, 3, 2, 0] (sscatter1 @2 (sscatter @[2, 2, 2, 2] (stranspose @[2, 3, 0, 1] (soneHot (sscatter1 @2 (ssum @2 (ssum @2 (stranspose @[0, 1, 3, 2] (sfromR dret)))) (\\i98 -> [let i99 = (-1) + i98 in ifH (0 <=. i99 &&* 0 <=. negate i99) 0 1, i98])) [0, 0]) !$ [0]) (\\[i101, i102, i103, i104] -> [2 * i101 + i103, i101, 2 * i104 + i102])) (\\i105 -> [i105, i105, i105])) !$ [0]) (\\i106 -> [let i107 = (-1) + i106 in ifH (0 <=. i107 &&* 0 <=. negate i107) 0 1, i106])) [0]) !$ [0]) (\\[i109, i110] -> [i109 + i110]))) (\\[i111, i112] -> [i111 + i112])) !$ [0])))"
      -- TODO: was "\\dret u1 -> rfromS (sconcrete (sreplicate [1,1,2,2] 0.0))"

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
      in rindex @_ @0 arrAt [0, iBw, iBw, 0]
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
rmaximum2 t0 = tlet t0 $ \t -> rindex t [0, 0, 0, 0]

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
    @?= "rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2, 2] (sfromVector (fromList [stranspose @[1, 2, 0] (sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (stranspose @[2, 0, 1] (sgather1 @2 (sreplicate @2 (str (sappend (sreplicate @1 (str (sappend (sreplicate @1 (sgather1 @2 (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\i34 -> [let i71 = ifH (notB (0 <=. negate i34) &&* notB (let i21 = (-1) + i34 in 0 <=. i21 &&* 0 <=. negate i21)) 1 0 in ifH (0 <=. negate i34) i71 (ifH (let i18 = (-1) + i34 in 0 <=. i18 &&* 0 <=. negate i18) i71 1)]))) (sconcrete (sreplicate [1,2] 0.0))))) (sreplicate @1 (str (sappend (sreplicate @1 (sgather1 @2 (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\i34 -> [let i70 = ifH (notB (0 <=. negate i34) &&* notB (let i20 = 1 + i34 in 0 <=. i20 &&* 0 <=. negate i20)) 1 0 in ifH (0 <=. negate i34) i70 (ifH (let i18 = (-1) + i34 in 0 <=. i18 &&* 0 <=. negate i18) i70 1)]))) (sconcrete (sreplicate [1,2] 0.0)))))) !$ [0] + sgather1 @2 (sreplicate @1 (stranspose @[2, 1, 0] (sappend (sreplicate @1 (sappend (sreplicate @1 (sgather1 @2 (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\i33 -> [ifH (notB (let i17 = 2 * i33 in 0 <=. i17 &&* 0 <=. negate i17) &&* notB (let i18 = (-1) + 2 * i33 in 0 <=. i18 &&* 0 <=. negate i18)) 1 0]))) (sconcrete (sreplicate [1,2] 0.0)))) (sconcrete (sreplicate [1,2,2] 0.0))) !$ [0])) (\\i56 -> [i56, i56]))) (\\i77 -> [2 * i77]))) (\\i80 -> [2 * i80]))) (\\i4 -> [2 * i4])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i46, i44, i43] -> [ifH (notB (notB (let i35 = 2 * i46 in 0 <=. i35 &&* 0 <=. negate i35) &&* notB (let i36 = 2 * i46 in 0 <=. i36 &&* 0 <=. negate i36)) &&* (notB (notB (let i37 = 2 * i44 in 0 <=. i37 &&* 0 <=. negate i37) &&* notB (let i38 = 2 * i44 in 0 <=. i38 &&* 0 <=. negate i38)) &&* notB (notB (let i39 = 2 * i43 in 0 <=. i39 &&* 0 <=. negate i39) &&* notB (let i40 = 2 * i43 in 0 <=. i40 &&* 0 <=. negate i40)))) 0 1, i46, i44, i43]))))"
    -- TODO: was "rfromS (sconcrete (sfromListLinear [2,2,2,2] [14.0,0.0,14.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2, 2] (stranspose @[1, 2, 3, 0] (sfromVector (fromList [stranspose @[1, 2, 0] (sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (str (sgather1 @2 (sreplicate @2 (sgather @[2, 2, 2] (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i34, i31, i12] -> [let i23 = ifH (notB (notB (0 <=. negate i31) &&* notB (let i22 = 1 + i31 in 0 <=. i22 &&* 0 <=. negate i22)) &&* (notB (notB (0 <=. negate i34) &&* notB (let i18 = (-1) + i34 in 0 <=. i18 &&* 0 <=. negate i18)) &&* notB (notB (let i20 = i12 + i34 in 0 <=. i20 &&* 0 <=. negate i20) &&* notB (let i21 = (-1) + (i12 + i34) in 0 <=. i21 &&* 0 <=. negate i21)))) 0 1 in ifH (0 <=. negate i12) i23 (ifH (let i19 = (-1) + i12 in 0 <=. i19 &&* 0 <=. negate i19) i23 1)]) + stranspose @[2, 0, 1] (sgather @[2, 2] (sreplicate @1 (sgather @[2, 2, 2] (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i28, i16, i33] -> [let i27 = ifH (notB (notB (0 <=. negate i28) &&* notB (let i20 = 1 + i28 in 0 <=. i20 &&* 0 <=. negate i20)) &&* notB (notB (let i17 = 2 * i33 in 0 <=. i17 &&* 0 <=. negate i17) &&* notB (let i18 = (-1) + 2 * i33 in 0 <=. i18 &&* 0 <=. negate i18))) 0 1 in ifH (0 <=. negate i16) i27 (ifH (let i22 = 1 + i16 in 0 <=. i22 &&* 0 <=. negate i22) i27 1)]))) (\\[i30, i29] -> [i29, i29, i30])))) (\\i1 -> [2 * i1, 0]))) (\\i2 -> [2 * i2]))) (\\i4 -> [2 * i4])), sconcrete (sreplicate [2,2,2] 0.0)]))) (\\[i46, i44, i43] -> [i46, i44, i43, ifH (notB (notB (let i35 = 2 * i46 in 0 <=. i35 &&* 0 <=. negate i35) &&* notB (let i36 = 2 * i46 in 0 <=. i36 &&* 0 <=. negate i36)) &&* (notB (notB (let i37 = 2 * i44 in 0 <=. i37 &&* 0 <=. negate i37) &&* notB (let i38 = 2 * i44 in 0 <=. i38 &&* 0 <=. negate i38)) &&* notB (notB (let i39 = 2 * i43 in 0 <=. i39 &&* 0 <=. negate i39) &&* notB (let i40 = 2 * i43 in 0 <=. i40 &&* 0 <=. negate i40)))) 0 1]))))"

testCNNOPP3b :: Assertion
testCNNOPP3b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dSame3) (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2, 2] (let t119 = str (sfromVector (fromList [stranspose @[0, 2, 1] (sgather @[2, 2] (stranspose @[1, 2, 3, 0] (sslice (SNat @1) (SNat @2) (str (sslice (SNat @0) (SNat @2) (stranspose @[0, 3, 2, 1] (sfromR u1)))))) (\\[i117, i118] -> [i117, i118 + i117, i118])), sconcrete (sreplicate [2,2,2] 0.0)])) !$ [0] in sfromVector (fromList [stranspose @[1, 2, 0] (sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (stranspose @[2, 0, 1] (sgather1 @2 (sreplicate @2 (sappend (sreplicate @1 (sappend (sreplicate @1 (t119 !$ [0, 0, 0])) (sreplicate @1 (t119 !$ [1, 1, 0])))) (sreplicate @1 (sappend (sreplicate @1 (t119 !$ [0, 0, 1])) (sreplicate @1 (t119 !$ [1, 1, 1])))) + sgather1 @2 (sreplicate @1 (sgather @[2, 2] (stranspose @[1, 2, 3, 4, 6, 5, 0] (sfromVector (fromList [stranspose @[1, 3, 4, 5, 0, 2] (sslice (SNat @1) (SNat @2) (stranspose @[5, 2, 0, 3, 4, 1] (sgather @[2, 2] (stranspose @[1, 2, 3, 0] (sslice (SNat @0) (SNat @2) (stranspose @[2, 3, 0, 1] (sgather @[2, 2] (sfromR u1) (\\[i120, i121] -> [i120 + i121]))))) (\\[i122, i123] -> [i122 + i123])))), sconcrete (sreplicate [2,2,2,2,2,2] 0.0)])) !$ [0, 0, 1, 1]) (\\[i124, i125] -> [i124, i125, let i126 = 1 + i125 ; i127 = 1 + i124 in ifH (notB (notB (0 <=. negate i125) &&* notB (0 <=. i126 &&* 0 <=. negate i126)) &&* notB (notB (0 <=. negate i124) &&* notB (0 <=. i127 &&* 0 <=. negate i127))) 0 1]))) (\\i128 -> [i128, i128]))) (\\i227 -> [2 * i227]))) (\\i230 -> [2 * i230]))) (\\i131 -> [2 * i131])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i132, i133, i134] -> [let i135 = 2 * i132 ; i136 = 2 * i132 ; i137 = 2 * i133 ; i138 = 2 * i133 ; i139 = 2 * i134 ; i140 = 2 * i134 in ifH (notB (notB (0 <=. i135 &&* 0 <=. negate i135) &&* notB (0 <=. i136 &&* 0 <=. negate i136)) &&* (notB (notB (0 <=. i137 &&* 0 <=. negate i137) &&* notB (0 <=. i138 &&* 0 <=. negate i138)) &&* notB (notB (0 <=. i139 &&* 0 <=. negate i139) &&* notB (0 <=. i140 &&* 0 <=. negate i140)))) 0 1, i132, i133, i134]))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2, 2] (let t119 = str (sfromVector (fromList [stranspose @[0, 2, 1] (sgather @[2, 2] (stranspose @[1, 2, 3, 0] (sslice (SNat @1) (SNat @2) (str (sslice (SNat @0) (SNat @2) (stranspose @[0, 3, 2, 1] (sfromR u1)))))) (\\[i117, i118] -> [i117, i118 + i117, i118])), sconcrete (sreplicate [2,2,2] 0.0)])) !$ [0] in sfromVector (fromList [stranspose @[1, 2, 0] (sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (stranspose @[2, 0, 1] (sgather1 @2 (sreplicate @2 (sappend (sreplicate @1 (sappend (sreplicate @1 (t119 !$ [0, 0, 0])) (sreplicate @1 (t119 !$ [1, 1, 0])))) (sreplicate @1 (sappend (sreplicate @1 (t119 !$ [0, 0, 1])) (sreplicate @1 (t119 !$ [1, 1, 1])))) + sgather1 @2 (sreplicate @1 (sgather @[2, 2] (stranspose @[3, 4, 1, 2, 6, 5, 0] (sfromVector (fromList [stranspose @[1, 3, 4, 5, 0, 2] (sslice (SNat @1) (SNat @2) (stranspose @[5, 2, 0, 3, 4, 1] (sgather @[2, 2] (stranspose @[1, 2, 3, 0] (sslice (SNat @0) (SNat @2) (stranspose @[2, 3, 0, 1] (sgather @[2, 2] (sfromR u1) (\\[i120, i121] -> [i120 + i121]))))) (\\[i122, i123] -> [i122 + i123])))), sconcrete (sreplicate [2,2,2,2,2,2] 0.0)])) !$ [1, 1, 0, 0]) (\\[i124, i125] -> [i124, i125, let i126 = 1 + i125 ; i127 = 1 + i124 in ifH (notB (notB (0 <=. negate i125) &&* notB (0 <=. i126 &&* 0 <=. negate i126)) &&* notB (notB (0 <=. negate i124) &&* notB (0 <=. i127 &&* 0 <=. negate i127))) 0 1]))) (\\i128 -> [i128, i128]))) (\\i129 -> [2 * i129]))) (\\i130 -> [2 * i130]))) (\\i131 -> [2 * i131])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i132, i133, i134] -> [let i135 = 2 * i132 ; i136 = 2 * i132 ; i137 = 2 * i133 ; i138 = 2 * i133 ; i139 = 2 * i134 ; i140 = 2 * i134 in ifH (notB (notB (0 <=. i135 &&* 0 <=. negate i135) &&* notB (0 <=. i136 &&* 0 <=. negate i136)) &&* (notB (notB (0 <=. i137 &&* 0 <=. negate i137) &&* notB (0 <=. i138 &&* 0 <=. negate i138)) &&* notB (notB (0 <=. i139 &&* 0 <=. negate i139) &&* notB (0 <=. i140 &&* 0 <=. negate i140)))) 0 1, i132, i133, i134]))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (let u151 = sscatter @[2, 2, 2] (ssum @2 (stranspose @[2, 0, 1] (sfromR dret))) (\\[i142, i143, i144] -> [let i145 = 2 * i142 ; i146 = 2 * i142 ; i147 = 2 * i143 ; i148 = 2 * i143 ; i149 = 2 * i144 ; i150 = 2 * i144 in ifH (notB (notB (0 <=. i145 &&* 0 <=. negate i145) &&* notB (0 <=. i146 &&* 0 <=. negate i146)) &&* (notB (notB (0 <=. i147 &&* 0 <=. negate i147) &&* notB (0 <=. i148 &&* 0 <=. negate i148)) &&* notB (notB (0 <=. i149 &&* 0 <=. negate i149) &&* notB (0 <=. i150 &&* 0 <=. negate i150)))) 0 1, i142, i143, i144]) ; m155 = ssum @2 (sscatter1 @2 (stranspose @[1, 2, 0] (sscatter1 @2 (stranspose @[2, 1, 0] (sscatter1 @2 (stranspose @[2, 0, 1] (u151 !$ [0])) (\\i152 -> [2 * i152]))) (\\i153 -> [2 * i153]))) (\\i154 -> [2 * i154])) ; w161 = stranspose @[6, 2, 3, 0, 1, 5, 4] (soneHot (sscatter @[2, 2] (ssum @1 (sscatter1 @2 m155 (\\i156 -> [i156, i156]))) (\\[i157, i158] -> [i157, i158, let i159 = 1 + i158 ; i160 = 1 + i157 in ifH (notB (notB (0 <=. negate i158) &&* notB (0 <=. i159 &&* 0 <=. negate i159)) &&* notB (notB (0 <=. negate i157) &&* notB (0 <=. i160 &&* 0 <=. negate i160))) 0 1])) [1, 1, 0, 0]) ; u166 = str (soneHot (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) m155)))) [0, 0, 0] + (soneHot (ssum @1 (sslice (SNat @1) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) m155)))) [1, 1, 0] + (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @1) (SNat @1) m155)))) [0, 0, 1] + soneHot (ssum @1 (sslice (SNat @1) (SNat @1) (ssum @1 (sslice (SNat @1) (SNat @1) m155)))) [1, 1, 1]))) [0]) in stranspose @[0, 3, 2, 1] (sappend (sconcrete (sfromListLinear [0,3,3,3] [])) (sappend (str (sappend (sconcrete (sreplicate [1,2,3,3] 0.0)) (sappend (stranspose @[3, 0, 1, 2] (sscatter @[2, 2] (stranspose @[0, 2, 1] (u166 !$ [0])) (\\[i167, i168] -> [i167, i168 + i167, i168]))) (sconcrete (sfromListLinear [0,2,3,3] []))))) (sconcrete (sreplicate [1,3,3,3] 0.0)))) + sscatter @[2, 2] (stranspose @[2, 3, 0, 1] (sappend (sconcrete (sfromListLinear [0,3,2,2,3] [])) (sappend (stranspose @[3, 0, 1, 2] (sscatter @[2, 2] (stranspose @[2, 5, 1, 3, 4, 0] (sappend (sconcrete (sreplicate [1,2,2,2,2,2] 0.0)) (sappend (stranspose @[4, 0, 5, 1, 2, 3] (w161 !$ [0])) (sconcrete (sfromListLinear [0,2,2,2,2,2] []))))) (\\[i162, i163] -> [i162 + i163]))) (sconcrete (sreplicate [1,3,2,2,3] 0.0))))) (\\[i164, i165] -> [i164 + i165]))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (let m155 = ssum @2 (sscatter1 @2 (stranspose @[1, 2, 0] (sscatter1 @2 (stranspose @[2, 1, 0] (sscatter1 @2 (sscatter @[2, 2, 2] (ssum @2 (stranspose @[2, 0, 1] (sfromR dret))) (\\[i142, i143, i144] -> [let i145 = 2 * i142 ; i146 = 2 * i142 ; i147 = 2 * i143 ; i148 = 2 * i143 ; i149 = 2 * i144 ; i150 = 2 * i144 in ifH (notB (notB (0 <=. i145 &&* 0 <=. negate i145) &&* notB (0 <=. i146 &&* 0 <=. negate i146)) &&* (notB (notB (0 <=. i147 &&* 0 <=. negate i147) &&* notB (0 <=. i148 &&* 0 <=. negate i148)) &&* notB (notB (0 <=. i149 &&* 0 <=. negate i149) &&* notB (0 <=. i150 &&* 0 <=. negate i150)))) 0 1, i144, i142, i143]) !$ [0]) (\\i152 -> [2 * i152]))) (\\i153 -> [2 * i153]))) (\\i154 -> [2 * i154])) in sappend (stranspose @[1, 3, 2, 0] (sappend (sconcrete (sreplicate [1,2,3,3] 0.0)) (stranspose @[3, 0, 1, 2] (sscatter @[2, 2] (stranspose @[1, 0, 3, 2] (soneHot (soneHot (m155 !$ [0, 0]) [0, 0, 0] + (soneHot (m155 !$ [0, 1]) [1, 1, 0] + (soneHot (m155 !$ [1, 0]) [0, 0, 1] + soneHot (m155 !$ [1, 1]) [1, 1, 1]))) [0]) !$ [0]) (\\[i167, i168] -> [i167, i168 + i167, i168]))))) (sconcrete (sreplicate [1,3,3,3] 0.0)) + sscatter @[2, 2] (stranspose @[2, 3, 0, 1] (sappend (stranspose @[3, 0, 1, 2] (sscatter @[2, 2] (stranspose @[2, 5, 1, 3, 4, 0] (sappend (sconcrete (sreplicate [1,2,2,2,2,2] 0.0)) (stranspose @[6, 5, 2, 4, 3, 0, 1] (soneHot (sscatter @[2, 2] (sscatter1 @2 m155 (\\i156 -> [i156, i156]) !$ [0]) (\\[i157, i158] -> [i157, i158, let i159 = 1 + i158 ; i160 = 1 + i157 in ifH (notB (notB (0 <=. negate i158) &&* notB (0 <=. i159 &&* 0 <=. negate i159)) &&* notB (notB (0 <=. negate i157) &&* notB (0 <=. i160 &&* 0 <=. negate i160))) 0 1])) [1, 1, 0, 0]) !$ [0]))) (\\[i162, i163] -> [i162 + i163]))) (sconcrete (sreplicate [1,3,2,2,3] 0.0)))) (\\[i164, i165] -> [i164 + i165]))"

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
      in rindex @_ @0 arrAt [0, iBw, iImg, iBh] + rindex arrAt [iImg, 1, iBw + 1, iBh]
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
rmaximum3 t0 = tlet t0 $ \t -> rindex t [0, 0, 0, 0]

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
    @?= "rfromS (str (let w86 = stranspose @[5, 6, 7, 8, 0, 1, 2, 3, 4] (sfromVector (fromList [stranspose @[2, 3, 4, 0, 5, 6, 7, 1] (sgather @[2, 2] (stranspose @[6, 0, 3, 1, 4, 5, 2] (sgather @[2, 2, 2] (stranspose @[4, 1, 3, 0, 2] (sgather @[2, 2] (stranspose @[3, 0, 4, 1, 2] (sgather @[2, 2] (sconcrete (sreplicate [2,3,3,3] 7.0)) (\\[i61, i64] -> [i61 + i64]))) (\\[i67, i69] -> [2 + (negate i69 + i67), i69]))) (\\[i71, i73, i76] -> [i71 * i73 + i76]))) (\\[i31, i8] -> [2 * i31 + i8])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0] in sappend (sreplicate @1 (stranspose @[0, 2, 1] w86 !$ [1, 0])) (sreplicate @1 (stranspose @[0, 2, 1] w86 !$ [1, 1]))))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (let w28 = sgather @[2, 2, 2, 2, 2, 2, 2, 2] (stranspose @[1, 2, 3, 4, 5, 6, 7, 8, 0] (sfromVector (fromList [stranspose @[2, 3, 4, 0, 5, 6, 7, 1] (sgather @[2, 2] (stranspose @[6, 0, 3, 1, 4, 5, 2] (sgather @[2, 2, 2] (stranspose @[3, 0, 2, 1] (sgather @[2, 2] (stranspose @[0, 2, 1] (sgather @[2, 2] (sconcrete (sreplicate [2,3,3,3] 7.0)) (\\[i41, i5] -> [i41 + i5]))) (\\[i40, i6] -> [i40, 2 + (negate i40 + i6)]))) (\\[i45, i35, i7] -> [i45 * i35 + i7]))) (\\[i31, i8] -> [2 * i31 + i8])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)]))) (\\[i43, i37, i33, i30, i23, i20, i18, i17] -> [i43, i37, i33, i30, i23, i20, i18, i17, ifH (notB (notB (let i9 = 1 + (i37 + i23) in 0 <=. i9 &&* 0 <=. negate i9) &&* notB (let i10 = i37 + i23 in 0 <=. i10 &&* 0 <=. negate i10)) &&* (notB (notB (let i11 = 2 + (negate i37 + i20) in 0 <=. i11 &&* 0 <=. negate i11) &&* notB (let i12 = 1 + (negate i37 + i20) in 0 <=. i12 &&* 0 <=. negate i12)) &&* (notB (notB (let i13 = i43 * i33 + i18 in 0 <=. i13 &&* 0 <=. negate i13) &&* notB (let i14 = (-1) + (i43 * i33 + i18) in 0 <=. i14 &&* 0 <=. negate i14)) &&* notB (notB (let i15 = 2 * i30 + i17 in 0 <=. i15 &&* 0 <=. negate i15) &&* notB (let i16 = (-1) + (2 * i30 + i17) in 0 <=. i16 &&* 0 <=. negate i16))))) 0 1]) in stranspose @[4, 5, 6, 7, 0, 1, 2, 3] w28 !$ [0, 0, 0, 0])"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP4b :: Assertion
testCNNOPP4b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded4 (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (str (let w129 = stranspose @[5, 6, 7, 8, 0, 1, 2, 3, 4] (sfromVector (fromList [stranspose @[2, 3, 4, 0, 5, 6, 7, 1] (sgather @[2, 2] (stranspose @[4, 7, 0, 3, 1, 5, 6, 2] (sgather @[2, 2, 2] (stranspose @[3, 4, 7, 1, 5, 6, 0, 2] (sgather @[2, 2] (stranspose @[6, 0, 7, 4, 3, 2, 1, 5] (sgather @[2, 2, 2, 2, 2] (stranspose @[0, 2, 1] (sfromR u1)) (\\[i223, i225, i226, i227, i228] -> [1 + sconcrete (sfromListLinear [2,2] [0,1,1,2]) `index0` [i223, i225]]))) (\\[i234, i237] -> [2 + (negate i237 + i234), i237]))) (\\[i240, i242, i245] -> [i240, i242, i240 * i242 + i245]))) (\\[i127, i128] -> [i127, 2 * i127 + i128])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0] in sappend (sreplicate @1 (stranspose @[0, 2, 1] w129 !$ [1, 0])) (sreplicate @1 (stranspose @[0, 2, 1] w129 !$ [1, 1]))))"
      -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (str (let m116 = str (sreplicate @2 (siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) ; w129 = stranspose @[5, 6, 7, 8, 0, 1, 2, 3, 4] (sfromVector (fromList [stranspose @[2, 3, 4, 0, 5, 6, 7, 1] (sgather @[2, 2] (stranspose @[4, 7, 0, 3, 1, 5, 6, 2] (sgather @[2, 2, 2] (stranspose @[3, 4, 7, 1, 5, 6, 0, 2] (sgather @[2, 2] (stranspose @[6, 0, 7, 4, 3, 2, 1, 5] (sgather @[2, 2, 2, 2, 2] (stranspose @[0, 2, 1] (sfromR u1)) (\\[i117, i118, i119, i120, i121] -> [1 + kfromS (m116 !$ [i117, i118])]))) (\\[i122, i123] -> [2 + (negate i123 + i122), i123]))) (\\[i124, i125, i126] -> [i124, i125, i124 * i125 + i126]))) (\\[i127, i128] -> [i127, 2 * i127 + i128])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0] in sappend (sreplicate @1 (stranspose @[0, 2, 1] w129 !$ [1, 0])) (sreplicate @1 (stranspose @[0, 2, 1] w129 !$ [1, 1]))))"
      -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (stranspose @[0, 2, 1] (let m116 = str (sreplicate @2 (siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) in sscatter @[2, 2, 2, 2, 2] (stranspose @[1, 6, 5, 4, 3, 7, 0, 2] (sscatter @[2, 2] (stranspose @[6, 3, 7, 0, 1, 4, 5, 2] (sscatter @[2, 2, 2] (stranspose @[2, 4, 7, 3, 0, 5, 6, 1] (sscatter @[2, 2] (stranspose @[3, 7, 0, 1, 2, 4, 5, 6] (stranspose @[4, 5, 6, 7, 8, 0, 1, 2, 3] (soneHot (stranspose @[0, 2, 1] (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (str (sfromR dret)))) [1, 0]) + stranspose @[0, 2, 1] (soneHot (ssum @1 (sslice (SNat @1) (SNat @1) (str (sfromR dret)))) [1, 1])) [0, 0, 0, 0]) !$ [0])) (\\[i132, i133] -> [i132, 2 * i132 + i133]))) (\\[i134, i135, i136] -> [i134, i135, i134 * i135 + i136]))) (\\[i137, i138] -> [2 + (negate i138 + i137), i138]))) (\\[i139, i140, i141, i142, i143] -> [1 + kfromS (m116 !$ [i139, i140])])))"
      -- TODO: was once "\\dret u1 -> rfromS (sconcrete (sreplicate [3,3,3,3] 0.0))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (stranspose @[0, 2, 1] (sscatter @[2, 2, 2, 2, 2] (stranspose @[1, 6, 5, 4, 3, 7, 0, 2] (sscatter @[2, 2] (stranspose @[6, 3, 7, 0, 1, 4, 5, 2] (sscatter @[2, 2, 2] (stranspose @[2, 4, 7, 3, 0, 5, 6, 1] (sscatter @[2, 2] (stranspose @[4, 8, 3, 5, 6, 7, 0, 1, 2] (soneHot (stranspose @[0, 2, 1] (soneHot (str (sfromR dret) !$ [0]) [1, 0]) + stranspose @[0, 2, 1] (soneHot (str (sfromR dret) !$ [1]) [1, 1])) [0, 0, 0, 0]) !$ [0]) (\\[i132, i133] -> [i132, 2 * i132 + i133]))) (\\[i134, i135, i136] -> [i134, i135, i134 * i135 + i136]))) (\\[i137, i138] -> [2 + (negate i138 + i137), i138]))) (\\[i139, i140, i141, i142, i143] -> [1 + sconcrete (sfromListLinear [2,2] [0,1,1,2]) `index0` [i139, i140]])))"
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
    @?= "rfromS (sreplicate @1 (sreplicate @1 (sgather @[2, 2] (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i15, i4] -> [let i14 = ifH (notB (0 <=. negate i15) &&* notB (let i10 = (-4) + i15 in 0 <=. i10 &&* 0 <=. negate i10)) 1 0 in ifH (0 <=. negate i4) i14 (ifH (let i12 = (-4) + i4 in 0 <=. i12 &&* 0 <=. negate i12) i14 1)]))))"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP5b :: Assertion
testCNNOPP5b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent conv2dSame4 (FTKR [5, 5, 5, 5] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (sappend (sreplicate @1 (sappend (sreplicate @1 (sfromR u1 !$ [0, 0, 0, 0])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (let m22 = sslice (SNat @0) (SNat @2) (str (sslice (SNat @0) (SNat @2) (sfromR u1 !$ [0, 0]))) in sappend (sreplicate @1 (sappend (sreplicate @1 (m22 !$ [0, 0])) (sconcrete (sfromListLinear [1] [0.0])))) (sconcrete (sreplicate [1,2] 0.0))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (sappend (sconcrete (sfromListLinear [0,5] [])) (sappend (str (sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (ssum @1 (sslice (SNat @0) (SNat @1) (str (ssum @1 (ssum @1 (sfromR dret)))))))) [0, 0]) (sconcrete (sreplicate [3,2] 0.0))))) (sconcrete (sreplicate [3,5] 0.0)))) [0, 0])"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (sappend (str (sappend (soneHot (sfromR dret !$ [0, 0, 0, 0]) [0, 0]) (sconcrete (sreplicate [3,2] 0.0)))) (sconcrete (sreplicate [3,5] 0.0))) [0, 0])"
      -- TODO: was "\\dret u1 -> rfromS (soneHot (sfromR dret !$ [0, 0, 0, 0]) [0, 0, 0, 0])"

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
      in rindex @_ @0 arrAt [0, 0, 0, 0]
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
    @?= "rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2, 2] (sfromVector (fromList [stranspose @[1, 2, 0] (sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (stranspose @[2, 0, 1] (sgather1 @2 (stranspose @[1, 2, 0] (sreplicate @2 (sreplicate @2 (sgather1 @2 (str (sfromVector (fromList [str (sgather1 @2 (str (sgather1 @2 (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\i54 -> [2 * i54, 2 * i54, 2 * i54]))) (\\i12 -> [2 * i12])), sconcrete (sreplicate [2,2] 0.0)])) !$ [0]) (\\i25 -> [ifH (notB (let i23 = 2 * i25 in 0 <=. i23 &&* 0 <=. negate i23) &&* notB (let i24 = 2 * i25 in 0 <=. i24 &&* 0 <=. negate i24)) 1 0, i25]))))) (\\i59 -> [2 * i59]))) (\\i62 -> [2 * i62]))) (\\i4 -> [2 * i4])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i39, i37, i36] -> [ifH (notB (notB (let i28 = 2 * i39 in 0 <=. i28 &&* 0 <=. negate i28) &&* notB (let i29 = 2 * i39 in 0 <=. i29 &&* 0 <=. negate i29)) &&* (notB (notB (let i30 = 2 * i37 in 0 <=. i30 &&* 0 <=. negate i30) &&* notB (let i31 = 2 * i37 in 0 <=. i31 &&* 0 <=. negate i31)) &&* notB (notB (let i32 = 2 * i36 in 0 <=. i32 &&* 0 <=. negate i32) &&* notB (let i33 = 2 * i36 in 0 <=. i33 &&* 0 <=. negate i33)))) 0 1, i39, i37, i36]))))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2, 2] (stranspose @[1, 2, 3, 0] (sfromVector (fromList [stranspose @[1, 2, 0] (sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (str (sgather1 @2 (sreplicate @2 (str (sreplicate @2 (sgather @[2, 2] (stranspose @[1, 2, 0] (sfromVector (fromList [str (sgather1 @2 (str (sgather1 @2 (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\i9 -> [2 * i9, 2 * i9, 2 * i9]))) (\\i12 -> [2 * i12])), sconcrete (sreplicate [2,2] 0.0)]))) (\\[i26, i25] -> [i26, i25, ifH (notB (notB (let i17 = 2 * i26 in 0 <=. i17 &&* 0 <=. negate i17) &&* notB (let i18 = 2 * i26 in 0 <=. i18 &&* 0 <=. negate i18)) &&* (notB (notB (let i19 = 2 * i26 in 0 <=. i19 &&* 0 <=. negate i19) &&* notB (let i20 = 2 * i26 in 0 <=. i20 &&* 0 <=. negate i20)) &&* (notB (notB (let i21 = 2 * i26 in 0 <=. i21 &&* 0 <=. negate i21) &&* notB (let i22 = 2 * i26 in 0 <=. i22 &&* 0 <=. negate i22)) &&* notB (notB (let i23 = 2 * i25 in 0 <=. i23 &&* 0 <=. negate i23) &&* notB (let i24 = 2 * i25 in 0 <=. i24 &&* 0 <=. negate i24))))) 0 1]))))) (\\i1 -> [2 * i1, 0]))) (\\i2 -> [2 * i2]))) (\\i4 -> [2 * i4])), sconcrete (sreplicate [2,2,2] 0.0)]))) (\\[i39, i37, i36] -> [i39, i37, i36, ifH (notB (notB (let i28 = 2 * i39 in 0 <=. i28 &&* 0 <=. negate i28) &&* notB (let i29 = 2 * i39 in 0 <=. i29 &&* 0 <=. negate i29)) &&* (notB (notB (let i30 = 2 * i37 in 0 <=. i30 &&* 0 <=. negate i30) &&* notB (let i31 = 2 * i37 in 0 <=. i31 &&* 0 <=. negate i31)) &&* notB (notB (let i32 = 2 * i36 in 0 <=. i32 &&* 0 <=. negate i32) &&* notB (let i33 = 2 * i36 in 0 <=. i33 &&* 0 <=. negate i33)))) 0 1]))))"

testCNNOPP6b :: Assertion
testCNNOPP6b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dSame3z) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2, 2] (sfromVector (fromList [stranspose @[1, 2, 0] (sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (stranspose @[2, 0, 1] (sgather1 @2 (stranspose @[1, 2, 0] (sreplicate @2 (sreplicate @2 (sgather1 @2 (str (sfromVector (fromList [str (sgather1 @2 (str (sgather1 @2 (stranspose @[2, 1, 0] (sfromR u1)) (\\i120 -> [2 * i120, 2 * i120, 2 * i120]))) (\\i64 -> [2 * i64])), sconcrete (sreplicate [2,2] 0.0)])) !$ [0]) (\\i111 -> [let i66 = 2 * i111 ; i67 = 2 * i111 in ifH (notB (0 <=. i66 &&* 0 <=. negate i66) &&* notB (0 <=. i67 &&* 0 <=. negate i67)) 1 0, i111]))))) (\\i125 -> [2 * i125]))) (\\i128 -> [2 * i128]))) (\\i70 -> [2 * i70])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i71, i72, i73] -> [let i74 = 2 * i71 ; i75 = 2 * i71 ; i76 = 2 * i72 ; i77 = 2 * i72 ; i78 = 2 * i73 ; i79 = 2 * i73 in ifH (notB (notB (0 <=. i74 &&* 0 <=. negate i74) &&* notB (0 <=. i75 &&* 0 <=. negate i75)) &&* (notB (notB (0 <=. i76 &&* 0 <=. negate i76) &&* notB (0 <=. i77 &&* 0 <=. negate i77)) &&* notB (notB (0 <=. i78 &&* 0 <=. negate i78) &&* notB (0 <=. i79 &&* 0 <=. negate i79)))) 0 1, i71, i72, i73]))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2, 2] (sfromVector (fromList [stranspose @[1, 2, 0] (sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (stranspose @[2, 0, 1] (sgather1 @2 (stranspose @[1, 2, 0] (sreplicate @2 (sreplicate @2 (sgather1 @2 (str (sfromVector (fromList [str (sgather1 @2 (str (sgather1 @2 (stranspose @[2, 1, 0] (sfromR u1)) (\\i63 -> [2 * i63, 2 * i63, 2 * i63]))) (\\i64 -> [2 * i64])), sconcrete (sreplicate [2,2] 0.0)])) !$ [0]) (\\i65 -> [let i66 = 2 * i65 ; i67 = 2 * i65 in ifH (notB (0 <=. i66 &&* 0 <=. negate i66) &&* notB (0 <=. i67 &&* 0 <=. negate i67)) 1 0, i65]))))) (\\i68 -> [2 * i68]))) (\\i69 -> [2 * i69]))) (\\i70 -> [2 * i70])), sconcrete (sreplicate [2,2,2] 0.0)])) (\\[i71, i72, i73] -> [let i74 = 2 * i71 ; i75 = 2 * i71 ; i76 = 2 * i72 ; i77 = 2 * i72 ; i78 = 2 * i73 ; i79 = 2 * i73 in ifH (notB (notB (0 <=. i74 &&* 0 <=. negate i74) &&* notB (0 <=. i75 &&* 0 <=. negate i75)) &&* (notB (notB (0 <=. i76 &&* 0 <=. negate i76) &&* notB (0 <=. i77 &&* 0 <=. negate i77)) &&* notB (notB (0 <=. i78 &&* 0 <=. negate i78) &&* notB (0 <=. i79 &&* 0 <=. negate i79)))) 0 1, i71, i72, i73]))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (stranspose @[2, 1, 0] (sscatter1 @2 (str (sscatter1 @2 (str (str (soneHot (sscatter1 @2 (ssum @2 (ssum @2 (stranspose @[2, 0, 1] (sscatter1 @2 (stranspose @[1, 2, 0] (sscatter1 @2 (stranspose @[2, 1, 0] (sscatter1 @2 (stranspose @[2, 0, 1] (sscatter @[2, 2, 2] (ssum @2 (stranspose @[2, 0, 1] (sfromR dret))) (\\[i81, i82, i83] -> [let i84 = 2 * i81 ; i85 = 2 * i81 ; i86 = 2 * i82 ; i87 = 2 * i82 ; i88 = 2 * i83 ; i89 = 2 * i83 in ifH (notB (notB (0 <=. i84 &&* 0 <=. negate i84) &&* notB (0 <=. i85 &&* 0 <=. negate i85)) &&* (notB (notB (0 <=. i86 &&* 0 <=. negate i86) &&* notB (0 <=. i87 &&* 0 <=. negate i87)) &&* notB (notB (0 <=. i88 &&* 0 <=. negate i88) &&* notB (0 <=. i89 &&* 0 <=. negate i89)))) 0 1, i81, i82, i83]) !$ [0])) (\\i91 -> [2 * i91]))) (\\i92 -> [2 * i92]))) (\\i93 -> [2 * i93]))))) (\\i94 -> [let i95 = 2 * i94 ; i96 = 2 * i94 in ifH (notB (0 <=. i95 &&* 0 <=. negate i95) &&* notB (0 <=. i96 &&* 0 <=. negate i96)) 1 0, i94])) [0]) !$ [0])) (\\i98 -> [2 * i98]))) (\\i99 -> [2 * i99, 2 * i99, 2 * i99])))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter1 @2 (str (sscatter1 @2 (stranspose @[1, 2, 0] (soneHot (sscatter1 @2 (ssum @2 (ssum @2 (stranspose @[2, 0, 1] (sscatter1 @2 (stranspose @[1, 2, 0] (sscatter1 @2 (stranspose @[2, 1, 0] (sscatter1 @2 (sscatter @[2, 2, 2] (ssum @2 (stranspose @[2, 0, 1] (sfromR dret))) (\\[i81, i82, i83] -> [let i84 = 2 * i81 ; i85 = 2 * i81 ; i86 = 2 * i82 ; i87 = 2 * i82 ; i88 = 2 * i83 ; i89 = 2 * i83 in ifH (notB (notB (0 <=. i84 &&* 0 <=. negate i84) &&* notB (0 <=. i85 &&* 0 <=. negate i85)) &&* (notB (notB (0 <=. i86 &&* 0 <=. negate i86) &&* notB (0 <=. i87 &&* 0 <=. negate i87)) &&* notB (notB (0 <=. i88 &&* 0 <=. negate i88) &&* notB (0 <=. i89 &&* 0 <=. negate i89)))) 0 1, i83, i81, i82]) !$ [0]) (\\i91 -> [2 * i91]))) (\\i92 -> [2 * i92]))) (\\i93 -> [2 * i93]))))) (\\i94 -> [let i95 = 2 * i94 ; i96 = 2 * i94 in ifH (notB (0 <=. i95 &&* 0 <=. negate i95) &&* notB (0 <=. i96 &&* 0 <=. negate i96)) 1 0, i94])) [0]) !$ [0]) (\\i98 -> [2 * i98]))) (\\i99 -> [2 * i99, 2 * i99, 2 * i99]))"
      -- TODO: was once "\\dret u1 -> rfromS (soneHot (ssum0 (stranspose @[0,1,3,2] (sfromR dret) !$ [0, 0, 0])) [0, 0, 0, 0])"

conv2dSame3z
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r)
conv2dSame3z arrA =
  let shB = [2, 2, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez3 shB arrA [iImg, iImg, iImg, iBw]
      in rindex @_ @0 arrAt [iBh, iBw, iImg, iBh]
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
    @?= "rfromS (sgather @[2, 2, 2, 2] (sfromVector (fromList [stranspose @[1, 2, 3, 0] (sgather1 @2 (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (stranspose @[2, 3, 0, 1] (sgather1 @2 (sreplicate @2 (sreplicate @2 (sgather @[2, 2] (sfromVector (fromList [str (sgather1 @2 (str (sgather1 @2 (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\i57 -> [2 * i57, 2 * i57, 2 * i57]))) (\\i11 -> [2 * i11])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i26, i25] -> [ifH (notB (notB (let i17 = 2 * i26 in 0 <=. i17 &&* 0 <=. negate i17) &&* notB (let i18 = 2 * i26 in 0 <=. i18 &&* 0 <=. negate i18)) &&* (notB (notB (let i19 = 2 * i26 in 0 <=. i19 &&* 0 <=. negate i19) &&* notB (let i20 = 2 * i26 in 0 <=. i20 &&* 0 <=. negate i20)) &&* (notB (notB (let i21 = 2 * i26 in 0 <=. i21 &&* 0 <=. negate i21) &&* notB (let i22 = 2 * i26 in 0 <=. i22 &&* 0 <=. negate i22)) &&* notB (notB (let i23 = 2 * i25 in 0 <=. i23 &&* 0 <=. negate i23) &&* notB (let i24 = 2 * i25 in 0 <=. i24 &&* 0 <=. negate i24))))) 0 1, i26, i25])))) (\\i61 -> [2 * i61]))) (\\[i64, i65] -> [2 * i65, 2 * i64]))) (\\i4 -> [2 * i4])), sconcrete (sreplicate [2,2,2,2] 0.0)])) (\\[i44, i41, i39, i38] -> [ifH (notB (notB (let i28 = 2 * i39 in 0 <=. i28 &&* 0 <=. negate i28) &&* notB (let i29 = 2 * i39 in 0 <=. i29 &&* 0 <=. negate i29)) &&* (notB (notB (let i30 = 2 * i44 in 0 <=. i30 &&* 0 <=. negate i30) &&* notB (let i31 = 2 * i44 in 0 <=. i31 &&* 0 <=. negate i31)) &&* (notB (notB (let i32 = 2 * i41 in 0 <=. i32 &&* 0 <=. negate i32) &&* notB (let i33 = 2 * i41 in 0 <=. i33 &&* 0 <=. negate i33)) &&* notB (notB (let i34 = 2 * i38 in 0 <=. i34 &&* 0 <=. negate i34) &&* notB (let i35 = 2 * i38 in 0 <=. i35 &&* 0 <=. negate i35))))) 0 1, i44, i41, i39, i38]))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromS (sgather @[2, 2, 2, 2] (stranspose @[1, 2, 3, 4, 0] (sfromVector (fromList [stranspose @[1, 2, 3, 0] (sgather1 @2 (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (stranspose @[1, 2, 0] (sgather1 @2 (sreplicate @2 (stranspose @[1, 2, 0] (sreplicate @2 (sgather @[2, 2] (stranspose @[1, 2, 0] (sfromVector (fromList [str (sgather1 @2 (str (sgather1 @2 (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\i9 -> [2 * i9, 2 * i9, 2 * i9]))) (\\i11 -> [2 * i11])), sconcrete (sreplicate [2,2] 0.0)]))) (\\[i26, i25] -> [i26, i25, ifH (notB (notB (let i17 = 2 * i26 in 0 <=. i17 &&* 0 <=. negate i17) &&* notB (let i18 = 2 * i26 in 0 <=. i18 &&* 0 <=. negate i18)) &&* (notB (notB (let i19 = 2 * i26 in 0 <=. i19 &&* 0 <=. negate i19) &&* notB (let i20 = 2 * i26 in 0 <=. i20 &&* 0 <=. negate i20)) &&* (notB (notB (let i21 = 2 * i26 in 0 <=. i21 &&* 0 <=. negate i21) &&* notB (let i22 = 2 * i26 in 0 <=. i22 &&* 0 <=. negate i22)) &&* notB (notB (let i23 = 2 * i25 in 0 <=. i23 &&* 0 <=. negate i23) &&* notB (let i24 = 2 * i25 in 0 <=. i24 &&* 0 <=. negate i24))))) 0 1]))))) (\\i1 -> [2 * i1]))) (\\[i43, i3] -> [2 * i3, 2 * i43]))) (\\i4 -> [2 * i4])), sconcrete (sreplicate [2,2,2,2] 0.0)]))) (\\[i44, i41, i39, i38] -> [i44, i41, i39, i38, ifH (notB (notB (let i28 = 2 * i39 in 0 <=. i28 &&* 0 <=. negate i28) &&* notB (let i29 = 2 * i39 in 0 <=. i29 &&* 0 <=. negate i29)) &&* (notB (notB (let i30 = 2 * i44 in 0 <=. i30 &&* 0 <=. negate i30) &&* notB (let i31 = 2 * i44 in 0 <=. i31 &&* 0 <=. negate i31)) &&* (notB (notB (let i32 = 2 * i41 in 0 <=. i32 &&* 0 <=. negate i32) &&* notB (let i33 = 2 * i41 in 0 <=. i33 &&* 0 <=. negate i33)) &&* notB (notB (let i34 = 2 * i38 in 0 <=. i34 &&* 0 <=. negate i34) &&* notB (let i35 = 2 * i38 in 0 <=. i35 &&* 0 <=. negate i35))))) 0 1]))"

testCNNOPP7b :: Assertion
testCNNOPP7b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3y . conv2dSame3y) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (sgather @[2, 2, 2, 2] (sfromVector (fromList [stranspose @[1, 2, 3, 0] (sgather1 @2 (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (stranspose @[2, 3, 0, 1] (sgather1 @2 (sreplicate @2 (sreplicate @2 (sgather @[2, 2] (sfromVector (fromList [str (sgather1 @2 (str (sgather1 @2 (stranspose @[2, 1, 0] (sfromR u1)) (\\i136 -> [2 * i136, 2 * i136, 2 * i136]))) (\\i67 -> [2 * i67])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i139, i138] -> [let i70 = 2 * i139 ; i71 = 2 * i139 ; i72 = 2 * i139 ; i73 = 2 * i139 ; i74 = 2 * i139 ; i75 = 2 * i139 ; i76 = 2 * i138 ; i77 = 2 * i138 in ifH (notB (notB (0 <=. i70 &&* 0 <=. negate i70) &&* notB (0 <=. i71 &&* 0 <=. negate i71)) &&* (notB (notB (0 <=. i72 &&* 0 <=. negate i72) &&* notB (0 <=. i73 &&* 0 <=. negate i73)) &&* (notB (notB (0 <=. i74 &&* 0 <=. negate i74) &&* notB (0 <=. i75 &&* 0 <=. negate i75)) &&* notB (notB (0 <=. i76 &&* 0 <=. negate i76) &&* notB (0 <=. i77 &&* 0 <=. negate i77))))) 0 1, i139, i138])))) (\\i144 -> [2 * i144]))) (\\[i147, i148] -> [2 * i148, 2 * i147]))) (\\i81 -> [2 * i81])), sconcrete (sreplicate [2,2,2,2] 0.0)])) (\\[i82, i83, i84, i85] -> [let i86 = 2 * i84 ; i87 = 2 * i84 ; i88 = 2 * i82 ; i89 = 2 * i82 ; i90 = 2 * i83 ; i91 = 2 * i83 ; i92 = 2 * i85 ; i93 = 2 * i85 in ifH (notB (notB (0 <=. i86 &&* 0 <=. negate i86) &&* notB (0 <=. i87 &&* 0 <=. negate i87)) &&* (notB (notB (0 <=. i88 &&* 0 <=. negate i88) &&* notB (0 <=. i89 &&* 0 <=. negate i89)) &&* (notB (notB (0 <=. i90 &&* 0 <=. negate i90) &&* notB (0 <=. i91 &&* 0 <=. negate i91)) &&* notB (notB (0 <=. i92 &&* 0 <=. negate i92) &&* notB (0 <=. i93 &&* 0 <=. negate i93))))) 0 1, i82, i83, i84, i85]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sgather @[2, 2, 2, 2] (sfromVector (fromList [stranspose @[1, 2, 3, 0] (sgather1 @2 (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (stranspose @[2, 3, 0, 1] (sgather1 @2 (sreplicate @2 (sreplicate @2 (sgather @[2, 2] (sfromVector (fromList [str (sgather1 @2 (str (sgather1 @2 (stranspose @[2, 1, 0] (sfromR u1)) (\\i66 -> [2 * i66, 2 * i66, 2 * i66]))) (\\i67 -> [2 * i67])), sconcrete (sreplicate [2,2] 0.0)])) (\\[i68, i69] -> [let i70 = 2 * i68 ; i71 = 2 * i68 ; i72 = 2 * i68 ; i73 = 2 * i68 ; i74 = 2 * i68 ; i75 = 2 * i68 ; i76 = 2 * i69 ; i77 = 2 * i69 in ifH (notB (notB (0 <=. i70 &&* 0 <=. negate i70) &&* notB (0 <=. i71 &&* 0 <=. negate i71)) &&* (notB (notB (0 <=. i72 &&* 0 <=. negate i72) &&* notB (0 <=. i73 &&* 0 <=. negate i73)) &&* (notB (notB (0 <=. i74 &&* 0 <=. negate i74) &&* notB (0 <=. i75 &&* 0 <=. negate i75)) &&* notB (notB (0 <=. i76 &&* 0 <=. negate i76) &&* notB (0 <=. i77 &&* 0 <=. negate i77))))) 0 1, i68, i69])))) (\\i78 -> [2 * i78]))) (\\[i79, i80] -> [2 * i80, 2 * i79]))) (\\i81 -> [2 * i81])), sconcrete (sreplicate [2,2,2,2] 0.0)])) (\\[i82, i83, i84, i85] -> [let i86 = 2 * i84 ; i87 = 2 * i84 ; i88 = 2 * i82 ; i89 = 2 * i82 ; i90 = 2 * i83 ; i91 = 2 * i83 ; i92 = 2 * i85 ; i93 = 2 * i85 in ifH (notB (notB (0 <=. i86 &&* 0 <=. negate i86) &&* notB (0 <=. i87 &&* 0 <=. negate i87)) &&* (notB (notB (0 <=. i88 &&* 0 <=. negate i88) &&* notB (0 <=. i89 &&* 0 <=. negate i89)) &&* (notB (notB (0 <=. i90 &&* 0 <=. negate i90) &&* notB (0 <=. i91 &&* 0 <=. negate i91)) &&* notB (notB (0 <=. i92 &&* 0 <=. negate i92) &&* notB (0 <=. i93 &&* 0 <=. negate i93))))) 0 1, i82, i83, i84, i85]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (stranspose @[2, 1, 0] (sscatter1 @2 (str (sscatter1 @2 (str (sscatter @[2, 2] (ssum @2 (ssum @2 (sscatter1 @2 (stranspose @[2, 3, 0, 1] (sscatter @[2, 2] (stranspose @[2, 3, 1, 0] (sscatter1 @2 (stranspose @[3, 0, 1, 2] (sscatter @[2, 2, 2, 2] (sfromR dret) (\\[i95, i96, i97, i98] -> [let i99 = 2 * i97 ; i100 = 2 * i97 ; i101 = 2 * i95 ; i102 = 2 * i95 ; i103 = 2 * i96 ; i104 = 2 * i96 ; i105 = 2 * i98 ; i106 = 2 * i98 in ifH (notB (notB (0 <=. i99 &&* 0 <=. negate i99) &&* notB (0 <=. i100 &&* 0 <=. negate i100)) &&* (notB (notB (0 <=. i101 &&* 0 <=. negate i101) &&* notB (0 <=. i102 &&* 0 <=. negate i102)) &&* (notB (notB (0 <=. i103 &&* 0 <=. negate i103) &&* notB (0 <=. i104 &&* 0 <=. negate i104)) &&* notB (notB (0 <=. i105 &&* 0 <=. negate i105) &&* notB (0 <=. i106 &&* 0 <=. negate i106))))) 0 1, i95, i96, i97, i98]) !$ [0])) (\\i108 -> [2 * i108]))) (\\[i109, i110] -> [2 * i110, 2 * i109]))) (\\i111 -> [2 * i111])))) (\\[i112, i113] -> [let i114 = 2 * i112 ; i115 = 2 * i112 ; i116 = 2 * i112 ; i117 = 2 * i112 ; i118 = 2 * i112 ; i119 = 2 * i112 ; i120 = 2 * i113 ; i121 = 2 * i113 in ifH (notB (notB (0 <=. i114 &&* 0 <=. negate i114) &&* notB (0 <=. i115 &&* 0 <=. negate i115)) &&* (notB (notB (0 <=. i116 &&* 0 <=. negate i116) &&* notB (0 <=. i117 &&* 0 <=. negate i117)) &&* (notB (notB (0 <=. i118 &&* 0 <=. negate i118) &&* notB (0 <=. i119 &&* 0 <=. negate i119)) &&* notB (notB (0 <=. i120 &&* 0 <=. negate i120) &&* notB (0 <=. i121 &&* 0 <=. negate i121))))) 0 1, i112, i113]) !$ [0])) (\\i123 -> [2 * i123]))) (\\i124 -> [2 * i124, 2 * i124, 2 * i124])))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter1 @2 (str (sscatter1 @2 (sscatter @[2, 2] (ssum @2 (ssum @2 (sscatter1 @2 (stranspose @[2, 3, 0, 1] (sscatter @[2, 2] (stranspose @[2, 3, 1, 0] (sscatter1 @2 (sscatter @[2, 2, 2, 2] (sfromR dret) (\\[i95, i96, i97, i98] -> [let i99 = 2 * i97 ; i100 = 2 * i97 ; i101 = 2 * i95 ; i102 = 2 * i95 ; i103 = 2 * i96 ; i104 = 2 * i96 ; i105 = 2 * i98 ; i106 = 2 * i98 in ifH (notB (notB (0 <=. i99 &&* 0 <=. negate i99) &&* notB (0 <=. i100 &&* 0 <=. negate i100)) &&* (notB (notB (0 <=. i101 &&* 0 <=. negate i101) &&* notB (0 <=. i102 &&* 0 <=. negate i102)) &&* (notB (notB (0 <=. i103 &&* 0 <=. negate i103) &&* notB (0 <=. i104 &&* 0 <=. negate i104)) &&* notB (notB (0 <=. i105 &&* 0 <=. negate i105) &&* notB (0 <=. i106 &&* 0 <=. negate i106))))) 0 1, i98, i95, i96, i97]) !$ [0]) (\\i108 -> [2 * i108]))) (\\[i109, i110] -> [2 * i110, 2 * i109]))) (\\i111 -> [2 * i111])))) (\\[i112, i113] -> [let i114 = 2 * i112 ; i115 = 2 * i112 ; i116 = 2 * i112 ; i117 = 2 * i112 ; i118 = 2 * i112 ; i119 = 2 * i112 ; i120 = 2 * i113 ; i121 = 2 * i113 in ifH (notB (notB (0 <=. i114 &&* 0 <=. negate i114) &&* notB (0 <=. i115 &&* 0 <=. negate i115)) &&* (notB (notB (0 <=. i116 &&* 0 <=. negate i116) &&* notB (0 <=. i117 &&* 0 <=. negate i117)) &&* (notB (notB (0 <=. i118 &&* 0 <=. negate i118) &&* notB (0 <=. i119 &&* 0 <=. negate i119)) &&* notB (notB (0 <=. i120 &&* 0 <=. negate i120) &&* notB (0 <=. i121 &&* 0 <=. negate i121))))) 0 1, i113, i112]) !$ [0]) (\\i123 -> [2 * i123]))) (\\i124 -> [2 * i124, 2 * i124, 2 * i124]))"
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
      in rindex @_ @0 arrAt [iBh, iBw, iImg, iBh]
    _ -> error "conv2dSame3y: impossible pattern needlessly required"

-- This test uses a disastrous version of smaximum, but shows how
-- smaxIndex gets non-trivially vectorized, preserving sharing, too.
testCNNOPP4bU :: Assertion
testCNNOPP4bU = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpaddedS4 @4 @2) (FTKS (SNat @31 :$$ SNat @31 :$$ SNat @31 :$$ SNat @31 :$$ ZSS) (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> let w52 = sgather @[15, 4] (stranspose @[4, 2, 3, 0, 1] (sgather @[15, 4] (stranspose @[2, 0, 1] u1) (\\[i99, i100] -> [2 * i99 + i100]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (sreshape @[31, 31, 15, 15, 16] (stranspose @[2, 3, 4, 0, 5, 1] (splainPart w52))) in sgather @[31, 31, 15, 15] w52 (\\[i54, i55, i56, i57] -> [i57, remH (u53 `index0` [i54, i55, i56, i57]) 4, i54, i55, i56, remH (quotH (u53 `index0` [i54, i55, i56, i57]) 4) 4])"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w52 = sgather @[15, 4] (stranspose @[4, 2, 3, 0, 1] (sgather @[15, 4] (stranspose @[2, 0, 1] u1) (\\[i48, i49] -> [2 * i48 + i49]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (sreshape @[31, 31, 15, 15, 16] (stranspose @[2, 3, 4, 0, 5, 1] (splainPart w52))) in sgather @[31, 31, 15, 15] w52 (\\[i54, i55, i56, i57] -> [i57, remH (kfromS (u53 !$ [i54, i55, i56, i57])) 4, i54, i55, i56, remH (quotH (kfromS (u53 !$ [i54, i55, i56, i57])) 4) 4])"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> stranspose @[1, 2, 0] (sscatter @[15, 4] (stranspose @[3, 4, 1, 2, 0] (sscatter @[15, 4] (let w52 = sgather @[15, 4] (stranspose @[4, 2, 3, 0, 1] (sgather @[15, 4] (stranspose @[2, 0, 1] u1) (\\[i48, i49] -> [2 * i48 + i49]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = smaxIndex (sreshape @[31, 31, 15, 15, 16] (stranspose @[2, 3, 4, 0, 5, 1] (splainPart w52))) in sscatter @[31, 31, 15, 15] dret (\\[i59, i60, i61, i62] -> [i62, remH (kfromS (u53 !$ [i59, i60, i61, i62])) 4, i59, i60, i61, remH (quotH (kfromS (u53 !$ [i59, i60, i61, i62])) 4) 4])) (\\[i63, i64] -> [2 * i63 + i64]))) (\\[i65, i66] -> [2 * i65 + i66]))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> stranspose @[1, 2, 0] (sscatter @[15, 4] (stranspose @[3, 4, 1, 2, 0] (sscatter @[15, 4] (let u53 = smaxIndex (sreshape @[31, 31, 15, 15, 16] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[15, 4] (stranspose @[4, 2, 3, 0, 1] (sgather @[15, 4] (stranspose @[2, 0, 1] (splainPart u1)) (\\[i116, i117] -> [2 * i116 + i117]))) (\\[i50, i51] -> [2 * i50 + i51])))) in sscatter @[31, 31, 15, 15] dret (\\[i59, i60, i61, i62] -> [i62, remH (u53 `index0` [i59, i60, i61, i62]) 4, i59, i60, i61, remH (quotH (u53 `index0` [i59, i60, i61, i62]) 4) 4])) (\\[i63, i64] -> [2 * i63 + i64]))) (\\[i65, i66] -> [2 * i65 + i66]))"

smaximum4 :: forall r sh target. (ADReady target, NumScalar r, KnownShS sh)
          => target (TKS sh r) -> target (TKS '[] r)
smaximum4 t0 | Refl <- lemAppNil @sh =
  tlet t0 $ \t ->
  tletPrimal (tprimalPart $ kfromS $ smaxIndex (sflatten t)) $ \maxIndex ->
    sindex t
    $ fromLinearIdxS (sshape t)
                     (kplainPart $ kfromPrimal @target maxIndex)

fromLinearIdxS :: forall sh j. IntegralH j
               => ShS sh -> j -> IxS sh j
fromLinearIdxS = \sh lin -> case go sh lin of (_, ix) -> ix
  where
    go :: ShS sh1 -> j -> (j, IxS sh1 j)
    go ZSS !n = (n, ZIS)
    go ((:$$) n sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotH` fromIntegral (fromSNat' n)
          i = tensLin `remH` fromIntegral (fromSNat' n)
      in (tensLin', i :.$ idxInTens)

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
  in sbuild @shOut $ \case
    [iImg, iChan, iBh, iBw] ->
      smaximum4 $ slicezS @shK1 arr [ iImg, iChan
                                    , fromIntegral stride * iBh
                                    , fromIntegral stride * iBw ]
    _ -> error "maxPool2dUnpaddedS4: impossible pattern needlessly required"

type IntOr8 = Int8
type Int8OrDouble = Int8

detSquare :: forall target. ADReady target
          => target (TKR 2 Double) -> target (TKScalar Double)
detSquare =
  let fact :: Int -> Int
      fact n = factAcc 1 n
        where factAcc acc i | i <= 1 = acc
              factAcc acc i = factAcc (i * acc) (i - 1)

      fused :: forall s.
               Int -> Int -> VSM.MVector s IntOr8 -> VSM.MVector s Bool
            -> ST s ()
      fused !len !idx0 !perm !freeSpots = do
        let nthFreeSpot :: Int -> Int -> ST s Int
            nthFreeSpot !pos !el = do
              free <- VSM.read freeSpots el
              if pos <= 0 && free
              then return el
              else nthFreeSpot (pos - fromEnum free) (el + 1)
            loop :: Int -> Int -> Int -> ST s ()
            loop _ _ 0 = return ()
            loop !idx !fi i2 = do
              let fi2 = fi `quot` i2
                  (idxDigit, idxRest) = idx `quotRem` fi2
              el <- nthFreeSpot idxDigit 0
              VSM.write perm (len - i2) (fromIntegral el)
              VSM.write freeSpots el False
              loop idxRest fi2 (i2 - 1)
        loop idx0 (fact len) len

      mutated :: forall s. Int -> ST s (VS.Vector IntOr8)
      mutated !len = do
        perms <- VSM.unsafeNew (len * fact len)
        freeSpots <- VSM.unsafeNew len
        let loop :: Int -> ST s ()
            loop (-1) = return ()
            loop i = do
              VSM.set freeSpots True
              fused len i (VSM.slice (i * len) len perms) freeSpots
              loop (i - 1)
        loop (fact len - 1)
        VS.unsafeFreeze perms

      idx_to_perm :: Int -> Nested.Ranked 2 IntOr8
      idx_to_perm n = Nested.rfromVector [fact n, n] $ runST $ mutated n

      inversion_number_from_idx :: Int -> Nested.Ranked 1 Int8OrDouble
      inversion_number_from_idx n =
        let loop :: Int -> Int -> Int -> Int -> Int8OrDouble
            loop s _ _ i | i == 1 = fromIntegral s
            loop s idx fi i =
              let fi2 = fi `quot` i
                  (s1, idx2) = idx `quotRem` fi2
                  s2 = s + s1
              in loop s2 idx2 fi2 (i - 1)
            f idx0 = loop 0 idx0 (fact n) n
        in Nested.rfromVector [fact n] $ VS.generate (fact n) f

      productR :: target (TKR 1 Double) -> target (TKScalar Double)
      productR = kfromR . rfold (*) (rscalar 1)

      det :: target (TKR 2 Double) -> target (TKScalar Double)
      det a =
        let ell = rwidth a
            p :: PlainOf target (TKR 2 IntOr8)
            p = rconcrete $ idx_to_perm ell
            q :: PlainOf target (TKR 1 Int8OrDouble)
            q = rconcrete $ inversion_number_from_idx ell
            f :: IntOf target -> target (TKScalar Double)
            f i = (-1) ** kfromIntegral (kfromPlain (q `rindex0` [i]))
                  * productR (rgather1 ell a $ \i2 ->
                                [i2, kfromIntegral $ p `rindex0` [i, i2]])
        in withSNat (fact ell) $ \ (SNat @k) ->
             ssum0 $ kbuild1 @k f
      {-
      gradient :: Input -> GradientOutput
      gradient a =
        let ell = rwidth a
        in if ell /= 5
             let art = gradArtifact det a
                 artSimp = simplifyArtifactRev art
             in traceShow ("gradient", printArtifactSimple art) $
                traceShow ("gradSimp", printArtifactSimple artSimp) $
                 gradInterpretArtifact artSimp (chunk ell a)
      -}
  in det

testDetSquarePP :: Assertion
testDetSquarePP = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent detSquare
                                     (FTKR [3, 3] (FTKScalar @Double))
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret m1 -> rfromS (sscatter @[3, 6] (sreverse (tproject2 (tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] (-1.0)) ** sfromIntegral (sconcrete (sfromListLinear [6] [0,1,1,2,2,3])) * sreplicate @6 dret) (let m8 = sgather @[3, 6] (sfromR m1) (\\[i6, i7] -> [i6, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `index0` [i7, i6])]) in tpair (sreverse (tproject2 (tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] 1.0)) m8))) (sreverse m8))))) (\\[i13, i14] -> [i13, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `index0` [i14, i13])]))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> rfromS (sscatter @[3, 6] (sreverse (tproject2 (let m8 = sgather @[3, 6] (sfromR m1) (\\[i6, i7] -> [i6, kfromIntegral (kfromS (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) !$ [i7, i6]))]) ; m9 = tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] 1.0)) m8 ; v10 = sconcrete (sreplicate [6] (-1.0)) ** sfromIntegral (sconcrete (sfromListLinear [6] [0,1,1,2,2,3])) in tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (v10 * sreplicate @6 (sfromK dret)) (tpair (sreverse (tproject2 m9)) (sreverse m8))))) (\\[i13, i14] -> [i13, kfromIntegral (kfromS (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) !$ [i14, i13]))]))"
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\m1 -> sdot0 (sconcrete (sreplicate [6] (-1.0)) ** sfromIntegral (sconcrete (sfromListLinear [6] [0,1,1,2,2,3]))) (tproject1 (tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] 1.0)) (sgather @[3, 6] (sfromR m1) (\\[i6, i7] -> [i6, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `index0` [i7, i6])]))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> kfromS (ssum @6 (let m8 = sgather @[3, 6] (sfromR m1) (\\[i6, i7] -> [i6, kfromIntegral (kfromS (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) !$ [i7, i6]))]) ; m9 = tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] 1.0)) m8 ; v10 = sconcrete (sreplicate [6] (-1.0)) ** sfromIntegral (sconcrete (sfromListLinear [6] [0,1,1,2,2,3])) in v10 * tproject1 (tpair (tproject1 m9) (sconcrete (sreplicate [3] Z1)))))"

testDetSquare3 :: Assertion
testDetSquare3 =
  assertEqualUpToEpsilon' 1e-5
    (ringestData [6,6] [-4.869053606042778e-3,5.097805950791719e-4,2.8429105389292052e-3,2.7764540017998364e-2,4.728231081593177e-3,-2.4786176657837146e-2,-2.3469141678115176e-3,1.1152144353350756e-2,-5.653171988563392e-3,-2.9237121329780706e-3,1.9330615364900276e-3,-9.47499409844526e-4,8.025631739575951e-3,1.532840697726606e-3,-7.047121923697899e-3,-4.305940089911722e-3,1.4834586948324607e-4,1.9922535230070225e-3,-8.022565662650867e-3,-1.2603575569596842e-2,8.144948602197404e-3,-9.343418236792108e-3,8.06305133890595e-3,1.7102844846324558e-2,4.888906896881243e-3,-4.884300437195866e-3,4.144990592410334e-4,-4.765756648788264e-3,-4.741976230085896e-3,1.3056977293001447e-2,1.0096879396193574e-2,1.1166653675142208e-2,-1.279846251614077e-4,-7.896243314270949e-3,-9.67019219688691e-3,-5.316279354872351e-3])
    (rev' @Double @0 (rfromK . detSquare)
                     (ringestData [6,6]
          (map (* 0.01)
             [ 40.1,32.1,40.1,32.1,40.1,22.0
             , 9.71,58.8943200001,18.1,29.1,32.1,40.1
             , 55.8943200001, 1, -2, 0.97,58.200001,1
             , 40.1,29.0,53.99432,7.1,58.8943200001,18.1
             , 32.1,40.1,29.0,53.99432,2.971,58.8943200001
             , 40.1,32.0,53.99432,0.97,25.8943200001, 5 ])))

testDetSquare9 :: Assertion
testDetSquare9 =
  assertEqualUpToEpsilon 1e-10
    (ringestData [10,10] [198.10693359375,-208.391845703125,-74.715576171875,-235.9921875,-56.984375,31.765625,20.578125,-214.5625,-41.9375,-181.75,-158.23355102539063,15.689483642578125,-6.07183837890625,-32.855712890625,-18.2464599609375,-13.33154296875,8.1669921875,9.7578125,36.15625,49.59375,4.102272751895559e15,-7.306139851602269e13,1.6344669707400714e16,-2.0387070048459585e15,1.1609737081775948e14,-5.972802872324755e15,-8.292337523172424e14,6.612381495486813e14,1.3074134839774018e15,-4.551880458211714e15,14.17529296875,-9.8779296875,28.02752685546875,-12.56640625,40.626953125,-29.2734375,4.2890625,41.9375,-2.474609375,-6.21875,-54.611328125,-16.91455078125,-39.5654296875,8.5,-6.6484375,35.75,-9.375e-2,-57.0625,19.8515625,-28.75,32.62109375,16.92626953125,94.29736328125,10.3125,-22.953125,-14.3125,-8.9375,9.625,0.259765625,-17.0,-4.10227275189546e15,7.306139851613288e13,-1.6344669707400854e16,2.0387070048459333e15,-1.1609737081777206e14,5.972802872324765e15,8.292337523172635e14,-6.612381495487908e14,-1.3074134839774085e15,4.551880458211696e15,-44.125,63.90625,24.578125,-34.1015625,-16.609375,-12.015625,0.109375,-7.28125,10.8671875,10.1875,-70.75,-21.0,-31.0625,31.78125,-19.25,77.75,-19.125,43.625,5.875,-32.375,51.25,-17.875,26.5,-10.34375,36.1875,23.4375,1.625,-45.625,-20.59375,-68.25])
    (grad detSquare
          (ringestData [10,10]
             [ 7, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432
             , 7, 25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432
             , 7, 40.1,32.1,40.1,89.0,53.99432,97.1,56.8200001,97.1,52.843201
             , 7, 97.1,55.8943200001,97.1,85.894001,97.1,85.801,18.1,29.1,32.1
             , 7, 40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001
             , 7, 97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1
             , 7, 40.1,32.1,40.1,89.0,53.99432,97.1,56.8200001,97.1,52.843201
             , 7, 97.1,55.8943200001, 1, -2, 97.1,58.200001,97.1,55.894320,97.1
             , 7, 29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1
             , 7, 32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6 ]))
