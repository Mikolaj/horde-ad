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
          (rgather @1 @1 @1
                   (4 :$: ZSR) t
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
  let !t1 = gatherNested1 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 317
  resetVarCounter
  let !t2 = gather1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 317
  length (show (simplifyInlineContract @(TKR 1 Float) t1))
    @?= length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t2))

testGatherSimp1 :: Assertion
testGatherSimp1 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000
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
          (rgather @1 @0 @1
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
          (rgather @3 @1 @1
                   (2 :$: 3 :$: 4 :$: ZSR) t
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
  let !t1 = gatherNested2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 570
  resetVarCounter
  let !t2 = gather2 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 390
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t1)) @?= 570
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 390

testGatherSimp2 :: Assertion
testGatherSimp2 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000
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
          (2 :$: ZSR)
          (rgather @3 @0 @2
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
  let !t1 = gatherNested12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 337
  resetVarCounter
  let !t2 = gather12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 337
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 337
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 337

testGatherSimp12 :: Assertion
testGatherSimp12 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000
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
  let !t1 = gatherReshape22 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 159
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 159
  resetVarCounter
  let !t2 = rreshape @2 @2 [2, 6]
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 159
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 159

testGatherSimp22 :: Assertion
testGatherSimp22 = do
  let varName = mkAstVarName (FTKR [6, 2] FTKScalar) . intToAstVarId $ 100000000
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
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 465
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 471
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              rreshape @2 @2 [2, 6]
                (t * rreplicate0N [6, 2] (kfromR $ rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [6, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 465
  length (show (simplifyInlineContract @(TKR 3 Float) @PrimalSpan t2)) @?= 471

testGatherSimp23 :: Assertion
testGatherSimp23 = do
  let varName = mkAstVarName (FTKR [6, 2] FTKScalar) . intToAstVarId $ 100000000
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
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 1132
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 862
  printAstSimple (simplifyInlineContract @(TKR 2 Float) t1)
    @?= "rfromS (smatmul2 (tfromPlain (STKS [6,8] STKScalar) (sconcrete (sfromListLinear [6,8] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.89432,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.89432,5.0,2.0,6.0,1.0,-2.0,0.92,0.1,-0.2,13.1,9.0,8.0,-4.0,34.0,2.99432,-33.0,26.0,2.0,2.0,2.0,2.0,-0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]))) (str (sreshape @[16, 8] (ttranspose (makePerm @[0, 2, 1]) (sreshape @[2, 2, 8, 4] (ttranspose (makePerm @[3, 7, 0, 1, 2, 4, 6, 5]) (sfromR w0)))))))"
  resetVarCounter
  let !t2 = (\t -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                            (rreshape @10 [8, 16] t))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 811
  length (show (simplifyInlineContract @(TKR 2 Float) @PrimalSpan t2)) @?= 541

testGatherSimpPP34 :: Assertion
testGatherSimpPP34 = do
  resetVarCounter
  let !t1 = (\t -> rbuild1 4 (\i ->
             gatherTranspose33 @(AstTensor AstMethodLet PrimalSpan) (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (kfromR $ rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 2534
  length (show (simplifyInlineContract @(TKR 3 Float) t1)) @?= 19868
  resetVarCounter
  let !t2 = (\t -> rbuild1 4 (\i ->
              (\t' -> rmatmul2 (rreshape [6, 8] (rconcrete $ unConcrete t48))
                               (rreshape @10 [8, 16] t'))
                (t * rreplicate0N [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] (kfromR $ rfromIndex0 i))))
            $ AstVar (mkAstVarName (FTKR [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] FTKScalar) . intToAstVarId $ 100000000)
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
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000
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
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000
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
  let varName = mkAstVarName (FTKR [2,4,2] FTKScalar) . intToAstVarId $ 100000000
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
                   (7 :$: ZSR) t
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
  let !t1 = scatterNested1 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 312
  resetVarCounter
  let !t2 = scatter1 $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 452
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t1)) @?= 312
  length (show (simplifyInlineContract @(TKR 1 Float) @PrimalSpan t2)) @?= 452

testScatterSimp1 :: Assertion
testScatterSimp1 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000
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
                   (2 :$: 3 :$: 4 :$: ZSR) t
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
  let !t1 = scatterNested2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 1088
  resetVarCounter
  let !t2 = scatter2 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 619
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 1088
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 619

testScatterSimp2 :: Assertion
testScatterSimp2 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000
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
          (2 :$: ZSR)
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
  let !t1 = scatterNested12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 684
  resetVarCounter
  let !t2 = scatter12 @(AstTensor AstMethodLet PrimalSpan) $ AstVar (mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 566
  length (show (simplifyInlineContract @(TKR 2 Float) t1)) @?= 684
  length (show (simplifyInlineContract @(TKR 2 Float) t2)) @?= 566

testScatterSimp12 :: Assertion
testScatterSimp12 = do
  let varName = mkAstVarName (FTKR [7, 2] FTKScalar) . intToAstVarId $ 100000000
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
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) . intToAstVarId $ 100000000)
  length (show t1) @?= 24384
  length (show (simplifyInlineContract @(TKR 10 Float) t1)) @?= 21668
  resetVarCounter
  let !t2 = barRelu @(AstTensor AstMethodLet PrimalSpan)
            $ AstVar (mkAstVarName (FTKR [1,2,2,1,2,2,2,2,2,1] FTKScalar) . intToAstVarId $ 100000000)
  length (show t2) @?= 12228
  length (show (simplifyInlineContract @(TKR 10 Float) t2)) @?= 12228

testCNNOPP2 :: Assertion
testCNNOPP2 = do
  resetVarCounter
  let t = maxPool2dUnpadded2
            (rconcrete $ Nested.rreplicatePrim (1 :$: 1 :$: 2 :$: 2 :$: ZSR) 1)
  printAstPretty (simplifyInlineContract t)
    @?= "rfromPlain (rfromS (sreplicate @2 (sreplicate @2 (str (sgather1 @2 (stranspose @[1, 3, 0, 2] (sfromVector (fromList [sconcrete (sreplicate [2,2,2,2] 0.0), sgather @[2, 2, 2, 2] (sgather1 @2 (stranspose @[2, 0, 3, 1] (sreplicate @1 (sgather1 @3 (str (sfromVector (fromList [stranspose @[1, 2, 4, 0, 3] (sgather @[2, 2] (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (sconcrete (sfromListLinear [2,3,2] [1.0,1.0,0.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,0.0])) (\\[i89, i90] -> [i89 + i90]))) (\\[i28, i20] -> [i28 + i20])), sconcrete (sreplicate [2,3,2,2,2] 0.0)])) !$ [0]) (\\i103 -> [ifH (0 <=. sconcrete (sfromListLinear [3] [1,0,-1]) `sindex0` [i103] &&* 0 <=. negate (sconcrete (sfromListLinear [3] [1,0,-1]) `sindex0` [i103])) 0 1, i103])))) (\\i25 -> [i25, i25, i25])) (\\[i40, i50, i44, i54] -> [2 * i50 + i40, i50, 2 * i54 + i44])])) !$ [0, 0]) (\\i86 -> [ifH (1 <=. sconcrete (sfromListLinear [2] [1,0]) `sindex0` [i86]) 0 1, i86]))))))"
    -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty t
    @?= "rfromPlain (rfromS (sreplicate @2 (sreplicate @2 (let u46 = let v39 = sconcrete (sreplicate [2] 1) + negate (siota (SNat @2)) in stranspose @[3, 0, 1, 2] (sgather @[2, 2, 2] (stranspose @[2, 3, 4, 0, 1] (sfromVector (fromList [sconcrete (sreplicate [2,2,2,2] 0.0), sgather @[2, 2, 2, 2] (sgather1 @2 (stranspose @[3, 0, 4, 5, 1, 2] (sreplicate @1 (let v19 = sconcrete (sreplicate [3] 1) + negate (siota (SNat @3)) in sgather @[3, 2, 2, 2, 2] (stranspose @[1, 2, 3, 4, 5, 0] (sfromVector (fromList [stranspose @[2, 3, 0, 4, 1] (sgather @[2, 2] (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (sconcrete (sfromListLinear [2,3,2] [1.0,1.0,0.0,0.0,0.0,0.0,1.0,1.0,0.0,0.0,0.0,0.0])) (\\[i33, i22] -> [i33 + i22]))) (\\[i28, i20] -> [i28 + i20])), sconcrete (sreplicate [3,2,2,2,2] 0.0)]))) (\\[i36, i31, i27, i23, i21] -> [i36, i31, i27, i23, i21, ifH (0 <=. sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (v19 `sindex0` [i36]) `sindex0` [i31]) `sindex0` [i27]) `sindex0` [i23]) `sindex0` [i21] &&* 0 <=. negate (sreplicate @2 (sreplicate @2 (sreplicate @2 (sreplicate @2 (v19 `sindex0` [i36]) `sindex0` [i31]) `sindex0` [i27]) `sindex0` [i23]) `sindex0` [i21])) 0 1])))) (\\i25 -> [i25, i25, i25, 0])) (\\[i54, i50, i44, i40] -> [2 * i50 + i40, i50, 2 * i54 + i44])]))) (\\[i49, i43, i41] -> [i49, i43, i41, ifH (1 <=. sreplicate @2 (sreplicate @2 (v39 `sindex0` [i49]) `sindex0` [i43]) `sindex0` [i41]) 0 1])) in stranspose @[2, 3, 0, 1] u46 !$ [0, 0]))))"

testCNNOPP2b :: Assertion
testCNNOPP2b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded2 (FTKR [1, 1, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (sreplicate @2 (sreplicate @2 (str (sgather1 @2 (stranspose @[1, 3, 0, 2] (sfromVector (fromList [sconcrete (sreplicate [2,2,2,2] 0.0), sgather @[2, 2, 2, 2] (sgather1 @2 (stranspose @[2, 0, 3, 1] (sreplicate @1 (sgather1 @3 (str (sfromVector (fromList [stranspose @[1, 2, 4, 0, 3] (sgather @[2, 2] (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (str (sappend (sreplicate @1 (sfromR u1 !$ [0, 0])) (sconcrete (sreplicate [2,2,2] 0.0)))) (\\[i212, i213] -> [i212 + i213]))) (\\[i121, i122] -> [i121 + i122])), sconcrete (sreplicate [2,3,2,2,2] 0.0)])) !$ [0]) (\\i226 -> [ifH (0 <=. sconcrete (sfromListLinear [3] [1,0,-1]) `sindex0` [i226] &&* 0 <=. negate (sconcrete (sfromListLinear [3] [1,0,-1]) `sindex0` [i226])) 0 1, i226])))) (\\i124 -> [i124, i124, i124])) (\\[i125, i126, i127, i128] -> [2 * i126 + i125, i126, 2 * i128 + i127])])) !$ [0, 0]) (\\i129 -> [ifH (1 <=. sconcrete (sfromListLinear [2] [1,0]) `sindex0` [i129]) 0 1, i129])))))"
    -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sreplicate @2 (sreplicate @2 (str (let v117 = sconcrete (sreplicate [2] 1) + negate (siota (SNat @2)) in sgather1 @2 (stranspose @[1, 3, 0, 2] (let v118 = sconcrete (sreplicate [3] 1) + negate (siota (SNat @3)) in sfromVector (fromList [sconcrete (sreplicate [2,2,2,2] 0.0), sgather @[2, 2, 2, 2] (sgather1 @2 (stranspose @[2, 0, 3, 1] (sreplicate @1 (sgather1 @3 (str (sfromVector (fromList [stranspose @[1, 2, 4, 0, 3] (sgather @[2, 2] (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (str (sappend (sreplicate @1 (sfromR u1 !$ [0, 0])) (sconcrete (sreplicate [2,2,2] 0.0)))) (\\[i119, i120] -> [i119 + i120]))) (\\[i121, i122] -> [i121 + i122])), sconcrete (sreplicate [2,3,2,2,2] 0.0)])) !$ [0]) (\\i123 -> [ifH (0 <=. v118 `sindex0` [i123] &&* 0 <=. negate (v118 `sindex0` [i123])) 0 1, i123])))) (\\i124 -> [i124, i124, i124])) (\\[i125, i126, i127, i128] -> [2 * i126 + i125, i126, 2 * i128 + i127])])) !$ [0, 0]) (\\i129 -> [ifH (1 <=. v117 `sindex0` [i129]) 0 1, i129])))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (ssum @1 (sslice (SNat @0) (SNat @1) (str (sscatter @[2, 2] (stranspose @[2, 3, 1, 0] (sscatter @[2, 2] (stranspose @[3, 0, 1, 4, 2] (str (soneHot (let v117 = sconcrete (sreplicate [2] 1) + negate (siota (SNat @2)) ; v118 = sconcrete (sreplicate [3] 1) + negate (siota (SNat @3)) in sscatter1 @3 (ssum @1 (stranspose @[1, 3, 0, 2] (sscatter1 @2 (sscatter @[2, 2, 2, 2] (stranspose @[2, 0, 3, 1] (soneHot (sscatter1 @2 (str (ssum @2 (ssum @2 (sfromR dret)))) (\\i131 -> [ifH (1 <=. v117 `sindex0` [i131]) 0 1, i131])) [0, 0]) !$ [1]) (\\[i133, i134, i135, i136] -> [2 * i134 + i133, i134, 2 * i136 + i135])) (\\i137 -> [i137, i137, i137])))) (\\i138 -> [ifH (0 <=. v118 `sindex0` [i138] &&* 0 <=. negate (v118 `sindex0` [i138])) 0 1, i138])) [0]) !$ [0])) (\\[i140, i141] -> [i140 + i141]))) (\\[i142, i143] -> [i142 + i143]))))) [0, 0])"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (sscatter @[2, 2] (stranspose @[2, 3, 1, 0] (sscatter @[2, 2] (stranspose @[0, 4, 1, 2, 5, 3] (sscatter1 @3 (stranspose @[1, 3, 0, 2] (sscatter1 @2 (sscatter @[2, 2, 2, 2] (sscatter1 @2 (ssum @2 (ssum @2 (stranspose @[0, 1, 3, 2] (sfromR dret)))) (\\i131 -> [ifH (1 <=. sconcrete (sfromListLinear [2] [1,0]) `sindex0` [i131]) 0 1, 0, i131, 0]) !$ [1]) (\\[i133, i134, i135, i136] -> [2 * i134 + i133, i134, 2 * i136 + i135])) (\\i137 -> [i137, i137, i137])) !$ [0]) (\\i138 -> [ifH (0 <=. sconcrete (sfromListLinear [3] [1,0,-1]) `sindex0` [i138] &&* 0 <=. negate (sconcrete (sfromListLinear [3] [1,0,-1]) `sindex0` [i138])) 0 1, 0, i138])) !$ [0]) (\\[i140, i141] -> [i140 + i141]))) (\\[i142, i143] -> [i142 + i143])) !$ [0])))"
    -- TODO: was once "\\dret u1 -> rfromS (sconcrete (sreplicate [1,1,2,2] 0.0))"

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
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [14.0,0.0,14.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromPlain (rfromS (stranspose @[1, 2, 0] (sreplicate @2 (let t124 = sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (str (sgather1 @2 (sreplicate @2 ((let m67 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m68 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2)))) ; v69 = sconcrete (sreplicate [2] 1) + negate (siota (SNat @2)) ; m70 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m71 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2)))) in sgather @[2, 2, 2] (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i107, i94, i81] -> [let i60 = ifH (0 <=. negate i94 &&* (notB (notB (0 <=. sreplicate @2 ((m71 !$ [i81]) `sindex0` [i107]) `sindex0` [i94] &&* 0 <=. negate (sreplicate @2 ((m71 !$ [i81]) `sindex0` [i107]) `sindex0` [i94])) &&* 1 <=. negate (sreplicate @2 ((m70 !$ [i81]) `sindex0` [i107]) `sindex0` [i94])) &&* notB (notB (0 <=. sreplicate @2 (sreplicate @2 (sreplicate @2 ((m68 !$ [i107]) `sindex0` [0]) `sindex0` [i81]) `sindex0` [i107]) `sindex0` [i94] &&* 0 <=. negate (sreplicate @2 (sreplicate @2 (sreplicate @2 ((m68 !$ [i107]) `sindex0` [0]) `sindex0` [i81]) `sindex0` [i107]) `sindex0` [i94])) &&* 1 <=. negate (sreplicate @2 (sreplicate @2 (sreplicate @2 ((m67 !$ [i107]) `sindex0` [0]) `sindex0` [i81]) `sindex0` [i107]) `sindex0` [i94])))) 0 1 in ifH (1 <=. i81) (ifH (1 <=. sreplicate @2 (sreplicate @2 (v69 `sindex0` [1]) `sindex0` [i107]) `sindex0` [i94]) 1 i60) i60])) + (let m72 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m73 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2)))) ; v74 = sconcrete (sreplicate [2] 1) + negate (siota (SNat @2)) ; m75 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m76 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2)))) in stranspose @[2, 0, 1] (sgather @[2, 2] (sreplicate @1 (sgather @[2, 2, 2] (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i88, i47, i114] -> [let i60 = ifH (0 <=. negate i47 &&* (notB (notB (0 <=. sreplicate @2 ((m76 !$ [i88]) `sindex0` [1]) `sindex0` [i47] &&* 0 <=. negate (sreplicate @2 ((m76 !$ [i88]) `sindex0` [1]) `sindex0` [i47])) &&* 1 <=. negate (sreplicate @2 ((m75 !$ [i88]) `sindex0` [1]) `sindex0` [i47])) &&* notB (notB (0 <=. sreplicate @2 ((m73 !$ [i114]) `sindex0` [i114]) `sindex0` [i47] &&* 0 <=. negate (sreplicate @2 ((m73 !$ [i114]) `sindex0` [i114]) `sindex0` [i47])) &&* 1 <=. negate (sreplicate @2 ((m72 !$ [i114]) `sindex0` [i114]) `sindex0` [i47])))) 0 1 in ifH (1 <=. sreplicate @2 (v74 `sindex0` [1]) `sindex0` [i47]) 1 i60]))) (\\[i100, i87] -> [i87, i87, i100]))))) (\\i1 -> [2 * i1, 0]))) (\\i2 -> [2 * i2]))) (\\i4 -> [2 * i4]) in sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [stranspose @[0, 2, 1] t124 `sindex0` [0, 0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)])))))"

testCNNOPP3b :: Assertion
testCNNOPP3b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dSame3) (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromR u1 `sindex0` [0, 0, 0, 1] + sfromR u1 `sindex0` [0, 1, 1, 1], 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)]))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sreplicate @2 (let m204 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2)))) ; i205 = ifH (0 <=. m204 `sindex0` [0, 1] &&* 0 <=. negate (m204 `sindex0` [0, 1])) 0 1 in sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromR u1 `sindex0` [0, 0, 0, 1] + kfromS (sfromVector (fromList [sfromR u1 `sindex0` [0, 1, 1, 1], 0.0]) !$ [i205]), 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)]))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (let m204 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2)))) ; i205 = ifH (0 <=. m204 `sindex0` [0, 1] &&* 0 <=. negate (m204 `sindex0` [0, 1])) 0 1 ; t207 = ssum @2 (stranspose @[2, 0, 1] (sfromR dret)) ; m208 = t207 !$ [0] ; v209 = m208 !$ [0] ; x210 = v209 `sindex0` [0] ; v211 = soneHot (sfromK x210) [i205] in soneHot (sfromK x210) [0, 0, 0, 1] + soneHot (sfromK (v211 `sindex0` [0])) [0, 1, 1, 1])"
    -- TODO: was once "\\dret u1 -> rfromS (let t88 = ssum @2 (stranspose @[2, 0, 1] (sfromR dret)) ; m89 = t88 !$ [0] ; v90 = m89 !$ [0] ; x91 = v90 `sindex0` [0] in soneHot (sfromK x91) [0, 0, 0, 1] + soneHot (sfromK x91) [0, 1, 1, 1])"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter1 @2 (let x236 = ssum0 (stranspose @[0, 1, 3, 2] (sfromR dret) !$ [0, 0, 0]) in sfromVector (fromList [x236, kfromS (sfromK x236)])) (\\i212 -> [0, i212, i212, 1]))"

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
    @?= "rfromPlain (rfromS (sgather @[2, 2, 2, 2] (stranspose @[5, 6, 7, 8, 0, 1, 2, 3, 4] (sfromVector (fromList [stranspose @[2, 3, 4, 0, 5, 6, 7, 1] (sgather @[2, 2] (stranspose @[6, 0, 3, 1, 4, 5, 2] (sgather @[2, 2, 2] (stranspose @[4, 1, 3, 0, 2] (sgather @[2, 2] (stranspose @[3, 0, 4, 1, 2] (sgather @[2, 2] (sconcrete (sreplicate [2,3,3,3] 7.0)) (\\[i143, i146] -> [i143 + i146]))) (\\[i149, i151] -> [2 + (negate i151 + i149), i151]))) (\\[i153, i155, i158] -> [i153 * i155 + i158]))) (\\[i90, i51] -> [2 * i90 + i51])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0]) (\\[i120, i108, i98, i89] -> [ifH (notB (notB (0 <=. sconcrete (sfromListLinear [2,2] [1,0,-1,-2]) `sindex0` [i89, 0] &&* 0 <=. negate (sconcrete (sfromListLinear [2,2] [1,0,-1,-2]) `sindex0` [i89, 0])) &&* 1 <=. negate (sconcrete (sfromListLinear [2,2] [0,-1,-2,-3]) `sindex0` [i89, 0])) &&* (notB (notB (0 <=. sconcrete (sfromListLinear [2,2,2] [1,0,1,0,1,0,0,-1]) `sindex0` [i120, i98, 0] &&* 0 <=. negate (sconcrete (sfromListLinear [2,2,2] [1,0,1,0,1,0,0,-1]) `sindex0` [i120, i98, 0])) &&* 1 <=. negate (sconcrete (sfromListLinear [2,2,2] [0,-1,0,-1,0,-1,-1,-2]) `sindex0` [i120, i98, 0])) &&* (0 <=. sconcrete (sfromListLinear [2,2] [-1,-2,0,-1]) `sindex0` [i108, 0] &&* 0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i108, 0]))) 0 1, i120, i108, i98, i89])))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromPlain (rfromS (let w81 = let m40 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m41 = sconcrete (sreplicate [2,2] (-1)) + (str (sreplicate @2 (siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2)))) ; t42 = stranspose @[1, 2, 0] (sreplicate @2 (str (sreplicate @2 (negate (siota (SNat @2)))) * sreplicate @2 (siota (SNat @2)))) + sreplicate @2 (sreplicate @2 (negate (siota (SNat @2)))) ; t43 = sconcrete (sreplicate [2,2,2] 1) + (stranspose @[1, 2, 0] (sreplicate @2 (str (sreplicate @2 (negate (siota (SNat @2)))) * sreplicate @2 (siota (SNat @2)))) + sreplicate @2 (sreplicate @2 (negate (siota (SNat @2))))) ; m44 = str (sreplicate @2 (sconcrete (sreplicate [2] (-2)) * siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2))) ; m45 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (sconcrete (sreplicate [2] (-2)) * siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2)))) in sgather @[2, 2, 2, 2, 2, 2, 2, 2] (stranspose @[1, 2, 3, 4, 5, 6, 7, 8, 0] (sfromVector (fromList [stranspose @[2, 3, 4, 0, 5, 6, 7, 1] (sgather @[2, 2] (stranspose @[6, 0, 3, 1, 4, 5, 2] (sgather @[2, 2, 2] (stranspose @[3, 0, 2, 1] (sgather @[2, 2] (stranspose @[0, 2, 1] (sgather @[2, 2] (sconcrete (sreplicate [2,3,3,3] 7.0)) (\\[i112, i75] -> [i112 + i75]))) (\\[i111, i66] -> [i111, 2 + (negate i111 + i66)]))) (\\[i122, i100, i58] -> [i122 * i100 + i58]))) (\\[i90, i51] -> [2 * i90 + i51])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)]))) (\\[i120, i108, i98, i89, i76, i67, i59, i52] -> [i120, i108, i98, i89, i76, i67, i59, i52, ifH (notB (notB (0 <=. (m45 !$ [i89]) `sindex0` [i52] &&* 0 <=. negate ((m45 !$ [i89]) `sindex0` [i52])) &&* 1 <=. negate ((m44 !$ [i89]) `sindex0` [i52])) &&* (notB (notB (0 <=. sreplicate @2 ((t43 !$ [i120, i98]) `sindex0` [i59]) `sindex0` [i52] &&* 0 <=. negate (sreplicate @2 ((t43 !$ [i120, i98]) `sindex0` [i59]) `sindex0` [i52])) &&* 1 <=. negate (sreplicate @2 ((t42 !$ [i120, i98]) `sindex0` [i59]) `sindex0` [i52])) &&* (0 <=. sreplicate @2 (sreplicate @2 ((m41 !$ [i108]) `sindex0` [i67]) `sindex0` [i59]) `sindex0` [i52] &&* 0 <=. sreplicate @2 (sreplicate @2 (sreplicate @2 ((m40 !$ [i108]) `sindex0` [i76]) `sindex0` [i67]) `sindex0` [i59]) `sindex0` [i52]))) 0 1]) in stranspose @[4, 5, 6, 7, 0, 1, 2, 3] w81 !$ [0, 0, 0, 0]))"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP4b :: Assertion
testCNNOPP4b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent maxPool2dUnpadded4 (FTKR [3, 3, 3, 3] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (sgather @[2, 2, 2, 2] (stranspose @[5, 6, 7, 8, 0, 1, 2, 3, 4] (sfromVector (fromList [stranspose @[2, 3, 4, 0, 5, 6, 7, 1] (sgather @[2, 2] (stranspose @[6, 0, 1, 2, 3, 4, 5] (sgather @[2, 2, 2, 2, 2, 2] (stranspose @[2, 1, 0] (sfromR u1)) (\\[i217, i218, i219, i220, i221, i222] -> [i217 * i219 + i222, 2 + (negate i218 + i221), 1 + sconcrete (sfromListLinear [2,2] [0,1,1,2]) `sindex0` [i218, i220]]))) (\\[i176, i177] -> [2 * i176 + i177])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0]) (\\[i178, i179, i180, i181] -> [ifH (notB (notB (0 <=. sconcrete (sfromListLinear [2,2] [1,0,-1,-2]) `sindex0` [i181, 0] &&* 0 <=. negate (sconcrete (sfromListLinear [2,2] [1,0,-1,-2]) `sindex0` [i181, 0])) &&* 1 <=. negate (sconcrete (sfromListLinear [2,2] [0,-1,-2,-3]) `sindex0` [i181, 0])) &&* (notB (notB (0 <=. sconcrete (sfromListLinear [2,2,2] [1,0,1,0,1,0,0,-1]) `sindex0` [i178, i180, 0] &&* 0 <=. negate (sconcrete (sfromListLinear [2,2,2] [1,0,1,0,1,0,0,-1]) `sindex0` [i178, i180, 0])) &&* 1 <=. negate (sconcrete (sfromListLinear [2,2,2] [0,-1,0,-1,0,-1,-1,-2]) `sindex0` [i178, i180, 0])) &&* (0 <=. sconcrete (sfromListLinear [2,2] [-1,-2,0,-1]) `sindex0` [i179, 0] &&* 0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i179, 0]))) 0 1, i178, i179, i180, i181]))"
      -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (let m163 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m164 = sconcrete (sreplicate [2,2] (-1)) + (str (sreplicate @2 (siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2)))) ; t165 = stranspose @[1, 2, 0] (sreplicate @2 (str (sreplicate @2 (negate (siota (SNat @2)))) * sreplicate @2 (siota (SNat @2)))) + sreplicate @2 (sreplicate @2 (negate (siota (SNat @2)))) ; t166 = sconcrete (sreplicate [2,2,2] 1) + (stranspose @[1, 2, 0] (sreplicate @2 (str (sreplicate @2 (negate (siota (SNat @2)))) * sreplicate @2 (siota (SNat @2)))) + sreplicate @2 (sreplicate @2 (negate (siota (SNat @2))))) ; m167 = str (sreplicate @2 (sconcrete (sreplicate [2] (-2)) * siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2))) ; m168 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (sconcrete (sreplicate [2] (-2)) * siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2)))) in sgather @[2, 2, 2, 2] (stranspose @[5, 6, 7, 8, 0, 1, 2, 3, 4] (let m169 = str (sreplicate @2 (siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) in sfromVector (fromList [stranspose @[2, 3, 4, 0, 5, 6, 7, 1] (sgather @[2, 2] (stranspose @[6, 0, 1, 2, 3, 4, 5] (sgather @[2, 2, 2, 2, 2, 2] (stranspose @[2, 1, 0] (sfromR u1)) (\\[i170, i171, i172, i173, i174, i175] -> [i170 * i172 + i175, 2 + (negate i171 + i174), 1 + m169 `sindex0` [i171, i173]]))) (\\[i176, i177] -> [2 * i176 + i177])), sconcrete (sreplicate [2,2,2,2,2,2,2,2] 0.0)])) !$ [0, 0, 0, 0]) (\\[i178, i179, i180, i181] -> [ifH (notB (notB (0 <=. m168 `sindex0` [i181, 0] &&* 0 <=. negate (m168 `sindex0` [i181, 0])) &&* 1 <=. negate (m167 `sindex0` [i181, 0])) &&* (notB (notB (0 <=. t166 `sindex0` [i178, i180, 0] &&* 0 <=. negate (t166 `sindex0` [i178, i180, 0])) &&* 1 <=. negate (t165 `sindex0` [i178, i180, 0])) &&* (0 <=. m164 `sindex0` [i179, 0] &&* 0 <=. m163 `sindex0` [i179, 0]))) 0 1, i178, i179, i180, i181]))"
      -- TODO: was once "\\u1 -> rfromS (sconcrete (sfromListLinear [2,2,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (stranspose @[2, 1, 0] (let m163 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m164 = sconcrete (sreplicate [2,2] (-1)) + (str (sreplicate @2 (siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2)))) ; t165 = stranspose @[1, 2, 0] (sreplicate @2 (str (sreplicate @2 (negate (siota (SNat @2)))) * sreplicate @2 (siota (SNat @2)))) + sreplicate @2 (sreplicate @2 (negate (siota (SNat @2)))) ; t166 = sconcrete (sreplicate [2,2,2] 1) + (stranspose @[1, 2, 0] (sreplicate @2 (str (sreplicate @2 (negate (siota (SNat @2)))) * sreplicate @2 (siota (SNat @2)))) + sreplicate @2 (sreplicate @2 (negate (siota (SNat @2))))) ; m167 = str (sreplicate @2 (sconcrete (sreplicate [2] (-2)) * siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2))) ; m168 = sconcrete (sreplicate [2,2] 1) + (str (sreplicate @2 (sconcrete (sreplicate [2] (-2)) * siota (SNat @2))) + sreplicate @2 (negate (siota (SNat @2)))) ; m169 = str (sreplicate @2 (siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) in sscatter @[2, 2, 2, 2, 2, 2] (stranspose @[1, 2, 3, 4, 5, 6, 0] (sscatter @[2, 2] (stranspose @[3, 7, 0, 1, 2, 4, 5, 6] (stranspose @[4, 5, 6, 7, 8, 0, 1, 2, 3] (soneHot (sscatter @[2, 2, 2, 2] (sfromR dret) (\\[i183, i184, i185, i186] -> [ifH (notB (notB (0 <=. m168 `sindex0` [i186, 0] &&* 0 <=. negate (m168 `sindex0` [i186, 0])) &&* 1 <=. negate (m167 `sindex0` [i186, 0])) &&* (notB (notB (0 <=. t166 `sindex0` [i183, i185, 0] &&* 0 <=. negate (t166 `sindex0` [i183, i185, 0])) &&* 1 <=. negate (t165 `sindex0` [i183, i185, 0])) &&* (0 <=. m164 `sindex0` [i184, 0] &&* 0 <=. m163 `sindex0` [i184, 0]))) 0 1, i183, i184, i185, i186])) [0, 0, 0, 0]) !$ [0])) (\\[i188, i189] -> [2 * i188 + i189]))) (\\[i190, i191, i192, i193, i194, i195] -> [i190 * i192 + i195, 2 + (negate i191 + i194), 1 + m169 `sindex0` [i191, i193]])))"
      -- TODO: was once "\\dret u1 -> rfromS (sconcrete (sreplicate [3,3,3,3] 0.0))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (sscatter @[2, 2, 2, 2, 2, 2] (stranspose @[1, 2, 3, 4, 5, 6, 0] (sscatter @[2, 2] (sscatter @[2, 2, 2, 2] (sfromR dret) (\\[i183, i184, i185, i186] -> [ifH (notB (notB (0 <=. sconcrete (sfromListLinear [2,2] [1,0,-1,-2]) `sindex0` [i186, 0] &&* 0 <=. negate (sconcrete (sfromListLinear [2,2] [1,0,-1,-2]) `sindex0` [i186, 0])) &&* 1 <=. negate (sconcrete (sfromListLinear [2,2] [0,-1,-2,-3]) `sindex0` [i186, 0])) &&* (notB (notB (0 <=. sconcrete (sfromListLinear [2,2,2] [1,0,1,0,1,0,0,-1]) `sindex0` [i183, i185, 0] &&* 0 <=. negate (sconcrete (sfromListLinear [2,2,2] [1,0,1,0,1,0,0,-1]) `sindex0` [i183, i185, 0])) &&* 1 <=. negate (sconcrete (sfromListLinear [2,2,2] [0,-1,0,-1,0,-1,-1,-2]) `sindex0` [i183, i185, 0])) &&* (0 <=. sconcrete (sfromListLinear [2,2] [-1,-2,0,-1]) `sindex0` [i184, 0] &&* 0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i184, 0]))) 0 1, i186, 0, i183, i184, i185, 0, 0, 0]) !$ [0]) (\\[i188, i189] -> [2 * i188 + i189]))) (\\[i190, i191, i192, i193, i194, i195] -> [1 + sconcrete (sfromListLinear [2,2] [0,1,1,2]) `sindex0` [i191, i193], 2 + (negate i191 + i194), i190 * i192 + i195]))"
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
    @?= "rfromPlain (rfromS (sreplicate @1 (sreplicate @1 (sgather @[2, 2] (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i35, i32] -> [ifH (0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i32, 0] &&* 0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i35, 0]) 0 1])))))"
      -- TODO: was once "rfromS (sconcrete (sfromListLinear [1,1,2,2] [7.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromPlain (rfromS (sreplicate @1 (sreplicate @1 (let m29 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m30 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) in sgather @[2, 2] (sconcrete (sfromListLinear [2] [7.0,0.0])) (\\[i35, i32] -> [ifH (0 <=. (m30 !$ [i32]) `sindex0` [0] &&* 0 <=. (m29 !$ [i35]) `sindex0` [0]) 0 1])))))"

-- In this test primal is trivial but gradient is not, so we know how much
-- scatters should be able to simplify in the future.
testCNNOPP5b :: Assertion
testCNNOPP5b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent conv2dSame4 (FTKR [5, 5, 5, 5] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (sgather @[2, 2] (sfromVector (fromList [str (sslice (SNat @0) (SNat @2) (str (sslice (SNat @0) (SNat @2) (sfromR u1 !$ [0, 0])))), sconcrete (sreplicate [2,2] 0.0)])) (\\[i42, i43] -> [ifH (0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i43, 0] &&* 0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i42, 0]) 0 1, i42, i43]))))"
      -- TODO: was once "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (str (sfromVector (fromList [sfromVector (fromList [sfromR u1 `sindex0` [0, 0, 0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)])))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (sreplicate @1 (sreplicate @1 (let m40 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m41 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) in sgather @[2, 2] (sfromVector (fromList [str (sslice (SNat @0) (SNat @2) (str (sslice (SNat @0) (SNat @2) (sfromR u1 !$ [0, 0])))), sconcrete (sreplicate [2,2] 0.0)])) (\\[i42, i43] -> [ifH (0 <=. m41 `sindex0` [i43, 0] &&* 0 <=. m40 `sindex0` [i42, 0]) 0 1, i42, i43]))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (let m40 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; m41 = str (sreplicate @2 (negate (siota (SNat @2)))) + sreplicate @2 (negate (siota (SNat @2))) ; t47 = sscatter @[2, 2] (ssum @1 (ssum @1 (sfromR dret))) (\\[i45, i46] -> [ifH (0 <=. m41 `sindex0` [i46, 0] &&* 0 <=. m40 `sindex0` [i45, 0]) 0 1, i45, i46]) in sappend (sconcrete (sfromListLinear [0,5] [])) (sappend (str (sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (str (t47 !$ [0])) (sconcrete (sreplicate [3,2] 0.0))))) (sconcrete (sreplicate [3,5] 0.0)))) [0, 0])"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (sappend (str (sappend (sscatter @[2, 2] (sfromR dret !$ [0, 0]) (\\[i45, i46] -> [ifH (0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i46, 0] &&* 0 <=. sconcrete (sfromListLinear [2,2] [0,-1,-1,-2]) `sindex0` [i45, 0]) 0 1, i46, i45]) !$ [0]) (sconcrete (sreplicate [3,2] 0.0)))) (sconcrete (sreplicate [3,5] 0.0))) [0, 0])"
      -- TODO: was once "\\dret u1 -> rfromS (soneHot (sfromK (sfromR dret `sindex0` [0, 0, 0, 0])) [0, 0, 0, 0])"

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
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromPlain (rfromS (stranspose @[1, 2, 0] (sreplicate @2 (let t31 = sgather1 @2 (stranspose @[2, 1, 0] (sgather1 @2 (str (sgather1 @2 (sreplicate @2 (str (sreplicate @2 (let m21 = sgather1 @2 (str (sgather1 @2 (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\i9 -> [2 * i9, 2 * i9, 2 * i9]))) (\\i12 -> [2 * i12]) in sfromVector (fromList [sfromVector (fromList [m21 `sindex0` [0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]))))) (\\i1 -> [2 * i1, 0]))) (\\i2 -> [2 * i2]))) (\\i4 -> [2 * i4]) in sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [stranspose @[0, 2, 1] t31 `sindex0` [0, 0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)])))))"

testCNNOPP6b :: Assertion
testCNNOPP6b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3 . conv2dSame3z) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromR u1 `sindex0` [0, 0, 0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)]))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sreplicate @2 (sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromR u1 `sindex0` [0, 0, 0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)]))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (sfromK (((ssum @2 (stranspose @[2, 0, 1] (sfromR dret)) !$ [0]) !$ [0]) `sindex0` [0])) [0, 0, 0, 0])"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (sfromK (ssum0 (stranspose @[0, 1, 3, 2] (sfromR dret) !$ [0, 0, 0]))) [0, 0, 0, 0])"

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
    @?= "rfromS (sconcrete (sfromListLinear [2,2,2,2] [7.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))"
  printAstPretty afcnn2T
    @?= "rfromPlain (rfromS (let u28 = sgather1 @2 (stranspose @[3, 2, 0, 1] (sgather @[2, 2] (stranspose @[1, 2, 0] (sgather1 @2 (sreplicate @2 (stranspose @[1, 2, 0] (sreplicate @2 (let m21 = sgather1 @2 (str (sgather1 @2 (sconcrete (sreplicate [2,2,2,2] 7.0)) (\\i9 -> [2 * i9, 2 * i9, 2 * i9]))) (\\i11 -> [2 * i11]) in sfromVector (fromList [sfromVector (fromList [m21 `sindex0` [0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]))))) (\\i1 -> [2 * i1]))) (\\[i32, i3] -> [2 * i3, 2 * i32]))) (\\i4 -> [2 * i4]) in stranspose @[1, 2, 0] (sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [str u28 `sindex0` [0, 0, 0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)]), sconcrete (sreplicate [2,2,2] 0.0)]))))"

testCNNOPP7b :: Assertion
testCNNOPP7b = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpadded3y . conv2dSame3y) (FTKR [2, 2, 2, 2] (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromR u1 `sindex0` [0, 0, 0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)]), sconcrete (sreplicate [2,2,2] 0.0)])))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (stranspose @[1, 2, 0] (sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromVector (fromList [sfromR u1 `sindex0` [0, 0, 0, 0], 0.0]), sconcrete (sreplicate [2] 0.0)]), sconcrete (sreplicate [2,2] 0.0)]), sconcrete (sreplicate [2,2,2] 0.0)])))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> rfromS (soneHot (sfromK ((((stranspose @[2, 0, 1] (sfromR dret) !$ [0]) !$ [0]) !$ [0]) `sindex0` [0])) [0, 0, 0, 0])"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> rfromS (soneHot (sfromK (sfromR dret `sindex0` [0, 0, 0, 0])) [0, 0, 0, 0])"

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
-- sargMax gets non-trivially vectorized, preserving sharing, too.
testCNNOPP4bU :: Assertion
testCNNOPP4bU = do
  resetVarCounter
  let artifactRev = revArtifactAdapt UseIncomingCotangent (maxPool2dUnpaddedS4 @4 @2) (FTKS (SNat @31 :$$ SNat @31 :$$ SNat @31 :$$ SNat @31 :$$ ZSS) (FTKScalar @Double))
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> let w52 = sgather @[15, 4] (stranspose @[4, 2, 3, 0, 1] (sgather @[15, 4] (stranspose @[2, 0, 1] u1) (\\[i105, i106] -> [2 * i105 + i106]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = sargMax (sreshape @[31, 31, 15, 15, 16] (stranspose @[2, 3, 4, 0, 5, 1] (splainPart w52))) in sgather @[31, 31, 15, 15] w52 (\\[i54, i55, i56, i57] -> [i57, remH (u53 `sindex0` [i54, i55, i56, i57]) 4, i54, i55, i56, remH (quotH (u53 `sindex0` [i54, i55, i56, i57]) 4) 4])"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w52 = sgather @[15, 4] (stranspose @[4, 2, 3, 0, 1] (sgather @[15, 4] (stranspose @[2, 0, 1] u1) (\\[i48, i49] -> [2 * i48 + i49]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = sargMax (sreshape @[31, 31, 15, 15, 16] (stranspose @[2, 3, 4, 0, 5, 1] (splainPart w52))) in sgather @[31, 31, 15, 15] w52 (\\[i54, i55, i56, i57] -> [i57, remH (u53 `sindex0` [i54, i55, i56, i57]) 4, i54, i55, i56, remH (quotH (u53 `sindex0` [i54, i55, i56, i57]) 4) 4])"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> stranspose @[1, 2, 0] (sscatter @[15, 4] (stranspose @[3, 4, 1, 2, 0] (sscatter @[15, 4] (let w52 = sgather @[15, 4] (stranspose @[4, 2, 3, 0, 1] (sgather @[15, 4] (stranspose @[2, 0, 1] u1) (\\[i48, i49] -> [2 * i48 + i49]))) (\\[i50, i51] -> [2 * i50 + i51]) ; u53 = sargMax (sreshape @[31, 31, 15, 15, 16] (stranspose @[2, 3, 4, 0, 5, 1] (splainPart w52))) in sscatter @[31, 31, 15, 15] dret (\\[i59, i60, i61, i62] -> [i62, remH (u53 `sindex0` [i59, i60, i61, i62]) 4, i59, i60, i61, remH (quotH (u53 `sindex0` [i59, i60, i61, i62]) 4) 4])) (\\[i63, i64] -> [2 * i63 + i64]))) (\\[i65, i66] -> [2 * i65 + i66]))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> stranspose @[1, 2, 0] (sscatter @[15, 4] (stranspose @[3, 4, 1, 2, 0] (sscatter @[15, 4] (let u116 = sargMax (sreshape @[31, 31, 15, 15, 16] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[15, 4] (stranspose @[4, 2, 3, 0, 1] (sgather @[15, 4] (stranspose @[2, 0, 1] (splainPart u1)) (\\[i124, i125] -> [2 * i124 + i125]))) (\\[i50, i51] -> [2 * i50 + i51])))) in sscatter @[31, 31, 15, 15] dret (\\[i59, i60, i61, i62] -> [i62, remH (u116 `sindex0` [i59, i60, i61, i62]) 4, i59, i60, i61, remH (quotH (u116 `sindex0` [i59, i60, i61, i62]) 4) 4])) (\\[i63, i64] -> [2 * i63 + i64]))) (\\[i65, i66] -> [2 * i65 + i66]))"

smaximum4 :: forall r sh target. (ADReady target, NumScalar r, KnownShS sh)
          => target (TKS sh r) -> target (TKS '[] r)
smaximum4 t0 | Refl <- lemAppNil @sh =
  tlet t0 $ \t ->
  tletPrimal (tprimalPart $ kfromS $ sargMax (sflatten t)) $ \argMax ->
    sindex t
    $ fromLinearIdxS (sshape t)
                     (kplainPart $ kfromPrimal @target argMax)

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
    @?= "\\dret m1 -> rfromS (sscatter @[3, 6] (sreverse (tproject2 (tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sfromPlain (sconcrete (sreplicate [6] (-1.0)) ** sfromIntegral (sconcrete (sfromListLinear [6] [0,1,1,2,2,3]))) * sreplicate @6 dret) (let m15 = sgather @[3, 6] (sfromR m1) (\\[i6, i7] -> [i6, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `sindex0` [i7, i6])]) in tpair (sreverse (tproject2 (tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] 1.0)) m15))) (sreverse m15))))) (\\[i13, i14] -> [i13, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `sindex0` [i14, i13])]))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> rfromS (sscatter @[3, 6] (sreverse (tproject2 (let m8 = sgather @[3, 6] (sfromR m1) (\\[i6, i7] -> [i6, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `sindex0` [i7, i6])]) ; m9 = tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] 1.0)) m8 ; v10 = sconcrete (sreplicate [6] (-1.0)) ** sfromIntegral (sconcrete (sfromListLinear [6] [0,1,1,2,2,3])) in tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sfromPlain v10 * sreplicate @6 (sfromK dret)) (tpair (sreverse (tproject2 m9)) (sreverse m8))))) (\\[i13, i14] -> [i13, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `sindex0` [i14, i13])]))"
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\m1 -> sdot0 (sfromPlain (sconcrete (sreplicate [6] (-1.0)) ** sfromIntegral (sconcrete (sfromListLinear [6] [0,1,1,2,2,3])))) (tproject1 (tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] 1.0)) (sgather @[3, 6] (sfromR m1) (\\[i6, i7] -> [i6, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `sindex0` [i7, i6])]))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> kfromS (ssum @6 (let m8 = sgather @[3, 6] (sfromR m1) (\\[i6, i7] -> [i6, kfromIntegral (sconcrete (sfromListLinear [6,3] [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]) `sindex0` [i7, i6])]) ; m9 = tmapAccumLDer (SNat @3) <lambda> <lambda> <lambda> (sconcrete (sreplicate [6] 1.0)) m8 ; v10 = sconcrete (sreplicate [6] (-1.0)) ** sfromIntegral (sconcrete (sfromListLinear [6] [0,1,1,2,2,3])) in sfromPlain v10 * tproject1 (tpair (tproject1 m9) (sconcrete (sreplicate [3] Z1)))))"

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
