{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Deterministic (non-QuickCheck) gradient-correctness tests of convolution
-- AD derivatives, at the poor man's benchmark data and sizes.
--
-- These are the deterministic counterpart of the convolution poor man's
-- benchmarks in "TestConvQuickCheck": on data of the same shapes and sizes
-- (the shared @benchData@ etc. helpers), they check that the gradient
-- programs those benchmarks and bench/ConvVjpBench.hs time — the symbolic
-- gradient and the handwritten term vectorized and interpreted — agree
-- with the handwritten gradients evaluated at the Concrete target, all
-- imported from that module. They live in a separate module so that
-- the whole testsuite's non-QuickCheck tests, whose timing is much more
-- deterministic, can be compared in isolation.
module TestConvCorrect (testTrees) where

import Prelude

import GHC.TypeLits (KnownNat, type (+), type (<=))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested.Shaped.Shape (knownShS)

import HordeAd
import HordeAd.Core.AstEnv (emptyEnv, extendEnv)
import HordeAd.Core.AstInterpret (interpretAstFull)

import EqEpsilon

import TestConvQuickCheck
  ( benchData
  , benchDataPadded
  , benchDataShrinking
  , conv2dPadded_dInp
  , conv2dPadded_dKrn
  , conv2dSame_dInp
  , conv2dSame_dKrn
  , conv2dShrinking_dInp
  , conv2dShrinking_dKrn
  )

testTrees :: [TestTree]
testTrees =
  -- Gradient-correctness checks at the convolution poor man's benchmark data
  -- and sizes from "TestConvQuickCheck": on data of those shapes, the
  -- symbolic gradient and the vectorized-and-interpreted handwritten term
  -- must agree with the handwritten gradient — and, at the small size, the
  -- concrete non-symbolic AD and the variable-cotangent term must too — so
  -- every path those poor man's benchmarks and bench/ConvVjpBench.hs time
  -- is verified correct at scale, not only timed.
  -- Same convolution: input and output the same size.
  [ testCase "conv2dSameVjp dKrn correct 6" (conv2dSameVjpKrnCorrect @6)
  , testCase "conv2dSameVjp dKrn correct 24" (conv2dSameVjpKrnCorrect @24)
  , testCase "conv2dSameVjp dKrn correct 96" (conv2dSameVjpKrnCorrect @96)
  , testCase "conv2dSameVjp dInp correct 6" (conv2dSameVjpInpCorrect @6)
  , testCase "conv2dSameVjp dInp correct 24" (conv2dSameVjpInpCorrect @24)
  , testCase "conv2dSameVjp dInp correct 96" (conv2dSameVjpInpCorrect @96)
  , testCase "conv2dSameVjp correct vs concrete 6" conv2dSameVjpConcrete6
  , testCase "conv2dSameVjp correct var cotangent 6" conv2dSameVjpVarCotangent6
  -- Shrinking convolution: input larger than output.
  , testCase "conv2dShrinkingVjp dKrn correct 6"
             (conv2dShrinkingVjpKrnCorrect @6)
  , testCase "conv2dShrinkingVjp dKrn correct 24"
             (conv2dShrinkingVjpKrnCorrect @24)
  , testCase "conv2dShrinkingVjp dKrn correct 96"
             (conv2dShrinkingVjpKrnCorrect @96)
  , testCase "conv2dShrinkingVjp dInp correct 6"
             (conv2dShrinkingVjpInpCorrect @6)
  , testCase "conv2dShrinkingVjp dInp correct 24"
             (conv2dShrinkingVjpInpCorrect @24)
  , testCase "conv2dShrinkingVjp dInp correct 96"
             (conv2dShrinkingVjpInpCorrect @96)
  , testCase "conv2dShrinkingVjp correct vs concrete 6"
             conv2dShrinkingVjpConcrete6
  -- Padded convolution: output larger than input.
  , testCase "conv2dPaddedVjp dKrn correct 6" (conv2dPaddedVjpKrnCorrect @6)
  , testCase "conv2dPaddedVjp dKrn correct 24" (conv2dPaddedVjpKrnCorrect @24)
  , testCase "conv2dPaddedVjp dKrn correct 96" (conv2dPaddedVjpKrnCorrect @96)
  , testCase "conv2dPaddedVjp dInp correct 6" (conv2dPaddedVjpInpCorrect @6)
  , testCase "conv2dPaddedVjp dInp correct 24" (conv2dPaddedVjpInpCorrect @24)
  , testCase "conv2dPaddedVjp dInp correct 96" (conv2dPaddedVjpInpCorrect @96)
  , testCase "conv2dPaddedVjp correct vs concrete 6" conv2dPaddedVjpConcrete6
  ]


-- * The same convolution variant

conv2dSameVjpKrnCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dSameVjpKrnCorrect =
  let (arrK, arrA, arrB) = benchData @nAw @Double 42
      handwritten, symbolic, vectorized :: Concrete (TKS '[3, 3, 3, 3] Double)
      handwritten = conv2dSame_dKrn @3 @3 @3 @nAw @nAw @3 @3
                                    (sconcrete (unConcrete arrA))
                                    (sconcrete (unConcrete arrB))
      symbolic = vjp (`conv2dSameS` sconcrete (unConcrete arrA))
                     (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      -- The same handwritten gradient built at the AST target, vectorized
      -- and interpreted — the computation the HandwrittenVectorized poor
      -- man's benchmarks and the H- variants of bench/ConvVjpBench.hs
      -- time; here its value is pinned to the Concrete-target one.
      vectorized = interpretAstFull emptyEnv
                   $ conv2dSame_dKrn @3 @3 @3 @nAw @nAw @3 @3
                                     (sconcrete (unConcrete arrA))
                                     (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 handwritten symbolic
        assertEqualUpToEpsilon 1e-5 handwritten vectorized

conv2dSameVjpInpCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dSameVjpInpCorrect =
  let (arrK, arrA, arrB) = benchData @nAw @Double 42
      handwritten, symbolic, vectorized
        :: Concrete (TKS '[3, 3, nAw, nAw] Double)
      handwritten = conv2dSame_dInp @3 @3 @3 @nAw @nAw @3 @3
                                    (sconcrete (unConcrete arrK))
                                    (sconcrete (unConcrete arrB))
      symbolic = vjp (conv2dSameS (sconcrete (unConcrete arrK)))
                     (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
      vectorized = interpretAstFull emptyEnv
                   $ conv2dSame_dInp @3 @3 @3 @nAw @nAw @3 @3
                                     (sconcrete (unConcrete arrK))
                                     (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 handwritten symbolic
        assertEqualUpToEpsilon 1e-5 handwritten vectorized

-- At the small size, also check the symbolic gradient against the concrete
-- (non-symbolic) AD, which is too slow to run at the larger sizes.
conv2dSameVjpConcrete6 :: Assertion
conv2dSameVjpConcrete6 =
  let (arrK, arrA, arrB) = benchData @6 @Double 42
      hKrn, cKrn :: Concrete (TKS '[3, 3, 3, 3] Double)
      hKrn = conv2dSame_dKrn @3 @3 @3 @6 @6 @3 @3
                             (sconcrete (unConcrete arrA))
                             (sconcrete (unConcrete arrB))
      cKrn = cvjp @_ @_ @_ @Concrete
                  (`conv2dSameS` sconcrete (unConcrete arrA))
                  (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      hInp, cInp :: Concrete (TKS '[3, 3, 6, 6] Double)
      hInp = conv2dSame_dInp @3 @3 @3 @6 @6 @3 @3
                             (sconcrete (unConcrete arrK))
                             (sconcrete (unConcrete arrB))
      cInp = cvjp @_ @_ @_ @Concrete
                  (conv2dSameS (sconcrete (unConcrete arrK)))
                  (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 hKrn cKrn
        assertEqualUpToEpsilon 1e-5 hInp cInp

-- At the small size, also check the handwritten terms with the incoming
-- cotangent kept as a variable and bound in the environment, both raw and
-- contracted — the exact terms the H-exec-raw and H-exec variants of
-- bench/ConvVjpBench.hs interpret (the constant-cotangent form is covered
-- by the vectorized legs above).
conv2dSameVjpVarCotangent6 :: Assertion
conv2dSameVjpVarCotangent6 =
  let (arrK, arrA, arrB) = benchData @6 @Double 42
      varNameB = mkAstVarName (FTKS (knownShS @'[3, 3, 6, 6])
                                    (FTKScalar @Double))
                              (intToAstVarId 100000099)
      env = extendEnv varNameB arrB emptyEnv
      hKrn, rawKrn, contractedKrn :: Concrete (TKS '[3, 3, 3, 3] Double)
      hKrn = conv2dSame_dKrn @3 @3 @3 @6 @6 @3 @3
                             (sconcrete (unConcrete arrA))
                             (sconcrete (unConcrete arrB))
      krnTermVar :: AstTensor AstMethodLet FullSpan (TKS '[3, 3, 3, 3] Double)
      krnTermVar = conv2dSame_dKrn @3 @3 @3 @6 @6 @3 @3
                                   (sconcrete (unConcrete arrA))
                                   (AstVar varNameB)
      rawKrn = interpretAstFull env krnTermVar
      contractedKrn = interpretAstFull env (simplifyInlineContract krnTermVar)
      hInp, rawInp, contractedInp :: Concrete (TKS '[3, 3, 6, 6] Double)
      hInp = conv2dSame_dInp @3 @3 @3 @6 @6 @3 @3
                             (sconcrete (unConcrete arrK))
                             (sconcrete (unConcrete arrB))
      inpTermVar :: AstTensor AstMethodLet FullSpan (TKS '[3, 3, 6, 6] Double)
      inpTermVar = conv2dSame_dInp @3 @3 @3 @6 @6 @3 @3
                                   (sconcrete (unConcrete arrK))
                                   (AstVar varNameB)
      rawInp = interpretAstFull env inpTermVar
      contractedInp = interpretAstFull env (simplifyInlineContract inpTermVar)
  in do assertEqualUpToEpsilon 1e-5 hKrn rawKrn
        assertEqualUpToEpsilon 1e-5 hKrn contractedKrn
        assertEqualUpToEpsilon 1e-5 hInp rawInp
        assertEqualUpToEpsilon 1e-5 hInp contractedInp


-- * The shrinking convolution variant

conv2dShrinkingVjpKrnCorrect
  :: forall nAw. (KnownNat nAw, 1 <= nAw) => Assertion
conv2dShrinkingVjpKrnCorrect =
  let (arrK, arrA, arrB) = benchDataShrinking @nAw @Double 42
      handwritten, symbolic, vectorized :: Concrete (TKS '[3, 3, 3, 3] Double)
      handwritten = conv2dShrinking_dKrn @3 @3 @3 @nAw @nAw @2 @2
                                         (sconcrete (unConcrete arrA))
                                         (sconcrete (unConcrete arrB))
      symbolic = vjp (`conv2dShrinkingS` sconcrete (unConcrete arrA))
                     (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      vectorized = interpretAstFull emptyEnv
                   $ conv2dShrinking_dKrn @3 @3 @3 @nAw @nAw @2 @2
                                          (sconcrete (unConcrete arrA))
                                          (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 handwritten symbolic
        assertEqualUpToEpsilon 1e-5 handwritten vectorized

conv2dShrinkingVjpInpCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dShrinkingVjpInpCorrect =
  let (arrK, arrA, arrB) = benchDataShrinking @nAw @Double 42
      handwritten, symbolic, vectorized
        :: Concrete (TKS '[3, 3, nAw + 2, nAw + 2] Double)
      handwritten = conv2dShrinking_dInp @3 @3 @3 @nAw @nAw @2 @2
                                         (sconcrete (unConcrete arrK))
                                         (sconcrete (unConcrete arrB))
      symbolic = vjp (conv2dShrinkingS (sconcrete (unConcrete arrK)))
                     (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
      vectorized = interpretAstFull emptyEnv
                   $ conv2dShrinking_dInp @3 @3 @3 @nAw @nAw @2 @2
                                          (sconcrete (unConcrete arrK))
                                          (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 handwritten symbolic
        assertEqualUpToEpsilon 1e-5 handwritten vectorized

conv2dShrinkingVjpConcrete6 :: Assertion
conv2dShrinkingVjpConcrete6 =
  let (arrK, arrA, arrB) = benchDataShrinking @6 @Double 42
      hKrn, cKrn :: Concrete (TKS '[3, 3, 3, 3] Double)
      hKrn = conv2dShrinking_dKrn @3 @3 @3 @6 @6 @2 @2
                                  (sconcrete (unConcrete arrA))
                                  (sconcrete (unConcrete arrB))
      cKrn = cvjp @_ @_ @_ @Concrete
                  (`conv2dShrinkingS` sconcrete (unConcrete arrA))
                  (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      hInp, cInp :: Concrete (TKS '[3, 3, 8, 8] Double)
      hInp = conv2dShrinking_dInp @3 @3 @3 @6 @6 @2 @2
                                  (sconcrete (unConcrete arrK))
                                  (sconcrete (unConcrete arrB))
      cInp = cvjp @_ @_ @_ @Concrete
                  (conv2dShrinkingS (sconcrete (unConcrete arrK)))
                  (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 hKrn cKrn
        assertEqualUpToEpsilon 1e-5 hInp cInp


-- * The padded convolution variant

conv2dPaddedVjpKrnCorrect :: forall nAw. (KnownNat nAw, 1 <= nAw) => Assertion
conv2dPaddedVjpKrnCorrect =
  let (arrK, arrA, arrB) = benchDataPadded @nAw @Double 42
      handwritten, symbolic, vectorized :: Concrete (TKS '[3, 3, 3, 3] Double)
      handwritten = conv2dPadded_dKrn @3 @3 @3 @nAw @nAw @2 @2
                                      (sconcrete (unConcrete arrA))
                                      (sconcrete (unConcrete arrB))
      symbolic = vjp (`conv2dPaddedS` sconcrete (unConcrete arrA))
                     (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      vectorized = interpretAstFull emptyEnv
                   $ conv2dPadded_dKrn @3 @3 @3 @nAw @nAw @2 @2
                                       (sconcrete (unConcrete arrA))
                                       (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 handwritten symbolic
        assertEqualUpToEpsilon 1e-5 handwritten vectorized

conv2dPaddedVjpInpCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dPaddedVjpInpCorrect =
  let (arrK, arrA, arrB) = benchDataPadded @nAw @Double 42
      handwritten, symbolic, vectorized
        :: Concrete (TKS '[3, 3, nAw, nAw] Double)
      handwritten = conv2dPadded_dInp @3 @3 @3 @nAw @nAw @2 @2
                                      (sconcrete (unConcrete arrK))
                                      (sconcrete (unConcrete arrB))
      symbolic = vjp (conv2dPaddedS (sconcrete (unConcrete arrK)))
                     (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
      vectorized = interpretAstFull emptyEnv
                   $ conv2dPadded_dInp @3 @3 @3 @nAw @nAw @2 @2
                                       (sconcrete (unConcrete arrK))
                                       (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 handwritten symbolic
        assertEqualUpToEpsilon 1e-5 handwritten vectorized

conv2dPaddedVjpConcrete6 :: Assertion
conv2dPaddedVjpConcrete6 =
  let (arrK, arrA, arrB) = benchDataPadded @6 @Double 42
      hKrn, cKrn :: Concrete (TKS '[3, 3, 3, 3] Double)
      hKrn = conv2dPadded_dKrn @3 @3 @3 @6 @6 @2 @2
                               (sconcrete (unConcrete arrA))
                               (sconcrete (unConcrete arrB))
      cKrn = cvjp @_ @_ @_ @Concrete
                  (`conv2dPaddedS` sconcrete (unConcrete arrA))
                  (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      hInp, cInp :: Concrete (TKS '[3, 3, 6, 6] Double)
      hInp = conv2dPadded_dInp @3 @3 @3 @6 @6 @2 @2
                               (sconcrete (unConcrete arrK))
                               (sconcrete (unConcrete arrB))
      cInp = cvjp @_ @_ @_ @Concrete
                  (conv2dPaddedS (sconcrete (unConcrete arrK)))
                  (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 hKrn cKrn
        assertEqualUpToEpsilon 1e-5 hInp cInp
