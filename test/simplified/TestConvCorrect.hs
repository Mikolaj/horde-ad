{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Deterministic (non-QuickCheck) gradient-correctness tests of convolution
-- AD derivatives, at the poor man's benchmark data and sizes.
--
-- These are the deterministic counterpart of the convolution poor man's
-- benchmarks in "TestConvQuickCheck": they check, on data of the same shapes
-- and sizes, that the symbolic gradient those poor man's benchmarks time is
-- also correct. They live in a separate module so that the whole testsuite's
-- non-QuickCheck tests, whose timing is much more deterministic, can be
-- compared in isolation from the randomized QuickCheck tests and poor man's
-- benchmarks. The poor man's benchmarks these mirror, the shared random-data
-- helpers (@benchData@ etc.) and the handwritten gradients they check against
-- all live in "TestConvQuickCheck".
module TestConvCorrect (testTrees) where

import Prelude

import GHC.TypeLits (KnownNat, type (+), type (<=))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import HordeAd

import EqEpsilon

import TestConvQuickCheck
  ( benchData, benchDataShrinking, benchDataPadded
  , conv2dPreserving_dKrn, conv2dPreserving_dInp
  , conv2dShrinking_dKrn, conv2dShrinking_dInp
  , conv2dPadded_dKrn, conv2dPadded_dInp )

testTrees :: [TestTree]
testTrees =
  -- Gradient-correctness checks at the convolution poor man's benchmark data
  -- and sizes from "TestConvQuickCheck": on data of those shapes, the symbolic
  -- gradient must agree with the handwritten one — and, at the small size,
  -- with the concrete non-symbolic AD too — so the path those poor man's
  -- benchmarks time is verified correct at scale, not only timed.
  -- Preserving convolution: input and output the same size.
  [ testCase "conv2dPreservingVjp dKrn correct 6" (conv2dPreservingVjpKrnCorrect @6)
  , testCase "conv2dPreservingVjp dKrn correct 24" (conv2dPreservingVjpKrnCorrect @24)
  , testCase "conv2dPreservingVjp dKrn correct 96" (conv2dPreservingVjpKrnCorrect @96)
  , testCase "conv2dPreservingVjp dInp correct 6" (conv2dPreservingVjpInpCorrect @6)
  , testCase "conv2dPreservingVjp dInp correct 24" (conv2dPreservingVjpInpCorrect @24)
  , testCase "conv2dPreservingVjp dInp correct 96" (conv2dPreservingVjpInpCorrect @96)
  , testCase "conv2dPreservingVjp correct vs concrete 6" conv2dPreservingVjpConcrete6
  -- Shrinking convolution: input larger than output.
  , testCase "conv2dShrinkingVjp dKrn correct 6" (conv2dShrinkingVjpKrnCorrect @6)
  , testCase "conv2dShrinkingVjp dKrn correct 24" (conv2dShrinkingVjpKrnCorrect @24)
  , testCase "conv2dShrinkingVjp dKrn correct 96" (conv2dShrinkingVjpKrnCorrect @96)
  , testCase "conv2dShrinkingVjp dInp correct 6" (conv2dShrinkingVjpInpCorrect @6)
  , testCase "conv2dShrinkingVjp dInp correct 24" (conv2dShrinkingVjpInpCorrect @24)
  , testCase "conv2dShrinkingVjp dInp correct 96" (conv2dShrinkingVjpInpCorrect @96)
  , testCase "conv2dShrinkingVjp correct vs concrete 6" conv2dShrinkingVjpConcrete6
  -- Padded convolution: output larger than input.
  , testCase "conv2dPaddedVjp dKrn correct 6" (conv2dPaddedVjpKrnCorrect @6)
  , testCase "conv2dPaddedVjp dKrn correct 24" (conv2dPaddedVjpKrnCorrect @24)
  , testCase "conv2dPaddedVjp dKrn correct 96" (conv2dPaddedVjpKrnCorrect @96)
  , testCase "conv2dPaddedVjp dInp correct 6" (conv2dPaddedVjpInpCorrect @6)
  , testCase "conv2dPaddedVjp dInp correct 24" (conv2dPaddedVjpInpCorrect @24)
  , testCase "conv2dPaddedVjp dInp correct 96" (conv2dPaddedVjpInpCorrect @96)
  , testCase "conv2dPaddedVjp correct vs concrete 6" conv2dPaddedVjpConcrete6
  ]


-- * The preserving convolution variant

conv2dPreservingVjpKrnCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dPreservingVjpKrnCorrect =
  let (arrK, arrA, arrB) = benchData @nAw @Double 42
      handwritten, symbolic :: Concrete (TKS '[3, 3, 3, 3] Double)
      handwritten = conv2dPreserving_dKrn @3 @3 @3 @nAw @nAw @3 @3
                                    (sconcrete (unConcrete arrA))
                                    (sconcrete (unConcrete arrB))
      symbolic = vjp (`conv2dPreservingS` sconcrete (unConcrete arrA))
                     (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
  in assertEqualUpToEpsilon 1e-5 handwritten symbolic

conv2dPreservingVjpInpCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dPreservingVjpInpCorrect =
  let (arrK, arrA, arrB) = benchData @nAw @Double 42
      handwritten, symbolic :: Concrete (TKS '[3, 3, nAw, nAw] Double)
      handwritten = conv2dPreserving_dInp @3 @3 @3 @nAw @nAw @3 @3
                                    (sconcrete (unConcrete arrK))
                                    (sconcrete (unConcrete arrB))
      symbolic = vjp (conv2dPreservingS (sconcrete (unConcrete arrK)))
                     (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in assertEqualUpToEpsilon 1e-5 handwritten symbolic

-- At the small size, also check the symbolic gradient against the concrete
-- (non-symbolic) AD, which is too slow to run at the larger sizes.
conv2dPreservingVjpConcrete6 :: Assertion
conv2dPreservingVjpConcrete6 =
  let (arrK, arrA, arrB) = benchData @6 @Double 42
      hKrn, cKrn :: Concrete (TKS '[3, 3, 3, 3] Double)
      hKrn = conv2dPreserving_dKrn @3 @3 @3 @6 @6 @3 @3
                             (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
      cKrn = cvjp @_ @_ @_ @Concrete (`conv2dPreservingS` sconcrete (unConcrete arrA))
                  (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      hInp, cInp :: Concrete (TKS '[3, 3, 6, 6] Double)
      hInp = conv2dPreserving_dInp @3 @3 @3 @6 @6 @3 @3
                             (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      cInp = cvjp @_ @_ @_ @Concrete (conv2dPreservingS (sconcrete (unConcrete arrK)))
                  (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 hKrn cKrn
        assertEqualUpToEpsilon 1e-5 hInp cInp


-- * The shrinking convolution variant

conv2dShrinkingVjpKrnCorrect :: forall nAw. (KnownNat nAw, 1 <= nAw) => Assertion
conv2dShrinkingVjpKrnCorrect =
  let (arrK, arrA, arrB) = benchDataShrinking @nAw @Double 42
      handwritten, symbolic :: Concrete (TKS '[3, 3, 3, 3] Double)
      handwritten = conv2dShrinking_dKrn @3 @3 @3 @nAw @nAw @2 @2
                                         (sconcrete (unConcrete arrA))
                                         (sconcrete (unConcrete arrB))
      symbolic = vjp (`conv2dShrinkingS` sconcrete (unConcrete arrA))
                     (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
  in assertEqualUpToEpsilon 1e-5 handwritten symbolic

conv2dShrinkingVjpInpCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dShrinkingVjpInpCorrect =
  let (arrK, arrA, arrB) = benchDataShrinking @nAw @Double 42
      handwritten, symbolic :: Concrete (TKS '[3, 3, nAw + 2, nAw + 2] Double)
      handwritten = conv2dShrinking_dInp @3 @3 @3 @nAw @nAw @2 @2
                                         (sconcrete (unConcrete arrK))
                                         (sconcrete (unConcrete arrB))
      symbolic = vjp (conv2dShrinkingS (sconcrete (unConcrete arrK)))
                     (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in assertEqualUpToEpsilon 1e-5 handwritten symbolic

conv2dShrinkingVjpConcrete6 :: Assertion
conv2dShrinkingVjpConcrete6 =
  let (arrK, arrA, arrB) = benchDataShrinking @6 @Double 42
      hKrn, cKrn :: Concrete (TKS '[3, 3, 3, 3] Double)
      hKrn = conv2dShrinking_dKrn @3 @3 @3 @6 @6 @2 @2
                                  (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
      cKrn = cvjp @_ @_ @_ @Concrete (`conv2dShrinkingS` sconcrete (unConcrete arrA))
                  (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      hInp, cInp :: Concrete (TKS '[3, 3, 8, 8] Double)
      hInp = conv2dShrinking_dInp @3 @3 @3 @6 @6 @2 @2
                                  (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      cInp = cvjp @_ @_ @_ @Concrete (conv2dShrinkingS (sconcrete (unConcrete arrK)))
                  (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 hKrn cKrn
        assertEqualUpToEpsilon 1e-5 hInp cInp


-- * The padded convolution variant

conv2dPaddedVjpKrnCorrect :: forall nAw. (KnownNat nAw, 1 <= nAw) => Assertion
conv2dPaddedVjpKrnCorrect =
  let (arrK, arrA, arrB) = benchDataPadded @nAw @Double 42
      handwritten, symbolic :: Concrete (TKS '[3, 3, 3, 3] Double)
      handwritten = conv2dPadded_dKrn @3 @3 @3 @nAw @nAw @2 @2
                                      (sconcrete (unConcrete arrA))
                                      (sconcrete (unConcrete arrB))
      symbolic = vjp (`conv2dPaddedS` sconcrete (unConcrete arrA))
                     (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
  in assertEqualUpToEpsilon 1e-5 handwritten symbolic

conv2dPaddedVjpInpCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dPaddedVjpInpCorrect =
  let (arrK, arrA, arrB) = benchDataPadded @nAw @Double 42
      handwritten, symbolic :: Concrete (TKS '[3, 3, nAw, nAw] Double)
      handwritten = conv2dPadded_dInp @3 @3 @3 @nAw @nAw @2 @2
                                      (sconcrete (unConcrete arrK))
                                      (sconcrete (unConcrete arrB))
      symbolic = vjp (conv2dPaddedS (sconcrete (unConcrete arrK)))
                     (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in assertEqualUpToEpsilon 1e-5 handwritten symbolic

conv2dPaddedVjpConcrete6 :: Assertion
conv2dPaddedVjpConcrete6 =
  let (arrK, arrA, arrB) = benchDataPadded @6 @Double 42
      hKrn, cKrn :: Concrete (TKS '[3, 3, 3, 3] Double)
      hKrn = conv2dPadded_dKrn @3 @3 @3 @6 @6 @2 @2
                               (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
      cKrn = cvjp @_ @_ @_ @Concrete (`conv2dPaddedS` sconcrete (unConcrete arrA))
                  (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      hInp, cInp :: Concrete (TKS '[3, 3, 6, 6] Double)
      hInp = conv2dPadded_dInp @3 @3 @3 @6 @6 @2 @2
                               (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
      cInp = cvjp @_ @_ @_ @Concrete (conv2dPaddedS (sconcrete (unConcrete arrK)))
                  (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in do assertEqualUpToEpsilon 1e-5 hKrn cKrn
        assertEqualUpToEpsilon 1e-5 hInp cInp
