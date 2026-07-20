{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Deterministic (non-QuickCheck) gradient-correctness tests of convolution
-- AD derivatives, at the poor man's benchmark data and sizes.
--
-- These are the deterministic counterpart of the convolution poor man's
-- benchmarks in "TestConvQuickCheck": on data of the same shapes and sizes
-- (the shared @benchData@ etc. helpers), they check that the symbolic
-- gradient those benchmarks time agrees with the handwritten gradients,
-- both imported from that module. They live in a separate module so that
-- the whole testsuite's non-QuickCheck tests, whose timing is much more
-- deterministic, can be compared in isolation.
module TestConvCorrect (testTrees) where

import Prelude

import GHC.TypeLits (KnownNat, type (+), type (<=))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import HordeAd

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
  -- and sizes from "TestConvQuickCheck": on data of those shapes, the symbolic
  -- gradient must agree with the handwritten one — and, at the small size,
  -- with the concrete non-symbolic AD too — so the path those poor man's
  -- benchmarks time is verified correct at scale, not only timed.
  -- Same convolution: input and output the same size.
  [ testCase "conv2dSameVjp dKrn correct 6" (conv2dSameVjpKrnCorrect @6)
  , testCase "conv2dSameVjp dKrn correct 24" (conv2dSameVjpKrnCorrect @24)
  , testCase "conv2dSameVjp dKrn correct 96" (conv2dSameVjpKrnCorrect @96)
  , testCase "conv2dSameVjp dInp correct 6" (conv2dSameVjpInpCorrect @6)
  , testCase "conv2dSameVjp dInp correct 24" (conv2dSameVjpInpCorrect @24)
  , testCase "conv2dSameVjp dInp correct 96" (conv2dSameVjpInpCorrect @96)
  , testCase "conv2dSameVjp correct vs concrete 6" conv2dSameVjpConcrete6
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
      handwritten, symbolic :: Concrete (TKS '[3, 3, 3, 3] Double)
      handwritten = conv2dSame_dKrn @3 @3 @3 @nAw @nAw @3 @3
                                    (sconcrete (unConcrete arrA))
                                    (sconcrete (unConcrete arrB))
      symbolic = vjp (`conv2dSameS` sconcrete (unConcrete arrA))
                     (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
  in assertEqualUpToEpsilon 1e-5 handwritten symbolic

conv2dSameVjpInpCorrect :: forall nAw. KnownNat nAw => Assertion
conv2dSameVjpInpCorrect =
  let (arrK, arrA, arrB) = benchData @nAw @Double 42
      handwritten, symbolic :: Concrete (TKS '[3, 3, nAw, nAw] Double)
      handwritten = conv2dSame_dInp @3 @3 @3 @nAw @nAw @3 @3
                                    (sconcrete (unConcrete arrK))
                                    (sconcrete (unConcrete arrB))
      symbolic = vjp (conv2dSameS (sconcrete (unConcrete arrK)))
                     (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
  in assertEqualUpToEpsilon 1e-5 handwritten symbolic

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


-- * The shrinking convolution variant

conv2dShrinkingVjpKrnCorrect
  :: forall nAw. (KnownNat nAw, 1 <= nAw) => Assertion
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
