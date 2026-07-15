{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | QuickCheck tests and poor man's benchmarks of convolution AD derivatives
-- vs handwritten derivatives. The matching deterministic (non-QuickCheck)
-- gradient-correctness checks live in "TestConvCorrect"; the shared
-- random-data helpers and handwritten gradients exported below are what that
-- module reuses.
module TestConvQuickCheck
  ( testTrees
    -- * Shared with "TestConvCorrect"
  , benchData, benchDataShrinking, benchDataPadded
  , conv2dSame_dKrn, conv2dSame_dInp
  , conv2dShrinking_dKrn, conv2dShrinking_dInp
  , conv2dPadded_dKrn, conv2dPadded_dInp
  ) where

import Prelude

import Data.Bifunctor (first, second)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:))
import GHC.TypeLits (KnownNat, type (+), type (-), type (<=), type (<=?))
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.QuickCheck hiding (label, shuffle)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstInterpret

import EqEpsilon
import Shared

import MnistData
import MnistFcnnRanked2 (XParams2)
import MnistFcnnRanked2 qualified

testTrees :: [TestTree]
testTrees =
  [ tensorADOnceMnistTests2
  , testCase "conv2dSameVjp dInp" test_conv2dSameVjp_dInp
  , testCase "conv2dSameVjp dKrn" test_conv2dSameVjp_dKrn
  , testProperty "conv2dSameVjp Quickcheck Double"
                 (quickcheck_conv2dSameVjp @Double)
  , testProperty "conv2dSameVjp Quickcheck Float"
                 (quickcheck_conv2dSameVjp @Float)
  , testCase "conv2dShrinkingVjp dInp" test_conv2dShrinkingVjp_dInp
  , testCase "conv2dShrinkingVjp dKrn" test_conv2dShrinkingVjp_dKrn
  , testProperty "conv2dShrinkingVjp Quickcheck Double"
                 (quickcheck_conv2dShrinkingVjp @Double)
  , testProperty "conv2dShrinkingVjp Quickcheck Float"
                 (quickcheck_conv2dShrinkingVjp @Float)
  , testCase "conv2dPaddedVjp dInp" test_conv2dPaddedVjp_dInp
  , testCase "conv2dPaddedVjp dKrn" test_conv2dPaddedVjp_dKrn
  , testProperty "conv2dPaddedVjp Quickcheck Double"
                 (quickcheck_conv2dPaddedVjp @Double)
  , testProperty "conv2dPaddedVjp Quickcheck Float"
                 (quickcheck_conv2dPaddedVjp @Float)
  , testProperty "conv2dSameJvp Quickcheck Double"
                 (quickcheck_conv2dSameJvp @Double)
  , testProperty "conv2dSameJvp Quickcheck Float"
                 (quickcheck_conv2dSameJvp @Float)
  , testProperty "conv2dShrinkingJvp Quickcheck Double"
                 (quickcheck_conv2dShrinkingJvp @Double)
  , testProperty "conv2dShrinkingJvp Quickcheck Float"
                 (quickcheck_conv2dShrinkingJvp @Float)
  , testProperty "conv2dPaddedJvp Quickcheck Double"
                 (quickcheck_conv2dPaddedJvp @Double)
  , testProperty "conv2dPaddedJvp Quickcheck Float"
                 (quickcheck_conv2dPaddedJvp @Float)
  , testProperty "conv2dSameVjp Bench dKrn Handwritten warmup"
                 (quickcheck_conv2dSameVjpKrnHandwritten @Double)
  , testProperty "conv2dSameVjp Bench dKrn Handwritten"
                 (quickcheck_conv2dSameVjpKrnHandwritten @Double)
  , testProperty "conv2dSameVjp Bench dKrn HandwrittenVectorized"
                 (quickcheck_conv2dSameVjpKrnHandwrittenVectorized @Double)
  , testProperty "conv2dSameVjp Bench dKrn Symbolic"
                 (quickcheck_conv2dSameVjpKrnSymbolic @Double)
  , testProperty "conv2dSameVjp Bench dKrn Concrete"
                 (quickcheck_conv2dSameVjpKrnConcrete @Double)
  , testProperty "conv2dSameVjp Bench dInp Handwritten"
                 (quickcheck_conv2dSameVjpInpHandwritten @Double)
  , testProperty "conv2dSameVjp Bench dInp HandwrittenVectorized"
                 (quickcheck_conv2dSameVjpInpHandwrittenVectorized @Double)
  , testProperty "conv2dSameVjp Bench dInp Symbolic"
                 (quickcheck_conv2dSameVjpInpSymbolic @Double)
  , testProperty "conv2dSameVjp Bench dInp Concrete"
                 (quickcheck_conv2dSameVjpInpConcrete @Double)
  -- Size-scaled poor man's benchmarks (see the definitions below), for the
  -- same, shrinking and padded convolutions, and for both the kernel and the
  -- input gradient. The matching gradient-correctness checks live in
  -- "TestConvCorrect", kept separate so the testsuite's non-QuickCheck, more
  -- deterministically timed tests can be compared as a group.
  -- Same convolution: input and output the same size.
  , testProperty "conv2dSameVjp Bench dKrn 6 SymbolicPerCall"
                 (sizedSymbolicPerCall @6)
  , testProperty "conv2dSameVjp Bench dKrn 6 SymbolicAmortized"
                 (sizedSymbolicAmortized @6)
  , testProperty "conv2dSameVjp Bench dKrn 6 HandwrittenVec"
                 (sizedHandwrittenVectorized @6)
  , testProperty "conv2dSameVjp Bench dKrn 24 SymbolicPerCall"
                 (sizedSymbolicPerCall @24)
  , testProperty "conv2dSameVjp Bench dKrn 24 SymbolicAmortized"
                 (sizedSymbolicAmortized @24)
  , testProperty "conv2dSameVjp Bench dKrn 24 HandwrittenVec"
                 (sizedHandwrittenVectorized @24)
  , testProperty "conv2dSameVjp Bench dInp 6 SymbolicPerCall"
                 (sizedSymbolicPerCallInp @6)
  , testProperty "conv2dSameVjp Bench dInp 6 SymbolicAmortized"
                 (sizedSymbolicAmortizedInp @6)
  , testProperty "conv2dSameVjp Bench dInp 6 HandwrittenVec"
                 (sizedHandwrittenVectorizedInp @6)
  , testProperty "conv2dSameVjp Bench dInp 24 SymbolicPerCall"
                 (sizedSymbolicPerCallInp @24)
  , testProperty "conv2dSameVjp Bench dInp 24 SymbolicAmortized"
                 (sizedSymbolicAmortizedInp @24)
  , testProperty "conv2dSameVjp Bench dInp 24 HandwrittenVec"
                 (sizedHandwrittenVectorizedInp @24)
  -- Shrinking convolution: input larger than output.
  , testProperty "conv2dShrinkingVjp Bench dKrn 6 SymbolicPerCall"
                 (shrinkingSymbolicPerCall @6)
  , testProperty "conv2dShrinkingVjp Bench dKrn 6 SymbolicAmortized"
                 (shrinkingSymbolicAmortized @6)
  , testProperty "conv2dShrinkingVjp Bench dKrn 6 HandwrittenVec"
                 (shrinkingHandwrittenVec @6)
  , testProperty "conv2dShrinkingVjp Bench dKrn 24 SymbolicPerCall"
                 (shrinkingSymbolicPerCall @24)
  , testProperty "conv2dShrinkingVjp Bench dKrn 24 SymbolicAmortized"
                 (shrinkingSymbolicAmortized @24)
  , testProperty "conv2dShrinkingVjp Bench dKrn 24 HandwrittenVec"
                 (shrinkingHandwrittenVec @24)
  , testProperty "conv2dShrinkingVjp Bench dInp 6 SymbolicPerCall"
                 (shrinkingSymbolicPerCallInp @6)
  , testProperty "conv2dShrinkingVjp Bench dInp 6 SymbolicAmortized"
                 (shrinkingSymbolicAmortizedInp @6)
  , testProperty "conv2dShrinkingVjp Bench dInp 6 HandwrittenVec"
                 (shrinkingHandwrittenVecInp @6)
  , testProperty "conv2dShrinkingVjp Bench dInp 24 SymbolicPerCall"
                 (shrinkingSymbolicPerCallInp @24)
  , testProperty "conv2dShrinkingVjp Bench dInp 24 SymbolicAmortized"
                 (shrinkingSymbolicAmortizedInp @24)
  , testProperty "conv2dShrinkingVjp Bench dInp 24 HandwrittenVec"
                 (shrinkingHandwrittenVecInp @24)
  -- Padded convolution: output larger than input.
  , testProperty "conv2dPaddedVjp Bench dKrn 6 SymbolicPerCall"
                 (paddedSymbolicPerCall @6)
  , testProperty "conv2dPaddedVjp Bench dKrn 6 SymbolicAmortized"
                 (paddedSymbolicAmortized @6)
  , testProperty "conv2dPaddedVjp Bench dKrn 6 HandwrittenVec"
                 (paddedHandwrittenVec @6)
  , testProperty "conv2dPaddedVjp Bench dKrn 24 SymbolicPerCall"
                 (paddedSymbolicPerCall @24)
  , testProperty "conv2dPaddedVjp Bench dKrn 24 SymbolicAmortized"
                 (paddedSymbolicAmortized @24)
  , testProperty "conv2dPaddedVjp Bench dKrn 24 HandwrittenVec"
                 (paddedHandwrittenVec @24)
  , testProperty "conv2dPaddedVjp Bench dInp 6 SymbolicPerCall"
                 (paddedSymbolicPerCallInp @6)
  , testProperty "conv2dPaddedVjp Bench dInp 6 SymbolicAmortized"
                 (paddedSymbolicAmortizedInp @6)
  , testProperty "conv2dPaddedVjp Bench dInp 6 HandwrittenVec"
                 (paddedHandwrittenVecInp @6)
  , testProperty "conv2dPaddedVjp Bench dInp 24 SymbolicPerCall"
                 (paddedSymbolicPerCallInp @24)
  , testProperty "conv2dPaddedVjp Bench dInp 24 SymbolicAmortized"
                 (paddedSymbolicAmortizedInp @24)
  , testProperty "conv2dPaddedVjp Bench dInp 24 HandwrittenVec"
                 (paddedHandwrittenVecInp @24)
  ]

-- This one is not convolution-related, but it's also QuickCheck.
tensorADOnceMnistTests2 :: TestTree
tensorADOnceMnistTests2 = inOrderTestGroup "conv2d Ranked2 Once MNIST tests"
  [ testProperty "VTO2 grad vs fwd" $
    \seed0 ->
    forAllShrink (chooseInt (0, 600)) shrinkIntegral $ \width1Hidden ->
    forAllShrink (chooseInt (0, 200)) shrinkIntegral $ \width1Hidden2 ->
    forAllShrink (chooseInt (0, 5)) shrinkIntegral $ \simp ->
    forAll (choose (0.01, 1)) $ \range ->
    forAll (choose (0.01, 1)) $ \range2 ->
    forAll (choose (0.5, 1.5)) $ \dt ->
    forAll (choose (0, 1e-7)) $ \(perturbation :: Double) ->
    withSNat (1 + width1Hidden) $ \(SNat @widthHidden) ->
    withSNat (1 + width1Hidden2) $ \(SNat @widthHidden2) ->
    let (glyph0, seed2) = randomValue @(Concrete (TKS '[SizeMnistGlyph] Double))
                                      0.5 (mkStdGen seed0)
        (label0, seed3) = randomValue @(Concrete (TKS '[SizeMnistLabel] Double))
                                      5 seed2
        (glyph, label) = ( rmap1 (rscalar 0.5 +) $ forgetShape glyph0
                         , rmap1 (rscalar 5 + ) $ forgetShape label0 )
        ds :: Concrete (XParams2 Double Double)
        (ds, seed4) = first forgetShape $
          randomValue
            @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                             Concrete widthHidden widthHidden2 Double Double)))
            range seed3
        (targetInit, artRaw) =
          MnistFcnnRanked2.mnistTrainBench2VTOGradient
            @Double (Proxy @Double) UseIncomingCotangent
            range2 seed4 (1 + width1Hidden) (1 + width1Hidden2)
        art = iterate simplifyArtifactRev artRaw !! simp
        stk = knownSTK @(XParams2 Double Double)
        ftk = tftk @Concrete stk targetInit
        parametersAndInput = tpair targetInit (tpair glyph label)
        (value0, _gradient0) = second tproject1 $
          revInterpretArtifact art parametersAndInput Nothing
        (value1, gradient1) = second tproject1 $
          revInterpretArtifact art parametersAndInput (Just $ kconcrete dt)
        f :: ADVal Concrete (XParams2 Double Double)
          -> ADVal Concrete (TKScalar Double)
        f adinputs =
          MnistFcnnRanked2.afcnnMnistLoss2
            (rfromPrimal glyph, rfromPrimal label) (fromTarget adinputs)
        (value2, derivative2) = cjvp2 f targetInit ds
--        goodDt :: forall r. GoodScalar r => r
--        goodDt = ifDifferentiable @r (realToFrac dt) 0
--        targetDt :: Concrete (XParams2 Double Double)
--        targetDt = replTarget goodDt ftk
        goodPerturbation :: forall r. NumScalar r => r
        goodPerturbation = ifDifferentiable @r (realToFrac perturbation) 0
        targetPerturbed :: Concrete (XParams2 Double Double)
        targetPerturbed = treplTarget goodPerturbation ftk
        targetInitPerturbed :: Concrete (XParams2 Double Double)
        targetInitPerturbed = taddTarget stk targetInit targetPerturbed
        (value3, derivative3) = cjvp2 f targetInit targetPerturbed
        value4 :: Concrete (TKScalar Double)
        value4 = MnistFcnnRanked2.afcnnMnistLoss2
                   (rfromPrimal glyph, rfromPrimal label)
                   (fromTarget targetInitPerturbed)
    in
      conjoin
        [ counterexample
            ("Objective function value from grad and jvp matches: "
             ++ show (value1, value2, value1 - value2))
            (abs (value1 - value2) < 1e-10)
        , counterexample
            ("Gradient and derivative agrees: "
             ++ show ( dt, derivative2, tdot0Target ftk gradient1 ds
                     , tdot0Target FTKScalar (kconcrete dt) derivative2
                       - tdot0Target ftk gradient1 ds ))
            (abs (tdot0Target FTKScalar (kconcrete dt) derivative2
                  - tdot0Target ftk gradient1 ds) < 1e-10)
--        , counterexample  -- this is implied by the other clauses
--            "Gradient is a linear function"
--            (gradient1 === tmultTarget stk targetDt gradient0)
        , counterexample
            "Objective function value unaffected by incoming cotangent"
            (value0 === value1)
        , counterexample
            "Objective function value unaffected by derivative perturbation"
            (value2 === value3)
        , counterexample
            ("Derivative approximates the perturbation of value: "
             ++ show ( value2, derivative3, value4
                     , (value3 + derivative3) - value4) )
            (abs ((value3 + derivative3) - value4) < 1e-6)
        ]
  ]

allClose :: (GoodScalar r, Fractional r, Linearizable a r, Linearizable b r)
         => a -> b -> Rational -> Bool
allClose expected actual eps =
  all (\(a, b) -> abs (a - b) <= fromRational eps)
  $ zip (linearize expected) (linearize actual)

flip42 :: (ADReady target, GoodScalar r)
       => target (TKS '[nCout, nCinp, nKh, nKw] r)
       -> target (TKS '[nCout, nCinp, nKh, nKw] r)
flip42 arr =
  stranspose @'[1, 2, 0]
  $ sreverse
  $ stranspose @'[3, 1, 2, 0]
  $ sreverse
  $ stranspose @'[3, 0, 1, 2] arr

-- | Hand-written reverse derivative of full convolution with respect
-- to the input image.
-- Example code that horde-ad generates for the same is in testSameCNNOPP0bW.
conv2dSame_dInp
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB shB1
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh, KnownNat nKw
     , ADReady target, NumScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , shB1 ~ '[1,     nCout,  nKh, nKw] )
  => target (TKS shK r)
  -> target (TKS shB r)
  -> target (TKS shA r)
conv2dSame_dInp arrK arrB =
  let arrKFlipped = flip42 arrK
      nKh = valueOf @nKh
      nKw = valueOf @nKw
  in sbuild @shA $ \case
    [iImg, iCinp, iAh, iAw] ->
      let arrBt = slicezS @shB1 arrB
                          [iImg,  0, iAh - nKh + 1, iAw - nKw + 1]
          arrKt = slicezS (stranspose @'[1, 0] arrKFlipped)
                          [iCinp, 0 , 0, 0]
      in sfromK $ sdot0 arrBt arrKt
    _ -> error "conv2dSame_dInp: impossible pattern needlessly required"
-- Note that
-- > ... in conv2dSameS (stranspose @'[1, 0] arrKFlipped) arrB
-- type-checks above, but test fails due to the lack of @- nKh + 1@.

-- | Hand-written reverse derivative of full convolution with respect
-- to the kernels.
-- This code vectorized is pretty-printed in test testSameCNNOPPKrnHandwritten.
-- Example code that horde-ad generates for the same is in testSameCNNOPP0cW.
conv2dSame_dKrn
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB shB1
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh, KnownNat nKw
     , ADReady target, NumScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , shB1 ~ '[nImgs, 1,     nAh, nAw] )
  => target (TKS shA r)
  -> target (TKS shB r)
  -> target (TKS shK r)
conv2dSame_dKrn arrA arrB =
  sbuild @shK $ \case
    [iCout, iCinp, iKh, iKw] ->
      let arrBt = slicezS @shB1 arrB
                          [0, iCout, 0, 0]
          arrAt = slicezS arrA
                          [0, iCinp, iKh, iKw]
      in sfromK $ sdot0 arrBt arrAt
    _ -> error "conv2dSame_dKrn: impossible pattern needlessly required"

test_conv2dSameVjp_dInp :: Assertion
test_conv2dSameVjp_dInp =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicatePrim knownShS 1.1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicatePrim knownShS (-2.2)
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 8] Double
      arrB = Nested.sreplicatePrim knownShS (-3.3)
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2dSame_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp @_ @_ @_ @Concrete
                    (conv2dSameS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dSameVjp_dKrn :: Assertion
test_conv2dSameVjp_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicatePrim knownShS 1.1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicatePrim knownShS 2.2
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 8] Double
      arrB = Nested.sreplicatePrim knownShS (-3.3)
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2dSame_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp @_ @_ @_ @Concrete
                    (`conv2dSameS` sconcrete arrA)
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2dSameVjp
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Nested.Shaped shB r
       -- ^ Output gradient of shape:
       --     batch x chas x output_height x output_width
  -> Bool
static_conv2dSameVjp SNat SNat SNat SNat SNat SNat SNat arrK arrA arrB =
  let -- Compare the AD version against the manual derivative.
      -- Note that manual versions don't take one of the arguments (the point
      -- at which the gradient is taken), because maths (something about
      -- convolution being linear and so gradient the same everywhere).
      -- First, the gradient wrt the input image taken at point @arrA@.
      dInp :: Concrete (TKS shA r)
      dInp = conv2dSame_dInp
               (sconcrete arrK) (sconcrete arrB)  -- handwritten
      vjpInp = vjp (conv2dSameS (sconcrete arrK))
                   (sconcrete arrA) (sconcrete arrB)  -- symbolic
      cvjpInp = cvjp @_ @_ @_ @Concrete
                     (conv2dSameS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrB)  -- concrete
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn :: Concrete (TKS shK r)
      dKrn = conv2dSame_dKrn
               (sconcrete arrA) (sconcrete arrB)  -- handwritten
      vjpKrn = vjp (`conv2dSameS` sconcrete arrA)
                   (sconcrete arrK) (sconcrete arrB)  -- symbolic
      cvjpKrn = cvjp @_ @_ @_ @Concrete
                     (`conv2dSameS` sconcrete arrA)
                     (sconcrete arrK) (sconcrete arrB)  -- concrete
  in allClose vjpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cvjpInp dInp 1e-5
     && allClose vjpKrn dKrn 1e-5
     && allClose cvjpKrn dKrn 1e-5

quickcheck_conv2dSameVjp
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjp =
  forAll (choose (0, 5)) $ \nImgs' ->
  forAll (choose (0, 5)) $ \nCinp' ->
  forAll (choose (0, 5)) $ \nCout' ->
  forAll (choose (0, 5)) $ \nAh' ->
  forAll (choose (0, 5)) $ \nAw' ->
  forAll (choose (0, 5)) $ \nKh' ->
  forAll (choose (0, 5)) $ \nKw' ->
    -- The glue below is needed to bridge the dependently-typed
    -- vs normal world.
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjp
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

-- | Hand-written reverse derivative of full shrinking convolution with respect
-- to the input image.
-- The @nKh1@ type variable reads \"nKh - 1\", while @nAh_nKh1@
-- reads \" nAh - nKh1\". We don't use explicit subtraction, because
-- it requires extra constraints to ensure type leven nats are not negative.
-- Example code that horde-ad generates for the same is
-- in testShrinkingCNNOPP0bW.
conv2dShrinking_dInp
  :: forall nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1 shK shA shB
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh_nKh1, KnownNat nAw_nKw1, KnownNat nKh1, KnownNat nKw1
     , ADReady target, NumScalar r
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinp, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1]
     , shB  ~ '[nImgs, nCout, nAh_nKh1, nAw_nKw1] )
  => target (TKS shK r)
  -> target (TKS shB r)
  -> target (TKS shA r)
conv2dShrinking_dInp arrK arrB =
  let arrKFlipped = flip42 arrK
  in conv2dPaddedS (stranspose @'[1, 0] arrKFlipped) arrB

-- | Hand-written reverse derivative of full shrinking convolution with respect
-- to the kernels.
-- The @nKh1@ type variable reads \"nKh - 1\", while @nAh_nKh1@
-- reads \" nAh - nKh1\". We don't use explicit subtraction, because
-- it requires extra constraints to ensure type leven nats are not negative.
-- Example code that horde-ad generates for the same is
-- in testShrinkingCNNOPP0cW.
conv2dShrinking_dKrn
  :: forall nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1 shK shA shB
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh_nKh1, KnownNat nAw_nKw1, KnownNat nKh1, KnownNat nKw1
     , ADReady target, NumScalar r
     , 1 <= nAh_nKh1, 1 <= nAw_nKw1
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinp, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1]
     , shB  ~ '[nImgs, nCout, nAh_nKh1, nAw_nKw1] )
  => target (TKS shA r)
  -> target (TKS shB r)
  -> target (TKS shK r)
conv2dShrinking_dKrn arrA arrB =
  stranspose @'[1, 0]
             (conv2dShrinkingS @_ @_ @_ @_ @_ @_ @(nAh_nKh1 - 1) @(nAw_nKw1 - 1)
                               (stranspose @'[1, 0] arrB)
                               (stranspose @'[1, 0] arrA))

test_conv2dShrinkingVjp_dInp :: Assertion
test_conv2dShrinkingVjp_dInp =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicatePrim knownShS 1.1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicatePrim knownShS (-2.2)
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 6] Double
      arrB = Nested.sreplicatePrim knownShS 3.3
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2dShrinking_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp @_ @_ @_ @Concrete
                    (conv2dShrinkingS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dShrinkingVjp_dKrn :: Assertion
test_conv2dShrinkingVjp_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicatePrim knownShS (-1.1)
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicatePrim knownShS 2.2
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 6] Double
      arrB = Nested.sreplicatePrim knownShS 3.3
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2dShrinking_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp @_ @_ @_ @Concrete
                    (`conv2dShrinkingS` sconcrete arrA)
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2dShrinkingVjp
  :: forall nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1 shK shA shB r.
     ( NumScalar r, Differentiable r
     , 1 <= nAh_nKh1, 1 <= nAw_nKw1
     , shK ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA ~ '[nImgs, nCinp, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1]
     , shB ~ '[nImgs, nCout, nAh_nKh1, nAw_nKw1] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh_nKh1 -> SNat nAw_nKw1 -> SNat nKh1 -> SNat nKw1
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Nested.Shaped shB r
       -- ^ Output gradient of shape:
       --     batch x chas x output_height x output_width
  -> Bool
static_conv2dShrinkingVjp SNat SNat SNat SNat SNat SNat SNat arrK arrA arrB =
  let -- Compare the AD version against the manual derivative.
      -- Note that manual versions don't take one of the arguments (the point
      -- at which the gradient is taken), because maths (something about
      -- convolution being linear and so gradient the same everywhere).
      -- First, the gradient wrt the input image taken at point @arrA@.
      dInp :: Concrete (TKS shA r)
      dInp = conv2dShrinking_dInp
               (sconcrete arrK) (sconcrete arrB)  -- handwritten
      vjpInp = vjp (conv2dShrinkingS (sconcrete arrK))
                   (sconcrete arrA) (sconcrete arrB)  -- symbolic
      cvjpInp = cvjp @_ @_ @_ @Concrete
                     (conv2dShrinkingS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrB)  -- concrete
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn :: Concrete (TKS shK r)
      dKrn = conv2dShrinking_dKrn
               (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = vjp (`conv2dShrinkingS` sconcrete arrA)
                   (sconcrete arrK) (sconcrete arrB)  -- symbolic
      cvjpKrn = cvjp @_ @_ @_ @Concrete
                     (`conv2dShrinkingS` sconcrete arrA)
                     (sconcrete arrK) (sconcrete arrB)  -- concrete
  in allClose vjpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cvjpInp dInp 1e-5
     && allClose vjpKrn dKrn 1e-5
     && allClose cvjpKrn dKrn 1e-5

quickcheck_conv2dShrinkingVjp
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dShrinkingVjp =
  forAll chooseAny $ \(seed0 :: Int) ->
  forAll (choose (0, 5)) $ \nImgs' ->
  forAll (choose (0, 5)) $ \nCinp' ->
  forAll (choose (0, 5)) $ \nCout' ->
  forAll (choose (1, 5)) $ \nAh_nKh1' ->
  forAll (choose (1, 5)) $ \nAw_nKw1' ->
  forAll (choose (0, 5)) $ \nKh1' ->
  forAll (choose (0, 5)) $ \nKw1' ->
    -- The glue below is needed to bridge the dependently-typed
    -- vs normal world.
    -- The @b@ is needed for GHC 9.10 to type-check this code.
    let b :: Bool
        b =
          withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
          withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
          withSNat nCout' $ \(nCout :: SNat nCout) ->
          withSNat nAh_nKh1' $ \(nAh_nKh1 :: SNat nAh_nKh1) ->
          withSNat nAw_nKw1' $ \(nAw_nKw1 :: SNat nAw_nKw1) ->
          withSNat nKh1' $ \(nKh1 :: SNat nKh1) ->
          withSNat nKw1' $ \(nKw1 :: SNat nKw1) ->
            gcastWith (unsafeCoerceRefl :: (1 <=? nAh_nKh1) :~: True) $
            gcastWith (unsafeCoerceRefl :: (1 <=? nAw_nKw1) :~: True) $
              let arrK :: Concrete (TKS '[nCout, nCinp, nKh1 + 1, nKw1 + 1] r)
                  (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
                  arrA :: Concrete (TKS '[ nImgs, nCinp
                                         , nAh_nKh1 + nKh1, nAw_nKw1 + nKw1 ] r)
                  (arrA, seed3) = randomValue 0.5 seed2
                  arrB :: Concrete (TKS '[nImgs, nCout, nAh_nKh1, nAw_nKw1] r)
                  (arrB, _) = randomValue 0.5 seed3
              in static_conv2dShrinkingVjp
                   nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
                   (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)
    in b

-- | Hand-written reverse derivative of full padded convolution with respect
-- to the input image.
-- The @nKh1@ type variable reads \"nKh - 1\".
-- We don't use explicit subtraction, because
-- it requires extra constraints to ensure type leven nats are not negative.
-- Example code that horde-ad generates for the same is
-- in testPaddedCNNOPP0bW.
conv2dPadded_dInp
  :: forall nImgs nCinp nCout nAh nAw nKh1 nKw1 shK shA shB
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh1, KnownNat nKw1
     , ADReady target, NumScalar r
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh + nKh1, nAw + nKw1] )
  => target (TKS shK r)
  -> target (TKS shB r)
  -> target (TKS shA r)
conv2dPadded_dInp arrK arrB =
  let arrKFlipped = flip42 arrK
  in conv2dShrinkingS (stranspose @'[1, 0] arrKFlipped) arrB

-- | Hand-written reverse derivative of full padded convolution with respect
-- to kernels.
-- The @nKh1@ type variable reads \"nKh - 1\".
-- We don't use explicit subtraction, because
-- it requires extra constraints to ensure type leven nats are not negative.
-- Example code that horde-ad generates for the same is
-- in testPaddedCNNOPP0cW.
conv2dPadded_dKrn
  :: forall nImgs nCinp nCout nAh nAw nKh1 nKw1 shK shA shB
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh1, KnownNat nKw1
     , ADReady target, NumScalar r
     , 1 <= nAh, 1 <= nAw
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh + nKh1, nAw + nKw1] )
  => target (TKS shA r)
  -> target (TKS shB r)
  -> target (TKS shK r)
conv2dPadded_dKrn arrA arrB =
  flip42
  $ conv2dShrinkingS @_ @_ @_ @_ @_ @_ @(nAh - 1) @(nAw - 1)
                     (stranspose @'[1, 0] arrA)
                     (stranspose @'[1, 0] arrB)

test_conv2dPaddedVjp_dInp :: Assertion
test_conv2dPaddedVjp_dInp =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicatePrim knownShS 1.1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicatePrim knownShS (-2.2)
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 10] Double
      arrB = Nested.sreplicatePrim knownShS 3.3
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2dPadded_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp @_ @_ @_ @Concrete
                    (conv2dPaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dPaddedVjp_dKrn :: Assertion
test_conv2dPaddedVjp_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicatePrim knownShS (-1.1)
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicatePrim knownShS 2.2
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 10] Double
      arrB = Nested.sreplicatePrim knownShS 3.3
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2dPadded_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp @_ @_ @_ @Concrete
                    (`conv2dPaddedS` sconcrete arrA)
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2dPaddedVjp
  :: forall nImgs nCinp nCout nAh nAw nKh1 nKw1 shK shA shB r.
     ( NumScalar r, Differentiable r
     , 1 <= nAh, 1 <= nAw
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh + nKh1, nAw + nKw1] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh1 -> SNat nKw1
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Nested.Shaped shB r
       -- ^ Output gradient of shape:
       --     batch x chas x output_height x output_width
  -> Bool
static_conv2dPaddedVjp SNat SNat SNat SNat SNat SNat SNat arrK arrA arrB =
  let -- Compare the AD version against the manual derivative.
      -- Note that manual versions don't take one of the arguments (the point
      -- at which the gradient is taken), because maths (something about
      -- convolution being linear and so gradient the same everywhere).
      -- First, the gradient wrt the input image taken at point @arrA@.
      dInp :: Concrete (TKS shA r)
      dInp = conv2dPadded_dInp
               (sconcrete arrK) (sconcrete arrB)  -- handwritten
      vjpInp = vjp (conv2dPaddedS (sconcrete arrK))
                   (sconcrete arrA) (sconcrete arrB)  -- symbolic
      cvjpInp = cvjp @_ @_ @_ @Concrete
                     (conv2dPaddedS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrB)  -- concrete
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn :: Concrete (TKS shK r)
      dKrn = conv2dPadded_dKrn
               (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = vjp (`conv2dPaddedS` sconcrete arrA)
                   (sconcrete arrK) (sconcrete arrB)  -- symbolic
      cvjpKrn = cvjp @_ @_ @_ @Concrete
                     (`conv2dPaddedS` sconcrete arrA)
                     (sconcrete arrK) (sconcrete arrB)  -- concrete
  in allClose vjpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cvjpInp dInp 1e-5
     && allClose vjpKrn dKrn 1e-5
     && allClose cvjpKrn dKrn 1e-5

quickcheck_conv2dPaddedVjp
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dPaddedVjp =
  forAll chooseAny $ \(seed0 :: Int) ->
  forAll (choose (0, 5)) $ \nImgs' ->
  forAll (choose (0, 5)) $ \nCinp' ->
  forAll (choose (0, 5)) $ \nCout' ->
  forAll (choose (1, 5)) $ \nAh' ->
  forAll (choose (1, 5)) $ \nAw' ->
  forAll (choose (0, 5)) $ \nKh1' ->
  forAll (choose (0, 5)) $ \nKw1' ->
    -- The glue below is needed to bridge the dependently-typed
    -- vs normal world.
    -- The @b@ is needed for GHC 9.10 to type-check this code.
    let b :: Bool
        b =
          withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
          withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
          withSNat nCout' $ \(nCout :: SNat nCout) ->
          withSNat nAh' $ \(nAh :: SNat nAh) ->
          withSNat nAw' $ \(nAw :: SNat nAw) ->
          withSNat nKh1' $ \(nKh1 :: SNat nKh1) ->
          withSNat nKw1' $ \(nKw1 :: SNat nKw1) ->
            gcastWith (unsafeCoerceRefl :: (1 <=? nAh) :~: True) $
            gcastWith (unsafeCoerceRefl :: (1 <=? nAw) :~: True) $
              let arrK :: Concrete (TKS '[nCout, nCinp, nKh1 + 1, nKw1 + 1] r)
                  (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
                  arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
                  (arrA, seed3) = randomValue 0.5 seed2
                  arrB
                    :: Concrete (TKS '[nImgs, nCout, nAh + nKh1, nAw + nKw1] r)
                  (arrB, _) = randomValue 0.5 seed3
              in static_conv2dPaddedVjp
                   nImgs nCinp nCout nAh nAw nKh1 nKw1
                   (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)
    in b

-- Forward derivative.
static_conv2dSameJvp
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r -> Nested.Shaped shK r
  -> Nested.Shaped shA r -> Nested.Shaped shA r
  -> Bool
static_conv2dSameJvp SNat SNat SNat SNat SNat SNat SNat
                     arrK arrK2 arrA arrA2 =
  let dInp :: Concrete (TKS shB r)
      dInp = conv2dSameS (sconcrete arrK) (sconcrete arrA2)
      jvpInp = jvp (conv2dSameS (sconcrete arrK))
                   (sconcrete arrA) (sconcrete arrA2)
      cjvpInp = cjvp @_ @_ @_ @Concrete
                     (conv2dSameS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS shB r)
      dKrn = conv2dSameS (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = jvp (`conv2dSameS` sconcrete arrA)
                   (sconcrete arrK) (sconcrete arrK2)
      cjvpKrn = cjvp @_ @_ @_ @Concrete
                     (`conv2dSameS` sconcrete arrA)
                     (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cjvpInp dInp 1e-5
     && allClose jvpKrn dKrn 1e-5
     && allClose cjvpKrn dKrn 1e-5

quickcheck_conv2dSameJvp
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameJvp =
  forAll (choose (0, 5)) $ \nImgs' ->
  forAll (choose (0, 5)) $ \nCinp' ->
  forAll (choose (0, 5)) $ \nCout' ->
  forAll (choose (0, 5)) $ \nAh' ->
  forAll (choose (0, 5)) $ \nAw' ->
  forAll (choose (0, 5)) $ \nKh' ->
  forAll (choose (0, 5)) $ \nKw' ->
    -- The glue below is needed to bridge the dependently-typed
    -- vs normal world.
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK, arrK2 :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            (arrK2, seed3) = randomValue 0.5 seed2
            arrA, arrA2 :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed4) = randomValue 0.5 seed3
            (arrA2, _) = randomValue 0.5 seed4
        in static_conv2dSameJvp
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrK2)
             (unConcrete arrA) (unConcrete arrA2)

-- Forward derivative.
static_conv2dShrinkingJvp
  :: forall nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1 shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA ~ '[nImgs, nCinp, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1]
     , shB  ~ '[nImgs, nCout, nAh_nKh1, nAw_nKw1])
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh_nKh1 -> SNat nAw_nKw1 -> SNat nKh1 -> SNat nKw1
  -> Nested.Shaped shK r -> Nested.Shaped shK r
  -> Nested.Shaped shA r -> Nested.Shaped shA r
  -> Bool
static_conv2dShrinkingJvp SNat SNat SNat SNat SNat SNat SNat
                          arrK arrK2 arrA arrA2 =
  let dInp :: Concrete (TKS shB r)
      dInp = conv2dShrinkingS (sconcrete arrK) (sconcrete arrA2)
      jvpInp = jvp (conv2dShrinkingS (sconcrete arrK))
                   (sconcrete arrA) (sconcrete arrA2)
      cjvpInp = cjvp @_ @_ @_ @Concrete
                     (conv2dShrinkingS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS shB r)
      dKrn = conv2dShrinkingS (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = jvp (`conv2dShrinkingS` sconcrete arrA)
                   (sconcrete arrK) (sconcrete arrK2)
      cjvpKrn = cjvp @_ @_ @_ @Concrete
                     (`conv2dShrinkingS` sconcrete arrA)
                     (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cjvpInp dInp 1e-5
     && allClose jvpKrn dKrn 1e-5
     && allClose cjvpKrn dKrn 1e-5

quickcheck_conv2dShrinkingJvp
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dShrinkingJvp =
  forAll (choose (0, 5)) $ \nImgs' ->
  forAll (choose (0, 5)) $ \nCinp' ->
  forAll (choose (0, 5)) $ \nCout' ->
  forAll (choose (0, 5)) $ \nAh_nKh1' ->
  forAll (choose (0, 5)) $ \nAw_nKw1' ->
  forAll (choose (0, 5)) $ \nKh1' ->
  forAll (choose (0, 5)) $ \nKw1' ->
    -- The glue below is needed to bridge the dependently-typed
    -- vs normal world.
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh_nKh1' $ \(nAh_nKh1 :: SNat nAh_nKh1) ->
    withSNat nAw_nKw1' $ \(nAw_nKw1 :: SNat nAw_nKw1) ->
    withSNat nKh1' $ \(nKh1 :: SNat nKh1) ->
    withSNat nKw1' $ \(nKw1 :: SNat nKw1) ->
      property $ \seed0 ->
        let arrK, arrK2 :: Concrete (TKS '[nCout, nCinp, nKh1 + 1, nKw1 + 1] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            (arrK2, seed3) = randomValue 0.5 seed2
            arrA, arrA2
              :: Concrete
                   (TKS '[nImgs, nCinp, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1] r)
            (arrA, seed4) = randomValue 0.5 seed3
            (arrA2, _) = randomValue 0.5 seed4
        in static_conv2dShrinkingJvp
             nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
             (unConcrete arrK) (unConcrete arrK2)
             (unConcrete arrA) (unConcrete arrA2)

-- Forward derivative.
static_conv2dPaddedJvp
  :: forall nImgs nCinp nCout nAh nAw nKh1 nKw1 shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh + nKh1, nAw + nKw1] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh1 -> SNat nKw1
  -> Nested.Shaped shK r -> Nested.Shaped shK r
  -> Nested.Shaped shA r -> Nested.Shaped shA r
  -> Bool
static_conv2dPaddedJvp SNat SNat SNat SNat SNat SNat SNat
                       arrK arrK2 arrA arrA2 =
  let dInp :: Concrete (TKS shB r)
      dInp = conv2dPaddedS (sconcrete arrK) (sconcrete arrA2)
      jvpInp = jvp (conv2dPaddedS (sconcrete arrK))
                   (sconcrete arrA) (sconcrete arrA2)
      cjvpInp = cjvp @_ @_ @_ @Concrete
                     (conv2dPaddedS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS shB r)
      dKrn = conv2dPaddedS (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = jvp (`conv2dPaddedS` sconcrete arrA)
                   (sconcrete arrK) (sconcrete arrK2)
      cjvpKrn = cjvp @_ @_ @_ @Concrete
                     (`conv2dPaddedS` sconcrete arrA)
                     (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cjvpInp dInp 1e-5
     && allClose jvpKrn dKrn 1e-5
     && allClose cjvpKrn dKrn 1e-5

quickcheck_conv2dPaddedJvp
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dPaddedJvp =
  forAll (choose (0, 5)) $ \nImgs' ->
  forAll (choose (0, 5)) $ \nCinp' ->
  forAll (choose (0, 5)) $ \nCout' ->
  forAll (choose (0, 5)) $ \nAh' ->
  forAll (choose (0, 5)) $ \nAw' ->
  forAll (choose (0, 5)) $ \nKh1' ->
  forAll (choose (0, 5)) $ \nKw1' ->
    -- The glue below is needed to bridge the dependently-typed
    -- vs normal world.
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh1' $ \(nKh1 :: SNat nKh1) ->
    withSNat nKw1' $ \(nKw1 :: SNat nKw1) ->
      property $ \seed0 ->
        let arrK, arrK2 :: Concrete (TKS '[nCout, nCinp, nKh1 + 1, nKw1 + 1] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            (arrK2, seed3) = randomValue 0.5 seed2
            arrA, arrA2 :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed4) = randomValue 0.5 seed3
            (arrA2, _) = randomValue 0.5 seed4
        in static_conv2dPaddedJvp
             nImgs nCinp nCout nAh nAw nKh1 nKw1
             (unConcrete arrK) (unConcrete arrK2)
             (unConcrete arrA) (unConcrete arrA2)


-- * Tests as poor man's benchmarks of handwritten vs generated gradients

static_conv2dSameVjpKrnHandwritten
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
  -> Nested.Shaped shA r
  -> Nested.Shaped shB r
  -> Bool
static_conv2dSameVjpKrnHandwritten SNat SNat SNat SNat SNat SNat SNat
                                   !_arrK arrA arrB =
  let dKrn :: Concrete (TKS shK r)
      dKrn = conv2dSame_dKrn (sconcrete arrA) (sconcrete arrB)
  in allClose dKrn dKrn 1e-5

quickcheck_conv2dSameVjpKrnHandwritten
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjpKrnHandwritten =
  forAll (choose (3, 3)) $ \nImgs' ->
  forAll (choose (3, 3)) $ \nCinp' ->
  forAll (choose (3, 3)) $ \nCout' ->
  forAll (choose (6, 6)) $ \nAh' ->
  forAll (choose (6, 6)) $ \nAw' ->
  forAll (choose (3, 3)) $ \nKh' ->
  forAll (choose (3, 3)) $ \nKw' ->
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjpKrnHandwritten
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

static_conv2dSameVjpKrnHandwrittenVectorized
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
  -> Nested.Shaped shA r
  -> Nested.Shaped shB r
  -> Bool
static_conv2dSameVjpKrnHandwrittenVectorized SNat SNat SNat SNat SNat SNat SNat
                                             !_arrK arrA arrB =
  let dKrn :: Concrete (TKS shK r)
      dKrn = interpretAstFull emptyEnv
             $ conv2dSame_dKrn (sconcrete arrA) (sconcrete arrB)
  in allClose dKrn dKrn 1e-5

quickcheck_conv2dSameVjpKrnHandwrittenVectorized
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjpKrnHandwrittenVectorized =
  forAll (choose (3, 3)) $ \nImgs' ->
  forAll (choose (3, 3)) $ \nCinp' ->
  forAll (choose (3, 3)) $ \nCout' ->
  forAll (choose (6, 6)) $ \nAh' ->
  forAll (choose (6, 6)) $ \nAw' ->
  forAll (choose (3, 3)) $ \nKh' ->
  forAll (choose (3, 3)) $ \nKw' ->
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjpKrnHandwrittenVectorized
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

static_conv2dSameVjpKrnSymbolic
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
  -> Nested.Shaped shA r
  -> Nested.Shaped shB r
  -> Bool
static_conv2dSameVjpKrnSymbolic SNat SNat SNat SNat SNat SNat SNat
                                arrK arrA arrB =
  let vjpKrn :: Concrete (TKS shK r)
      vjpKrn = vjp (`conv2dSameS` sconcrete arrA)
                   (sconcrete arrK) (sconcrete arrB)
  in allClose vjpKrn vjpKrn 1e-5

quickcheck_conv2dSameVjpKrnSymbolic
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjpKrnSymbolic =
  forAll (choose (3, 3)) $ \nImgs' ->
  forAll (choose (3, 3)) $ \nCinp' ->
  forAll (choose (3, 3)) $ \nCout' ->
  forAll (choose (6, 6)) $ \nAh' ->
  forAll (choose (6, 6)) $ \nAw' ->
  forAll (choose (3, 3)) $ \nKh' ->
  forAll (choose (3, 3)) $ \nKw' ->
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjpKrnSymbolic
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

static_conv2dSameVjpKrnConcrete
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
  -> Nested.Shaped shA r
  -> Nested.Shaped shB r
  -> Bool
static_conv2dSameVjpKrnConcrete SNat SNat SNat SNat SNat SNat SNat
                                arrK arrA arrB =
  let cvjpKrn :: Concrete (TKS shK r)
      cvjpKrn = cvjp @_ @_ @_ @Concrete
                     (`conv2dSameS` sconcrete arrA)
                     (sconcrete arrK) (sconcrete arrB)
  in allClose cvjpKrn cvjpKrn 1e-5

quickcheck_conv2dSameVjpKrnConcrete
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjpKrnConcrete =
  forAll (choose (3, 3)) $ \nImgs' ->
  forAll (choose (3, 3)) $ \nCinp' ->
  forAll (choose (3, 3)) $ \nCout' ->
  forAll (choose (6, 6)) $ \nAh' ->
  forAll (choose (6, 6)) $ \nAw' ->
  forAll (choose (3, 3)) $ \nKh' ->
  forAll (choose (3, 3)) $ \nKw' ->
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjpKrnConcrete
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

static_conv2dSameVjpInpHandwritten
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
  -> Nested.Shaped shA r
  -> Nested.Shaped shB r
  -> Bool
static_conv2dSameVjpInpHandwritten SNat SNat SNat SNat SNat SNat SNat
                                   arrK !_arrA arrB =
  let dInp :: Concrete (TKS shA r)
      dInp = conv2dSame_dInp (sconcrete arrK) (sconcrete arrB)
  in allClose dInp dInp 1e-5

quickcheck_conv2dSameVjpInpHandwritten
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjpInpHandwritten =
  forAll (choose (3, 3)) $ \nImgs' ->
  forAll (choose (3, 3)) $ \nCinp' ->
  forAll (choose (3, 3)) $ \nCout' ->
  forAll (choose (6, 6)) $ \nAh' ->
  forAll (choose (6, 6)) $ \nAw' ->
  forAll (choose (3, 3)) $ \nKh' ->
  forAll (choose (3, 3)) $ \nKw' ->
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjpInpHandwritten
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

static_conv2dSameVjpInpHandwrittenVectorized
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
  -> Nested.Shaped shA r
  -> Nested.Shaped shB r
  -> Bool
static_conv2dSameVjpInpHandwrittenVectorized SNat SNat SNat SNat SNat SNat SNat
                                             arrK !_arrA arrB =
  let dInp :: Concrete (TKS shA r)
      dInp = interpretAstFull emptyEnv
             $ conv2dSame_dInp (sconcrete arrK) (sconcrete arrB)
  in allClose dInp dInp 1e-5

quickcheck_conv2dSameVjpInpHandwrittenVectorized
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjpInpHandwrittenVectorized =
  forAll (choose (3, 3)) $ \nImgs' ->
  forAll (choose (3, 3)) $ \nCinp' ->
  forAll (choose (3, 3)) $ \nCout' ->
  forAll (choose (6, 6)) $ \nAh' ->
  forAll (choose (6, 6)) $ \nAw' ->
  forAll (choose (3, 3)) $ \nKh' ->
  forAll (choose (3, 3)) $ \nKw' ->
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjpInpHandwrittenVectorized
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

static_conv2dSameVjpInpSymbolic
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
  -> Nested.Shaped shA r
  -> Nested.Shaped shB r
  -> Bool
static_conv2dSameVjpInpSymbolic SNat SNat SNat SNat SNat SNat SNat
                                arrK arrA arrB =
  let vjpInp :: Concrete (TKS shA r)
      vjpInp = vjp (conv2dSameS (sconcrete arrK))
                   (sconcrete arrA) (sconcrete arrB)
  in allClose vjpInp vjpInp 1e-5

quickcheck_conv2dSameVjpInpSymbolic
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjpInpSymbolic =
  forAll (choose (3, 3)) $ \nImgs' ->
  forAll (choose (3, 3)) $ \nCinp' ->
  forAll (choose (3, 3)) $ \nCout' ->
  forAll (choose (6, 6)) $ \nAh' ->
  forAll (choose (6, 6)) $ \nAw' ->
  forAll (choose (3, 3)) $ \nKh' ->
  forAll (choose (3, 3)) $ \nKw' ->
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjpInpSymbolic
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

static_conv2dSameVjpInpConcrete
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( NumScalar r, Differentiable r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
  -> Nested.Shaped shA r
  -> Nested.Shaped shB r
  -> Bool
static_conv2dSameVjpInpConcrete SNat SNat SNat SNat SNat SNat SNat
                                arrK arrA arrB =
  let cvjpInp :: Concrete (TKS shA r)
      cvjpInp = cvjp @_ @_ @_ @Concrete
                     (conv2dSameS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrB)
  in allClose cvjpInp cvjpInp 1e-5

quickcheck_conv2dSameVjpInpConcrete
  :: forall r. (NumScalar r, Differentiable r)
  => Property
quickcheck_conv2dSameVjpInpConcrete =
  forAll (choose (3, 3)) $ \nImgs' ->
  forAll (choose (3, 3)) $ \nCinp' ->
  forAll (choose (3, 3)) $ \nCout' ->
  forAll (choose (6, 6)) $ \nAh' ->
  forAll (choose (6, 6)) $ \nAw' ->
  forAll (choose (3, 3)) $ \nKh' ->
  forAll (choose (3, 3)) $ \nKw' ->
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh' $ \(nAh :: SNat nAh) ->
    withSNat nAw' $ \(nAw :: SNat nAw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dSameVjpInpConcrete
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)


-- * Honest, size-scaled poor man's benchmarks
--
-- The @Bench dKrn Symbolic@ property above calls full @vjp@ on every run
-- with the (per-run random) input baked into the objective, so it rebuilds
-- and re-simplifies the derivative artifact each run. That build cost is a
-- roughly size-independent tax that symbolic AD is meant to pay once and
-- amortize over many interpretations, so a per-call poor man's benchmark
-- overstates the cost of symbolic AD relative to its intended use. These
-- variants make the distinction explicit and scale @nAh = nAw@, keeping
-- @nImgs = nCinp = nCout = 3@ and @nKh = nKw = 3@:
--
-- * @SymbolicPerCall@ rebuilds the artifact every run (the honest cost of
--   the misleading poor man's benchmark above);
-- * @SymbolicAmortized@ builds the artifact once (shared across all runs)
--   and only interprets it per run — the intended usage;
-- * @HandwrittenVec@ is the handwritten gradient vectorized and interpreted
--   per run, for comparison.
--
-- At small sizes the build tax roughly doubles the per-call symbolic time
-- while the amortized cost is competitive with the handwritten one; as the
-- size grows the fixed tax shrinks relative to interpretation.

-- | Kernel, input and output-gradient of the poor man's benchmark shapes
-- (@nImgs = nCinp = nCout = 3@, @nKh = nKw = 3@, @nAh = nAw@), from one seed.
benchData
  :: forall nAw r. (KnownNat nAw, NumScalar r)
  => Int
  -> ( Concrete (TKS '[3, 3, 3, 3] r)
     , Concrete (TKS '[3, 3, nAw, nAw] r)
     , Concrete (TKS '[3, 3, nAw, nAw] r) )
benchData seed =
  let (arrK, seed2) = randomValue 0.5 (mkStdGen seed)
      (arrA, seed3) = randomValue 0.5 seed2
      (arrB, _) = randomValue 0.5 seed3
  in (arrK, arrA, arrB)

sizedSymbolicPerCall :: forall nAw. KnownNat nAw => Property
sizedSymbolicPerCall =
  property $ \seed0 ->
    let (arrK, arrA, arrB) = benchData @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, 3, 3] Double)
        v = vjp (`conv2dSameS` sconcrete (unConcrete arrA))
                (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

sizedSymbolicAmortized :: forall nAw. KnownNat nAw => Property
sizedSymbolicAmortized =
  let (arrK0, arrA0, _) = benchData @nAw @Double 1
      -- Built once and shared as a thunk across every property run.
      art = simplifyArtifactRev
            $ vjpArtifact (`conv2dSameS` sconcrete (unConcrete arrA0))
                          (sconcrete (unConcrete arrK0)
                           :: Concrete (TKS '[3, 3, 3, 3] Double))
  in property $ \seed0 ->
       let (_, _, arrB) = benchData @nAw @Double seed0
           v :: Concrete (TKS '[3, 3, 3, 3] Double)
           v = vjpInterpretArtifact art (sconcrete (unConcrete arrK0))
                                        (sconcrete (unConcrete arrB))
       in allClose v v 1e-5

sizedHandwrittenVectorized :: forall nAw. KnownNat nAw => Property
sizedHandwrittenVectorized =
  property $ \seed0 ->
    let (_, arrA, arrB) = benchData @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, 3, 3] Double)
        v = interpretAstFull emptyEnv
            $ conv2dSame_dKrn @3 @3 @3 @nAw @nAw @3 @3
                              (sconcrete (unConcrete arrA))
                              (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

-- The same trio, for the input gradient (the @sscatter@ path).

sizedSymbolicPerCallInp :: forall nAw. KnownNat nAw => Property
sizedSymbolicPerCallInp =
  property $ \seed0 ->
    let (arrK, arrA, arrB) = benchData @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, nAw, nAw] Double)
        v = vjp (conv2dSameS (sconcrete (unConcrete arrK)))
                (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

sizedSymbolicAmortizedInp :: forall nAw. KnownNat nAw => Property
sizedSymbolicAmortizedInp =
  let (arrK0, arrA0, _) = benchData @nAw @Double 1
      art = simplifyArtifactRev
            $ vjpArtifact (conv2dSameS (sconcrete (unConcrete arrK0)))
                          (sconcrete (unConcrete arrA0)
                           :: Concrete (TKS '[3, 3, nAw, nAw] Double))
  in property $ \seed0 ->
       let (_, _, arrB) = benchData @nAw @Double seed0
           v :: Concrete (TKS '[3, 3, nAw, nAw] Double)
           v = vjpInterpretArtifact art (sconcrete (unConcrete arrA0))
                                        (sconcrete (unConcrete arrB))
       in allClose v v 1e-5

sizedHandwrittenVectorizedInp :: forall nAw. KnownNat nAw => Property
sizedHandwrittenVectorizedInp =
  property $ \seed0 ->
    let (arrK, _, arrB) = benchData @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, nAw, nAw] Double)
        v = interpretAstFull emptyEnv
            $ conv2dSame_dInp @3 @3 @3 @nAw @nAw @3 @3
                              (sconcrete (unConcrete arrK))
                              (sconcrete (unConcrete arrB))
    in allClose v v 1e-5


-- * The shrinking convolution variant
--
-- Kernel is 3x3, so with output size @nAw@ the input is @(nAw+2)^2@ (the
-- output shrinks by the kernel size minus one). The poor man's benchmarks
-- mirror the @Same@ ones above.

benchDataShrinking
  :: forall nAw r. (KnownNat nAw, NumScalar r)
  => Int
  -> ( Concrete (TKS '[3, 3, 3, 3] r)
     , Concrete (TKS '[3, 3, nAw + 2, nAw + 2] r)
     , Concrete (TKS '[3, 3, nAw, nAw] r) )
benchDataShrinking seed =
  let (arrK, seed2) = randomValue 0.5 (mkStdGen seed)
      (arrA, seed3) = randomValue 0.5 seed2
      (arrB, _) = randomValue 0.5 seed3
  in (arrK, arrA, arrB)

shrinkingSymbolicPerCall :: forall nAw. (KnownNat nAw, 1 <= nAw) => Property
shrinkingSymbolicPerCall =
  property $ \seed0 ->
    let (arrK, arrA, arrB) = benchDataShrinking @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, 3, 3] Double)
        v = vjp (`conv2dShrinkingS` sconcrete (unConcrete arrA))
                (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

shrinkingSymbolicAmortized :: forall nAw. (KnownNat nAw, 1 <= nAw) => Property
shrinkingSymbolicAmortized =
  let (arrK0, arrA0, _) = benchDataShrinking @nAw @Double 1
      art = simplifyArtifactRev
            $ vjpArtifact (`conv2dShrinkingS` sconcrete (unConcrete arrA0))
                          (sconcrete (unConcrete arrK0)
                           :: Concrete (TKS '[3, 3, 3, 3] Double))
  in property $ \seed0 ->
       let (_, _, arrB) = benchDataShrinking @nAw @Double seed0
           v :: Concrete (TKS '[3, 3, 3, 3] Double)
           v = vjpInterpretArtifact art (sconcrete (unConcrete arrK0))
                                        (sconcrete (unConcrete arrB))
       in allClose v v 1e-5

shrinkingHandwrittenVec :: forall nAw. (KnownNat nAw, 1 <= nAw) => Property
shrinkingHandwrittenVec =
  property $ \seed0 ->
    let (_, arrA, arrB) = benchDataShrinking @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, 3, 3] Double)
        v = interpretAstFull emptyEnv
            $ conv2dShrinking_dKrn @3 @3 @3 @nAw @nAw @2 @2
                                   (sconcrete (unConcrete arrA))
                                   (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

-- The same trio, for the input gradient (the @sscatter@ path).

shrinkingSymbolicPerCallInp :: forall nAw. KnownNat nAw => Property
shrinkingSymbolicPerCallInp =
  property $ \seed0 ->
    let (arrK, arrA, arrB) = benchDataShrinking @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, nAw + 2, nAw + 2] Double)
        v = vjp (conv2dShrinkingS (sconcrete (unConcrete arrK)))
                (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

shrinkingSymbolicAmortizedInp :: forall nAw. KnownNat nAw => Property
shrinkingSymbolicAmortizedInp =
  let (arrK0, arrA0, _) = benchDataShrinking @nAw @Double 1
      art = simplifyArtifactRev
            $ vjpArtifact (conv2dShrinkingS (sconcrete (unConcrete arrK0)))
                          (sconcrete (unConcrete arrA0)
                           :: Concrete (TKS '[3, 3, nAw + 2, nAw + 2] Double))
  in property $ \seed0 ->
       let (_, _, arrB) = benchDataShrinking @nAw @Double seed0
           v :: Concrete (TKS '[3, 3, nAw + 2, nAw + 2] Double)
           v = vjpInterpretArtifact art (sconcrete (unConcrete arrA0))
                                        (sconcrete (unConcrete arrB))
       in allClose v v 1e-5

shrinkingHandwrittenVecInp :: forall nAw. KnownNat nAw => Property
shrinkingHandwrittenVecInp =
  property $ \seed0 ->
    let (arrK, _, arrB) = benchDataShrinking @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, nAw + 2, nAw + 2] Double)
        v = interpretAstFull emptyEnv
            $ conv2dShrinking_dInp @3 @3 @3 @nAw @nAw @2 @2
                                   (sconcrete (unConcrete arrK))
                                   (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

-- * The padded convolution variant
--
-- Kernel is 3x3, so with input size @nAw@ the output is @(nAw+2)^2@ (the
-- output grows). The poor man's benchmarks mirror the @Same@ ones above.

benchDataPadded
  :: forall nAw r. (KnownNat nAw, NumScalar r)
  => Int
  -> ( Concrete (TKS '[3, 3, 3, 3] r)
     , Concrete (TKS '[3, 3, nAw, nAw] r)
     , Concrete (TKS '[3, 3, nAw + 2, nAw + 2] r) )
benchDataPadded seed =
  let (arrK, seed2) = randomValue 0.5 (mkStdGen seed)
      (arrA, seed3) = randomValue 0.5 seed2
      (arrB, _) = randomValue 0.5 seed3
  in (arrK, arrA, arrB)

paddedSymbolicPerCall :: forall nAw. (KnownNat nAw, 1 <= nAw) => Property
paddedSymbolicPerCall =
  property $ \seed0 ->
    let (arrK, arrA, arrB) = benchDataPadded @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, 3, 3] Double)
        v = vjp (`conv2dPaddedS` sconcrete (unConcrete arrA))
                (sconcrete (unConcrete arrK)) (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

paddedSymbolicAmortized :: forall nAw. (KnownNat nAw, 1 <= nAw) => Property
paddedSymbolicAmortized =
  let (arrK0, arrA0, _) = benchDataPadded @nAw @Double 1
      art = simplifyArtifactRev
            $ vjpArtifact (`conv2dPaddedS` sconcrete (unConcrete arrA0))
                          (sconcrete (unConcrete arrK0)
                           :: Concrete (TKS '[3, 3, 3, 3] Double))
  in property $ \seed0 ->
       let (_, _, arrB) = benchDataPadded @nAw @Double seed0
           v :: Concrete (TKS '[3, 3, 3, 3] Double)
           v = vjpInterpretArtifact art (sconcrete (unConcrete arrK0))
                                        (sconcrete (unConcrete arrB))
       in allClose v v 1e-5

paddedHandwrittenVec :: forall nAw. (KnownNat nAw, 1 <= nAw) => Property
paddedHandwrittenVec =
  property $ \seed0 ->
    let (_, arrA, arrB) = benchDataPadded @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, 3, 3] Double)
        v = interpretAstFull emptyEnv
            $ conv2dPadded_dKrn @3 @3 @3 @nAw @nAw @2 @2
                                (sconcrete (unConcrete arrA))
                                (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

-- The same trio, for the input gradient (the @sscatter@ path).

paddedSymbolicPerCallInp :: forall nAw. KnownNat nAw => Property
paddedSymbolicPerCallInp =
  property $ \seed0 ->
    let (arrK, arrA, arrB) = benchDataPadded @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, nAw, nAw] Double)
        v = vjp (conv2dPaddedS (sconcrete (unConcrete arrK)))
                (sconcrete (unConcrete arrA)) (sconcrete (unConcrete arrB))
    in allClose v v 1e-5

paddedSymbolicAmortizedInp :: forall nAw. KnownNat nAw => Property
paddedSymbolicAmortizedInp =
  let (arrK0, arrA0, _) = benchDataPadded @nAw @Double 1
      art = simplifyArtifactRev
            $ vjpArtifact (conv2dPaddedS (sconcrete (unConcrete arrK0)))
                          (sconcrete (unConcrete arrA0)
                           :: Concrete (TKS '[3, 3, nAw, nAw] Double))
  in property $ \seed0 ->
       let (_, _, arrB) = benchDataPadded @nAw @Double seed0
           v :: Concrete (TKS '[3, 3, nAw, nAw] Double)
           v = vjpInterpretArtifact art (sconcrete (unConcrete arrA0))
                                        (sconcrete (unConcrete arrB))
       in allClose v v 1e-5

paddedHandwrittenVecInp :: forall nAw. KnownNat nAw => Property
paddedHandwrittenVecInp =
  property $ \seed0 ->
    let (arrK, _, arrB) = benchDataPadded @nAw @Double seed0
        v :: Concrete (TKS '[3, 3, nAw, nAw] Double)
        v = interpretAstFull emptyEnv
            $ conv2dPadded_dInp @3 @3 @3 @nAw @nAw @2 @2
                                (sconcrete (unConcrete arrK))
                                (sconcrete (unConcrete arrB))
    in allClose v v 1e-5
