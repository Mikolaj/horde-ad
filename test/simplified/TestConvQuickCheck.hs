{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | QuickCheck tests of convolution AD derivatives vs handwritten derivatives.
module TestConvQuickCheck (testTrees, conv2dSame_dKrn) where

import Prelude

import Data.Type.Equality (gcastWith, (:~:))
import GHC.TypeLits (KnownNat, type (+), type (-), type (<=), type (<=?))
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.QuickCheck hiding (label, shuffle)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstInterpret

import EqEpsilon
import Shared

testTrees :: [TestTree]
testTrees =
  [ testCase "conv2dSameVjp dInp" test_conv2dSameVjp_dInp
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
     , ADReady target, GoodScalar r
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
  in sbuild @(Rank shA) $ \case
    [iImg, iCinp, iAh, iAw] ->
      let arrBt = slicezS @shB1 arrB
                          [iImg,  0, iAh - nKh + 1, iAw - nKw + 1]
          arrKt = slicezS (stranspose @'[1, 0] arrKFlipped)
                          [iCinp, 0 , 0, 0]
      in sdot0 arrBt arrKt
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
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , shB1 ~ '[nImgs, 1,     nAh, nAw] )
  => target (TKS shA r)
  -> target (TKS shB r)
  -> target (TKS shK r)
conv2dSame_dKrn arrA arrB =
  sbuild @(Rank shK) $ \case
    [iCout, iCinp, iKh, iKw] ->
      let arrBt = slicezS @shB1 arrB
                          [0, iCout, 0, 0]
          arrAt = slicezS arrA
                          [0, iCinp, iKh, iKw]
      in sdot0 arrBt arrAt
    _ -> error "conv2dSame_dKrn: impossible pattern needlessly required"

test_conv2dSameVjp_dInp :: Assertion
test_conv2dSameVjp_dInp =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1.1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS (-2.2)
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 8] Double
      arrB = Nested.sreplicateScal knownShS (-3.3)
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2dSame_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp (conv2dSameS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dSameVjp_dKrn :: Assertion
test_conv2dSameVjp_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1.1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS 2.2
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 8] Double
      arrB = Nested.sreplicateScal knownShS (-3.3)
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2dSame_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp (`conv2dSameS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2dSameVjp
  :: forall nImgs nCinp nCout nAh nAw nKh nKw shK shA shB r.
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      cvjpInp = cvjp (conv2dSameS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrB)  -- concrete
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn :: Concrete (TKS shK r)
      dKrn = conv2dSame_dKrn
               (sconcrete arrA) (sconcrete arrB)  -- handwritten
      vjpKrn = vjp (`conv2dSameS` (sconcrete arrA))
                   (sconcrete arrK) (sconcrete arrB)  -- symbolic
      cvjpKrn = cvjp (`conv2dSameS` (sconcrete arrA))
                     (sconcrete arrK) (sconcrete arrB)  -- concrete
  in allClose vjpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cvjpInp dInp 1e-5
     && allClose vjpKrn dKrn 1e-5
     && allClose cvjpKrn dKrn 1e-5

quickcheck_conv2dSameVjp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     , ADReady target, GoodScalar r
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
     , ADReady target, GoodScalar r
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
      arrA = Nested.sreplicateScal knownShS 1.1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS (-2.2)
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 6] Double
      arrB = Nested.sreplicateScal knownShS 3.3
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2dShrinking_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp (conv2dShrinkingS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dShrinkingVjp_dKrn :: Assertion
test_conv2dShrinkingVjp_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS (-1.1)
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS 2.2
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 6] Double
      arrB = Nested.sreplicateScal knownShS 3.3
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2dShrinking_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp (`conv2dShrinkingS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2dShrinkingVjp
  :: forall nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1 shK shA shB r.
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      cvjpInp = cvjp (conv2dShrinkingS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrB)  -- concrete
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn :: Concrete (TKS shK r)
      dKrn = conv2dShrinking_dKrn
               (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = vjp (`conv2dShrinkingS` (sconcrete arrA))
                   (sconcrete arrK) (sconcrete arrB)  -- symbolic
      cvjpKrn = cvjp (`conv2dShrinkingS` (sconcrete arrA))
                     (sconcrete arrK) (sconcrete arrB)  -- concrete
  in allClose vjpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cvjpInp dInp 1e-5
     && allClose vjpKrn dKrn 1e-5
     && allClose cvjpKrn dKrn 1e-5

quickcheck_conv2dShrinkingVjp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     , ADReady target, GoodScalar r
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
     , ADReady target, GoodScalar r
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
      arrA = Nested.sreplicateScal knownShS 1.1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS (-2.2)
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 10] Double
      arrB = Nested.sreplicateScal knownShS 3.3
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2dPadded_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp (conv2dPaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dPaddedVjp_dKrn :: Assertion
test_conv2dPaddedVjp_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS (-1.1)
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS 2.2
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 10] Double
      arrB = Nested.sreplicateScal knownShS 3.3
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2dPadded_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp (`conv2dPaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2dPaddedVjp
  :: forall nImgs nCinp nCout nAh nAw nKh1 nKw1 shK shA shB r.
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      cvjpInp = cvjp (conv2dPaddedS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrB)  -- concrete
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn :: Concrete (TKS shK r)
      dKrn = conv2dPadded_dKrn
               (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = vjp (`conv2dPaddedS` (sconcrete arrA))
                   (sconcrete arrK) (sconcrete arrB)  -- symbolic
      cvjpKrn = cvjp (`conv2dPaddedS` (sconcrete arrA))
                     (sconcrete arrK) (sconcrete arrB)  -- concrete
  in allClose vjpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose cvjpInp dInp 1e-5
     && allClose vjpKrn dKrn 1e-5
     && allClose cvjpKrn dKrn 1e-5

quickcheck_conv2dPaddedVjp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      cjvpInp = cjvp (conv2dSameS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS shB r)
      dKrn = conv2dSameS (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = jvp (`conv2dSameS` (sconcrete arrA))
                   (sconcrete arrK) (sconcrete arrK2)
      cjvpKrn = cjvp (`conv2dSameS` (sconcrete arrA))
                     (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-7
     && allClose cjvpInp dInp 1e-7
     && allClose jvpKrn dKrn 1e-7
     && allClose cjvpKrn dKrn 1e-7

quickcheck_conv2dSameJvp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      cjvpInp = cjvp (conv2dShrinkingS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS shB r)
      dKrn = conv2dShrinkingS (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = jvp (`conv2dShrinkingS` (sconcrete arrA))
                   (sconcrete arrK) (sconcrete arrK2)
      cjvpKrn = cjvp (`conv2dShrinkingS` (sconcrete arrA))
                     (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-7
     && allClose cjvpInp dInp 1e-7
     && allClose jvpKrn dKrn 1e-7
     && allClose cjvpKrn dKrn 1e-7

quickcheck_conv2dShrinkingJvp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      cjvpInp = cjvp (conv2dPaddedS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS shB r)
      dKrn = conv2dPaddedS (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = jvp (`conv2dPaddedS` (sconcrete arrA))
                   (sconcrete arrK) (sconcrete arrK2)
      cjvpKrn = cjvp (`conv2dPaddedS` (sconcrete arrA))
                     (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-7
     && allClose cjvpInp dInp 1e-7
     && allClose jvpKrn dKrn 1e-7
     && allClose cjvpKrn dKrn 1e-7

quickcheck_conv2dPaddedJvp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     ( GoodScalar r, Fractional r
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
  :: forall r. (GoodScalar r, Fractional r)
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
     ( GoodScalar r, Fractional r
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
  :: forall r. (GoodScalar r, Fractional r)
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
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      vjpKrn = vjp (`conv2dSameS` (sconcrete arrA))
                   (sconcrete arrK) (sconcrete arrB)
  in allClose vjpKrn vjpKrn 1e-5

quickcheck_conv2dSameVjpKrnSymbolic
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      cvjpKrn = cvjp (`conv2dSameS` (sconcrete arrA))
                     (sconcrete arrK) (sconcrete arrB)
  in allClose cvjpKrn cvjpKrn 1e-5

quickcheck_conv2dSameVjpKrnConcrete
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     ( GoodScalar r, Fractional r
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
  :: forall r. (GoodScalar r, Fractional r)
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
     ( GoodScalar r, Fractional r
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
  :: forall r. (GoodScalar r, Fractional r)
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
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
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
      cvjpInp = cvjp (conv2dSameS (sconcrete arrK))
                     (sconcrete arrA) (sconcrete arrB)
  in allClose cvjpInp cvjpInp 1e-5

quickcheck_conv2dSameVjpInpConcrete
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
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
