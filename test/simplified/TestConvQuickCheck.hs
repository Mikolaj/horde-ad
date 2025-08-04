{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | QuickCheck tests of convolution AD derivatives vs handwritten derivatives.
module TestConvQuickCheck (testTrees) where

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

import EqEpsilon
import Shared

testTrees :: [TestTree]
testTrees =
  [ testCase "conv2dUnpaddedVjp dInp" test_conv2dUnpaddedVjp_dInp
  , testCase "conv2dUnpaddedVjp dKrn" test_conv2dUnpaddedVjp_dKrn
  , testProperty "conv2dUnpaddedVjp Quickcheck Double" (quickcheck_conv2dUnpaddedVjp @Double)
  , testProperty "conv2dUnpaddedVjp Quickcheck Float" (quickcheck_conv2dUnpaddedVjp @Float)
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
  , testProperty "conv2dUnpaddedJvp Quickcheck Double"
                 (quickcheck_conv2dUnpaddedJvp @Double)
  , testProperty "conv2dUnpaddedJvp Quickcheck Float"
                 (quickcheck_conv2dUnpaddedJvp @Float)
  , testProperty "conv2dShrinkingJvp Quickcheck Double"
                 (quickcheck_conv2dShrinkingJvp @Double)
  , testProperty "conv2dShrinkingJvp Quickcheck Float"
                 (quickcheck_conv2dShrinkingJvp @Float)
  , testProperty "conv2dPaddedJvp Quickcheck Double"
                 (quickcheck_conv2dPaddedJvp @Double)
  , testProperty "conv2dPaddedJvp Quickcheck Float"
                 (quickcheck_conv2dPaddedJvp @Float)
  ]

flip42 :: (ADReady target, GoodScalar r)
       => target (TKS '[nCout, nCinp, nKh, nKw] r)
       -> target (TKS '[nCout, nCinp, nKh, nKw] r)
flip42 arr =
  stranspose @'[1, 2, 0]
  $ sreverse
  $ stranspose @'[3, 1, 2, 0]
  $ sreverse
  $ stranspose @'[3, 0, 1, 2] arr

-- | Derivative of full convolution with respect to the input image,
-- where the output size is the same as the input size.
conv2dUnpadded_dInp
  :: forall shK shA shB shB1 sh1 nImgs nCinp nCout nAh nAw nKh nKw
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw
     , KnownNat nKh, KnownNat nKw
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , shB1 ~ '[1,     1,     nKh, nKw]
     , sh1  ~ '[nCout] )
  => target (TKS shK r)
  -> target (TKS shB r)
  -> target (TKS shA r)
conv2dUnpadded_dInp arrK arrB =
  let arrKFlipped = flip42 arrK
      nKh = valueOf @nKh
      nKw = valueOf @nKw
  in sbuild @(Rank shA) $ \case
    [iImg, iCinp, iAh, iAw] ->
      let arr1 :: target (TKS sh1 r)
          arr1 = sbuild @(Rank sh1) $ \case
            [iCout] ->
              let arrBt = slicezS @shB1 arrB
                                  [iImg,  iCout, iAh - nKh + 1, iAw - nKw + 1]
                  arrKt = slicezS arrKFlipped
                                  [iCout, iCinp, 0, 0]
              in sdot0 arrBt arrKt
            _ -> error "conv2dUnpadded_dInp: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2dUnpadded_dInp: impossible pattern needlessly required"
-- Note that
-- > ... in conv2dUnpaddedS (stranspose @'[1, 0] arrKFlipped) arrB
-- type-checks above, but test fails.

-- TODO: this is wrong and so the QuickCheck property for this is disabled.
-- | Derivative of full convolution with respect to the kernels,
-- where the output size is the same as the input size.
conv2dUnpadded_dKrn
  :: forall shK shA shB shB1 sh1 nImgs nCinp nCout nAh nAw nKh nKw
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh, KnownNat nKw
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , shB1 ~ '[1,     1,     nAh, nAw]
     , sh1  ~ '[nCout] )
  => target (TKS shA r)
  -> target (TKS shB r)
  -> target (TKS shK r)
conv2dUnpadded_dKrn arrA arrB =
  sbuild @(Rank shK) $ \case
    [iCout, iCinp, iKh, iKw] ->
      let arr1 :: target (TKS sh1 r)
          arr1 = sbuild @(Rank sh1) $ \case
            [iImg] ->
              let arrBt = slicezS @shB1 arrB
                                  [iImg, iCout, 0, 0]
                  arrAt = slicezS arrA
                                  [iImg, iCinp, iKh, iKw]
              in sdot0 arrBt arrAt
            _ -> error "conv2dUnpadded_dKrn: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2dUnpadded_dKrn: impossible pattern needlessly required"

test_conv2dUnpaddedVjp_dInp :: Assertion
test_conv2dUnpaddedVjp_dInp =
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
      dInp = conv2dUnpadded_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dUnpaddedVjp_dKrn :: Assertion
test_conv2dUnpaddedVjp_dKrn =
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
      dKrn = conv2dUnpadded_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp (`conv2dUnpaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

allClose :: (GoodScalar r, Fractional r, Linearizable a r, Linearizable b r)
         => a -> b -> Rational -> Bool
allClose expected actual eps =
  all (\(a, b) -> abs (a - b) <= fromRational eps)
  $ zip (linearize expected) (linearize actual)

static_conv2dUnpaddedVjp
  :: forall r nImgs nCinp nCout nAh nAw nKh nKw
            shK shA shB.
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
static_conv2dUnpaddedVjp SNat SNat SNat SNat SNat SNat SNat arrK arrA arrB =
  let -- Compare the AD version against the manual derivative.
      -- Note that manual versions don't take one of the arguments (the point
      -- at which the gradient is taken), because maths (something about
      -- convolution being linear and so gradient the same everywhere).
      -- First, the gradient wrt the input image taken at point @arrA@.
      dInp :: Concrete (TKS shA r)
      dInp = conv2dUnpadded_dInp (sconcrete arrK) (sconcrete arrB)  -- handwritten
      vjpInp = cvjp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
      -- Second, the gradient wrt the kernels taken at point @arrK@.
--      dKrn :: Concrete (TKS shK r)
--      dKrn = conv2dUnpadded_dKrn (sconcrete arrA) (sconcrete arrB) -- handwritten
--      vjpKrn = cvjp (`conv2dUnpaddedS` (sconcrete arrA))
--                    (sconcrete arrK) (sconcrete arrB)
  in allClose vjpInp dInp 1e-5
     -- && allClose vjpKrn dKrn 1e-5

quickcheck_conv2dUnpaddedVjp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2dUnpaddedVjp =
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
        in static_conv2dUnpaddedVjp
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

-- | Derivative of full shrinking convolution with respect to the input image,
-- where the output size is the same as the input size.
conv2dShrinking_dInp
  :: forall shK shA shB nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
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

-- | Derivative of full shrinking convolution with respect to the kernels,
-- where the output size is the same as the input size.
conv2dShrinking_dKrn
  :: forall shK shA shB nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
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
             (conv2dShrinkingS @nCout @nImgs @(nAh_nKh1 - 1) @(nAw_nKw1 - 1)
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
  :: forall r nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
            shK shA shB.
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
      vjpInp = cvjp (conv2dShrinkingS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn :: Concrete (TKS shK r)
      dKrn = conv2dShrinking_dKrn
               (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = cvjp (`conv2dShrinkingS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in allClose vjpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose vjpKrn dKrn 1e-5

quickcheck_conv2dShrinkingVjp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2dShrinkingVjp =
  forAll chooseAny $ \(seed0 :: Int) ->
  forAll (choose (0, 4)) $ \nImgs' ->
  forAll (choose (0, 4)) $ \nCinp' ->
  forAll (choose (0, 4)) $ \nCout' ->
  forAll (choose (1, 4)) $ \nAh_nKh1' ->
  forAll (choose (1, 4)) $ \nAw_nKw1' ->
  forAll (choose (0, 4)) $ \nKh1' ->
  forAll (choose (0, 4)) $ \nKw1' ->
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

-- | Derivative of full padded convolution with respect to the input image,
-- where the output size is the same as the input size.
conv2dPadded_dInp
  :: forall shK shA shB nImgs nCinp nCout nAh nAw nKh1 nKw1
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

-- | Derivative of full padded convolution with respect to the kernels,
-- where the output size is the same as the input size.
conv2dPadded_dKrn
  :: forall shK shA shB nImgs nCinp nCout nAh nAw nKh1 nKw1
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
  $ conv2dShrinkingS @nCinp @nImgs @(nAh - 1) @(nAw - 1)
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
  :: forall r nImgs nCinp nCout nAh nAw nKh1 nKw1
            shK shA shB.
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
      vjpInp = cvjp (conv2dPaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn :: Concrete (TKS shK r)
      dKrn = conv2dPadded_dKrn
               (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = cvjp (`conv2dPaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in allClose vjpInp dInp 1e-5  -- 1e-7 is too much for Float
     && allClose vjpKrn dKrn 1e-5

quickcheck_conv2dPaddedVjp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2dPaddedVjp =
  forAll chooseAny $ \(seed0 :: Int) ->
  forAll (choose (0, 4)) $ \nImgs' ->
  forAll (choose (0, 4)) $ \nCinp' ->
  forAll (choose (0, 4)) $ \nCout' ->
  forAll (choose (1, 4)) $ \nAh' ->
  forAll (choose (1, 4)) $ \nAw' ->
  forAll (choose (0, 4)) $ \nKh1' ->
  forAll (choose (0, 4)) $ \nKw1' ->
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
                  arrB :: Concrete (TKS '[nImgs, nCout, nAh + nKh1, nAw + nKw1] r)
                  (arrB, _) = randomValue 0.5 seed3
              in static_conv2dPaddedVjp
                   nImgs nCinp nCout nAh nAw nKh1 nKw1
                   (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)
    in b

static_conv2dUnpaddedJvp
  :: forall r nImgs nCinp nCout nAh nAw nKh nKw
            shK shA.
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Bool
static_conv2dUnpaddedJvp SNat SNat SNat SNat SNat SNat SNat
                         arrK arrK2 arrA arrA2 =
  let dInp :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
      dInp = conv2dUnpaddedS
               (sconcrete arrK) (sconcrete arrA2)
      jvpInp = cjvp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS '[nImgs, nCout, nAh, nAw] r)
      dKrn = conv2dUnpaddedS
               (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = cjvp (`conv2dUnpaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-7
     && allClose jvpKrn dKrn 1e-7

quickcheck_conv2dUnpaddedJvp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2dUnpaddedJvp =
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
            arrA, arrA2
              :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed4) = randomValue 0.5 seed3
            (arrA2, _) = randomValue 0.5 seed4
        in static_conv2dUnpaddedJvp
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrK2)
             (unConcrete arrA) (unConcrete arrA2)

static_conv2dShrinkingJvp
  :: forall r nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
            shK shA.
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
     , shK ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA ~ '[nImgs, nCinp, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh_nKh1 -> SNat nAw_nKw1 -> SNat nKh1 -> SNat nKw1
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Bool
static_conv2dShrinkingJvp SNat SNat SNat SNat SNat SNat SNat
                          arrK arrK2 arrA arrA2 =
  let dInp :: Concrete (TKS '[nImgs, nCout, nAh_nKh1, nAw_nKw1] r)
      dInp = conv2dShrinkingS
               (sconcrete arrK) (sconcrete arrA2)
      jvpInp = cjvp (conv2dShrinkingS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS '[nImgs, nCout, nAh_nKh1, nAw_nKw1] r)
      dKrn = conv2dShrinkingS
               (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = cjvp (`conv2dShrinkingS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-7
     && allClose jvpKrn dKrn 1e-7

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
              :: Concrete (TKS '[ nImgs, nCinp
                                , nAh_nKh1 + nKh1, nAw_nKw1 + nKw1 ] r)
            (arrA, seed4) = randomValue 0.5 seed3
            (arrA2, _) = randomValue 0.5 seed4
        in static_conv2dShrinkingJvp
             nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
             (unConcrete arrK) (unConcrete arrK2)
             (unConcrete arrA) (unConcrete arrA2)

static_conv2dPaddedJvp
  :: forall r nImgs nCinp nCout nAh nAw nKh1 nKw1
            shK shA.
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
     , shK ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA ~ '[nImgs, nCinp, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh1 -> SNat nKw1
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Bool
static_conv2dPaddedJvp SNat SNat SNat SNat SNat SNat SNat
                       arrK arrK2 arrA arrA2 =
  let dInp :: Concrete (TKS '[nImgs, nCout, nAh + nKh1, nAw + nKw1] r)
      dInp = conv2dPaddedS
               (sconcrete arrK) (sconcrete arrA2)
      jvpInp = cjvp (conv2dPaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrA2)
      dKrn :: Concrete (TKS '[nImgs, nCout, nAh + nKh1, nAw + nKw1] r)
      dKrn = conv2dPaddedS
               (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = cjvp (`conv2dPaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrK2)
  in allClose jvpInp dInp 1e-7
     && allClose jvpKrn dKrn 1e-7

quickcheck_conv2dPaddedJvp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2dPaddedJvp =
  forAll (choose (0, 4)) $ \nImgs' ->
  forAll (choose (0, 4)) $ \nCinp' ->
  forAll (choose (0, 4)) $ \nCout' ->
  forAll (choose (0, 4)) $ \nAh' ->
  forAll (choose (0, 4)) $ \nAw' ->
  forAll (choose (0, 4)) $ \nKh1' ->
  forAll (choose (0, 4)) $ \nKw1' ->
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
            arrA, arrA2
              :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] r)
            (arrA, seed4) = randomValue 0.5 seed3
            (arrA2, _) = randomValue 0.5 seed4
        in static_conv2dPaddedJvp
             nImgs nCinp nCout nAh nAw nKh1 nKw1
             (unConcrete arrK) (unConcrete arrK2)
             (unConcrete arrA) (unConcrete arrA2)
