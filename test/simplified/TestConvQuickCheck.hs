{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | QuickCheck tests of convolution AD derivatives vs handwritten derivatives.
module TestConvQuickCheck (testTrees) where

import Prelude

import GHC.TypeLits (KnownNat, type (+))
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.QuickCheck hiding (label, shuffle)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape

import HordeAd
import HordeAd.Core.Adaptor

import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "conv2dVjp dInp" test_conv2dVjp_dInp
  , testCase "conv2dVjp dKrn" test_conv2dVjp_dKrn
  , testProperty "conv2dVjp Quickcheck Double" (quickcheck_conv2dVjp @Double)
  , testProperty "conv2dVjp Quickcheck Float" (quickcheck_conv2dVjp @Float)
  , testCase "conv2dShrinkingVjp dInp" test_conv2dShrinkingVjp_dInp
  , testCase "conv2dShrinkingVjp dKrn" test_conv2dShrinkingVjp_dKrn
  , testProperty "conv2dShrinkingVjp Quickcheck Double"
                 (quickcheck_conv2dShrinkingVjp @Double)
  , testProperty "conv2dShrinkingVjp Quickcheck Float"
                 (quickcheck_conv2dShrinkingVjp @Float)
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

-- | Derivative of full convolution with respect to the input image,
-- where the output size is the same as the input size.
conv2d_dInp
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
conv2d_dInp arrK arrB =
  let nKh = valueOf @nKh
      nKw = valueOf @nKw
  in sbuild @(Rank shA) $ \case
    [iImg, iCinp, iAh, iAw] ->
      let arr1 :: target (TKS sh1 r)
          arr1 = sbuild @(Rank sh1) $ \case
            [iCout] ->
              let arrBt = slicezS @shB1 arrB
                                  [iImg,  iCout, iAh - nKh + 1, iAw - nKw + 1]
                  arrKt = slicezS arrK
                                  [iCout, iCinp, 0, 0]
              in sdot0 arrBt arrKt
            _ -> error "conv2d_dInp: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2d_dInp: impossible pattern needlessly required"

-- | Another variant taken from the Futhark code.
-- Does not match the cvjp, either, according to QuickCheck tests.
_conv2d_dInp_fut
  :: forall shK shA shB sh1 nImgs nCinp nCout nAh nAw nKh nKw
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw
     , KnownNat nKh, KnownNat nKw
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , sh1  ~ '[nCout, nAh, nAw] )
  => target (TKS shK r)
  -> target (TKS shB r)
  -> target (TKS shA r)
_conv2d_dInp_fut arrK arrB =
  let nKh = valueOf @nKh
      nKw = valueOf @nKw
      padh = nKh `quotH` 2
      padw = nKw `quotH` 2
  in sbuild @(Rank shA) $ \case
    [iImg, iCinp, iAh, iAw] ->
      let arr1 :: target (TKS sh1 r)
          arr1 = sbuild @(Rank sh1) $ \case
            [iCout, iBh, iBw] ->
              let iKh = iAh - iBh + padh
                  iKw = iAw - iBw + padw
                  xOut = sindex0 arrB [iImg, iCout, iBh, iBw]
                  xKrn = sindex0 arrK [iCout, iCinp, iKh, iKw]
              in xOut * xKrn
            _ -> error "conv2d_dInp: impossible pattern needlessly required"
      in ssum0 arr1
    _ -> error "conv2d_dInp: impossible pattern needlessly required"

-- | Derivative of full convolution with respect to the kernels,
-- where the output size is the same as the input size.
conv2d_dKrn
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
conv2d_dKrn arrA arrB =
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
            _ -> error "conv2d_dKrn: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2d_dKrn: impossible pattern needlessly required"

test_conv2dVjp_dInp :: Assertion
test_conv2dVjp_dInp =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS  1
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 8] Double
      arrB = Nested.sreplicateScal knownShS 1
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2d_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dVjp_dKrn :: Assertion
test_conv2dVjp_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS 1
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 8] Double
      arrB = Nested.sreplicateScal knownShS 1
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2d_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp (`conv2dUnpaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2dVjp
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
static_conv2dVjp SNat SNat SNat SNat SNat SNat SNat arrK arrA arrB =
  let -- Compare the AD version against the manual derivative.
      -- Note that manual versions don't take one of the arguments (the point
      -- at which the gradient is taken), because maths (something about
      -- convolution being linear and so gradient the same everywhere).
      -- First, the gradient wrt the input image taken at point @arrA@.
      dInp = conv2d_dInp (sconcrete arrK) (sconcrete arrB)  -- handwritten
      vjpInp = cvjp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
      -- Second, the gradient wrt the kernels taken at point @arrK@.
--      dKrn = conv2d_dKrn (sconcrete arrA) (sconcrete arrB) -- handwritten
--      vjpKrn = cvjp (`conv2dUnpaddedS` (sconcrete arrA))
--                    (sconcrete arrK) (sconcrete arrB)
  in abs (kfromS (ssum0 (vjpInp - dInp))) <= 1e-7
--     && abs (kfromS (ssum0 (vjpKrn - dKrn))) <= 1e-7

quickcheck_conv2dVjp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2dVjp =
  forAll (choose (0, 2)) $ \nImgs' ->
  forAll (choose (0, 2)) $ \nCinp' ->
  forAll (choose (0, 2)) $ \nCout' ->
  forAll (choose (0, 2)) $ \nAh' ->
  forAll (choose (0, 2)) $ \nAw' ->
  forAll (choose (0, 2)) $ \nKh' ->
  forAll (choose (0, 2)) $ \nKw' ->
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
        in static_conv2dVjp
             nImgs nCinp nCout nAh nAw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

-- | Derivative of full shrinking convolution with respect to the input image,
-- where the output size is the same as the input size.
conv2dShrinking_dInp
  :: forall shK shA shB shB1 sh1 nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh_nKh1, KnownNat nAw_nKw1
     , KnownNat nKh1, KnownNat nKw1
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinp, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1]
     , shB  ~ '[nImgs, nCout, nAh_nKh1, nAw_nKw1]
     , shB1 ~ '[1,     1,     nKh1 + 1, nKw1 + 1]
     , sh1  ~ '[nCout] )
  => target (TKS shK r)
  -> target (TKS shB r)
  -> target (TKS shA r)
conv2dShrinking_dInp arrK arrB =
  let nKh1 = valueOf @nKh1
      nKw1 = valueOf @nKw1
  in sbuild @(Rank shA) $ \case
    [iImg, iCinp, iAh, iAw] ->
      let arr1 :: target (TKS sh1 r)
          arr1 = sbuild @(Rank sh1) $ \case
            [iCout] ->
              let arrBt = slicezS @shB1 arrB
                                  [iImg, iCout, iAh - nKh1, iAw - nKw1]
                  arrKt = slicezS arrK
                                  [iCout, iCinp, 0, 0]
              in sdot0 arrBt arrKt
            _ -> error "conv2dShrinking_dInp: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2dShrinking_dInp: impossible pattern needlessly required"

-- | Derivative of full shrinking convolution with respect to the kernels,
-- where the output size is the same as the input size.
conv2dShrinking_dKrn
  :: forall shK shA shB shB1 sh1 nImgs nCinp nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh_nKh1, KnownNat nAw_nKw1, KnownNat nKh1, KnownNat nKw1
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinp, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1]
     , shB  ~ '[nImgs, nCout, nAh_nKh1, nAw_nKw1]
     , shB1 ~ '[1,     1,     nAh_nKh1, nAw_nKw1]
     , sh1  ~ '[nCout] )
  => target (TKS shA r)
  -> target (TKS shB r)
  -> target (TKS shK r)
conv2dShrinking_dKrn arrA arrB =
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
            _ -> error "conv2dShrinking_dKrn: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2dShrinking_dKrn: impossible pattern needlessly required"

test_conv2dShrinkingVjp_dInp :: Assertion
test_conv2dShrinkingVjp_dInp =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS  1
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 6] Double
      arrB = Nested.sreplicateScal knownShS 1
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
      arrA = Nested.sreplicateScal knownShS 1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS 1
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 6] Double
      arrB = Nested.sreplicateScal knownShS 1
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
      dInp = conv2dShrinking_dInp
               (sconcrete arrK) (sconcrete arrB)  -- handwritten
      vjpInp = cvjp (conv2dShrinkingS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
      -- Second, the gradient wrt the kernels taken at point @arrK@.
--      dKrn = conv2dShrinking_dKrn
--               (sconcrete arrA) (sconcrete arrB) -- handwritten
--      vjpKrn = cvjp (`conv2dShrinkingS` (sconcrete arrA))
--                    (sconcrete arrK) (sconcrete arrB)
  in abs (kfromS (ssum0 (vjpInp - dInp))) <= 1e-5  -- 1e-7 is too much for Float
--     && abs (kfromS (ssum0 (vjpKrn - dKrn))) <= 1e-7

quickcheck_conv2dShrinkingVjp
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2dShrinkingVjp =
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
  let dInp = conv2dUnpaddedS
               (sconcrete arrK) (sconcrete arrA2)
      jvpInp = cjvp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrA2)
      dKrn = conv2dUnpaddedS
               (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = cjvp (`conv2dUnpaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrK2)
  in abs (kfromS (ssum0 (jvpInp - dInp))) <= 1e-7
     && abs (kfromS (ssum0 (jvpKrn - dKrn))) <= 1e-7

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
  let dInp = conv2dShrinkingS
               (sconcrete arrK) (sconcrete arrA2)
      jvpInp = cjvp (conv2dShrinkingS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrA2)
      dKrn = conv2dShrinkingS
               (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = cjvp (`conv2dShrinkingS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrK2)
  in abs (kfromS (ssum0 (jvpInp - dInp))) <= 1e-7
     && abs (kfromS (ssum0 (jvpKrn - dKrn))) <= 1e-7

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
  let dInp = conv2dPaddedS
               (sconcrete arrK) (sconcrete arrA2)
      jvpInp = cjvp (conv2dPaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrA2)
      dKrn = conv2dPaddedS
               (sconcrete arrK2) (sconcrete arrA)
      jvpKrn = cjvp (`conv2dPaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrK2)
  in abs (kfromS (ssum0 (jvpInp - dInp))) <= 1e-7
     && abs (kfromS (ssum0 (jvpKrn - dKrn))) <= 1e-7

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
