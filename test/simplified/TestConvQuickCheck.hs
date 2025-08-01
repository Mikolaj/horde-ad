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
  [ testCase "conv2d_dInp" test_conv2d_dInp
  , testCase "conv2d_dKrn" test_conv2d_dKrn
  , testProperty "conv2d_quickcheck Double" (quickcheck_conv2d @Double)
  , testProperty "conv2d_quickcheck Float" (quickcheck_conv2d @Float)
  , testCase "conv2dShrinking_dInp" test_conv2dShrinking_dInp
  , testCase "conv2dShrinking_dKrn" test_conv2dShrinking_dKrn
  , testProperty "conv2dShrinking_quickcheck Double"
                 (quickcheck_conv2dShrinking @Double)
  , testProperty "conv2dShrinking_quickcheck Float"
                 (quickcheck_conv2dShrinking @Float)
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
                  arrKt = slicezS @shB1 arrK
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
              let arrBt = slicezS @shB1 arrB [iImg, iCout, 0,   0  ]
                  arrAt = slicezS @shB1 arrA [iImg, iCinp, iKh, iKw]
              in sdot0 arrBt arrAt
            _ -> error "conv2d_dKrn: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2d_dKrn: impossible pattern needlessly required"

test_conv2d_dInp :: Assertion
test_conv2d_dInp =
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

test_conv2d_dKrn :: Assertion
test_conv2d_dKrn =
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

static_conv2d
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
static_conv2d SNat SNat SNat SNat SNat SNat SNat arrK arrA arrB =
  let -- Compare the AD version against the manual derivative.
      -- Note that manual versions don't take one of the arguments (the point
      -- at which the gradient is taken), because maths (something about
      -- convolution being linear and so gradient the same everywhere).
      -- First, the gradient wrt the input image taken at point @arrA@.
      dInp = conv2d_dInp (sconcrete arrK) (sconcrete arrB)  -- handwritten
      vjpInp = cvjp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn = conv2d_dKrn (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = cvjp (`conv2dUnpaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in abs (kfromS (ssum0 (vjpInp - dInp))) <= 1e-7
     && abs (kfromS (ssum0 (vjpKrn - dKrn))) <= 1e-7

quickcheck_conv2d
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2d =
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
        in static_conv2d nImgs nCinp nCout nAh nAw nKh nKw
                         (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)

-- | Derivative of full shrinking convolution with respect to the input image,
-- where the output size is the same as the input size.
conv2dShrinking_dInp
  :: forall shK shA shB shB1 sh1 nImgs nCinp nCout nAh_nKh nAw_nKw nKh nKw
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh_nKh, KnownNat nAw_nKw
     , KnownNat nKh, KnownNat nKw
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh_nKh + nKh, nAw_nKw + nKw]
     , shB  ~ '[nImgs, nCout, nAh_nKh, nAw_nKw]
     , shB1 ~ '[1,     1,     nKh, nKw]
     , sh1  ~ '[nCout] )
  => target (TKS shK r)
  -> target (TKS shB r)
  -> target (TKS shA r)
conv2dShrinking_dInp arrK arrB =
  let nKh = valueOf @nKh
      nKw = valueOf @nKw
  in sbuild @(Rank shA) $ \case
    [iImg, iCinp, iAh, iAw] ->
      let arr1 :: target (TKS sh1 r)
          arr1 = sbuild @(Rank sh1) $ \case
            [iCout] ->
              let arrBt = slicezS @shB1 arrB
                                  [iImg,  iCout, iAh - nKh + 1, iAw - nKw + 1]
                  arrKt = slicezS @shB1 arrK
                                  [iCout, iCinp, 0, 0]
              in sdot0 arrBt arrKt
            _ -> error "conv2d_dInp: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2d_dInp: impossible pattern needlessly required"

-- | Derivative of full shrinking convolution with respect to the kernels,
-- where the output size is the same as the input size.
conv2dShrinking_dKrn
  :: forall shK shA shB shB1 sh1 nImgs nCinp nCout nAh_nKh nAw_nKw nKh nKw
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh_nKh, KnownNat nAw_nKw, KnownNat nKh, KnownNat nKw
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh_nKh + nKh, nAw_nKw + nKw]
     , shB  ~ '[nImgs, nCout, nAh_nKh, nAw_nKw]
     , shB1 ~ '[1,     1,     nAh_nKh, nAw_nKw]
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
              let arrBt = slicezS @shB1 arrB [iImg, iCout, 0,   0  ]
                  arrAt = slicezS @shB1 arrA [iImg, iCinp, iKh, iKw]
              in sdot0 arrBt arrAt
            _ -> error "conv2d_dKrn: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2d_dKrn: impossible pattern needlessly required"

test_conv2dShrinking_dInp :: Assertion
test_conv2dShrinking_dInp =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS  1
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 3, 5] Double
      arrB = Nested.sreplicateScal knownShS 1
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2dShrinking_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp (conv2dShrinkingS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2dShrinking_dKrn :: Assertion
test_conv2dShrinking_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS 1
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 3, 5] Double
      arrB = Nested.sreplicateScal knownShS 1
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2dShrinking_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp (`conv2dShrinkingS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2dShrinking
  :: forall r nImgs nCinp nCout nAh_nKh nAw_nKw nKh nKw
            shK shA shB.
     ( GoodScalar r, ADTensorScalar r ~ r, Fractional r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh_nKh + nKh, nAw_nKw + nKw]
     , shB ~ '[nImgs, nCout, nAh_nKh, nAw_nKw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh_nKh -> SNat nAw_nKw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Nested.Shaped shB r
       -- ^ Output gradient of shape:
       --     batch x chas x output_height x output_width
  -> Bool
static_conv2dShrinking SNat SNat SNat SNat SNat SNat SNat arrK arrA arrB =
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
      dKrn = conv2dShrinking_dKrn
               (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = cvjp (`conv2dShrinkingS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in abs (kfromS (ssum0 (vjpInp - dInp))) <= 1e-7
     && abs (kfromS (ssum0 (vjpKrn - dKrn))) <= 1e-7

quickcheck_conv2dShrinking
  :: forall r. (GoodScalar r, ADTensorScalar r ~ r, Fractional r)
  => Property
quickcheck_conv2dShrinking =
  forAll (choose (0, 2)) $ \nImgs' ->
  forAll (choose (0, 2)) $ \nCinp' ->
  forAll (choose (0, 2)) $ \nCout' ->
  forAll (choose (0, 2)) $ \nAh_nKh' ->
  forAll (choose (0, 2)) $ \nAw_nKw' ->
  forAll (choose (0, 2)) $ \nKh' ->
  forAll (choose (0, 2)) $ \nKw' ->
    -- The glue below is needed to bridge the dependently-typed
    -- vs normal world.
    withSNat nImgs' $ \(nImgs :: SNat nImgs) ->
    withSNat nCinp' $ \(nCinp :: SNat nCinp) ->
    withSNat nCout' $ \(nCout :: SNat nCout) ->
    withSNat nAh_nKh' $ \(nAh_nKh :: SNat nAh_nKh) ->
    withSNat nAw_nKw' $ \(nAw_nKw :: SNat nAw_nKw) ->
    withSNat nKh' $ \(nKh :: SNat nKh) ->
    withSNat nKw' $ \(nKw :: SNat nKw) ->
      property $ \seed0 ->
        let arrK :: Concrete (TKS '[nCout, nCinp, nKh, nKw] r)
            (arrK, seed2) = randomValue 0.5 (mkStdGen seed0)
            arrA :: Concrete (TKS '[ nImgs, nCinp
                                   , nAh_nKh + nKh, nAw_nKw + nKw ] r)
            (arrA, seed3) = randomValue 0.5 seed2
            arrB :: Concrete (TKS '[nImgs, nCout, nAh_nKh, nAw_nKw] r)
            (arrB, _) = randomValue 0.5 seed3
        in static_conv2dShrinking
             nImgs nCinp nCout nAh_nKh nAw_nKw nKh nKw
             (unConcrete arrK) (unConcrete arrA) (unConcrete arrB)
