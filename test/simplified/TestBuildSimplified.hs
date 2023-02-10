{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, FlexibleInstances,
             OverloadedLists, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module TestBuildSimplified (testTrees) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.RankedS as OR
import           GHC.TypeLits (KnownNat)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import TestAdaptorSimplified (assertEqualUpToEpsilon', rev')
import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "Konst0Rev" testKonst0Rev
  , testCase "Konst0TinyA" testKonst0TinyA
--  , testCase "Konst0LittleA" testKonst0LittleA
--  , testCase "Konst0LittleB" testKonst0LittleB
--  , testCase "Konst0p" testKonst0p
  ]

-- The following are borrowed from https://github.com/benl23x5/adops.
-- Here defined using ranked, not shaped, tensors, but with sized indexes.

-- | Unpadded full convolution,
--   where the output size is the same as the input size.
conv2d
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r -> TensorOf 4 r
conv2d arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = tshape arrA
      [nCoutK, _nCinpK, nKh, nKw] = tshape arrK
      nCinp = assert (True {-Ast fails: nCinpA == nCinpK-}) nCinpA
      shB = [nImgs, nCoutK, nAh, nAw]
      shK1 = [1, nCinp, nKh, nKw]
  in tbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in tdot0 arrAt arrKt
    _ -> error "conv2d: impossible pattern needlessly required"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicez :: (ADReady r, KnownNat n)
       => ShapeInt n -> TensorOf n r -> IndexOf n r -> TensorOf n r
slicez shOut d ixBase =
  tbuild shOut $ \ixResult -> indexz0 d (zipWith_Index (+) ixBase ixResult)

-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
indexz0 :: forall r n. (ADReady r, KnownNat n)
        => TensorOf n r -> IndexOf n r -> TensorOf 0 r
indexz0 d ix = tcond (within0 @r (tshape d) ix) (tindex d ix) 0

-- | Given an index and shape, check if the index is fully within the shape.
within0 :: forall r n. ADReady r
        => ShapeInt n -> IndexOf n r -> BoolOf r
within0 sh ix =
  let within :: IntOf r -> IntOf r -> BoolOf r
      within i dim = andBool @r (leqInt @r 0 i) (gtInt @r dim i)
        -- TODO: why is each @r needed? (with GHC 9.0.2 at least)
        -- this prevents infix use and so harm readability
  in foldr (andBool @r) (fromBool @r True)
     $ zipWith within (indexToList ix) (map fromIntegral $ shapeToList sh)

conv2dA
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dA = conv2d $ tconst $ OR.fromList [1, 1, 1, 1] [-0.2]

conv2dB
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dB = conv2d $ tconst $ OR.fromList [2, 2, 2, 2] [5, 2, 6, 1, -2, 0, 0.1, -0.2, 13.1, 9, 8, -4, 582934, 2.99432, -335, 26]

testKonst0Rev :: Assertion
testKonst0Rev =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [2, 2, 2, 2] [18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001])
    (rev @(OR.Array 4 Double) conv2dB (tkonst0N [2, 2, 2, 2] 0))

testKonst0TinyA :: Assertion
testKonst0TinyA =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 1, 1, 1] [-0.2])
    (rev' @(OR.Array 4 Double) conv2dA (tkonst0N [1, 1, 1, 1] 0))

testKonst0LittleA :: Assertion
testKonst0LittleA =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 2, 1, 1] [18.1,29.1])
    (rev' @(OR.Array 4 Double) conv2dA (tkonst0N [1, 2, 1, 1] 0))

testKonst0LittleB :: Assertion
testKonst0LittleB =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 2, 1, 1] [18.1,29.1])
    (rev' @(OR.Array 4 Double) conv2dB (tkonst0N [1, 2, 1, 1] 0))

testKonst0p :: Assertion
testKonst0p =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 2, 2, 2] [18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001])
    (rev' @(OR.Array 4 Double) conv2dA (tkonst0N [2, 2, 2, 2] 0))
