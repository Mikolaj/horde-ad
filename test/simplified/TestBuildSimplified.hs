{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, FlexibleInstances,
             OverloadedLists, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module TestBuildSimplified (testTrees) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.RankedS as OR
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import HordeAd.Internal.TensorOps
import TestAdaptorSimplified (assertEqualUpToEpsilon', rev')
import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "KonstG0Rev" testKonstG0Rev
  , testCase "KonstG0Tiny1" testKonstG0Tiny1
  , testCase "KonstG0TinyS" testKonstG0TinyS
  , testCase "KonstG0TinyA" testKonstG0TinyA
  , testCase "KonstG0LittleA" testKonstG0LittleA
  , testCase "KonstG5LittleB" testKonstG5LittleB
  , testCase "KonstG5LittleC" testKonstG5LittleC
  , testCase "KonstG5BigB" testKonstG5BigB
  , testCase "KonstGNotBigB" testKonstGNotBigB
  , testCase "KonstG5BigC" testKonstG5BigC
  , testCase "KonstGNotBigC" testKonstGNotBigC
  , testCase "Konst0RevLaborious" testKonst0RevLaborious
  , testCase "Konst0Tiny1Laborious" testKonst0Tiny1Laborious
  , testCase "Konst0TinySLaborious" testKonst0TinySLaborious
  , testCase "Konst0TinyALaborious" testKonst0TinyALaborious
  , testCase "Konst0LittleALaborious" testKonst0LittleALaborious
  , testCase "Konst5LittleBLaborious" testKonst5LittleBLaborious
  , testCase "Konst5LittleCLaborious" testKonst5LittleCLaborious
  , testCase "Konst5BigBLaborious" testKonst5BigBLaborious
  , testCase "KonstNotBigBLaborious" testKonstNotBigBLaborious
  , testCase "Konst5BigCLaborious" testKonst5BigCLaborious
  , testCase "KonstNotBigCLaborious" testKonstNotBigCLaborious
  , testCase "Konst0RevFailed" testKonst0RevFailed
  , testCase "Konst0Tiny1Failed" testKonst0Tiny1Failed
  , testCase "Konst0TinySFailed" testKonst0TinySFailed
  ]

-- The examples reproduce and transformed in this file are borrowed
-- from https://github.com/benl23x5/adops.
-- Here it's defined using ranked tensors with sized indexes.

t16 :: (Numeric r, Fractional r) => OR.Array 4 r
t16 = OR.fromList [2, 2, 2, 2] [5, 2, 6, 1, -2, 0, 0.1, -0.2, 13.1, 9, 8, -4, 582934, 2.99432, -335, 26]

-- Test comments are currently outdated. The first implementation
-- is currently correct only by chance (and this may change).
-- The "laborious" implementation is the solid one.

-- | Unpadded full convolution,
--   where the output size is the same as the input size.
conv2d
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r -> TensorOf 4 r
conv2d arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = tshape arrA
      [nCoutK, nCinpK, nKh, nKw] = tshape arrK
      nCinp = assert (nCinpA == nCinpK) nCinpA
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
slicez :: forall n r. (ADReady r, KnownNat n)
       => ShapeInt n -> TensorOf n r -> IndexOf n r -> TensorOf n r
slicez shOut d ixBase =
  tbuild shOut $ \ixResult ->
    tindex @r @n @0 d (zipWith_Index (+) ixBase ixResult)
      -- tindex0 would not require a single type application here

conv2d1
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2d1 = conv2dFailed $ tconst $ OR.fromList [1, 1, 1, 1] [-0.2]

conv2dA
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dA = conv2d $ tconst $ OR.fromList [1, 2, 1, 1] [-0.2, 25.0003]

conv2dB
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dB = conv2d $ tconst t16

conv2dC
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dC = flip conv2d $ tconst t16

testKonstG0Rev :: Assertion
testKonstG0Rev =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [2, 2, 2, 2] [18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001])
    (rev @(OR.Array 4 Double) conv2dB (tkonst0N [2, 2, 2, 2] 0))

testKonstG0Tiny1 :: Assertion
testKonstG0Tiny1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 1, 1, 1] [-0.2])
    (rev' @(OR.Array 4 Double) conv2d1 (tkonst0N [1, 1, 1, 1] 0))

testKonstG0TinyS :: Assertion
testKonstG0TinyS =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 1, 1, 1] [582665.99432])
    (rev' @(OR.Array 4 Double)
          (conv2d $ tconst $ tkonst0NR [1, 1, 1, 1] (tsum0R t16))
          (OR.fromList [1, 1, 1, 1] [0]))

testKonstG0TinyA :: Assertion
testKonstG0TinyA =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 2, 1, 1] [-0.2,25.0003])
    (rev' @(OR.Array 4 Double) conv2dA (tkonst0N [1, 2, 1, 1] 0))

testKonstG0LittleA :: Assertion
testKonstG0LittleA =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 2, 2, 2] [-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003])
    (rev' @(OR.Array 4 Double) conv2dA (tkonst0N [2, 2, 2, 2] 0))

testKonstG5LittleB :: Assertion
testKonstG5LittleB =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [2, 2, 2, 2] [18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001])
    (rev' @(OR.Array 4 Double) conv2dB (tkonst0N [2, 2, 2, 2] 5))

testKonstG5LittleC :: Assertion
testKonstG5LittleC =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [2, 2, 2, 2] [40.1,8.0,11.0,-3.0,582625.89432,28.79432,-309.09999999999997,25.8,40.1,8.0,11.0,-3.0,582625.89432,28.79432,-309.09999999999997,25.8])
    (rev' @(OR.Array 4 Double) conv2dC (tkonst0N [2, 2, 2, 2] 5))

testKonstG5BigB :: Assertion
testKonstG5BigB =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3, 2, 4, 2] [18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001])
    (rev' @(OR.Array 4 Double) conv2dB (tkonst0N [3, 2, 4, 2] 5))

-- The gradient is the same as above, because one argument is the same
-- and convolution is linear.
testKonstGNotBigB :: Assertion
testKonstGNotBigB =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3, 2, 4, 2] [18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001])
    (rev' @(OR.Array 4 Double) conv2dB
          (tfromList0N [3, 2, 4, 2] [37, 36 .. -10]))

testKonstG5BigC :: Assertion
testKonstG5BigC =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3, 2, 4, 2] [40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0,40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0,40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0])
    (rev' @(OR.Array 4 Double) conv2dC (tkonst0N [3, 2, 4, 2] 5))

-- The gradient is the same as above, because one argument is the same
-- and convolution is linear.
testKonstGNotBigC :: Assertion
testKonstGNotBigC =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3, 2, 4, 2] [40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0,40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0,40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0])
    (rev' @(OR.Array 4 Double) conv2dC
          (tfromList0N [3, 2, 4, 2] [37, 36 .. -10]))


-- * A laborious version

-- It needlessly gates the indexing behind a conditional, despite
-- the current indexing giving 0 when out of bounds.
-- However, if another value than 0 was needed, the conditional
-- would be necessary and, in the presense of vectorization,
-- which prevents conditional from being lazy, permissing indexing
-- would still be neeeded.

-- The tests are copied from above and the required test results are
-- the same in order to verify that the conditional is indeed spurious.

-- | Unpadded full convolution,
--   where the output size is the same as the input size.
conv2dLaborious
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r -> TensorOf 4 r
conv2dLaborious arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = tshape arrA
      [nCoutK, nCinpK, nKh, nKw] = tshape arrK
      nCinp = assert (nCinpA == nCinpK) nCinpA
      shB = [nImgs, nCoutK, nAh, nAw]
      shK1 = [1, nCinp, nKh, nKw]
  in tbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezLaborious shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicezLaborious shK1 arrK [iCout, 0, 0, 0]
      in tdot0 arrAt arrKt
    _ -> error "conv2d: impossible pattern needlessly required"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicezLaborious
  :: (ADReady r, KnownNat n)
  => ShapeInt n -> TensorOf n r -> IndexOf n r -> TensorOf n r
slicezLaborious shOut d ixBase =
  tbuild shOut $ \ixResult -> indexz0Laborious d (zipWith_Index (+) ixBase ixResult)

-- Note that this is now spurious, since the current version of index
-- returns 0 when out of bounds. But if another values was required,
-- the current vections of index would be needed together with this
-- conditional.
-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
indexz0Laborious
  :: forall r n. (ADReady r, KnownNat n)
  => TensorOf n r -> IndexOf n r -> TensorOf 0 r
indexz0Laborious d ix = tcond (within0 @r (tshape d) ix) (d ! ix) 0

-- | Given an index and shape, check if the index is fully within the shape.
within0 :: forall r n. ADReady r
        => ShapeInt n -> IndexOf n r -> BoolOf r
within0 sh ix =
  let within :: IntOf r -> IntOf r -> BoolOf r
      within i dim = andBool @r (leqInt @r 0 i) (gtInt @r dim i)
        -- TODO: why is each @r needed? (with GHC 9.0.2 at least);
        -- this prevents infix use and so harms readability
  in foldr (andBool @r) (fromBool @r True)
     $ zipWith within (indexToList ix) (map fromIntegral $ shapeToList sh)

conv2d1Laborious
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2d1Laborious = conv2dLaborious $ tconst $ OR.fromList [1, 1, 1, 1] [-0.2]

conv2dALaborious
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dALaborious = conv2dLaborious $ tconst $ OR.fromList [1, 2, 1, 1] [-0.2, 25.0003]

conv2dBLaborious
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dBLaborious = conv2dLaborious $ tconst t16

conv2dCLaborious
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dCLaborious = flip conv2dLaborious $ tconst t16

testKonst0RevLaborious :: Assertion
testKonst0RevLaborious =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [2, 2, 2, 2] [18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001])
    (rev @(OR.Array 4 Double) conv2dBLaborious (tkonst0N [2, 2, 2, 2] 0))

testKonst0Tiny1Laborious :: Assertion
testKonst0Tiny1Laborious =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 1, 1, 1] [-0.2])
    (rev' @(OR.Array 4 Double) conv2d1Laborious (tkonst0N [1, 1, 1, 1] 0))

testKonst0TinySLaborious :: Assertion
testKonst0TinySLaborious =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 1, 1, 1] [582665.99432])
    (rev' @(OR.Array 4 Double)
          (conv2dLaborious $ tconst $ tkonst0NR [1, 1, 1, 1] (tsum0R t16))
          (OR.fromList [1, 1, 1, 1] [0]))

testKonst0TinyALaborious :: Assertion
testKonst0TinyALaborious =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 2, 1, 1] [-0.2,25.0003])
    (rev' @(OR.Array 4 Double) conv2dALaborious (tkonst0N [1, 2, 1, 1] 0))

testKonst0LittleALaborious :: Assertion
testKonst0LittleALaborious =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 2, 2, 2] [-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003])
    (rev' @(OR.Array 4 Double) conv2dALaborious (tkonst0N [2, 2, 2, 2] 0))

testKonst5LittleBLaborious :: Assertion
testKonst5LittleBLaborious =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [2, 2, 2, 2] [18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001])
    (rev' @(OR.Array 4 Double) conv2dBLaborious (tkonst0N [2, 2, 2, 2] 5))

testKonst5LittleCLaborious :: Assertion
testKonst5LittleCLaborious =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [2, 2, 2, 2] [40.1,8.0,11.0,-3.0,582625.89432,28.79432,-309.09999999999997,25.8,40.1,8.0,11.0,-3.0,582625.89432,28.79432,-309.09999999999997,25.8])
    (rev' @(OR.Array 4 Double) conv2dCLaborious (tkonst0N [2, 2, 2, 2] 5))

testKonst5BigBLaborious :: Assertion
testKonst5BigBLaborious =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3, 2, 4, 2] [18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001])
    (rev' @(OR.Array 4 Double) conv2dBLaborious (tkonst0N [3, 2, 4, 2] 5))

-- The gradient is the same as above, because one argument is the same
-- and convolution is linear.
testKonstNotBigBLaborious :: Assertion
testKonstNotBigBLaborious =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3, 2, 4, 2] [18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,582597.1,582625.8943200001,582597.1,582625.8943200001])
    (rev' @(OR.Array 4 Double) conv2dBLaborious
          (tfromList0N [3, 2, 4, 2] [37, 36 .. -10]))

testKonst5BigCLaborious :: Assertion
testKonst5BigCLaborious =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3, 2, 4, 2] [40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0,40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0,40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0])
    (rev' @(OR.Array 4 Double) conv2dCLaborious (tkonst0N [3, 2, 4, 2] 5))

-- The gradient is the same as above, because one argument is the same
-- and convolution is linear.
testKonstNotBigCLaborious :: Assertion
testKonstNotBigCLaborious =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3, 2, 4, 2] [40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0,40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0,40.1,8.0,11.0,-3.0,0.0,0.0,0.0,0.0,582625.8943200001,28.794320000000003,-309.09999999999997,25.8,0.0,0.0,0.0,0.0])
    (rev' @(OR.Array 4 Double) conv2dCLaborious
          (tfromList0N [3, 2, 4, 2] [37, 36 .. -10]))


-- * A failed version

-- That's due to the conditional not being lazy and the indexing
-- (and gather) crashing when out of bounds. Either of these needs to be
-- fixed or, alternatively, the Ast term needs to be simplified after all
-- variables are known, but before interpretation, and all inaccessible
-- subtensor expressions need to be replaced with something safe, like 0,
-- which would likely grow the term a lot.
--
-- The failure would manifest in rev` that uses vectorization
-- and for tensors larger than 1-element, where indexes out of bounds
-- are generated (on purpose) in this code.
-- It would manifest with the older version of tindex that crashed
-- when out of bounds.

conv2dFailed
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r -> TensorOf 4 r
conv2dFailed arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = tshape arrA
      [nCoutK, nCinpK, nKh, nKw] = tshape arrK
      nCinp = assert (nCinpA == nCinpK) nCinpA
      shB = [nImgs, nCoutK, nAh, nAw]
      shK1 = [1, nCinp, nKh, nKw]
  in tbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezFailed shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicezFailed shK1 arrK [iCout, 0, 0, 0]
      in tdot0 arrAt arrKt
    _ -> error "conv2d: impossible pattern needlessly required"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicezFailed
  :: (ADReady r, KnownNat n)
  => ShapeInt n -> TensorOf n r -> IndexOf n r -> TensorOf n r
slicezFailed shOut d ixBase =
  tbuild shOut $ \ixResult ->
    indexz0Failed d (zipWith_Index (+) ixBase ixResult)

-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
indexz0Failed
  :: forall r n. (ADReady r, KnownNat n)
  => TensorOf n r -> IndexOf n r -> TensorOf 0 r
indexz0Failed d ix = tcond (within0 @r (tshape d) ix) (d ! ix) 0

conv2d1Failed
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2d1Failed = conv2dFailed $ tconst $ OR.fromList [1, 1, 1, 1] [-0.2]

conv2dBFailed
  :: ADReady r
  => TensorOf 4 r -> TensorOf 4 r
conv2dBFailed = conv2dFailed $ tconst t16

testKonst0RevFailed :: Assertion
testKonst0RevFailed =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [2, 2, 2, 2] [18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001,18.1,29.1,32.1,40.1,582932.0,582934.99432,582597.1,582625.8943200001])
    (rev @(OR.Array 4 Double) conv2dBFailed (tkonst0N [2, 2, 2, 2] 0))

testKonst0Tiny1Failed :: Assertion
testKonst0Tiny1Failed =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 1, 1, 1] [-0.2])
    (rev' @(OR.Array 4 Double) conv2d1Failed (tkonst0N [1, 1, 1, 1] 0))

testKonst0TinySFailed :: Assertion
testKonst0TinySFailed =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1, 1, 1, 1] [582665.99432])
    (rev' @(OR.Array 4 Double)
          (conv2dFailed $ tconst $ tkonst0NR [1, 1, 1, 1] (tsum0R t16))
          (OR.fromList [1, 1, 1, 1] [0]))
