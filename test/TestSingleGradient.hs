{-# LANGUAGE FlexibleContexts #-}
module TestSingleGradient (testTrees) where

import Prelude

import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Numeric.LinearAlgebra (Numeric)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

type DualDeltaF = DualDelta Float

type VecDualDeltaF = VecDualDelta Float

testTrees :: [TestTree]
testTrees = [ dfTests
            , readmeTests
            ]

dfShow :: (VecDualDeltaF -> DeltaMonadGradient Float DualDeltaF)
       -> [Float]
       -> ([Float], Float)
dfShow f deltaInput =
  let ((results, _), value) = df f (V.fromList deltaInput, V.empty)
  in (V.toList results, value)

fX :: DeltaMonad Float m => VecDualDeltaF -> m DualDeltaF
fX vec = do
  let x = var vec 0
  return x

fX1Y :: DeltaMonad Float m => VecDualDeltaF -> m DualDeltaF
fX1Y vec = do
  let x = var vec 0
      y = var vec 1
  x1 <- x +\ scalar 1
  x1 *\ y

fXXY :: DeltaMonad Float m => VecDualDeltaF -> m DualDeltaF
fXXY vec = do
  let x = var vec 0
      y = var vec 1
  xy <- x *\ y
  x *\ xy

fXYplusZ :: DeltaMonad Float m => VecDualDeltaF -> m DualDeltaF
fXYplusZ vec = do
  let x = var vec 0
      y = var vec 1
      z = var vec 2
  xy <- x *\ y
  xy +\ z

fXtoY :: DeltaMonad Float m => VecDualDeltaF -> m DualDeltaF
fXtoY vec = do
  let x = var vec 0
      y = var vec 1
  x **\ y

freluX :: DeltaMonad Float m => VecDualDeltaF -> m DualDeltaF
freluX vec = do
  let x = var vec 0
  reluAct x

fquad :: DeltaMonad Float m => VecDualDeltaF -> m DualDeltaF
fquad vec = do
  let x = var vec 0
      y = var vec 1
  x2 <- squareDual x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ scalar 5

dfTests :: TestTree
dfTests = testGroup "Simple df application tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ dfShow f v @?= expected)
    [ ("fX", fX, [99], ([1.0],99.0))
    , ("fX1Y", fX1Y, [3, 2], ([2.0,4.0],8.0))
    , ("fXXY", fXXY, [3, 2], ([12.0,9.0],18.0))
    , ("fXYplusZ", fXYplusZ, [1, 2, 3], ([2.0,1.0,1.0],5.0))
    , ( "fXtoY", fXtoY, [0.00000000000001, 2]
      , ([2.0e-14,-3.2236188e-27],9.9999994e-29) )
    , ("fXtoY2", fXtoY, [1, 2], ([2.0,0.0],1.0))
    , ("freluX", freluX, [-1], ([0.0],0.0))
    , ("freluX2", freluX, [0], ([0.0],0.0))
    , ("freluX3", freluX, [0.0001], ([1.0],1.0e-4))
    , ("freluX4", freluX, [99], ([1.0],99.0))
    , ("fquad", fquad, [2, 3], ([4.0,6.0],18.0))
    ]

-- The input vector is meant to have 3 elements, the output vector
-- two elements. In the future we may use something like
-- https://hackage.haskell.org/package/vector-sized-1.5.0
-- to express the sizes in types, or we may be able to handle tuples
-- automatically. For now, the user has to translate from tuples
-- to vectors manually and we omit this straightforward boilerplate code here.
--
-- TODO: work on user-friendly errors if the input record is too short.
-- TODO: give the output vector the same type as the input vector,
-- which is a pair of an unboxed vector of scalars and a boxed vector
-- of deltas (the output vector currently is a boxed vector of pairs;
-- this is related to the ongoing work on shapes of scalar containers).
atanReadmePoly :: (RealFloat r, Numeric r)
               => VecDualDelta r -> Data.Vector.Vector (DualDelta r)
atanReadmePoly vec =
  let x : y : z : _ = vars vec
      w = x * sin y
  in V.fromList [atan2 z w, z * x]

-- According to the paper, to handle functions with non-scalar results,
-- we dot-product them with dt which, for simplicity, we here set
-- to a record containing only ones. We could also apply the dot-product
-- automatically in the library code (though perhaps we should
-- emit a warning too, in case the user just forgot to apply
-- a loss function and that's the only reason the result is not a scalar?).
-- For now, let's perform the dot product in user code.
--
-- The @sumDual@ introduces the only Delta-binding in this reverse
-- gradient computations. If the code above had any repeated
-- non-variable expressions, the user would need to make it monadic
-- and apply another binding-introducing operation already there.
atanReadmeMPoly :: (RealFloat r, DeltaMonad r m, Numeric r)
                => VecDualDelta r -> m (DualDelta r)
atanReadmeMPoly vec =
  sumDual $ atanReadmePoly vec
    -- dot product with ones is the sum of all elements

dfAtanReadmeMPoly :: ( RealFloat r, Numeric r
                     , Num (Data.Vector.Storable.Vector r) )
                  => Domain r -> (Domain' r, r)
dfAtanReadmeMPoly ds =
  let ((res, _), value) = df atanReadmeMPoly (ds, V.empty)
  in (res, value)

readmeTests :: TestTree
readmeTests = testGroup "Tests of code from the library's future README"
  [ testCase "Poly Float (1.1, 2.2, 3.3)"
    $ dfAtanReadmeMPoly (V.fromList [1.1 :: Float, 2.2, 3.3])
      @?= (V.fromList [3.0715904, 0.18288425, 1.1761366], 4.937552)
  , testCase "Poly Double (1.1, 2.2, 3.3)"
    $ dfAtanReadmeMPoly (V.fromList [1.1 :: Double, 2.2, 3.3])
      @?= ( V.fromList [ 3.071590389300859
                       , 0.18288422990948425
                       , 1.1761365368997136 ]
          , 4.9375516951604155 )
  ]
