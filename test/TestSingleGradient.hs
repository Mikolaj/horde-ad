{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module TestSingleGradient (testTrees) where

import Prelude

import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector, konst)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd hiding (sumElementsVectorOfDelta)

type DualNumberF = DualNumber Float

type DualNumberVariablesF = DualNumberVariables Float

testTrees :: [TestTree]
testTrees = [ dfTests
            , readmeTests
            , readmeTestsV
            ]

-- Unfortunately, monadic versions of the operations below are not
-- polymorphic over whether they operate on scalars, vectors or other types,
-- so we should probably abandon them.

(+\) :: (DeltaMonad r m, Num r)
     => DualNumber r -> DualNumber r -> m (DualNumber r)
(+\) u v = returnLet $ u + v

(*\) :: (DeltaMonad r m, Num r)
     => DualNumber r -> DualNumber r -> m (DualNumber r)
(*\) u v = returnLet $ u * v

(**\) :: (DeltaMonad r m, Floating r)
      => DualNumber r -> DualNumber r -> m (DualNumber r)
(**\) u v = returnLet $ u ** v

squareDual :: (DeltaMonad r m, Num r) => DualNumber r -> m (DualNumber r)
squareDual = returnLet . square

dfShow :: (DualNumberVariablesF -> DeltaMonadGradient Float DualNumberF)
       -> [Float]
       -> ([Float], Float)
dfShow f deltaInput =
  let ((results, _, _), value) = df f (V.fromList deltaInput, V.empty, V.empty)
  in (V.toList results, value)

fX :: DeltaMonad Float m => DualNumberVariablesF -> m DualNumberF
fX variables = do
  let x = var variables 0
  return x

fX1Y :: DeltaMonad Float m => DualNumberVariablesF -> m DualNumberF
fX1Y variables = do
  let x = var variables 0
      y = var variables 1
  x1 <- x +\ scalar 1
  x1 *\ y

fXXY :: DeltaMonad Float m => DualNumberVariablesF -> m DualNumberF
fXXY variables = do
  let x = var variables 0
      y = var variables 1
  xy <- x *\ y
  x *\ xy

fXYplusZ :: DeltaMonad Float m => DualNumberVariablesF -> m DualNumberF
fXYplusZ variables = do
  let x = var variables 0
      y = var variables 1
      z = var variables 2
  xy <- x *\ y
  xy +\ z

fXtoY :: DeltaMonad Float m => DualNumberVariablesF -> m DualNumberF
fXtoY variables = do
  let x = var variables 0
      y = var variables 1
  x **\ y

freluX :: DeltaMonad Float m => DualNumberVariablesF -> m DualNumberF
freluX variables = do
  let x = var variables 0
  reluAct x

fquad :: DeltaMonad Float m => DualNumberVariablesF -> m DualNumberF
fquad variables = do
  let x = var variables 0
      y = var variables 1
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
-- TODO: while we used weakly-typed vectors, work on user-friendly errors
-- if the input record is too short.
atanReadmePoly :: (RealFloat r, Numeric r)
               => DualNumberVariables r -> Data.Vector.Vector (DualNumber r)
atanReadmePoly variables =
  let x : y : z : _ = vars variables
      w = x * sin y
  in V.fromList [atan2 z w, z * x]

-- According to the paper, to handle functions with non-scalar results,
-- we dot-product them with dt which, for simplicity, we here set
-- to a record containing only ones. We could also apply the dot-product
-- automatically in the library code (though perhaps we should
-- emit a warning too, in case the user just forgot to apply
-- a loss function and that's the only reason the result is not a scalar?).
-- For now, let's perform the dot product in user code.
-- Here is the code for dot product with ones, which is just the sum
-- of elements of a vector:
sumElementsVectorOfDelta :: Num r
                         => Data.Vector.Vector (DualNumber r)
                         -> DualNumber r
sumElementsVectorOfDelta = V.foldl' (+) (scalar 0)

-- Here we introduce the only Delta-let binding (@returnLet@) to ensure
-- that if this code is used in a larger context and repeated,
-- no explosion of delta-expression can happen.
-- If the code above had any repeated non-variable expressions
-- (e.g., if @w@ appeared twice) the user would need to make it monadic
-- and apply @returnLet@ already there.
atanReadmeMPoly :: (DeltaMonad r m, RealFloat r, Numeric r)
                => DualNumberVariables r -> m (DualNumber r)
atanReadmeMPoly variables =
  returnLet $ sumElementsVectorOfDelta $ atanReadmePoly variables

-- The underscores and empty vectors are placeholders for the vector
-- and matrix components of the parameters triple, which we here don't use
-- (we construct vectors, but from scalar parameters).
dfAtanReadmeMPoly :: (RealFloat r, Numeric r, Num (Vector r))
                  => Domain r -> (Domain' r, r)
dfAtanReadmeMPoly ds =
  let ((result, _, _), value) = df atanReadmeMPoly (ds, V.empty, V.empty)
  in (result, value)

readmeTests :: TestTree
readmeTests = testGroup "Tests of code from the library's README"
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

-- And here's a version of the example that uses vector parameters
-- (quite wasteful in this case) and transforms intermediate results
-- via a primitive differentiable type of vectors instead of inside
-- vectors of primitive differentiable scalars.

atanReadmePolyV :: (RealFloat r, Numeric r)
                => DualNumberVariables r -> DualNumber (Vector r)
atanReadmePolyV variables =
  let xyzVector = varV variables 0
      x = indexDeltaOfVector xyzVector 0
      y = indexDeltaOfVector xyzVector 1
      z = indexDeltaOfVector xyzVector 2
      w = x * sin y
  in deltaSeq $ V.fromList [atan2 z w, z * x]

atanReadmeMPolyV :: (DeltaMonad r m, RealFloat r, Numeric r)
                 => DualNumberVariables r -> m (DualNumber r)
atanReadmeMPolyV variables =
  returnLet $ atanReadmePolyV variables <.>!! konst 1 2

-- The underscores and empty vectors are placeholders for the vector
-- and matrix components of the parameters triple, which we here don't use
-- (we construct vectors, but from scalar parameters).
dfAtanReadmeMPolyV :: (RealFloat r, Numeric r, Num (Vector r))
                   => DomainV r -> (DomainV' r, r)
dfAtanReadmeMPolyV dsV =
  let ((_, result, _), value) = df atanReadmeMPolyV (V.empty, dsV, V.empty)
  in (result, value)

readmeTestsV :: TestTree
readmeTestsV = testGroup "Tests of vector-based code from the library's README"
  [ testCase "PolyV Float (1.1, 2.2, 3.3)"
    $ dfAtanReadmeMPolyV (V.singleton $ V.fromList [1.1 :: Float, 2.2, 3.3])
      @?= ( V.singleton $ V.fromList [3.0715904, 0.18288425, 1.1761366]
          , 4.937552 )
  , testCase "PolyV Double (1.1, 2.2, 3.3)"
    $ dfAtanReadmeMPolyV (V.singleton $ V.fromList [1.1 :: Double, 2.2, 3.3])
      @?= ( V.singleton $ V.fromList [ 3.071590389300859
                                     , 0.18288422990948425
                                     , 1.1761365368997136 ]
          , 4.9375516951604155 )
  ]
