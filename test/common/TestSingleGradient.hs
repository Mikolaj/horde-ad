{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module TestSingleGradient (testTrees, fquad, quad) where

import Prelude

import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Test.Tasty.QuickCheck

import HordeAd hiding (sumElementsVectorOfDual)
import HordeAd.Core.DualClass (DifferentiationScheme (..))

testTrees :: [TestTree]
testTrees = [ testDReverse0
            , testDReverse1
            , testDForward
            , testDFastForward
            , quickCheckForwardAndBackward
            , readmeTests
            , readmeTestsV
            ]

-- Unfortunately, monadic versions of the operations below are not
-- polymorphic over whether they operate on scalars, vectors or other types,
-- so we should probably abandon them.

(+\) :: DualMonad d r m => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(+\) u v = returnLet $ u + v

(*\) :: DualMonad d r m => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(*\) u v = returnLet $ u * v

(**\) :: DualMonad d r m
      => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(**\) u v = returnLet $ u ** v

dReverse0
  :: HasDelta r
  => (DualNumberVariables 'DifferentiationSchemeGradient r -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
  -> [r]
  -> ([r], r)
dReverse0 f deltaInput =
  let ((results, _, _, _), value) =
        dReverse 1 f (V.fromList deltaInput, V.empty, V.empty, V.empty)
  in (V.toList results, value)

fX :: DualMonad 'DifferentiationSchemeGradient Float m
   => DualNumberVariables 'DifferentiationSchemeGradient Float -> m (DualNumber 'DifferentiationSchemeGradient Float)
fX variables = do
  let x = var0 variables 0
  return x

fX1Y :: DualMonad 'DifferentiationSchemeGradient Float m
     => DualNumberVariables 'DifferentiationSchemeGradient Float -> m (DualNumber 'DifferentiationSchemeGradient Float)
fX1Y variables = do
  let x = var0 variables 0
      y = var0 variables 1
  x1 <- x +\ 1
  x1 *\ y

fXXY :: DualMonad 'DifferentiationSchemeGradient Float m
     => DualNumberVariables 'DifferentiationSchemeGradient Float -> m (DualNumber 'DifferentiationSchemeGradient Float)
fXXY variables = do
  let x = var0 variables 0
      y = var0 variables 1
  xy <- x *\ y
  x *\ xy

fXYplusZ :: DualMonad 'DifferentiationSchemeGradient Float m
         => DualNumberVariables 'DifferentiationSchemeGradient Float -> m (DualNumber 'DifferentiationSchemeGradient Float)
fXYplusZ variables = do
  let x = var0 variables 0
      y = var0 variables 1
      z = var0 variables 2
  xy <- x *\ y
  xy +\ z

fXtoY :: DualMonad 'DifferentiationSchemeGradient Float m
      => DualNumberVariables 'DifferentiationSchemeGradient Float -> m (DualNumber 'DifferentiationSchemeGradient Float)
fXtoY variables = do
  let x = var0 variables 0
      y = var0 variables 1
  x **\ y

freluX :: DualMonad 'DifferentiationSchemeGradient Float m
       => DualNumberVariables 'DifferentiationSchemeGradient Float -> m (DualNumber 'DifferentiationSchemeGradient Float)
freluX variables = do
  let x = var0 variables 0
  reluAct x

quad :: DualMonad d r m
     => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
quad x y = do
  x2 <- returnLet $ square x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ 5

fquad :: forall r d m. DualMonad d r m
      => DualNumberVariables d r -> m (DualNumber d r)
fquad variables = do
  let x = var0 variables 0
      y = var0 variables 1
  quad x y

testDReverse0 :: TestTree
testDReverse0 = testGroup "Simple dReverse application tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ dReverse0 f v @?= expected)
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
    , ("scalarSum", vec_omit_scalarSum_aux, [1, 1, 3], ([1.0,1.0,1.0],5.0))
    ]

vec_omit_scalarSum_aux
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
vec_omit_scalarSum_aux vec = returnLet $ foldlDual' (+) 0 vec

sumElementsV
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
sumElementsV variables = do
  let x = var1 variables 0
  returnLet $ sumElements0 x

altSumElementsV
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
altSumElementsV variables = do
  let x = var1 variables 0
  returnLet $ altSumElements0 x

dReverse1
  :: (r ~ Float, d ~ 'DifferentiationSchemeGradient)
  => (DualNumberVariables d r -> DualMonadGradient r (DualNumber d r))
  -> [[Float]]
  -> ([[Float]], Float)
dReverse1 f deltaInput =
  let ((_, results, _, _), value) =
        dReverse 1 f
          (V.empty, V.fromList (map V.fromList deltaInput), V.empty, V.empty)
  in (map V.toList $ V.toList results, value)

testDReverse1 :: TestTree
testDReverse1 = testGroup "Simple dReverse application to vectors tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ dReverse1 f v @?= expected)
    [ ("sumElementsV", sumElementsV, [[1, 1, 3]], ([[1.0,1.0,1.0]],5.0))
    , ("altSumElementsV", altSumElementsV, [[1, 1, 3]], ([[1.0,1.0,1.0]],5.0))
    ]

testDForward :: TestTree
testDForward =
 testGroup "Simple dForward application tests" $
  map (\(txt, f, v, expected) ->
        let vp = listsToParameters v
        in testCase txt $ dForward f vp vp @?= expected)
    [ ("fquad", fquad, ([2 :: Double, 3], []), (26.0, 18.0))
    , ( "atanReadmeM", atanReadmeM, ([1.1, 2.2, 3.3], [])
      , (7.662345305800865, 4.9375516951604155) )
    , ( "vatanReadmeM", vatanReadmeM, ([], [1.1, 2.2, 3.3])
      , (7.662345305800865, 4.9375516951604155) )
    ]

listsToParameters :: ([Double], [Double]) -> Domains Double
listsToParameters (a0, a1) =
  (V.fromList a0, V.singleton $ V.fromList a1, V.empty, V.empty)

testDFastForward :: TestTree
testDFastForward =
 testGroup "Simple dFastForward application tests" $
  map (\(txt, f, v, expected) ->
        let vp = listsToParameters v
        in testCase txt $ dFastForward f vp vp @?= expected)
    [ ("fquad", fquad, ([2 :: Double, 3], []), (26.0, 18.0))
    , ( "atanReadmeM", atanReadmeM, ([1.1, 2.2, 3.3], [])
      , (7.662345305800865, 4.9375516951604155) )
    , ( "vatanReadmeM", vatanReadmeM, ([], [1.1, 2.2, 3.3])
      , (7.662345305800865, 4.9375516951604155) )
    ]

qcTest :: TestName
       -> (forall d r m. DualMonad d r m
           => DualNumberVariables d r -> m (DualNumber d r))
       -> ((Double, Double, Double) -> ([Double], [Double]))
       -> TestTree
qcTest txt f fArg =
  testProperty txt
  $ forAll (choose ((-2, -2, -2), (2, 2, 2))) $ \xyz dsRaw ->
    forAll (choose ( (-1e-7, -1e-7, -1e-7)
                   , (1e-7, 1e-7, 1e-7) )) $ \perturbationRaw ->
    forAll (choose (-10, 10)) $ \dt ->
      let args = listsToParameters $ fArg xyz
          ds = listsToParameters $ fArg dsRaw
          perturbation = listsToParameters $ fArg perturbationRaw
          ff@(derivative, ffValue) = dFastForward f args ds
          (derivativeAtPerturbation, valueAtPerturbation) =
            dFastForward f args perturbation
          close a b = abs (a - b) <= 1e-4
          (gradient, revValue) = dReverse dt f args
      in -- Two forward derivative implementations agree fully:
         dForward f args ds === ff
         -- Objective function value from gradients is the same.
         .&&. ffValue == revValue
         -- Gradients and derivatives agree.
         .&&. close (dt * derivative)
                    (dotParameters gradient ds)
         -- Objective function value is unaffected by perturbation.
         .&&. ffValue == valueAtPerturbation
         -- Derivative approximates the perturbation of value.
         .&&. close (primalValue
                                 f (addParameters
                                                  args perturbation))
                    (ffValue + derivativeAtPerturbation)

-- The formula for comparing derivative and gradient is due to @awf
-- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
quickCheckForwardAndBackward :: TestTree
quickCheckForwardAndBackward =
  testGroup "Simple QuickCheck of gradient vs derivative vs perturbation" $
    [ qcTest "fquad" fquad (\(x, y, _z) -> ([x, y], []))
    , qcTest "atanReadmeM" atanReadmeM
             (\(x, y, z) -> ([x, y, z], []))
    , qcTest "vatanReadmeM" vatanReadmeM
             (\(x, y, z) -> ([], [x, y, z]))
    ]

-- A function that goes from `R^3` to `R^2`, with a representation
-- of the input and the output tuple that is convenient for interfacing
-- with the library.
atanReadmeOriginal :: RealFloat a => a -> a -> a -> Data.Vector.Vector a
atanReadmeOriginal x y z =
  let w = x * sin y
  in V.fromList [atan2 z w, z * x]

-- Here we instantiate the function to dual numbers
-- and add a glue code that selects the function inputs from
-- a uniform representation of objective function parameters
-- represented as delta-variables (`DualNumberVariables`).
atanReadmeVariables
  :: IsScalar d r
  => DualNumberVariables d r -> Data.Vector.Vector (DualNumber d r)
atanReadmeVariables variables =
  let x : y : z : _ = vars variables
  in atanReadmeOriginal x y z

-- According to the paper, to handle functions with non-scalar results,
-- we dot-product them with dt which, for simplicity, we here set
-- to a record containing only ones. We could also apply the dot-product
-- automatically in the library code (though perhaps we should
-- emit a warning too, in case the user just forgot to apply
-- a loss function and that's the only reason the result is not a scalar?).
-- For now, let's perform the dot product in user code.

-- Here is the function for dot product with ones, which is just the sum
-- of elements of a vector.
sumElementsOfDualNumbers
  :: IsScalar d r
  => Data.Vector.Vector (DualNumber d r) -> DualNumber d r
sumElementsOfDualNumbers = V.foldl' (+) 0

-- Here we apply the function.
atanReadmeScalar
  :: IsScalar d r
  => DualNumberVariables d r -> DualNumber d r
atanReadmeScalar = sumElementsOfDualNumbers . atanReadmeVariables

-- Here we introduce a single delta-let binding (`returnLet`) to ensure
-- that if this code is used in a larger context and repeated,
-- no explosion of delta-expressions can happen.
-- If the code above had any repeated non-variable expressions
-- (e.g., if @w@ appeared twice) the user would need to make it monadic
-- and apply @returnLet@ already there.
atanReadmeM
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
atanReadmeM = returnLet . atanReadmeScalar

-- The underscores and empty vectors are placeholders for the vector,
-- matrix and arbitrary tensor components of the parameters tuple,
-- which we here don't use (above we construct a vector output,
-- but it's a vector of scalar parameters, not a single parameter
-- of rank 1).
atanReadmeDReverse :: HasDelta r
                   => Domain0 r -> (Domain0 r, r)
atanReadmeDReverse ds =
  let ((result, _, _, _), value) =
        dReverse 1 atanReadmeM (ds, V.empty, V.empty, V.empty)
  in (result, value)

readmeTests :: TestTree
readmeTests = testGroup "Simple tests for README"
  [ testCase " Float (1.1, 2.2, 3.3)"
    $ atanReadmeDReverse (V.fromList [1.1 :: Float, 2.2, 3.3])
      @?= (V.fromList [3.0715904, 0.18288425, 1.1761366], 4.937552)
  , testCase " Double (1.1, 2.2, 3.3)"
    $ atanReadmeDReverse (V.fromList [1.1 :: Double, 2.2, 3.3])
      @?= ( V.fromList [ 3.071590389300859
                       , 0.18288422990948425
                       , 1.1761365368997136 ]
          , 4.9375516951604155 )
  ]

-- And here's a version of the example that uses vector parameters
-- (quite wasteful in this case) and transforms intermediate results
-- via a primitive differentiable type of vectors instead of inside
-- vectors of primitive differentiable scalars.

vatanReadmeM
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
vatanReadmeM variables = do
  let xyzVector = var1 variables 0
      [x, y, z] = map (index0 xyzVector) [0, 1, 2]
      v = seq1 $ atanReadmeOriginal x y z
  returnLet $ sumElements0 v

vatanReadmeDReverse :: HasDelta r
                    => Domain1 r -> (Domain1 r, r)
vatanReadmeDReverse dsV =
  let ((_, result, _, _), value) =
        dReverse 1 vatanReadmeM (V.empty, dsV, V.empty, V.empty)
  in (result, value)

readmeTestsV :: TestTree
readmeTestsV = testGroup "Simple tests of vector-based code for README"
  [ testCase "V Float (1.1, 2.2, 3.3)"
    $ vatanReadmeDReverse (V.singleton $ V.fromList [1.1 :: Float, 2.2, 3.3])
      @?= ( V.singleton $ V.fromList [3.0715904, 0.18288425, 1.1761366]
          , 4.937552 )
  , testCase "V Double (1.1, 2.2, 3.3)"
    $ vatanReadmeDReverse (V.singleton $ V.fromList [1.1 :: Double, 2.2, 3.3])
      @?= ( V.singleton $ V.fromList [ 3.071590389300859
                                     , 0.18288422990948425
                                     , 1.1761365368997136 ]
          , 4.9375516951604155 )
  ]
