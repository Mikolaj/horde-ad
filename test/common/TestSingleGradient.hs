{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
-- Needed due to unsafePerformIO:
{-# OPTIONS_GHC -fno-full-laziness #-}
module TestSingleGradient (testTrees) where

import Prelude

import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd hiding (sumElementsVectorOfDual)

import TestCommon
import TestCommonEqEpsilon

testTrees :: [TestTree]
testTrees = [ testDReverse0
            , testDReverse1
            , testPrintDf
            , testDForward
            , testDFastForward
            , quickCheckForwardAndBackward
            , readmeTests
            , readmeTestsV
            ]

dReverse0
  :: HasDelta r
  => (DualNumberVariables 'DModeGradient r
      -> DualMonadGradient r (DualNumber 'DModeGradient r))
  -> [r]
  -> IO ([r], r)
dReverse0 f deltaInput = do
  ((!results, _, _, _), !value) <-
    dReverse 1 f (V.fromList deltaInput, V.empty, V.empty, V.empty)
  return (V.toList results, value)

fX :: DualMonad 'DModeGradient Float m
   => DualNumberVariables 'DModeGradient Float
   -> m (DualNumber 'DModeGradient Float)
fX variables = do
  let x = var0 variables 0
  return x

fXp1 :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fXp1 variables = do
  let x = var0 variables 0
  x +\ 1

fXpX :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fXpX variables = do
  let x = var0 variables 0
  x +\ x

fXX :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fXX variables = do
  let x = var0 variables 0
  x *\ x

fX1X :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fX1X variables = do
  let x = var0 variables 0
  x1 <- x +\ 1
  x1 *\ x

fX1Y :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fX1Y variables = do
  let x = var0 variables 0
      y = var0 variables 1
  x1 <- x +\ 1
  x1 *\ y

fY1X :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fY1X variables = do
  let x = var0 variables 0
      y = var0 variables 1
  x1 <- y +\ 1
  x1 *\ x

fXXY :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fXXY variables = do
  let x = var0 variables 0
      y = var0 variables 1
  xy <- x *\ y
  x *\ xy

fXYplusZ :: DualMonad 'DModeGradient Float m
         => DualNumberVariables 'DModeGradient Float
         -> m (DualNumber 'DModeGradient Float)
fXYplusZ variables = do
  let x = var0 variables 0
      y = var0 variables 1
      z = var0 variables 2
  xy <- x *\ y
  xy +\ z

fXtoY :: DualMonad 'DModeGradient Float m
      => DualNumberVariables 'DModeGradient Float
      -> m (DualNumber 'DModeGradient Float)
fXtoY variables = do
  let x = var0 variables 0
      y = var0 variables 1
  x **\ y

freluX :: DualMonad 'DModeGradient Float m
       => DualNumberVariables 'DModeGradient Float
       -> m (DualNumber 'DModeGradient Float)
freluX variables = do
  let x = var0 variables 0
  reluAct x

testDReverse0 :: TestTree
testDReverse0 = testGroup "Simple dReverse application tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ do
          res <- dReverse0 f v
          res @?~ expected)
    [ ("fX", fX, [99], ([1.0],99.0))
    , ("fXagain", fX, [99], ([1.0],99.0))
    , ("fXp1", fXp1, [99], ([1.0],100))
    , ("fXpX", fXpX, [99], ([2.0],198))
    , ("fXX", fXX, [2], ([4],4))
    , ("fX1X", fX1X, [2], ([5],6))
    , ("fX1Y", fX1Y, [3, 2], ([2.0,4.0],8.0))
    , ("fY1X", fY1X, [2, 3], ([4.0,2.0],8.0))
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

-- hlint would complain about spurious @id@, so we need to define our own.
id2 :: a -> a
id2 x = x

sinKonst
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
sinKonst variables = do
  let x = var1 variables 0
  return $ sumElements0 $
    sin x + (id2 $ id2 $ id2 $ konst1 1 2)

powKonst
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
powKonst variables = do
  let x = var1 variables 0
  return $ sumElements0 $
    x ** (sin x + (id2 $ id2 $ id2 $ konst1 (sumElements0 x) 2))

sinKonstS
  :: forall d r m. DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
sinKonstS variables = do
  let x = varS variables 0
  return $ sumElements0 $ fromS1
    ((sin x + (id2 $ id2 $ id2 $ konstS 1))
       :: DualNumber d (OS.Array '[2] r))

dReverse1
  :: (r ~ Float, d ~ 'DModeGradient)
  => (DualNumberVariables d r -> DualMonadGradient r (DualNumber d r))
  -> [[r]]
  -> IO ([[r]], r)
dReverse1 f deltaInput = do
  ((_, !results, _, _), !value) <-
    dReverse 1 f
             (V.empty, V.fromList (map V.fromList deltaInput), V.empty, V.empty)
  return (map V.toList $ V.toList results, value)

testDReverse1 :: TestTree
testDReverse1 = testGroup "Simple dReverse application to vectors tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ do
          res <- dReverse1 f v
          res @?~ expected)
    [ ("sumElementsV", sumElementsV, [[1, 1, 3]], ([[1.0,1.0,1.0]],5.0))
    , ("altSumElementsV", altSumElementsV, [[1, 1, 3]], ([[1.0,1.0,1.0]],5.0))
    , ( "sinKonst", sinKonst, [[1, 3]]
      , ([[0.5403023,-0.9899925]],2.982591) )
    , ( "powKonst", powKonst, [[1, 3]]
      , ([[108.7523,131.60072]],95.58371) )
    ]

testPrintDf :: TestTree
testPrintDf = testGroup "Pretty printing test" $
  map (\(txt, f, v, expected) ->
        testCase txt $ do
          output <- prettyPrintDf f
                      (V.empty, V.fromList (map V.fromList v), V.empty, V.empty)
          output @?= expected)
    [ ( "sumElementsV", sumElementsV, [[1 :: Float, 1, 3]]
      , "Delta0 0 (DeltaId 0) (SumElements0 (Input1 (DeltaId 0)) 3)" )
    , ( "altSumElementsV", altSumElementsV, [[1, 1, 3]]
      , "Delta0\n  5\n  (DeltaId 5)\n  (Add0\n     (Delta0 4 (DeltaId 4) (Index0 (Input1 (DeltaId 0)) 2 3))\n     (Delta0\n        3\n        (DeltaId 3)\n        (Add0\n           (Delta0 2 (DeltaId 2) (Index0 (Input1 (DeltaId 0)) 1 3))\n           (Delta0\n              1\n              (DeltaId 1)\n              (Add0\n                 (Delta0 0 (DeltaId 0) (Index0 (Input1 (DeltaId 0)) 0 3)) Zero0)))))" )
    , ( "sinKonst", sinKonst, [[1, 3]]
      , "Delta0\n  3\n  (DeltaId 0)\n  (SumElements0\n     (Delta1\n        2\n        (DeltaId 3)\n        (Add1\n           (Delta1\n              0\n              (DeltaId 1)\n              (Scale1 [ 0.5403023 , -0.9899925 ] (Input1 (DeltaId 0))))\n           (Delta1 1 (DeltaId 2) (Konst1 Zero0 2))))\n     2)" )
    , ( "powKonst", powKonst, [[1, 3]]
      , "Delta0\n  7\n  (DeltaId 1)\n  (SumElements0\n     (Delta1\n        6\n        (DeltaId 6)\n        (Add1\n           (Delta1\n              4\n              (DeltaId 4)\n              (Scale1 [ 4.8414707 , 130.56084 ] (Input1 (DeltaId 0))))\n           (Delta1\n              5\n              (DeltaId 5)\n              (Scale1\n                 [ 0.0 , 103.91083 ]\n                 (Delta1\n                    3\n                    (DeltaId 3)\n                    (Add1\n                       (Delta1\n                          0\n                          (DeltaId 1)\n                          (Scale1 [ 0.5403023 , -0.9899925 ] (Input1 (DeltaId 0))))\n                       (Delta1\n                          2\n                          (DeltaId 2)\n                          (Konst1\n                             (Delta0 1 (DeltaId 0) (SumElements0 (Input1 (DeltaId 0)) 2))\n                             2))))))))\n     2)" )
    ]

testDForward :: TestTree
testDForward =
 testGroup "Simple dForward application tests" $
  map (\(txt, f, v, expected) ->
        let vp = listsToParameters v
        in testCase txt $ do
          res <- dForward f vp vp
          res @?~ expected)
    [ ("fquad", fquad, ([2 :: Double, 3], []), (26.0, 18.0))
    , ( "atanReadmeM", atanReadmeM, ([1.1, 2.2, 3.3], [])
      , (7.662345305800865, 4.9375516951604155) )
    , ( "vatanReadmeM", vatanReadmeM, ([], [1.1, 2.2, 3.3])
      , (7.662345305800865, 4.9375516951604155) )
    ]

testDFastForward :: TestTree
testDFastForward =
 testGroup "Simple dFastForward application tests" $
  map (\(txt, f, v, expected) ->
        let vp = listsToParameters v
        in testCase txt $ dFastForward f vp vp @?~ expected)
    [ ("fquad", fquad, ([2 :: Double, 3], []), (26.0, 18.0))
    , ( "atanReadmeM", atanReadmeM, ([1.1, 2.2, 3.3], [])
      , (7.662345305800865, 4.9375516951604155) )
    , ( "vatanReadmeM", vatanReadmeM, ([], [1.1, 2.2, 3.3])
      , (7.662345305800865, 4.9375516951604155) )
    ]

-- The formula for comparing derivative and gradient is due to @awf
-- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
quickCheckForwardAndBackward :: TestTree
quickCheckForwardAndBackward =
  testGroup "Simple QuickCheck of gradient vs derivative vs perturbation"
    [ quickCheckTest0 "fquad" fquad (\(x, y, _z) -> ([x, y], [], [], []))
    , quickCheckTest0 "atanReadmeM" atanReadmeM
             (\(x, y, z) -> ([x, y, z], [], [], []))
    , quickCheckTest0 "vatanReadmeM" vatanReadmeM
             (\(x, y, z) -> ([], [x, y, z], [], []))
    , quickCheckTest0 "sinKonst" sinKonst  -- powKonst NaNs immediately
             (\(x, _, z) -> ([], [x, z], [], []))
    , quickCheckTest0 "sinKonstS" sinKonstS
             (\(x, _, z) -> ([], [], [], [x, z]))
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
                   => Domain0 r -> IO (Domain0 r, r)
atanReadmeDReverse ds = do
  ((!result, _, _, _), !value) <-
    dReverse 1 atanReadmeM (ds, V.empty, V.empty, V.empty)
  return (result, value)

readmeTests :: TestTree
readmeTests = testGroup "Simple tests for README"
  [ testCase " Float (1.1, 2.2, 3.3)" $ do
      res <- atanReadmeDReverse (V.fromList [1.1 :: Float, 2.2, 3.3])
      res @?~ (V.fromList [3.0715904, 0.18288425, 1.1761366], 4.937552)
  , testCase " Double (1.1, 2.2, 3.3)" $ do
      res <- atanReadmeDReverse (V.fromList [1.1 :: Double, 2.2, 3.3])
      res @?~ ( V.fromList [ 3.071590389300859
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
                    => Domain1 r -> IO(Domain1 r, r)
vatanReadmeDReverse dsV = do
  ((_, !result, _, _), !value) <-
    dReverse 1 vatanReadmeM (V.empty, dsV, V.empty, V.empty)
  return (result, value)

readmeTestsV :: TestTree
readmeTestsV = testGroup "Simple tests of vector-based code for README"
  [ testCase "V Float (1.1, 2.2, 3.3)" $ do
      res <- vatanReadmeDReverse (V.singleton $ V.fromList [1.1 :: Float, 2.2, 3.3])
      res @?~ ( V.singleton $ V.fromList [3.0715904, 0.18288425, 1.1761366]
              , 4.937552 )
  , testCase "V Double (1.1, 2.2, 3.3)" $ do
      res <- vatanReadmeDReverse (V.singleton $ V.fromList [1.1 :: Double, 2.2, 3.3])
      res @?~ ( V.singleton $ V.fromList [ 3.071590389300859
                                         , 0.18288422990948425
                                         , 1.1761365368997136 ]
              , 4.9375516951604155 )
  ]
