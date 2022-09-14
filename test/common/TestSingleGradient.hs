{-# LANGUAGE DataKinds, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestSingleGradient (testTrees, finalCounter) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (type (+))
import           System.IO (hPutStrLn, stderr)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd hiding (sumElementsVectorOfDual)
import HordeAd.Core.DualClass (unsafeGetFreshId)
  -- for a special test

import TestCommon
import TestCommonEqEpsilon

testTrees :: [TestTree]
testTrees = [ testDReverse0
            , testDReverse1
            , testPrintDf
            , testDForward
            , testDFastForward
            , quickCheckForwardAndBackward
            , oldReadmeTests
            , oldReadmeTestsV
            , readmeTests0
            , testGroup "Simple tests of tensor-based code for README"
                        [testCase "S" testFooS]
            ]

revIO0
  :: HasDelta r
  => (ADValInputs 'ADModeGradient r
      -> ADVal 'ADModeGradient r)
  -> [r]
  -> IO ([r], r)
revIO0 f deltaInput = do
  ((!results, _, _, _), !v) <-
    revIO 1 f (V.fromList deltaInput, V.empty, V.empty, V.empty)
  return (V.toList results, v)

fX :: ADValInputs 'ADModeGradient Float
   -> ADVal 'ADModeGradient Float
fX inputs = at0 inputs 0

fXp1 :: ADValInputs 'ADModeGradient Float
     -> ADVal 'ADModeGradient Float
fXp1 inputs =
  let x = at0 inputs 0
  in x + 1

fXpX :: ADValInputs 'ADModeGradient Float
     -> ADVal 'ADModeGradient Float
fXpX inputs =
  let x = at0 inputs 0
  in x + x

fXX :: ADValInputs 'ADModeGradient Float
    -> ADVal 'ADModeGradient Float
fXX inputs =
  let x = at0 inputs 0
  in x * x

fX1X :: ADValInputs 'ADModeGradient Float
     -> ADVal 'ADModeGradient Float
fX1X inputs =
  let x = at0 inputs 0
      x1 = x + 1
  in x1 * x

fX1Y :: ADValInputs 'ADModeGradient Float
     -> ADVal 'ADModeGradient Float
fX1Y inputs =
  let x = at0 inputs 0
      y = at0 inputs 1
      x1 = x + 1
  in x1 * y

fY1X :: ADValInputs 'ADModeGradient Float
     -> ADVal 'ADModeGradient Float
fY1X inputs =
  let x = at0 inputs 0
      y = at0 inputs 1
      x1 = y + 1
  in x1 * x

fXXY ::  ADValInputs 'ADModeGradient Float
     -> ADVal 'ADModeGradient Float
fXXY inputs =
  let x = at0 inputs 0
      y = at0 inputs 1
      xy = x * y
  in x * xy

fXYplusZ :: ADValInputs 'ADModeGradient Float
         -> ADVal 'ADModeGradient Float
fXYplusZ inputs =
  let x = at0 inputs 0
      y = at0 inputs 1
      z = at0 inputs 2
      xy = x * y
  in xy + z

fXtoY :: ADValInputs 'ADModeGradient Float
      -> ADVal 'ADModeGradient Float
fXtoY inputs =
  let x = at0 inputs 0
      y = at0 inputs 1
  in x ** y

freluX :: ADValInputs 'ADModeGradient Float
       -> ADVal 'ADModeGradient Float
freluX inputs =
  let x = at0 inputs 0
  in relu x

testDReverse0 :: TestTree
testDReverse0 = testGroup "Simple revIO application tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ do
          res <- revIO0 f v
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
    , ("scalarSum", vec_scalarSum_aux, [1, 1, 3], ([1.0,1.0,1.0],5.0))
    ]

vec_scalarSum_aux
  :: ADModeAndNum d r
  => ADValInputs d r -> ADVal d r
vec_scalarSum_aux = foldlDual' (+) 0

sumElementsV
  :: ADModeAndNum d r
  => ADValInputs d r -> ADVal d r
sumElementsV inputs =
  let x = at1 inputs 0
  in sumElements0 x

altSumElementsV
  :: ADModeAndNum d r
  => ADValInputs d r -> ADVal d r
altSumElementsV inputs =
  let x = at1 inputs 0
  in altSumElements0 x

-- hlint would complain about spurious @id@, so we need to define our own.
id2 :: a -> a
id2 x = x

sinKonst
  :: ADModeAndNum d r
  => ADValInputs d r -> ADVal d r
sinKonst inputs =
  let x = at1 inputs 0
  in sumElements0 $
       sin x + (id2 $ id2 $ id2 $ konst1 1 2)

powKonst
  :: ADModeAndNum d r
  => ADValInputs d r -> ADVal d r
powKonst inputs =
  let x = at1 inputs 0
  in sumElements0 $
       x ** (sin x + (id2 $ id2 $ id2 $ konst1 (sumElements0 x) 2))

sinKonstS
  :: forall d r. ADModeAndNum d r
  => ADValInputs d r -> ADVal d r
sinKonstS inputs =
  let x = atS inputs 0
  in sumElements0 $ fromS1
       ((sin x + (id2 $ id2 $ id2 $ konstS 1))
         :: ADVal d (OS.Array '[2] r))

dReverse1
  :: (r ~ Float, d ~ 'ADModeGradient)
  => (ADValInputs d r -> ADVal d r)
  -> [[r]]
  -> IO ([[r]], r)
dReverse1 f deltaInput = do
  ((_, !results, _, _), !v) <-
    revIO 1 f
             (V.empty, V.fromList (map V.fromList deltaInput), V.empty, V.empty)
  return (map V.toList $ V.toList results, v)

testDReverse1 :: TestTree
testDReverse1 = testGroup "Simple revIO application to vectors tests" $
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
          let output =
                prettyPrintDf f
                  (V.empty, V.fromList (map V.fromList v), V.empty, V.empty)
          length output @?= expected)
    [ ( "sumElementsV", sumElementsV, [[1 :: Float, 1, 3]]
      , 54 )
    , ( "altSumElementsV", altSumElementsV, [[1, 1, 3]]
      , 337 )
    , ( "sinKonst", sinKonst, [[1, 3]]
      , 237 )
    , ( "powKonst", powKonst, [[1, 3]]
      , 692 )
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
    , ( "atanOldReadme", atanOldReadme, ([1.1, 2.2, 3.3], [])
      , (7.662345305800865, 4.9375516951604155) )
    , ( "vatanOldReadme", vatanOldReadme, ([], [1.1, 2.2, 3.3])
      , (7.662345305800865, 4.9375516951604155) )
    ]

testDFastForward :: TestTree
testDFastForward =
 testGroup "Simple fwdFun application tests" $
  map (\(txt, f, v, expected) ->
        let vp = listsToParameters v
        in testCase txt $ fwdFun f vp vp @?~ expected)
    [ ("fquad", fquad, ([2 :: Double, 3], []), (26.0, 18.0))
    , ( "atanOldReadme", atanOldReadme, ([1.1, 2.2, 3.3], [])
      , (7.662345305800865, 4.9375516951604155) )
    , ( "vatanOldReadme", vatanOldReadme, ([], [1.1, 2.2, 3.3])
      , (7.662345305800865, 4.9375516951604155) )
    ]

-- The formula for comparing derivative and gradient is due to @awf
-- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
quickCheckForwardAndBackward :: TestTree
quickCheckForwardAndBackward =
  testGroup "Simple QuickCheck of gradient vs derivative vs perturbation"
    [ quickCheckTest0 "fquad" fquad (\(x, y, _z) -> ([x, y], [], [], []))
    , quickCheckTest0 "atanOldReadme" atanOldReadme
             (\(x, y, z) -> ([x, y, z], [], [], []))
    , quickCheckTest0 "vatanOldReadme" vatanOldReadme
             (\(x, y, z) -> ([], [x, y, z], [], []))
    , quickCheckTest0 "sinKonst" sinKonst  -- powKonst NaNs immediately
             (\(x, _, z) -> ([], [x, z], [], []))
    , quickCheckTest0 "sinKonstS" sinKonstS
             (\(x, _, z) -> ([], [], [], [x, z]))
   ]

-- A function that goes from `R^3` to `R^2`, with a representation
-- of the input and the output tuple that is convenient for interfacing
-- with the library.
atanOldReadmeOriginal :: RealFloat a => a -> a -> a -> Data.Vector.Vector a
atanOldReadmeOriginal x y z =
  let w = x * sin y
  in V.fromList [atan2 z w, z * x]

-- Here we instantiate the function to dual numbers
-- and add a glue code that selects the function inputs from
-- a uniform representation of objective function parameters
-- represented as delta-inputs (`ADValInputs`).
atanOldReadmeInputs
  :: ADModeAndNum d r
  => ADValInputs d r -> Data.Vector.Vector (ADVal d r)
atanOldReadmeInputs inputs =
  let x : y : z : _ = atList0 inputs
  in atanOldReadmeOriginal x y z

-- According to the paper, to handle functions with non-scalar results,
-- we dot-product them with dt which, for simplicity, we here set
-- to a record containing only ones. We could also apply the dot-product
-- automatically in the library code (though perhaps we should
-- emit a warning too, in case the user just forgot to apply
-- a loss function and that's the only reason the result is not a scalar?).
-- For now, let's perform the dot product in user code.

-- Here is the function for dot product with ones, which is just the sum
-- of elements of a vector.
sumElementsOfADVals
  :: ADModeAndNum d r
  => Data.Vector.Vector (ADVal d r) -> ADVal d r
sumElementsOfADVals = V.foldl' (+) 0

-- Here we apply the function.
atanOldReadme
  :: ADModeAndNum d r
  => ADValInputs d r -> ADVal d r
atanOldReadme = sumElementsOfADVals . atanOldReadmeInputs

-- The underscores and empty vectors are placeholders for the vector,
-- matrix and arbitrary tensor components of the parameters tuple,
-- which we here don't use (above we construct a vector output,
-- but it's a vector of scalar parameters, not a single parameter
-- of rank 1).
atanOldReadmeDReverse :: HasDelta r
                   => Domain0 r -> IO (Domain0 r, r)
atanOldReadmeDReverse ds = do
  ((!result, _, _, _), !v) <-
    revIO 1 atanOldReadme (ds, V.empty, V.empty, V.empty)
  return (result, v)

oldReadmeTests :: TestTree
oldReadmeTests = testGroup "Simple tests for README"
  [ testCase " Float (1.1, 2.2, 3.3)" $ do
      res <- atanOldReadmeDReverse (V.fromList [1.1 :: Float, 2.2, 3.3])
      res @?~ (V.fromList [3.0715904, 0.18288425, 1.1761366], 4.937552)
  , testCase " Double (1.1, 2.2, 3.3)" $ do
      res <- atanOldReadmeDReverse (V.fromList [1.1 :: Double, 2.2, 3.3])
      res @?~ ( V.fromList [ 3.071590389300859
                           , 0.18288422990948425
                           , 1.1761365368997136 ]
              , 4.9375516951604155 )
  ]

-- And here's a version of the example that uses vector parameters
-- (quite wasteful in this case) and transforms intermediate results
-- via a primitive differentiable type of vectors instead of inside
-- vectors of primitive differentiable scalars.

vatanOldReadme
  :: ADModeAndNum d r
  => ADValInputs d r -> ADVal d r
vatanOldReadme inputs =
  let xyzVector = at1 inputs 0
      [x, y, z] = map (index0 xyzVector) [0, 1, 2]
      v = seq1 $ atanOldReadmeOriginal x y z
  in sumElements0 v

vatanOldReadmeDReverse :: HasDelta r
                    => Domain1 r -> IO (Domain1 r, r)
vatanOldReadmeDReverse dsV = do
  ((_, !result, _, _), !v) <-
    revIO 1 vatanOldReadme (V.empty, dsV, V.empty, V.empty)
  return (result, v)

oldReadmeTestsV :: TestTree
oldReadmeTestsV = testGroup "Simple tests of vector-based code for README"
  [ testCase "V Float (1.1, 2.2, 3.3)" $ do
      res <- vatanOldReadmeDReverse (V.singleton $ V.fromList [1.1 :: Float, 2.2, 3.3])
      res @?~ ( V.singleton $ V.fromList [3.0715904, 0.18288425, 1.1761366]
              , 4.937552 )
  , testCase "V Double (1.1, 2.2, 3.3)" $ do
      res <- vatanOldReadmeDReverse (V.singleton $ V.fromList [1.1 :: Double, 2.2, 3.3])
      res @?~ ( V.singleton $ V.fromList [ 3.071590389300859
                                         , 0.18288422990948425
                                         , 1.1761365368997136 ]
              , 4.9375516951604155 )
  ]

finalCounter :: TestTree
finalCounter = testCase "Final counter value" $ do
  counter <- unsafeGetFreshId
  hPutStrLn stderr $ printf "\nFinal counter value: %d" counter
  assertBool "counter dangerously high" $ counter < 2 ^ (62 :: Int)

-- A function that goes from `R^3` to `R`.
foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

testFoo :: Assertion
testFoo =
  assertEqualUpToEps (1e-10 :: Double)
    (rev foo (1.1, 2.2, 3.3))
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)

bar :: RealFloat a => (a,a,a) -> a
bar (x,y,z) =
  let w = foo (x,y,z) * sin y
  in atan2 z w + z * w

testBar :: Assertion
testBar =
  assertEqualUpToEps (1e-9 :: Double)
    (rev bar (1.1, 2.2, 3.3))
    (6.221706565357043, -12.856908977773593, 6.043601532156671)

-- A check if gradient computation is re-entrant.
-- This test fails (not on first run, but on repetition) if old terms,
-- from before current iteration of gradient descent, are not soundly
-- handled in new computations (due to naive impurity, TH, plugins,
-- or just following the papers that assume a single isolated run).
-- This example requires monomorphic types and is contrived,
-- but GHC does optimize and factor out some accidentally constant
-- subterms in real examples (presumably after it monomorphizes them)
-- causing exactly the same danger.
-- This example also tests unused parameters (x), another common cause
-- of crashes in naive gradient computing code.
baz :: ( ADVal 'ADModeGradient Double
       , ADVal 'ADModeGradient Double
       , ADVal 'ADModeGradient Double )
    -> ADVal 'ADModeGradient Double
baz (_x,y,z) =
  let w = fooConstant * bar (y,y,z) * sin y
  in atan2 z w + z * w

-- An "old term", computed once, stored at top level.
fooConstant :: ADVal 'ADModeGradient Double
fooConstant = foo (7, 8, 9)

testBaz :: Assertion
testBaz =
  assertEqualUpToEps (1e-9 :: Double)
    (rev baz (1.1, 2.2, 3.3))
    (0, -5219.20995030263, 2782.276274462047)

-- If terms are numbered and @z@ is, wrongly, decorated with number 0,
-- here @fooConstant@ is likely to clash with @z@, since it was numbered
-- starting from 0, too.
-- The test fails if term numbering is reset to 0 between gradient computation
-- runs (verified) as well as when delta-expression evaluation assumes
-- it can only encounter terms numbered in the current run and,
-- e.g., allocates an array with only that much space (not verified).
-- Actually, with term counter zeroed just before @rev@ application,
-- even a single @testBaz@ execution produces wrong results, but this test
-- is likely to fail in less naive implementations, as well.
testBazRenumbered :: Assertion
testBazRenumbered =
  assertEqualUpToEps (1e-9 :: Double)
    (rev (\(x,y,z) -> z + baz (x,y,z)) (1.1, 2.2, 3.3))
    (0, -5219.20995030263, 2783.276274462047)

-- A dual-number and list-based version of a function that goes
-- from `R^3` to `R`.
fooD :: ADModeAndNum d r => [ADVal d r] -> ADVal d r
fooD [x, y, z] =
  let w = x * sin y
  in atan2 z w + z * w
fooD _ = error "wrong number of arguments"

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsD (1e-10 :: Double)
    (rev fooD [1.1, 2.2, 3.3])
    [2.4396285219055063, -1.953374825727421, 0.9654825811012627]

rev :: (HasDelta r, Adaptable r x rs)
     => (x -> ADVal 'ADModeGradient r) -> x -> rs
rev f x =
  let g inputs = f $ fromADValInputs inputs
  in fromDomains $ fst $ revFun 1 g (toDomains x)

-- Inspired by adaptors from @tomjaguarpaw's branch.
class Adaptable r fdr rs | fdr -> rs, rs -> fdr where
  toDomains :: fdr -> Domains r
  fromADValInputs :: ADValInputs 'ADModeGradient r -> fdr
  fromDomains :: Domains r -> rs

instance ADModeAndNum 'ADModeGradient r
         => Adaptable r ( ADVal 'ADModeGradient r
                        , ADVal 'ADModeGradient r
                        , ADVal 'ADModeGradient r ) (r, r, r) where
  toDomains (D a _, D b _, D c _) =
    (V.fromList [a, b, c], V.empty, V.empty, V.empty)
  fromADValInputs inputs = case atList0 inputs of
    r1 : r2 : r3 : _ -> (r1, r2, r3)
    _ -> error "fromADValInputs in Adaptable r (r, r, r)"
  fromDomains (v, _, _, _) = case V.toList v of
    r1 : r2 : r3 : _ -> (r1, r2, r3)
    _ -> error "fromADValInputs in Adaptable r (r, r, r)"

-- TODO
instance ADModeAndNum 'ADModeGradient r
         => Adaptable r [ADVal 'ADModeGradient r] [r] where
  toDomains [D a _, D b _, D c _] =
    (V.fromList [a, b, c], V.empty, V.empty, V.empty)
  fromADValInputs inputs = case atList0 inputs of
    r1 : r2 : r3 : _ -> [r1, r2, r3]
    _ -> error "fromADValInputs in Adaptable r [r]"
  fromDomains (v, _, _, _) = case V.toList v of
    r1 : r2 : r3 : _ -> [r1, r2, r3]
    _ -> error "fromADValInputs in Adaptable r [r]"

instance (ADModeAndNum 'ADModeGradient r, OS.Shape sh1, OS.Shape sh2, OS.Shape sh3)
         => Adaptable r ( ADVal 'ADModeGradient (OS.Array sh1 r)
                        , ADVal 'ADModeGradient (OS.Array sh2 r)
                        , ADVal 'ADModeGradient (OS.Array sh3 r) )
                        (OS.Array sh1 r, OS.Array sh2 r, OS.Array sh3 r) where
  toDomains (D a _, D b _, D c _) =
    ( V.empty, V.empty, V.empty
    , V.fromList [ Data.Array.Convert.convert a
                 , Data.Array.Convert.convert b
                 , Data.Array.Convert.convert c ] )
  fromADValInputs inputs =
    let a = atS inputs 0
        b = atS inputs 1
        c = atS inputs 2
    in (a, b, c)
  fromDomains (_, _, _, v) = case V.toList v of
    a : b : c : _ -> ( Data.Array.Convert.convert a
                     , Data.Array.Convert.convert b
                     , Data.Array.Convert.convert c )
    _ -> error "fromADValInputs in Adaptable r (S, S, S)"

assertEqualUpToEps :: Double -> (Double, Double, Double) -> (Double, Double, Double) -> Assertion
assertEqualUpToEps _eps (r1, r2, r3) (u1, u2, u3) =  -- TODO: use the _eps instead of the default one
  r1 @?~ u1 >> r2 @?~ u2 >> r3 @?~ u3

assertEqualUpToEpsD :: Double -> [Double] -> [Double] -> Assertion
assertEqualUpToEpsD _eps l1 l2 =  -- TODO
  l1 @?~ l2

readmeTests0 :: TestTree
readmeTests0 = testGroup "Simple tests of tuple-based code for README"
  [ testCase "foo T Double (1.1, 2.2, 3.3)" $
      testFoo
  , testCase "bar T Double (1.1, 2.2, 3.3)" $
      testBar
  , testCase "baz old to force fooConstant" $
      testBaz
  , testCase "baz new to check if mere repetition breaks things" $
      testBaz
  , testCase "baz again to use fooConstant with renumbered terms" $
      testBazRenumbered
   , testCase "fooD T Double [1.1, 2.2, 3.3]" $
      testFooD
  ]

-- A dual-number version of a function that goes from three rank one
-- (vector-like) tensors to `R`. It multiplies first elements
-- of the first tensor by the second of the second and by the third
-- of the third.
-- Solving type-level inequalities is too hard, so we use the type-level plus
-- to express the bounds on tensor sizes.
fooS :: (ADModeAndNum d r, len1 ~ (l1 + 1), len2 ~ (l2 + 2), len3 ~ (l3 + 3))
     => StaticNat len1 -> StaticNat len2 -> StaticNat len3
     -> ( ADVal d (OS.Array '[len1] r)
        , ADVal d (OS.Array '[len2] r)
        , ADVal d (OS.Array '[len3] r) ) -> ADVal d r
fooS MkSN MkSN MkSN (x1, x2, x3) =
  fromS0 $ indexS @0 x1 * indexS @1 x2 * indexS @2 x3

testFooS :: Assertion
testFooS =
  assertEqualUpToEpsS (1e-10 :: Double)
    (rev (fooS (MkSN @1) (MkSN @5) (MkSN @3))
          ( ravelFromListS $ map from0S [1.1]
          , ravelFromListS $ map from0S [2.2, 2.3, 7.2, 7.3, 7.4]
          , ravelFromListS $ map from0S [3.3, 3.4, 3.5]) )
    ( OS.fromList [8.049999999999999]
    , OS.fromList [0, 3.8500000000000005, 0, 0, 0]
    , OS.fromList [0, 0, 2.53] )

-- A hack: the normal assertEqualUpToEps should work here. And AssertClose should work for shaped and untyped tensors.
assertEqualUpToEpsS :: (OS.Shape sh1, OS.Shape sh2, OS.Shape sh3) => Double -> (OS.Array sh1 Double, OS.Array sh2 Double, OS.Array sh3 Double) -> (OS.Array sh1 Double, OS.Array sh2 Double, OS.Array sh3 Double) -> Assertion
assertEqualUpToEpsS _eps (r1, r2, r3) (u1, u2, u3) =  -- TODO: use the _eps instead of the default one
  OS.toList r1 @?~ OS.toList u1 >> OS.toList r2 @?~ OS.toList u2 >> OS.toList r3 @?~ OS.toList u3
