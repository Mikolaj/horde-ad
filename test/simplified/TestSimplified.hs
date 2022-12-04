{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
module TestSimplified (testTrees) where

import Prelude

import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as LA
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import Tool.EqEpsilon

import Prelude ()

testTrees :: [TestTree]
testTrees = [ testCase "B" testFooBuild
            , testCase "M" testFooMap
            , testCase "HHH Warm-up" testSingleMapHMatrix
            , testCase "HHH SingleMapHMatrix" testSingleMapHMatrix
            , testCase "HHH BulkHMatrix" testBulkHMatrix
            , testCase "HHH SingleMapVector" testSingleMapVector
            , testCase "HHH BulkVector25" testBulkVector25 ]

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

-- TODO: probably dummy instances suffice to extend to full ADModeAndNum d r
bar :: (RealFloat r, IsPrimal d r)
    => (ADVal d r, ADVal d r) -> ADVal d r
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooBuild1 :: forall r d. ADModeAndNum d r
          => ADVal d (Vector r) -> ADVal d (Vector r)
fooBuild1 v =
  let v' = liftToAst v :: ADVal d (Ast d (Vector r))
      r' = sumElements10 v' :: ADVal d (Ast d r)
  in buildAst1 2 ("ix", r' * foo (3, 5 * r', r' * liftToAst (minimum0 v))
                        + bar (r', index10 v' (AstVar "ix" + 1)))
       -- note how foo and bar are used in the Ast universe without lifting
       -- their result, just as sumElements10 and index10 is

fooMap1 :: ADModeAndNum d r
        => ADVal d r -> ADVal d (Vector r)
fooMap1 r =
  let v = fooBuild1 $ konst1 r 130
      r' = liftToAst r
  in mapAst1 ("x", varAst "x" * r' + 5) v

-- In simplified horde-ad we don't have access to the highest level API
-- (adaptors), so the testing glue is tedious:
testFooBuild :: Assertion
testFooBuild =
  (domains1 $ fst
   $ revOnDomains
       1
       (\adinputs -> fooBuild1 (adinputs `at1` 0))
       (domainsFrom01 V.empty (V.singleton (V.fromList [1.1 :: Double, 2.2]))))
  @?~ V.fromList [2.4396285219055063, 9]

testFooMap :: Assertion
testFooMap =
  (domains1 $ fst
   $ revOnDomains 1 (\adinputs -> fooMap1 (adinputs `at0` 0))
                    (domainsFrom01 (V.singleton (1.1 :: Double)) V.empty))
  @?~ V.fromList [2.4396285219055063, 9]

len :: Int
len = 100000000  -- 100M

testBulkHMatrix :: Assertion
testBulkHMatrix = do
  let !x = VS.replicate len (0.9999999999 :: Double)
  let !res = x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x  -- 50 ops
  res @?= res

testSingleMapHMatrix :: Assertion
testSingleMapHMatrix = do
  let !v = VS.replicate len (0.9999999999 :: Double)
  let !res = LA.cmap (\ !x -> x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x) v
  res @?= res

testSingleMapVector :: Assertion
testSingleMapVector = do
  let !v = VS.replicate len (0.9999999999 :: Double)
  let !res = VS.map (\ !x -> x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x ** x) v
  res @?= res

testBulkVector25 :: Assertion
testBulkVector25 = do
  let !v = VS.replicate len (0.9999999999 :: Double)
  let !res = VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v $ VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v (VS.zipWith (**) v v)))))))))))))))))))))  -- only ~25 ops
  res @?= res
