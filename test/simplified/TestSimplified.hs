{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
module TestSimplified (testTrees) where

import Prelude

import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd hiding (sumElementsVectorOfDual)

import Tool.EqEpsilon

import Prelude ()

testTrees :: [TestTree]
testTrees = [ testCase "B" testFooBuild
            , testCase "M" testFooMap ]

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
  let -- Without @VectorLike@ and support for @Ast d (Vector r)@:
      -- r' = liftToAst (sumElements0 v) :: ADVal d (Ast d r)
      -- now:
      v' = liftToAst v :: ADVal d (Ast d (Vector r))
      r' = sumElements0 v' :: ADVal d (Ast d r)
      astOfIndex = indexAst10 v' (AstIntVar "ix" + 1)
  in buildAst1 2 ("ix", r' * foo (3, r', r' * astOfIndex) + bar (r', 3))
       -- note how foo and bar are used in the Ast universe without lifting
       -- their result, just as sumElements0 is

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
