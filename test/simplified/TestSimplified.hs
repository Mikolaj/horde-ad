{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
module TestSimplified (testTrees) where

import Prelude

import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as LA
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import Tool.EqEpsilon

import Prelude ()

testTrees :: [TestTree]
testTrees = [ testCase "fooBuild1" testFooBuild
            , testCase "fooMap1" testFooMap
            , testCase "fooNoGo" testFooNoGo ]

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

bar :: ADModeAndNumNew d r
    => (ADVal d r, ADVal d r) -> ADVal d r
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooBuild1 :: forall r d. ADModeAndNum d r
          => ADVal d (Vector r) -> ADVal d (Vector r)
fooBuild1 v =
  let v' = liftToAst v :: ADVal d (Ast r d (Vector r))
      r' = sumElements10 v' :: ADVal d (Ast r d r)
  in buildAst1 2 ("ix", r' * foo (3, 5 * r', r' * liftToAst (minimum0 v))
                        + bar (r', index10 v' (AstIntVar "ix" + 1)))
       -- note how foo and bar are used in the Ast universe without lifting
       -- their result, just as sumElements10 and index10 is

fooMap1 :: ADModeAndNum d r
        => ADVal d r -> ADVal d (Vector r)
fooMap1 r =
  let v = fooBuild1 $ konst1 r 130
      r' = liftToAst r
  in mapAst1 ("x", varAst0 "x" * r' + 5) v

-- A test that doesn't vectorize currently due to conditionals
-- and so falls back to POPL.
fooNoGo :: forall r d. ADModeAndNum d r
        => ADVal d (Vector r) -> ADVal d (Vector r)
fooNoGo v =
  let v' = liftToAst v :: ADVal d (Ast r d (Vector r))
      r' = sumElements10 v' :: ADVal d (Ast r d r)
  in buildAst1 3 ("ix",
       index10 v' (AstIntVar "ix")
       + condAst (AstBoolOp AndOut  -- TODO: overload &&, <=, >, etc.
                            [ index10 v' (AstIntVar "ix" * 2) `leqAst` 0
                            , 6 `gtIntAst` abs (AstIntVar "ix") ])
                 r' (5 * r'))
     / slice1 1 3 (mapAst1 ("x", condAst (varAst0 "x" `gtAst` r')
                                         r' (varAst0 "x")) v)
     * buildAst1 3 ("ix", 1)

-- In simplified horde-ad we don't have access to the highest level API
-- (adaptors), so the testing glue is tedious:
testFooBuild :: Assertion
testFooBuild =
  (domains1 $ fst
   $ revOnDomains
       (LA.konst 1 2)  -- 1 wrong due to fragility of hmatrix optimization
       (\adinputs -> fooBuild1 (adinputs `at1` 0))
       (domainsFrom01 V.empty
                      (V.singleton (V.fromList [1.1 :: Double, 2.2, 3.3, 4]))))
  @?~ V.singleton (V.fromList [-3020.5084001833748,-3450.748658164765,-3180.4186403350423,-3289.368401082208])

testFooMap :: Assertion
testFooMap =
  (domains0 $ fst
   $ revOnDomains
       (LA.konst 1 2)  -- 1 wrong due to fragility of hmatrix optimization
       (\adinputs -> fooMap1 (adinputs `at0` 0))
       (domainsFrom01 (V.singleton (1.1 :: Double)) V.empty))
  @?~ V.fromList [2.70437106657724e7]

testFooNoGo :: Assertion
testFooNoGo =
  (domains1 $ fst
   $ revOnDomains
       (LA.konst 1 3)  -- 1 wrong due to fragility of hmatrix optimization
       (\adinputs -> fooNoGo (adinputs `at1` 0))
       (domainsFrom01 V.empty
                      (V.singleton (V.fromList
                                      [1.1 :: Double, 2.2, 3.3, 4, 5]))))
  @?~ V.singleton (V.fromList [5.492424242424241,-11.002066115702474,-2.0766758494031228,-4.33712121212122e-2,5.037878787878787])
