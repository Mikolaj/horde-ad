{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
module TestSimplified (testTrees) where

import Prelude

import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as LA
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import Tool.EqEpsilon

import Prelude ()

testTrees :: [TestTree]
testTrees = [ testCase "fooBuild1" testFooBuild
            , testCase "fooMap1" testFooMap
            , testCase "fooNoGo" testFooNoGo
            , testCase "nestedBuildMap" testNestedBuildMap ]

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

bar :: ADModeAndNumNew d r
    => (ADVal d r, ADVal d r) -> ADVal d r
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

-- Note how fooBuild1 is used below in contexts where r
-- is values (testFooBuild), where r is ASTs (nestedBuildMap)
-- and where it can be instantiated to either (fooMap1).
fooBuild1 :: forall d r. ADModeAndNumNew d r
          => ADVal d (VectorOf r) -> ADVal d (VectorOf r)
fooBuild1 v =
  let v' = (liftToAst v  -- we don't know if @r@ is values or ASTs, so we lift
            :: ADVal d (Ast1 d (Under r)))
           :: ADVal d (VectorOf (Ast0 d (Under r)))
      r' = sumElements10 v' :: ADVal d (Ast0 d (Under r))
  in buildAst1 3 $ \ix ->
       r' * foo ( 3
                , 5 * r'
                , r' * minimum0 v' * liftToAst (minimum0 v))
       + bar (r', index10 v' (ix + 1))
       -- note how foo and bar are used in the Ast universe without lifting
       -- their result, just as sumElements10 and index10 is

fooMap1 :: ADModeAndNumNew d r
        => ADVal d r -> ADVal d (VectorOf r)
fooMap1 r =
  let v = fooBuild1 $ konst1 r 130
      r' = liftToAst r
  in mapAst1 (\x -> x * r' + 5) v

-- A test that doesn't vectorize currently due to conditionals
-- and so falls back to POPL.
fooNoGo :: forall r d. ADModeAndNumNew d r
        => ADVal d (VectorOf r) -> ADVal d (VectorOf r)
fooNoGo v =
  let v' = liftToAst v :: ADVal d (Ast1 d (Under r))
      r' = sumElements10 v' :: ADVal d (Ast0 d (Under r))
  in buildAst1 3 (\ix ->
       index10 v' ix
       + condAst (AstBoolOp AndOut  -- TODO: overload &&, <=, >, etc.
                            [ index10 v' (ix * 2) `leqAst` 0
                            , 6 `gtIntAst` abs ix ])
                 r' (5 * r'))
     / slice1 1 3 (mapAst1 (\x -> condAst (x `gtAst` r')
                                          r' x) v)
     * buildAst1 3 (\ _ix -> 1)

nestedBuildMap :: forall r d. ADModeAndNumNew d r
               => ADVal d r -> ADVal d (VectorOf r)
nestedBuildMap r =
  let w x = konst1 x (AstIntCond (x `leqAst` 0) 3 4)
      v' = konst1 (liftToAst r) 7
      nestedMap x = mapAst1 (\y -> x / y) (w x)
      variableLengthBuild iy = buildAst1 (iy + 1) (\ix -> index10 v' (ix + 1))
      doublyBuild = buildAst1 5 (\iy -> minimum0 (variableLengthBuild iy))
  in mapAst1 (\x -> x
                    * sumElements10
                        (buildAst1 3 (\ix -> bar ( x
                                                 , index10 v' ix) )
                         + fooBuild1 (nestedMap x)
                         / fooMap1 x)
             ) doublyBuild

-- In simplified horde-ad we don't have access to the highest level API
-- (adaptors), so the testing glue is tedious:
testFooBuild :: Assertion
testFooBuild =
  (domains1 $ fst
   $ revOnDomains
       (LA.konst 1 3)  -- 1 wrong due to fragility of hmatrix optimization
       (\adinputs -> fooBuild1 (adinputs `at1` 0))
       (domainsFrom01 V.empty
                      (V.singleton (V.fromList [1.1 :: Double, 2.2, 3.3, 4]))))
  @?~ V.singleton (V.fromList [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])

testFooMap :: Assertion
testFooMap =
  (domains0 $ fst
   $ revOnDomains
       (LA.konst 1 3)  -- 1 wrong due to fragility of hmatrix optimization
       (\adinputs -> fooMap1 (adinputs `at0` 0))
       (domainsFrom01 (V.singleton (1.1 :: Double)) V.empty))
  @?~ V.fromList [4.438131773948992e7]

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

testNestedBuildMap :: Assertion
testNestedBuildMap =
  (domains0 $ fst
   $ revOnDomains
       (LA.konst 1 5)  -- "1" wrong due to fragility of hmatrix optimization
       (\adinputs -> nestedBuildMap (adinputs `at0` 0))
       (domainsFrom01 (V.singleton (1.1 :: Double)) V.empty))
  @?~ V.fromList [107.25984443006627]
