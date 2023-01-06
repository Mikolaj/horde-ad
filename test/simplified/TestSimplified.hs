{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
module TestSimplified (testTrees) where

import Prelude

import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import Tool.EqEpsilon

import Prelude ()

testTrees :: [TestTree]
testTrees = [ testCase "barADVal" testBarADVal
            , testCase "fooBuild1" testFooBuild
            , testCase "fooMap1" testFooMap
            , testCase "fooNoGo" testFooNoGo
            , testCase "nestedBuildMap" testNestedBuildMap ]

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

bar :: forall a. RealFloat a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

barAst :: RealFloat r => (Ast r r, Ast r r) -> Ast r r
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

barADVal :: forall r d. ADModeAndNum d r => (ADVal d r, ADVal d r) -> ADVal d r
barADVal = bar @(ADVal d r)

fooBuild1 :: ADReady r => VectorOf r -> VectorOf r
fooBuild1 v =
  let r = lsumElements10 v
      v' = lminElement v
  in lbuild1 3 $ \ix ->
       r * foo ( 3
               , 5 * r
               , r * lminElement v * v')
       + bar (r, lindex10 v (ix + 1))

fooMap1 :: ADReady r => r -> VectorOf r
fooMap1 r =
  let v = fooBuild1 $ lkonst1 r 130
  in lmap1 (\x -> x * r + 5) v

-- A test that doesn't vectorize currently due to conditionals
-- and so falls back to POPL.
-- Also, we haven't defined a class for conditionals so far,
-- so this uses raw AST instead of sufficiently polymorphic code.
fooNoGo :: (Numeric r, RealFloat r, Num (Vector r))
        => Ast r (Vector r) -> Ast r (Vector r)
fooNoGo v =
  let r = lsumElements10 v
  in lbuild1 3 (\ix ->
       barAst (3.14, bar (3.14, lindex10 v ix))
       + AstCond (AstBoolOp AndOut  -- TODO: overload &&, <=, >, etc.
                            [ lindex10 v (ix * 2) `leqAst` 0
                            , 6 `gtIntAst` abs ix ])
                 r (5 * r))
     / lslice1 1 3 (lmap1 (\x -> AstCond (x `gtAst` r) r x) v)
     * lbuild1 3 (\ _ix -> 1)

-- TODO: remove the need for the 2 type hints; using VectorOf in the definition
-- of VectorLike class may be enough
nestedBuildMap :: forall r. ADReady r => r -> VectorOf r
nestedBuildMap r =
  let w x = lkonst1 x 4  -- (AstIntCond (x `leqAst` 0) 3 4)
      v' = lkonst1 r 7 :: VectorOf r
      nestedMap x = lmap1 (\y -> x / y) (w x)
      variableLengthBuild iy = lbuild1 (iy + 1) (\ix -> lindex10 v' (ix + 1)) :: VectorOf r
      doublyBuild = lbuild1 5 (\iy -> lminElement (variableLengthBuild iy))
  in lmap1 (\x -> x
                  * lsumElements10
                      (lbuild1 3 (\ix -> bar ( x
                                             , lindex10 v' ix) )
                       + fooBuild1 (nestedMap x)
                       / fooMap1 x)
           ) doublyBuild

-- In simplified horde-ad we don't have access to the highest level API
-- (adaptors), so the testing glue is tedious:
testBarADVal :: Assertion
testBarADVal =
  (domains0 $ fst
   $ revOnDomains
       42.2
       (\adinputs -> barADVal (adinputs `at0` 0, adinputs `at0` 1))
       (domainsFrom01 (V.fromList [1.1 :: Double, 3]) V.empty))
  @?~ V.fromList [11.49618087412679,-135.68959896367525]

-- For sufficiently polymorphic code, we test vectorization with a fallback
-- to other methods, so the test harness is even more complex.
testFooBuild :: Assertion
testFooBuild =
  (domains1 $ fst
   $ revOnDomains
       (LA.konst 1 3)  -- 1 wrong due to fragility of hmatrix optimization
       (\adinputs ->
          interpretAst (IM.singleton (-1) (AstVarR1 $ adinputs `at1` 0))
                       (fooBuild1 (AstVar1 (AstVarName (-1)))))
       (domainsFrom01 V.empty
                      (V.singleton (V.fromList [1.1 :: Double, 2.2, 3.3, 4]))))
  @?~ V.singleton (V.fromList [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])

testFooMap :: Assertion
testFooMap =
  (domains0 $ fst
   $ revOnDomains
       (LA.konst 1 3)  -- 1 wrong due to fragility of hmatrix optimization
       (\adinputs ->
          interpretAst (IM.singleton (-1) (AstVarR0 $ adinputs `at0` 0))
                       (fooMap1 (AstVar0 (AstVarName (-1)))))
       (domainsFrom01 (V.singleton (1.1 :: Double)) V.empty))
  @?~ V.fromList [4.438131773948809e7]

testFooNoGo :: Assertion
testFooNoGo =
  (domains1 $ fst
   $ revOnDomains
       (LA.konst 1 3)  -- 1 wrong due to fragility of hmatrix optimization
       (\adinputs ->
          interpretAst (IM.singleton (-1) (AstVarR1 $ adinputs `at1` 0))
                       (fooNoGo (AstVar1 (AstVarName (-1)))))
       (domainsFrom01 V.empty
                      (V.singleton (V.fromList
                                      [1.1 :: Double, 2.2, 3.3, 4, 5]))))
  @?~ V.singleton (V.fromList [344.3405885672822,-396.1811403813819,7.735358041386672,-0.8403418295960372,5.037878787878787])

testNestedBuildMap :: Assertion
testNestedBuildMap =
  (domains0 $ fst
   $ revOnDomains
       (LA.konst 1 5)  -- "1" wrong due to fragility of hmatrix optimization
       (\adinputs ->
          interpretAst (IM.singleton (-1) (AstVarR0 $ adinputs `at0` 0))
                       (nestedBuildMap (AstVar0 (AstVarName (-1)))))
       (domainsFrom01 (V.singleton (1.1 :: Double)) V.empty))
  @?~ V.fromList [107.25984443006627]
