{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestGradient (testTrees) where

import Prelude

import qualified Data.Array.ShapedS as OS
import           GHC.TypeLits (KnownNat, type (+))
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd hiding (sumElementsVectorOfDual)
import HordeAd.Core.DualClass (Dual)

import Tool.EqEpsilon
import Tool.Shared

testTrees :: [TestTree]
testTrees = [ quickCheckForwardAndBackward
            , readmeTests0
            , readmeTestsS
            ]

-- hlint would complain about spurious @id@, so we need to define our own.
id2 :: a -> a
id2 x = x

sinKonstS
  :: forall d r. ADModeAndNum d r
  => ADInputs d r -> ADVal d r
sinKonstS inputs =
  let x = atS inputs 0
  in sumElements0 $ fromS1
       ((sin x + (id2 $ id2 $ id2 $ konstS 1))
         :: ADVal d (OS.Array '[2] r))

-- The formula for comparing derivative and gradient is due to @awf
-- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
quickCheckForwardAndBackward :: TestTree
quickCheckForwardAndBackward =
  testGroup "Simple QuickCheck of gradient vs derivative vs perturbation"
    [ quickCheckTest0 "sinKonstS" sinKonstS
             (\(x, _, z) -> ([], [], [], [x, z]))
   ]

-- * Newer README tests

readmeTests0 :: TestTree
readmeTests0 = testGroup "Simple tests of tuple-based code for README"
  [ testCase "foo T Double (1.1, 2.2, 3.3)" testFoo
  , testCase "bar T Double (1.1, 2.2, 3.3)" testBar
  , testCase "baz old to force fooConstant" testBaz
  , testCase "baz new to check if mere repetition breaks things" testBaz
  , testCase "baz again to use fooConstant with renumbered terms" testBazRenumbered
  , testCase "fooD T Double [1.1, 2.2, 3.3]" testFooD
  ]

readmeTestsS :: TestTree
readmeTestsS = testGroup "Simple tests of shaped tensor-based code for README"
  [ testCase "S" testFooS
  , testCase "V" testBarV
  , testCase "F" testBarF
  , testCase "R" testBarR
  ]

-- A function that goes from `R^3` to `R`.
foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

testFoo :: Assertion
testFoo =
  assertEqualUpToEpsilon 1e-10
    (rev @Double foo (1.1, 2.2, 3.3))
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)

bar :: RealFloat a => (a,a,a) -> a
bar (x,y,z) =
  let w = foo (x,y,z) * sin y
  in atan2 z w + z * w

testBar :: Assertion
testBar =
  assertEqualUpToEpsilon 1e-9
    (rev (bar @(ADVal 'ADModeGradient Double)) (1.1, 2.2, 3.3))
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
  assertEqualUpToEpsilon 1e-9
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
  assertEqualUpToEpsilon 1e-9
    (rev (\(x,y,z) -> z + baz (x,y,z)) (1.1, 2.2, 3.3))
    (0, -5219.20995030263, 2783.276274462047)

-- A dual-number and list-based version of a function that goes
-- from `R^3` to `R`.
fooD :: forall r d. ADModeAndNum d r => [ADVal d r] -> ADVal d r
fooD [x, y, z] =
  let w = x * sin y
  in atan2 z w + z * w
fooD _ = error "wrong number of arguments"

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsilon 1e-10
    (rev fooD [1.1 :: Double, 2.2, 3.3])
    [2.4396285219055063, -1.953374825727421, 0.9654825811012627]

-- A dual-number version of a function that goes from three rank one
-- (vector-like) tensors to `R`. It multiplies first elements
-- of the first tensor by the second of the second and by the third
-- of the third.
-- Solving type-level inequalities is too hard, so we use the type-level plus
-- to express the bounds on tensor sizes.
fooS :: forall r len1 l1 len2 l2 len3 l3 len4 l4 d.
        ( ADModeAndNum d r
        , len1 ~ (l1 + 1), len2 ~ (l2 + 2), len3 ~ (l3 + 3), len4 ~ (l4 + 4) )
     => StaticNat len1 -> StaticNat len2 -> StaticNat len3 -> StaticNat len4
     -> ( ADVal d (OS.Array '[len1] r)
        , ADVal d (OS.Array '[len2] r)
        , ADVal d (OS.Array '[len3] r)
        , ADVal d (OS.Array '[len4] r) ) -> ADVal d r
fooS MkSN MkSN MkSN MkSN (x1, x2, x3, x4) =
  fromS0 $ indexS @0 x1 * indexS @1 x2 * indexS @2 x3 * indexS @3 x4

testFooS :: Assertion
testFooS =
  assertEqualUpToEpsilon 1e-12
    (rev (fooS (MkSN @1) (MkSN @5) (MkSN @3) (MkSN @4))
          ( OS.fromList [1.1 :: Double]
          , OS.fromList [2.2, 2.3, 7.2, 7.3, 7.4]
          , OS.fromList [3.3, 3.4, 3.5]
          , OS.fromList [4.4, 4.5, 4.6, 4.7]) )
    ( OS.fromList [37.834999999999994]
    , OS.fromList [0, 18.095000000000002, 0, 0, 0]
    , OS.fromList [0, 0, 11.891]
    , OS.fromList [0, 0, 0, 8.854999999999999] )

barS :: (ADModeAndNum d r, OS.Shape sh)
     => StaticNat n1 -> StaticNat n2
     -> ( ADVal d r
        , ADVal d (OS.Array '[n1, n2] r)
        , [ADVal d (OS.Array (n2 ': sh) r)] )
     -> [ADVal d (OS.Array (n1 ': sh) r)]
barS MkSN MkSN (s, w, xs) =
  map (\x -> konstS s * dot w x) xs
    -- konstS is needed, after all, because @s@ is a differentiable quantity
    -- with a given type, and not a constant that would be interpreted according
    -- to the inferred type

-- TODO: this is a fake implementation and of the medium-general variant
dot :: (ADModeAndNum d r, OS.Shape sh, KnownNat n1)
    => ADVal d (OS.Array '[n1, n2] r)
    -> ADVal d (OS.Array (n2 ': sh) r)
    -> ADVal d (OS.Array (n1 ': sh) r)
dot _ _ = konstS 42

bar_3_75
  :: forall r k sh d.
     ( d ~ 'ADModeValue, AdaptableScalar d r
     , KnownNat k, OS.Shape sh)
  => ( r
     , OS.Array '[3, 75] r
     , [OS.Array (75 ': sh) r] )
  -> OS.Array (k ': 3 ': sh) r
bar_3_75 = value (ravelFromListS . barS (MkSN @3) (MkSN @75))
  -- @ravelFromListS@ is needed, because @valueFun@ expects the objective
  -- function to have a dual number codomain and here we'd have a list
  -- of dual numbers. The same problem is worked around with @head@ below.

testBarV :: Assertion
testBarV =
  assertEqualUpToEpsilon 1e-12
    (bar_3_75 @Double @2 @'[3, 337]
       ( 1.1
       , OS.constant 17.3  -- TODO: create more interesting test data
       , [ OS.constant 2.4
         , OS.constant 3.6 ] ))
    (OS.constant 46.2)

bar_jvp_3_75
  :: forall r sh d.
     ( d ~ 'ADModeDerivative, Dual d r ~ r, AdaptableScalar d r
     , OS.Shape sh )
  => ( r
     , OS.Array '[3, 75] r
     , [OS.Array (75 ': sh) r] )
  -> ( r
     , OS.Array '[3, 75] r
     , [OS.Array (75 ': sh) r] )
  -> OS.Array (3 ': sh) r
bar_jvp_3_75 = fwd (head . barS (MkSN @3) (MkSN @75))
  -- TODO: implement real jvp (forward) and vjp (back)
  -- TODO: @head@ is required, because our engine so far assumes
  -- objective functions have dual number codomains (though they may be
  -- of arbitrary rank). The same problem is worked around with
  -- @ravelFromListS@ below.

testBarF :: Assertion
testBarF =
  assertEqualUpToEpsilon 1e-7
    (bar_jvp_3_75 @Double @'[12, 2, 5, 2]
       ( 1.1
       , OS.constant 17.3  -- TODO: create more interesting test data
       , [ OS.constant 2.4
         , OS.constant 3.6 ] )  -- input
       ( 2.1
       , OS.constant 18.3
       , [ OS.constant 3.4
         , OS.constant 4.6 ] ))  -- ds
    (OS.constant 88.2)

bar_rev_3_75
  :: forall r sh d.
     ( d ~ 'ADModeGradient, HasDelta r, AdaptableScalar d r
     , OS.Shape sh)
  => ( r
     , OS.Array '[3, 75] r
     , [OS.Array (75 ': sh) r] )
  -> ( r
     , OS.Array '[3, 75] r
     , [OS.Array (75 ': sh) r] )
bar_rev_3_75 = rev ((head :: [ADVal d (OS.Array (n1 ': sh) r)]
                          -> ADVal d (OS.Array (n1 ': sh) r))
                    . barS (MkSN @3) (MkSN @75))
  -- TODO: @head@ is required, because our engine so far assumes
  -- objective functions with dual number codomains (though they may be
  -- of arbitrary ranks)

testBarR :: Assertion
testBarR =
  assertEqualUpToEpsilon 1e-7
    (bar_rev_3_75 @Double @'[2, 3, 341, 1, 5]
       ( 1.1
       , OS.constant 17.3  -- TODO: create more interesting test data
       , [ OS.constant 2.4
         , OS.constant 3.6 ] ))  -- input
    ( 1288980.0
    , OS.constant 0
    , [ OS.constant 0
      , OS.constant 0 ] )
