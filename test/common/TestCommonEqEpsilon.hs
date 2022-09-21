{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             UndecidableInstances #-}
module TestCommonEqEpsilon (EqEpsilon, setEpsilonEq,
                            assertEqualUpToEpsilon,
                            assertCloseElem, (@?~)) where

import Data.Typeable
import Prelude

import qualified Data.Array.ShapedS as OS
import           Data.IORef
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Storable as VS
import           System.IO.Unsafe
import           Test.Tasty.HUnit
import           Test.Tasty.Options

newtype EqEpsilon = EqEpsilon Rational
  deriving (Typeable, Num, Fractional)

instance IsOption EqEpsilon where
  defaultValue = EqEpsilon eqEpsilonDefault
  parseValue s = fmap (EqEpsilon . toRational) ((safeRead :: String -> Maybe Double) s)
  optionName = return "eq-epsilon"
  optionHelp = return $ "Epsilon to use for floating point comparisons: abs(a-b) < epsilon . Default: " ++ show eqEpsilonDefault

-- Default value for eqEpsilonRef
eqEpsilonDefault :: Rational
eqEpsilonDefault = 1e-6

-- Ugly global epsilon used to compare floating point values.
eqEpsilonRef :: IORef Rational
{-# NOINLINE eqEpsilonRef #-}
eqEpsilonRef = unsafePerformIO $ newIORef eqEpsilonDefault

-- Ugly global epsilon setter (to be called once).
setEpsilonEq :: EqEpsilon -> IO ()
setEpsilonEq (EqEpsilon x) = atomicWriteIORef eqEpsilonRef x

----------------------------------------------------------------------------
-- Helper functions
----------------------------------------------------------------------------

go_assert_list :: (a -> a -> Assertion) -- ^ The function used to make an assertion on two elements (expected, actual)
               -> [a]                   -- ^ The expected value
               -> [a]                   -- ^ The actual value
               -> Assertion
go_assert_list _ [] [] = assertBool "" True
go_assert_list _ [] (_:_) = assertFailure "More list elements than expected!"
go_assert_list _ (_:_) [] = assertFailure "Less list elements than expected!"
go_assert_list mk (head_exp:tail_exp) (head_act:tail_act) =
      mk head_exp head_act >> go_assert_list mk tail_exp tail_act

assert_list :: (a -> a -> Assertion) -- ^ The function used to make an assertion on two elements (expected, actual)
            -> [a]                   -- ^ The expected value
            -> [a]                   -- ^ The actual value
            -> Assertion
assert_list make_assert expected actual =
  if lenE == lenA then
    go_assert_list make_assert expected actual
  else
    assertFailure $ "List too " ++ (if lenE < lenA then "long" else "short") ++ ": expected " ++ show lenE ++ "elements, but got: " ++ show lenA
  where
    lenE :: Int = length expected
    lenA :: Int = length actual

assert_shape :: (VS.Storable a, OS.Shape sh)
             => (a -> a -> Assertion) -- ^ The function used to make an assertion on two elements (expected, actual)
             -> OS.Array sh a         -- ^ The expected value
             -> OS.Array sh a         -- ^ The actual value
             -> Assertion
assert_shape make_assert expected actual =
  if shapeE == shapeA then
    assert_list make_assert (OS.toList expected) (OS.toList actual)
  else
    assertFailure $ "Expected shape: " ++ show shapeE ++ ", but got: " ++ show shapeA
  where
    shapeE = OS.shapeL expected
    shapeA = OS.shapeL actual

-- | Foldable to list.
asList :: Foldable t => t a -> [a]
asList = foldr (:) []

----------------------------------------------------------------------------
-- Generic comparisons with explicit error margin
----------------------------------------------------------------------------

-- | Asserts that the specified actual floating point value is close to the expected value.
-- The output message will contain the prefix, the expected value, and the
-- actual value.
--
-- If the prefix is the empty string (i.e., @\"\"@), then the prefix is omitted
-- and only the expected and actual values are output.
assertEqualUpToEps :: (Fractional a, Ord a, Show a, HasCallStack)
                   => String -- ^ The message prefix
                   -> a      -- ^ The error margin
                   -> a      -- ^ The expected value
                   -> a      -- ^ The actual value
                   -> Assertion
assertEqualUpToEps preface eqEpsilon expected actual = do
  assertBool (msg eqEpsilon) (abs (expected-actual) < eqEpsilon)
  where msg errorMargin = (if null preface then "" else preface ++ "\n") ++
                           "expected: " ++ show expected ++ "\n but got: " ++ show actual ++
                           "\n (maximum margin of error: " ++ show errorMargin ++ ")"

----------------------------------------------------------------------------
-- AssertEqualUpToEpsilon class
----------------------------------------------------------------------------

class (Fractional z, Ord z, Show z) => AssertEqualUpToEpsilon z a where
  assertEqualUpToEpsilon :: z -- ^ The error margin (i.e., the epsilon)
                         -> a -- ^ The expected value
                         -> a -- ^ The actual value
                         -> Assertion

instance {-# OVERLAPPABLE #-} (Fractional a, Ord a, Show a) => AssertEqualUpToEpsilon a a where
  assertEqualUpToEpsilon :: a -> a -> a -> Assertion
  assertEqualUpToEpsilon = assertEqualUpToEps ""

instance {-# OVERLAPPABLE #-} (AssertEqualUpToEpsilon z a,
                               AssertEqualUpToEpsilon z b) => AssertEqualUpToEpsilon z (a,b) where
  assertEqualUpToEpsilon :: z -> (a,b) -> (a,b) -> Assertion
  assertEqualUpToEpsilon eqEpsilon (e1,e2) (a1,a2) =
    assertEqualUpToEpsilon eqEpsilon e1 a1 >>
    assertEqualUpToEpsilon eqEpsilon e2 a2

instance {-# OVERLAPPABLE #-} (AssertEqualUpToEpsilon z a,
                               AssertEqualUpToEpsilon z b,
                               AssertEqualUpToEpsilon z c) => AssertEqualUpToEpsilon z (a,b,c) where
  assertEqualUpToEpsilon :: z -> (a,b,c) -> (a,b,c) -> Assertion
  assertEqualUpToEpsilon eqEpsilon (e1,e2,e3) (a1,a2,a3) =
    assertEqualUpToEpsilon eqEpsilon e1 a1 >>
    assertEqualUpToEpsilon eqEpsilon e2 a2 >>
    assertEqualUpToEpsilon eqEpsilon e3 a3

instance {-# OVERLAPPABLE #-} (AssertEqualUpToEpsilon z a,
                               AssertEqualUpToEpsilon z b,
                               AssertEqualUpToEpsilon z c,
                               AssertEqualUpToEpsilon z d) => AssertEqualUpToEpsilon z (a,b,c,d) where
  assertEqualUpToEpsilon :: z -> (a,b,c,d) -> (a,b,c,d) -> Assertion
  assertEqualUpToEpsilon eqEpsilon (e1,e2,e3,e4) (a1,a2,a3,a4) =
    assertEqualUpToEpsilon eqEpsilon e1 a1 >>
    assertEqualUpToEpsilon eqEpsilon e2 a2 >>
    assertEqualUpToEpsilon eqEpsilon e3 a3 >>
    assertEqualUpToEpsilon eqEpsilon e4 a4

instance {-# OVERLAPPABLE #-} (Traversable t, AssertEqualUpToEpsilon z a) => AssertEqualUpToEpsilon z (t a) where
  assertEqualUpToEpsilon :: z -> t a -> t a -> Assertion
  assertEqualUpToEpsilon eqEpsilon expected actual =
    assert_list (assertEqualUpToEpsilon eqEpsilon) (asList expected) (asList actual)

instance {-# OVERLAPPABLE #-} (VS.Storable a, AssertEqualUpToEpsilon z a) => AssertEqualUpToEpsilon z (VS.Vector a) where
  assertEqualUpToEpsilon :: z -> VS.Vector a -> VS.Vector a -> Assertion
  assertEqualUpToEpsilon eqEpsilon expected actual =
    assert_list (assertEqualUpToEpsilon eqEpsilon) (VG.toList expected) (VG.toList actual)

instance {-# OVERLAPPABLE #-} (VS.Storable a, OS.Shape sh1, AssertEqualUpToEpsilon z a) => AssertEqualUpToEpsilon z (OS.Array sh1 a) where
  assertEqualUpToEpsilon :: z -> OS.Array sh1 a -> OS.Array sh1 a -> Assertion
  assertEqualUpToEpsilon eqEpsilon = assert_shape (assertEqualUpToEpsilon eqEpsilon)

----------------------------------------------------------------------------
-- Generic comparisons without explicit error margin
----------------------------------------------------------------------------

-- | Asserts that the specified actual floating point value is close to the expected value.
-- The output message will contain the prefix, the expected value, and the
-- actual value.
--
-- If the prefix is the empty string (i.e., @\"\"@), then the prefix is omitted
-- and only the expected and actual values are output.
assertClose :: (Fractional a, Ord a, Show a, HasCallStack)
            => String -- ^ The message prefix
            -> a      -- ^ The expected value
            -> a      -- ^ The actual value
            -> Assertion
assertClose preface expected actual = do
  eqEpsilon <- readIORef eqEpsilonRef
  assertEqualUpToEps preface (fromRational eqEpsilon) expected actual

-- | Asserts that the specified actual floating point value is close to at least one of the expected values.
assertCloseElem :: forall a. (Fractional a, Ord a, Show a, HasCallStack)
                => String   -- ^ The message prefix
                -> [a]      -- ^ The expected values
                -> a        -- ^ The actual value
                -> Assertion
assertCloseElem preface expected actual = do
  eqEpsilon <- readIORef eqEpsilonRef
  go_assert eqEpsilon expected
  where
    msg = (if null preface then "" else preface ++ "\n") ++
           "wrong result: " ++ show actual ++ " is expected to be a member of " ++ show expected
    go_assert :: Rational -> [a] -> Assertion
    go_assert _ [] = assertFailure msg
    go_assert eqEps (h:t) =
      if abs (h-actual) < fromRational eqEps then assertClose msg h actual else go_assert eqEps t

-- | Asserts that the specified actual floating point value list is close to the expected value.
assertCloseList :: (AssertClose a)
                => [a]      -- ^ The expected value
                -> [a]      -- ^ The actual value
                -> Assertion
assertCloseList = assert_list (flip (@?~))

----------------------------------------------------------------------------
-- AssertClose class together with (@?~) operator
----------------------------------------------------------------------------

-- | Things that can be asserted to be "approximately equal" to each other. The
--   contract for this relation is that it must be reflexive and symmetrical,
--   but not necessarily transitive.
class AssertClose a where
  -- | Makes an assertion that the actual value is close to the expected value.
  (@?~) :: a -- ^ The actual value
        -> a -- ^ The expected value
        -> Assertion

instance {-# OVERLAPPABLE #-} (Fractional a, Ord a, Show a) => AssertClose a where
  (@?~) :: a -> a -> Assertion
  (@?~) actual expected =
    assertClose "" expected actual

instance (AssertClose a) => AssertClose (a,a) where
  (@?~) :: (a,a) -> (a,a) -> Assertion
  (@?~) actual expected =
    (@?~) (fst actual) (fst expected) >> (@?~) (snd actual) (snd expected)

instance {-# OVERLAPPABLE #-} (Traversable t, AssertClose a) => AssertClose (t a) where
  (@?~) :: t a -> t a -> Assertion
  (@?~) actual expected =
    assertCloseList (asList expected) (asList actual)

instance {-# OVERLAPPABLE #-} (Traversable t, AssertClose a) => AssertClose (t a, a) where
  (@?~) :: (t a, a) -> (t a, a) -> Assertion
  (@?~) (actual_xs, actual_x) (expected_xs, expected_x) =
    (@?~) actual_x expected_x >> assertCloseList (asList expected_xs) (asList actual_xs)

instance {-# OVERLAPPABLE #-} (VS.Storable a, AssertClose a) => AssertClose (VS.Vector a) where
  (@?~) :: VS.Vector a -> VS.Vector a -> Assertion
  (@?~) actual_xs expected_xs = assertCloseList (VG.toList expected_xs) (VG.toList actual_xs)

-- TODO; make an instance for pairs instead
instance (VS.Storable a, AssertClose a) => AssertClose (VS.Vector a, a) where
  (@?~) :: (VS.Vector a, a) -> (VS.Vector a, a) -> Assertion
  (@?~) (actual_xs, actual_x) (expected_xs, expected_x) =
    (@?~) actual_x expected_x >> assertCloseList (VG.toList expected_xs) (VG.toList actual_xs)
