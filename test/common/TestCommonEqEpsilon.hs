{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving,
             UndecidableInstances #-}
module TestCommonEqEpsilon (EqEpsilon, setEpsilonEq,
                            assertEqualUpToEps,
                            assertEqualUpToEps3,
                            assertEqualUpToEpsList,
                            assertCloseElem, (@?~)) where

import Data.Typeable
import Prelude

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

-- | Asserts that the specified actual floating point value is close to the expected value.
-- The output message will contain the prefix, the expected value, and the
-- actual value.
--
-- If the prefix is the empty string (i.e., @\"\"@), then the prefix is omitted
-- and only the expected and actual values are output.
assertEqualUpToEps :: forall a. (Fractional a, Ord a, Show a, HasCallStack)
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

assertEqualUpToEps3 :: forall a. (Fractional a, Ord a, Show a, HasCallStack)
                    => String  -- ^ The message prefix
                    -> a       -- ^ The error margin
                    -> (a,a,a) -- ^ The expected value
                    -> (a,a,a) -- ^ The actual value
                    -> Assertion
assertEqualUpToEps3 preface eqEpsilon (e1,e2,e3) (a1,a2,a3) =
  assertEqualUpToEps preface eqEpsilon e1 a1 >>
  assertEqualUpToEps preface eqEpsilon e2 a2 >>
  assertEqualUpToEps preface eqEpsilon e3 a3

assert_list :: forall a. ()
            => (a -> a -> Assertion) -- ^ The function used to make an assertion on two elements (expected, actual)
            -> [a]                   -- ^ The expected value
            -> [a]                   -- ^ The actual value
            -> Assertion
assert_list make_assert expected actual =
  go_assert expected actual
  where
    len1 :: Int = length expected
    len2 :: Int = length actual
    msgneq :: String = "expected " ++ show len1 ++ " elements, but got " ++ show len2
    go_assert :: [a] -> [a] -> Assertion
    go_assert [] [] = assertBool "" True
    go_assert [] (_:_) = assertFailure msgneq
    go_assert (_:_) [] = assertFailure msgneq
    go_assert (head_exp:tail_exp) (head_act:tail_act) =
      make_assert head_exp head_act >> go_assert tail_exp tail_act

assertEqualUpToEpsList :: forall a. (Fractional a, Ord a, Show a, HasCallStack)
                       => String   -- ^ The message prefix
                       -> a        -- ^ The error margin
                       -> [a]      -- ^ The expected value
                       -> [a]      -- ^ The actual value
                       -> Assertion
assertEqualUpToEpsList preface eqEpsilon = assert_list (assertEqualUpToEps preface eqEpsilon)

-- | Asserts that the specified actual floating point value is close to the expected value.
-- The output message will contain the prefix, the expected value, and the
-- actual value.
--
-- If the prefix is the empty string (i.e., @\"\"@), then the prefix is omitted
-- and only the expected and actual values are output.
assertClose :: forall a. (Fractional a, Ord a, Show a, HasCallStack)
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
assertCloseList :: forall a. (AssertClose a)
                => [a]      -- ^ The expected value
                -> [a]      -- ^ The actual value
                -> Assertion
assertCloseList = assert_list (flip (@?~))

-- | Foldable to list.
asList :: Foldable t => t a -> [a]
asList = foldr (:) []

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
