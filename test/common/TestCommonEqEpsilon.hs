{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, UndecidableInstances #-}

module TestCommonEqEpsilon (EqEpsilon, setEpsilonEq, assertCloseElem, (@?~)) where

import Prelude
import Data.Typeable

import           Control.Exception
import           Data.IORef
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Storable as VS
import           System.IO.Unsafe
import qualified Test.HUnit.Approx
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

exceptionHandler :: HUnitFailure -> IO ()
exceptionHandler e = putStrLn $ "Hello from exceptionHandler! We got HUnitFailure: " ++ show e

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
  putStrLn "DEBUG-XXX-0"
  eqEpsilon <- readIORef eqEpsilonRef
  putStrLn "DEBUG-XXX-1"
  putStrLn "DEBUG-XXX-2"
  catch (Test.HUnit.Approx.assertApproxEqual preface (fromRational eqEpsilon) expected actual) exceptionHandler
  putStrLn "DEBUG-XXX-3"

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
assertCloseList :: forall a. (AssertClose a, HasCallStack)
                => [a]      -- ^ The expected value
                -> [a]      -- ^ The actual value
                -> Assertion
assertCloseList expected actual =
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
      (@?~) head_act head_exp >> go_assert tail_exp tail_act

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

instance (VS.Storable a, AssertClose a) => AssertClose (VS.Vector a, a) where
  (@?~) :: (VS.Vector a, a) -> (VS.Vector a, a) -> Assertion
  (@?~) (actual_xs, actual_x) (expected_xs, expected_x) =
    (@?~) actual_x expected_x >> assertCloseList (VG.toList expected_xs) (VG.toList actual_xs)
