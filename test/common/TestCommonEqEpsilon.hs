{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TestCommonEqEpsilon (EqEpsilon, setEpsilonEq, assertCloseElem, assertCloseList, (@?~)) where

import Prelude
import Data.Typeable

import Data.IORef
import System.IO.Unsafe
import Test.Tasty.HUnit
import Test.Tasty.Options

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
assertClose :: forall a. (Fractional a, Ord a, Show a, HasCallStack)
            => String -- ^ The message prefix
            -> a      -- ^ The expected value
            -> a      -- ^ The actual value
            -> Assertion
assertClose preface expected actual = do
  eqEpsilon <- readIORef eqEpsilonRef
  assertBool msg (abs (expected-actual) < fromRational eqEpsilon)
  where msg = (if null preface then "" else preface ++ "\n") ++
               "expected: " ++ show expected ++ "\n but got: " ++ show actual

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
assertCloseList :: forall a. (Fractional a, Ord a, Show a, HasCallStack)
                => String   -- ^ The message prefix
                -> [a]      -- ^ The expected value
                -> [a]      -- ^ The actual value
                -> Assertion
assertCloseList preface expected actual =
  go_assert expected actual
  where
    len1 :: Int = length expected
    len2 :: Int = length actual
    msgneq :: String = (if null preface then "" else preface ++ "\n") ++
                        "expected " ++ show len1 ++ " elements, but got " ++ show len2
    go_assert :: [a] -> [a] -> Assertion
    go_assert [] [] = assertBool preface True
    go_assert [] (_:_) = assertFailure msgneq
    go_assert (_:_) [] = assertFailure msgneq
    go_assert (h1:t1) (h2:t2) =
      assertClose preface h1 h2 >> go_assert t1 t2

infix  1 @?~

-- | Asserts that the specified actual value is close to the expected value
--   (with the actual value on the left-hand side).
(@?~)
  :: (Fractional a, Ord a, Show a, HasCallStack)
  => a -- ^ The actual value
  -> a -- ^ The expected value
  -> Assertion
actual @?~ expected = assertClose "" expected actual
