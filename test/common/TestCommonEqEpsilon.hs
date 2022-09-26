{-# LANGUAGE FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving,
             QuantifiedConstraints,
             UndecidableInstances #-}
module TestCommonEqEpsilon (EqEpsilon, setEpsilonEq,
                            assertEqualUpToEpsilon,
                            assertCloseElem, assertClose, (@?~)) where

import Data.Typeable
import Prelude

import qualified Data.Array.ShapedS as OS
import           Data.IORef
import qualified Data.Vector.Storable as VS
import           System.IO.Unsafe
import           Test.Tasty.HUnit
import           Test.Tasty.Options

import           TestCommon

newtype EqEpsilon = EqEpsilon Rational
  deriving (Typeable, Num, Fractional)

instance IsOption EqEpsilon where
  defaultValue = EqEpsilon eqEpsilonDefault
  parseValue s = fmap (EqEpsilon . toRational) ((safeRead :: String -> Maybe Double) s)
  optionName = return "eq-epsilon"
  optionHelp = return $ "Epsilon to use for floating point comparisons: abs(a-b) < epsilon . Default: " ++ show (fromRational eqEpsilonDefault :: Double)

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

assert_shape :: forall a b. (HasShape a, Linearizable a b)
             => (b -> b -> Assertion) -- ^ The function used to make an assertion on two elements (expected, actual)
             -> a                     -- ^ The expected value
             -> a                     -- ^ The actual value
             -> Assertion
assert_shape make_assert expected actual =
  if shapeE == shapeA then
    assert_list make_assert (linearize expected) (linearize actual)
  else
    assertFailure $ "Expected shape: " ++ show shapeE ++ ", but got: " ++ show shapeA
  where
    shapeE = shapeL expected
    shapeA = shapeL actual

----------------------------------------------------------------------------
-- Generic comparisons with explicit error margin
----------------------------------------------------------------------------

-- | Asserts that the specified actual floating point value is close to the expected value.
-- The output message will contain the prefix, the expected value, and the
-- actual value.
--
-- If the prefix is the empty string (i.e., @\"\"@), then the prefix is omitted
-- and only the expected and actual values are output.
assert_close_eps :: (Num a, Ord a, Show a, HasCallStack)
                   => String -- ^ The message prefix
                   -> String -- ^ The message suffix
                   -> a      -- ^ The error margin
                   -> a      -- ^ The expected value
                   -> a      -- ^ The actual value
                   -> Assertion
assert_close_eps preface epilogue eqEpsilon expected actual = do
  assertBool (msg eqEpsilon) (abs (expected-actual) < eqEpsilon)
  where msg errorMargin = (if null preface then "" else preface ++ "\n") ++
                           "expected: " ++ show expected ++ "\n but got: " ++ show actual ++
                           "\n (maximum margin of error: " ++ show errorMargin ++ ")" ++
                           (if null epilogue then "" else "\n" ++ epilogue)

----------------------------------------------------------------------------
-- AssertEqualUpToEpsilon class
----------------------------------------------------------------------------

class (Fractional z, Show a) => AssertEqualUpToEpsilon z a | a -> z where

  assertEqualUpToEpsilonWithMsg :: String -- ^ The message suffix
                                -> z      -- ^ The error margin (i.e., the epsilon)
                                -> a      -- ^ The expected value
                                -> a      -- ^ The actual value
                                -> Assertion

  assertEqualUpToEpsilon :: z -- ^ The error margin (i.e., the epsilon)
                         -> a -- ^ The expected value
                         -> a -- ^ The actual value
                         -> Assertion
  assertEqualUpToEpsilon error_margin expected actual =
    assertEqualUpToEpsilonWithMsg ("Expected: " ++ (show expected) ++ "\n but got: " ++ (show actual)) error_margin expected actual

instance AssertEqualUpToEpsilon Double Double where
  assertEqualUpToEpsilonWithMsg :: String -> Double -> Double -> Double -> Assertion
  assertEqualUpToEpsilonWithMsg = assert_close_eps ""

instance AssertEqualUpToEpsilon Float Float where
  assertEqualUpToEpsilonWithMsg :: String -> Float -> Float -> Float -> Assertion
  assertEqualUpToEpsilonWithMsg = assert_close_eps ""

instance (AssertEqualUpToEpsilon z a,
          AssertEqualUpToEpsilon z b) => AssertEqualUpToEpsilon z (a,b) where
  assertEqualUpToEpsilonWithMsg :: String -> z -> (a,b) -> (a,b) -> Assertion
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2) (a1,a2) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2

instance (AssertEqualUpToEpsilon z a,
          AssertEqualUpToEpsilon z b,
          AssertEqualUpToEpsilon z c) => AssertEqualUpToEpsilon z (a,b,c) where
  assertEqualUpToEpsilonWithMsg :: String -> z -> (a,b,c) -> (a,b,c) -> Assertion
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3) (a1,a2,a3) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3

instance (AssertEqualUpToEpsilon z a,
          AssertEqualUpToEpsilon z b,
          AssertEqualUpToEpsilon z c,
          AssertEqualUpToEpsilon z d) => AssertEqualUpToEpsilon z (a,b,c,d) where
  assertEqualUpToEpsilonWithMsg :: String -> z -> (a,b,c,d) -> (a,b,c,d) -> Assertion
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3,e4) (a1,a2,a3,a4) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e4 a4

instance (VS.Storable a, OS.Shape sh1, AssertEqualUpToEpsilon z a) => AssertEqualUpToEpsilon z (OS.Array sh1 a) where
  assertEqualUpToEpsilonWithMsg :: String -> z -> OS.Array sh1 a -> OS.Array sh1 a -> Assertion
  assertEqualUpToEpsilonWithMsg msg eqEpsilon expected actual = assert_list (assertEqualUpToEpsilonWithMsg msg eqEpsilon) (linearize expected) (linearize actual)

instance {-# OVERLAPPABLE #-} (Fractional z, Show a, HasShape a, Linearizable a b, AssertEqualUpToEpsilon z b) => AssertEqualUpToEpsilon z a where
  assertEqualUpToEpsilonWithMsg :: String -> z -> a -> a -> Assertion
  assertEqualUpToEpsilonWithMsg msg eqEpsilon = assert_shape (assertEqualUpToEpsilonWithMsg msg eqEpsilon)

----------------------------------------------------------------------------
-- Generic comparisons without explicit error margin
----------------------------------------------------------------------------

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
      if abs (h-actual) < fromRational eqEps then assert_close_eps msg "" (fromRational eqEps) h actual else go_assert eqEps t

assertClose :: (AssertEqualUpToEpsilon z a)
      => a -- ^ The expected value
      -> a -- ^ The actual value
      -> Assertion
assertClose expected actual = do
  eqEpsilon <- readIORef eqEpsilonRef
  assertEqualUpToEpsilon (fromRational eqEpsilon) expected actual

(@?~) :: (AssertEqualUpToEpsilon z a)
      => a -- ^ The actual value
      -> a -- ^ The expected value
      -> Assertion
(@?~) = flip assertClose
