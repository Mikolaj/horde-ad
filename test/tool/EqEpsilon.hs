{-# LANGUAGE UndecidableInstances #-}
-- | Operations for comparing values up to a tolerance margin, to be used
-- for tests.
module EqEpsilon
  ( EqEpsilon, setEpsilonEq
  , AssertEqualUpToEpsilon(..)
  , assertEqualUpToEpsilonWithMark, assertEqualUpToEpsilon
  , assertCloseElem, assertClose, (@?~)
  ) where

import Prelude

import Data.Int (Int64)
import Data.IORef
import Foreign.C (CInt)
import System.IO.Unsafe (unsafePerformIO)
import Test.Tasty.HUnit
import Test.Tasty.Options

import Shared

newtype EqEpsilon = EqEpsilon Rational

instance IsOption EqEpsilon where
  defaultValue = EqEpsilon eqEpsilonDefault
  parseValue s = fmap (EqEpsilon . toRational)
                      ((safeRead :: String -> Maybe Double) s)
  optionName = return "eq-epsilon"
  optionHelp = return $ "Epsilon to use for floating point comparisons: abs(a-b) <= epsilon. Default: " ++ show (fromRational eqEpsilonDefault :: Double)

-- | Default value for eqEpsilonRef.
eqEpsilonDefault :: Rational
eqEpsilonDefault = 1e-6

-- | Global epsilon used to compare floating point values.
eqEpsilonRef :: IORef Rational
{-# NOINLINE eqEpsilonRef #-}
eqEpsilonRef = unsafePerformIO $ newIORef eqEpsilonDefault

-- | Global epsilon setter (to be called once).
setEpsilonEq :: EqEpsilon -> IO ()
setEpsilonEq (EqEpsilon x) = atomicWriteIORef eqEpsilonRef x


-- * Helper functions

assert_list :: forall a. HasCallStack
            => (a -> a -> Assertion)
                 -- ^ The function used to make an assertion
                 -- on two elements (expected, actual)
            -> [a]  -- ^ The expected value
            -> [a]  -- ^ The actual value
            -> Assertion
assert_list make_assert expected actual =
  if lenE == lenA then
    go_assert_list expected actual
  else
    assertFailure $ "List too " ++ (if lenE < lenA then "long" else "short")
                    ++ ": expected " ++ show lenE ++ " elements, but got: "
                    ++ show lenA
  where
    lenE :: Int = length expected
    lenA :: Int = length actual

    go_assert_list :: [a]  -- The expected value
                   -> [a]  -- The actual value
                   -> Assertion
    go_assert_list [] [] = assertBool "" True
    go_assert_list [] (_:_) = assertFailure "More list elements than expected!"
    go_assert_list (_:_) [] = assertFailure "Less list elements than expected!"
    go_assert_list (head_exp:tail_exp) (head_act:tail_act) =
      make_assert head_exp head_act >> go_assert_list tail_exp tail_act

assert_shape
  :: forall a b. (HasShape a, Linearizable a b, HasCallStack)
  => (b -> b -> Assertion)  -- ^ The function used to make an assertion
                            -- on two elements (expected, actual)
  -> a                      -- ^ The expected value
  -> a                      -- ^ The actual value
  -> Assertion
assert_shape make_assert expected actual =
  if shapeE == shapeA then
    assert_list make_assert (linearize expected) (linearize actual)
  else
    assertFailure $ "Expected shape: " ++ show shapeE ++ ", but got: "
                    ++ show shapeA
  where
    shapeE = shapeL expected
    shapeA = shapeL actual


-- * Generic comparisons with explicit error margin

-- | Asserts that the specified actual floating point value is close
-- to the expected value. The output message will contain the prefix,
-- the expected value, and the actual value.
--
-- If the prefix is the empty string (i.e., @\"\"@), then the prefix is omitted
-- and only the expected and actual values are output.
assert_close_eps :: (Real a, Show a, HasCallStack)
                 => String    -- ^ The message prefix
                 -> String    -- ^ The message suffix
                 -> Rational  -- ^ The error margin
                 -> a         -- ^ The expected value
                 -> a         -- ^ The actual value
                 -> Assertion
assert_close_eps preface epilogue eqEpsilon expected actual = do
  assertBool (message eqEpsilon)
             (realToFrac (abs (expected - actual)) <= eqEpsilon)
  where
    msg = "expected: " ++ show expected ++ "\n but got: " ++ show actual
    message errorMargin =
      (if null preface then "" else preface ++ "\n")
      ++ msg ++ "\n (maximum margin of error: "
      ++ show (realToFrac errorMargin :: Double) ++ ")"
      ++ (if null epilogue
             || (lowercase epilogue == lowercase preface)
             || (lowercase epilogue == lowercase msg)
          then ""
          else "\n" ++ epilogue)


-- * AssertEqualUpToEpsilon class

class Show a => AssertEqualUpToEpsilon a where
  assertEqualUpToEpsilonWithMsg
    :: String    -- ^ message suffix
    -> Rational  -- ^ error margin (i.e., the epsilon)
    -> a         -- ^ expected value
    -> a         -- ^ actual value
    -> Assertion

assertEqualUpToEpsilonWithMark
  :: (AssertEqualUpToEpsilon a, HasCallStack)
  => String  -- ^ message suffix's prefix
  -> Rational  -- ^ error margin (i.e., the epsilon)
  -> a  -- ^ expected value
  -> a  -- ^ actual value
  -> Assertion
assertEqualUpToEpsilonWithMark mark error_margin expected actual =
  let prefix = if null mark then "" else "*In " ++ mark ++ "*\n"
  in assertEqualUpToEpsilonWithMsg
       (prefix ++ "Expected: " ++ show expected
               ++ "\n but got: " ++ show actual)
       error_margin
       expected actual

assertEqualUpToEpsilon
  :: (AssertEqualUpToEpsilon a, HasCallStack)
  => Rational  -- ^ error margin (i.e., the epsilon)
  -> a  -- ^ expected value
  -> a  -- ^ actual value
  -> Assertion
assertEqualUpToEpsilon = assertEqualUpToEpsilonWithMark ""

instance AssertEqualUpToEpsilon Double where
  assertEqualUpToEpsilonWithMsg = assert_close_eps ""

instance AssertEqualUpToEpsilon Float where
  assertEqualUpToEpsilonWithMsg = assert_close_eps ""

instance AssertEqualUpToEpsilon Int64 where
  assertEqualUpToEpsilonWithMsg = assert_close_eps ""

instance AssertEqualUpToEpsilon CInt where
  assertEqualUpToEpsilonWithMsg = assert_close_eps ""

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b)
         => AssertEqualUpToEpsilon (a,b) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2) (a1,a2) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b,
          AssertEqualUpToEpsilon c)
         => AssertEqualUpToEpsilon (a,b,c) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3) (a1,a2,a3) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b,
          AssertEqualUpToEpsilon c,
          AssertEqualUpToEpsilon d)
         => AssertEqualUpToEpsilon (a,b,c,d) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3,e4) (a1,a2,a3,a4) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e4 a4

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b,
          AssertEqualUpToEpsilon c,
          AssertEqualUpToEpsilon d,
          AssertEqualUpToEpsilon e)
         => AssertEqualUpToEpsilon (a,b,c,d,e) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3,e4,e5)
                                              (a1,a2,a3,a4,a5) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e4 a4 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e5 a5

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b,
          AssertEqualUpToEpsilon c,
          AssertEqualUpToEpsilon d,
          AssertEqualUpToEpsilon e,
          AssertEqualUpToEpsilon f)
         => AssertEqualUpToEpsilon (a,b,c,d,e,f) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3,e4,e5,e6)
                                              (a1,a2,a3,a4,a5,a6) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e4 a4 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e5 a5 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e6 a6

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b,
          AssertEqualUpToEpsilon c,
          AssertEqualUpToEpsilon d,
          AssertEqualUpToEpsilon e,
          AssertEqualUpToEpsilon f,
          AssertEqualUpToEpsilon g)
         => AssertEqualUpToEpsilon (a,b,c,d,e,f,g) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3,e4,e5,e6,e7)
                                              (a1,a2,a3,a4,a5,a6,a7) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e4 a4 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e5 a5 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e6 a6 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e7 a7

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b,
          AssertEqualUpToEpsilon c,
          AssertEqualUpToEpsilon d,
          AssertEqualUpToEpsilon e,
          AssertEqualUpToEpsilon f,
          AssertEqualUpToEpsilon g,
          AssertEqualUpToEpsilon h)
         => AssertEqualUpToEpsilon (a,b,c,d,e,f,g,h) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3,e4,e5,e6,e7,e8)
                                              (a1,a2,a3,a4,a5,a6,a7,a8) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e4 a4 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e5 a5 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e6 a6 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e7 a7 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e8 a8

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b,
          AssertEqualUpToEpsilon c,
          AssertEqualUpToEpsilon d,
          AssertEqualUpToEpsilon e,
          AssertEqualUpToEpsilon f,
          AssertEqualUpToEpsilon g,
          AssertEqualUpToEpsilon h,
          AssertEqualUpToEpsilon i)
         => AssertEqualUpToEpsilon (a,b,c,d,e,f,g,h,i) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3,e4,e5,e6,e7,e8,e9)
                                              (a1,a2,a3,a4,a5,a6,a7,a8,a9) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1 a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2 a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3 a3 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e4 a4 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e5 a5 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e6 a6 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e7 a7 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e8 a8 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e9 a9

instance (AssertEqualUpToEpsilon a,
          AssertEqualUpToEpsilon b,
          AssertEqualUpToEpsilon c,
          AssertEqualUpToEpsilon d,
          AssertEqualUpToEpsilon e,
          AssertEqualUpToEpsilon f,
          AssertEqualUpToEpsilon g,
          AssertEqualUpToEpsilon h,
          AssertEqualUpToEpsilon i,
          AssertEqualUpToEpsilon j)
         => AssertEqualUpToEpsilon (a,b,c,d,e,f,g,h,i,j) where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon (e1,e2,e3,e4,e5,e6,e7,e8,e9,e10)
                                              (a1,a2,a3,a4,a5,a6,a7,a8,a9,a10) =
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e1  a1 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e2  a2 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e3  a3 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e4  a4 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e5  a5 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e6  a6 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e7  a7 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e8  a8 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e9  a9 >>
    assertEqualUpToEpsilonWithMsg msg eqEpsilon e10 a10

instance {-# OVERLAPPABLE #-}
         (Show a, HasShape a, Linearizable a b, AssertEqualUpToEpsilon b)
         => AssertEqualUpToEpsilon a where
  assertEqualUpToEpsilonWithMsg msg eqEpsilon =
    assert_shape (assertEqualUpToEpsilonWithMsg msg eqEpsilon)


-- * Generic comparisons without explicit error margin

-- | Asserts that the specified actual floating point value is close
-- to at least one of the expected values.
assertCloseElem :: forall a. (Real a, Fractional a, Show a, HasCallStack)
                => String   -- ^ The message prefix
                -> [a]      -- ^ The expected values
                -> a        -- ^ The actual value
                -> Assertion
assertCloseElem preface expected actual = do
  eqEpsilon <- readIORef eqEpsilonRef
  go_assert eqEpsilon expected
  where
    msg = (if null preface then "" else preface ++ "\n")
          ++ "wrong result: " ++ show actual
          ++ " is expected to be a member of " ++ show expected
    go_assert :: Rational -> [a] -> Assertion
    go_assert _ [] = assertFailure msg
    go_assert eqEps (h:t) =
      if abs (h-actual) <= fromRational eqEps
      then assert_close_eps msg "" (fromRational eqEps) h actual
      else go_assert eqEps t

assertClose :: (AssertEqualUpToEpsilon a, HasCallStack)
      => a  -- ^ The expected value
      -> a  -- ^ The actual value
      -> Assertion
assertClose expected actual = do
  eqEpsilon <- readIORef eqEpsilonRef
  assertEqualUpToEpsilon (fromRational eqEpsilon) expected actual

infix 1 @?~
(@?~) :: (AssertEqualUpToEpsilon a, HasCallStack)
      => a  -- ^ The actual value
      -> a  -- ^ The expected value
      -> Assertion
(@?~) = flip assertClose
