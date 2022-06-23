module TestCommonEqEpsilon (eqEpsilonDefault, setEpsilonEq, assertClose, assertCloseElem, assertCloseList) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Data.IORef
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.IO.Unsafe
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

-- Default value for eqEpsilonRef
eqEpsilonDefault :: Double
eqEpsilonDefault = 1e-6

-- Ugly global epsilon used to compare floating point values.
eqEpsilonRef :: IORef Double
{-# NOINLINE eqEpsilonRef #-}
eqEpsilonRef = unsafePerformIO $ newIORef eqEpsilonDefault

-- Ugly global epsilon setter (to be called once).
setEpsilonEq :: Double -> IO ()
setEpsilonEq = atomicWriteIORef eqEpsilonRef

-- | Asserts that the specified actual floating point value is close to the expected value.
-- The output message will contain the prefix, the expected value, and the
-- actual value.
--
-- If the prefix is the empty string (i.e., @\"\"@), then the prefix is omitted
-- and only the expected and actual values are output.
assertClose :: String -- ^ The message prefix
            -> Double -- ^ The expected value
            -> Double -- ^ The actual value
            -> Assertion
assertClose preface expected actual = do
  eqEpsilon <- readIORef eqEpsilonRef
  assertBool msg (abs(expected-actual) < eqEpsilon)
  where msg = (if null preface then "" else preface ++ "\n") ++
               "expected: " ++ show expected ++ "\n but got: " ++ show actual

-- | Asserts that the specified actual floating point value is close to at least one of the expected values.
assertCloseElem :: String   -- ^ The message prefix
                -> [Double] -- ^ The expected values
                -> Double   -- ^ The actual value
                -> Assertion
assertCloseElem preface expected actual = do
  eqEpsilon <- readIORef eqEpsilonRef
  go_assert eqEpsilon expected
  where
    msg = (if null preface then "" else preface ++ "\n") ++
           "wrong result: " ++ show actual ++ " is expected to be a member of " ++ show expected
    go_assert :: Double -> [Double] -> Assertion
    go_assert _ [] = assertFailure msg
    go_assert eqEps (h1:t1) =
      if abs(h1-actual) < eqEps then assertClose msg h1 actual else go_assert eqEps t1

-- | Asserts that the specified actual floating point value list is close to the expected value.
assertCloseList :: String   -- ^ The message prefix
                -> [Double] -- ^ The expected value
                -> [Double] -- ^ The actual value
                -> Assertion
assertCloseList preface expected actual =
  go_assert expected actual
  where
    len1 :: Int = length expected
    len2 :: Int = length actual
    msgneq :: String = (if null preface then "" else preface ++ "\n") ++
                        "expected " ++ show len1 ++ " elements, but got " ++ show len2
    go_assert :: [Double] -> [Double] -> Assertion
    go_assert [] [] = assertBool preface True
    go_assert [] (_:_) = assertFailure msgneq
    go_assert (_:_) [] = assertFailure msgneq
    go_assert (h1:t1) (h2:t2) =
      assertClose preface h1 h2 >> go_assert t1 t2
