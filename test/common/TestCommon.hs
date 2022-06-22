{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
module TestCommon (eqEpsilonDefault, setEpsilonEq, assertClose, assertCloseElem, assertCloseList,
                   (+\), (*\), (**\),
                   listsToParameters,
                   cmpTwo, cmpTwoSimple,
                   qcPropDom, quickCheckTest0, fquad, quad
                  ) where

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

import HordeAd hiding (sumElementsVectorOfDual)
import HordeAd.Core.DualClass (Dual)

-- Default value for eqEpsilonRef
eqEpsilonDefault :: Double
eqEpsilonDefault = 1e-6

-- Ugly global epsilon used to compare floating point values.
eqEpsilonRef :: IORef Double
eqEpsilonRef = unsafePerformIO $ newIORef eqEpsilonDefault

-- Ugly global epsilon setter (to be called once).
setEpsilonEq :: Double -> IO ()
setEpsilonEq newEpsilonEq =
  atomicWriteIORef eqEpsilonRef newEpsilonEq

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
  eqEpsilon <- (readIORef eqEpsilonRef)
  assertBool msg (abs(expected-actual) < eqEpsilon)
  where msg = (if null preface then "" else preface ++ "\n") ++
               "expected: " ++ show expected ++ "\n but got: " ++ show actual

-- | Asserts that the specified actual floating point value is close to at least one of the expected values.
assertCloseElem :: String   -- ^ The message prefix
                -> [Double] -- ^ The expected values
                -> Double   -- ^ The actual value
                -> Assertion
assertCloseElem preface expected actual = do
  eqEpsilon <- (readIORef eqEpsilonRef)
  go_assert eqEpsilon expected
  where
    msg = (if null preface then "" else preface ++ "\n") ++
           "wrong result: " ++ show actual ++ " is expected to be a member of " ++ show expected
    go_assert :: Double -> [Double] -> Assertion
    go_assert _ [] = assertFailure msg
    go_assert eqEps (h1:t1) =
      if (abs(h1-actual) < eqEps) then (assertClose msg h1 actual) else (go_assert eqEps t1)

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
      (assertClose preface h1 h2) >> (go_assert t1 t2)

(+\) :: DualMonad d r m
     => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(+\) u v = returnLet $ u + v

(*\) :: DualMonad d r m
     => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(*\) u v = returnLet $ u * v

(**\) :: DualMonad d r m
      => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(**\) u v = returnLet $ u ** v

-- Checks if 2 numbers are close enough.
close1 :: forall r. (Ord r, Fractional r)
          => r -> r -> Bool
close1 a b = abs (a - b) <= 1e-4

-- Checks if 2 number pairs are close enough.
close2 :: forall r. (Ord r, Fractional r)
          => (r,r) -> (r,r) -> Property
close2 (a1, b1) (a2, b2) = close1 a1 a2 .&&. close1 b1 b2

quad :: DualMonad d r m
     => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
quad x y = do
  x2 <- returnLet $ square x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ 5

fquad :: forall r d m. DualMonad d r m
      => DualNumberVariables d r -> m (DualNumber d r)
fquad variables = do
  let x = var0 variables 0
      y = var0 variables 1
  quad x y

listsToParameters :: forall r. (OT.Storable r)
                  => ([r], [r]) -> Domains r
listsToParameters (a0, a1) =
  (V.fromList a0, V.singleton $ V.fromList a1, V.empty, V.empty)

listsToParameters4 :: ([Double], [Double], [Double], [Double]) -> Domains Double
listsToParameters4 (a0, a1, a2, aX) =
  ( V.fromList a0
  , V.singleton $ V.fromList a1
  , if null a2 then V.empty else V.singleton $ HM.matrix 1 a2
  , if null aX then V.empty else V.singleton $ OT.fromList [length aX] aX )

quickCheckTest0 :: TestName
       -> (forall d r m. ( DualMonad d r m
                         , Floating (Out (DualNumber d (Vector r)))
                         , Floating (Out (DualNumber d (OS.Array '[2] r))) )
           => DualNumberVariables d r -> m (DualNumber d r))
       -> ((Double, Double, Double) -> ([Double], [Double], [Double], [Double]))
       -> TestTree
quickCheckTest0 txt f fArg =
  qcTestRanges txt f (listsToParameters4 . fArg) ((-2, -2, -2), (2, 2, 2)) ((-1e-7, -1e-7, -1e-7), (1e-7, 1e-7, 1e-7)) (-10, 10)

-- A quick check to compare the derivatives and values of 2 given functions.
cmpTwo
  :: ( m ~ DualMonadForward r, d ~ 'DModeDerivative, Dual d r ~ r
     , DualMonad d r m )
  => (DualNumberVariables d r -> m (DualNumber d r))
  -> (DualNumberVariables d r -> m (DualNumber d r))
  -> Domains r
  -> Domains r
  -> Domains r
  -> Domains r
  -> Property
cmpTwo f1 f2 params1 params2 ds1 ds2 =
  close2 (dFastForward f1 params1 ds1) (dFastForward f2 params2 ds2)

-- A quick check to compare the derivatives and values of 2 given functions.
cmpTwoSimple
  :: ( m ~ DualMonadForward r, d ~ 'DModeDerivative, Dual d r ~ r
     , DualMonad d r m )
  => (DualNumberVariables d r -> m (DualNumber d r))
  -> (DualNumberVariables d r -> m (DualNumber d r))
  -> Domains r
  -> Domains r
  -> Property
cmpTwoSimple f1 f2 parameters ds =
  cmpTwo f1 f2 parameters parameters ds ds

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
qcPropDom :: (forall d r m. ( DualMonad d r m
                            , r ~ Double
                            , Floating (Out (DualNumber d (Vector r)))
                            , Floating (Out (DualNumber d (OS.Array '[2] r))) )
              => DualNumberVariables d r -> m (DualNumber d r))
       -> Domains Double
       -> Domains Double
       -> Domains Double
       -> Double
       -> Property
qcPropDom f args ds perturbation dt =
      let ff@(derivative, ffValue) = dFastForward f args ds
          (derivativeAtPerturbation, valueAtPerturbation) = dFastForward f args perturbation
          (gradient, revValue) = dReverse dt f args
      in -- Two forward derivative implementations agree fully:
         dForward f args ds === ff
         -- Objective function value from gradients is the same.
         .&&. ffValue == revValue
         -- Gradients and derivatives agree.
         .&&. close1 (dt * derivative)
                     (dotParameters gradient ds)
         -- Objective function value is unaffected by perturbation.
         .&&. ffValue == valueAtPerturbation
         -- Derivative approximates the perturbation of value.
         .&&. close1 (primalValue
                                  f (addParameters
                                                   args perturbation))
                     (ffValue + derivativeAtPerturbation)

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
qcPropFArg :: (forall d r m. ( DualMonad d r m
                         , Floating (Out (DualNumber d (Vector r)))
                         , Floating (Out (DualNumber d (OS.Array '[2] r))) )
               => DualNumberVariables d r -> m (DualNumber d r))
       -> ((Double, Double, Double) -> Domains Double)
       -> (Double, Double, Double)
       -> (Double, Double, Double)
       -> (Double, Double, Double)
       -> Double
       -> Property
qcPropFArg f fArgDom xyz dsRaw perturbationRaw dt =
      let args = fArgDom xyz
          ds = fArgDom dsRaw
          perturbation = fArgDom perturbationRaw
      in qcPropDom f args ds perturbation dt

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
qcTestRanges :: TestName
       -> (forall d r m. ( DualMonad d r m
                         , Floating (Out (DualNumber d (Vector r)))
                         , Floating (Out (DualNumber d (OS.Array '[2] r))) )
           => DualNumberVariables d r -> m (DualNumber d r))
       -> ((Double, Double, Double) -> Domains Double)
       -> ((Double, Double, Double), (Double, Double, Double))
       -> ((Double, Double, Double), (Double, Double, Double))
       -> (Double, Double)
       -> TestTree
qcTestRanges txt f fArgDom dsRange perturbationRange dtRange =
  testProperty txt $
  forAll (choose dsRange) $ \xyz dsRaw ->
  forAll (choose perturbationRange) $ \perturbationRaw ->
  forAll (choose dtRange) $ \dt ->
  qcPropFArg f fArgDom xyz dsRaw perturbationRaw dt
