{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
-- Needed due to unsafePerformIO:
{-# OPTIONS_GHC -fno-full-laziness #-}
module TestCommon (listsToParameters,
                   cmpTwo, cmpTwoSimple,
                   qcPropDom, quickCheckTest0, fquad, quad
                  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM
import           Test.Tasty
import           Test.Tasty.QuickCheck

import HordeAd hiding (sumElementsVectorOfDual)
import HordeAd.Core.DualClass (Dual)

-- Checks if 2 numbers are close enough.
close1 :: forall r. (Ord r, Fractional r)
          => r -> r -> Bool
close1 a b = abs (a - b) <= 1e-4

-- Checks if 2 number pairs are close enough.
close2 :: forall r. (Ord r, Fractional r)
          => (r,r) -> (r,r) -> Property
close2 (a1, b1) (a2, b2) = close1 a1 a2 .&&. close1 b1 b2

quad :: IsScalar d r
     => DualNumber d r -> DualNumber d r -> DualNumber d r
quad x y =
  let x2 = square x
      y2 = y * y
      tmp = x2 + y2
  in tmp + 5

fquad :: forall r d. IsScalar d r
      => DualNumberVariables d r -> DualNumber d r
fquad variables =
  let x = var0 variables 0
      y = var0 variables 1
  in quad x y

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
       -> (forall d r. IsScalar d r
           => DualNumberVariables d r -> DualNumber d r)
       -> ((Double, Double, Double) -> ([Double], [Double], [Double], [Double]))
       -> TestTree
quickCheckTest0 txt f fArg =
  qcTestRanges txt f (listsToParameters4 . fArg) ((-2, -2, -2), (2, 2, 2)) ((-1e-7, -1e-7, -1e-7), (1e-7, 1e-7, 1e-7)) (-10, 10)

-- A quick check to compare the derivatives and values of 2 given functions.
cmpTwo
  :: (d ~ 'DModeDerivative, Dual d r ~ r, IsScalar d r)
  => (DualNumberVariables d r -> DualNumber d r)
  -> (DualNumberVariables d r -> DualNumber d r)
  -> Domains r
  -> Domains r
  -> Domains r
  -> Domains r
  -> Property
cmpTwo f1 f2 params1 params2 ds1 ds2 =
  close2 (dFastForward f1 params1 ds1) (dFastForward f2 params2 ds2)

-- A quick check to compare the derivatives and values of 2 given functions.
cmpTwoSimple
  :: (d ~ 'DModeDerivative, Dual d r ~ r, IsScalar d r)
  => (DualNumberVariables d r -> DualNumber d r)
  -> (DualNumberVariables d r -> DualNumber d r)
  -> Domains r
  -> Domains r
  -> Property
cmpTwoSimple f1 f2 parameters ds =
  cmpTwo f1 f2 parameters parameters ds ds

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
qcPropDom :: (forall d r. ( IsScalar d r
                            , r ~ Double )
              => DualNumberVariables d r -> DualNumber d r)
          -> Domains Double
          -> Domains Double
          -> Domains Double
          -> Double
          -> IO Property
qcPropDom f args ds perturbation dt = do
  let ff@(derivative, ffValue) = dFastForward f args ds
      (derivativeAtPerturbation, valueAtPerturbation) =
        dFastForward f args perturbation
  (gradient, revValue) <- dReverse dt f args
  res <- dForward f args ds
  return $!
    -- Two forward derivative implementations agree fully:
    res === ff
    -- Objective function value from gradients is the same.
    .&&. ffValue == revValue
    -- Gradients and derivatives agree.
    .&&. close1 (dt * derivative)
                (dotParameters gradient ds)
    -- Objective function value is unaffected by perturbation.
    .&&. ffValue == valueAtPerturbation
    -- Derivative approximates the perturbation of value.
    .&&. close1 (primalValue f (addParameters args perturbation))
                (ffValue + derivativeAtPerturbation)

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
qcPropFArg :: (forall d r. IsScalar d r
               => DualNumberVariables d r -> DualNumber d r)
           -> ((Double, Double, Double) -> Domains Double)
           -> (Double, Double, Double)
           -> (Double, Double, Double)
           -> (Double, Double, Double)
           -> Double
           -> IO Property
qcPropFArg f fArgDom xyz dsRaw perturbationRaw dt = do
  let args = fArgDom xyz
      ds = fArgDom dsRaw
      perturbation = fArgDom perturbationRaw
  qcPropDom f args ds perturbation dt

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
qcTestRanges
  :: TestName
  -> (forall d r. IsScalar d r
      => DualNumberVariables d r -> DualNumber d r)
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
  ioProperty $ qcPropFArg f fArgDom xyz dsRaw perturbationRaw dt
