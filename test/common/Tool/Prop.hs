module Tool.Prop
  ( listsToParameters, cmpTwo, cmpTwoSimple
  , qcPropDom, quickCheckTest0, fquad, quad
  ) where

import Prelude

import Test.Tasty
import Test.Tasty.QuickCheck

import HordeAd

-- Checks if 2 numbers are close enough.
close1 :: forall r. (Ord r, Fractional r)
       => r -> r -> Bool
close1 a b = abs (a - b) <= 1e-4

-- Checks if 2 number pairs are close enough.
close2 :: forall r. (Ord r, Fractional r)
       => (r,r) -> (r,r) -> Property
close2 (a1, b1) (a2, b2) = close1 a1 a2 .&&. close1 b1 b2

quad :: ADModeAndNum d r
     => ADVal d r -> ADVal d r -> ADVal d r
quad x y =
  let x2 = square x
      y2 = y * y
      tmp = x2 + y2
  in tmp + 5

fquad :: forall r d. ADModeAndNum d r
      => ADInputs d r -> ADVal d r
fquad inputs =
  let x = at0 inputs 0
      y = at0 inputs 1
  in quad x y

quickCheckTest0
  :: TestName
  -> (forall d r. ADModeAndNum d r => ADInputs d r -> ADVal d r)
  -> ((Double, Double, Double)
      -> ([Double], [Double], [Double], [Double]))
  -> TestTree
quickCheckTest0 txt f fArg =
  qcTestRanges txt f (listsToParameters4 . fArg)
               ((-2, -2, -2), (2, 2, 2))
               ((-1e-7, -1e-7, -1e-7), (1e-7, 1e-7, 1e-7)) (-10, 10)

-- A quick check to compare the derivatives and values of 2 given functions.
cmpTwo
  :: (d ~ 'ADModeDerivative, Dual d r ~ r, ADModeAndNum d r)
  => (ADInputs d r -> ADVal d r)
  -> (ADInputs d r -> ADVal d r)
  -> Domains r
  -> Domains r
  -> Domains r
  -> Domains r
  -> Property
cmpTwo f1 f2 params1 params2 ds1 ds2 =
  close2 (fwdOnDomains params1 f1 ds1) (fwdOnDomains params2 f2 ds2)

-- A quick check to compare the derivatives and values of 2 given functions.
cmpTwoSimple
  :: (d ~ 'ADModeDerivative, Dual d r ~ r, ADModeAndNum d r)
  => (ADInputs d r -> ADVal d r)
  -> (ADInputs d r -> ADVal d r)
  -> Domains r
  -> Domains r
  -> Property
cmpTwoSimple f1 f2 parameters ds =
  cmpTwo f1 f2 parameters parameters ds ds

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
qcPropDom :: (forall d r. (ADModeAndNum d r, r ~ Double)
              => ADInputs d r -> ADVal d r)
          -> Domains Double
          -> Domains Double
          -> Domains Double
          -> Double
          -> Property
qcPropDom f args ds perturbation dt =
  let ff@(derivative, ffValue) = fwdOnDomains args f ds
      (derivativeAtPerturbation, valueAtPerturbation) =
        fwdOnDomains args f perturbation
      (gradient, revValue) = revOnDomains dt f args
      res = slowFwdOnDomains args f ds
  in
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
    .&&. close1 (valueOnDomains f (addParameters args perturbation))
                (ffValue + derivativeAtPerturbation)

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
qcPropFArg :: (forall d r. ADModeAndNum d r
               => ADInputs d r -> ADVal d r)
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
-- and all kinds of computing of the value of the objective function.
qcTestRanges
  :: TestName
  -> (forall d r. ADModeAndNum d r
      => ADInputs d r -> ADVal d r)
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
