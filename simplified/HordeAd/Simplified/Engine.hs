{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilies #-}
-- | The implementation of calculating gradient, derivative and value
-- of an objective function defined on dual numbers, as defined
-- in "HordeAd.Core.DualNumber". Together with that module, this forms
-- the basic high-level API of the horde-ad library. Optimizers, etc.,
-- are add-ons.
module HordeAd.Simplified.Engine
  ( -- * The most often used part of the high-level API
    revFun, fwdFun, valueFun
  , -- * The less often used part of the high-level API
    revIO, valueGeneral
  , -- * Operations exposed not for the library users but add-on makers
    revGeneral, fwdGeneral
  , generateDeltaInputs, initializerFixed
  , -- * Internal operations, exposed, e.g., for tests
    slowFwdGeneral, slowFwd, slowFwdFun
  , prettyPrintDf
  ) where

import Prelude

import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM
import           Text.Show.Pretty (ppShow)

-- import           System.Mem (performMinorGC)

import HordeAd.Simplified.Delta
  (derivativeFromDelta, gradientFromDelta, toInputId)
import HordeAd.Simplified.DualClass (Dual, dInput, dummyDual, packDeltaDt)
import HordeAd.Simplified.DualNumber
import HordeAd.Simplified.PairOfVectors (ADInputs (..), makeADInputs)

-- * Evaluation that ignores the dual part of the dual numbers.
-- It's intended for efficiently calculating the value of the function only.

-- The general case, needed for old hacky tests using only scalars.
valueGeneral
  :: Numeric r
  => (ADInputs 'ADModeValue r -> a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueGeneral #-}
valueGeneral f (params0, params1) =
  let replicateDummy p = V.replicate (V.length p) dummyDual
      inputs = makeADInputs (params0, params1)
                            ( replicateDummy params0  -- dummy
                            , replicateDummy params1 )
  in f inputs

valueFun
  :: Numeric r
  => (ADInputs 'ADModeValue r -> ADVal 'ADModeValue a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueFun #-}
valueFun f parameters =
  let D v _ = valueGeneral f parameters
  in v


-- * Evaluation that computes gradients.

revGeneralFun
  :: (HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r)
  => a
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> ADInputs 'ADModeGradient r
  -> (Domains r, a)
-- The functions in which @revGeneralFun@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revGeneralFun #-}
revGeneralFun dt f inputs@ADInputs{..} =
  let dim0 = V.length inputPrimal0
      dim1 = V.length inputPrimal1
      -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started
      !(D v deltaTopLevel) = f inputs
      deltaDt = packDeltaDt dt deltaTopLevel
  in let gradient = gradientFromDelta dim0 dim1 deltaDt
     in (gradient, v)

-- Tests expect this to be in IO by historical accident.
-- But we can possibly add hacks here in the future, such as @performMinorGC@.
revGeneral
  :: (HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r)
  => a
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> ADInputs 'ADModeGradient r
  -> IO (Domains r, a)
{-# INLINE revGeneral #-}
revGeneral dt f inputs = return $! revGeneralFun dt f inputs

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newbies may have trouble understanding it.
-- Also, as of now, @revFun@ is restricted to objective functions with scalar
-- codomains, while VJP is fully general.
revFun
  :: (HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r)
  => a
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> Domains r
  -> (Domains r, a)
revFun dt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in revGeneralFun dt f inputs

revIO
  :: (HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r)
  => a
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> Domains r
  -> IO (Domains r, a)
revIO dt f parameters = return $! revFun dt f parameters


-- * The slow evaluation for derivatives that uses the same
-- delta expressions as for gradients. See @fwdFun@
-- for a fast variant.

slowFwdGeneralFun
  :: HasDelta r
  => ADInputs 'ADModeGradient r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> (r, r)
{-# INLINE slowFwdGeneralFun #-}
slowFwdGeneralFun inputs@ADInputs{..} f ds =
  let dim0 = V.length inputPrimal0
      dim1 = V.length inputPrimal1
      !(D v deltaTopLevel) = f inputs
  in let derivative = derivativeFromDelta dim0 dim1 deltaTopLevel ds
     in (derivative, v)

slowFwdGeneral
  :: HasDelta r
  => ADInputs 'ADModeGradient r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> IO (r, r)
{-# INLINE slowFwdGeneral #-}
slowFwdGeneral inputs f ds = return $! slowFwdGeneralFun inputs f ds

-- The direction vector ds is taken as an extra argument.
slowFwdFun
  :: HasDelta r
  => Domains r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> (r, r)
slowFwdFun parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in slowFwdGeneralFun inputs f ds

slowFwd
  :: HasDelta r
  => Domains r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> IO (r, r)
slowFwd parameters f ds = return $! slowFwdFun parameters f ds


-- * Evaluation for efficiently computing forward derivatives.

fwdGeneral
  :: ADInputs 'ADModeDerivative r
  -> (ADInputs 'ADModeDerivative r -> ADVal 'ADModeDerivative a)
  -> (Dual 'ADModeDerivative a, a)
{-# INLINE fwdGeneral #-}
fwdGeneral inputs f =
  let D v d = f inputs
  in (d, v)

-- JVP (jacobian-vector product) or Rop (right operation) are alternative
-- names, but newbies may have trouble understanding it.
-- The direction vector ds is taken as an extra argument.
--
-- The type equality constraint is needed, because the `Dual` type family
-- can't declare it, because it needs to remain injective.
fwdFun
  :: (Numeric r, Dual 'ADModeDerivative r ~ r)
  => Domains r
  -> (ADInputs 'ADModeDerivative r -> ADVal 'ADModeDerivative a)
  -> Domains r  -- ds
  -> (Dual 'ADModeDerivative a, a)
fwdFun parameters f (params0, params1) =
  let inputs =
        makeADInputs
          parameters
          (V.convert params0, params1)  -- ds
  in fwdGeneral inputs f


-- * Additional mechanisms

prettyPrintDf
  :: HasDelta r
  => (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> String
prettyPrintDf f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
      !(D _ deltaTopLevel) = f inputs
  in ppShow deltaTopLevel

generateDeltaInputs
  :: forall r. ADModeAndNum 'ADModeGradient r
  => Domains r
  -> ( Data.Vector.Vector (Dual 'ADModeGradient r)
     , Data.Vector.Vector (Dual 'ADModeGradient (Vector r)) )
generateDeltaInputs (params0, params1) =
  let intToInput :: forall a v.
                    (IsPrimalAndHasFeatures 'ADModeGradient a r, V.Vector v a)
                 => v a -> Data.Vector.Vector (Dual 'ADModeGradient a)
      intToInput p = V.generate (V.length p) (dInput . toInputId)
      !v0 = intToInput params0
      !v1 = intToInput params1
  in (v0, v1)
{-# SPECIALIZE generateDeltaInputs
  :: Domains Double
  -> ( Data.Vector.Vector (Dual 'ADModeGradient Double)
     , Data.Vector.Vector (Dual 'ADModeGradient (Vector Double)) ) #-}

-- | Initialize parameters using a uniform distribution with a fixed range
-- taken from an argument.
--
-- Must be Double, because @randomVector@ only works on that.
--
-- This only works fine for nets with levels that have similar size and use
-- the same activation function. Otherwise, the range should vary per level.
-- A rule of thumb range for weights is @sqrt(6 / (F_in + F_out)@,
-- where @F_in + F_out@ is the sum of inputs and outputs of the largest level.
-- See https://github.com/pytorch/pytorch/issues/15314 and their newer code.
initializerFixed :: Int -> Double -> (Int, [Int])
                 -> ((Int, Int), Int, Double, Domains Double)
initializerFixed seed range (nParams0, lParams1) =
  let vParams1 = V.fromList lParams1
      createRandomVector n seedV =
        HM.scale (2 * range)
        $ HM.randomVector seedV HM.Uniform n - HM.scalar 0.5
      params0Init = createRandomVector nParams0 seed
      params1Init =
        V.imap (\i nPV -> createRandomVector nPV (seed + nPV + i)) vParams1
      totalParams = nParams0
                    + V.sum vParams1
  in ( (nParams0, V.length vParams1)
     , totalParams
     , range
     , (params0Init, params1Init) )
