{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilies #-}
-- | The implementation of calculating gradient, derivative and value
-- of an objective function defined on dual numbers, as defined
-- in "HordeAd.Core.DualNumber". Together with that module, this forms
-- the basic high-level API of the horde-ad library. Optimizers, etc.,
-- are add-ons.
module HordeAd.Core.Engine
  ( -- * The most often used part of the high-level API
    revOnDomains, fwdOnDomains, valueOnDomains
  , -- * The less often used part of the high-level API
    valueGeneral
  , -- * Operations exposed not for the library users but add-on makers
    revOnADInputs, fwdOnADInputs
  , generateDeltaInputs, initializerFixed, initializerFixed01
  , -- * Internal operations, exposed, e.g., for tests
    slowFwdOnADInputs, slowFwdOnDomains
  , prettyPrintDf, domainsFrom01, domainsFrom012X, domainsTo01
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Text.Show.Pretty (ppShow)

import HordeAd.Core.DualClass (Dual, dInput, dummyDual, packDeltaDt, pattern D)
import HordeAd.Core.DualNumber
import HordeAd.Core.PairOfVectors (ADInputs (..), makeADInputs)
import HordeAd.Internal.Delta
  (derivativeFromDelta, gradientFromDelta, toInputId)

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
valueGeneral f (params0, params1, params2, paramsX) =
  let replicateDummy p = V.replicate (V.length p) dummyDual
      inputs = makeADInputs (params0, params1, params2, paramsX)
                            ( replicateDummy params0  -- dummy
                            , replicateDummy params1
                            , replicateDummy params2
                            , replicateDummy paramsX )
  in f inputs

valueOnDomains
  :: Numeric r
  => (ADInputs 'ADModeValue r -> ADVal 'ADModeValue a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueOnDomains #-}
valueOnDomains f parameters =
  let D v _ = valueGeneral f parameters
  in v


-- * Evaluation that computes gradients.

revOnADInputs
  :: (HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r)
  => a
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> ADInputs 'ADModeGradient r
  -> (Domains r, a)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs dt f inputs@ADInputs{..} =
  let dim0 = V.length inputPrimal0
      dim1 = V.length inputPrimal1
      dim2 = V.length inputPrimal2
      dimX = V.length inputPrimalX
      -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started
      !(D v deltaTopLevel) = f inputs
      deltaDt = packDeltaDt dt deltaTopLevel
  in let gradient = gradientFromDelta dim0 dim1 dim2 dimX deltaDt
     in (gradient, v)

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newbies may have trouble understanding it.
-- Also, as of now, @revOnDomains@ is restricted to objective functions with
-- codomains comprising of one rank type (either scalar or vector or matrix
-- or tensor; never a tuple of those), while VJP is fully general.
revOnDomains
  :: (HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r)
  => a
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> Domains r
  -> (Domains r, a)
revOnDomains dt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in revOnADInputs dt f inputs


-- * The slow evaluation for derivatives that uses the same
-- delta expressions as for gradients. See @fwdOnDomains@
-- for a fast variant.

slowFwdOnADInputs
  :: HasDelta r
  => ADInputs 'ADModeGradient r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> (r, r)
{-# INLINE slowFwdOnADInputs #-}
slowFwdOnADInputs inputs@ADInputs{..} f ds =
  let dim0 = V.length inputPrimal0
      dim1 = V.length inputPrimal1
      dim2 = V.length inputPrimal2
      dimX = V.length inputPrimalX
      !(D v deltaTopLevel) = f inputs
  in let derivative = derivativeFromDelta dim0 dim1 dim2 dimX deltaTopLevel ds
     in (derivative, v)

-- The direction vector ds is taken as an extra argument.
slowFwdOnDomains
  :: HasDelta r
  => Domains r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> (r, r)
slowFwdOnDomains parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in slowFwdOnADInputs inputs f ds


-- * Evaluation for efficiently computing forward derivatives.

fwdOnADInputs
  :: ADInputs 'ADModeDerivative r
  -> (ADInputs 'ADModeDerivative r -> ADVal 'ADModeDerivative a)
  -> (Dual 'ADModeDerivative a, a)
{-# INLINE fwdOnADInputs #-}
fwdOnADInputs inputs f =
  let D v d = f inputs
  in (d, v)

-- JVP (jacobian-vector product) or Rop (right operation) are alternative
-- names, but newbies may have trouble understanding it.
-- The direction vector ds is taken as an extra argument.
--
-- The type equality constraint is needed, because the `Dual` type family
-- can't declare it, because it needs to remain injective.
fwdOnDomains
  :: (Numeric r, Dual 'ADModeDerivative r ~ r)
  => Domains r
  -> (ADInputs 'ADModeDerivative r -> ADVal 'ADModeDerivative a)
  -> Domains r  -- ds
  -> (Dual 'ADModeDerivative a, a)
fwdOnDomains parameters f (params0, params1, params2, paramsX) =
  let inputs =
        makeADInputs
          parameters
          (V.convert params0, params1, params2, paramsX)  -- ds
  in fwdOnADInputs inputs f


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
     , Data.Vector.Vector (Dual 'ADModeGradient (Vector r))
     , Data.Vector.Vector (Dual 'ADModeGradient (Matrix r))
     , Data.Vector.Vector (Dual 'ADModeGradient (OT.Array r)) )
generateDeltaInputs (params0, params1, params2, paramsX) =
  let intToInput :: forall a v.
                    (IsPrimalAndHasFeatures 'ADModeGradient a r, V.Vector v a)
                 => v a -> Data.Vector.Vector (Dual 'ADModeGradient a)
      intToInput p = V.generate (V.length p) (dInput . toInputId)
      !v0 = intToInput params0
      !v1 = intToInput params1
      !v2 = intToInput params2
      !vX = intToInput paramsX
  in (v0, v1, v2, vX)
{-# SPECIALIZE generateDeltaInputs
  :: Domains Double
  -> ( Data.Vector.Vector (Dual 'ADModeGradient Double)
     , Data.Vector.Vector (Dual 'ADModeGradient (Vector Double))
     , Data.Vector.Vector (Dual 'ADModeGradient (Matrix Double))
     , Data.Vector.Vector (Dual 'ADModeGradient (OT.Array Double)) ) #-}

-- | Initialize parameters using a uniform distribution with a fixed range
-- taken from an argument.
--
-- Must be Double, because @randomVector@ only works on that.
--
-- This only works fine for nets with levels that have similar size and use
-- the same activation function. Otherwise, the range should vary per level.
-- A rule of thumb range for weights is @sqrt(6 / (F_in + F_out))@,
-- where @F_in + F_out@ is the sum of inputs and outputs of the largest level.
-- See https://github.com/pytorch/pytorch/issues/15314 and their newer code.
initializerFixed :: Int -> Double -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
                 -> ((Int, Int, Int, Int), Int, Double, Domains Double)
initializerFixed seed range (nParams0, lParams1, lParams2, lParamsX) =
  let vParams1 = V.fromList lParams1
      vParams2 = V.fromList lParams2
      vParamsX = V.fromList lParamsX
      createRandomVector n seedV =
        LA.scale (2 * range)
        $ LA.randomVector seedV LA.Uniform n - LA.scalar 0.5
      params0Init = createRandomVector nParams0 seed
      params1Init =
        V.imap (\i nPV -> createRandomVector nPV (seed + nPV + i)) vParams1
      params2Init =
        V.imap (\i (rows, cols) ->
                  LA.reshape cols
                  $ createRandomVector (rows * cols) (seed + rows + i)) vParams2
      paramsXInit =
        V.imap (\i sh ->
                  let sz = product sh
                  in OT.fromVector sh
                     $ createRandomVector sz (seed + sz + i)) vParamsX
      totalParams = nParams0
                    + V.sum vParams1
                    + V.sum (V.map (uncurry (*)) vParams2)
                    + V.sum (V.map product vParamsX)
  in ( (nParams0, V.length vParams1, V.length vParams2, V.length vParamsX)
     , totalParams
     , range
     , (params0Init, params1Init, params2Init, paramsXInit) )

initializerFixed01 :: Int -> Double -> (Int, [Int])
                   -> ((Int, Int), Int, Double, Domains Double)
initializerFixed01 seed range (nParams0, lParams1) =
  let ((n0, n1, _, _), totalParams, range2, parameters) =
        initializerFixed seed range (nParams0, lParams1, [], [])
  in ((n0, n1), totalParams, range2, parameters)

-- * Simplified version compatibility shims

domainsFrom01 :: Domain0 r -> Domain1 r -> Domains r
domainsFrom01 params0 params1 = (params0, params1, V.empty, V.empty)

domainsFrom012X :: Domain0 r -> Domain1 r -> Domain2 r -> DomainX r -> Domains r
domainsFrom012X a b c d = (a, b, c, d)

domainsTo01 :: Domains r -> (Domain0 r, Domain1 r)
domainsTo01 (a, b, _, _) = (a, b)
