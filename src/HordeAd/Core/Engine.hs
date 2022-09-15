{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilies #-}
-- | The implementation of calculating gradient, derivative and value
-- of an objective function defined on dual numbers, as defined
-- in "HordeAd.Core.DualNumber". Together with that module, this forms
-- the basic high-level API of the horde-ad library. Optimizers, etc.,
-- are add-ons.
module HordeAd.Core.Engine
  ( -- * The most often used part of the high-level API
    revFun, fwdFun, valueFun
  , -- * The less often used part of the high-level API
    revIO, valueGeneral
  , -- * Operations exposed not for the library users but add-on makers
    revGeneral, fwdGeneral
  , generateDeltaInputs, initializerFixed
  , -- * Internal operations, exposed, e.g., for tests
    dForwardGeneral, dForward, dForwardFun
  , prettyPrintDf
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM
import           Text.Show.Pretty (ppShow)

-- import           System.Mem (performMinorGC)

import HordeAd.Core.DualClass
  (Dual, IsPrimal (..), IsPrimalAndHasFeatures, dInput)
import HordeAd.Core.DualNumber
import HordeAd.Core.PairOfVectors (ADInputs (..), makeADInputs)
import HordeAd.Internal.Delta
  (derivativeFromDelta, gradientFromDelta, toInputId)

-- * Evaluation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

-- The general case, needed for old hacky tests using only scalars.
valueGeneral
  :: forall r a. ADModeAndNum 'ADModeValue r
  => (ADInputs 'ADModeValue r -> a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueGeneral #-}
valueGeneral f (params0, params1, params2, paramsX) =
  let replicateZeros p = V.replicate (V.length p) dZero
      inputs = makeADInputs
                    (params0, params1, params2, paramsX)
                    ( replicateZeros params0  -- dummy
                    , replicateZeros params1
                    , replicateZeros params2
                    , replicateZeros paramsX )
  in f inputs

valueFun
  :: forall r a. ADModeAndNum 'ADModeValue r
  => (ADInputs 'ADModeValue r -> ADVal 'ADModeValue a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueFun #-}
valueFun f parameters =
  let D v _ = valueGeneral f parameters
  in v


-- * The fully-fledged evaluation for gradients.

revGeneralFun
  :: forall r. HasDelta r
  => r
  -> ADInputs 'ADModeGradient r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> (Domains r, r)
-- The functions in which @revGeneral@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revGeneralFun #-}
revGeneralFun dt inputs@ADInputs{..} f =
  let dim0 = V.length inputPrimal0
      dim1 = V.length inputPrimal1
      dim2 = V.length inputPrimal2
      dimX = V.length inputPrimalX
      -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started
      !(D v deltaTopLevel) = f inputs
  in let gradient = gradientFromDelta dim0 dim1 dim2 dimX deltaTopLevel dt
     in (gradient, v)

-- Tests expect this to be in IO by historical accident.
-- But we can possibly add hacks here in the future, such as @performMinorGC@.
revGeneral
  :: forall r. HasDelta r
  => r
  -> ADInputs 'ADModeGradient r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> IO (Domains r, r)
{-# INLINE revGeneral #-}
revGeneral dt inputs f = return $! revGeneralFun dt inputs f

-- jvp (jacobian-vector product) is an alternative name, but newbies
-- might have trouble understanding it.
revFun
  :: HasDelta r
  => r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> (Domains r, r)
revFun dt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in revGeneralFun dt inputs f

revIO
  :: HasDelta r
  => r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> IO (Domains r, r)
revIO dt f parameters = return $! revFun dt f parameters


-- * The slow evaluation for derivatives that uses the same
-- delta expressions as for gradients. See @fwdGeneral@
-- for an efficient variant.

dForwardGeneralFun
  :: forall r. HasDelta r
  => ADInputs 'ADModeGradient r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> (r, r)
{-# INLINE dForwardGeneralFun #-}
dForwardGeneralFun inputs@ADInputs{..} f ds =
  let dim0 = V.length inputPrimal0
      dim1 = V.length inputPrimal1
      dim2 = V.length inputPrimal2
      dimX = V.length inputPrimalX
      !(D v deltaTopLevel) = f inputs
  in let derivative = derivativeFromDelta dim0 dim1 dim2 dimX deltaTopLevel ds
     in (derivative, v)

dForwardGeneral
  :: forall r. HasDelta r
  => ADInputs 'ADModeGradient r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> IO (r, r)
{-# INLINE dForwardGeneral #-}
dForwardGeneral inputs f ds = return $! dForwardGeneralFun inputs f ds

-- The direction vector ds is taken as an extra argument.
dForwardFun
  :: HasDelta r
  => (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> Domains r
  -> (r, r)
dForwardFun f parameters ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in dForwardGeneralFun inputs f ds

dForward
  :: HasDelta r
  => (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> Domains r
  -> IO (r, r)
dForward f parameters ds = return $! dForwardFun f parameters ds


-- * The evaluation for efficiently computing forward derivatives.

fwdGeneral
  :: Dual 'ADModeDerivative r ~ r
  => ADInputs 'ADModeDerivative r
  -> (ADInputs 'ADModeDerivative r -> ADVal 'ADModeDerivative r)
  -> (r, r)
{-# INLINE fwdGeneral #-}
fwdGeneral inputs f =
  let D v d = f inputs
  in (d, v)

-- The direction vector ds is taken as an extra argument.
fwdFun
  :: forall r. (Numeric r, Dual 'ADModeDerivative r ~ r)
  => (ADInputs 'ADModeDerivative r -> ADVal 'ADModeDerivative r)
  -> Domains r
  -> Domains r
  -> (r, r)
fwdFun f parameters (params0, params1, params2, paramsX) =
  let inputs =
        makeADInputs
          parameters
          (V.convert params0, params1, params2, paramsX)  -- ds
  in fwdGeneral inputs f


-- * Additional mechanisms

prettyPrintDf
  :: forall r. HasDelta r
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
  let intToInput
        :: forall a v. (IsPrimalAndHasFeatures 'ADModeGradient a r, V.Vector v a)
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
-- A rule of thumb range for weights is @sqrt(6 / (F_in + F_out)@,
-- where @F_in + F_out@ is the sum of inputs and outputs of the largest level.
-- See https://github.com/pytorch/pytorch/issues/15314 and their newer code.
initializerFixed :: Int -> Double -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
                 -> ((Int, Int, Int, Int), Int, Double, Domains Double)
initializerFixed seed range (nParams0, lParams1, lParams2, lParamsX) =
  let vParams1 = V.fromList lParams1
      vParams2 = V.fromList lParams2
      vParamsX = V.fromList lParamsX
      createRandomVector n seedV =
        HM.scale (2 * range)
        $ HM.randomVector seedV HM.Uniform n - HM.scalar 0.5
      params0Init = createRandomVector nParams0 seed
      params1Init =
        V.imap (\i nPV -> createRandomVector nPV (seed + nPV + i)) vParams1
      params2Init =
        V.imap (\i (rows, cols) ->
                 HM.reshape cols
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
