{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilies #-}
-- | Several implementations of the monad in which our dual numbers live
-- and implementations of calculating gradient, derivative and value
-- of an objective function defined on dual numbers.
module HordeAd.Core.Engine
  ( primalValueGeneral, primalValue
  , dReverseGeneral, dReverse
  , dForwardGeneral, dForward
  , dFastForwardGeneral, dFastForward
  , prettyPrintDf
  , generateDeltaInputs, initializerFixed
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
import HordeAd.Core.PairOfVectors (DualNumberInputs (..), makeDualNumberInputs)
import HordeAd.Internal.Delta
  (derivativeFromDelta, gradientFromDelta, toDeltaId)

-- * Evaluation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

-- The general case, needed for old hacky tests using only scalars.
primalValueGeneral
  :: forall r a. IsScalar 'DModeValue r
  => (DualNumberInputs 'DModeValue r -> a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE primalValueGeneral #-}
primalValueGeneral f (params0, params1, params2, paramsX) =
  let replicateZeros p = V.replicate (V.length p) dZero
      inputs = makeDualNumberInputs
                    (params0, params1, params2, paramsX)
                    ( replicateZeros params0  -- dummy
                    , replicateZeros params1
                    , replicateZeros params2
                    , replicateZeros paramsX )
  in f inputs

primalValue
  :: forall r a. IsScalar 'DModeValue r
  => (DualNumberInputs 'DModeValue r -> DualNumber 'DModeValue a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE primalValue #-}
primalValue f parameters =
  let D value _ = primalValueGeneral f parameters
  in value


-- * The fully-fledged evaluation for gradients.

-- This and other functions don't need to be in @IO@; it's a historical
-- accident, but it proves useful for performance hacks, e.g., forcing GC.
dReverseGeneral
  :: forall r. HasDelta r
  => r
  -> DualNumberInputs 'DModeGradient r
  -> (DualNumberInputs 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> IO (Domains r, r)
-- The functions in which @dReverseGeneral@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE dReverseGeneral #-}
dReverseGeneral dt
                inputs@DualNumberInputs{..} f = do
  let dim0 = V.length inputPrimal0
      dim1 = V.length inputPrimal1
      dim2 = V.length inputPrimal2
      dimX = V.length inputPrimalX
      -- Evaluate completely after terms constructed, to free memory before
      -- before evaluation allocates new memory and new FFI is started
      !(D value deltaTopLevel) = f inputs
  -- Uncomment for benchmarks to make GC more predictable and so
  -- benchmark results less random. This slows down parallel tests much
  -- more than sequential benchmarks.
--  performMinorGC
  let gradient = gradientFromDelta dim0 dim1 dim2 dimX deltaTopLevel dt
  return (gradient, value)

dReverse
  :: HasDelta r
  => r
  -> (DualNumberInputs 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> Domains r
  -> IO (Domains r, r)
dReverse dt f parameters = do
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeDualNumberInputs parameters deltaInputs
  dReverseGeneral dt inputs f


-- * The slow evaluation for derivatives that uses the same
-- delta expressions as for gradients. See @dFastForwardGeneral@
-- for an efficient variant.

dForwardGeneral
  :: forall r. HasDelta r
  => DualNumberInputs 'DModeGradient r
  -> (DualNumberInputs 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> Domains r
  -> IO (r, r)
{-# INLINE dForwardGeneral #-}
dForwardGeneral inputs@DualNumberInputs{..} f ds = do
  let dim0 = V.length inputPrimal0
      dim1 = V.length inputPrimal1
      dim2 = V.length inputPrimal2
      dimX = V.length inputPrimalX
      !(D value deltaTopLevel) = f inputs
  let derivative = derivativeFromDelta dim0 dim1 dim2 dimX deltaTopLevel ds
  return (derivative, value)

-- The direction vector ds is taken as an extra argument.
dForward
  :: HasDelta r
  => (DualNumberInputs 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> Domains r
  -> Domains r
  -> IO (r, r)
dForward f parameters ds = do
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeDualNumberInputs parameters deltaInputs
  dForwardGeneral inputs f ds

-- * The evaluation for efficiently computing forward derivatives.

dFastForwardGeneral
  :: Dual 'DModeDerivative r ~ r
  => DualNumberInputs 'DModeDerivative r
  -> (DualNumberInputs 'DModeDerivative r -> DualNumber 'DModeDerivative r)
  -> (r, r)
{-# INLINE dFastForwardGeneral #-}
dFastForwardGeneral inputs f =
  let D value d = f inputs
  in (d, value)

-- The direction vector ds is taken as an extra argument.
dFastForward
  :: forall r. (Numeric r, Dual 'DModeDerivative r ~ r)
  => (DualNumberInputs 'DModeDerivative r -> DualNumber 'DModeDerivative r)
  -> Domains r
  -> Domains r
  -> (r, r)
dFastForward f parameters (params0, params1, params2, paramsX) =
  let inputs =
        makeDualNumberInputs
          parameters
          (V.convert params0, params1, params2, paramsX)  -- ds
  in dFastForwardGeneral inputs f


-- * Additional mechanisms

prettyPrintDf
  :: forall r. HasDelta r
  => (DualNumberInputs 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> Domains r
  -> IO String
prettyPrintDf f parameters = do
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeDualNumberInputs parameters deltaInputs
      !(D _ deltaTopLevel) = f inputs
  return $! ppShow deltaTopLevel

generateDeltaInputs
  :: forall r. IsScalar 'DModeGradient r
  => Domains r
  -> ( Data.Vector.Vector (Dual 'DModeGradient r)
     , Data.Vector.Vector (Dual 'DModeGradient (Vector r))
     , Data.Vector.Vector (Dual 'DModeGradient (Matrix r))
     , Data.Vector.Vector (Dual 'DModeGradient (OT.Array r)) )
generateDeltaInputs (params0, params1, params2, paramsX) =
  let intToInput
        :: forall a v. (IsPrimalAndHasFeatures 'DModeGradient a r, V.Vector v a)
        => v a -> Data.Vector.Vector (Dual 'DModeGradient a)
      intToInput p = V.generate (V.length p) (dInput . toDeltaId)
      !v0 = intToInput params0
      !v1 = intToInput params1
      !v2 = intToInput params2
      !vX = intToInput paramsX
  in (v0, v1, v2, vX)
{-# SPECIALIZE generateDeltaInputs
  :: Domains Double
  -> ( Data.Vector.Vector (Dual 'DModeGradient Double)
     , Data.Vector.Vector (Dual 'DModeGradient (Vector Double))
     , Data.Vector.Vector (Dual 'DModeGradient (Matrix Double))
     , Data.Vector.Vector (Dual 'DModeGradient (OT.Array Double)) ) #-}

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
