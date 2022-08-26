{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             TypeFamilies #-}
-- Needed due to unsafePerformIO:
{-# OPTIONS_GHC -fno-full-laziness #-}
-- | Several implementations of the monad in which our dual numbers live
-- and implementations of calculating gradient, derivative and value
-- of an objective function defined on dual numbers.
module HordeAd.Core.Engine
  ( primalValueGeneral, primalValue
  , dReverseGeneral, dReverse
  , dForwardGeneral, dForward
  , dFastForwardGeneral, dFastForward
  , prettyPrintDf
  , generateDeltaVars, initializerFixed
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import           Data.Functor (void)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM
import           Text.Show.Pretty (ppShow)

import HordeAd.Core.DualClass
  ( Dual
  , IsPrimal (..)
  , IsPrimalWithScalar
  , dVar
  , finalizeCounters
  , initializeCounters
  )
import HordeAd.Core.DualNumber
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)
import HordeAd.Internal.Delta
  (derivativeFromDelta, gradientFromDelta, toDeltaId)

-- * Evaluation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

-- The general case, needed for old hacky tests using only scalars.
primalValueGeneral
  :: forall r a. IsScalar 'DModeValue r
  => (DualNumberVariables 'DModeValue r -> a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE primalValueGeneral #-}
primalValueGeneral f (params0, params1, params2, paramsX) =
  let replicateZeros p = V.replicate (V.length p) dZero
      variables = makeDualNumberVariables
                    (params0, params1, params2, paramsX)
                    ( replicateZeros params0  -- dummy
                    , replicateZeros params1
                    , replicateZeros params2
                    , replicateZeros paramsX )
  in f variables

primalValue
  :: forall r a. IsScalar 'DModeValue r
  => (DualNumberVariables 'DModeValue r -> DualNumber 'DModeValue a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE primalValue #-}
primalValue f parameters =
  let D value _ = primalValueGeneral f parameters
  in value


-- * The fully-fledged evaluation for gradients.

dReverseGeneral
  :: forall r. HasDelta r
  => r
  -> DualNumberVariables 'DModeGradient r
  -> (DualNumberVariables 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> IO (Domains r, r)
-- The functions in which @dReverseGeneral@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE dReverseGeneral #-}
dReverseGeneral dt
                variables@(params0, _, params1, _, params2, _, paramsX, _)
                f = do
  let dim0 = V.length params0
      dim1 = V.length params1
      dim2 = V.length params2
      dimX = V.length paramsX
  initializeCounters dim0 dim1 dim2 dimX
  let -- It needs to be fully evaluated before finalizing the counters,
      -- because it modifies the counters (via impure side-effect):
      !(D !value !d) = f variables
  counters <- finalizeCounters
  let gradient = gradientFromDelta dim0 dim1 dim2 dimX counters d dt
  return (gradient, value)

dReverse
  :: HasDelta r
  => r
  -> (DualNumberVariables 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> Domains r
  -> IO (Domains r, r)
dReverse dt f parameters = do
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  dReverseGeneral dt variables f


-- * The fully-fledged but slow evaluation for derivatives that uses
-- the same delta expressions as for gradients. See @dFastForwardGeneral@
-- for an efficient variant.
dForwardGeneral
  :: forall r. HasDelta r
  => DualNumberVariables 'DModeGradient r
  -> (DualNumberVariables 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> Domains r
  -> IO (r, r)
{-# INLINE dForwardGeneral #-}
dForwardGeneral variables@(params0, _, params1, _, params2, _, paramsX, _)
                f ds = do
  let dim0 = V.length params0
      dim1 = V.length params1
      dim2 = V.length params2
      dimX = V.length paramsX
  initializeCounters dim0 dim1 dim2 dimX
  let -- It needs to be fully evaluated before finalizing the counters,
      -- because it modifies the counters (via impure side-effect):
      !(D !value !d) = f variables
  counters <- finalizeCounters
  let derivative = derivativeFromDelta dim0 dim1 dim2 dimX counters d ds
  return (derivative, value)

-- The direction vector ds is taken as an extra argument.
dForward
  :: HasDelta r
  => (DualNumberVariables 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> Domains r
  -> Domains r
  -> IO (r, r)
dForward f parameters ds = do
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  dForwardGeneral variables f ds

-- * The evaluation for efficiently computing forward derivatives.

dFastForwardGeneral
  :: Dual 'DModeDerivative r ~ r
  => DualNumberVariables 'DModeDerivative r
  -> (DualNumberVariables 'DModeDerivative r -> DualNumber 'DModeDerivative r)
  -> (r, r)
{-# INLINE dFastForwardGeneral #-}
dFastForwardGeneral variables f =
  let D value d = f variables
  in (d, value)

-- The direction vector ds is taken as an extra argument.
dFastForward
  :: forall r. (Numeric r, Dual 'DModeDerivative r ~ r)
  => (DualNumberVariables 'DModeDerivative r -> DualNumber 'DModeDerivative r)
  -> Domains r
  -> Domains r
  -> (r, r)
dFastForward f parameters (params0, params1, params2, paramsX) =
  let variables =
        makeDualNumberVariables
          parameters
          (V.convert params0, params1, params2, paramsX)  -- ds
  in dFastForwardGeneral variables f


-- * Additional mechanisms

prettyPrintDf
  :: forall r. HasDelta r
  => (DualNumberVariables 'DModeGradient r -> DualNumber 'DModeGradient r)
  -> Domains r
  -> IO String
prettyPrintDf f parameters@(params0, params1, params2, paramsX) = do
  let dim0 = V.length params0
      dim1 = V.length params1
      dim2 = V.length params2
      dimX = V.length paramsX
  initializeCounters dim0 dim1 dim2 dimX
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
      D _ deltaTopLevel = f variables
      s = ppShow deltaTopLevel
      -- It needs to be fully evaluated before finalizing the counters,
      -- because it modifies the counters (via impure side-effect):
      !_ = length s
  void finalizeCounters
  return s

generateDeltaVars
  :: forall r. IsScalar 'DModeGradient r
  => Domains r
  -> ( Data.Vector.Vector (Dual 'DModeGradient r)
     , Data.Vector.Vector (Dual 'DModeGradient (Vector r))
     , Data.Vector.Vector (Dual 'DModeGradient (Matrix r))
     , Data.Vector.Vector (Dual 'DModeGradient (OT.Array r)) )
generateDeltaVars (params0, params1, params2, paramsX) =
  let vVar :: forall a v. (IsPrimalWithScalar 'DModeGradient a r, V.Vector v a)
           => v a -> Data.Vector.Vector (Dual 'DModeGradient a)
      vVar p = V.generate (V.length p) (dVar . toDeltaId)
      !v0 = vVar params0
      !v1 = vVar params1
      !v2 = vVar params2
      !vX = vVar paramsX
  in (v0, v1, v2, vX)
{-# SPECIALIZE generateDeltaVars
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
