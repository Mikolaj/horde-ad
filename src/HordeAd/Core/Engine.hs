{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             TypeFamilies #-}
-- | Several implementations of the monad in which our dual numbers live
-- and implementations of calculating gradient, derivative and value
-- of an objective function defined on dual numbers.
module HordeAd.Core.Engine
  ( Domain0, Domain1, Domain2, DomainX, Domains
  , DualMonadValue, primalValueGeneral, primalValue
  , DualMonadGradient, dReverseGeneral, dReverse, dForwardGeneral, dForward, prettyPrintDf
  , DualMonadForward, dFastForwardGeneral, dFastForward
  , generateDeltaVars, initializerFixed
  ) where

import Prelude

import           Control.Monad.Trans.State.Strict
import qualified Data.Array.DynamicS as OT
import           Data.Functor.Identity
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Core.DualClass
  ( DifferentiationScheme (..)
  , Dual
  , HasVariables (bindInState, dVar)
  , IsDual (..)
  )
import HordeAd.Core.DualNumber
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)
import HordeAd.Internal.Delta
  ( DeltaState (..)
  , derivativeFromDelta
  , gradientFromDelta
  , ppBindings
  , toDeltaId
  )

-- * The dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

-- An overcomplicated
-- @type DualMonadValue r = Identity@
-- to avoid @-Wno-orphans@ and @UndecidableInstances@.
newtype DualMonadValue r a = DualMonadValue
  { runDualMonadValue :: Identity a }
  deriving (Monad, Functor, Applicative)

instance IsScalar 'DifferentiationSchemeGradient r
         => DualMonad 'DifferentiationSchemeGradient r (DualMonadValue r) where
  returnLet (D u _u') = DualMonadValue $ Identity $ D u dZero

-- The general case, needed for old, hacky tests using only scalars.
primalValueGeneral
  :: forall r a. IsScalar 'DifferentiationSchemeGradient r
  => (DualNumberVariables 'DifferentiationSchemeGradient r
      -> DualMonadValue r a)
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
  in runIdentity $ runDualMonadValue $ f variables

primalValue
  :: forall r a. IsScalar 'DifferentiationSchemeGradient r
  => (DualNumberVariables 'DifferentiationSchemeGradient r
      -> DualMonadValue r (DualNumber 'DifferentiationSchemeGradient a))
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE primalValue #-}
primalValue f parameters =
  let D value _ = primalValueGeneral f parameters
  in value


-- * The fully-fledged monad implementation for gradients
-- and the code that uses it to compute gradients and also derivatives.

newtype DualMonadGradient r a = DualMonadGradient
  { runDualMonadGradient :: State (DeltaState r) a }
  deriving (Monad, Functor, Applicative)

instance IsScalar 'DifferentiationSchemeGradient r
         => DualMonad 'DifferentiationSchemeGradient
                      r (DualMonadGradient r) where
  returnLet
    :: forall a. HasVariables a r
    => DualNumber 'DifferentiationSchemeGradient a
    -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient a)
  returnLet (D u u') = DualMonadGradient $ do
    st <- get
    let (!stNew, !dId) = bindInState u' st
    put stNew
    return $! D u (dVar @a @r dId)

initializeState :: forall r. IsScalar 'DifferentiationSchemeGradient r
                => Domains r -> DeltaState r
initializeState (params0, params1, params2, paramsX) =
  DeltaState { deltaCounter0 = toDeltaId (V.length params0)
             , deltaCounter1 = toDeltaId (V.length params1)
             , deltaCounter2 = toDeltaId (V.length params2)
             , deltaCounterX = toDeltaId (V.length paramsX)
             , deltaBindings = []
             }

dReverseGeneral
  :: forall r. HasDelta r
  => r
  -> DualNumberVariables 'DifferentiationSchemeGradient r
  -> (DualNumberVariables 'DifferentiationSchemeGradient r
      -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
  -> (Domains r, r)
-- The functions in which @dReverseGeneral@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE dReverseGeneral #-}
dReverseGeneral dt
                variables@(params0, _, params1, _, params2, _, paramsX, _)
                f =
  let dim0 = V.length params0
      dim1 = V.length params1
      dim2 = V.length params2
      dimX = V.length paramsX
      initialState = initializeState @r (params0, params1, params2, paramsX)
      (D value d, st) = runState (runDualMonadGradient (f variables))
                                 initialState
      gradient = gradientFromDelta dim0 dim1 dim2 dimX st d dt
  in (gradient, value)

dReverse :: HasDelta r
   => r
   -> (DualNumberVariables 'DifferentiationSchemeGradient r
       -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
   -> Domains r
   -> (Domains r, r)
dReverse dt f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in dReverseGeneral dt variables f

-- This function uses @DualMonadGradient@ for an inefficient computation
-- of forward derivaties. See @dFastForwardGeneral@ for an efficient variant.
dForwardGeneral
  :: forall r. HasDelta r
  => DualNumberVariables 'DifferentiationSchemeGradient r
  -> (DualNumberVariables 'DifferentiationSchemeGradient r
      -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
  -> Domains r
  -> (r, r)
{-# INLINE dForwardGeneral #-}
dForwardGeneral variables@(params0, _, params1, _, params2, _, paramsX, _)
                f ds =
  let initialState = initializeState @r (params0, params1, params2, paramsX)
      (D value d, st) = runState (runDualMonadGradient (f variables))
                                 initialState
  in (derivativeFromDelta st d ds, value)

-- The direction vector ds is taken as an extra argument.
dForward
  :: HasDelta r
  => (DualNumberVariables 'DifferentiationSchemeGradient r
      -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
  -> Domains r
  -> Domains r
  -> (r, r)
dForward f parameters ds =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in dForwardGeneral variables f ds


-- * A monad for efficiently computing forward derivatives.

newtype DualMonadForward r a = DualMonadForward
  { runDualMonadForward :: Identity a }
  deriving (Monad, Functor, Applicative)

instance IsScalar 'DifferentiationSchemeDerivative r
         => DualMonad 'DifferentiationSchemeDerivative
                      r (DualMonadForward r) where
  returnLet (D u u') = DualMonadForward $ Identity $ D u u'

-- This the efficient variant of forward derivative computation.
dFastForwardGeneral
  :: Dual 'DifferentiationSchemeDerivative r ~ r
  => DualNumberVariables 'DifferentiationSchemeDerivative r
  -> (DualNumberVariables 'DifferentiationSchemeDerivative r
      -> DualMonadForward r (DualNumber 'DifferentiationSchemeDerivative r))
  -> (r, r)
{-# INLINE dFastForwardGeneral #-}
dFastForwardGeneral variables f =
  let D value d = runIdentity $ runDualMonadForward $ f variables
  in (d, value)

-- The direction vector ds is taken as an extra argument.
dFastForward
  :: forall r. (Numeric r, Dual 'DifferentiationSchemeDerivative r ~ r)
  => (DualNumberVariables 'DifferentiationSchemeDerivative r
      -> DualMonadForward r (DualNumber 'DifferentiationSchemeDerivative r))
  -> Domains r
  -> Domains r
  -> (r, r)
dFastForward f parameters (params0, params1, params2, paramsX) =
  let variables =
        makeDualNumberVariables
          parameters
          (V.convert params0, params1, params2, paramsX)  -- ds
      (derivative, value) = dFastForwardGeneral variables f
  in (derivative, value)


-- * Additional mechanisms

prettyPrintDf
  :: forall r. (Show r, HasDelta r)
  => Bool
  -> (DualNumberVariables 'DifferentiationSchemeGradient r
      -> DualMonadGradient r (DualNumber 'DifferentiationSchemeGradient r))
  -> Domains r
  -> String
prettyPrintDf reversed f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
      initialState = initializeState @r parameters
      (D _ deltaTopLevel, st) = runState (runDualMonadGradient (f variables))
                                         initialState
  in ppBindings reversed st deltaTopLevel

generateDeltaVars
  :: forall r. IsScalar 'DifferentiationSchemeGradient r
  => Domains r
  -> ( Data.Vector.Vector (Dual 'DifferentiationSchemeGradient r)
     , Data.Vector.Vector (Dual 'DifferentiationSchemeGradient (Vector r))
     , Data.Vector.Vector (Dual 'DifferentiationSchemeGradient (Matrix r))
     , Data.Vector.Vector (Dual 'DifferentiationSchemeGradient (OT.Array r)) )
generateDeltaVars (params0, params1, params2, paramsX) =
  let vVar :: forall a v. (HasVariables a r, V.Vector v a)
           => v a -> Data.Vector.Vector (Dual 'DifferentiationSchemeGradient a)
      vVar p = V.generate (V.length p) (dVar @a @r . toDeltaId)
      !v0 = vVar params0
      !v1 = vVar params1
      !v2 = vVar params2
      !vX = vVar paramsX
  in (v0, v1, v2, vX)

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
