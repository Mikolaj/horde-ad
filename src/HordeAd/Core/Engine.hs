{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeFamilies,
             UndecidableInstances #-}
-- | Several implementations of the monad in which our dual numbers live
-- and the implementations of calculating a gradient, derivative or value
-- of an objective function defined on dual numbers.
module HordeAd.Core.Engine
  ( Domain0, Domain1, Domain2, DomainX, Domains
  , DualMonadValue, primalValueGeneric, primalValue
  , DualMonadGradient, generalDf, df, generalDforward, dforward, prettyPrintDf
  , DualMonadForward, generalDfastForward, dfastForward
  , generateDeltaVars, initializerFixed
  ) where

import Prelude

import           Control.Monad.Trans.State.Strict
import qualified Data.Array.DynamicS as OT
import           Data.Functor.Identity
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
  (Domain0, Domain1, Domain2, DomainX, Domains, DualMonad (..), DualNumber (..))
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)
import HordeAd.Internal.Delta
  (DeltaState (..), evalBindings, evalBindingsForward, ppBindings, toDeltaId)

-- * The dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

-- An overcomplicated
-- @type DualMonadValue r = Identity@
-- to avoid @-Wno-orphans@ and @UndecidableInstances@.
newtype DualMonadValue r a = DualMonadValue
  { runDualMonadValue :: Identity a }
  deriving (Monad, Functor, Applicative)

-- @UndecidableInstances@ needed anyway due to this constraint.
instance IsScalar r => DualMonad r (DualMonadValue r) where
  returnLet (D u _u') = DualMonadValue $ Identity $ D u dZero

-- The general case, needed for old, hacky tests using only scalars.
primalValueGeneric :: forall r a. IsScalar r
                   => (DualNumberVariables r -> DualMonadValue r a)
                   -> Domains r
                   -> a
-- Small enough that inline won't hurt.
{-# INLINE primalValueGeneric #-}
primalValueGeneric f (params0, params1, params2, paramsX) =
  let replicateZeros p = V.replicate (V.length p) dZero
      variables = makeDualNumberVariables
                    (params0, params1, params2, paramsX)
                    ( replicateZeros params0  -- dummy
                    , replicateZeros params1
                    , replicateZeros params2
                    , replicateZeros paramsX )
  in runIdentity $ runDualMonadValue $ f variables

primalValue :: forall r a. IsScalar r
            => (DualNumberVariables r -> DualMonadValue r (DualNumber a))
            -> Domains r
            -> Primal a
-- Small enough that inline won't hurt.
{-# INLINE primalValue #-}
primalValue f parameters =
  let D value _ = primalValueGeneric f parameters
  in value


-- * The fully-fledged monad implementation for gradients
-- and the code that uses it to compute gradients.

newtype DualMonadGradient r a = DualMonadGradient
  { runDualMonadGradient :: State (DeltaState (Primal r)) a }
  deriving (Monad, Functor, Applicative)

instance IsScalar r => DualMonad r (DualMonadGradient r) where
  returnLet (D u u') = DualMonadGradient $ do
    st <- get
    let (!stNew, !dId) = bindInState u' st
    put stNew
    return $! D u (dVar dId)

initializeState :: forall r. IsScalar r => Domains r -> DeltaState (Primal r)
initializeState (params0, params1, params2, paramsX) =
  DeltaState { deltaCounter0 = toDeltaId (V.length params0)
             , deltaCounter1 = toDeltaId (V.length params1)
             , deltaCounter2 = toDeltaId (V.length params2)
             , deltaCounterX = toDeltaId (V.length paramsX)
             , deltaBindings = []
             }

generalDf :: forall r. HasDelta r
          => DualNumberVariables r
          -> (DualNumberVariables r -> DualMonadGradient r (DualNumber r))
          -> (Domains r, Primal r)
-- The functions in which @generalDf@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE generalDf #-}
generalDf variables@(params0, _, params1, _, params2, _, paramsX, _) f =
  let dim0 = V.length params0
      dim1 = V.length params1
      dim2 = V.length params2
      dimX = V.length paramsX
      initialState = initializeState @r (params0, params1, params2, paramsX)
      (D value d, st) = runState (runDualMonadGradient (f variables))
                                 initialState
      dt = 1  -- fixed for simplicity, but can be overriden
              -- by changing the objective function
      gradient = evalBindings dim0 dim1 dim2 dimX st d dt
  in (gradient, value)

df :: HasDelta r
   => (DualNumberVariables r -> DualMonadGradient r (DualNumber r))
   -> Domains r
   -> (Domains r, Primal r)
df f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in generalDf variables f

-- This function uses @DualMonadGradient@ for an inefficient computation
-- of forward derivaties. See @generalDfastForward@ for an efficient variant.
generalDforward
  :: forall r. HasDelta r
  => DualNumberVariables r
  -> (DualNumberVariables r -> DualMonadGradient r (DualNumber r))
  -> Domains r
  -> (Primal r, Primal r)
{-# INLINE generalDforward #-}
generalDforward variables@(params0, _, params1, _, params2, _, paramsX, _)
                f ds =
  let initialState = initializeState @r (params0, params1, params2, paramsX)
      (D value d, st) = runState (runDualMonadGradient (f variables))
                                 initialState
  in (evalBindingsForward st d ds, value)

-- The direction vector ds is taken as an extra argument.
dforward
  :: HasDelta r
  => (DualNumberVariables r -> DualMonadGradient r (DualNumber r))
  -> Domains r
  -> Domains r
  -> (Primal r, Primal r)
dforward f parameters ds =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in generalDforward variables f ds


-- * A monad for efficiently computing forward derivatives.

newtype DualMonadForward r a = DualMonadForward
  { runDualMonadForward :: Identity a }
  deriving (Monad, Functor, Applicative)

instance IsScalar r => DualMonad r (DualMonadForward r) where
  returnLet (D u u') = DualMonadForward $ Identity $ D u u'

-- This the efficient variant of forward derivative computation.
generalDfastForward
  :: DualNumberVariables r
  -> (DualNumberVariables r -> DualMonadForward r (DualNumber r))
  -> (r, Primal r)
{-# INLINE generalDfastForward #-}
generalDfastForward variables f =
  let D value d = runIdentity $ runDualMonadForward $ f variables
  in (d, value)

-- The direction vector ds is taken as an extra argument.
dfastForward
  :: forall r. HasForward r
  => (DualNumberVariables r -> DualMonadForward r (DualNumber r))
  -> Domains r
  -> Domains r
  -> (Primal r, Primal r)
dfastForward f parameters (params0, params1, params2, paramsX) =
  let variables =
        makeDualNumberVariables
          parameters
          (V.convert params0, params1, params2, paramsX)  -- ds
      (derivative, value) = generalDfastForward variables f
  in (derivative, value)


-- * Additional mechanisms

prettyPrintDf :: forall r. (Show (Primal r), HasDelta r)
              => Bool
              -> (DualNumberVariables r -> DualMonadGradient r (DualNumber r))
              -> Domains r
              -> String
prettyPrintDf reversed f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
      initialState = initializeState @r parameters
      (D _ deltaTopLevel, st) = runState (runDualMonadGradient (f variables))
                                         initialState
  in ppBindings reversed st deltaTopLevel

generateDeltaVars :: IsScalar r
                  => Domains r
                  -> ( Data.Vector.Vector r
                     , Data.Vector.Vector (Tensor1 r)
                     , Data.Vector.Vector (Tensor2 r)
                     , Data.Vector.Vector (TensorX r) )
generateDeltaVars (params0, params1, params2, paramsX) =
  let vVar p = V.generate (V.length p) (dVar . toDeltaId)
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
