{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             TypeFamilies #-}
-- | Several implementations of the monad in which our dual numbers live
-- and implementations of calculating gradient, derivative and value
-- of an objective function defined on dual numbers.
module HordeAd.Core.Engine
  ( DualMonadValue, primalValueGeneral, primalValue
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
  (Dual, IsPrimal (..), IsPrimalWithScalar, bindInState, dVar)
import HordeAd.Core.DualNumber
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)
import HordeAd.Internal.Delta
  ( CodeOut (..)
  , DeltaState (..)
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

instance IsScalar 'DModeValue r
         => DualMonad 'DModeValue r (DualMonadValue r) where
  returnLet (D u _u') = DualMonadValue $ Identity $ D u dZero

-- The general case, needed for old, hacky tests using only scalars.
primalValueGeneral
  :: forall r a. IsScalar 'DModeValue r
  => (DualNumberVariables 'DModeValue r
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
  :: forall r a. IsScalar 'DModeValue r
  => (DualNumberVariables 'DModeValue r
      -> DualMonadValue r (DualNumber 'DModeValue a))
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

instance IsScalar 'DModeGradient r
         => DualMonad 'DModeGradient
                      r (DualMonadGradient r) where
  returnLet (D u u') = DualMonadGradient $ do
    st <- get
    let (!stNew, !dId) = bindInState u' st
    put stNew
    return $! D u (dVar dId)

initializeState :: forall r. IsScalar 'DModeGradient r
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
  -> DualNumberVariables 'DModeGradient r
  -> (DualNumberVariables 'DModeGradient r
      -> DualMonadGradient r (DualNumber 'DModeGradient r))
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
      initialState = initializeState (params0, params1, params2, paramsX)
      (D value d, st) = runState (runDualMonadGradient (f variables))
                                 initialState
      inlineDerivative primCode primalArgs dualArgs =
        let D _ u' = outDualNumber primCode primalArgs dualArgs
        in u'
      gradient =
        gradientFromDelta inlineDerivative inlineDerivative inlineDerivative
                          inlineDerivative inlineDerivative
                          dim0 dim1 dim2 dimX st d dt
  in (gradient, value)

dReverse :: HasDelta r
   => r
   -> (DualNumberVariables 'DModeGradient r
       -> DualMonadGradient r (DualNumber 'DModeGradient r))
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
  => DualNumberVariables 'DModeGradient r
  -> (DualNumberVariables 'DModeGradient r
      -> DualMonadGradient r (DualNumber 'DModeGradient r))
  -> Domains r
  -> (r, r)
{-# INLINE dForwardGeneral #-}
dForwardGeneral variables@(params0, _, params1, _, params2, _, paramsX, _)
                f ds =
  let initialState = initializeState (params0, params1, params2, paramsX)
      (D value d, st) = runState (runDualMonadGradient (f variables))
                                 initialState
      inlineDerivative primCode primalArgs dualArgs =
        let D _ u' = outDualNumber primCode primalArgs dualArgs
        in u'
  in ( derivativeFromDelta inlineDerivative inlineDerivative inlineDerivative
                           inlineDerivative inlineDerivative
                           st d ds
     , value )

-- The direction vector ds is taken as an extra argument.
dForward
  :: HasDelta r
  => (DualNumberVariables 'DModeGradient r
      -> DualMonadGradient r (DualNumber 'DModeGradient r))
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

instance IsScalar 'DModeDerivative r
         => DualMonad 'DModeDerivative
                      r (DualMonadForward r) where
  returnLet (D u u') = DualMonadForward $ Identity $ D u u'

-- This the efficient variant of forward derivative computation.
dFastForwardGeneral
  :: Dual 'DModeDerivative r ~ r
  => DualNumberVariables 'DModeDerivative r
  -> (DualNumberVariables 'DModeDerivative r
      -> DualMonadForward r (DualNumber 'DModeDerivative r))
  -> (r, r)
{-# INLINE dFastForwardGeneral #-}
dFastForwardGeneral variables f =
  let D value d = runIdentity $ runDualMonadForward $ f variables
  in (d, value)

-- The direction vector ds is taken as an extra argument.
dFastForward
  :: forall r. (Numeric r, Dual 'DModeDerivative r ~ r)
  => (DualNumberVariables 'DModeDerivative r
      -> DualMonadForward r (DualNumber 'DModeDerivative r))
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
  :: forall r. HasDelta r
  => Bool
  -> (DualNumberVariables 'DModeGradient r
      -> DualMonadGradient r (DualNumber 'DModeGradient r))
  -> Domains r
  -> String
prettyPrintDf reversed f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
      initialState = initializeState parameters
      (D _ deltaTopLevel, st) = runState (runDualMonadGradient (f variables))
                                         initialState
  in ppBindings reversed st deltaTopLevel

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

outDualNumber :: (IsPrimal d a, RealFloat a, Show a, Show (Dual d a))
              => CodeOut -> [a] -> [Dual d a]
              -> DualNumber d a
outDualNumber PlusOut [u, v] [u', v'] = D u u' + D v v'
outDualNumber MinusOut [u, v] [u', v'] = D u u' - D v v'
outDualNumber TimesOut [u, v] [u', v'] = D u u' * D v v'
outDualNumber NegateOut [u] [u'] = negate $ D u u'
outDualNumber AbsOut [u] [u'] = abs $ D u u'
outDualNumber SignumOut [u] [u'] = signum $ D u u'
outDualNumber DivideOut [u, v] [u', v'] = D u u' / D v v'
outDualNumber RecipOut [u] [u'] = recip $ D u u'
outDualNumber ExpOut [u] [u'] = exp $ D u u'
outDualNumber LogOut [u] [u'] = log $ D u u'
outDualNumber SqrtOut [u] [u'] = sqrt $ D u u'
outDualNumber PowerOut [u, v] [u', v'] = D u u' ** D v v'
outDualNumber LogBaseOut [u, v] [u', v'] = logBase (D u u') (D v v')
outDualNumber SinOut [u] [u'] = sin $ D u u'
outDualNumber CosOut [u] [u'] = cos $ D u u'
outDualNumber TanOut [u] [u'] = tan $ D u u'
outDualNumber AsinOut [u] [u'] = asin $ D u u'
outDualNumber AcosOut [u] [u'] = acos $ D u u'
outDualNumber AtanOut [u] [u'] = atan $ D u u'
outDualNumber SinhOut [u] [u'] = sinh $ D u u'
outDualNumber CoshOut [u] [u'] = cosh $ D u u'
outDualNumber TanhOut [u] [u'] = tanh $ D u u'
outDualNumber AsinhOut [u] [u'] = asinh $ D u u'
outDualNumber AcoshOut [u] [u'] = acosh $ D u u'
outDualNumber AtanhOut [u] [u'] = atanh $ D u u'
outDualNumber Atan2Out [u, v] [u', v'] = atan2 (D u u') (D v v')
outDualNumber primCode primalArgs dualArgs =
  error $ "outDualNumber: wrong number of arguments"
          ++ show (primCode, primalArgs, dualArgs)
