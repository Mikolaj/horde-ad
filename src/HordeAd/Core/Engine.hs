{-# LANGUAGE ConstraintKinds, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TypeFamilies, UndecidableInstances #-}
-- | Two implementations of the monad in which our dual numbers live
-- and the implementation of deriving a gradient.
module HordeAd.Core.Engine
  ( Domain, DomainV, DomainL, DomainX, Domains
  , DeltaMonadValue, primalValueGeneric, primalValue
  , DeltaMonadGradient, generalDf, df, generalDforward, dforward, prettyPrintDf
  , DeltaMonadForward, generalDfastForward, dfastForward
  , generateDeltaVars, initializerFixed
  ) where

import Prelude

import           Control.Monad.Trans.State.Strict
import           Data.Functor.Identity
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM
import           Text.Show.Pretty (ppShow)

import HordeAd.Core.Delta
  (DeltaState (..), evalBindings, evalBindingsForward, ppBinding, toDeltaId)
import HordeAd.Core.DualNumber
  (DeltaMonad (..), Domain, DomainL, DomainV, DomainX, Domains, DualNumber (..))
import HordeAd.Core.DualClass
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- * The dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

-- An overcomplicated
-- @type DeltaMonadValue r = Identity@
-- to avoid @-Wno-orphans@ and @UndecidableInstances@.
newtype DeltaMonadValue r a = DeltaMonadValue
  { runDeltaMonadValue :: Identity a }
  deriving (Monad, Functor, Applicative)

-- @UndecidableInstances@ needed due to this constraint.
instance IsScalar r => DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = DeltaMonadValue $ Identity $ D u dZero

-- The general case, needed for old, hacky tests before 'Delta' extension.
--
-- Small enough that inline won't hurt.
primalValueGeneric :: forall r a. IsScalar r
                   => (DualNumberVariables r -> DeltaMonadValue r a)
                   -> Domains r
                   -> a
{-# INLINE primalValueGeneric #-}
primalValueGeneric f (params, paramsV, paramsL, paramsX) =
  let replicateZeros p = V.replicate (V.length p) dZero
      variables = makeDualNumberVariables
                    (params, paramsV, paramsL, paramsX)
                    ( replicateZeros params  -- dummy
                    , replicateZeros paramsV
                    , replicateZeros paramsL
                    , replicateZeros paramsX )
  in runIdentity $ runDeltaMonadValue $ f variables

-- Small enough that inline won't hurt.
primalValue :: forall r a. IsScalar r
            => (DualNumberVariables r -> DeltaMonadValue r (DualNumber a))
            -> Domains r
            -> Primal a
{-# INLINE primalValue #-}
primalValue f parameters =
  let D value _ = primalValueGeneric f parameters
  in value

-- * The fully-fledged monad implementation for gradients
-- and the code that uses it to compute single gradients and to do
-- gradient descent.

newtype DeltaMonadGradient r a = DeltaMonadGradient
  { runDeltaMonadGradient :: State (DeltaState (Primal r)) a }
  deriving (Monad, Functor, Applicative)

instance IsScalar r => DeltaMonad r (DeltaMonadGradient r) where
  returnLet (D u u') = DeltaMonadGradient $ do
    st <- get
    let (!stNew, !dId) = bindInState u' st
    put stNew
    return $! D u (dVar dId)

-- The functions in which @generalDf@ inlines and which are used in client code
-- are not inlined there, so the bloat is limited.
generalDf :: HasDelta r
          => DualNumberVariables r
          -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
          -> (Domains r, Primal r)
{-# INLINE generalDf #-}
generalDf variables@(params, _, paramsV, _, paramsL, _, paramsX, _) f =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      dimX = V.length paramsX
      initialState = DeltaState
        { deltaCounter0 = toDeltaId dim
        , deltaCounter1 = toDeltaId dimV
        , deltaCounter2 = toDeltaId dimL
        , deltaCounterX = toDeltaId dimX
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaMonadGradient (f variables))
                                 initialState
      gradient = evalBindings dim dimV dimL dimX st d
  in (gradient, value)

df :: HasDelta r
   => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
   -> Domains r
   -> (Domains r, Primal r)
df f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in generalDf variables f

-- This function uses @DeltaMonadGradient@ for an inefficient computation
-- of forward derivaties. See @generalDfastForward@ for an efficient variant.
generalDforward
  :: HasDelta r
  => DualNumberVariables r
  -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
  -> Domains r
  -> (Primal r, Primal r)
{-# INLINE generalDforward #-}
generalDforward variables@(params, _, paramsV, _, paramsL, _, paramsX, _)
                f direction =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      dimX = V.length paramsX
      initialState = DeltaState
        { deltaCounter0 = toDeltaId dim
        , deltaCounter1 = toDeltaId dimV
        , deltaCounter2 = toDeltaId dimL
        , deltaCounterX = toDeltaId dimX
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaMonadGradient (f variables))
                                 initialState
  in (evalBindingsForward st d direction, value)

-- In a simple-minded way, just for test, we set the direction vector,
-- the dual counterpart of paramters, the dt, to be equal to main parameters.
dforward
  :: HasDelta r
  => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
  -> Domains r
  -> (Primal r, Primal r)
dforward f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in generalDforward variables f parameters

-- * A monad for efficiently computing forward derivatives.

newtype DeltaMonadForward r a = DeltaMonadForward
  { runDeltaMonadForward :: Identity a }
  deriving (Monad, Functor, Applicative)

instance IsScalar r => DeltaMonad r (DeltaMonadForward r) where
  returnLet (D u u') = DeltaMonadForward $ Identity $ D u u'

-- This the efficient variant of forward derivative computation.
generalDfastForward
  :: DualNumberVariables r
  -> (DualNumberVariables r -> DeltaMonadForward r (DualNumber r))
  -> (r, Primal r)
{-# INLINE generalDfastForward #-}
generalDfastForward variables f =
  let D value d = runIdentity $ runDeltaMonadForward $ f variables
  in (d, value)

-- In a simple-minded way, just for test, we set the direction vector,
-- the dual counterpart of paramters, the dt, to be equal to main parameters.
dfastForward
  :: forall r. HasForward r
  => (DualNumberVariables r -> DeltaMonadForward r (DualNumber r))
  -> Domains r
  -> (Primal r, Primal r)
dfastForward f parameters@(params, paramsV, paramsL, paramsX) =
  let variables =
        makeDualNumberVariables
          parameters
          (V.convert params, paramsV, paramsL, paramsX)
      (derivative, value) = generalDfastForward variables f
  in (derivative, value)


-- * Additional mechanisms

prettyPrintDf :: (Show (Primal r), HasDelta r)
              => Bool
              -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
              -> Domains r
              -> String
prettyPrintDf reversed f parameters@(params, paramsV, paramsL, paramsX) =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
      dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      dimX = V.length paramsX
      initialState = DeltaState
        { deltaCounter0 = toDeltaId dim
        , deltaCounter1 = toDeltaId dimV
        , deltaCounter2 = toDeltaId dimL
        , deltaCounterX = toDeltaId dimX
        , deltaBindings = []
        }
      (D _ d0, st) = runState (runDeltaMonadGradient (f variables))
                             initialState
  in if reversed
     then concat $ foldl' (\ !l b -> l ++ ppBinding "where" b)
                          ["COMPUTE " ++ ppShow d0 ++ "\n"]
                          (deltaBindings st)
     else concat $ foldl' (\ !l b -> ppBinding "let" b ++ l)
                          ["in " ++ ppShow d0 ++ "\n"]
                          (deltaBindings st)

generateDeltaVars :: IsScalar r
                  => Domains r
                  -> ( Data.Vector.Vector r
                     , Data.Vector.Vector (Tensor1 r)
                     , Data.Vector.Vector (Tensor2 r)
                     , Data.Vector.Vector (TensorX r) )
generateDeltaVars (params, paramsV, paramsL, paramsX) =
  let vVar p = V.generate (V.length p) (dVar . toDeltaId)
      !v0 = vVar params
      !v1 = vVar paramsV
      !v2 = vVar paramsL
      !vX = vVar paramsX
  in (v0, v1, v2, vX)

-- TODO: extend to tensors if it turns out we use them alongside
-- matrices and vectors, not instead of them.
--
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
initializerFixed :: Int -> Double -> (Int, [Int], [(Int, Int)])
                 -> ((Int, Int, Int), Int, Double, Domains Double)
initializerFixed seed range (nParams, lParamsV, lParamsL) =
  let vParamsV = V.fromList lParamsV
      vParamsL = V.fromList lParamsL
      createRandomVector n seedV =
        HM.scale (2 * range)
        $ HM.randomVector seedV HM.Uniform n - HM.scalar 0.5
      params0 = createRandomVector nParams seed
      paramsV0 =
        V.imap (\i nPV -> createRandomVector nPV (seed + nPV + i)) vParamsV
      paramsL0 =
        V.imap (\i (rows, cols) ->
                 HM.reshape cols
                 $ createRandomVector (rows * cols) (seed + rows + i)) vParamsL
      totalParams = nParams
                    + V.sum vParamsV
                    + V.sum (V.map (uncurry (*)) vParamsL)
  in ( (nParams, V.length vParamsV, V.length vParamsL)
     , totalParams
     , range
     , (params0, paramsV0, paramsL0, V.empty) )
