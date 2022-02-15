{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Two implementations of the monad in which our dual numbers live
-- and the implementation of deriving a gradient.
module HordeAd.Core.Engine
  ( Domain, Domain', DomainV, DomainV', DomainL, DomainL', Domains, Domains'
  , DeltaMonadValue, primalValueGeneric, primalValue
  , DeltaMonadGradient, generalDf, df, generateDeltaVars, initializerFixed
  ) where

import Prelude

import           Control.Monad.Trans.State.Strict
import           Data.Functor.Identity
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.Random

import HordeAd.Core.Delta
import HordeAd.Core.DualNumber (DeltaMonad (..), DualNumber (..))
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- import Debug.Trace

type Domain r = Vector r

type Domain' r = Domain r

type DomainV r = Data.Vector.Vector (Vector r)

type DomainV' r = DomainV r

type DomainL r = Data.Vector.Vector (Matrix r)

type DomainL' r = DomainL r

type Domains r = (Domain r, DomainV r, DomainL r)

type Domains' r = (Domain' r, DomainV' r, DomainL' r)

-- * First comes the dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

type DeltaMonadValue r = Identity

instance DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = Identity $ D u Zero
  returnLetV (D u _u') = Identity $ D u Zero
  returnLetL (D u _u') = Identity $ D u Zero

-- The general case, needed for old, hacky tests before 'Delta' extension.
--
-- Small enough that inline won't hurt.
primalValueGeneric :: Numeric r
                   => (DualNumberVariables r -> DeltaMonadValue r a)
                   -> Domains r
                   -> a
{-# INLINE primalValueGeneric #-}
primalValueGeneric f (params, paramsV, paramsL) =
  let variables = makeDualNumberVariables
                    (params, paramsV, paramsL)
                    ( V.replicate (V.length params) Zero  -- dummy
                    , V.replicate (V.length paramsV) Zero
                    , V.replicate (V.length paramsL) Zero )
  in runIdentity $ f variables

-- Small enough that inline won't hurt.
primalValue :: Numeric r
            => (DualNumberVariables r -> DeltaMonadValue r (DualNumber a))
            -> Domains r
            -> a
{-# INLINE primalValue #-}
primalValue f parameters =
  let D value _ = primalValueGeneric f parameters
  in value

-- * Here's the fully-fledged monad implementation for gradients
-- and the code that uses it to compute single gradients and to do
-- gradient descent.

newtype DeltaMonadGradient r a = DeltaMonadGradient
  { runDeltaMonadGradient :: State (DeltaState r) a }
  deriving (Monad, Functor, Applicative)

instance DeltaMonad r (DeltaMonadGradient r) where
  returnLet (D u u') = DeltaMonadGradient $ do
    did@(DeltaId i) <- gets deltaCounter0
    modify $ \s ->
      s { deltaCounter0 = DeltaId $ succ i
        , deltaBindings = DScalar did u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetV (D u u') = DeltaMonadGradient $ do
    did@(DeltaId i) <- gets deltaCounter1
    modify $ \s ->
      s { deltaCounter1 = DeltaId $ succ i
        , deltaBindings = DVector did u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetL (D u u') = DeltaMonadGradient $ do
    did@(DeltaId i) <- gets deltaCounter2
    modify $ \s ->
      s { deltaCounter2 = DeltaId $ succ i
        , deltaBindings = DMatrix did u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)

-- The functions in which it inlines and which are used in client code
-- are not inlined there, so the bloat is limited.
generalDf :: (Eq r, Numeric r, Num (Vector r))
          => DualNumberVariables r
          -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
          -> (Domains' r, r)
{-# INLINE generalDf #-}
generalDf variables@(params, _, paramsV, _, paramsL, _) f =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      initialState = DeltaState
        { deltaCounter0 = DeltaId dim
        , deltaCounter1 = DeltaId dimV
        , deltaCounter2 = DeltaId dimL
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaMonadGradient (f variables))
                                 initialState
      gradient = evalBindings dim dimV dimL st d
  in (gradient, value)

df :: forall r. (Eq r, Numeric r, Num (Vector r))
   => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
   -> Domains r
   -> (Domains' r, r)
df f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in generalDf variables f

generateDeltaVars :: Numeric r
                  => Domains r -> ( Data.Vector.Vector (Delta r)
                                  , Data.Vector.Vector (Delta (Vector r))
                                  , Data.Vector.Vector (Delta (Matrix r)) )
generateDeltaVars (params, paramsV, paramsL) =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      vVar = V.generate dim (Var . DeltaId)
      vVarV = V.generate dimV (Var . DeltaId)
      vVarL = V.generate dimL (Var . DeltaId)
  in (vVar, vVarV, vVarL)

-- | Initialize parameters using a uniform distribution with a fixed range
-- taken from an argument.
--
-- Must be Double, because @uniformSample@ only works on that.
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
      params0 = V.unfoldrExactN nParams (uniformR (- range, range))
                $ mkStdGen seed
      paramsV0 =
        V.imap (\i nPV -> V.unfoldrExactN nPV (uniformR (- range, range))
                                          (mkStdGen $ seed + nPV + i))
               vParamsV
      paramsL0 = V.imap (\i (rows, cols) ->
                           HM.uniformSample (seed + rows + i) rows
                                            (replicate cols (- range, range)))
                        vParamsL
      totalParams = nParams
                    + V.sum vParamsV
                    + V.sum (V.map (uncurry (*)) vParamsL)
  in ( (nParams, V.length vParamsV, V.length vParamsL)
     , totalParams
     , range
     , (params0, paramsV0, paramsL0) )
