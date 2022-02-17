{-# LANGUAGE ConstraintKinds, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Two implementations of the monad in which our dual numbers live
-- and the implementation of deriving a gradient.
module HordeAd.Core.Engine
  ( IsScalar
  , Domain, DomainV, DomainL,  Domains
  , DeltaMonadValue, primalValueGeneric, primalValue
  , DeltaMonadGradient, generalDf, df, prettyPrintDf
  , generateDeltaVars, initializerFixed
  ) where

import Prelude

import           Control.Monad.Trans.State.Strict
import           Data.Functor.Identity
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.Random
import           Text.Show.Pretty (ppShow)

import HordeAd.Core.Delta
import HordeAd.Core.DualNumber (DeltaMonad (..), DualNumber (..))
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- import Debug.Trace

type Domain r = Vector r

type DomainV r = Data.Vector.Vector (Vector r)

type DomainL r = Data.Vector.Vector (Matrix r)

type Domains r = (Domain r, DomainV r, DomainL r)

-- * First comes the dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

type DeltaMonadValue r = Identity

-- This the only place that requires @UndecidableInstances@.
instance IsScalar r => DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = Identity $ D u zeroD

-- The general case, needed for old, hacky tests before 'Delta' extension.
--
-- Small enough that inline won't hurt.
primalValueGeneric :: IsScalar r
                   => (DualNumberVariables r -> DeltaMonadValue r a)
                   -> Domains r
                   -> a
{-# INLINE primalValueGeneric #-}
primalValueGeneric f (params, paramsV, paramsL) =
  let replicateZeros p = V.replicate (V.length p) zeroD
      variables = makeDualNumberVariables
                    (params, paramsV, paramsL)
                    ( replicateZeros params  -- dummy
                    , replicateZeros paramsV
                    , replicateZeros paramsL )
  in runIdentity $ f variables

-- Small enough that inline won't hurt.
primalValue :: IsScalar r
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

instance IsScalar r => DeltaMonad r (DeltaMonadGradient r) where
  returnLet (D u u') = DeltaMonadGradient $ do
    st <- get
    let (!stNew, !dId) = bindInState u' st
    put stNew
    return $! D u (varD dId)

-- The functions in which @generalDf@ inlines and which are used in client code
-- are not inlined there, so the bloat is limited.
generalDf :: (Eq r, IsScalar r)
          => DualNumberVariables r
          -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
          -> (Domains r, r)
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

df :: (Eq r, IsScalar r)
   => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
   -> Domains r
   -> (Domains r, r)
df f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in generalDf variables f

prettyPrintDf :: forall r. (Show r, IsScalar r)
              => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
              -> Domains r
              -> String
prettyPrintDf f parameters@(params, paramsV, paramsL) =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
      dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      initialState = DeltaState
        { deltaCounter0 = DeltaId dim
        , deltaCounter1 = DeltaId dimV
        , deltaCounter2 = DeltaId dimL
        , deltaBindings = []
        }
      (D _ d0, st) = runState (runDeltaMonadGradient (f variables))
                             initialState
      ppBinding :: DeltaBinding r -> [String]
      ppBinding = \case
        DScalar (DeltaId i) d ->
          ["letS DeltaId_", show i, " = ", ppShow d, "\n"]
        DVector (DeltaId i) d ->
          ["letV DeltaId_", show i, " = ", ppShow d, "\n"]
        DMatrix (DeltaId i) d ->
          ["letM DeltaId_", show i, " = ", ppShow d, "\n"]
  in concat $ foldl' (\ !l b -> ppBinding b ++ l) ["in " ++ ppShow d0]
                     (deltaBindings st)

generateDeltaVars :: IsScalar r
                  => Domains r -> ( Data.Vector.Vector (DeltaScalar r)
                                  , Data.Vector.Vector (DeltaVector r)
                                  , Data.Vector.Vector (DeltaMatrix r) )
generateDeltaVars (params, paramsV, paramsL) =
  let vVar p = V.generate (V.length p) (varD . DeltaId)
  in (vVar params, vVar paramsV, vVar paramsL)

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
