{-# LANGUAGE ConstraintKinds, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TypeFamilies #-}
-- | Two implementations of the monad in which our dual numbers live
-- and the implementation of deriving a gradient.
module HordeAd.Core.Engine
  ( Domain, DomainV, DomainL, DomainX, Domains
  , DeltaMonadValue, primalValueGeneric, primalValue
  , DeltaMonadGradient, generalDf, df, generalDforward, prettyPrintDf
  , generateDeltaVars, initializerFixed
  ) where

import Prelude

import           Control.Monad.Trans.State.Strict
import qualified Data.Array.DynamicS as OT
import           Data.Functor.Identity
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Vector)
import qualified Numeric.LinearAlgebra as HM
import           Text.Show.Pretty (ppShow)

import HordeAd.Core.Delta
  ( DeltaState (..)
  , Domain
  , DomainL
  , DomainV
  , DomainX
  , Domains
  , evalBindings
  , evalBindingsForward
  , ppBinding
  , toDeltaId
  )
import HordeAd.Core.DualNumber (DeltaMonad (..), DualNumber (..))
import HordeAd.Core.IsTensor
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- * First comes the dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

-- An overcomplicated
-- @type DeltaMonadValue r = Identity@
-- to avoid @-Wno-orphans@ and @UndecidableInstances@.
newtype DeltaMonadValue r a = DeltaMonadValue
  { runDeltaMonadValue :: Identity a }
  deriving (Monad, Functor, Applicative)

-- This the only place that requires @UndecidableInstances@.
instance IsScalar r => DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = DeltaMonadValue $ Identity $ D u zeroD

-- The general case, needed for old, hacky tests before 'Delta' extension.
--
-- Small enough that inline won't hurt.
primalValueGeneric :: IsScalar r
                   => (DualNumberVariables r -> DeltaMonadValue r a)
                   -> Domains r
                   -> a
{-# INLINE primalValueGeneric #-}
primalValueGeneric f (params, paramsV, paramsL, paramsX) =
  let replicateZeros p = V.replicate (V.length p) zeroD
      variables = makeDualNumberVariables
                    (params, paramsV, paramsL, paramsX)
                    ( replicateZeros params  -- dummy
                    , replicateZeros paramsV
                    , replicateZeros paramsL
                    , replicateZeros paramsX )
  in runIdentity $ runDeltaMonadValue $ f variables

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

df :: (Eq r, IsScalar r)
   => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
   -> Domains r
   -> (Domains r, r)
df f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in generalDf variables f

generalDforward
  :: IsScalar r
  => DualNumberVariables r
  -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
  -> Domains r
  -> (r, r)
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

prettyPrintDf :: forall r. (Show r, IsScalar r)
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
                  -> ( Data.Vector.Vector (DeltaExpression r)
                     , Data.Vector.Vector (DeltaExpression (Vector r))
                     , Data.Vector.Vector (DeltaExpression (Matrix r))
                     , Data.Vector.Vector (DeltaExpression (OT.Array r)) )
generateDeltaVars (params, paramsV, paramsL, paramsX) =
  let vVar p = V.generate (V.length p) (varD . toDeltaId)
  in (vVar params, vVar paramsV, vVar paramsL, vVar paramsX)

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
