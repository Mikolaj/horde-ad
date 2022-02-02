{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-orphans #-}
-- | Two implementations of the monad in which our dual numbers live,
-- an implementation of deriving a gradient and several gradient descent
-- schemes.
module HordeAd.Engine where

import Prelude

import           Control.Monad.Trans.State.Strict
import           Data.Functor.Identity
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector, rows)
import qualified Numeric.LinearAlgebra

import HordeAd.Delta
import HordeAd.DualNumber (DeltaMonad (..), DualNumber (..))
import HordeAd.PairOfVectors (VecDualNumber, vecDualNumberFromVars)

-- import Debug.Trace

-- * First comes the dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

type Domain r = Vector r

type Domain' r = Domain r

type DomainV r = Data.Vector.Vector (Vector r)

type DomainV' r = DomainV r

type DomainL r = Data.Vector.Vector (Matrix r)

type DomainL' r = DomainL r

type DeltaMonadValue r = Identity

instance DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = Identity $ D u Zero
  returnLetV (D u _u') = Identity $ D u Zero
  returnLetL (D u _u') = Identity $ D u Zero

-- The general case, needed for old, hacky tests before 'Delta' extension.
--
-- Small enough that inline won't hurt.
valueDual :: Numeric r
          => (VecDualNumber r -> DeltaMonadValue r a)
          -> (Domain r, DomainV r, DomainL r)
          -> a
{-# INLINE valueDual #-}
valueDual f (ds, dsV, dsL) =
  let vec = vecDualNumberFromVars (ds, dsV, dsL)
                                  ( V.replicate (V.length ds) Zero  -- dummy
                                  , V.replicate (V.length dsV) Zero
                                  , V.replicate (V.length dsL) Zero )
  in runIdentity $ f vec

-- Small enough that inline won't hurt.
valueDualNumber :: Numeric r
               => (VecDualNumber r -> DeltaMonadValue r (DualNumber a))
               -> (Domain r, DomainV r, DomainL r)
               -> a
{-# INLINE valueDualNumber #-}
valueDualNumber f ds =
  let D value _ = valueDual f ds
  in value

-- * Here's the fully-fledged monad implementation for gradients
-- and the code that uses it to compute single gradients and to do
-- gradient descent.

newtype DeltaMonadGradient r a = DeltaMonadGradient
  { runDeltaMonadGradient :: State (DeltaState r) a }
  deriving (Monad, Functor, Applicative)

instance DeltaMonad r (DeltaMonadGradient r) where
  returnLet (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DScalar u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetV (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DVector u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetL (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DMatrix u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)

-- The functions in which it inlines and which are used in client code
-- are not inlined there, so the bloat is limited.
generalDf :: (Eq r, Numeric r, Num (Vector r))
          => VecDualNumber r
          -> (VecDualNumber r -> DeltaMonadGradient r (DualNumber r))
          -> ((Domain' r, DomainV' r, DomainL' r), r)
{-# INLINE generalDf #-}
generalDf vec@(ds, _, dsV, _, dsL, _) f =
  let dim = V.length ds
      dimV = V.length dsV
      dimL = V.length dsL
      initialState = DeltaState
        { deltaCounter = DeltaId $ dim + dimV + dimL
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaMonadGradient (f vec)) initialState
      gradient = evalBindings dim dimV dimL st d
  in (gradient, value)

df :: forall r. (Eq r, Numeric r, Num (Vector r))
   => (VecDualNumber r -> DeltaMonadGradient r (DualNumber r))
   -> (Domain r, DomainV r, DomainL r)
   -> ((Domain' r, DomainV' r, DomainL' r), r)
df f (params, paramsV, paramsL) =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      vVar = V.generate dim (Var . DeltaId)
      vVarV = V.generate dimV (Var . DeltaId . (+ dim))
      vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
      variables = (vVar, vVarV, vVarL)
      vecDualNumber = vecDualNumberFromVars (params, paramsV, paramsL) variables
  in generalDf vecDualNumber f

-- | Simple Gradient Descent.
gdSimple :: forall r. (Eq r, Numeric r, Num (Vector r))
         => r
         -> (VecDualNumber r -> DeltaMonadGradient r (DualNumber r))
         -> Int  -- ^ requested number of iterations
         -> (Domain r, DomainV r, DomainL r)  -- ^ initial parameters
         -> (Domain' r, DomainV' r, DomainL' r)
gdSimple gamma f n0 (params0, paramsV0, paramsL0) =
  go n0 params0 paramsV0 paramsL0
 where
  dim = V.length params0
  dimV = V.length paramsV0
  dimL = V.length paramsL0
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
  variables = (vVar, vVarV, vVarL)
  go :: Int -> Domain r -> DomainV r -> DomainL r
     -> (Domain' r, DomainV' r, DomainL' r)
  go 0 !params !paramsV !paramsL = (params, paramsV, paramsL)
  go n params paramsV paramsL =
    let vecDualNumber =
          vecDualNumberFromVars (params, paramsV, paramsL) variables
        (gradient, gradientV, gradientL) = fst $ generalDf vecDualNumber f
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
        paramsVNew = V.zipWith (\i r -> i - Numeric.LinearAlgebra.scale gamma r)
                               paramsV gradientV
        paramsLNew = V.zipWith (\i r -> i - Numeric.LinearAlgebra.scale gamma r)
                               paramsL gradientL
    in go (pred n) paramsNew paramsVNew paramsLNew

-- | Stochastic Gradient Descent.
sgd :: forall r a. (Eq r, Numeric r, Num (Vector r))
    => r
    -> (a -> VecDualNumber r -> DeltaMonadGradient r (DualNumber r))
    -> [a]  -- ^ training data
    -> (Domain r, DomainV r, DomainL r)  -- ^ initial parameters
    -> (Domain' r, DomainV' r, DomainL' r)
sgd gamma f trainingData (params0, paramsV0, paramsL0) =
  go trainingData params0 paramsV0 paramsL0
 where
  dim = V.length params0
  dimV = V.length paramsV0
  dimL = V.length paramsL0
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
  variables = (vVar, vVarV, vVarL)
  go :: [a] -> Domain r -> DomainV r -> DomainL r
     -> (Domain' r, DomainV' r, DomainL' r)
  go [] !params !paramsV !paramsL = (params, paramsV, paramsL)
  go (a : rest) params paramsV paramsL =
    let vecDualNumber =
          vecDualNumberFromVars (params, paramsV, paramsL) variables
        (gradient, gradientV, gradientL) = fst $ generalDf vecDualNumber (f a)
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
        paramsVNew = V.zipWith (\i r -> i - Numeric.LinearAlgebra.scale gamma r)
                               paramsV gradientV
        paramsLNew = V.zipWith (\i r -> i - Numeric.LinearAlgebra.scale gamma r)
                               paramsL gradientL
    in go rest paramsNew paramsVNew paramsLNew

-- | Relatively Smart Gradient Descent.
-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gdSmart :: forall r. (
--                     Show r,
                       Ord r, Fractional r, Numeric r
                     , Num (Vector r)
                     )
        => (VecDualNumber r -> DeltaMonadGradient r (DualNumber r))
        -> Int  -- ^ requested number of iterations
        -> (Domain r, DomainV r, DomainL r)  -- ^ initial parameters
        -> ((Domain' r, DomainV' r, DomainL' r), r)
gdSmart f n0 (params0, paramsV0, paramsL0) =
  go n0 params0 paramsV0 paramsL0 0.1 gradient0 gradientV0 gradientL0 value0 0
 where
  dim = V.length params0
  dimV = V.length paramsV0
  dimL = V.length paramsL0
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
  variables = (vVar, vVarV, vVarL)
  vecDualNumber0 = vecDualNumberFromVars (params0, paramsV0, paramsL0) variables
  ((gradient0, gradientV0, gradientL0), value0) = generalDf vecDualNumber0 f
  go :: Int -> Domain r -> DomainV r -> DomainL r -> r
     -> Domain' r -> DomainV' r -> DomainL' r -> r -> Int
     -> ((Domain' r, DomainV' r, DomainL' r), r)
  go 0 !params !paramsV !paramsL !gamma
     _gradientPrev _gradientVPrev _gradientLPrev _valuePrev !_i =
    ((params, paramsV, paramsL), gamma)
  go _ params paramsV paramsL 0 _ _ _ _ _ = ((params, paramsV, paramsL), 0)
  go n params paramsV paramsL gamma
     gradientPrev gradientVPrev gradientLPrev valuePrev i =
--    traceShow (n, gamma, valuePrev, i) $
--    traceShow ("params" :: String, params) $
--    traceShow ("gradient" :: String, gradientPrev) $
    --
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let paramsNew = V.zipWith (\p r -> p - gamma * r) params gradientPrev
        paramsVNew = V.zipWith (\p r -> p - Numeric.LinearAlgebra.scale gamma r)
                               paramsV gradientVPrev
        paramsLNew = V.zipWith (\p r -> p - Numeric.LinearAlgebra.scale gamma r)
                               paramsL gradientLPrev
        vecDualNumber =
          vecDualNumberFromVars (paramsNew, paramsVNew, paramsLNew) variables
        ((gradient, gradientV, gradientL), value) = generalDf vecDualNumber f
    in if | V.all (== 0) gradientPrev
            && V.all (== V.empty) gradientVPrev
            && V.all (\r -> rows r <= 0) gradientLPrev
            -> ((params, paramsV, paramsL), gamma)
          | value > valuePrev ->
--              traceShow ("value > valuePrev" :: String, value, valuePrev) $
              go n params paramsV paramsL (gamma / 2)  -- overshot
                 gradientPrev gradientVPrev gradientLPrev valuePrev 0
          | i == 10 -> go (pred n) paramsNew paramsVNew paramsLNew (gamma * 2)
                          gradient gradientV gradientL value 0
          | otherwise -> go (pred n) paramsNew paramsVNew paramsLNew gamma
                            gradient gradientV gradientL value (i + 1)
