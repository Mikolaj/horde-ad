{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-orphans #-}
-- | Two implementations of the monad in which our dual numbers live,
-- an implementation of deriving a gradient and several gradient descent
-- schemes.
module HordeAd.Engine where

import Prelude

import           Control.Monad.Trans.State.Strict
import           Data.Functor.Identity
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Foreign.Storable (Storable)

import HordeAd.Delta
import HordeAd.DualDelta (DeltaMonad (..), DualDelta (..))
import HordeAd.PairOfVectors (VecDualDelta, lengthDualDelta)

-- import Debug.Trace

-- * First comes the dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

type DeltaMonadValue r = Identity

instance DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = Identity $ D u Zero
  returnLetV (D u _u') = Identity $ D u Zero

-- The general case.
--
-- Small enough that inline won't hurt.
valueDual :: Storable r
          => (VecDualDelta r -> DeltaMonadValue r a)
          -> Domain r
          -> a
{-# INLINE valueDual #-}
valueDual f ds =
  let dim = V.length ds
      vVar = V.replicate dim Zero  -- dummy
  in runIdentity $ f (ds, vVar, V.empty)

-- A common case, but not the only one, see MNIST.
valueDualDelta :: Storable r
               => (VecDualDelta r -> DeltaMonadValue r (DualDelta r))
               -> Domain r
               -> r
{-# INLINE valueDualDelta #-}
valueDualDelta f ds =
  let D value _ = valueDual f ds
  in value

-- * Here's the fully-fledged monad implementation for gradients
-- and the code that uses it to compute single gradients and to do
-- gradient descent.

newtype DeltaMonadGradient r a = DeltaMonadGradient
  { runDeltaMonadGradient :: State (DeltaState r) a }
  deriving (Monad, Functor, Applicative)

instance DeltaMonad r (DeltaMonadGradient r) where
  -- TODO: when varied benchmarks are available, check if returning v always,
  -- except for @Add@, is faster. Probably @Zero@ and @Var@ appear too rarely
  -- to matter if @Scale@ turns out to require bindings.
  returnLet (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = Left u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetV (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = Right u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)

-- Takes a lot of functions as arguments, hence the inline,
-- but the functions in which it inlines and which are used in client code
-- are not inlined there, so the bloat is limited.
generalDf :: Storable r
          => (domain -> (VecDualDelta r, Int))
          -> (Int -> DeltaState r -> Delta r -> domain')
          -> (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
          -> domain
          -> (domain', r)
{-# INLINE generalDf #-}
generalDf initVars evalBindings f deltaInput =
  let (ds, dim) = initVars deltaInput
      initialState = DeltaState
        { deltaCounter = DeltaId dim
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaMonadGradient (f ds)) initialState
      gradient = evalBindings (lengthDualDelta ds) st d
  in (gradient, value)

type Domain r = Data.Vector.Storable.Vector r

type Domain' r = Domain r

df :: forall r. (Eq r, Num r, Storable r)
   => (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
   -> Domain r
   -> (Domain' r, r)
df =
  let initVars :: Domain r -> (VecDualDelta r, Int)
      initVars deltaInput =
        let dim = V.length deltaInput
        in ((deltaInput, V.generate dim (Var . DeltaId), V.empty), dim)
  in generalDf initVars evalBindingsV

-- | Simple Gradient Descent.
gdSimple :: forall r. (Eq r, Num r, Storable r)
         => r
         -> (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
         -> Int  -- ^ requested number of iterations
         -> Domain r  -- ^ initial parameters
         -> Domain' r
gdSimple gamma f n0 params0 = go n0 params0 where
  dim = V.length params0
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  vVar = V.generate dim (Var . DeltaId)
  go :: Int -> Domain r -> Domain' r
  go 0 !params = params
  go n params =
    let initVars :: (VecDualDelta r, Int)
        initVars = ((params, vVar, V.empty), dim)
        gradient = fst $ generalDf (const initVars) evalBindingsV f params
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
    in go (pred n) paramsNew

-- | Stochastic Gradient Descent.
sgd :: forall r a. (Eq r, Num r, Storable r)
    => r
    -> (a -> VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
    -> [a]  -- ^ training data
    -> Domain r  -- ^ initial parameters
    -> Domain' r
sgd gamma f trainingData params0 = go trainingData params0 where
  dim = V.length params0
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  vVar = V.generate dim (Var . DeltaId)
  go :: [a] -> Domain r -> Domain' r
  go [] !params = params
  go (a : rest) params =
    let initVars :: (VecDualDelta r, Int)
        initVars = ((params, vVar, V.empty), dim)
        gradient = fst $ generalDf (const initVars) evalBindingsV (f a) params
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
    in go rest paramsNew

-- | Relatively Smart Gradient Descent.
-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gdSmart :: forall r.
             (
--               Show r,
               Ord r, Fractional r, Storable r
             )
        => (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
        -> Int  -- ^ requested number of iterations
        -> Domain r  -- ^ initial parameters
        -> (Domain' r, r)
gdSmart f n0 params0 = go n0 params0 0.1 gradient0 value0 0 where
  dim = V.length params0
  vVar = V.generate dim (Var . DeltaId)
  initVars0 :: (VecDualDelta r, Int)
  initVars0 = ((params0, vVar, V.empty), dim)
  (gradient0, value0) = generalDf (const initVars0) evalBindingsV f params0
  go :: Int -> Domain r -> r -> Domain r -> r -> Int -> (Domain' r, r)
  go 0 !params !gamma _gradientPrev _valuePrev !_i = (params, gamma)
  go _ params 0 _ _ _ = (params, 0)
  go n params gamma gradientPrev valuePrev i =
--    traceShow (n, gamma, valuePrev, i) $
--    traceShow ("params" :: String, params) $
--    traceShow ("gradient" :: String, gradientPrev) $
    --
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let paramsNew = V.zipWith (\p r -> p - gamma * r) params gradientPrev
        initVars = ((paramsNew, vVar, V.empty), dim)
        (gradient, value) = generalDf (const initVars) evalBindingsV f paramsNew
    in if | V.all (== 0) gradientPrev -> (params, gamma)
          | value > valuePrev ->
--              traceShow ("value > valuePrev" :: String, value, valuePrev) $
              go n params (gamma / 2) gradientPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) paramsNew (gamma * 2) gradient value 0
          | otherwise -> go (pred n) paramsNew gamma gradient value (i + 1)












-- selective fusion (hand-writing gradients of larger expressions,
-- sometimes, as in the case of the composition of cross-entropy and softMax,
-- enabling simplification and always saving the time and space needed
-- to auto-derive that; so it seems it should never hurt;
-- however, sometimes the best handwritten gradient is exactly as large
-- and as complex as the derived one)
--
-- checkpointing (limiting space usage?)
