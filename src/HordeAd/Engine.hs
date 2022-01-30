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
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Numeric.LinearAlgebra (Numeric, konst)

import HordeAd.Delta
import HordeAd.DualDelta (DeltaMonad (..), DualDelta (..))
import HordeAd.PairOfVectors (VecDualDelta)

-- import Debug.Trace

-- * First comes the dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

type Domain r = Data.Vector.Storable.Vector r

type Domain' r = Domain r

type DomainV r = Data.Vector.Vector (Data.Vector.Storable.Vector r)

type DomainV' r = DomainV r

type DeltaMonadValue r = Identity

instance DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = Identity $ D u Zero
  returnLetV (D u _u') = Identity $ D u Zero

-- The general case, needed for old, hacky tests before 'Delta' extension.
--
-- Small enough that inline won't hurt.
valueDual :: Numeric r
          => (VecDualDelta r -> DeltaMonadValue r a)
          -> (Domain r, DomainV r)
          -> a
{-# INLINE valueDual #-}
valueDual f (ds, dsV) =
  let dim = V.length ds
      vVar = V.replicate dim Zero  -- dummy
  in runIdentity $ f (ds, vVar, V.map (`D` Zero) dsV)

-- Small enough that inline won't hurt.
valueDualDelta :: Numeric r
               => (VecDualDelta r -> DeltaMonadValue r (DualDelta a))
               -> (Domain r, DomainV r)
               -> a
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
generalDf :: (VecDualDelta r, Int, Int)
          -> (Int -> Int -> DeltaState r -> Delta r -> domain')
          -> (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
          -> (domain', r)
{-# INLINE generalDf #-}
generalDf (ds, dim, dimV) evalBindings f =
  let initialState = DeltaState
        { deltaCounter = DeltaId $ dim + dimV
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaMonadGradient (f ds)) initialState
      gradient = evalBindings dim dimV st d
  in (gradient, value)

df :: forall r. (Eq r, Numeric r, Num (Data.Vector.Storable.Vector r))
   => (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
   -> (Domain r, DomainV r)
   -> ((Domain' r, DomainV' r), r)
df f (deltaInput, deltaInputV) =
  let initVars :: (VecDualDelta r, Int, Int)
      initVars =
        let dim = V.length deltaInput
            dimV = V.length deltaInputV
            vVarV = V.generate dimV (Var . DeltaId . (+ dim))
        in ( ( deltaInput
             , V.generate dim (Var . DeltaId)
             , V.zipWith D deltaInputV vVarV )
           , dim
           , dimV )
  in generalDf initVars evalBindingsV f

-- | Simple Gradient Descent.
gdSimple :: forall r. (Eq r, Numeric r, Num (Data.Vector.Storable.Vector r))
         => r
         -> (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
         -> Int  -- ^ requested number of iterations
         -> (Domain r, DomainV r)  -- ^ initial parameters
         -> (Domain' r, DomainV' r)
gdSimple gamma f n0 (params0, paramsV0) = go n0 params0 paramsV0 where
  dim = V.length params0
  dimV = V.length paramsV0
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  go :: Int -> Domain r -> DomainV r -> (Domain' r, DomainV' r)
  go 0 !params !paramsV = (params, paramsV)
  go n params paramsV =
    let initVars :: (VecDualDelta r, Int, Int)
        initVars = ((params, vVar, V.zipWith D paramsV vVarV), dim, dimV)
        (gradient, gradientV) = fst $ generalDf initVars evalBindingsV f
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
        paramsVNew = V.zipWith (\i r -> i - konst gamma (V.length r) * r)
                               paramsV gradientV
    in go (pred n) paramsNew paramsVNew

-- | Stochastic Gradient Descent.
sgd :: forall r a. (Eq r, Numeric r, Num (Data.Vector.Storable.Vector r))
    => r
    -> (a -> VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
    -> [a]  -- ^ training data
    -> (Domain r, DomainV r)  -- ^ initial parameters
    -> (Domain' r, DomainV' r)
sgd gamma f trainingData (params0, paramsV0) =
  go trainingData params0 paramsV0
 where
  dim = V.length params0
  dimV = V.length paramsV0
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  go :: [a] -> Domain r -> DomainV r -> (Domain' r, DomainV' r)
  go [] !params !paramsV = (params, paramsV)
  go (a : rest) params paramsV =
    let initVars :: (VecDualDelta r, Int, Int)
        initVars = ((params, vVar, V.zipWith D paramsV vVarV), dim, dimV)
        (gradient, gradientV) = fst $ generalDf initVars evalBindingsV (f a)
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
        paramsVNew = V.zipWith (\i r -> i - konst gamma (V.length r) * r)
                               paramsV gradientV
    in go rest paramsNew paramsVNew

-- | Relatively Smart Gradient Descent.
-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gdSmart :: forall r.
             (
--               Show r,
               Ord r, Fractional r
             , Numeric r, Num (Data.Vector.Storable.Vector r)
             )
        => (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
        -> Int  -- ^ requested number of iterations
        -> (Domain r, DomainV r)  -- ^ initial parameters
        -> ((Domain' r, DomainV' r), r)
gdSmart f n0 (params0, paramsV0) =
  go n0 params0 paramsV0 0.1 gradient0 gradientV0 value0 0
 where
  dim = V.length params0
  dimV = V.length paramsV0
  vVar = V.generate dim (Var . DeltaId)
  vVarV = V.generate dimV (Var . DeltaId . (+ dim))
  initVars0 :: (VecDualDelta r, Int, Int)
  initVars0 = ((params0, vVar, V.zipWith D paramsV0 vVarV), dim, dimV)
  ((gradient0, gradientV0), value0) = generalDf initVars0 evalBindingsV f
  go :: Int -> Domain r -> DomainV r -> r -> Domain' r -> DomainV' r -> r -> Int
     -> ((Domain' r, DomainV' r), r)
  go 0 !params !paramsV !gamma _gradientPrev _gradientVPrev _valuePrev !_i =
    ((params, paramsV), gamma)
  go _ params paramsV 0 _ _ _ _ = ((params, paramsV), 0)
  go n params paramsV gamma gradientPrev gradientVPrev valuePrev i =
--    traceShow (n, gamma, valuePrev, i) $
--    traceShow ("params" :: String, params) $
--    traceShow ("gradient" :: String, gradientPrev) $
    --
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let paramsNew = V.zipWith (\p r -> p - gamma * r) params gradientPrev
        paramsVNew = V.zipWith (\p r -> p - konst gamma (V.length r) * r)
                               paramsV gradientVPrev
        initVars = ((paramsNew, vVar, V.zipWith D paramsVNew vVarV), dim, dimV)
        ((gradient, gradientV), value) = generalDf initVars evalBindingsV f
    in if | V.all (== 0) gradientPrev
            && V.all (== V.empty) gradientVPrev -> ((params, paramsV), gamma)
          | value > valuePrev ->
--              traceShow ("value > valuePrev" :: String, value, valuePrev) $
              go n params paramsV (gamma / 2)
                 gradientPrev gradientVPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) paramsNew paramsVNew (gamma * 2)
                          gradient gradientV value 0
          | otherwise -> go (pred n) paramsNew paramsVNew gamma
                            gradient gradientV value (i + 1)
