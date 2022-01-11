{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, RankNTypes #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module AD where

import Prelude

import           Control.Exception (assert)
import           Control.Monad (foldM, when)
import           Control.Monad.ST.Strict (ST)
import           Control.Monad.Trans.State.Strict
import           Data.Functor.Identity
import           Data.List (foldl')
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Unboxed

-- Tagless final doesn't seem to work well, because we need to gather
-- @Delta@ while doing @DualDelta@ operations, but evaluate on concrete
-- vectors that correspond to only the second component of dual numbers.
-- Also, initial encoding gives us full control over
-- when to evaluate. With final, we'd need to be careful
-- about laziness to ensure the optimal evaluation order is chosen
-- (whatever it is for a given differentiated program).
data Delta r =
    Zero
  | Scale r (Delta r)
  | Add (Delta r) (Delta r)
  | Var DeltaId

newtype DeltaId = DeltaId Int
  deriving (Show, Eq, Ord, Enum)

-- This can't be environment in a Reader, because subtrees add their own
-- identifiers for sharing, instead of parents naming their subtrees.
-- This must be the "evaluate Let backwards" from SPJ's talk.
-- This and the need to control evaluation order contribute to
-- the difficulty of applying any HOAS concept instead of the monad
-- with bindings accumulated in state.
-- Note that each variable is created only once, but the subexpression
-- it's a part of can get duplicated grossly.
data DeltaState r = DeltaState
  { deltaCounter  :: DeltaId
  , deltaBindings :: [Delta r]
  }

-- Making the second field non-strict makes computing value of a function
-- twice faster, but computing the gradient slower by 30% (it's then hard
-- to keep the accumulator in argument function to @foldl'@ fully strict, etc.),
-- which is much bigger a difference in absolute terms. Then @valueDual.vVar@
-- can be set to @undefined@. The decision depends on the application.
-- Another option is to make @var@ part of the @DeltaMonad@ API
-- and provide a cheaper one for @DeltaMonadValue@. A comprehensive solution
-- could be putting all constructors of @Delta@ inside the @DeltaMonad@ class,
-- as a mock final tagless approach, that would probably be implemented
-- as an inductive type for @DeltaMonadGradient@ anyway.
data DualDelta r = D r (Delta r)

type VecDualDelta r = (Domain r, Data.Vector.Vector (Delta r))

buildVector :: forall s v r. (Eq r, Num r, VM.MVector (V.Mutable v) r)
            => Int -> DeltaState r -> Delta r
            -> ST s (V.Mutable v s r)
buildVector dim st d0 = do
  let DeltaId storeSize = deltaCounter st
  store <- VM.replicate storeSize 0
  let eval :: r -> Delta r -> ST s ()
      eval !r = \case
        Zero -> return ()
        Scale k d -> eval (k * r) d
        Add d1 d2 -> eval r d1 >> eval r d2
        Var (DeltaId i) -> VM.modify store (+ r) i
  eval 1 d0  -- dt is 1 or hardwired in f
  let evalUnlessZero :: DeltaId -> Delta r -> ST s DeltaId
      evalUnlessZero delta@(DeltaId !i) d = do
        r <- store `VM.read` i
        when (r /= 0) $  -- we init with exactly 0 above so the comparison is OK
          eval r d
        return $! pred delta
  minusOne <- foldM evalUnlessZero (DeltaId $ pred storeSize) (deltaBindings st)
  let _A = assert (minusOne == DeltaId (-1)) ()
  return $! VM.slice 0 dim store

evalBindingsV :: (Eq r, Num r, V.Vector v r)
              => VecDualDelta i -> DeltaState r -> Delta r -> v r
evalBindingsV ds st d0 = V.create $ buildVector (V.length $ snd ds) st d0

class (Monad m, Functor m, Applicative m) => DeltaMonad r m | m -> r where
  returnLetD :: r -> Delta r -> m (DualDelta r)

newtype DeltaMonadGradient r a = DeltaMonadGradient
  { runDeltaMonadGradient :: State (DeltaState r) a }
  deriving (Monad, Functor, Applicative)

instance DeltaMonad r (DeltaMonadGradient r) where
  -- TODO: when varied benchmarks are available, check if returning v always,
  -- except for @Add@, is faster. Probably @Zero@ and @Var@ appear too rarely
  -- to matter if @Scale@ turns out to require bindings.
  returnLetD r v = DeltaMonadGradient $ do
    i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = succ i
        , deltaBindings = v : deltaBindings s
        }
    return $! D r (Var i)

type DeltaMonadValue r = Identity

instance DeltaMonad r (DeltaMonadValue r) where
  returnLetD r _v = Identity $ D r Zero

-- Small enough that inline won't hurt.
valueDual :: Data.Vector.Unboxed.Unbox r
          => (VecDualDelta r -> DeltaMonadValue r a)
          -> Domain r
          -> a
{-# INLINE valueDual #-}
valueDual f ds =
  let dim = V.length ds
      vVar = V.replicate dim Zero  -- dummy
  in runIdentity $ f (ds, vVar)

-- A common case, but not the only one, see MNIST.
valueDualDelta :: Data.Vector.Unboxed.Unbox r
               => (VecDualDelta r -> DeltaMonadValue r (DualDelta r))
               -> Domain r
               -> r
{-# INLINE valueDualDelta #-}
valueDualDelta f ds =
  let D value _ = valueDual f ds
  in value

var :: Data.Vector.Unboxed.Unbox r
    => Int -> VecDualDelta r -> DualDelta r
var i (vValue, vVar) = D (vValue V.! i) (vVar V.! i)

-- Takes a lot of functions as arguments, hence the inline,
-- but the functions in which it inlines and which are used in client code
-- are not inlined there, so the bloat is limited.
generalDf :: (domain -> (VecDualDelta r, Int))
          -> (VecDualDelta r -> DeltaState r -> Delta r -> domain')
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
      gradient = evalBindings ds st d
  in (gradient, value)

type Domain r = Data.Vector.Unboxed.Vector r

type Domain' r = Domain r

df :: forall r. (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
   => (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
   -> Domain r
   -> (Domain' r, r)
df =
  let initVars :: Domain r -> (VecDualDelta r, Int)
      initVars deltaInput =
        let dim = V.length deltaInput
        in ((deltaInput, V.generate dim (Var . DeltaId)), dim)
  in generalDf initVars evalBindingsV

gradDesc :: forall r. (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
         => r
         -> (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
         -> Int  -- ^ requested number of iterations
         -> Domain r  -- ^ initial parameters
         -> Domain' r
gradDesc gamma f n0 params0 = go n0 params0 where
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
        initVars = ((params, vVar), dim)
        gradient = fst $ generalDf (const initVars) evalBindingsV f params
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
    in go (pred n) paramsNew

gradDescStochastic
  :: forall r a. (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
  => r
  -> (a -> VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
  -> [a]  -- ^ training data
  -> Domain r  -- ^ initial parameters
  -> Domain' r
gradDescStochastic gamma f trainingData params0 = go trainingData params0 where
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
        initVars = ((params, vVar), dim)
        gradient = fst $ generalDf (const initVars) evalBindingsV (f a) params
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
    in go rest paramsNew

-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gradDescSmart :: forall r. (Ord r, Fractional r, Data.Vector.Unboxed.Unbox r)
              => (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
              -> Int  -- ^ requested number of iterations
              -> Domain r  -- ^ initial parameters
              -> (Domain' r, r)
gradDescSmart f n0 params0 = go n0 params0 0.1 gradient0 value0 0 where
  dim = V.length params0
  vVar = V.generate dim (Var . DeltaId)
  initVars0 :: (VecDualDelta r, Int)
  initVars0 = ((params0, vVar), dim)
  (gradient0, value0) = generalDf (const initVars0) evalBindingsV f params0
  go :: Int -> Domain r -> r -> Domain r -> r -> Int -> (Domain' r, r)
  go 0 !params !gamma _gradientPrev _valuePrev !_i = (params, gamma)
  go _ params 0 _ _ _ = (params, 0)
  go n params gamma gradientPrev valuePrev i =
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let paramsNew = V.zipWith (\p r -> p - gamma * r) params gradientPrev
        initVars = ((paramsNew, vVar), dim)
        (gradient, value) = generalDf (const initVars) evalBindingsV f paramsNew
    in if | V.all (== 0) gradientPrev -> (params, gamma)
          | value > valuePrev ->
              go n params (gamma / 2) gradientPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) paramsNew (gamma * 2) gradient value 0
          | otherwise -> go (pred n) paramsNew gamma gradient value (i + 1)

(*\) :: (DeltaMonad r m, Num r) => DualDelta r -> DualDelta r -> m (DualDelta r)
(*\) (D u u') (D v v') =
  returnLetD (u * v) (Add (Scale v u') (Scale u v'))

(+\) :: (DeltaMonad r m, Num r) => DualDelta r -> DualDelta r -> m (DualDelta r)
(+\) (D u u') (D v v') =
  returnLetD (u + v) (Add u' v')

(-\) :: (DeltaMonad r m, Num r) => DualDelta r -> DualDelta r -> m (DualDelta r)
(-\) (D u u') (D v v') =
  returnLetD (u - v) (Add u' (Scale (-1) v'))

negateDual :: (DeltaMonad r m, Num r) => DualDelta r -> m (DualDelta r)
negateDual (D v v') =
  returnLetD (- v) (Scale (-1) v')

-- Should be denoted by @/\@, but it would be misleading.
divideDual :: (DeltaMonad r m, Fractional r)
           => DualDelta r -> DualDelta r -> m (DualDelta r)
divideDual (D u u') (D v v') =
  returnLetD (u / v) (Scale (recip $ v * v) (Add (Scale v u') (Scale (- u) v')))

(**\) :: (DeltaMonad r m, Floating r)
      => DualDelta r -> DualDelta r -> m (DualDelta r)
(**\) (D u u') (D v v') =
  returnLetD (u ** v) (Add (Scale (v * (u ** (v - 1))) u')
                           (Scale ((u ** v) * log u) v'))

expDual :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
expDual (D u u') = do
  let expU = exp u
  returnLetD expU (Scale expU u')

logDual :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
logDual (D u u') =
  returnLetD (log u) (Scale (recip u) u')

scalar :: r -> DualDelta r
scalar k = D k Zero

scale :: (DeltaMonad r m, Num r) => r -> DualDelta r -> m (DualDelta r)
scale k (D u u') =
  returnLetD (k * u) (Scale k u')

-- In addition to convenience, this offers fusion of all bindings
-- coming from binary addition into a single binding.
sumDual :: forall m r . (DeltaMonad r m, Num r)
        => Data.Vector.Vector (DualDelta r)
        -> m (DualDelta r)
sumDual us = do
  let f :: DualDelta r -> DualDelta r -> DualDelta r
      f (D acc acc') (D u u') = D (acc + u) (Add acc' u')
      D sumUs sumUs' = V.foldl' f (scalar 0) us
  returnLetD sumUs sumUs'

-- The same as @sumDual@ but for lists. Inlined to help list fusion,
-- which is, alas, not guaranteed regardless.
sumListDual :: forall m r . (DeltaMonad r m, Num r)
            => [DualDelta r]
            -> m (DualDelta r)
{-# INLINE sumListDual #-}
sumListDual us = do
  let f :: DualDelta r -> DualDelta r -> DualDelta r
      f (D acc acc') (D u u') = D (acc + u) (Add acc' u')
      D sumUs sumUs' = foldl' f (scalar 0) us
  returnLetD sumUs sumUs'

-- Inlined to avoid the tiny overhead of calling an unknown function.
-- This operation is needed, because @sumListDual@ doesn't (always) fuse.
sumResultsDual :: forall m a r.
                    (DeltaMonad r m, Num r, Data.Vector.Unboxed.Unbox a)
               => (a -> m (DualDelta r))
               -> Data.Vector.Unboxed.Vector a
               -> m (DualDelta r)
{-# INLINE sumResultsDual #-}
sumResultsDual f as = do
  let g :: DualDelta r -> a -> m (DualDelta r)
      g (D acc acc') a = do
        (D u u') <- f a
        return $! D (acc + u) (Add acc' u')
  D sumUs sumUs' <- V.foldM g (scalar 0) as
  returnLetD sumUs sumUs'

tanhAct :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
tanhAct (D u u') = do
  let y = tanh u
  returnLetD y (Scale (1 - y * y) u')

reluAct :: (DeltaMonad r m, Num r, Ord r) => DualDelta r -> m (DualDelta r)
reluAct (D u u') =
  returnLetD (max 0 u) (Scale (if u > 0 then 1 else 0) u')

logisticAct :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
logisticAct (D u u') = do
  let y = recip (1 + exp (- u))
  returnLetD y (Scale (y * (1 - y)) u')

softMaxActUnfused :: (DeltaMonad r m, Floating r)
                  => Data.Vector.Vector (DualDelta r)
                  -> m (Data.Vector.Vector (DualDelta r))
softMaxActUnfused us = do
  expUs <- V.mapM expDual us
  sumExpUs <- sumDual expUs
  V.mapM (`divideDual` sumExpUs) expUs

-- | Compute the output of a neuron, without applying activation function,
-- from trainable inputs in @xs@ and parameters (the bias and weights)
-- at @vec@ starting at @offset@. Useful for neurons in the middle
-- of the network, receiving inputs from other neurons.
sumTrainableInputs :: forall m r.
                        (DeltaMonad r m, Num r, Data.Vector.Unboxed.Unbox r)
                   => Data.Vector.Vector (DualDelta r)
                   -> Int
                   -> VecDualDelta r
                   -> m (DualDelta r)
sumTrainableInputs xs offset vec = do
  let bias = var offset vec
      f :: DualDelta r -> Int -> DualDelta r -> DualDelta r
      f (D acc acc') i (D u u') =
        let (D v v') = var (offset + 1 + i) vec
        in D (acc + u * v) (Add acc' (Add (Scale v u') (Scale u v')))
      D xsum xsum' = V.ifoldl' f bias xs
  returnLetD xsum xsum'

-- | Compute the output of a neuron, without applying activation function,
-- from constant data in @xs@ and parameters (the bias and weights)
-- at @vec@ starting at @offset@. Useful for neurons at the bottom
-- of the network, tasked with ingesting the data.
sumConstantData :: forall m r.
                     (DeltaMonad r m, Num r, Data.Vector.Unboxed.Unbox r)
                => Domain r
                -> Int
                -> VecDualDelta r
                -> m (DualDelta r)
sumConstantData xs offset vec = do
  let bias = var offset vec
      f :: DualDelta r -> Int -> r -> DualDelta r
      f (D acc acc') i r =
        let (D v v') = var (offset + 1 + i) vec
        in D (acc + r * v) (Add acc' (Scale r v'))
      D xsum xsum' = V.ifoldl' f bias xs
  returnLetD xsum xsum'

lossSquaredUnfused :: (DeltaMonad r m, Num r)
                   => r -> DualDelta r -> m (DualDelta r)
lossSquaredUnfused targ res = do
  diff <- res -\ scalar targ
  diff *\ diff

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyUnfused
  :: forall m r. (DeltaMonad r m, Floating r, Data.Vector.Unboxed.Unbox r)
  => Data.Vector.Unboxed.Vector r
  -> Data.Vector.Vector (DualDelta r)
  -> m (DualDelta r)
lossCrossEntropyUnfused targ res = do
  let f :: DualDelta r -> Int -> DualDelta r -> m (DualDelta r)
      f !acc !i d = do
        rLog <- logDual d
        rLogScaled <- scale (targ V.! i) rLog
        acc +\ rLogScaled
  dotProductLog <- V.ifoldM' f (scalar 0) res
  negateDual dotProductLog




















-- recursion and recursive types
-- selective fusion of delta (for individual subfunctions: pre-computing,
--   inlining results and simplifying delta-expressions; the usual inlining
--   considerations apply)
-- checkpointing (limiting space usage?)
