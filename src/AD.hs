{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-missing-methods #-}
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
import qualified Data.Vector.Unboxed.Mutable

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
  deriving (Show, Eq, Ord)

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

-- The "pair of vectors" type representing a vector of @DualDelta r@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).
type VecDualDelta r = (Domain r, Data.Vector.Vector (Delta r))

ifoldMDelta' :: forall m a r. (Monad m, Data.Vector.Unboxed.Unbox r)
             => (a -> Int -> DualDelta r -> m a)
             -> a
             -> VecDualDelta r
             -> m a
{-# INLINE ifoldMDelta' #-}
ifoldMDelta' f a (vecR, vecD) = do
  let g :: a -> Int -> r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc i b
  V.ifoldM' g a vecR

foldMDelta' :: forall m a r. (Monad m, Data.Vector.Unboxed.Unbox r)
            => (a -> DualDelta r -> m a)
            -> a
            -> VecDualDelta r
            -> m a
{-# INLINE foldMDelta' #-}
foldMDelta' f a (vecR, vecD) = do
  let g :: a -> Int -> r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc b
  V.ifoldM' g a vecR

ifoldlDelta' :: forall a r. Data.Vector.Unboxed.Unbox r
             => (a -> Int -> DualDelta r -> a)
             -> a
             -> VecDualDelta r
             -> a
{-# INLINE ifoldlDelta' #-}
ifoldlDelta' f a (vecR, vecD) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc i b
  V.ifoldl' g a vecR

foldlDelta' :: forall a r. Data.Vector.Unboxed.Unbox r
            => (a -> DualDelta r -> a)
            -> a
            -> VecDualDelta r
            -> a
{-# INLINE foldlDelta' #-}
foldlDelta' f a (vecR, vecD) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc b
  V.ifoldl' g a vecR

buildVector :: forall s r. (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
            => Int -> DeltaState r -> Delta r
            -> ST s (Data.Vector.Unboxed.Mutable.MVector s r)
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

evalBindingsV :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
              => VecDualDelta i -> DeltaState r -> Delta r
              -> Data.Vector.Unboxed.Vector r
evalBindingsV ds st d0 = V.create $ buildVector (V.length $ snd ds) st d0

class (Monad m, Functor m, Applicative m) => DeltaMonad r m | m -> r where
  returnLet :: DualDelta r -> m (DualDelta r)

newtype DeltaMonadGradient r a = DeltaMonadGradient
  { runDeltaMonadGradient :: State (DeltaState r) a }
  deriving (Monad, Functor, Applicative)

instance DeltaMonad r (DeltaMonadGradient r) where
  -- TODO: when varied benchmarks are available, check if returning v always,
  -- except for @Add@, is faster. Probably @Zero@ and @Var@ appear too rarely
  -- to matter if @Scale@ turns out to require bindings.
  returnLet (D u u') = DeltaMonadGradient $ do
    i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = succ i
        , deltaBindings = u' : deltaBindings s
        }
    return $! D u (Var i)

type DeltaMonadValue r = Identity

instance DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = Identity $ D u Zero

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
    => VecDualDelta r -> Int -> DualDelta r
var (vValue, vVar) i = D (vValue V.! i) (vVar V.! i)

-- Unsafe, but handy for toy examples.
vars :: Data.Vector.Unboxed.Unbox r
     => VecDualDelta r -> [DualDelta r]
vars vec = map (var vec) [0 ..]

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

-- | Simple Gradient Descent.
gdSimple :: forall r. (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
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
        initVars = ((params, vVar), dim)
        gradient = fst $ generalDf (const initVars) evalBindingsV f params
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
    in go (pred n) paramsNew

-- | Stochastic Gradient Descent.
sgd :: forall r a. (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
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
        initVars = ((params, vVar), dim)
        gradient = fst $ generalDf (const initVars) evalBindingsV (f a) params
        paramsNew = V.zipWith (\i r -> i - gamma * r) params gradient
    in go rest paramsNew

-- | Relatively Smart Gradient Descent.
-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gdSmart :: forall r. (Ord r, Fractional r, Data.Vector.Unboxed.Unbox r)
        => (VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
        -> Int  -- ^ requested number of iterations
        -> Domain r  -- ^ initial parameters
        -> (Domain' r, r)
gdSmart f n0 params0 = go n0 params0 0.1 gradient0 value0 0 where
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

scalar :: r -> DualDelta r
scalar r = D r Zero

scale :: Num r => r -> DualDelta r -> DualDelta r
scale r (D u u') = D (r * u) (Scale r u')

-- This instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so defaulting to the derived instance.
deriving instance Eq r => Eq (DualDelta r)

deriving instance Ord r => Ord (DualDelta r)

-- These instances are dangerous. Expressions should be wrapped in
-- the monadic @returnLet@ whenever there is a possibility they can be
-- used multiple times in a larger expression. Safer yet, monadic arithmetic
-- operations that already include @returnLet@ should be used instead,
-- such as @+\@, @*\@, etc.
instance Num r => Num (DualDelta r) where
  D u u' + D v v' = D (u + v) (Add u' v')
  D u u' - D v v' = D (u - v) (Add u' (Scale (-1) v'))
  D u u' * D v v' = D (u * v) (Add (Scale v u') (Scale u v'))
  negate (D v v') = D (- v) (Scale (-1) v')
  abs = undefined  -- TODO
  signum = undefined  -- TODO
  fromInteger = scalar . fromInteger

(+\) :: (DeltaMonad r m, Num r) => DualDelta r -> DualDelta r -> m (DualDelta r)
(+\) u v = returnLet $ u + v

(-\) :: (DeltaMonad r m, Num r) => DualDelta r -> DualDelta r -> m (DualDelta r)
(-\) u v = returnLet $ u - v

(*\) :: (DeltaMonad r m, Num r) => DualDelta r -> DualDelta r -> m (DualDelta r)
(*\) u v = returnLet $ u * v

negateDual :: (DeltaMonad r m, Num r) => DualDelta r -> m (DualDelta r)
negateDual v = returnLet $ -v

instance Real r => Real (DualDelta r) where
  toRational = undefined  -- TODO?

instance Fractional r => Fractional (DualDelta r) where
  D u u' / D v v' =
    D (u / v) (Scale (recip $ v * v) (Add (Scale v u') (Scale (- u) v')))
  recip = undefined  -- TODO
  fromRational = scalar . fromRational

-- Should be denoted by @/\@, but it would be misleading.
divideDual :: (DeltaMonad r m, Fractional r)
           => DualDelta r -> DualDelta r -> m (DualDelta r)
divideDual u v = returnLet $ u / v

instance Floating r => Floating (DualDelta r) where
  pi = scalar pi
  exp (D u u') = let expU = exp u
                 in D expU (Scale expU u')
  log (D u u') = D (log u) (Scale (recip u) u')
  sqrt = undefined  -- TODO
  D u u' ** D v v' = D (u ** v) (Add (Scale (v * (u ** (v - 1))) u')
                                     (Scale ((u ** v) * log u) v'))
  logBase = undefined  -- TODO
  sin (D u u') = D (sin u) (Scale (cos u) u')
  cos (D u u') = D (cos u) (Scale (- (sin u)) u')
  tan = undefined  -- TODO
  asin = undefined  -- TODO
  acos = undefined  -- TODO
  atan = undefined  -- TODO
  sinh = undefined  -- TODO
  cosh = undefined  -- TODO
  tanh (D u u') = let y = tanh u
                  in D y (Scale (1 - y * y) u')
  asinh = undefined  -- TODO
  acosh = undefined  -- TODO
  atanh = undefined  -- TODO

expDual :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
expDual u = returnLet $ exp u

logDual :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
logDual u = returnLet $ log u

(**\) :: (DeltaMonad r m, Floating r)
      => DualDelta r -> DualDelta r -> m (DualDelta r)
(**\) u v = returnLet $ u ** v

tanhDual :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
tanhDual u = returnLet $ tanh u

instance RealFrac r => RealFrac (DualDelta r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance RealFloat r => RealFloat (DualDelta r) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in D (atan2 u v) (Add (Scale (- u * t) v') (Scale (v * t) u'))
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a continuous codomain

-- Most of the operations below are selectively fused.
-- In principle, they should be coded in a way that guarantees that
-- no exponential explosion can happen regardless of context
-- in which they are used, if only all their arguments are let-bound.

scaleDual :: (DeltaMonad r m, Num r) => r -> DualDelta r -> m (DualDelta r)
scaleDual r u = returnLet $ scale r u

-- Optimized and clearer to write @u ** 2@.
squareDual :: (DeltaMonad r m, Num r) => DualDelta r -> m (DualDelta r)
squareDual (D u u') = returnLet $ D (u * u) (Scale (2 * u) u')

-- In addition to convenience, this eliminates all Delta bindings
-- coming from binary addition into a single binding
-- (and so makes automatic fusion possible in the future).
-- BTW, this is also a dot product with a vector that contains only ones.
sumDual :: forall m r. (DeltaMonad r m, Num r)
        => Data.Vector.Vector (DualDelta r)
        -> m (DualDelta r)
sumDual us = returnLet $ V.foldl' (+) (scalar 0) us

-- The same as @sumDual@ but for lists. Inlined to help list fusion,
-- which is, alas, not guaranteed regardless.
sumListDual :: forall m r. (DeltaMonad r m, Num r)
            => [DualDelta r]
            -> m (DualDelta r)
{-# INLINE sumListDual #-}
sumListDual us = returnLet $ foldl' (+) (scalar 0) us

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
      g !acc a = do
        u <- f a
        return $! acc + u
  sumUs <- V.foldM g (scalar 0) as
  returnLet sumUs

tanhAct :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
tanhAct = tanhDual

reluAct :: (DeltaMonad r m, Num r, Ord r) => DualDelta r -> m (DualDelta r)
reluAct (D u u') =
  returnLet $ D (max 0 u) (Scale (if u > 0 then 1 else 0) u')

logisticAct :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
logisticAct (D u u') = do
  let y = recip (1 + exp (- u))
  returnLet $ D y (Scale (y * (1 - y)) u')

softMaxAct :: (DeltaMonad r m, Floating r)
           => Data.Vector.Vector (DualDelta r)
           -> m (Data.Vector.Vector (DualDelta r))
softMaxAct us = do
  let expUs = V.map exp us
  -- This has to be let-bound, becuse it's used many times below.
  sumExpUs <- sumDual expUs
  V.mapM (`divideDual` sumExpUs) expUs

-- | Compute the output of a neuron, without applying activation function,
-- from trainable inputs in @xs@ and parameters (the bias and weights)
-- at @vec@ starting at @offset@. Useful for neurons in the middle
-- of the network, receiving inputs from other neurons.
--
-- Note that functions like that, with Delta in the type signature
-- (which is really indispensable due to accessing variable parameters
-- in a special way) make it impossible to implement the function
-- to be differentiated as fully polymorphic @:: Num r => [r] -> m r@
-- function and so have no overhead when computing the value
-- with a dummy monad. Another case is selectively fused operations,
-- unless we include all of them, even very ad hoc ones,
-- in a class with implementations both on @D@ and on plain @r@.
sumTrainableInputs :: forall m r.
                        (DeltaMonad r m, Num r, Data.Vector.Unboxed.Unbox r)
                   => Data.Vector.Vector (DualDelta r)
                   -> Int
                   -> VecDualDelta r
                   -> m (DualDelta r)
sumTrainableInputs xs offset vec = do
  let bias = var vec offset
      f :: DualDelta r -> Int -> DualDelta r -> DualDelta r
      f !acc i u =
        let v = var vec (offset + 1 + i)
        in acc + u * v
  returnLet $ V.ifoldl' f bias xs

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
  let bias = var vec offset
      f :: DualDelta r -> Int -> r -> DualDelta r
      f !acc i r =
        let v = var vec (offset + 1 + i)
        in acc + scale r v
  returnLet $ V.ifoldl' f bias xs

lossSquared :: (DeltaMonad r m, Num r)
            => r -> DualDelta r -> m (DualDelta r)
lossSquared targ res = squareDual $ res - scalar targ

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy
  :: forall m r. (DeltaMonad r m, Floating r, Data.Vector.Unboxed.Unbox r)
  => Data.Vector.Unboxed.Vector r
  -> Data.Vector.Vector (DualDelta r)
  -> m (DualDelta r)
lossCrossEntropy targ res = do
  let f :: DualDelta r -> Int -> DualDelta r -> DualDelta r
      f !acc i d = acc + scale (targ V.! i) (log d)
  negateDual $ V.ifoldl' f (scalar 0) res




















-- recursion and recursive types
-- selective fusion of delta (for individual subfunctions: pre-computing,
--   inlining results and simplifying delta-expressions; the usual inlining
--   considerations apply)
-- checkpointing (limiting space usage?)
