{-# LANGUAGE FunctionalDependencies, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-missing-methods #-}
module HordeAd.DualDelta where

import Prelude

import           Data.List (foldl')
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed

import HordeAd.Delta (Delta (..))

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

class (Monad m, Functor m, Applicative m) => DeltaMonad r m | m -> r where
  returnLet :: DualDelta r -> m (DualDelta r)

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
    let recipSq = recip (v * v)
    in D (u / v) (Add (Scale (v * recipSq) u') (Scale (- u * recipSq) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in D (recip v) (Scale minusRecipSq v')
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

-- Most of the operations below are selectively have Delta
-- let-bindings --- close to only as many as really needed.
-- The number of let-bindings is enough to guarantee that
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

reluLeakyAct :: (DeltaMonad r m, Fractional r, Ord r)
             => DualDelta r -> m (DualDelta r)
reluLeakyAct (D u u') =
  returnLet $ D (if u > 0 then u else 0.01 * u)
                (Scale (if u > 0 then 1 else 0.01) u')

logisticAct :: (DeltaMonad r m, Floating r) => DualDelta r -> m (DualDelta r)
logisticAct (D u u') = do
  let y = recip (1 + exp (- u))
  returnLet $ D y (Scale (y * (1 - y)) u')

softMaxAct :: (DeltaMonad r m, Floating r)
           => Data.Vector.Vector (DualDelta r)
           -> m (Data.Vector.Vector (DualDelta r))
softMaxAct us = do
  let expUs = V.map exp us
  -- This has to be let-bound, because it's used many times below.
  sumExpUs <- sumDual expUs
  let recipSum = recip sumExpUs
  V.mapM (*\ recipSum) expUs

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
