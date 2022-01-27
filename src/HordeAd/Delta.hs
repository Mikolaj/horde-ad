{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function.
--
-- The algebraic structure here is, more or less, a vector space.
-- The extra ingenious variable constructor is used both for avoiding
-- exponential blowup and replacing the one-hot functionality with
-- something much cheaper.
module HordeAd.Delta
  ( Delta (..)
  , DeltaId (..)
  , DeltaState (..)
  , evalBindingsV
  ) where

import Prelude

import           Control.Exception (assert)
import           Control.Monad (foldM, when)
import           Control.Monad.ST.Strict (ST)
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
  deriving (Show, Eq, Ord)

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
      evalUnlessZero (DeltaId !i) d = do
        r <- store `VM.read` i
        when (r /= 0) $  -- we init with exactly 0 above so the comparison is OK
          eval r d
        return $! DeltaId (pred i)
  minusOne <- foldM evalUnlessZero (DeltaId $ pred storeSize) (deltaBindings st)
  let _A = assert (minusOne == DeltaId (-1)) ()
  return $! VM.slice 0 dim store

evalBindingsV :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
              => Int -> DeltaState r -> Delta r
              -> Data.Vector.Unboxed.Vector r
evalBindingsV dim st d0 = V.create $ buildVector dim st d0
