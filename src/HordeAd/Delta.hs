{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, KindSignatures #-}
-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function. Neel Krishnaswami calls that "sparse vector expressions",
-- and indeed the codomain of the evaluation function is a vector,
-- because the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- The algebraic structure here is, more or less, a vector space.
-- The extra ingenious variable constructor is used both to represent
-- sharing in order to avoid exponential blowup and to replace the one-hot
-- functionality with something cheaper and more uniform.
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
import           Data.Kind (Type)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Mutable
import qualified Data.Vector.Storable
import qualified Data.Vector.Storable.Mutable
import           Foreign.Storable (Storable)

-- Tagless final doesn't seem to work well, because we need to gather
-- @Delta@ while doing @DualDelta@ operations, but evaluate on concrete
-- vectors that correspond to only the second component of dual numbers.
-- Also, initial encoding gives us full control over
-- when to evaluate. With final, we'd need to be careful
-- about laziness to ensure the optimal evaluation order is chosen
-- (whatever it is for a given differentiated program).
data Delta :: Type -> Type where
  Zero :: Delta r
  Scale :: r -> Delta r -> Delta r
  Add :: Delta r -> Delta r -> Delta r
  Var :: DeltaId -> Delta r
  Dot :: Data.Vector.Storable.Vector r -> Delta (Data.Vector.Storable.Vector r)
      -> Delta r
  Konst :: Delta r -> Int -> Delta (Data.Vector.Storable.Vector r)

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
  , deltaBindings :: [Either (Delta r) (Delta (Data.Vector.Storable.Vector r))]
  }

buildVector :: forall s r. (Eq r, Num r, Storable r)
            => Int -> DeltaState r -> Delta r
            -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                    , Data.Vector.Mutable.MVector
                        s (Data.Vector.Storable.Vector r) )
buildVector dim st d0 = do
  let DeltaId storeSize = deltaCounter st
  store <- VM.replicate storeSize 0
  -- TODO: this allocation costs us 7% runtime in 25/train2 2500 750:
  storeV <- VM.replicate storeSize (V.empty :: Data.Vector.Storable.Vector r)
  let eval :: r -> Delta r -> ST s ()
      eval !r = \case
        Zero -> return ()
        Scale k d -> eval (k * r) d
        Add d1 d2 -> eval r d1 >> eval r d2
        Var (DeltaId i) -> VM.modify store (+ r) i
        Dot vr vd -> evalV (V.map (* r) vr) vd
        Konst{} -> error "buildVector: konst can't result in a scalar"
      evalV :: Data.Vector.Storable.Vector r
            -> Delta (Data.Vector.Storable.Vector r)
            -> ST s ()
      evalV !vr = \case
        Zero -> return ()
        Scale k d -> evalV (V.zipWith (*) k vr) d
        Add d1 d2 -> evalV vr d1 >> evalV vr d2
        Var (DeltaId i) -> VM.modify storeV (V.zipWith (+) vr) i
        Dot{} -> error "buildVector: unboxed vectors of vectors not possible"
        Konst d _n -> V.mapM_ (\r -> eval r d) vr
  eval 1 d0  -- dt is 1 or hardwired in f
  let evalUnlessZero :: DeltaId
                     -> Either (Delta r) (Delta (Data.Vector.Storable.Vector r))
                     -> ST s DeltaId
      evalUnlessZero (DeltaId !i) (Left d) = do
        r <- store `VM.read` i
        when (r /= 0) $  -- we init with exactly 0 above so the comparison is OK
          eval r d
        return $! DeltaId (pred i)
      evalUnlessZero (DeltaId !i) (Right d) = do
        r <- storeV `VM.read` i
        when (r /= V.empty) $
          evalV r d
        return $! DeltaId (pred i)
  minusOne <- foldM evalUnlessZero (DeltaId $ pred storeSize) (deltaBindings st)
  let _A = assert (minusOne == DeltaId (-1)) ()
  return (VM.slice 0 dim store, VM.slice 0 dim storeV)

evalBindingsV2 :: forall r. (Eq r, Num r, Storable r)
               => Int -> DeltaState r -> Delta r
               -> ( Data.Vector.Storable.Vector r
                  , Data.Vector.Vector (Data.Vector.Storable.Vector r) )
evalBindingsV2 dim st d0 =
  let built :: forall s.
                 ST s ( Data.Vector.Storable.Mutable.MVector s r
                      , Data.Vector.Mutable.MVector
                          s (Data.Vector.Storable.Vector r) )
      built = buildVector dim st d0
  in ( V.create $ fst <$> built
     , V.create $ snd <$> built )
       -- TODO: this probably runs buildVector twice;
       -- thawing/freezing or IO is needed?

-- for compatibility with old engine
evalBindingsV :: forall r. (Eq r, Num r, Storable r)
              => Int -> DeltaState r -> Delta r
              -> (Data.Vector.Storable.Vector r)
evalBindingsV dim st d0 = fst $ evalBindingsV2 dim st d0
