-- | The "pair of vectors" implementation of vectors of dual numbers.
-- This is much faster than "vector of pairs" implementation, but terribly
-- hard to use, in particular to efficiently construct such pairs
-- of vectors using monadic operations in @ST@ (a bit easier in @IO@,
-- but so far we've managed to avoid it).
module HordeAd.PairOfVectors
  ( VecDualDelta
  , vecDualDeltaFromVars, var, vars, varV
  , ifoldMDelta', foldMDelta', ifoldlDelta', foldlDelta'
  ) where

import Prelude

import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Foreign.Storable (Storable)

import HordeAd.Delta
import HordeAd.DualDelta (DualDelta (..))

-- The "pair of vectors" type representing a vector of @DualDelta r@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).
type VecDualDelta r =
  ( -- The component for scalars, optimized as pair of vectors.
    Data.Vector.Storable.Vector r
  , Data.Vector.Vector (Delta r)
  , -- The component for vectors. This is a normal vector of "pairs".
    Data.Vector.Vector (DualDelta (Data.Vector.Storable.Vector r))
  )

vecDualDeltaFromVars
  :: Data.Vector.Vector (Delta r)
  -> Data.Vector.Vector (Delta (Data.Vector.Storable.Vector r))
  -> ( Data.Vector.Storable.Vector r
     , Data.Vector.Vector (Data.Vector.Storable.Vector r) )
  -> VecDualDelta r
{-# INLINE vecDualDeltaFromVars #-}
vecDualDeltaFromVars vVar vVarV (params, paramsV) =
  (params, vVar, V.zipWith D paramsV vVarV)

var :: Storable r
    => VecDualDelta r -> Int -> DualDelta r
var (vValue, vVar, _) i = D (vValue V.! i) (vVar V.! i)

varV :: VecDualDelta r -> Int -> DualDelta (Data.Vector.Storable.Vector r)
varV (_, _, vVecVars) i = vVecVars V.! i

-- Unsafe, but handy for toy examples.
vars :: Storable r
     => VecDualDelta r -> [DualDelta r]
vars vec = map (var vec) [0 ..]

ifoldMDelta' :: forall m a r. (Monad m, Storable r)
             => (a -> Int -> DualDelta r -> m a)
             -> a
             -> VecDualDelta r
             -> m a
{-# INLINE ifoldMDelta' #-}
ifoldMDelta' f a (vecR, vecD, _) = do
  let g :: a -> Int -> r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc i b
  V.ifoldM' g a vecR

foldMDelta' :: forall m a r. (Monad m, Storable r)
            => (a -> DualDelta r -> m a)
            -> a
            -> VecDualDelta r
            -> m a
{-# INLINE foldMDelta' #-}
foldMDelta' f a (vecR, vecD, _) = do
  let g :: a -> Int -> r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc b
  V.ifoldM' g a vecR

ifoldlDelta' :: forall a r. Storable r
             => (a -> Int -> DualDelta r -> a)
             -> a
             -> VecDualDelta r
             -> a
{-# INLINE ifoldlDelta' #-}
ifoldlDelta' f a (vecR, vecD, _) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc i b
  V.ifoldl' g a vecR

foldlDelta' :: forall a r. Storable r
            => (a -> DualDelta r -> a)
            -> a
            -> VecDualDelta r
            -> a
{-# INLINE foldlDelta' #-}
foldlDelta' f a (vecR, vecD, _) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc b
  V.ifoldl' g a vecR
