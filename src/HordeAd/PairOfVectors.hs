-- | The "pair of vectors" implementation of vectors of dual numbers.
-- This is much faster than "vector of pairs" implementation, but terribly
-- hard to use, in particular to efficiently construct such pairs
-- of vectors using monadic operations in @ST@ (a bit easier in @IO@,
-- but so far we've managed to avoid it).
module HordeAd.PairOfVectors
  ( VecDualNumber
  , vecDualNumberFromVars, var, vars, varV, varL
  , ifoldMDelta', foldMDelta', ifoldlDelta', foldlDelta'
  ) where

import Prelude

import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Foreign.Storable (Storable)
import           Numeric.LinearAlgebra (Matrix, Vector)

import HordeAd.Delta
import HordeAd.DualNumber (DualNumber (..))

-- The first two components of the triple are the "pair of vectors"
-- type representing a vector of @DualNumber r@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).
type VecDualNumber r =
  ( -- The component for scalars, optimized as pair of vectors.
    Vector r
  , Data.Vector.Vector (Delta r)
  , -- The component for vectors. This is a normal vector of "pairs".
    Data.Vector.Vector (DualNumber (Vector r))
  , -- The component for matrices.
    Data.Vector.Vector (DualNumber (Matrix r))
  )

vecDualNumberFromVars
  :: Data.Vector.Vector (Delta r)
  -> Data.Vector.Vector (Delta (Vector r))
  -> Data.Vector.Vector (Delta (Matrix r))
  -> ( Vector r
     , Data.Vector.Vector (Vector r)
     , Data.Vector.Vector (Matrix r) )
  -> VecDualNumber r
{-# INLINE vecDualNumberFromVars #-}
vecDualNumberFromVars vVar vVarV vVarL (params, paramsV, paramsL) =
  (params, vVar, V.zipWith D paramsV vVarV, V.zipWith D paramsL vVarL)

var :: Storable r => VecDualNumber r -> Int -> DualNumber r
var (vValue, vVar, _, _) i = D (vValue V.! i) (vVar V.! i)

varV :: VecDualNumber r -> Int -> DualNumber (Vector r)
varV (_, _, v, _) i = v V.! i

varL :: VecDualNumber r -> Int -> DualNumber (Matrix r)
varL (_, _, _, v) i = v V.! i

-- Unsafe, but handy for toy examples.
vars :: Storable r => VecDualNumber r -> [DualNumber r]
vars vec = map (var vec) [0 ..]

ifoldMDelta' :: forall m a r. (Monad m, Storable r)
             => (a -> Int -> DualNumber r -> m a)
             -> a
             -> VecDualNumber r
             -> m a
{-# INLINE ifoldMDelta' #-}
ifoldMDelta' f a (vecR, vecD, _, _) = do
  let g :: a -> Int -> r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc i b
  V.ifoldM' g a vecR

foldMDelta' :: forall m a r. (Monad m, Storable r)
            => (a -> DualNumber r -> m a)
            -> a
            -> VecDualNumber r
            -> m a
{-# INLINE foldMDelta' #-}
foldMDelta' f a (vecR, vecD, _, _) = do
  let g :: a -> Int -> r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc b
  V.ifoldM' g a vecR

ifoldlDelta' :: forall a r. Storable r
             => (a -> Int -> DualNumber r -> a)
             -> a
             -> VecDualNumber r
             -> a
{-# INLINE ifoldlDelta' #-}
ifoldlDelta' f a (vecR, vecD, _, _) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc i b
  V.ifoldl' g a vecR

foldlDelta' :: forall a r. Storable r
            => (a -> DualNumber r -> a)
            -> a
            -> VecDualNumber r
            -> a
{-# INLINE foldlDelta' #-}
foldlDelta' f a (vecR, vecD, _, _) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc b
  V.ifoldl' g a vecR
