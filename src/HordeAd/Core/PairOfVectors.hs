{-# LANGUAGE TypeFamilies #-}
-- | The "pair of vectors" implementation of vectors of dual numbers.
-- This is much faster than "vector of pairs" implementation, but terribly
-- hard to use in case of scalar dual numbers, in particular to efficiently
-- construct in @ST@ such pairs of vectors from monadic operations that create
-- vector elements (a bit easier in @IO@, but so far we managed to avoid @IO@).
-- For this reason, this representation is currently used only to represent
-- the inputs of functions, that is, dual numbers with initial values
-- of parameters and with `Delta` variables assigned to each.
module HordeAd.Core.PairOfVectors
  ( DualNumberVariables
  , makeDualNumberVariables, var, vars, varV, varL
  , ifoldMDelta', foldMDelta', ifoldlDelta', foldlDelta'
  ) where

import Prelude

import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Vector)

import HordeAd.Core.DualNumber (DualNumber (..))
import HordeAd.Core.IsTensor

-- These are optimized as "pair of vectors" representing vectors of @DualNumber@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).
type DualNumberVariables r =
  ( Vector r
  , Data.Vector.Vector (DeltaExpression r)
  , Data.Vector.Vector (Vector r)
  , Data.Vector.Vector (DeltaExpression (Vector r))
  , Data.Vector.Vector (Matrix r)
  , Data.Vector.Vector (DeltaExpression (Matrix r))
  )

makeDualNumberVariables
  :: ( Vector r
     , Data.Vector.Vector (Vector r)
     , Data.Vector.Vector (Matrix r) )
  -> ( Data.Vector.Vector (DeltaExpression r)
     , Data.Vector.Vector (DeltaExpression (Vector r))
     , Data.Vector.Vector (DeltaExpression (Matrix r)) )
  -> DualNumberVariables r
{-# INLINE makeDualNumberVariables #-}
makeDualNumberVariables (params, paramsV, paramsL) (vs, vsV, vsL)
  = (params, vs, paramsV, vsV, paramsL, vsL)

var :: IsScalar r => DualNumberVariables r -> Int -> DualNumber r
var (vValue, vVar, _, _, _, _) i = D (vValue V.! i) (vVar V.! i)

varV :: DualNumberVariables r -> Int -> DualNumber (Vector r)
varV (_, _, vValue, vVar, _, _) i = D (vValue V.! i) (vVar V.! i)

varL :: DualNumberVariables r -> Int -> DualNumber (Matrix r)
varL (_, _, _, _, vValue, vVar) i = D (vValue V.! i) (vVar V.! i)

-- Unsafe, but handy for toy examples.
vars :: IsScalar r => DualNumberVariables r -> [DualNumber r]
vars vec = map (var vec) [0 ..]

ifoldMDelta' :: forall m a r. (Monad m, IsScalar r)
             => (a -> Int -> DualNumber r -> m a)
             -> a
             -> DualNumberVariables r
             -> m a
{-# INLINE ifoldMDelta' #-}
ifoldMDelta' f a (vecR, vecD, _, _, _, _) = do
  let g :: a -> Int -> r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc i b
  V.ifoldM' g a vecR

foldMDelta' :: forall m a r. (Monad m, IsScalar r)
            => (a -> DualNumber r -> m a)
            -> a
            -> DualNumberVariables r
            -> m a
{-# INLINE foldMDelta' #-}
foldMDelta' f a (vecR, vecD, _, _, _, _) = do
  let g :: a -> Int -> r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc b
  V.ifoldM' g a vecR

ifoldlDelta' :: forall a r. IsScalar r
             => (a -> Int -> DualNumber r -> a)
             -> a
             -> DualNumberVariables r
             -> a
{-# INLINE ifoldlDelta' #-}
ifoldlDelta' f a (vecR, vecD, _, _, _, _) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc i b
  V.ifoldl' g a vecR

foldlDelta' :: forall a r. IsScalar r
            => (a -> DualNumber r -> a)
            -> a
            -> DualNumberVariables r
            -> a
{-# INLINE foldlDelta' #-}
foldlDelta' f a (vecR, vecD, _, _, _, _) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc b
  V.ifoldl' g a vecR
