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
  , makeDualNumberVariables, var, vars, varV, varL, varX, varS
  , ifoldMDelta', foldMDelta', ifoldlDelta', foldlDelta'
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V

import HordeAd.Core.DualNumber
  (Domain, DomainL, DomainV, DomainX, Domains, DualNumber (..))
import HordeAd.Core.DualClass

-- These are optimized as "pair of vectors" representing vectors of @DualNumber@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).

type DualNumberVariables r =
  ( Domain r
  , Data.Vector.Vector r
  , DomainV r
  , Data.Vector.Vector (Tensor1 r)
  , DomainL r
  , Data.Vector.Vector (Tensor2 r)
  , DomainX r
  , Data.Vector.Vector (TensorX r)
  )

makeDualNumberVariables
  :: Domains r
  -> ( Data.Vector.Vector r
     , Data.Vector.Vector (Tensor1 r)
     , Data.Vector.Vector (Tensor2 r)
     , Data.Vector.Vector (TensorX r) )
  -> DualNumberVariables r
{-# INLINE makeDualNumberVariables #-}
makeDualNumberVariables (params, paramsV, paramsL, paramsX) (vs, vsV, vsL, vsX)
  = (params, vs, paramsV, vsV, paramsL, vsL, paramsX, vsX)

var :: IsScalar r => DualNumberVariables r -> Int -> DualNumber r
var (vValue, vVar, _, _, _, _, _, _) i = D (vValue V.! i) (vVar V.! i)

-- Unsafe, but handy for toy examples.
vars :: IsScalar r => DualNumberVariables r -> [DualNumber r]
vars vec = map (var vec) [0 ..]

varV :: IsScalar r => DualNumberVariables r -> Int -> DualNumber (Tensor1 r)
varV (_, _, vValue, vVar, _, _, _, _) i = D (vValue V.! i) (vVar V.! i)

varL :: IsScalar r => DualNumberVariables r -> Int -> DualNumber (Tensor2 r)
varL (_, _, _, _, vValue, vVar, _, _) i = D (vValue V.! i) (vVar V.! i)

varX :: IsScalar r => DualNumberVariables r -> Int -> DualNumber (TensorX r)
varX (_, _, _, _, _, _, vValue, vVar) i = D (vValue V.! i) (vVar V.! i)

varS :: (OS.Shape sh, IsScalarS sh r)
     => DualNumberVariables r -> Int -> DualNumber (TensorS sh r)
varS (_, _, _, _, _, _, vValue, vVar) i =
  D (Data.Array.Convert.convert $ vValue V.! i) (dFromXS $ vVar V.! i)

ifoldMDelta' :: forall m a r. (Monad m, IsScalar r)
             => (a -> Int -> DualNumber r -> m a)
             -> a
             -> DualNumberVariables r
             -> m a
{-# INLINE ifoldMDelta' #-}
ifoldMDelta' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> Primal r -> m a
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
foldMDelta' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> Primal r -> m a
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
ifoldlDelta' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> Primal r -> a
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
foldlDelta' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> Primal r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc b
  V.ifoldl' g a vecR
