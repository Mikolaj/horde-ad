{-# LANGUAGE TypeFamilies #-}
-- | The "pair of vectors" implementation of vectors of dual numbers.
-- This is much faster than "vector of pairs" implementation, but terribly
-- hard to use in case of scalar dual numbers, in particular to efficiently
-- construct in @ST@ such pairs of vectors from monadic operations that create
-- vector elements (a bit easier in @IO@, but so far we managed to avoid @IO@).
-- For this reason, this representation is currently used only to represent
-- the inputs of functions, that is, dual numbers with initial values
-- of parameters and, in case of dual components that are delta-expressions,
-- with @Delta@ variables assigned to each.
module HordeAd.Core.PairOfVectors
  ( DualNumberVariables
  , makeDualNumberVariables, var0, vars, var1, var2, varX, varS
  , ifoldMDual', foldMDual', ifoldlDual', foldlDual'
  ) where

import Prelude

import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)

import HordeAd.Core.DualNumber

-- These are optimized as "pair of vectors" representing vectors of @DualNumber@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).

type DualNumberVariables r =
  ( Domain0 r
  , Data.Vector.Vector r
  , Domain1 r
  , Data.Vector.Vector (Tensor1 r)
  , Domain2 r
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
makeDualNumberVariables (params0, params1, params2, paramsX)
                        (vs0, vs1, vs2, vsX)
  = (params0, vs0, params1, vs1, params2, vs2, paramsX, vsX)

var0 :: IsScalar r => DualNumberVariables r -> Int -> DualNumber r
var0 (vValue, vVar, _, _, _, _, _, _) i = D (vValue V.! i) (vVar V.! i)

-- Unsafe, but handy for toy examples.
vars :: IsScalar r => DualNumberVariables r -> [DualNumber r]
vars vec = map ( var0 vec) [0 ..]

var1 :: IsScalar r => DualNumberVariables r -> Int -> DualNumber (Tensor1 r)
var1 (_, _, vValue, vVar, _, _, _, _) i = D (vValue V.! i) (vVar V.! i)

var2 :: IsScalar r => DualNumberVariables r -> Int -> DualNumber (Tensor2 r)
var2 (_, _, _, _, vValue, vVar, _, _) i = D (vValue V.! i) (vVar V.! i)

varX :: IsScalar r => DualNumberVariables r -> Int -> DualNumber (TensorX r)
varX (_, _, _, _, _, _, vValue, vVar) i = D (vValue V.! i) (vVar V.! i)

varS :: (IsScalar r, OS.Shape sh)
     => DualNumberVariables r -> Int -> DualNumber (TensorS r sh)
varS (_, _, _, _, _, _, vValue, vVar) i =
  inline fromXS $ D (vValue V.! i) (vVar V.! i)

ifoldMDual' :: forall m a r. (Monad m, IsScalar r)
             => (a -> Int -> DualNumber r -> m a)
             -> a
             -> DualNumberVariables r
             -> m a
{-# INLINE ifoldMDual' #-}
ifoldMDual' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> Primal r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc i b
  V.ifoldM' g a vecR

foldMDual' :: forall m a r. (Monad m, IsScalar r)
            => (a -> DualNumber r -> m a)
            -> a
            -> DualNumberVariables r
            -> m a
{-# INLINE foldMDual' #-}
foldMDual' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> Primal r -> m a
      g !acc i valX = do
        let !b = D valX (vecD V.! i)
        f acc b
  V.ifoldM' g a vecR

ifoldlDual' :: forall a r. IsScalar r
             => (a -> Int -> DualNumber r -> a)
             -> a
             -> DualNumberVariables r
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> Primal r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc i b
  V.ifoldl' g a vecR

foldlDual' :: forall a r. IsScalar r
            => (a -> DualNumber r -> a)
            -> a
            -> DualNumberVariables r
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> Primal r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc b
  V.ifoldl' g a vecR
