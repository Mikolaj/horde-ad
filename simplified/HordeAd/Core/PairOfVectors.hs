{-# LANGUAGE CPP, TypeFamilies #-}
-- | The "pair of vectors" implementation of vectors of dual numbers.
-- This is much faster than "vector of pairs" implementation, but terribly
-- hard to use in case of rank 0 dual numbers, because they need to be stored
-- in unboxed vectors, unlike the other ranks. In particular, it's hard
-- to efficiently construct in @ST@ such pairs of vectors of rank 0 dual
-- numbers from monadic operations that create individual vector elements
-- (a bit easier in @IO@, but so far we managed to avoid @IO@).
--
-- For this reason, this representation is currently used only to represent
-- the inputs of functions, that is, dual numbers with initial values
-- of parameters and, in case of dual components containing delta-expressions,
-- with @Delta@ inputs assigned to each.
module HordeAd.Core.PairOfVectors
  ( ADInputs(..)
  , makeADInputs, at0, at1
  , ifoldlDual', foldlDual'
  ) where

import Prelude

import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.DualClass (Dual)
import HordeAd.Core.DualNumber

-- These are optimized as "pair of vectors" representing vectors of @ADVal@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).

data ADInputs d r = ADInputs
  { inputPrimal0 :: Domain0 r
  , inputDual0   :: Data.Vector.Vector (Dual d r)
  , inputPrimal1 :: Domain1 r
  , inputDual1   :: Data.Vector.Vector (Dual d (Vector r))
  }

makeADInputs
  :: Domains r
  -> ( Data.Vector.Vector (Dual d r)
     , Data.Vector.Vector (Dual d (Vector r)) )
  -> ADInputs d r
{-# INLINE makeADInputs #-}
makeADInputs (params0, params1)
             (vs0, vs1)
  = ADInputs params0 vs0 params1 vs1

at0 :: ADModeAndNum d r => ADInputs d r -> Int -> ADVal d r
{-# INLINE at0 #-}
at0 ADInputs{..} i = D (inputPrimal0 V.! i) (inputDual0 V.! i)

at1 :: ADInputs d r -> Int -> ADVal d (Vector r)
{-# INLINE at1 #-}
at1 ADInputs{..} i = D (inputPrimal1 V.! i) (inputDual1 V.! i)

ifoldlDual' :: forall a d r. ADModeAndNum d r
             => (a -> Int -> ADVal d r -> a)
             -> a
             -> ADInputs d r
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (inputDual0 V.! i)
        in f acc i b
  V.ifoldl' g a inputPrimal0

foldlDual' :: forall a d r. ADModeAndNum d r
            => (a -> ADVal d r -> a)
            -> a
            -> ADInputs d r
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (inputDual0 V.! i)
        in f acc b
  V.ifoldl' g a inputPrimal0
