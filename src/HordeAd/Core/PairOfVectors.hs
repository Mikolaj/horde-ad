{-# LANGUAGE CPP, TypeFamilies #-}
-- | The "pair of vectors" implementation of vectors of dual numbers.
-- This is much faster than "vector of pairs" implementation, but terribly
-- hard to use in case of scalar dual numbers, in particular to efficiently
-- construct in @ST@ such pairs of vectors from monadic operations that create
-- vector elements (a bit easier in @IO@, but so far we managed to avoid @IO@).
-- For this reason, this representation is currently used only to represent
-- the inputs of functions, that is, dual numbers with initial values
-- of parameters and, in case of dual components that are delta-expressions,
-- with @Delta@ inputs assigned to each.
module HordeAd.Core.PairOfVectors
  ( ADInputs(..)
  , makeADInputs, at0, atList0, at1, at2, atX, atS
  , ifoldlDual', foldlDual'
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Matrix, Vector)

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
  , inputPrimal2 :: Domain2 r
  , inputDual2   :: Data.Vector.Vector (Dual d (Matrix r))
  , inputPrimalX :: DomainX r
  , inputDualX   :: Data.Vector.Vector (Dual d (OT.Array r))
  }

makeADInputs
  :: Domains r
  -> ( Data.Vector.Vector (Dual d r)
     , Data.Vector.Vector (Dual d (Vector r))
     , Data.Vector.Vector (Dual d (Matrix r))
     , Data.Vector.Vector (Dual d (OT.Array r)) )
  -> ADInputs d r
{-# INLINE makeADInputs #-}
makeADInputs (params0, params1, params2, paramsX)
                        (vs0, vs1, vs2, vsX)
  = ADInputs params0 vs0 params1 vs1 params2 vs2 paramsX vsX

at0 :: ADModeAndNum d r => ADInputs d r -> Int -> ADVal d r
{-# INLINE at0 #-}
at0 ADInputs{..} i = D (inputPrimal0 V.! i) (inputDual0 V.! i)

-- Unsafe, but handy for toy examples.
atList0 :: ADModeAndNum d r => ADInputs d r -> [ADVal d r]
atList0 vec = map (at0 vec) [0 ..]

at1 :: ADInputs d r -> Int -> ADVal d (Vector r)
{-# INLINE at1 #-}
at1 ADInputs{..} i = D (inputPrimal1 V.! i) (inputDual1 V.! i)

at2 :: ADInputs d r -> Int -> ADVal d (Matrix r)
{-# INLINE at2 #-}
at2 ADInputs{..} i = D (inputPrimal2 V.! i) (inputDual2 V.! i)

atX :: ADInputs d r -> Int -> ADVal d (OT.Array r)
{-# INLINE atX #-}
atX ADInputs{..} i = D (inputPrimalX V.! i) (inputDualX V.! i)

atS :: (ADModeAndNum d r, OS.Shape sh)
     => ADInputs d r -> Int -> ADVal d (OS.Array sh r)
{-# INLINE atS #-}
atS ADInputs{..} i =
#if defined(VERSION_ghc_typelits_natnormalise)
  inline fromXS $ D (inputPrimalX V.! i) (inputDualX V.! i)
#else
  undefined
#endif

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
