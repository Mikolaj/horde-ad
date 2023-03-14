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
  , makeADInputs, nullADInputs, at0, at1, at2, atX, atS
  , ifoldlDual', foldlDual'
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)

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
makeADInputs Domains{..} (vs0, vs1, vs2, vsX)
  = ADInputs domains0 vs0 domains1 vs1 domains2 vs2 domainsX vsX

inputsToDomains :: ADInputs d r -> Domains r
inputsToDomains ADInputs{..} =
  Domains inputPrimal0 inputPrimal1 inputPrimal2 inputPrimalX

nullADInputs :: Numeric r => ADInputs d r -> Bool
nullADInputs adinputs = nullDomains (inputsToDomains adinputs)

-- We could use @dDnotShared@ here and below, but the gains are negligible.
at0 :: ADModeAndNum d r => ADInputs d r -> Int -> ADVal d r
{-# INLINE at0 #-}
at0 ADInputs{..} i = dD (inputPrimal0 V.! i) (inputDual0 V.! i)

at1 :: ADModeAndNum d r => ADInputs d r -> Int -> ADVal d (Vector r)
{-# INLINE at1 #-}
at1 ADInputs{..} i = dD (inputPrimal1 V.! i) (inputDual1 V.! i)

at2 :: ADModeAndNum d r => ADInputs d r -> Int -> ADVal d (Matrix r)
{-# INLINE at2 #-}
at2 ADInputs{..} i = dD (inputPrimal2 V.! i) (inputDual2 V.! i)

atX :: ADModeAndNum d r => ADInputs d r -> Int -> ADVal d (OT.Array r)
{-# INLINE atX #-}
atX ADInputs{..} i = dD (inputPrimalX V.! i) (inputDualX V.! i)

atS :: (ADModeAndNum d r, OS.Shape sh)
    => ADInputs d r -> Int -> ADVal d (OS.Array sh r)
{-# INLINE atS #-}
atS ADInputs{..} i =
#if defined(VERSION_ghc_typelits_natnormalise)
  inline fromXS $ dD (inputPrimalX V.! i) (inputDualX V.! i)
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
        let !b = dD valX (inputDual0 V.! i)
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
        let !b = dD valX (inputDual0 V.! i)
        in f acc b
  V.ifoldl' g a inputPrimal0
