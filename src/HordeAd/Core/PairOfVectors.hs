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
  ( DualNumberInputs(..)
  , makeDualNumberInputs, at0, atList0, at1, at2, atX, atS
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

-- These are optimized as "pair of vectors" representing vectors of @DualNumber@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).

data DualNumberInputs d r = DualNumberInputs
  { inputPrimal0 :: Domain0 r
  , inputDual0   :: Data.Vector.Vector (Dual d r)
  , inputPrimal1 :: Domain1 r
  , inputDual1   :: Data.Vector.Vector (Dual d (Vector r))
  , inputPrimal2 :: Domain2 r
  , inputDual2   :: Data.Vector.Vector (Dual d (Matrix r))
  , inputPrimalX :: DomainX r
  , inputDualX   :: Data.Vector.Vector (Dual d (OT.Array r))
  }

makeDualNumberInputs
  :: Domains r
  -> ( Data.Vector.Vector (Dual d r)
     , Data.Vector.Vector (Dual d (Vector r))
     , Data.Vector.Vector (Dual d (Matrix r))
     , Data.Vector.Vector (Dual d (OT.Array r)) )
  -> DualNumberInputs d r
{-# INLINE makeDualNumberInputs #-}
makeDualNumberInputs (params0, params1, params2, paramsX)
                        (vs0, vs1, vs2, vsX)
  = DualNumberInputs params0 vs0 params1 vs1 params2 vs2 paramsX vsX

at0 :: IsScalar d r => DualNumberInputs d r -> Int -> DualNumber d r
{-# INLINE at0 #-}
at0 DualNumberInputs{..} i = D (inputPrimal0 V.! i) (inputDual0 V.! i)

-- Unsafe, but handy for toy examples.
atList0 :: IsScalar d r => DualNumberInputs d r -> [DualNumber d r]
atList0 vec = map (at0 vec) [0 ..]

at1 :: DualNumberInputs d r -> Int -> DualNumber d (Vector r)
{-# INLINE at1 #-}
at1 DualNumberInputs{..} i = D (inputPrimal1 V.! i) (inputDual1 V.! i)

at2 :: DualNumberInputs d r -> Int -> DualNumber d (Matrix r)
{-# INLINE at2 #-}
at2 DualNumberInputs{..} i = D (inputPrimal2 V.! i) (inputDual2 V.! i)

atX :: DualNumberInputs d r -> Int -> DualNumber d (OT.Array r)
{-# INLINE atX #-}
atX DualNumberInputs{..} i = D (inputPrimalX V.! i) (inputDualX V.! i)

atS :: (IsScalar d r, OS.Shape sh)
     => DualNumberInputs d r -> Int -> DualNumber d (OS.Array sh r)
{-# INLINE atS #-}
atS DualNumberInputs{..} i =
#if defined(VERSION_ghc_typelits_natnormalise)
  inline fromXS $ D (inputPrimalX V.! i) (inputDualX V.! i)
#else
  undefined
#endif

ifoldlDual' :: forall a d r. IsScalar d r
             => (a -> Int -> DualNumber d r -> a)
             -> a
             -> DualNumberInputs d r
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a DualNumberInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (inputDual0 V.! i)
        in f acc i b
  V.ifoldl' g a inputPrimal0

foldlDual' :: forall a d r. IsScalar d r
            => (a -> DualNumber d r -> a)
            -> a
            -> DualNumberInputs d r
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a DualNumberInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (inputDual0 V.! i)
        in f acc b
  V.ifoldl' g a inputPrimal0
