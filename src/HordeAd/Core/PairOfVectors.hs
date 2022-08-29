{-# LANGUAGE CPP, TypeFamilies #-}
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
  ( DualNumberVariables(..)
  , makeDualNumberVariables, var0, vars, var1, var2, varX, varS
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

data DualNumberVariables d r = DualNumberVariables
  { inputPrimal0 :: Domain0 r
  , inputDual0   :: Data.Vector.Vector (Dual d r)
  , inputPrimal1 :: Domain1 r
  , inputDual1   :: Data.Vector.Vector (Dual d (Vector r))
  , inputPrimal2 :: Domain2 r
  , inputDual2   :: Data.Vector.Vector (Dual d (Matrix r))
  , inputPrimalX :: DomainX r
  , inputDualX   :: Data.Vector.Vector (Dual d (OT.Array r))
  }

makeDualNumberVariables
  :: Domains r
  -> ( Data.Vector.Vector (Dual d r)
     , Data.Vector.Vector (Dual d (Vector r))
     , Data.Vector.Vector (Dual d (Matrix r))
     , Data.Vector.Vector (Dual d (OT.Array r)) )
  -> DualNumberVariables d r
{-# INLINE makeDualNumberVariables #-}
makeDualNumberVariables (params0, params1, params2, paramsX)
                        (vs0, vs1, vs2, vsX)
  = DualNumberVariables params0 vs0 params1 vs1 params2 vs2 paramsX vsX

var0 :: IsScalar d r => DualNumberVariables d r -> Int -> DualNumber d r
{-# INLINE var0 #-}
var0 DualNumberVariables{..} i = D (inputPrimal0 V.! i) (inputDual0 V.! i)

-- Unsafe, but handy for toy examples.
vars :: IsScalar d r => DualNumberVariables d r -> [DualNumber d r]
vars vec = map (var0 vec) [0 ..]

var1 :: DualNumberVariables d r -> Int -> DualNumber d (Vector r)
{-# INLINE var1 #-}
var1 DualNumberVariables{..} i = D (inputPrimal1 V.! i) (inputDual1 V.! i)

var2 :: DualNumberVariables d r -> Int -> DualNumber d (Matrix r)
{-# INLINE var2 #-}
var2 DualNumberVariables{..} i = D (inputPrimal2 V.! i) (inputDual2 V.! i)

varX :: DualNumberVariables d r -> Int -> DualNumber d (OT.Array r)
{-# INLINE varX #-}
varX DualNumberVariables{..} i = D (inputPrimalX V.! i) (inputDualX V.! i)

varS :: (IsScalar d r, OS.Shape sh)
     => DualNumberVariables d r -> Int -> DualNumber d (OS.Array sh r)
{-# INLINE varS #-}
varS DualNumberVariables{..} i =
#if defined(VERSION_ghc_typelits_natnormalise)
  inline fromXS $ D (inputPrimalX V.! i) (inputDualX V.! i)
#else
  undefined
#endif

ifoldlDual' :: forall a d r. IsScalar d r
             => (a -> Int -> DualNumber d r -> a)
             -> a
             -> DualNumberVariables d r
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a DualNumberVariables{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (inputDual0 V.! i)
        in f acc i b
  V.ifoldl' g a inputPrimal0

foldlDual' :: forall a d r. IsScalar d r
            => (a -> DualNumber d r -> a)
            -> a
            -> DualNumberVariables d r
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a DualNumberVariables{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (inputDual0 V.! i)
        in f acc b
  V.ifoldl' g a inputPrimal0
