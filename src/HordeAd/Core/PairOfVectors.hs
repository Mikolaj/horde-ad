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
  ( DualNumberVariables
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

type DualNumberVariables d r =
  ( Domain0 r
  , Data.Vector.Vector (Dual d r)
  , Domain1 r
  , Data.Vector.Vector (Dual d (Vector r))
  , Domain2 r
  , Data.Vector.Vector (Dual d (Matrix r))
  , DomainX r
  , Data.Vector.Vector (Dual d (OT.Array r))
  )

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
  = (params0, vs0, params1, vs1, params2, vs2, paramsX, vsX)

var0 :: IsScalar d r => DualNumberVariables d r -> Int -> DualNumber d r
var0 (vValue, vVar, _, _, _, _, _, _) i = D (vValue V.! i) (vVar V.! i)

-- Unsafe, but handy for toy examples.
vars :: IsScalar d r => DualNumberVariables d r -> [DualNumber d r]
vars vec = map ( var0 vec) [0 ..]

var1 :: DualNumberVariables d r -> Int -> DualNumber d (Vector r)
var1 (_, _, vValue, vVar, _, _, _, _) i = D (vValue V.! i) (vVar V.! i)

var2 :: DualNumberVariables d r -> Int -> DualNumber d (Matrix r)
var2 (_, _, _, _, vValue, vVar, _, _) i = D (vValue V.! i) (vVar V.! i)

varX :: DualNumberVariables d r -> Int -> DualNumber d (OT.Array r)
varX (_, _, _, _, _, _, vValue, vVar) i = D (vValue V.! i) (vVar V.! i)

varS :: (IsScalar d r, OS.Shape sh)
     => DualNumberVariables d r -> Int -> DualNumber d (OS.Array sh r)
varS (_, _, _, _, _, _, vValue, vVar) i =
#if defined(VERSION_ghc_typelits_natnormalise)
  inline fromXS $ D (vValue V.! i) (vVar V.! i)
#else
  undefined
#endif

ifoldlDual' :: forall a d r. IsScalar d r
             => (a -> Int -> DualNumber d r -> a)
             -> a
             -> DualNumberVariables d r
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc i b
  V.ifoldl' g a vecR

foldlDual' :: forall a d r. IsScalar d r
            => (a -> DualNumber d r -> a)
            -> a
            -> DualNumberVariables d r
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a (vecR, vecD, _, _, _, _, _, _) = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = D valX (vecD V.! i)
        in f acc b
  V.ifoldl' g a vecR
