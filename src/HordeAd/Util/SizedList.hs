{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | @GHC.Nat@-indexed lists, tensors shapes and indexes.
module HordeAd.Util.SizedList
  ( -- * Sized lists and their permutations
    permInverse
  , backpermutePrefixList
  , withListShape, withListSh
  ) where

import Prelude

import Control.Arrow (first)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.List (sort)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))

import Data.Array.Nested
  ( IShR
  , IxR (..)
  , KnownShS (..)
  , ListR (..)
  , Rank
  , ShR (..)
  , pattern (:.:)
  , pattern (:::)
  , pattern ZIR
  , pattern ZR
  )

import Data.Array.Nested.Internal.Shape (shrSize)

import HordeAd.Core.Types

-- * Sized lists and their permutations

-- | Standard strict sized lists indexed by the GHC @Nat@ type.
--
-- Note that in GHC 9.4, @[a]@ and our strict @ListR@ no longer have
-- the same representation in some corner cases, so we can't
-- @unsafeCoerce@ between the two.
-- Wise men say it's because \"coercing @data T = MkT a@ to @data T2 a= MkT2 !a@
-- is no longer working in 9.4\" and we have @StrictData@ set in .cabal file.
-- We could unset @StrictData@ for this file and recover the shared
-- representation, but for as long as we don't have performance problems,
-- let's avoid @unsafeCoerce@ anyway. The list being strict should be
-- more performant, too, given that it's always short (the size of
-- tensor rank) and usually eventually needed. We could still (in GHC 9.4
-- at least) coerce the strict @ListR@ to @[i]@, but not the other
-- way around.

-- | As in orthotope, we usually backpermute, in which case a permutation lists
-- indices into the list to permute. However, we use the same type for
-- an occasional forward permutation.
type PermR = [Int]

permInverse :: PermR -> PermR
permInverse perm = map snd $ sort $ zip perm [0 .. length perm - 1]

backpermutePrefixList :: PermR -> [i] -> [i]
backpermutePrefixList p l = map (l !!) p ++ drop (length p) l


-- * Tensor indexes as fully encapsulated sized lists, with operations

-- TODO: make sure this is covered in ox-arrays:
-- | An index in an n-dimensional array represented as a sized list.
-- The slowest-moving index is at the head position;
-- thus the index 'i :.: j :.: Z' represents 'a[i][j]' in traditional C notation.
--
-- Since we don't have type-level shape information in this variant,
-- we don't assume the indexes are legal, meaning non-negative and bound
-- by some shape. Consequently, there are no runtime checks for that
-- until we we actually attempt projecting. In case that the values
-- are terms, there is no absolute corrcetness criterion anyway,
-- because the eventual integer value depends on a variable valuation.

-- * Tensor shapes as fully encapsulated sized lists, with operations

-- Both shape representations denote the same shape.
withListShape
  :: forall i a.
     [i]
  -> (forall n. KnownNat n => ShR n i -> a)
  -> a
withListShape shList f =
  case someNatVal $ toInteger (length shList) of
    Just (SomeNat @n _) -> f $ (fromList shList :: ShR n i)
    _ -> error "withListShape: impossible someNatVal error"

-- All three shape representations denote the same shape.
withListSh
  :: KnownShS sh
  => Proxy sh
  -> (forall n. (KnownNat n, Rank sh ~ n)
      => IShR n -> a)
  -> a
withListSh (Proxy @sh) f =
  let shList = toList $ knownShS @sh
  in case someNatVal $ toInteger (length shList) of
    Just (SomeNat @n _) ->
      gcastWith (unsafeCoerceRefl :: Rank sh :~: n) $
      f $ fromList shList
    _ -> error "withListSh: impossible someNatVal error"
