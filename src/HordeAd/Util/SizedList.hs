{-# LANGUAGE DerivingStrategies, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | @GHC.Nat@-indexed lists, tensors shapes and indexes.
module HordeAd.Util.SizedList
  ( Shape, Index, toLinearIdx
  ) where

import Prelude

import           Control.Arrow (first)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.Exts (IsList (..))
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , SomeNat (..)
  , cmpNat
  , sameNat
  , someNatVal
  , type (+)
  , type (-)
  )
import           Unsafe.Coerce (unsafeCoerce)

-- | Standard strict sized lists indexed by the GHC @Nat@ type.
--
-- Note that in GHC 9.4, @[a]@ and our strict @SizedList@ no longer have
-- the same representation in some corner cases, so we can't
-- @unsafeCoerce@ between the two.
-- Wise men say it's because \"coercing @data T = MkT a@ to @data T2 a= MkT2 !a@
-- is no longer working in 9.4\" and we have @StrictData@ set in .cabal file.
-- We could unset @StrictData@ for this file and recover the shared
-- representation, but for as long as we don't have performance problems,
-- let's avoid @unsafeCoerce@ anyway. The list being strict should be
-- more performant, too, given that it's always short (the size of
-- tensor rank) and usually eventually needed. We could still (in GHC 9.4
-- at least) coerce the strict @SizedList@ to @[i]@, but not the other
-- way around.
infixr 3 :::
type role SizedList nominal representational
data SizedList (n :: Nat) i where
  ZR :: SizedList 0 i
  (:::) :: forall n {i}. KnownNat n
        => i -> SizedList n i -> SizedList (1 + n) i


-- * Tensor indexes as fully encapsulated sized lists, with operations

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
type role Index nominal representational
newtype Index n i = Index (SizedList n i)

pattern ZIR :: forall n i. () => n ~ 0 => Index n i
pattern ZIR = Index ZR

infixr 3 :.:
pattern (:.:)
  :: forall {n1} {i}.
     forall n. (KnownNat n, (1 + n) ~ n1)
  => i -> Index n i -> Index n1 i
pattern i :.: sh <- (unconsIndex -> Just (UnconsIndexRes sh i))
  where i :.: (Index sh) = Index (i ::: sh)
{-# COMPLETE ZIR, (:.:) #-}

type role UnconsIndexRes representational nominal
data UnconsIndexRes i n1 =
  forall n. (KnownNat n, (1 + n) ~ n1) => UnconsIndexRes (Index n i) i
unconsIndex :: Index n1 i -> Maybe (UnconsIndexRes i n1)
unconsIndex (Index sh) = case sh of
  i ::: sh' -> Just (UnconsIndexRes (Index sh') i)
  ZR -> Nothing

-- * Tensor shapes as fully encapsulated sized lists, with operations

-- | The shape of an n-dimensional array represented as a sized list.
-- The order of dimensions corresponds to that in @Index@.
type role Shape nominal representational
newtype Shape n i = Shape (SizedList n i)

pattern ZSR :: forall n i. () => n ~ 0 => Shape n i
pattern ZSR = Shape ZR

infixr 3 :$:
pattern (:$:)
  :: forall {n1} {i}.
     forall n. (KnownNat n, (1 + n) ~ n1)
  => i -> Shape n i -> Shape n1 i
pattern i :$: sh <- (unconsShape -> Just (MkUnconsShapeRes sh i))
  where i :$: (Shape sh) = Shape (i ::: sh)
{-# COMPLETE ZSR, (:$:) #-}

type role UnconsShapeRes representational nominal
data UnconsShapeRes i n1 =
  forall n. (KnownNat n, (1 + n) ~ n1) => MkUnconsShapeRes (Shape n i) i
unconsShape :: Shape n1 i -> Maybe (UnconsShapeRes i n1)
unconsShape (Shape sh) = case sh of
  i ::: sh' -> Just (MkUnconsShapeRes (Shape sh') i)
  ZR -> Nothing

-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdx :: forall m n i j. (Integral i, Num j)
            => Shape (m + n) i -> Index m j -> j
toLinearIdx = \sh idx -> go sh idx 0
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: Shape (m1 + n) i -> Index m1 j -> j -> j
    go sh ZIR tensidx = fromIntegral 0 * tensidx
    go (n :$: sh) (i :.: idx) tensidx = go sh idx (fromIntegral n * tensidx + i)
    go _ _ _ = error "toLinearIdx: impossible pattern needlessly required"
