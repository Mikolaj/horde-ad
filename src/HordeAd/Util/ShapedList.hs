{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | @[Nat]@-indexed lists to be used as is for lists of tensor variables,
-- tensor shapes and tensor indexes.
module HordeAd.Util.ShapedList
  ( toLinearIdx, fromLinearIdx
  ) where

import Prelude

import Data.Functor.Const
import Data.Type.Equality (gcastWith, (:~:))
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation (DropLen, TakeLen)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (IShX, StaticShX (..), listxRank)
import Data.Array.Mixed.Types (fromSNat', unsafeCoerceRefl)
import Data.Array.Nested
  ( IxR
  , IxS (..)
  , KnownShS (..)
  , KnownShX (..)
  , ListS (..)
  , Rank
  , ShS (..)
  , type (++)
  )
import Data.Array.Nested.Internal.Shape
  (listsDropLenPerm, listsRank, shsLength, shsRank)

import HordeAd.Core.Types
import HordeAd.Util.SizedList qualified as SizedList

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdx :: forall sh1 sh2 j. (KnownShS sh2, Num j)
            => (Int -> j) -> ShS (sh1 ++ sh2) -> IxS sh1 j -> j
toLinearIdx fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. ShS (sh3 ++ sh2) -> IxS sh3 j -> j -> j
    go _sh ZIS tensidx = fromInt (sizeT @(sh3 ++ sh2)) * tensidx
    go ((:$$) n sh) (i :.$ idx) tensidx =
      go sh idx (fromInt (sNatValue n) * tensidx + i)
    go _ _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
fromLinearIdx :: forall sh j. (Num j, IntegralF j)
              => (Int -> j) -> ShS sh -> j -> IxS sh j
fromLinearIdx fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShS sh1 -> j -> (j, IxS sh1 j)
    go ZSS n = (n, ZIS)
    go ((:$$) k@SNat sh) _ | sNatValue k == 0 =
      (fromInt 0, fromInt 0 :.$ zeroOf fromInt sh)
    go ((:$$) n@SNat sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotF` fromInt (sNatValue n)
          i = tensLin `remF` fromInt (sNatValue n)
      in (tensLin', i :.$ idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => (Int -> j) -> ShS sh -> IxS sh j
zeroOf _ ZSS = ZIS
zeroOf fromInt ((:$$) SNat sh) = fromInt 0 :.$ zeroOf fromInt sh
