{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | @[Nat]@-indexed lists to be used as is for lists of tensor variables,
-- tensor shapes and tensor indexes.
module HordeAd.Util.ShapedList
  ( ) where

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
