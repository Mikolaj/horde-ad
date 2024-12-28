{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | @GHC.Nat@-indexed lists, tensors shapes and indexes.
module HordeAd.Util.SizedList
  ( -- * Sized lists and their permutations
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
