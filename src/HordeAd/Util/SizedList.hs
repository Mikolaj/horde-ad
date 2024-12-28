{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | @GHC.Nat@-indexed lists, tensors shapes and indexes.
module HordeAd.Util.SizedList
  ( -- * Sized lists and their permutations
    withListShape, withListSh
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
