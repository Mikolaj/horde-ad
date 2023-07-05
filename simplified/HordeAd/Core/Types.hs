-- | Some fundamental kinds, type families and types.
module HordeAd.Core.Types
  ( TensorKind, RankedTensorKind, ShapedTensorKind
  ) where

import Prelude

import Data.Kind (Type)
import GHC.TypeLits (Nat)

type TensorKind k = Type -> k -> Type

type RankedTensorKind = TensorKind Nat

type ShapedTensorKind = TensorKind [Nat]
