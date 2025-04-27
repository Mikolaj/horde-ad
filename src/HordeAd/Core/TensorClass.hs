{-# LANGUAGE AllowAmbiguousTypes #-}
module HordeAd.Core.TensorClass
  ( ) where

import Prelude

import Data.Default
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , cmpNat
  , sameNat
  , type (+)
  , type (-)
  , type (<=)
  )
import Numeric.LinearAlgebra (Numeric)
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Lemmas
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  (IShX, StaticShX (..), ssxAppend, ssxFromShape, ssxReplicate)
import Data.Array.Nested
  ( IShR
  , IxS (..)
  , KnownShS (..)
  , KnownShX (..)
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , pattern (:$:)
  , pattern (:.$)
  , pattern (:.:)
  , pattern ZIR
  , pattern ZIS
  , pattern ZSR
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shCvtSX, shsAppend)

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

class BaseTensor (target :: Target) where
  index :: (TensorKind r, KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2))
        => target (TKS2 (sh1 ++ sh2) r) -> IxSOf target sh1
        -> target (TKS2 sh2 r)
  szipWith41 :: (TensorKind r1, KnownNat n, KnownShS sh1)
             => target (TKS2 (n ': sh1) r1)
             -> target (TKS2 (sh1) r1)
  szipWith41 u = index u (undefined :.$ ZIS)
  sfold :: forall rn sh. KnownShS sh
        => FullTensorKind (TKS2 sh rn)
  sfold = 


-- this is the only error
         (FTKS @sh knownShS (FTKScalar @rn))
-- this fixes it:
--         (FTKS @sh knownShS undefined)

      