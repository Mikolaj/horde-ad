{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | Additional classes that help in comparing values in tests.
module Shared
  ( lowercase, HasShape (shapeL), Linearizable (linearize)
  ) where

import Prelude

import Data.Char qualified
import Data.Foldable qualified
import Data.Vector.Storable qualified as VS
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)

import Data.Array.Nested (KnownShS (..))
import Data.Array.Nested qualified as Nested

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Types

lowercase :: String -> String
lowercase = map Data.Char.toLower

----------------------------------------------------------------------------
-- Things that have shape
----------------------------------------------------------------------------

class HasShape a where
  shapeL :: a -> [Int]

instance (KnownNat n, Nested.PrimElt a) => HasShape (Nested.Ranked n a) where
  shapeL = toList . Nested.rshape

instance KnownShS sh => HasShape (Nested.Shaped sh a) where
  shapeL _ = toList $ knownShS @sh

instance HasShape (RepORArray y) => HasShape (RepN y) where
  shapeL = shapeL . unRepN

instance HasShape Z0 where
  shapeL _ = [0]

instance {-# OVERLAPPABLE #-} (Foldable t) => HasShape (t a) where
  shapeL = (: []) . length

----------------------------------------------------------------------------
-- Things that can be linearized, i.e. converted to a list
----------------------------------------------------------------------------

class Linearizable a b | a -> b where
  linearize :: a -> [b]

instance (VS.Storable a, Nested.PrimElt a)
         => Linearizable (Nested.Ranked n a) a where
  linearize = VS.toList . Nested.rtoVector

instance (VS.Storable a, Nested.PrimElt a)
         => Linearizable (Nested.Shaped sh a) a where
  linearize = VS.toList . Nested.stoVector

instance Linearizable (RepORArray y) a
         => Linearizable (RepN y) a where
  linearize = linearize . unRepN

instance Linearizable Z0 Z0 where
  linearize _ = []

instance {-# OVERLAPPABLE #-} (Foldable t) => Linearizable (t a) a where
  linearize = Data.Foldable.toList
