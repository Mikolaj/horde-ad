{-# LANGUAGE UndecidableInstances #-}
-- | Additional classes that help in comparing values in tests.
module Shared
  ( lowercase, HasShape (shapeL), Linearizable (linearize)
  ) where

import Prelude

import Data.Char qualified
import Data.Foldable qualified
import Data.Int (Int64)
import Data.Vector.Storable qualified as VS
import Foreign.C (CInt)
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Types

lowercase :: String -> String
lowercase = map Data.Char.toLower

-- | Things that have shape.
class HasShape a where
  shapeL :: a -> [Int]

instance (KnownNat n, Nested.PrimElt a) => HasShape (Nested.Ranked n a) where
  shapeL = toList . Nested.rshape

instance KnownShS sh => HasShape (Nested.Shaped sh a) where
  shapeL _ = toList $ knownShS @sh

instance HasShape (RepConcrete y) => HasShape (Concrete y) where
  shapeL = shapeL . unConcrete

instance HasShape Double where
  shapeL _ = []

instance HasShape Float where
  shapeL _ = []

instance HasShape Int64 where
  shapeL _ = []

instance HasShape CInt where
  shapeL _ = []

instance HasShape Z1 where
  shapeL _ = [0]

instance {-# OVERLAPPABLE #-} (Foldable t) => HasShape (t a) where
  shapeL = (: []) . length

-- | Things that can be linearized, i.e. converted to a list.
class Linearizable a b | a -> b where
  linearize :: a -> [b]

instance (VS.Storable a, Nested.PrimElt a)
         => Linearizable (Nested.Ranked n a) a where
  linearize = VS.toList . Nested.rtoVector

instance (VS.Storable a, Nested.PrimElt a)
         => Linearizable (Nested.Shaped sh a) a where
  linearize = VS.toList . Nested.stoVector

instance Linearizable (RepConcrete y) a
         => Linearizable (Concrete y) a where
  linearize = linearize . unConcrete

instance Linearizable Double Double where
  linearize x = [x]

instance Linearizable Float Float where
  linearize x = [x]

instance Linearizable Int64 Int64 where
  linearize x = [x]

instance Linearizable CInt CInt where
  linearize x = [x]

instance Linearizable Z1 Z1 where
  linearize _ = []

instance {-# OVERLAPPABLE #-} (Foldable t) => Linearizable (t a) a where
  linearize = Data.Foldable.toList
