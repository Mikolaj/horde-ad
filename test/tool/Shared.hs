{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | Additional classes that help in comparing values in tests.
module Shared
  ( lowercase, HasShape (shapeL), Linearizable (linearize)
  ) where

import Prelude

import Data.Char qualified
import Data.Foldable qualified
import Data.Int (Int64)
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Storable qualified as VS
import Foreign.C (CInt)
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)
import Type.Reflection (Typeable, typeRep)

import Data.Array.Nested (KnownShS (..))
import Data.Array.Nested qualified as Nested

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
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

instance BaseTensor target => HasShape (DynamicTensor target) where
  shapeL (DynamicRanked t) = toList $ rshape t
  shapeL (DynamicShaped @_ @sh _) = toList $ knownShS @sh
  shapeL (DynamicRankedDummy @_ @sh _ _) = toList $ knownShS @sh
  shapeL (DynamicShapedDummy @_ @sh _ _) = toList $ knownShS @sh

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

instance ( forall r n. (GoodScalar r, KnownNat n)
           => Linearizable (target (TKR n r)) r
         , forall r sh. (GoodScalar r, KnownShS sh)
           => Linearizable (target (TKS sh r)) r )
         => Linearizable (DynamicTensor target) Double where
  linearize (DynamicRanked @r2 @n2 t) =
    map toDouble $ linearize @(target (TKR n2 r2)) @r2 t
  linearize (DynamicShaped @r2 @sh2 t) =
    map toDouble $ linearize @(target (TKS sh2 r2)) @r2 t
  linearize (DynamicRankedDummy @_ @sh _ _) = replicate (sizeT @sh) 0
  linearize (DynamicShapedDummy @_ @sh _ _) = replicate (sizeT @sh) 0

instance Linearizable Z0 Z0 where
  linearize _ = []

toDouble :: forall r. Typeable r => r -> Double
toDouble =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> id
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> realToFrac
      _ -> case testEquality (typeRep @r) (typeRep @Int64) of
        Just Refl -> fromIntegral
        _ -> case testEquality (typeRep @r) (typeRep @CInt) of
          Just Refl -> fromIntegral
          _ -> error "an unexpected underlying scalar type"  -- catch absurd

instance {-# OVERLAPPABLE #-} (Foldable t) => Linearizable (t a) a where
  linearize = Data.Foldable.toList
