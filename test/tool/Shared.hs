{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | Additional classes that help in comparing values in tests.
module Shared
  ( lowercase, HasShape (shapeL), Linearizable (linearize)
  ) where

import Prelude

import Data.Array.RankedS qualified as OR
import Data.Char qualified
import Data.Foldable qualified
import Data.Int (Int64)
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Storable qualified as VS
import Foreign.C (CInt)
import GHC.TypeLits (KnownNat)
import Type.Reflection (Typeable, typeRep)

import Data.Array.Nested qualified as Nested

import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..), FlipS (..))
import HordeAd.Util.SizedList

lowercase :: String -> String
lowercase = map Data.Char.toLower

----------------------------------------------------------------------------
-- Things that have shape
----------------------------------------------------------------------------

class HasShape a where
  shapeL :: a -> OR.ShapeL

instance (VS.Storable a) => HasShape (VS.Vector a) where
  shapeL = (: []) . VS.length

instance HasShape (FlipR OR.Array a n) where
  shapeL = OR.shapeL . runFlipR

instance Nested.PrimElt a => HasShape (ORArray a n) where
  shapeL = OR.shapeL . Nested.rtoOrthotope . runFlipR

instance KnownShS sh => HasShape (OSArray a sh) where
  shapeL _ = shapeT @sh

instance RankedTensor ranked => HasShape (DynamicTensor ranked) where
  shapeL (DynamicRanked t) = shapeToList $ rshape t
  shapeL (DynamicShaped @_ @sh _) = shapeT @sh
  shapeL (DynamicRankedDummy @_ @sh _ _) = shapeT @sh
  shapeL (DynamicShapedDummy @_ @sh _ _) = shapeT @sh

instance {-# OVERLAPPABLE #-} (Foldable t) => HasShape (t a) where
  shapeL = (: []) . length

----------------------------------------------------------------------------
-- Things that can be linearized, i.e. converted to a list
----------------------------------------------------------------------------

class Linearizable a b | a -> b where
  linearize :: a -> [b]

instance (VS.Storable a) => Linearizable (VS.Vector a) a where
  linearize = VS.toList

instance (VS.Storable a, Nested.PrimElt a)
         => Linearizable (ORArray a n) a where
  linearize = VS.toList . Nested.rtoVector . runFlipR

instance (VS.Storable a, Nested.PrimElt a)
         => Linearizable (OSArray a sh) a where
  linearize = VS.toList . Nested.stoVector . runFlipS

instance (VS.Storable a) => Linearizable (OR.Array n a) a where
  linearize = OR.toList

instance (VS.Storable a) => Linearizable (FlipR OR.Array a n) a where
  linearize = OR.toList . runFlipR

instance ( forall r n. (GoodScalar r, KnownNat n)
           => Linearizable (ranked r n) r
         , forall r sh. (GoodScalar r, KnownShS sh)
           => Linearizable (shaped r sh) r
         , shaped ~ ShapedOf ranked )  -- a hack for quantified constraints
         => Linearizable (DynamicTensor ranked) Double where
  linearize (DynamicRanked @r2 @n2 t) =
    map toDouble $ linearize @(ranked r2 n2) @r2 t
  linearize (DynamicShaped @r2 @sh2 t) =
    map toDouble $ linearize @(ShapedOf ranked r2 sh2) @r2 t
  linearize (DynamicRankedDummy @_ @sh _ _) = replicate (sizeT @sh) 0
  linearize (DynamicShapedDummy @_ @sh _ _) = replicate (sizeT @sh) 0

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
