{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | Additional classes that help in comparing values in tests.
module Shared
  ( lowercase, HasShape (shapeL), Linearizable (linearize)
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.Char
import qualified Data.Foldable
import qualified Data.Vector.Storable as VS
import           GHC.TypeLits (KnownNat)
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (FlipS (..))
import HordeAd.Internal.TensorFFI
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

instance HasShape (Flip OR.Array a n) where
  shapeL = OR.shapeL . runFlip

instance KnownShape sh => HasShape (FlipS OS.Array a sh) where
  shapeL = OS.shapeL . runFlipS

instance HasShape (LA.Matrix a) where
  shapeL matrix = [LA.rows matrix, LA.cols matrix]

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

instance (VS.Storable a, KnownShape sh)
         => Linearizable (OS.Array sh a) a where
  linearize = OS.toList

instance (VS.Storable a, KnownShape sh)
         => Linearizable (FlipS OS.Array a sh) a where
  linearize = OS.toList . runFlipS

instance (VS.Storable a) => Linearizable (OR.Array n a) a where
  linearize = OR.toList

instance (VS.Storable a) => Linearizable (Flip OR.Array a n) a where
  linearize = OR.toList . runFlip

instance (LA.Element a) => Linearizable (LA.Matrix a) a where
  linearize = LA.toList . LA.flatten

instance ( forall r n. (GoodScalar r, KnownNat n)
           => Linearizable (ranked r n) r
         , forall r sh. (GoodScalar r, KnownShape sh)
           => Linearizable (shaped r sh) r
         , shaped ~ ShapedOf ranked )  -- a hack for quantified constraints
         => Linearizable (DynamicTensor ranked) Double where
  linearize (DynamicRanked @r2 @n2 t) =
    map toDouble $ linearize @(ranked r2 n2) @r2 t
  linearize (DynamicShaped @r2 @sh2 t) =
    map toDouble $ linearize @(ShapedOf ranked r2 sh2) @r2 t
  linearize (DynamicRankedDummy @_ @sh _ _) = replicate (sizeT @sh) 0
  linearize (DynamicShapedDummy @_ @sh _ _) = replicate (sizeT @sh) 0

instance {-# OVERLAPPABLE #-} (Foldable t) => Linearizable (t a) a where
  linearize = Data.Foldable.toList
