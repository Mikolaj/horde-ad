module Shared
  ( lowercase, HasShape (shapeL), Linearizable (linearize)
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.Char
import qualified Data.Foldable
import qualified Data.Vector.Storable as VS
import qualified Numeric.LinearAlgebra as LA

lowercase :: String -> String
lowercase = map Data.Char.toLower

----------------------------------------------------------------------------
-- Things that have shape
----------------------------------------------------------------------------

-- | Shape of the thing, typically a list of the sizes of its dimensions.
type ShapeL = [Int]

class HasShape a where
  shapeL :: a -> ShapeL

instance (VS.Storable a) => HasShape (VS.Vector a) where
  shapeL = (: []) . VS.length

instance HasShape (OD.Array a) where
  shapeL = OD.shapeL

instance HasShape (Flip OR.Array a n) where
  shapeL = OR.shapeL . runFlip

instance OS.Shape sh => HasShape (Flip OS.Array a sh) where
  shapeL = OS.shapeL . runFlip

instance HasShape (LA.Matrix a) where
  shapeL matrix = [LA.rows matrix, LA.cols matrix]

instance {-# OVERLAPPABLE #-} (Foldable t) => HasShape (t a) where
  shapeL = (: []) . length

----------------------------------------------------------------------------
-- Things that can be linearized, i.e. converted to a list
----------------------------------------------------------------------------

class Linearizable a b | a -> b where
  linearize :: a -> [b]

instance (VS.Storable a) => Linearizable (VS.Vector a) a where
  linearize = VS.toList

instance (VS.Storable a) => Linearizable (OD.Array a) a where
  linearize = OD.toList

instance (VS.Storable a, OS.Shape sh)
         => Linearizable (OS.Array sh a) a where
  linearize = OS.toList

instance (VS.Storable a, OS.Shape sh)
         => Linearizable (Flip OS.Array a sh) a where
  linearize = OS.toList . runFlip

instance (VS.Storable a) => Linearizable (OR.Array n a) a where
  linearize = OR.toList

instance (VS.Storable a) => Linearizable (Flip OR.Array a n) a where
  linearize = OR.toList . runFlip

instance (LA.Element a) => Linearizable (LA.Matrix a) a where
  linearize = LA.toList . LA.flatten

instance {-# OVERLAPPABLE #-} (Foldable t) => Linearizable (t a) a where
  linearize = Data.Foldable.toList
