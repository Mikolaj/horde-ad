module Tool.Shared
  ( lowercase, HasShape (shapeL), Linearizable (linearize)
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
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

instance HasShape (OT.Array a) where
  shapeL = OT.shapeL

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

instance (VS.Storable a) => Linearizable (OT.Array a) a where
  linearize = OT.toList

instance (VS.Storable a, OS.Shape sh) => Linearizable (OS.Array sh a) a where
  linearize = OS.toList

instance (VS.Storable a) => Linearizable (OR.Array n a) a where
  linearize = OR.toList

instance (LA.Element a) => Linearizable (LA.Matrix a) a where
  linearize = LA.toList . LA.flatten

instance {-# OVERLAPPABLE #-} (Foldable t) => Linearizable (t a) a where
  linearize = Data.Foldable.toList
