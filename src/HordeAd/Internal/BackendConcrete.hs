-- | Miscellaneous more or less general purpose tensor operations using
-- the orthotope package tensor representation and hmatrix package
-- (and also our own) FFI bindings.
module HordeAd.Internal.BackendConcrete
  ( module HordeAd.Internal.BackendConcrete
  ) where

import Prelude hiding (foldl')

import           Control.Arrow (second)
import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Internal as OI
import qualified Data.Array.Internal.RankedG as RG
import qualified Data.Array.Internal.RankedS as RS
import qualified Data.Array.Internal.ShapedG as SG
import qualified Data.Array.Internal.ShapedS as SS
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Functor (void)
import           Data.Int (Int64)
import           Data.List (foldl')
import           Data.List.Index (imap)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Map as M
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable.Mutable as VM
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , SomeNat (..)
  , fromSNat
  , sameNat
  , someNatVal
  , type (+)
  , type (<=)
  )
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import qualified HordeAd.Util.SizedList as SizedList

toLinearIdx :: forall m n i j. (Integral i, Num j)
            => SizedList.Shape (m + n) i -> SizedList.Index m j -> j
toLinearIdx = SizedList.toLinearIdx
