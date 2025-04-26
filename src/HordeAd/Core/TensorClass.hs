{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library and it's relatively orthogonal to the
-- differentiation interface in "HordeAd.Core.Engine".
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
  (!$) :: forall r sh1 sh2.
                  ( TensorKind r, KnownShS sh1, KnownShS sh2
                  , KnownShS (sh1 ++ sh2) )
               => target (TKS2 (sh1 ++ sh2) r) -> IxSOf target sh1
               -> target (TKS2 sh2 r)
  infixl 9 !$
  sbuild1 :: forall r n sh. (TensorKind r, KnownNat n, KnownShS sh)
          => (IntOf target -> target (TKS2 sh r))
          -> target (TKS2 (n ': sh) r)
  szipWith41 :: forall r1 r2 r3 r4 r n sh1 sh2 sh3 sh4 sh.
                ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r4
                , TensorKind r, KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
                , KnownShS sh )
             => (target (TKS2 sh1 r1)  -> target (TKS2 sh r))
             -> target (TKS2 (n ': sh1) r1)
             -> target (TKS2 (n ': sh) r)
  szipWith41 f u = sbuild1 (\i -> f (u !$ (i :.$ ZIS)))
  tproject1 :: (TensorKind x, TensorKind z)
            => target (TKProduct x z)
            -> target x
  tftk :: STensorKindType y -> target y -> FullTensorKind y
  sfold
    :: forall rn rm sh shm k.
       (KnownShS sh)
    => target (TKS2 sh rn)
  sfold  = dmapAccumL


-- this is the only error
         (FTKS @sh knownShS (FTKScalar @rn))
-- this fixes it:
--         (FTKS @sh knownShS undefined)


      
  dmapAccumL
    :: forall k accShs bShs eShs.
       FullTensorKind accShs
    -> target accShs
    