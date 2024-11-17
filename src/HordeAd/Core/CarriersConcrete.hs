{-# LANGUAGE UndecidableInstances #-}
-- | Tensor operations implementation using the ox-arrays package.
module HordeAd.Core.CarriersConcrete
  ( IIxR64, IIxS64
  , Nested.Ranked, Nested.Shaped, Nested.Mixed
  , RepScalar(..), RepORArray, RepN(..)
  ) where

import Prelude hiding (foldl')

import Control.DeepSeq (NFData (..))
import Data.Int (Int64)
import Data.Kind (Type)

import Data.Array.Nested (IxR, IxS)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.HVector
import HordeAd.Core.Types

-- TODO: check what the following did in tsum0R and if worth emulating
-- (also in sum1Inner and extremum and maybe tdot0R):
-- LA.sumElements $ OI.toUnorderedVectorT sh t

type role RepScalar nominal
type RepScalar :: Type -> Type
newtype RepScalar r = RepScalar {unRepScalar :: Nested.Ranked 0 r}

deriving instance Show (Nested.Ranked 0 r) => Show (RepScalar r)

deriving instance NFData (Nested.Ranked 0 r) => NFData (RepScalar r)

type family RepORArray (y :: TensorKindType) = result | result -> y where
  RepORArray (TKScalar r) = RepScalar r  -- for injectivity
  RepORArray (TKR r n) = Nested.Ranked n r
  RepORArray (TKS r sh) = Nested.Shaped sh r
  RepORArray (TKX r sh) = Nested.Mixed sh r
  RepORArray (TKProduct x z) = (RepORArray x, RepORArray z)
  RepORArray TKUntyped = HVector RepN

-- Needed because `RepORArray` can't be partially applied.
-- This type also lets us work around the woes with defining Show
-- for the Rep type family. It gives us a concrete thing
-- to attach a Show instance to.
type role RepN nominal
newtype RepN y = RepN {unRepN :: RepORArray y}

instance TensorKind y
         => Show (RepN y) where
  showsPrec d (RepN t) = case stensorKind @y of
    STKScalar _ -> showsPrec d t
    STKR STKScalar{} SNat -> showsPrec d t
    STKS STKScalar{} sh -> withKnownShS sh $ showsPrec d t
    STKX STKScalar{} sh -> withKnownShX sh $ showsPrec d t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      showsPrec d (RepN $ fst t, RepN $ snd t)
    STKUntyped -> showsPrec d t
    _ -> error "TODO"

instance TensorKind y
         => NFData (RepN y) where
  rnf (RepN t) = case stensorKind @y of
    STKScalar _ -> rnf t
    STKR STKScalar{} SNat -> rnf t
    STKS STKScalar{} sh -> withKnownShS sh $ rnf t
    STKX STKScalar{} sh -> withKnownShX sh $ rnf t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      rnf (RepN $ fst t, RepN $ snd t)
    STKUntyped -> rnf t
    _ -> error "TODO"

type IIxR64 n = IxR n Int64

type IIxS64 sh = IxS sh Int64

type instance BoolOf RepN = Bool

type instance HFunOf RepN x z = RepORArray x -> RepORArray z

type instance PrimalOf RepN = RepN

type instance DualOf RepN = DummyDualTarget

type instance ShareOf RepN = RepN
