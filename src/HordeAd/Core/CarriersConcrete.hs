{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
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
import Data.Vector.Generic qualified as V

import Data.Array.Mixed.Internal.Arith qualified as Mixed.Internal.Arith
  (liftVEltwise2)
import Data.Array.Nested (IxR, IxS, KnownShS (..))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal.Mixed
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

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
  RepORArray (TKR n r) = Nested.Ranked n r
  RepORArray (TKS sh r) = Nested.Shaped sh r
  RepORArray (TKX sh r) = Nested.Mixed sh r
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
    STKR SNat STKScalar{} -> showsPrec d t
    STKS sh STKScalar{} -> withKnownShS sh $ showsPrec d t
    STKX sh STKScalar{} -> withKnownShX sh $ showsPrec d t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      showsPrec d (RepN $ fst t, RepN $ snd t)
    STKUntyped -> showsPrec d t
    _ -> error "TODO"

instance TensorKind y
         => NFData (RepN y) where
  rnf (RepN t) = case stensorKind @y of
    STKScalar _ -> rnf t
    STKR SNat STKScalar{} -> rnf t
    STKS sh STKScalar{} -> withKnownShS sh $ rnf t
    STKX sh STKScalar{} -> withKnownShX sh $ rnf t
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


instance (Nested.PrimElt r, Integral r)
         => IntegralF (Nested.Ranked n r) where
  -- These can't be partial, because our conditionals are not lazy
  -- and so the counterfactual branches, with zeros, may get executed
  -- even though they are subsequently ignored.
  quotF = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quot a b) x y)))
                            -- TODO: do better somehow
  remF = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else rem a b) x y)))
                            -- TODO: do better somehow

instance (Nested.PrimElt r, Integral r)
         => IntegralF (Nested.Shaped sh r) where
  quotF = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quot a b) x y)))
                            -- TODO: do better somehow
  remF = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else rem a b) x y)))
                            -- TODO: do better somehow

instance (Nested.PrimElt r, Integral r)
         => IntegralF (Nested.Mixed sh r) where
  quotF =   (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quot a b) x y)))
                            -- TODO: do better somehow
  remF =    (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else rem a b) x y)))
                            -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloatF (Nested.Ranked n r) where
  atan2F = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r, KnownShS sh)
         => RealFloatF (Nested.Shaped sh r) where
  atan2F = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloatF (Nested.Mixed sh r) where
  atan2F =   (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow
