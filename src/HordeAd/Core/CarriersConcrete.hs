{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor operations implementation using the ox-arrays package.
module HordeAd.Core.CarriersConcrete
  ( RepN(..)
  ) where

import Prelude hiding (foldl')

import Data.Vector.Generic qualified as V

import Data.Array.Mixed.Internal.Arith qualified as Mixed.Internal.Arith
  (liftVEltwise2)
import Data.Array.Nested (KnownShS (..))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal.Mixed
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- TODO: check what the following did in tsum0R and if worth emulating
-- (also in sum1Inner and extremum and maybe tdot0R):
-- LA.sumElements $ OI.toUnorderedVectorT sh t

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
