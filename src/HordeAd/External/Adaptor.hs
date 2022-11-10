{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, RankNTypes, TypeFamilies,
             TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module HordeAd.External.Adaptor
  ( Adaptable
  , value, rev, fwd
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric)

import HordeAd.Core.DualClass (Dual)
  -- for a special test
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors
import HordeAd.Internal.Delta (toShapedOrDummy)

value :: ( Numeric r
         , Adaptable 'ADModeValue r advals vals )
      => (advals -> ADVal 'ADModeValue a) -> vals -> a
value f vals =
  let g inputs = f $ fromADInputs inputs
  in valueFun g (toDomains vals)

rev :: ( HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r
       , Adaptable 'ADModeGradient r advals vals )
    => (advals -> ADVal 'ADModeGradient a) -> vals -> vals
rev f vals =
  let g inputs = f $ fromADInputs inputs
  in fromDomains $ fst $ revFun 1 g (toDomains vals)

fwd :: ( Numeric r, Dual 'ADModeDerivative r ~ r
       , Adaptable 'ADModeDerivative r advals vals )
    => (advals -> ADVal 'ADModeDerivative a) -> vals -> vals
    -> Dual 'ADModeDerivative a  -- normally equals @a@
fwd f x ds =
  let g inputs = f $ fromADInputs inputs
  in fst $ fwdFun (toDomains x) g (toDomains ds)

-- Inspired by adaptors from @tomjaguarpaw's branch.
type Adaptable d r advals vals =
  (AdaptableDomains r vals, AdaptableInputs d r advals)

-- TODO: here, @| vals -> r@ fails when uncommenting the instance below.
-- Probably associated type families are unavoidable
-- and then probably we'd have a single class again, not two joined
-- in the single constraint @Adaptable@.
class AdaptableDomains r vals | vals -> r where
  toDomains :: vals -> Domains r
  fromDomains :: Domains r -> vals

class AdaptableInputs d r advals | advals -> r where
  fromADInputs :: ADInputs d r -> advals

instance Numeric r => AdaptableDomains r (r, r, r) where
  toDomains (a, b, c) =
    (V.fromList [a, b, c], V.empty, V.empty, V.empty)
  fromDomains (v, _, _, _) = case V.toList v of
    r1 : r2 : r3 : _ -> (r1, r2, r3)
    _ -> error "fromDomains in Adaptable r (r, r, r)"

instance ADModeAndNum d r
         => AdaptableInputs d r ( ADVal d r
                                , ADVal d r
                                , ADVal d r ) where
  fromADInputs inputs = case map (at0 inputs) [0 ..] of
    r1 : r2 : r3 : _ -> (r1, r2, r3)
    _ -> error "fromADInputs in Adaptable r (r, r, r)"

-- TODO
instance Numeric r => AdaptableDomains r [r] where
  toDomains [a, b, c] =
    (V.fromList [a, b, c], V.empty, V.empty, V.empty)
  toDomains _ = error "toDomains in Adaptable r [r]"
  fromDomains (v, _, _, _) = case V.toList v of
    r1 : r2 : r3 : _ -> [r1, r2, r3]
    _ -> error "fromDomains in Adaptable r [r]"

instance ADModeAndNum d r
         => AdaptableInputs d r [ADVal d r] where
  fromADInputs inputs = case map (at0 inputs) [0 ..] of
    r1 : r2 : r3 : _ -> [r1, r2, r3]
    _ -> error "fromADInputs in Adaptable r [r]"

{-
-- The error is
--
-- src/HordeAd/External/Adaptor.hs:63:10: error:
--     Functional dependencies conflict between instance declarations:
--       instance Numeric r => AdaptableDomains r (r, r, r)
--         -- Defined at src/HordeAd/External/Adaptor.hs:63:10
--       instance (Numeric r, OS.Shape sh1, OS.Shape sh2, OS.Shape sh3) =>
--                AdaptableDomains r (OS.Array sh1 r, OS.Array sh2 r, OS.Array sh3 r)
--         -- Defined at src/HordeAd/External/Adaptor.hs:93:10
--
-- and probably means that fundep is wrong, because from a @OS.Array sh Double@
-- triple I can deduce either that r is Double by this instance or that
-- r is @OS.Array sh Double@ by an instance above.
-- Later on the ambiguity could be resolved, but fundeps don't have a way
-- to delay resolving such ambiguities.
-- I hope associated type families, perhaps with the AllowAmbiguousTypes
-- extension, permit encoding and storing such ambiguities until they
-- can be resolved. I may be totally wrong in any of this.
instance ( Numeric r
         , OS.Shape sh1, OS.Shape sh2, OS.Shape sh3 )
         => AdaptableDomains r ( OS.Array sh1 r
                               , OS.Array sh2 r
                               , OS.Array sh3 r ) where
  toDomains (a, b, c) =
    ( V.empty, V.empty, V.empty
    , V.fromList [ Data.Array.Convert.convert a
                 , Data.Array.Convert.convert b
                 , Data.Array.Convert.convert c ] )
  fromDomains (_, _, _, v) = case V.toList v of
    a : b : c : _ -> ( toShapedOrDummy a
                     , toShapedOrDummy b
                     , toShapedOrDummy c )
    _ -> error "fromDomains in Adaptable r (S, S, S)"

instance ( ADModeAndNum d r
         , OS.Shape sh1, OS.Shape sh2, OS.Shape sh3 )
         => AdaptableInputs d r ( ADVal d (OS.Array sh1 r)
                                , ADVal d (OS.Array sh2 r)
                                , ADVal d (OS.Array sh3 r) ) where
  fromADInputs inputs =
    let a = atS inputs 0
        b = atS inputs 1
        c = atS inputs 2
    in (a, b, c)
-}

instance ( Numeric r
         , OS.Shape sh1, OS.Shape sh2, OS.Shape sh3, OS.Shape sh4 )
         => AdaptableDomains r ( OS.Array sh1 r
                               , OS.Array sh2 r
                               , OS.Array sh3 r
                               , OS.Array sh4 r ) where
  toDomains (a, b, c, d) =
    ( V.empty, V.empty, V.empty
    , V.fromList [ Data.Array.Convert.convert a
                 , Data.Array.Convert.convert b
                 , Data.Array.Convert.convert c
                 , Data.Array.Convert.convert d ] )
  fromDomains (_, _, _, v) = case V.toList v of
    a : b : c : d : _ -> ( toShapedOrDummy a
                         , toShapedOrDummy b
                         , toShapedOrDummy c
                         , toShapedOrDummy d )
    _ -> error "fromDomains in Adaptable r (S, S, S, S)"

instance ( ADModeAndNum d r
         , OS.Shape sh1, OS.Shape sh2, OS.Shape sh3, OS.Shape sh4 )
         => AdaptableInputs d r ( ADVal d (OS.Array sh1 r)
                                , ADVal d (OS.Array sh2 r)
                                , ADVal d (OS.Array sh3 r)
                                , ADVal d (OS.Array sh4 r) ) where
  fromADInputs inputs =
    let a = atS inputs 0
        b = atS inputs 1
        c = atS inputs 2
        d = atS inputs 3
    in (a, b, c, d)

instance (Numeric r, OS.Shape sh, KnownNat n1, KnownNat n2)
         => AdaptableDomains r ( r
                               , OS.Array '[n1, n2] r
                               , [OS.Array (n2 ': sh) r] ) where
  toDomains (a, b, c) =
    ( V.singleton a, V.empty, V.empty
    , V.fromList $ Data.Array.Convert.convert b
                   : map Data.Array.Convert.convert c )
  fromDomains (vr, _, _, vs) = case V.toList vs of
    b : c -> ( vr V.! 0
             , toShapedOrDummy b
             , map toShapedOrDummy c )
    _ -> error "fromDomains in Adaptable r ..."

instance (ADModeAndNum d r, OS.Shape sh, KnownNat n1, KnownNat n2)
         => AdaptableInputs d r ( ADVal d r
                                , ADVal d (OS.Array '[n1, n2] r)
                                , [ADVal d (OS.Array (n2 ': sh) r)] ) where
  fromADInputs inputs@ADInputs{..} =
    let a = at0 inputs 0
        (b, c) =
          case zipWith dD (V.toList inputPrimalX) (V.toList inputDualX) of
            xb : xc -> (fromXS xb, map fromXS xc)
            _ -> error "fromADInputs in Adaptable r ..."
    in (a, b, c)
