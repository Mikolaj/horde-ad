{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, RankNTypes, TypeFamilies, TypeOperators,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module HordeAd.External.Adaptor
  ( Adaptable, AdaptableDomains
  , value, rev, fwd
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl', unzip4)
import qualified Data.Vector.Generic as V
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
  let g inputs = f $ fst $ fromADInputs inputs
  in valueFun g (toDomains vals)

rev :: forall a r advals vals.
       ( HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r
       , Adaptable 'ADModeGradient r advals vals )
    => (advals -> ADVal 'ADModeGradient a) -> vals -> vals
rev f vals =
  let g inputs = f $ fst $ fromADInputs inputs
  in fst $ fromDomains vals $ fst $ revFun 1 g (toDomains vals)

fwd :: ( Numeric r, Dual 'ADModeDerivative r ~ r
       , Adaptable 'ADModeDerivative r advals vals )
    => (advals -> ADVal 'ADModeDerivative a) -> vals -> vals
    -> Dual 'ADModeDerivative a  -- normally equals @a@
fwd f x ds =
  let g inputs = f $ fst $ fromADInputs inputs
  in fst $ fwdFun (toDomains x) g (toDomains ds)

-- Inspired by adaptors from @tomjaguarpaw's branch.
type Adaptable d r advals vals =
  (AdaptableDomains r vals, AdaptableInputs d r advals)

class AdaptableDomains r vals | vals -> r where
  toDomains :: vals -> Domains r
  fromDomains :: vals -> Domains r -> (vals, Domains r)

class AdaptableInputs d r advals | advals -> r where
  fromADInputs :: ADInputs d r -> (advals, ADInputs d r)

instance AdaptableDomains Double Double where
  toDomains a = (V.singleton a, V.empty, V.empty, V.empty)
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons v0 of
    Just (a, rest) -> (a, (rest, v1, v2, vX))
    Nothing -> error "fromDomains in AdaptableDomains Double Double"

instance ADModeAndNum d Double
         => AdaptableInputs d Double (ADVal d Double) where
  fromADInputs inputs@ADInputs{..} = case V.uncons inputPrimal0 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual0 of
      Just (aDual, restDual) ->
        ( dD aPrimal aDual
        , inputs {inputPrimal0 = restPrimal, inputDual0 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs Double"
    Nothing -> error "fromADInputs in AdaptableInputs Double"

instance (Numeric r, OS.Shape sh)
         => AdaptableDomains r (OS.Array sh r) where
  toDomains a =
    (V.empty, V.empty, V.empty, V.singleton (Data.Array.Convert.convert a))
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons vX of
    Just (a, rest) -> (toShapedOrDummy a, (v0, v1, v2, rest))
    Nothing -> error "fromDomains in AdaptableDomains r (OS.Array sh r)"

instance (ADModeAndNum d r, OS.Shape sh)
         => AdaptableInputs d r (ADVal d (OS.Array sh r)) where
  fromADInputs inputs@ADInputs{..} = case V.uncons inputPrimalX of
    Just (aPrimal, restPrimal) -> case V.uncons inputDualX of
      Just (aDual, restDual) ->
        ( fromXS $ dD aPrimal aDual
        , inputs {inputPrimalX = restPrimal, inputDualX = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (OS.Array sh r)"
    Nothing -> error "fromADInputs in AdaptableInputs (OS.Array sh r)"

instance (Numeric r, AdaptableDomains r a)
         => AdaptableDomains r [a] where
  toDomains l =
    let (l0, l1, l2, lX) = unzip4 $ map toDomains l
    in (V.concat l0, V.concat l1, V.concat l2, V.concat lX)
  fromDomains lInit params =
    let f (lAcc, restAcc) aInit = let (a, rest) = fromDomains aInit restAcc
                                  in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], params) lInit
    in (reverse l, restAll)

instance ( ADModeAndNum d r
         , AdaptableInputs d r (ADVal d a) )
         => AdaptableInputs d r [ADVal d a] where
  fromADInputs _inputs = undefined

instance ( Numeric r
         , AdaptableDomains r a
         , AdaptableDomains r b ) => AdaptableDomains r (a, b) where
  toDomains (a, b) =
    let (a0, a1, a2, aX) = toDomains a
        (b0, b1, b2, bX) = toDomains b
    in ( V.concat [a0, b0]
       , V.concat [a1, b1]
       , V.concat [a2, b2]
       , V.concat [aX, bX] )
  fromDomains (aInit, bInit) params =
    let (a, aRest) = fromDomains aInit params
        (b, bRest) = fromDomains bInit aRest
    in ((a, b), bRest)

instance ( Numeric r
         , AdaptableDomains r a
         , AdaptableDomains r b
         , AdaptableDomains r c ) => AdaptableDomains r (a, b, c) where
  toDomains (a, b, c) =
    let (a0, a1, a2, aX) = toDomains a
        (b0, b1, b2, bX) = toDomains b
        (c0, c1, c2, cX) = toDomains c
    in ( V.concat [a0, b0, c0]
       , V.concat [a1, b1, c1]
       , V.concat [a2, b2, c2]
       , V.concat [aX, bX, cX] )
  fromDomains (aInit, bInit, cInit) params =
    let (a, aRest) = fromDomains aInit params
        (b, bRest) = fromDomains bInit aRest
        (c, rest) = fromDomains cInit bRest
    in ((a, b, c), rest)

instance ( Numeric r
         , AdaptableDomains r a
         , AdaptableDomains r b
         , AdaptableDomains r c
         , AdaptableDomains r d ) => AdaptableDomains r (a, b, c, d) where
  toDomains (a, b, c, d) =
    let (a0, a1, a2, aX) = toDomains a
        (b0, b1, b2, bX) = toDomains b
        (c0, c1, c2, cX) = toDomains c
        (d0, d1, d2, dX) = toDomains d
    in ( V.concat [a0, b0, c0, d0]
       , V.concat [a1, b1, c1, d1]
       , V.concat [a2, b2, c2, d2]
       , V.concat [aX, bX, cX, dX] )
  fromDomains (aInit, bInit, cInit, dInit) params =
    let (a, aRest) = fromDomains aInit params
        (b, bRest) = fromDomains bInit aRest
        (c, cRest) = fromDomains cInit bRest
        (d, rest) = fromDomains dInit cRest
    in ((a, b, c, d), rest)

instance ( ADModeAndNum d r
         , AdaptableInputs d r a
         , AdaptableInputs d r b
         , AdaptableInputs d r c )
         => AdaptableInputs d r (a, b, c) where
  fromADInputs _inputs = undefined

instance ( ADModeAndNum d r
         , AdaptableInputs d r a
         , AdaptableInputs d r b
         , AdaptableInputs d r c
         , AdaptableInputs d r d' )
         => AdaptableInputs d r (a, b, c, d') where
  fromADInputs _inputs = undefined
