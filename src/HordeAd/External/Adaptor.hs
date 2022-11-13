{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, RankNTypes, TypeFamilies,
             TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module HordeAd.External.Adaptor
  ( Adaptable, AdaptableScalar
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

value :: forall a vals r advals.
         ( r ~ Scalar vals, vals ~ Value advals
         , Numeric r, Adaptable 'ADModeValue advals )
      => (advals -> ADVal 'ADModeValue a) -> vals -> a
value f vals =
  let g inputs = f $ fst $ fromADInputs vals inputs
  in valueFun g (toDomains vals)

rev :: forall a vals r advals.
       ( r ~ Scalar vals, vals ~ Value advals
       , HasDelta r, IsPrimalAndHasFeatures 'ADModeGradient a r
       , Adaptable 'ADModeGradient advals )
    => (advals -> ADVal 'ADModeGradient a) -> vals -> vals
rev f vals =
  let g inputs = f $ fst $ fromADInputs vals inputs
  in fst $ fromDomains vals $ fst $ revFun 1 g (toDomains vals)

fwd :: forall a vals r advals.
       ( r ~ Scalar vals, vals ~ Value advals
       , Numeric r, Dual 'ADModeDerivative r ~ r
       , Adaptable 'ADModeDerivative advals )
    => (advals -> ADVal 'ADModeDerivative a) -> vals -> vals
    -> Dual 'ADModeDerivative a  -- normally equals @a@
fwd f x ds =
  let g inputs = f $ fst $ fromADInputs ds inputs
  in fst $ fwdFun (toDomains x) g (toDomains ds)

-- Inspired by adaptors from @tomjaguarpaw's branch.
type Adaptable d advals =
  ( AdaptableDomains (Value advals)
  , AdaptableInputs d (Scalar (Value advals)) advals )

type AdaptableScalar d r =
  ( Scalar r ~ r, Value (ADVal d r) ~ r
  , ADModeAndNum d r, Adaptable d (ADVal d r) )

class AdaptableDomains vals where
  type Scalar vals
  toDomains
    :: Numeric (Scalar vals)
    => vals -> Domains (Scalar vals)
  fromDomains
    :: Numeric (Scalar vals)
    => vals -> Domains (Scalar vals) -> (vals, Domains (Scalar vals))

class AdaptableInputs d r advals where
  type Value advals
  fromADInputs
    :: Value advals -> ADInputs d r -> (advals, ADInputs d r)

instance AdaptableDomains Double where
  type Scalar Double = Double
  toDomains a = (V.singleton a, V.empty, V.empty, V.empty)
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons v0 of
    Just (a, rest) -> (a, (rest, v1, v2, vX))
    Nothing -> error "fromDomains in AdaptableDomains Double"

instance ADModeAndNum d Double
         => AdaptableInputs d Double (ADVal d Double) where
  type Value (ADVal d Double) = Double
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimal0 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual0 of
      Just (aDual, restDual) ->
        ( dD aPrimal aDual
        , inputs {inputPrimal0 = restPrimal, inputDual0 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs Double"
    Nothing -> error "fromADInputs in AdaptableInputs Double"

instance OS.Shape sh
         => AdaptableDomains (OS.Array sh r) where
  type Scalar (OS.Array sh r) = r
  toDomains a =
    (V.empty, V.empty, V.empty, V.singleton (Data.Array.Convert.convert a))
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons vX of
    Just (a, rest) -> (toShapedOrDummy a, (v0, v1, v2, rest))
    Nothing -> error "fromDomains in AdaptableDomains (OS.Array sh r)"

instance (ADModeAndNum d r, OS.Shape sh)
         => AdaptableInputs d r (ADVal d (OS.Array sh r)) where
  type Value (ADVal d (OS.Array sh r)) = OS.Array sh r
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimalX of
    Just (aPrimal, restPrimal) -> case V.uncons inputDualX of
      Just (aDual, restDual) ->
        ( fromXS $ dD aPrimal aDual
        , inputs {inputPrimalX = restPrimal, inputDualX = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (OS.Array sh r)"
    Nothing -> error "fromADInputs in AdaptableInputs (OS.Array sh r)"

instance AdaptableDomains a
         => AdaptableDomains [a] where
  type Scalar [a] = Scalar a
  toDomains l =
    let (l0, l1, l2, lX) = unzip4 $ map toDomains l
    in (V.concat l0, V.concat l1, V.concat l2, V.concat lX)
  fromDomains lInit source =
    let f (lAcc, restAcc) aInit =
          let (a, rest) = fromDomains aInit restAcc
          in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], source) lInit
    in (reverse l, restAll)

instance AdaptableInputs d r a
         => AdaptableInputs d r [a] where
  type Value [a] = [Value a]
  fromADInputs lInit sources =
    let f (lAcc, restAcc) aInit =
          let (a, rest) = fromADInputs aInit restAcc
          in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], sources) lInit
    in (reverse l, restAll)

instance ( r ~ Scalar a, r ~ Scalar b
         , AdaptableDomains a
         , AdaptableDomains b ) => AdaptableDomains (a, b) where
  type Scalar (a, b) = Scalar a
  toDomains (a, b) =
    let (a0, a1, a2, aX) = toDomains a
        (b0, b1, b2, bX) = toDomains b
    in ( V.concat [a0, b0]
       , V.concat [a1, b1]
       , V.concat [a2, b2]
       , V.concat [aX, bX] )
  fromDomains (aInit, bInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
    in ((a, b), bRest)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c ) => AdaptableDomains (a, b, c) where
  type Scalar (a, b, c) = Scalar a
  toDomains (a, b, c) =
    let (a0, a1, a2, aX) = toDomains a
        (b0, b1, b2, bX) = toDomains b
        (c0, c1, c2, cX) = toDomains c
    in ( V.concat [a0, b0, c0]
       , V.concat [a1, b1, c1]
       , V.concat [a2, b2, c2]
       , V.concat [aX, bX, cX] )
  fromDomains (aInit, bInit, cInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
        (c, rest) = fromDomains cInit bRest
    in ((a, b, c), rest)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c
         , AdaptableDomains d ) => AdaptableDomains (a, b, c, d) where
  type Scalar (a, b, c, d) = Scalar a
  toDomains (a, b, c, d) =
    let (a0, a1, a2, aX) = toDomains a
        (b0, b1, b2, bX) = toDomains b
        (c0, c1, c2, cX) = toDomains c
        (d0, d1, d2, dX) = toDomains d
    in ( V.concat [a0, b0, c0, d0]
       , V.concat [a1, b1, c1, d1]
       , V.concat [a2, b2, c2, d2]
       , V.concat [aX, bX, cX, dX] )
  fromDomains (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
        (c, cRest) = fromDomains cInit bRest
        (d, rest) = fromDomains dInit cRest
    in ((a, b, c, d), rest)

instance ( AdaptableInputs d r a
         , AdaptableInputs d r b )
         => AdaptableInputs d r (a, b) where
  type Value (a, b) = (Value a, Value b)
  fromADInputs (aInit, bInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, rest) = fromADInputs bInit aRest
    in ((a, b), rest)

instance ( AdaptableInputs d r a
         , AdaptableInputs d r b
         , AdaptableInputs d r c )
         => AdaptableInputs d r (a, b, c) where
  type Value (a, b, c) = (Value a, Value b, Value c)
  fromADInputs (aInit, bInit, cInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, rest) = fromADInputs cInit bRest
    in ((a, b, c), rest)

instance ( AdaptableInputs d r a
         , AdaptableInputs d r b
         , AdaptableInputs d r c
         , AdaptableInputs d r d' )
         => AdaptableInputs d r (a, b, c, d') where
  type Value (a, b, c, d') = (Value a, Value b, Value c, Value d')
  fromADInputs (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, cRest) = fromADInputs cInit bRest
        (d, rest) = fromADInputs dInit cRest
    in ((a, b, c, d), rest)
