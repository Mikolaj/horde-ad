{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, RankNTypes, TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module HordeAd.External.Adaptor
  ( Adaptable, AdaptableScalar
  , value, rev, fwd
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl', unzip4)
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)

import HordeAd.Core.DualClass (Dual, toDynamicOrDummy, toShapedOrDummy)
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors

value :: forall a vals r advals d.
         ( r ~ Scalar vals, vals ~ Value advals
         , d ~ Mode advals, d ~ 'ADModeValue
         , Numeric r, Adaptable advals )
      => (advals -> ADVal d a) -> vals -> a
value f vals =
  let g inputs = f $ fst $ fromADInputs vals inputs
  in valueFun g (toDomains vals)

rev :: forall a vals r advals d.
       ( r ~ Scalar vals, vals ~ Value advals
       , d ~ Mode advals, d ~ 'ADModeGradient
       , HasDelta r, IsPrimalAndHasFeatures d a r
       , Adaptable advals )
    => (advals -> ADVal d a) -> vals -> vals
rev f vals =
  let g inputs = f $ fst $ fromADInputs vals inputs
  in fst $ fromDomains vals $ fst $ revFun 1 g (toDomains vals)

fwd :: forall a vals r advals d.
       ( r ~ Scalar vals, vals ~ Value advals
       , d ~ Mode advals, d ~ 'ADModeDerivative
       , Numeric r, Dual d r ~ r
       , Adaptable advals )
    => (advals -> ADVal d a) -> vals -> vals
    -> Dual d a  -- normally equals @a@
fwd f x ds =
  let g inputs = f $ fst $ fromADInputs ds inputs
  in fst $ fwdFun (toDomains x) g (toDomains ds)

-- Inspired by adaptors from @tomjaguarpaw's branch.
type Adaptable advals =
  ( AdaptableDomains (Value advals)
  , AdaptableInputs (Scalar (Value advals)) advals )

type AdaptableScalar d r =
  ( Scalar r ~ r, Value (ADVal d r) ~ r, Mode (ADVal d r) ~ d
  , ADModeAndNum d r, Adaptable (ADVal d r) )

-- TODO: merge these two classes. Is it even possible?
-- Bonus points if no AllowAmbiguousTypes nor UndecidableInstances
-- have to be added.
class AdaptableDomains vals where
  type Scalar vals
  toDomains
    :: Numeric (Scalar vals)
    => vals -> Domains (Scalar vals)
  fromDomains
    :: Numeric (Scalar vals)
    => vals -> Domains (Scalar vals) -> (vals, Domains (Scalar vals))

class AdaptableInputs r advals where
  type Value advals
  type Mode advals :: ADMode
  fromADInputs
    :: Value advals -> ADInputs (Mode advals) r
    -> (advals, ADInputs (Mode advals) r)

instance AdaptableDomains Double where
  type Scalar Double = Double
  toDomains a = (V.singleton a, V.empty, V.empty, V.empty)
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons v0 of
    Just (a, rest) -> (a, (rest, v1, v2, vX))
    Nothing -> error "fromDomains in AdaptableDomains Double"

instance ADModeAndNum d Double
         => AdaptableInputs Double (ADVal d Double) where
  type Value (ADVal d Double) = Double
  type Mode (ADVal d Double) = d
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimal0 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual0 of
      Just (aDual, restDual) ->
        ( dD aPrimal aDual
        , inputs {inputPrimal0 = restPrimal, inputDual0 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs Double"
    Nothing -> error "fromADInputs in AdaptableInputs Double"

instance AdaptableDomains Float where
  type Scalar Float = Float
  toDomains a = (V.singleton a, V.empty, V.empty, V.empty)
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons v0 of
    Just (a, rest) -> (a, (rest, v1, v2, vX))
    Nothing -> error "fromDomains in AdaptableDomains Float"

instance ADModeAndNum d Float
         => AdaptableInputs Float (ADVal d Float) where
  type Value (ADVal d Float) = Float
  type Mode (ADVal d Float) = d
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimal0 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual0 of
      Just (aDual, restDual) ->
        ( dD aPrimal aDual
        , inputs {inputPrimal0 = restPrimal, inputDual0 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs Float"
    Nothing -> error "fromADInputs in AdaptableInputs Float"

instance AdaptableDomains (Vector r) where
  type Scalar (Vector r) = r
  toDomains a = (V.empty, V.singleton a, V.empty, V.empty)
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons v1 of
    Just (a, rest) -> (a, (v0, rest, v2, vX))
    Nothing -> error "fromDomains in AdaptableDomains (Vector r)"

instance ADModeAndNum d r
         => AdaptableInputs r (ADVal d (Vector r)) where
  type Value (ADVal d (Vector r)) = Vector r
  type Mode (ADVal d (Vector r)) = d
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimal1 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual1 of
      Just (aDual, restDual) ->
        ( dD aPrimal aDual
        , inputs {inputPrimal1 = restPrimal, inputDual1 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (Vector r)"
    Nothing -> error "fromADInputs in AdaptableInputs (Vector r)"

instance AdaptableDomains (Matrix r) where
  type Scalar (Matrix r) = r
  toDomains a = (V.empty, V.empty, V.singleton a, V.empty)
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons v2 of
    Just (a, rest) -> (a, (v0, v1, rest, vX))
    Nothing -> error "fromDomains in AdaptableDomains (Matrix r)"

instance ADModeAndNum d r
         => AdaptableInputs r (ADVal d (Matrix r)) where
  type Value (ADVal d (Matrix r)) = Matrix r
  type Mode (ADVal d (Matrix r)) = d
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimal2 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual2 of
      Just (aDual, restDual) ->
        ( dD aPrimal aDual
        , inputs {inputPrimal2 = restPrimal, inputDual2 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (Matrix r)"
    Nothing -> error "fromADInputs in AdaptableInputs (Matrix r)"

instance AdaptableDomains (OT.Array r) where
  type Scalar (OT.Array r) = r
  toDomains a = (V.empty, V.empty, V.empty, V.singleton a)
  fromDomains aInit (v0, v1, v2, vX) = case V.uncons vX of
    Just (a, rest) -> (toDynamicOrDummy (OT.shapeL aInit) a, (v0, v1, v2, rest))
    Nothing -> error "fromDomains in AdaptableDomains (OT.Array r)"

instance ADModeAndNum d r
         => AdaptableInputs r (ADVal d (OT.Array r)) where
  type Value (ADVal d (OT.Array r)) = OT.Array r
  type Mode (ADVal d (OT.Array r)) = d
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimalX of
    Just (aPrimal, restPrimal) -> case V.uncons inputDualX of
      Just (aDual, restDual) ->
        ( dD aPrimal aDual
        , inputs {inputPrimalX = restPrimal, inputDualX = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (OT.Array r)"
    Nothing -> error "fromADInputs in AdaptableInputs (OT.Array r)"

instance OS.Shape sh
         => AdaptableDomains (OS.Array sh r) where
  type Scalar (OS.Array sh r) = r
  toDomains a =
    (V.empty, V.empty, V.empty, V.singleton (Data.Array.Convert.convert a))
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons vX of
    Just (a, rest) -> (toShapedOrDummy a, (v0, v1, v2, rest))
    Nothing -> error "fromDomains in AdaptableDomains (OS.Array sh r)"

instance (ADModeAndNum d r, OS.Shape sh)
         => AdaptableInputs r (ADVal d (OS.Array sh r)) where
  type Value (ADVal d (OS.Array sh r)) = OS.Array sh r
  type Mode (ADVal d (OS.Array sh r)) = d
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

instance AdaptableInputs r a
         => AdaptableInputs r [a] where
  type Value [a] = [Value a]
  type Mode [a] = Mode a
  fromADInputs lInit source =
    let f (lAcc, restAcc) aInit =
          let (a, rest) = fromADInputs aInit restAcc
          in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], source) lInit
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

instance ( d ~ Mode a, d ~ Mode b
         , AdaptableInputs r a
         , AdaptableInputs r b )
         => AdaptableInputs r (a, b) where
  type Value (a, b) = (Value a, Value b)
  type Mode (a, b) = Mode a
  fromADInputs (aInit, bInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, rest) = fromADInputs bInit aRest
    in ((a, b), rest)

instance ( d ~ Mode a, d ~ Mode b, d ~ Mode c
         , AdaptableInputs r a
         , AdaptableInputs r b
         , AdaptableInputs r c )
         => AdaptableInputs r (a, b, c) where
  type Value (a, b, c) = (Value a, Value b, Value c)
  type Mode (a, b, c) = Mode a
  fromADInputs (aInit, bInit, cInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, rest) = fromADInputs cInit bRest
    in ((a, b, c), rest)

instance ( dd ~ Mode a, dd ~ Mode b, dd ~ Mode c, dd ~ Mode d
         , AdaptableInputs r a
         , AdaptableInputs r b
         , AdaptableInputs r c
         , AdaptableInputs r d )
         => AdaptableInputs r (a, b, c, d) where
  type Value (a, b, c, d) = (Value a, Value b, Value c, Value d)
  type Mode (a, b, c, d) = Mode a
  fromADInputs (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, cRest) = fromADInputs cInit bRest
        (d, rest) = fromADInputs dInit cRest
    in ((a, b, c, d), rest)

instance (r ~ Scalar a, r ~ Scalar b, AdaptableDomains a, AdaptableDomains b)
         => AdaptableDomains (Either a b) where
  type Scalar (Either a b) = Scalar a
  toDomains e = case e of
    Left a -> toDomains a
    Right b -> toDomains b
  fromDomains eInit source = case eInit of
    Left a -> let (a2, rest) = fromDomains a source
              in (Left a2, rest)
    Right b -> let (b2, rest) = fromDomains b source
               in (Right b2, rest)

instance (dd ~ Mode a, dd ~ Mode b, AdaptableInputs r a, AdaptableInputs r b)
         => AdaptableInputs r (Either a b) where
  type Value (Either a b) = Either (Value a) (Value b)
  type Mode (Either a b) = Mode a
  fromADInputs eInit source = case eInit of
    Left a -> let (a2, rest) = fromADInputs a source
              in (Left a2, rest)
    Right b -> let (b2, rest) = fromADInputs b source
               in (Right b2, rest)

instance AdaptableDomains a
         => AdaptableDomains (Maybe a) where
  type Scalar (Maybe a) = Scalar a
  toDomains e = case e of
    Nothing -> (V.empty, V.empty, V.empty, V.empty)
    Just a -> toDomains a
  fromDomains eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromDomains a source
              in (Just a2, rest)

instance AdaptableInputs r a
         => AdaptableInputs r (Maybe a) where
  type Value (Maybe a) = Maybe (Value a)
  type Mode (Maybe a) = Mode a
  fromADInputs eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromADInputs a source
              in (Just a2, rest)
