{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module HordeAd.External.Adaptor
  ( Adaptable, AdaptableScalar
  , AdaptableDomains(toDomains, nParams, nScalars)
  , RandomDomains(randomVals)
  , AdaptableInputs(Value), parseADInputs
  , value, valueAtDomains, rev, revDt, fwd
  ) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl', unzip4)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors
import HordeAd.Internal.TensorOps

value :: forall a vals r advals d.
         ( r ~ Scalar vals, vals ~ Value advals
         , d ~ Mode advals, d ~ 'ADModeValue
         , Numeric r, Adaptable advals )
      => (advals -> ADVal d a) -> vals -> a
value f vals = valueAtDomains vals (toDomains vals) f

valueAtDomains :: forall a vals r advals d.
                  ( r ~ Scalar vals, vals ~ Value advals
                  , d ~ Mode advals, d ~ 'ADModeValue
                  , Numeric r, Adaptable advals )
               => vals -> Domains r -> (advals -> ADVal d a) -> a
valueAtDomains vals flattenedParameters f =
  let g inputs = f $ parseADInputs vals inputs
  in valueOnDomains g flattenedParameters

rev :: forall a vals r advals d.
       ( r ~ Scalar vals, vals ~ Value advals
       , d ~ Mode advals, d ~ 'ADModeGradient
       , HasDelta r, IsPrimalAndHasInputs d a r
       , Adaptable advals )
    => (advals -> ADVal d a) -> vals
    -> vals
rev f vals = revDt f vals 1

-- This version additionally takes the sensitivity parameter.
revDt :: forall a vals r advals d.
         ( r ~ Scalar vals, vals ~ Value advals
         , d ~ Mode advals, d ~ 'ADModeGradient
         , HasDelta r, IsPrimalAndHasInputs d a r
         , Adaptable advals )
      => (advals -> ADVal d a) -> vals -> a
      -> vals
revDt f vals dt =
  let g inputs = f $ parseADInputs vals inputs
  in parseDomains vals $ fst $ revOnDomains dt g (toDomains vals)

-- This takes the sensitivity parameter, by convention.
fwd :: forall a vals r advals d.
       ( r ~ Scalar vals, vals ~ Value advals
       , d ~ Mode advals, d ~ 'ADModeDerivative
       , Numeric r, Dual d r ~ r
       , Adaptable advals )
    => (advals -> ADVal d a) -> vals -> vals
    -> Dual d a  -- normally equals @a@
fwd f x ds =
  let g inputs = f $ parseADInputs ds inputs
  in fst $ fwdOnDomains (toDomains x) g (toDomains ds)

-- Inspired by adaptors from @tomjaguarpaw's branch.
type Adaptable advals =
  ( AdaptableDomains (Value advals)
  , AdaptableInputs (Scalar (Value advals)) advals )

type AdaptableScalar d r =
  ( Scalar r ~ r, Value (ADVal d r) ~ r, Mode (ADVal d r) ~ d
  , ADModeAndNum d r, Adaptable (ADVal d r)
  , Random r )

-- TODO: merge these two classes. Is it even possible?
-- Bonus points if no AllowAmbiguousTypes nor UndecidableInstances
-- have to be added.
class AdaptableDomains vals where
  type Scalar vals
  toDomains :: Numeric (Scalar vals)
            => vals -> Domains (Scalar vals)
  fromDomains :: Numeric (Scalar vals)
              => vals -> Domains (Scalar vals)
              -> (vals, Domains (Scalar vals))
  nParams :: vals -> Int
  nScalars :: Numeric (Scalar vals)
              => vals -> Int

class RandomDomains vals where
  randomVals
    :: forall r g.
       ( RandomGen g
       , r ~ Scalar vals, Numeric r, Fractional r, Random r, Num (Vector r) )
    => r -> g -> (vals, g)

class AdaptableInputs r advals where
  type Value advals
  type Mode advals :: ADMode
  fromADInputs :: Value advals -> ADInputs (Mode advals) r
               -> (advals, ADInputs (Mode advals) r)

parseDomains :: (AdaptableDomains vals, Numeric (Scalar vals))
             => vals -> Domains (Scalar vals) -> vals
parseDomains aInit domains =
  let (vals, rest) = fromDomains aInit domains
  in assert (nullDomains rest) vals

parseADInputs :: (AdaptableInputs r advals, Numeric r)
              => Value advals -> ADInputs (Mode advals) r
              -> advals
parseADInputs aInit inputs =
  let (advals, rest) = fromADInputs aInit inputs
  in assert (nullADInputs rest) advals

instance AdaptableDomains Double where
  type Scalar Double = Double
  toDomains a = Domains (V.singleton a) V.empty V.empty V.empty
  fromDomains _aInit (Domains v0 v1 v2 vX) = case V.uncons v0 of
    Just (a, rest) -> (a, Domains rest v1 v2 vX)
    Nothing -> error "fromDomains in AdaptableDomains Double"
  nParams _ = 1
  nScalars _ = 1

instance RandomDomains Double where
  randomVals range = randomR (- range, range)
    -- note that unlike in hmatrix the range is closed from the top

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
  toDomains a = Domains (V.singleton a) V.empty V.empty V.empty
  fromDomains _aInit (Domains v0 v1 v2 vX) = case V.uncons v0 of
    Just (a, rest) -> (a, Domains rest v1 v2 vX)
    Nothing -> error "fromDomains in AdaptableDomains Float"
  nParams _ = 1
  nScalars _ = 1

instance RandomDomains Float where
  randomVals range = randomR (- range, range)

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
  toDomains a = Domains V.empty (V.singleton a) V.empty V.empty
  fromDomains aInit (Domains v0 v1 v2 vX) = case V.uncons v1 of
    Just (a, rest) -> (toVectorOrDummy (LA.size aInit) a, Domains v0 rest v2 vX)
    Nothing -> error "fromDomains in AdaptableDomains (Vector r)"
  nParams _ = 1
  nScalars = V.length

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
  toDomains a = Domains V.empty V.empty (V.singleton a) V.empty
  fromDomains aInit (Domains v0 v1 v2 vX) = case V.uncons v2 of
    Just (a, rest) -> (toMatrixOrDummy (LA.size aInit) a, Domains v0 v1 rest vX)
    Nothing -> error "fromDomains in AdaptableDomains (Matrix r)"
  nParams _ = 1
  nScalars m = let (rows, cols) = LA.size m in rows * cols

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

instance AdaptableDomains (OD.Array r) where
  type Scalar (OD.Array r) = r
  toDomains a = Domains V.empty V.empty V.empty (V.singleton a)
  fromDomains aInit (Domains v0 v1 v2 vX) = case V.uncons vX of
    Just (a, rest) ->
      (toDynamicOrDummy (OD.shapeL aInit) a, Domains v0 v1 v2 rest)
    Nothing -> error "fromDomains in AdaptableDomains (OD.Array r)"
  nParams _ = 1
  nScalars = OD.size

instance ADModeAndNum d r
         => AdaptableInputs r (ADVal d (OD.Array r)) where
  type Value (ADVal d (OD.Array r)) = OD.Array r
  type Mode (ADVal d (OD.Array r)) = d
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimalX of
    Just (aPrimal, restPrimal) -> case V.uncons inputDualX of
      Just (aDual, restDual) ->
        ( dD aPrimal aDual
        , inputs {inputPrimalX = restPrimal, inputDualX = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (OD.Array r)"
    Nothing -> error "fromADInputs in AdaptableInputs (OD.Array r)"

{- TODO: requires IncoherentInstances no matter what pragma I stick in
-- A special case, because for @Double@ we have faster @randomVals@,
-- though the quality of randomness is worse (going through a single @Int@).
instance {-# OVERLAPS #-} {-# OVERLAPPING #-}
         OS.Shape sh
         => AdaptableDomains (OS.Array sh Double) where
  type Scalar (OS.Array sh Double) = Double
  toDomains a =
    (V.empty, V.empty, V.empty, V.singleton (Data.Array.Convert.convert a))
  fromDomains _aInit (v0, v1, v2, vX) = case V.uncons vX of
    Just (a, rest) -> (toShapedOrDummy a, (v0, v1, v2, rest))
    Nothing -> error "fromDomains in AdaptableDomains (OS.Array sh r)"
  randomVals range g =
    let -- Note that hmatrix produces numbers from the range open at the top,
        -- unlike package random.
        createRandomVector n seedInt =
          LA.scale (2 * range)
          $ LA.randomVector seedInt LA.Uniform n - LA.scalar 0.5
        (i, g2) = random g
        arr = OS.fromVector $ createRandomVector (OS.sizeP (Proxy @sh)) i
    in (arr, g2)
-}

instance OS.Shape sh
         => AdaptableDomains (OS.Array sh r) where
  type Scalar (OS.Array sh r) = r
  toDomains a =
    Domains V.empty V.empty V.empty (V.singleton (Data.Array.Convert.convert a))
  fromDomains _aInit (Domains v0 v1 v2 vX) = case V.uncons vX of
    Just (a, rest) -> (toShapedOrDummy a, Domains v0 v1 v2 rest)
    Nothing -> error "fromDomains in AdaptableDomains (OS.Array sh r)"
  nParams _ = 1
  nScalars = OS.size

instance OS.Shape sh
         => RandomDomains (OS.Array sh r) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OS.fromVector $ createRandomVector (OS.sizeP (Proxy @sh)) g1
    in (arr, g2)

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
    let (l0, l1, l2, lX) = unzip4 $ map (domainsToQuadruple . toDomains) l
    in Domains (V.concat l0) (V.concat l1) (V.concat l2) (V.concat lX)
  fromDomains lInit source =
    let f (lAcc, restAcc) aInit =
          let (a, rest) = fromDomains aInit restAcc
          in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], source) lInit
    in (reverse l, restAll)
    -- is the following as performant? benchmark:
    -- > fromDomains lInit source =
    -- >   let f = swap . flip fromDomains
    -- >   in swap $ mapAccumL f source lInit
  nParams = sum . map nParams
  nScalars = sum . map nScalars

domainsToQuadruple :: Domains r -> (Domain0 r, Domain1 r, Domain2 r, DomainX r)
domainsToQuadruple Domains{..} = (domains0, domains1, domains2, domainsX)

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
    let Domains a0 a1 a2 aX = toDomains a
        Domains b0 b1 b2 bX = toDomains b
    in Domains (V.concat [a0, b0])
               (V.concat [a1, b1])
               (V.concat [a2, b2])
               (V.concat [aX, bX])
  fromDomains (aInit, bInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
    in ((a, b), bRest)
  nParams (a, b) = nParams a + nParams b
  nScalars (a, b) = nScalars a + nScalars b

instance ( r ~ Scalar a, r ~ Scalar b
         , RandomDomains a
         , RandomDomains b ) => RandomDomains (a, b) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
    in ((v1, v2), g2)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c ) => AdaptableDomains (a, b, c) where
  type Scalar (a, b, c) = Scalar a
  toDomains (a, b, c) =
    let Domains a0 a1 a2 aX = toDomains a
        Domains b0 b1 b2 bX = toDomains b
        Domains c0 c1 c2 cX = toDomains c
    in Domains (V.concat [a0, b0, c0])
               (V.concat [a1, b1, c1])
               (V.concat [a2, b2, c2])
               (V.concat [aX, bX, cX])
  fromDomains (aInit, bInit, cInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
        (c, rest) = fromDomains cInit bRest
    in ((a, b, c), rest)
  nParams (a, b, c) = nParams a + nParams b + nParams c
  nScalars (a, b, c) = nScalars a + nScalars b + nScalars c

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , RandomDomains a
         , RandomDomains b
         , RandomDomains c ) => RandomDomains (a, b, c) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
    in ((v1, v2, v3), g3)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c
         , AdaptableDomains d ) => AdaptableDomains (a, b, c, d) where
  type Scalar (a, b, c, d) = Scalar a
  toDomains (a, b, c, d) =
    let Domains a0 a1 a2 aX = toDomains a
        Domains b0 b1 b2 bX = toDomains b
        Domains c0 c1 c2 cX = toDomains c
        Domains d0 d1 d2 dX = toDomains d
    in Domains (V.concat [a0, b0, c0, d0])
               (V.concat [a1, b1, c1, d1])
               (V.concat [a2, b2, c2, d2])
               (V.concat [aX, bX, cX, dX])
  fromDomains (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
        (c, cRest) = fromDomains cInit bRest
        (d, rest) = fromDomains dInit cRest
    in ((a, b, c, d), rest)
  nParams (a, b, c, d) = nParams a + nParams b + nParams c + nParams d
  nScalars (a, b, c, d) = nScalars a + nScalars b + nScalars c + nScalars d

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , RandomDomains a
         , RandomDomains b
         , RandomDomains c
         , RandomDomains d ) => RandomDomains (a, b, c, d) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
        (v4, g4) = randomVals range g3
    in ((v1, v2, v3, v4), g4)

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

instance ( d ~ Mode a, d ~ Mode b, d ~ Mode c, d ~ Mode dd
         , AdaptableInputs r a
         , AdaptableInputs r b
         , AdaptableInputs r c
         , AdaptableInputs r dd )
         => AdaptableInputs r (a, b, c, dd) where
  type Value (a, b, c, dd) = (Value a, Value b, Value c, Value dd)
  type Mode (a, b, c, dd) = Mode a
  fromADInputs (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, cRest) = fromADInputs cInit bRest
        (dd, rest) = fromADInputs dInit cRest
    in ((a, b, c, dd), rest)

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
  nParams = either nParams nParams
  nScalars = either nScalars nScalars

instance (d ~ Mode a, d ~ Mode b, AdaptableInputs r a, AdaptableInputs r b)
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
    Nothing -> Domains V.empty V.empty V.empty V.empty
    Just a -> toDomains a
  fromDomains eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromDomains a source
              in (Just a2, rest)
  nParams = maybe 0 nParams
  nScalars = maybe 0 nScalars

instance AdaptableInputs r a
         => AdaptableInputs r (Maybe a) where
  type Value (Maybe a) = Maybe (Value a)
  type Mode (Maybe a) = Mode a
  fromADInputs eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromADInputs a source
              in (Just a2, rest)
