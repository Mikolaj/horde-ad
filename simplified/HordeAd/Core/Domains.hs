{-# LANGUAGE UndecidableInstances #-}
-- | A general representation of the domains of objective functions
-- that become the codomains of the gradient functions.
module HordeAd.Core.Domains
  ( DynamicTensor(..)
  , DomainsCollection(..)
  , AdaptableDomains(..)
  , parseDomains
  , RandomDomains(randomVals)
  ) where

import Prelude

import           Control.Arrow ((&&&))
import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OD
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.Random

import HordeAd.Internal.TensorOps

-- * Domains

-- The untyped versions of tensors, to put many ranks/shapes in one vector.
class DynamicTensor r where
  type DTensorOf r = result | result -> r
  ddummy :: DTensorOf r
  disDummy :: DTensorOf r -> Bool

class DomainsCollection r where
  type Domains r = result | result -> r
  doms0 :: Domains r -> DTensorOf r
  domsR :: Domains r -> Domains r
  mkDoms :: DTensorOf r -> Domains r -> Domains r
  emptyDoms0 :: DTensorOf r
  isEmptyDoms :: Domains r -> Bool
  uncons0 :: Domains r -> Maybe (r, Domains r)
  unconsR :: Domains r -> Maybe (DTensorOf r, Domains r)
  concatDom0 :: [DTensorOf r] -> DTensorOf r
  concatDomR :: [Domains r] -> Domains r

instance DynamicTensor Double where
  type DTensorOf Double = OD.Array Double
  ddummy = dummyTensor
  disDummy = isTensorDummy

instance DynamicTensor Float where
  type DTensorOf Float = OD.Array Float
  ddummy = dummyTensor
  disDummy = isTensorDummy

instance DomainsCollection Double where
  type Domains Double = Data.Vector.Vector (OD.Array Double)
  doms0 v = v V.! 0
  domsR v = V.slice 1 (V.length v - 1) v
  mkDoms = V.cons
  emptyDoms0 = OD.constant [0] 0
  isEmptyDoms params = OD.shapeL (doms0 params) == [0] && V.null (domsR params)
  uncons0 params =
    let v = OD.toVector $ doms0 params
    in case V.uncons v of
      Nothing -> Nothing
      Just (h, rest) ->
        Just (h, mkDoms (OD.fromVector [V.length rest] rest) (domsR params))
  unconsR params =
    let v = domsR params
    in case V.uncons v of
      Nothing -> Nothing
      Just (h, rest) ->
        Just (h, mkDoms (doms0 params) rest)
  concatDom0 = OD.concatOuter
  concatDomR = V.concat

instance DomainsCollection Float where
  type Domains Float = Data.Vector.Vector (OD.Array Float)
  doms0 v = v V.! 0
  domsR v = V.slice 1 (V.length v - 1) v
  mkDoms = V.cons
  emptyDoms0 = OD.constant [0] 0
  isEmptyDoms params = OD.shapeL (doms0 params) == [0] && V.null (domsR params)
  uncons0 params =
    let v = OD.toVector $ doms0 params
    in case V.uncons v of
      Nothing -> Nothing
      Just (h, rest) ->
        Just (h, mkDoms (OD.fromVector [V.length rest] rest) (domsR params))
  unconsR params =
    let v = domsR params
    in case V.uncons v of
      Nothing -> Nothing
      Just (h, rest) ->
        Just (h, mkDoms (doms0 params) rest)
  concatDom0 = OD.concatOuter
  concatDomR = V.concat


-- * Adaptor classes

-- Inspired by adaptors from @tomjaguarpaw's branch.
class AdaptableDomains vals where
  type Scalar vals
  type Value vals
  toDomains :: vals -> Domains (Scalar vals)
  fromDomains :: Value vals -> Domains (Scalar vals)
              -> Maybe (vals, Domains (Scalar vals))
  nParams :: vals -> Int
  nScalars :: vals -> Int

class RandomDomains vals where
  randomVals
    :: forall r g.
       ( RandomGen g
       , r ~ Scalar vals, Numeric r, Fractional r, Random r, Num (Vector r) )
    => r -> g -> (vals, g)

parseDomains
  :: (AdaptableDomains vals, DomainsCollection (Scalar vals))
  => Value vals -> Domains (Scalar vals) -> vals
parseDomains aInit domains =
  case fromDomains aInit domains of
    Just (vals, rest) -> assert (isEmptyDoms rest) vals
    Nothing -> error "parseDomains: Nothing"


-- * Basic Adaptor class instances

instance AdaptableDomains Double where
  type Scalar Double = Double
  type Value Double = Double
  toDomains a = mkDoms (OD.constant [1] a) V.empty
  fromDomains _aInit = uncons0
  nParams _ = 1
  nScalars _ = 1

instance RandomDomains Double where
  randomVals range = randomR (- range, range)
    -- note that unlike in hmatrix the range is closed from the top

instance AdaptableDomains Float where
  type Scalar Float = Float
  type Value Float = Float
  toDomains a = mkDoms (OD.constant [1] a) V.empty
  fromDomains _aInit = uncons0
  nParams _ = 1
  nScalars _ = 1

instance RandomDomains Float where
  randomVals range = randomR (- range, range)

instance (AdaptableDomains a, r ~ Scalar a, DomainsCollection r)
         => AdaptableDomains [a] where
  type Scalar [a] = Scalar a
  type Value [a] = [Value a]
  toDomains l =
    let (l0, l1) = unzip $ map ((doms0 &&& domsR) . toDomains) l
    in mkDoms (concatDom0 l0) (concatDomR l1)
  fromDomains lInit source =
    let f (lAcc, restAcc) aInit =
          case fromDomains aInit restAcc of
            Just (a, rest) -> (a : lAcc, rest)
            Nothing -> error "fromDomains [a]"
        (l, restAll) = foldl' f ([], source) lInit
    in Just (reverse l, restAll)
    -- is the following as performant? benchmark:
    -- > fromDomains lInit source =
    -- >   let f = swap . flip fromDomains
    -- >   in swap $ mapAccumL f source lInit
  nParams = sum . map nParams
  nScalars = sum . map nScalars

instance ( DomainsCollection r
         , r ~ Scalar a, r ~ Scalar b
         , AdaptableDomains a
         , AdaptableDomains b ) => AdaptableDomains (a, b) where
  type Scalar (a, b) = Scalar a
  type Value (a, b) = (Value a, Value b)
  toDomains (a, b) =
    let (a0, a1) = doms0 &&& domsR $ toDomains a
        (b0, b1) = doms0 &&& domsR $ toDomains b
    in mkDoms (concatDom0 [a0, b0])
              (concatDomR [a1, b1])
  fromDomains (aInit, bInit) source = do
    (a, aRest) <- fromDomains aInit source
    (b, bRest) <- fromDomains bInit aRest
    return ((a, b), bRest)
  nParams (a, b) = nParams a + nParams b
  nScalars (a, b) = nScalars a + nScalars b

instance ( r ~ Scalar a, r ~ Scalar b
         , RandomDomains a
         , RandomDomains b ) => RandomDomains (a, b) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
    in ((v1, v2), g2)

instance ( DomainsCollection r
         , r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c ) => AdaptableDomains (a, b, c) where
  type Scalar (a, b, c) = Scalar a
  type Value (a, b, c) = (Value a, Value b, Value c)
  toDomains (a, b, c) =
    let (a0, a1) = doms0 &&& domsR $ toDomains a
        (b0, b1) = doms0 &&& domsR $ toDomains b
        (c0, c1) = doms0 &&& domsR $ toDomains c
    in mkDoms (concatDom0 [a0, b0, c0])
              (concatDomR [a1, b1, c1])
  fromDomains (aInit, bInit, cInit) source = do
    (a, aRest) <- fromDomains aInit source
    (b, bRest) <- fromDomains bInit aRest
    (c, cRest) <- fromDomains cInit bRest
    return ((a, b, c), cRest)
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

instance ( DomainsCollection r
         , r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c
         , AdaptableDomains d ) => AdaptableDomains (a, b, c, d) where
  type Scalar (a, b, c, d) = Scalar a
  type Value (a, b, c, d) = (Value a, Value b, Value c, Value d)
  toDomains (a, b, c, d) =
    let (a0, a1) = doms0 &&& domsR $ toDomains a
        (b0, b1) = doms0 &&& domsR $ toDomains b
        (c0, c1) = doms0 &&& domsR $ toDomains c
        (d0, d1) = doms0 &&& domsR $ toDomains d
    in mkDoms (concatDom0 [a0, b0, c0, d0])
              (concatDomR [a1, b1, c1, d1])
  fromDomains (aInit, bInit, cInit, dInit) source = do
    (a, aRest) <- fromDomains aInit source
    (b, bRest) <- fromDomains bInit aRest
    (c, cRest) <- fromDomains cInit bRest
    (d, dRest) <- fromDomains dInit cRest
    return ((a, b, c, d), dRest)
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

instance ( r ~ Scalar a, r ~ Scalar b
         , AdaptableDomains a, AdaptableDomains b )
         => AdaptableDomains (Either a b) where
  type Scalar (Either a b) = Scalar a
  type Value (Either a b) = Either (Value a) (Value b)
  toDomains e = case e of
    Left a -> toDomains a
    Right b -> toDomains b
  fromDomains eInit source = case eInit of
    Left a -> case fromDomains a source of
                Just (a2, rest) -> Just (Left a2, rest)
                Nothing -> Nothing
    Right b -> case fromDomains b source of
                 Just (b2, rest) -> Just (Right b2, rest)
                 Nothing -> Nothing
  nParams = either nParams nParams
  nScalars = either nScalars nScalars

instance ( AdaptableDomains a, DomainsCollection (Scalar a) )
         => AdaptableDomains (Maybe a) where
  type Scalar (Maybe a) = Scalar a
  type Value (Maybe a) = Maybe (Value a)
  toDomains e = case e of
    Nothing -> mkDoms emptyDoms0 (concatDomR [])
    Just a -> toDomains a
  fromDomains eInit source = case eInit of
    Nothing -> Just (Nothing, source)
    Just a -> case fromDomains a source of
                Just (a2, rest) -> Just (Just a2, rest)
                Nothing -> Nothing
  nParams = maybe 0 nParams
  nScalars = maybe 0 nScalars
