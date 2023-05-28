{-# LANGUAGE UndecidableInstances #-}
-- | A general representation of the domains of objective functions
-- that become the codomains of the gradient functions.
module HordeAd.Core.Domains
  ( DynamicTensor(..), Domains
  , Underlying, AdaptableDomains(..), parseDomains
  , RandomDomains(..)
  ) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OD
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.Random

-- The untyped versions of tensors, to put many ranks/shapes in one vector.
class DynamicTensor r where
  type DTensorOf r = result | result -> r

instance DynamicTensor Double where
  type DTensorOf Double = OD.Array Double

instance DynamicTensor Float where
  type DTensorOf Float = OD.Array Float

-- * Adaptor classes

-- When r is Ast, this is used for domains composed of variables only,
-- to adapt them into more complex types and back again. This is not used
-- for vectors of large terms, since they'd share values, so we'd need
-- AstDomainsLet, but these would make adapting the vector costly.
-- DomainsOf is used for that and the only reasons DomainsOf exists
-- is to prevent mixing up the two (and complicating the definition
-- below with errors in the AstDomainsLet case).
type Domains r = Data.Vector.Vector (DTensorOf r)

type Underlying a = Scalar (Value a)

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
  type ToRanked vals
  toRanked :: vals -> ToRanked vals

parseDomains
  :: AdaptableDomains vals
  => Value vals -> Domains (Scalar vals) -> vals
parseDomains aInit domains =
  case fromDomains aInit domains of
    Just (vals, rest) -> assert (V.null rest) vals
    Nothing -> error "parseDomains: Nothing"


-- * Basic Adaptor class instances

instance AdaptableDomains Double where
  type Scalar Double = Double
  type Value Double = Double
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

instance AdaptableDomains Float where
  type Scalar Float = Float
  type Value Float = Float
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

instance (AdaptableDomains a, r ~ Scalar a)
         => AdaptableDomains [a] where
  type Scalar [a] = Scalar a
  type Value [a] = [Value a]
  toDomains = V.concat . map toDomains
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

instance ( r ~ Scalar a, r ~ Scalar b
         , AdaptableDomains a
         , AdaptableDomains b ) => AdaptableDomains (a, b) where
  type Scalar (a, b) = Scalar a
  type Value (a, b) = (Value a, Value b)
  toDomains (a, b) =
    let a1 = toDomains a
        b1 = toDomains b
    in V.concat [a1, b1]
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
  type ToRanked (a, b) = (ToRanked a, ToRanked b)
  toRanked (a, b) = (toRanked a, toRanked b)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c ) => AdaptableDomains (a, b, c) where
  type Scalar (a, b, c) = Scalar a
  type Value (a, b, c) = (Value a, Value b, Value c)
  toDomains (a, b, c) =
    let a1 = toDomains a
        b1 = toDomains b
        c1 = toDomains c
    in V.concat [a1, b1, c1]
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
  type ToRanked (a, b, c) = (ToRanked a, ToRanked b, ToRanked c)
  toRanked (a, b, c) = (toRanked a, toRanked b, toRanked c)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c
         , AdaptableDomains d ) => AdaptableDomains (a, b, c, d) where
  type Scalar (a, b, c, d) = Scalar a
  type Value (a, b, c, d) = (Value a, Value b, Value c, Value d)
  toDomains (a, b, c, d) =
    let a1 = toDomains a
        b1 = toDomains b
        c1 = toDomains c
        d1 = toDomains d
    in V.concat [a1, b1, c1, d1]
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
  type ToRanked (a, b, c, d) = (ToRanked a, ToRanked b, ToRanked c, ToRanked d)
  toRanked (a, b, c, d) = (toRanked a, toRanked b, toRanked c, toRanked d)

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

instance AdaptableDomains a
         => AdaptableDomains (Maybe a) where
  type Scalar (Maybe a) = Scalar a
  type Value (Maybe a) = Maybe (Value a)
  toDomains e = case e of
    Nothing -> V.concat []
    Just a -> toDomains a
  fromDomains eInit source = case eInit of
    Nothing -> Just (Nothing, source)
    Just a -> case fromDomains a source of
                Just (a2, rest) -> Just (Just a2, rest)
                Nothing -> Nothing
  nParams = maybe 0 nParams
  nScalars = maybe 0 nScalars
