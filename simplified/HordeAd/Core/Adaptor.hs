{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | A general representation of the domains of objective functions
-- that become the codomains of the gradient functions.
module HordeAd.Core.Adaptor
  ( GoodScalar, DynamicExists(..), Domains, DomainsOD, sizeDomainsOD
  , AdaptableDomains(..), parseDomains, RandomDomains(..)
  ) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OD
import           Data.Kind (Type)
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.Random
import           Type.Reflection (Typeable)

import HordeAd.Core.TensorOps

-- * Basic definitions

type GoodScalarConstraint r =
  (Show r, Numeric r, RealFloat r, Floating (Vector r), RowSum r, Typeable r)

-- Attempted optimization via storing one pointer to a class dictionary
-- in existential datatypes instead of six pointers. No effect, strangely.
class GoodScalarConstraint r => GoodScalar r
instance GoodScalarConstraint r => GoodScalar r

data DynamicExists (dynamic :: Type -> Type) =
  forall r. GoodScalar r => DynamicExists (dynamic r)
deriving instance (forall r. GoodScalar r => Show (dynamic r))
                  => Show (DynamicExists dynamic)

-- When r is Ast, this is used for domains composed of variables only,
-- to adapt them into more complex types and back again. This is not used
-- for vectors of large terms, since they'd share values, so we'd need
-- AstDomainsLet, but these would make adapting the vector costly.
-- DomainsOf is used for that and the only reasons DomainsOf exists
-- is to prevent mixing up the two (and complicating the definition
-- below with errors in the AstDomainsLet case).
type Domains dynamic = Data.Vector.Vector (DynamicExists dynamic)

type DomainsOD = Domains OD.Array

sizeDomainsOD :: DomainsOD -> Int
sizeDomainsOD d = let f (DynamicExists t) = OD.size t
                  in V.sum (V.map f d)

-- * Adaptor classes

-- Inspired by adaptors from @tomjaguarpaw's branch.
class AdaptableDomains (dynamic :: Type -> Type) vals where
  type Value vals
  toDomains :: vals -> Domains dynamic
  fromDomains :: Value vals -> Domains dynamic
              -> Maybe (vals, Domains dynamic)

class RandomDomains vals where
  randomVals :: forall g. RandomGen g
             => Double -> g -> (vals, g)
  toValue :: vals -> Value vals

parseDomains
  :: AdaptableDomains dynamic vals
  => Value vals -> Domains dynamic -> vals
parseDomains aInit domains =
  case fromDomains aInit domains of
    Just (vals, rest) -> assert (V.null rest) vals
    Nothing -> error "parseDomains: Nothing"


-- * Basic Adaptor class instances

instance AdaptableDomains dynamic a
         => AdaptableDomains dynamic [a] where
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

instance RandomDomains a
         => RandomDomains [a] where
  randomVals = undefined  -- TODO: split RandomDomains?
  toValue as = map toValue as

instance ( AdaptableDomains dynamic a
         , AdaptableDomains dynamic b ) => AdaptableDomains dynamic (a, b) where
  type Value (a, b) = (Value a, Value b)
  toDomains (a, b) =
    let a1 = toDomains a
        b1 = toDomains b
    in V.concat [a1, b1]
  fromDomains (aInit, bInit) source = do
    (a, aRest) <- fromDomains aInit source
    (b, bRest) <- fromDomains bInit aRest
    return ((a, b), bRest)

instance ( RandomDomains a
         , RandomDomains b ) => RandomDomains (a, b) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
    in ((v1, v2), g2)
  toValue (a, b) = (toValue a, toValue b)

instance ( AdaptableDomains dynamic a
         , AdaptableDomains dynamic b
         , AdaptableDomains dynamic c ) => AdaptableDomains dynamic (a, b, c) where
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

instance ( RandomDomains a
         , RandomDomains b
         , RandomDomains c ) => RandomDomains (a, b, c) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
    in ((v1, v2, v3), g3)
  toValue (a, b, c) = (toValue a, toValue b, toValue c)

instance ( AdaptableDomains dynamic a
         , AdaptableDomains dynamic b
         , AdaptableDomains dynamic c
         , AdaptableDomains dynamic d ) => AdaptableDomains dynamic (a, b, c, d) where
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

instance ( RandomDomains a
         , RandomDomains b
         , RandomDomains c
         , RandomDomains d ) => RandomDomains (a, b, c, d) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
        (v4, g4) = randomVals range g3
    in ((v1, v2, v3, v4), g4)
  toValue (a, b, c, d) = (toValue a, toValue b, toValue c, toValue d)

instance ( AdaptableDomains dynamic a, AdaptableDomains dynamic b )
         => AdaptableDomains dynamic (Either a b) where
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

instance AdaptableDomains dynamic a
         => AdaptableDomains dynamic (Maybe a) where
  type Value (Maybe a) = Maybe (Value a)
  toDomains e = case e of
    Nothing -> V.concat []
    Just a -> toDomains a
  fromDomains eInit source = case eInit of
    Nothing -> Just (Nothing, source)
    Just a -> case fromDomains a source of
                Just (a2, rest) -> Just (Just a2, rest)
                Nothing -> Nothing
