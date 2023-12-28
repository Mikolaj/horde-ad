-- | A general representation of the domains of objective functions
-- that become the codomains of the reverse derivative functions.
module HordeAd.Core.Adaptor
  ( AdaptableDomains(..), parseDomains, ForgetShape(..), RandomDomains(..)
  ) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           System.Random

-- import qualified Data.Array.RankedS as OR
-- import           Data.List (foldl')
-- import HordeAd.Core.Ast
-- import           GHC.TypeLits (KnownNat)

import HordeAd.Core.Types

-- * Adaptor classes

-- Inspired by adaptors from @tomjaguarpaw's branch.
class AdaptableDomains (ranked :: RankedTensorType) vals where
  type Value vals  -- ^ a helper type, with the same general shape,
                   -- but possibly more concrete, e.g., arrays instead of terms
  toDomains :: vals -> Domains ranked
    -- ^ represent a value of the domain of objective function
    -- in a canonical, much less typed way common to all possible types
  fromDomains :: Value vals -> Domains ranked
              -> Maybe (vals, Domains ranked)
    -- ^ recovers a value of the domain of objective function
    -- from its canonical representation, using the general shape
    -- recorded in a value of a more concrete type; the remainder
    -- may be used in a different recursive call working on the same data

-- | Recovers a value of the domain of objective function and asserts
-- there is no remainder. This is the main call of the recursive
-- procedure where @fromDomains@ calls itself for sub-values.
parseDomains
  :: AdaptableDomains ranked vals
  => Value vals -> Domains ranked -> vals
parseDomains aInit domains =
  case fromDomains aInit domains of
    Just (vals, rest) -> assert (V.null rest) vals
    Nothing -> error "parseDomains: Nothing"

-- | A helper class for for converting all tensors inside a type
-- from shaped to ranked.
class ForgetShape vals where
  type NoShape vals
  forgetShape :: vals -> NoShape vals

-- | A helper class for randomly generating initial parameters.
class RandomDomains vals where
  randomVals :: forall g. RandomGen g
             => Double -> g -> (vals, g)


-- * Basic Adaptor class instances

{- This is temporarily moved to TensorADVal in order to specialize manually
instance AdaptableDomains ranked a
         => AdaptableDomains ranked [a] where
  {-# SPECIALIZE instance
      (KnownNat n, AdaptableDomains OD.Array (OR.Array n Double))
      => AdaptableDomains OD.Array
                          [OR.Array n Double] #-}
  {-# SPECIALIZE instance
      ( KnownNat n, AstSpan s
      , AdaptableDomains (AstDynamic s)
                         (AstRanked s Double n) )
      => AdaptableDomains (AstDynamic s)
                          [AstRanked s Double n] #-}
  -- TODO: Specialize to ADVal, too, which requires resolving a module dep loop
  type Value [a] = [Value a]
  toDomains = V.concat . map toDomains
  fromDomains lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromDomains aInit restAcc of
            Just (a, rest) -> (a : lAcc, rest)
            Nothing -> error "fromDomains [a]"
        (l, !restAll) = foldl' f ([], source) lInit
        !rl = reverse l
    in Just (rl, restAll)
    -- is the following as performant? benchmark:
    -- > fromDomains lInit source =
    -- >   let f = swap . flip fromDomains
    -- >   in swap $ mapAccumL f source lInit
-}

instance ForgetShape a
         => ForgetShape [a] where
  type NoShape [a] = [NoShape a]
  forgetShape = map forgetShape

instance AdaptableDomains ranked a
         => AdaptableDomains ranked (Data.Vector.Vector a) where
  type Value (Data.Vector.Vector a) = Data.Vector.Vector (Value a)
  toDomains = V.concatMap toDomains
  fromDomains lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromDomains aInit restAcc of
            Just (a, rest) -> (V.snoc lAcc a, rest)
              -- this snoc, if the vector is long, is very costly;
              -- a solution might be to define Value to be a list
            Nothing -> error "fromDomains [a]"
        (!l, !restAll) = V.foldl' f (V.empty, source) lInit
    in Just (l, restAll)

instance ForgetShape a
         => ForgetShape (Data.Vector.Vector a) where
  type NoShape (Data.Vector.Vector a) = Data.Vector.Vector (NoShape a)
  forgetShape = V.map forgetShape

instance ( AdaptableDomains ranked a
         , AdaptableDomains ranked b ) => AdaptableDomains ranked (a, b) where
  type Value (a, b) = (Value a, Value b)
  toDomains (a, b) =
    let a1 = toDomains a
        b1 = toDomains b
    in V.concat [a1, b1]
  fromDomains (aInit, bInit) source = do
    (a, aRest) <- fromDomains aInit source
    (b, bRest) <- fromDomains bInit aRest
    return ((a, b), bRest)

instance ( ForgetShape a
         , ForgetShape b ) => ForgetShape (a, b) where
  type NoShape (a, b) = (NoShape a, NoShape b)
  forgetShape (a, b) = (forgetShape a, forgetShape b)

instance ( RandomDomains a
         , RandomDomains b ) => RandomDomains (a, b) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
    in ((v1, v2), g2)

instance ( AdaptableDomains ranked a
         , AdaptableDomains ranked b
         , AdaptableDomains ranked c )
         => AdaptableDomains ranked (a, b, c) where
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

instance ( ForgetShape a
         , ForgetShape b
         , ForgetShape c ) => ForgetShape (a, b, c) where
  type NoShape (a, b, c) = (NoShape a, NoShape b, NoShape c)
  forgetShape (a, b, c) = (forgetShape a, forgetShape b, forgetShape c)

instance ( RandomDomains a
         , RandomDomains b
         , RandomDomains c ) => RandomDomains (a, b, c) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
    in ((v1, v2, v3), g3)

instance ( AdaptableDomains ranked a
         , AdaptableDomains ranked b
         , AdaptableDomains ranked c
         , AdaptableDomains ranked d )
         => AdaptableDomains ranked (a, b, c, d) where
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

instance ( ForgetShape a
         , ForgetShape b
         , ForgetShape c
         , ForgetShape d ) => ForgetShape (a, b, c, d) where
  type NoShape (a, b, c, d) =
    (NoShape a, NoShape b, NoShape c, NoShape d)
  forgetShape (a, b, c, d) =
    (forgetShape a, forgetShape b, forgetShape c, forgetShape d)

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

instance ( AdaptableDomains ranked a
         , AdaptableDomains ranked b
         , AdaptableDomains ranked c
         , AdaptableDomains ranked d
         , AdaptableDomains ranked e )
         => AdaptableDomains ranked (a, b, c, d, e) where
  type Value (a, b, c, d, e) = (Value a, Value b, Value c, Value d, Value e)
  toDomains (a, b, c, d, e) =
    let a1 = toDomains a
        b1 = toDomains b
        c1 = toDomains c
        d1 = toDomains d
        e1 = toDomains e
    in V.concat [a1, b1, c1, d1, e1]
  fromDomains (aInit, bInit, cInit, dInit, eInit) source = do
    (a, aRest) <- fromDomains aInit source
    (b, bRest) <- fromDomains bInit aRest
    (c, cRest) <- fromDomains cInit bRest
    (d, dRest) <- fromDomains dInit cRest
    (e, eRest) <- fromDomains eInit dRest
    return ((a, b, c, d, e), eRest)

instance ( ForgetShape a
         , ForgetShape b
         , ForgetShape c
         , ForgetShape d
         , ForgetShape e ) => ForgetShape (a, b, c, d, e) where
  type NoShape (a, b, c, d, e) =
    (NoShape a, NoShape b, NoShape c, NoShape d, NoShape e)
  forgetShape (a, b, c, d, e) =
    (forgetShape a, forgetShape b, forgetShape c, forgetShape d, forgetShape e)

instance ( RandomDomains a
         , RandomDomains b
         , RandomDomains c
         , RandomDomains d
         , RandomDomains e ) => RandomDomains (a, b, c, d, e) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
        (v4, g4) = randomVals range g3
        (v5, g5) = randomVals range g4
    in ((v1, v2, v3, v4, v5), g5)

instance ( AdaptableDomains ranked a, AdaptableDomains ranked b )
         => AdaptableDomains ranked (Either a b) where
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

instance ( ForgetShape a
         , ForgetShape b ) => ForgetShape (Either a b) where
  type NoShape (Either a b) = Either (NoShape a) (NoShape b)
  forgetShape e = case e of
    Left a -> Left $ forgetShape a
    Right b -> Right $ forgetShape b

instance AdaptableDomains ranked a
         => AdaptableDomains ranked (Maybe a) where
  type Value (Maybe a) = Maybe (Value a)
  toDomains e = case e of
    Nothing -> V.concat []
    Just a -> toDomains a
  fromDomains eInit source = case eInit of
    Nothing -> Just (Nothing, source)
    Just a -> case fromDomains a source of
                Just (a2, rest) -> Just (Just a2, rest)
                Nothing -> Nothing

instance ForgetShape a
         => ForgetShape (Maybe a) where
  type NoShape (Maybe a) = Maybe (NoShape a)
  forgetShape = fmap forgetShape
