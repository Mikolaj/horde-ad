-- | Operations on the product (heterogeneous list) object for tensors.
-- In particular, adaptors for working with such types of collections of tensors
-- that are isormorphic to products.
--
-- This is used as a representation of the domains of objective functions
-- that become the codomains of the reverse derivative functions
-- and also to hangle multiple arguments and results of fold-like operations.
module HordeAd.Core.Adaptor
  ( AdaptableHVector(..), parseHVector, ForgetShape(..), RandomHVector(..)
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

import HordeAd.Core.HVector
import HordeAd.Core.Types

-- * Adaptor classes

-- Inspired by adaptors from @tomjaguarpaw's branch.
class AdaptableHVector (ranked :: RankedTensorType) vals where
  type Value vals  -- ^ a helper type, with the same general shape,
                   -- but possibly more concrete, e.g., arrays instead of terms
  toHVector :: vals -> HVector ranked
    -- ^ represent a value of the domain of objective function
    -- in a canonical, much less typed way common to all possible types
  fromHVector :: Value vals -> HVector ranked
              -> Maybe (vals, HVector ranked)
    -- ^ recovers a value of the domain of objective function
    -- from its canonical representation, using the general shape
    -- recorded in a value of a more concrete type; the remainder
    -- may be used in a different recursive call working on the same data

-- | Recovers a value of the domain of objective function and asserts
-- there is no remainder. This is the main call of the recursive
-- procedure where @fromHVector@ calls itself for sub-values.
parseHVector
  :: AdaptableHVector ranked vals
  => Value vals -> HVector ranked -> vals
parseHVector aInit hVector =
  case fromHVector aInit hVector of
    Just (vals, rest) -> assert (V.null rest) vals
    Nothing -> error "parseHVector: Nothing"

-- | A helper class for for converting all tensors inside a type
-- from shaped to ranked.
class ForgetShape vals where
  type NoShape vals
  forgetShape :: vals -> NoShape vals

-- | A helper class for randomly generating initial parameters.
class RandomHVector vals where
  randomVals :: forall g. RandomGen g
             => Double -> g -> (vals, g)


-- * Basic Adaptor class instances

{- This is temporarily moved to TensorADVal in order to specialize manually
instance AdaptableHVector ranked a
         => AdaptableHVector ranked [a] where
  {-# SPECIALIZE instance
      (KnownNat n, AdaptableHVector OD.Array (OR.Array n Double))
      => AdaptableHVector OD.Array
                          [OR.Array n Double] #-}
  {-# SPECIALIZE instance
      ( KnownNat n, AstSpan s
      , AdaptableHVector (AstDynamic s)
                         (AstRanked s Double n) )
      => AdaptableHVector (AstDynamic s)
                          [AstRanked s Double n] #-}
  -- TODO: Specialize to ADVal, too, which requires resolving a module dep loop
  type Value [a] = [Value a]
  toHVector = V.concat . map toHVector
  fromHVector lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromHVector aInit restAcc of
            Just (a, rest) -> (a : lAcc, rest)
            Nothing -> error "fromHVector [a]"
        (l, !restAll) = foldl' f ([], source) lInit
        !rl = reverse l
    in Just (rl, restAll)
    -- is the following as performant? benchmark:
    -- > fromHVector lInit source =
    -- >   let f = swap . flip fromHVector
    -- >   in swap $ mapAccumL f source lInit
-}

instance ForgetShape a
         => ForgetShape [a] where
  type NoShape [a] = [NoShape a]
  forgetShape = map forgetShape

instance AdaptableHVector ranked a
         => AdaptableHVector ranked (Data.Vector.Vector a) where
  type Value (Data.Vector.Vector a) = Data.Vector.Vector (Value a)
  toHVector = V.concatMap toHVector
  fromHVector lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromHVector aInit restAcc of
            Just (a, rest) -> (V.snoc lAcc a, rest)
              -- this snoc, if the vector is long, is very costly;
              -- a solution might be to define Value to be a list
            Nothing -> error "fromHVector [a]"
        (!l, !restAll) = V.foldl' f (V.empty, source) lInit
    in Just (l, restAll)

instance ForgetShape a
         => ForgetShape (Data.Vector.Vector a) where
  type NoShape (Data.Vector.Vector a) = Data.Vector.Vector (NoShape a)
  forgetShape = V.map forgetShape

instance ( AdaptableHVector ranked a
         , AdaptableHVector ranked b ) => AdaptableHVector ranked (a, b) where
  type Value (a, b) = (Value a, Value b)
  toHVector (a, b) =
    let a1 = toHVector a
        b1 = toHVector b
    in V.concat [a1, b1]
  fromHVector (aInit, bInit) source = do
    (a, aRest) <- fromHVector aInit source
    (b, bRest) <- fromHVector bInit aRest
    return ((a, b), bRest)

instance ( ForgetShape a
         , ForgetShape b ) => ForgetShape (a, b) where
  type NoShape (a, b) = (NoShape a, NoShape b)
  forgetShape (a, b) = (forgetShape a, forgetShape b)

instance ( RandomHVector a
         , RandomHVector b ) => RandomHVector (a, b) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
    in ((v1, v2), g2)

instance ( AdaptableHVector ranked a
         , AdaptableHVector ranked b
         , AdaptableHVector ranked c )
         => AdaptableHVector ranked (a, b, c) where
  type Value (a, b, c) = (Value a, Value b, Value c)
  toHVector (a, b, c) =
    let a1 = toHVector a
        b1 = toHVector b
        c1 = toHVector c
    in V.concat [a1, b1, c1]
  fromHVector (aInit, bInit, cInit) source = do
    (a, aRest) <- fromHVector aInit source
    (b, bRest) <- fromHVector bInit aRest
    (c, cRest) <- fromHVector cInit bRest
    return ((a, b, c), cRest)

instance ( ForgetShape a
         , ForgetShape b
         , ForgetShape c ) => ForgetShape (a, b, c) where
  type NoShape (a, b, c) = (NoShape a, NoShape b, NoShape c)
  forgetShape (a, b, c) = (forgetShape a, forgetShape b, forgetShape c)

instance ( RandomHVector a
         , RandomHVector b
         , RandomHVector c ) => RandomHVector (a, b, c) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
    in ((v1, v2, v3), g3)

instance ( AdaptableHVector ranked a
         , AdaptableHVector ranked b
         , AdaptableHVector ranked c
         , AdaptableHVector ranked d )
         => AdaptableHVector ranked (a, b, c, d) where
  type Value (a, b, c, d) = (Value a, Value b, Value c, Value d)
  toHVector (a, b, c, d) =
    let a1 = toHVector a
        b1 = toHVector b
        c1 = toHVector c
        d1 = toHVector d
    in V.concat [a1, b1, c1, d1]
  fromHVector (aInit, bInit, cInit, dInit) source = do
    (a, aRest) <- fromHVector aInit source
    (b, bRest) <- fromHVector bInit aRest
    (c, cRest) <- fromHVector cInit bRest
    (d, dRest) <- fromHVector dInit cRest
    return ((a, b, c, d), dRest)

instance ( ForgetShape a
         , ForgetShape b
         , ForgetShape c
         , ForgetShape d ) => ForgetShape (a, b, c, d) where
  type NoShape (a, b, c, d) =
    (NoShape a, NoShape b, NoShape c, NoShape d)
  forgetShape (a, b, c, d) =
    (forgetShape a, forgetShape b, forgetShape c, forgetShape d)

instance ( RandomHVector a
         , RandomHVector b
         , RandomHVector c
         , RandomHVector d ) => RandomHVector (a, b, c, d) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
        (v4, g4) = randomVals range g3
    in ((v1, v2, v3, v4), g4)

instance ( AdaptableHVector ranked a
         , AdaptableHVector ranked b
         , AdaptableHVector ranked c
         , AdaptableHVector ranked d
         , AdaptableHVector ranked e )
         => AdaptableHVector ranked (a, b, c, d, e) where
  type Value (a, b, c, d, e) = (Value a, Value b, Value c, Value d, Value e)
  toHVector (a, b, c, d, e) =
    let a1 = toHVector a
        b1 = toHVector b
        c1 = toHVector c
        d1 = toHVector d
        e1 = toHVector e
    in V.concat [a1, b1, c1, d1, e1]
  fromHVector (aInit, bInit, cInit, dInit, eInit) source = do
    (a, aRest) <- fromHVector aInit source
    (b, bRest) <- fromHVector bInit aRest
    (c, cRest) <- fromHVector cInit bRest
    (d, dRest) <- fromHVector dInit cRest
    (e, eRest) <- fromHVector eInit dRest
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

instance ( RandomHVector a
         , RandomHVector b
         , RandomHVector c
         , RandomHVector d
         , RandomHVector e ) => RandomHVector (a, b, c, d, e) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
        (v4, g4) = randomVals range g3
        (v5, g5) = randomVals range g4
    in ((v1, v2, v3, v4, v5), g5)

instance ( AdaptableHVector ranked a, AdaptableHVector ranked b )
         => AdaptableHVector ranked (Either a b) where
  type Value (Either a b) = Either (Value a) (Value b)
  toHVector e = case e of
    Left a -> toHVector a
    Right b -> toHVector b
  fromHVector eInit source = case eInit of
    Left a -> case fromHVector a source of
                Just (a2, rest) -> Just (Left a2, rest)
                Nothing -> Nothing
    Right b -> case fromHVector b source of
                 Just (b2, rest) -> Just (Right b2, rest)
                 Nothing -> Nothing

instance ( ForgetShape a
         , ForgetShape b ) => ForgetShape (Either a b) where
  type NoShape (Either a b) = Either (NoShape a) (NoShape b)
  forgetShape e = case e of
    Left a -> Left $ forgetShape a
    Right b -> Right $ forgetShape b

instance AdaptableHVector ranked a
         => AdaptableHVector ranked (Maybe a) where
  type Value (Maybe a) = Maybe (Value a)
  toHVector e = case e of
    Nothing -> V.concat []
    Just a -> toHVector a
  fromHVector eInit source = case eInit of
    Nothing -> Just (Nothing, source)
    Just a -> case fromHVector a source of
                Just (a2, rest) -> Just (Just a2, rest)
                Nothing -> Nothing

instance ForgetShape a
         => ForgetShape (Maybe a) where
  type NoShape (Maybe a) = Maybe (NoShape a)
  forgetShape = fmap forgetShape
