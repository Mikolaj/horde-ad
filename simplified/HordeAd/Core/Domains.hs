{-# LANGUAGE UndecidableInstances #-}
-- | A general representation of the domains of objective functions
-- that become the codomains of the gradient functions.
module HordeAd.Core.Domains
  ( DynamicTensor(..)
  , DomainsCollection(..)
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V

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
