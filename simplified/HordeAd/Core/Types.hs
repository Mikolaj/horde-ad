{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | Some fundamental kinds, type families and types.
module HordeAd.Core.Types
  ( TensorKind, RankedTensorKind, ShapedTensorKind
  , GoodScalar, DynamicExists(..), Domains, DomainsOD, sizeDomainsOD
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import           Data.Kind (Type)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (Nat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Type.Reflection (Typeable)

import HordeAd.Core.TensorOps

type TensorKind k = Type -> k -> Type

type RankedTensorKind = TensorKind Nat

type ShapedTensorKind = TensorKind [Nat]

type GoodScalarConstraint r =
  (Show r, Numeric r, RealFloat r, Floating (Vector r), RowSum r, Typeable r)

-- Attempted optimization via storing one pointer to a class dictionary
-- in existential datatypes instead of six pointers. No effect, strangely.
class GoodScalarConstraint r => GoodScalar r
instance GoodScalarConstraint r => GoodScalar r

data DynamicExists :: (Type -> Type) -> Type where
  DynamicExists :: forall r dynamic. GoodScalar r
                => dynamic r -> DynamicExists dynamic
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
