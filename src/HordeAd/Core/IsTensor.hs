{-# LANGUAGE ConstraintKinds, TypeFamilyDependencies #-}
-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function. Neel Krishnaswami calls that "sparse vector expressions",
-- and indeed even in the simplest case of a function defined on scalars only,
-- the non-empty portion of the codomain of the evaluation function is a vector,
-- because the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- The 'sparcity' is less obvious when the domain of the function consists
-- of multiple vectors and matrices and when the expressions themselves
-- contain vectors and matrices. However, a single tiny delta
-- expression (e.g., a sum of two variables) may denote a vector of matrices.
-- Even a delta expression containing a big matrix denotes something much
-- bigger: a whole vector of such matrices (and vectors and scalars).
--
-- The algebraic structure here is an extension of vector space.
-- The crucial extra constructor for variables is used both to represent
-- sharing in order to avoid exponential blowup and to replace the one-hot
-- access to parameters with something cheaper and more uniform.
-- A lot of the remaining additional structure is for introducing
-- and reducing dimensions.
module HordeAd.Core.IsTensor
  ( IsScalar, IsTensorWithScalar
  , IsTensor(DeltaExpression, zeroD, scaleD, addD, varD, bindInState)
  , -- only needed, because GHC doesn't specialize fully without them
    -- in "HordeAd.Core.PairOfVectors"
    Delta0, Delta1, Delta2
  ) where

import Prelude

import Numeric.LinearAlgebra (Matrix, Numeric, Vector)

import HordeAd.Core.Delta

-- | Each shape of a containers of parameters ('tensor') has its own
-- collection of vector space-like constructors with which the sparse
-- vector expression (`delta expressions`) are built.
class IsTensor a where
  type DeltaExpression a = result | result -> a
  zeroD :: DeltaExpression a
  scaleD :: a -> DeltaExpression a -> DeltaExpression a
  addD :: DeltaExpression a -> DeltaExpression a -> DeltaExpression a
  varD :: DeltaId a -> DeltaExpression a
  type ScalarOfTensor a
  bindInState :: DeltaExpression a
              -> DeltaState (ScalarOfTensor a)
              -> (DeltaState (ScalarOfTensor a), DeltaId a)

instance IsTensor Double where
  type DeltaExpression Double = Delta0 Double
  zeroD = Zero0
  scaleD = Scale0
  addD = Add0
  varD = Var0
  type ScalarOfTensor Double = Double
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance IsTensor Float where
  type DeltaExpression Float = Delta0 Float
  zeroD = Zero0
  scaleD = Scale0
  addD = Add0
  varD = Var0
  type ScalarOfTensor Float = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance IsTensor (Vector r) where
  type DeltaExpression (Vector r) = Delta1 r
  zeroD = Zero1
  scaleD = Scale1
  addD = Add1
  varD = Var1
  type ScalarOfTensor (Vector r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance IsTensor (Matrix r) where
  type DeltaExpression (Matrix r) = Delta2 r
  zeroD = Zero2
  scaleD = Scale2
  addD = Add2
  varD = Var2
  type ScalarOfTensor (Matrix r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState2

-- | A shorthand for a useful set of constraints.
type IsTensorWithScalar a r = (IsTensor a, ScalarOfTensor a ~ r)

-- | A mega-shorthand for a bundle of connected type constraints.
type IsScalar r = ( IsTensorWithScalar r r, DeltaExpression r ~ Delta0 r
                  , Numeric r, Num (Vector r), Num (Matrix r) )
