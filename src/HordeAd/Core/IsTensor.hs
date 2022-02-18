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
    DeltaScalar, DeltaVector, DeltaMatrix
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

bindScalarInState :: DeltaScalar r -> DeltaState r -> (DeltaState r, DeltaId r)
{-# INLINE bindScalarInState #-}
bindScalarInState u' st =
  let dId@(DeltaId i) = deltaCounter0 st
  in ( st { deltaCounter0 = DeltaId $ succ i
          , deltaBindings = DScalar dId u' : deltaBindings st
          }
     , dId )

instance IsTensor Double where
  type DeltaExpression Double = DeltaScalar Double
  zeroD = ZeroScalar
  scaleD = ScaleScalar
  addD = AddScalar
  varD = VarScalar
  type ScalarOfTensor Double = Double
  {-# INLINE bindInState #-}
  bindInState = bindScalarInState

instance IsTensor Float where
  type DeltaExpression Float = DeltaScalar Float
  zeroD = ZeroScalar
  scaleD = ScaleScalar
  addD = AddScalar
  varD = VarScalar
  type ScalarOfTensor Float = Float
  {-# INLINE bindInState #-}
  bindInState = bindScalarInState

instance IsTensor (Vector r) where
  type DeltaExpression (Vector r) = DeltaVector r
  zeroD = ZeroVector
  scaleD = ScaleVector
  addD = AddVector
  varD = VarVector
  type ScalarOfTensor (Vector r) = r
  {-# INLINE bindInState #-}
  bindInState u' st =
    let dId@(DeltaId i) = deltaCounter1 st
    in ( st { deltaCounter1 = DeltaId $ succ i
            , deltaBindings = DVector dId u' : deltaBindings st
            }
       , dId )

instance IsTensor (Matrix r) where
  type DeltaExpression (Matrix r) = DeltaMatrix r
  zeroD = ZeroMatrix
  scaleD = ScaleMatrix
  addD = AddMatrix
  varD = VarMatrix
  type ScalarOfTensor (Matrix r) = r
  {-# INLINE bindInState #-}
  bindInState u' st =
    let dId@(DeltaId i) = deltaCounter2 st
    in ( st { deltaCounter2 = DeltaId $ succ i
            , deltaBindings = DMatrix dId u' : deltaBindings st
            }
       , dId )

-- | A shorthand for a useful set of constraints.
type IsTensorWithScalar a r = (IsTensor a, ScalarOfTensor a ~ r)

-- | A mega-shorthand for a bundle of connected type constraints.
type IsScalar r = ( IsTensorWithScalar r r, DeltaExpression r ~ DeltaScalar r
                  , Numeric r, Num (Vector r), Num (Matrix r) )
