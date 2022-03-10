{-# LANGUAGE ConstraintKinds, FlexibleInstances, GeneralizedNewtypeDeriving,
             TypeFamilyDependencies #-}
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
module HordeAd.Core.HasDual
  ( IsScalar, HasDualWithScalar
  , HasDual(DualOf, zeroD, scaleD, addD, varD, bindInState)
  , Forward(..)
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)

import HordeAd.Core.Delta

-- | Each shape of a containers of parameters ('tensor') has its own
-- collection of vector space-like constructors with which the sparse
-- vector expression (`delta expressions`) are built.
class HasDual a where
  type DualOf a = result | result -> a
  zeroD :: DualOf a
  scaleD :: a -> DualOf a -> DualOf a
  addD :: DualOf a -> DualOf a -> DualOf a
  varD :: DeltaId a -> DualOf a
  type ScalarOf a
  bindInState :: DualOf a
              -> DeltaState (ScalarOf a)
              -> (DeltaState (ScalarOf a), DeltaId a)

instance HasDual Double where
  type DualOf Double = Delta0 Double
  zeroD = Zero0
  scaleD = Scale0
  addD = Add0
  varD = Var0
  type ScalarOf Double = Double
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasDual Float where
  type DualOf Float = Delta0 Float
  zeroD = Zero0
  scaleD = Scale0
  addD = Add0
  varD = Var0
  type ScalarOf Float = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasDual (Vector r) where
  type DualOf (Vector r) = Delta1 r
  zeroD = Zero1
  scaleD = Scale1
  addD = Add1
  varD = Var1
  type ScalarOf (Vector r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance HasDual (Matrix r) where
  type DualOf (Matrix r) = Delta2 r
  zeroD = Zero2
  scaleD = Scale2
  addD = Add2
  varD = Var2
  type ScalarOf (Matrix r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance HasDual (OT.Array r) where
  type DualOf (OT.Array r) = DeltaX r
  zeroD = ZeroX
  scaleD = ScaleX
  addD = AddX
  varD = VarX
  type ScalarOf (OT.Array r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance OS.Shape sh => HasDual (OS.Array sh r) where
  type DualOf (OS.Array sh r) = DeltaS sh r
  zeroD = ZeroS
  scaleD = ScaleS
  addD = AddS
  varD = VarS
  type ScalarOf (OS.Array sh r) = r
  {-# INLINE bindInState #-}
  bindInState u' st = let (st2, did) = bindInStateX (FromSX u') st
                      in (st2, covertDeltaId did)

-- | A shorthand for a useful set of constraints.
type HasDualWithScalar a r = (HasDual a, ScalarOf a ~ r)

-- | A mega-shorthand for a bundle of connected type constraints.
type IsScalar r = ( HasDualWithScalar r r, DualOf r ~ Delta0 r
                  , Numeric r, Num (Vector r), Num (Matrix r) )


-- * Alternative instances: forward derivatives computed on the spot

newtype Forward a = Forward a
  deriving Num

instance HasDual (Forward Double) where
  type DualOf (Forward Double) = Double
  zeroD = 0
  scaleD (Forward k) d = k * d
  addD d e = d + e
  varD = undefined  -- no variables are needed, because no blowup possible
  type ScalarOf (Forward Double) = Double
  {-# INLINE bindInState #-}
  bindInState = undefined  -- no variables, so no bindings

{-
instance HasDual Float where
  type DualOf Float = Delta0 Float
  zeroD = Zero0
  scaleD = Scale0
  addD = Add0
  varD = Var0
  type ScalarOf Float = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasDual (Vector r) where
  type DualOf (Vector r) = Delta1 r
  zeroD = Zero1
  scaleD = Scale1
  addD = Add1
  varD = Var1
  type ScalarOf (Vector r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance HasDual (Matrix r) where
  type DualOf (Matrix r) = Delta2 r
  zeroD = Zero2
  scaleD = Scale2
  addD = Add2
  varD = Var2
  type ScalarOf (Matrix r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance HasDual (OT.Array r) where
  type DualOf (OT.Array r) = DeltaX r
  zeroD = ZeroX
  scaleD = ScaleX
  addD = AddX
  varD = VarX
  type ScalarOf (OT.Array r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance OS.Shape sh => HasDual (OS.Array sh r) where
  type DualOf (OS.Array sh r) = DeltaS sh r
  zeroD = ZeroS
  scaleD = ScaleS
  addD = AddS
  varD = VarS
  type ScalarOf (OS.Array sh r) = r
  {-# INLINE bindInState #-}
  bindInState u' st = let (st2, did) = bindInStateX (FromSX u') st
                      in (st2, covertDeltaId did)
-}
