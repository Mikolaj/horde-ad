{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             GeneralizedNewtypeDeriving, TypeFamilyDependencies #-}
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
  , HasDual(DualOf, dzero, dscale, dadd, dvar, bindInState)
  , HasRanks(..)
  , Forward(..)
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Data.Coerce (coerce)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Core.Delta

-- | A shorthand for a useful set of constraints.
type HasDualWithScalar a r = (HasDual a, ScalarOf a ~ r)

-- | A mega-shorthand for a bundle of connected type constraints.
type IsScalar r = ( HasDualWithScalar r r, HasRanks r
                  , HasDual  (Vector r), HasDual (Matrix r)
                  , ScalarOf (Vector r) ~ r, ScalarOf (Matrix r) ~ r
                  , Numeric r, Num (Vector r), Num (Matrix r) )

-- | Each shape of a containers of parameters ('tensor') has its own
-- collection of vector space-like constructors with which the sparse
-- vector expression (`delta expressions`) are built.
class HasDual a where
  type DualOf a = result | result -> a
  dzero :: DualOf a
  dscale :: a -> DualOf a -> DualOf a
  dadd :: DualOf a -> DualOf a -> DualOf a
  dvar :: DeltaId a -> DualOf a
  type ScalarOf a
  bindInState :: DualOf a
              -> DeltaState (ScalarOf a)
              -> (DeltaState (ScalarOf a), DeltaId a)

class HasRanks r where
  dsumElements0 :: DualOf (Vector r) -> Int -> DualOf r
  dindex0 :: DualOf (Vector r) -> Int -> Int -> DualOf r
  ddot0 :: Vector r -> DualOf (Vector r) -> DualOf r
  dfromX0 :: DualOf (OT.Array r) -> DualOf r
  dfromS0 :: DualOf (OS.Array '[] r) -> DualOf r

  dseq1 :: Data.Vector.Vector (DualOf r) -> DualOf (Vector r)
  dkonst1 :: DualOf r -> Int -> DualOf (Vector r)
  dappend1 :: DualOf (Vector r) -> Int -> DualOf (Vector r) -> DualOf (Vector r)
  dslice1 :: Int -> Int -> DualOf (Vector r) -> Int -> DualOf (Vector r)
  dsumRows1 :: DualOf (Matrix r) -> Int -> DualOf (Vector r)
  dsumColumns1 :: DualOf (Matrix r) -> Int -> DualOf (Vector r)
  dm_VD1 :: Matrix r -> DualOf (Vector r) -> DualOf (Vector r)
  dmD_V1 :: DualOf (Matrix r) -> Vector r -> DualOf (Vector r)
  dfromX1 :: DualOf (OT.Array r) -> DualOf (Vector r)
  dfromS1 :: DualOf (OS.Array '[len] r) -> DualOf (Vector r)

  dfromRows2 :: Data.Vector.Vector (DualOf (Vector r)) -> DualOf (Matrix r)
  dfromColumns2 :: Data.Vector.Vector (DualOf (Vector r)) -> DualOf (Matrix r)
  dtranspose2 :: DualOf (Matrix r) -> DualOf (Matrix r)
  dm_MD2 :: Matrix r -> DualOf (Matrix r) -> DualOf (Matrix r)
  dmD_M2 :: DualOf (Matrix r) -> Matrix r -> DualOf (Matrix r)
  drowAppend2 :: DualOf (Matrix r) -> Int -> DualOf (Matrix r)
              -> DualOf (Matrix r)
  dcolumnAppend2 :: DualOf (Matrix r) -> Int -> DualOf (Matrix r)
                 -> DualOf (Matrix r)
  drowSlice2 :: Int -> Int -> DualOf (Matrix r) -> Int -> DualOf (Matrix r)
  dcolumnSlice2 :: Int -> Int -> DualOf (Matrix r) -> Int -> DualOf (Matrix r)
  dasRow2 :: DualOf (Vector r) -> DualOf (Matrix r)
  dasColumn2 :: DualOf (Vector r) -> DualOf (Matrix r)
  dfromX2 :: DualOf (OT.Array r) -> DualOf (Matrix r)
  dfromS2 :: DualOf (OS.Array '[rows, cols] r) -> DualOf (Matrix r)

  -- TODO: tensors

instance HasDual Double where
  type DualOf Double = Delta0 Double
  dzero = Zero0
  dscale = Scale0
  dadd = Add0
  dvar = Var0
  type ScalarOf Double = Double
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasRanks Double where
  dsumElements0 = SumElements0
  dindex0 = Index0
  ddot0 = Dot0
  dfromX0 = FromX0
  dfromS0 = FromS0

instance HasDual Float where
  type DualOf Float = Delta0 Float
  dzero = Zero0
  dscale = Scale0
  dadd = Add0
  dvar = Var0
  type ScalarOf Float = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState0

-- I hate this duplication:
instance HasDual (Vector Double) where
  type DualOf (Vector Double) = Delta1 Double
  dzero = Zero1
  dscale = Scale1
  dadd = Add1
  dvar = Var1
  type ScalarOf (Vector Double) = Double
  {-# INLINE bindInState #-}
  bindInState = bindInState1

-- I hate this duplication with this:
instance HasDual (Vector Float) where
  type DualOf (Vector Float) = Delta1 Float
  dzero = Zero1
  dscale = Scale1
  dadd = Add1
  dvar = Var1
  type ScalarOf (Vector Float) = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance HasDual (Matrix Double) where
  type DualOf (Matrix Double) = Delta2 Double
  dzero = Zero2
  dscale = Scale2
  dadd = Add2
  dvar = Var2
  type ScalarOf (Matrix Double) = Double
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance HasDual (Matrix Float) where
  type DualOf (Matrix Float) = Delta2 Float
  dzero = Zero2
  dscale = Scale2
  dadd = Add2
  dvar = Var2
  type ScalarOf (Matrix Float) = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance HasDual (OT.Array Double) where
  type DualOf (OT.Array Double) = DeltaX Double
  dzero = ZeroX
  dscale = ScaleX
  dadd = AddX
  dvar = VarX
  type ScalarOf (OT.Array Double) = Double
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance HasDual (OT.Array Float) where
  type DualOf (OT.Array Float) = DeltaX Float
  dzero = ZeroX
  dscale = ScaleX
  dadd = AddX
  dvar = VarX
  type ScalarOf (OT.Array Float) = Float
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance OS.Shape sh => HasDual (OS.Array sh Double) where
  type DualOf (OS.Array sh Double) = DeltaS sh Double
  dzero = ZeroS
  dscale = ScaleS
  dadd = AddS
  dvar = VarS
  type ScalarOf (OS.Array sh Double) = Double
  {-# INLINE bindInState #-}
  bindInState u' st = let (st2, did) = bindInStateX (FromSX u') st
                      in (st2, covertDeltaId did)

instance OS.Shape sh => HasDual (OS.Array sh Float) where
  type DualOf (OS.Array sh Float) = DeltaS sh Float
  dzero = ZeroS
  dscale = ScaleS
  dadd = AddS
  dvar = VarS
  type ScalarOf (OS.Array sh Float) = Float
  {-# INLINE bindInState #-}
  bindInState u' st = let (st2, did) = bindInStateX (FromSX u') st
                      in (st2, covertDeltaId did)


-- * Alternative instances: forward derivatives computed on the spot

newtype Forward a = Forward a
  deriving Num

-- I hate this duplication:
instance HasDual (Forward Double) where
  type DualOf (Forward Double) = Double
  dzero = 0
  dscale (Forward k) d = k * d
  dadd d e = d + e
  dvar = undefined  -- no variables are needed, because no blowup possible
  type ScalarOf (Forward Double) = Double
  bindInState = undefined  -- no variables, so no bindings

instance HasRanks (Forward Double) where
  dsumElements0 vd _ = HM.sumElements vd
  dindex0 d ix _ = d V.! ix
  ddot0 vr vd = coerce vr HM.<.> vd
  dfromX0 = OT.unScalar
  dfromS0 = OS.unScalar
  -- TODO: the rest

-- I hate this duplication with this:
instance HasDual (Forward Float) where
  type DualOf (Forward Float) = Float
  dzero = 0
  dscale (Forward k) d = k * d
  dadd d e = d + e
  dvar = undefined
  type ScalarOf (Forward Float) = Float
  bindInState = undefined

instance HasRanks (Forward Float) where
  dsumElements0 vd _ = HM.sumElements vd
  dindex0 d ix _ = d V.! ix
  ddot0 vr vd = coerce vr HM.<.> vd
  dfromX0 = OT.unScalar
  dfromS0 = OS.unScalar
  -- TODO: the rest

instance Num (Vector r) => HasDual (Vector (Forward r)) where
  type DualOf (Vector (Forward r)) = Vector r
  dzero = 0
  dscale k d = coerce k * d
  dadd = (+)
  dvar = undefined
  type ScalarOf (Vector (Forward r)) = r
  bindInState = undefined

instance Num (Matrix r) => HasDual (Matrix (Forward r)) where
  type DualOf (Matrix (Forward r)) = Matrix r
  dzero = 0
  dscale k d = coerce k * d
  dadd = (+)
  dvar = undefined
  type ScalarOf (Matrix (Forward r)) = r
  bindInState = undefined

instance Num (OT.Array r) => HasDual (OT.Array (Forward r)) where
  type DualOf (OT.Array (Forward r)) = OT.Array r
  dzero = 0
  dscale _k _d = undefined  -- TODO: coerce k * d
  dadd = (+)
  dvar = undefined
  type ScalarOf (OT.Array (Forward r)) = r
  bindInState = undefined

instance Num (OS.Array sh r) => HasDual (OS.Array sh (Forward r)) where
  type DualOf (OS.Array sh (Forward r)) = OS.Array sh r
  dzero = 0
  dscale _k _d = undefined  -- TODO: coerce k * d
  dadd = (+)
  dvar = undefined
  type ScalarOf (OS.Array sh (Forward r)) = r
  bindInState = undefined
