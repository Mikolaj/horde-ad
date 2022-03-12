{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, FlexibleInstances,
             GeneralizedNewtypeDeriving, TypeFamilyDependencies,
             TypeOperators #-}
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
  , HasDual(DualOf, dZero, dScale, dAdd, dVar, bindInState)
  , HasRanks(..)
  , Forward(..)
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Data.Coerce (coerce)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Core.Delta

-- | A shorthand for a useful set of constraints.
type HasDualWithScalar a r = (HasDual a, ScalarOf a ~ r)

-- | A mega-shorthand for a bundle of connected type constraints.
type IsScalar r = ( HasDualWithScalar r r, HasRanks r
                  , HasDual (Vector r), HasDual (Matrix r), HasDual (OT.Array r)
                  , ScalarOf (Vector r) ~ r, ScalarOf (Matrix r) ~ r
                  , Numeric r, Num (Vector r), Num (Matrix r) )

-- | Each shape of a containers of parameters ('tensor') has its own
-- collection of vector space-like constructors with which the sparse
-- vector expression (`delta expressions`) are built.
class HasDual a where
  type DualOf a = result | result -> a
  dZero :: DualOf a
  dScale :: a -> DualOf a -> DualOf a
  dAdd :: DualOf a -> DualOf a -> DualOf a
  dVar :: DeltaId a -> DualOf a
  type ScalarOf a
  bindInState :: DualOf a
              -> DeltaState (ScalarOf a)
              -> (DeltaState (ScalarOf a), DeltaId a)

class HasRanks r where
  dSumElements0 :: DualOf (Vector r) -> Int -> DualOf r
  dIndex0 :: DualOf (Vector r) -> Int -> Int -> DualOf r
  dDot0 :: Vector r -> DualOf (Vector r) -> DualOf r
  dFromX0 :: DualOf (OT.Array r) -> DualOf r
  dFromS0 :: DualOf (OS.Array '[] r) -> DualOf r

  dSeq1 :: Data.Vector.Vector (DualOf r) -> DualOf (Vector r)
  dKonst1 :: DualOf r -> Int -> DualOf (Vector r)
  dAppend1 :: DualOf (Vector r) -> Int -> DualOf (Vector r) -> DualOf (Vector r)
  dSlice1 :: Int -> Int -> DualOf (Vector r) -> Int -> DualOf (Vector r)
  dSumRows1 :: DualOf (Matrix r) -> Int -> DualOf (Vector r)
  dSumColumns1 :: DualOf (Matrix r) -> Int -> DualOf (Vector r)
  dM_VD1 :: Matrix r -> DualOf (Vector r) -> DualOf (Vector r)
  dMD_V1 :: DualOf (Matrix r) -> Vector r -> DualOf (Vector r)
  dFromX1 :: DualOf (OT.Array r) -> DualOf (Vector r)
  dFromS1 :: DualOf (OS.Array '[len] r) -> DualOf (Vector r)

  dFromRows2 :: Data.Vector.Vector (DualOf (Vector r)) -> DualOf (Matrix r)
  dFromColumns2 :: Data.Vector.Vector (DualOf (Vector r)) -> DualOf (Matrix r)
  dTranspose2 :: DualOf (Matrix r) -> DualOf (Matrix r)
  dM_MD2 :: Matrix r -> DualOf (Matrix r) -> DualOf (Matrix r)
  dMD_M2 :: DualOf (Matrix r) -> Matrix r -> DualOf (Matrix r)
  dRowAppend2 :: DualOf (Matrix r) -> Int -> DualOf (Matrix r)
              -> DualOf (Matrix r)
  dColumnAppend2 :: DualOf (Matrix r) -> Int -> DualOf (Matrix r)
                 -> DualOf (Matrix r)
  dRowSlice2 :: Int -> Int -> DualOf (Matrix r) -> Int -> DualOf (Matrix r)
  dColumnSlice2 :: Int -> Int -> DualOf (Matrix r) -> Int -> DualOf (Matrix r)
  dAsRow2 :: DualOf (Vector r) -> DualOf (Matrix r)
  dAsColumn2 :: DualOf (Vector r) -> DualOf (Matrix r)
  dFromX2 :: DualOf (OT.Array r) -> DualOf (Matrix r)
  dFromS2 :: DualOf (OS.Array '[rows, cols] r) -> DualOf (Matrix r)

  dAppendX :: DualOf (OT.Array r) -> Int -> DualOf (OT.Array r)
           -> DualOf (OT.Array r)
  dSliceX :: Int -> Int -> DualOf (OT.Array r) -> Int -> DualOf (OT.Array r)
  dFrom0X :: DualOf r -> DualOf (OT.Array r)
  dFrom1X :: DualOf (Vector r) -> DualOf (OT.Array r)
  dFrom2X :: DualOf (Matrix r) -> Int -> DualOf (OT.Array r)
  dFromSX :: DualOf (OS.Array sh r) -> DualOf (OT.Array r)

  dAppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
           => DualOf (OS.Array (m ': sh) r) -> DualOf (OS.Array (n ': sh) r)
           -> DualOf (OS.Array ((m + n) ': sh) r)
  dSliceS :: forall i n k rest.
             (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
          => DualOf (OS.Array (i + n + k ': rest) r)
          -> DualOf (OS.Array (n ': rest) r)
  dFrom0S :: DualOf r -> DualOf (OS.Array '[] r)
  dFrom1S :: DualOf (Vector r) -> DualOf (OS.Array '[n] r)
  dFrom2S :: forall rows cols. KnownNat cols
          => DualOf (Matrix r) -> DualOf (OS.Array '[rows, cols] r)
  dFromXS :: DualOf (OT.Array r) -> DualOf (OS.Array sh r)

-- I hate this duplication:
instance HasDual Double where
  type DualOf Double = Delta0 Double
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  dVar = Var0
  type ScalarOf Double = Double
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasRanks Double where
  dSumElements0 = SumElements0
  dIndex0 = Index0
  dDot0 = Dot0
  dFromX0 = FromX0
  dFromS0 = FromS0

-- I hate this duplication with this:
instance HasDual Float where
  type DualOf Float = Delta0 Float
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  dVar = Var0
  type ScalarOf Float = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasRanks Float where
  dSumElements0 = SumElements0
  dIndex0 = Index0
  dDot0 = Dot0
  dFromX0 = FromX0
  dFromS0 = FromS0

-- I hate this duplication:
instance HasDual (Vector Double) where
  type DualOf (Vector Double) = Delta1 Double
  dZero = Zero1
  dScale = Scale1
  dAdd = Add1
  dVar = Var1
  type ScalarOf (Vector Double) = Double
  {-# INLINE bindInState #-}
  bindInState = bindInState1

-- I hate this duplication with this:
instance HasDual (Vector Float) where
  type DualOf (Vector Float) = Delta1 Float
  dZero = Zero1
  dScale = Scale1
  dAdd = Add1
  dVar = Var1
  type ScalarOf (Vector Float) = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance HasDual (Matrix Double) where
  type DualOf (Matrix Double) = Delta2 Double
  dZero = Zero2
  dScale = Scale2
  dAdd = Add2
  dVar = Var2
  type ScalarOf (Matrix Double) = Double
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance HasDual (Matrix Float) where
  type DualOf (Matrix Float) = Delta2 Float
  dZero = Zero2
  dScale = Scale2
  dAdd = Add2
  dVar = Var2
  type ScalarOf (Matrix Float) = Float
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance HasDual (OT.Array Double) where
  type DualOf (OT.Array Double) = DeltaX Double
  dZero = ZeroX
  dScale = ScaleX
  dAdd = AddX
  dVar = VarX
  type ScalarOf (OT.Array Double) = Double
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance HasDual (OT.Array Float) where
  type DualOf (OT.Array Float) = DeltaX Float
  dZero = ZeroX
  dScale = ScaleX
  dAdd = AddX
  dVar = VarX
  type ScalarOf (OT.Array Float) = Float
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance OS.Shape sh => HasDual (OS.Array sh Double) where
  type DualOf (OS.Array sh Double) = DeltaS sh Double
  dZero = ZeroS
  dScale = ScaleS
  dAdd = AddS
  dVar = VarS
  type ScalarOf (OS.Array sh Double) = Double
  {-# INLINE bindInState #-}
  bindInState u' st = let (st2, did) = bindInStateX (FromSX u') st
                      in (st2, covertDeltaId did)

instance OS.Shape sh => HasDual (OS.Array sh Float) where
  type DualOf (OS.Array sh Float) = DeltaS sh Float
  dZero = ZeroS
  dScale = ScaleS
  dAdd = AddS
  dVar = VarS
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
  dZero = 0
  dScale (Forward k) d = k * d
  dAdd d e = d + e
  dVar = undefined  -- no variables are needed, because no blowup possible
  type ScalarOf (Forward Double) = Double
  bindInState = undefined  -- no variables, so no bindings

instance HasRanks (Forward Double) where
  dSumElements0 vd _ = HM.sumElements vd
  dIndex0 d ix _ = d V.! ix
  dDot0 vr vd = coerce vr HM.<.> vd
  dFromX0 = OT.unScalar
  dFromS0 = OS.unScalar
  -- TODO: the rest

-- I hate this duplication with this:
instance HasDual (Forward Float) where
  type DualOf (Forward Float) = Float
  dZero = 0
  dScale (Forward k) d = k * d
  dAdd d e = d + e
  dVar = undefined
  type ScalarOf (Forward Float) = Float
  bindInState = undefined

instance HasRanks (Forward Float) where
  dSumElements0 vd _ = HM.sumElements vd
  dIndex0 d ix _ = d V.! ix
  dDot0 vr vd = coerce vr HM.<.> vd
  dFromX0 = OT.unScalar
  dFromS0 = OS.unScalar
  -- TODO: the rest

instance Num (Vector r) => HasDual (Vector (Forward r)) where
  type DualOf (Vector (Forward r)) = Vector r
  dZero = 0
  dScale k d = coerce k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (Vector (Forward r)) = r
  bindInState = undefined

instance Num (Matrix r) => HasDual (Matrix (Forward r)) where
  type DualOf (Matrix (Forward r)) = Matrix r
  dZero = 0
  dScale k d = coerce k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (Matrix (Forward r)) = r
  bindInState = undefined

instance Num (OT.Array r) => HasDual (OT.Array (Forward r)) where
  type DualOf (OT.Array (Forward r)) = OT.Array r
  dZero = 0
  dScale _k _d = undefined  -- TODO: coerce k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (OT.Array (Forward r)) = r
  bindInState = undefined

instance Num (OS.Array sh r) => HasDual (OS.Array sh (Forward r)) where
  type DualOf (OS.Array sh (Forward r)) = OS.Array sh r
  dZero = 0
  dScale _k _d = undefined  -- TODO: coerce k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (OS.Array sh (Forward r)) = r
  bindInState = undefined
