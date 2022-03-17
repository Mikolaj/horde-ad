{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilyDependencies, TypeOperators,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
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
  ( HasDualWithScalar, IsScalar, IsScalarS, HasDelta, HasForward
  , HasDual(Dual, dZero, dScale, dAdd, dVar, bindInState)
  , HasRanks(..)
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Core.Delta

-- * Abbreviations

-- | A shorthand for a useful set of constraints.
type HasDualWithScalar a r = (HasDual a, ScalarOf a ~ Dual r, Num (Dual a))

-- | A mega-shorthand for a bundle of connected type constraints.
type IsScalar r =
       ( Ord (Dual r), Numeric (Dual r), HasRanks r
       , HasDualWithScalar r r, HasDualWithScalar (Tensor1 r) r
       , HasDualWithScalar (Tensor2 r) r, HasDualWithScalar (TensorX r) r
       , Dual (Tensor1 r) ~ Vector (Dual r)
       , Dual (Tensor2 r) ~ Matrix (Dual r)
       , Dual (TensorX r) ~ OT.Array (Dual r) )

type IsScalarS (sh :: [Nat]) r =
       ( IsScalar r, HasDualWithScalar (TensorS sh r) r
       , Dual (TensorS sh r) ~ OS.Array sh (Dual r) )

-- | A constraint stating dual numbers with this dual component
-- are implemented via gathering delta expressions in state.
type HasDelta r = (IsScalar r, r ~ Delta0 (Dual r))

-- | A constraint stating dual numbers with this dual component
-- are implemented via computing forward derivative on the spot.
type HasForward r = ( IsScalar r, Dual r ~ r, Tensor1 r ~ Vector r
                    , Tensor2 r ~ Matrix r, TensorX r ~ OT.Array r )


-- * Class definitions

-- | Each shape of a containers of parameters ('tensor') has its own
-- collection of vector space-like constructors with which the sparse
-- vector expression (`delta expressions`) are built.
class HasDual a where  -- HasPrimal? IsDual?
  type Dual a  -- can't be injective, because same for gradient and derivative
       -- Primal
  dZero :: a
  dScale :: Dual a -> a -> a
  dAdd :: a -> a -> a
  dVar :: DeltaId (Dual a) -> a
  type ScalarOf a  -- Scalar
  bindInState :: a
              -> DeltaState (ScalarOf a)
              -> (DeltaState (ScalarOf a), DeltaId (Dual a))

class HasRanks r where  -- IsTensor0?
  type Tensor1 r = result | result -> r
  type Tensor2 r = result | result -> r
  type TensorX r = result | result -> r
  type TensorS (sh :: [Nat]) r = result | result -> sh r

  dSumElements0 :: Tensor1 r -> Int -> r
  dIndex0 :: Tensor1 r -> Int -> Int -> r
  dDot0 :: Dual (Tensor1 r) -> Tensor1 r -> r
  dFromX0 :: TensorX r -> r
  dFromS0 :: TensorS '[] r -> r

  dSeq1 :: Data.Vector.Vector r -> Tensor1 r
  dKonst1 :: r -> Int -> Tensor1 r
  dAppend1 :: Tensor1 r -> Int -> Tensor1 r -> Tensor1 r
  dSlice1 :: Int -> Int -> Tensor1 r -> Int -> Tensor1 r
  dSumRows1 :: Tensor2 r -> Int -> Tensor1 r
  dSumColumns1 :: Tensor2 r -> Int -> Tensor1 r
  dM_VD1 :: Dual (Tensor2 r) -> Tensor1 r -> Tensor1 r
  dMD_V1 :: Tensor2 r -> Dual (Tensor1 r) -> Tensor1 r
  dFromX1 :: TensorX r -> Tensor1 r
  dFromS1 :: forall len. KnownNat len
          => TensorS '[len] r -> Tensor1 r

  dFromRows2 :: Data.Vector.Vector (Tensor1 r) -> Tensor2 r
  dFromColumns2 :: Data.Vector.Vector (Tensor1 r) -> Tensor2 r
  dTranspose2 :: Tensor2 r -> Tensor2 r
  dM_MD2 :: Dual (Tensor2 r) -> Tensor2 r -> Tensor2 r
  dMD_M2 :: Tensor2 r -> Dual (Tensor2 r) -> Tensor2 r
  dRowAppend2 :: Tensor2 r -> Int -> Tensor2 r
              -> Tensor2 r
  dColumnAppend2 :: Tensor2 r -> Int -> Tensor2 r
                 -> Tensor2 r
  dRowSlice2 :: Int -> Int -> Tensor2 r -> Int -> Tensor2 r
  dColumnSlice2 :: Int -> Int -> Tensor2 r -> Int -> Tensor2 r
  dAsRow2 :: Tensor1 r -> Tensor2 r
  dAsColumn2 :: Tensor1 r -> Tensor2 r
  dFromX2 :: TensorX r -> Tensor2 r
  dFromS2 :: forall rows cols. (KnownNat rows, KnownNat cols)
          => TensorS '[rows, cols] r -> Tensor2 r

  dAppendX :: TensorX r -> Int -> TensorX r
           -> TensorX r
  dSliceX :: Int -> Int -> TensorX r -> Int -> TensorX r
  dFrom0X :: r -> TensorX r
  dFrom1X :: Tensor1 r -> TensorX r
  dFrom2X :: Tensor2 r -> Int -> TensorX r
  dFromSX :: forall sh. OS.Shape sh
          => TensorS sh r -> TensorX r

  dAppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
           => TensorS (m ': sh) r -> TensorS (n ': sh) r
           -> TensorS ((m + n) ': sh) r
  dSliceS :: forall i n k rest.
             (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
          => TensorS (i + n + k ': rest) r
          -> TensorS (n ': rest) r
  dFrom0S :: r -> TensorS '[] r
  dFrom1S :: KnownNat n => Tensor1 r -> TensorS '[n] r
  dFrom2S :: forall rows cols. (KnownNat rows, KnownNat cols)
          => Tensor2 r -> TensorS '[rows, cols] r
  dFromXS :: OS.Shape sh => TensorX r -> TensorS sh r


-- * Backprop gradient method instances

instance HasDual (Delta0 r) where
  type Dual (Delta0 r) = r
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  dVar = Var0
  type ScalarOf (Delta0 r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasRanks (Delta0 r) where
  type Tensor1 (Delta0 r) = Delta1 r
  type Tensor2 (Delta0 r) = Delta2 r
  type TensorX (Delta0 r) = DeltaX r
  type TensorS sh (Delta0 r) = DeltaS sh r
  dSumElements0 = SumElements0
  dIndex0 = Index0
  dDot0 = Dot0
  dFromX0 = FromX0
  dFromS0 = FromS0
  dSeq1 = Seq1
  dKonst1 = Konst1
  dAppend1 = Append1
  dSlice1 = Slice1
  dSumRows1 = SumRows1
  dSumColumns1 = SumColumns1
  dM_VD1 = M_VD1
  dMD_V1 = MD_V1
  dFromX1 = FromX1
  dFromS1 = FromS1
  dFromRows2 = FromRows2
  dFromColumns2 = FromColumns2
  dTranspose2 = Transpose2
  dM_MD2 = M_MD2
  dMD_M2 = MD_M2
  dRowAppend2 = RowAppend2
  dColumnAppend2 = ColumnAppend2
  dRowSlice2 = RowSlice2
  dColumnSlice2 = ColumnSlice2
  dAsRow2 = AsRow2
  dAsColumn2 = AsColumn2
  dFromX2 = FromX2
  dFromS2 = FromS2
  dAppendX = AppendX
  dSliceX = SliceX
  dFrom0X = From0X
  dFrom1X = From1X
  dFrom2X = From2X
  dFromSX = FromSX
  dAppendS = AppendS
--  dSliceS :: forall i n k rest.
--             (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
--          => Dual (OS.Array (i + n + k ': rest) Double)
--          -> Dual (OS.Array (n ': rest) Double)
  dSliceS = undefined  -- TODO: SliceS @i
  dFrom0S = From0S
  dFrom1S = From1S
  dFrom2S = From2S
  dFromXS = FromXS

instance HasDual (Delta1 r) where
  type Dual (Delta1 r) = Vector r
  dZero = Zero1
  dScale = Scale1
  dAdd = Add1
  dVar = Var1
  type ScalarOf (Delta1 r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance HasDual (Delta2 r) where
  type Dual (Delta2 r) = Matrix r
  dZero = Zero2
  dScale = Scale2
  dAdd = Add2
  dVar = Var2
  type ScalarOf (Delta2 r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance HasDual (DeltaX r) where
  type Dual (DeltaX r) = OT.Array r
  dZero = ZeroX
  dScale = ScaleX
  dAdd = AddX
  dVar = VarX
  type ScalarOf (DeltaX r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance OS.Shape sh => HasDual (DeltaS sh r) where
  type Dual (DeltaS sh r) = OS.Array sh r
  dZero = ZeroS
  dScale = ScaleS
  dAdd = AddS
  dVar = VarS
  type ScalarOf (DeltaS sh r) = r
  {-# INLINE bindInState #-}
  bindInState u' st = let (st2, did) = bindInStateX (FromSX u') st
                      in (st2, covertDeltaId did)


-- * Alternative instances: forward derivatives computed on the spot

instance HasDual Double where
  type Dual Double = Double
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined  -- no variables are needed, because no blowup possible
  type ScalarOf Double = Double
  bindInState = undefined  -- no variables, so no bindings

instance HasDual Float where
  type Dual Float = Float
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined
  type ScalarOf Float = Float
  bindInState = undefined

-- These constraints force @UndecidableInstances@.
instance Num (Vector r) => HasDual (Vector r) where
  type Dual (Vector r) = Vector r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (Vector r) = r
  bindInState = undefined

instance Num (Matrix r) => HasDual (Matrix r) where
  type Dual (Matrix r) = Matrix r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (Matrix r) = r
  bindInState = undefined

instance Num (OT.Array r) => HasDual (OT.Array r) where
  type Dual (OT.Array r) = OT.Array r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (OT.Array r) = r
  bindInState = undefined

instance Num (OS.Array sh r) => HasDual (OS.Array sh r) where
  type Dual (OS.Array sh r) = OS.Array sh r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (OS.Array sh r) = r
  bindInState = undefined

instance HasRanks Double where
  type Tensor1 Double = Vector Double
  type Tensor2 Double = Matrix Double
  type TensorX Double = OT.Array Double
  type TensorS sh Double = OS.Array sh Double
  dSumElements0 vd _ = HM.sumElements vd
  dIndex0 d ix _ = d V.! ix
  dDot0 = (HM.<.>)
  dFromX0 = OT.unScalar
  dFromS0 = OS.unScalar
  dSeq1 = V.convert
  dKonst1 = HM.konst
  dAppend1 d _k e = d V.++ e
  dSlice1 i n d _len = V.slice i n d
  dM_VD1 = (HM.#>)
  dMD_V1 = (HM.#>)
  dSumRows1 dm _cols = V.fromList $ map HM.sumElements $ HM.toRows dm
  dSumColumns1 dm _rows = V.fromList $ map HM.sumElements $ HM.toColumns dm
  dFromX1 = OT.toVector
  dFromS1 = OS.toVector
  dFromRows2 = HM.fromRows . V.toList
  dFromColumns2 = HM.fromColumns . V.toList
  dTranspose2 = HM.tr'
  dM_MD2 = (HM.<>)
  dMD_M2 = (HM.<>)
  dAsRow2 = HM.asRow
  dAsColumn2 = HM.asColumn
  dRowAppend2 d _k e = d HM.=== e
  dColumnAppend2 d _k e = d HM.||| e
  dRowSlice2 i n d _rows = HM.takeRows n $ HM.dropRows i d
  dColumnSlice2 i n d _cols = HM.takeColumns n $ HM.dropColumns i d
  dFromX2 d = case OT.shapeL d of
    [_rows, cols] -> HM.reshape cols $ OT.toVector d
    _ -> error "dFromX2: wrong tensor dimensions"
  dFromS2 d = case OS.shapeL d of
    [_rows, cols] -> HM.reshape cols $ OS.toVector d
    _ -> error "dFromS2: wrong tensor dimensions"
  dAppendX d _k e = d `OT.append` e
  dSliceX i n d _len = OT.slice [(i, n)] d
  dFrom0X = OT.scalar
  dFrom1X d = OT.fromVector [V.length d] d
  dFrom2X d cols = OT.fromVector [HM.rows d, cols] $ HM.flatten d
  dFromSX = Data.Array.Convert.convert
  dAppendS = OS.append
--  dSliceS :: forall i n k rest.
--             (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
--          => Dual (OS.Array (i + n + k ': rest) Double)
--          -> Dual (OS.Array (n ': rest) Double)
  dSliceS = undefined  -- TODO: OS.slice @'[ '(i, n) ] d
  dFrom0S = OS.scalar
  dFrom1S = OS.fromVector
  dFrom2S = OS.fromVector . HM.flatten
  dFromXS = Data.Array.Convert.convert

instance HasRanks Float where
  type Tensor1 Float = Vector Float
  type Tensor2 Float = Matrix Float
  type TensorX Float = OT.Array Float
  type TensorS sh Float = OS.Array sh Float
  -- Below it's completely repeated after the @Double@ case.
  dSumElements0 vd _ = HM.sumElements vd
  dIndex0 d ix _ = d V.! ix
  dDot0 = (HM.<.>)
  dFromX0 = OT.unScalar
  dFromS0 = OS.unScalar
  dSeq1 = V.convert
  dKonst1 = HM.konst
  dAppend1 d _k e = d V.++ e
  dSlice1 i n d _len = V.slice i n d
  dM_VD1 = (HM.#>)
  dMD_V1 = (HM.#>)
  dSumRows1 dm _cols = V.fromList $ map HM.sumElements $ HM.toRows dm
  dSumColumns1 dm _rows = V.fromList $ map HM.sumElements $ HM.toColumns dm
  dFromX1 = OT.toVector
  dFromS1 = OS.toVector
  dFromRows2 = HM.fromRows . V.toList
  dFromColumns2 = HM.fromColumns . V.toList
  dTranspose2 = HM.tr'
  dM_MD2 = (HM.<>)
  dMD_M2 = (HM.<>)
  dAsRow2 = HM.asRow
  dAsColumn2 = HM.asColumn
  dRowAppend2 d _k e = d HM.=== e
  dColumnAppend2 d _k e = d HM.||| e
  dRowSlice2 i n d _rows = HM.takeRows n $ HM.dropRows i d
  dColumnSlice2 i n d _cols = HM.takeColumns n $ HM.dropColumns i d
  dFromX2 d = case OT.shapeL d of
    [_rows, cols] -> HM.reshape cols $ OT.toVector d
    _ -> error "dFromX2: wrong tensor dimensions"
  dFromS2 d = case OS.shapeL d of
    [_rows, cols] -> HM.reshape cols $ OS.toVector d
    _ -> error "dFromS2: wrong tensor dimensions"
  dAppendX d _k e = d `OT.append` e
  dSliceX i n d _len = OT.slice [(i, n)] d
  dFrom0X = OT.scalar
  dFrom1X d = OT.fromVector [V.length d] d
  dFrom2X d cols = OT.fromVector [HM.rows d, cols] $ HM.flatten d
  dFromSX = Data.Array.Convert.convert
  dAppendS = OS.append
--  dSliceS :: forall i n k rest.
--             (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
--          => Dual (OS.Array (i + n + k ': rest) Double)
--          -> Dual (OS.Array (n ': rest) Double)
  dSliceS = undefined  -- TODO: OS.slice @'[ '(i, n) ] d
  dFrom0S = OS.scalar
  dFrom1S = OS.fromVector
  dFrom2S = OS.fromVector . HM.flatten
  dFromXS = Data.Array.Convert.convert
