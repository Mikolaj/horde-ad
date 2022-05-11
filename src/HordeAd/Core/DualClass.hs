{-# LANGUAGE AllowAmbiguousTypes, CPP, ConstraintKinds, DataKinds,
             FlexibleInstances, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, TypeFamilyDependencies, TypeOperators,
             UndecidableInstances #-}
#if !MIN_VERSION_base(4,17,0)
{-# LANGUAGE IncoherentInstances #-}
#endif
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The class of dual components of dual numbers and related classes,
-- type families, constraints and instances. This is a low-level API
-- used to define types and operations in "HordeAd.Core.DualNumber"
-- that is the high-level API.
module HordeAd.Core.DualClass
  ( {- IsDualWithScalar, IsScalar, HasDelta, HasForward
  , IsDual(Primal, dZero, dScale, dAdd, dVar, bindInState)
  , HasRanks(..)
  , -} Delta0  -- re-export; should be rarely used
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.Kind (Type)
import           Data.MonoTraversable (Element, MonoFunctor)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Internal.Delta

{-

-- * Abbreviations for export (not used anywhere below)

-- | A shorthand for a useful set of constraints. The intended semantics
-- (not fully enforced by the constraints in isolation) is that the first
-- type is a dual component of a dual number type at an unknown rank
-- and the second type is a dual component of the same dual number types
-- collection at the scalar level (rank 0), which also implies the underlying
-- scalar type is the same. Additionally, the primal component
-- corresponding to the first type is required to satisfy constraint @Num@.
type IsDualWithScalar a r =
  ( IsDual a, ScalarOf a ~ Primal r, Floating (Primal a)
  , MonoFunctor (Primal a), Element (Primal a) ~ Primal r )

-- | A mega-shorthand for a bundle of connected type constraints.
-- The @Scalar@ in the name means that this type is a dual component
-- of a dual number type at the scalar (rank 0) level.
-- A more precise name would be @IsRank0DualWithAWellBehavedSetOfAllRanks@.
type IsScalar r =
       ( HasRanks r, Ord (Primal r), Numeric (Primal r), RealFloat (Primal r)
       , IsDualWithScalar r r, IsDualWithScalar (Tensor1 r) r
       , IsDualWithScalar (Tensor2 r) r, IsDualWithScalar (TensorX r) r
       , Primal (Tensor1 r) ~ Vector (Primal r)
       , Primal (Tensor2 r) ~ Matrix (Primal r)
       , Primal (TensorX r) ~ OT.Array (Primal r)
       -- This fragment is for @TensorS@ and it's irregular, because we can't
       -- mention @sh@ and so fully apply @TensorS@.
       , IsDualS (TensorS r), ScalarOfS (TensorS r) ~ Primal r
-- If we haven't inlined away @PrimalS@, we'd need this type equality,
-- which appears to work fine (but involves the @RevArray@ newtype wrapper,
-- so would incur the need to coerce all the time).
--       , PrimalS (TensorS r) ~ RevArray (Primal r)
       )

-- | A constraint expressing that dual numbers with this dual component
-- are implemented via gathering delta expressions in state.
type HasDelta r = (IsScalar r, r ~ Delta0 (Primal r))

-- | A constraint expressing that dual numbers with this dual component
-- are implemented via computing forward derivative on the spot.
type HasForward r = ( IsScalar r, r ~ ScalarOf r, Tensor1 r ~ Vector r
                    , Tensor2 r ~ Matrix r, TensorX r ~ OT.Array r )

-}

-- * Class definitions

-- | Each shape of containers of parameters (a tensor of particular rank)
-- has its own collection of vector-space-like operations that are
-- a crucial part of the machinery for computing gradients or derivatives
-- of objective functions defined on dual numbers.
--
-- The chosen representation makes the dual component of dual numbers
-- the argument of the class and the primal component the result
-- of the associated type synonym family @Primal@. A disadvantage
-- of this approach is that the @Primal@ type family is not injective
-- because it has the same value, say @Double@, in the instance
-- @Delta0 Double@ for computing gradients via delta-expressions
-- and in the instance @Double@ for computing forward derivatives on the spot.
-- The lack of injectivity results in a lot of @AllowAmbiguousTypes@ pragmas
-- and type arguments to functions.
--
-- Another disadvantage is @UndecidableInstances@ pragmas,
-- e.g., due to @Illegal nested constraint ‘Ord (Primal r)’@.
-- Yet another disadvantage is that once the gradient-based method
-- and an underlying scalar is chosen, a fully instantiated type
-- of a dual number function is peppered with @Delta0 Double@, etc.
-- This forces writing such function using spurious polymorphism,
-- with constraints that determine that the type is, in fact, monomorphic.
-- E.g., @(HasDelta r, Primal r ~ Double)@ constraint that permits
-- writing @r@ instead of @Delta0 Double@.
--
-- However, all this is better than the inverse problem, where the argument
-- of the class is the primal component and @Dual@ is an injective
-- associated type family. There, we'd need two different instances
-- for @Double@ to cover both gradients and forward derivatives.
-- This could be done via a newtype, which would incur some notational overhead
-- and the need to define many instances for the newtype, e.g., all hmatrix
-- instances, which requires fragile code based on hmatrix internal modules.
class IsDual a dual where
  dZero :: dual
  dScale :: a -> dual -> dual
  dAdd :: dual -> dual -> dual
  dVar :: DeltaId a -> dual
  type ScalarOf a dual
         -- verbose name to remember not to export from this module;
         -- can't be injective
  bindInState :: dual
              -> DeltaState (ScalarOf a dual)
              -> (DeltaState (ScalarOf a dual), DeltaId a)

-- | An instance of the class is a type of rank 0 (scalar rank) dual components
-- of dual numbers. The associated type synonym families are dual component
-- counterparts at the remaining ranks, with the same underlying scalar.
-- The operations relate the dual and primal component at various ranks.
-- Not many of these properties are enforced by the definition of the class
-- itself, but together with the 'IsScalar' constraint, a lot is captured.
class HasRanks r dual0 tensor1 tensor2 tensorX tensorS where
  dSumElements0 :: tensor1 r -> Int -> dual0
  dIndex0 :: tensor1 r -> Int -> Int -> dual0
  dDot0 :: Vector r -> tensor1 r -> dual0
  dFromX0 :: tensorX r -> dual0
  dFromS0 :: tensorS '[] r -> dual0

  dSeq1 :: Data.Vector.Vector dual0 -> tensor1 r
  dKonst1 :: dual0 -> Int -> tensor1 r
  dAppend1 :: tensor1 r -> Int -> tensor1 r -> tensor1 r
  dSlice1 :: Int -> Int -> tensor1 r -> Int -> tensor1 r
  dSumRows1 :: tensor2 r -> Int -> tensor1 r
  dSumColumns1 :: tensor2 r -> Int -> tensor1 r
  dM_VD1 :: Matrix r -> tensor1 r -> tensor1 r
  dMD_V1 :: tensor2 r -> Vector r -> tensor1 r
  dFromX1 :: tensorX r -> tensor1 r
  dFromS1 :: KnownNat len
          => tensorS '[len] r -> tensor1 r
  dReverse1 :: tensor1 r -> tensor1 r
  dFlatten1 :: Int -> Int -> tensor2 r -> tensor1 r
  dFlattenX1 :: OT.ShapeL -> tensorX r -> tensor1 r
  dFlattenS1 :: OS.Shape sh
             => tensorS sh r -> tensor1 r

  dFromRows2 :: Data.Vector.Vector (tensor1 r) -> tensor2 r
  dFromColumns2 :: Data.Vector.Vector (tensor1 r) -> tensor2 r
  dKonst2 :: dual0 -> (Int, Int) -> tensor2 r
  dTranspose2 :: tensor2 r -> tensor2 r
  dM_MD2 :: Matrix r -> tensor2 r -> tensor2 r
  dMD_M2 :: tensor2 r -> Matrix r -> tensor2 r
  dRowAppend2 :: tensor2 r -> Int -> tensor2 r -> tensor2 r
  dColumnAppend2 :: tensor2 r -> Int -> tensor2 r -> tensor2 r
  dRowSlice2 :: Int -> Int -> tensor2 r -> Int -> tensor2 r
  dColumnSlice2 :: Int -> Int -> tensor2 r -> Int -> tensor2 r
  dAsRow2 :: tensor1 r -> tensor2 r
  dAsColumn2 :: tensor1 r -> tensor2 r
  dFromX2 :: tensorX r -> tensor2 r
  dFromS2 :: (KnownNat rows, KnownNat cols)
          => tensorS '[rows, cols] r -> tensor2 r

  dFlipud2 :: tensor2 r -> tensor2 r
  dFliprl2 :: tensor2 r -> tensor2 r
  dReshape2 :: Int -> tensor1 r -> tensor2 r
  dConv2 :: Matrix r -> tensor2 r -> tensor2 r

  dKonstX :: dual0 -> OT.ShapeL -> tensorX r
  dAppendX :: tensorX r -> Int -> tensorX r -> tensorX r
  dSliceX :: Int -> Int -> tensorX r -> Int -> tensorX r
  dIndexX :: tensorX r -> Int -> Int -> tensorX r
  dRavelFromListX :: [tensorX r] -> tensorX r
  dReshapeX :: OT.ShapeL -> OT.ShapeL -> tensorX r -> tensorX r
  dFrom0X :: dual0 -> tensorX r
  dFrom1X :: tensor1 r -> tensorX r
  dFrom2X :: tensor2 r -> Int -> tensorX r
  dFromSX :: OS.Shape sh
          => tensorS sh r -> tensorX r

  dKonstS :: OS.Shape sh
          => dual0 -> tensorS sh r
  dAppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
           => tensorS (m ': sh) r -> tensorS (n ': sh) r
           -> tensorS ((m + n) ': sh) r
  dSliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
          => Proxy i -> Proxy n -> tensorS (i + n + k ': rest) r
          -> tensorS (n ': rest) r
  dIndexS :: (KnownNat ix, KnownNat k, OS.Shape rest)
          => tensorS (ix + 1 + k ': rest) r -> Proxy ix -> tensorS rest r
  dRavelFromListS :: (KnownNat k, OS.Shape rest)
                  => [tensorS rest r] -> tensorS (k : rest) r
  dReshapeS :: (OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh')
            => tensorS sh r -> tensorS sh' r
  dFrom0S :: dual0 -> tensorS '[] r
  dFrom1S :: KnownNat n => tensor1 r -> tensorS '[n] r
  dFrom2S :: (KnownNat rows, KnownNat cols)
          => Proxy cols -> tensor2 r -> tensorS '[rows, cols] r
  dFromXS :: OS.Shape sh => tensorX r -> tensorS sh r


-- * Backprop gradient method instances

instance IsDual r (Delta0 r) where
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  dVar = Var0
  type ScalarOf r (Delta0 r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasRanks r (Delta0 r) Delta1 Delta2 DeltaX DeltaS where
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
  dReverse1 = Reverse1
  dFlatten1 = Flatten1
  dFlattenX1 = FlattenX1
  dFlattenS1 = FlattenS1
  dFromRows2 = FromRows2
  dFromColumns2 = FromColumns2
  dKonst2 = Konst2
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
  dFlipud2 = Flipud2
  dFliprl2 = Fliprl2
  dReshape2 = Reshape2
  dConv2 = Conv2
  dKonstX = KonstX
  dAppendX = AppendX
  dSliceX = SliceX
  dIndexX = IndexX
  dRavelFromListX = RavelFromListX
  dReshapeX = ReshapeX
  dFrom0X = From0X
  dFrom1X = From1X
  dFrom2X = From2X
  dFromSX = FromSX
  dKonstS = KonstS
  dAppendS = AppendS
  dSliceS = SliceS
  dIndexS = IndexS
  dRavelFromListS = RavelFromListS
  dReshapeS = ReshapeS
  dFrom0S = From0S
  dFrom1S = From1S
  dFrom2S = From2S
  dFromXS = FromXS

instance IsDual (Vector r) (Delta1 r) where
  dZero = Zero1
  dScale = Scale1
  dAdd = Add1
  dVar = Var1
  type ScalarOf (Vector r) (Delta1 r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance IsDual (Matrix r) (Delta2 r) where
  dZero = Zero2
  dScale = Scale2
  dAdd = Add2
  dVar = Var2
  type ScalarOf (Matrix r) (Delta2 r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance IsDual (OT.Array r) (DeltaX r) where
  dZero = ZeroX
  dScale = ScaleX
  dAdd = AddX
  dVar = VarX
  type ScalarOf (OT.Array r) (DeltaX r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance OS.Shape sh => IsDual (OS.Array sh r) (DeltaS sh r) where
  dZero = ZeroS
  dScale = ScaleS
  dAdd = AddS
  dVar = VarS
  type ScalarOf (OS.Array sh r) (DeltaS sh r) = r
  {-# INLINE bindInState #-}
  bindInState u' st = let (st2, did) = bindInStateX (FromSX u') st
                      in (st2, covertDeltaId did)


-- * Alternative instances: forward derivatives computed on the spot

instance Num r => IsDual Double Double where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined  -- no variables are needed, because no blowup possible
  type ScalarOf Double Double = Double
  bindInState = undefined  -- no variables, so no bindings

instance Num r => IsDual Float Float where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined
  type ScalarOf Float Float = Float
  bindInState = undefined

-- These constraints force @UndecidableInstances@.
instance Num (Vector r) => IsDual (Vector r) (Vector r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined
  type ScalarOf (Vector r) (Vector r) = r
  bindInState = undefined

instance Num (Matrix r) => IsDual (Matrix r) (Matrix r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined
  type ScalarOf (Matrix r) (Matrix r) = r
  bindInState = undefined

instance Num (OT.Array r) => IsDual (OT.Array r) (OT.Array r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined
  type ScalarOf (OT.Array r) (OT.Array r) = r
  bindInState = undefined

instance (OS.Shape sh, Num (OS.Array sh r))
         => IsDual (OS.Array sh r) (OS.Array sh r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined
  type ScalarOf (OS.Array sh r) (OS.Array sh r) = r
  bindInState = undefined

instance (Numeric r, Num (Vector r))
         => HasRanks r r Vector Matrix OT.Array OS.Array where
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
  dReverse1 = V.reverse
  dFlatten1 _rows _cols = HM.flatten
  dFlattenX1 _sh = OT.toVector
  dFlattenS1 = OS.toVector
  dFromRows2 = HM.fromRows . V.toList
  dFromColumns2 = HM.fromColumns . V.toList
  dKonst2 = HM.konst
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
  dFlipud2 = HM.flipud
  dFliprl2 = HM.fliprl
  dReshape2 = HM.reshape
  dConv2 = HM.conv2
  dKonstX d sz = OT.constant sz d
  dAppendX d _k e = d `OT.append` e
  dSliceX i n d _len = OT.slice [(i, n)] d
  dIndexX d ix _len = OT.index d ix
  dRavelFromListX ld =
    let sh = case ld of
          d : _ -> length ld : OT.shapeL d
          [] -> []
    in OT.ravel $ OTB.fromList sh ld
  dReshapeX _sh = OT.reshape
  dFrom0X = OT.scalar
  dFrom1X d = OT.fromVector [V.length d] d
  dFrom2X d cols = OT.fromVector [HM.rows d, cols] $ HM.flatten d
  dFromSX = Data.Array.Convert.convert
  dKonstS = OS.constant
  dAppendS = OS.append
  dSliceS (_ :: Proxy i) (_ :: Proxy n) = OS.slice @'[ '(i, n) ]
  dIndexS d proxyIx = OS.index d (fromInteger $ natVal proxyIx)
  dRavelFromListS = OS.ravel . OSB.fromList
  dReshapeS = OS.reshape
  dFrom0S = OS.scalar
  dFrom1S = OS.fromVector
  dFrom2S _ = OS.fromVector . HM.flatten
  dFromXS = Data.Array.Convert.convert
