{-# LANGUAGE AllowAmbiguousTypes, CPP, ConstraintKinds, DataKinds,
             FlexibleInstances, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, TypeFamilyDependencies, TypeOperators,
             UndecidableInstances #-}
#if !MIN_VERSION_base(4,17,0)
{-# LANGUAGE IncoherentInstances #-}
#endif
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The class of dual components of dual numbers and related classes,
-- constraints and instances.
module HordeAd.Core.DualClass
  ( IsDualWithScalar, IsScalar
  , HasDelta, HasForward
  , IsDual(Primal, dZero, dScale, dAdd, dVar, bindInState)
  , HasRanks(..)
  , Delta0  -- re-export; should be rarely used
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.Kind (Type)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Internal.Delta

-- * Abbreviations for export (not used anywhere below)

-- | A shorthand for a useful set of constraints. The intended semantics
-- (not fully enforced by the constraints in isolation) is that the first
-- type is a dual component of a dual number type at an unknown rank
-- and the second type is a dual component of the same dual number types
-- collection at the scalar level (rank 0), which also implies the underlying
-- scalar type is the same. Additionally, the primal component
-- corresponding to the first type is required to satisfy constraint @Num@.
type IsDualWithScalar a r =
  (IsDual a, ScalarOf a ~ Primal r, Floating (Primal a))

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
class IsDual a where
  type Primal a  -- can't be injective, because same for gradient and derivative
  dZero :: a
  dScale :: Primal a -> a -> a
  dAdd :: a -> a -> a
  dVar :: DeltaId (Primal a) -> a
  type ScalarOf a  -- verbose name to remember not to export from this module
  bindInState :: a
              -> DeltaState (ScalarOf a)
              -> (DeltaState (ScalarOf a), DeltaId (Primal a))

-- We had to inline @PrimalS@ in the signatures of the methods and everywhere
-- else in the code, because @~@ doesn't work on higher-rank types.
-- However, note that @Primal (TensorS sh r)@ is not inline and it's
-- used a lot in real code, because it's present in the API.
class IsDualS (t :: [Nat] -> Type) where
-- This is inlined away in order to avoid using the @RevArray@ newtype wrapper
-- that would be needed to partially apply @OS.Array@. Thanks to inlining
-- we can use @OS.Array@ below without the wrapper and not even
-- export @RevArray@, simplifying the API of this module.
--   type PrimalS t :: [Nat] -> Type
  dZeroS :: forall sh. OS.Shape sh => t sh
  dScaleS :: forall sh. OS.Shape sh => OS.Array sh (ScalarOfS t) -> t sh -> t sh
  dAddS :: forall sh. OS.Shape sh => t sh -> t sh -> t sh
  dVarS :: forall sh. OS.Shape sh => DeltaId (OS.Array sh (ScalarOfS t)) -> t sh
  type ScalarOfS t :: Type
  bindInStateS :: forall sh. OS.Shape sh
               => t sh
               -> DeltaState (ScalarOfS t)
               -> ( DeltaState (ScalarOfS t)
                  , DeltaId (OS.Array sh (ScalarOfS t)) )

-- This instance saves us from splitting @DualNumber@ and @DualNumberS@,
-- @scale@ and @scaleS@, etc., despite inlining @PrimalS@ (but not @Primal@).
instance (IsDualS t, OS.Shape sh) => IsDual (t sh) where
  type Primal (t sh) = OS.Array sh (ScalarOfS t)
  dZero = dZeroS
  dScale = dScaleS
  dAdd = dAddS
  dVar = dVarS
  type ScalarOf (t sh) = ScalarOfS t
  {-# INLINE bindInState #-}
  bindInState = bindInStateS

-- | An instance of the class is a type of rank 0 (scalar rank) dual components
-- of dual numbers. The associated type synonym families are dual component
-- counterparts at the remaining ranks, with the same underlying scalar.
-- The operations relate the dual and primal component at various ranks.
-- Not many of these properties are enforced by the definition of the class
-- itself, but together with the 'IsScalar' constraint, a lot is captured.
class HasRanks r where
  type Tensor1 r = result | result -> r
  type Tensor2 r = result | result -> r
  type TensorX r = result | result -> r
  type TensorS r = (result :: [Nat] -> Type) | result -> r

  dSumElements0 :: Tensor1 r -> Int -> r
  dIndex0 :: Tensor1 r -> Int -> Int -> r
  dDot0 :: Primal (Tensor1 r) -> Tensor1 r -> r
  dFromX0 :: TensorX r -> r
  dFromS0 :: TensorS r '[] -> r

  dSeq1 :: Data.Vector.Vector r -> Tensor1 r
  dKonst1 :: r -> Int -> Tensor1 r
  dAppend1 :: Tensor1 r -> Int -> Tensor1 r -> Tensor1 r
  dSlice1 :: Int -> Int -> Tensor1 r -> Int -> Tensor1 r
  dSumRows1 :: Tensor2 r -> Int -> Tensor1 r
  dSumColumns1 :: Tensor2 r -> Int -> Tensor1 r
  dM_VD1 :: Primal (Tensor2 r) -> Tensor1 r -> Tensor1 r
  dMD_V1 :: Tensor2 r -> Primal (Tensor1 r) -> Tensor1 r
  dFromX1 :: TensorX r -> Tensor1 r
  dFromS1 :: KnownNat len
          => TensorS r '[len] -> Tensor1 r
  dReverse1 :: Tensor1 r -> Tensor1 r
  dFlatten1 :: Int -> Int -> Tensor2 r -> Tensor1 r
  dFlattenX1 :: OT.ShapeL -> TensorX r -> Tensor1 r
  dFlattenS1 :: OS.Shape sh
             => TensorS r sh -> Tensor1 r

  dFromRows2 :: Data.Vector.Vector (Tensor1 r) -> Tensor2 r
  dFromColumns2 :: Data.Vector.Vector (Tensor1 r) -> Tensor2 r
  dKonst2 :: r -> (Int, Int) -> Tensor2 r
  dTranspose2 :: Tensor2 r -> Tensor2 r
  dM_MD2 :: Primal (Tensor2 r) -> Tensor2 r -> Tensor2 r
  dMD_M2 :: Tensor2 r -> Primal (Tensor2 r) -> Tensor2 r
  dRowAppend2 :: Tensor2 r -> Int -> Tensor2 r -> Tensor2 r
  dColumnAppend2 :: Tensor2 r -> Int -> Tensor2 r -> Tensor2 r
  dRowSlice2 :: Int -> Int -> Tensor2 r -> Int -> Tensor2 r
  dColumnSlice2 :: Int -> Int -> Tensor2 r -> Int -> Tensor2 r
  dAsRow2 :: Tensor1 r -> Tensor2 r
  dAsColumn2 :: Tensor1 r -> Tensor2 r
  dFromX2 :: TensorX r -> Tensor2 r
  dFromS2 :: (KnownNat rows, KnownNat cols)
          => TensorS r '[rows, cols] -> Tensor2 r

  dFlipud2 :: Tensor2 r -> Tensor2 r
  dFliprl2 :: Tensor2 r -> Tensor2 r
  dReshape2 :: Int -> Tensor1 r -> Tensor2 r
  dConv2 :: Primal (Tensor2 r) -> Tensor2 r -> Tensor2 r

  dKonstX :: r -> OT.ShapeL -> TensorX r
  dAppendX :: TensorX r -> Int -> TensorX r -> TensorX r
  dSliceX :: Int -> Int -> TensorX r -> Int -> TensorX r
  dIndexX :: TensorX r -> Int -> Int -> TensorX r
  dRavelFromListX :: [TensorX r] -> TensorX r
  dReshapeX :: OT.ShapeL -> OT.ShapeL -> TensorX r -> TensorX r
  dFrom0X :: r -> TensorX r
  dFrom1X :: Tensor1 r -> TensorX r
  dFrom2X :: Tensor2 r -> Int -> TensorX r
  dFromSX :: OS.Shape sh
          => TensorS r sh -> TensorX r

  dKonstS :: OS.Shape sh
          => r -> TensorS r sh
  dAppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
           => TensorS r (m ': sh) -> TensorS r (n ': sh)
           -> TensorS r ((m + n) ': sh)
  dSliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
          => Proxy i -> Proxy n -> TensorS r (i + n + k ': rest)
          -> TensorS r (n ': rest)
  dIndexS :: (KnownNat ix, KnownNat k, OS.Shape rest)
          => TensorS r (ix + 1 + k ': rest) -> Proxy ix -> TensorS r rest
  dRavelFromListS :: (KnownNat k, OS.Shape rest)
                  => [TensorS r rest] -> TensorS r (k : rest)
  dReshapeS :: (OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh')
            => TensorS r sh -> TensorS r sh'
  dFrom0S :: r -> TensorS r '[]
  dFrom1S :: KnownNat n => Tensor1 r -> TensorS r '[n]
  dFrom2S :: (KnownNat rows, KnownNat cols)
          => Proxy cols -> Tensor2 r -> TensorS r '[rows, cols]
  dFromXS :: OS.Shape sh => TensorX r -> TensorS r sh


-- * Backprop gradient method instances

instance IsDual (Delta0 r) where
  type Primal (Delta0 r) = r
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
  type TensorS (Delta0 r) = DeltaS r
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

instance IsDual (Delta1 r) where
  type Primal (Delta1 r) = Vector r
  dZero = Zero1
  dScale = Scale1
  dAdd = Add1
  dVar = Var1
  type ScalarOf (Delta1 r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance IsDual (Delta2 r) where
  type Primal (Delta2 r) = Matrix r
  dZero = Zero2
  dScale = Scale2
  dAdd = Add2
  dVar = Var2
  type ScalarOf (Delta2 r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance IsDual (DeltaX r) where
  type Primal (DeltaX r) = OT.Array r
  dZero = ZeroX
  dScale = ScaleX
  dAdd = AddX
  dVar = VarX
  type ScalarOf (DeltaX r) = r
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance IsDualS (DeltaS r) where
  dZeroS = ZeroS
  dScaleS = ScaleS
  dAddS = AddS
  dVarS = VarS
  type ScalarOfS (DeltaS r) = r
  {-# INLINE bindInStateS #-}
  bindInStateS u' st = let (st2, did) = bindInStateX (FromSX u') st
                       in (st2, covertDeltaId did)


-- * Alternative instances: forward derivatives computed on the spot

instance IsDual Double where
  type Primal Double = Double
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined  -- no variables are needed, because no blowup possible
  type ScalarOf Double = Double
  bindInState = undefined  -- no variables, so no bindings

instance IsDual Float where
  type Primal Float = Float
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  dVar = undefined
  type ScalarOf Float = Float
  bindInState = undefined

-- These constraints force @UndecidableInstances@.
instance Num (Vector r) => IsDual (Vector r) where
  type Primal (Vector r) = Vector r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (Vector r) = r
  bindInState = undefined

instance Num (Matrix r) => IsDual (Matrix r) where
  type Primal (Matrix r) = Matrix r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (Matrix r) = r
  bindInState = undefined

instance Num (OT.Array r) => IsDual (OT.Array r) where
  type Primal (OT.Array r) = OT.Array r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  dVar = undefined
  type ScalarOf (OT.Array r) = r
  bindInState = undefined

-- Due to this definition, which is necessary to partially apply @OS.Array@
-- to the @r@ argument, we need a lot of coercions in the code below
-- (but not anywhere else, I hope?).
newtype RevArray r sh = RevArray {unRevArray :: OS.Array sh r}

instance (forall sh. OS.Shape sh => Num (OS.Array sh r))
         => IsDualS (RevArray r) where
  dZeroS = RevArray 0
  dScaleS k d = RevArray $ k * unRevArray d
  dAddS d e = RevArray $ unRevArray d + unRevArray e
  dVarS = undefined
  type ScalarOfS (RevArray r) = r
  bindInStateS = undefined

instance HasRanks Double where
  type Tensor1 Double = Vector Double
  type Tensor2 Double = Matrix Double
  type TensorX Double = OT.Array Double
  type TensorS Double = RevArray Double
  dSumElements0 vd _ = HM.sumElements vd
  dIndex0 d ix _ = d V.! ix
  dDot0 = (HM.<.>)
  dFromX0 = OT.unScalar
  dFromS0 = OS.unScalar . unRevArray
  dSeq1 = V.convert
  dKonst1 = HM.konst
  dAppend1 d _k e = d V.++ e
  dSlice1 i n d _len = V.slice i n d
  dM_VD1 = (HM.#>)
  dMD_V1 = (HM.#>)
  dSumRows1 dm _cols = V.fromList $ map HM.sumElements $ HM.toRows dm
  dSumColumns1 dm _rows = V.fromList $ map HM.sumElements $ HM.toColumns dm
  dFromX1 = OT.toVector
  dFromS1 = OS.toVector . unRevArray
  dReverse1 = V.reverse
  dFlatten1 _rows _cols = HM.flatten
  dFlattenX1 _sh = OT.toVector
  dFlattenS1 = OS.toVector . unRevArray
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
  dFromS2 d = case OS.shapeL $ unRevArray d of
    [_rows, cols] -> HM.reshape cols $ OS.toVector $ unRevArray d
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
  dFromSX = Data.Array.Convert.convert . unRevArray
  dKonstS = RevArray . OS.constant
  dAppendS d e = RevArray $ OS.append (unRevArray d) (unRevArray e)
  dSliceS (_ :: Proxy i) (_ :: Proxy n) =
    RevArray . OS.slice @'[ '(i, n) ] . unRevArray
  dIndexS d proxyIx = RevArray
                      $ OS.index (unRevArray d) (fromInteger $ natVal proxyIx)
  dRavelFromListS = RevArray . OS.ravel . OSB.fromList . map unRevArray
  dReshapeS = RevArray . OS.reshape . unRevArray
  dFrom0S = RevArray . OS.scalar
  dFrom1S = RevArray . OS.fromVector
  dFrom2S _ = RevArray . OS.fromVector . HM.flatten
  dFromXS = RevArray . Data.Array.Convert.convert

instance HasRanks Float where
  type Tensor1 Float = Vector Float
  type Tensor2 Float = Matrix Float
  type TensorX Float = OT.Array Float
  type TensorS Float = RevArray Float
  -- Below it's completely repeated after the @Double@ case.
  dSumElements0 vd _ = HM.sumElements vd
  dIndex0 d ix _ = d V.! ix
  dDot0 = (HM.<.>)
  dFromX0 = OT.unScalar
  dFromS0 = OS.unScalar . unRevArray
  dSeq1 = V.convert
  dKonst1 = HM.konst
  dAppend1 d _k e = d V.++ e
  dSlice1 i n d _len = V.slice i n d
  dM_VD1 = (HM.#>)
  dMD_V1 = (HM.#>)
  dSumRows1 dm _cols = V.fromList $ map HM.sumElements $ HM.toRows dm
  dSumColumns1 dm _rows = V.fromList $ map HM.sumElements $ HM.toColumns dm
  dFromX1 = OT.toVector
  dFromS1 = OS.toVector . unRevArray
  dReverse1 = V.reverse
  dFlatten1 _rows _cols = HM.flatten
  dFlattenX1 _sh = OT.toVector
  dFlattenS1 = OS.toVector . unRevArray
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
  dFromS2 d = case OS.shapeL $ unRevArray d of
    [_rows, cols] -> HM.reshape cols $ OS.toVector $ unRevArray d
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
  dFromSX = Data.Array.Convert.convert . unRevArray
  dKonstS = RevArray . OS.constant
  dAppendS d e = RevArray $ OS.append (unRevArray d) (unRevArray e)
  dSliceS (_ :: Proxy i) (_ :: Proxy n) =
    RevArray . OS.slice @'[ '(i, n) ] . unRevArray
  dIndexS d proxyIx = RevArray
                      $ OS.index (unRevArray d) (fromInteger $ natVal proxyIx)
  dRavelFromListS = RevArray . OS.ravel . OSB.fromList . map unRevArray
  dReshapeS = RevArray . OS.reshape . unRevArray
  dFrom0S = RevArray . OS.scalar
  dFrom1S = RevArray . OS.fromVector
  dFrom2S _ = RevArray . OS.fromVector . HM.flatten
  dFromXS = RevArray . Data.Array.Convert.convert
