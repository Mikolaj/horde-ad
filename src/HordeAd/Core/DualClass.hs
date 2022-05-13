{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, TypeFamilyDependencies, TypeOperators,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The class defining dual components of dual numbers and related classes,
-- type families, constraints and instances. This is a low-level API
-- used to define types and operations in "HordeAd.Core.DualNumber"
-- that is the high-level API.
module HordeAd.Core.DualClass
  ( IsDualWithScalar, IsScalar, HasDelta
  , DifferentiationScheme(..), Dual
  , IsDual(..), HasVariables(..), HasRanks(..)
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.MonoTraversable (Element, MonoFunctor)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Internal.Delta

-- * Abbreviations to export (not used anywhere below)

-- | A shorthand for a useful set of constraints. The main intended semantics
-- (not fully enforced by the constraint in isolation) is that the second
-- type is the primal component of a dual number type at an unknown rank
-- and the third type is its underlying scalar.
type IsDualWithScalar (d :: DifferentiationScheme) a r =
  ( IsDual d a, HasVariables a r
  , Floating a, MonoFunctor a, Element a ~ r )

-- | A mega-shorthand for a bundle of connected type constraints.
-- The @Scalar@ in the name means that the second argument is the underlying
-- scalar type of a well behaved (wrt the differentiation mode in the first
-- argument) collection of primal and dual components of dual numbers.
type IsScalar (d :: DifferentiationScheme) r =
  ( HasRanks d r, Ord r, Numeric r, RealFloat r
  , IsDualWithScalar d r r, IsDualWithScalar d (Vector r) r
  , IsDualWithScalar d (Matrix r) r, IsDualWithScalar d (OT.Array r) r
  -- This fragment is for @OS.Array@ and it's irregular, because we can't
  -- mention @sh@ and so fully apply the type constructor.
  , IsDualS d r  -- TODO: Floating (OS.Array sh r), MonoFunctor
  )

-- | Is a scalar and will be used to compute gradients via delta-expressions.
type HasDelta r = ( IsScalar 'DifferentiationSchemeGradient r
                  , Dual 'DifferentiationSchemeGradient r ~ Delta0 r )


-- * Class definitions

-- | The enumeration of all possible differentiation (and more generally,
-- computation with dual numbers) modes.
data DifferentiationScheme =
    DifferentiationSchemeGradient
  | DifferentiationSchemeDerivative

-- | The type family that enumerates all possible "ranks"
-- for each differentiation mode.
-- The second type argument is meant to be the primal component
-- of dual numbers. The result is the dual component.
--
-- Rank 0 is special because, in derivatives mode, the dual component
-- is not the primal component wrapped in a datatype or newtype constructor.
-- This makes impossible a representation of primal and dual components as
-- the primal plus the type constructor for creating the dual.
--
-- Rank S is special, because of the extra type parameter @sh@ representing
-- a shape. This is another obstacle to a dual number representation via
-- a single-argument type constructor.
type family Dual (d :: DifferentiationScheme) a = result
                                                | result -> d a where
  Dual 'DifferentiationSchemeGradient Double = Delta0 Double
  Dual 'DifferentiationSchemeGradient Float = Delta0 Float
  Dual 'DifferentiationSchemeGradient (Vector r) = Delta1 r
  Dual 'DifferentiationSchemeGradient (Matrix r) = Delta2 r
  Dual 'DifferentiationSchemeGradient (OT.Array r) = DeltaX r
  Dual 'DifferentiationSchemeGradient (OS.Array sh r) = DeltaS sh r
-- not injective:  Dual 'DifferentiationSchemeDerivative r = r
  Dual 'DifferentiationSchemeDerivative Double = Double
  Dual 'DifferentiationSchemeDerivative Float = Float
  Dual 'DifferentiationSchemeDerivative (Vector r) = Vector r
  Dual 'DifferentiationSchemeDerivative (Matrix r) = Matrix r
  Dual 'DifferentiationSchemeDerivative (OT.Array r) = OT.Array r
  Dual 'DifferentiationSchemeDerivative (OS.Array sh r) = OS.Array sh r

-- | Second argument is a primal component of dual numbers at some rank
-- wrt the differentiation mode given in the first argument.
class IsDual d a where
  dZero :: Dual d a
  dScale :: a -> Dual d a -> Dual d a
  dAdd :: Dual d a -> Dual d a -> Dual d a

-- | Part 1/2 of a hack to squeeze the shaped tensors rank,
-- with its extra @sh@ parameter, into the 'IsDual' class.
class IsDualS d r where
  dZeroS :: forall sh. OS.Shape sh => Dual d (OS.Array sh r)
  dScaleS :: forall sh. OS.Shape sh
          => OS.Array sh r -> Dual d (OS.Array sh r) -> Dual d (OS.Array sh r)
  dAddS :: forall sh. OS.Shape sh
        => Dual d (OS.Array sh r) -> Dual d (OS.Array sh r)
        -> Dual d (OS.Array sh r)

-- | Part 2/2 of a hack to squeeze the shaped tensors rank,
-- with its extra @sh@ parameter, into the 'IsDual' class.
instance (IsDualS d r, OS.Shape sh) => IsDual d (OS.Array sh r) where
  dZero = dZeroS
  dScale = dScaleS
  dAdd = dAddS

-- | Assuming that the first argument is the primal component of dual numbers
-- with the underyling scalar in the second argument and with differentiation
-- mode `DifferentiationSchemeGradient`, it additionally admits delta-variable
-- introduction and binding as defined by the methods of the class.
class HasVariables a r | a -> r where
  dVar :: DeltaId a -> Dual 'DifferentiationSchemeGradient a
  bindInState :: Dual 'DifferentiationSchemeGradient a
              -> DeltaState r
              -> (DeltaState r, DeltaId a )

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first argument.
class HasRanks (d :: DifferentiationScheme) r where
  dSumElements0 :: Dual d (Vector r) -> Int -> Dual d r
  dIndex0 :: Dual d (Vector r) -> Int -> Int -> Dual d r
  dDot0 :: Vector r -> Dual d (Vector r) -> Dual d r
  dFromX0 :: Dual d (OT.Array r) -> Dual d r
  dFromS0 :: Dual d (OS.Array '[] r) -> Dual d r

  dSeq1 :: Data.Vector.Vector (Dual d r) -> Dual d (Vector r)
  dKonst1 :: Dual d r -> Int -> Dual d (Vector r)
  dAppend1 :: Dual d (Vector r) -> Int -> Dual d (Vector r) -> Dual d (Vector r)
  dSlice1 :: Int -> Int -> Dual d (Vector r) -> Int -> Dual d (Vector r)
  dSumRows1 :: Dual d (Matrix r) -> Int -> Dual d (Vector r)
  dSumColumns1 :: Dual d (Matrix r) -> Int -> Dual d (Vector r)
  dM_VD1 :: Matrix r -> Dual d (Vector r) -> Dual d (Vector r)
  dMD_V1 :: Dual d (Matrix r) -> Vector r -> Dual d (Vector r)
  dFromX1 :: Dual d (OT.Array r) -> Dual d (Vector r)
  dFromS1 :: KnownNat len
          => Dual d (OS.Array '[len] r) -> Dual d (Vector r)
  dReverse1 :: Dual d (Vector r) -> Dual d (Vector r)
  dFlatten1 :: Int -> Int -> Dual d (Matrix r) -> Dual d (Vector r)
  dFlattenX1 :: OT.ShapeL -> Dual d (OT.Array r) -> Dual d (Vector r)
  dFlattenS1 :: OS.Shape sh
             => Dual d (OS.Array sh r) -> Dual d (Vector r)

  dFromRows2 :: Data.Vector.Vector (Dual d (Vector r)) -> Dual d (Matrix r)
  dFromColumns2 :: Data.Vector.Vector (Dual d (Vector r)) -> Dual d (Matrix r)
  dKonst2 :: Dual d r -> (Int, Int) -> Dual d (Matrix r)
  dTranspose2 :: Dual d (Matrix r) -> Dual d (Matrix r)
  dM_MD2 :: Matrix r -> Dual d (Matrix r) -> Dual d (Matrix r)
  dMD_M2 :: Dual d (Matrix r) -> Matrix r -> Dual d (Matrix r)
  dRowAppend2 :: Dual d (Matrix r) -> Int -> Dual d (Matrix r) -> Dual d (Matrix r)
  dColumnAppend2 :: Dual d (Matrix r) -> Int -> Dual d (Matrix r) -> Dual d (Matrix r)
  dRowSlice2 :: Int -> Int -> Dual d (Matrix r) -> Int -> Dual d (Matrix r)
  dColumnSlice2 :: Int -> Int -> Dual d (Matrix r) -> Int -> Dual d (Matrix r)
  dAsRow2 :: Dual d (Vector r) -> Dual d (Matrix r)
  dAsColumn2 :: Dual d (Vector r) -> Dual d (Matrix r)
  dFromX2 :: Dual d (OT.Array r) -> Dual d (Matrix r)
  dFromS2 :: (KnownNat rows, KnownNat cols)
          => Dual d (OS.Array '[rows, cols] r) -> Dual d (Matrix r)

  dFlipud2 :: Dual d (Matrix r) -> Dual d (Matrix r)
  dFliprl2 :: Dual d (Matrix r) -> Dual d (Matrix r)
  dReshape2 :: Int -> Dual d (Vector r) -> Dual d (Matrix r)
  dConv2 :: Matrix r -> Dual d (Matrix r) -> Dual d (Matrix r)

  dKonstX :: Dual d r -> OT.ShapeL -> Dual d (OT.Array r)
  dAppendX :: Dual d (OT.Array r) -> Int -> Dual d (OT.Array r) -> Dual d (OT.Array r)
  dSliceX :: Int -> Int -> Dual d (OT.Array r) -> Int -> Dual d (OT.Array r)
  dIndexX :: Dual d (OT.Array r) -> Int -> Int -> Dual d (OT.Array r)
  dRavelFromListX :: [Dual d (OT.Array r)] -> Dual d (OT.Array r)
  dReshapeX :: OT.ShapeL -> OT.ShapeL -> Dual d (OT.Array r) -> Dual d (OT.Array r)
  dFrom0X :: Dual d r -> Dual d (OT.Array r)
  dFrom1X :: Dual d (Vector r) -> Dual d (OT.Array r)
  dFrom2X :: Dual d (Matrix r) -> Int -> Dual d (OT.Array r)
  dFromSX :: OS.Shape sh
          => Dual d (OS.Array sh r) -> Dual d (OT.Array r)

  dKonstS :: OS.Shape sh
          => Dual d r -> Dual d (OS.Array sh r)
  dAppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
           => Dual d (OS.Array (m ': sh) r) -> Dual d (OS.Array (n ': sh) r)
           -> Dual d (OS.Array ((m + n) ': sh) r)
  dSliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
          => Proxy i -> Proxy n -> Dual d (OS.Array (i + n + k ': rest) r)
          -> Dual d (OS.Array (n ': rest) r)
  dIndexS :: (KnownNat ix, KnownNat k, OS.Shape rest)
          => Dual d (OS.Array (ix + 1 + k ': rest) r)
          -> Proxy ix -> Dual d (OS.Array rest r)
  dRavelFromListS :: (KnownNat k, OS.Shape rest)
                  => [Dual d (OS.Array rest r)]
                  -> Dual d (OS.Array (k : rest) r)
  dReshapeS :: (OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh')
            => Dual d (OS.Array sh r) -> Dual d (OS.Array sh' r)
  dFrom0S :: Dual d r -> Dual d (OS.Array '[] r)
  dFrom1S :: KnownNat n => Dual d (Vector r) -> Dual d (OS.Array '[n] r)
  dFrom2S :: (KnownNat rows, KnownNat cols)
          => Proxy cols
          -> Dual d (Matrix r) -> Dual d (OS.Array '[rows, cols] r)
  dFromXS :: OS.Shape sh => Dual d (OT.Array r) -> Dual d (OS.Array sh r)


-- * Backprop gradient method instances

instance IsDual 'DifferentiationSchemeGradient Double where
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0

instance IsDual 'DifferentiationSchemeGradient Float where
  -- Identical as above:
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0

instance IsDual 'DifferentiationSchemeGradient (Vector r) where
  dZero = Zero1
  dScale = Scale1
  dAdd = Add1

instance IsDual 'DifferentiationSchemeGradient (Matrix r) where
  dZero = Zero2
  dScale = Scale2
  dAdd = Add2

instance IsDual 'DifferentiationSchemeGradient (OT.Array r) where
  dZero = ZeroX
  dScale = ScaleX
  dAdd = AddX

instance IsDualS 'DifferentiationSchemeGradient r where
  dZeroS = ZeroS
  dScaleS = ScaleS
  dAddS = AddS

instance HasVariables Double Double where
  dVar = Var0
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasVariables Float Float where
  dVar = Var0
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasVariables (Vector r) r where
  dVar = Var1
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance HasVariables (Matrix r) r where
  dVar = Var2
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance HasVariables (OT.Array r) r where
  dVar = VarX
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance OS.Shape sh => HasVariables (OS.Array sh r) r where
  dVar = VarS
  {-# INLINE bindInState #-}
  bindInState u' st = let (st2, did) = bindInStateX (FromSX u') st
                      in (st2, covertDeltaId did)

instance Dual 'DifferentiationSchemeGradient r ~ Delta0 r
         => HasRanks 'DifferentiationSchemeGradient r where
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


-- * Alternative instances: forward derivatives computed on the spot

instance IsDual 'DifferentiationSchemeDerivative Double where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

instance IsDual 'DifferentiationSchemeDerivative Float where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

-- These constraints force @UndecidableInstances@.
instance Num (Vector r)
         => IsDual 'DifferentiationSchemeDerivative (Vector r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

instance Num (Matrix r)
         => IsDual 'DifferentiationSchemeDerivative (Matrix r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

instance Num (OT.Array r)
         => IsDual 'DifferentiationSchemeDerivative (OT.Array r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

instance (Numeric r, Num (Vector r))
         => IsDualS 'DifferentiationSchemeDerivative r where
  dZeroS = 0
  dScaleS k d = k * d
  dAddS d e = d + e

instance ( Numeric r, Num (Vector r)
         , Dual 'DifferentiationSchemeDerivative r ~ r )
         => HasRanks 'DifferentiationSchemeDerivative r where
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
