{-# LANGUAGE AllowAmbiguousTypes, CPP, ConstraintKinds, DataKinds,
             FlexibleInstances, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, TypeFamilyDependencies, TypeOperators,
             UndecidableInstances #-}
#if defined(VERSION_ghc_typelits_natnormalise)
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
#endif
-- | The class defining dual components of dual numbers. It contains
-- relevant classes, type families, constraints and instances.
-- This is a mid-level API ("HordeAd.Internal.Delta" is low level)
-- used to define types and operations in "HordeAd.Core.DualNumber"
-- that is the high-level API.
--
-- This module contains impurity, which produces pure data with particular
-- properties that low level modules require (a specific order
-- of per-node integer identifiers) and that can't be controlled, accessed
-- nor observed by any other module nor by users of the library.
-- The @Show@ instance is the only way the impurity can be detected
-- and so it should be used only in debugging or low-level testing context.
-- Similarly, instances such as @Eq@ or @Read@ should not be added.
module HordeAd.Core.DualClass
  ( IsPrimalWithScalar, IsPrimalAndHasFeatures, IsScalar, HasDelta
  , DMode(..), Dual, IsPrimal(..), HasRanks(..), HasInputs(..)
  , -- * Internal operations
    unsafeGetFreshId
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.MonoTraversable (Element, MonoFunctor)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Internal.Delta

-- * Abbreviations to export (not used anywhere below)

-- | The intended semantics (not fully enforced by the constraint in isolation)
-- is that the second type is the primal component of a dual number type
-- at an unknown rank, with the given differentiation mode
-- and underlying scalar.
type IsPrimalWithScalar (d :: DMode) a r =
  (IsPrimal d a, ScalarOf a ~ r)

-- | A shorthand for a useful set of constraints.
type IsPrimalAndHasFeatures (d :: DMode) a r =
  ( IsPrimalWithScalar d a r
  , HasInputs a, RealFloat a, MonoFunctor a, Element a ~ r )

-- | A mega-shorthand for a bundle of connected type constraints.
-- The @Scalar@ in the name means that the second argument is the underlying
-- scalar type of a well behaved (wrt the differentiation mode in the first
-- argument) collection of primal and dual components of dual numbers.
type IsScalar (d :: DMode) r =
  ( HasRanks d r, Ord r, Numeric r, Show r
  , IsPrimalAndHasFeatures d r r
  , IsPrimalAndHasFeatures d (Vector r) r
  , IsPrimalAndHasFeatures d (Matrix r) r
  , IsPrimalAndHasFeatures d (OT.Array r) r
  -- This fragment is for @OS.Array@ and it's irregular, because we can't
  -- mention @sh@ and so fully apply the type constructor.
  , IsPrimalS d r  -- TODO: Floating (OS.Array sh r), MonoFunctor
  )

-- | Is a scalar and will be used to compute gradients via delta-expressions.
type HasDelta r = ( IsScalar 'DModeGradient r
                  , Dual 'DModeGradient r ~ Delta0 r )


-- * Class definitions

-- | The enumeration of all possible differentiation (and more generally,
-- computation with dual numbers) schemes.
data DMode =
    DModeGradient
  | DModeDerivative
  | DModeValue

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
type family Dual (d :: DMode) a = result | result -> d a where
  Dual 'DModeGradient Double = Delta0 Double
  Dual 'DModeGradient Float = Delta0 Float
  Dual 'DModeGradient (Vector r) = Delta1 r
  Dual 'DModeGradient (Matrix r) = Delta2 r
  Dual 'DModeGradient (OT.Array r) = DeltaX r
  Dual 'DModeGradient (OS.Array sh r) = DeltaS sh r
-- not injective:  Dual 'DModeDerivative r = r
  Dual 'DModeDerivative Double = Double
  Dual 'DModeDerivative Float = Float
  Dual 'DModeDerivative (Vector r) = Vector r
  Dual 'DModeDerivative (Matrix r) = Matrix r
  Dual 'DModeDerivative (OT.Array r) = OT.Array r
  Dual 'DModeDerivative (OS.Array sh r) = OS.Array sh r
  Dual 'DModeValue a = DummyDual a

-- A bit more verbose, but a bit faster than @data@, perhaps by chance.
newtype DummyDual a = DummyDual ()

-- | The underlying scalar of a given primal component of a dual number.
-- A long name to remember not to use, unless necessary, and not to export.
type family ScalarOf a where
  ScalarOf Double = Double
  ScalarOf Float = Float
  ScalarOf (Vector r) = r
  ScalarOf (Matrix r) = r
  ScalarOf (OT.Array r) = r
  ScalarOf (OS.Array sh r) = r

-- | Second argument is a primal component of dual numbers at some rank
-- wrt the differentiation mode given in the first argument.
class IsPrimal d a where
  dZero :: Dual d a
  dScale :: a -> Dual d a -> Dual d a
  dAdd :: Dual d a -> Dual d a -> Dual d a

-- | Part 1/2 of a hack to squeeze the shaped tensors rank,
-- with its extra @sh@ parameter, into the 'IsPrimal' class.
class IsPrimalS d r where
  dZeroS :: forall sh. OS.Shape sh => Dual d (OS.Array sh r)
  dScaleS :: forall sh. OS.Shape sh
          => OS.Array sh r -> Dual d (OS.Array sh r) -> Dual d (OS.Array sh r)
  dAddS :: forall sh. OS.Shape sh
        => Dual d (OS.Array sh r) -> Dual d (OS.Array sh r)
        -> Dual d (OS.Array sh r)

-- | Part 2/2 of a hack to squeeze the shaped tensors rank,
-- with its extra @sh@ parameter, into the 'IsPrimal' class.
instance (IsPrimalS d r, OS.Shape sh) => IsPrimal d (OS.Array sh r) where
  dZero = dZeroS
  dScale = dScaleS
  dAdd = dAddS

-- | Assuming that the first argument is the primal component of dual numbers
-- with the underyling scalar in the second argument and with differentiation
-- mode `DModeGradient`, it additionally admits delta-input
-- introduction and binding as defined by the methods of the class.
class HasInputs a where
  dInput :: DeltaId a -> Dual 'DModeGradient a

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first argument.
class HasRanks (d :: DMode) r where
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

-- | This, just as many other @DModeGradient@ instances, is an impure instance.
-- Each created term tree node gets an @Int@ identifier
-- that is afterwards incremented (and never changed in any other way).
-- The identifiers are not part of any non-internal module API
-- and the impure counter that gets incremented is exposed only
-- to be used in special low level tests. The per-node identifiers
-- are used only in internal modules. They are assigned once and then read-only.
-- They ensure that subterms that are shared in memory are evaluated only once.
-- If pointer equality worked efficiently (e.g., if compact regions
-- with sharing were cheaper), we wouldn't need the impurity.
--
-- Given that we have to use impurity anyway, we make the implementation
-- faster by ensuring the order of identifiers reflects data dependency,
-- that is, parent nodes always have higher identifier than child nodes.
-- The bangs in the implementation of the instances are necessary to ensure
-- call by value, which is needed for that identifier ordering.
--
-- As long as "HordeAd.Internal.Delta" is used exclusively through
-- smart constructors from this API and the API is not (wrongly) modified,
-- the impurity is completely safe. Even compiler optimizations,
-- e.g., as cse and full-laziness, can't break the required invariants.
-- On the contrary, they increase sharing and make evaluation yet cheaper.
-- Of course, if the compiler, e.g., stopped honouring @NOINLINE@,
-- all this breaks down.
instance IsPrimal 'DModeGradient Double where
  dZero = Zero0
  dScale !k !d = wrapDelta0 $ Scale0 k d
  dAdd !d !e = wrapDelta0 $ Add0 d e

-- | This is an impure instance. See above.
instance IsPrimal 'DModeGradient Float where
  -- Identical as above:
  dZero = Zero0
  dScale !k !d = wrapDelta0 $ Scale0 k d
  dAdd !d !e = wrapDelta0 $ Add0 d e

-- | This is an impure instance. See above.
instance IsPrimal 'DModeGradient (Vector r) where
  dZero = Zero1
  dScale !k !d = wrapDelta1 $ Scale1 k d
  dAdd !d !e = wrapDelta1 $ Add1 d e

-- | This is an impure instance. See above.
instance IsPrimal 'DModeGradient (Matrix r) where
  dZero = Zero2
  dScale !k !d = wrapDelta2 $ Scale2 k d
  dAdd !d !e = wrapDelta2 $ Add2 d e

-- | This is an impure instance. See above.
instance IsPrimal 'DModeGradient (OT.Array r) where
  dZero = ZeroX
  dScale !k !d = wrapDeltaX $ ScaleX k d
  dAdd !d !e = wrapDeltaX $ AddX d e

-- | This is an impure instance. See above.
instance IsPrimalS 'DModeGradient r where
  dZeroS = ZeroS
  dScaleS !k !d = wrapDeltaS $ ScaleS k d
  dAddS !d !e = wrapDeltaS $ AddS d e

instance HasInputs Double where
  dInput = Input0

instance HasInputs Float where
  dInput = Input0

instance HasInputs (Vector r) where
  dInput = Input1

instance HasInputs (Matrix r) where
  dInput = Input2

instance HasInputs (OT.Array r) where
  dInput = InputX

instance HasInputs (OS.Array sh r) where
  dInput = InputS

-- | This is an impure instance. See above.
instance Dual 'DModeGradient r ~ Delta0 r
         => HasRanks 'DModeGradient r where
  dSumElements0 !vd !n = wrapDelta0 $ SumElements0 vd n
  dIndex0 !d !ix !k = wrapDelta0 $ Index0 d ix k
  dDot0 !v !vd = wrapDelta0 $ Dot0 v vd
  dFromX0 !d = wrapDelta0 $ FromX0 d
  dFromS0 !d = wrapDelta0 $ FromS0 d
  dSeq1 !lsd = wrapDelta1 $ Seq1 lsd
  dKonst1 !d !n = wrapDelta1 $ Konst1 d n
  dAppend1 !d !k !e = wrapDelta1 $ Append1 d k e
  dSlice1 !i !n !d !len = wrapDelta1 $ Slice1 i n d len
  dSumRows1 !dm !cols = wrapDelta1 $ SumRows1 dm cols
  dSumColumns1 !dm !rows = wrapDelta1 $ SumColumns1 dm rows
  dM_VD1 !m !dRow = wrapDelta1 $ M_VD1 m dRow
  dMD_V1 !md !row = wrapDelta1 $ MD_V1 md row
  dFromX1 !d = wrapDelta1 $ FromX1 d
  dFromS1 !d = wrapDelta1 $ FromS1 d
  dReverse1 !d = wrapDelta1 $ Reverse1 d
  dFlatten1 !rows !cols !d = wrapDelta1 $ Flatten1 rows cols d
  dFlattenX1 !sh !d = wrapDelta1 $ FlattenX1 sh d
  dFlattenS1 !d = wrapDelta1 $ FlattenS1 d
  dFromRows2 !lvd = wrapDelta2 $ FromRows2 lvd
  dFromColumns2 !lvd = wrapDelta2 $ FromColumns2 lvd
  dKonst2 !d !sz = wrapDelta2 $ Konst2 d sz
  dTranspose2 !md = wrapDelta2 $ Transpose2 md
  dM_MD2 !m !md = wrapDelta2 $ M_MD2 m md
  dMD_M2 !md !m = wrapDelta2 $ MD_M2 md m
  dRowAppend2 !d !k !e = wrapDelta2 $ RowAppend2 d k e
  dColumnAppend2 !d !k !e = wrapDelta2 $ ColumnAppend2 d k e
  dRowSlice2 !i !n !d !rows = wrapDelta2 $ RowSlice2 i n d rows
  dColumnSlice2 !i !n !d !cols = wrapDelta2 $ ColumnSlice2 i n d cols
  dAsRow2 !dRow = wrapDelta2 $ AsRow2 dRow
  dAsColumn2 !dCol = wrapDelta2 $ AsColumn2 dCol
  dFromX2 !d = wrapDelta2 $ FromX2 d
  dFromS2 !d = wrapDelta2 $ FromS2 d
  dFlipud2 !d = wrapDelta2 $ Flipud2 d
  dFliprl2 !d = wrapDelta2 $ Fliprl2 d
  dReshape2 !cols !d = wrapDelta2 $ Reshape2 cols d
  dConv2 !m !md = wrapDelta2 $ Conv2 m md
  dKonstX !d !sz = wrapDeltaX $ KonstX d sz
  dAppendX !d !k !e = wrapDeltaX $ AppendX d k e
  dSliceX !i !n !d !len = wrapDeltaX $ SliceX i n d len
  dIndexX !d !ix !len = wrapDeltaX $ IndexX d ix len
  dRavelFromListX !ld = wrapDeltaX $ RavelFromListX ld
  dReshapeX !sh !sh' !d = wrapDeltaX $ ReshapeX sh sh' d
  dFrom0X !d = wrapDeltaX $ From0X d
  dFrom1X !d = wrapDeltaX $ From1X d
  dFrom2X !d !cols = wrapDeltaX $ From2X d cols
  dFromSX !d = wrapDeltaX $ FromSX d
  dKonstS !d = wrapDeltaS $ KonstS d
  dAppendS !d !e = wrapDeltaS $ AppendS d e
  dSliceS !iProxy !nProxy !d = wrapDeltaS $ SliceS iProxy nProxy d
  dIndexS !d !ixProxy = wrapDeltaS $ IndexS d ixProxy
  dRavelFromListS !ld = wrapDeltaS $ RavelFromListS ld
  dReshapeS !d = wrapDeltaS $ ReshapeS d
  dFrom0S !d = wrapDeltaS $ From0S d
  dFrom1S !d = wrapDeltaS $ From1S d
  dFrom2S !proxyCols !d = wrapDeltaS $ From2S proxyCols d
  dFromXS !d = wrapDeltaS $ FromXS d


-- * Alternative instances: forward derivatives computed on the spot

instance IsPrimal 'DModeDerivative Double where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

instance IsPrimal 'DModeDerivative Float where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

-- These constraints force @UndecidableInstances@.
instance Num (Vector r)
         => IsPrimal 'DModeDerivative (Vector r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

instance Num (Matrix r)
         => IsPrimal 'DModeDerivative (Matrix r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

instance Num (OT.Array r)
         => IsPrimal 'DModeDerivative (OT.Array r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e

instance (Numeric r, Num (Vector r))
         => IsPrimalS 'DModeDerivative r where
  dZeroS = 0
  dScaleS k d = k * d
  dAddS d e = d + e

instance ( Numeric r, Num (Vector r)
         , Dual 'DModeDerivative r ~ r )
         => HasRanks 'DModeDerivative r where
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
#if defined(VERSION_ghc_typelits_natnormalise)
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
#endif


-- * Other alternative instances: only the objective function's value computed

instance IsPrimal 'DModeValue Double where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()

instance IsPrimal 'DModeValue Float where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()

instance IsPrimal 'DModeValue (Vector r) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()

instance IsPrimal 'DModeValue (Matrix r) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()

instance IsPrimal 'DModeValue (OT.Array r) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()

instance IsPrimalS 'DModeValue r where
  dZeroS = DummyDual ()
  dScaleS _ _ = DummyDual ()
  dAddS _ _ = DummyDual ()

instance HasRanks 'DModeValue r where
  dSumElements0 _ _ = DummyDual ()
  dIndex0 _ _ _ = DummyDual ()
  dDot0 _ _ = DummyDual ()
  dFromX0 _ = DummyDual ()
  dFromS0 _ = DummyDual ()
  dSeq1 _ = DummyDual ()
  dKonst1 _ _ = DummyDual ()
  dAppend1 _ _ _ = DummyDual ()
  dSlice1 _ _ _ _ = DummyDual ()
  dM_VD1 _ _ = DummyDual ()
  dMD_V1 _ _ = DummyDual ()
  dSumRows1 _ _ = DummyDual ()
  dSumColumns1 _ _ = DummyDual ()
  dFromX1 _ = DummyDual ()
  dFromS1 _ = DummyDual ()
  dReverse1 _ = DummyDual ()
  dFlatten1 _ _ _ = DummyDual ()
  dFlattenX1 _ _ = DummyDual ()
  dFlattenS1 _ = DummyDual ()
  dFromRows2 _ = DummyDual ()
  dFromColumns2 _ = DummyDual ()
  dKonst2 _ _ = DummyDual ()
  dTranspose2 _ = DummyDual ()
  dM_MD2 _ _ = DummyDual ()
  dMD_M2 _ _ = DummyDual ()
  dAsRow2 _ = DummyDual ()
  dAsColumn2 _ = DummyDual ()
  dRowAppend2 _ _ _ = DummyDual ()
  dColumnAppend2 _ _ _ = DummyDual ()
  dRowSlice2 _ _ _ _ = DummyDual ()
  dColumnSlice2 _ _ _ _ = DummyDual ()
  dFromX2 _ = DummyDual ()
  dFromS2 _ = DummyDual ()
  dFlipud2 _ = DummyDual ()
  dFliprl2 _ = DummyDual ()
  dReshape2 _ _ = DummyDual ()
  dConv2 _ _ = DummyDual ()
  dKonstX _ _ = DummyDual ()
  dAppendX _ _ _ = DummyDual ()
  dSliceX _ _ _ _ = DummyDual ()
  dIndexX _ _ _ = DummyDual ()
  dRavelFromListX _ = DummyDual ()
  dReshapeX _ _ _ = DummyDual ()
  dFrom0X _ = DummyDual ()
  dFrom1X _ = DummyDual ()
  dFrom2X _ _ = DummyDual ()
  dFromSX _ = DummyDual ()
#if defined(VERSION_ghc_typelits_natnormalise)
  dKonstS _ = DummyDual ()
  dAppendS _ _ = DummyDual ()
  dSliceS _ _ _ = DummyDual ()
  dIndexS _ _ = DummyDual ()
  dRavelFromListS _ = DummyDual ()
  dReshapeS _ = DummyDual ()
  dFrom0S _ = DummyDual ()
  dFrom1S _ = DummyDual ()
  dFrom2S _ _ = DummyDual ()
  dFromXS _ = DummyDual ()
#endif


unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 100000000)

-- | Do not use; this is exposed only for special low level tests,
-- just as the @Show@ instance.
--
-- This is the only operation directly touching the single impure counter
-- that holds fresh and continuously incremented integer identifiers,
-- The impurity in this module, stemming from the use of this operation
-- under @unsafePerformIO@ is thread-safe, admits parallel tests
-- and does not require @-fno-full-laziness@ nor @-fno-cse@.
-- The only tricky point is mandatory use of the smart constructors
-- above and that any new smart constructors should be similarly
-- call-by-value to ensure proper order of identifiers of subterms.
--
-- We start at a large number to make tests measuring the size of pretty
-- printed terms less fragile. @Counter@ datatype is just as safe,
-- but faster than an @MVar@ and than an atomic @IORef@
-- (and even non-atomic @IORef@). The operation is manually inlined
-- to prevent GHCs deciding otherwise and causing performance anomalies.
unsafeGetFreshId :: IO Int
{-# INLINE unsafeGetFreshId #-}
unsafeGetFreshId = atomicAddCounter_ unsafeGlobalCounter 1

-- The following functions are the only places, except for global
-- variable definitions, that contain `unsafePerformIO'.
-- BTW, test don't show a speedup from `unsafeDupablePerformIO`,
-- perhaps due to counter gaps that it may introduce.
wrapDelta0 :: Delta0' r -> Delta0 r
{-# NOINLINE wrapDelta0 #-}
wrapDelta0 !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Delta0 n d

wrapDelta1 :: Delta1' r -> Delta1 r
{-# NOINLINE wrapDelta1 #-}
wrapDelta1 !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Delta1 n d

wrapDelta2 :: Delta2' r -> Delta2 r
{-# NOINLINE wrapDelta2 #-}
wrapDelta2 !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Delta2 n d

wrapDeltaX :: DeltaX' r -> DeltaX r
{-# NOINLINE wrapDeltaX #-}
wrapDeltaX !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! DeltaX n d

wrapDeltaS :: DeltaS' sh r -> DeltaS sh r
{-# NOINLINE wrapDeltaS #-}
wrapDeltaS !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! DeltaS n d
