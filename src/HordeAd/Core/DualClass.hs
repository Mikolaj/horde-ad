{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances, GADTs,
             MultiParamTypeClasses, PolyKinds, QuantifiedConstraints,
             TypeFamilyDependencies, UndecidableInstances #-}
#if defined(VERSION_ghc_typelits_natnormalise)
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
#endif
-- | The class defining dual components of dual numbers and
-- the dual number type itself, hiding its constructor, but exposing
-- a couple of smart constructors.
--
-- This module defines the relevant classes, type families,
-- constraints and instances for the dual numbers data structure.
-- This is a mid-level API ("HordeAd.Internal.Delta" is low level)
-- used to define types and operations in "HordeAd.Core.DualNumber"
-- that is the foundation of the high-level API.
--
-- This module contains impurity, which produces pure data with a particular
-- property. The property is an order of per-node integer identifiers
-- that represents data dependencies and sharing. The low-level API
-- depends on this property, but is completely isolated from the impurity.
-- The high-level API invokes the impurity through smart constructors,
-- but can't observe any impure behaviour. Neither can any other module
-- in the package, except for the testing modules that import
-- testing-exclusive operations and instances.
--
-- @Show@ is such a testing-only instance and so should be used
-- only in debugging or testing. Similarly, instances such as @Eq@
-- or @Read@ should not be auto-derived, but carefully crafted to respect
-- sharing. This applies regardless of impurity, because repeated processing
-- of the same shared terms is prohibitive expensive.
module HordeAd.Core.DualClass
  ( -- * The most often used part of the mid-level API that gets re-exported in high-level API
    ADVal, pattern D, dD, dDnotShared
  , ADMode(..), ADModeAndNum
  , -- * The less often used part of the mid-level API that gets re-exported in high-level API; it leaks implementation details
    IsPrimal(..), IsPrimalAndHasFeatures, HasDelta
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), HasInputs(..)
  , dummyDual, toShapedOrDummy, toDynamicOrDummy
  , -- * Internal operations, exposed, e.g., for tests
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
import qualified Numeric.LinearAlgebra as LA
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Internal.Delta

-- * The main dual number type

-- | Values the objective functions operate on. The first type argument
-- is the automatic differentiation mode and the second is the underlying
-- basic values (scalars, vectors, matrices, tensors and any other
-- supported containers of scalars).
--
-- Here, the datatype is implemented as dual numbers (hence @D@),
-- where the primal component, the basic value, the \"number\"
-- can be any containers of scalars. The primal component has the type
-- given as the second type argument and the dual component (with the type
-- determined by the type faimly @Dual@) is defined elsewhere.
data ADVal (d :: ADMode) a = D a (Dual d a)

-- | Smart constructor for 'D' of 'ADVal' that additionally records sharing
-- information, if applicable for the differentiation mode in question.
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: IsPrimal d a => a -> Dual d a -> ADVal d a
dD a dual = D a (recordSharing dual)

-- | This a not so smart constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: a -> Dual d a -> ADVal d a
dDnotShared = D


-- * Abbreviations to export (not used anywhere below)

-- | The intended semantics (not fully enforced by the constraint in isolation)
-- is that the second type is the primal component of a dual number type
-- at an unknown rank, with the given differentiation mode
-- and underlying scalar.
type IsPrimalWithScalar (d :: ADMode) a r =
  (IsPrimal d a, ScalarOf a ~ r)

-- | A shorthand for a useful set of constraints.
type IsPrimalAndHasFeatures (d :: ADMode) a r =
  ( IsPrimalWithScalar d a r
  , HasInputs a, RealFloat a, MonoFunctor a, Element a ~ r )

-- | A mega-shorthand for a bundle of connected type constraints.
-- The @Scalar@ in the name means that the second argument is the underlying
-- scalar type of a well behaved (wrt the differentiation mode in the first
-- argument) collection of primal and dual components of dual numbers.
type ADModeAndNum (d :: ADMode) r =
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
type HasDelta r = ( ADModeAndNum 'ADModeGradient r
                  , Dual 'ADModeGradient r ~ Delta0 r )


-- * Class definitions

-- | The enumeration of all available automatic differentiation computation
-- modes.
data ADMode =
    ADModeGradient
  | ADModeDerivative
  | ADModeValue

-- | The type family that enumerates all possible \"ranks\" for each
-- automatic differentiation mode. The second type argument is meant
-- to be the primal component of dual numbers. The result is the dual component.
--
-- Rank 0 is troublesome because, in derivative mode, the dual component
-- is not the primal component wrapped in a datatype or newtype constructor.
-- This makes impossible a representation of primal and dual components as
-- the primal plus the type constructor for creating the dual.
--
-- Rank S is troublesome because of the extra type parameter @sh@ representing
-- a shape. This is another obstacle to a dual number representation via
-- a single-argument type constructor.
type family Dual (d :: ADMode) a = result | result -> d a where
  Dual 'ADModeGradient Double = Delta0 Double
  Dual 'ADModeGradient Float = Delta0 Float
  Dual 'ADModeGradient (Vector r) = Delta1 r
  Dual 'ADModeGradient (Matrix r) = Delta2 r
  Dual 'ADModeGradient (OT.Array r) = DeltaX r
  Dual 'ADModeGradient (OS.Array sh r) = DeltaS sh r
-- not injective:  Dual 'ADModeDerivative r = r
  Dual 'ADModeDerivative Double = Double
  Dual 'ADModeDerivative Float = Float
  Dual 'ADModeDerivative (Vector r) = Vector r
  Dual 'ADModeDerivative (Matrix r) = Matrix r
  Dual 'ADModeDerivative (OT.Array r) = OT.Array r
  Dual 'ADModeDerivative (OS.Array sh r) = OS.Array sh r
  Dual 'ADModeValue a = DummyDual a

-- A bit more verbose, but a bit faster than @data@, perhaps by chance.
newtype DummyDual a = DummyDual ()

dummyDual :: DummyDual a
dummyDual = DummyDual ()

-- | The underlying scalar of a given primal component of a dual number.
-- A long name to remember not to use, unless necessary, and not to export.
type family ScalarOf a where
  ScalarOf Double = Double
  ScalarOf Float = Float
  ScalarOf (Vector r) = r
  ScalarOf (Matrix r) = r
  ScalarOf (OT.Array r) = r
  ScalarOf (OS.Array sh r) = r

-- | Second argument is the primal component of a dual number at some rank
-- wrt the differentiation mode given in the first argument.
class IsPrimal d a where
  dZero :: Dual d a
  dScale :: a -> Dual d a -> Dual d a
  dAdd :: Dual d a -> Dual d a -> Dual d a
  recordSharing :: Dual d a -> Dual d a

-- | Part 1/2 of a hack to squeeze the shaped tensors rank,
-- with its extra @sh@ parameter, into the 'IsPrimal' class.
class IsPrimalS d r where
  dZeroS :: forall sh. OS.Shape sh => Dual d (OS.Array sh r)
  dScaleS :: forall sh. OS.Shape sh
          => OS.Array sh r -> Dual d (OS.Array sh r) -> Dual d (OS.Array sh r)
  dAddS :: forall sh. OS.Shape sh
        => Dual d (OS.Array sh r) -> Dual d (OS.Array sh r)
        -> Dual d (OS.Array sh r)
  recordSharingS :: forall sh. OS.Shape sh
                 => Dual d (OS.Array sh r) -> Dual d (OS.Array sh r)

-- | Part 2/2 of a hack to squeeze the shaped tensors rank,
-- with its extra @sh@ parameter, into the 'IsPrimal' class.
instance (IsPrimalS d r, OS.Shape sh) => IsPrimal d (OS.Array sh r) where
  dZero = dZeroS
  dScale = dScaleS
  dAdd = dAddS
  recordSharing = recordSharingS

-- | Assuming that the type argument is the primal component of dual numbers
-- with differentiation mode `ADModeGradient`, this class makes available
-- the additional operations of delta-input and of packing a delta expression
-- and a dt parameter for computing its gradient.
class HasInputs a where
  dInput :: InputId a -> Dual 'ADModeGradient a
  packDeltaDt :: a -> Dual 'ADModeGradient a -> DeltaDt (ScalarOf a)

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first parameter.
class HasRanks (d :: ADMode) r where
  dSumElements0 :: Dual d (Vector r) -> Int -> Dual d r
  dIndex10 :: Dual d (Vector r) -> Int -> Int -> Dual d r
  dIndex20 :: Dual d (Matrix r) -> (Int, Int) -> (Int, Int) -> Dual d r
  dIndexX0 :: Dual d (OT.Array r) -> [Int] -> [Int] -> Dual d r
  dDot0 :: Vector r -> Dual d (Vector r) -> Dual d r
  dFromX0 :: Dual d (OT.Array r) -> Dual d r
  dFromS0 :: Dual d (OS.Array '[] r) -> Dual d r

  dFromList1 :: [Dual d r] -> Dual d (Vector r)
  dFromVector1 :: Data.Vector.Vector (Dual d r) -> Dual d (Vector r)
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
  dBuild1 :: RealFrac r => Int -> (Int -> Dual d r) -> Dual d (Vector r)

  dFromList2 :: (Int, Int) -> [Dual d r] -> Dual d (Matrix r)
  dFromVector2 :: (Int, Int) -> Data.Vector.Vector (Dual d r)
               -> Dual d (Matrix r)
  dFromRows2 :: Data.Vector.Vector (Dual d (Vector r)) -> Dual d (Matrix r)
  dFromColumns2 :: Data.Vector.Vector (Dual d (Vector r)) -> Dual d (Matrix r)
  dKonst2 :: Dual d r -> (Int, Int) -> Dual d (Matrix r)
  dTranspose2 :: Dual d (Matrix r) -> Dual d (Matrix r)
  dM_MD2 :: Matrix r -> Dual d (Matrix r) -> Dual d (Matrix r)
  dMD_M2 :: Dual d (Matrix r) -> Matrix r -> Dual d (Matrix r)
  dRowAppend2 :: Dual d (Matrix r) -> Int -> Dual d (Matrix r)
              -> Dual d (Matrix r)
  dColumnAppend2 :: Dual d (Matrix r) -> Int -> Dual d (Matrix r)
                 -> Dual d (Matrix r)
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
  dBuild2 :: RealFrac r
          => (Int, Int) -> ((Int, Int) -> Dual d r) -> Dual d (Matrix r)

  dFromListX :: OT.ShapeL -> [Dual d r] -> Dual d (OT.Array r)
  dFromVectorX :: OT.ShapeL -> Data.Vector.Vector (Dual d r)
               -> Dual d (OT.Array r)
  dKonstX :: Dual d r -> OT.ShapeL -> Dual d (OT.Array r)
  dAppendX :: Dual d (OT.Array r) -> Int -> Dual d (OT.Array r)
           -> Dual d (OT.Array r)
  dSliceX :: Int -> Int -> Dual d (OT.Array r) -> Int -> Dual d (OT.Array r)
  dIndexX :: Dual d (OT.Array r) -> Int -> Int -> Dual d (OT.Array r)
  dRavelFromListX :: [Dual d (OT.Array r)] -> Dual d (OT.Array r)
  dReshapeX :: OT.ShapeL -> OT.ShapeL -> Dual d (OT.Array r)
            -> Dual d (OT.Array r)
  dFrom0X :: Dual d r -> Dual d (OT.Array r)
  dFrom1X :: Dual d (Vector r) -> Dual d (OT.Array r)
  dFrom2X :: Dual d (Matrix r) -> Int -> Dual d (OT.Array r)
  dFromSX :: OS.Shape sh
          => Dual d (OS.Array sh r) -> Dual d (OT.Array r)

  dBuildX :: OT.ShapeL -> ([Int] -> Dual d r) -> Dual d (OT.Array r)

  dFromListS :: OS.Shape sh
             => [Dual d r] -> Dual d (OS.Array sh r)
  dFromVectorS :: OS.Shape sh
               => Data.Vector.Vector (Dual d r)
               -> Dual d (OS.Array sh r)
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

  dBuildS :: OS.Shape sh => ([Int] -> Dual d r) -> Dual d (OS.Array sh r)

-- * Backprop gradient method instances

-- | This, just as many other @ADModeGradient@ instances, is an impure
-- instance, because 'recordSharing' adorns terms with an @Int@ identifier
-- from a counter that is afterwards incremented (and never changed
-- in any other way).
--
-- The identifiers are not part of any non-internal module API
-- and the impure counter that gets incremented is not exposed
-- (except for low level tests). The identifiers are read only in internal
-- modules. They are assigned here once and ever accessed read-only.
-- Their uniqueness ensures that subterms that are shared in memory
-- are evaluated only once. If pointer equality worked efficiently
-- (e.g., if compact regions with sharing were cheaper), we wouldn't need
-- the impurity.
--
-- Given that we have to use impurity anyway, we make the implementation
-- faster by ensuring the order of identifiers reflects data dependency,
-- that is, parent nodes always have higher identifier than child nodes.
-- The @StrictData@ extension ensures that the implementation of the instances
-- are call by value, which is needed for that identifier ordering.
--
-- As long as "HordeAd.Internal.Delta" is used exclusively through
-- smart constructors from this API, the impurity is completely safe.
-- Even compiler optimizations, e.g., cse and full-laziness,
-- can't break the required invariants. On the contrary,
-- they increase sharing and make evaluation yet cheaper.
-- Of course, if the compiler, e.g., stops honouring @NOINLINE@,
-- all this breaks down.
--
-- The pattern-matching in 'recordSharing' is a crucial optimization
-- and it could, presumably, be extended to further limit which
-- terms get an identifier. Alternatively, 'HordeAd.Core.DualNumber.dD'
-- or library definitions that use it could be made smarter.
instance IsPrimal 'ADModeGradient Double where
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  recordSharing d = case d of
    Zero0 -> d
    Input0{} -> d
    Let0{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta0 d

-- | This is an impure instance. See above.
instance IsPrimal 'ADModeGradient Float where
  -- Identical as above:
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  recordSharing d = case d of
    Zero0 -> d
    Input0{} -> d
    Let0{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta0 d

-- | This is an impure instance. See above.
instance IsPrimal 'ADModeGradient (Vector r) where
  dZero = Zero1
  dScale = Scale1
  dAdd = Add1
  recordSharing d = case d of
    Zero1 -> d
    Input1{} -> d
    Let1{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta1 d

-- | This is an impure instance. See above.
instance IsPrimal 'ADModeGradient (Matrix r) where
  dZero = Zero2
  dScale = Scale2
  dAdd = Add2
  recordSharing d = case d of
    Zero2 -> d
    Input2{} -> d
    Let2{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta2 d

-- | This is an impure instance. See above.
instance IsPrimal 'ADModeGradient (OT.Array r) where
  dZero = ZeroX
  dScale = ScaleX
  dAdd = AddX
  recordSharing d = case d of
    ZeroX -> d
    InputX{} -> d
    LetX{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaX d

-- | This is an impure instance. See above.
instance IsPrimalS 'ADModeGradient r where
  dZeroS = ZeroS
  dScaleS = ScaleS
  dAddS = AddS
  recordSharingS d = case d of
    ZeroS -> d
    InputS{} -> d
    LetS{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaS d

instance HasInputs Double where
  dInput = Input0
  packDeltaDt = DeltaDt0

instance HasInputs Float where
  dInput = Input0
  packDeltaDt = DeltaDt0

instance HasInputs (Vector r) where
  dInput = Input1
  packDeltaDt = DeltaDt1

instance HasInputs (Matrix r) where
  dInput = Input2
  packDeltaDt = DeltaDt2

instance HasInputs (OT.Array r) where
  dInput = InputX
  packDeltaDt = DeltaDtX

instance OS.Shape sh => HasInputs (OS.Array sh r) where
  dInput = InputS
  packDeltaDt = DeltaDtS

-- | This is an impure instance. See above.
instance Dual 'ADModeGradient r ~ Delta0 r
         => HasRanks 'ADModeGradient r where
  dSumElements0 = SumElements0
  dIndex10 = Index10
  dIndex20 = Index20
  dIndexX0 = IndexX0
  dDot0 = Dot0
  dFromX0 = FromX0
  dFromS0 = FromS0
  dFromList1 = FromList1
  dFromVector1 = FromVector1
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
  dBuild1 = Build1
  dFromList2 = FromList2
  dFromVector2 = FromVector2
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
  dBuild2 = Build2
  dFromListX = FromListX
  dFromVectorX = FromVectorX
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
  dBuildX = BuildX
  dFromListS = FromListS
  dFromVectorS = FromVectorS
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
  dBuildS = BuildS


-- * Alternative instance: forward derivatives computed on the spot

instance IsPrimal 'ADModeDerivative Double where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  recordSharing = id

instance IsPrimal 'ADModeDerivative Float where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  recordSharing = id

-- These constraints force @UndecidableInstances@.
instance Num (Vector r)
         => IsPrimal 'ADModeDerivative (Vector r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  recordSharing = id

instance Num (Matrix r)
         => IsPrimal 'ADModeDerivative (Matrix r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  recordSharing = id

instance Num (OT.Array r)
         => IsPrimal 'ADModeDerivative (OT.Array r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  recordSharing = id

instance (Numeric r, Num (Vector r))
         => IsPrimalS 'ADModeDerivative r where
  dZeroS = 0
  dScaleS k d = k * d
  dAddS d e = d + e
  recordSharingS = id

instance ( Numeric r, Num (Vector r)
         , Dual 'ADModeDerivative r ~ r )
         => HasRanks 'ADModeDerivative r where
  dSumElements0 vd _ = LA.sumElements vd
  dIndex10 d ix _ = d V.! ix
  dIndex20 d ix _ = d `LA.atIndex` ix
  dIndexX0 d ix _ = d `atIndexInTensor` ix
  dDot0 = (LA.<.>)
  dFromX0 = OT.unScalar
  dFromS0 = OS.unScalar
  dFromList1 = V.fromList
  dFromVector1 = V.convert
  dKonst1 = LA.konst
  dAppend1 d _k e = d V.++ e
  dSlice1 i n d _len = V.slice i n d
  dM_VD1 = (LA.#>)
  dMD_V1 = (LA.#>)
  dSumRows1 dm _cols = V.fromList $ map LA.sumElements $ LA.toRows dm
  dSumColumns1 dm _rows = V.fromList $ map LA.sumElements $ LA.toColumns dm
  dFromX1 = OT.toVector
  dFromS1 = OS.toVector
  dReverse1 = V.reverse
  dFlatten1 _rows _cols = LA.flatten
  dFlattenX1 _sh = OT.toVector
  dFlattenS1 = OS.toVector
  dBuild1 n f = LA.build n (f . floor)
  dFromList2 (i, j) = j LA.>< i
  dFromVector2 (_i, j) = LA.reshape j . V.convert
  dFromRows2 = LA.fromRows . V.toList
  dFromColumns2 = LA.fromColumns . V.toList
  dKonst2 = LA.konst
  dTranspose2 = LA.tr'
  dM_MD2 = (LA.<>)
  dMD_M2 = (LA.<>)
  dAsRow2 = LA.asRow
  dAsColumn2 = LA.asColumn
  dRowAppend2 d _k e = d LA.=== e
  dColumnAppend2 d _k e = d LA.||| e
  dRowSlice2 i n d _rows = LA.takeRows n $ LA.dropRows i d
  dColumnSlice2 i n d _cols = LA.takeColumns n $ LA.dropColumns i d
  dFromX2 d = case OT.shapeL d of
    [_rows, cols] -> LA.reshape cols $ OT.toVector d
    _ -> error "dFromX2: wrong tensor dimensions"
  dFromS2 d = case OS.shapeL d of
    [_rows, cols] -> LA.reshape cols $ OS.toVector d
    _ -> error "dFromS2: wrong tensor dimensions"
  dFlipud2 = LA.flipud
  dFliprl2 = LA.fliprl
  dReshape2 = LA.reshape
  dConv2 = LA.conv2
  dBuild2 n f = LA.build n (\i j -> f (floor i, floor j))
  dFromListX sh = OT.fromList sh
  dFromVectorX sh = OT.fromVector sh . V.convert
  dKonstX d sh = OT.constant sh d
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
  dFrom2X d cols = OT.fromVector [LA.rows d, cols] $ LA.flatten d
  dFromSX = Data.Array.Convert.convert
  dBuildX = OT.generate
#if defined(VERSION_ghc_typelits_natnormalise)
  dFromListS = OS.fromList
  dFromVectorS = OS.fromVector . V.convert
  dKonstS = OS.constant
  dAppendS = OS.append
  dSliceS (_ :: Proxy i) (_ :: Proxy n) = OS.slice @'[ '(i, n) ]
  dIndexS d proxyIx = OS.index d (fromInteger $ natVal proxyIx)
  dRavelFromListS = OS.ravel . OSB.fromList
  dReshapeS = OS.reshape
  dFrom0S = OS.scalar
  dFrom1S = OS.fromVector
  dFrom2S _ = OS.fromVector . LA.flatten
  dFromXS = Data.Array.Convert.convert
  dBuildS = OS.generate
#endif


-- * Another alternative instance: only the objective function's value computed

instance IsPrimal 'ADModeValue Double where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing = id

instance IsPrimal 'ADModeValue Float where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing = id

instance IsPrimal 'ADModeValue (Vector r) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing = id

instance IsPrimal 'ADModeValue (Matrix r) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing = id

instance IsPrimal 'ADModeValue (OT.Array r) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing = id

instance IsPrimalS 'ADModeValue r where
  dZeroS = DummyDual ()
  dScaleS _ _ = DummyDual ()
  dAddS _ _ = DummyDual ()
  recordSharingS = id

instance HasRanks 'ADModeValue r where
  dSumElements0 _ _ = DummyDual ()
  dIndex10 _ _ _ = DummyDual ()
  dIndex20 _ _ _ = DummyDual ()
  dIndexX0 _ _ _ = DummyDual ()
  dDot0 _ _ = DummyDual ()
  dFromX0 _ = DummyDual ()
  dFromS0 _ = DummyDual ()
  dFromList1 _ = DummyDual ()
  dFromVector1 _ = DummyDual ()
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
  dBuild1 _ _ = DummyDual ()
  dFromList2 _ _ = DummyDual ()
  dFromVector2 _ _ = DummyDual ()
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
  dBuild2 _ _ = DummyDual ()
  dFromListX _ _ = DummyDual ()
  dFromVectorX _ _ = DummyDual ()
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
  dBuildX _ _ = DummyDual ()
#if defined(VERSION_ghc_typelits_natnormalise)
  dFromListS _ = DummyDual ()
  dFromVectorS _ = DummyDual ()
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
  dBuildS _ = DummyDual ()
#endif


unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 100000000)

-- | Do not use; this is exposed only for special low level tests,
-- similarly as the @Show@ instance.
--
-- This is the only operation directly touching the single impure counter
-- that holds fresh and continuously incremented integer identifiers,
-- The impurity in this module, stemming from the use of this operation
-- under @unsafePerformIO@, is thread-safe, admits parallel tests
-- and does not require @-fno-full-laziness@ nor @-fno-cse@.
-- The only tricky point is mandatory use of the smart constructors
-- above and that any new smart constructors should be similarly
-- call-by-value to ensure proper order of identifiers of subterms.
--
-- We start at a large number to make tests measuring the size of pretty
-- printed terms less fragile. @Counter@ datatype is just as safe,
-- but faster than an @MVar@ or an atomic @IORef@ (and even non-atomic @IORef@).
-- The operation is manually inlined to prevent GHCs deciding otherwise
-- and causing performance anomalies.
unsafeGetFreshId :: IO Int
{-# INLINE unsafeGetFreshId #-}
unsafeGetFreshId = atomicAddCounter_ unsafeGlobalCounter 1

-- The following functions are the only places, except for global
-- variable definitions, that contain `unsafePerformIO'.
-- BTW, tests don't show a speedup from `unsafeDupablePerformIO`,
-- perhaps due to counter gaps that it may introduce.
wrapDelta0 :: Delta0 r -> Delta0 r
{-# NOINLINE wrapDelta0 #-}
wrapDelta0 !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Let0 (NodeId n) d

wrapDelta1 :: Delta1 r -> Delta1 r
{-# NOINLINE wrapDelta1 #-}
wrapDelta1 !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Let1 (NodeId n) d

wrapDelta2 :: Delta2 r -> Delta2 r
{-# NOINLINE wrapDelta2 #-}
wrapDelta2 !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Let2 (NodeId n) d

wrapDeltaX :: DeltaX r -> DeltaX r
{-# NOINLINE wrapDeltaX #-}
wrapDeltaX !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! LetX (NodeId n) d

wrapDeltaS :: DeltaS sh r -> DeltaS sh r
{-# NOINLINE wrapDeltaS #-}
wrapDeltaS !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! LetS (NodeId n) d
