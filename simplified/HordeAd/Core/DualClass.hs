{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilyDependencies,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
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
    ADMode(..)
  , -- * The less often used part of the mid-level API that gets re-exported in high-level API; it leaks implementation details
    IsPrimal(..), IsPrimalR(..), IsPrimalAndHasFeatures, IsPrimalAndHasInputs
  , Element
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), HasInputs(..), dummyDual
  , -- * Internal operations, exposed for tests, debugging and experiments
    unsafeGetFreshId
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.MonoTraversable (Element, MonoFunctor)
import qualified Data.Strict.Vector as Data.Vector
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Show.Functions ()

import HordeAd.Core.SizedIndex
import HordeAd.Internal.Delta
import HordeAd.Internal.TensorOps

-- * Abbreviations to export (not used anywhere below)

-- | The intended semantics (not fully enforced by the constraint in isolation)
-- is that the second type is the primal component of a dual number type
-- at an unknown rank, with the given differentiation mode
-- and underlying scalar.
type IsPrimalWithScalar (d :: ADMode) a r =
  (IsPrimal d a, MonoFunctor a, Element a ~ r)

-- | A shorthand for a useful set of constraints.
type IsPrimalAndHasFeatures (d :: ADMode) a r =
  (IsPrimalWithScalar d a r, RealFloat a)

-- | A shorthand for a useful set of constraints.
type IsPrimalAndHasInputs (d :: ADMode) a r =
  (IsPrimalAndHasFeatures d a r, HasInputs a)


-- * Class definitions

-- | The enumeration of all available automatic differentiation computation
-- modes.
data ADMode =
    ADModeGradient
  | ADModeDerivative
  | ADModeValue
  deriving Show

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
  Dual 'ADModeGradient (OT.Array r) = DeltaX r
  Dual 'ADModeGradient (OR.Array n r) = Delta1 n r
-- not injective:  Dual 'ADModeDerivative r = r
  Dual 'ADModeDerivative Double = Double
  Dual 'ADModeDerivative Float = Float
  Dual 'ADModeDerivative (OT.Array r) = OT.Array r
  Dual 'ADModeDerivative (OR.Array n r) = OR.Array n r
  Dual 'ADModeValue a = DummyDual a

-- A bit more verbose, but a bit faster than @data@, perhaps by chance.
newtype DummyDual r = DummyDual ()
  deriving Show

dummyDual :: DummyDual r
dummyDual = DummyDual ()

-- | Second argument is the primal component of a dual number at some rank
-- wrt the differentiation mode given in the first argument.
class IsPrimal d a where
  dZero :: Dual d a
  dScale :: a -> Dual d a -> Dual d a
  dAdd :: Dual d a -> Dual d a -> Dual d a
  recordSharing :: Dual d a -> Dual d a

-- | Part 1/2 of a hack to squeeze the ranked tensors rank,
-- with its extra @n@ parameter, into the 'IsPrimal' class.
class IsPrimalR d r where
  dZeroR :: KnownNat n => Dual d (OR.Array n r)
  dScaleR :: KnownNat n
          => OR.Array n r -> Dual d (OR.Array n r) -> Dual d (OR.Array n r)
  dAddR :: KnownNat n
        => Dual d (OR.Array n r) -> Dual d (OR.Array n r)
        -> Dual d (OR.Array n r)
  recordSharingR :: Dual d (OR.Array n r) -> Dual d (OR.Array n r)

-- | Part 2/2 of a hack to squeeze the ranked tensors rank,
-- with its extra @n@ parameter, into the 'IsPrimal' class.
instance (IsPrimalR d r, KnownNat n) => IsPrimal d (OR.Array n r) where
  dZero = dZeroR
  dScale = dScaleR
  dAdd = dAddR
  recordSharing = recordSharingR

-- | Assuming that the type argument is the primal component of dual numbers
-- with differentiation mode `ADModeGradient`, this class makes available
-- the additional operations of delta-input and of packing a delta expression
-- and a dt parameter for computing its gradient.
class HasInputs a where
  dInput :: InputId a -> Dual 'ADModeGradient a
  packDeltaDt :: a -> Dual 'ADModeGradient a -> DeltaDt (Element a)

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first parameter.
class HasRanks (d :: ADMode) r where
  dIndex0 :: KnownNat n
          => Dual d (OR.Array n r) -> IndexInt n -> ShapeInt n -> Dual d r
  dSum0 :: KnownNat n
        => ShapeInt n -> Dual d (OR.Array n r) -> Dual d r
  dDot0 :: KnownNat n
        => OR.Array n r -> Dual d (OR.Array n r) -> Dual d r
  dUnScalar0 :: Dual d (OR.Array 0 r) -> Dual d r

  dIndex1 :: KnownNat n
          => Dual d (OR.Array (1 + n) r) -> Int -> Int -> Dual d (OR.Array n r)
  dIndexN :: (KnownNat n, KnownNat m)
          => Dual d (OR.Array (m + n) r) -> IndexInt m -> ShapeInt (m + n)
          -> Dual d (OR.Array n r)
  dSum1 :: KnownNat n
        => Int -> Dual d (OR.Array (1 + n) r) -> Dual d (OR.Array n r)
  dScalar1 :: Dual d r -> Dual d (OR.Array 0 r)
  dFromList1 :: KnownNat n
             => [Dual d (OR.Array n r)]
             -> Dual d (OR.Array (1 + n) r)
  dFromVector1 :: KnownNat n
               => Data.Vector.Vector (Dual d (OR.Array n r))
               -> Dual d (OR.Array (1 + n) r)
  dFromList01 :: KnownNat n
              => ShapeInt n -> [Dual d r] -> Dual d (OR.Array n r)
  dFromVector01 :: KnownNat n
                => ShapeInt n -> Data.Vector.Vector (Dual d r)
                -> Dual d (OR.Array n r)
  dKonst1 :: KnownNat n
          => Int -> Dual d (OR.Array n r) -> Dual d (OR.Array (1 + n) r)
  dKonst01 :: KnownNat n
           => ShapeInt n -> Dual d r -> Dual d (OR.Array n r)
  dAppend1 :: KnownNat n
           => Dual d (OR.Array n r) -> Int -> Dual d (OR.Array n r)
           -> Dual d (OR.Array n r)
  dSlice1 :: KnownNat n
          => Int -> Int -> Dual d (OR.Array n r) -> Int -> Dual d (OR.Array n r)
  dReverse1 :: KnownNat n
            => Dual d (OR.Array n r) -> Dual d (OR.Array n r)
  dTransposeGeneral1 :: KnownNat n
                     => Permutation -> Dual d (OR.Array n r)
                     -> Dual d (OR.Array n r)
  dReshape1 :: (KnownNat n, KnownNat m)
            => ShapeInt n -> ShapeInt m -> Dual d (OR.Array n r)
            -> Dual d (OR.Array m r)
  dBuild1 :: KnownNat n
          => Int -> (Int -> Dual d (OR.Array n r))
          -> Dual d (OR.Array (1 + n) r)
  dBuild01 :: KnownNat n
           => ShapeInt n -> (IndexInt n -> Dual d r) -> Dual d (OR.Array n r)
  dGather1 :: (KnownNat p, KnownNat n)
           => (Int -> IndexInt p)
           -> ShapeInt (p + n) -> Dual d (OR.Array (p + n) r)
           -> Int -> Dual d (OR.Array (1 + n) r)
  dGatherN1 :: (KnownNat m, KnownNat p, KnownNat n)
            => (IndexInt m -> IndexInt p)
            -> ShapeInt (p + n) -> Dual d (OR.Array (p + n) r)
            -> ShapeInt (m + n) -> Dual d (OR.Array (m + n) r)
  dScatter1 :: (KnownNat p, KnownNat n)
            => (Int -> IndexInt p)
            -> Int -> Dual d (OR.Array (1 + n) r)
            -> ShapeInt (p + n) -> Dual d (OR.Array (p + n) r)
  dScatterN1 :: (KnownNat m, KnownNat p, KnownNat n)
             => (IndexInt m -> IndexInt p)
             -> ShapeInt (m + n) -> Dual d (OR.Array (m + n) r)
             -> ShapeInt (p + n) -> Dual d (OR.Array (p + n) r)

  dFromX1 :: KnownNat n
          => Dual d (OT.Array r) -> Dual d (OR.Array n r)

  dFrom1X :: Dual d (OR.Array n r) -> Dual d (OT.Array r)

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
instance IsPrimalR 'ADModeGradient r where
  dZeroR = Zero1
  dScaleR = Scale1
  dAddR = Add1
  recordSharingR d = case d of
    Zero1 -> d
    FromX1{} -> d
    Let1{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta1 d

instance HasInputs Double where
  dInput = Input0
  packDeltaDt = DeltaDt0

instance HasInputs Float where
  dInput = Input0
  packDeltaDt = DeltaDt0

instance KnownNat n => HasInputs (OR.Array n r) where
  dInput = undefined  -- not needed
  packDeltaDt = DeltaDt1

instance HasInputs (OT.Array r) where
  dInput = InputX
  packDeltaDt = undefined  -- not needed

-- | This is an impure instance. See above.
instance Dual 'ADModeGradient r ~ Delta0 r
         => HasRanks 'ADModeGradient r where
  dIndex0 = Index0
  dSum0 = Sum0
  dDot0 = Dot0
  dUnScalar0 = UnScalar0

  dIndex1 = Index1
  dIndexN = IndexN
  dSum1 = Sum1
  dScalar1 = Scalar1
  dFromList1 = FromList1
  dFromVector1 = FromVector1
  dFromList01 = FromList01
  dFromVector01 = FromVector01
  dKonst1 = Konst1
  dKonst01 = Konst01
  dAppend1 = Append1
  dSlice1 = Slice1
  dReverse1 = Reverse1
  dTransposeGeneral1 = TransposeGeneral1
  dReshape1 = Reshape1
  dBuild1 = Build1
  dBuild01 = Build01
  dGather1 = Gather1
  dGatherN1 = GatherN1
  dScatter1 = Scatter1
  dScatterN1 = ScatterN1

  dFromX1 = FromX1

  dFrom1X = From1X

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

instance (Numeric r, Num (Vector r))
         => IsPrimalR 'ADModeDerivative r where
  dZeroR = 0
  dScaleR k d = k * d
  dAddR d e = d + e
  recordSharingR = id

instance ( Numeric r, Num (Vector r)
         , Dual 'ADModeDerivative r ~ r )
         => HasRanks 'ADModeDerivative r where
  dIndex0 d ixs _ = tindex0R d ixs
  dSum0 _ = tsum0R
  dDot0 = tdot0R
  dUnScalar0 = OR.unScalar

  dIndex1 d ix _ = tindexR d ix
  dIndexN d ixs _ = tindexNR d ixs
  dSum1 _ = tsumR
  dScalar1 = OR.scalar
  dFromList1 = tfromListR
  dFromVector1 = tfromVectorR
  dFromList01 = tfromList0NR
  dFromVector01 = tfromVector0NR
  dKonst1 = tkonstR
  dKonst01 = tkonst0NR
  dAppend1 d _k = tappendR d
  dSlice1 i n d _len = tsliceR i n d
  dReverse1 = treverseR
  dTransposeGeneral1 = ttransposeGeneralR
  dReshape1 _sh = treshapeR
  dBuild1 = tbuildR
  dBuild01 = tbuild0NR
  dGather1 f _sh = tgatherR f
  dGatherN1 f _shd = tgatherNR f
  dScatter1 f _n = tscatterR f
  dScatterN1 f _shd = tscatterNR f

  dFromX1 = Data.Array.Convert.convert

  dFrom1X = Data.Array.Convert.convert

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

instance IsPrimalR 'ADModeValue r where
  dZeroR = DummyDual ()
  dScaleR _ _ = DummyDual ()
  dAddR _ _ = DummyDual ()
  recordSharingR = id

-- This requires UndecidableInstances.
instance HasRanks 'ADModeValue r where
  dIndex0 _ _ _ = DummyDual ()
  dSum0 _ _ = DummyDual ()
  dDot0 _ _ = DummyDual ()
  dUnScalar0 _ = DummyDual ()

  dIndex1 _ _ _ = DummyDual ()
  dIndexN _ _ _ = DummyDual ()
  dSum1 _ _ = DummyDual ()
  dScalar1 _ = DummyDual ()
  dFromList1 _ = DummyDual ()
  dFromVector1 _ = DummyDual ()
  dFromList01 _ _ = DummyDual ()
  dFromVector01 _ _ = DummyDual ()
  dKonst1 _ _ = DummyDual ()
  dKonst01 _ _ = DummyDual ()
  dAppend1 _ _ _ = DummyDual ()
  dSlice1 _ _ _ _ = DummyDual ()
  dReverse1 _ = DummyDual ()
  dTransposeGeneral1 _ _ = DummyDual ()
  dReshape1 _ _ _ = DummyDual ()
  dBuild1 _ _ = DummyDual ()
  dBuild01 _ _ = DummyDual ()
  dGather1 _ _ _ _ = DummyDual ()
  dGatherN1 _ _ _ _ = DummyDual ()
  dScatter1 _ _ _ _ = DummyDual ()
  dScatterN1 _ _ _ _ = DummyDual ()

  dFromX1 _ = DummyDual ()

  dFrom1X _ = DummyDual ()

-- * Counter handling

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

wrapDelta1 :: Delta1 n r -> Delta1 n r
{-# NOINLINE wrapDelta1 #-}
wrapDelta1 !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Let1 (NodeId n) d
