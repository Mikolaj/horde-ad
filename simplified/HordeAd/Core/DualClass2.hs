{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The class defining dual components of dual numbers and
-- the dual number type itself, hiding its constructor, but exposing
-- a couple of smart constructors.
--
-- This module defines the relevant classes, type families,
-- constraints and instances for the dual numbers data structure.
-- This is a mid-level API ("HordeAd.Core.Delta" is low level)
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
module HordeAd.Core.DualClass2
  ( -- * The most often used part of the mid-level API that gets re-exported in high-level API
    ADMode(..)
  , -- * The less often used part of the mid-level API that gets re-exported in high-level API; it leaks implementation details
    IsPrimal(..), IsPrimalR(..), IsPrimalAndHasFeatures, IsPrimalAndHasInputs
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), HasInputs(..), dummyDual
  , -- * Internal operations, exposed for tests, debugging and experiments
    unsafeGetFreshId
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.MonoTraversable (Element, MonoFunctor)
import qualified Data.Strict.Vector as Data.Vector
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Vector)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Delta
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
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
-- This hack is untimately needed because we have 3 instances
-- for @OR.Array@, one for each @d@, and the compiler can't see that
-- it exhausts all possible forms of @d@ and so constraints expressed with
-- a variable @d@ are satisfied. A similar hack for instances of @TensorOf@
-- woudln't work, because instances of type families are illegal.
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
instance (IsPrimalR d r, KnownNat n)
         => IsPrimal d (OR.Array n r) where
  dZero = dZeroR
  dScale = dScaleR
  dAdd = dAddR
  recordSharing = recordSharingR

-- | Assuming that the type argument is the primal component of dual numbers
-- with differentiation mode `ADModeGradient`, this class makes available
-- the additional operations of delta-input and of packing a delta expression
-- and a dt parameter for computing its gradient.
class HasInputs a where
  packDeltaDt :: a -> a -> Dual 'ADModeGradient a -> DeltaDt (Element a)
  inputConstant :: Element a -> a -> a

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first parameter.
class HasRanks (d :: ADMode) r where
  dInput0 :: InputId r -> Dual d r
  dIndex0 :: KnownNat n
          => Dual d (TensorOf n r) -> IndexOf n r -> ShapeInt n -> Dual d r
  dSum0 :: KnownNat n
        => ShapeInt n -> Dual d (TensorOf n r) -> Dual d r
  dDot0 :: KnownNat n
        => TensorOf n r -> Dual d (TensorOf n r) -> Dual d r
  dUnScalar0 :: Dual d (TensorOf 0 r) -> Dual d r

  dInput1 :: InputId (OR.Array n r) -> Dual d (TensorOf n r)
--  dIndex1 :: KnownNat n
--         => Dual d (TensorOf (1 + n) r) -> Int -> Int -> Dual d (TensorOf n r)
  dIndexN :: (KnownNat n, KnownNat m)
          => Dual d (TensorOf (m + n) r) -> IndexOf m r -> ShapeInt (m + n)
          -> Dual d (TensorOf n r)
  dSum1 :: KnownNat n
        => Int -> Dual d (TensorOf (1 + n) r) -> Dual d (TensorOf n r)
  dScalar1 :: Dual d r -> Dual d (TensorOf 0 r)
  dFromList1 :: KnownNat n
             => [Dual d (TensorOf n r)]
             -> Dual d (TensorOf (1 + n) r)
  dFromVector1 :: KnownNat n
               => Data.Vector.Vector (Dual d (TensorOf n r))
               -> Dual d (TensorOf (1 + n) r)
--  dFromList01 :: KnownNat n
--              => ShapeInt n -> [Dual d r] -> Dual d (TensorOf n r)
--  dFromVector01 :: KnownNat n
--                => ShapeInt n -> Data.Vector.Vector (Dual d r)
--                -> Dual d (TensorOf n r)
  dKonst1 :: KnownNat n
          => Int -> Dual d (TensorOf n r) -> Dual d (TensorOf (1 + n) r)
--  dKonst01 :: KnownNat n
--           => ShapeInt n -> Dual d r -> Dual d (TensorOf n r)
  dAppend1 :: KnownNat n
           => Dual d (TensorOf (1 + n) r) -> Int -> Dual d (TensorOf (1 + n) r)
           -> Dual d (TensorOf (1 + n) r)
  dSlice1 :: KnownNat n
          => Int -> Int -> Dual d (TensorOf (1 + n) r) -> Int
          -> Dual d (TensorOf (1 + n) r)
  dReverse1 :: KnownNat n
            => Dual d (TensorOf (1 + n) r) -> Dual d (TensorOf (1 + n) r)
  dTranspose1 :: KnownNat n
              => Permutation -> Dual d (TensorOf n r) -> Dual d (TensorOf n r)
  dReshape1 :: (KnownNat n, KnownNat m)
            => ShapeInt n -> ShapeInt m -> Dual d (TensorOf n r)
            -> Dual d (TensorOf m r)
  dBuild1 :: KnownNat n
          => Int -> (Int -> Dual d (TensorOf n r))
          -> Dual d (TensorOf (1 + n) r)
--  dGather1 :: (KnownNat p, KnownNat n)
--           => (Int -> IndexOf p r)
--           -> ShapeInt (p + n) -> Dual d (TensorOf (p + n) r)
--           -> Int -> Dual d (TensorOf (1 + n) r)
  dGatherN :: (KnownNat m, KnownNat p, KnownNat n)
           => ShapeInt (m + n) -> Dual d (TensorOf (p + n) r)
           -> (IndexOf m r -> IndexOf p r)
           -> ShapeInt (p + n)
           -> Dual d (TensorOf (m + n) r)
--  dScatter1 :: (KnownNat p, KnownNat n)
--            => (Int -> IndexOf p r)
--            -> Int -> Dual d (TensorOf (1 + n) r)
--            -> ShapeInt (p + n) -> Dual d (TensorOf (p + n) r)
  dScatterN :: (KnownNat m, KnownNat p, KnownNat n)
            => ShapeInt (p + n) -> Dual d (TensorOf (m + n) r)
            -> (IndexOf m r -> IndexOf p r)
            -> ShapeInt (m + n)
            -> Dual d (TensorOf (p + n) r)

  dFromX1 :: KnownNat n
          => Dual d (DynamicTensor r) -> Dual d (TensorOf n r)

  dFrom1X :: KnownNat n
          => Dual d (TensorOf n r) -> Dual d (DynamicTensor r)

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
-- As long as "HordeAd.Core.Delta" is used exclusively through
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

-- | This is a trivial and so a pure instance.
instance IsPrimal 'ADModeGradient (OT.Array r) where
  dZero = undefined
  dScale = undefined
  dAdd = undefined
  recordSharing = id

-- | This is an impure instance. See above.
instance IsPrimalR 'ADModeGradient Double where
  dZeroR = Zero1
  dScaleR = Scale1
  dAddR = Add1
  recordSharingR d = case d of
    Zero1 -> d
    Input1{} -> d
    FromX1{} -> d
    Let1{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta1 d

instance IsPrimalR 'ADModeGradient Float where
  dZeroR = Zero1
  dScaleR = Scale1
  dAddR = Add1
  recordSharingR d = case d of
    Zero1 -> d
    Input1{} -> d
    FromX1{} -> d
    Let1{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta1 d

instance HasInputs Double where
  packDeltaDt t _tsh = DeltaDt0 t
  inputConstant r _tsh = r

instance HasInputs Float where
  packDeltaDt t _tsh = DeltaDt0 t
  inputConstant r _tsh = r

instance KnownNat n => HasInputs (OR.Array n Double) where
  packDeltaDt t tsh =
    let sh = OR.shapeL t
        sh' = OR.shapeL tsh
    in assert (sh == sh'
               `blame` "packDeltaDt: dt and codomain differ in shape: "
               `swith` (sh, sh'))
       $ DeltaDt1 t
  inputConstant r tsh = OR.constant (OR.shapeL tsh) r

instance KnownNat n => HasInputs (OR.Array n Float) where
  packDeltaDt t tsh =
    let sh = OR.shapeL t
        sh' = OR.shapeL tsh
    in assert (sh == sh'
               `blame` "packDeltaDt: dt and codomain differ in shape: "
               `swith` (sh, sh'))
       $ DeltaDt1 t
  inputConstant r tsh = OR.constant (OR.shapeL tsh) r

-- | This is an impure instance. See above.
instance HasRanks 'ADModeGradient Double where
  dInput0 = Input0
  dIndex0 = Index0
  dSum0 = Sum0
  dDot0 = Dot0
  dUnScalar0 = UnScalar0

  dInput1 = Input1
--  dIndex1 = Index1
  dIndexN = IndexN
  dSum1 = Sum1
  dScalar1 = Scalar1
  dFromList1 = FromList1
  dFromVector1 = FromVector1
--  dFromList01 = FromList01
--  dFromVector01 = FromVector01
  dKonst1 = Konst1
--  dKonst01 = Konst01
  dAppend1 = Append1
  dSlice1 = Slice1
  dReverse1 = Reverse1
  dTranspose1 = Transpose1
  dReshape1 = Reshape1
  dBuild1 = Build1
--  dGather1 = Gather1
  dGatherN = GatherN
--  dScatter1 = Scatter1
  dScatterN = ScatterN

  dFromX1 = FromX1

  dFrom1X = From1X

instance HasRanks 'ADModeGradient Float where
  dInput0 = Input0
  dIndex0 = Index0
  dSum0 = Sum0
  dDot0 = Dot0
  dUnScalar0 = UnScalar0

  dInput1 = Input1
--  dIndex1 = Index1
  dIndexN = IndexN
  dSum1 = Sum1
  dScalar1 = Scalar1
  dFromList1 = FromList1
  dFromVector1 = FromVector1
--  dFromList01 = FromList01
--  dFromVector01 = FromVector01
  dKonst1 = Konst1
--  dKonst01 = Konst01
  dAppend1 = Append1
  dSlice1 = Slice1
  dReverse1 = Reverse1
  dTranspose1 = Transpose1
  dReshape1 = Reshape1
  dBuild1 = Build1
--  dGather1 = Gather1
  dGatherN = GatherN
--  dScatter1 = Scatter1
  dScatterN = ScatterN

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

instance Num (OT.Array r)
         => IsPrimal 'ADModeDerivative (OT.Array r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  recordSharing = id

instance IsPrimalR 'ADModeDerivative Double where
  dZeroR = 0
  dScaleR k d = k * d
  dAddR d e = d + e
  recordSharingR = id

-- Completely copied from above.
instance IsPrimalR 'ADModeDerivative Float where
  dZeroR = 0
  dScaleR k d = k * d
  dAddR d e = d + e
  recordSharingR = id

instance HasRanks 'ADModeDerivative Double where
  dInput0 = undefined
  dIndex0 d ixs _ = tindex0R d ixs
  dSum0 _ = tsum0R
  dDot0 = tdot0R
  dUnScalar0 = OR.unScalar

  dInput1 = undefined
--  dIndex1 d ix _ = tindexZ1R d ix
  dIndexN d ixs _ = tindexZR d ixs
  dSum1 _ = tsumR
  dScalar1 = OR.scalar
  dFromList1 = tfromListR
  dFromVector1 = tfromVectorR
--  dFromList01 = tfromList0NR
--  dFromVector01 = tfromVector0NR
  dKonst1 = tkonstR
--  dKonst01 = tkonst0NR
  dAppend1 d _k = tappendR d
  dSlice1 i n d _len = tsliceR i n d
  dReverse1 = treverseR
  dTranspose1 = ttransposeR
  dReshape1 _sh = treshapeR
  dBuild1 = tbuild1R
--  dGather1 f _sh u k = tgatherZ1R k u f
  dGatherN sh d f _shd = tgatherZR sh d f
--  dScatter1 f _n = tscatter1R f
  dScatterN sh d f _shd = tscatterNR sh d f

  dFromX1 = tfromD

  dFrom1X = tfromR

instance HasRanks 'ADModeDerivative Float where
  dInput0 = undefined
  dIndex0 d ixs _ = tindex0R d ixs
  dSum0 _ = tsum0R
  dDot0 = tdot0R
  dUnScalar0 = OR.unScalar

  dInput1 = undefined
--  dIndex1 d ix _ = tindex1R d ix
  dIndexN d ixs _ = tindexZR d ixs
  dSum1 _ = tsumR
  dScalar1 = OR.scalar
  dFromList1 = tfromListR
  dFromVector1 = tfromVectorR
--  dFromList01 = tfromList0NR
--  dFromVector01 = tfromVector0NR
  dKonst1 = tkonstR
--  dKonst01 = tkonst0NR
  dAppend1 d _k = tappendR d
  dSlice1 i n d _len = tsliceR i n d
  dReverse1 = treverseR
  dTranspose1 = ttransposeR
  dReshape1 _sh = treshapeR
  dBuild1 = tbuild1R
--  dGather1 f _sh u k = tgatherZ1R k u f
  dGatherN sh d f _shd = tgatherZR sh d f
--  dScatter1 f _n = tscatter1R f
  dScatterN sh d f _shd = tscatterNR sh d f

  dFromX1 = tfromD

  dFrom1X = tfromR

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

instance IsPrimal 'ADModeValue (OT.Array r) where
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
  dInput0 = undefined
  dIndex0 _ _ _ = DummyDual ()
  dSum0 _ _ = DummyDual ()
  dDot0 _ _ = DummyDual ()
  dUnScalar0 _ = DummyDual ()

  dInput1 = undefined
--  dIndex1 _ _ _ = DummyDual ()
  dIndexN _ _ _ = DummyDual ()
  dSum1 _ _ = DummyDual ()
  dScalar1 _ = DummyDual ()
  dFromList1 _ = DummyDual ()
  dFromVector1 _ = DummyDual ()
--  dFromList01 _ _ = DummyDual ()
--  dFromVector01 _ _ = DummyDual ()
  dKonst1 _ _ = DummyDual ()
--  dKonst01 _ _ = DummyDual ()
  dAppend1 _ _ _ = DummyDual ()
  dSlice1 _ _ _ _ = DummyDual ()
  dReverse1 _ = DummyDual ()
  dTranspose1 _ _ = DummyDual ()
  dReshape1 _ _ _ = DummyDual ()
  dBuild1 _ _ = DummyDual ()
--  dGather1 _ _ _ _ = DummyDual ()
  dGatherN _ _ _ _ = DummyDual ()
--  dScatter1 _ _ _ _ = DummyDual ()
  dScatterN _ _ _ _ = DummyDual ()

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
