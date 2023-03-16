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
module HordeAd.Core.DualClass
  ( -- * The most often used part of the mid-level API that gets re-exported in high-level API
    IsPrimal(..), IsPrimalR(..), IsPrimalA (..), IsPrimalWithScalar
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), dummyDual
  , -- * Internal operations, exposed for tests, debugging and experiments
    unsafeGetFreshId
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.MonoTraversable (Element)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import           GHC.TypeLits (KnownNat, sameNat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.AstVectorize ()
import HordeAd.Core.Delta
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

-- * Abbreviations to export (not used anywhere below)

-- | The intended semantics (not fully enforced by the constraint in isolation)
-- is that the second type is the primal component of a dual number type
-- at an unknown rank, with the given differentiation mode
-- and underlying scalar.
type IsPrimalWithScalar a r =
  (IsPrimal a, Element a ~ r)


-- * Class definitions

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
type family Dual a = result | result -> a where
  Dual Double = Delta0 Double
  Dual Float = Delta0 Float
  Dual (AstScalar r) = Delta0 (AstScalar r)
  Dual (OT.Array Double) = DeltaX Double
  Dual (OT.Array Float) = DeltaX Float
  Dual (OR.Array n Double) = Delta1 n Double
  Dual (OR.Array n Float) = Delta1 n Float
  Dual (AstDynamic r) = DeltaX (AstScalar r)
  Dual (Ast n r) = Delta1 n (AstScalar r)

-- A bit more verbose, but a bit faster than @data@, perhaps by chance.
newtype DummyDual r = DummyDual ()
  deriving Show

dummyDual :: DummyDual r
dummyDual = DummyDual ()

-- | Second argument is the primal component of a dual number at some rank
-- wrt the differentiation mode given in the first argument.
class IsPrimal a where
  dZero :: Dual a
  dScale :: a -> Dual a -> Dual a
  dAdd :: Dual a -> Dual a -> Dual a
  recordSharing :: Dual a -> Dual a
  packDeltaDt :: Either (Element a, a) a -> Dual a -> DeltaDt (Element a)

-- | Part 1/2 of a hack to squeeze the ranked tensors rank,
-- with its extra @n@ parameter, into the 'IsPrimal' class and assert it
-- for all @n@ values. A similar hack with @TensorOf@ wouldn't work,
-- because instances of type families are illegal.
class IsPrimalR r where
  dZeroR :: KnownNat n => Dual (OR.Array n r)
  dScaleR :: KnownNat n
          => OR.Array n r -> Dual (OR.Array n r) -> Dual (OR.Array n r)
  dAddR :: KnownNat n
        => Dual (OR.Array n r) -> Dual (OR.Array n r)
        -> Dual (OR.Array n r)
  recordSharingR :: Dual (OR.Array n r) -> Dual (OR.Array n r)
  packDeltaDtR :: KnownNat n
               => Either (r, OR.Array n r) (OR.Array n r) -> Dual (OR.Array n r)
               -> DeltaDt r

-- | Part 2/2 of a hack to squeeze the ranked tensors rank,
-- with its extra @n@ parameter, into the 'IsPrimal' class.
instance (IsPrimalR r, KnownNat n)
         => IsPrimal (OR.Array n r) where
  dZero = dZeroR
  dScale = dScaleR
  dAdd = dAddR
  recordSharing = recordSharingR
  packDeltaDt = packDeltaDtR

-- An analogous hack for Ast.
class IsPrimalA r where
  dZeroA :: KnownNat n => Dual (Ast n r)
  dScaleA :: KnownNat n
          => Ast n r -> Dual (Ast n r) -> Dual (Ast n r)
  dAddA :: KnownNat n
        => Dual (Ast n r) -> Dual (Ast n r) -> Dual (Ast n r)
  recordSharingA :: Dual (Ast n r) -> Dual (Ast n r)
  packDeltaDtA :: KnownNat n
               => Either (AstScalar r, Ast n r) (Ast n r) -> Dual (Ast n r)
               -> DeltaDt (AstScalar r)

instance (IsPrimalA r, KnownNat n)
         => IsPrimal (Ast n r) where
  dZero = dZeroA
  dScale = dScaleA
  dAdd = dAddA
  recordSharing = recordSharingA
  packDeltaDt = packDeltaDtA

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first parameter.
class HasRanks r where
  dInput0 :: InputId r -> Dual r
  dIndex0 :: KnownNat n
          => Dual (TensorOf n r) -> IndexOf n r -> ShapeInt n -> Dual r
  dSum0 :: KnownNat n
        => ShapeInt n -> Dual (TensorOf n r) -> Dual r
  dDot0 :: KnownNat n
        => TensorOf n r -> Dual (TensorOf n r) -> Dual r
  dUnScalar0 :: Dual (TensorOf 0 r) -> Dual r

  dInput1 :: InputId (TensorOf n r) -> Dual (TensorOf n r)
--  dIndexZ1 :: KnownNat n
--         => Dual (TensorOf (1 + n) r) -> Int -> Int -> Dual (TensorOf n r)
  dIndexZ :: (KnownNat n, KnownNat m)
          => Dual (TensorOf (m + n) r) -> IndexOf m r -> ShapeInt (m + n)
          -> Dual (TensorOf n r)
  dSum1 :: KnownNat n
        => Int -> Dual (TensorOf (1 + n) r) -> Dual (TensorOf n r)
  dScalar1 :: Dual r -> Dual (TensorOf 0 r)
  dFromList1 :: KnownNat n
             => [Dual (TensorOf n r)]
             -> Dual (TensorOf (1 + n) r)
  dFromVector1 :: KnownNat n
               => Data.Vector.Vector (Dual (TensorOf n r))
               -> Dual (TensorOf (1 + n) r)
--  dFromList01 :: KnownNat n
--              => ShapeInt n -> [Dual r] -> Dual (TensorOf n r)
--  dFromVector01 :: KnownNat n
--                => ShapeInt n -> Data.Vector.Vector (Dual r)
--                -> Dual (TensorOf n r)
  dKonst1 :: KnownNat n
          => Int -> Dual (TensorOf n r) -> Dual (TensorOf (1 + n) r)
--  dKonst01 :: KnownNat n
--           => ShapeInt n -> Dual r -> Dual (TensorOf n r)
  dAppend1 :: KnownNat n
           => Dual (TensorOf (1 + n) r) -> Int -> Dual (TensorOf (1 + n) r)
           -> Dual (TensorOf (1 + n) r)
  dSlice1 :: KnownNat n
          => Int -> Int -> Dual (TensorOf (1 + n) r) -> Int
          -> Dual (TensorOf (1 + n) r)
  dReverse1 :: KnownNat n
            => Dual (TensorOf (1 + n) r) -> Dual (TensorOf (1 + n) r)
  dTranspose1 :: KnownNat n
              => Permutation -> Dual (TensorOf n r) -> Dual (TensorOf n r)
  dReshape1 :: (KnownNat n, KnownNat m)
            => ShapeInt n -> ShapeInt m -> Dual (TensorOf n r)
            -> Dual (TensorOf m r)
  dBuild1 :: KnownNat n
          => Int -> (IntOf r -> Dual (TensorOf n r))
          -> Dual (TensorOf (1 + n) r)
--  dGatherZ1 :: (KnownNat p, KnownNat n)
--           => (Int -> IndexOf p r)
--           -> ShapeInt (p + n) -> Dual (TensorOf (p + n) r)
--           -> Int -> Dual (TensorOf (1 + n) r)
  dGatherZ :: (KnownNat m, KnownNat p, KnownNat n)
           => ShapeInt (m + n) -> Dual (TensorOf (p + n) r)
           -> (IndexOf m r -> IndexOf p r)
           -> ShapeInt (p + n)
           -> Dual (TensorOf (m + n) r)
--  dScatterZ1 :: (KnownNat p, KnownNat n)
--            => (Int -> IndexOf p r)
--            -> Int -> Dual (TensorOf (1 + n) r)
--            -> ShapeInt (p + n) -> Dual (TensorOf (p + n) r)
  dScatterZ :: (KnownNat m, KnownNat p, KnownNat n)
            => ShapeInt (p + n) -> Dual (TensorOf (m + n) r)
            -> (IndexOf m r -> IndexOf p r)
            -> ShapeInt (m + n)
            -> Dual (TensorOf (p + n) r)

  dFromX1 :: KnownNat n
          => Dual (DynamicTensor r) -> Dual (TensorOf n r)

  dFrom1X :: KnownNat n
          => Dual (TensorOf n r) -> Dual (DynamicTensor r)

-- * Backprop gradient method instances

-- | This is an impure
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
instance IsPrimal Double where
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  recordSharing d = case d of
    Zero0 -> d
    Input0{} -> d
    Let0{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta0 d
  packDeltaDt et = DeltaDt0 (either fst id et)

-- | This is an impure instance. See above.
instance IsPrimal Float where
  -- Identical as above:
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  recordSharing d = case d of
    Zero0 -> d
    Input0{} -> d
    Let0{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta0 d
  packDeltaDt et = DeltaDt0 (either fst id et)

instance IsPrimal (AstScalar r) where
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  recordSharing d = case d of
    Zero0 -> d
    Input0{} -> d
    Let0{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta0 d
  packDeltaDt et = DeltaDt0 (either fst id et)

-- | This is a trivial and so a pure instance.
instance IsPrimal (OT.Array r) where
  dZero = undefined
  dScale = undefined
  dAdd = undefined
  recordSharing = id
  packDeltaDt = undefined

-- | This is an impure instance. See above.
instance IsPrimalR Double where
  dZeroR = Zero1
  dScaleR = Scale1
  dAddR = Add1
  recordSharingR d = case d of
    Zero1 -> d
    Input1{} -> d
    FromX1{} -> d
    Let1{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta1 d
  packDeltaDtR (Left (r, tsh)) = DeltaDt1 (tkonst0N (tshape tsh) (tscalar r))
  packDeltaDtR (Right t) = DeltaDt1 t

instance IsPrimalR Float where
  dZeroR = Zero1
  dScaleR = Scale1
  dAddR = Add1
  recordSharingR d = case d of
    Zero1 -> d
    Input1{} -> d
    FromX1{} -> d
    Let1{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta1 d
  packDeltaDtR (Left (r, tsh)) = DeltaDt1 (tkonst0N (tshape tsh) (tscalar r))
  packDeltaDtR (Right t) = DeltaDt1 t

-- TODO: should this manage sharing of the terms?
instance (Show r, Numeric r, Tensor (AstScalar r)) => IsPrimalA r where
  dZeroA = Zero1
  dScaleA = Scale1
  dAddA = Add1
  recordSharingA d = case d of
    Zero1 -> d
    Input1{} -> d
    FromX1{} -> d
    Let1{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDelta1 d
  packDeltaDtA (Left (r, tsh)) = DeltaDt1 (tkonst0N (tshape tsh) (tscalar r))
  packDeltaDtA (Right t) = DeltaDt1 t

instance IsPrimal (AstDynamic r) where
  dZero = undefined
  dScale = undefined
  dAdd (From1X @n1 d1) (From1X @n2 d2) = case sameNat (Proxy @n1) (Proxy @n2) of
    Just Refl -> From1X $ Add1 d1 d2
    _ -> error "dAdd (IsPrimal (AstDynamic r)): summand types don't match"
  recordSharing = id
  packDeltaDt = undefined

-- | This is an impure instance. See above.
instance HasRanks Double where
  dInput0 = Input0
  dIndex0 = Index0
  dSum0 = Sum0
  dDot0 = Dot0
  dUnScalar0 = UnScalar0

  dInput1 = Input1
--  dIndex1 = Index1
  dIndexZ = IndexZ
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
  dGatherZ = GatherZ
--  dScatter1 = Scatter1
  dScatterZ = ScatterZ

  dFromX1 = FromX1

  dFrom1X = From1X

instance HasRanks Float where
  dInput0 = Input0
  dIndex0 = Index0
  dSum0 = Sum0
  dDot0 = Dot0
  dUnScalar0 = UnScalar0

  dInput1 = Input1
--  dIndex1 = Index1
  dIndexZ = IndexZ
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
  dGatherZ = GatherZ
--  dScatter1 = Scatter1
  dScatterZ = ScatterZ

  dFromX1 = FromX1

  dFrom1X = From1X

instance (Show r, Numeric r) => HasRanks (AstScalar r) where
  dInput0 = Input0
  dIndex0 = Index0
  dSum0 = Sum0
  dDot0 = Dot0
  dUnScalar0 = UnScalar0

  dInput1 = Input1
--  dIndex1 = Index1
  dIndexZ = IndexZ
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
  dGatherZ = GatherZ
--  dScatter1 = Scatter1
  dScatterZ = ScatterZ

  dFromX1 = FromX1

  dFrom1X = From1X

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
