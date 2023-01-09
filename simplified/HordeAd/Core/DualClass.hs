{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, StandaloneDeriving, TypeFamilyDependencies,
             UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
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
    ADVal, dD, dDnotShared
  , ADMode(..), ADModeAndNum
  , IntOf, VectorOf
  , -- * The less often used part of the mid-level API that gets re-exported in high-level API; it leaks implementation details
    pattern D
  , IsPrimal(..), IsPrimalAndHasFeatures, IsPrimalAndHasInputs, HasDelta
  , Element, HasPrimal(..)
  , VectorLike(..), ADReady
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), HasInputs(..), dummyDual
  , -- * Internal operations, exposed for tests, debugging and experiments
    unsafeGetFreshId
  ) where

import Prelude

import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.MonoTraversable (Element, MonoFunctor)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Show.Functions ()

import HordeAd.Core.Ast
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

deriving instance (Show a, Show (Dual d a)) => Show (ADVal d a)

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
  (IsPrimal d a, MonoFunctor a, Element a ~ r)

-- | A shorthand for a useful set of constraints.
type IsPrimalAndHasFeatures (d :: ADMode) a r =
  (IsPrimalWithScalar d a r, RealFloat a)

-- | A shorthand for a useful set of constraints.
type IsPrimalAndHasInputs (d :: ADMode) a r =
  (IsPrimalAndHasFeatures d a r, HasInputs a)

-- | A mega-shorthand for a bundle of connected type constraints.
-- The @Scalar@ in the name means that the second argument is the underlying
-- scalar type of a well behaved (wrt the differentiation mode in the first
-- argument) collection of primal and dual components of dual numbers.
type ADModeAndNum (d :: ADMode) r =
  ( Numeric r
  , Show r
  , HasPrimal r
  , HasRanks (Vector r) d r
  , IsPrimalAndHasFeatures d r r
  , IsPrimalAndHasFeatures d (Vector r) r
  , IntOf r ~ Int
  )

-- | Is a scalar and will be used to compute gradients via delta-expressions.
type HasDelta r = ( ADModeAndNum 'ADModeGradient r
                  , HasInputs r
                  , Dual 'ADModeGradient r ~ Delta0 r )


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
  Dual 'ADModeGradient (Vector r) = Delta1 r
-- not injective:  Dual 'ADModeDerivative r = r
  Dual 'ADModeDerivative Double = Double
  Dual 'ADModeDerivative Float = Float
  Dual 'ADModeDerivative (Vector r) = Vector r
  Dual 'ADModeValue a = DummyDual a 'ADModeValue

-- A bit more verbose, but a bit faster than @data@, perhaps by chance.
newtype DummyDual r (d :: ADMode) = DummyDual ()
  deriving Show

dummyDual :: DummyDual r d
dummyDual = DummyDual ()

type family IntOf a where
  IntOf Double = Int
  IntOf Float = Int
  IntOf (Vector r) = Int
  IntOf (Ast r a) = AstInt r
  IntOf (ADVal d r) = Int

type family VectorOf a = result | result -> a where
  VectorOf Double = Vector Double
  VectorOf Float = Vector Float
  VectorOf (Ast r r) = Ast r (Vector r)
  VectorOf (ADVal d r) = ADVal d (Vector r)

-- We could accept any @RealFloat@ instead of @PrimalOf a@, but then
-- we'd need to coerce, e.g., via realToFrac, which is risky and lossy.
-- Also, the stricter typing is likely to catch real errors most of the time,
-- not just sloppy omission of explitic coercions.
class HasPrimal a where
  type PrimalOf a
  type DualOf a
  constant :: PrimalOf a -> a
  scale :: Num (PrimalOf a) => PrimalOf a -> a -> a
  primalPart :: a -> PrimalOf a
  dualPart :: a -> DualOf a
  ddD :: PrimalOf a -> DualOf a -> a
  -- TODO: we'd probably also need dZero, dIndex10 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?
  --
  -- Unrelated, but no better home ATM:
  fromIntOf :: IntOf a -> a

class VectorOf r ~ vector => VectorLike vector r | vector -> r where
  llength :: vector -> IntOf r
  lminIndex :: vector -> IntOf r
  lmaxIndex :: vector -> IntOf r

  lsumElements10 :: vector -> r
  lindex10 :: vector -> IntOf r -> r
  lminimum0 :: vector -> r
  lmaximum0 :: vector -> r
  ldot0 :: vector -> vector -> r

  lfromList1 :: [r] -> vector
  lfromVector1 :: Data.Vector.Vector r -> vector
  lkonst1 :: r -> IntOf r -> vector
  lappend1 :: vector -> vector -> vector
  lslice1 :: IntOf r -> IntOf r -> vector -> vector
  lreverse1 :: vector -> vector
  lbuild1 :: IntOf r -> (IntOf r -> r) -> vector
  lmap1 :: (r -> r) -> vector -> vector

type ADReady r =
  ( RealFloat r, HasPrimal r, HasPrimal (VectorOf r), VectorLike (VectorOf r) r
  , Integral (IntOf r), Fractional (VectorOf r) )

-- | Second argument is the primal component of a dual number at some rank
-- wrt the differentiation mode given in the first argument.
class IsPrimal d a where
  dZero :: Dual d a
  dScale :: a -> Dual d a -> Dual d a
  dAdd :: Dual d a -> Dual d a -> Dual d a
  recordSharing :: Dual d a -> Dual d a

-- | Assuming that the type argument is the primal component of dual numbers
-- with differentiation mode `ADModeGradient`, this class makes available
-- the additional operations of delta-input and of packing a delta expression
-- and a dt parameter for computing its gradient.
class HasInputs a where
  dInput :: InputId a -> Dual 'ADModeGradient a
  packDeltaDt :: a -> Dual 'ADModeGradient a -> DeltaDt (Element a)

-- The constraint has Element in addition to VectorOf,
-- because vector is more often determined, while r remains unknown.
-- For the same reason, IntOf vector works, but IntOf r doesn't.
-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first parameter.
class (Element vector ~ r, VectorOf r ~ vector)
      => HasRanks vector (d :: ADMode) r | vector -> r where
  dSumElements10 :: Dual d vector -> IntOf vector -> Dual d r
  dIndex10 :: Dual d vector -> IntOf vector -> IntOf vector -> Dual d r
  dDot0 :: vector -> Dual d vector -> Dual d r

  dFromList1 :: [Dual d r] -> Dual d vector
  dFromVector1 :: Data.Vector.Vector (Dual d r) -> Dual d vector
  dKonst1 :: Dual d r -> IntOf vector -> Dual d vector
  dAppend1 :: Dual d vector -> IntOf vector -> Dual d vector -> Dual d vector
  dSlice1 :: IntOf vector -> IntOf vector -> Dual d vector -> IntOf vector
          -> Dual d vector
  dReverse1 :: Dual d vector -> Dual d vector
  dBuild1 :: IntOf vector -> (IntOf vector -> Dual d r) -> Dual d vector


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

instance HasInputs Double where
  dInput = Input0
  packDeltaDt = DeltaDt0

instance HasInputs Float where
  dInput = Input0
  packDeltaDt = DeltaDt0

instance HasInputs (Vector r) where
  dInput = Input1
  packDeltaDt = DeltaDt1

-- | This is an impure instance. See above.
instance (Dual 'ADModeGradient r ~ Delta0 r, VectorOf r ~ Vector r)
         => HasRanks (Vector r) 'ADModeGradient r where
  dSumElements10 = SumElements10
  dIndex10 = Index10
  dDot0 = Dot0
  dFromList1 = FromList1
  dFromVector1 = FromVector1
  dKonst1 = Konst1
  dAppend1 = Append1
  dSlice1 = Slice1
  dReverse1 = Reverse1
  dBuild1 = Build1


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

instance Num (Vector r)
         => IsPrimal 'ADModeDerivative (Vector r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  recordSharing = id

instance ( Numeric r, VectorOf r ~ Vector r
         , Dual 'ADModeDerivative r ~ r )
         => HasRanks (Vector r) 'ADModeDerivative r where
  dSumElements10 vd _ = LA.sumElements vd
  dIndex10 d ix _ = d V.! ix
  dDot0 = (LA.<.>)
  dFromList1 = V.fromList
  dFromVector1 = V.convert
  dKonst1 = LA.konst
  dAppend1 d _k e = d V.++ e
  dSlice1 i n d _len = V.slice i n d
  dReverse1 = V.reverse
  dBuild1 n f = V.fromList $ map f [0 .. n - 1]


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

-- This requires UndecidableInstances.
instance (Element vector ~ r, VectorOf r ~ vector)
         => HasRanks vector 'ADModeValue r where
  dSumElements10 _ _ = DummyDual ()
  dIndex10 _ _ _ = DummyDual ()
  dDot0 _ _ = DummyDual ()
  dFromList1 _ = DummyDual ()
  dFromVector1 _ = DummyDual ()
  dKonst1 _ _ = DummyDual ()
  dAppend1 _ _ _ = DummyDual ()
  dSlice1 _ _ _ _ = DummyDual ()
  dReverse1 _ = DummyDual ()
  dBuild1 _ _ = DummyDual ()


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

wrapDelta1 :: Delta1 r -> Delta1 r
{-# NOINLINE wrapDelta1 #-}
wrapDelta1 !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Let1 (NodeId n) d
