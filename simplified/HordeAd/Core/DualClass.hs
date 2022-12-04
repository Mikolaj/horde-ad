{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances, GADTs,
             MultiParamTypeClasses, PolyKinds, QuantifiedConstraints,
             TypeFamilyDependencies #-}
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
    ADVal, pattern D, dD, dDnotShared
  , ADMode(..), ADModeAndNum
  , -- * The less often used part of the mid-level API that gets re-exported in high-level API; it leaks implementation details
    IsPrimal(..), IsPrimalAndHasFeatures, HasDelta
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), HasInputs(..), dummyDual
  , -- * Internal operations, exposed for tests, debugging and experiments
    unsafeGetFreshId, Ast(..), AstInt(..), CodeOut(..), RelOut(..)
  ) where

import Prelude

import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.MonoTraversable (Element, MonoFunctor)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
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
  ( IsPrimalWithScalar d a r, IsPrimalWithScalar d (Ast d r) (Ast d r)
  , HasInputs a, RealFloat a, MonoFunctor a, Element a ~ r )

-- | A mega-shorthand for a bundle of connected type constraints.
-- The @Scalar@ in the name means that the second argument is the underlying
-- scalar type of a well behaved (wrt the differentiation mode in the first
-- argument) collection of primal and dual components of dual numbers.
type ADModeAndNum (d :: ADMode) r =
  ( HasRanks d r, Ord r, Numeric r, Show r
  , IsPrimalAndHasFeatures d r r
  , IsPrimalAndHasFeatures d (Vector r) r
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
  Dual 'ADModeGradient (Ast 'ADModeGradient a) =
    DummyDual 'ADModeGradient a
  Dual 'ADModeGradient (Vector r) = Delta1 r
-- not injective:  Dual 'ADModeDerivative r = r
  Dual 'ADModeDerivative Double = Double
  Dual 'ADModeDerivative Float = Float
  Dual 'ADModeDerivative (Ast 'ADModeDerivative a) =
    DummyDual 'ADModeDerivative a
  Dual 'ADModeDerivative (Vector r) = Vector r
  Dual 'ADModeValue a = DummyDual 'ADModeValue a

-- A bit more verbose, but a bit faster than @data@, perhaps by chance.
newtype DummyDual (d :: ADMode) a = DummyDual ()

dummyDual :: DummyDual d a
dummyDual = DummyDual ()

-- | The underlying scalar of a given primal component of a dual number.
-- A long name to remember not to use, unless necessary, and not to export.
type family ScalarOf a where
  ScalarOf Double = Double
  ScalarOf Float = Float
  ScalarOf (Ast d a) = (Ast d a)
  ScalarOf (Vector r) = r

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
  packDeltaDt :: a -> Dual 'ADModeGradient a -> DeltaDt (ScalarOf a)

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first parameter.
class HasRanks (d :: ADMode) r where
  dSumElements0 :: Dual d (Vector r) -> Int -> Dual d r
  dIndex10 :: Dual d (Vector r) -> Int -> Int -> Dual d r
  dDot0 :: Vector r -> Dual d (Vector r) -> Dual d r

  dFromList1 :: [Dual d r] -> Dual d (Vector r)
  dFromVector1 :: Data.Vector.Vector (Dual d r) -> Dual d (Vector r)
  dKonst1 :: Dual d r -> Int -> Dual d (Vector r)
  dAppend1 :: Dual d (Vector r) -> Int -> Dual d (Vector r) -> Dual d (Vector r)
  dSlice1 :: Int -> Int -> Dual d (Vector r) -> Int -> Dual d (Vector r)
  dReverse1 :: Dual d (Vector r) -> Dual d (Vector r)
  dBuild1 :: Int -> (Int -> Dual d r) -> Dual d (Vector r)


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

instance IsPrimal 'ADModeGradient (Ast 'ADModeGradient a) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing _ = DummyDual ()

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
instance Dual 'ADModeGradient r ~ Delta0 r
         => HasRanks 'ADModeGradient r where
  dSumElements0 = SumElements0
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

instance IsPrimal 'ADModeDerivative (Ast 'ADModeDerivative a) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing _ = DummyDual ()

instance Num (Vector r)
         => IsPrimal 'ADModeDerivative (Vector r) where
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  recordSharing = id

instance ( Numeric r
         , Dual 'ADModeDerivative r ~ r )
         => HasRanks 'ADModeDerivative r where
  dSumElements0 vd _ = LA.sumElements vd
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

instance IsPrimal 'ADModeValue (Ast 'ADModeValue a) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing _ = DummyDual ()

instance IsPrimal 'ADModeValue (Vector r) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing = id

instance HasRanks 'ADModeValue r where
  dSumElements0 _ _ = DummyDual ()
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


-- * Definitions for the fake scalar Ast

-- TODO: GADT this so that the variables can't be mixed up and/or split
-- into mutually recursive types
-- | @Ast@ is a fake scalar imitating a real scalar @r@. It builds up
-- an AST instead of reducing @r@ arithmetic operations to their results.
data Ast (d :: ADMode) a =
    AstOp CodeOut [Ast d a]
  | AstRel RelOut [Ast d a]
  | AstIndex (Ast d (Vector a)) AstInt
  | AstCond AstBool (Ast d a) (Ast d a)
  | AstConst (ADVal d a)
  | AstVar String  -- instantiated to @r@

data AstInt =
    AstIntOp CodeOut [AstInt]
  | AstIntConst Int
  | AstIntVar String  -- instantiated to @Int@

data AstBool  -- TODO

-- deriving instance (Show a, Numeric a) => Show (Ast a)

-- @Out@ is a leftover from the outlining mechanism deleted in
-- https://github.com/Mikolaj/horde-ad/commit/c59947e13082c319764ec35e54b8adf8bc01691f
data CodeOut =
    PlusOut | MinusOut | TimesOut | NegateOut | AbsOut | SignumOut
  | DivideOut | RecipOut
  | ExpOut | LogOut | SqrtOut | PowerOut | LogBaseOut
  | SinOut | CosOut | TanOut | AsinOut | AcosOut | AtanOut
  | SinhOut | CoshOut | TanhOut | AsinhOut | AcoshOut | AtanhOut
  | Atan2Out
  | MaxOut | MinOut
  deriving Show

data RelOut =
    EqOut | Neq
  | LeqOut| GeqOut | LOut | GOut

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (Ast d a) where

instance Ord (Ast d a) where

instance (Num a, IsPrimal d a) => Num (Ast d a) where
  u + v = AstOp PlusOut [u, v]
  u - v = AstOp MinusOut [u, v]
  u * v = AstOp TimesOut [u, v]
  negate u = AstOp NegateOut [u]
  abs v = AstOp AbsOut [v]
  signum v = AstOp SignumOut [v]
  fromInteger k = AstConst (D (fromInteger k) dZero)

instance (Real a, IsPrimal d a) => Real (Ast d a) where
  toRational = undefined  -- TODO?

-- The rest TODO.
instance (Fractional a, IsPrimal d a) => Fractional (Ast d a) where
instance (Floating a, IsPrimal d a) => Floating (Ast d a) where
instance (RealFrac a, IsPrimal d a) => RealFrac (Ast d a) where
instance (RealFloat a, IsPrimal d a) => RealFloat (Ast d a) where

instance Num AstInt where
  u + v = AstIntOp PlusOut [u, v]
  u - v = AstIntOp MinusOut [u, v]
  u * v = AstIntOp TimesOut [u, v]
  negate u = AstIntOp NegateOut [u]
  abs v = AstIntOp AbsOut [v]
  signum v = AstIntOp SignumOut [v]
  fromInteger = AstIntConst . fromInteger
