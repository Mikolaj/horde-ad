{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances, GADTs,
             MultiParamTypeClasses, PolyKinds, QuantifiedConstraints,
             StandaloneDeriving, TypeFamilyDependencies,
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
    ADVal, pattern D, dD, dDnotShared
  , ADMode(..), ADModeAndNum, ADModeAndNumNew, IsVectorWithScalar
  , -- * The less often used part of the mid-level API that gets re-exported in high-level API; it leaks implementation details
    IsPrimal(..), IsPrimalAndHasFeatures, IsPrimalAndHasInputs, HasDelta
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), HasInputs(..), NumOf, dummyDual
  , -- * Internal operations, exposed for tests, debugging and experiments
    unsafeGetFreshId
  , VectorLike(..), Ast(..), AstVarName(..), AstVar(..), AstInt(..), AstBool(..)
  , CodeOut(..), CodeIntOut(..), CodeBoolOut(..), RelOut(..)
  ) where

import Prelude

import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Numeric.LinearAlgebra.Data (arctan2)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Show.Functions ()

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
  ( Numeric r, Show r
  , HasRanks (Vector r) d r
  , HasRanks (Ast r d (Vector r)) d (Ast r d r)
  , IsPrimalAndHasFeatures d r r
  , IsPrimalAndHasFeatures d (Ast r d r) (Ast r d r)
  , IsPrimalAndHasFeatures d (Vector r) r
  , IsPrimalAndHasFeatures d (Ast r d (Vector r)) (Ast r d r)
  )

type ADModeAndNumNew (d :: ADMode) r = IsPrimalAndHasFeatures d r r

-- | A shorthand for a useful set of constraints.
type IsVectorWithScalar (d :: ADMode) v r =
  ( IsPrimalAndHasFeatures d r r, IsPrimalAndHasFeatures d v r, HasRanks v d r
  , VectorLike v )

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
  Dual 'ADModeGradient (Ast r 'ADModeGradient a) =
    DummyDual r 'ADModeGradient a
  Dual 'ADModeGradient (Vector r) = Delta1 r
-- not injective:  Dual 'ADModeDerivative r = r
  Dual 'ADModeDerivative Double = Double
  Dual 'ADModeDerivative Float = Float
  Dual 'ADModeDerivative (Ast r 'ADModeDerivative a) =
    DummyDual r 'ADModeDerivative a
  Dual 'ADModeDerivative (Vector r) = Vector r
  Dual 'ADModeValue a = DummyDual a 'ADModeValue a

-- A bit more verbose, but a bit faster than @data@, perhaps by chance.
newtype DummyDual r (d :: ADMode) a = DummyDual ()
  deriving Show

dummyDual :: DummyDual a d a
dummyDual = DummyDual ()

type family NumOf a where
  NumOf Double = Int
  NumOf Float = Int
  NumOf (Vector r) = Int
  NumOf (Ast r d a) = AstInt r d

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

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first parameter.
class Element vector ~ r => HasRanks vector (d :: ADMode) r where
  dSumElements10 :: Dual d vector -> NumOf vector -> Dual d r
  dIndex10 :: Dual d vector -> NumOf vector -> NumOf vector -> Dual d r
  dDot0 :: vector -> Dual d vector -> Dual d r

  dFromList1 :: [Dual d r] -> Dual d vector
  dFromVector1 :: Data.Vector.Vector (Dual d r) -> Dual d vector
  dKonst1 :: Dual d r -> NumOf vector -> Dual d vector
  dAppend1 :: Dual d vector -> NumOf vector -> Dual d vector -> Dual d vector
  dSlice1 :: NumOf vector -> NumOf vector -> Dual d vector -> NumOf vector
          -> Dual d vector
  dReverse1 :: Dual d vector -> Dual d vector
  dBuild1 :: NumOf vector -> (NumOf vector -> Dual d r) -> Dual d vector


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

instance IsPrimal 'ADModeGradient (Ast r 'ADModeGradient a) where
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

instance HasRanks (Ast r 'ADModeGradient (Vector r)) 'ADModeGradient
                  (Ast r 'ADModeGradient r) where
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

instance IsPrimal 'ADModeDerivative (Ast r 'ADModeDerivative a) where
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

instance HasRanks (Ast r 'ADModeDerivative (Vector r)) 'ADModeDerivative
                  (Ast r 'ADModeDerivative r) where
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

instance IsPrimal 'ADModeValue (Ast r 'ADModeValue a) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing _ = DummyDual ()

instance IsPrimal 'ADModeValue (Vector r) where
  dZero = DummyDual ()
  dScale _ _ = DummyDual ()
  dAdd _ _ = DummyDual ()
  recordSharing = id

instance Element vector ~ r => HasRanks vector 'ADModeValue r where
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


-- * Definitions for the Ast primal value wrapper

class VectorLike vector where
  llength :: vector -> NumOf vector
  lminElement :: vector -> Element vector
  lmaxElement :: vector -> Element vector
  lminIndex :: vector -> NumOf vector
  lmaxIndex :: vector -> NumOf vector
  lsumElements10 :: vector -> Element vector
  lindex10 :: vector -> NumOf vector -> Element vector
  lkonst1 :: Element vector -> NumOf vector -> vector
  lslice1 :: NumOf vector -> NumOf vector -> vector -> vector
  lfromList1 :: [Element vector] -> vector

instance Numeric r => VectorLike (Vector r) where
  llength = V.length
  lminElement = LA.minElement
  lmaxElement = LA.maxElement
  lminIndex = LA.minIndex
  lmaxIndex = LA.maxIndex
  lsumElements10 = LA.sumElements
  lindex10 = (V.!)
  lkonst1 = LA.konst
  lslice1 = V.slice
  lfromList1 = V.fromList

instance VectorLike (Ast r d (Vector r)) where
  llength = AstLength
  lminElement = AstMinElement
  lmaxElement = AstMaxElement
  lminIndex = AstMinIndex
  lmaxIndex = AstMaxIndex
  lsumElements10 = AstSumElements10
  lindex10 = AstIndex10
  lkonst1 = AstKonst1
  lslice1 = AstSlice1
  lfromList1 = AstFromList1

-- TODO: consider sharing Ast expressions, both within the primal part
-- and between primal and dual
-- | @Ast@ turns primal values and their operations into AST-building
-- counterparts.
data Ast :: Type -> ADMode -> Type -> Type where
  AstOp :: CodeOut -> [Ast r d a] -> Ast r d a
  AstCond :: AstBool r d -> Ast r d a -> Ast r d a -> Ast r d a
  AstConst :: a -> Ast r d a
  AstD :: ADVal d a -> Ast r d a

  AstVar :: AstVarName (ADVal d r) -> Ast r d r

  AstOMap1 :: (Ast r d r -> Ast r d r) -> Ast r d (Vector r)
           -> Ast r d (Vector r)  -- TODO: is the function OK? nope

  AstMinElement :: Ast r d (Vector r) -> Ast r d r
  AstMaxElement :: Ast r d (Vector r) -> Ast r d r

  AstSumElements10 :: Ast r d (Vector r) -> Ast r d r
  AstIndex10 :: Ast r d (Vector r) -> AstInt r d -> Ast r d r
  AstDot0 :: Ast r d (Vector r) -> Ast r d (Vector r) -> Ast r d r

  AstFromList1 :: [Ast r d r] -> Ast r d (Vector r)
  AstFromVector1 :: Data.Vector.Vector (Ast r d r) -> Ast r d (Vector r)
  AstKonst1 :: Ast r d r -> AstInt r d -> Ast r d (Vector r)
  AstAppend1 :: Ast r d (Vector r) -> Ast r d (Vector r) -> Ast r d (Vector r)
  AstSlice1 :: AstInt r d -> AstInt r d -> Ast r d (Vector r)
            -> Ast r d (Vector r)
  AstReverse1 :: Ast r d (Vector r) -> Ast r d (Vector r)
  AstBuild1 :: AstInt r d -> (AstVarName Int, Ast r d r) -> Ast r d (Vector r)
  AstMap1 :: (AstVarName (ADVal d r), Ast r d r) -> Ast r d (Vector r)
          -> Ast r d (Vector r)

newtype AstVarName t = AstVarName String
  deriving (Show, Eq)

data AstVar r d =
    AstVar0 (ADVal d r)
  | AstVarI Int

data AstInt :: Type -> ADMode -> Type where
  AstIntOp :: CodeIntOut -> [AstInt r d] -> AstInt r d
  AstIntCond :: AstBool r d -> AstInt r d -> AstInt r d -> AstInt r d
  AstIntConst :: Int -> AstInt r d
  AstIntVar :: AstVarName Int -> AstInt r d

  AstLength :: Ast r d (Vector r) -> AstInt r d
  AstMinIndex :: Ast r d (Vector r) -> AstInt r d
  AstMaxIndex :: Ast r d (Vector r) -> AstInt r d

data AstBool :: Type -> ADMode -> Type where
  AstBoolOp :: CodeBoolOut -> [AstBool r d] -> AstBool r d
  AstBoolConst :: Bool -> AstBool r d
  AstRel :: RelOut -> [Ast r d r] -> AstBool r d  -- TODO: Vector?
  AstRelInt :: RelOut -> [AstInt r d] -> AstBool r d

deriving instance ( Show a, Show r, Numeric r
                  , Show (ADVal d a), Show (ADVal d r)
                  , Show (ADVal d (Vector r))
                  , Show (AstInt r d), Show (AstBool r d) )
                  => Show (Ast r d a)

deriving instance (Show (ADVal d r), Show (ADVal d (Vector r)))
                  => Show (AstVar r d)

deriving instance ( Show r, Numeric r
                  , Show (ADVal d r)
                  , Show (ADVal d (Vector r))
                  , Show (AstInt r d), Show (AstBool r d) )
                  => Show (AstInt r d)

deriving instance ( Show r, Numeric r
                  , Show (ADVal d r)
                  , Show (ADVal d (Vector r))
                  , Show (AstInt r d), Show (AstBool r d) )
                  => Show (AstBool r d)

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

data CodeIntOut =
    PlusIntOut | MinusIntOut | TimesIntOut | NegateIntOut
  | AbsIntOut | SignumIntOut
  | MaxIntOut | MinIntOut
  deriving Show

data CodeBoolOut =
    NotOut | AndOut | OrOut | IffOut
  deriving Show

data RelOut =
    EqOut | NeqOut
  | LeqOut| GeqOut | LsOut | GtOut
  deriving Show


-- * Unlawful instances of AST types; they are lawful modulo evaluation

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (Ast r d a) where

instance Ord a => Ord (Ast r d a) where
  max u v = AstOp MaxOut [u, v]
  min u v = AstOp MinOut [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num a => Num (Ast r d a) where
  u + v = AstOp PlusOut [u, v]
  u - v = AstOp MinusOut [u, v]
  u * v = AstOp TimesOut [u, v]
  negate u = AstOp NegateOut [u]
  abs v = AstOp AbsOut [v]
  signum v = AstOp SignumOut [v]
  fromInteger = AstConst . fromInteger

instance Real a => Real (Ast r d a) where
  toRational = undefined  -- TODO?

instance Fractional a => Fractional (Ast r d a) where
  u / v = AstOp DivideOut  [u, v]
  recip v = AstOp RecipOut [v]
  fromRational = AstConst . fromRational

instance Floating a => Floating (Ast r d a) where
  pi = AstConst pi
  exp u = AstOp ExpOut [u]
  log u = AstOp LogOut [u]
  sqrt u = AstOp SqrtOut [u]
  u ** v = AstOp PowerOut [u, v]
  logBase u v = AstOp LogBaseOut [u, v]
  sin u = AstOp SinOut [u]
  cos u = AstOp CosOut [u]
  tan u = AstOp TanOut [u]
  asin u = AstOp AsinOut [u]
  acos u = AstOp AcosOut [u]
  atan u = AstOp AtanOut [u]
  sinh u = AstOp SinhOut [u]
  cosh u = AstOp CoshOut [u]
  tanh u = AstOp TanhOut [u]
  asinh u = AstOp AsinhOut [u]
  acosh u = AstOp AcoshOut [u]
  atanh u = AstOp AtanhOut [u]

instance RealFrac a => RealFrac (Ast r d a) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance RealFloat a => RealFloat (Ast r d a) where
  atan2 u v = AstOp Atan2Out [u, v]
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

instance Eq (AstInt r d) where

instance Ord (AstInt r d) where
  max u v = AstIntOp MaxIntOut [u, v]
  min u v = AstIntOp MinIntOut [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num (AstInt r d) where
  u + v = AstIntOp PlusIntOut [u, v]
  u - v = AstIntOp MinusIntOut [u, v]
  u * v = AstIntOp TimesIntOut [u, v]
  negate u = AstIntOp NegateIntOut [u]
  abs v = AstIntOp AbsIntOut [v]
  signum v = AstIntOp SignumIntOut [v]
  fromInteger = AstIntConst . fromInteger

type instance Element (Ast r d (Vector r)) = Ast r d r

type instance Element (Ast Double d Double) = Ast Double d Double

type instance Element (Ast Float d Float) = Ast Float d Float

instance MonoFunctor (Ast r d (Vector r)) where
  omap = AstOMap1

instance MonoFunctor (Ast Double d Double) where
  omap f = f

instance MonoFunctor (Ast Float d Float) where
  omap f = f


-- * Orphan instances

-- TODO: move to separate orphan module(s) at some point
-- This requires UndecidableInstances

instance (Num (Vector r), Numeric r, Ord r)
         => Real (Vector r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Num (Vector r), Numeric r, Fractional r, Ord r)
         => RealFrac (Vector r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance ( Floating (Vector r), Numeric r, RealFloat r )
         => RealFloat (Vector r) where
  atan2 = arctan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain

type instance Element Double = Double

type instance Element Float = Float

instance MonoFunctor Double where
  omap f = f

instance MonoFunctor Float where
  omap f = f
