{-# LANGUAGE UndecidableInstances #-}
-- | The class relating the primal datatype to its dual counterpart
-- and the instances of the class for all kinds it's going to be use at
-- (@Nat@ and @[Nat]@). This class abstract over some of the operations
-- involving primal and dual components of dual numbers, most importantly
-- the @Share@ operations for sharing delta expressions, regardless
-- of the typing of the tensors being used (ranked vs shaped).
--
-- This module uses and rather safely encapsulates impure side-effects.
-- The impurity produces pure data with a particular property.
-- The property is an order of per-node integer identifiers that represents
-- data dependencies and sharing between delta expressions. The low-level API
-- depends on this property, but is completely isolated from the impurity.
-- The high-level API triggers the impurity but can't observe
-- any impure behaviour. Neither can any other module in the package,
-- except for the testing modules that import testing-exclusive class instances
-- and operations for reading or reseting the impure counter.
module HordeAd.Core.IsPrimal
  ( Dual, IsPrimal(..)
  , unsafeGetFreshId, resetIdCounter, wrapDelta
  ) where

import Prelude

import Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter, writeIORefU)
import Data.Kind (Constraint, Type)
import GHC.TypeLits (KnownNat, Nat)
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested (KnownShX)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.Delta
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

-- | The type family that to each dfferentiable type assigns
-- its delta expression type. The dispatch is on the type parameter @ty@,
-- which is 'Nat', @[Nat]@ or @()@, respectively.
type Dual :: TensorType ty -> TensorType ty
type family Dual f r z = result | result -> f r z where
  Dual ranked r z = DeltaR ranked r z
  Dual shaped r z = DeltaS shaped r z
  Dual mixed r z = DeltaX mixed r z
  Dual (HVectorPseudoTensor ranked) r z = HVectorPseudoTensor (DeltaR ranked) r z


-- * The IsPrimal class and its instances

-- | The class states that @f r z@ type is the primal component
-- of a dual number as exeplified by the operations.
--
-- The OfShape hacks are needed to recover shape from ranked tensors,
-- in particular in case of numeric literals and also for forward derivative.
type IsPrimal :: TensorType ty -> Type -> ty -> Constraint
class IsPrimal f r z where
  dZeroOfShape :: f r z -> Dual f r z
  dScale :: f r z -> Dual f r z -> Dual f r z
  dAdd :: Dual f r z -> Dual f r z -> Dual f r z
  intOfShape :: f r z -> Int -> f r z
  sharePrimal :: f r z -> f r z  -- impure
  shareDual :: Dual f r z -> Dual f r z

-- | The instances are impure, because 'shareDual'
-- adorns terms with an @Int@ identifier from a counter that is afterwards
-- incremented (and never changed in any other way).
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
-- The pattern-matching in 'shareDual' is a crucial optimization
-- and it could, presumably, be extended to further limit which
-- terms get an identifier. Alternatively, 'HordeAd.Core.DualNumber.dD'
-- or library definitions that use it could be made smarter.
instance ( GoodScalar r, KnownNat n, RankedTensor ranked, ShareTensor ranked
         , ProductTensor ranked )
         => IsPrimal @Nat ranked r n where
  dZeroOfShape tsh = DeltaR $ ZeroR (rshape tsh)
  dScale _ (DeltaR (ZeroR sh)) = DeltaR $ ZeroR sh
  dScale v (DeltaR u') = DeltaR $ ScaleR v u'
  dAdd (DeltaR ZeroR{}) w = w
  dAdd v (DeltaR ZeroR{}) = v
  dAdd (DeltaR v) (DeltaR w) = DeltaR $ AddR v w
  intOfShape tsh c = rconst $ Nested.rreplicateScal (rshape tsh) (fromIntegral c)
  sharePrimal = tshare
  shareDual d = DeltaR $ wrapDelta (unDeltaR d)

instance ( GoodScalar r, KnownShS sh, ShapedTensor shaped
         , ShareTensor (RankedOf shaped), ProductTensor (RankedOf shaped) )
         => IsPrimal @[Nat] shaped r sh where
  dZeroOfShape _tsh = DeltaS ZeroS
  dScale _ (DeltaS ZeroS) = DeltaS ZeroS
  dScale v (DeltaS u') = DeltaS $ ScaleS v u'
  dAdd (DeltaS ZeroS) w = w
  dAdd v (DeltaS ZeroS) = v
  dAdd (DeltaS v) (DeltaS w) = DeltaS $ AddS v w
  intOfShape tsh c =  -- not needed for shaped, here, but ranked above needs it,
                      -- so we have to use it for both
    sconst $ Nested.sreplicateScal (sshape tsh) (fromIntegral c)
  sharePrimal = tshare
  shareDual d = DeltaS $ wrapDelta (unDeltaS d)

instance ( GoodScalar r, KnownShX sh, mixed ~ MixedOf (RankedOf mixed)
         , RankedTensor (RankedOf mixed)
         , ShareTensor (RankedOf mixed), ProductTensor (RankedOf mixed) )
         => IsPrimal @[Maybe Nat] mixed r sh where
  dZeroOfShape tsh = DeltaX $ ZeroX (xshape tsh)
  dScale _ (DeltaX (ZeroX sh)) = DeltaX (ZeroX sh)
  dScale v (DeltaX u') = DeltaX $ ScaleX v u'
  dAdd (DeltaX ZeroX{}) w = w
  dAdd v (DeltaX ZeroX{}) = v
  dAdd (DeltaX v) (DeltaX w) = DeltaX $ AddX v w
  intOfShape tsh c =
    xconst $ Nested.mreplicateScal (xshape tsh) (fromIntegral c)
  sharePrimal = tshare
  shareDual d = DeltaX $ wrapDelta (unDeltaX d)


-- * Counter handling

unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 100000001)

-- | Do not use; this is exposed only for special low level tests.
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

-- Only for tests, e.g., to ensure show applied to terms has stable length.
-- Tests using this need to be run with -ftest_seq to avoid variable confusion.
resetIdCounter :: IO ()
resetIdCounter = writeIORefU unsafeGlobalCounter 100000001

-- Tests don't show a speedup from `unsafeDupablePerformIO`,
-- perhaps due to counter gaps that it may introduce.
wrapDelta :: TensorKind y => Delta ranked y -> Delta ranked y
{-# NOINLINE wrapDelta #-}
wrapDelta d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! case d of
    ZeroR{} -> d
    -- SFromR{} -> d
    -- the term inside SFromR is most likely shared already, but are we sure?
    ZeroS -> d
    ZeroX{} -> d
    InputG{} -> d
    ShareG{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> ShareG (NodeId n) d
