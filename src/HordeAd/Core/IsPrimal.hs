{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}
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
  ( unsafeGetFreshId, resetIdCounter, shareDelta
  ) where

import Prelude

import Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter, writeIORefU)
import Data.Kind (Constraint, Type)
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat)
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested (KnownShX)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.Delta
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

-- | The instances are impure, because 'shareDelta'
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
-- The pattern-matching in 'shareDelta' is a crucial optimization
-- and it could, presumably, be extended to further limit which
-- terms get an identifier. Alternatively, 'HordeAd.Core.DualNumber.dD'
-- or library definitions that use it could be made smarter.


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
shareDelta :: forall y target. TensorKind y
           => Delta target y -> Delta target y
{-# NOINLINE shareDelta #-}
shareDelta d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! case d of
    ZeroG{} -> d
    PairG d1 d2 -> PairG (shareDelta d1) (shareDelta d2)
      -- PairG is only a container; all work is done inside; TODO: more cases
    HToH hv ->
      let shareDynamic :: DynamicTensor (Delta target)
                       -> DynamicTensor (Delta target)
          shareDynamic t = case t of
            DynamicRanked u -> DynamicRanked $ shareDelta u
            DynamicShaped u -> DynamicShaped $ shareDelta u
            DynamicRankedDummy{} -> t
            DynamicShapedDummy{} -> t
      in HToH $ V.map shareDynamic hv
    -- SFromR{} -> d
    -- the term inside SFromR is most likely shared already, but are we sure?
    InputG{} -> d
    ShareG{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> ShareG (NodeId n) d
