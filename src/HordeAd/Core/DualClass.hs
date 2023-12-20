-- | The classe generalizing the most basic delta expression
-- of the ranked and shaped kind.
-- This is a mid-level API ("HordeAd.Core.Delta" is low level)
-- used to define types and operations in "HordeAd.Core.DualNumber"
-- that is the foundation of the high-level API.
-- WIthout this module, all dual number definitions for arithmetic
-- operations would need to be duplicated, one copy with ranked types
-- and another with shaped types.
--
-- This module also contains and rather safely encapsulates impure side-effects.
-- The impurity produces pure data with a particular property.
-- The property is an order of per-node integer identifiers that represents
-- data dependencies and sharing between delta expressions. The low-level API
-- depends on this property, but is completely isolated from the impurity.
-- The high-level API triggers the impurity but can't observe
-- any impure behaviour. Neither can any other module in the package,
-- except for the testing modules that import testing-exclusive class instances
-- and operations for reading or reseting the impure counter.
--
-- @Show@ is such a testing-only class instance and so should be used
-- only in debugging or testing. Similarly, instances such as @Eq@
-- or @Read@ should not be auto-derived, but carefully crafted to respect
-- sharing. This applies regardless of impurity, because repeated processing
-- of the same shared terms is prohibitively expensive.
module HordeAd.Core.DualClass
  ( IsPrimal(..)
  , unsafeGetFreshId, resetIdCounter, wrapDeltaR, wrapDeltaS
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.Kind (Constraint, Type)
import           GHC.TypeLits (KnownNat)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.Delta
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.SizedIndex

-- * The class and its instances

-- | The class states that @f r z@ type is the primal component
-- of a dual number as exeplified by the operations.
--
-- The OfShape hacks are needed to recover shape from ranked tensors,
-- in particular in case of numeric literals and also for forward derivative.

type IsPrimal :: TensorKind k -> Type -> k -> Constraint
class IsPrimal f r z where
  dZeroOfShape :: f r z -> Dual f r z
  dScale :: f r z -> Dual f r z -> Dual f r z
  dAdd :: Dual f r z -> Dual f r z -> Dual f r z
  intOfShape :: f r z -> Int -> f r z
  recordSharingPrimal :: f r z -> ADShare -> (ADShare, f r z)
  recordSharing :: Dual f r z -> Dual f r z

-- | This and some others are impure instances, because 'recordSharing'
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
-- The pattern-matching in 'recordSharing' is a crucial optimization
-- and it could, presumably, be extended to further limit which
-- terms get an identifier. Alternatively, 'HordeAd.Core.DualNumber.dD'
-- or library definitions that use it could be made smarter.
instance (GoodScalar r, KnownNat n) => IsPrimal (Flip OR.Array) r n where
  dZeroOfShape tsh = ZeroR (rshape tsh)
  dScale _ (ZeroR sh) = ZeroR sh
  dScale v u' = ScaleR v u'
  dAdd ZeroR{} w = w
  dAdd v ZeroR{} = v
  dAdd v w = AddR v w
  intOfShape tsh c =
    rconst $ OR.constant (OR.shapeL $ runFlip tsh) (fromIntegral c)
  recordSharingPrimal r l = (l, r)
  recordSharing d = case d of
    ZeroR{} -> d
    InputR{} -> d
    DToR{} -> d
    SToR{} -> d
    LetR{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaR d

instance (GoodScalar r, Sh.Shape sh) => IsPrimal (Flip OS.Array) r sh where
  dZeroOfShape _tsh = ZeroS
  dScale _ ZeroS = ZeroS
  dScale v u' = ScaleS v u'
  dAdd ZeroS w = w
  dAdd v ZeroS = v
  dAdd v w = AddS v w
  intOfShape _tsh c =  -- this is not needed for OS, but OR needs it
    sconst $ fromIntegral c
  recordSharingPrimal r l = (l, r)
  recordSharing d = case d of
    ZeroS -> d
    InputS{} -> d
    DToS{} -> d
    RToS{} -> d
    LetS{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaS d

instance GoodScalar r => IsPrimal (Clown OD.Array) r '() where
  dZeroOfShape (Clown tsh) =
    withListShape (dshape @(Flip OR.Array) tsh) $ \ (sh :: Shape n Int) ->
      RToD @n (ZeroR sh)
  dScale = undefined
  dAdd = undefined
  intOfShape = undefined
  recordSharingPrimal = undefined
  recordSharing  = undefined


-- * Counter handling

unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 100000001)

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

-- Only for tests, e.g., to ensure show applied to terms has stable length.
-- Tests using this need to be run with -ftest_seq to avoid variable confusion.
resetIdCounter :: IO ()
resetIdCounter = writeIORefU unsafeGlobalCounter 100000001

-- Tests don't show a speedup from `unsafeDupablePerformIO`,
-- perhaps due to counter gaps that it may introduce.
wrapDeltaR :: DeltaR ranked shaped r n -> DeltaR ranked shaped r n
{-# NOINLINE wrapDeltaR #-}
wrapDeltaR !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! LetR (NodeId n) d

wrapDeltaS :: DeltaS ranked shaped r sh -> DeltaS ranked shaped r sh
{-# NOINLINE wrapDeltaS #-}
wrapDeltaS !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! LetS (NodeId n) d
