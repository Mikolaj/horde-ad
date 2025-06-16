-- | This module uses and rather safely encapsulates impure side-effects.
-- The impurity produces pure data with a particular property.
-- The property is an order of per-node integer identifiers that represents
-- data dependencies and sharing between delta expressions. The low-level API
-- of AD depends on this property, but is completely isolated from the impurity.
-- The high-level API of AD triggers the impurity but can't observe
-- any impure behaviour. Neither can any other module in the package,
-- except for the testing modules that import testing-exclusive
-- low level operations on the impure counter.
module HordeAd.Core.DeltaFreshId
  ( shareDelta
    -- * Low level counter manipulation to be used only in sequential tests
  , resetIdCounter
  ) where

import Prelude

import Control.Concurrent.Counter (Counter, add, new, set)
import System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Delta

unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (new 100000001)

-- | Do not use; this is exposed only for special low level tests.
-- e.g., to ensure @show@ applied to terms has a stable length.
-- Tests using this need to be run with -ftest_seq to avoid variable confusion.
resetIdCounter :: IO ()
resetIdCounter = set unsafeGlobalCounter 100000001

-- This is the only operation directly touching the single impure counter
-- that holds fresh and continuously incremented integer identifiers,
--
-- We start at a large number to make tests measuring the size of pretty
-- printed terms less fragile. @Counter@ datatype is just as safe,
-- but faster than an @MVar@ or an atomic @IORef@ (and even non-atomic @IORef@).
-- The operation is manually inlined to prevent GHCs deciding otherwise
-- and causing performance anomalies in benchmarks.
unsafeGetFreshId :: IO Int
{-# INLINE unsafeGetFreshId #-}
unsafeGetFreshId = add unsafeGlobalCounter 1

-- Tests don't show a speedup from `unsafeDupablePerformIO`,
-- perhaps due to counter gaps that it may introduce.
--
-- | The impurity exported from this module by @shareDelta@,
-- stemming from the use of 'unsafeGetFreshId' under @unsafePerformIO@,
-- is thread-safe, admits parallel tests
-- and does not require @-fno-full-laziness@ nor @-fno-cse@.
--
-- The pattern-matching in @shareDelta@ is a crucial optimization
-- and it could be extended to limit which terms get an identifier,
-- trading off sharing for reducing direct memory usage.
shareDelta :: forall y target.
              Delta target y -> Delta target y
{-# NOINLINE shareDelta #-}
shareDelta d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! case d of
    DeltaShare{} -> d  -- should not happen, but older/lower id is safer anyway
    DeltaInput{} -> d
    DeltaPair DeltaShare{} DeltaShare{} -> d  -- all work done inside
    DeltaProject1 DeltaShare{} -> d
    DeltaProject2 DeltaShare{} -> d
    DeltaZero{} -> d
    _ -> DeltaShare (mkNodeId (ftkDelta d) n) d
