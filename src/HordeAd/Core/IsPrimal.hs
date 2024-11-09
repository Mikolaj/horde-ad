-- | This module uses and rather safely encapsulates impure side-effects.
-- The impurity produces pure data with a particular property.
-- The property is an order of per-node integer identifiers that represents
-- data dependencies and sharing between delta expressions. The low-level API
-- of AD depends on this property, but is completely isolated from the impurity.
-- The high-level API of AD triggers the impurity but can't observe
-- any impure behaviour. Neither can any other module in the package,
-- except for the testing modules that import testing-exclusive
-- low level operations on the impure counter.
module HordeAd.Core.IsPrimal
  ( shareDelta
    -- * Low level counter manipulation to be used only in tests
  , resetIdCounter
  ) where

import Prelude

import Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter, writeIORefU)
import Data.Vector.Generic qualified as V
import System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Delta
import HordeAd.Core.HVector
import HordeAd.Core.Types

unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 100000001)

-- This is the only operation directly touching the single impure counter
-- that holds fresh and continuously incremented integer identifiers,
--
-- We start at a large number to make tests measuring the size of pretty
-- printed terms less fragile. @Counter@ datatype is just as safe,
-- but faster than an @MVar@ or an atomic @IORef@ (and even non-atomic @IORef@).
-- The operation is manually inlined to prevent GHCs deciding otherwise
-- and causing performance anomalies.
unsafeGetFreshId :: IO Int
{-# INLINE unsafeGetFreshId #-}
unsafeGetFreshId = atomicAddCounter_ unsafeGlobalCounter 1

-- | Do not use; this is exposed only for special low level tests.
-- e.g., to ensure @show@ applied to terms has a stable length.
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
