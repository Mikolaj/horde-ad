{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The classes generalizing delta expressions and exposing them
-- in a more polymorphic way.
-- This is a mid-level API ("HordeAd.Core.Delta" is low level)
-- used to define types and operations in "HordeAd.Core.DualNumber"
-- that is the foundation of the high-level API.
--
-- This module contains impurity, which produces pure data with a particular
-- property. The property is an order of per-node integer identifiers
-- that represents data dependencies and sharing. The low-level API
-- depends on this property, but is completely isolated from the impurity.
-- The high-level API introducess the impurity but can't observe
-- any impure behaviour. Neither can any other module in the package,
-- except for the testing modules that import testing-exclusive operations
-- and instances.
--
-- @Show@ is such a testing-only instance and so should be used
-- only in debugging or testing. Similarly, instances such as @Eq@
-- or @Read@ should not be auto-derived, but carefully crafted to respect
-- sharing. This applies regardless of impurity, because repeated processing
-- of the same shared terms is prohibitive expensive.
module HordeAd.Core.DualClass
  ( -- * The most often used part of the mid-level API that gets re-exported in high-level API
    IsPrimal(..)
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), HasConversions(..)
  , -- * Internal operations, exposed for tests, debugging and experiments
    unsafeGetFreshId, resetIdCounter
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import           GHC.TypeLits (KnownNat, sameNat, type (+))
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.Delta
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorAst ()
import HordeAd.Core.TensorClass

-- * Class definitions

-- | Second argument is the primal component of a dual number at some rank
-- wrt the differentiation mode given in the first argument.
class IsPrimal f r z where
  dZero :: Dual f r z
  dScale :: f r z -> Dual f r z -> Dual f r z
  dScaleByScalar :: f r z -> Int -> Dual f r z -> Dual f r z
  dAdd :: Dual f r z -> Dual f r z -> Dual f r z
  recordSharing :: Dual f r z -> Dual f r z
  recordSharingPrimal :: f r z -> ADShare r -> (ADShare r, f r z)
  letWrapPrimal :: ADShare r -> f r z -> f r z
  intOfShape :: f r z -> Int -> f r z

-- This indirection indueces a few blocks of boilerplate in this module
-- but makes unnecessary hundreds of type applications, repeated
-- and instantiated method signatures and explicit foralls elsewhere,
-- mostly in TensorADVal.
class HasRanks ranked where
  dInputR :: InputId (ranked r n) -> Dual ranked r n
  dIndexR :: (KnownNat n, KnownNat m)
          => Dual ranked r (m + n) -> IndexOf (ranked r 0) m
          -> ShapeInt (m + n)
          -> Dual ranked r n
  dSumR :: KnownNat n
        => Int -> Dual ranked r (1 + n) -> Dual ranked r n
  dSum0R :: KnownNat n
        => ShapeInt n -> Dual ranked r n -> Dual ranked r 0
  dDot0R :: (KnownNat n, Show (ranked r n))
        => ranked r n -> Dual ranked r n -> Dual ranked r 0
  dScatterR :: (KnownNat m, KnownNat p, KnownNat n)
            => ShapeInt (p + n) -> Dual ranked r (m + n)
            -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
            -> ShapeInt (m + n)
            -> Dual ranked r (p + n)
  dFromListR :: KnownNat n
             => [Dual ranked r n]
             -> Dual ranked r (1 + n)
  dFromVectorR :: KnownNat n
               => Data.Vector.Vector (Dual ranked r n)
               -> Dual ranked r (1 + n)
  dReplicateR :: KnownNat n
          => Int -> Dual ranked r n -> Dual ranked r (1 + n)
  dAppendR :: KnownNat n
           => Dual ranked r (1 + n) -> Int -> Dual ranked r (1 + n)
           -> Dual ranked r (1 + n)
  dSliceR :: KnownNat n
          => Int -> Int -> Dual ranked r (1 + n) -> Int
          -> Dual ranked r (1 + n)
  dReverseR :: KnownNat n
            => Dual ranked r (1 + n) -> Dual ranked r (1 + n)
  dTransposeR :: KnownNat n
              => Permutation -> Dual ranked r n -> Dual ranked r n
  dReshapeR :: (KnownNat n, KnownNat m)
            => ShapeInt n -> ShapeInt m -> Dual ranked r n
            -> Dual ranked r m
  dBuildR :: KnownNat n
          => Int -> (IntOf (ranked r 0) -> Dual ranked r n)
          -> Dual ranked r (1 + n)
  dGatherR :: (KnownNat m, KnownNat p, KnownNat n)
           => ShapeInt (m + n) -> Dual ranked r (p + n)
           -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
           -> ShapeInt (p + n)
           -> Dual ranked r (m + n)

-- This indirection is useful to prevent long strings of trivial
-- conversions on tape stemming from packing tensors into Domains.
class HasConversions ranked shaped | ranked -> shaped, shaped -> ranked where
  dDToR :: forall n r. KnownNat n
        => Dual (Clown (DynamicOf ranked)) r '() -> Dual ranked r n
  dSToR :: forall sh r. KnownNat (OS.Rank sh)
        => Dual shaped r sh -> Dual ranked r (OS.Rank sh)
  dRToD :: KnownNat n
        => Dual ranked r n -> Dual (Clown (DynamicOf ranked)) r '()
  dSToD :: (OS.Shape sh, KnownNat (OS.Rank sh))
        => Dual shaped r sh -> Dual (Clown (DynamicOf shaped)) r '()
  dRToS :: OS.Shape sh
        => Dual ranked r (OS.Rank sh) -> Dual shaped r sh
  dDToS :: OS.Shape sh
        => Dual (Clown (DynamicOf shaped)) r '() -> Dual shaped r sh


-- * Delta expression method instances

-- | This is an impure instance, because 'recordSharing' adorns terms
-- with an @Int@ identifier from a counter that is afterwards incremented
-- (and never changed in any other way).
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

-- | This is an impure instance. See above.
instance (GoodScalar r, KnownNat n) => IsPrimal (Flip OR.Array) r n where
  dZero = ZeroR
  dScale = ScaleR
  dScaleByScalar tsh c =
    ScaleR (Flip $ OR.constant (OR.shapeL $ runFlip tsh) (fromIntegral c))
  dAdd = AddR
  recordSharing d = case d of
    ZeroR -> d
    InputR{} -> d
    DToR{} -> d
    LetR{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaR d
  recordSharingPrimal r l = (l, r)
  letWrapPrimal _ r = r
  intOfShape tsh c =
    Flip $ OR.constant (OR.shapeL $ runFlip tsh) (fromIntegral c)

instance (GoodScalar r, KnownNat n) => IsPrimal AstRanked r n where
  dZero = ZeroR
  dScale = ScaleR
  dScaleByScalar tsh c =
    ScaleR (treplicate0N (tshape tsh) (fromIntegral c))
  dAdd = AddR
  recordSharing d = case d of
    ZeroR -> d
    InputR{} -> d
    DToR{} -> d
    LetR{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaR d
  recordSharingPrimal = astRegisterADShare
  letWrapPrimal = tletWrap
  intOfShape tsh c = treplicate0N (tshape tsh) (fromIntegral c)

{- TODO: this should suffice to merge both HasRanks instances, but it doesn't:
class ( Dual (ranked r y) ~ DeltaR ranked r y
      , DeltaR ranked r y ~ Dual (ranked r y) )
      => DualIsDeltaR ranked r y where
instance ( Dual (ranked r y) ~ DeltaR ranked r y
         , DeltaR ranked r y ~ Dual (ranked r y) )
         => DualIsDeltaR ranked r y where

class (forall r12 y. (KnownNat y, GoodScalar r12) => c ranked r12 y) => CYRanked ranked c where
instance (forall r12 y. (KnownNat y, GoodScalar r12) => c ranked r12 y) => CYRanked ranked c where

instance CYRanked ranked DualIsDeltaR => HasRanks ranked where
-}

instance HasRanks (Flip OR.Array) where
  dInputR = InputR
  dIndexR = IndexR
  dSumR = SumR
  dSum0R = Sum0R
  dDot0R = Dot0R
  dScatterR = ScatterR
  dFromListR = FromListR
  dFromVectorR = FromVectorR
  dReplicateR = ReplicateR
  dAppendR = AppendR
  dSliceR = SliceR
  dReverseR = ReverseR
  dTransposeR = TransposeR
  dReshapeR = ReshapeR
  dBuildR = BuildR
  dGatherR = GatherR

instance (ranked ~ Flip OR.Array, shaped ~ Flip OS.Array)
         => HasConversions (Flip OR.Array) (Flip OS.Array) where
  dDToR :: forall n r. KnownNat n
         => Dual (Clown OD.Array) r '() -> Dual ranked r n
  dDToR (RToD @_ @_ @n1 d) =
    case sameNat (Proxy @n1) (Proxy @n) of
      Just Refl -> d
      _ -> error "dDToR: different ranks in DToR(RToD)"
  dDToR d = DToR d
  dSToR :: forall sh r. KnownNat (OS.Rank sh)
        => Dual shaped r sh -> Dual ranked r (OS.Rank sh)
  dSToR (RToS @_ @_ @sh1 d) =
    -- TODO: compare sh, not n:
    case sameNat (Proxy @(OS.Rank sh1)) (Proxy @(OS.Rank sh)) of
      Just Refl -> d
      _ -> error "dSToR: different shapes in SToR(RToS)"
  dSToR d = SToR d
  dRToD = RToD
  dSToD = SToD
  dRToS = RToS
  dDToS = DToS

instance HasRanks AstRanked where
  dInputR = InputR
  dIndexR = IndexR
  dSumR = SumR
  dSum0R = Sum0R
  dDot0R = Dot0R
  dScatterR = ScatterR
  dFromListR = FromListR
  dFromVectorR = FromVectorR
  dReplicateR = ReplicateR
  dAppendR = AppendR
  dSliceR = SliceR
  dReverseR = ReverseR
  dTransposeR = TransposeR
  dReshapeR = ReshapeR
  dBuildR = BuildR
  dGatherR = GatherR

instance (ranked ~ AstRanked, shaped ~ AstShaped)
         => HasConversions AstRanked AstShaped where
  dDToR :: forall n r. KnownNat n
         => Dual (Clown AstDynamic) r '() -> Dual ranked r n
  dDToR (RToD @_ @_ @n1 d) =
    case sameNat (Proxy @n1) (Proxy @n) of
      Just Refl -> d
      _ -> error "dDToR: different ranks in DToR(RToD)"
  dDToR d = DToR d
  dSToR :: forall sh r. KnownNat (OS.Rank sh)
-- TODO: test in new GHC and report; this doesn't work:
--        => Dual (shaped r sh) -> Dual (ranked r (OS.Rank sh))
        => Dual AstShaped r sh -> Dual AstRanked r (OS.Rank sh)
  dSToR (RToS @_ @_ @sh1 d) =
    -- TODO: compare sh, not n:
    case sameNat (Proxy @(OS.Rank sh1)) (Proxy @(OS.Rank sh)) of
      Just Refl -> d
      _ -> error "dSToR: different shapes in SToR(RToS)"
  dSToR d = SToR d
  dRToD = RToD
  dSToD = SToD
  dRToS = RToS
  dDToS = DToS


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
wrapDeltaR :: DeltaR ranked shaped n r -> DeltaR ranked shaped n r
{-# NOINLINE wrapDeltaR #-}
wrapDeltaR !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! LetR (NodeId n) d
