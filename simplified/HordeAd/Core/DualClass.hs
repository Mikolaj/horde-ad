{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
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
    IsPrimal(..), IsPrimalR(..), IsPrimalA (..)
  , -- * The API elements used for implementing high-level API, but not re-exported in high-level API
    Dual, HasRanks(..), HasConversions(..)
  , -- * Internal operations, exposed for tests, debugging and experiments
    unsafeGetFreshId, resetIdCounter
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
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
import HordeAd.Core.Domains
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorAst ()
import HordeAd.Core.TensorClass

-- * Class definitions

-- | Second argument is the primal component of a dual number at some rank
-- wrt the differentiation mode given in the first argument.
class IsPrimal a where
  dZero :: Dual a
  dScale :: a -> Dual a -> Dual a
  dScaleByScalar :: a -> Int -> Dual a -> Dual a
  dAdd :: Dual a -> Dual a -> Dual a
  recordSharing :: Dual a -> Dual a
  recordSharingPrimal :: a -> ADShare (Underlying a)
                      -> (ADShare (Underlying a), a)
  letWrapPrimal :: ADShare (Underlying a) -> a -> a
  intOfShape :: a -> Int -> a

-- | Part 1/2 of a hack to squeeze the ranked tensors rank,
-- with its extra @n@ parameter, into the 'IsPrimal' class and assert it
-- for all @n@ values. A similar hack with @TensorOf@ wouldn't work,
-- because instances of type families are illegal.
class IsPrimalR r where
  dZeroR :: KnownNat n => Dual (Flip OR.Array r n)
  dScaleR :: KnownNat n
          => Flip OR.Array r n -> Dual (Flip OR.Array r n) -> Dual (Flip OR.Array r n)
  dScaleByScalarR :: KnownNat n
                  => Flip OR.Array r n -> Int -> Dual (Flip OR.Array r n)
                  -> Dual (Flip OR.Array r n)
  dAddR :: KnownNat n
        => Dual (Flip OR.Array r n) -> Dual (Flip OR.Array r n)
        -> Dual (Flip OR.Array r n)
  recordSharingR :: Dual (Flip OR.Array r n) -> Dual (Flip OR.Array r n)
  recordSharingPrimalR :: Flip OR.Array r n -> ADShare r
                       -> (ADShare r, Flip OR.Array r n)
  letWrapPrimalR :: ADShare r -> Flip OR.Array r n -> Flip OR.Array r n
  packDeltaDtR :: KnownNat n
               => Either (Flip OR.Array r n) (Flip OR.Array r n) -> Dual (Flip OR.Array r n)
               -> DeltaDt (Flip OR.Array) r
  intOfShapeR :: KnownNat n
              => Flip OR.Array r n -> Int -> Flip OR.Array r n

-- | Part 2/2 of a hack to squeeze the ranked tensors rank,
-- with its extra @n@ parameter, into the 'IsPrimal' class.
instance (IsPrimalR r, KnownNat n)
         => IsPrimal (Flip OR.Array r n) where
  dZero = dZeroR
  dScale = dScaleR
  dScaleByScalar = dScaleByScalarR
  dAdd = dAddR
  recordSharing = recordSharingR
  recordSharingPrimal = recordSharingPrimalR
  letWrapPrimal = letWrapPrimalR
  intOfShape = intOfShapeR

-- An analogous hack for Ast.
class IsPrimalA r where
  dZeroA :: KnownNat n => Dual (Ast n r)
  dScaleA :: KnownNat n
          => Ast n r -> Dual (Ast n r) -> Dual (Ast n r)
  dScaleByScalarA :: KnownNat n
                  => Ast n r -> Int -> Dual (Ast n r) -> Dual (Ast n r)
  dAddA :: KnownNat n
        => Dual (Ast n r) -> Dual (Ast n r) -> Dual (Ast n r)
  recordSharingA :: Dual (Ast n r) -> Dual (Ast n r)
  recordSharingPrimalA :: KnownNat n
                       => Ast n r -> ADShare r -> (ADShare r, Ast n r)
  letWrapPrimalA :: ADShare r -> Ast n r -> Ast n r
  packDeltaDtA :: KnownNat n
               => Either (Ast n r) (Ast n r) -> Dual (Ast n r)
               -> DeltaDt AstRanked r
  intOfShapeA :: KnownNat n
              => Ast n r -> Int -> Ast n r

instance (IsPrimalA r, KnownNat n)
         => IsPrimal (Ast n r) where
  dZero = dZeroA
  dScale = dScaleA
  dScaleByScalar = dScaleByScalarA
  dAdd = dAddA
  recordSharing = recordSharingA
  recordSharingPrimal = recordSharingPrimalA
  letWrapPrimal = letWrapPrimalA
  intOfShape = intOfShapeA

-- | The class provides methods required for the second type parameter
-- to be the underlying scalar of a well behaved collection of dual numbers
-- of various ranks wrt the differentation mode given in the first parameter.
class HasRanks ranked where
  dInputR :: InputId (ranked r n) -> Dual (ranked r n)
  dIndexZ :: (KnownNat n, KnownNat m)
          => Dual (ranked r (m + n)) -> IndexOf (ranked r 0) m -> ShapeInt (m + n)
          -> Dual (ranked r n)
  dSumR :: KnownNat n
        => Int -> Dual (ranked r (1 + n)) -> Dual (ranked r n)
  dSum0 :: KnownNat n
        => ShapeInt n -> Dual (ranked r n) -> Dual (ranked r 0)
  dDot0 :: (KnownNat n, Show (ranked r n))
        => ranked r n -> Dual (ranked r n) -> Dual (ranked r 0)
--  dScatterZ1 :: (KnownNat p, KnownNat n)
--            => (Int -> IndexOf (ranked r 0) p)
--            -> Int -> Dual (ranked r (1 + n))
--            -> ShapeInt (p + n) -> Dual (ranked r (p + n))
  dScatterZ :: (KnownNat m, KnownNat p, KnownNat n)
            => ShapeInt (p + n) -> Dual (ranked r (m + n))
            -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
            -> ShapeInt (m + n)
            -> Dual (ranked r (p + n))
  dFromListR :: KnownNat n
             => [Dual (ranked r n)]
             -> Dual (ranked r (1 + n))
  dFromVectorR :: KnownNat n
               => Data.Vector.Vector (Dual (ranked r n))
               -> Dual (ranked r (1 + n))
--  dFromList0R :: KnownNat n
--              => ShapeInt n -> [Dual r] -> Dual (ranked r n)
--  dFromVector0R :: KnownNat n
--                => ShapeInt n -> Data.Vector.Vector (Dual r)
--                -> Dual (ranked r n)
  dReplicateR :: KnownNat n
          => Int -> Dual (ranked r n) -> Dual (ranked r (1 + n))
--  dReplicate0R :: KnownNat n
--           => ShapeInt n -> Dual r -> Dual (ranked r n)
  dAppendR :: KnownNat n
           => Dual (ranked r (1 + n)) -> Int -> Dual (ranked r (1 + n))
           -> Dual (ranked r (1 + n))
  dSliceR :: KnownNat n
          => Int -> Int -> Dual (ranked r (1 + n)) -> Int
          -> Dual (ranked r (1 + n))
  dReverseR :: KnownNat n
            => Dual (ranked r (1 + n)) -> Dual (ranked r (1 + n))
  dTransposeR :: KnownNat n
              => Permutation -> Dual (ranked r n) -> Dual (ranked r n)
  dReshapeR :: (KnownNat n, KnownNat m)
            => ShapeInt n -> ShapeInt m -> Dual (ranked r n)
            -> Dual (ranked r m)
  dBuildR :: KnownNat n
          => Int -> (IntOf (ranked r 0) -> Dual (ranked r n))
          -> Dual (ranked r (1 + n))
--  dGatherZ1 :: (KnownNat p, KnownNat n)
--           => (Int -> IndexOf (ranked r 0) p)
--           -> ShapeInt (p + n) -> Dual (ranked r (p + n))
--           -> Int -> Dual (ranked r (1 + n))
  dGatherZ :: (KnownNat m, KnownNat p, KnownNat n)
           => ShapeInt (m + n) -> Dual (ranked r (p + n))
           -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
           -> ShapeInt (p + n)
           -> Dual (ranked r (m + n))

class HasConversions dynamic ranked where
  dFromD :: KnownNat n
         => Dual (dynamic r) -> Dual (ranked r n)
  dFromR :: KnownNat n
         => Dual (ranked r n) -> Dual (dynamic r)


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
instance GoodScalar r => IsPrimalR r where
  dZeroR = ZeroR
  dScaleR = ScaleR
  dScaleByScalarR tsh c =
    ScaleR (Flip $ OR.constant (OR.shapeL $ runFlip tsh) (fromIntegral c))
  dAddR = AddR
  recordSharingR d = case d of
    ZeroR -> d
    InputR{} -> d
    FromD{} -> d
    LetR{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaR d
  recordSharingPrimalR r l = (l, r)
  letWrapPrimalR _ r = r
  packDeltaDtR (Left tsh) = DeltaDtR (treplicate0N (tshape tsh) 1)
  packDeltaDtR (Right t) = DeltaDtR t
  intOfShapeR tsh c =
    Flip $ OR.constant (OR.shapeL $ runFlip tsh) (fromIntegral c)

instance GoodScalar r
         => IsPrimalA r where
  dZeroA = ZeroR
  dScaleA = ScaleR
  dScaleByScalarA tsh c =
    ScaleR (treplicate0N (tshape tsh) (fromIntegral c))
  dAddA = AddR
  recordSharingA d = case d of
    ZeroR -> d
    InputR{} -> d
    FromD{} -> d
    LetR{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaR d
  recordSharingPrimalA = astRegisterADShare
  letWrapPrimalA = tletWrap
  packDeltaDtA (Left tsh) = DeltaDtR (treplicate0N (tshape tsh) 1)
  packDeltaDtA (Right t) = DeltaDtR t
  intOfShapeA tsh c = treplicate0N (tshape tsh) (fromIntegral c)

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
  dIndexZ = IndexZ
  dSumR = SumR
  dSum0 = Sum0
  dDot0 = Dot0
--  dScatter1 = Scatter1
  dScatterZ = ScatterZ
  dFromListR = FromListR
  dFromVectorR = FromVectorR
--  dFromList0R = FromList0R
--  dFromVector0R = FromVector0R
  dReplicateR = ReplicateR
--  dReplicate0R = Replicate0R
  dAppendR = AppendR
  dSliceR = SliceR
  dReverseR = ReverseR
  dTransposeR = TransposeR
  dReshapeR = ReshapeR
  dBuildR = BuildR
--  dGather1 = Gather1
  dGatherZ = GatherZ

instance (dynamic ~ OD.Array, ranked ~ Flip OR.Array)
         => HasConversions OD.Array (Flip OR.Array) where
  dFromD :: forall n2 r. KnownNat n2
         => Dual (dynamic r) -> Dual (ranked r n2)
  dFromD (FromR @_ @n1 d) =
    case sameNat (Proxy @n1) (Proxy @n2) of
      Just Refl -> d
      _ -> error "dFromD: different ranks in FromD(FromR)"
  dFromR = FromR

instance HasRanks AstRanked where
  dInputR = InputR
  dIndexZ = IndexZ
  dSumR = SumR
  dSum0 = Sum0
  dDot0 = Dot0
--  dScatter1 = Scatter1
  dScatterZ = ScatterZ
  dFromListR = FromListR
  dFromVectorR = FromVectorR
--  dFromList0R = FromList0R
--  dFromVector0R = FromVector0R
  dReplicateR = ReplicateR
--  dReplicate0R = Replicate0R
  dAppendR = AppendR
  dSliceR = SliceR
  dReverseR = ReverseR
  dTransposeR = TransposeR
  dReshapeR = ReshapeR
  dBuildR = BuildR
--  dGather1 = Gather1
  dGatherZ = GatherZ

instance (dynamic ~ AstDynamic, ranked ~ AstRanked)
         => HasConversions AstDynamic AstRanked where
  dFromD :: forall n2 r. KnownNat n2
         => Dual (dynamic r) -> Dual (ranked r n2)
  dFromD (FromR @_ @n1 d) =
    case sameNat (Proxy @n1) (Proxy @n2) of
      Just Refl -> d
      _ -> error "dFromD: different ranks in FromD(FromR)"
  dFromR = FromR


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
wrapDeltaR :: DeltaR ranked n r -> DeltaR ranked n r
{-# NOINLINE wrapDeltaR #-}
wrapDeltaR !d = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! LetR (NodeId n) d
