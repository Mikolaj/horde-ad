{-# LANGUAGE AllowAmbiguousTypes, DerivingVia, ImpredicativeTypes,
             UndecidableInstances, UndecidableSuperClasses, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Some fundamental type families and types.
module HordeAd.Core.Types
  ( -- * Definitions to help express and manipulate type-level natural numbers
    SNat, pattern SNat, withSNat, sNatValue, proxyFromSNat, valueOf
  , pattern SNat'
    -- * Kinds of the functors that determine the structure of a tensor type
  , Target, TensorKindType (..), TKR, TKS, TKX, TKUnit
    -- * Some fundamental constraints and types
  , GoodScalar, Differentiable, IfDifferentiable(..)
  , BuildTensorKind, RazeTensorKind, ADTensorKind, ADTensorScalar, Z0(..)
    -- * Type families that tensors will belong to
  , IntOf, HFunOf, PrimalOf, DualOf, ShareOf
  , IxROf, IxSOf, IxXOf
    -- * Misc
  , Dict(..), IntegralF(..), RealFloatF(..)
  , backpermutePrefixList
  , toLinearIdx, fromLinearIdx, toLinearIdxS, fromLinearIdxS
  , toLinearIdxX, fromLinearIdxX
    -- * Feature requests for ox-arrays
  , Head, Take, Drop
  , ixsRank, ssxRank, ixxRank
  , takeSized, dropSized, splitAt_Sized, takeIndex, dropIndex, splitAt_Index
  , takeShape, dropShape, splitAt_Shape
  , splitAt_SizedS, dropIxS, takeShS, dropShS
  , takeShX, dropShX, takeIxX, dropIxX
  , listsTakeLen, listsDropLen, shsDropLen
  , zipSized, zipWith_Sized, zipIndex, zipWith_Index
  , zipSizedS, zipWith_SizedS, zipIndexS, zipWith_IndexS
  , permRInverse, ixxHead, ssxPermutePrefix, shxPermutePrefix
  , withCastRS, withCastXS, shCastSR, shCastSX
  , ixrToIxs, ixsToIxr, ixxToIxs, ixsToIxx
  , ixsToShS, {-ixxToSSX,-} listsToShS, listrToNonEmpty
  , withKnownPerm
    -- * Ops only needed as a workaround for other ops not provided.
  , ssxTakeIx
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Data.Array.Internal.RankedS qualified as RS
import Data.Coerce (coerce)
import Data.Default
import Data.Foldable qualified as Foldable
import Data.Functor.Const
import Data.Int (Int64)
import Data.Kind (Type)
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector.Storable qualified as V
import Foreign.C (CInt)
import Foreign.Storable (Storable (..))
import GHC.Exts (IsList (..), withDict)
import GHC.Generics (Generic)
import GHC.TypeLits
  ( KnownNat
  , Nat
  , SNat
  , fromSNat
  , pattern SNat
  , sameNat
  , type (+)
  , type (-)
  , withSomeSNat
  )
import System.Random
import Type.Reflection (Typeable)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Internal.Arith (NumElt (..))
import Data.Array.Mixed.Permutation (DropLen, PermR, TakeLen)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (Dict (..), Tail, fromSNat', unsafeCoerceRefl)
import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape

-- * Definitions to help express and manipulate type-level natural numbers

instance NFData (SNat n) where
  rnf _ = ()

withSNat :: Int -> (forall n. KnownNat n => (SNat n -> r)) -> r
withSNat i f = withSomeSNat (fromIntegral i) $ \case
  Just snat@SNat -> f snat
  Nothing -> error "withSNat: negative argument"

sNatValue :: forall n. SNat n -> Int
{-# INLINE sNatValue #-}
sNatValue = fromInteger . fromSNat

proxyFromSNat :: SNat n -> Proxy n
proxyFromSNat SNat = Proxy

{-# INLINE valueOf #-}
valueOf :: forall n r. (KnownNat n, Num r) => r
valueOf = fromInteger $ fromSNat (SNat @n)

pattern SNat' :: forall n m. KnownNat n => (KnownNat m, n ~ m) => SNat m
pattern SNat' <- (matchSNat (Proxy @n) -> Just (Refl :: n :~: m))
  where SNat' = SNat

matchSNat :: forall n m proxy. KnownNat n => proxy n -> SNat m -> Maybe (n :~: m)
matchSNat p m@SNat = sameNat p m


-- * Types of types of tensors

type Target = TensorKindType -> Type

type GoodScalarConstraint r =
  ( Show r, Ord r, Num r, Typeable r, IfDifferentiable r, Default r
  , NFData r, Nested.PrimElt r, Nested.KnownElt r, Nested.NumElt r
  , forall sh. Show (Nested.Mixed sh r), forall sh. Ord (Nested.Mixed sh r)
  , forall sh. NFData (Nested.Mixed sh r))

type data TensorKindType =
    TKScalar Type
  | TKR2 Nat TensorKindType
  | TKS2 [Nat] TensorKindType
  | TKX2 [Maybe Nat] TensorKindType
  | TKProduct TensorKindType TensorKindType

type TKR n r = TKR2 n (TKScalar r)
type TKS sh r = TKS2 sh (TKScalar r)
type TKX sh r = TKX2 sh (TKScalar r)

type TKUnit = TKScalar Z0


-- * Some fundamental constraints

-- Attempted optimization via storing one pointer to a class dictionary
-- in existential datatypes instead of six pointers. No effect, strangely.
-- As a side effect, this avoids ImpredicativeTypes.
-- Also, the constraint can be represented by a single Dict.
class GoodScalarConstraint r => GoodScalar r
instance GoodScalarConstraint r => GoodScalar r

type Differentiable r =
  (RealFloatF r, Nested.FloatElt r, RealFrac r, Random r)

-- We white-list all types on which we permit differentiation (e.g., SGD)
-- to work. This is for technical typing purposes and imposes updates
-- (and buggy omissions) when new scalar types are added, but it has
-- the advantage of giving more control and visiblity. As of the time
-- of writing, this is the only place underlying scalars are enumerated.
class IfDifferentiable r where
  ifDifferentiable :: (Differentiable r => a) -> a -> a

instance {-# OVERLAPPABLE #-} IfDifferentiable r where
  ifDifferentiable _ a = a

-- The white-listed differentiable types.
instance IfDifferentiable Double where
  ifDifferentiable ra _ = ra
instance IfDifferentiable Float where
  ifDifferentiable ra _ = ra

type family BuildTensorKind k tk where
  BuildTensorKind k (TKScalar r) = TKS '[k] r
  BuildTensorKind k (TKR2 n r) = TKR2 (1 + n) r
  BuildTensorKind k (TKS2 sh r) = TKS2 (k : sh) r
  BuildTensorKind k (TKX2 sh r) = TKX2 (Just k : sh) r
  BuildTensorKind k (TKProduct y z) =
    TKProduct (BuildTensorKind k y) (BuildTensorKind k z)

-- This is an inverse of BuildTensorKind.
-- This could be more efficient
--   RazeTensorKind (TKS2 '[m] (TKScalar r)) = TKScalar r
-- but then we'd lose the simplifying property that razing does not
-- change the tensor kind variant, which is important, e.g.,
-- when rewriting AstFromS t and trying to use AstFromS of the razed t.
type family RazeTensorKind tk where
  RazeTensorKind (TKR2 n r) = TKR2 (n - 1) r
  RazeTensorKind (TKS2 sh r) = TKS2 (Tail sh) r
  RazeTensorKind (TKX2 sh r) = TKX2 (Tail sh) r
  RazeTensorKind (TKProduct y z) =
    TKProduct (RazeTensorKind y) (RazeTensorKind z)

type family ADTensorKind tk where
  ADTensorKind (TKScalar r) = TKScalar (ADTensorScalar r)
  ADTensorKind (TKR2 n r) = TKR2 n (ADTensorKind r)
  ADTensorKind (TKS2 sh r) = TKS2 sh (ADTensorKind r)
  ADTensorKind (TKX2 sh r) = TKX2 sh (ADTensorKind r)
  ADTensorKind (TKProduct y z) =
    TKProduct (ADTensorKind y) (ADTensorKind z)

type family ADTensorScalar r where
  ADTensorScalar Double = Double
  ADTensorScalar Float = Float
  ADTensorScalar t = Z0

data Z0 = Z0
 deriving (Eq, Ord, Show)

instance NFData Z0 where
  rnf Z0 = ()

instance Storable Z0 where
  sizeOf _ = 0
  alignment _ = 1
  peek _ = return Z0
  poke _ _ = return ()

instance Num Z0 where
  Z0 + Z0 = Z0
  Z0 * Z0 = Z0
  negate Z0 = Z0
  abs Z0 = Z0
  signum Z0 = Z0
  fromInteger _ = Z0

instance Default Z0 where
  def = Z0

instance Nested.PrimElt Z0
newtype instance Nested.Internal.Mixed sh Z0 = M_NilZ0 (Nested.Internal.Mixed sh (Nested.Internal.Primitive Z0)) deriving (Eq, Generic)  -- no content, orthotope optimises this (via Vector)
deriving instance Ord (Nested.Mixed sh Z0)
newtype instance Nested.Internal.MixedVecs s sh Z0 = MV_NilZ0 (V.MVector s Z0)  -- no content, MVector optimises this
deriving via Nested.Primitive Z0 instance Nested.Elt Z0
deriving via Nested.Primitive Z0 instance Nested.KnownElt Z0

instance NumElt Z0 where
  numEltAdd _ arr1 _arr2 = arr1
  numEltSub _ arr1 _arr2 = arr1
  numEltMul _ arr1 _arr2 = arr1
  numEltNeg _ arr = arr
  numEltAbs _ arr = arr
  numEltSignum _ arr = arr
  numEltSum1Inner _ arr = RS.index arr 0
  numEltProduct1Inner _ arr = RS.index arr 0
  numEltSumFull _ _arr = Z0
  numEltProductFull _ _arr = Z0
  numEltMinIndex snat _arr = replicate (sNatValue snat) 0
  numEltMaxIndex snat _arr = replicate (sNatValue snat) 0
  numEltDotprodInner _ arr1 _arr2 = RS.index arr1 0


-- * Type families that tensors will belong to

-- This is used only in indexing and similar contexts.
-- If used as size or shape, it would give more expressiveness,
-- but would lead to irregular tensors, especially after vectorization,
-- and would prevent statically known shapes.
type IntOf (f :: Target) = PrimalOf f (TKScalar Int64)

-- | The type family is defined in order to give a special instance
-- for AST that preservs sharing and, even more importantly, keeps
-- the computation of dervative functions lazy. See the definition
-- of 'AstLambda' and the code that processes it, maintaining laziness.
--
-- The type family can't easily be made injective, because the @ADVal f@
-- instance is independent of @f@.
type family HFunOf (f :: Target)
                   (x :: TensorKindType) (z :: TensorKindType) :: Type

type family PrimalOf (f :: Target) :: Target

type family DualOf (f :: Target) :: Target

type family ShareOf (f :: Target) :: Target

-- TODO: move this comment elsewhere?
-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :.: ZIR).
type IxROf (f :: Target) n = IxR n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The values of this type are bounded by the shape.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IxSOf (f :: Target) (sh :: [Nat]) = IxS sh (IntOf f)

type IxXOf (f :: Target) (sh :: [Maybe Nat]) = IxX sh (IntOf f)


-- * Misc

-- TODO: move all these somewhere

class Num a => IntegralF a where
  quotF, remF :: a -> a -> a

instance IntegralF Int64 where
  quotF = quot
  remF = rem

instance IntegralF CInt where
  quotF = quot
  remF = rem

class Floating a => RealFloatF a where
  atan2F :: a -> a -> a

instance RealFloatF Float where
  atan2F = atan2

instance RealFloatF Double where
  atan2F = atan2

{- TODO: these would be better, but everything then overlaps with everything:
instance {-# OVERLAPPABLE #-} Integral r => IntegralF r where
  quotF = quot
  remF = rem

instance {-# OVERLAPPABLE #-} (Floating r, RealFloat r) => RealFloatF r where
  atan2F = atan2
-}

backpermutePrefixList :: PermR -> [i] -> [i]
backpermutePrefixList p l = map (l !!) p ++ drop (length p) l

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
--
-- Warning: @fromInteger@ of type @j@ cannot be used.
toLinearIdx :: forall m n j. Num j
            => (Int -> j) -> ShR (m + n) Int -> IxR m j -> j
toLinearIdx fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: ShR (m1 + n) Int -> IxR m1 j -> j -> j
    go sh ZIR tensidx = fromInt (shrSize sh) * tensidx
    go (n :$: sh) (i :.: idx) tensidx = go sh idx (fromInt n * tensidx + i)

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
--
-- Warning: @fromInteger@ of type @j@ cannot be used.
fromLinearIdx :: forall n j. IntegralF j
              => (Int -> j) -> ShR n Int -> j -> IxR n j
fromLinearIdx fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShR n1 Int -> j -> (j, IxR n1 j)
    go ZSR n = (n, ZIR)
    go (k :$: sh) _ | signum k == 0 =
      (fromInt 0, fromInt 0 :.: zeroOf fromInt sh)
    go (n :$: sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotF` fromInt n
          i = tensLin `remF` fromInt n
      in (tensLin', i :.: idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => (Int -> j) -> ShR n i -> IxR n j
zeroOf _ ZSR = ZIR
zeroOf fromInt (_ :$: sh) = fromInt 0 :.: zeroOf fromInt sh

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdxS :: forall sh1 sh2 j. Num j
             => (Int -> j) -> ShS (sh1 ++ sh2) -> IxS sh1 j -> j
toLinearIdxS fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. ShS (sh3 ++ sh2) -> IxS sh3 j -> j -> j
    go sh ZIS tensidx = fromInt (shsSize sh) * tensidx
    go ((:$$) n sh) (i :.$ idx) tensidx =
      go sh idx (fromInt (sNatValue n) * tensidx + i)
    go _ _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
fromLinearIdxS :: forall sh j. IntegralF j
               => (Int -> j) -> ShS sh -> j -> IxS sh j
fromLinearIdxS fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShS sh1 -> j -> (j, IxS sh1 j)
    go ZSS n = (n, ZIS)
    go ((:$$) k sh) _ | sNatValue k == 0 =
      (fromInt 0, fromInt 0 :.$ zeroOfS fromInt sh)
    go ((:$$) n sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotF` fromInt (sNatValue n)
          i = tensLin `remF` fromInt (sNatValue n)
      in (tensLin', i :.$ idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOfS :: Num j => (Int -> j) -> ShS sh -> IxS sh j
zeroOfS _ ZSS = ZIS
zeroOfS fromInt ((:$$) _ sh) = fromInt 0 :.$ zeroOfS fromInt sh

toLinearIdxX :: forall sh1 sh2 j. Num j
             => (Int -> j) -> IShX (sh1 ++ sh2) -> IxX sh1 j -> j
toLinearIdxX fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. IShX (sh3 ++ sh2) -> IxX sh3 j -> j -> j
    go sh ZIX tensidx = fromInt (shxSize sh) * tensidx
    go ((:$%) n sh) (i :.% idx) tensidx =
      go sh idx (fromInt (fromSMayNat' n) * tensidx + i)
    go _ _ _ = error "toLinearIdx: impossible pattern needlessly required"

fromLinearIdxX :: forall sh j. IntegralF j
               => (Int -> j) -> IShX sh -> j -> IxX sh j
fromLinearIdxX fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: IShX sh1 -> j -> (j, IxX sh1 j)
    go ZSX n = (n, ZIX)
    go ((:$%) k sh) _ | fromSMayNat' k == 0 =
      (fromInt 0, fromInt 0 :.% zeroOfX fromInt sh)
    go ((:$%) n sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotF` fromInt (fromSMayNat' n)
          i = tensLin `remF` fromInt (fromSMayNat' n)
      in (tensLin', i :.% idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOfX :: Num j => (Int -> j) -> IShX sh -> IxX sh j
zeroOfX _ ZSX = ZIX
zeroOfX fromInt ((:$%) _ sh) = fromInt 0 :.% zeroOfX fromInt sh


-- * Shopping list for ox-arrays

-- All of this should have better names and types, just as in ox-arrays,
-- and be consistently added for all 9 kinds of shape things.

-- - Permutation.permInverse for ShS instead of only for StaticShX (the proof
--   does not convert (easily)). Though, frankly, the proof is often useless,
--   due to how bad GHC is at reasoning (no (++) congruence, no (:~:)
--   transitivity, etc., see astGatherCase.AstTransposeS
--   and astTransposeAsGatherS), so it's easier to postulate the thing
--   GHC needs in one or two clauses than to write a dozen bread crumbs
--   to lead GHC to grudgingly use the proof.

-- - The Proxies in listsIndex are unused.

type Head :: [k] -> k
type family Head l where
  Head (x : _) = x

type family Take (n :: Nat) (xs :: [k]) :: [k] where
  Take 0 xs = '[]
  Take n (x ': xs) = x ': Take (n - 1) xs

type family Drop (n :: Nat) (xs :: [k]) :: [k] where
  Drop 0 xs = xs
  Drop n (x ': xs) = Drop (n - 1) xs

-- BTW, shall we keep *Rank and *Product for each of the 6 list types
-- and remove *Length and *Size? If not remove, define it for all shape types?
-- Related: I think rsize, ssize and msize can be safely removed.
ixsRank :: IxS sh i -> SNat (Rank sh)
ixsRank (IxS l) = listsRank l

ssxRank :: StaticShX sh -> SNat (Rank sh)
ssxRank (StaticShX l) = listxRank l

ixxRank :: IxX sh f -> SNat (Rank sh)
ixxRank (IxX list) = listxRank list

takeSized :: forall len sh i. (KnownShS sh, KnownNat len, KnownShS (Take len sh))
          => ListS sh (Const i) -> ListS (Take len sh) (Const i)
takeSized ix = fromList $ take (valueOf @len) $ toList ix

dropSized :: forall len sh i. (KnownShS sh, KnownNat len, KnownShS (Drop len sh))
          => ListS sh (Const i) -> ListS (Drop len sh) (Const i)
dropSized ix = fromList $ drop (valueOf @len) $ toList ix

splitAt_Sized
  :: (KnownShS sh, KnownNat len, KnownShS (Drop len sh), KnownShS (Take len sh))
  => ListS sh (Const i)
  -> (ListS (Take len sh) (Const i), ListS (Drop len sh) (Const i))
splitAt_Sized ix = (takeSized ix, dropSized ix)

takeIndex :: forall m n i. (KnownNat m, KnownNat n)
          => IxR (m + n) i -> IxR m i
takeIndex (IxR ix) = IxR $ takeSizedS ix

dropIndex :: forall m n i. (KnownNat m, KnownNat n)
          => IxR (m + n) i -> IxR n i
dropIndex (IxR ix) = IxR $ dropSizedS ix

splitAt_Index :: (KnownNat m, KnownNat n)
              => IxR (m + n) i -> (IxR m i, IxR n i)
splitAt_Index ix = (takeIndex ix, dropIndex ix)

takeShape :: forall m n i. (KnownNat n, KnownNat m)
          => ShR (m + n) i -> ShR m i
takeShape (ShR ix) = ShR $ takeSizedS ix

dropShape :: forall m n i. (KnownNat m, KnownNat n)
          => ShR (m + n) i -> ShR n i
dropShape (ShR ix) = ShR $ dropSizedS ix

splitAt_Shape :: (KnownNat m, KnownNat n)
              => ShR (m + n) i -> (ShR m i, ShR n i)
splitAt_Shape ix = (takeShape ix, dropShape ix)

takeSizedS :: forall len n i. (KnownNat n, KnownNat len)
           => ListR (len + n) i -> ListR len i
takeSizedS ix = fromList $ take (valueOf @len) $ toList ix

dropSizedS :: forall len n i. (KnownNat len, KnownNat n)
           => ListR (len + n) i -> ListR n i
dropSizedS ix = fromList $ drop (valueOf @len) $ toList ix

splitAt_SizedS :: (KnownNat m, KnownNat n)
               => ListR (m + n) i -> (ListR m i, ListR n i)
splitAt_SizedS ix = (takeSizedS ix, dropSizedS ix)

dropIxS :: forall len sh i. (KnownShS sh, KnownNat len, KnownShS (Drop len sh))
        => IxS sh i -> IxS (Drop len sh) i
dropIxS (IxS ix) = IxS $ dropSized ix

-- TODO
takeShS :: forall len sh. (KnownNat len, KnownShS sh)
        => ShS sh -> ShS (Take len sh)
takeShS sh0 = fromList2 $ take (valueOf @len) $ toList sh0
 where
  fromList2 topl = ShS (go (knownShS @sh) topl)
    where  -- TODO: induction over (unary) SNat?
      go :: forall sh'. ShS sh' -> [Int] -> ListS (Take len sh') SNat
      go _ [] = gcastWith (unsafeCoerceRefl :: len :~: 0) $ gcastWith (unsafeCoerceRefl :: sh' :~: '[]) ZS
      go (sn :$$ sh) (i : is)
        | i == fromSNat' sn = unsafeCoerce $ sn ::$ go sh is
        | otherwise = error $ "takeShS: Value does not match typing (type says "
                                ++ show (fromSNat' sn) ++ ", list contains " ++ show i ++ ")"
      go _ _ = error $ "takeShS: Mismatched list length (type says "
                         ++ show (shsLength (knownShS @sh)) ++ ", list has length "
                         ++ show (length topl) ++ ")"

-- TODO
dropShS :: forall len sh. (KnownNat len, KnownShS sh)
        => ShS sh -> ShS (Drop len sh)
dropShS sh0 = fromList2 $ drop (valueOf @len) $ toList sh0
 where
  fromList2 topl = ShS (go (knownShS @sh) $ replicate (valueOf @len) (-1) ++ topl)
    where  -- TODO: induction over (unary) SNat?
      go :: forall sh'. ShS sh' -> [Int] -> ListS (Drop len sh') SNat
      go _ [] = gcastWith (unsafeCoerceRefl :: len :~: 0) $ gcastWith (unsafeCoerceRefl :: sh' :~: '[]) ZS
      go (sn :$$ sh) (i : is)
        | i == -1 = unsafeCoerce $ go sh is
        | i == fromSNat' sn = unsafeCoerce $ sn ::$ go sh is
        | otherwise = error $ "dropShS: Value does not match typing (type says "
                                ++ show (fromSNat' sn) ++ ", list contains " ++ show i ++ ")"
      go _ _ = error $ "dropShS: Mismatched list length (type says "
                         ++ show (shsLength (knownShS @sh)) ++ ", list has length "
                         ++ show (length topl) ++ ")"

takeShX :: forall len sh. (KnownNat len, KnownShX sh, KnownShX (Take len sh))
        => IShX sh -> IShX (Take len sh)
takeShX sh0 = fromList $ take (valueOf @len) $ toList sh0

dropShX :: forall len sh. (KnownNat len, KnownShX sh, KnownShX (Drop len sh))
        => IShX sh -> IShX (Drop len sh)
dropShX sh0 = fromList $ drop (valueOf @len) $ toList sh0

takeIxX :: forall len sh i. (KnownNat len, KnownShX sh, KnownShX (Take len sh))
        => IxX sh i -> IxX (Take len sh) i
takeIxX sh0 = fromList $ take (valueOf @len) $ toList sh0

dropIxX :: forall len sh i. (KnownNat len, KnownShX sh, KnownShX (Drop len sh))
        => IxX sh i -> IxX (Drop len sh) i
dropIxX sh0 = fromList $ drop (valueOf @len) $ toList sh0

listsTakeLen :: forall f g sh1 sh2.
                ListS sh1 f -> ListS sh2 g -> ListS (TakeLen sh1 sh2) g
listsTakeLen ZS _ = ZS
listsTakeLen (_ ::$ sh1) (n ::$ sh2) = n ::$ listsTakeLen sh1 sh2
listsTakeLen (_ ::$ _) ZS = error "listsTakeLen: list too short"

listsDropLen :: forall f g sh1 sh2.
                ListS sh1 f -> ListS sh2 g -> ListS (DropLen sh1 sh2) g
listsDropLen ZS sh = sh
listsDropLen (_ ::$ sh1) (_ ::$ sh2) = listsDropLen sh1 sh2
listsDropLen (_ ::$ _) ZS = error "listsDropLen: list too short"

shsDropLen :: Permutation.Perm is -> ShS sh -> ShS (DropLen is sh)
shsDropLen = coerce (listsDropLenPerm @SNat)

zipSized :: ListR n i -> ListR n j -> ListR n (i, j)
zipSized ZR ZR = ZR
zipSized (i ::: irest) (j ::: jrest) = (i, j) ::: zipSized irest jrest
zipSized _ _ = error "zipSized: impossible pattern needlessly required"

zipWith_Sized :: (i -> j -> k) -> ListR n i -> ListR n j
              -> ListR n k
zipWith_Sized _ ZR ZR = ZR
zipWith_Sized f (i ::: irest) (j ::: jrest) =
  f i j ::: zipWith_Sized f irest jrest
zipWith_Sized _ _ _ =
  error "zipWith_Sized: impossible pattern needlessly required"

zipIndex :: IxR n i -> IxR n j -> IxR n (i, j)
zipIndex (IxR l1) (IxR l2) = IxR $ zipSized l1 l2

zipWith_Index :: (i -> j -> k) -> IxR n i -> IxR n j -> IxR n k
zipWith_Index f (IxR l1) (IxR l2) = IxR $ zipWith_Sized f l1 l2

zipSizedS :: ListS sh (Const i) -> ListS sh (Const j) -> ListS sh (Const (i, j))
zipSizedS ZS ZS = ZS
zipSizedS (Const i ::$ irest) (Const j ::$ jrest) =
  Const (i, j) ::$ zipSizedS irest jrest

zipWith_SizedS :: (i -> j -> k)
              -> ListS sh (Const i) -> ListS sh (Const j)
              -> ListS sh (Const k)
zipWith_SizedS _ ZS ZS = ZS
zipWith_SizedS f (Const i ::$ irest) (Const j ::$ jrest) =
  Const (f i j) ::$ zipWith_SizedS f irest jrest

zipIndexS :: IxS sh i -> IxS sh j -> IxS sh (i, j)
zipIndexS (IxS l1) (IxS l2) = IxS $ zipSizedS l1 l2

zipWith_IndexS :: (i -> j -> k) -> IxS sh i -> IxS sh j -> IxS sh k
zipWith_IndexS f (IxS l1) (IxS l2) = IxS $ zipWith_SizedS f l1 l2

-- Also permInverse for S would be very handy (see how unreadable
-- is permInverse applied to S terms in AstSimplify).
permRInverse :: PermR -> PermR
permRInverse perm = map snd $ sort $ zip perm [0 .. length perm - 1]

listxHead :: ListX (mn ': sh) f -> f mn
listxHead (i ::% _) = i

ixxHead :: IxX (n : sh) i -> i
ixxHead (IxX list) = getConst (listxHead list)

ssxPermutePrefix :: Permutation.Perm is -> StaticShX sh
                 -> StaticShX (Permutation.PermutePrefix is sh)
ssxPermutePrefix = undefined

shxPermutePrefix :: Permutation.Perm is -> ShX sh i
                 -> ShX (Permutation.PermutePrefix is sh) i
shxPermutePrefix = undefined

withCastRS :: forall n r.
              IShR n
           -> (forall sh. n ~ Rank sh => ShS sh -> r)
           -> r
withCastRS ZSR f = f ZSS
withCastRS (n :$: rest') f = withSNat n $ \snat ->
  withCastRS rest' (\rest -> f (snat :$$ rest))

withCastXS :: forall sh' r.
              IShX sh'
           -> (forall sh. Rank sh' ~ Rank sh => ShS sh -> r)
           -> r
withCastXS ZSX f = f ZSS
withCastXS (Nested.SKnown snat@SNat :$% rest') f =
  withCastXS rest' (\rest -> f (snat :$$ rest))
withCastXS (Nested.SUnknown k :$% rest') f = withSNat k $ \snat ->
  withCastXS rest' (\rest -> f (snat :$$ rest))

shCastSR :: ShS sh -> IShR (Rank sh)
shCastSR ZSS = ZSR
shCastSR (snat2 :$$ rest) =
  sNatValue snat2 :$: shCastSR rest

-- The constraint is erroneously reported as redundant.
shCastSX :: Rank sh ~ Rank sh' => StaticShX sh' -> ShS sh -> IShX sh'
shCastSX ZKX ZSS = ZSX
shCastSX ((:!%) @_ @restx (Nested.SKnown snat1) restx)
         ((:$$) @_ @rest snat2 rest) =
  gcastWith (unsafeCoerceRefl :: Rank restx :~: Rank rest) $  -- why!
  if sNatValue snat1 == sNatValue snat2
  then Nested.SKnown snat1 :$% shCastSX restx rest
  else error $ "shCastSX: shapes don't match: " ++ show (snat1, snat2)
shCastSX ((:!%) @_ @restx (Nested.SUnknown ()) restx)
         ((:$$) @_ @rest snat2 rest) =
  gcastWith (unsafeCoerceRefl :: Rank restx :~: Rank rest) $  -- why!
  Nested.SUnknown (sNatValue snat2) :$% shCastSX restx rest

-- TODO; make more typed, ensure ranks match, use singletons instead of constraints,
-- give better names and do the same for ListS, etc.
ixrToIxs :: (KnownShS sh, KnownNat (Rank sh))
         => IxR (Rank sh) i -> IxS sh i
ixrToIxs = fromList . toList
ixsToIxr :: (KnownShS sh, KnownNat (Rank sh))
         => IxS sh i -> IxR (Rank sh) i
ixsToIxr = fromList . toList
ixxToIxs :: (KnownShS sh, KnownShX sh')
         => IxX sh' i -> IxS sh i
ixxToIxs = fromList . toList
ixsToIxx :: (KnownShS sh, KnownShX sh')
         => IxS sh i -> IxX sh' i
ixsToIxx = fromList . toList

-- TODO: this can be retired when we have a conversion from IxS to ShS
sixKnown :: IxS sh i -> Dict KnownShS sh
sixKnown ZIS = Dict
sixKnown (_ :.$ sh) | Dict <- sixKnown sh = Dict

-- TODO: ixrToShR :: IxR sh i -> ShR sh i

ixsToShS :: IxS sh i -> ShS sh
ixsToShS ix | Dict <- sixKnown ix = knownShS

_ixxToSSX :: IxX sh i -> StaticShX sh
_ixxToSSX (IxX _list) = error "TODO"

-- TODO: this can be retired when we have a conversion from ListS to ShS;
slistKnown :: ListS sh i -> Dict KnownShS sh
slistKnown ZS = Dict
slistKnown (_ ::$ sh) | Dict <- slistKnown sh = Dict

listsToShS :: ListS sh i -> ShS sh
listsToShS l | Dict <- slistKnown l = knownShS

listrToNonEmpty :: ListR (n + 1) i -> NonEmpty i
listrToNonEmpty l = listrHead l :| Foldable.toList (listrTail l)

instance NFData i => NFData (ListR n i) where
  rnf ZR = ()
  rnf (x ::: l) = rnf x `seq` rnf l

withKnownPerm :: forall perm r. Permutation.Perm perm -> (Permutation.KnownPerm perm => r) -> r
withKnownPerm perm = withDict @(Permutation.KnownPerm perm) perm

-- TODO:
_withPermShift1 :: forall is r. -- Permutation.IsPermutation is
                  Permutation.Perm is
               -> (Permutation.IsPermutation (0 : Permutation.MapSucc is) =>
                   Permutation.Perm (0 : Permutation.MapSucc is) -> r)
               -> r
_withPermShift1 _perm _f = undefined  -- f (Permutation.permShift1 perm)


-- This is only needed as a workaround for other ops not provided.

listxTake :: forall f g sh sh'. ListX (sh ++ sh') f -> ListX sh g -> ListX sh f
listxTake _ ZX = ZX
listxTake (i ::% long') ((::%) @_ @_ @sh2 _ short) = i ::% listxTake @f @g @sh2 @sh' long' short

ssxTakeIx :: forall sh sh' i. StaticShX (sh ++ sh') -> IxX sh i -> StaticShX sh
ssxTakeIx = coerce (listxTake @(Nested.SMayNat () SNat) @(Const i) @_ @sh')
