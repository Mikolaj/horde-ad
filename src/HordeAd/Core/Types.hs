{-# LANGUAGE AllowAmbiguousTypes, DerivingVia, ImpredicativeTypes,
             UndecidableInstances, UndecidableSuperClasses, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | An assortment of type families and types fundamental for horde-ad.
module HordeAd.Core.Types
  ( -- * Re-exports and definitions to help express and manipulate type-level natural numbers
    SNat, pattern SNat, pattern SNat'
  , withSNat, sNatValue, proxyFromSNat, valueOf
    -- * Kinds of the parameterized types that determine the structure of a tensor
  , Target, TK (..), TKR, TKS, TKX, TKUnit, TKAllNum
    -- * Some fundamental constraints and types related to tensors
  , GoodScalar, NumScalar, GoodScalarConstraint
  , Differentiable, ifDifferentiable
  , BuildTensorKind, RazeTensorKind, ADTensorKind, ADTensorScalar
    -- * Type families that tensors belong to
  , IntOf, HFunOf, PrimalOf, DualOf, PlainOf, ShareOf, BoolOf
  , IxROf, IxSOf, IxXOf
    -- * The Z1 Num unit type and its instances
  , Z1(..)
    -- * Misc
  , Dict(..), IntegralH(..), RealFloatH(..), Boolean (..), EqH(..), OrdH(..)
  , backpermutePrefixList
  , toLinearIdxR, fromLinearIdxR, toLinearIdxS, fromLinearIdxS
  , toLinearIdxX, fromLinearIdxX
    -- * Feature requests for ox-arrays
  , Take, Drop, UnMapSucc
  , listsTake, listsDrop, listsSplitAt, ixrTake, ixrDrop, ixrSplitAt
  , shrTake, shrDrop, shrSplitAt
  , listrSplitAt, ixsDrop, shsTake, shsDrop
  , shxTake, shxDrop, ixxTake, ixxDrop'
  , listsTakeLen, listsDropLen, shsDropLen
  , permRInverse, ssxPermutePrefix, shxPermutePrefix
  , shCastSX, lemRankMapJust'
  , shsFromIxS, shsFromListS
  , normalizePermutationHack, backpermCycle, permCycle
  , permUnShift1
  , ssxTakeIx
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Data.Array.Internal.RankedS qualified as RS
import Data.Boolean (Boolean (..))
import Data.Coerce (coerce)
import Data.Default
import Data.Functor.Const
import Data.Int (Int16, Int32, Int64, Int8)
import Data.Kind (Constraint, Type)
import Data.List (dropWhileEnd, sort)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Storable qualified as V
import Foreign.C (CInt)
import Foreign.Storable (Storable (..))
import GHC.Exts (IsList (..))
import GHC.Generics (Generic)
import GHC.TypeLits
  ( ErrorMessage (..)
  , KnownNat
  , Nat
  , SNat
  , TypeError
  , fromSNat
  , pattern SNat
  , sameNat
  , type (+)
  , type (-)
  , withSomeSNat
  )
import System.Random
import Type.Reflection (Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested (MapJust, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (shxFromShS)
import Data.Array.Nested.Mixed qualified as Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation (DropLen, PermR, TakeLen)
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Dict (..), Tail, fromSNat', unsafeCoerceRefl)
import Data.Array.Strided.Orthotope (NumElt (..), fromO, toO)

-- * Definitions to help express and manipulate type-level natural numbers

instance NFData (SNat n) where
  rnf _ = ()

withSNat :: Int -> (forall n. KnownNat n => (SNat n -> r)) -> r
{-# INLINE withSNat #-}
withSNat i f = withSomeSNat (fromIntegral i) $ \case
  Just snat@SNat -> f snat
  Nothing -> error $ "withSNat: negative argument: " ++ show i

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

matchSNat :: forall n m proxy. KnownNat n
          => proxy n -> SNat m -> Maybe (n :~: m)
matchSNat p m@SNat = sameNat p m


-- * Kinds of the functors that determine the structure of a tensor type

-- | The parameterized carrier types of the algebras
-- that are the targets of interpretation -- of AST
-- and instantiation of the @Ops@ tensor classes. E.g., the type
-- that represents tensor kinds in concrete arrays is one such target.
-- AST itself is another. Dual numbers is yet another target.
type Target = TK -> Type

-- | The type of tensor kinds constraining the shapes
-- of (nested pairs of) tensors.
type data TK =
    TKScalar Type
  | TKR2 Nat TK
  | TKS2 [Nat] TK
  | TKX2 [Maybe Nat] TK
  | TKProduct TK TK

type TKR n r = TKR2 n (TKScalar r)
type TKS sh r = TKS2 sh (TKScalar r)
type TKX sh r = TKX2 sh (TKScalar r)

type TKUnit = TKScalar Z1

type family TKAllNum (y :: TK) :: Constraint where
  TKAllNum (TKScalar Int64) = ()
  TKAllNum (TKScalar Int32) = ()
  TKAllNum (TKScalar Int16) = ()
  TKAllNum (TKScalar Int8) = ()
  TKAllNum (TKScalar CInt) = ()
  TKAllNum (TKScalar Double) = ()
  TKAllNum (TKScalar Float) = ()
  TKAllNum (TKScalar Z1) = ()
  TKAllNum (TKR2 _ y) = TKAllNum y
  TKAllNum (TKS2 _ y) = TKAllNum y
  TKAllNum (TKX2 _ y) = TKAllNum y
  TKAllNum (TKProduct x y) = (TKAllNum x, TKAllNum y)
  TKAllNum a =
    TypeError (Text "TKAllNum: No Num instance for type " :<>: ShowType a)


-- * Some fundamental constraints and types

type GoodScalarConstraint r =
  ( Show r, Ord r, Typeable r, Typeable (ADTensorScalar r)
  , Default r, NFData r, Nested.PrimElt r, Nested.KnownElt r
  , forall sh. Show (Nested.Mixed sh r), forall sh. Ord (Nested.Mixed sh r)
  , forall sh. NFData (Nested.Mixed sh r))

-- Attempted optimization via storing one pointer to a class dictionary
-- in existential datatypes instead of six pointers. No effect, strangely.
-- As a side effect, this avoids ImpredicativeTypes.
-- Also, the constraint can be represented by a single Dict.
--
-- | The constraint that signifies a scalar type, e.g., a float or an integers,
-- is a well-behaved cell content of tensors supported by horde-ad.
class GoodScalarConstraint r => GoodScalar r
instance GoodScalarConstraint r => GoodScalar r

class (GoodScalarConstraint r, Num r, Nested.NumElt r, TKAllNum (TKScalar r))
      => NumScalar r
instance
      (GoodScalarConstraint r, Num r, Nested.NumElt r, TKAllNum (TKScalar r))
      => NumScalar r

-- | The constraint for scalars that can be non-trivially differentiated,
-- e.g., floating numbers, but not integers.
type Differentiable r =
  (RealFloatH r, Nested.FloatElt r, RealFrac r, RealFloat r, Random r)

-- We white-list all types on which we permit differentiation (e.g., SGD)
-- to work. This is for technical typing purposes and imposes updates
-- (and buggy omissions) when new scalar types are added, but it has
-- the advantage of giving more control and visiblity. Sadly the list
-- is repeated in several other places.
--
-- BTW, a lot of occurrences of the non-differentiable case appears
-- when the parameters of the objective functions contain a ListR,
-- in which nil is represented as Z1, which is not differentiable.
-- In other cases it should be rare.
ifDifferentiable :: forall r a. Typeable r
                 => (Differentiable r => a) -> a -> a
{-# INLINE ifDifferentiable #-}
ifDifferentiable ra _
  | Just Refl <- testEquality (typeRep @r) (typeRep @Double) = ra
ifDifferentiable ra _
  | Just Refl <- testEquality (typeRep @r) (typeRep @Float) = ra
ifDifferentiable _ a = a

type family BuildTensorKind k tk where
  BuildTensorKind k (TKScalar r) = TKS '[k] r
  BuildTensorKind k (TKR2 n x) = TKR2 (1 + n) x
  BuildTensorKind k (TKS2 sh x) = TKS2 (k : sh) x
  BuildTensorKind k (TKX2 sh x) = TKX2 (Just k : sh) x
  BuildTensorKind k (TKProduct y z) =
    TKProduct (BuildTensorKind k y) (BuildTensorKind k z)

-- This is an inverse of BuildTensorKind.
-- This could be more efficient
--   RazeTensorKind (TKS2 '[m] (TKScalar r)) = TKScalar r
-- but then we'd lose the simplifying property that razing does not
-- change the tensor kind variant, which is important, e.g.,
-- when rewriting AstFromS t and trying to use AstFromS of the razed t.
type family RazeTensorKind tk where
  RazeTensorKind (TKR2 n x) = TKR2 (n - 1) x
  RazeTensorKind (TKS2 sh x) = TKS2 (Tail sh) x
  RazeTensorKind (TKX2 sh x) = TKX2 (Tail sh) x
  RazeTensorKind (TKProduct y z) =
    TKProduct (RazeTensorKind y) (RazeTensorKind z)

type family ADTensorKind tk where
  ADTensorKind (TKScalar r) = TKScalar (ADTensorScalar r)
  ADTensorKind (TKR2 n x) = TKR2 n (ADTensorKind x)
  ADTensorKind (TKS2 sh x) = TKS2 sh (ADTensorKind x)
  ADTensorKind (TKX2 sh x) = TKX2 sh (ADTensorKind x)
  ADTensorKind (TKProduct y z) =
    TKProduct (ADTensorKind y) (ADTensorKind z)

type family ADTensorScalar r where
  ADTensorScalar Double = Double
  ADTensorScalar Float = Float
  ADTensorScalar t = Z1


-- * Type families that tensors belong to

-- This is used only in indexing and similar contexts.
-- If used as size or shape, it would give more expressiveness,
-- but would lead to irregular tensors, especially after vectorization,
-- and would prevent statically known shapes.
-- | The (arbitrariliy chosen) type of scalars to be used for indexing.
type IntOf (f :: Target) = PlainOf f (TKScalar Int64)

type BoolOf (f :: Target) = PlainOf f (TKScalar Bool)

-- | The type family is defined in order to give a special instance
-- for AST that preserves sharing and, even more importantly, keeps
-- the computation of dervative functions lazy. See the definition
-- of 'HordeAd.Core.Ast.AstLambda' and the code that processes it,
-- maintaining laziness.
--
-- The type family can't easily be made injective, because the @ADVal f@
-- instance is independent of @f@.
type family HFunOf (f :: Target)
                   (x :: TK) (z :: TK) :: Type

type family PrimalOf (f :: Target) :: Target

type family DualOf (f :: Target) :: Target

type family PlainOf (f :: Target) :: Target

type family ShareOf (f :: Target) :: Target

-- | Ranked index, that is, a sized list of individual indices into
-- ranked tensors.
--
-- Thanks to the OverloadedLists mechanism, values of this type
-- and of 'IxSOf' and 'IxXOf' can be written using the normal
-- list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :.: ZIR).
type IxROf (f :: Target) n = IxR n (IntOf f)

-- | Shaped index, that is, a sized list of individual indices into
-- shaped tensors.
--
-- The values of this type are additionally decorated with a shape type @sh@,
-- which indirectly determines in what tensor operations
-- (e.g., what indexing) the values can appear. The type has no direct
-- relation to the runtime payload of the list, except that the list
-- has the same length as the shape. In particular, the individual
-- indices can be "out of bounds" with respect to the shape type.
type IxSOf (f :: Target) (sh :: [Nat]) = IxS sh (IntOf f)

-- | Mixed index, that is, a sized list of individual indices
-- into tensors with mixed ranked-shaped typing.
type IxXOf (f :: Target) (sh :: [Maybe Nat]) = IxX sh (IntOf f)


-- * The Z1 Num unit type and its instances

data Z1 = Z1
 deriving (Eq, Ord, Show)

instance NFData Z1 where
  rnf Z1 = ()

instance Storable Z1 where
  sizeOf _ = 0
  alignment _ = 1
  peek _ = return Z1
  poke _ _ = return ()

instance Num Z1 where
  Z1 + Z1 = Z1
  Z1 * Z1 = Z1
  negate Z1 = Z1
  abs Z1 = Z1
  signum Z1 = Z1
  fromInteger _ = Z1

instance Default Z1 where
  def = Z1

instance Nested.PrimElt Z1
newtype instance Mixed.Mixed sh Z1 = M_NilZ1 (Mixed.Mixed sh (Mixed.Primitive Z1)) deriving (Eq, Ord, Generic)  -- no content, orthotope optimises this (via Vector)
newtype instance Mixed.MixedVecs s sh Z1 = MV_NilZ1 (V.MVector s Z1)  -- no content, MVector optimises this
deriving via Nested.Primitive Z1 instance Nested.Elt Z1
deriving via Nested.Primitive Z1 instance Nested.KnownElt Z1

instance NumElt Z1 where
  numEltAdd _ arr1 _arr2 = arr1
  numEltSub _ arr1 _arr2 = arr1
  numEltMul _ arr1 _arr2 = arr1
  numEltNeg _ arr = arr
  numEltAbs _ arr = arr
  numEltSignum _ arr = arr
  numEltSum1Inner _ arr = fromO (RS.index (toO arr) 0)
  numEltProduct1Inner _ arr = fromO (RS.index (toO arr) 0)
  numEltSumFull _ _arr = Z1
  numEltProductFull _ _arr = Z1
  numEltMinIndex snat _arr = replicate (sNatValue snat) 0
  numEltMaxIndex snat _arr = replicate (sNatValue snat) 0
  numEltDotprodInner _ arr1 _arr2 = fromO (RS.index (toO arr1) 0)


-- * Misc

-- TODO: move all these somewhere

-- | A variant of Integral for horde-ad without the problematic operations:
-- 'mod' and 'rem' that are very slow, pair-producing operations that don't fit
-- the AST GADT format and 'toInteger' that doesn't make sense with AST
-- without an environment to look up variables in.
class Num a => IntegralH a where
  quotH, remH :: a -> a -> a

instance IntegralH Int64 where
  quotH a b = if b == 0 then a else quot a b
  remH a b = if b == 0 then a else rem a b

instance IntegralH Int32 where
  quotH a b = if b == 0 then a else quot a b
  remH a b = if b == 0 then a else rem a b

instance IntegralH Int16 where
  quotH a b = if b == 0 then a else quot a b
  remH a b = if b == 0 then a else rem a b

instance IntegralH Int8 where
  quotH a b = if b == 0 then a else quot a b
  remH a b = if b == 0 then a else rem a b

instance IntegralH CInt where
  quotH a b = if b == 0 then a else quot a b
  remH a b = if b == 0 then a else rem a b

-- | The standard 'RealFloat' brings in a lot of operations we are not
-- interested in and 'RealFrac' and 'Real' that we can't faithfully implement
-- (e.g., 'toRational' doesn't make sense with AST without an environment).
class (Floating a) => RealFloatH a where
  atan2H :: a -> a -> a

instance RealFloatH Float where
  atan2H = atan2

instance RealFloatH Double where
  atan2H = atan2

{- TODO: these would be better, but everything then overlaps with everything:
instance {-# OVERLAPPABLE #-} Integral r => IntegralH r where
  quotH a b = if b == 0 then a else quot a b
  remH a b = if b == 0 then a else rem a b

instance {-# OVERLAPPABLE #-} (Floating r, RealFloat r) => RealFloatH r where
  atan2H = atan2
-}

infix 4 ==., /=.
class Boolean (BoolOf f) => EqH (f :: Target) y where
  (==.), (/=.) :: f y -> f y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (BoolOf f) => OrdH (f :: Target) y where
  (<.), (<=.), (>.), (>=.) :: f y -> f y -> BoolOf f
  u <. v = notB (v <=. u)
  u >. v = notB (u <=. v)
  u >=. v = v <=. u

backpermutePrefixList :: PermR -> [i] -> [i]
backpermutePrefixList p l = map (l !!) p ++ drop (length p) l

-- I can't switch to ixxFromLinear and ixxToLinear from ox-arrays
-- even just because IntegralH is not available in ox-arrays.
--
-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
--
-- Warning: @fromInteger@ of type @j@ cannot be used.
toLinearIdxR :: forall m n j. Num j
             => (Int -> j) -> ShR (m + n) Int -> IxR m j -> j
{-# INLINE toLinearIdxR #-}
toLinearIdxR fromInt = \sh idx -> go sh idx (fromInt 0)
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
fromLinearIdxR :: forall n j. IntegralH j
               => (Int -> j) -> ShR n Int -> j -> IxR n j
{-# INLINE fromLinearIdxR #-}
fromLinearIdxR fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShR n1 Int -> j -> (j, IxR n1 j)
    go ZSR n = (n, ZIR)
    go (k :$: sh) _ | signum k == 0 =
      (fromInt 0, fromInt 0 :.: zeroOfR fromInt sh)
    go (n :$: sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotH` fromInt n
          i = tensLin `remH` fromInt n
      in (tensLin', i :.: idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOfR :: Num j => (Int -> j) -> ShR n i -> IxR n j
{-# INLINE zeroOfR #-}
zeroOfR _ ZSR = ZIR
zeroOfR fromInt (_ :$: sh) = fromInt 0 :.: zeroOfR fromInt sh

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdxS :: forall sh1 sh2 j. Num j
             => ShS (sh1 ++ sh2) -> IxS sh1 j -> j
{-# INLINE toLinearIdxS #-}
toLinearIdxS = \sh idx -> go sh idx 0
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. ShS (sh3 ++ sh2) -> IxS sh3 j -> j -> j
    go sh ZIS tensidx = fromIntegral (shsSize sh) * tensidx
    go ((:$$) n sh) (i :.$ idx) tensidx =
      go sh idx (fromIntegral (sNatValue n) * tensidx + i)
    go _ _ _ = error "toLinearIdxS: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
fromLinearIdxS :: forall sh j. IntegralH j
               => ShS sh -> j -> IxS sh j
{-# INLINE fromLinearIdxS #-}
fromLinearIdxS = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShS sh1 -> j -> (j, IxS sh1 j)
    go ZSS n = (n, ZIS)
    go ((:$$) k sh) _ | sNatValue k == 0 = (0, 0 :.$ zeroOfS sh)
    go ((:$$) n sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotH` fromIntegral (sNatValue n)
          i = tensLin `remH` fromIntegral (sNatValue n)
      in (tensLin', i :.$ idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOfS :: Num j => ShS sh -> IxS sh j
{-# INLINE zeroOfS #-}
zeroOfS ZSS = ZIS
zeroOfS ((:$$) _ sh) = 0 :.$ zeroOfS sh

toLinearIdxX :: forall sh1 sh2 j. Num j
             => (Int -> j) -> IShX (sh1 ++ sh2) -> IxX sh1 j -> j
{-# INLINE toLinearIdxX #-}
toLinearIdxX fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. IShX (sh3 ++ sh2) -> IxX sh3 j -> j -> j
    go sh ZIX tensidx = fromInt (shxSize sh) * tensidx
    go ((:$%) n sh) (i :.% idx) tensidx =
      go sh idx (fromInt (fromSMayNat' n) * tensidx + i)
    go _ _ _ = error "toLinearIdxX: impossible pattern needlessly required"

fromLinearIdxX :: forall sh j. IntegralH j
               => (Int -> j) -> IShX sh -> j -> IxX sh j
{-# INLINE fromLinearIdxX #-}
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
          tensLin' = tensLin `quotH` fromInt (fromSMayNat' n)
          i = tensLin `remH` fromInt (fromSMayNat' n)
      in (tensLin', i :.% idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOfX :: Num j => (Int -> j) -> IShX sh -> IxX sh j
{-# INLINE zeroOfX #-}
zeroOfX _ ZSX = ZIX
zeroOfX fromInt ((:$%) _ sh) = fromInt 0 :.% zeroOfX fromInt sh


-- * Shopping list for ox-arrays

-- All of the below should have better types and/or implementations,
-- just as in ox-arrays, and should have variants for all 10 kinds
-- of shape things.

-- ** Conversions and related

-- The constraint is erroneously reported as redundant.
shCastSX :: Rank sh ~ Rank sh' => StaticShX sh' -> ShS sh -> IShX sh'
shCastSX ssx sh = shxCast' ssx (shxFromShS sh)

-- Sometimes ShS is not available.
lemRankMapJust' :: proxy sh -> Rank (MapJust sh) :~: Rank sh
lemRankMapJust' _ = unsafeCoerceRefl


-- ** Permutation-related operations

-- - Permutation.permInverse for ShS would be helpful in addition to
--   for StaticShX (the proof does not convert (easily)).
--   Though, frankly, the proof is often useless,
--   due to how bad GHC is at reasoning (no (++) congruence, no (:~:)
--   transitivity, etc., see astGatherCase.AstTransposeS
--   and astTransposeAsGatherS), so it's easier to postulate the thing
--   GHC needs in one or two clauses than to write a dozen bread crumbs
--   to lead GHC to grudgingly use the proof.

permRInverse :: PermR -> PermR
permRInverse perm = map snd $ sort $ zip perm [0 .. length perm - 1]

-- TODO: port to shaped permutations and then remove the Hack suffix
normalizePermutationHack :: Permutation.PermR -> Permutation.PermR
normalizePermutationHack perm =
  map fst $ dropWhileEnd (uncurry (==)) $ zip perm [0 ..]

-- TODO: can this be defined for Permutation.Perm using @Mod@?
-- A representation of a cycle backpermutation that moves elements
-- to indexes one less (the the left, to the back).
backpermCycle :: Int -> Permutation.PermR
backpermCycle 0 = []
backpermCycle 1 = []
backpermCycle n = [k `mod` n | k <- [1 .. n]]

-- TODO: can this be defined for Permutation.Perm using @Mod@?
-- A representation of a cycle permutation that is reverse to @backpermCycle@.
permCycle :: Int -> Permutation.PermR
permCycle 0 = []
permCycle 1 = []
permCycle n = [k `mod` n | k <- [-1, 0 .. n - 2]]

type family UnMapSucc is where
  UnMapSucc '[] = '[]
  UnMapSucc (i : is) = i - 1 : UnMapSucc is

-- The inverse of permShift1. Morally:
-- permUnShift1 :: Permutation.Perm (0 : Permutation.MapSucc l)
--              -> Permutation.Perm l
permUnShift1 :: Permutation.Perm (0 : l)
             -> Permutation.Perm (UnMapSucc l)
permUnShift1 (Permutation.PCons _ permRest) =
  Permutation.permFromList
    (permUnMapSucc (Permutation.permToList' permRest)) unsafeCoerce
 where
  permUnMapSucc :: [Int] -> [Int]
  permUnMapSucc [] = []
  permUnMapSucc (i : ns) = i - 1 : permUnMapSucc ns

-- TODO:
_withPermShift1 :: forall is r. -- Permutation.IsPermutation is
                  Permutation.Perm is
               -> (Permutation.IsPermutation (0 : Permutation.MapSucc is) =>
                   Permutation.Perm (0 : Permutation.MapSucc is) -> r)
               -> r
_withPermShift1 _perm _f = undefined  -- f (Permutation.permShift1 perm)

ssxPermutePrefix :: Permutation.Perm is -> StaticShX sh
                 -> StaticShX (Permutation.PermutePrefix is sh)
ssxPermutePrefix = undefined

shxPermutePrefix :: Permutation.Perm is -> ShX sh i
                 -> ShX (Permutation.PermutePrefix is sh) i
shxPermutePrefix = undefined

-- ** Takes and drops; this is postponed until we decide how to handle this; in particular, IIRC, unary nats for ranks is a pre-requisite for the most promising approach. There may be an ox-arrays branch for that. However, this requires lots of effort, so it's probably future work.

type family Take (n :: Nat) (xs :: [k]) :: [k] where
  Take 0 xs = '[]
  Take n (x ': xs) = x ': Take (n - 1) xs

type family Drop (n :: Nat) (xs :: [k]) :: [k] where
  Drop 0 xs = xs
  Drop n (x ': xs) = Drop (n - 1) xs

listsTake :: forall len sh i.
             (KnownShS sh, KnownNat len, KnownShS (Take len sh))
          => ListS sh (Const i) -> ListS (Take len sh) (Const i)
listsTake ix = fromList $ take (valueOf @len) $ toList ix

listsDrop :: forall len sh i.
             (KnownShS sh, KnownNat len, KnownShS (Drop len sh))
          => ListS sh (Const i) -> ListS (Drop len sh) (Const i)
listsDrop ix = fromList $ drop (valueOf @len) $ toList ix

listsSplitAt
  :: forall sh len i.
     (KnownShS sh, KnownNat len, KnownShS (Drop len sh), KnownShS (Take len sh))
  => ListS sh (Const i)
  -> (ListS (Take len sh) (Const i), ListS (Drop len sh) (Const i))
listsSplitAt ix = (listsTake @len ix, listsDrop @len ix)

ixrTake :: forall m n i. (KnownNat m, KnownNat n)
        => IxR (m + n) i -> IxR m i
ixrTake (IxR ix) = IxR $ listrTake ix

ixrDrop :: forall m n i. (KnownNat m, KnownNat n)
        => IxR (m + n) i -> IxR n i
ixrDrop (IxR ix) = IxR $ listrDrop ix

ixrSplitAt :: (KnownNat m, KnownNat n)
           => IxR (m + n) i -> (IxR m i, IxR n i)
ixrSplitAt ix = (ixrTake ix, ixrDrop ix)

shrTake :: forall m n i. (KnownNat n, KnownNat m)
        => ShR (m + n) i -> ShR m i
shrTake (ShR ix) = ShR $ listrTake ix

shrDrop :: forall m n i. (KnownNat m, KnownNat n)
          => ShR (m + n) i -> ShR n i
shrDrop (ShR ix) = ShR $ listrDrop ix

shrSplitAt :: (KnownNat m, KnownNat n)
           => ShR (m + n) i -> (ShR m i, ShR n i)
shrSplitAt ix = (shrTake ix, shrDrop ix)

listrTake :: forall len n i. (KnownNat n, KnownNat len)
          => ListR (len + n) i -> ListR len i
listrTake ix = fromList $ take (valueOf @len) $ toList ix

listrDrop :: forall len n i. (KnownNat len, KnownNat n)
          => ListR (len + n) i -> ListR n i
listrDrop ix = fromList $ drop (valueOf @len) $ toList ix

listrSplitAt :: (KnownNat m, KnownNat n)
             => ListR (m + n) i -> (ListR m i, ListR n i)
listrSplitAt ix = (listrTake ix, listrDrop ix)

ixsDrop :: forall len sh i. (KnownShS sh, KnownNat len, KnownShS (Drop len sh))
        => IxS sh i -> IxS (Drop len sh) i
ixsDrop (IxS ix) = IxS $ listsDrop @len ix

-- TODO
shsTake :: forall len sh. (KnownNat len, KnownShS sh)
        => ShS sh -> ShS (Take len sh)
shsTake sh0 = fromList2 $ take (valueOf @len) $ toList sh0
 where
  fromList2 topl = ShS (go (knownShS @sh) topl)
    where  -- TODO: induction over (unary) SNat?
      go :: forall sh'. ShS sh' -> [Int] -> ListS (Take len sh') SNat
      go _ [] = gcastWith (unsafeCoerceRefl :: len :~: 0) $ gcastWith (unsafeCoerceRefl :: sh' :~: '[]) ZS
      go (sn :$$ sh) (i : is)
        | i == fromSNat' sn = unsafeCoerce $ sn ::$ go sh is
        | otherwise = error $ "shsTake: Value does not match typing (type says "
                                ++ show (fromSNat' sn) ++ ", list contains " ++ show i ++ ")"
      go _ _ = error $ "shsTake: Mismatched list length (type says "
                         ++ show (shsLength (knownShS @sh)) ++ ", list has length "
                         ++ show (length topl) ++ ")"

-- TODO
shsDrop :: forall len sh. (KnownNat len, KnownShS sh)
        => ShS sh -> ShS (Drop len sh)
shsDrop sh0 = fromList2 $ drop (valueOf @len) $ toList sh0
 where
  fromList2 topl = ShS (go (knownShS @sh) $ replicate (valueOf @len) (-1) ++ topl)
    where  -- TODO: induction over (unary) SNat?
      go :: forall sh'. ShS sh' -> [Int] -> ListS (Drop len sh') SNat
      go _ [] = gcastWith (unsafeCoerceRefl :: len :~: 0) $ gcastWith (unsafeCoerceRefl :: sh' :~: '[]) ZS
      go (sn :$$ sh) (i : is)
        | i == -1 = unsafeCoerce $ go sh is
        | i == fromSNat' sn = unsafeCoerce $ sn ::$ go sh is
        | otherwise = error $ "shsDrop: Value does not match typing (type says "
                                ++ show (fromSNat' sn) ++ ", list contains " ++ show i ++ ")"
      go _ _ = error $ "shsDrop: Mismatched list length (type says "
                         ++ show (shsLength (knownShS @sh)) ++ ", list has length "
                         ++ show (length topl) ++ ")"

shxTake :: forall len sh. (KnownNat len, KnownShX sh, KnownShX (Take len sh))
        => IShX sh -> IShX (Take len sh)
shxTake sh0 = fromList $ take (valueOf @len) $ toList sh0

shxDrop :: forall len sh. (KnownNat len, KnownShX sh, KnownShX (Drop len sh))
        => IShX sh -> IShX (Drop len sh)
shxDrop sh0 = fromList $ drop (valueOf @len) $ toList sh0

ixxTake :: forall len sh i. (KnownNat len, KnownShX sh, KnownShX (Take len sh))
        => IxX sh i -> IxX (Take len sh) i
ixxTake sh0 = fromList $ take (valueOf @len) $ toList sh0

ixxDrop' :: forall len sh i. (KnownNat len, KnownShX sh, KnownShX (Drop len sh))
         => IxX sh i -> IxX (Drop len sh) i
ixxDrop' sh0 = fromList $ drop (valueOf @len) $ toList sh0

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

-- This is only needed as a workaround for other ops not provided.

listxTake :: forall f g sh sh'. ListX (sh ++ sh') f -> ListX sh g -> ListX sh f
listxTake _ ZX = ZX
listxTake (i ::% long') ((::%) @_ @_ @sh2 _ short) =
  i ::% listxTake @f @g @sh2 @sh' long' short

ssxTakeIx :: forall sh sh' i. StaticShX (sh ++ sh') -> IxX sh i -> StaticShX sh
ssxTakeIx = coerce (listxTake @(Nested.SMayNat () SNat) @(Const i) @_ @sh')
