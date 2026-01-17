{-# LANGUAGE AllowAmbiguousTypes, DerivingVia, ImpredicativeTypes,
             UndecidableInstances, UndecidableSuperClasses, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | An assortment of type families and types fundamental for horde-ad.
module HordeAd.Core.Types
  ( -- * Re-exports and definitions to help express and manipulate type-level natural numbers
    SNat, pattern SNat, pattern SNat'
  , withSNat, proxyFromSNat, valueOf, snatSucc
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
  , pattern Is, mapAccumL'
  , Dict(..), IntegralH(..), RealFloatH(..), Boolean (..), EqH(..), OrdH(..)
  , backpermutePrefixList
    -- * Feature requests for ox-arrays
  , Take, Drop, UnMapSucc
  , listsTake, listsDrop, listsSplitAt, ixrTake, ixrDrop, ixrSplitAt
  , shrTake, shrDrop, ixsTake, ixsDrop, shsTake, shsDrop
  , shxTake, shxDrop, ixxTake, ixxDrop'
  , listsTakeLen, listsDropLen
  , permRInverse, ssxPermutePrefix, shxPermutePrefix
  , shCastSX, lemRankMapJust'
  , normalizePermutationHack, backpermCycle, permCycle
  , permUnShift1
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Data.Boolean (Boolean (..))
import Data.Default
import Data.Foldable qualified as Foldable
import Data.Int (Int16, Int32, Int64, Int8)
import Data.Kind (Constraint, Type)
import Data.List (dropWhileEnd, sort)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality
  (gcastWith, testEquality, type (~~), (:~:) (Refl), (:~~:) (HRefl))
import Data.Vector.Storable qualified as V
import Foreign.C (CInt)
import Foreign.Storable (Storable (..))
import GHC.Exts (IsList (..), oneShot)
import GHC.Generics (Generic)
import GHC.TypeLits
  ( ErrorMessage (..)
  , KnownNat
  , Nat
  , SNat
  , TypeError
  , pattern SNat
  , sameNat
  , type (+)
  , type (-)
  )
import GHC.TypeNats qualified as TN
import System.Random
import Type.Reflection (TypeRep, Typeable, eqTypeRep, pattern TypeRep, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested (MapJust)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (shxFromShS)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed qualified as Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation (DropLen, PermR, TakeLen)
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Dict (..), Tail, fromSNat', unsafeCoerceRefl)
import Data.Array.Strided.Arith (NumElt (..))
import Data.Array.Strided.Array as SA

-- * Definitions to help express and manipulate type-level natural numbers

instance NFData (SNat n) where
  rnf _ = ()

withSNat :: Int -> (forall n. KnownNat n => (SNat n -> r)) -> r
{-# INLINE withSNat #-}
withSNat i f = TN.withSomeSNat (toEnum i) $ \case
  snat@SNat -> f snat

proxyFromSNat :: SNat n -> Proxy n
proxyFromSNat SNat = Proxy

{-# INLINE valueOf #-}
valueOf :: forall n r. (KnownNat n, Num r) => r
valueOf = fromIntegral $ fromSNat' (SNat @n)

pattern SNat' :: forall n m. KnownNat n => n ~ m => SNat m
pattern SNat' <- (matchSNat (Proxy @n) -> Just (Refl :: n :~: m))
  where SNat' = SNat

matchSNat :: forall n m proxy. KnownNat n
          => proxy n -> SNat m -> Maybe (n :~: m)
matchSNat p m@SNat = sameNat p m

snatSucc :: SNat n -> SNat (1 + n)
snatSucc SNat = SNat


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
  TKAllNum (TKScalar Int) = ()
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
  ( RealFloatH r, Nested.FloatElt r, RealFrac r, RealFloat r, Random r
  , ADTensorScalar r ~ r )

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
                 => (Differentiable r => a) -> (ADTensorScalar r ~ Z1 => a) -> a
{-# INLINE ifDifferentiable #-}
ifDifferentiable ra _
  | Just Refl <- testEquality (typeRep @r) (typeRep @Double) = ra
ifDifferentiable ra _
  | Just Refl <- testEquality (typeRep @r) (typeRep @Float) = ra
ifDifferentiable _ a = gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z1) a

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
type IntOf (f :: Target) = PlainOf f (TKScalar Int)

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
  numEltSum1Inner _ = indexZ1
  numEltProduct1Inner _ = indexZ1
  numEltSumFull _ _arr = Z1
  numEltProductFull _ _arr = Z1
  numEltMinIndex snat _arr = replicate (fromSNat' snat) 0
  numEltMaxIndex snat _arr = replicate (fromSNat' snat) 0
  numEltDotprodInner _ arr1 _arr2 = indexZ1 arr1

indexZ1 :: SA.Array (1 + n) a -> SA.Array n a
indexZ1 SA.Array{ SA.arrShape = _ : sh
                , SA.arrStrides = _ : strides
                , SA.arrOffset = _
                , SA.arrValues } = SA.Array { SA.arrShape = sh
                                            , SA.arrStrides = strides
                                            , SA.arrOffset = 0
                                            , SA.arrValues = arrValues }
indexZ1 _ = error "indexZ1: impossible"


-- * Misc

-- TODO: move all these somewhere

pattern Is :: forall a b. Typeable a => a ~~ b => TypeRep b
pattern Is <- (eqTypeRep (TypeRep @a) -> Just (HRefl :: a :~~: b))
  where Is = TypeRep

-- All below is copied from Data.OldList but made strict in state.
mapAccumL' :: (acc -> x -> (acc, y)) -> acc -> [x] -> (acc, [y])
{-# INLINE [1] mapAccumL' #-}
mapAccumL' _ s [] = (s, [])
mapAccumL' f !s (x : xs) = (s'', y : ys)
 where (s', y) = f s x
       (s'', ys) = mapAccumL' f s' xs

-- This apparently increases performance, so it must somehow work.
{-# RULES
"mapAccumL'" [~1] forall f s xs . mapAccumL' f s xs = foldr (mapAccumLF' f) pairWithNil xs s
"mapAccumL'List" [1] forall f s xs . foldr (mapAccumLF' f) pairWithNil xs s = mapAccumL' f s xs
 #-}

pairWithNil :: acc -> (acc, [y])
{-# INLINE [0] pairWithNil #-}
pairWithNil x = (x, [])

mapAccumLF' :: (acc -> x -> (acc, y)) -> x -> (acc -> (acc, [y])) -> acc
            -> (acc, [y])
{-# INLINE [0] mapAccumLF' #-}
mapAccumLF' f = \x r -> oneShot (\ !s ->
                          let (s', y) = f s x
                              (s'', ys) = r s'
                          in (s'', y : ys))

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

instance IntegralH Int where
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
  Permutation.permFromListCont
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

-- TODO: shed the constraints by using listsFromListSPartial Proxy Proxy
listsTake :: forall len sh i. (KnownNat len, KnownShS (Take len sh))
          => ListS sh i -> ListS (Take len sh) i
listsTake l = fromList $ take (valueOf @len) $ listsToList l

listsDrop :: forall len sh i. (KnownNat len, KnownShS (Drop len sh))
          => ListS sh i -> ListS (Drop len sh) i
listsDrop l = fromList $ drop (valueOf @len) $ listsToList l

listsSplitAt
  :: forall sh len i.
     (KnownNat len, KnownShS (Drop len sh), KnownShS (Take len sh))
  => ListS sh i
  -> (ListS (Take len sh) i, ListS (Drop len sh) i)
listsSplitAt ix = (listsTake @len ix, listsDrop @len ix)

ixrTake :: forall m n i. KnownNat m
        => IxR (m + n) i -> IxR m i
ixrTake (IxR ix) = IxR $ listrTake ix

ixrDrop :: forall m n i. (KnownNat m, KnownNat n)
        => IxR (m + n) i -> IxR n i
ixrDrop (IxR ix) = IxR $ listrDrop ix

ixrSplitAt :: (KnownNat m, KnownNat n)
           => IxR (m + n) i -> (IxR m i, IxR n i)
ixrSplitAt ix = (ixrTake ix, ixrDrop ix)

shrTake :: forall m n. KnownNat m
        => IShR (m + n) -> IShR m
shrTake (ShR ix) =
  gcastWith (unsafeCoerceRefl
             :: Take m (Nested.Replicate (m + n) (Nothing @Nat))
                :~: Nested.Replicate m Nothing) $
  case lemKnownReplicate (SNat @m) of
    Dict -> ShR $ shxTake @m ix

shrDrop :: forall m n. (KnownNat m, KnownNat n)
        => IShR (m + n) -> IShR n
shrDrop (ShR ix) =
  gcastWith (unsafeCoerceRefl
             :: Drop m (Nested.Replicate (m + n) (Nothing @Nat))
                :~: Nested.Replicate n Nothing) $
  case lemKnownReplicate (SNat @n) of
    Dict -> ShR $ shxDrop @m ix

listrTake :: forall len n i. KnownNat len
          => ListR (len + n) i -> ListR len i
listrTake ix = fromList $ take (valueOf @len) $ Foldable.toList ix

listrDrop :: forall len n i. (KnownNat len, KnownNat n)
          => ListR (len + n) i -> ListR n i
listrDrop ix = fromList $ drop (valueOf @len) $ Foldable.toList ix

ixsTake :: forall len sh i. (KnownNat len, KnownShS (Take len sh))
        => IxS sh i -> IxS (Take len sh) i
ixsTake (IxS ix) = IxS $ listsTake @len ix

ixsDrop :: forall len sh i. (KnownNat len, KnownShS (Drop len sh))
        => IxS sh i -> IxS (Drop len sh) i
ixsDrop (IxS ix) = IxS $ listsDrop @len ix

-- TODO
shsTake :: forall len sh. KnownNat len
        => ShS sh -> ShS (Take len sh)
shsTake sh0 = fromList2 $ take (valueOf @len) $ shsToList sh0
 where
  fromList2 topl = ShS (ShX (go sh0 topl))
    where  -- TODO: induction over (unary) SNat?
      go :: forall sh'. ShS sh' -> [Int] -> ListH (MapJust (Take len sh')) Int
      go _ [] = gcastWith (unsafeCoerceRefl :: len :~: 0) $ gcastWith (unsafeCoerceRefl :: sh' :~: '[]) ZH
      go (sn :$$ sh) (i : is)
        | i == fromSNat' sn = unsafeCoerce $ sn `ConsKnown` go sh is
        | otherwise = error $ "shsTake: Value does not match typing (type says "
                                ++ show (fromSNat' sn) ++ ", list contains " ++ show i ++ ")"
      go _ _ = error $ "shsTake: Mismatched list length (type says "
                         ++ show (shsLength sh0) ++ ", list has length "
                         ++ show (length topl) ++ ")"

-- TODO
shsDrop :: forall len sh. KnownNat len
        => ShS sh -> ShS (Drop len sh)
shsDrop sh0 = fromList2 $ drop (valueOf @len) $ shsToList sh0
 where
  fromList2 topl = ShS (ShX (go sh0 $ replicate (valueOf @len) (-1) ++ topl))
    where  -- TODO: induction over (unary) SNat?
      go :: forall sh'. ShS sh' -> [Int] -> ListH (MapJust (Drop len sh')) Int
      go _ [] = gcastWith (unsafeCoerceRefl :: len :~: 0) $ gcastWith (unsafeCoerceRefl :: sh' :~: '[]) ZH
      go (sn :$$ sh) (i : is)
        | i == -1 = unsafeCoerce $ go sh is
        | i == fromSNat' sn = unsafeCoerce $ sn `ConsKnown` go sh is
        | otherwise = error $ "shsDrop: Value does not match typing (type says "
                                ++ show (fromSNat' sn) ++ ", list contains " ++ show i ++ ")"
      go _ _ = error $ "shsDrop: Mismatched list length (type says "
                         ++ show (shsLength sh0) ++ ", list has length "
                         ++ show (length topl) ++ ")"

shxTake :: forall len sh. (KnownNat len, KnownShX (Take len sh))
        => IShX sh -> IShX (Take len sh)
shxTake sh0 = fromList $ take (valueOf @len) $ shxToList sh0

shxDrop :: forall len sh. (KnownNat len, KnownShX (Drop len sh))
        => IShX sh -> IShX (Drop len sh)
shxDrop sh0 = fromList $ drop (valueOf @len) $ shxToList sh0

ixxTake :: forall len sh i. (KnownNat len, KnownShX (Take len sh))
        => IxX sh i -> IxX (Take len sh) i
ixxTake sh0 = fromList $ take (valueOf @len) $ Foldable.toList sh0

ixxDrop' :: forall len sh i. (KnownNat len, KnownShX (Drop len sh))
         => IxX sh i -> IxX (Drop len sh) i
ixxDrop' sh0 = fromList $ drop (valueOf @len) $ Foldable.toList sh0

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
