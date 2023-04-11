{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library.
module HordeAd.Core.TensorClass
  ( Domain0, DomainR, Domains
  , domains0, domainsR, mkDomains, emptyDomain0, nullDomains
  , ADShare
  , emptyADShare, insertADShare, mergeADShare, flattenADShare, assocsADShare
  , IndexOf, ShapeInt, Tensor(..), DynamicTensor(..), DomainsTensor(..), ADReady
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           Data.Kind (Constraint, Type)
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric)

import HordeAd.Core.SizedIndex
import HordeAd.Internal.TensorOps

-- * Domains datatypes definition

-- | Helper definitions to shorten type signatures. @Domains@, among other
-- roles, is the internal representation of domains of objective functions.
type Domain0 r = TensorOf 1 r

-- To store ranked tensors (or Ast terms) we use their untyped versions
-- instead of, e.g,. the unerlying vectors of the tensors,
-- to prevent frequent linearization of the tensors (e.g., after transpose).
type DomainR r = Data.Vector.Vector (DTensorOf r)

type Domains r = Data.Vector.Vector (DTensorOf r)

domains0 :: Tensor r => Domains r -> Domain0 r
domains0 v = tfromD $ v V.! 0

domainsR :: Domains r -> DomainR r
domainsR v = V.slice 1 (V.length v - 1) v

mkDomains :: DynamicTensor r => Domain0 r -> DomainR r -> Domains r
mkDomains t = V.cons (dfromR t)

emptyDomain0 :: Tensor r => Domain0 r
emptyDomain0 = tzero (singletonShape 0)

nullDomains :: Tensor r => Domains r -> Bool
nullDomains params = tlength (domains0 params) == 0 && V.null (domainsR params)

-- Data invariant: the list is reverse-sorted wrt keys.
-- This permits not inspecting too long a prefix of the list, usually,
-- which is crucial for performance. The strictness is crucial for correctness
-- in the presence of impurity for generating fresh variables.
data ADShare r = ADShareNil | ADShareCons !Int !(DTensorOf r) !(ADShare r)
deriving instance Show (DTensorOf r) => Show (ADShare r)

emptyADShare :: ADShare r
emptyADShare = ADShareNil

insertADShare :: Int -> DTensorOf r -> ADShare r -> ADShare r
insertADShare !i !t !s =
  let insertList !l2@(ADShareCons key2 x2 rest2) =
        case compare i key2 of
          EQ -> l2  -- the lists only ever grow and only in fresh/unique way,
                    -- so identical key means identical payload
          LT -> ADShareCons key2 x2 $ insertList rest2
          GT -> ADShareCons i t l2
      insertList ADShareNil = ADShareCons i t ADShareNil
  in insertList s

mergeADShare :: ADShare r -> ADShare r -> ADShare r
mergeADShare !l1@(ADShareCons key1 x1 rest1) !l2@(ADShareCons key2 x2 rest2) =
  case compare key1 key2 of
    EQ -> ADShareCons key1 x1 $ mergeADShare rest1 rest2
    LT -> ADShareCons key2 x2 $ mergeADShare l1 rest2
    GT -> ADShareCons key1 x1 $ mergeADShare rest1 l2
mergeADShare l ADShareNil = l
mergeADShare ADShareNil l = l

flattenADShare :: [ADShare r] -> ADShare r
flattenADShare = foldl' mergeADShare emptyADShare

assocsADShare :: ADShare r -> [(Int, DTensorOf r)]
assocsADShare ADShareNil = []
assocsADShare (ADShareCons key1 x1 rest1) = (key1, x1) : assocsADShare rest1

_lengthADShare :: ADShare r -> Int
_lengthADShare ADShareNil = 0
_lengthADShare (ADShareCons _ _ rest) = 1 + _lengthADShare rest

{-
-- but better to express the strictness already in the type

-- Data invariant: the list is reverse-sorted wrt keys and strict.
-- This permits not inspecting too long a prefix of the list, usually,
-- which is crucial for performance. Keeping the order and the bangs
-- also ensures stritnessw, which is crucial for correctness
-- in the presence of impurity for generating fresh variables.
newtype ADShare r =
  ADShare {unADShare :: [(Int, DTensorOf r)]}
deriving instance Show (DTensorOf r) => Show (ADShare r)

emptyADShare :: ADShare r
emptyADShare = ADShare []

insertADShare :: Int -> DTensorOf r -> ADShare r -> ADShare r
insertADShare !i !t (ADShare s) =
  let insertList !l2@((key2, x2) : rest2) =
        case compare i key2 of
          EQ -> l2
          LT -> (key2, x2) : insertList rest2
          GT -> (i, t) : l2
      insertList [] = [(i, t)]
  in ADShare $ insertList s

mergeADShare :: ADShare r -> ADShare r -> ADShare r
mergeADShare (ADShare s1) (ADShare s2) =
  let mergeLists !l1@((key1, x1) : rest1) !l2@((key2, x2) : rest2) =
        case compare key1 key2 of
         EQ -> l1  -- the lists only ever grow and only in fresh/unique way,
                   -- so an identical key means the rest is the same
         LT -> (key2, x2) : mergeLists l1 rest2
         GT -> (key1, x1) : mergeLists rest1 l2
      mergeLists l [] = l
      mergeLists [] l = l
  in ADShare $ mergeLists s1 s2

flattenADShare :: [ADShare r] -> ADShare r
flattenADShare ls = foldl' mergeADShare emptyADShare ls

assocsADShare :: ADShare r -> [(Int, DTensorOf r)]
assocsADShare = unADShare

-- better than these below, but still breaks tests and performance
newtype ADShare r = ADShare {unADShare :: EM.EnumMap Int (DTensorOf r)}
deriving instance Show (DTensorOf r) => Show (ADShare r)

emptyADShare :: ADShare r
emptyADShare = ADShare EM.empty

insertADShare :: Int -> DTensorOf r -> ADShare r -> ADShare r
insertADShare !i !t (ADShare !s) = ADShare $ EM.insert i t s

mergeADShare :: ADShare r -> ADShare r -> ADShare r
mergeADShare (ADShare !s1) (ADShare !s2) = ADShare $ EM.union s1 s2

flattenADShare :: [ADShare r] -> ADShare r
flattenADShare !ls = ADShare $ EM.unions $ map unADShare ls

assocsADShare :: ADShare r -> [(Int, DTensorOf r)]
assocsADShare (ADShare !s) = EM.toDescList s

-- OOM in blowupLet 3000
newtype ADShare r =
  ADShare {unADShare :: [(Int, DTensorOf r)]}
deriving instance Show (DTensorOf r) => Show (ADShare r)

emptyADShare :: ADShare r
emptyADShare = ADShare []

insertADShare :: Int -> DTensorOf r -> ADShare r -> ADShare r
insertADShare !i !t (ADShare !s) = ADShare $ (i, t) : s

mergeADShare :: ADShare r -> ADShare r -> ADShare r
mergeADShare (ADShare !s1) (ADShare !s2) = let !_ = length s1 + length s2
                                           in ADShare $ s1 ++ s2

flattenADShare :: [ADShare r] -> ADShare r
flattenADShare !ls = let !_ = sum $ map (length . unADShare) ls
                     in ADShare $ concatMap unADShare ls

assocsADShare :: ADShare r -> [(Int, DTensorOf r)]
assocsADShare = EM.toDescList . EM.fromList . unADShare

-- no benefit from strict elements
newtype ADShare r = ADShare {unADShare :: IM.IntMap (DTensorOf r)}
deriving instance Show (DTensorOf r) => Show (ADShare r)

emptyADShare :: ADShare r
emptyADShare = ADShare IM.empty

insertADShare :: Int -> DTensorOf r -> ADShare r -> ADShare r
insertADShare !i !t (ADShare !s) = ADShare $ IM.insert i t s

mergeADShare :: ADShare r -> ADShare r -> ADShare r
mergeADShare (ADShare !s1) (ADShare !s2) = ADShare $ IM.union s1 s2

flattenADShare :: [ADShare r] -> ADShare r
flattenADShare !ls = ADShare $ IM.unions $ map unADShare ls

assocsADShare :: ADShare r -> [(Int, DTensorOf r)]
assocsADShare (ADShare !s) = IM.toDescList s
-}


-- * Tensor class definition

-- @IntOf r@ as size or shape gives more expressiveness,
-- but leads to irregular tensors, especially after vectorization,
-- and prevents statically known shapes.
-- However, if we switched to @Data.Array.Shaped@ and moved most of the shapes
-- to the type level, we'd recover some of the expressiveness, while retaining
-- statically known (type-parameterized) shapes.

-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :. ZI).
type IndexOf n r = Index n (IntOf r)

-- TODO: when we have several times more operations, split into
-- Array (Container) and Tensor (Numeric), with the latter containing the few
-- Ord and Num operations and numeric superclasses.
-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class (Num r, Num (TensorOf 0 r), Num (TensorOf 1 r), Integral (IntOf r))
      => Tensor r where
  type TensorOf (n :: Nat) r = result | result -> n r
  type IntOf r

  tlet :: KnownNat n
       => TensorOf n r -> (TensorOf n r -> TensorOf m r)
       -> TensorOf m r
  tlet a f = f a

  -- Integer codomain
  tshape :: KnownNat n => TensorOf n r -> ShapeInt n
  trank :: forall n. KnownNat n => TensorOf n r -> Int
  trank _ = valueOf @n
  tsize :: KnownNat n => TensorOf n r -> Int
  tsize = sizeShape . tshape
  tlength :: KnownNat n => TensorOf (1 + n) r -> Int
  tlength v = case tshape v of
    ZS -> error "tlength: impossible pattern needlessly required"
    k :$ _ -> k
  tminIndex0 :: TensorOf 1 r -> IntOf r  -- partial
  tminIndex :: KnownNat n => TensorOf n r -> IndexOf n r
  tminIndex t = fromLinearIdx (tshape t) (tminIndex0 (tflatten t))
  tmaxIndex0 :: TensorOf 1 r -> IntOf r  -- partial
  tmaxIndex :: KnownNat n => TensorOf n r -> IndexOf n r
  tmaxIndex t = fromLinearIdx (tshape t) (tmaxIndex0 (tflatten t))
  tfloor :: TensorOf 0 r -> IntOf r
  default tfloor  -- a more narrow type to rule out Ast
    :: (IntOf r ~ CInt, RealFrac r) => TensorOf 0 r -> IntOf r
  tfloor = floor . tunScalar

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
  tindex, (!) :: (KnownNat m, KnownNat n)
              => TensorOf (m + n) r -> IndexOf m r -> TensorOf n r
  infixl 9 !
  (!) = tindex  -- prefix form better when type applications are necessary
  tsum :: KnownNat n => TensorOf (1 + n) r -> TensorOf n r
  tsum0 :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tsum0 = tsum . tflatten
  tdot0 :: KnownNat n => TensorOf n r -> TensorOf n r -> TensorOf 0 r
  tdot0 t u = tsum (tflatten t * tflatten u)
  tmatmul1 :: TensorOf 2 r -> TensorOf 1 r -> TensorOf 1 r
  tmatmul1 m v = tbuild1 (tlength m) (\i -> tdot0 v (m ! [i]))
-- how to generalize (#69)? these equivalent definitions generalize differently:
-- tmatmul1 m v = tbuild1 (tlength m) (\i -> tsum (v * m ! [i]))
-- tmatmul1 m v = tflatten $ tmap1 (tkonst 1 . tdot0 v) m
  tmatmul2 :: TensorOf 2 r -> TensorOf 2 r -> TensorOf 2 r
  tmatmul2 m1 m2 = tmap1 (tmatmul1 (ttr m2)) m1
  tminimum :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tminimum t = t ! tminIndex t
  tmaximum :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tmaximum t = t ! tmaxIndex t
  tfromIndex0 :: IntOf r -> TensorOf 0 r
  default tfromIndex0  -- the more narrow type rules out Ast
    :: IntOf r ~ CInt => IntOf r -> TensorOf 0 r
  tfromIndex0 = tscalar . fromIntegral
  tfromIndex1 :: IndexOf n r -> TensorOf 1 r
  tfromIndex1 = tfromList . map tfromIndex0 . indexToList
  tscatter :: (KnownNat m, KnownNat n, KnownNat p)
           => ShapeInt (p + n) -> TensorOf (m + n) r
           -> (IndexOf m r -> IndexOf p r)
           -> TensorOf (p + n) r
  tscatter1 :: (KnownNat n, KnownNat p)
            => ShapeInt (p + n) -> TensorOf (1 + n) r
            -> (IntOf r -> IndexOf p r)
            -> TensorOf (p + n) r
  tscatter1 sh v f = tscatter @r @1 sh v
                              (\(i :. ZI) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined)
  tfromList :: KnownNat n => [TensorOf n r] -> TensorOf (1 + n) r
  tfromList0N :: KnownNat n => ShapeInt n -> [r] -> TensorOf n r
  tfromList0N sh = treshape sh . tfromList . map tscalar
  tfromVector :: KnownNat n
              => Data.Vector.Vector (TensorOf n r) -> TensorOf (1 + n) r
  tfromVector v = tfromList (V.toList v)  -- horribly inefficient for large vs
  tfromVector0N :: KnownNat n
                => ShapeInt n -> Data.Vector.Vector r -> TensorOf n r
  tfromVector0N sh = treshape sh . tfromVector . V.map tscalar
  tkonst :: KnownNat n => Int -> TensorOf n r -> TensorOf (1 + n) r
  tkonst0N :: KnownNat n => ShapeInt n -> TensorOf 0 r -> TensorOf n r
  tkonst0N sh = treshape sh . tkonst (sizeShape sh)
  tappend :: KnownNat n
          => TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tconcat :: KnownNat n
          => [TensorOf (1 + n) r] -> TensorOf (1 + n) r
  tconcat = foldr1 tappend
  tslice :: KnownNat n
         => Int -> Int -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tuncons :: KnownNat n
          => TensorOf (1 + n) r -> Maybe (TensorOf n r, TensorOf (1 + n) r)
  tuncons v = if tlength v == 0
              then Nothing
              else Just (v ! [0], tslice 1 (tlength v - 1) v)
  treverse :: KnownNat n => TensorOf (1 + n) r -> TensorOf (1 + n) r
  ttr :: KnownNat n => TensorOf (2 + n) r -> TensorOf (2 + n) r
  ttr = ttranspose [1, 0]
  ttranspose :: KnownNat n => Permutation -> TensorOf n r -> TensorOf n r
  tflatten :: KnownNat n => TensorOf n r -> TensorOf 1 r
  tflatten u = treshape (flattenShape $ tshape u) u
  treshape :: (KnownNat n, KnownNat m)
           => ShapeInt m -> TensorOf n r -> TensorOf m r
  tbuild :: forall m n. (KnownNat m, KnownNat n)
         => ShapeInt (m + n) -> (IndexOf m r -> TensorOf n r)
         -> TensorOf (m + n) r
  tbuild sh0 f0 =
    let buildSh :: KnownNat m1
                => ShapeInt m1 -> (IndexOf m1 r -> TensorOf n r)
                -> TensorOf (m1 + n) r
        buildSh ZS f = f ZI
        buildSh (k :$ sh) f = tbuild1 k (\i -> buildSh sh (\ix -> f (i :. ix)))
    in buildSh (takeShape @m @n sh0) f0
  tbuild1 :: KnownNat n  -- this form requires less type applications
          => Int -> (IntOf r -> TensorOf n r) -> TensorOf (1 + n) r
  tmap :: (KnownNat m, KnownNat n)
       => (TensorOf n r -> TensorOf n r)
       -> TensorOf (m + n) r -> TensorOf (m + n) r
  tmap f v = tbuild (tshape v) (\ix -> f (v ! ix))
  tmap1 :: KnownNat n
        => (TensorOf n r -> TensorOf n r)
        -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tmap1 f u = tbuild1 (tlength u) (\i -> f (u ! [i]))
  tmap0N :: KnownNat n
         => (TensorOf 0 r -> TensorOf 0 r) -> TensorOf n r -> TensorOf n r
  tmap0N f v = tbuild (tshape v) (\ix -> f $ v ! ix)
  tzipWith :: (KnownNat m, KnownNat n)
           => (TensorOf n r -> TensorOf n r -> TensorOf n r)
           -> TensorOf (m + n) r -> TensorOf (m + n) r -> TensorOf (m + n) r
  tzipWith f u v = tbuild (tshape v) (\ix -> f (u ! ix) (v ! ix))
  tzipWith1 :: KnownNat n
            => (TensorOf n r -> TensorOf n r -> TensorOf n r)
            -> TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tzipWith1 f u v = tbuild1 (tlength u) (\i -> f (u ! [i]) (v ! [i]))
  tzipWith0N :: KnownNat n
             => (TensorOf 0 r -> TensorOf 0 r -> TensorOf 0 r)
             -> TensorOf n r -> TensorOf n r -> TensorOf n r
  tzipWith0N f u v = tbuild (tshape v) (\ix -> f (u ! ix) (v ! ix))
  tgather :: (KnownNat m, KnownNat n, KnownNat p)
          => ShapeInt (m + n) -> TensorOf (p + n) r
          -> (IndexOf m r -> IndexOf p r)
          -> TensorOf (m + n) r
  tgather1 :: (KnownNat n, KnownNat p)
           => Int -> TensorOf (p + n) r
           -> (IntOf r -> IndexOf p r)
           -> TensorOf (1 + n) r
  tgather1 k v f = tgather @r @1 (k :$ dropShape (tshape v)) v
                                 (\(i :. ZI) -> f i)

  tscalar :: r -> TensorOf 0 r
  tunScalar :: TensorOf 0 r -> r


  -- ** No serviceable parts beyond this point ** --

  -- Needed to avoid Num (TensorOf n r) constraints all over the place
  -- and also wrong shape in @0@ with ranked (not shaped) tensors.
  tzero :: KnownNat n
        => ShapeInt n -> TensorOf n r
  tzero sh = tkonst0N sh 0
  tsumOfList :: KnownNat n
             => [TensorOf n r] -> TensorOf n r  -- TODO: declare nonempty
  default tsumOfList
    :: Num (TensorOf n r)
    => [TensorOf n r] -> TensorOf n r
  tsumOfList = sum
  tmult :: KnownNat n
        => TensorOf n r -> TensorOf n r -> TensorOf n r
  default tmult
    :: Num (TensorOf n r)
    => TensorOf n r -> TensorOf n r -> TensorOf n r
  tmult = (*)
  tscaleByScalar :: KnownNat n => r -> TensorOf n r -> TensorOf n r
  tscaleByScalar s v = v `tmult` tkonst0N (tshape v) (tscalar s)

  -- The primal/dual distinction
  type ScalarOf r
  type Primal r
  type DualOf (n :: Nat) r
  tconst :: KnownNat n => OR.Array n (ScalarOf r) -> TensorOf n r
  tconstant :: KnownNat n => TensorOf n (Primal r) -> TensorOf n r
  tscale0 :: Primal r -> r -> r
  tprimalPart :: TensorOf n r -> TensorOf n (Primal r)
  tdualPart :: TensorOf n r -> DualOf n r
  tD :: KnownNat n => TensorOf n (Primal r) -> DualOf n r -> TensorOf n r
  tScale :: KnownNat n => TensorOf n (Primal r) -> DualOf n r -> DualOf n r
  -- TODO: we'd probably also need dZero, dIndex0 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

  -- Operations for delayed let bindings creation
  tregister :: KnownNat n
            => TensorOf n r -> [(Int, DTensorOf r)]
            -> ([(Int, DTensorOf r)], TensorOf n r)
  tregister r l = (l, r)
  tletWrap :: ADShare r -> TensorOf n r -> TensorOf n r
  tletWrap _l u = u

  -- Conversion
  tfromD :: KnownNat n
         => DTensorOf r -> TensorOf n r

 -- The untyped versions of the tensor, to put many ranks in one vector
class DynamicTensor r where
  type DTensorOf r = result | result -> r
  dfromR :: KnownNat n
         => TensorOf n r -> DTensorOf r

class DomainsTensor r where
  ddummy :: DTensorOf r
  disDummy :: DTensorOf r -> Bool
  daddR :: forall n. KnownNat n
        => TensorOf n r -> DTensorOf r -> DTensorOf r
  dshape :: DTensorOf r -> [Int]
  type DomainsOf r
  tletDomains :: DomainsOf r
              -> (DomainsOf r -> TensorOf n r)
              -> TensorOf n r
  tletDomains a f = f a
  dmkDomains :: Data.Vector.Vector (DTensorOf r) -> DomainsOf r
  default dmkDomains
    :: Data.Vector.Vector (DTensorOf r) ~ DomainsOf r
    => Data.Vector.Vector (DTensorOf r) -> DomainsOf r
  dmkDomains = id
  dlet :: KnownNat n
       => TensorOf n r -> (TensorOf n r -> DomainsOf r)
       -> DomainsOf r
  dlet a f = f a
  dletWrap :: [(Int, DTensorOf r)] -> DomainsOf r -> DomainsOf r
  dletWrap _l u = u


-- * The giga-constraint

type Many (f :: Type -> Constraint) r = (f (TensorOf 0 r), f (TensorOf 1 r), f (TensorOf 2 r), f (TensorOf 3 r), f (TensorOf 4 r), f (TensorOf 5 r), f (TensorOf 6 r), f (TensorOf 7 r), f (TensorOf 8 r), f (TensorOf 9 r), f (TensorOf 10 r), f (TensorOf 11 r), f (TensorOf 12 r))

type ADReady r =
  ( Tensor r, Tensor (Primal r), Show r, RealFloat r
  , RealFloat (Primal r), Numeric (ScalarOf r), RealFloat (ScalarOf r)
  , Many RealFloat r
  , Many RealFloat (Primal r)
  , IfB r, IfB (IntOf r)
  , Many IfB r
  , Many IfB (Primal r)
  , EqB r, EqB (IntOf r)
  , Many EqB r
  , Many EqB (Primal r)
  , OrdB r, OrdB (IntOf r)
  , Many OrdB r
  , Many OrdB (Primal r)
  , Boolean (BooleanOf r)
  , ( BooleanOf r ~ BooleanOf (TensorOf 0 r)
    , BooleanOf r ~ BooleanOf (TensorOf 1 r)
    , BooleanOf r ~ BooleanOf (TensorOf 2 r)
    , BooleanOf r ~ BooleanOf (TensorOf 3 r)
    , BooleanOf r ~ BooleanOf (TensorOf 4 r)
    , BooleanOf r ~ BooleanOf (TensorOf 5 r)
    , BooleanOf r ~ BooleanOf (TensorOf 6 r)
    , BooleanOf r ~ BooleanOf (TensorOf 7 r)
    , BooleanOf r ~ BooleanOf (TensorOf 8 r)
    , BooleanOf r ~ BooleanOf (TensorOf 9 r)
    , BooleanOf r ~ BooleanOf (TensorOf 10 r)
    , BooleanOf r ~ BooleanOf (TensorOf 11 r)
    , BooleanOf r ~ BooleanOf (TensorOf 12 r) )
  , ( BooleanOf r ~ BooleanOf (TensorOf 0 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 1 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 2 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 3 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 4 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 5 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 6 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 7 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 8 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 9 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 10 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 11 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 12 (Primal r)) )
  , BooleanOf r ~ BooleanOf (IntOf r)  -- placing this last gives better errors
  )
  -- any of the @BooleanOf r ~ ...@ lines above breaks GHC <= 9.0.2


-- * Tensor class instances for concrete arrays

instance Tensor Double where
  type TensorOf n Double = OR.Array n Double
  type IntOf Double = CInt
  tshape = tshapeR
  tminIndex0 = tminIndexR
  tmaxIndex0 = tmaxIndexR
  tfloor = floor . tunScalar
  tindex = tindexZR
  tsum = tsumR
  tsum0 = tscalar . tsum0R
  tdot0 u v = tscalar $ tdot0R u v
  tscatter = tscatterZR
  tscatter1 = tscatterZ1R
  tfromList = tfromListR
  tfromList0N = tfromList0NR
  tfromVector = tfromVectorR
  tfromVector0N = tfromVector0NR
  tkonst = tkonstR
  tkonst0N sh = tkonst0NR sh . tunScalar
  tappend = tappendR
  tslice = tsliceR
  treverse = treverseR
  ttranspose = ttransposeR
  treshape = treshapeR
  tbuild = tbuildNR
  tbuild1 = tbuild1R
  tmap0N = tmap0NR
  tzipWith0N = tzipWith0NR
  tgather = tgatherZR
  tgather1 = tgatherZ1R
  tscalar = tscalarR
  tunScalar = tunScalarR
  tscaleByScalar = tscaleByScalarR
  type ScalarOf Double = Double
  type Primal Double = Double
  type DualOf n Double = ()
  tconst = id
  tconstant = id
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u
  tScale _ _ = ()
  tfromD = Data.Array.Convert.convert

instance DynamicTensor Double where
  type DTensorOf Double = OD.Array Double
  dfromR = Data.Array.Convert.convert

instance DomainsTensor Double where
  ddummy = dummyTensor
  disDummy = isTensorDummy
  daddR r d = if isTensorDummy d then dfromR r else dfromR r + d
  dshape = OD.shapeL
  type DomainsOf Double = Domains Double

instance Tensor Float where
  type TensorOf n Float = OR.Array n Float
  type IntOf Float = CInt
  tshape = tshapeR
  tminIndex0 = tminIndexR
  tmaxIndex0 = tmaxIndexR
  tfloor = floor . tunScalar
  tindex = tindexZR
  tsum = tsumR
  tsum0 = tscalar . tsum0R
  tdot0 u v = tscalar $ tdot0R u v
  tscatter = tscatterZR
  tscatter1 = tscatterZ1R
  tfromList = tfromListR
  tfromList0N = tfromList0NR
  tfromVector = tfromVectorR
  tfromVector0N = tfromVector0NR
  tkonst = tkonstR
  tkonst0N sh = tkonst0NR sh . tunScalar
  tappend = tappendR
  tslice = tsliceR
  treverse = treverseR
  ttranspose = ttransposeR
  treshape = treshapeR
  tbuild = tbuildNR
  tbuild1 = tbuild1R
  tmap0N = tmap0NR
  tzipWith0N = tzipWith0NR
  tgather = tgatherZR
  tgather1 = tgatherZ1R
  tscalar = tscalarR
  tunScalar = tunScalarR
  tscaleByScalar = tscaleByScalarR
  type ScalarOf Float = Float
  type Primal Float = Float
  type DualOf n Float = ()
  tconst = id
  tconstant = id
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u
  tScale _ _ = ()
  tfromD = Data.Array.Convert.convert

instance DynamicTensor Float where
  type DTensorOf Float = OD.Array Float
  dfromR = Data.Array.Convert.convert

instance DomainsTensor Float where
  ddummy = dummyTensor
  disDummy = isTensorDummy
  daddR r d = if isTensorDummy d then dfromR r else dfromR r + d
  dshape = OD.shapeL
  type DomainsOf Float = Domains Float

{- These instances are increasingly breaking stuff, so disabled:

-- A stub just to type-check and rewrite away before any computation
-- takes place. Also many others below.
instance Eq r => Eq (a -> r) where  -- embarrassing

instance Ord r => Ord (a -> r) where

instance Num r => Num (a -> r) where

instance Enum (a -> r) where

instance (Enum (a -> r), Real r) => Integral (a -> r) where

instance Fractional r => Fractional (a -> r) where

instance Floating r => Floating (a -> r) where

instance Real r => Real (a -> r) where

instance RealFrac r => RealFrac (a -> r) where

instance RealFloat r => RealFloat (a -> r) where

type instance BooleanOf (ORB.Array n (z -> a)) = z -> BooleanOf a

-- A stub instance for experiments with stored functions
instance Tensor r
         => Tensor (a -> r) where
  type TensorOf n (a -> r) = ORB.Array n (a -> r)
  type IntOf (a -> r) = a -> IntOf r
  tshape = undefined
  tminIndex = undefined
  tmaxIndex = undefined
  tfloor = undefined
  tindex = undefined
  tsum = undefined
  tfromIndex0 = undefined
  tfromList = undefined
  tfromVector = undefined
  tkonst = undefined
  tappend = undefined
  tslice = undefined
  treverse = undefined
  ttranspose = undefined
  treshape = undefined
  tbuild1 = undefined
  tscalar = ORB.scalar
  tunScalar = ORB.unScalar
  type ScalarOf (a -> r) = ScalarOf r
  tconst = tconst
-}
