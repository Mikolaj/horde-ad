{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Data.Array.Nested.Permutation where

import Data.Coerce (coerce)
import Data.List (sort)
import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Ord
import GHC.Exts (withDict)
import GHC.TypeError
import GHC.TypeLits
import GHC.TypeNats qualified as TN

import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Types


-- * Permutations

-- | A "backward" permutation of a dimension list. The operation on the
-- dimension list is most similar to @backpermute@ in the @vector@ package; see
-- 'Permute' for code that implements this.
data Perm list where
  PNil :: Perm '[]
  PCons :: SNat a -> Perm l -> Perm (a : l)
infixr 5 `PCons`
deriving instance Show (Perm list)
deriving instance Eq (Perm list)

instance TestEquality Perm where
  testEquality PNil PNil = Just Refl
  testEquality (x `PCons` xs) (y `PCons` ys)
    | Just Refl <- testEquality x y
    , Just Refl <- testEquality xs ys = Just Refl
  testEquality _ _ = Nothing

permRank :: Perm list -> SNat (Rank list)
permRank PNil = SNat
permRank (_ `PCons` l) | SNat <- permRank l = SNat

permFromListCont :: [Int] -> (forall list. Perm list -> r) -> r
permFromListCont [] k = k PNil
permFromListCont (x : xs) k = withSomeSNat (fromIntegral x) $ \case
  Just sn -> permFromListCont xs $ \list -> k (sn `PCons` list)
  Nothing -> error $ "Data.Array.Nested.Permutation.permFromListCont: negative number in list: " ++ show x

permToList :: Perm list -> [Natural]
permToList PNil = mempty
permToList (x `PCons` l) = TN.fromSNat x : permToList l

permToList' :: Perm list -> [Int]
permToList' = map fromIntegral . permToList

-- | When called as @permCheckPermutation p k@, if @p@ is a permutation of
-- @[0 .. 'length' ('permToList' p) - 1]@, @Just k@ is returned. If it isn't,
-- then @Nothing@ is returned.
permCheckPermutation :: forall r list. Perm list -> (IsPermutation list => r) -> Maybe r
permCheckPermutation = \p k ->
  let n = permRank p
  in case (provePerm1 (Proxy @list) n p, provePerm2 (SNat @0) n p) of
       (Just Refl, Just Refl) -> Just k
       _ -> Nothing
  where
    lemElemCount :: (0 <= n, Compare n m ~ LT)
                 => proxy n -> proxy m -> Elem n (Count 0 m) :~: True
    lemElemCount _ _ = unsafeCoerceRefl

    lemCount :: (OrdCond (Compare i n) True False True ~ True)
             => proxy i -> proxy n -> Count i n :~: i : Count (i + 1) n
    lemCount _ _ = unsafeCoerceRefl

    lemElem :: Elem x ys ~ True => proxy x -> proxy' (y : ys) -> Elem x (y : ys) :~: True
    lemElem _ _ = unsafeCoerceRefl

    provePerm1 :: Proxy isTop -> SNat (Rank isTop) -> Perm is'
               -> Maybe (AllElem' is' (Count 0 (Rank isTop)) :~: True)
    provePerm1 _ _ PNil = Just Refl
    provePerm1 p rtop@SNat (PCons sn@SNat perm)
      | Just Refl <- provePerm1 p rtop perm
      = case (cmpNat (SNat @0) sn, cmpNat sn rtop) of
          (LTI, LTI) | Refl <- lemElemCount sn rtop -> Just Refl
          (EQI, LTI) | Refl <- lemElemCount sn rtop -> Just Refl
          _ -> Nothing
      | otherwise
      = Nothing

    provePerm2 :: SNat i -> SNat n -> Perm is'
               -> Maybe (AllElem' (Count i n) is' :~: True)
    provePerm2 = \i@(SNat :: SNat i) n@SNat perm ->
      case cmpNat i n of
        EQI -> Just Refl
        LTI | Refl <- lemCount i n
            , Just Refl <- provePerm2 (SNat @(i + 1)) n perm
            -> checkElem i perm
            | otherwise -> Nothing
        GTI -> error "unreachable"
      where
        checkElem :: SNat i -> Perm is' -> Maybe (Elem i is' :~: True)
        checkElem _ PNil = Nothing
        checkElem i@SNat (PCons k@SNat perm :: Perm is') =
          case sameNat i k of
            Just Refl -> Just Refl
            Nothing | Just Refl <- checkElem i perm, Refl <- lemElem i (Proxy @is') -> Just Refl
                    | otherwise -> Nothing

-- | Utility class for generating permutations from type class information.
class KnownPerm l where makePerm :: Perm l
instance KnownPerm '[] where makePerm = PNil
instance (KnownNat n, KnownPerm l) => KnownPerm (n : l) where makePerm = natSing `PCons` makePerm

withKnownPerm :: forall l r. Perm l -> (KnownPerm l => r) -> r
withKnownPerm = withDict @(KnownPerm l)

-- | Untyped permutations for ranked arrays
type PermR = [Int]


-- ** Applying permutations

type family Elem x l where
  Elem x '[] = 'False
  Elem x (x : _) = 'True
  Elem x (_ : ys) = Elem x ys

type family AllElem' as bs where
  AllElem' '[] bs = 'True
  AllElem' (a : as) bs = Elem a bs && AllElem' as bs

type AllElem as bs = Assert (AllElem' as bs)
  (TypeError (Text "The elements of " :<>: ShowType as :<>: Text " are not all in " :<>: ShowType bs))

type family Count i n where
  Count n n = '[]
  Count i n = i : Count (i + 1) n

type IsPermutation as = (AllElem as (Count 0 (Rank as)), AllElem (Count 0 (Rank as)) as)

type family Index i sh where
  Index 0 (n : sh) = n
  Index i (_ : sh) = Index (i - 1) sh

type family Permute is sh where
  Permute '[] sh = '[]
  Permute (i : is) sh = Index i sh : Permute is sh

type PermutePrefix is sh = Permute is (TakeLen is sh) ++ DropLen is sh

type family TakeLen ref l where
  TakeLen '[] l = '[]
  TakeLen (_ : ref) (x : xs) = x : TakeLen ref xs

type family DropLen ref l where
  DropLen '[] l = l
  DropLen (_ : ref) (_ : xs) = DropLen ref xs

listhTakeLen :: forall i is sh. Perm is -> ListH sh i -> ListH (TakeLen is sh) i
listhTakeLen PNil _ = ZH
listhTakeLen (_ `PCons` is) (n `ConsUnknown` sh) = n `ConsUnknown` listhTakeLen is sh
listhTakeLen (_ `PCons` is) (n `ConsKnown` sh) = n `ConsKnown` listhTakeLen is sh
listhTakeLen (_ `PCons` _) ZH = error "Permutation longer than shape"

listhDropLen :: forall i is sh. Perm is -> ListH sh i -> ListH (DropLen is sh) i
listhDropLen PNil sh = sh
listhDropLen (_ `PCons` is) (_ `ConsUnknown` sh) = listhDropLen is sh
listhDropLen (_ `PCons` is) (_ `ConsKnown` sh) = listhDropLen is sh
listhDropLen (_ `PCons` _) ZH = error "Permutation longer than shape"

listhPermute :: forall i is sh. Perm is -> ListH sh i -> ListH (Permute is sh) i
listhPermute PNil _ = ZH
listhPermute (i `PCons` (is :: Perm is')) (sh :: ListH sh i) =
  case listhIndex i sh of
    SUnknown x -> x `ConsUnknown` listhPermute is sh
    SKnown x -> x `ConsKnown` listhPermute is sh

listhIndex :: forall i k sh. SNat k -> ListH sh i -> SMayNat i (Index k sh)
listhIndex SZ (n `ConsUnknown` _) = SUnknown n
listhIndex SZ (n `ConsKnown` _) = SKnown n
listhIndex (SS (i :: SNat k')) ((_ :: i) `ConsUnknown` (sh :: ListH sh' i))
  | Refl <- lemIndexSucc (Proxy @k') (Proxy @Nothing) (Proxy @sh')
  = listhIndex i sh
listhIndex (SS (i :: SNat k')) ((_ :: SNat n) `ConsKnown` (sh :: ListH sh' i))
  | Refl <- lemIndexSucc (Proxy @k') (Proxy @(Just n)) (Proxy @sh')
  = listhIndex i sh
listhIndex _ ZH = error "Index into empty shape"

listhPermutePrefix :: forall i is sh. Perm is -> ListH sh i -> ListH (PermutePrefix is sh) i
listhPermutePrefix perm sh = listhAppend (listhPermute perm (listhTakeLen perm sh)) (listhDropLen perm sh)

ssxTakeLen :: forall is sh. Perm is -> StaticShX sh -> StaticShX (TakeLen is sh)
ssxTakeLen = coerce (listhTakeLen @())

ssxDropLen :: Perm is -> StaticShX sh -> StaticShX (DropLen is sh)
ssxDropLen = coerce (listhDropLen @())

ssxPermute :: Perm is -> StaticShX sh -> StaticShX (Permute is sh)
ssxPermute = coerce (listhPermute @())

ssxIndex :: SNat k -> StaticShX sh -> SMayNat () (Index k sh)
ssxIndex k = coerce (listhIndex @() k)

ssxPermutePrefix :: Perm is -> StaticShX sh -> StaticShX (PermutePrefix is sh)
ssxPermutePrefix = coerce (listhPermutePrefix @())

shxTakeLen :: forall is sh. Perm is -> IShX sh -> IShX (TakeLen is sh)
shxTakeLen = coerce (listhTakeLen @Int)

shxDropLen :: Perm is -> IShX sh -> IShX (DropLen is sh)
shxDropLen = coerce (listhDropLen @Int)

shxPermute :: Perm is -> IShX sh -> IShX (Permute is sh)
shxPermute = coerce (listhPermute @Int)

shxIndex :: forall k sh i. SNat k -> ShX sh i -> SMayNat i (Index k sh)
shxIndex k = coerce (listhIndex @i k)

shxPermutePrefix :: Perm is -> IShX sh -> IShX (PermutePrefix is sh)
shxPermutePrefix = coerce (listhPermutePrefix @Int)


listxTakeLen :: forall i is sh. Perm is -> ListX sh i -> ListX (TakeLen is sh) i
listxTakeLen PNil _ = ZX
listxTakeLen (_ `PCons` is) (n ::% sh) = n ::% listxTakeLen is sh
listxTakeLen (_ `PCons` _) ZX = error "Permutation longer than shape"

listxDropLen :: forall i is sh. Perm is -> ListX sh i -> ListX (DropLen is sh) i
listxDropLen PNil sh = sh
listxDropLen (_ `PCons` is) (_ ::% sh) = listxDropLen is sh
listxDropLen (_ `PCons` _) ZX = error "Permutation longer than shape"

listxPermute :: forall i is sh. Perm is -> ListX sh i -> ListX (Permute is sh) i
listxPermute PNil _ = ZX
listxPermute (i `PCons` (is :: Perm is')) (sh :: ListX sh f) =
  listxIndex i sh ::% listxPermute is sh

listxIndex :: forall j i sh. SNat i -> ListX sh j -> j
listxIndex SZ (n ::% _) = n
listxIndex (SS i) (_ ::% sh) = listxIndex i sh
listxIndex _ ZX = error "Index into empty shape"

listxPermutePrefix :: forall i is sh. Perm is -> ListX sh i -> ListX (PermutePrefix is sh) i
listxPermutePrefix perm sh = listxAppend (listxPermute perm (listxTakeLen perm sh)) (listxDropLen perm sh)

ixxPermutePrefix :: forall i is sh. Perm is -> IxX sh i -> IxX (PermutePrefix is sh) i
ixxPermutePrefix = coerce (listxPermutePrefix @i)

-- * Operations on permutations

permInverse :: Perm is
            -> (forall is'.
                     IsPermutation is'
                  => Perm is'
                  -> (forall sh. Rank sh ~ Rank is => StaticShX sh -> Permute is' (Permute is sh) :~: sh)
                  -> r)
            -> r
permInverse = \perm k ->
  genPerm perm $ \(invperm :: Perm is') ->
    fromMaybe
      (error $ "permInverse: did not generate permutation? perm = " ++ show perm
               ++ " ; invperm = " ++ show invperm)
      (permCheckPermutation invperm
        (k invperm
           (\ssh -> case permCheckInverse perm invperm ssh of
                      Just eq -> eq
                      Nothing -> error $ "permInverse: did not generate inverse? perm = " ++ show perm
                                             ++ " ; invperm = " ++ show invperm)))
  where
    genPerm :: Perm is -> (forall is'. Perm is' -> r) -> r
    genPerm perm =
      let permList = permToList' perm
      in toHList $ map snd (sort (zip permList [0..]))
      where
        toHList :: [Natural] -> (forall is'. Perm is' -> r) -> r
        toHList [] k = k PNil
        toHList (n : ns) k = toHList ns $ \l -> TN.withSomeSNat n $ \sn -> k (PCons sn l)

    permCheckInverse :: Perm is -> Perm is' -> StaticShX sh
                     -> Maybe (Permute is' (Permute is sh) :~: sh)
    permCheckInverse perm perminv ssh =
      ssxEqType (ssxPermute perminv (ssxPermute perm ssh)) ssh

type family MapSucc is where
  MapSucc '[] = '[]
  MapSucc (i : is) = i + 1 : MapSucc is

permShift1 :: Perm l -> Perm (0 : MapSucc l)
permShift1 = (SNat @0 `PCons`) . permMapSucc
  where
    permMapSucc :: Perm l -> Perm (MapSucc l)
    permMapSucc PNil = PNil
    permMapSucc ((SNat :: SNat i) `PCons` ns) = SNat @(i + 1) `PCons` permMapSucc ns


-- * Lemmas

lemRankPermute :: Proxy sh -> Perm is -> Rank (Permute is sh) :~: Rank is
lemRankPermute _ PNil = Refl
lemRankPermute p (_ `PCons` is) | Refl <- lemRankPermute p is = Refl

lemRankDropLen :: forall is sh. (Rank is <= Rank sh)
               => StaticShX sh -> Perm is -> Rank (DropLen is sh) :~: Rank sh - Rank is
lemRankDropLen ZKX PNil = Refl
lemRankDropLen (_ :!% sh) (_ `PCons` is)
  | Refl <- lemRankDropLen sh is
#if MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
  = Refl
#else
  = unsafeCoerceRefl
#endif
lemRankDropLen (_ :!% _) PNil = Refl
lemRankDropLen ZKX (_ `PCons` _) = error "1 <= 0"

lemIndexSucc :: Proxy i -> Proxy a -> Proxy l
             -> Index (i + 1) (a : l) :~: Index i l
lemIndexSucc _ _ _ = unsafeCoerceRefl
