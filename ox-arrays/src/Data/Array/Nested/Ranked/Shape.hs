{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Data.Array.Nested.Ranked.Shape where

import Control.DeepSeq (NFData(..))
import Data.Coerce (coerce)
import Data.Foldable qualified as Foldable
import Data.Kind (Type)
import Data.Proxy
import Data.Type.Equality
import GHC.Exts (build)
import GHC.IsList (IsList)
import GHC.IsList qualified as IsList
import GHC.TypeLits
import GHC.TypeNats qualified as TN
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation
import Data.Array.Nested.Types


-- * Ranked lists

type role ListR nominal representational
type ListR :: Nat -> Type -> Type
data ListR n i where
  ZR :: ListR 0 i
  (:::) :: forall n {i}. i -> ListR n i -> ListR (n + 1) i
deriving instance Eq i => Eq (ListR n i)
deriving instance Ord i => Ord (ListR n i)
infixr 3 :::

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (ListR n i)
#else
instance Show i => Show (ListR n i) where
  showsPrec _ = listrShow shows
#endif

instance NFData i => NFData (ListR n i) where
  rnf ZR = ()
  rnf (x ::: l) = rnf x `seq` rnf l

instance Functor (ListR n) where
  {-# INLINE fmap #-}
  fmap _ ZR = ZR
  fmap f (x ::: xs) = f x ::: fmap f xs

instance Foldable (ListR n) where
  {-# INLINE foldMap #-}
  foldMap _ ZR = mempty
  foldMap f (x ::: xs) = f x <> foldMap f xs
  {-# INLINE foldr #-}
  foldr _ z ZR = z
  foldr f z (x ::: xs) = f x (foldr f z xs)
  toList = listrToList
  null ZR = False
  null _ = True

data UnconsListRRes i n1 =
  forall n. (n + 1 ~ n1) => UnconsListRRes (ListR n i) i
listrUncons :: ListR n1 i -> Maybe (UnconsListRRes i n1)
listrUncons (i ::: sh') = Just (UnconsListRRes sh' i)
listrUncons ZR = Nothing

-- | This checks only whether the ranks are equal, not whether the actual
-- values are.
listrEqRank :: ListR n i -> ListR n' i -> Maybe (n :~: n')
listrEqRank ZR ZR = Just Refl
listrEqRank (_ ::: sh) (_ ::: sh')
  | Just Refl <- listrEqRank sh sh'
  = Just Refl
listrEqRank _ _ = Nothing

-- | This compares the lists for value equality.
listrEqual :: Eq i => ListR n i -> ListR n' i -> Maybe (n :~: n')
listrEqual ZR ZR = Just Refl
listrEqual (i ::: sh) (j ::: sh')
  | Just Refl <- listrEqual sh sh'
  , i == j
  = Just Refl
listrEqual _ _ = Nothing

{-# INLINE listrShow #-}
listrShow :: forall n i. (i -> ShowS) -> ListR n i -> ShowS
listrShow f l = showString "[" . go "" l . showString "]"
  where
    go :: String -> ListR n' i -> ShowS
    go _ ZR = id
    go prefix (x ::: xs) = showString prefix . f x . go "," xs

listrLength :: ListR n i -> Int
listrLength = length

listrRank :: ListR n i -> SNat n
listrRank ZR = SNat
listrRank (_ ::: sh) = snatSucc (listrRank sh)

listrAppend :: ListR n i -> ListR m i -> ListR (n + m) i
listrAppend ZR sh = sh
listrAppend (x ::: xs) sh = x ::: listrAppend xs sh

listrFromList :: SNat n -> [i] -> ListR n i
listrFromList topsn topl = go topsn topl
  where
    go :: SNat n' -> [i] -> ListR n' i
    go SZ [] = ZR
    go (SS n) (i : is) = i ::: go n is
    go _ _ = error $ "listrFromList: Mismatched list length (type says "
                     ++ show (fromSNat topsn) ++ ", list has length "
                     ++ show (length topl) ++ ")"

{-# INLINEABLE listrToList #-}
listrToList :: ListR n i -> [i]
listrToList list = build (\(cons :: i -> is -> is) (nil :: is) ->
  let go :: ListR n i -> is
      go ZR = nil
      go (i ::: is) = i `cons` go is
  in go list)

listrHead :: ListR (n + 1) i -> i
listrHead (i ::: _) = i

listrTail :: ListR (n + 1) i -> ListR n i
listrTail (_ ::: sh) = sh

listrInit :: ListR (n + 1) i -> ListR n i
listrInit (n ::: sh@(_ ::: _)) = n ::: listrInit sh
listrInit (_ ::: ZR) = ZR

listrLast :: ListR (n + 1) i -> i
listrLast (_ ::: sh@(_ ::: _)) = listrLast sh
listrLast (n ::: ZR) = n

-- | Performs a runtime check that the lengths are identical.
listrCast :: SNat n' -> ListR n i -> ListR n' i
listrCast = listrCastWithName "listrCast"

listrIndex :: forall k n i. (k + 1 <= n) => SNat k -> ListR n i -> i
listrIndex SZ (x ::: _) = x
listrIndex (SS i) (_ ::: xs) | Refl <- lemLeqSuccSucc (Proxy @k) (Proxy @n) = listrIndex i xs
listrIndex _ ZR = error "k + 1 <= 0"

listrZip :: ListR n i -> ListR n j -> ListR n (i, j)
listrZip ZR ZR = ZR
listrZip (i ::: irest) (j ::: jrest) = (i, j) ::: listrZip irest jrest
listrZip _ _ = error "listrZip: impossible pattern needlessly required"

{-# INLINE listrZipWith #-}
listrZipWith :: (i -> j -> k) -> ListR n i -> ListR n j -> ListR n k
listrZipWith _ ZR ZR = ZR
listrZipWith f (i ::: irest) (j ::: jrest) =
  f i j ::: listrZipWith f irest jrest
listrZipWith _ _ _ =
  error "listrZipWith: impossible pattern needlessly required"

listrSplitAt :: m <= n' => SNat m -> ListR n' i -> (ListR m i, ListR (n' - m) i)
listrSplitAt SZ sh = (ZR, sh)
listrSplitAt (SS m) (n ::: sh) = (\(pre, post) -> (n ::: pre, post)) (listrSplitAt m sh)
listrSplitAt SS{} ZR = error "m' + 1 <= 0"

listrPermutePrefix :: forall i n. PermR -> ListR n i -> ListR n i
listrPermutePrefix = \perm sh ->
  TN.withSomeSNat (fromIntegral (length perm)) $ \permlen@SNat ->
  case listrRank sh of { shlen@SNat ->
  let sperm = listrFromList permlen perm in
  case cmpNat permlen shlen of
    LTI -> let (pre, post) = listrSplitAt permlen sh in listrAppend (applyPermRFull permlen sperm pre) post
    EQI -> let (pre, post) = listrSplitAt permlen sh in listrAppend (applyPermRFull permlen sperm pre) post
    GTI -> error $ "Length of permutation (" ++ show (fromSNat' permlen) ++ ")"
                   ++ " > length of shape (" ++ show (fromSNat' shlen) ++ ")"
  }
  where
    applyPermRFull :: SNat m -> ListR k Int -> ListR m i -> ListR k i
    applyPermRFull _ ZR _ = ZR
    applyPermRFull sm@SNat (i ::: perm) l =
      TN.withSomeSNat (fromIntegral i) $ \si@(SNat :: SNat idx) ->
        case cmpNat (SNat @(idx + 1)) sm of
          LTI -> listrIndex si l ::: applyPermRFull sm perm l
          EQI -> listrIndex si l ::: applyPermRFull sm perm l
          GTI -> error "listrPermutePrefix: Index in permutation out of range"


-- * Ranked indices

-- | An index into a rank-typed array.
type role IxR nominal representational
type IxR :: Nat -> Type -> Type
newtype IxR n i = IxR (ListR n i)
  deriving (Eq, Ord, NFData, Functor, Foldable)

pattern ZIR :: forall n i. () => n ~ 0 => IxR n i
pattern ZIR = IxR ZR

pattern (:.:)
  :: forall {n1} {i}.
     forall n. (n + 1 ~ n1)
  => i -> IxR n i -> IxR n1 i
pattern i :.: sh <- IxR (listrUncons -> Just (UnconsListRRes (IxR -> sh) i))
  where i :.: IxR sh = IxR (i ::: sh)
infixr 3 :.:

{-# COMPLETE ZIR, (:.:) #-}

-- For convenience, this contains regular 'Int's instead of bounded integers
-- (traditionally called \"@Fin@\").
type IIxR n = IxR n Int

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (IxR n i)
#else
instance Show i => Show (IxR n i) where
  showsPrec _ (IxR l) = listrShow shows l
#endif

ixrLength :: IxR sh i -> Int
ixrLength (IxR l) = listrLength l

ixrRank :: IxR n i -> SNat n
ixrRank (IxR sh) = listrRank sh

ixrZero :: SNat n -> IIxR n
ixrZero SZ = ZIR
ixrZero (SS n) = 0 :.: ixrZero n

{-# INLINEABLE ixrFromList #-}
ixrFromList :: forall n i. SNat n -> [i] -> IxR n i
ixrFromList = coerce (listrFromList @_ @i)

ixrToList :: IxR n i -> [i]
ixrToList = Foldable.toList

ixrHead :: IxR (n + 1) i -> i
ixrHead (IxR list) = listrHead list

ixrTail :: IxR (n + 1) i -> IxR n i
ixrTail (IxR list) = IxR (listrTail list)

ixrInit :: IxR (n + 1) i -> IxR n i
ixrInit (IxR list) = IxR (listrInit list)

ixrLast :: IxR (n + 1) i -> i
ixrLast (IxR list) = listrLast list

-- | Performs a runtime check that the lengths are identical.
ixrCast :: SNat n' -> IxR n i -> IxR n' i
ixrCast n (IxR idx) = IxR (listrCastWithName "ixrCast" n idx)

ixrAppend :: forall n m i. IxR n i -> IxR m i -> IxR (n + m) i
ixrAppend = coerce (listrAppend @_ @i)

ixrZip :: IxR n i -> IxR n j -> IxR n (i, j)
ixrZip (IxR l1) (IxR l2) = IxR $ listrZip l1 l2

{-# INLINE ixrZipWith #-}
ixrZipWith :: (i -> j -> k) -> IxR n i -> IxR n j -> IxR n k
ixrZipWith f (IxR l1) (IxR l2) = IxR $ listrZipWith f l1 l2

ixrPermutePrefix :: forall n i. PermR -> IxR n i -> IxR n i
ixrPermutePrefix = coerce (listrPermutePrefix @i)

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer.
{-# INLINEABLE ixrToLinear #-}
ixrToLinear :: Num i => IShR m -> IxR m i -> i
ixrToLinear (ShR sh) ix = ixxToLinear sh (ixxFromIxR ix)

ixxFromIxR :: IxR n i -> IxX (Replicate n Nothing) i
ixxFromIxR = unsafeCoerce  -- TODO: switch to coerce once newtypes overhauled

{-# INLINEABLE ixrFromLinear #-}
ixrFromLinear :: forall i m. Num i => IShR m -> Int -> IxR m i
ixrFromLinear (ShR sh) i
  | Refl <- lemRankReplicate (Proxy @m)
  = ixrFromIxX $ ixxFromLinear sh i

ixrFromIxX :: IxX sh i -> IxR (Rank sh) i
ixrFromIxX = unsafeCoerce  -- TODO: switch to coerce once newtypes overhauled

shrEnum :: IShR n -> [IIxR n]
shrEnum = shrEnum'

{-# INLINABLE shrEnum' #-}  -- ensure this can be specialised at use site
shrEnum' :: forall i n. Num i => IShR n -> [IxR n i]
shrEnum' (ShR sh)
  | Refl <- lemRankReplicate (Proxy @n)
  = (unsafeCoerce :: [IxX (Replicate n Nothing) i] -> [IxR n i]) $ shxEnum' sh
      -- TODO: switch to coerce once newtypes overhauled

-- * Ranked shapes

type role ShR nominal representational
type ShR :: Nat -> Type -> Type
newtype ShR n i = ShR (ShX (Replicate n Nothing) i)
  deriving (Eq, Ord, NFData, Functor)

pattern ZSR :: forall n i. () => n ~ 0 => ShR n i
pattern ZSR <- ShR (matchZSR @n -> Just Refl)
  where ZSR = ShR ZSX

matchZSR :: forall n i. ShX (Replicate n Nothing) i -> Maybe (n :~: 0)
matchZSR ZSX | Refl <- lemReplicateEmpty (Proxy @n) Refl = Just Refl
matchZSR _ = Nothing

pattern (:$:)
  :: forall {n1} {i}.
     forall n. (n + 1 ~ n1)
  => i -> ShR n i -> ShR n1 i
pattern i :$: shl <- (shrUncons -> Just (UnconsShRRes shl i))
  where i :$: ShR shl | Refl <- lemReplicateSucc2 (Proxy @n1) Refl
                      = ShR (SUnknown i :$% shl)

data UnconsShRRes i n1 =
  forall n. (n + 1 ~ n1) => UnconsShRRes (ShR n i) i
shrUncons :: forall n1 i. ShR n1 i -> Maybe (UnconsShRRes i n1)
shrUncons (ShR (SUnknown x :$% (sh' :: ShX sh' i)))
  | Refl <- lemReplicateCons (Proxy @sh') (Proxy @n1) Refl
  , Refl <- lemReplicateCons2 (Proxy @sh') (Proxy @n1) Refl
  = Just (UnconsShRRes (ShR sh') x)
shrUncons (ShR _) = Nothing

infixr 3 :$:

{-# COMPLETE ZSR, (:$:) #-}

type IShR n = ShR n Int

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (ShR n i)
#else
instance Show i => Show (ShR n i) where
  showsPrec d (ShR l) = showsPrec d l
#endif

-- | This checks only whether the ranks are equal, not whether the actual
-- values are.
shrEqRank :: ShR n i -> ShR n' i -> Maybe (n :~: n')
shrEqRank ZSR ZSR = Just Refl
shrEqRank (_ :$: sh) (_ :$: sh')
  | Just Refl <- shrEqRank sh sh'
  = Just Refl
shrEqRank _ _ = Nothing

-- | This compares the shapes for value equality.
shrEqual :: Eq i => ShR n i -> ShR n' i -> Maybe (n :~: n')
shrEqual ZSR ZSR = Just Refl
shrEqual (i :$: sh) (i' :$: sh')
  | Just Refl <- shrEqual sh sh'
  , i == i'
  = Just Refl
shrEqual _ _ = Nothing

shrLength :: ShR sh i -> Int
shrLength (ShR l) = shxLength l

-- | This function can also be used to conjure up a 'KnownNat' dictionary;
-- pattern matching on the returned 'SNat' with the 'pattern SNat' pattern
-- synonym yields 'KnownNat' evidence.
shrRank :: forall n i. ShR n i -> SNat n
shrRank (ShR sh) | Refl <- lemRankReplicate (Proxy @n) = shxRank sh

-- | The number of elements in an array described by this shape.
shrSize :: IShR n -> Int
shrSize (ShR sh) = shxSize sh

-- This is equivalent to but faster than @coerce (shxFromList (ssxReplicate snat))@.
-- We don't report the size of the list in case of errors in order not to retain the list.
{-# INLINEABLE shrFromList #-}
shrFromList :: SNat n -> [Int] -> IShR n
shrFromList snat topl = ShR $ ShX $ go snat topl
  where
    go :: SNat n -> [Int] -> ListH (Replicate n Nothing) Int
    go SZ [] = ZH
    go SZ _ = error $ "shrFromList: List too long (type says " ++ show (fromSNat' snat) ++ ")"
    go (SS sn :: SNat n1) (i : is) | Refl <- lemReplicateSucc2 (Proxy @n1) Refl = ConsUnknown i (go sn is)
    go _ _ = error $ "shrFromList: List too short (type says " ++ show (fromSNat' snat) ++ ")"

-- This is equivalent to but faster than @coerce shxToList@.
{-# INLINEABLE shrToList #-}
shrToList :: IShR n -> [Int]
shrToList (ShR (ShX l)) = build (\(cons :: i -> is -> is) (nil :: is) ->
  let go :: ListH sh Int -> is
      go ZH = nil
      go (ConsUnknown i rest) = i `cons` go rest
      go ConsKnown{} = error "shrToList: impossible case"
  in go l)

shrHead :: forall n i. ShR (n + 1) i -> i
shrHead (ShR sh)
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = case shxHead @Nothing @(Replicate n Nothing) sh of
      SUnknown i -> i

shrTail :: forall n i. ShR (n + 1) i -> ShR n i
shrTail
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = coerce (shxTail @_ @_ @i)

shrInit :: forall n i. ShR (n + 1) i -> ShR n i
shrInit
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = -- TODO: change this and all other unsafeCoerceRefl to lemmas:
    gcastWith (unsafeCoerceRefl
               :: Init (Replicate (n + 1) (Nothing @Nat)) :~: Replicate n Nothing) $
    coerce (shxInit @_ @_ @i)

shrLast :: forall n i. ShR (n + 1) i -> i
shrLast (ShR sh)
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = case shxLast sh of
      SUnknown i -> i
      SKnown{} -> error "shrLast: impossible SKnown"

-- | Performs a runtime check that the lengths are identical.
shrCast :: SNat n' -> ShR n i -> ShR n' i
shrCast SZ ZSR = ZSR
shrCast (SS n) (i :$: sh) = i :$: shrCast n sh
shrCast _ _ = error "shrCast: ranks don't match"

shrAppend :: forall n m i. ShR n i -> ShR m i -> ShR (n + m) i
shrAppend =
  -- lemReplicatePlusApp requires an SNat
  gcastWith (unsafeCoerceRefl
             :: Replicate n (Nothing @Nat) ++ Replicate m Nothing :~: Replicate (n + m) Nothing) $
  coerce (shxAppend @_ @_ @i)

{-# INLINE shrZipWith #-}
shrZipWith :: (i -> j -> k) -> ShR n i -> ShR n j -> ShR n k
shrZipWith _ ZSR ZSR = ZSR
shrZipWith f (i :$: irest) (j :$: jrest) =
  f i j :$: shrZipWith f irest jrest
shrZipWith _ _ _ =
  error "shrZipWith: impossible pattern needlessly required"

shrSplitAt :: m <= n' => SNat m -> ShR n' i -> (ShR m i, ShR (n' - m) i)
shrSplitAt SZ sh = (ZSR, sh)
shrSplitAt (SS m) (n :$: sh) = (\(pre, post) -> (n :$: pre, post)) (shrSplitAt m sh)
shrSplitAt SS{} ZSR = error "m' + 1 <= 0"

shrIndex :: forall k sh i. SNat k -> ShR sh i -> i
shrIndex k (ShR sh) = case shxIndex @_ @_ @i k sh of
  SUnknown i -> i
  SKnown{} -> error "shrIndex: impossible SKnown"

-- Copy-pasted from listrPermutePrefix, probably unavoidably.
shrPermutePrefix :: forall i n. PermR -> ShR n i -> ShR n i
shrPermutePrefix = \perm sh ->
  TN.withSomeSNat (fromIntegral (length perm)) $ \permlen@SNat ->
  case shrRank sh of { shlen@SNat ->
  let sperm = shrFromList permlen perm in
  case cmpNat permlen shlen of
    LTI -> let (pre, post) = shrSplitAt permlen sh in shrAppend (applyPermRFull permlen sperm pre) post
    EQI -> let (pre, post) = shrSplitAt permlen sh in shrAppend (applyPermRFull permlen sperm pre) post
    GTI -> error $ "Length of permutation (" ++ show (fromSNat' permlen) ++ ")"
                   ++ " > length of shape (" ++ show (fromSNat' shlen) ++ ")"
  }
  where
    applyPermRFull :: SNat m -> ShR k Int -> ShR m i -> ShR k i
    applyPermRFull _ ZSR _ = ZSR
    applyPermRFull sm@SNat (i :$: perm) l =
      TN.withSomeSNat (fromIntegral i) $ \si@(SNat :: SNat idx) ->
        case cmpNat (SNat @(idx + 1)) sm of
          LTI -> shrIndex si l :$: applyPermRFull sm perm l
          EQI -> shrIndex si l :$: applyPermRFull sm perm l
          GTI -> error "shrPermutePrefix: Index in permutation out of range"


-- | Untyped: length is checked at runtime.
instance KnownNat n => IsList (ListR n i) where
  type Item (ListR n i) = i
  fromList = listrFromList (SNat @n)
  toList = Foldable.toList

-- | Untyped: length is checked at runtime.
instance KnownNat n => IsList (IxR n i) where
  type Item (IxR n i) = i
  fromList = IxR . IsList.fromList
  toList = Foldable.toList

-- | Untyped: length is checked at runtime.
instance KnownNat n => IsList (IShR n) where
  type Item (IShR n) = Int
  fromList = shrFromList (SNat @n)
  toList = shrToList


-- * Internal helper functions

listrCastWithName :: String -> SNat n' -> ListR n i -> ListR n' i
listrCastWithName _ SZ ZR = ZR
listrCastWithName name (SS n) (i ::: l) = i ::: listrCastWithName name n l
listrCastWithName name _ _ = error $ name ++ ": ranks don't match"
