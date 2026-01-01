{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
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
module Data.Array.Nested.Mixed.Shape where

import Control.DeepSeq (NFData(..))
import Data.Bifunctor (first)
import Data.Coerce
import Data.Foldable qualified as Foldable
import Data.Kind (Constraint, Type)
import Data.Monoid (Sum(..))
import Data.Proxy
import Data.Type.Equality
import GHC.Exts (Int(..), Int#, build, quotRemInt#, withDict)
import GHC.IsList (IsList)
import GHC.IsList qualified as IsList
import GHC.TypeLits
#if !MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
import GHC.TypeLits.Orphans ()
#endif

import Data.Array.Nested.Types


-- | The length of a type-level list. If the argument is a shape, then the
-- result is the rank of that shape.
type family Rank sh where
  Rank '[] = 0
  Rank (_ : sh) = Rank sh + 1


-- * Mixed lists to be used IxX and shaped and ranked lists and indexes

type role ListX nominal representational
type ListX :: [Maybe Nat] -> Type -> Type
data ListX sh i where
  ZX :: ListX '[] i
  (::%) :: forall n sh {i}. i -> ListX sh i -> ListX (n : sh) i
deriving instance Eq i => Eq (ListX sh i)
deriving instance Ord i => Ord (ListX sh i)
infixr 3 ::%

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (ListX sh i)
#else
instance Show i => Show (ListX sh i) where
  showsPrec _ = listxShow shows
#endif

instance NFData i => NFData (ListX sh i) where
  rnf ZX = ()
  rnf (x ::% l) = rnf x `seq` rnf l

data UnconsListXRes i sh1 =
  forall n sh. (n : sh ~ sh1) => UnconsListXRes (ListX sh i) i
listxUncons :: ListX sh1 f -> Maybe (UnconsListXRes f sh1)
listxUncons (i ::% shl') = Just (UnconsListXRes shl' i)
listxUncons ZX = Nothing

instance Functor (ListX l) where
  {-# INLINE fmap #-}
  fmap _ ZX = ZX
  fmap f (x ::% xs) = f x ::% fmap f xs

instance Foldable (ListX l) where
  {-# INLINE foldMap #-}
  foldMap _ ZX = mempty
  foldMap f (x ::% xs) = f x <> foldMap f xs
  {-# INLINE foldr #-}
  foldr _ z ZX = z
  foldr f z (x ::% xs) = f x (foldr f z xs)
  toList = listxToList
  null ZX = False
  null _ = True

listxLength :: ListX sh i -> Int
listxLength = length

listxRank :: ListX sh i -> SNat (Rank sh)
listxRank ZX = SNat
listxRank (_ ::% l) | SNat <- listxRank l = SNat

{-# INLINE listxShow #-}
listxShow :: forall sh i. (i -> ShowS) -> ListX sh i -> ShowS
listxShow f l = showString "[" . go "" l . showString "]"
  where
    go :: String -> ListX sh' i -> ShowS
    go _ ZX = id
    go prefix (x ::% xs) = showString prefix . f x . go "," xs

listxFromList :: StaticShX sh -> [i] -> ListX sh i
listxFromList topssh topl = go topssh topl
  where
    go :: StaticShX sh' -> [i] -> ListX sh' i
    go ZKX [] = ZX
    go (_ :!% sh) (i : is) = i ::% go sh is
    go _ _ = error $ "listxFromList: Mismatched list length (type says "
                       ++ show (ssxLength topssh) ++ ", list has length "
                       ++ show (length topl) ++ ")"

{-# INLINEABLE listxToList #-}
listxToList :: ListX sh i -> [i]
listxToList list = build (\(cons :: i -> is -> is) (nil :: is) ->
  let go :: ListX sh i -> is
      go ZX = nil
      go (i ::% is) = i `cons` go is
  in go list)

listxHead :: ListX (mn ': sh) i -> i
listxHead (i ::% _) = i

listxTail :: ListX (n : sh) i -> ListX sh i
listxTail (_ ::% sh) = sh

listxAppend :: ListX sh i -> ListX sh' i -> ListX (sh ++ sh') i
listxAppend ZX idx' = idx'
listxAppend (i ::% idx) idx' = i ::% listxAppend idx idx'

listxDrop :: forall i j sh sh'. ListX sh j -> ListX (sh ++ sh') i -> ListX sh' i
listxDrop ZX long = long
listxDrop (_ ::% short) long = case long of _ ::% long' -> listxDrop short long'

listxInit :: forall i n sh. ListX (n : sh) i -> ListX (Init (n : sh)) i
listxInit (i ::% sh@(_ ::% _)) = i ::% listxInit sh
listxInit (_ ::% ZX) = ZX

listxLast :: forall i n sh. ListX (n : sh) i -> i
listxLast (_ ::% sh@(_ ::% _)) = listxLast sh
listxLast (x ::% ZX) = x

{-# INLINE listxZipWith #-}
listxZipWith :: (i -> j -> k) -> ListX sh i -> ListX sh j -> ListX sh k
listxZipWith _ ZX ZX = ZX
listxZipWith f (i ::% is) (j ::% js) = f i j ::% listxZipWith f is js


-- * Mixed indices

-- | An index into a mixed-typed array.
type role IxX nominal representational
type IxX :: [Maybe Nat] -> Type -> Type
newtype IxX sh i = IxX (ListX sh i)
  deriving (Eq, Ord, NFData, Functor, Foldable)

pattern ZIX :: forall sh i. () => sh ~ '[] => IxX sh i
pattern ZIX = IxX ZX

pattern (:.%)
  :: forall {sh1} {i}.
     forall n sh. (n : sh ~ sh1)
  => i -> IxX sh i -> IxX sh1 i
pattern i :.% shl <- IxX (listxUncons -> Just (UnconsListXRes (IxX -> shl) i))
  where i :.% IxX shl = IxX (i ::% shl)
infixr 3 :.%

{-# COMPLETE ZIX, (:.%) #-}

-- For convenience, this contains regular 'Int's instead of bounded integers
-- (traditionally called \"@Fin@\").
type IIxX sh = IxX sh Int

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (IxX sh i)
#else
instance Show i => Show (IxX sh i) where
  showsPrec _ (IxX l) = listxShow shows l
#endif

ixxLength :: IxX sh i -> Int
ixxLength (IxX l) = listxLength l

ixxRank :: IxX sh i -> SNat (Rank sh)
ixxRank (IxX l) = listxRank l

ixxZero :: StaticShX sh -> IIxX sh
ixxZero ZKX = ZIX
ixxZero (_ :!% ssh) = 0 :.% ixxZero ssh

ixxZero' :: IShX sh -> IIxX sh
ixxZero' ZSX = ZIX
ixxZero' (_ :$% sh) = 0 :.% ixxZero' sh

{-# INLINEABLE ixxFromList #-}
ixxFromList :: forall sh i. StaticShX sh -> [i] -> IxX sh i
ixxFromList = coerce (listxFromList @_ @i)

ixxToList :: IxX sh i -> [i]
ixxToList = Foldable.toList

ixxHead :: IxX (n : sh) i -> i
ixxHead (IxX list) = listxHead list

ixxTail :: IxX (n : sh) i -> IxX sh i
ixxTail (IxX list) = IxX (listxTail list)

ixxAppend :: forall sh sh' i. IxX sh i -> IxX sh' i -> IxX (sh ++ sh') i
ixxAppend = coerce (listxAppend @_ @i)

ixxDrop :: forall sh sh' i. IxX sh i -> IxX (sh ++ sh') i -> IxX sh' i
ixxDrop = coerce (listxDrop @i @i)

ixxInit :: forall n sh i. IxX (n : sh) i -> IxX (Init (n : sh)) i
ixxInit = coerce (listxInit @i)

ixxLast :: forall n sh i. IxX (n : sh) i -> i
ixxLast = coerce (listxLast @i)

ixxCast :: StaticShX sh' -> IxX sh i -> IxX sh' i
ixxCast ZKX ZIX = ZIX
ixxCast (_ :!% sh) (i :.% idx) = i :.% ixxCast sh idx
ixxCast _ _ = error "ixxCast: ranks don't match"

ixxZip :: IxX sh i -> IxX sh j -> IxX sh (i, j)
ixxZip ZIX ZIX = ZIX
ixxZip (i :.% is) (j :.% js) = (i, j) :.% ixxZip is js

{-# INLINE ixxZipWith #-}
ixxZipWith :: (i -> j -> k) -> IxX sh i -> IxX sh j -> IxX sh k
ixxZipWith _ ZIX ZIX = ZIX
ixxZipWith f (i :.% is) (j :.% js) = f i j :.% ixxZipWith f is js

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer.
{-# INLINEABLE ixxToLinear #-}
ixxToLinear :: Num i => IShX sh -> IxX sh i -> i
ixxToLinear = \sh i -> go sh i 0
  where
    go :: Num i => IShX sh -> IxX sh i -> i -> i
    go ZSX ZIX !a = a
    go (n :$% sh) (i :.% ix) a = go sh ix (fromIntegral (fromSMayNat' n) * a + i)

{-# INLINEABLE ixxFromLinear #-}
ixxFromLinear :: Num i => IShX sh -> Int -> IxX sh i
ixxFromLinear = \sh ->  -- give this function arity 1 so that suffixes is shared when it's called many times
    let suffixes = drop 1 (scanr (*) 1 (shxToList sh))
    in fromLin0 sh suffixes
  where
    -- Unfold first iteration of fromLin to do the range check.
    -- Don't inline this function at first to allow GHC to inline the outer
    -- function and realise that 'suffixes' is shared. But then later inline it
    -- anyway, to avoid the function call. Removing the pragma makes GHC
    -- somehow unable to recognise that 'suffixes' can be shared in a loop.
    {-# NOINLINE [0] fromLin0 #-}
    fromLin0 :: Num i => IShX sh -> [Int] -> Int -> IxX sh i
    fromLin0 sh suffixes i =
        if i < 0 then outrange sh i else
        case (sh, suffixes) of
          (ZSX, _) | i > 0 -> outrange sh i
                   | otherwise -> ZIX
          ((fromSMayNat' -> n) :$% sh', suff : suffs) ->
            let (q, r) = i `quotRem` suff
            in if q >= n then outrange sh i else
               fromIntegral q :.% fromLin sh' suffs r
          _ -> error "impossible"

    fromLin :: Num i => IShX sh -> [Int] -> Int -> IxX sh i
    fromLin ZSX _ !_ = ZIX
    fromLin (_ :$% sh') (suff : suffs) i =
      let (q, r) = i `quotRem` suff  -- suff == shrSize sh'
      in fromIntegral q :.% fromLin sh' suffs r
    fromLin _ _ _ = error "impossible"

    {-# NOINLINE outrange #-}
    outrange :: IShX sh -> Int -> a
    outrange sh i = error $ "ixxFromLinear: out of range (" ++ show i ++
                            " in array of shape " ++ show sh ++ ")"

shxEnum :: IShX sh -> [IIxX sh]
shxEnum = shxEnum'

{-# INLINABLE shxEnum' #-}  -- ensure this can be specialised at use site
shxEnum' :: Num i => IShX sh -> [IxX sh i]
shxEnum' sh = [fromLin sh suffixes li# | I# li# <- [0 .. shxSize sh - 1]]
  where
    suffixes = drop 1 (scanr (*) 1 (shxToList sh))

    fromLin :: Num i => IShX sh -> [Int] -> Int# -> IxX sh i
    fromLin ZSX _ _ = ZIX
    fromLin (_ :$% sh') (I# suff# : suffs) i# =
      let !(# q#, r# #) = i# `quotRemInt#` suff#  -- suff == shrSize sh'
      in fromIntegral (I# q#) :.% fromLin sh' suffs r#
    fromLin _ _ _ = error "impossible"


-- * Mixed shape-like lists to be used for ShX and StaticShX

data SMayNat i n where
  SUnknown :: i -> SMayNat i Nothing
  SKnown :: SNat n -> SMayNat i (Just n)
deriving instance Show i => Show (SMayNat i n)
deriving instance Eq i => Eq (SMayNat i n)
deriving instance Ord i => Ord (SMayNat i n)

instance (NFData i, forall m. NFData (SNat m)) => NFData (SMayNat i n) where
  rnf (SUnknown i) = rnf i
  rnf (SKnown x) = rnf x

instance TestEquality (SMayNat i) where
  testEquality SUnknown{} SUnknown{} = Just Refl
  testEquality (SKnown n) (SKnown m) | Just Refl <- testEquality n m = Just Refl
  testEquality _ _ = Nothing

{-# INLINE fromSMayNat #-}
fromSMayNat :: (n ~ Nothing => i -> r)
            -> (forall m. n ~ Just m => SNat m -> r)
            -> SMayNat i n -> r
fromSMayNat f _ (SUnknown i) = f i
fromSMayNat _ g (SKnown s) = g s

{-# INLINE fromSMayNat' #-}
fromSMayNat' :: SMayNat Int n -> Int
fromSMayNat' = fromSMayNat id fromSNat'

type family AddMaybe n m where
  AddMaybe Nothing _ = Nothing
  AddMaybe (Just _) Nothing = Nothing
  AddMaybe (Just n) (Just m) = Just (n + m)

smnAddMaybe :: SMayNat Int n -> SMayNat Int m -> SMayNat Int (AddMaybe n m)
smnAddMaybe (SUnknown n) m = SUnknown (n + fromSMayNat' m)
smnAddMaybe (SKnown n) (SUnknown m) = SUnknown (fromSNat' n + m)
smnAddMaybe (SKnown n) (SKnown m) = SKnown (snatPlus n m)


type role ListH nominal representational
type ListH :: [Maybe Nat] -> Type -> Type
data ListH sh i where
  ZH :: ListH '[] i
  ConsUnknown :: forall sh i. i -> ListH sh i -> ListH (Nothing : sh) i
-- TODO: bring this UNPACK back when GHC no longer crashes:
-- ConsKnown :: forall n sh i. {-# UNPACK #-} SNat n -> ListH sh i -> ListH (Just n : sh) i
  ConsKnown :: forall n sh i. SNat n -> ListH sh i -> ListH (Just n : sh) i
deriving instance Ord i => Ord (ListH sh i)

-- A manually defined instance and this INLINEABLE is needed to specialize
-- mdot1Inner (otherwise GHC warns specialization breaks down here).
instance Eq i => Eq (ListH sh i) where
  {-# INLINEABLE (==) #-}
  ZH == ZH = True
  ConsUnknown i1 sh1 == ConsUnknown i2 sh2 = i1 == i2 && sh1 == sh2
  ConsKnown _ sh1 == ConsKnown _ sh2 = sh1 == sh2

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (ListH sh i)
#else
instance Show i => Show (ListH sh i) where
  showsPrec _ = listhShow shows
#endif

instance NFData i => NFData (ListH sh i) where
  rnf ZH = ()
  rnf (x `ConsUnknown` l) = rnf x `seq` rnf l
  rnf (SNat `ConsKnown` l) = rnf l

data UnconsListHRes i sh1 =
  forall n sh. (n : sh ~ sh1) => UnconsListHRes (ListH sh i) (SMayNat i n)
listhUncons :: ListH sh1 i -> Maybe (UnconsListHRes i sh1)
listhUncons (i `ConsUnknown` shl') = Just (UnconsListHRes shl' (SUnknown i))
listhUncons (i `ConsKnown` shl') = Just (UnconsListHRes shl' (SKnown i))
listhUncons ZH = Nothing

-- | This checks only whether the types are equal; if the elements of the list
-- are not singletons, their values may still differ. This corresponds to
-- 'testEquality', except on the penultimate type parameter.
listhEqType :: ListH sh i -> ListH sh' i -> Maybe (sh :~: sh')
listhEqType ZH ZH = Just Refl
listhEqType (_ `ConsUnknown` sh) (_ `ConsUnknown` sh')
  | Just Refl <- listhEqType sh sh'
  = Just Refl
listhEqType (n `ConsKnown` sh) (m `ConsKnown` sh')
  | Just Refl <- testEquality n m
  , Just Refl <- listhEqType sh sh'
  = Just Refl
listhEqType _ _ = Nothing

-- | This checks whether the two lists actually contain equal values. This is
-- more than 'testEquality', and corresponds to @geq@ from @Data.GADT.Compare@
-- in the @some@ package (except on the penultimate type parameter).
listhEqual :: Eq i => ListH sh i -> ListH sh' i -> Maybe (sh :~: sh')
listhEqual ZH ZH = Just Refl
listhEqual (n `ConsUnknown` sh) (m `ConsUnknown` sh')
  | n == m
  , Just Refl <- listhEqual sh sh'
  = Just Refl
listhEqual (n `ConsKnown` sh) (m `ConsKnown` sh')
  | Just Refl <- testEquality n m
  , Just Refl <- listhEqual sh sh'
  = Just Refl
listhEqual _ _ = Nothing

{-# INLINE listhFmap #-}
listhFmap :: (forall n. SMayNat i n -> SMayNat j n) -> ListH sh i -> ListH sh j
listhFmap _ ZH = ZH
listhFmap f (x `ConsUnknown` xs) = case f (SUnknown x) of
  SUnknown y -> y `ConsUnknown` listhFmap f xs
listhFmap f (x `ConsKnown` xs) = case f (SKnown x) of
  SKnown y -> y `ConsKnown` listhFmap f xs

{-# INLINE listhFoldMap #-}
listhFoldMap :: Monoid m => (forall n. SMayNat i n -> m) -> ListH sh i -> m
listhFoldMap _ ZH = mempty
listhFoldMap f (x `ConsUnknown` xs) = f (SUnknown x) <> listhFoldMap f xs
listhFoldMap f (x `ConsKnown` xs) = f (SKnown x) <> listhFoldMap f xs

listhLength :: ListH sh i -> Int
listhLength = getSum . listhFoldMap (\_ -> Sum 1)

listhRank :: ListH sh i -> SNat (Rank sh)
listhRank ZH = SNat
listhRank (_ `ConsUnknown` l) | SNat <- listhRank l = SNat
listhRank (_ `ConsKnown` l) | SNat <- listhRank l = SNat

{-# INLINE listhShow #-}
listhShow :: forall sh i. (forall n. SMayNat i n -> ShowS) -> ListH sh i -> ShowS
listhShow f l = showString "[" . go "" l . showString "]"
  where
    go :: String -> ListH sh' i -> ShowS
    go _ ZH = id
    go prefix (x `ConsUnknown` xs) = showString prefix . f (SUnknown x) . go "," xs
    go prefix (x `ConsKnown` xs) = showString prefix . f (SKnown x) . go "," xs

listhHead :: ListH (mn ': sh) i -> SMayNat i mn
listhHead (i `ConsUnknown` _) = SUnknown i
listhHead (i `ConsKnown` _) = SKnown i

listhTail :: ListH (n : sh) i -> ListH sh i
listhTail (_ `ConsUnknown` sh) = sh
listhTail (_ `ConsKnown` sh) = sh

listhAppend :: ListH sh i -> ListH sh' i -> ListH (sh ++ sh') i
listhAppend ZH idx' = idx'
listhAppend (i `ConsUnknown` idx) idx' = i `ConsUnknown` listhAppend idx idx'
listhAppend (i `ConsKnown` idx) idx' = i `ConsKnown` listhAppend idx idx'

listhDrop :: forall i j sh sh'. ListH sh j -> ListH (sh ++ sh') i -> ListH sh' i
listhDrop ZH long = long
listhDrop (_ `ConsUnknown` short) long = case long of
  _ `ConsUnknown` long' -> listhDrop short long'
listhDrop (_ `ConsKnown` short) long = case long of
  _ `ConsKnown` long' -> listhDrop short long'

listhInit :: forall i n sh. ListH (n : sh) i -> ListH (Init (n : sh)) i
listhInit (i `ConsUnknown` sh@(_ `ConsUnknown` _)) = i `ConsUnknown` listhInit sh
listhInit (i `ConsUnknown` sh@(_ `ConsKnown` _)) = i `ConsUnknown` listhInit sh
listhInit (_ `ConsUnknown` ZH) = ZH
listhInit (i `ConsKnown` sh@(_ `ConsUnknown` _)) = i `ConsKnown` listhInit sh
listhInit (i `ConsKnown` sh@(_ `ConsKnown` _)) = i `ConsKnown` listhInit sh
listhInit (_ `ConsKnown` ZH) = ZH

listhLast :: forall i n sh. ListH (n : sh) i -> SMayNat i (Last (n : sh))
listhLast (_ `ConsUnknown` sh@(_ `ConsUnknown` _)) = listhLast sh
listhLast (_ `ConsUnknown` sh@(_ `ConsKnown` _)) = listhLast sh
listhLast (x `ConsUnknown` ZH) = SUnknown x
listhLast (_ `ConsKnown` sh@(_ `ConsUnknown` _)) = listhLast sh
listhLast (_ `ConsKnown` sh@(_ `ConsKnown` _)) = listhLast sh
listhLast (x `ConsKnown` ZH) = SKnown x

-- * Mixed shapes

-- | This is a newtype over 'ListH'.
type role ShX nominal representational
type ShX :: [Maybe Nat] -> Type -> Type
newtype ShX sh i = ShX (ListH sh i)
  deriving (Eq, Ord, NFData)

pattern ZSX :: forall sh i. () => sh ~ '[] => ShX sh i
pattern ZSX = ShX ZH

pattern (:$%)
  :: forall {sh1} {i}.
     forall n sh. (n : sh ~ sh1)
  => SMayNat i n -> ShX sh i -> ShX sh1 i
pattern i :$% shl <- ShX (listhUncons -> Just (UnconsListHRes (ShX -> shl) i))
  where i :$% ShX shl = case i of; SUnknown x -> ShX (x `ConsUnknown` shl); SKnown x -> ShX (x `ConsKnown` shl)
infixr 3 :$%

{-# COMPLETE ZSX, (:$%) #-}

type IShX sh = ShX sh Int

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (ShX sh i)
#else
instance Show i => Show (ShX sh i) where
  showsPrec _ (ShX l) = listhShow (fromSMayNat shows (shows . fromSNat)) l
#endif

instance Functor (ShX sh) where
  {-# INLINE fmap #-}
  fmap f (ShX l) = ShX (listhFmap (fromSMayNat (SUnknown . f) SKnown) l)

-- | This checks only whether the types are equal; unknown dimensions might
-- still differ. This corresponds to 'testEquality', except on the penultimate
-- type parameter.
shxEqType :: ShX sh i -> ShX sh' i -> Maybe (sh :~: sh')
shxEqType ZSX ZSX = Just Refl
shxEqType (SKnown n@SNat :$% sh) (SKnown m@SNat :$% sh')
  | Just Refl <- sameNat n m
  , Just Refl <- shxEqType sh sh'
  = Just Refl
shxEqType (SUnknown _ :$% sh) (SUnknown _ :$% sh')
  | Just Refl <- shxEqType sh sh'
  = Just Refl
shxEqType _ _ = Nothing

-- | This checks whether all dimensions have the same value. This is more than
-- 'testEquality', and corresponds to @geq@ from @Data.GADT.Compare@ in the
-- @some@ package (except on the penultimate type parameter).
shxEqual :: Eq i => ShX sh i -> ShX sh' i -> Maybe (sh :~: sh')
shxEqual ZSX ZSX = Just Refl
shxEqual (SKnown n@SNat :$% sh) (SKnown m@SNat :$% sh')
  | Just Refl <- sameNat n m
  , Just Refl <- shxEqual sh sh'
  = Just Refl
shxEqual (SUnknown i :$% sh) (SUnknown j :$% sh')
  | i == j
  , Just Refl <- shxEqual sh sh'
  = Just Refl
shxEqual _ _ = Nothing

shxLength :: ShX sh i -> Int
shxLength (ShX l) = listhLength l

shxRank :: ShX sh i -> SNat (Rank sh)
shxRank (ShX l) = listhRank l

-- | The number of elements in an array described by this shape.
shxSize :: IShX sh -> Int
shxSize ZSX = 1
shxSize (n :$% sh) = fromSMayNat' n * shxSize sh

-- We don't report the size of the list in case of errors in order not to retain the list.
{-# INLINEABLE shxFromList #-}
shxFromList :: StaticShX sh -> [Int] -> IShX sh
shxFromList (StaticShX topssh) topl = ShX $ go topssh topl
  where
    go :: ListH sh' () -> [Int] -> ListH sh' Int
    go ZH [] = ZH
    go ZH _ = error $ "shxFromList: List too long (type says " ++ show (listhLength topssh) ++ ")"
    go (ConsKnown sn sh) (i : is)
      | i == fromSNat' sn = ConsKnown sn (go sh is)
      | otherwise = error $ "shxFromList: Value does not match typing"
    go (ConsUnknown () sh) (i : is) = ConsUnknown i (go sh is)
    go _ _ = error $ "shxFromList: List too short (type says " ++ show (listhLength topssh) ++ ")"

{-# INLINEABLE shxToList #-}
shxToList :: IShX sh -> [Int]
shxToList (ShX l) = build (\(cons :: i -> is -> is) (nil :: is) ->
  let go :: ListH sh Int -> is
      go ZH = nil
      go (ConsUnknown i rest) = i `cons` go rest
      go (ConsKnown sn rest) = fromSNat' sn `cons` go rest
  in go l)

-- If it ever matters for performance, this is unsafeCoercible.
shxFromSSX :: StaticShX (MapJust sh) -> ShX (MapJust sh) i
shxFromSSX ZKX = ZSX
shxFromSSX (SKnown n :!% sh :: StaticShX (MapJust sh))
  | Refl <- lemMapJustCons @sh Refl
  = SKnown n :$% shxFromSSX sh
shxFromSSX (SUnknown _ :!% _) = error "unreachable"

-- | This may fail if @sh@ has @Nothing@s in it.
shxFromSSX2 :: StaticShX sh -> Maybe (ShX sh i)
shxFromSSX2 ZKX = Just ZSX
shxFromSSX2 (SKnown n :!% sh) = (SKnown n :$%) <$> shxFromSSX2 sh
shxFromSSX2 (SUnknown _ :!% _) = Nothing

shxAppend :: forall sh sh' i. ShX sh i -> ShX sh' i -> ShX (sh ++ sh') i
shxAppend = coerce (listhAppend @_ @i)

shxHead :: ShX (n : sh) i -> SMayNat i n
shxHead (ShX list) = listhHead list

shxTail :: ShX (n : sh) i -> ShX sh i
shxTail (ShX list) = ShX (listhTail list)

shxTakeSSX :: forall sh sh' i proxy. proxy sh' -> StaticShX sh -> ShX (sh ++ sh') i -> ShX sh i
shxTakeSSX _ ZKX _ = ZSX
shxTakeSSX p (_ :!% ssh1) (n :$% sh) = n :$% shxTakeSSX p ssh1 sh

shxTakeSh :: forall sh sh' i proxy. proxy sh' -> ShX sh i -> ShX (sh ++ sh') i -> ShX sh i
shxTakeSh _ ZSX _ = ZSX
shxTakeSh p (_ :$% ssh1) (n :$% sh) = n :$% shxTakeSh p ssh1 sh

shxDropSSX :: forall sh sh' i. StaticShX sh -> ShX (sh ++ sh') i -> ShX sh' i
shxDropSSX = coerce (listhDrop @i @())

shxDropIx :: forall sh sh' i j. IxX sh j -> ShX (sh ++ sh') i -> ShX sh' i
shxDropIx ZIX long = long
shxDropIx (_ :.% short) long = case long of _ :$% long' -> shxDropIx short long'

shxDropSh :: forall sh sh' i. ShX sh i -> ShX (sh ++ sh') i -> ShX sh' i
shxDropSh = coerce (listhDrop @i @i)

shxInit :: forall n sh i. ShX (n : sh) i -> ShX (Init (n : sh)) i
shxInit = coerce (listhInit @i)

shxLast :: forall n sh i. ShX (n : sh) i -> SMayNat i (Last (n : sh))
shxLast = coerce (listhLast @i)

{-# INLINE shxZipWith #-}
shxZipWith :: (forall n. SMayNat i n -> SMayNat j n -> SMayNat k n)
           -> ShX sh i -> ShX sh j -> ShX sh k
shxZipWith _ ZSX ZSX = ZSX
shxZipWith f (i :$% is) (j :$% js) = f i j :$% shxZipWith f is js

-- This is a weird operation, so it has a long name
shxCompleteZeros :: StaticShX sh -> IShX sh
shxCompleteZeros ZKX = ZSX
shxCompleteZeros (SUnknown () :!% ssh) = SUnknown 0 :$% shxCompleteZeros ssh
shxCompleteZeros (SKnown n :!% ssh) = SKnown n :$% shxCompleteZeros ssh

shxSplitApp :: proxy sh' -> StaticShX sh -> ShX (sh ++ sh') i -> (ShX sh i, ShX sh' i)
shxSplitApp _ ZKX idx = (ZSX, idx)
shxSplitApp p (_ :!% ssh) (i :$% idx) = first (i :$%) (shxSplitApp p ssh idx)

shxCast :: StaticShX sh' -> IShX sh -> Maybe (IShX sh')
shxCast ZKX ZSX = Just ZSX
shxCast (SKnown m    :!% ssh) (SKnown n   :$% sh) | Just Refl <- testEquality n m = (SKnown n :$%) <$> shxCast ssh sh
shxCast (SKnown m    :!% ssh) (SUnknown n :$% sh) | n == fromSNat' m              = (SKnown m :$%) <$> shxCast ssh sh
shxCast (SUnknown () :!% ssh) (SKnown n   :$% sh)                                 = (SUnknown (fromSNat' n) :$%) <$> shxCast ssh sh
shxCast (SUnknown () :!% ssh) (SUnknown n :$% sh)                                 = (SUnknown n :$%) <$> shxCast ssh sh
shxCast _ _ = Nothing

-- | Partial version of 'shxCast'.
shxCast' :: StaticShX sh' -> IShX sh -> IShX sh'
shxCast' ssh sh = case shxCast ssh sh of
  Just sh' -> sh'
  Nothing -> error $ "shxCast': Mismatch: (" ++ show sh ++ ") does not match (" ++ show ssh ++ ")"


-- * Static mixed shapes

-- | The part of a shape that is statically known. (A newtype over 'ListH'.)
type StaticShX :: [Maybe Nat] -> Type
newtype StaticShX sh = StaticShX (ListH sh ())
  deriving (NFData)

instance Eq (StaticShX sh) where _ == _ = True
instance Ord (StaticShX sh) where compare _ _ = EQ

pattern ZKX :: forall sh. () => sh ~ '[] => StaticShX sh
pattern ZKX = StaticShX ZH

pattern (:!%)
  :: forall {sh1}.
     forall n sh. (n : sh ~ sh1)
  => SMayNat () n -> StaticShX sh -> StaticShX sh1
pattern i :!% shl <- StaticShX (listhUncons -> Just (UnconsListHRes (StaticShX -> shl) i))
  where i :!% StaticShX shl = case i of; SUnknown () -> StaticShX (() `ConsUnknown` shl); SKnown x -> StaticShX (x `ConsKnown` shl)

infixr 3 :!%

{-# COMPLETE ZKX, (:!%) #-}

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show (StaticShX sh)
#else
instance Show (StaticShX sh) where
  showsPrec _ (StaticShX l) = listhShow (fromSMayNat shows (shows . fromSNat)) l
#endif

instance TestEquality StaticShX where
  testEquality (StaticShX l1) (StaticShX l2) = listhEqType l1 l2

ssxLength :: StaticShX sh -> Int
ssxLength (StaticShX l) = listhLength l

ssxRank :: StaticShX sh -> SNat (Rank sh)
ssxRank (StaticShX l) = listhRank l

-- | @ssxEqType = 'testEquality'@. Provided for consistency.
ssxEqType :: StaticShX sh -> StaticShX sh' -> Maybe (sh :~: sh')
ssxEqType = testEquality

ssxAppend :: StaticShX sh -> StaticShX sh' -> StaticShX (sh ++ sh')
ssxAppend = coerce (listhAppend @_ @())

ssxHead :: StaticShX (n : sh) -> SMayNat () n
ssxHead (StaticShX list) = listhHead list

ssxTail :: StaticShX (n : sh) -> StaticShX sh
ssxTail (StaticShX list) = StaticShX (listhTail list)

ssxTakeIx :: forall sh sh' i. Proxy sh' -> IxX sh i -> StaticShX (sh ++ sh') -> StaticShX sh
ssxTakeIx _ (IxX ZX) _ = ZKX
ssxTakeIx proxy (IxX (_ ::% long)) short = case short of i :!% short' -> i :!% ssxTakeIx proxy (IxX long) short'

ssxDropIx :: forall sh sh' i. IxX sh i -> StaticShX (sh ++ sh') -> StaticShX sh'
ssxDropIx (IxX ZX) long = long
ssxDropIx (IxX (_ ::% short)) long = case long of _ :!% long' -> ssxDropIx (IxX short) long'

ssxDropSh :: forall sh sh' i. ShX sh i -> StaticShX (sh ++ sh') -> StaticShX sh'
ssxDropSh = coerce (listhDrop @() @i)

ssxDropSSX :: forall sh sh'. StaticShX sh -> StaticShX (sh ++ sh') -> StaticShX sh'
ssxDropSSX = coerce (listhDrop @() @())

ssxInit :: forall n sh. StaticShX (n : sh) -> StaticShX (Init (n : sh))
ssxInit = coerce (listhInit @())

ssxLast :: forall n sh. StaticShX (n : sh) -> SMayNat () (Last (n : sh))
ssxLast = coerce (listhLast @())

ssxReplicate :: SNat n -> StaticShX (Replicate n Nothing)
ssxReplicate SZ = ZKX
ssxReplicate (SS (n :: SNat n'))
  | Refl <- lemReplicateSucc @(Nothing @Nat) n
  = SUnknown () :!% ssxReplicate n

ssxIotaFrom :: StaticShX sh -> Int -> [Int]
ssxIotaFrom ZKX _ = []
ssxIotaFrom (_ :!% ssh) i = i : ssxIotaFrom ssh (i + 1)

ssxFromShX :: ShX sh i -> StaticShX sh
ssxFromShX ZSX = ZKX
ssxFromShX (n :$% sh) = fromSMayNat (\_ -> SUnknown ()) SKnown n :!% ssxFromShX sh

ssxFromSNat :: SNat n -> StaticShX (Replicate n Nothing)
ssxFromSNat SZ = ZKX
ssxFromSNat (SS (n :: SNat nm1)) | Refl <- lemReplicateSucc @(Nothing @Nat) n = SUnknown () :!% ssxFromSNat n


-- | Evidence for the static part of a shape. This pops up only when you are
-- polymorphic in the element type of an array.
type KnownShX :: [Maybe Nat] -> Constraint
class KnownShX sh where knownShX :: StaticShX sh
instance KnownShX '[] where knownShX = ZKX
instance (KnownNat n, KnownShX sh) => KnownShX (Just n : sh) where knownShX = SKnown natSing :!% knownShX
instance KnownShX sh => KnownShX (Nothing : sh) where knownShX = SUnknown () :!% knownShX

withKnownShX :: forall sh r. StaticShX sh -> (KnownShX sh => r) -> r
withKnownShX = withDict @(KnownShX sh)


-- * Flattening

type Flatten sh = Flatten' 1 sh

type family Flatten' acc sh where
  Flatten' acc '[] = Just acc
  Flatten' acc (Nothing : sh) = Nothing
  Flatten' acc (Just n : sh) = Flatten' (acc * n) sh

-- This function is currently unused
ssxFlatten :: StaticShX sh -> SMayNat () (Flatten sh)
ssxFlatten = go (SNat @1)
  where
    go :: SNat acc -> StaticShX sh -> SMayNat () (Flatten' acc sh)
    go acc ZKX = SKnown acc
    go _ (SUnknown () :!% _) = SUnknown ()
    go acc (SKnown sn :!% sh) = go (snatMul acc sn) sh

shxFlatten :: IShX sh -> SMayNat Int (Flatten sh)
shxFlatten = go (SNat @1)
  where
    go :: SNat acc -> IShX sh -> SMayNat Int (Flatten' acc sh)
    go acc ZSX = SKnown acc
    go acc (SUnknown n :$% sh) = SUnknown (goUnknown (fromSNat' acc * n) sh)
    go acc (SKnown sn :$% sh) = go (snatMul acc sn) sh

    goUnknown :: Int -> IShX sh -> Int
    goUnknown acc ZSX = acc
    goUnknown acc (SUnknown n :$% sh) = goUnknown (acc * n) sh
    goUnknown acc (SKnown sn :$% sh) = goUnknown (acc * fromSNat' sn) sh


-- | Very untyped: only length is checked (at runtime).
instance KnownShX sh => IsList (ListX sh i) where
  type Item (ListX sh i) = i
  fromList = listxFromList (knownShX @sh)
  toList = listxToList

-- | Very untyped: only length is checked (at runtime), index bounds are __not checked__.
instance KnownShX sh => IsList (IxX sh i) where
  type Item (IxX sh i) = i
  fromList = IxX . IsList.fromList
  toList = Foldable.toList

-- | Untyped: length and known dimensions are checked (at runtime).
instance KnownShX sh => IsList (IShX sh) where
  type Item (IShX sh) = Int
  fromList = shxFromList (knownShX @sh)
  toList = shxToList
