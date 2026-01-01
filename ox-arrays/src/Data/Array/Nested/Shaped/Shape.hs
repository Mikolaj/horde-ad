{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
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
module Data.Array.Nested.Shaped.Shape where

import Control.DeepSeq (NFData(..))
import Data.Array.Shape qualified as O
import Data.Coerce (coerce)
import Data.Foldable qualified as Foldable
import Data.Kind (Constraint, Type)
import Data.Type.Equality
import GHC.Exts (build, withDict)
import GHC.IsList (IsList)
import GHC.IsList qualified as IsList
import GHC.TypeLits
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation
import Data.Array.Nested.Types


-- * Shaped lists

type role ListS nominal representational
type ListS :: [Nat] -> Type -> Type
data ListS sh i where
  ZS :: ListS '[] i
  (::$) :: forall n sh {i}. i -> ListS sh i -> ListS (n : sh) i
deriving instance Eq i => Eq (ListS sh i)
deriving instance Ord i => Ord (ListS sh i)

infixr 3 ::$

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (ListS sh i)
#else
instance Show i => Show (ListS sh i) where
  showsPrec _ = listsShow shows
#endif

instance NFData i => NFData (ListS n i) where
  rnf ZS = ()
  rnf (x ::$ l) = rnf x `seq` rnf l

data UnconsListSRes i sh1 =
  forall n sh. (n : sh ~ sh1) => UnconsListSRes (ListS sh i) i
listsUncons :: ListS sh1 i -> Maybe (UnconsListSRes i sh1)
listsUncons (x ::$ sh') = Just (UnconsListSRes sh' x)
listsUncons ZS = Nothing

listsShow :: forall sh i. (i -> ShowS) -> ListS sh i -> ShowS
listsShow f l = showString "[" . go "" l . showString "]"
  where
    go :: String -> ListS sh' i -> ShowS
    go _ ZS = id
    go prefix (x ::$ xs) = showString prefix . f x . go "," xs

instance Functor (ListS l) where
  {-# INLINE fmap #-}
  fmap _ ZS = ZS
  fmap f (x ::$ xs) = f x ::$ fmap f xs

instance Foldable (ListS l) where
  {-# INLINE foldMap #-}
  foldMap _ ZS = mempty
  foldMap f (x ::$ xs) = f x <> foldMap f xs
  {-# INLINE foldr #-}
  foldr _ z ZS = z
  foldr f z (x ::$ xs) = f x (foldr f z xs)
  toList = listsToList
  null ZS = False
  null _ = True

listsLength :: ListS sh i -> Int
listsLength = length

listsRank :: ListS sh i -> SNat (Rank sh)
listsRank ZS = SNat
listsRank (_ ::$ sh) = snatSucc (listsRank sh)

listsFromList :: ShS sh -> [i] -> ListS sh i
listsFromList topsh topl = go topsh topl
  where
    go :: ShS sh' -> [i] -> ListS sh' i
    go ZSS [] = ZS
    go (_ :$$ sh) (i : is) = i ::$ go sh is
    go _ _ = error $ "listsFromList: Mismatched list length (type says "
                     ++ show (shsLength topsh) ++ ", list has length "
                     ++ show (length topl) ++ ")"

{-# INLINEABLE listsFromListS #-}
listsFromListS :: ListS sh i0 -> [i] -> ListS sh i
listsFromListS topl0 topl = go topl0 topl
  where
    go :: ListS sh i0 -> [i] -> ListS sh i
    go ZS [] = ZS
    go (_ ::$ l0) (i : is) = i ::$ go l0 is
    go _ _ = error $ "listsFromListS: Mismatched list length (the model says "
                       ++ show (listsLength topl0) ++ ", list has length "
                       ++ show (length topl) ++ ")"

{-# INLINEABLE listsToList #-}
listsToList :: ListS sh i -> [i]
listsToList list = build (\(cons :: i -> is -> is) (nil :: is) ->
  let go :: ListS sh i -> is
      go ZS = nil
      go (i ::$ is) = i `cons` go is
  in go list)

listsHead :: ListS (n : sh) i -> i
listsHead (i ::$ _) = i

listsTail :: ListS (n : sh) i -> ListS sh i
listsTail (_ ::$ sh) = sh

listsInit :: ListS (n : sh) i -> ListS (Init (n : sh)) i
listsInit (n ::$ sh@(_ ::$ _)) = n ::$ listsInit sh
listsInit (_ ::$ ZS) = ZS

listsLast :: ListS (n : sh) i -> i
listsLast (_ ::$ sh@(_ ::$ _)) = listsLast sh
listsLast (n ::$ ZS) = n

listsAppend :: ListS sh i -> ListS sh' i -> ListS (sh ++ sh') i
listsAppend ZS idx' = idx'
listsAppend (i ::$ idx) idx' = i ::$ listsAppend idx idx'

listsZip :: ListS sh i -> ListS sh j -> ListS sh (i, j)
listsZip ZS ZS = ZS
listsZip (i ::$ is) (j ::$ js) = (i, j) ::$ listsZip is js

{-# INLINE listsZipWith #-}
listsZipWith :: (i -> j -> k) -> ListS sh i -> ListS sh j -> ListS sh k
listsZipWith _ ZS ZS = ZS
listsZipWith f (i ::$ is) (j ::$ js) = f i j ::$ listsZipWith f is js

listsTakeLenPerm :: forall i is sh. Perm is -> ListS sh i -> ListS (TakeLen is sh) i
listsTakeLenPerm PNil _ = ZS
listsTakeLenPerm (_ `PCons` is) (n ::$ sh) = n ::$ listsTakeLenPerm is sh
listsTakeLenPerm (_ `PCons` _) ZS = error "Permutation longer than shape"

listsDropLenPerm :: forall i is sh. Perm is -> ListS sh i -> ListS (DropLen is sh) i
listsDropLenPerm PNil sh = sh
listsDropLenPerm (_ `PCons` is) (_ ::$ sh) = listsDropLenPerm is sh
listsDropLenPerm (_ `PCons` _) ZS = error "Permutation longer than shape"

listsPermute :: forall i is sh. Perm is -> ListS sh i -> ListS (Permute is sh) i
listsPermute PNil _ = ZS
listsPermute (i `PCons` (is :: Perm is')) (sh :: ListS sh f) =
  case listsIndex i sh of
    item -> item ::$ listsPermute is sh

-- TODO: try to remove this SNat now that the KnownNat constraint in ListS is removed
listsIndex :: forall j i sh. SNat i -> ListS sh j -> j
listsIndex SZ (n ::$ _) = n
listsIndex (SS i) (_ ::$ sh) = listsIndex i sh
listsIndex _ ZS = error "Index into empty shape"

listsPermutePrefix :: forall i is sh. Perm is -> ListS sh i -> ListS (PermutePrefix is sh) i
listsPermutePrefix perm sh = listsAppend (listsPermute perm (listsTakeLenPerm perm sh)) (listsDropLenPerm perm sh)

-- * Shaped indices

-- | An index into a shape-typed array.
type role IxS nominal representational
type IxS :: [Nat] -> Type -> Type
newtype IxS sh i = IxS (ListS sh i)
  deriving (Eq, Ord, NFData, Functor, Foldable)

pattern ZIS :: forall sh i. () => sh ~ '[] => IxS sh i
pattern ZIS = IxS ZS

-- | Note: The 'KnownNat' constraint on '(:.$)' is deprecated and should be
-- removed in a future release.
pattern (:.$)
  :: forall {sh1} {i}.
     forall n sh. (n : sh ~ sh1)
  => i -> IxS sh i -> IxS sh1 i
pattern i :.$ shl <- IxS (listsUncons -> Just (UnconsListSRes (IxS -> shl) i))
  where i :.$ IxS shl = IxS (i ::$ shl)
infixr 3 :.$

{-# COMPLETE ZIS, (:.$) #-}

-- For convenience, this contains regular 'Int's instead of bounded integers
-- (traditionally called \"@Fin@\").
type IIxS sh = IxS sh Int

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show i => Show (IxS sh i)
#else
instance Show i => Show (IxS sh i) where
  showsPrec _ (IxS l) = listsShow (\i -> shows i) l
#endif

ixsLength :: IxS sh i -> Int
ixsLength (IxS l) = listsLength l

ixsRank :: IxS sh i -> SNat (Rank sh)
ixsRank (IxS l) = listsRank l

ixsFromList :: forall sh i. ShS sh -> [i] -> IxS sh i
ixsFromList = coerce (listsFromList @_ @i)

{-# INLINEABLE ixsFromIxS #-}
ixsFromIxS :: forall sh i0 i. IxS sh i0 -> [i] -> IxS sh i
ixsFromIxS = coerce (listsFromListS @_ @i0 @i)

ixsToList :: IxS sh i -> [i]
ixsToList = Foldable.toList

ixsZero :: ShS sh -> IIxS sh
ixsZero ZSS = ZIS
ixsZero (_ :$$ sh) = 0 :.$ ixsZero sh

ixsHead :: IxS (n : sh) i -> i
ixsHead (IxS list) = listsHead list

ixsTail :: IxS (n : sh) i -> IxS sh i
ixsTail (IxS list) = IxS (listsTail list)

ixsInit :: IxS (n : sh) i -> IxS (Init (n : sh)) i
ixsInit (IxS list) = IxS (listsInit list)

ixsLast :: IxS (n : sh) i -> i
ixsLast (IxS list) = listsLast list

ixsCast :: IxS sh i -> IxS sh i
ixsCast ZIS = ZIS
ixsCast (i :.$ idx) = i :.$ ixsCast idx

ixsAppend :: forall sh sh' i. IxS sh i -> IxS sh' i -> IxS (sh ++ sh') i
ixsAppend = coerce (listsAppend @_ @i)

ixsZip :: IxS sh i -> IxS sh j -> IxS sh (i, j)
ixsZip ZIS ZIS = ZIS
ixsZip (i :.$ is) (j :.$ js) = (i, j) :.$ ixsZip is js

{-# INLINE ixsZipWith #-}
ixsZipWith :: (i -> j -> k) -> IxS sh i -> IxS sh j -> IxS sh k
ixsZipWith _ ZIS ZIS = ZIS
ixsZipWith f (i :.$ is) (j :.$ js) = f i j :.$ ixsZipWith f is js

ixsPermutePrefix :: forall i is sh. Perm is -> IxS sh i -> IxS (PermutePrefix is sh) i
ixsPermutePrefix = coerce (listsPermutePrefix @i)

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer.
{-# INLINEABLE ixsToLinear #-}
ixsToLinear :: Num i => ShS sh -> IxS sh i -> i
ixsToLinear (ShS sh) ix = ixxToLinear sh (ixxFromIxS ix)

ixxFromIxS :: IxS sh i -> IxX (MapJust sh) i
ixxFromIxS = unsafeCoerce  -- TODO: switch to coerce once newtypes overhauled

{-# INLINEABLE ixsFromLinear #-}
ixsFromLinear :: Num i => ShS sh -> Int -> IxS sh i
ixsFromLinear (ShS sh) i = ixsFromIxX $ ixxFromLinear sh i

ixsFromIxX :: IxX (MapJust sh) i -> IxS sh i
ixsFromIxX = unsafeCoerce  -- TODO: switch to coerce once newtypes overhauled

shsEnum :: ShS sh -> [IIxS sh]
shsEnum = shsEnum'

{-# INLINABLE shsEnum' #-}  -- ensure this can be specialised at use site
shsEnum' :: Num i => ShS sh -> [IxS sh i]
shsEnum' (ShS sh) = (unsafeCoerce :: [IxX (MapJust sh) i] -> [IxS sh i]) $ shxEnum' sh
                      -- TODO: switch to coerce once newtypes overhauled

-- * Shaped shapes

-- | The shape of a shape-typed array given as a list of 'SNat' values.
--
-- Note that because the shape of a shape-typed array is known statically, you
-- can also retrieve the array shape from a 'KnownShS' dictionary.
type role ShS nominal
type ShS :: [Nat] -> Type
newtype ShS sh = ShS (ShX (MapJust sh) Int)
  deriving (NFData)

instance Eq (ShS sh) where _ == _ = True
instance Ord (ShS sh) where compare _ _ = EQ

pattern ZSS :: forall sh. () => sh ~ '[] => ShS sh
pattern ZSS <- ShS (matchZSX -> Just Refl)
  where ZSS = ShS ZSX

matchZSX :: forall sh i. ShX (MapJust sh) i -> Maybe (sh :~: '[])
matchZSX ZSX | Refl <- lemMapJustEmpty @sh Refl = Just Refl
matchZSX _ = Nothing

pattern (:$$)
  :: forall {sh1}.
     forall n sh. (n : sh ~ sh1)
  => SNat n -> ShS sh -> ShS sh1
pattern i :$$ shl <- (shsUncons -> Just (UnconsShSRes i shl))
  where i :$$ ShS shl = ShS (SKnown i :$% shl)

data UnconsShSRes sh1 =
  forall n sh. (n : sh ~ sh1) => UnconsShSRes (SNat n) (ShS sh)
shsUncons :: forall sh1. ShS sh1 -> Maybe (UnconsShSRes sh1)
shsUncons (ShS (SKnown x :$% sh'))
  | Refl <- lemMapJustCons @sh1 Refl
  = Just (UnconsShSRes x (ShS sh'))
shsUncons (ShS _) = Nothing

infixr 3 :$$

{-# COMPLETE ZSS, (:$$) #-}

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show (ShS sh)
#else
instance Show (ShS sh) where
  showsPrec d (ShS shx) = showsPrec d shx
#endif

instance TestEquality ShS where
  testEquality (ShS shx1) (ShS shx2) = case shxEqType shx1 shx2 of
    Nothing -> Nothing
    Just Refl -> Just unsafeCoerceRefl

-- | @'shsEqual' = 'testEquality'@. (Because 'ShS' is a singleton, types are
-- equal if and only if values are equal.)
shsEqual :: ShS sh -> ShS sh' -> Maybe (sh :~: sh')
shsEqual = testEquality

shsLength :: ShS sh -> Int
shsLength (ShS shx) = shxLength shx

shsRank :: forall sh. ShS sh -> SNat (Rank sh)
shsRank (ShS shx) =
  gcastWith (unsafeCoerceRefl
             :: Rank (MapJust sh) :~: Rank sh) $
  shxRank shx

shsSize :: ShS sh -> Int
shsSize (ShS sh) = shxSize sh

-- | This is a partial @const@ that fails when the second argument
-- doesn't match the first. We don't report the size of the list
-- in case of errors in order not to retain the list.
{-# INLINEABLE shsFromList #-}
shsFromList :: ShS sh -> [Int] -> ShS sh
shsFromList sh0@(ShS (ShX topsh)) topl = go topsh topl `seq` sh0
  where
    go :: ListH sh' Int -> [Int] -> ()
    go ZH [] = ()
    go ZH _ = error $ "shsFromList: List too long (type says " ++ show (listhLength topsh) ++ ")"
    go (ConsKnown sn sh) (i : is)
      | i == fromSNat' sn = go sh is
      | otherwise = error $ "shsFromList: Value does not match typing"
    go ConsUnknown{} _ = error "shsFromList: impossible case"
    go _ _ = error $ "shsFromList: List too short (type says " ++ show (listhLength topsh) ++ ")"

-- This is equivalent to but faster than @coerce shxToList@.
{-# INLINEABLE shsToList #-}
shsToList :: ShS sh -> [Int]
shsToList (ShS (ShX l)) = build (\(cons :: i -> is -> is) (nil :: is) ->
  let go :: ListH sh Int -> is
      go ZH = nil
      go ConsUnknown{} = error "shsToList: impossible case"
      go (ConsKnown snat rest) = fromSNat' snat `cons` go rest
  in go l)

shsHead :: ShS (n : sh) -> SNat n
shsHead (ShS shx) = case shxHead shx of
  SKnown SNat -> SNat

shsTail :: forall n sh. ShS (n : sh) -> ShS sh
shsTail = coerce (shxTail @_ @_ @Int)

shsInit :: forall n sh. ShS (n : sh) -> ShS (Init (n : sh))
shsInit =
  gcastWith (unsafeCoerceRefl
             :: Init (Just n : MapJust sh) :~: MapJust (Init (n : sh))) $
  coerce (shxInit @_ @_ @Int)

shsLast :: forall n sh. ShS (n : sh) -> SNat (Last (n : sh))
shsLast (ShS shx) =
  gcastWith (unsafeCoerceRefl
             :: Last (Just n : MapJust sh) :~: Just (Last (n : sh))) $
  case shxLast shx of
    SKnown SNat -> SNat

shsAppend :: forall sh sh'. ShS sh -> ShS sh' -> ShS (sh ++ sh')
shsAppend =
  gcastWith (unsafeCoerceRefl
             :: MapJust sh ++ MapJust sh' :~: MapJust (sh ++ sh')) $
  coerce (shxAppend @_ @_ @Int)

shsTakeLen :: forall is sh. Perm is -> ShS sh -> ShS (TakeLen is sh)
shsTakeLen =
  gcastWith (unsafeCoerceRefl
             :: TakeLen is (MapJust sh) :~: MapJust (TakeLen is sh)) $
  coerce shxTakeLen

shsDropLen :: forall is sh. Perm is -> ShS sh -> ShS (DropLen is sh)
shsDropLen =
  gcastWith (unsafeCoerceRefl
             :: DropLen is (MapJust sh) :~: MapJust (DropLen is sh)) $
  coerce shxDropLen

shsPermute :: forall is sh. Perm is -> ShS sh -> ShS (Permute is sh)
shsPermute =
  gcastWith (unsafeCoerceRefl
             :: Permute is (MapJust sh) :~: MapJust (Permute is sh)) $
  coerce shxPermute

shsIndex :: forall i sh. SNat i -> ShS sh -> SNat (Index i sh)
shsIndex i (ShS sh) =
  gcastWith (unsafeCoerceRefl
             :: Index i (MapJust sh) :~: Just (Index i sh)) $
  case shxIndex @_ @_ @Int i sh of
    SKnown SNat -> SNat

shsPermutePrefix :: forall is sh. Perm is -> ShS sh -> ShS (PermutePrefix is sh)
shsPermutePrefix perm (ShS shx)
  {- TODO: here and elsewhere, solve the module dependency cycle and add this:
  | Refl <- lemTakeLenMapJust perm sh
  , Refl <- lemDropLenMapJust perm sh
  , Refl <- lemPermuteMapJust perm sh
  , Refl <- lemMapJustApp (shsPermute perm (shsTakeLen perm sh)) (shsDropLen perm sh) -}
  = gcastWith (unsafeCoerceRefl
               :: Permute is (TakeLen is (MapJust sh))
                  ++ DropLen is (MapJust sh)
                  :~: MapJust (Permute is (TakeLen is sh) ++ DropLen is sh)) $
    ShS (shxPermutePrefix perm shx)

type family Product sh where
  Product '[] = 1
  Product (n : ns) = n * Product ns

shsProduct :: ShS sh -> SNat (Product sh)
shsProduct ZSS = SNat
shsProduct (n :$$ sh) = n `snatMul` shsProduct sh

-- | Evidence for the static part of a shape. This pops up only when you are
-- polymorphic in the element type of an array.
type KnownShS :: [Nat] -> Constraint
class KnownShS sh where knownShS :: ShS sh
instance KnownShS '[] where knownShS = ZSS
instance (KnownNat n, KnownShS sh) => KnownShS (n : sh) where knownShS = natSing :$$ knownShS

withKnownShS :: forall sh r. ShS sh -> (KnownShS sh => r) -> r
withKnownShS = withDict @(KnownShS sh)

shsKnownShS :: ShS sh -> Dict KnownShS sh
shsKnownShS ZSS = Dict
shsKnownShS (SNat :$$ sh) | Dict <- shsKnownShS sh = Dict

shsOrthotopeShape :: ShS sh -> Dict O.Shape sh
shsOrthotopeShape ZSS = Dict
shsOrthotopeShape (SNat :$$ sh) | Dict <- shsOrthotopeShape sh = Dict


-- | Untyped: length is checked at runtime.
instance KnownShS sh => IsList (ListS sh i) where
  type Item (ListS sh i) = i
  fromList = listsFromList (knownShS @sh)
  toList = listsToList

-- | Very untyped: only length is checked (at runtime), index bounds are __not checked__.
instance KnownShS sh => IsList (IxS sh i) where
  type Item (IxS sh i) = i
  fromList = IxS . IsList.fromList
  toList = Foldable.toList

-- | Untyped: length and values are checked at runtime.
instance KnownShS sh => IsList (ShS sh) where
  type Item (ShS sh) = Int
  fromList = shsFromList (knownShS @sh)
  toList = shsToList
