{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
{-# LANGUAGE TypeAbstractions #-}
#endif
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Data.Array.Nested.Convert (
  -- * Shape\/index\/list casting functions
  -- ** To ranked
  ixrFromIxS, ixrFromIxX, shrFromShS, shrFromShXAnyShape, shrFromShX,
  listrCast, ixrCast, shrCast,
  -- ** To shaped
  ixsFromIxR, ixsFromIxX, ixsFromIxX', withShsFromShR, shsFromShX, withShsFromShX, shsFromSSX,
  ixsCast,
  -- ** To mixed
  ixxFromIxR, ixxFromIxS, shxFromShR, shxFromShS,
  ixxCast, shxCast, shxCast',

  -- * Array conversions
  convert,
  Conversion(..),

  -- * Special cases of array conversions
  --
  -- | These functions can all be implemented using 'convert' in some way,
  -- but some have fewer constraints.
  rtoMixed, rcastToMixed, rcastToShaped,
  stoMixed, scastToMixed, stoRanked,
  mcast, mcastToShaped, mtoRanked,
) where

import Control.Category
import Data.Coerce (coerce)
import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Base
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Base
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types

-- * Shape or index or list casting functions

-- * To ranked

-- TODO: change all those unsafeCoerces into coerces by defining shaped
-- and ranekd index types as newtypes of the mixed index type
-- and similarly for the sized lists or, preferably, by defining
-- all as newtypes over [], exploiting fusion and getting free toList.
ixrFromIxS :: IxS sh i -> IxR (Rank sh) i
ixrFromIxS = unsafeCoerce

-- ixrFromIxX re-exported

shrFromShS :: ShS sh -> IShR (Rank sh)
shrFromShS ZSS = ZSR
shrFromShS (n :$$ sh) = fromSNat' n :$: shrFromShS sh

shrFromShXAnyShape :: IShX sh -> IShR (Rank sh)
shrFromShXAnyShape ZSX = ZSR
shrFromShXAnyShape (n :$% idx) = fromSMayNat' n :$: shrFromShXAnyShape idx

shrFromShX :: IShX (Replicate n Nothing) -> IShR n
shrFromShX = coerce

-- listrCast re-exported
-- ixrCast re-exported
-- shrCast re-exported

-- * To shaped

ixsFromIxR :: IxR (Rank sh) i -> IxS sh i
ixsFromIxR = unsafeCoerce  -- TODO: switch to coerce once newtypes overhauled

-- ixsFromIxX re-exported

-- | Performs a runtime check that @Rank sh'@ match @Rank sh@. Equivalent to
-- the following, but less verbose:
--
-- > ixsFromIxX' sh idx = ixsFromIxX sh (ixxCast (shxFromShS sh) idx)
ixsFromIxX' :: ShS sh -> IxX sh' i -> IxS sh i
ixsFromIxX' ZSS ZIX = ZIS
ixsFromIxX' (_ :$$ sh) (n :.% idx) = n :.$ ixsFromIxX' sh idx
ixsFromIxX' _ _ = error "ixsFromIxX': index rank does not match shape rank"

-- | Produce an existential 'ShS' from an 'IShR'.
withShsFromShR :: IShR n -> (forall sh. Rank sh ~ n => ShS sh -> r) -> r
withShsFromShR ZSR k = k ZSS
withShsFromShR (n :$: sh) k =
  withShsFromShR sh $ \sh' ->
    withSomeSNat (fromIntegral @Int @Integer n) $ \case
      Just sn@SNat -> k (sn :$$ sh')
      Nothing -> error $ "withShsFromShR: negative dimension size (" ++ show n ++ ")"

shsFromShX :: IShX (MapJust sh) -> ShS sh
shsFromShX = coerce

-- | Produce an existential 'ShS' from an 'IShX'. If you already know that
-- @sh'@ is @MapJust@ of something, use 'shsFromShX' instead.
withShsFromShX :: IShX sh' -> (forall sh. Rank sh ~ Rank sh' => ShS sh -> r) -> r
withShsFromShX ZSX k = k ZSS
withShsFromShX (SKnown sn@SNat :$% sh) k =
  withShsFromShX sh $ \sh' ->
    k (sn :$$ sh')
withShsFromShX (SUnknown n :$% sh) k =
  withShsFromShX sh $ \sh' ->
    withSomeSNat (fromIntegral @Int @Integer n) $ \case
      Just sn@SNat -> k (sn :$$ sh')
      Nothing -> error $ "withShsFromShX: negative SUnknown dimension size (" ++ show n ++ ")"

-- If it ever matters for performance, this is unsafeCoercible.
shsFromSSX :: StaticShX (MapJust sh) -> ShS sh
shsFromSSX = shsFromShX Prelude.. shxFromSSX

-- ixsCast re-exported

-- * To mixed

-- ixxFromIxR re-exported
-- ixxFromIxS re-exported

shxFromShR :: ShR n i -> ShX (Replicate n Nothing) i
shxFromShR = coerce

shxFromShS :: ShS sh -> IShX (MapJust sh)
shxFromShS = coerce

-- ixxCast re-exported
-- shxCast re-exported
-- shxCast' re-exported


-- * Array conversions

-- | The constructors that perform runtime shape checking are marked with a
-- tick (@'@): 'ConvXS'' and 'ConvXX''. For the other constructors, the types
-- ensure that the shapes are already compatible. To convert between 'Ranked'
-- and 'Shaped', go via 'Mixed'.
--
-- The guiding principle behind 'Conversion' is that it should represent the
-- array restructurings, or perhaps re-presentations, that do not change the
-- underlying 'XArray's. This leads to the inclusion of some operations that do
-- not look like simple conversions (casts) at first glance, like 'ConvZip'.
--
-- /Note/: Haddock gleefully renames type variables in constructors so that
-- they match the data type head as much as possible. See the source for a more
-- readable presentation of this data type.
data Conversion a b where
  ConvId  :: Conversion a a
  ConvCmp :: Conversion b c -> Conversion a b -> Conversion a c

  ConvRX  :: Conversion (Ranked n a) (Mixed (Replicate n Nothing) a)
  ConvSX  :: Conversion (Shaped sh a) (Mixed (MapJust sh) a)

  ConvXR  :: Elt a
          => Conversion (Mixed sh a) (Ranked (Rank sh) a)
  ConvXS  :: Conversion (Mixed (MapJust sh) a) (Shaped sh a)
  ConvXS' :: (Rank sh ~ Rank sh', Elt a)
          => ShS sh'
          -> Conversion (Mixed sh a) (Shaped sh' a)

  ConvXX' :: (Rank sh ~ Rank sh', Elt a)
          => StaticShX sh'
          -> Conversion (Mixed sh a) (Mixed sh' a)

  ConvRR  :: Conversion a b
          -> Conversion (Ranked n a) (Ranked n b)
  ConvSS  :: Conversion a b
          -> Conversion (Shaped sh a) (Shaped sh b)
  ConvXX  :: Conversion a b
          -> Conversion (Mixed sh a) (Mixed sh b)
  ConvT2  :: Conversion a a'
          -> Conversion b b'
          -> Conversion (a, b) (a', b')

  Conv0X  :: Elt a
          => Conversion a (Mixed '[] a)
  ConvX0  :: Conversion (Mixed '[] a) a

  ConvNest   :: Elt a => StaticShX sh
             -> Conversion (Mixed (sh ++ sh') a) (Mixed sh (Mixed sh' a))
  ConvUnnest :: Conversion (Mixed sh (Mixed sh' a)) (Mixed (sh ++ sh') a)

  ConvZip   :: (Elt a, Elt b)
            => Conversion (Mixed sh a, Mixed sh b) (Mixed sh (a, b))
  ConvUnzip :: (Elt a, Elt b)
            => Conversion (Mixed sh (a, b)) (Mixed sh a, Mixed sh b)
deriving instance Show (Conversion a b)

instance Category Conversion where
  id = ConvId
  (.) = ConvCmp

convert :: (Elt a, Elt b) => Conversion a b -> a -> b
convert = \c x -> munScalar (go c (mscalar x))
  where
    -- The 'esh' is the extension shape: the conversion happens under a whole
    -- bunch of additional dimensions that it does not touch. These dimensions
    -- are 'esh'.
    -- The strategy is to unwind step-by-step to a large Mixed array, and to
    -- perform the required checks and conversions when re-nesting back up.
    go :: Conversion a b -> Mixed esh a -> Mixed esh b
    go ConvId x = x
    go (ConvCmp c1 c2) x = go c1 (go c2 x)
    go ConvRX (M_Ranked x) = x
    go ConvSX (M_Shaped x) = x
    go (ConvXR @_ @sh) (M_Nest @esh esh x)
      | Refl <- lemRankAppRankEqRepNo (Proxy @esh) (Proxy @sh)
      = let ssx' = ssxAppend (ssxFromShX esh)
                             (ssxReplicate (shxRank (shxDropSSX @esh @sh (ssxFromShX esh) (mshape x))))
        in M_Ranked (M_Nest esh (mcast ssx' x))
    go ConvXS (M_Nest esh x) = M_Shaped (M_Nest esh x)
    go (ConvXS' @sh @sh' sh') (M_Nest @esh esh x)
      | Refl <- lemRankAppRankEqMapJust (Proxy @esh) (Proxy @sh) (Proxy @sh')
      = M_Shaped (M_Nest esh (mcast (ssxFromShX (shxAppend esh (shxFromShS sh')))
                                    x))
    go (ConvXX' @sh @sh' ssx) (M_Nest @esh esh x)
      | Refl <- lemRankAppRankEq (Proxy @esh) (Proxy @sh) (Proxy @sh')
      = M_Nest esh $ mcast (ssxFromShX esh `ssxAppend` ssx) x
    go (ConvRR c) (M_Ranked (M_Nest esh x)) = M_Ranked (M_Nest esh (go c x))
    go (ConvSS c) (M_Shaped (M_Nest esh x)) = M_Shaped (M_Nest esh (go c x))
    go (ConvXX c) (M_Nest esh x) = M_Nest esh (go c x)
    go (ConvT2 c1 c2) (M_Tup2 x1 x2) = M_Tup2 (go c1 x1) (go c2 x2)
    go Conv0X (x :: Mixed esh a)
      | Refl <- lemAppNil @esh
      = M_Nest (mshape x) x
    go ConvX0 (M_Nest @esh _ x)
      | Refl <- lemAppNil @esh
      = x
    go (ConvNest @_ @sh @sh' ssh) (M_Nest @esh esh x)
      | Refl <- lemAppAssoc (Proxy @esh) (Proxy @sh) (Proxy @sh')
      = M_Nest esh (M_Nest (shxTakeSSX (Proxy @sh') (ssxFromShX esh `ssxAppend` ssh) (mshape x)) x)
    go (ConvUnnest @sh @sh') (M_Nest @esh esh (M_Nest _ x))
      | Refl <- lemAppAssoc (Proxy @esh) (Proxy @sh) (Proxy @sh')
      = M_Nest esh x
    go ConvZip x =
      -- no need to check that the two esh's are equal because they were zipped previously
      let (M_Nest esh x1, M_Nest _ x2) = munzip x
      in M_Nest esh (mzip x1 x2)
    go ConvUnzip (M_Nest esh x) =
      let (x1, x2) = munzip x
      in mzip (M_Nest esh x1) (M_Nest esh x2)

    lemRankAppRankEq :: Rank sh ~ Rank sh'
                     => Proxy esh -> Proxy sh -> Proxy sh'
                     -> Rank (esh ++ sh) :~: Rank (esh ++ sh')
    lemRankAppRankEq _ _ _ = unsafeCoerceRefl

    lemRankAppRankEqRepNo :: Proxy esh -> Proxy sh
                          -> Rank (esh ++ sh) :~: Rank (esh ++ Replicate (Rank sh) Nothing)
    lemRankAppRankEqRepNo _ _ = unsafeCoerceRefl

    lemRankAppRankEqMapJust :: Rank sh ~ Rank sh'
                            => Proxy esh -> Proxy sh -> Proxy sh'
                            -> Rank (esh ++ sh) :~: Rank (esh ++ MapJust sh')
    lemRankAppRankEqMapJust _ _ _ = unsafeCoerceRefl


-- * Special cases of array conversions

mcast :: forall sh1 sh2 a. (Rank sh1 ~ Rank sh2, Elt a)
      => StaticShX sh2 -> Mixed sh1 a -> Mixed sh2 a
mcast ssh2 arr
  | Refl <- lemAppNil @sh1
  , Refl <- lemAppNil @sh2
  = mcastPartial (ssxFromShX (mshape arr)) ssh2 (Proxy @'[]) arr

mtoRanked :: forall sh a. Elt a => Mixed sh a -> Ranked (Rank sh) a
mtoRanked = convert ConvXR

rtoMixed :: forall n a. Ranked n a -> Mixed (Replicate n Nothing) a
rtoMixed (Ranked arr) = arr

-- | A more weakly-typed version of 'rtoMixed' that does a runtime shape
-- compatibility check.
rcastToMixed :: (Rank sh ~ n, Elt a) => StaticShX sh -> Ranked n a -> Mixed sh a
rcastToMixed sshx rarr@(Ranked arr)
  | Refl <- lemRankReplicate (rrank rarr)
  = mcast sshx arr

mcastToShaped :: forall sh sh' a. (Elt a, Rank sh ~ Rank sh')
              => ShS sh' -> Mixed sh a -> Shaped sh' a
mcastToShaped targetsh = convert (ConvXS' targetsh)

stoMixed :: forall sh a. Shaped sh a -> Mixed (MapJust sh) a
stoMixed (Shaped arr) = arr

-- | A more weakly-typed version of 'stoMixed' that does a runtime shape
-- compatibility check.
scastToMixed :: forall sh sh' a. (Elt a, Rank sh ~ Rank sh')
             => StaticShX sh' -> Shaped sh a -> Mixed sh' a
scastToMixed sshx sarr@(Shaped arr)
  | Refl <- lemRankMapJust (sshape sarr)
  = mcast sshx arr

stoRanked :: Elt a => Shaped sh a -> Ranked (Rank sh) a
stoRanked sarr@(Shaped arr)
  | Refl <- lemRankMapJust (sshape sarr)
  = mtoRanked arr

rcastToShaped :: Elt a => Ranked (Rank sh) a -> ShS sh -> Shaped sh a
rcastToShaped (Ranked arr) targetsh
  | Refl <- lemRankReplicate (shxRank (shxFromShS targetsh))
  , Refl <- lemRankMapJust targetsh
  = mcastToShaped targetsh arr
