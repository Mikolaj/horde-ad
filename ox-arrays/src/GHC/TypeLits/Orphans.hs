-- | Compatibility module adding some additional instances not yet defined in
-- base-4.18 with GHC 9.6.
{-# OPTIONS -Wno-orphans #-}
module GHC.TypeLits.Orphans where

import GHC.TypeLits


instance Eq (SNat n) where
  _ == _ = True

instance Ord (SNat n) where
  compare _ _ = EQ
