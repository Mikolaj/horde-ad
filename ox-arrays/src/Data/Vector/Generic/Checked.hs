{-# LANGUAGE CPP #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Data.Vector.Generic.Checked (
  fromListNChecked,
) where

import Data.Stream.Monadic qualified as Stream
import Data.Vector.Fusion.Bundle.Monadic qualified as VBM
import Data.Vector.Fusion.Bundle.Size qualified as VBS
import Data.Vector.Fusion.Util qualified as VFU
import Data.Vector.Generic qualified as VG

-- for INLINE_FUSED and INLINE_INNER
#include "vector.h"


-- These functions are copied over and lightly edited from the vector and
-- vector-stream packages, and thus inherit their BSD-3-Clause license with:
-- Copyright (c) 2008-2012, Roman Leshchinskiy
--               2020-2022, Alexey Kuleshevich
--               2020-2022, Aleksey Khudyakov
--               2020-2022, Andrew Lelechenko

fromListNChecked :: VG.Vector v a => Int -> [a] -> v a
{-# INLINE fromListNChecked #-}
fromListNChecked n = VG.unstream . bundleFromListNChecked n

bundleFromListNChecked :: Int -> [a] -> VBM.Bundle VFU.Id v a
{-# INLINE_FUSED bundleFromListNChecked #-}
bundleFromListNChecked nTop xsTop
  | nTop < 0 = error "fromListNChecked: length negative"
  | otherwise =
      VBM.fromStream (Stream.Stream step (xsTop, nTop)) (VBS.Max (VFU.delay_inline max nTop 0))
  where
    {-# INLINE_INNER step #-}
    step (xs,n) | n == 0 = case xs of
                             [] -> return Stream.Done
                             _:_ -> error "fromListNChecked: list too long"
    step (x:xs,n)        = return (Stream.Yield x (xs,n-1))
    step ([],_)          = error "fromListNChecked: list too short"
