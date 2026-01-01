{-# LANGUAGE ImportQualifiedPost #-}
module Data.Array.Strided.Orthotope (
  module Data.Array.Strided.Orthotope,
  module Data.Array.Strided.Arith,
) where

import Data.Array.Internal qualified as OI
import Data.Array.Internal.RankedG qualified as RG
import Data.Array.Internal.RankedS qualified as RS

import Data.Array.Strided qualified as AS
import Data.Array.Strided.Arith

-- for liftVEltwise1
import Data.Array.Strided.Arith.Internal (stridesDense)
import Data.Vector.Storable qualified as VS
import Foreign.Storable
import GHC.TypeLits


fromO :: RS.Array n a -> AS.Array n a
fromO (RS.A (RG.A sh (OI.T strides offset vec))) = AS.Array sh strides offset vec

toO :: AS.Array n a -> RS.Array n a
toO (AS.Array sh strides offset vec) = RS.A (RG.A sh (OI.T strides offset vec))

{-# INLINE liftO1 #-}
liftO1 :: (AS.Array n a -> AS.Array n' b)
       -> RS.Array n a -> RS.Array n' b
liftO1 f = toO . f . fromO

{-# INLINE liftO2 #-}
liftO2 :: (AS.Array n a -> AS.Array n1 b -> AS.Array n2 c)
       -> RS.Array n a -> RS.Array n1 b -> RS.Array n2 c
liftO2 f x y = toO (f (fromO x) (fromO y))

-- We don't inline this lifting function, because its code is not just
-- a wrapper, being relatively long and expensive.
{-# INLINEABLE liftVEltwise1 #-}
liftVEltwise1 :: (Storable a, Storable b)
              => SNat n
              -> (VS.Vector a -> VS.Vector b)
              -> RS.Array n a -> RS.Array n b
liftVEltwise1 SNat f arr@(RS.A (RG.A sh (OI.T strides offset vec)))
  | Just (blockOff, blockSz) <- stridesDense sh offset strides =
      let vec' = f (VS.slice blockOff blockSz vec)
      in RS.A (RG.A sh (OI.T strides (offset - blockOff) vec'))
  | otherwise = RS.fromVector sh (f (RS.toVector arr))
