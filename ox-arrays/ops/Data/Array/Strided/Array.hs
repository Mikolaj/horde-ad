{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Strided.Array where

import Data.List.NonEmpty qualified as NE
import Data.Proxy
import Data.Vector.Storable qualified as VS
import Foreign.Storable
import GHC.TypeLits


data Array (n :: Nat) a = Array
  { arrShape :: ![Int]
  , arrStrides :: ![Int]
  , arrOffset :: !Int
  , arrValues :: !(VS.Vector a)
  }

-- | Takes a vector in normalised order (inner dimension, i.e. last in the
-- list, iterates fastest).
arrayFromVector :: forall a n. (Storable a, KnownNat n) => [Int] -> VS.Vector a -> Array n a
arrayFromVector sh vec
  | VS.length vec == shsize
  , length sh == fromIntegral (natVal (Proxy @n))
  = Array sh strides 0 vec
  | otherwise = error $ "arrayFromVector: Shape " ++ show sh ++ " does not match vector length " ++ show (VS.length vec)
  where
    shsize = product sh
    strides = NE.tail (NE.scanr (*) 1 sh)

arrayFromConstant :: Storable a => [Int] -> a -> Array n a
arrayFromConstant sh x = Array sh (0 <$ sh) 0 (VS.singleton x)

arrayRevDims :: [Bool] -> Array n a -> Array n a
arrayRevDims bs (Array sh strides offset vec)
  | length bs == length sh =
      Array sh
            (zipWith (\b s -> if b then -s else s) bs strides)
            (offset + sum (zipWith3 (\b n s -> if b then (n - 1) * s else 0) bs sh strides))
            vec
  | otherwise = error $ "arrayRevDims: " ++ show (length bs) ++ " booleans given but rank " ++ show (length sh)
