{-# LANGUAGE UndecidableInstances #-}
-- | FFI bindings to the C code for tensor (in vector representation)
-- operations.
module HordeAd.Internal.TensorFFI
  ( module HordeAd.Internal.TensorFFI
  ) where

import Prelude

import qualified Data.Array.Internal as OI
import qualified Data.Array.Internal.RankedG as RG
import qualified Data.Array.Internal.RankedS as RS
import qualified Data.Array.RankedS as OR
import           Data.Functor (void)
import           Data.Int (Int64)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable.Mutable as VM
import           Foreign (Ptr)
import           Foreign.C (CInt (..))
import           GHC.TypeLits (KnownNat, sameNat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import qualified Numeric.LinearAlgebra as LA
import           System.IO.Unsafe (unsafePerformIO)

tsum0R
  :: Numeric r
  => OR.Array n r -> r
tsum0R (RS.A (RG.A sh (OI.T _ _ vt))) | V.length vt == 1 =
  fromIntegral (product sh) * vt V.! 0
-- tsumInR t@(RS.A (RG.A _ (OI.T _ _ vt))) | V.length vt == 1 =
tsum0R (RS.A (RG.A sh t)) =
  LA.sumElements $ OI.toUnorderedVectorT sh t

-- Sum the outermost dimension.
--
-- No NOINLINE, because apparently nothing breaks and hmatrix, etc.
-- also don't put NOINLINE in the functions using FFI.
tsumR
  :: forall n r. (KnownNat n, Numeric r, RowSum r)
  => OR.Array (1 + n) r -> OR.Array n r
tsumR (RS.A (RG.A (k : sh) (OI.T (_ : ss) o vt))) | V.length vt == 1 =
  RS.A (RG.A sh (OI.T ss o (V.map (* fromIntegral k) vt)))
tsumR t = case OR.shapeL t of
  [] -> error "tsumR: null shape"
  0 : sh2 -> OR.constant sh2 0  -- the shape is known from sh, so no ambiguity
  k : sh2 -> case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.scalar $ tsum0R t
    _ -> OR.fromVector sh2 $ unsafePerformIO $ do  -- unsafe only due to FFI
      v <- V.unsafeThaw $ OR.toVector t
      VM.unsafeWith v $ \ptr -> do
        let len2 = product sh2
        v2 <- VM.new len2
        VM.unsafeWith v2 $ \ptr2 -> do
          rowSum len2 k ptr ptr2
          void $ V.unsafeFreeze v
          V.unsafeFreeze v2

-- Sum the innermost dimension (at least at rank 2; TODO: generalize).
tsumInR
  :: forall n r. (KnownNat n, Numeric r, RowSum r)
  => OR.Array (1 + n) r -> OR.Array n r
tsumInR t = case OR.shapeL t of
  [] -> error "tsumInR: null shape"
  k2 : 0 : [] ->
    OR.constant [k2] 0  -- the shape is known from sh, so no ambiguity
  k2 : k : [] -> case t of
    RS.A (RG.A _ (OI.T (s2 : _) o vt)) | V.length vt == 1 ->
      RS.A (RG.A [k2] (OI.T [s2] o (V.map (* fromIntegral k) vt)))
    _ -> let sh2 = [k2]
         in OR.fromVector sh2 $ unsafePerformIO $ do  -- unsafe only due to FFI
           v <- V.unsafeThaw $ OR.toVector t
           VM.unsafeWith v $ \ptr -> do
             let len2 = product sh2
             v2 <- VM.new len2
             VM.unsafeWith v2 $ \ptr2 -> do
               columnSum k len2 ptr ptr2
               void $ V.unsafeFreeze v
               V.unsafeFreeze v2
  _ -> error "tsumInR: not yet generalized beyond rank 2"

foreign import ccall unsafe "row_sum_double"
  c_row_sum_double :: CInt -> CInt -> Ptr Double -> Ptr Double -> IO ()

foreign import ccall unsafe "column_sum_double"
  c_column_sum_double :: CInt -> CInt -> Ptr Double -> Ptr Double -> IO ()

foreign import ccall unsafe "row_sum_float"
  c_row_sum_float :: CInt -> CInt -> Ptr Float -> Ptr Float -> IO ()

foreign import ccall unsafe "column_sum_float"
  c_column_sum_float :: CInt -> CInt -> Ptr Float -> Ptr Float -> IO ()

foreign import ccall unsafe "row_sum_float"
  c_row_sum_int64 :: CInt -> CInt -> Ptr Int64 -> Ptr Int64 -> IO ()

foreign import ccall unsafe "column_sum_float"
  c_column_sum_int64 :: CInt -> CInt -> Ptr Int64 -> Ptr Int64 -> IO ()

foreign import ccall unsafe "row_sum_float"
  c_row_sum_cInt :: CInt -> CInt -> Ptr CInt -> Ptr CInt -> IO ()

foreign import ccall unsafe "column_sum_float"
  c_column_sum_cInt :: CInt -> CInt -> Ptr CInt -> Ptr CInt -> IO ()

class RowSum r where
  rowSum :: Int -> Int -> Ptr r -> Ptr r -> IO ()
  columnSum :: Int -> Int -> Ptr r -> Ptr r -> IO ()

instance RowSum Double where
  rowSum n k ptr ptr2 =
    c_row_sum_double (fromIntegral n) (fromIntegral k) ptr ptr2
  columnSum n k ptr ptr2 =
    c_column_sum_double (fromIntegral n) (fromIntegral k) ptr ptr2

instance RowSum Float where
  rowSum n k ptr ptr2 =
    c_row_sum_float (fromIntegral n) (fromIntegral k) ptr ptr2
  columnSum n k ptr ptr2 =
    c_column_sum_float (fromIntegral n) (fromIntegral k) ptr ptr2

instance RowSum Int64 where
  rowSum n k ptr ptr2 =
    c_row_sum_int64 (fromIntegral n) (fromIntegral k) ptr ptr2
  columnSum n k ptr ptr2 =
    c_column_sum_int64 (fromIntegral n) (fromIntegral k) ptr ptr2

instance RowSum CInt where
  rowSum n k ptr ptr2 =
    c_row_sum_cInt (fromIntegral n) (fromIntegral k) ptr ptr2
  columnSum n k ptr ptr2 =
    c_column_sum_cInt (fromIntegral n) (fromIntegral k) ptr ptr2

instance {-# OVERLAPPABLE #-} Numeric r => RowSum r where
  rowSum = error "RowSum: TODO"
  columnSum = error "RowSum: TODO"
