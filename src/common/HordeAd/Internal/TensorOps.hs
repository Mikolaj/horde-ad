{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Miscellaneous more or less general purpose tensor operations.
module HordeAd.Internal.TensorOps
  ( module HordeAd.Internal.TensorOps
  ) where

import Prelude

import           Control.Arrow (first, second)
import           Control.Exception.Assert.Sugar
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Internal as OI
import qualified Data.Array.Internal.DynamicG
import qualified Data.Array.Internal.DynamicS
import qualified Data.Array.Internal.RankedG as RG
import qualified Data.Array.Internal.RankedS as RS
import qualified Data.Array.Internal.ShapedG
import qualified Data.Array.Internal.ShapedS
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Functor (void)
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Map as M
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable.Mutable as VM
import           Foreign (Ptr)
import           Foreign.C (CInt (..))
import           GHC.TypeLits (KnownNat, sameNat, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.SizedIndex
import HordeAd.Internal.OrthotopeOrphanInstances (liftVR)

type IndexInt n = Index n CInt

dummyTensor :: Numeric r => OD.Array r
dummyTensor =  -- an inconsistent tensor array
  Data.Array.Internal.DynamicS.A
  $ Data.Array.Internal.DynamicG.A []
  $ OI.T [] (-1) V.empty

isTensorDummy :: OD.Array r -> Bool
isTensorDummy (Data.Array.Internal.DynamicS.A
                 (Data.Array.Internal.DynamicG.A _
                    (OI.T _ (-1) _))) = True
isTensorDummy _ = False

toVectorOrDummy :: Numeric r
                => Int -> Vector r -> Vector r
toVectorOrDummy size x = if V.null x
                         then LA.konst 0 size
                         else x

toMatrixOrDummy :: Numeric r
                => (Int, Int) -> Matrix r -> Matrix r
toMatrixOrDummy size x = if LA.size x == (0, 0)
                         then LA.konst 0 size
                         else x

toDynamicOrDummy :: Numeric r
                 => OD.ShapeL -> OD.Array r -> OD.Array r
toDynamicOrDummy sh x = if isTensorDummy x
                        then OD.constant sh 0
                        else x

toShapedOrDummy :: (Numeric r, OS.Shape sh)
                => OD.Array r -> OS.Array sh r
toShapedOrDummy x = if isTensorDummy x
                    then OS.constant 0
                    else Data.Array.Convert.convert x

tindex0D :: Numeric r => OD.Array r -> [Int] -> r
tindex0D (Data.Array.Internal.DynamicS.A
            (Data.Array.Internal.DynamicG.A _
               OI.T{..})) is =
  values V.! (offset + sum (zipWith (*) is strides))
    -- TODO: tests are needed to verify if order of dimensions is right

-- There is no OR.update, so we convert.
updateR :: (Numeric a, KnownNat n)
        => OR.Array n a -> [(IndexInt n, a)] -> OR.Array n a
updateR arr upd = Data.Array.Convert.convert
                  $ OD.update (Data.Array.Convert.convert arr)
                  $ map (first (map fromIntegral . indexToList)) upd

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall m n a. (Numeric a, KnownNat m, KnownNat n)
         => OR.Array (m + n) a -> [(IndexInt m, OR.Array n a)]
         -> OR.Array (m + n) a
updateNR arr upd =
  let RS.A (RG.A shRaw OI.T{offset, values}) = OR.normalize arr
      !_A = assert (offset == 0) ()
  in let sh = listShapeToShape shRaw
         f t (ix, u) =
           let v = OR.toVector u
               i = fromIntegral $ toLinearIdx @m @n sh ix
           in LA.vjoin [V.take i t, v, V.drop (i + V.length v) t]
     in OR.fromVector shRaw (foldl' f values upd)

tsum0D
  :: Numeric r
  => OD.Array r -> r
tsum0D (Data.Array.Internal.DynamicS.A (Data.Array.Internal.DynamicG.A sh t)) =
  LA.sumElements $ OI.toUnorderedVectorT sh t

treplicate0ND
  :: Numeric r
  => ShapeInt n -> r -> OD.Array r
treplicate0ND sh = OD.constant (shapeToList sh)

tshapeR
  :: KnownNat n
  => OR.Array n r -> ShapeInt n
tshapeR = listShapeToShape . OR.shapeL

tsizeR
  :: OR.Array n r -> Int
tsizeR = OR.size

tlengthR
  :: OR.Array (1 + n) r -> Int
tlengthR u = case OR.shapeL u of
  [] -> error "tlength: missing dimensions"
  k : _ -> k

tminIndexR
  :: Numeric r
  => OR.Array 1 r -> CInt
tminIndexR = fromIntegral . LA.minIndex . OR.toVector

tmaxIndexR
  :: Numeric r
  => OR.Array 1 r -> CInt
tmaxIndexR = fromIntegral . LA.maxIndex . OR.toVector

ixInBounds :: [CInt] -> [Int] -> Bool
ixInBounds ix sh =
  and $ zipWith (\i dim -> 0 <= i && i < fromIntegral dim) ix sh

tindexNR
  :: forall m n r. (KnownNat m, Show r, Numeric r)
  => OR.Array (m + n) r -> IndexInt m -> OR.Array n r
tindexNR v@(RS.A (RG.A sh OI.T{strides, offset, values})) ix =
  let l = indexToList ix
      linear = offset + sum (zipWith (*) (map fromIntegral l) strides)
      plen = valueOf @m  -- length of prefix being indexed out of
      !_A = assert (ixInBounds l sh `blame` (ix, sh, v)) ()
  in
    RS.A (RG.A (drop plen sh) OI.T{ strides = drop plen strides
                                  , offset = linear
                                  , values })

tindexZR
  :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
  => OR.Array (m + n) r -> IndexInt m -> OR.Array n r
tindexZR v ix =
  let sh = OR.shapeL v
  in if ixInBounds (indexToList ix) sh
     then tindexNR v ix
     else OR.constant (drop (valueOf @m) sh) 0

tindex1R
  :: Numeric r
  => OR.Array (1 + n) r -> CInt -> OR.Array n r
tindex1R t i = OR.index t (fromIntegral i)

-- TODO: optimize to tindex1R for n == 0
tindex0R
  :: Numeric r
  => OR.Array n r -> IndexInt n -> r
tindex0R (RS.A (RG.A _ OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral $ indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way

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

instance {-# OVERLAPPABLE #-} Numeric r => RowSum r where
  rowSum = error "RowSum: TODO"
  columnSum = error "RowSum: TODO"

tsum0R
  :: Numeric r
  => OR.Array n r -> r
tsum0R (RS.A (RG.A sh (OI.T _ _ vt))) | V.length vt == 1 =
  fromIntegral (product sh) * vt V.! 0
-- tsumInR t@(RS.A (RG.A _ (OI.T _ _ vt))) | V.length vt == 1 =
tsum0R (RS.A (RG.A sh t)) =
  LA.sumElements $ OI.toUnorderedVectorT sh t

tdot0R
  :: Numeric r
  => OR.Array n r -> OR.Array n r -> r
tdot0R (RS.A (RG.A sh (OI.T _ _ vt))) (RS.A (RG.A _ (OI.T _ _ vu)))
  | V.length vt == 1 && V.length vu == 1 =
      fromIntegral (product sh) * vt V.! 0 * vu V.! 0
tdot0R t u = OR.toVector t LA.<.> OR.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0R (t * u)

tdot1InR
  :: (Numeric r, Show r, Num (Vector r), RowSum r)
  => OR.Array 2 r -> OR.Array 2 r -> OR.Array 1 r
tdot1InR t@(RS.A (RG.A _ (OI.T _ _ vt))) u@(RS.A (RG.A _ (OI.T _ _ vu))) =
  if V.length vt == 1 || V.length vu == 1
  then tsumInR (t * u)
  else let lt = map OR.toVector $ ORB.toList $ OR.unravel t
           lu = map OR.toVector $ ORB.toList $ OR.unravel u
           l = zipWith (LA.<.>) lt lu
       in OR.fromList [length l] $ l

tmatvecmulR
  :: Numeric r
  => OR.Array 2 r -> OR.Array 1 r -> OR.Array 1 r
tmatvecmulR t u =
  let t2 = OR.toVector t
      u2 = OR.toVector u
      (trows, tcols) = case OR.shapeL t of
        [r, c] -> (r, c)
        _ -> error "tmatvecmulR: wrong shape"
  in OR.fromVector [trows] $ LA.reshape tcols t2 LA.#> u2

tmatmul2R
  :: Numeric r
  => OR.Array 2 r -> OR.Array 2 r -> OR.Array 2 r
tmatmul2R t u =
  let t2 = OR.toVector t
      u2 = OR.toVector u
      (trows, tcols) = case OR.shapeL t of
        [r, c] -> (r, c)
        _ -> error "tmatmul2R: wrong shape"
      ucols = case OR.shapeL u of
        [_, c] -> c
        _ -> error "tmatmul2R: wrong shape"
  in OR.fromVector [trows, ucols] $ LA.flatten
     $ LA.reshape tcols t2 LA.<> LA.reshape ucols u2

tminimum0R
  :: Numeric r
  => OR.Array 1 r -> r
tminimum0R = LA.minElement . OR.toVector

tmaximum0R
  :: Numeric r
  => OR.Array 1 r -> r
tmaximum0R = LA.maxElement . OR.toVector

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probbaly optimal in this respect
-- (the only new vectors are created by LA.vjoin, but this is done on demand).
-- TODO: optimize updateNR and make it consume and forget arguments
-- one by one to make the above true
--
-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensors is added at such an index.
tscatterZR :: forall m p n r.
              ( KnownNat m, KnownNat p, KnownNat n, NumAndDebug r
              , Num (Vector r) )
           => ShapeInt (p + n) -> OR.Array (m + n) r
           -> (IndexInt m -> IndexInt p)
           -> OR.Array (p + n) r
tscatterZR sh t f =
  let (shm', shn) = splitAt (valueOf @m) $ OR.shapeL t
      s = product shm'
      shm = listShapeToShape shm'
      g ix =
        let ix2 = f ix
        in if ixInBounds (indexToList ix2) (shapeToList sh)
           then M.insertWith (++) ix2 [OR.toVector $ t `tindexNR` ix]
           else id
      ivs = foldr g M.empty [ fromLinearIdx shm i
                            | i <- [0 .. fromIntegral s - 1] ]
  in updateNR (treplicate0NR sh 0) $ map (second $ OR.fromVector shn . sum)
                               $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OR.fromVector
-- or optimize tscatterNR and instantiate it instead
tscatterZ1R :: (Numeric r, Show r, Num (Vector r), KnownNat p, KnownNat n)
            => ShapeInt (p + n) -> OR.Array (1 + n) r -> (CInt -> IndexInt p)
            -> OR.Array (p + n) r
tscatterZ1R sh t f = case OR.shapeL t of
  0 : _ -> OR.constant (shapeToList sh) 0
  _ ->
    V.sum $ V.imap (\i ti ->
                     let ix2 = f $ fromIntegral i
                     in if ixInBounds (indexToList ix2) (shapeToList sh)
                        then updateNR (treplicate0NR sh 0) [(ix2, ti)]
                        else treplicate0NR sh 0)
          $ ORB.toVector $ OR.unravel t

tfromListR
  :: forall n r. (KnownNat n, Numeric r)
  => [OR.Array n r] -> OR.Array (1 + n) r
tfromListR [] =
  case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.fromList [0] []  -- the only case where we can guess sh
    _ ->  error "tfromListR: shape ambiguity, no arguments"
tfromListR l = OR.ravel $ ORB.fromList [length l] l

tfromList0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> [r] -> OR.Array n r
tfromList0NR sh = OR.fromList (shapeToList sh)

tfromVectorR
  :: forall n r. (KnownNat n, Numeric r)
  => Data.Vector.Vector (OR.Array n r) -> OR.Array (1 + n) r
tfromVectorR l | V.null l =
  case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.fromList [0] []
    _ ->  error "tfromVectorR: shape ambiguity, no arguments"
tfromVectorR l = OR.ravel $ ORB.fromVector [V.length l] $ V.convert l

tfromVector0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> Data.Vector.Vector r -> OR.Array n r
tfromVector0NR sh l = OR.fromVector (shapeToList sh) $ V.convert l

treplicateR
  :: forall n r. (KnownNat n, Numeric r)
  => Int -> OR.Array n r -> OR.Array (1 + n) r
treplicateR 0 u = OR.fromList (0 : OR.shapeL u) []
treplicateR s u = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> OR.constant [s] (OR.unScalar u)
  _ -> OR.ravel $ ORB.constant [s] u

treplicate0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> r -> OR.Array n r
treplicate0NR sh = OR.constant (shapeToList sh)

tappendR
  :: (KnownNat n, Numeric r)
  => OR.Array n r -> OR.Array n r -> OR.Array n r
tappendR = OR.append

tsliceR
  :: Int -> Int -> OR.Array n r -> OR.Array n r
tsliceR i k = OR.slice [(i, k)]

treverseR
  :: OR.Array (1 + n) r -> OR.Array (1 + n) r
treverseR = OR.rev [0]

ttransposeR
  :: KnownNat n
  => Permutation -> OR.Array n r -> OR.Array n r
ttransposeR = OR.transpose

treshapeR
  :: (KnownNat n, KnownNat m, Numeric r)
  => ShapeInt m -> OR.Array n r -> OR.Array m r
treshapeR sh = OR.reshape (shapeToList sh)

-- TODO: use tbuild0R and tbuild1R whenever faster and possible;
-- also consider generating a flat vector and reshaping at the end
-- to save on creating the intermediate tensors, though that's
-- a negligible cost if the tensors of rank n don't have a small size
tbuildNR
  :: forall m n r. (KnownNat m, KnownNat n, Numeric r)
  => ShapeInt (m + n) -> (IndexInt m -> OR.Array n r) -> OR.Array (m + n) r
tbuildNR sh0 f0 =
  let buildSh :: forall m1. KnownNat m1
              => ShapeInt m1 -> (IndexInt m1 -> OR.Array n r)
              -> OR.Array (m1 + n) r
      buildSh ZS f = f ZI
      buildSh (0 :$ sh) _ =
        OR.fromList (0 : shapeToList sh ++ shapeToList (dropShape @m @n sh0)) []
      buildSh (k :$ sh) f =
        let g i = buildSh sh (\ix -> f (i :. ix))
        in OR.ravel $ ORB.fromList [k]
           $ map g [0 .. fromIntegral k - 1]
  in buildSh (takeShape @m @n sh0) f0

tbuild1R
  :: forall n r. (KnownNat n, Numeric r)
  => Int -> (CInt -> OR.Array n r) -> OR.Array (1 + n) r
tbuild1R 0 _ = tfromListR []  -- if we applied f, we'd change strictness
tbuild1R k f = OR.ravel $ ORB.fromList [k]
               $ map f [0 .. fromIntegral k - 1]  -- hope this fuses

tmap0NR
  :: Numeric r
  => (OR.Array 0 r -> OR.Array 0 r) -> OR.Array n r -> OR.Array n r
tmap0NR f = OR.mapA (tunScalarR . f . tscalarR)
            -- too slow: tbuildNR (tshapeR v) (\ix -> f $ v `tindexNR` ix)
            -- bad type: liftVR . LA.cmap

tzipWith0NR
  :: Numeric r
  => (OR.Array 0 r -> OR.Array 0 r -> OR.Array 0 r)
  -> OR.Array n r -> OR.Array n r
  -> OR.Array n r
tzipWith0NR f = OR.zipWithA (\x y -> tunScalarR $ f (tscalarR x) (tscalarR y))
                -- bad type: liftVR2 . Numeric.LinearAlgebra.Devel.zipVectorWith

tgatherNR :: forall m p n r.
             (KnownNat m, KnownNat p, KnownNat n, Show r, Numeric r)
          => ShapeInt (m + n) -> OR.Array (p + n) r
          -> (IndexInt m -> IndexInt p)
          -> OR.Array (m + n) r
tgatherNR sh t f =
  let shm = takeShape @m sh
      s = sizeShape shm
      l = [ OR.toVector $ t `tindexNR` f (fromLinearIdx shm i)
          | i <- [0 .. fromIntegral s - 1] ]
  in OR.fromVector (shapeToList sh) $ LA.vjoin l

tgather1R :: forall p n r. (KnownNat p, KnownNat n, Show r, Numeric r)
          => Int -> OR.Array (p + n) r -> (CInt -> IndexInt p)
          -> OR.Array (1 + n) r
tgather1R 0 t _ = OR.fromList (0 : drop (valueOf @p) (OR.shapeL t)) []
tgather1R k t f =
  let l = map (\i -> t `tindexNR` f i) [0 .. fromIntegral k - 1]
  in OR.ravel $ ORB.fromList [k] l

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexZR
--
-- Note how tindexZR is used. The semantics of the operation
-- permits index out of bounds and the result of such indexing is zero.
tgatherZR :: forall m p n r.
             (KnownNat m, KnownNat p, KnownNat n, Show r, Numeric r)
          => ShapeInt (m + n) -> OR.Array (p + n) r
          -> (IndexInt m -> IndexInt p)
          -> OR.Array (m + n) r
tgatherZR sh t f =
  let shm = takeShape @m sh
      s = sizeShape shm
      l = [ OR.toVector $ t `tindexZR` f (fromLinearIdx shm i)
          | i <- [0 .. fromIntegral s - 1] ]
  in OR.fromVector (shapeToList sh) $ LA.vjoin l

tgatherZ1R :: forall p n r. (KnownNat p, KnownNat n, Show r, Numeric r)
           => Int -> OR.Array (p + n) r -> (CInt -> IndexInt p)
           -> OR.Array (1 + n) r
tgatherZ1R 0 t _ = OR.fromList (0 : drop (valueOf @p) (OR.shapeL t)) []
tgatherZ1R k t f =
  let l = map (\i -> t `tindexZR` f i) [0 .. fromIntegral k - 1]
  in OR.ravel $ ORB.fromList [k] l

tscalarR
  :: Numeric r
  => r -> OR.Array 0 r
tscalarR = OR.scalar

tunScalarR
  :: Numeric r
  => OR.Array 0 r -> r
tunScalarR = OR.unScalar

tscaleByScalarR :: (Numeric r, KnownNat n)
                => r -> OR.Array n r -> OR.Array n r
tscaleByScalarR s v = liftVR (LA.scale s) v

-- We often debug around here, so let's add Show and obfuscate it
-- to avoid warnings that it's unused. The addition silences warnings upstream.
type NumAndDebug r = (Numeric r, Show r)

tsum0S
  :: (Numeric r, OS.Shape sh)
  => OS.Array sh r -> r
tsum0S arr@(Data.Array.Internal.ShapedS.A (Data.Array.Internal.ShapedG.A t)) =
  LA.sumElements $ OI.toUnorderedVectorT (OS.shapeL arr) t

-- Takes a shape.
fromLinearIdx2 :: Integral i => [i] -> i -> [i]
fromLinearIdx2 = \sh lin -> snd (go sh lin)
  where
    go [] n = (n, [])
    go (n : sh) lin =
      let (tensLin, idxInTens) = go sh lin
          (tensLin', i) = tensLin `quotRem` n
      in (tensLin', i : idxInTens)
