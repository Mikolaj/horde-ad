{-# LANGUAGE DataKinds #-}
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
import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Internal
import qualified Data.Array.Internal.DynamicG
import qualified Data.Array.Internal.DynamicS
import qualified Data.Array.Internal.RankedG
import qualified Data.Array.Internal.RankedS
import qualified Data.Array.Internal.ShapedG
import qualified Data.Array.Internal.ShapedS
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl')
import qualified Data.Strict.Map as M
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import qualified Numeric.LinearAlgebra.Devel
import           Text.Show.Functions ()

import HordeAd.Core.SizedIndex
import HordeAd.Internal.OrthotopeOrphanInstances (liftVR, liftVR2)

dummyTensor :: Numeric r => OT.Array r
dummyTensor =  -- an inconsistent tensor array
  Data.Array.Internal.DynamicS.A
  $ Data.Array.Internal.DynamicG.A []
  $ Data.Array.Internal.T [] (-1) V.empty

isTensorDummy :: OT.Array r -> Bool
isTensorDummy (Data.Array.Internal.DynamicS.A
                 (Data.Array.Internal.DynamicG.A _
                    (Data.Array.Internal.T _ (-1) _))) = True
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

toShapedOrDummy :: (Numeric r, OS.Shape sh)
                => OT.Array r -> OS.Array sh r
toShapedOrDummy x = if isTensorDummy x
                    then OS.constant 0
                    else Data.Array.Convert.convert x

toDynamicOrDummy :: Numeric r
                 => OT.ShapeL -> OT.Array r -> OT.Array r
toDynamicOrDummy sh x = if isTensorDummy x
                        then OT.constant sh 0
                        else x

tindex0D :: Numeric r => OT.Array r -> [Int] -> r
tindex0D (Data.Array.Internal.DynamicS.A
            (Data.Array.Internal.DynamicG.A _
               Data.Array.Internal.T{..})) is =
  values V.! (offset + sum (zipWith (*) is strides))
    -- TODO: tests are needed to verify if order of dimensions is right

-- There is no OR.update, so we convert.
updateR :: (Numeric a, KnownNat n)
        => OR.Array n a -> [(IndexInt n, a)] -> OR.Array n a
updateR arr upd = Data.Array.Convert.convert
                  $ OT.update (Data.Array.Convert.convert arr)
                  $ map (first indexToList) upd

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall m n a. (Numeric a, KnownNat m, KnownNat n)
         => OR.Array (m + n) a -> [(IndexInt m, OR.Array n a)]
         -> OR.Array (m + n) a
updateNR arr upd =
  let Data.Array.Internal.RankedS.A
        (Data.Array.Internal.RankedG.A shRaw
           Data.Array.Internal.T{offset, values}) = OR.normalize arr
      !_A = assert (offset == 0) ()
  in let sh = listShapeToShape shRaw
         f t (ix, u) =
           let v = OR.toVector u
               i = toLinearIdx @m @n sh ix
           in LA.vjoin [V.take i t, v, V.drop (i + V.length v) t]
     in OR.fromVector shRaw (foldl' f values upd)

tsum0D
  :: Numeric r
  => OT.Array r -> r
tsum0D (Data.Array.Internal.DynamicS.A (Data.Array.Internal.DynamicG.A sh t)) =
  LA.sumElements $ Data.Array.Internal.toUnorderedVectorT sh t

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
  => OR.Array 1 r -> Int
tminIndexR = LA.minIndex . OR.toVector

tmaxIndexR
  :: Numeric r
  => OR.Array 1 r -> Int
tmaxIndexR = LA.maxIndex . OR.toVector

tindexR
  :: Numeric r
  => OR.Array (1 + n) r -> Int -> OR.Array n r
tindexR = OR.index

-- TODO: optimize to tindexR for n == 0
tindex0R
  :: Numeric r
  => OR.Array n r -> IndexInt n -> r
tindex0R (Data.Array.Internal.RankedS.A
            (Data.Array.Internal.RankedG.A _
               Data.Array.Internal.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (indexToList ix) strides))
    -- to avoid linearizing @values@, we do everything in unsized way

tindexNR
  :: forall m n r. KnownNat m
  => OR.Array (m + n) r -> IndexInt m -> OR.Array n r
tindexNR (Data.Array.Internal.RankedS.A
            (Data.Array.Internal.RankedG.A sh
               Data.Array.Internal.T{strides, offset, values})) ix =
  let i = offset + sum (zipWith (*) (indexToList ix) strides)
      plen = valueOf @m  -- length of prefix being indexed out of
  in
    Data.Array.Internal.RankedS.A
      (Data.Array.Internal.RankedG.A (drop plen sh)
         Data.Array.Internal.T{strides = drop plen strides, offset = i, values})

tsumR
  :: (KnownNat n, Numeric r, Num (Vector r))
  => OR.Array (1 + n) r -> OR.Array n r
tsumR = ORB.sumA . OR.unravel

tsum0R
  :: Numeric r
  => OR.Array n r -> r
tsum0R (Data.Array.Internal.RankedS.A (Data.Array.Internal.RankedG.A sh t)) =
  LA.sumElements $ Data.Array.Internal.toUnorderedVectorT sh t

tdot0R
  :: Numeric r
  => OR.Array n r -> OR.Array n r -> r
tdot0R u v = OR.toVector u LA.<.> OR.toVector v
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT

tminimum0R
  :: Numeric r
  => OR.Array 1 r -> r
tminimum0R = LA.minElement . OR.toVector

tmaximum0R
  :: Numeric r
  => OR.Array 1 r -> r
tmaximum0R = LA.maxElement . OR.toVector

tunScalarR
  :: Numeric r
  => OR.Array 0 r -> r
tunScalarR = OR.unScalar

tscalarR
  :: Numeric r
  => r -> OR.Array 0 r
tscalarR = OR.scalar

tfromListR
  :: (KnownNat n, Numeric r)
  => [OR.Array n r] -> OR.Array (1 + n) r
tfromListR l = OR.ravel $ ORB.fromList [length l] l

tfromList0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> [r] -> OR.Array n r
tfromList0NR sh = OR.fromList (shapeToList sh)

tfromVectorR
  :: (KnownNat n, Numeric r)
  => Data.Vector.Vector (OR.Array n r) -> OR.Array (1 + n) r
tfromVectorR l = OR.ravel $ ORB.fromVector [V.length l] $ V.convert l

tfromVector0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> Data.Vector.Vector r -> OR.Array n r
tfromVector0NR sh l = OR.fromVector (shapeToList sh) $ V.convert l

tkonstR
  :: (KnownNat n, Numeric r)
  =>  Int -> OR.Array n r -> OR.Array (1 + n) r
tkonstR s u = OR.ravel $ ORB.constant [s] u

tkonst0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> r -> OR.Array n r
tkonst0NR sh = OR.constant (shapeToList sh)

tappendR
  :: (KnownNat n, Numeric r)
  => OR.Array n r -> OR.Array n r -> OR.Array n r
tappendR = OR.append

tsliceR
  :: Int -> Int -> OR.Array n r -> OR.Array n r
tsliceR i k = OR.slice [(i, k)]

treverseR
  :: OR.Array n r -> OR.Array n r
treverseR = OR.rev [0]

ttransposeGeneralR
  :: KnownNat n
  => Permutation -> OR.Array n r -> OR.Array n r
ttransposeGeneralR = OR.transpose

treshapeR
  :: (KnownNat n, KnownNat m, Numeric r)
  => ShapeInt m -> OR.Array n r -> OR.Array m r
treshapeR sh = OR.reshape (shapeToList sh)

tbuildR
  :: (KnownNat n, Numeric r)
  => Int -> (Int -> OR.Array n r) -> OR.Array (1 + n) r
tbuildR k f = OR.ravel $ ORB.fromList [k]
              $ map f [0 .. k - 1]  -- hope this fuses

tbuild0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> (IndexInt n -> r) -> OR.Array n r
tbuild0NR sh f = OR.generate (shapeToList sh) (f . listToIndex)

-- TODO: use tbuild0R and tbuildR whenever faster and possible;
-- also consider generating a flat vector and reshaping at the end
-- to save on creating the intermediate tensors, though that's
-- a negligible cost if the tensors of rank n don't have a small size
tbuildNR
  :: forall m n r. (KnownNat m, KnownNat n, Numeric r)
  => ShapeInt (m + n) -> (IndexInt m -> OR.Array n r) -> OR.Array (m + n) r
tbuildNR sh0 f0 =
  let buildSh :: KnownNat m1
              => ShapeInt m1 -> (IndexInt m1 -> OR.Array n r)
              -> OR.Array (m1 + n) r
      buildSh ZS f = f ZI
      buildSh (k :$ sh) f =
        let g i = buildSh sh (\ix -> f (i :. ix))
        in OR.ravel $ ORB.fromList [k]
           $ map g [0 .. k - 1]
  in buildSh (takeShape @m @n sh0) f0

tmap0NR
  :: (KnownNat n, Numeric r)
  => (r -> r) -> OR.Array n r -> OR.Array n r
tmap0NR = liftVR . LA.cmap

tzipWith0NR
  :: (KnownNat n, Numeric r)
  => (r -> r -> r) -> OR.Array n r -> OR.Array n r -> OR.Array n r
tzipWith0NR = liftVR2 . Numeric.LinearAlgebra.Devel.zipVectorWith

tgatherR :: (Numeric r, KnownNat p, KnownNat n)
         => (Int -> IndexInt p)
         -> OR.Array (p + n) r -> Int -> OR.Array (1 + n) r
tgatherR f t k =
  let l = map (\i -> t `tindexNR` f i) [0 .. k - 1]
  in OR.ravel $ ORB.fromList [k] l

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexNR
tgatherNR :: forall m p n r. (KnownNat m, KnownNat p, KnownNat n, Numeric r)
          => (IndexInt m -> IndexInt p)
          -> OR.Array (p + n) r
          -> ShapeInt (m + n) -> OR.Array (m + n) r
tgatherNR f t sh =
  let shm = takeShape @m sh
      s = shapeSize shm
      l = map (\ix -> OR.toVector $ t `tindexNR` f ix)
              [fromLinearIdx shm i | i <- [0 .. s - 1]]
  in OR.fromVector (shapeToList sh) $ LA.vjoin l

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OR.fromVector
-- or optimize tscatterNR and instantiate it instead
tscatterR :: (Numeric r, Num (Vector r), KnownNat p, KnownNat n)
          => (Int -> IndexInt p)
          -> OR.Array (1 + n) r -> ShapeInt (p + n) -> OR.Array (p + n) r
tscatterR f t sh =
  V.sum $ V.imap (\i ti -> updateNR (tkonst0NR sh 0) [(f i, ti)])
        $ ORB.toVector $ OR.unravel t

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probbaly optimal in this respect
-- (the only new vectors are created by LA.vjoin, but this is done on demand).
-- TODO: optimize updateNR and make it consume and forget arguments
-- one by one to make the above true
tscatterNR :: forall m p n r.
              (KnownNat m, KnownNat p, KnownNat n, Numeric r, Num (Vector r))
           => (IndexInt m -> IndexInt p)
           -> OR.Array (m + n) r
           -> ShapeInt (p + n) -> OR.Array (p + n) r
tscatterNR f t sh =
  let (shm', shn) = splitAt (valueOf @m) $ OR.shapeL t
      s = product shm'
      shm = listShapeToShape shm'
      g ix = M.insertWith (++) (f ix) [OR.toVector $ t `tindexNR` ix]
      ivs = foldr g M.empty [fromLinearIdx shm i | i <- [0 .. s - 1]]
  in updateNR (tkonst0NR sh 0) $ map (second $ OR.fromVector shn . sum)
                               $ M.assocs ivs

tsum0S
  :: (Numeric r, OS.Shape sh)
  => OS.Array sh r -> r
tsum0S arr@(Data.Array.Internal.ShapedS.A (Data.Array.Internal.ShapedG.A t)) =
  LA.sumElements $ Data.Array.Internal.toUnorderedVectorT (OS.shapeL arr) t

-- Takes a shape.
fromLinearIdx2 :: Integral i => [i] -> i -> [i]
fromLinearIdx2 = \sh lin -> snd (go sh lin)
  where
    go [] n = (n, [])
    go (n : sh) lin =
      let (tensLin, idxInTens) = go sh lin
          (tensLin', i) = tensLin `quotRem` n
      in (tensLin', i : idxInTens)
