{-# LANGUAGE CPP, DataKinds, DeriveAnyClass, DeriveGeneric, DerivingStrategies,
             GADTs, GeneralizedNewtypeDeriving, KindSignatures, RankNTypes,
             StandaloneDeriving, UnboxedTuples #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Miscellaneous more or less general purpose tensor operations.
module HordeAd.Internal.TensorOps
  ( module HordeAd.Internal.TensorOps
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
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
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Text.Show.Functions ()
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Internal.OrthotopeOrphanInstances ()

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

atPathInTensorD :: Numeric r => OT.Array r -> [Int] -> r
atPathInTensorD (Data.Array.Internal.DynamicS.A
                   (Data.Array.Internal.DynamicG.A _
                      Data.Array.Internal.T{..})) is =
  values V.! (offset + sum (zipWith (*) is strides))
    -- TODO: tests are needed to verify if order of dimensions is right

atPathInTensorR :: Numeric r => OR.Array n r -> [Int] -> r
atPathInTensorR (Data.Array.Internal.RankedS.A
                   (Data.Array.Internal.RankedG.A _
                      Data.Array.Internal.T{..})) is =
  values V.! (offset + sum (zipWith (*) is strides))

atPathInTensorNR :: (Numeric r, KnownNat n)
                 => OR.Array (1 + m + n) r -> [Int] -> OR.Array n r
atPathInTensorNR arr ixs =
  let Data.Array.Internal.DynamicS.A
        (Data.Array.Internal.DynamicG.A sh
           Data.Array.Internal.T{..}) =
             OT.normalize $ Data.Array.Convert.convert arr
               -- OT to avoid KnownNat m, which breaks typing of other code
               -- due to no sized lists
      !_A = assert (offset == 0) ()
  in let pathToIx is = sum (zipWith (*) is strides)
         ix = pathToIx ixs
         shN = drop (length ixs) sh
         len = product shN
     in OR.fromVector shN $ V.slice ix len values
  -- Old implementation:
  -- Data.Array.Convert.convert
  -- $ foldl' OT.index (Data.Array.Convert.convert v) is

updateR :: (Numeric a, KnownNat n)
        => OR.Array n a -> [([Int], a)] -> OR.Array n a
updateR arr upd = Data.Array.Convert.convert
                   $ OT.update (Data.Array.Convert.convert arr) upd

-- The paths (lists of indexes) are of length @m@.
updateNR :: (Numeric a, KnownNat n, KnownNat m)
         => OR.Array (m + n) a -> [([Int], OR.Array n a)]
         -> OR.Array (m + n) a
updateNR arr upd =
  let Data.Array.Internal.RankedS.A
        (Data.Array.Internal.RankedG.A sh
           Data.Array.Internal.T{..}) = OR.normalize arr
      !_A = assert (offset == 0) ()
  in let pathToIx is = sum (zipWith (*) is strides)
         f t (ixs, u) =
           let v = OR.toVector u
               ix = pathToIx ixs
           in LA.vjoin [V.take ix t, v, V.drop (ix + V.length v) t]
     in OR.fromVector sh (foldl' f values upd)

tsum0D
  :: Numeric r
  => OT.Array r -> r
tsum0D (Data.Array.Internal.DynamicS.A (Data.Array.Internal.DynamicG.A sh t)) =
  LA.sumElements $ Data.Array.Internal.toUnorderedVectorT sh t

tlengthR
  :: OR.Array (1 + n) r -> Int
tlengthR u = case OR.shapeL u of
  [] -> error "tlength: missing dimensions"
  k : _ -> k

tsizeR
  :: OR.Array n r -> Int
tsizeR = OR.size

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

tindex0R
  :: Numeric r
  => OR.Array (1 + n) r -> [Int] -> r
tindex0R = atPathInTensorR

tindexNR
  :: (KnownNat n, Numeric r)
  => OR.Array (1 + m + n) r -> [Int] -> OR.Array n r
tindexNR = atPathInTensorNR

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

tminimum0R
  :: Numeric r
  => OR.Array 1 r -> r
tminimum0R = LA.minElement . OR.toVector

tmaximum0R
  :: Numeric r
  => OR.Array 1 r -> r
tmaximum0R = LA.maxElement . OR.toVector

tfromListR
  :: (KnownNat n, Numeric r)
  => [OR.Array n r] -> OR.Array (1 + n) r
tfromListR l = OR.ravel $ ORB.fromList [length l] l

tfromList0NR
  :: (KnownNat n, Numeric r)
  => [Int] -> [r] -> OR.Array n r
tfromList0NR = OR.fromList

tfromVectorR
  :: (KnownNat n, Numeric r)
  => Data.Vector.Vector (OR.Array n r) -> OR.Array (1 + n) r
tfromVectorR l = OR.ravel $ ORB.fromVector [V.length l] $ V.convert l

tfromVector0NR
  :: (KnownNat n, Numeric r)
  => [Int] -> Data.Vector.Vector r -> OR.Array n r
tfromVector0NR sh l = OR.fromVector sh $ V.convert l

tkonstR
  :: (KnownNat n, Numeric r)
  =>  Int -> OR.Array n r -> OR.Array (1 + n) r
tkonstR n u = OR.ravel $ ORB.constant [n] u

tkonst0NR
  :: (KnownNat n, Numeric r)
  => [Int] -> r -> OR.Array (1 + n) r
tkonst0NR sh r = OR.constant sh r

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
  => [Int] -> OR.Array n r -> OR.Array n r
ttransposeGeneralR = OR.transpose

treshapeR
  :: (KnownNat n, KnownNat m, Numeric r)
  => [Int] -> OR.Array n r -> OR.Array m r
treshapeR = OR.reshape

tbuildR
  :: (KnownNat n, Numeric r)
  => Int -> (Int -> OR.Array n r) -> OR.Array (1 + n) r
tbuildR n f = tfromListR $ map f [0 .. n - 1]

tbuild0NR
  :: (KnownNat n, Numeric r)
  => [Int] -> ([Int] -> r) -> OR.Array n r
tbuild0NR = OR.generate

tgatherR :: (Numeric r, KnownNat n)
         => Int -> (Int -> [Int])
         -> OR.Array (m + n) r -> OR.Array (1 + n) r
tgatherR n f t =
  let l = map (\i -> unsafeCoerce t `atPathInTensorNR` f i) [0 .. n - 1]
  in OR.ravel $ ORB.fromList [n] l

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OR.fromVector
tscatterR :: (Numeric r, Num (Vector r), KnownNat n, KnownNat m)
          => (Int -> [Int])
          -> OR.Array (1 + n) r -> OR.ShapeL -> OR.Array (m + n) r
tscatterR f t sh =
  V.sum $ V.imap (\i ti -> updateNR (OR.constant sh 0) [(f i, ti)])
        $ ORB.toVector $ OR.unravel t
tsum0S
  :: (Numeric r, OS.Shape sh)
  => OS.Array sh r -> r
tsum0S arr@(Data.Array.Internal.ShapedS.A (Data.Array.Internal.ShapedG.A t)) =
  LA.sumElements $ Data.Array.Internal.toUnorderedVectorT (OS.shapeL arr) t

-- The two below copied from Data.Array.Internal.
getStrides :: [Int] -> [Int]
getStrides = scanr (*) 1

toIx :: [Int] -> Int -> [Int]
toIx [] _ = []
toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
