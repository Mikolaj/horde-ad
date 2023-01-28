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

import           Control.DeepSeq (NFData)
import           Control.Exception.Assert.Sugar
import           Control.Monad (liftM2)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Internal
import qualified Data.Array.Internal.DynamicG
import qualified Data.Array.Internal.DynamicS
import qualified Data.Array.Internal.RankedG
import qualified Data.Array.Internal.RankedS
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import qualified Data.EnumMap.Strict as EM
import           Data.Kind (Type)
import           Data.List (foldl', sort)
import           Data.List.Index (ifoldl')
import           Data.Primitive (Prim)
import           Data.STRef (newSTRef, readSTRef, writeSTRef)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Generics (Generic)
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Text.Show.Functions ()
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Internal.OrthotopeOrphanInstances

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

atPathInTensor :: Numeric r => OT.Array r -> [Int] -> r
atPathInTensor (Data.Array.Internal.DynamicS.A
                   (Data.Array.Internal.DynamicG.A _
                      Data.Array.Internal.T{..})) is =
  values V.! (offset + sum (zipWith (*) is strides))
    -- TODO: tests are needed to verify if order of dimensions is right

atPathInTensorOR :: Numeric r => OR.Array n r -> [Int] -> r
atPathInTensorOR (Data.Array.Internal.RankedS.A
                    (Data.Array.Internal.RankedG.A _
                       Data.Array.Internal.T{..})) is =
  values V.! (offset + sum (zipWith (*) is strides))

atPathInTensorORN :: (Numeric r, KnownNat n)
                  => OR.Array (1 + m + n) r -> [Int] -> OR.Array n r
atPathInTensorORN arr ixs =
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

updateOR :: (Numeric a, KnownNat n)
         => OR.Array n a -> [([Int], a)] -> OR.Array n a
updateOR arr upd = Data.Array.Convert.convert
                   $ OT.update (Data.Array.Convert.convert arr) upd

-- The paths (lists of indexes) are of length @m@.
updateORN :: (Numeric a, KnownNat n, KnownNat m)
          => OR.Array (m + n) a -> [([Int], OR.Array n a)]
          -> OR.Array (m + n) a
updateORN arr upd =
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

gather :: (Numeric r, KnownNat n)
       => Int -> (Int -> [Int])
       -> OR.Array (m + n) r -> OR.Array (1 + n) r
gather n f t =
  let l = map (\i -> unsafeCoerce t `atPathInTensorORN` f i) [0 .. n - 1]
  in OR.ravel $ ORB.fromList [n] l

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OR.fromVector
scatter :: (Numeric r, Num (Vector r), KnownNat n, KnownNat m)
        => (Int -> [Int])
        -> OR.Array (1 + n) r -> OR.ShapeL -> OR.Array (m + n) r
scatter f t sh =
  V.sum $ V.imap (\i ti -> updateORN (OR.constant sh 0) [(f i, ti)])
        $ ORB.toVector $ OR.unravel t

-- Copied from Data.Array.Internal.
getStrides :: [Int] -> [Int]
getStrides = scanr (*) 1
toIx :: [Int] -> Int -> [Int]
toIx [] _ = []
toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
