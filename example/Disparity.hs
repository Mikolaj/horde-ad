{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-compat-unqualified-imports #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
-- | TODO: outdated, uses the old API
module Disparity where
import qualified Data.Array.ShapedS as OS
import           Data.List
import qualified Foreign.Storable as F
import           GHC.TypeLits (KnownNat)
import           HordeAd
import           Prelude
import qualified System.Random as R


-- | Disparity cost volume.
--
--   Take two arrays of multi channel 2d images, where the first contains
--   left views of the scene and the second contains right views.
--
--   For each pair of images, slice the right image over the left image,
--   and for each offset produce the L1 distance indicating how well correponding
--   multi-channel image elements in the right image match those in the left.
--
--   Described in:
--    Anytime Stereo Image Depth Estimation on Mobile Devices
--    Wang, Lai et al, ICRA 2019
--    https://arxiv.org/abs/1810.11408
--    Section III b).
--
costVolume
 :: forall d r nImgs nChas nRows nCols nCount shA shO.
    ( ADModeAndNum d r
    , KnownNat nImgs, KnownNat nChas, KnownNat nRows, KnownNat nCols
    , shA ~ '[nImgs, nChas,  nRows, nCols]
    , shO ~ '[nImgs, nCount, nRows, nCols])
 => Int
 -> SNat nCount
 -> ADVal d (OS.Array shA r)
 -> ADVal d (OS.Array shA r)
 -> ADVal d (OS.Array shO r)

costVolume iStart SNat arrL arrR =
  buildS @shO $ \[iImg, iDisp, iRow, iCol] ->
    let arrVecL = buildS @'[nChas] $ \[iCha] ->
                    indexzS0 arrL [iImg, iCha, iRow, iCol]
        iSrc    = iCol - iStart - iDisp
        arrVecR = buildS @'[nChas] $ \[iCha] ->
                    indexzS0 arrR [iImg, iCha, iRow, iSrc]
    in  sumElements10
         $ flattenS1
         $ zipWithOuterS (\xL xR -> abs (xL - xR)) arrVecL arrVecR



-- Write out an example test vector.
testCostVolume
 = let  arrL    = random @'[1, 2, 4, 6] @Double 1
        arrR    = random @'[1, 2, 4, 6] @Double 2
        arrS    = random @'[1, 4, 4, 6] @Double 3
          -- TODO: this is unused
        arrO    = primal $ costVolume 0 (SNat :: SNat 4) (constant arrL) (constant arrR)
        arrDL   = revDt (\aL -> costVolume 0 SNat aL (constant arrR)) arrL arrO
        arrDR   = revDt (\aR -> costVolume 0 SNat (constant arrL) aR) arrR arrO
   in   putStrLn $ unlines
         [ "arrL  = " ++ show arrL
         , "arrR  = " ++ show arrR
         , "arrS  = " ++ show arrS
         , "arrO  = " ++ show arrO
         , "arrDR = " ++ show arrDR
         , "arrDL = " ++ show arrDL ]


-- | Generate an array of random values for testing.
random
 :: forall sh a
 .  (Num a, R.UniformRange a, F.Storable a, OS.Shape sh)
 => Int -> OS.Array sh a
random seed
 = let  xs = OS.fromList
           $ take (OS.size xs)
           $ unfoldr (Just . R.uniformR (-1, 1)) (R.mkStdGen seed)
   in   xs


-- TODO: where is the real version of this defined?
primal :: ADVal 'ADModeValue a -> a
primal (D a _) = a
