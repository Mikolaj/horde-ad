module Main
  ( main
  ) where

import Prelude

import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))

import Data.Array.Nested (ListR (..))
import Data.Array.Nested qualified as Nested

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Types

import MnistData
import MnistFcnnRanked1 qualified

valsInitVTOPP :: MnistFcnnRanked1.ADFcnnMnist1Parameters RepN 1 1 Double
valsInitVTOPP =
  ( ( (RepN $ Nested.sfromList1Prim (SNat @SizeMnistGlyph)
       $ replicate sizeMnistGlyphInt 0) ::: ZR
    , RepN $ Nested.sfromList1Prim (SNat @1) [1] )
  , ( (RepN $ Nested.sfromList1Prim (SNat @1) [1]) ::: ZR
    , RepN $ Nested.sfromList1Prim (SNat @1) [1] )
  , ( fromList (replicate sizeMnistLabelInt
                          (RepN $ Nested.sfromList1Prim (SNat @1) [1]))
    , RepN $ Nested.sfromList1Prim (SNat @SizeMnistLabel)
      $ replicate 10 0 ) )

main
  :: forall r. r ~ Double
  => IO ()
main = do
  let ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters RepN 1 1 Double
            -> Double
      ftest = MnistFcnnRanked1.afcnnMnistTest1 (SNat @1) (SNat @1)
      blackGlyph = Nested.rfromList1Prim $ replicate sizeMnistGlyphInt 0
      blackLabel = Nested.rfromList1Prim $ replicate 10 0
      !testErrorFinal = ftest [(blackGlyph, blackLabel)] valsInitVTOPP
  return ()

{- copying this function from MnistFcnnRanked1 here and calling the copy
   eliminates the segfault:
afcnnMnistTest1
  :: forall target widthHidden widthHidden2 r.
     (target ~ RepN, GoodScalar r, Differentiable r)
  => SNat widthHidden -> SNat widthHidden2
  -> [MnistDataLinearR r]
  -> MnistFcnnRanked1.ADFcnnMnist1Parameters target widthHidden widthHidden2 r
  -> r
afcnnMnistTest1 _ _ [] _ = 0
afcnnMnistTest1 widthHidden widthHidden2 dataList testParams =
  let matchesLabels :: MnistDataLinearR r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = rconcrete glyph
            nn :: MnistFcnnRanked1.ADFcnnMnist1Parameters target widthHidden widthHidden2 r
               -> target (TKR 1 r)
            nn = MnistFcnnRanked1.afcnnMnist1 logisticS softMax1S
                             widthHidden widthHidden2 (sfromR glyph1)
            v = Nested.rtoVector $ unRepN $ nn testParams
        in V.maxIndex v == V.maxIndex (Nested.rtoVector label)
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
-}
