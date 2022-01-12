{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             RankNTypes #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistTools where

import Prelude

import           Codec.Compression.GZip (decompress)
import           Control.Exception (assert)
import qualified Data.ByteString.Lazy as LBS
import           Data.IDX
import           Data.Maybe (fromMaybe)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           GHC.Exts (inline)
import           System.IO (IOMode (ReadMode), withBinaryFile)

import AD

type DualDeltaD = DualDelta Double

type VecDualDeltaD = VecDualDelta Double

sizeMnistGlyph :: Int
sizeMnistGlyph = 784

sizeMnistLabel :: Int
sizeMnistLabel = 10

lenMnist :: Int -> Int
lenMnist widthHidden =
  widthHidden * (sizeMnistGlyph + 1) + 10 * (widthHidden + 1)

type MnistData = ( Data.Vector.Unboxed.Vector Double
                 , Data.Vector.Unboxed.Vector Double )

hiddenLayerMnist :: forall m. DeltaMonad Double m
                 => (DualDeltaD -> m DualDeltaD)
                 -> Domain Double
                 -> VecDualDeltaD
                 -> Int
                 -> m (Data.Vector.Vector DualDeltaD)
hiddenLayerMnist factivation xs vec width = do
  let nWeightsAndBias = V.length xs + 1
      f :: Int -> m DualDeltaD
      f i = do
        outSum <- sumConstantData xs (i * nWeightsAndBias) vec
        factivation outSum
  V.generateM width f

outputLayerMnist :: forall m. DeltaMonad Double m
                 => (Data.Vector.Vector DualDeltaD
                     -> m (Data.Vector.Vector DualDeltaD))
                 -> Data.Vector.Vector DualDeltaD
                 -> Int
                 -> VecDualDeltaD
                 -> Int
                 -> m (Data.Vector.Vector DualDeltaD)
outputLayerMnist factivation hiddenVec offset vec width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m DualDeltaD
      f i = sumTrainableInputs hiddenVec (offset + i * nWeightsAndBias) vec
  vOfSums <- V.generateM width f
  factivation vOfSums

-- @inline@ used to fix performance loss due to calling unknown functions.
-- Benchmarks show barely any improvement, probably due to the activation
-- functions being called only @width@ times per gradient calculation
-- and also the cost dominated by GC. So, it's safe to revert this optimization.
nnMnist :: DeltaMonad Double m
        => (DualDeltaD -> m DualDeltaD)
        -> (Data.Vector.Vector DualDeltaD
            -> m (Data.Vector.Vector DualDeltaD))
        -> Int
        -> Domain Double
        -> VecDualDeltaD
        -> m (Data.Vector.Vector DualDeltaD)
nnMnist factivationHidden factivationOutput widthHidden xs vec = do
  let !_A = assert (sizeMnistGlyph == V.length xs) ()
  hiddenVec <- inline hiddenLayerMnist factivationHidden xs vec widthHidden
  inline outputLayerMnist factivationOutput hiddenVec
                          (widthHidden * (sizeMnistGlyph + 1))
                          vec sizeMnistLabel

nnMnistLoss :: DeltaMonad Double m
            => Int
            -> MnistData
            -> VecDualDeltaD
            -> m DualDeltaD
nnMnistLoss widthHidden (xs, targ) vec = do
  res <- inline nnMnist logisticAct softMaxActUnfused widthHidden xs vec
  lossCrossEntropyUnfused targ res

testMnist :: [MnistData] -> Domain Double -> Int -> Double
testMnist xs res widthHidden =
  let f = inline nnMnist logisticAct softMaxActUnfused widthHidden
      matchesLabels :: MnistData -> Bool
      matchesLabels (glyphs, labels) =
        let value = V.map (\(D r _) -> r) $ valueDual (f glyphs) res
        in V.maxIndex value == V.maxIndex labels
  in fromIntegral (length (filter matchesLabels xs)) / fromIntegral (length xs)

readMnistData :: LBS.ByteString -> LBS.ByteString -> [MnistData]
readMnistData glyphsBS labelsBS =
  let glyphs = fromMaybe (error "wrong MNIST glyphs file")
               $ decodeIDX glyphsBS
      labels = fromMaybe (error "wrong MNIST labels file")
               $ decodeIDXLabels labelsBS
      intData = fromMaybe (error "can't decode MNIST file into integers")
                $ labeledIntData labels glyphs
      f :: (Int, Data.Vector.Unboxed.Vector Int) -> MnistData
      -- Copied from library backprop to enable comparison of results.
      -- I have no idea how this is different from @labeledDoubleData@, etc.
      f (labN, v) =
        ( V.map (\r -> fromIntegral r / 255) v
        , V.generate sizeMnistLabel (\i -> if i == labN then 1 else 0) )
  in map f intData

trainGlyphsPath, trainLabelsPath, testGlyphsPath, testLabelsPath :: FilePath
trainGlyphsPath = "samplesData/train-images-idx3-ubyte.gz"
trainLabelsPath = "samplesData/train-labels-idx1-ubyte.gz"
testGlyphsPath  = "samplesData/t10k-images-idx3-ubyte.gz"
testLabelsPath  = "samplesData/t10k-labels-idx1-ubyte.gz"

loadMnistData :: FilePath -> FilePath -> IO [MnistData]
loadMnistData glyphsPath labelsPath =
  withBinaryFile glyphsPath ReadMode $ \glyphsHandle ->
    withBinaryFile labelsPath ReadMode $ \labelsHandle -> do
      glyphsContents <- LBS.hGetContents glyphsHandle
      labelsContents <- LBS.hGetContents labelsHandle
      return $! readMnistData (decompress glyphsContents)
                              (decompress labelsContents)
