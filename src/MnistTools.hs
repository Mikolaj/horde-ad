{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             RankNTypes #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistTools where

import Prelude

import           Codec.Compression.GZip (decompress)
import           Control.Exception (assert)
import qualified Data.ByteString.Lazy as LBS
import           Data.IDX
import           Data.List (sortOn)
import           Data.Maybe (fromMaybe)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           GHC.Exts (inline)
import           System.IO (IOMode (ReadMode), withBinaryFile)
import           System.Random

import AD

-- * General tools

type DualDeltaD = DualDelta Double

type VecDualDeltaD = VecDualDelta Double

sizeMnistGlyph :: Int
sizeMnistGlyph = 784

sizeMnistLabel :: Int
sizeMnistLabel = 10

-- Actually, a better representation, supported by @Data.IDX@,
-- is an integer label and a picture (the same vector as below).
-- Then we'd use @lossCrossEntropy@ that picks a component according
-- to the label instead of performing a dot product with scaling.
-- This results in much smaller Delta expressions.
-- Our library makes this easy to express and gradients compute fine.
-- OTOH, methods with only matrix operations and graphs can't handle that.
-- However, the goal of the exercise it too implement the same
-- neural net that backprop uses for benchmarks and compare.
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

middleLayerMnist :: forall m. DeltaMonad Double m
                 => (DualDeltaD -> m DualDeltaD)
                 -> Data.Vector.Vector DualDeltaD
                 -> Int
                 -> VecDualDeltaD
                 -> Int
                 -> m (Data.Vector.Vector DualDeltaD)
middleLayerMnist factivation hiddenVec offset vec width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m DualDeltaD
      f i = do
        outSum <- sumTrainableInputs hiddenVec
                                     (offset + i * nWeightsAndBias)
                                     vec
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

-- * 1 hidden layer

lenMnist :: Int -> Int
lenMnist widthHidden =
  widthHidden * (sizeMnistGlyph + 1) + sizeMnistLabel * (widthHidden + 1)

-- One hidden layer of width @widthHidden@.
--
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
nnMnistLoss widthHidden (x, targ) vec = do
  res <- inline nnMnist logisticAct softMaxAct widthHidden x vec
  lossCrossEntropy targ res

generalTestMnist :: (Domain Double
                     -> VecDualDeltaD
                     -> DeltaMonadValue Double (Data.Vector.Vector DualDeltaD))
                 -> [MnistData] -> Domain Double
                 -> Double
{-# INLINE generalTestMnist #-}
generalTestMnist nn xs res =
  let matchesLabels :: MnistData -> Bool
      matchesLabels (glyph, label) =
        let value = V.map (\(D r _) -> r) $ valueDual (nn glyph) res
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels xs)) / fromIntegral (length xs)

testMnist :: Int -> [MnistData] -> Domain Double -> Double
testMnist widthHidden xs res =
  generalTestMnist (inline nnMnist logisticAct softMaxAct widthHidden) xs res

-- * 2 hidden layers

lenMnist2 :: Int -> Int -> Int
lenMnist2 widthHidden widthHidden2 =
  widthHidden * (sizeMnistGlyph + 1)
  + widthHidden2 * (widthHidden + 1)
  + sizeMnistLabel * (widthHidden + 1)

-- Two hidden layers of width @widthHidden@ and (the middle one) @widthHidden2@.
-- Both hidden layers use the same activation function.
nnMnist2 :: DeltaMonad Double m
         => (DualDeltaD -> m DualDeltaD)
         -> (Data.Vector.Vector DualDeltaD
             -> m (Data.Vector.Vector DualDeltaD))
         -> Int
         -> Int
         -> Domain Double
         -> VecDualDeltaD
         -> m (Data.Vector.Vector DualDeltaD)
nnMnist2 factivationHidden factivationOutput widthHidden widthHidden2
         xs vec = do
  let !_A = assert (sizeMnistGlyph == V.length xs) ()
  hiddenVec <- inline hiddenLayerMnist factivationHidden xs vec widthHidden
  let offsetMiddle = widthHidden * (sizeMnistGlyph + 1)
  middleVec <- inline middleLayerMnist factivationHidden hiddenVec
                                       offsetMiddle vec widthHidden2
  let offsetOutput = offsetMiddle + widthHidden2 * (widthHidden + 1)
  inline outputLayerMnist factivationOutput middleVec
                          offsetOutput vec sizeMnistLabel

nnMnistLoss2 :: DeltaMonad Double m
             => Int
             -> Int
             -> MnistData
             -> VecDualDeltaD
             -> m DualDeltaD
nnMnistLoss2 widthHidden widthHidden2 (x, targ) vec = do
  res <- inline nnMnist2 logisticAct softMaxAct widthHidden widthHidden2 x vec
  lossCrossEntropy targ res

testMnist2 :: Int -> Int -> [MnistData] -> Domain Double -> Double
testMnist2 widthHidden widthHidden2 xs res =
  generalTestMnist (inline nnMnist2 logisticAct softMaxAct
                                    widthHidden widthHidden2)
                   xs res

-- * Reading data files

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

-- Good enough for QuickCheck, so good enough for me.
shuffle :: RandomGen g => g -> [a] -> [a]
shuffle g l =
  let rnds = randoms g :: [Int]
  in map fst $ sortOn snd $ zip l rnds
