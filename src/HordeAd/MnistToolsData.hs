{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Parsing and pre-processing MNIST data.
module HordeAd.MnistToolsData where

import Prelude

import           Codec.Compression.GZip (decompress)
import qualified Data.ByteString.Lazy as LBS
import           Data.IDX
import           Data.List (sortOn)
import           Data.Maybe (fromMaybe)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import qualified Data.Vector.Unboxed
import           System.IO (IOMode (ReadMode), withBinaryFile)
import           System.Random

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
-- However, the goal of the exercise it to implement the same
-- neural net that backprop uses for benchmarks and compare.
type MnistData r = ( Data.Vector.Storable.Vector r
                   , Data.Vector.Storable.Vector r )

readMnistData :: LBS.ByteString -> LBS.ByteString -> [MnistData Double]
readMnistData glyphsBS labelsBS =
  let glyphs = fromMaybe (error "wrong MNIST glyphs file")
               $ decodeIDX glyphsBS
      labels = fromMaybe (error "wrong MNIST labels file")
               $ decodeIDXLabels labelsBS
      intData = fromMaybe (error "can't decode MNIST file into integers")
                $ labeledIntData labels glyphs
      f :: (Int, Data.Vector.Unboxed.Vector Int) -> MnistData Double
      -- Copied from library backprop to enable comparison of results.
      -- I have no idea how this is different from @labeledDoubleData@, etc.
      f (labN, v) =
        ( V.map (\r -> fromIntegral r / 255) $ V.convert v
        , V.generate sizeMnistLabel (\i -> if i == labN then 1 else 0) )
  in map f intData

trainGlyphsPath, trainLabelsPath, testGlyphsPath, testLabelsPath :: FilePath
trainGlyphsPath = "samplesData/train-images-idx3-ubyte.gz"
trainLabelsPath = "samplesData/train-labels-idx1-ubyte.gz"
testGlyphsPath  = "samplesData/t10k-images-idx3-ubyte.gz"
testLabelsPath  = "samplesData/t10k-labels-idx1-ubyte.gz"

loadMnistData :: FilePath -> FilePath -> IO [MnistData Double]
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

chunksOf :: Int -> [e] -> [[e]]
chunksOf n = go where
  go [] = []
  go l = let (chunk, rest) = splitAt n l
         in chunk : go rest
