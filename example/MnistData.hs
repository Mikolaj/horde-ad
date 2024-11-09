{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Parsing and pre-processing MNIST data.
module MnistData where

import Prelude

import Codec.Compression.GZip (decompress)
import Data.Array.Internal (valueOf)
import Data.Array.Ranked qualified as ORB
import Data.Array.RankedS qualified as OR
import Data.Array.Shaped qualified as OSB
import Data.Array.ShapedS qualified as OS
import Data.ByteString.Lazy qualified as LBS
import Data.IDX
import Data.List (sortOn)
import Data.Maybe (fromMaybe)
import Data.Vector.Generic qualified as V
import Data.Vector.Storable (Vector)
import Data.Vector.Storable qualified as VS
import Data.Vector.Unboxed qualified
import GHC.TypeLits (KnownNat, Nat, type (*))
import System.IO (IOMode (ReadMode), withBinaryFile)
import System.Random

import HordeAd
import HordeAd.Internal.BackendOX (RepN)

type SizeMnistWidth = 28 :: Nat

sizeMnistWidth :: SNat SizeMnistWidth
sizeMnistWidth = SNat @SizeMnistWidth

sizeMnistWidthInt :: Int
sizeMnistWidthInt = sNatValue sizeMnistWidth

type SizeMnistHeight = SizeMnistWidth

sizeMnistHeight :: SNat SizeMnistHeight
sizeMnistHeight = SNat @SizeMnistHeight

sizeMnistHeightInt :: Int
sizeMnistHeightInt = valueOf @SizeMnistHeight

type SizeMnistGlyph = SizeMnistWidth * SizeMnistHeight

sizeMnistGlyphInt :: Int
sizeMnistGlyphInt = valueOf @SizeMnistGlyph

type SizeMnistLabel = 10 :: Nat

sizeMnistLabel :: SNat SizeMnistLabel
sizeMnistLabel = SNat @SizeMnistLabel

sizeMnistLabelInt :: Int
sizeMnistLabelInt = sNatValue sizeMnistLabel

type LengthTestData = 10000 :: Nat

-- Actually, a better representation, supported by @Data.IDX@,
-- is an integer label and a picture (the same vector as below).
-- Then we'd use @lossCrossEntropy@ that picks a component according
-- to the label instead of performing a dot product with scaling.
-- This results in much smaller Delta expressions.
-- Our library makes this easy to express and gradients compute fine.
-- OTOH, methods with only matrix operations and graphs can't handle that.
-- However, the goal of the exercise it to implement the same
-- neural net that backprop uses for comparative benchmarks.
-- Also, loss computation is not the bottleneck and the more general
-- mechanism that admits non-discrete target labels fuses nicely
-- with softMax. This also seems to be the standard or at least
-- a simple default in tutorial.
type MnistData r = (Vector r, Vector r)

type MnistDataS r =
  ( OS.Array '[SizeMnistHeight, SizeMnistWidth] r
  , OS.Array '[SizeMnistLabel] r )

type MnistDataBatchS batch_size r =
  ( OS.Array '[batch_size, SizeMnistHeight, SizeMnistWidth] r
  , OS.Array '[batch_size, SizeMnistLabel] r )

type MnistDataR r =
  ( OR.Array 2 r
  , OR.Array 1 r )

type MnistDataBatchR r =
  ( OR.Array 3 r  -- [batch_size, SizeMnistHeight, SizeMnistWidth]
  , OR.Array 2 r )  -- [batch_size, SizeMnistLabel]

shapeBatch :: VS.Storable r => MnistData r -> MnistDataS r
shapeBatch (input, target) = (OS.fromVector input, OS.fromVector target)
{-# SPECIALIZE shapeBatch :: MnistData Double -> MnistDataS Double #-}
{-# SPECIALIZE shapeBatch :: MnistData Float -> MnistDataS Float #-}

packBatch :: forall batch_size r. (VS.Storable r, KnownNat batch_size)
          => [MnistDataS r] -> MnistDataBatchS batch_size r
packBatch l =
  let (inputs, targets) = unzip l
  in (OS.ravel $ OSB.fromList inputs, OS.ravel $ OSB.fromList targets)
{-# SPECIALIZE packBatch :: forall batch_size. KnownNat batch_size => [MnistDataS Double] -> MnistDataBatchS batch_size Double #-}
{-# SPECIALIZE packBatch :: forall batch_size. KnownNat batch_size => [MnistDataS Float] -> MnistDataBatchS batch_size Float #-}

rankBatch :: VS.Storable r => MnistData r -> MnistDataR r
rankBatch (input, target) =
  ( OR.fromVector [sizeMnistHeightInt, sizeMnistWidthInt] input
  , OR.fromVector [sizeMnistLabelInt] target )

packBatchR :: VS.Storable r
           => [MnistDataR r] -> MnistDataBatchR r
packBatchR l =
  let (inputs, targets) = unzip l
  in ( OR.ravel $ ORB.fromList [length inputs] inputs
     , OR.ravel $ ORB.fromList [length targets] targets )

readMnistData :: forall r. (VS.Storable r, Fractional r)
              => LBS.ByteString -> LBS.ByteString -> [MnistData r]
readMnistData glyphsBS labelsBS =
  let glyphs = fromMaybe (error "wrong MNIST glyphs file")
               $ decodeIDX glyphsBS
      labels = fromMaybe (error "wrong MNIST labels file")
               $ decodeIDXLabels labelsBS
      intData = fromMaybe (error "can't decode MNIST file into integers")
                $ labeledIntData labels glyphs
      f :: (Int, Data.Vector.Unboxed.Vector Int) -> MnistData r
      -- Copied from library backprop to enable comparison of results.
      -- I have no idea how this is different from @labeledDoubleData@, etc.
      f (labN, v) =
        ( V.map (\r -> fromIntegral r / 255) $ V.convert v
        , V.generate sizeMnistLabelInt (\i -> if i == labN then 1 else 0) )
  in map f intData
{-# SPECIALIZE readMnistData :: LBS.ByteString -> LBS.ByteString -> [MnistData Double] #-}
{-# SPECIALIZE readMnistData :: LBS.ByteString -> LBS.ByteString -> [MnistData Float] #-}

trainGlyphsPath, trainLabelsPath, testGlyphsPath, testLabelsPath :: FilePath
trainGlyphsPath = "samplesData/train-images-idx3-ubyte.gz"
trainLabelsPath = "samplesData/train-labels-idx1-ubyte.gz"
testGlyphsPath  = "samplesData/t10k-images-idx3-ubyte.gz"
testLabelsPath  = "samplesData/t10k-labels-idx1-ubyte.gz"

loadMnistData :: (VS.Storable r, Fractional r)
              => FilePath -> FilePath -> IO [MnistData r]
loadMnistData glyphsPath labelsPath =
  withBinaryFile glyphsPath ReadMode $ \glyphsHandle ->
    withBinaryFile labelsPath ReadMode $ \labelsHandle -> do
      glyphsContents <- LBS.hGetContents glyphsHandle
      labelsContents <- LBS.hGetContents labelsHandle
      return $! readMnistData (decompress glyphsContents)
                              (decompress labelsContents)
{-# SPECIALIZE loadMnistData :: FilePath -> FilePath -> IO [MnistData Double] #-}
{-# SPECIALIZE loadMnistData :: FilePath -> FilePath -> IO [MnistData Float] #-}

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


{-# SPECIALIZE sgd
  :: KnownNat n
  => Double
  -> (MnistData Double
      -> HVector (ADVal RepN)
      -> ADVal RepN (TKR Double n))
  -> [MnistData Double]
  -> HVector RepN
  -> (HVector RepN, RepN (TKR Double n)) #-}

{- TODO: RULE left-hand side too complicated to desugar

{-# SPECIALIZE sgdAdam
  :: KnownNat y
  => (MnistDataBatchR Double -> HVector (ADVal ORArray)
      -> ADVal ORArray Double y)
  -> [MnistDataBatchR Double]
  -> HVector ORArray
  -> StateAdam
  -> (HVector ORArray, StateAdam) #-}

-}
