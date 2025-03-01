{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Parsing and pre-processing MNIST data.
module MnistData where

import Prelude

import Codec.Compression.GZip (decompress)
import Data.ByteString.Lazy qualified as LBS
import Data.IDX
import Data.List (sortBy)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.Vector.Generic qualified as V
import Data.Vector.Storable (Vector)
import Data.Vector.Storable qualified as VS
import Data.Vector.Unboxed qualified
import GHC.TypeLits (KnownNat, Nat, type (*))
import System.IO (IOMode (ReadMode), withBinaryFile)
import System.Random

import Data.Array.Nested (KnownShS (..), ShR (..), pattern (:$:), pattern ZSR)
import Data.Array.Nested qualified as Nested

import HordeAd

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

type MnistDataLinearR r =
  ( Nested.Ranked 1 r
  , Nested.Ranked 1 r )

type MnistDataR r =
  ( Nested.Ranked 2 r
  , Nested.Ranked 1 r )

type MnistDataBatchR r =
  ( Nested.Ranked 3 r  -- [batch_size, SizeMnistHeight, SizeMnistWidth]
  , Nested.Ranked 2 r )  -- [batch_size, SizeMnistLabel]

type MnistDataS r =
  ( Nested.Shaped '[SizeMnistHeight, SizeMnistWidth] r
  , Nested.Shaped '[SizeMnistLabel] r )

type MnistDataBatchS batch_size r =
  ( Nested.Shaped '[batch_size, SizeMnistHeight, SizeMnistWidth] r
  , Nested.Shaped '[batch_size, SizeMnistLabel] r )

mkMnistDataLinearR :: Nested.PrimElt r
                   => MnistData r -> MnistDataLinearR r
mkMnistDataLinearR (input, target) =
  ( Nested.rfromVector
      (sizeMnistGlyphInt :$: ZSR) input
  , Nested.rfromVector
      (sizeMnistLabelInt :$: ZSR) target )

mkMnistDataR :: Nested.PrimElt r
             => MnistData r -> MnistDataR r
mkMnistDataR (input, target) =
  ( Nested.rfromVector
      (sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR) input
  , Nested.rfromVector
      (sizeMnistLabelInt :$: ZSR) target )

mkMnistDataBatchR :: Nested.Elt r
                  => [MnistDataR r] -> MnistDataBatchR r
mkMnistDataBatchR l =
  let (inputs, targets) = unzip l
  in ( Nested.rfromListOuter $ NonEmpty.fromList inputs
     , Nested.rfromListOuter $ NonEmpty.fromList targets )

mkMnistDataS :: Nested.PrimElt r
             => MnistData r -> MnistDataS r
mkMnistDataS (input, target) =
  (Nested.sfromVector knownShS input, Nested.sfromVector knownShS target)
{-# SPECIALIZE mkMnistDataS :: MnistData Double -> MnistDataS Double #-}
{-# SPECIALIZE mkMnistDataS :: MnistData Float -> MnistDataS Float #-}

mkMnistDataBatchS :: forall batch_size r. (Nested.Elt r, KnownNat batch_size)
                  => [MnistDataS r] -> MnistDataBatchS batch_size r
mkMnistDataBatchS l =
  let (inputs, targets) = unzip l
  in ( Nested.sfromListOuter (SNat @batch_size)
       $ NonEmpty.fromList inputs
     , Nested.sfromListOuter (SNat @batch_size)
       $ NonEmpty.fromList targets )
{-# SPECIALIZE mkMnistDataBatchS :: forall batch_size. KnownNat batch_size => [MnistDataS Double] -> MnistDataBatchS batch_size Double #-}
{-# SPECIALIZE mkMnistDataBatchS :: forall batch_size. KnownNat batch_size => [MnistDataS Float] -> MnistDataBatchS batch_size Float #-}

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
        let !vGlyph = V.map (\r -> fromIntegral r / 255) $ V.convert v
            !vLabel = V.generate sizeMnistLabelInt
                                 (\i -> if i == labN then 1 else 0)
        in (vGlyph, vLabel)
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
shuffle :: StdGen -> [a] -> [a]
shuffle g l =
  let rnds = randoms g :: [Int]
      res = map fst $ sortBy (comparing snd) $ zip l rnds
  in foldr seq () res `seq` res

chunksOf :: Int -> [e] -> [[e]]
chunksOf n = go where
  go [] = []
  go l = let (chunk, rest) = splitAt n l
         in chunk : go rest

{-
{-# SPECIALIZE sgd
  :: KnownNat n
  => Double
  -> (MnistData Double
      -> HVector (ADVal RepN)
      -> ADVal RepN (TKR n Double))
  -> [MnistData Double]
  -> HVector RepN
  -> (HVector RepN, RepN (TKR n Double)) #-}
-}

{- TODO: RULE left-hand side too complicated to desugar

{-# SPECIALIZE sgdAdam
  :: KnownNat y
  => (MnistDataBatchR Double -> HVector (ADVal Nested.Ranked)
      -> ADVal Nested.Ranked Double y)
  -> [MnistDataBatchR Double]
  -> HVector Nested.Ranked
  -> StateAdam
  -> (HVector Nested.Ranked, StateAdam) #-}

-}
