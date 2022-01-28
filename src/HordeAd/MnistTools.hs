{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Specialized tools for processing MNIST data and building fully connected
-- neural networks that can classify MNIST digits.
module HordeAd.MnistTools where

import Prelude

import           Codec.Compression.GZip (decompress)
import           Control.Exception (assert)
import qualified Data.ByteString.Lazy as LBS
import           Data.IDX
import           Data.List (sortOn)
import           Data.Maybe (fromMaybe)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import qualified Data.Vector.Unboxed
import           Foreign.Storable (Storable)
import           GHC.Exts (inline)
import           System.IO (IOMode (ReadMode), withBinaryFile)
import           System.Random

import HordeAd.DualDelta
import HordeAd.Engine
import HordeAd.PairOfVectors (VecDualDelta, var)

-- * General tools

-- | Compute the output of a neuron, without applying activation function,
-- from trainable inputs in @xs@ and parameters (the bias and weights)
-- at @vec@ starting at @offset@. Useful for neurons in the middle
-- of the network, receiving inputs from other neurons.
--
-- Note that functions like that, with Delta in the type signature
-- (which is really indispensable due to accessing variable parameters
-- in a special way) make it impossible to implement the function
-- to be differentiated as fully polymorphic @:: Num r => [r] -> m r@
-- function and so have no overhead when computing the value
-- with a dummy monad. Another case is selectively fused operations,
-- unless we include all of them, even very ad hoc ones,
-- in a class with implementations both on @D@ and on plain @r@.
sumTrainableInputs :: forall m r.
                        (DeltaMonad r m, Num r, Storable r)
                   => Data.Vector.Vector (DualDelta r)
                   -> Int
                   -> VecDualDelta r
                   -> m (DualDelta r)
sumTrainableInputs xs offset vec = do
  let bias = var vec offset
      f :: DualDelta r -> Int -> DualDelta r -> DualDelta r
      f !acc i u =
        let v = var vec (offset + 1 + i)
        in acc + u * v
  returnLet $ V.ifoldl' f bias xs

-- | Compute the output of a neuron, without applying activation function,
-- from constant data in @xs@ and parameters (the bias and weights)
-- at @vec@ starting at @offset@. Useful for neurons at the bottom
-- of the network, tasked with ingesting the data.
sumConstantData :: forall m r.
                     (DeltaMonad r m, Num r, Storable r)
                => Domain r
                -> Int
                -> VecDualDelta r
                -> m (DualDelta r)
sumConstantData xs offset vec = do
  let bias = var vec offset
      f :: DualDelta r -> Int -> r -> DualDelta r
      f !acc i r =
        let v = var vec (offset + 1 + i)
        in acc + scale r v
  returnLet $ V.ifoldl' f bias xs

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

hiddenLayerMnist :: forall m r.
                      (DeltaMonad r m, Num r, Storable r)
                 => (DualDelta r -> m (DualDelta r))
                 -> Data.Vector.Storable.Vector r
                 -> VecDualDelta r
                 -> Int
                 -> m (Data.Vector.Vector (DualDelta r))
hiddenLayerMnist factivation x vec width = do
  let nWeightsAndBias = V.length x + 1
      f :: Int -> m (DualDelta r)
      f i = do
        outSum <- sumConstantData x (i * nWeightsAndBias) vec
        factivation outSum
  V.generateM width f

middleLayerMnist :: forall m r.
                      (DeltaMonad r m, Num r, Storable r)
                 => (DualDelta r -> m (DualDelta r))
                 -> Data.Vector.Vector (DualDelta r)
                 -> Int
                 -> VecDualDelta r
                 -> Int
                 -> m (Data.Vector.Vector (DualDelta r))
middleLayerMnist factivation hiddenVec offset vec width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m (DualDelta r)
      f i = do
        outSum <- sumTrainableInputs hiddenVec
                                     (offset + i * nWeightsAndBias)
                                     vec
        factivation outSum
  V.generateM width f

outputLayerMnist :: forall m r.
                      (DeltaMonad r m, Num r, Storable r)
                 => (Data.Vector.Vector (DualDelta r)
                     -> m (Data.Vector.Vector (DualDelta r)))
                 -> Data.Vector.Vector (DualDelta r)
                 -> Int
                 -> VecDualDelta r
                 -> Int
                 -> m (Data.Vector.Vector (DualDelta r))
outputLayerMnist factivation hiddenVec offset vec width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m (DualDelta r)
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
nnMnist :: (DeltaMonad r m, Floating r, Storable r)
        => (DualDelta r -> m (DualDelta r))
        -> (Data.Vector.Vector (DualDelta r)
            -> m (Data.Vector.Vector (DualDelta r)))
        -> Int
        -> Data.Vector.Storable.Vector r
        -> VecDualDelta r
        -> m (Data.Vector.Vector (DualDelta r))
nnMnist factivationHidden factivationOutput widthHidden x vec = do
  let !_A = assert (sizeMnistGlyph == V.length x) ()
  hiddenVec <- inline hiddenLayerMnist factivationHidden x vec widthHidden
  inline outputLayerMnist factivationOutput hiddenVec
                          (widthHidden * (sizeMnistGlyph + 1))
                          vec sizeMnistLabel

nnMnistLoss :: (DeltaMonad r m, Floating r, Storable r)
            => Int
            -> MnistData r
            -> VecDualDelta r
            -> m (DualDelta r)
nnMnistLoss widthHidden (x, targ) vec = do
  res <- inline nnMnist logisticAct softMaxAct widthHidden x vec
  lossCrossEntropy targ res

generalTestMnist :: forall r. (Ord r, Fractional r, Storable r)
                 => (Domain r
                     -> VecDualDelta r
                     -> DeltaMonadValue r
                          (Data.Vector.Vector (DualDelta r)))
                 -> [MnistData r] -> Domain r
                 -> r
{-# INLINE generalTestMnist #-}
generalTestMnist nn xs res =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let value = V.map (\(D r _) -> r)
                    $ valueDual (nn glyph) (res, undefined)
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels xs)) / fromIntegral (length xs)

testMnist :: (Ord r, Floating r, Storable r)
          => Int -> [MnistData r] -> Domain r -> r
testMnist widthHidden xs res =
  generalTestMnist (inline nnMnist logisticAct softMaxAct widthHidden) xs res

-- * 2 hidden layers

lenMnist2 :: Int -> Int -> Int
lenMnist2 widthHidden widthHidden2 =
  widthHidden * (sizeMnistGlyph + 1)
  + widthHidden2 * (widthHidden + 1)
  + sizeMnistLabel * (widthHidden2 + 1)

-- Two hidden layers of width @widthHidden@ and (the middle one) @widthHidden2@.
-- Both hidden layers use the same activation function.
nnMnist2 :: (DeltaMonad r m, Fractional r, Storable r)
         => (DualDelta r -> m (DualDelta r))
         -> (Data.Vector.Vector (DualDelta r)
             -> m (Data.Vector.Vector (DualDelta r)))
         -> Int
         -> Int
         -> Data.Vector.Storable.Vector r
         -> VecDualDelta r
         -> m (Data.Vector.Vector (DualDelta r))
nnMnist2 factivationHidden factivationOutput widthHidden widthHidden2
         x vec = do
  let !_A = assert (sizeMnistGlyph == V.length x) ()
  hiddenVec <- inline hiddenLayerMnist factivationHidden x vec widthHidden
  let offsetMiddle = widthHidden * (sizeMnistGlyph + 1)
  middleVec <- inline middleLayerMnist factivationHidden hiddenVec
                                       offsetMiddle vec widthHidden2
  let offsetOutput = offsetMiddle + widthHidden2 * (widthHidden + 1)
  inline outputLayerMnist factivationOutput middleVec
                          offsetOutput vec sizeMnistLabel

nnMnistLoss2 :: (DeltaMonad r m, Floating r, Storable r)
             => Int
             -> Int
             -> MnistData r
             -> VecDualDelta r
             -> m (DualDelta r)
nnMnistLoss2 widthHidden widthHidden2 (x, targ) vec = do
  res <- inline nnMnist2 logisticAct softMaxAct widthHidden widthHidden2 x vec
  lossCrossEntropy targ res

testMnist2 :: (Ord r, Floating r, Storable r)
           => Int -> Int -> [MnistData r] -> Domain r -> r
testMnist2 widthHidden widthHidden2 xs res =
  generalTestMnist (inline nnMnist2 logisticAct softMaxAct
                                    widthHidden widthHidden2)
                   xs res

-- * Reading data files

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
