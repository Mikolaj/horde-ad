{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes, TypeFamilies,
             TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestSpeechRNN (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Exception (assert)
import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.ShapedS as OS
import qualified Data.ByteString.Lazy as LBS
import           Data.List (foldl', unfoldr)
import           Data.Proxy (Proxy (Proxy))
import           Data.Serialize
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.IO
  (IOMode (ReadMode), hPutStrLn, stderr, withBinaryFile)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

-- until stylish-haskell accepts NoStarIsType
import qualified GHC.TypeLits

import HordeAd

testTrees :: [TestTree]
testTrees = [ mnistRNNTestsLong
            , speechRNNTestsShort
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ speechRNNTestsShort
                      ]


type SpeechDataBatch batch_size window_size n_labels r =
  ( OS.Array '[batch_size, window_size] r
  , OS.Array '[batch_size, n_labels] r )

chunksOf :: Int -> [e] -> [[e]]
chunksOf n = go where
  go [] = []
  go l = let (chunk, rest) = splitAt n l
         in chunk : go rest

-- The last chunk is thrown away if smaller than batch size.
-- It crashes if the size of either file doesn't match the other.
-- TODO: perhaps then warn instead of failing an assertion.
-- TODO: perhaps warn about the last chunk, too.
-- TODO: this could be so much more elegant, e.g., if OS.fromList
-- returned the remaining list and so no manual size calculations would
-- be required.
-- TODO: performance, see https://github.com/schrammc/mnist-idx/blob/master/src/Data/IDX/Internal.hs
decodeSpeechData
  :: forall batch_size window_size n_labels r.
     ( Serialize r, Numeric r
     , KnownNat batch_size, KnownNat window_size, KnownNat n_labels )
  => LBS.ByteString -> LBS.ByteString
  -> [SpeechDataBatch batch_size window_size n_labels r]
decodeSpeechData soundsBs labelsBs =
  let soundsChunkSize = valueOf @batch_size * valueOf @window_size
      labelsChunkSize = valueOf @batch_size * valueOf @n_labels
      !_A1 = assert
               (fromIntegral (LBS.length soundsBs - 8) * labelsChunkSize
                == fromIntegral (LBS.length labelsBs - 8) * soundsChunkSize) ()
      cutBs :: Int -> LBS.ByteString -> [[r]]
      cutBs chunkSize bs =
        let list :: [r] = case decodeLazy bs of
              Left err -> error err
              Right l -> l
        in filter (\ch -> length ch >= chunkSize)
           $ chunksOf chunkSize list
      soundsChunks :: [[r]] = cutBs soundsChunkSize soundsBs
      labelsChunks :: [[r]] = cutBs labelsChunkSize labelsBs
      !_A2 = assert (length soundsChunks > 0) ()
      !_A3 = assert (length soundsChunks == length labelsChunks) ()
      makeSpeechDataBatch
        :: [r] -> [r] -> SpeechDataBatch batch_size window_size n_labels r
      makeSpeechDataBatch soundsCh labelsCh =
        (OS.fromList soundsCh, OS.fromList labelsCh)
  in zipWith makeSpeechDataBatch soundsChunks labelsChunks

loadSpeechData
  :: forall batch_size window_size n_labels r.
     ( Serialize r, Numeric r
     , KnownNat batch_size, KnownNat window_size, KnownNat n_labels )
  => FilePath -> FilePath
  -> IO [SpeechDataBatch batch_size window_size n_labels r]
loadSpeechData soundsPath labelsPath =
  withBinaryFile soundsPath ReadMode $ \soundsHandle ->
    withBinaryFile labelsPath ReadMode $ \labelsHandle -> do
      soundsContents <- LBS.hGetContents soundsHandle
      labelsContents <- LBS.hGetContents labelsHandle
      let !_A1 = assert (LBS.length soundsContents > 0) ()
      return $! decodeSpeechData soundsContents labelsContents

speechTestCaseRNN
  :: forall out_width batch_size window_size n_labels d r m.
     ( KnownNat out_width, KnownNat batch_size, KnownNat window_size
     , KnownNat n_labels
     , r ~ Double, d ~ 'DModeGradient, m ~ DualMonadGradient Double )
  => String
  -> Int
  -> Int
  -> (forall out_width' batch_size' window_size' n_labels'.
      ( DualMonad d r m, KnownNat out_width', KnownNat batch_size'
      , KnownNat n_labels' )
      => Proxy out_width'
      -> SpeechDataBatch batch_size' window_size' n_labels' r
      -> DualNumberVariables d r
      -> m (DualNumber d r))
  -> (forall out_width' batch_size' window_size' n_labels'.
      ( IsScalar d r, KnownNat out_width', KnownNat batch_size'
      , KnownNat n_labels' )
      => Proxy out_width'
      -> SpeechDataBatch batch_size' window_size' n_labels' r
      -> Domains r
      -> r)
  -> (forall out_width'. KnownNat out_width'
      => Proxy out_width' -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Double
  -> TestTree
speechTestCaseRNN prefix epochs maxBatches trainWithLoss ftest flen expected =
  testCase prefix $
    1.0 @?= 1.0

mnistRNNTestsLong :: TestTree
mnistRNNTestsLong = testGroup "Speech RNN long tests"
  []

speechRNNTestsShort :: TestTree
speechRNNTestsShort = testGroup "Speech RNN short tests"
  [ testCase "Load and sanity check speech" $ do
      speechDataBatchList <-
        loadSpeechData
          @64 @257 @1 @Float
          "/home/mikolaj/Downloads/volleyball.float32.257.spectrogram.bin"
          "/home/mikolaj/Downloads/volleyball.float32.1.rms.bin"
      length speechDataBatchList @?= 859 `div` 64
  ]
