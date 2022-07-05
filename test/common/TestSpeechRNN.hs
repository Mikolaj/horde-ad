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
import qualified Data.Array.Shape
import qualified Data.Array.Shaped as OSB
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
import HordeAd.Tool.MnistData (chunksOf, shuffle)
import HordeAd.Tool.MnistRnnShaped
  (LayerWeigthsRNN, rnnMnistLayerS, unrollLastS, zeroStateS)

import TestCommonEqEpsilon

testTrees :: [TestTree]
testTrees = [ mnistRNNTestsLong
            , speechRNNTestsShort
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ speechRNNTestsShort
                      ]


type SpeechDataBatch batch_size block_size window_size n_labels r =
  ( OS.Array '[batch_size, block_size, window_size] r
  , OS.Array '[batch_size, n_labels] r )

-- The last chunk is thrown away if smaller than batch size.
-- It crashes if the size of either file doesn't match the other.
-- TODO: perhaps then warn instead of failing an assertion.
-- TODO: perhaps warn about the last chunk, too.
-- TODO: this could be so much more elegant, e.g., if OS.fromList
-- returned the remaining list and so no manual size calculations would
-- be required.
-- TODO: performance, see https://github.com/schrammc/mnist-idx/blob/master/src/Data/IDX/Internal.hs
decodeSpeechData
  :: forall batch_size block_size window_size n_labels r.
     ( Serialize r, Numeric r, Fractional r
     , KnownNat batch_size, KnownNat block_size, KnownNat window_size
     , KnownNat n_labels )
  => LBS.ByteString -> LBS.ByteString
  -> [SpeechDataBatch batch_size block_size window_size n_labels r]
decodeSpeechData soundsBs labelsBs =
  let soundsChunkSize =
        valueOf @batch_size * valueOf @block_size * valueOf @window_size
      labelsChunkSize =
        valueOf @batch_size * valueOf @block_size * valueOf @n_labels
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
        :: [r] -> [r]
        -> SpeechDataBatch batch_size block_size window_size n_labels r
      makeSpeechDataBatch soundsCh labelsCh =
        let labelsBlockSize = valueOf @block_size * valueOf @n_labels
            labelsBlocks = chunksOf labelsBlockSize labelsCh
            -- Tmp hack that only makes sense for n_labels == 1.
            avgLabels ch = sum ch / fromIntegral (length ch)
            labelsAvg = map avgLabels labelsBlocks
        in (OS.fromList soundsCh, OS.fromList labelsAvg)
  in zipWith makeSpeechDataBatch soundsChunks labelsChunks

loadSpeechData
  :: forall batch_size block_size window_size n_labels r.
     ( Serialize r, Numeric r, Fractional r
     , KnownNat batch_size, KnownNat block_size, KnownNat window_size
     , KnownNat n_labels )
  => FilePath -> FilePath
  -> IO [SpeechDataBatch batch_size block_size window_size n_labels r]
loadSpeechData soundsPath labelsPath =
  withBinaryFile soundsPath ReadMode $ \soundsHandle ->
    withBinaryFile labelsPath ReadMode $ \labelsHandle -> do
      soundsContents <- LBS.hGetContents soundsHandle
      labelsContents <- LBS.hGetContents labelsHandle
      let !_A1 = assert (LBS.length soundsContents > 0) ()
      return $! decodeSpeechData soundsContents labelsContents


rnnSpeechTwo
  :: forall out_width batch_size window_size d r m.
     ( DualMonad d r m, KnownNat out_width, KnownNat batch_size
     , KnownNat window_size )
  => DualNumber d (OS.Array '[2 GHC.TypeLits.* out_width, batch_size] r)
       -- initial state
  -> OS.Array '[window_size, batch_size] r
  -> ( LayerWeigthsRNN window_size out_width d r
     , LayerWeigthsRNN out_width out_width d r )
  -> m ( DualNumber d (OS.Array '[out_width, batch_size] r)
       , DualNumber d (OS.Array '[2 GHC.TypeLits.* out_width, batch_size] r) )
           -- final state
rnnSpeechTwo s x ((wX, wS, b), (wX2, wS2, b2)) = do
  let s1 = sliceS @0 @out_width s
      s2 = sliceS @out_width @out_width s
  (vec1, s1') <- rnnMnistLayerS s1 (constant x) (wX, wS, b)
  (vec2, s2') <- rnnMnistLayerS s2 vec1 (wX2, wS2, b2)
  s3 <- returnLet $ appendS s1' s2'
  return (vec2, s3)

rnnSpeechZero
  :: forall out_width batch_size block_size window_size n_labels d r m.
     ( DualMonad d r m, KnownNat out_width, KnownNat batch_size
     , KnownNat block_size, KnownNat window_size, KnownNat n_labels )
  => OS.Array '[block_size, window_size, batch_size] r
  -- All below is the type of all parameters of this nn. The same is reflected
  -- in the length function below and read from variables further down.
  -> ( LayerWeigthsRNN window_size out_width d r
     , LayerWeigthsRNN out_width out_width d r )
  -> DualNumber d (OS.Array '[n_labels, out_width] r)
  -> DualNumber d (OS.Array '[n_labels] r)
  -> m (DualNumber d (OS.Array '[n_labels, batch_size] r))
rnnSpeechZero xs ((wX, wS, b), (wX2, wS2, b2)) w3 b3 = do
  (out, _s) <- zeroStateS (unrollLastS rnnSpeechTwo) xs
                          ((wX, wS, b), (wX2, wS2, b2))
  returnLet $ w3 <>$ out + asColumnS b3

rnnSpeechLen
  :: forall out_width window_size n_labels.
     (KnownNat out_width, KnownNat window_size, KnownNat n_labels)
  => Proxy out_width -> Proxy window_size -> Proxy n_labels
  -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
rnnSpeechLen _ _ _ =
  ( 0
  , []
  , []
  , [ Data.Array.Shape.shapeT @'[out_width, window_size]
    , Data.Array.Shape.shapeT @'[out_width, out_width]
    , Data.Array.Shape.shapeT @'[out_width]
    , Data.Array.Shape.shapeT @'[out_width, out_width]
    , Data.Array.Shape.shapeT @'[out_width, out_width]
    , Data.Array.Shape.shapeT @'[out_width]
    , Data.Array.Shape.shapeT @'[n_labels, out_width]
    , Data.Array.Shape.shapeT @'[n_labels]
    ]
  )

rnnSpeech
  :: forall out_width batch_size block_size window_size n_labels d r m.
     ( DualMonad d r m, KnownNat out_width, KnownNat batch_size
     , KnownNat block_size, KnownNat window_size, KnownNat n_labels )
  => OS.Array '[window_size, block_size, batch_size] r
  -> DualNumberVariables d r
  -> m (DualNumber d (OS.Array '[n_labels, batch_size] r))
rnnSpeech xs variables = do
  let wX = varS variables 0
      wS = varS variables 1
      b = varS variables 2
      wX2 = varS variables 3
      wS2 = varS variables 4
      b2 = varS variables 5
      w3 = varS variables 6
      b3 = varS variables 7
  rnnSpeechZero @out_width xs ((wX, wS, b), (wX2, wS2, b2)) w3 b3

rnnSpeechLossFused
  :: forall out_width batch_size block_size window_size n_labels d r m.
     ( DualMonad d r m, KnownNat out_width, KnownNat batch_size
     , KnownNat block_size, KnownNat window_size, KnownNat n_labels )
  => Proxy out_width
  -> SpeechDataBatch batch_size block_size window_size n_labels r
  -> DualNumberVariables d r
  -> m (DualNumber d r)
rnnSpeechLossFused _ (sounds, labels) variables = do
  let xs = OS.transpose @'[2, 1, 0] sounds
  result <- rnnSpeech @out_width @batch_size @block_size @window_size @n_labels
                      xs variables
  let targets2 = HM.tr $ HM.reshape (valueOf @n_labels)
                       $ OS.toVector labels
  vec <- lossSoftMaxCrossEntropyL targets2 (fromS2 result)
  returnLet $ scale (recip $ fromIntegral (valueOf @batch_size :: Int))
            $ sumElements0 vec

rnnSpeechTest
  :: forall out_width batch_size block_size window_size n_labels d r m.
     ( IsScalar 'DModeValue r, KnownNat out_width, KnownNat batch_size
     , KnownNat block_size, KnownNat window_size, KnownNat n_labels )
  => Proxy out_width
  -> SpeechDataBatch batch_size block_size window_size n_labels r
  -> Domains r
  -> r
rnnSpeechTest _ (sounds, labels) parameters =
  let xs = OS.transpose @'[2, 1, 0] sounds
      outputS =
        primalValue
           (rnnSpeech @out_width @batch_size @block_size @window_size @n_labels
                      xs)
           parameters
      outputs = map OS.toVector $ OSB.toList $ OS.unravel
                $ OS.transpose @'[1, 0] $ outputS
      targets = map OS.toVector $ OSB.toList $ OS.unravel labels
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs targets))
     / fromIntegral (valueOf @batch_size :: Int)

speechTestCaseRNN
  :: forall out_width batch_size block_size window_size n_labels d r m.
     ( KnownNat out_width, KnownNat batch_size, KnownNat block_size
     , KnownNat window_size, KnownNat n_labels
     , r ~ Float, d ~ 'DModeGradient, m ~ DualMonadGradient Float )
  => String
  -> Int
  -> Int
  -> (forall out_width' batch_size' block_size' window_size' n_labels'.
      ( DualMonad d r m, KnownNat out_width', KnownNat batch_size'
      , KnownNat block_size', KnownNat window_size', KnownNat n_labels' )
      => Proxy out_width'
      -> SpeechDataBatch batch_size' block_size' window_size' n_labels' r
      -> DualNumberVariables d r
      -> m (DualNumber d r))
  -> (forall out_width' batch_size' block_size' window_size' n_labels'.
      ( IsScalar 'DModeValue r, KnownNat out_width', KnownNat batch_size'
      , KnownNat block_size', KnownNat window_size', KnownNat n_labels' )
      => Proxy out_width'
      -> SpeechDataBatch batch_size' block_size' window_size' n_labels' r
      -> Domains r
      -> r)
  -> (forall out_width' window_size' n_labels'.
      (KnownNat out_width', KnownNat window_size', KnownNat n_labels')
      => Proxy out_width' -> Proxy window_size' -> Proxy n_labels'
      -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Float
  -> TestTree
speechTestCaseRNN prefix epochs maxBatches trainWithLoss ftest flen expected =
  let proxy_out_width = Proxy @out_width
      batch_size = valueOf @batch_size
      ((_, _, _, nParamsX), totalParams, range, parametersInitDouble) =
        initializerFixed 44 0.2
          (flen proxy_out_width (Proxy @window_size) (Proxy @n_labels))
      parametersInit = undefined  -- TODO
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (valueOf @out_width :: Int), show batch_size
                        , show nParamsX, show totalParams, show range ]
  in testCase name $ do
    hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
           prefix epochs maxBatches
    speechDataBatchList <-
      loadSpeechData
        @batch_size @block_size @window_size @n_labels
        "/home/mikolaj/Downloads/volleyball.float32.257.spectrogram.bin"
        "/home/mikolaj/Downloads/volleyball.float32.1.rms.bin"
    let trainData = speechDataBatchList
        testDataBatch = head speechDataBatchList
        -- There is some visual feedback, because some of these take long.
        runBatch
          :: (Domains r, StateAdam r)
          -> ( Int
             , [SpeechDataBatch batch_size block_size window_size n_labels r] )
          -> IO (Domains r, StateAdam r)
        runBatch (parameters@(!_, !_, !_, !_), stateAdam) (k, batch) = do
          let f = trainWithLoss proxy_out_width
              res@(parameters2, _) = sgdAdam f batch parameters stateAdam
              -- TODO: instead concatenate mini-batches
              !trainScore = ftest proxy_out_width (head batch) parameters2
              !testScore = ftest proxy_out_width testDataBatch parameters2
              !lenBatch = length batch
          hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenBatch
          hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
          hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
          return res
        runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
        runEpoch n (params2, _) | n > epochs = return params2
        runEpoch n paramsStateAdam = do
          hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
              batches = take maxBatches
                        $ zip [1 ..]
                        $ chunksOf batch_size trainDataShuffled
          !res <- foldM runBatch paramsStateAdam batches
          runEpoch (succ n) res
    res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
    let testErrorFinal = 1 - ftest proxy_out_width testDataBatch res
    testErrorFinal @?~ expected


mnistRNNTestsLong :: TestTree
mnistRNNTestsLong = testGroup "Speech RNN long tests"
  []

speechRNNTestsShort :: TestTree
speechRNNTestsShort = testGroup "Speech RNN short tests"
  [ testCase "Load and sanity check speech" $ do
      speechDataBatchList <-
        loadSpeechData
          @32 @20 @257 @1 @Float
          "/home/mikolaj/Downloads/volleyball.float32.257.spectrogram.bin"
          "/home/mikolaj/Downloads/volleyball.float32.1.rms.bin"
      length speechDataBatchList @?= 859 `div` (32 * 20)
      minimum (map (OS.minimumA . fst) speechDataBatchList) @?= 0.0
      maximum (map (OS.maximumA . fst) speechDataBatchList) @?= 26.52266
      minimum (map (OS.minimumA . snd) speechDataBatchList) @?= 0.0
      maximum (map (OS.maximumA . snd) speechDataBatchList) @?= 1.0
  , speechTestCaseRNN @128 @32 @20 @257 @1 "1 epoch, 1 batch" 1 1
                      rnnSpeechLossFused rnnSpeechTest rnnSpeechLen
                      0.4375
  ]
