-- | Tests of "MnistRnnRanked2" neural networks using a few different
-- optimization pipelines.
--
-- *Not* LSTM.
-- Doesn't train without Adam, regardless of whether mini-batch sgd. It does
-- train with Adam, but only after very carefully tweaking initialization.
-- This is extremely sensitive to initial parameters, more than to anything
-- else. Probably, gradient is vanishing if parameters are initialized
-- with a probability distribution that doesn't have the right variance. See
-- https://stats.stackexchange.com/questions/301285/what-is-vanishing-gradient.
module TestMnistRNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import Data.Array.RankedS qualified as OR
import Data.IntMap.Strict qualified as IM
import Data.Vector.Generic qualified as V
import GHC.TypeLits (SomeNat (..), someNatVal)
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Text.Printf

import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.External.OptimizerTools
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))

import EqEpsilon

import MnistData
import MnistRnnRanked2 qualified

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNA
            , tensorADValMnistTestsRNNI
            , tensorADValMnistTestsRNNO
            , tensorMnistTestsPP
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseRNNA
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            forgetShape $ fst
            $ randomVals @(MnistRnnRanked2.ADRnnMnistParametersShaped
                             OSArray width r)
                0.4 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector (ORArray) -> r
      ftest = MnistRnnRanked2.rnnMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: (HVector (ORArray), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (ORArray), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal (ORArray))
                   -> ADVal ranked r 0
                 f (glyphR, labelR) adinputs =
                   MnistRnnRanked2.rnnMnistLossFusedR
                     miniBatchSize (rconst $ Nested.rfromOrthotope SNat glyphR, rconst $ Nested.rfromOrthotope SNat labelR)
                     (parseHVector (fromDValue valsInit) adinputs)
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector (ORArray), StateAdam) -> IO (HVector (ORArray))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (hVectorInit, initialStateAdam (voidFromHVector hVectorInit))
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNA
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNA :: TestTree
tensorADValMnistTestsRNNA = testGroup "RNN ADVal MNIST tests"
  [ mnistTestCaseRNNA "RNNA 1 epoch, 1 batch" 1 1 128 5 50
                       (0.9 :: Double)
  , mnistTestCaseRNNA "RNNA artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNA "RNNA artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.9336734693877551 :: Double)
  , mnistTestCaseRNNA "RNNA 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseRNNI
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            forgetShape $ fst
            $ randomVals @(MnistRnnRanked2.ADRnnMnistParametersShaped
                             OSArray width r)
                0.4 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector (ORArray) -> r
      ftest = MnistRnnRanked2.rnnMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, hVectorPrimal, var, _)
         <- funToAstRevIOTKNew $ FTKUntyped $ voidFromHVector hVectorInit
       let testDataR = packBatchR testData
       (varGlyph, _, astGlyph) <-
         funToAstIO
           (FTKR $ miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistRnnRanked2.rnnMnistLossFusedR
                   miniBatchSize (AstRanked astGlyph, AstRanked astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (unRawHVector hVectorPrimal))
           runBatch :: (HVector (ORArray), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (ORArray), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal (ORArray))
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = extendEnv var (HVectorPseudoTensor varInputs) emptyEnv
                       envMnist = extendEnv varGlyph (rconst $ Nested.rfromOrthotope SNat glyph)
                                  $ extendEnv varLabel (rconst $ Nested.rfromOrthotope SNat label) env
                   in interpretAst envMnist $ unAstRanked ast
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector (ORArray), StateAdam) -> IO (HVector (ORArray))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (hVectorInit, initialStateAdam (voidFromHVector hVectorInit))
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNI
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNI :: TestTree
tensorADValMnistTestsRNNI = testGroup "RNN Intermediate MNIST tests"
  [ mnistTestCaseRNNI "RNNI 1 epoch, 1 batch" 1 1 128 5 50
                       (0.9 :: Double)
  , mnistTestCaseRNNI "RNNI artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNI "RNNI artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.9336734693877551 :: Double)
  , mnistTestCaseRNNI "RNNI 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseRNNO
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNO prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
 -- TODO: use withKnownNat when we no longer support GHC 9.4
 case someNatVal $ toInteger width of
  Nothing -> error "impossible someNatVal error"
  Just (SomeNat @width _) ->
    let valsInitShaped
          :: MnistRnnRanked2.ADRnnMnistParametersShaped OSArray width r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
        valsInit = forgetShape valsInitShaped
        hVectorInit = toHVectorOf valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show width, show miniBatchSize
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r -> HVector (ORArray) -> r
        ftest = MnistRnnRanked2.rnnMnistTestR valsInit
    in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           dataInit = case chunksOf miniBatchSize testData of
             d : _ -> let (dglyph, dlabel) = packBatchR d
                      in ( FlipR $ Nested.rfromOrthotope SNat dglyph
                         , FlipR $ Nested.rfromOrthotope SNat dlabel )
             [] -> error "empty test data"
           f = \ (pars, (glyphR, labelR)) ->
             MnistRnnRanked2.rnnMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           (artRaw, _) = revArtifactAdapt False f (valsInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchR r] -> (HVector (ORArray), StateAdam)
              -> (HVector (ORArray), StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat glyph
                 labelD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifactTKNew art parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientHVector)
           runBatch :: (HVector (ORArray), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (ORArray), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = go chunkR (parameters, stateAdam)
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector (ORArray), StateAdam) -> IO (HVector (ORArray))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (hVectorInit, initialStateAdam (voidFromHVector hVectorInit))
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       assertEqualUpToEpsilon 1e-1 expected testErrorFinal

{-# SPECIALIZE mnistTestCaseRNNO
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNO :: TestTree
tensorADValMnistTestsRNNO = testGroup "RNN Once MNIST tests"
  [ mnistTestCaseRNNO "RNNO 1 epoch, 1 batch" 1 1 128 5 500
                       (0.898 :: Double)
  , mnistTestCaseRNNO "RNNO artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNO "RNNO artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNO "RNNO 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for RNN MNIST tests"
  [ testCase "RNNOPP" testRNNOPP
  , testCase "RNNOPP2" testRNNOPP2
  ]

valsInitRNNOPP
  :: Int -> Int -> MnistRnnRanked2.ADRnnMnistParameters (ORArray) Double
valsInitRNNOPP out_width sizeMnistHeightI =
  ( ( FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width, sizeMnistHeightI]
                    (map fromIntegral [0 .. out_width * sizeMnistHeightI - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( FlipR
       $ Nested.rfromOrthotope SNat
     $ OR.fromList [sizeMnistLabelInt, out_width]
                    (map fromIntegral [0 .. sizeMnistLabelInt * out_width - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [sizeMnistLabelInt]
                    (map fromIntegral [0 .. sizeMnistLabelInt - 1]) ) )

testRNNOPP :: Assertion
testRNNOPP = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 1
      sizeMnistHeightI = 1
      blackGlyph :: AstRanked PrimalSpan Double 3
      blackGlyph = AstRanked
                   $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @1)
                       (7 :: AstTensor PrimalSpan (TKR Double 0))
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m21 m22 m23 v24 m25 m26 v27 m28 v29 -> let m3 = rreshape [2,1] (rreplicate 2 0.0) ; m5 = tanh (rtranspose [1,0] (rreplicate 1 v24) + rsum (rtranspose [2,1,0] (rreplicate 1 m22) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m23) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m3)))) ; m7 = tanh (rtranspose [1,0] (rreplicate 1 v24) + rsum (rtranspose [2,1,0] (rreplicate 1 m22) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m23) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m3)))) ; m10 = tanh (rtranspose [1,0] (rreplicate 1 v27) + rsum (rtranspose [2,1,0] (rreplicate 1 m25) * rtranspose [1,0] (rreplicate 1 m7)) + rsum (rtranspose [2,1,0] (rreplicate 1 m26) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m3)))) ; t11 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m5 m10))) ; m13 = rappend (rreshape [1,1] (rreplicate 1 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m28) * rtranspose [1,0] (rreplicate 1 m21))) (rreshape [0,1] (rreplicate 0 0.0))) ; m14 = (rconst (rfromListLinear [1,1] [1.0]) - m10 * m10) * rslice 1 1 m13 ; m17 = (rconst (rfromListLinear [1,1] [1.0]) - m7 * m7) * rsum (rtranspose [1,2,0] (rreplicate 1 m25) * rtranspose [1,0] (rreplicate 1 m14)) ; m19 = (rconst (rfromListLinear [1,1] [1.0]) - m5 * m5) * rslice 0 1 m13 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m19)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m17)), rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 0 1 m3)) * rtranspose [2,1,0] (rreplicate 1 m19)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 0 1 m3)) * rtranspose [2,1,0] (rreplicate 1 m17)), rsum (rtranspose [1,0] m19) + rsum (rtranspose [1,0] m17), rsum (rtranspose [2,0,1] (rreplicate 1 m7) * rtranspose [2,1,0] (rreplicate 1 m14)), rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 1 1 m3)) * rtranspose [2,1,0] (rreplicate 1 m14)), rsum (rtranspose [1,0] m14), rsum (rtranspose [2,1,0] t11 * rtranspose [2,1,0] (rreplicate 1 m21)), rsum (rtranspose [1,0] m21)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m31 m32 v33 m34 m35 v36 m37 v38 -> let m3 = rreshape [2,1] (rreplicate 2 0.0) ; m5 = tanh (rtranspose [1,0] (rreplicate 1 v33) + rsum (rtranspose [2,1,0] (rreplicate 1 m31) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m32) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m3)))) ; m7 = tanh (rtranspose [1,0] (rreplicate 1 v33) + rsum (rtranspose [2,1,0] (rreplicate 1 m31) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m32) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m3)))) ; m10 = tanh (rtranspose [1,0] (rreplicate 1 v36) + rsum (rtranspose [2,1,0] (rreplicate 1 m34) * rtranspose [1,0] (rreplicate 1 m7)) + rsum (rtranspose [2,1,0] (rreplicate 1 m35) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m3)))) ; t11 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m5 m10))) in [rsum (rtranspose [2,1,0] (rreplicate 1 m37) * t11) + rtranspose [1,0] (rreplicate 1 v38)]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m45 m46 m47 v48 m49 m50 v51 m52 v53 -> let m5 = tanh (rtranspose [1,0] (rreplicate 1 v48) + rsum (rtranspose [2,1,0] (rreplicate 1 m46) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m47) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m7 = tanh (rtranspose [1,0] (rreplicate 1 v48) + rsum (rtranspose [2,1,0] (rreplicate 1 m46) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m47) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m10 = tanh (rtranspose [1,0] (rreplicate 1 v51) + rsum (rtranspose [2,1,0] (rreplicate 1 m49) * rtranspose [1,0] (rreplicate 1 m7)) + rsum (rtranspose [2,1,0] (rreplicate 1 m50) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m13 = rappend (rconst (rfromListLinear [1,1] [0.0])) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m52) * rtranspose [1,0] (rreplicate 1 m45))) (rreplicate 0 (rreplicate 1 0.0))) ; m14 = (rconst (rfromListLinear [1,1] [1.0]) - m10 * m10) * rslice 1 1 m13 ; m17 = (rconst (rfromListLinear [1,1] [1.0]) - m7 * m7) * rsum (rtranspose [1,2,0] (rreplicate 1 m49) * rtranspose [1,0] (rreplicate 1 m14)) ; m19 = (rconst (rfromListLinear [1,1] [1.0]) - m5 * m5) * rslice 0 1 m13 in [rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m19)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m17)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m19)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m17)), rsum (rtranspose [1,0] m19) + rsum (rtranspose [1,0] m17), rsum (rtranspose [2,0,1] (rreplicate 1 m7) * rtranspose [2,1,0] (rreplicate 1 m14)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m14)), rsum (rtranspose [1,0] m14), rsum (rtranspose [2,0,1] (rreplicate 10 m10) * rtranspose [2,1,0] (rreplicate 1 m45)), rsum (rtranspose [1,0] m45)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m55 m56 v57 m58 m59 v60 m61 v62 -> [rsum (rtranspose [2,1,0] (rreplicate 1 m61) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 1 v60) + rsum (rtranspose [2,1,0] (rreplicate 1 m58) * rtranspose [1,0] (rreplicate 1 (tanh (rtranspose [1,0] (rreplicate 1 v57) + rsum (rtranspose [2,1,0] (rreplicate 1 m55) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m56) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 1 m59) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rtranspose [1,0] (rreplicate 1 v62)]"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstRanked PrimalSpan Double 3
      blackGlyph = AstRanked
                   $ AstReplicate (SNat @2)
                   $ AstReplicate (SNat @2)
                   $ AstReplicate (SNat @2)
                       (7 :: AstTensor PrimalSpan (TKR Double 0))
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m38 m39 m40 v41 m42 m43 v44 m45 v46 -> let m4 = rreshape [4,2] (rreplicate 8 0.0) ; m6 = tanh (rtranspose [1,0] (rreplicate 2 v41) + rsum (rtranspose [2,1,0] (rreplicate 2 m39) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m40) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m4)))) ; m8 = tanh (rtranspose [1,0] (rreplicate 2 v41) + rsum (rtranspose [2,1,0] (rreplicate 2 m39) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m40) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m4)))) ; m11 = tanh (rtranspose [1,0] (rreplicate 2 v44) + rsum (rtranspose [2,1,0] (rreplicate 2 m42) * rtranspose [1,0] (rreplicate 2 m8)) + rsum (rtranspose [2,1,0] (rreplicate 2 m43) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m4)))) ; m12 = rappend m6 m11 ; m14 = tanh (rtranspose [1,0] (rreplicate 2 v41) + rsum (rtranspose [2,1,0] (rreplicate 2 m39) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m40) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v41) + rsum (rtranspose [2,1,0] (rreplicate 2 m39) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m40) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 v44) + rsum (rtranspose [2,1,0] (rreplicate 2 m42) * rtranspose [1,0] (rreplicate 2 m16)) + rsum (rtranspose [2,1,0] (rreplicate 2 m43) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)))) ; t20 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m14 m19))) ; m22 = rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m45) * rtranspose [1,0] (rreplicate 2 m38))) (rreshape [0,2] (rreplicate 0 0.0))) ; m23 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * rslice 2 2 m22 ; m26 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * rsum (rtranspose [1,2,0] (rreplicate 2 m42) * rtranspose [1,0] (rreplicate 2 m23)) ; m28 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * rslice 0 2 m22 ; m30 = rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m40) * rtranspose [1,0] (rreplicate 2 m28))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m40) * rtranspose [1,0] (rreplicate 2 m26))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m43) * rtranspose [1,0] (rreplicate 2 m23))) (rreshape [0,2] (rreplicate 0 0.0))) ; m31 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m11 * m11) * rslice 2 2 m30 ; m34 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m8 * m8) * rsum (rtranspose [1,2,0] (rreplicate 2 m42) * rtranspose [1,0] (rreplicate 2 m31)) ; m36 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m6 * m6) * rslice 0 2 m30 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m36)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m34)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m28)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m26)), rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m4)) * rtranspose [2,1,0] (rreplicate 2 m36)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m4)) * rtranspose [2,1,0] (rreplicate 2 m34)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m26)), rsum (rtranspose [1,0] m36) + rsum (rtranspose [1,0] m34) + rsum (rtranspose [1,0] m28) + rsum (rtranspose [1,0] m26), rsum (rtranspose [2,0,1] (rreplicate 2 m8) * rtranspose [2,1,0] (rreplicate 2 m31)) + rsum (rtranspose [2,0,1] (rreplicate 2 m16) * rtranspose [2,1,0] (rreplicate 2 m23)), rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m4)) * rtranspose [2,1,0] (rreplicate 2 m31)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m23)), rsum (rtranspose [1,0] m31) + rsum (rtranspose [1,0] m23), rsum (rtranspose [2,1,0] t20 * rtranspose [2,1,0] (rreplicate 2 m38)), rsum (rtranspose [1,0] m38)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m48 m49 v50 m51 m52 v53 m54 v55 -> let m4 = rreshape [4,2] (rreplicate 8 0.0) ; m6 = tanh (rtranspose [1,0] (rreplicate 2 v50) + rsum (rtranspose [2,1,0] (rreplicate 2 m48) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m49) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m4)))) ; m8 = tanh (rtranspose [1,0] (rreplicate 2 v50) + rsum (rtranspose [2,1,0] (rreplicate 2 m48) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m49) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m4)))) ; m11 = tanh (rtranspose [1,0] (rreplicate 2 v53) + rsum (rtranspose [2,1,0] (rreplicate 2 m51) * rtranspose [1,0] (rreplicate 2 m8)) + rsum (rtranspose [2,1,0] (rreplicate 2 m52) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m4)))) ; m12 = rappend m6 m11 ; m14 = tanh (rtranspose [1,0] (rreplicate 2 v50) + rsum (rtranspose [2,1,0] (rreplicate 2 m48) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m49) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v50) + rsum (rtranspose [2,1,0] (rreplicate 2 m48) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m49) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 v53) + rsum (rtranspose [2,1,0] (rreplicate 2 m51) * rtranspose [1,0] (rreplicate 2 m16)) + rsum (rtranspose [2,1,0] (rreplicate 2 m52) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)))) ; t20 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m14 m19))) in [rsum (rtranspose [2,1,0] (rreplicate 2 m54) * t20) + rtranspose [1,0] (rreplicate 2 v55)]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m76 m77 m78 v79 m80 m81 v82 m83 v84 -> let m6 = tanh (rtranspose [1,0] (rreplicate 2 v79) + rsum (rtranspose [2,1,0] (rreplicate 2 m77) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m78) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m8 = tanh (rtranspose [1,0] (rreplicate 2 v79) + rsum (rtranspose [2,1,0] (rreplicate 2 m77) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m78) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m11 = tanh (rtranspose [1,0] (rreplicate 2 v82) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 m8)) + rsum (rtranspose [2,1,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m12 = rappend m6 m11 ; m14 = tanh (rtranspose [1,0] (rreplicate 2 v79) + rsum (rtranspose [2,1,0] (rreplicate 2 m77) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m78) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v79) + rsum (rtranspose [2,1,0] (rreplicate 2 m77) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m78) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 v82) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 m16)) + rsum (rtranspose [2,1,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)))) ; m22 = rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 m76))) (rreplicate 0 (rreplicate 2 0.0))) ; m23 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * rslice 2 2 m22 ; m26 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * rsum (rtranspose [1,2,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 m23)) ; m28 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * rslice 0 2 m22 ; m30 = rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m78) * rtranspose [1,0] (rreplicate 2 m28))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m78) * rtranspose [1,0] (rreplicate 2 m26))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 m23))) (rreplicate 0 (rreplicate 2 0.0))) ; m31 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m11 * m11) * rslice 2 2 m30 ; m34 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m8 * m8) * rsum (rtranspose [1,2,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 m31)) ; m36 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m6 * m6) * rslice 0 2 m30 in [rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m36)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m34)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m26)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m36)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m34)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m26)), rsum (rtranspose [1,0] m36) + rsum (rtranspose [1,0] m34) + rsum (rtranspose [1,0] m28) + rsum (rtranspose [1,0] m26), rsum (rtranspose [2,0,1] (rreplicate 2 m8) * rtranspose [2,1,0] (rreplicate 2 m31)) + rsum (rtranspose [2,0,1] (rreplicate 2 m16) * rtranspose [2,1,0] (rreplicate 2 m23)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m31)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m23)), rsum (rtranspose [1,0] m31) + rsum (rtranspose [1,0] m23), rsum (rtranspose [2,0,1] (rreplicate 10 m19) * rtranspose [2,1,0] (rreplicate 2 m76)), rsum (rtranspose [1,0] m76)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m86 m87 v88 m89 m90 v91 m92 v93 -> let m12 = rappend (tanh (rtranspose [1,0] (rreplicate 2 v88) + rsum (rtranspose [2,1,0] (rreplicate 2 m86) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m87) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) (tanh (rtranspose [1,0] (rreplicate 2 v91) + rsum (rtranspose [2,1,0] (rreplicate 2 m89) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v88) + rsum (rtranspose [2,1,0] (rreplicate 2 m86) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m87) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m90) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) in [rsum (rtranspose [2,1,0] (rreplicate 2 m92) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 2 v91) + rsum (rtranspose [2,1,0] (rreplicate 2 m89) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v88) + rsum (rtranspose [2,1,0] (rreplicate 2 m86) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m87) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m90) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12))))))) + rtranspose [1,0] (rreplicate 2 v93)]"
