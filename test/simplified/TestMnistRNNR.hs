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
import HordeAd.Core.TensorAst
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
       (_, hVectorPrimal, vars, _)
         <- funToAstRevIO (voidFromHVector hVectorInit)
       let testDataR = packBatchR testData
       (varGlyph, _, astGlyph) <-
         funToAstIO
           (TKFR $ miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, _, astLabel) <-
         funToAstIO (TKFR $ miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
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
                   let env = foldr extendEnvD emptyEnv
                             $ zip vars $ V.toList varInputs
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
       (varGlyph, varGlyphD, astGlyph) <-
         funToAstIO
           (TKFR $ miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, varLabelD, astLabel) <-
         funToAstIO (TKFR $ miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let envInit = extendEnv varGlyph (rconstant $ AstRaw astGlyph)
                     $ extendEnv varLabel (rconstant $ AstRaw astLabel)
                       emptyEnv
           f = MnistRnnRanked2.rnnMnistLossFusedR
                 miniBatchSize (AstRanked astGlyph, AstRanked astLabel)
           (AstArtifact varDtAgain vars1Again gradientRaw primal, _) =
             revProduceArtifactH False f envInit valsInit
                                 (voidFromHVector hVectorInit)
           gradient = simplifyInlineHVectorRaw gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           art = AstArtifact varDtAgain vars1AndInputAgain gradient primal
           go :: [MnistDataBatchR r] -> (HVector (ORArray), StateAdam)
              -> (HVector (ORArray), StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat glyph
                 labelD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifact art parametersAndInput Nothing
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
      sizeMnistWidthI = 1
      sizeMnistHeightI = 1
      blackGlyph :: AstRanked PrimalSpan Double 3
      blackGlyph = AstRanked
                   $ AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI
                   $ AstReplicate batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m19 m1 m2 v3 m4 m5 v6 m7 v8 -> let m10 = rreshape [2,1] (rreplicate 2 0.0) ; t11 = rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)) ; m12 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * t11)) ; t13 = rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)) ; m14 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * t13)) ; t15 = rtranspose [1,0] (rreplicate 1 m14) ; t16 = rtranspose [1,0] (rreplicate 1 (rslice 1 1 m10)) ; m17 = tanh (rtranspose [1,0] (rreplicate 1 v6) + rsum (rtranspose [2,1,0] (rreplicate 1 m4) * t15) + rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t16)) ; t18 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m12 m17))) ; m20 = rappend (rreshape [1,1] (rreplicate 1 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 m7) * rreplicate 1 m19))) (rreshape [0,1] (rreplicate 0 0.0))) ; m21 = (rconst (rfromListLinear [1,1] [1.0]) - m17 * m17) * rslice 1 1 m20 ; t22 = rreplicate 1 m21 ; t23 = rreplicate 1 m21 ; m24 = (rconst (rfromListLinear [1,1] [1.0]) - m14 * m14) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 m4) * t23)) ; t25 = rreplicate 1 m24 ; m26 = (rconst (rfromListLinear [1,1] [1.0]) - m12 * m12) * rslice 0 1 m20 ; t27 = rreplicate 1 m26 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m26)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m24)), rsum (rtranspose [2,1,0] (t11 * t27)) + rsum (rtranspose [2,1,0] (t13 * t25)), rsum (rtranspose [1,0] m26) + rsum (rtranspose [1,0] m24), rsum (rtranspose [2,1,0] (t15 * t23)), rsum (rtranspose [2,1,0] (t16 * t22)), rsum (rtranspose [1,0] m21), rsum (rtranspose [2,1,0] (t18 * rreplicate 1 m19)), rsum (rtranspose [1,0] m19)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m1 m2 v3 m4 m5 v6 m7 v8 -> let m10 = rreshape [2,1] (rreplicate 2 0.0) ; t11 = rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)) ; m12 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * t11)) ; t13 = rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)) ; m14 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * t13)) ; t15 = rtranspose [1,0] (rreplicate 1 m14) ; t16 = rtranspose [1,0] (rreplicate 1 (rslice 1 1 m10)) ; m17 = tanh (rtranspose [1,0] (rreplicate 1 v6) + rsum (rtranspose [2,1,0] (rreplicate 1 m4) * t15) + rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t16)) ; t18 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m12 m17))) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * t18) + rtranspose [1,0] (rreplicate 1 v8)]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m19 m1 m2 v3 m4 m5 v6 m7 v8 -> let m12 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m14 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m17 = tanh (rtranspose [1,0] (rreplicate 1 v6) + rsum (rtranspose [2,1,0] (rreplicate 1 m4) * rtranspose [1,0] (rreplicate 1 m14)) + rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m20 = rappend (rconst (rfromListLinear [1,1] [0.0])) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m19))) (rreplicate 0 (rreplicate 1 0.0))) ; m21 = (rconst (rfromListLinear [1,1] [1.0]) - m17 * m17) * rslice 1 1 m20 ; m24 = (rconst (rfromListLinear [1,1] [1.0]) - m14 * m14) * rsum (rtranspose [1,2,0] (rreplicate 1 m4) * rtranspose [1,0] (rreplicate 1 m21)) ; m26 = (rconst (rfromListLinear [1,1] [1.0]) - m12 * m12) * rslice 0 1 m20 in [rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m26)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m24)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m26)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m24)), rsum (rtranspose [1,0] m26) + rsum (rtranspose [1,0] m24), rsum (rtranspose [2,0,1] (rreplicate 1 m14) * rtranspose [2,1,0] (rreplicate 1 m21)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m21)), rsum (rtranspose [1,0] m21), rsum (rtranspose [2,0,1] (rreplicate 10 m17) * rtranspose [2,1,0] (rreplicate 1 m19)), rsum (rtranspose [1,0] m19)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1 m2 v3 m4 m5 v6 m7 v8 -> [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 1 v6) + rsum (rtranspose [2,1,0] (rreplicate 1 m4) * rtranspose [1,0] (rreplicate 1 (tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rtranspose [1,0] (rreplicate 1 v8)]"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistWidthI = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstRanked PrimalSpan Double 3
      blackGlyph = AstRanked
                   $ AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI
                   $ AstReplicate batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m28 m1 m2 v3 m4 m5 v6 m7 v8 -> let m11 = rreshape [4,2] (rreplicate 8 0.0) ; t12 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)) ; m13 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * t12)) ; t14 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)) ; m15 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * t14)) ; t16 = rtranspose [1,0] (rreplicate 2 m15) ; t17 = rtranspose [1,0] (rreplicate 2 (rslice 2 2 m11)) ; m18 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * t16) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * t17)) ; m19 = rappend m13 m18 ; t20 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m19)) ; m21 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * t20)) ; t22 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m19)) ; m23 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * t22)) ; t24 = rtranspose [1,0] (rreplicate 2 m23) ; t25 = rtranspose [1,0] (rreplicate 2 (rslice 2 2 m19)) ; m26 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * t24) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * t25)) ; t27 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m21 m26))) ; m29 = rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m7) * rreplicate 2 m28))) (rreshape [0,2] (rreplicate 0 0.0))) ; m30 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m26 * m26) * rslice 2 2 m29 ; t31 = rreplicate 2 m30 ; t32 = rreplicate 2 m30 ; m33 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m23 * m23) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m4) * t32)) ; t34 = rreplicate 2 m33 ; m35 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m21 * m21) * rslice 0 2 m29 ; t36 = rreplicate 2 m35 ; m37 = rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m2) * t36))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m2) * t34))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m5) * t31))) (rreshape [0,2] (rreplicate 0 0.0))) ; m38 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m18 * m18) * rslice 2 2 m37 ; t39 = rreplicate 2 m38 ; t40 = rreplicate 2 m38 ; m41 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m15 * m15) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m4) * t40)) ; t42 = rreplicate 2 m41 ; m43 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m13 * m13) * rslice 0 2 m37 ; t44 = rreplicate 2 m43 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m43)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m41)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m35)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m33)), rsum (rtranspose [2,1,0] (t12 * t44)) + rsum (rtranspose [2,1,0] (t14 * t42)) + rsum (rtranspose [2,1,0] (t20 * t36)) + rsum (rtranspose [2,1,0] (t22 * t34)), rsum (rtranspose [1,0] m43) + rsum (rtranspose [1,0] m41) + rsum (rtranspose [1,0] m35) + rsum (rtranspose [1,0] m33), rsum (rtranspose [2,1,0] (t16 * t40)) + rsum (rtranspose [2,1,0] (t24 * t32)), rsum (rtranspose [2,1,0] (t17 * t39)) + rsum (rtranspose [2,1,0] (t25 * t31)), rsum (rtranspose [1,0] m38) + rsum (rtranspose [1,0] m30), rsum (rtranspose [2,1,0] (t27 * rreplicate 2 m28)), rsum (rtranspose [1,0] m28)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m1 m2 v3 m4 m5 v6 m7 v8 -> let m11 = rreshape [4,2] (rreplicate 8 0.0) ; t12 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)) ; m13 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * t12)) ; t14 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)) ; m15 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * t14)) ; t16 = rtranspose [1,0] (rreplicate 2 m15) ; t17 = rtranspose [1,0] (rreplicate 2 (rslice 2 2 m11)) ; m18 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * t16) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * t17)) ; m19 = rappend m13 m18 ; t20 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m19)) ; m21 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * t20)) ; t22 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m19)) ; m23 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * t22)) ; t24 = rtranspose [1,0] (rreplicate 2 m23) ; t25 = rtranspose [1,0] (rreplicate 2 (rslice 2 2 m19)) ; m26 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * t24) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * t25)) ; t27 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m21 m26))) in [rsum (rtranspose [2,1,0] (rreplicate 2 m7) * t27) + rtranspose [1,0] (rreplicate 2 v8)]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m28 m1 m2 v3 m4 m5 v6 m7 v8 -> let m13 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m15 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m18 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m15)) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m19 = rappend m13 m18 ; m21 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m19)))) ; m23 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m19)))) ; m26 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m23)) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m19)))) ; m29 = rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m7) * rtranspose [1,0] (rreplicate 2 m28))) (rreplicate 0 (rreplicate 2 0.0))) ; m30 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m26 * m26) * rslice 2 2 m29 ; m33 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m23 * m23) * rsum (rtranspose [1,2,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m30)) ; m35 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m21 * m21) * rslice 0 2 m29 ; m37 = rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 m35))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 m33))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 m30))) (rreplicate 0 (rreplicate 2 0.0))) ; m38 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m18 * m18) * rslice 2 2 m37 ; m41 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m15 * m15) * rsum (rtranspose [1,2,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m38)) ; m43 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m13 * m13) * rslice 0 2 m37 in [rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m43)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m41)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m35)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m33)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m43)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m41)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m19)) * rtranspose [2,1,0] (rreplicate 2 m35)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m19)) * rtranspose [2,1,0] (rreplicate 2 m33)), rsum (rtranspose [1,0] m43) + rsum (rtranspose [1,0] m41) + rsum (rtranspose [1,0] m35) + rsum (rtranspose [1,0] m33), rsum (rtranspose [2,0,1] (rreplicate 2 m15) * rtranspose [2,1,0] (rreplicate 2 m38)) + rsum (rtranspose [2,0,1] (rreplicate 2 m23) * rtranspose [2,1,0] (rreplicate 2 m30)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m38)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m19)) * rtranspose [2,1,0] (rreplicate 2 m30)), rsum (rtranspose [1,0] m38) + rsum (rtranspose [1,0] m30), rsum (rtranspose [2,0,1] (rreplicate 10 m26) * rtranspose [2,1,0] (rreplicate 2 m28)), rsum (rtranspose [1,0] m28)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1 m2 v3 m4 m5 v6 m7 v8 -> let m19 = rappend (tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) (tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) in [rsum (rtranspose [2,1,0] (rreplicate 2 m7) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m19))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m19))))))) + rtranspose [1,0] (rreplicate 2 v8)]"
