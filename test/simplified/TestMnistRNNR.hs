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

import           Control.Monad (foldM, unless)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (SomeNat (..), someNatVal)
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.TensorAst
import HordeAd.External.OptimizerTools

import EqEpsilon

import           MnistData
import qualified MnistRnnRanked2

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
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
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
                             (Flip OS.Array) width r)
                0.4 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
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
           runBatch :: (HVector (Flip OR.Array), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal (Flip OR.Array))
                   -> ADVal ranked r 0
                 f (glyphR, labelR) adinputs =
                   MnistRnnRanked2.rnnMnistLossFusedR
                     miniBatchSize (rconst glyphR, rconst labelR)
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
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
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
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
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
                             (Flip OS.Array) width r)
                0.4 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
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
         funToAstIOR
           (miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, _, astLabel) <-
         funToAstIOR (miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistRnnRanked2.rnnMnistLossFusedR
                   miniBatchSize (astGlyph, astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (unRawHVector hVectorPrimal))
           runBatch :: (HVector (Flip OR.Array), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal (Flip OR.Array))
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvD EM.empty
                             $ zip vars $ V.toList varInputs
                       envMnist = extendEnvR varGlyph (rconst glyph)
                                  $ extendEnvR varLabel (rconst label) env
                   in interpretAst envMnist ast
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
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
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
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
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
          :: MnistRnnRanked2.ADRnnMnistParametersShaped (Flip OS.Array) width r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
        valsInit = forgetShape valsInitShaped
        hVectorInit = toHVectorOf valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show width, show miniBatchSize
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
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
         funToAstIOR
           (miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, varLabelD, astLabel) <-
         funToAstIOR (miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let envInit = extendEnvR varGlyph (rconstant $ AstRaw astGlyph)
                     $ extendEnvR varLabel (rconstant $ AstRaw astLabel)
                       EM.empty
           f = MnistRnnRanked2.rnnMnistLossFusedR
                 miniBatchSize (astGlyph, astLabel)
           (((varDtAgain, vars1Again), gradientRaw, primal), _) =
             revProduceArtifactH False f envInit valsInit
                                 (voidFromHVector hVectorInit)
           gradient = simplifyAstHVector6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistDataBatchR r] -> (HVector (Flip OR.Array), StateAdam)
              -> (HVector (Flip OR.Array), StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconst glyph
                 labelD = DynamicRanked $ rconst label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifact (vars, gradient, primal)
                                         parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientHVector)
           runBatch :: (HVector (Flip OR.Array), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
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
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
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
  :: Int -> Int -> MnistRnnRanked2.ADRnnMnistParameters (Flip OR.Array) Double
valsInitRNNOPP out_width sizeMnistHeightI =
  ( ( Flip
      $ OR.fromList [out_width, sizeMnistHeightI]
                    (map fromIntegral [0 .. out_width * sizeMnistHeightI - 1])
    , Flip
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , Flip
      $ OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( Flip
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , Flip
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , Flip $ OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( Flip
      $ OR.fromList [sizeMnistLabelInt, out_width]
                    (map fromIntegral [0 .. sizeMnistLabelInt * out_width - 1])
    , Flip
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
      blackGlyph = AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI
                   $ AstReplicate batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printGradient6Pretty renames artifactRev
    @?= "\\m15 m1 m2 v3 m4 m5 v6 m7 v8 -> let m10 = rreshape [2,1] (rreplicate 2 0.0) ; m11 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)))) ; m12 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)))) ; m13 = tanh (rtranspose [1,0] (rreplicate 1 v6) + rsum (rtranspose [2,1,0] (rreplicate 1 m4) * rtranspose [1,0] (rreplicate 1 m12)) + rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m10)))) ; t14 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m11 m13))) in let [m16 @Natural @Double @[10,1]] = [m15] in let m17 = rappend (rreshape [1,1] (rreplicate 1 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 m7) * rreplicate 1 m16))) (rreshape [0,1] (rreplicate 0 0.0))) ; m18 = (rconst (fromList [1,1] [1.0]) - m13 * m13) * rslice 1 1 m17 ; m19 = (rconst (fromList [1,1] [1.0]) - m12 * m12) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 m4) * rreplicate 1 m18)) ; m20 = (rconst (fromList [1,1] [1.0]) - m11 * m11) * rslice 0 1 m17 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m20)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m19)), rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)) * rreplicate 1 m20)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)) * rreplicate 1 m19)), rsum (rtranspose [1,0] m20) + rsum (rtranspose [1,0] m19), rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 m12) * rreplicate 1 m18)), rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rslice 1 1 m10)) * rreplicate 1 m18)), rsum (rtranspose [1,0] m18), rsum (rtranspose [2,1,0] (t14 * rreplicate 1 m16)), rsum (rtranspose [1,0] m16)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 m2 v3 m4 m5 v6 m7 v8 -> let m10 = rreshape [2,1] (rreplicate 2 0.0) ; m11 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)))) ; m12 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m10)))) ; m13 = tanh (rtranspose [1,0] (rreplicate 1 v6) + rsum (rtranspose [2,1,0] (rreplicate 1 m4) * rtranspose [1,0] (rreplicate 1 m12)) + rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m10)))) ; t14 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m11 m13))) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * t14) + rtranspose [1,0] (rreplicate 1 v8)]"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m15 m1 m2 v3 m4 m5 v6 m7 v8 -> let m11 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m12 = tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m13 = tanh (rtranspose [1,0] (rreplicate 1 v6) + rsum (rtranspose [2,1,0] (rreplicate 1 m4) * rtranspose [1,0] (rreplicate 1 m12)) + rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m17 = rappend (rconst (fromList [1,1] [0.0])) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m15))) (rreplicate 0 (rreplicate 1 0.0))) ; m18 = (rconst (fromList [1,1] [1.0]) - m13 * m13) * rslice 1 1 m17 ; m19 = (rconst (fromList [1,1] [1.0]) - m12 * m12) * rsum (rtranspose [1,2,0] (rreplicate 1 m4) * rtranspose [1,0] (rreplicate 1 m18)) ; m20 = (rconst (fromList [1,1] [1.0]) - m11 * m11) * rslice 0 1 m17 in [rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m20)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m19)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m20)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m19)), rsum (rtranspose [1,0] m20) + rsum (rtranspose [1,0] m19), rsum (rtranspose [2,0,1] (rreplicate 1 m12) * rtranspose [2,1,0] (rreplicate 1 m18)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m18)), rsum (rtranspose [1,0] m18), rsum (rtranspose [2,0,1] (rreplicate 10 m13) * rtranspose [2,1,0] (rreplicate 1 m15)), rsum (rtranspose [1,0] m15)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m1 m2 v3 m4 m5 v6 m7 v8 -> [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 1 v6) + rsum (rtranspose [2,1,0] (rreplicate 1 m4) * rtranspose [1,0] (rreplicate 1 (tanh (rtranspose [1,0] (rreplicate 1 v3) + rsum (rtranspose [2,1,0] (rreplicate 1 m1) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m2) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rtranspose [1,0] (rreplicate 1 v8)]"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistWidthI = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstRanked PrimalSpan Double 3
      blackGlyph = AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI
                   $ AstReplicate batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printGradient6Pretty renames artifactRev
    @?= "\\m20 m1 m2 v3 m4 m5 v6 m7 v8 -> let m11 = rreshape [4,2] (rreplicate 8 0.0) ; m12 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)))) ; m13 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)))) ; m14 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m13)) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m11)))) ; m15 = rappend m12 m14 ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15)))) ; m17 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15)))) ; m18 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m17)) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m15)))) ; t19 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m16 m18))) in let [m21 @Natural @Double @[10,2]] = [m20] in let m22 = rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m7) * rreplicate 2 m21))) (rreshape [0,2] (rreplicate 0 0.0))) ; m23 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m18 * m18) * rslice 2 2 m22 ; m24 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m17 * m17) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m4) * rreplicate 2 m23)) ; m25 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * rslice 0 2 m22 ; m26 = rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m2) * rreplicate 2 m25))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m2) * rreplicate 2 m24))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m5) * rreplicate 2 m23))) (rreshape [0,2] (rreplicate 0 0.0))) ; m27 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * rslice 2 2 m26 ; m28 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m13 * m13) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 m4) * rreplicate 2 m27)) ; m29 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m12 * m12) * rslice 0 2 m26 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m29)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m28)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m25)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m24)), rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)) * rreplicate 2 m29)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)) * rreplicate 2 m28)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15)) * rreplicate 2 m25)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15)) * rreplicate 2 m24)), rsum (rtranspose [1,0] m29) + rsum (rtranspose [1,0] m28) + rsum (rtranspose [1,0] m25) + rsum (rtranspose [1,0] m24), rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 m13) * rreplicate 2 m27)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 m17) * rreplicate 2 m23)), rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rslice 2 2 m11)) * rreplicate 2 m27)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rslice 2 2 m15)) * rreplicate 2 m23)), rsum (rtranspose [1,0] m27) + rsum (rtranspose [1,0] m23), rsum (rtranspose [2,1,0] (t19 * rreplicate 2 m21)), rsum (rtranspose [1,0] m21)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 m2 v3 m4 m5 v6 m7 v8 -> let m11 = rreshape [4,2] (rreplicate 8 0.0) ; m12 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)))) ; m13 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m11)))) ; m14 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m13)) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m11)))) ; m15 = rappend m12 m14 ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15)))) ; m17 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15)))) ; m18 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m17)) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m15)))) ; t19 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m16 m18))) in [rsum (rtranspose [2,1,0] (rreplicate 2 m7) * t19) + rtranspose [1,0] (rreplicate 2 v8)]"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m20 m1 m2 v3 m4 m5 v6 m7 v8 -> let m12 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m13 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m14 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m13)) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m15 = rappend m12 m14 ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15)))) ; m17 = tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15)))) ; m18 = tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m17)) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m15)))) ; m22 = rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m7) * rtranspose [1,0] (rreplicate 2 m20))) (rreplicate 0 (rreplicate 2 0.0))) ; m23 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m18 * m18) * rslice 2 2 m22 ; m24 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m17 * m17) * rsum (rtranspose [1,2,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m23)) ; m25 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * rslice 0 2 m22 ; m26 = rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 m25))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 m24))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 m23))) (rreplicate 0 (rreplicate 2 0.0))) ; m27 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * rslice 2 2 m26 ; m28 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m13 * m13) * rsum (rtranspose [1,2,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 m27)) ; m29 = (rconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m12 * m12) * rslice 0 2 m26 in [rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m29)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m25)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m24)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m29)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m15)) * rtranspose [2,1,0] (rreplicate 2 m25)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m15)) * rtranspose [2,1,0] (rreplicate 2 m24)), rsum (rtranspose [1,0] m29) + rsum (rtranspose [1,0] m28) + rsum (rtranspose [1,0] m25) + rsum (rtranspose [1,0] m24), rsum (rtranspose [2,0,1] (rreplicate 2 m13) * rtranspose [2,1,0] (rreplicate 2 m27)) + rsum (rtranspose [2,0,1] (rreplicate 2 m17) * rtranspose [2,1,0] (rreplicate 2 m23)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m27)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m15)) * rtranspose [2,1,0] (rreplicate 2 m23)), rsum (rtranspose [1,0] m27) + rsum (rtranspose [1,0] m23), rsum (rtranspose [2,0,1] (rreplicate 10 m18) * rtranspose [2,1,0] (rreplicate 2 m20)), rsum (rtranspose [1,0] m20)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m1 m2 v3 m4 m5 v6 m7 v8 -> let m15 = rappend (tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) (tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) in [rsum (rtranspose [2,1,0] (rreplicate 2 m7) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 2 v6) + rsum (rtranspose [2,1,0] (rreplicate 2 m4) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v3) + rsum (rtranspose [2,1,0] (rreplicate 2 m1) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m2) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m15))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m5) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m15))))))) + rtranspose [1,0] (rreplicate 2 v8)]"
