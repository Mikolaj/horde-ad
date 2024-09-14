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
      ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
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
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal ORArray)
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
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
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
      ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
      ftest = MnistRnnRanked2.rnnMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, _, var, hVector)
         <- funToAstRevIO $ FTKUntyped $ voidFromHVector hVectorInit
       let testDataR = packBatchR testData
       (varGlyph, _, astGlyph) <-
         funToAstIO
           (FTKR $ miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let ast :: AstRanked FullSpan r 0
           ast = MnistRnnRanked2.rnnMnistLossFusedR
                   miniBatchSize (AstRanked astGlyph, AstRanked astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (dunHVector $ unHVectorPseudoTensor (rankedY (stensorKind @TKUntyped) hVector)))
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal ORArray)
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
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
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
        ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
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
           go :: [MnistDataBatchR r] -> (HVector ORArray, StateAdam)
              -> (HVector ORArray, StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat glyph
                 labelD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat label
                 parametersAndInput =
                   HVectorPseudoTensor
                   $ V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   unHVectorPseudoTensor
                   $ fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientHVector)
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
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
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
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
  :: Int -> Int -> MnistRnnRanked2.ADRnnMnistParameters ORArray Double
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
                       (7 :: AstTensor AstMethodLet PrimalSpan (TKR Double 0))
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m20 m29 m30 v31 m32 m33 v34 m35 v36 -> let m11 = rreshape [2,1] (rreplicate 2 0.0) ; m13 = tanh (rtranspose [1,0] (rreplicate 1 v31) + rsum (rtranspose [2,1,0] (rreplicate 1 m29) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m30) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m11)))) ; m15 = tanh (rtranspose [1,0] (rreplicate 1 v31) + rsum (rtranspose [2,1,0] (rreplicate 1 m29) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m30) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m11)))) ; m18 = tanh (rtranspose [1,0] (rreplicate 1 v34) + rsum (rtranspose [2,1,0] (rreplicate 1 m32) * rtranspose [1,0] (rreplicate 1 m15)) + rsum (rtranspose [2,1,0] (rreplicate 1 m33) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m11)))) ; t19 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m13 m18))) ; m21 = rappend (rreshape [1,1] (rreplicate 1 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m35) * rtranspose [1,0] (rreplicate 1 m20))) (rreshape [0,1] (rreplicate 0 0.0))) ; m22 = (rconst (rfromListLinear [1,1] [1.0]) - m18 * m18) * rslice 1 1 m21 ; m25 = (rconst (rfromListLinear [1,1] [1.0]) - m15 * m15) * rsum (rtranspose [1,2,0] (rreplicate 1 m32) * rtranspose [1,0] (rreplicate 1 m22)) ; m27 = (rconst (rfromListLinear [1,1] [1.0]) - m13 * m13) * rslice 0 1 m21 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m27)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m25)), rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 0 1 m11)) * rtranspose [2,1,0] (rreplicate 1 m27)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 0 1 m11)) * rtranspose [2,1,0] (rreplicate 1 m25)), rsum (rtranspose [1,0] m27) + rsum (rtranspose [1,0] m25), rsum (rtranspose [2,0,1] (rreplicate 1 m15) * rtranspose [2,1,0] (rreplicate 1 m22)), rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 1 1 m11)) * rtranspose [2,1,0] (rreplicate 1 m22)), rsum (rtranspose [1,0] m22), rsum (rtranspose [2,1,0] (t19 * rreplicate 1 m20)), rsum (rtranspose [1,0] m20)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m37 m38 v39 m40 m41 v42 m43 v44 -> let m11 = rreshape [2,1] (rreplicate 2 0.0) ; m13 = tanh (rtranspose [1,0] (rreplicate 1 v39) + rsum (rtranspose [2,1,0] (rreplicate 1 m37) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m38) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m11)))) ; m15 = tanh (rtranspose [1,0] (rreplicate 1 v39) + rsum (rtranspose [2,1,0] (rreplicate 1 m37) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m38) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m11)))) ; m18 = tanh (rtranspose [1,0] (rreplicate 1 v42) + rsum (rtranspose [2,1,0] (rreplicate 1 m40) * rtranspose [1,0] (rreplicate 1 m15)) + rsum (rtranspose [2,1,0] (rreplicate 1 m41) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m11)))) ; t19 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m13 m18))) in rsum (rtranspose [2,1,0] (rreplicate 1 m43) * t19) + rtranspose [1,0] (rreplicate 1 v44)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m20 m51 m52 v53 m54 m55 v56 m57 v58 -> let m13 = tanh (rtranspose [1,0] (rreplicate 1 v53) + rsum (rtranspose [2,1,0] (rreplicate 1 m51) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m52) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m15 = tanh (rtranspose [1,0] (rreplicate 1 v53) + rsum (rtranspose [2,1,0] (rreplicate 1 m51) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m52) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m18 = tanh (rtranspose [1,0] (rreplicate 1 v56) + rsum (rtranspose [2,1,0] (rreplicate 1 m54) * rtranspose [1,0] (rreplicate 1 m15)) + rsum (rtranspose [2,1,0] (rreplicate 1 m55) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m21 = rappend (rconst (rfromListLinear [1,1] [0.0])) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m57) * rtranspose [1,0] (rreplicate 1 m20))) (rreplicate 0 (rreplicate 1 0.0))) ; m22 = (rconst (rfromListLinear [1,1] [1.0]) - m18 * m18) * rslice 1 1 m21 ; m25 = (rconst (rfromListLinear [1,1] [1.0]) - m15 * m15) * rsum (rtranspose [1,2,0] (rreplicate 1 m54) * rtranspose [1,0] (rreplicate 1 m22)) ; m27 = (rconst (rfromListLinear [1,1] [1.0]) - m13 * m13) * rslice 0 1 m21 in [rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m27)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m25)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m27)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m25)), rsum (rtranspose [1,0] m27) + rsum (rtranspose [1,0] m25), rsum (rtranspose [2,0,1] (rreplicate 1 m15) * rtranspose [2,1,0] (rreplicate 1 m22)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m22)), rsum (rtranspose [1,0] m22), rsum (rtranspose [2,0,1] (rreplicate 10 m18) * rtranspose [2,1,0] (rreplicate 1 m20)), rsum (rtranspose [1,0] m20)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m65 m66 v67 m68 m69 v70 m71 v72 -> rsum (rtranspose [2,1,0] (rreplicate 1 m71) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 1 v70) + rsum (rtranspose [2,1,0] (rreplicate 1 m68) * rtranspose [1,0] (rreplicate 1 (tanh (rtranspose [1,0] (rreplicate 1 v67) + rsum (rtranspose [2,1,0] (rreplicate 1 m65) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m66) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 1 m69) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rtranspose [1,0] (rreplicate 1 v72)"

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
                       (7 :: AstTensor AstMethodLet PrimalSpan (TKR Double 0))
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m29 m46 m47 v48 m49 m50 v51 m52 v53 -> let m12 = rreshape [4,2] (rreplicate 8 0.0) ; m14 = tanh (rtranspose [1,0] (rreplicate 2 v48) + rsum (rtranspose [2,1,0] (rreplicate 2 m46) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m47) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v48) + rsum (rtranspose [2,1,0] (rreplicate 2 m46) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m47) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 v51) + rsum (rtranspose [2,1,0] (rreplicate 2 m49) * rtranspose [1,0] (rreplicate 2 m16)) + rsum (rtranspose [2,1,0] (rreplicate 2 m50) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)))) ; m20 = rappend m14 m19 ; m22 = tanh (rtranspose [1,0] (rreplicate 2 v48) + rsum (rtranspose [2,1,0] (rreplicate 2 m46) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m47) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m20)))) ; m24 = tanh (rtranspose [1,0] (rreplicate 2 v48) + rsum (rtranspose [2,1,0] (rreplicate 2 m46) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m47) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m20)))) ; m27 = tanh (rtranspose [1,0] (rreplicate 2 v51) + rsum (rtranspose [2,1,0] (rreplicate 2 m49) * rtranspose [1,0] (rreplicate 2 m24)) + rsum (rtranspose [2,1,0] (rreplicate 2 m50) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m20)))) ; t28 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m22 m27))) ; m30 = rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m52) * rtranspose [1,0] (rreplicate 2 m29))) (rreshape [0,2] (rreplicate 0 0.0))) ; m31 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m27 * m27) * rslice 2 2 m30 ; m34 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m24 * m24) * rsum (rtranspose [1,2,0] (rreplicate 2 m49) * rtranspose [1,0] (rreplicate 2 m31)) ; m36 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m22 * m22) * rslice 0 2 m30 ; m38 = rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m47) * rtranspose [1,0] (rreplicate 2 m36))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m47) * rtranspose [1,0] (rreplicate 2 m34))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m50) * rtranspose [1,0] (rreplicate 2 m31))) (rreshape [0,2] (rreplicate 0 0.0))) ; m39 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * rslice 2 2 m38 ; m42 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * rsum (rtranspose [1,2,0] (rreplicate 2 m49) * rtranspose [1,0] (rreplicate 2 m39)) ; m44 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * rslice 0 2 m38 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m44)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m42)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m36)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m34)), rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m44)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m42)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m20)) * rtranspose [2,1,0] (rreplicate 2 m36)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m20)) * rtranspose [2,1,0] (rreplicate 2 m34)), rsum (rtranspose [1,0] m44) + rsum (rtranspose [1,0] m42) + rsum (rtranspose [1,0] m36) + rsum (rtranspose [1,0] m34), rsum (rtranspose [2,0,1] (rreplicate 2 m16) * rtranspose [2,1,0] (rreplicate 2 m39)) + rsum (rtranspose [2,0,1] (rreplicate 2 m24) * rtranspose [2,1,0] (rreplicate 2 m31)), rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m39)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m20)) * rtranspose [2,1,0] (rreplicate 2 m31)), rsum (rtranspose [1,0] m39) + rsum (rtranspose [1,0] m31), rsum (rtranspose [2,1,0] (t28 * rreplicate 2 m29)), rsum (rtranspose [1,0] m29)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m54 m55 v56 m57 m58 v59 m60 v61 -> let m12 = rreshape [4,2] (rreplicate 8 0.0) ; m14 = tanh (rtranspose [1,0] (rreplicate 2 v56) + rsum (rtranspose [2,1,0] (rreplicate 2 m54) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m55) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v56) + rsum (rtranspose [2,1,0] (rreplicate 2 m54) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m55) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 v59) + rsum (rtranspose [2,1,0] (rreplicate 2 m57) * rtranspose [1,0] (rreplicate 2 m16)) + rsum (rtranspose [2,1,0] (rreplicate 2 m58) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)))) ; m20 = rappend m14 m19 ; m22 = tanh (rtranspose [1,0] (rreplicate 2 v56) + rsum (rtranspose [2,1,0] (rreplicate 2 m54) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m55) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m20)))) ; m24 = tanh (rtranspose [1,0] (rreplicate 2 v56) + rsum (rtranspose [2,1,0] (rreplicate 2 m54) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m55) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m20)))) ; m27 = tanh (rtranspose [1,0] (rreplicate 2 v59) + rsum (rtranspose [2,1,0] (rreplicate 2 m57) * rtranspose [1,0] (rreplicate 2 m24)) + rsum (rtranspose [2,1,0] (rreplicate 2 m58) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m20)))) ; t28 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m22 m27))) in rsum (rtranspose [2,1,0] (rreplicate 2 m60) * t28) + rtranspose [1,0] (rreplicate 2 v61)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m29 m82 m83 v84 m85 m86 v87 m88 v89 -> let m14 = tanh (rtranspose [1,0] (rreplicate 2 v84) + rsum (rtranspose [2,1,0] (rreplicate 2 m82) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 v84) + rsum (rtranspose [2,1,0] (rreplicate 2 m82) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 v87) + rsum (rtranspose [2,1,0] (rreplicate 2 m85) * rtranspose [1,0] (rreplicate 2 m16)) + rsum (rtranspose [2,1,0] (rreplicate 2 m86) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m20 = rappend m14 m19 ; m22 = tanh (rtranspose [1,0] (rreplicate 2 v84) + rsum (rtranspose [2,1,0] (rreplicate 2 m82) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m20)))) ; m24 = tanh (rtranspose [1,0] (rreplicate 2 v84) + rsum (rtranspose [2,1,0] (rreplicate 2 m82) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m20)))) ; m27 = tanh (rtranspose [1,0] (rreplicate 2 v87) + rsum (rtranspose [2,1,0] (rreplicate 2 m85) * rtranspose [1,0] (rreplicate 2 m24)) + rsum (rtranspose [2,1,0] (rreplicate 2 m86) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m20)))) ; m30 = rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m88) * rtranspose [1,0] (rreplicate 2 m29))) (rreplicate 0 (rreplicate 2 0.0))) ; m31 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m27 * m27) * rslice 2 2 m30 ; m34 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m24 * m24) * rsum (rtranspose [1,2,0] (rreplicate 2 m85) * rtranspose [1,0] (rreplicate 2 m31)) ; m36 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m22 * m22) * rslice 0 2 m30 ; m38 = rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 m36))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 m34))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m86) * rtranspose [1,0] (rreplicate 2 m31))) (rreplicate 0 (rreplicate 2 0.0))) ; m39 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * rslice 2 2 m38 ; m42 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * rsum (rtranspose [1,2,0] (rreplicate 2 m85) * rtranspose [1,0] (rreplicate 2 m39)) ; m44 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * rslice 0 2 m38 in [rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m44)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m42)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m36)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m34)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m44)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m42)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m20)) * rtranspose [2,1,0] (rreplicate 2 m36)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m20)) * rtranspose [2,1,0] (rreplicate 2 m34)), rsum (rtranspose [1,0] m44) + rsum (rtranspose [1,0] m42) + rsum (rtranspose [1,0] m36) + rsum (rtranspose [1,0] m34), rsum (rtranspose [2,0,1] (rreplicate 2 m16) * rtranspose [2,1,0] (rreplicate 2 m39)) + rsum (rtranspose [2,0,1] (rreplicate 2 m24) * rtranspose [2,1,0] (rreplicate 2 m31)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m39)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m20)) * rtranspose [2,1,0] (rreplicate 2 m31)), rsum (rtranspose [1,0] m39) + rsum (rtranspose [1,0] m31), rsum (rtranspose [2,0,1] (rreplicate 10 m27) * rtranspose [2,1,0] (rreplicate 2 m29)), rsum (rtranspose [1,0] m29)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m110 m111 v112 m113 m114 v115 m116 v117 -> let m20 = rappend (tanh (rtranspose [1,0] (rreplicate 2 v112) + rsum (rtranspose [2,1,0] (rreplicate 2 m110) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m111) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) (tanh (rtranspose [1,0] (rreplicate 2 v115) + rsum (rtranspose [2,1,0] (rreplicate 2 m113) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v112) + rsum (rtranspose [2,1,0] (rreplicate 2 m110) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m111) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m114) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) in rsum (rtranspose [2,1,0] (rreplicate 2 m116) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 2 v115) + rsum (rtranspose [2,1,0] (rreplicate 2 m113) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v112) + rsum (rtranspose [2,1,0] (rreplicate 2 m110) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m111) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m20))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m114) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m20))))))) + rtranspose [1,0] (rreplicate 2 v117)"
