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
    @?= "\\m38 m47 m48 v49 m50 m51 v52 m53 v54 -> let m11 = rreshape [2,1] (rreplicate 2 0.0) ; m18 = tanh (rtranspose [1,0] (rreplicate 1 v49) + rsum (rtranspose [2,1,0] (rreplicate 1 m47) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m48) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m11)))) ; m26 = tanh (rtranspose [1,0] (rreplicate 1 v49) + rsum (rtranspose [2,1,0] (rreplicate 1 m47) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m48) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m11)))) ; m33 = tanh (rtranspose [1,0] (rreplicate 1 v52) + rsum (rtranspose [2,1,0] (rreplicate 1 m50) * rtranspose [1,0] (rreplicate 1 m26)) + rsum (rtranspose [2,1,0] (rreplicate 1 m51) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m11)))) ; t36 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m18 m33))) ; m39 = rappend (rreshape [1,1] (rreplicate 1 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m53) * rtranspose [1,0] (rreplicate 1 m38))) (rreshape [0,1] (rreplicate 0 0.0))) ; m40 = (rconst (rfromListLinear [1,1] [1.0]) - m33 * m33) * rslice 1 1 m39 ; m43 = (rconst (rfromListLinear [1,1] [1.0]) - m26 * m26) * rsum (rtranspose [1,2,0] (rreplicate 1 m50) * rtranspose [1,0] (rreplicate 1 m40)) ; m45 = (rconst (rfromListLinear [1,1] [1.0]) - m18 * m18) * rslice 0 1 m39 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m45)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m43)), rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 0 1 m11)) * rtranspose [2,1,0] (rreplicate 1 m45)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 0 1 m11)) * rtranspose [2,1,0] (rreplicate 1 m43)), rsum (rtranspose [1,0] m45) + rsum (rtranspose [1,0] m43), rsum (rtranspose [2,0,1] (rreplicate 1 m26) * rtranspose [2,1,0] (rreplicate 1 m40)), rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 1 1 m11)) * rtranspose [2,1,0] (rreplicate 1 m40)), rsum (rtranspose [1,0] m40), rsum (rtranspose [2,1,0] (t36 * rreplicate 1 m38)), rsum (rtranspose [1,0] m38)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m223 m224 v225 m226 m227 v228 m229 v230 -> let m11 = rreshape [2,1] (rreplicate 2 0.0) ; m18 = tanh (rtranspose [1,0] (rreplicate 1 v225) + rsum (rtranspose [2,1,0] (rreplicate 1 m223) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m224) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m11)))) ; m26 = tanh (rtranspose [1,0] (rreplicate 1 v225) + rsum (rtranspose [2,1,0] (rreplicate 1 m223) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m224) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m11)))) ; m33 = tanh (rtranspose [1,0] (rreplicate 1 v228) + rsum (rtranspose [2,1,0] (rreplicate 1 m226) * rtranspose [1,0] (rreplicate 1 m26)) + rsum (rtranspose [2,1,0] (rreplicate 1 m227) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m11)))) ; t36 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m18 m33))) in rsum (rtranspose [2,1,0] (rreplicate 1 m229) * t36) + rtranspose [1,0] (rreplicate 1 v230)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m38 m573 m574 v575 m576 m577 v578 m579 v580 -> let m18 = tanh (rtranspose [1,0] (rreplicate 1 v575) + rsum (rtranspose [2,1,0] (rreplicate 1 m573) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m574) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m26 = tanh (rtranspose [1,0] (rreplicate 1 v575) + rsum (rtranspose [2,1,0] (rreplicate 1 m573) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m574) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m33 = tanh (rtranspose [1,0] (rreplicate 1 v578) + rsum (rtranspose [2,1,0] (rreplicate 1 m576) * rtranspose [1,0] (rreplicate 1 m26)) + rsum (rtranspose [2,1,0] (rreplicate 1 m577) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m39 = rappend (rconst (rfromListLinear [1,1] [0.0])) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m579) * rtranspose [1,0] (rreplicate 1 m38))) (rreplicate 0 (rreplicate 1 0.0))) ; m40 = (rconst (rfromListLinear [1,1] [1.0]) - m33 * m33) * rslice 1 1 m39 ; m43 = (rconst (rfromListLinear [1,1] [1.0]) - m26 * m26) * rsum (rtranspose [1,2,0] (rreplicate 1 m576) * rtranspose [1,0] (rreplicate 1 m40)) ; m45 = (rconst (rfromListLinear [1,1] [1.0]) - m18 * m18) * rslice 0 1 m39 in [rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m45)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m43)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m45)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m43)), rsum (rtranspose [1,0] m45) + rsum (rtranspose [1,0] m43), rsum (rtranspose [2,0,1] (rreplicate 1 m26) * rtranspose [2,1,0] (rreplicate 1 m40)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m40)), rsum (rtranspose [1,0] m40), rsum (rtranspose [2,0,1] (rreplicate 10 m33) * rtranspose [2,1,0] (rreplicate 1 m38)), rsum (rtranspose [1,0] m38)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m755 m756 v757 m758 m759 v760 m761 v762 -> rsum (rtranspose [2,1,0] (rreplicate 1 m761) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 1 v760) + rsum (rtranspose [2,1,0] (rreplicate 1 m758) * rtranspose [1,0] (rreplicate 1 (tanh (rtranspose [1,0] (rreplicate 1 v757) + rsum (rtranspose [2,1,0] (rreplicate 1 m755) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m756) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 1 m759) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rtranspose [1,0] (rreplicate 1 v762)"

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
    @?= "\\m62 m79 m80 v81 m82 m83 v84 m85 v86 -> let m12 = rreshape [4,2] (rreplicate 8 0.0) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 v81) + rsum (rtranspose [2,1,0] (rreplicate 2 m79) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m27 = tanh (rtranspose [1,0] (rreplicate 2 v81) + rsum (rtranspose [2,1,0] (rreplicate 2 m79) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m34 = tanh (rtranspose [1,0] (rreplicate 2 v84) + rsum (rtranspose [2,1,0] (rreplicate 2 m82) * rtranspose [1,0] (rreplicate 2 m27)) + rsum (rtranspose [2,1,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)))) ; m35 = rappend m19 m34 ; m42 = tanh (rtranspose [1,0] (rreplicate 2 v81) + rsum (rtranspose [2,1,0] (rreplicate 2 m79) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m35)))) ; m50 = tanh (rtranspose [1,0] (rreplicate 2 v81) + rsum (rtranspose [2,1,0] (rreplicate 2 m79) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m35)))) ; m57 = tanh (rtranspose [1,0] (rreplicate 2 v84) + rsum (rtranspose [2,1,0] (rreplicate 2 m82) * rtranspose [1,0] (rreplicate 2 m50)) + rsum (rtranspose [2,1,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m35)))) ; t60 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m42 m57))) ; m63 = rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m85) * rtranspose [1,0] (rreplicate 2 m62))) (rreshape [0,2] (rreplicate 0 0.0))) ; m64 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m57 * m57) * rslice 2 2 m63 ; m67 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m50 * m50) * rsum (rtranspose [1,2,0] (rreplicate 2 m82) * rtranspose [1,0] (rreplicate 2 m64)) ; m69 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m42 * m42) * rslice 0 2 m63 ; m71 = rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 m69))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 m67))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 m64))) (rreshape [0,2] (rreplicate 0 0.0))) ; m72 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m34 * m34) * rslice 2 2 m71 ; m75 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m27 * m27) * rsum (rtranspose [1,2,0] (rreplicate 2 m82) * rtranspose [1,0] (rreplicate 2 m72)) ; m77 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * rslice 0 2 m71 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m77)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m75)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m69)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m67)), rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m77)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m75)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m35)) * rtranspose [2,1,0] (rreplicate 2 m69)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m35)) * rtranspose [2,1,0] (rreplicate 2 m67)), rsum (rtranspose [1,0] m77) + rsum (rtranspose [1,0] m75) + rsum (rtranspose [1,0] m69) + rsum (rtranspose [1,0] m67), rsum (rtranspose [2,0,1] (rreplicate 2 m27) * rtranspose [2,1,0] (rreplicate 2 m72)) + rsum (rtranspose [2,0,1] (rreplicate 2 m50) * rtranspose [2,1,0] (rreplicate 2 m64)), rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m72)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m35)) * rtranspose [2,1,0] (rreplicate 2 m64)), rsum (rtranspose [1,0] m72) + rsum (rtranspose [1,0] m64), rsum (rtranspose [2,1,0] (t60 * rreplicate 2 m62)), rsum (rtranspose [1,0] m62)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m399 m400 v401 m402 m403 v404 m405 v406 -> let m12 = rreshape [4,2] (rreplicate 8 0.0) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 v401) + rsum (rtranspose [2,1,0] (rreplicate 2 m399) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m400) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m27 = tanh (rtranspose [1,0] (rreplicate 2 v401) + rsum (rtranspose [2,1,0] (rreplicate 2 m399) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m400) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m34 = tanh (rtranspose [1,0] (rreplicate 2 v404) + rsum (rtranspose [2,1,0] (rreplicate 2 m402) * rtranspose [1,0] (rreplicate 2 m27)) + rsum (rtranspose [2,1,0] (rreplicate 2 m403) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)))) ; m35 = rappend m19 m34 ; m42 = tanh (rtranspose [1,0] (rreplicate 2 v401) + rsum (rtranspose [2,1,0] (rreplicate 2 m399) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m400) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m35)))) ; m50 = tanh (rtranspose [1,0] (rreplicate 2 v401) + rsum (rtranspose [2,1,0] (rreplicate 2 m399) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m400) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m35)))) ; m57 = tanh (rtranspose [1,0] (rreplicate 2 v404) + rsum (rtranspose [2,1,0] (rreplicate 2 m402) * rtranspose [1,0] (rreplicate 2 m50)) + rsum (rtranspose [2,1,0] (rreplicate 2 m403) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m35)))) ; t60 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m42 m57))) in rsum (rtranspose [2,1,0] (rreplicate 2 m405) * t60) + rtranspose [1,0] (rreplicate 2 v406)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m62 m1051 m1052 v1053 m1054 m1055 v1056 m1057 v1058 -> let m19 = tanh (rtranspose [1,0] (rreplicate 2 v1053) + rsum (rtranspose [2,1,0] (rreplicate 2 m1051) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m27 = tanh (rtranspose [1,0] (rreplicate 2 v1053) + rsum (rtranspose [2,1,0] (rreplicate 2 m1051) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m34 = tanh (rtranspose [1,0] (rreplicate 2 v1056) + rsum (rtranspose [2,1,0] (rreplicate 2 m1054) * rtranspose [1,0] (rreplicate 2 m27)) + rsum (rtranspose [2,1,0] (rreplicate 2 m1055) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m35 = rappend m19 m34 ; m42 = tanh (rtranspose [1,0] (rreplicate 2 v1053) + rsum (rtranspose [2,1,0] (rreplicate 2 m1051) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m35)))) ; m50 = tanh (rtranspose [1,0] (rreplicate 2 v1053) + rsum (rtranspose [2,1,0] (rreplicate 2 m1051) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m35)))) ; m57 = tanh (rtranspose [1,0] (rreplicate 2 v1056) + rsum (rtranspose [2,1,0] (rreplicate 2 m1054) * rtranspose [1,0] (rreplicate 2 m50)) + rsum (rtranspose [2,1,0] (rreplicate 2 m1055) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m35)))) ; m63 = rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m1057) * rtranspose [1,0] (rreplicate 2 m62))) (rreplicate 0 (rreplicate 2 0.0))) ; m64 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m57 * m57) * rslice 2 2 m63 ; m67 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m50 * m50) * rsum (rtranspose [1,2,0] (rreplicate 2 m1054) * rtranspose [1,0] (rreplicate 2 m64)) ; m69 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m42 * m42) * rslice 0 2 m63 ; m71 = rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 m69))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 m67))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m1055) * rtranspose [1,0] (rreplicate 2 m64))) (rreplicate 0 (rreplicate 2 0.0))) ; m72 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m34 * m34) * rslice 2 2 m71 ; m75 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m27 * m27) * rsum (rtranspose [1,2,0] (rreplicate 2 m1054) * rtranspose [1,0] (rreplicate 2 m72)) ; m77 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * rslice 0 2 m71 in [rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m77)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m75)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m69)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m67)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m77)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m75)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m35)) * rtranspose [2,1,0] (rreplicate 2 m69)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m35)) * rtranspose [2,1,0] (rreplicate 2 m67)), rsum (rtranspose [1,0] m77) + rsum (rtranspose [1,0] m75) + rsum (rtranspose [1,0] m69) + rsum (rtranspose [1,0] m67), rsum (rtranspose [2,0,1] (rreplicate 2 m27) * rtranspose [2,1,0] (rreplicate 2 m72)) + rsum (rtranspose [2,0,1] (rreplicate 2 m50) * rtranspose [2,1,0] (rreplicate 2 m64)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m72)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m35)) * rtranspose [2,1,0] (rreplicate 2 m64)), rsum (rtranspose [1,0] m72) + rsum (rtranspose [1,0] m64), rsum (rtranspose [2,0,1] (rreplicate 10 m57) * rtranspose [2,1,0] (rreplicate 2 m62)), rsum (rtranspose [1,0] m62)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1391 m1392 v1393 m1394 m1395 v1396 m1397 v1398 -> let m35 = rappend (tanh (rtranspose [1,0] (rreplicate 2 v1393) + rsum (rtranspose [2,1,0] (rreplicate 2 m1391) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1392) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) (tanh (rtranspose [1,0] (rreplicate 2 v1396) + rsum (rtranspose [2,1,0] (rreplicate 2 m1394) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v1393) + rsum (rtranspose [2,1,0] (rreplicate 2 m1391) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1392) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1395) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) in rsum (rtranspose [2,1,0] (rreplicate 2 m1397) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 2 v1396) + rsum (rtranspose [2,1,0] (rreplicate 2 m1394) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v1393) + rsum (rtranspose [2,1,0] (rreplicate 2 m1391) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1392) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m35))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1395) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m35))))))) + rtranspose [1,0] (rreplicate 2 v1398)"
