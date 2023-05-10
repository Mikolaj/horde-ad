module TestMnistRNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Compose
import           Data.List.Index (imap)
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Domains
import HordeAd.Core.DualNumber (ADTensor, ADVal, dDnotShared)
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.External.Optimizer
import HordeAd.External.OptimizerTools

import EqEpsilon

import           MnistData
import qualified MnistRnnRanked2

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNA
            , tensorADValMnistTestsRNNI
            , tensorADValMnistTestsRNNO
            ]

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCaseRNNA
  :: forall r.
     ( ADTensor r, ADReady r, ADReady (ADVal r)
     , Primal (ADVal r) ~ r, Primal r ~ r, Value r ~ r, Floating (Vector r)
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , Ranked (ADVal r) ~ Compose ADVal (Flip OR.Array r)
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width batchSize expected =
  let nParams1 = MnistRnnRanked2.rnnMnistLenR width
      params1Init =
        imap (\i sh -> OD.fromVector sh
                       $ V.map realToFrac
                       $ (LA.randomVector (44 + product sh + i) LA.Uniform
                                          (product sh)
                          - LA.scalar 0.5) * LA.scalar 0.4)
             nParams1
      parametersInit = mkDoms (dfromR $ tconst emptyR)
                              (fromListDoms params1Init)
      emptyR = OR.fromList [0] []
      emptyR2 = OR.fromList [0, 0] []
      valsInit = ( (emptyR2, emptyR2, emptyR)
                 , (emptyR2, emptyR2, emptyR)
                 , (emptyR2, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show batchSize
                        , show (length nParams1)
                        , show (sum $ map product nParams1) ]
      ftest :: Int -> MnistDataBatchR r -> Domains r -> r
      ftest batchSize' mnist testParams =
        MnistRnnRanked2.rnnMnistTestR batchSize' mnist
          (\f -> runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: (Domains r, StateAdam r)
                    -> (Int, [MnistDataR r])
                    -> IO (Domains r, StateAdam r)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADVal r) -> ADVal r
                 f (glyphR, labelR) adinputs =
                   MnistRnnRanked2.rnnMnistLossFusedR
                     batchSize (tconst glyphR, tconst labelR)
                               (parseDomains valsInit adinputs)
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch >= batchSize)
                          $ chunksOf batchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (batchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf (10 * batchSize) trainDataShuffled
             !res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
       let testErrorFinal = 1 - ftest (batchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

tensorADValMnistTestsRNNA :: TestTree
tensorADValMnistTestsRNNA = testGroup "RNN ADVal MNIST tests"
  [ mnistTestCaseRNNA "RNNA 1 epoch, 1 batch" 1 1 32 4
                       (1 :: Double)
  , mnistTestCaseRNNA "RNNA artificial 1 2 3 4 5" 2 3 4 5
                       (0.93333334 :: Float)
  , mnistTestCaseRNNA "RNNA artificial 5 4 3 2 1" 5 4 3 2
                       (0.875 :: Double)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCaseRNNI
  :: forall r.
     ( ADTensor r, ADReady r, InterpretAst (ADVal r)
     , Value r ~ r, Value (ADVal r) ~ r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , Primal r ~ r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width batchSize expected =
  let nParams1 = MnistRnnRanked2.rnnMnistLenR width
      params1Init =
        imap (\i sh -> OD.fromVector sh
                       $ V.map realToFrac
                       $ (LA.randomVector (44 + product sh + i) LA.Uniform
                                          (product sh)
                          - LA.scalar 0.5) * LA.scalar 0.4)
             nParams1
      parametersInit = mkDoms (dfromR $ tconst emptyR)
                              (fromListDoms params1Init)
      emptyR = OR.fromList [0] []
      emptyR2 = OR.fromList [0, 0] []
      valsInit = ( (emptyR2, emptyR2, emptyR)
                 , (emptyR2, emptyR2, emptyR)
                 , (emptyR2, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show batchSize
                        , show (length nParams1)
                        , show (sum $ map product nParams1) ]
      ftest :: Int -> MnistDataBatchR r -> Domains r -> r
      ftest batchSize' mnist testParams =
        MnistRnnRanked2.rnnMnistTestR batchSize' mnist
          (\f -> runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           shapes1 = nParams1
           (vars1, asts1) = unzip $ map funToAstD shapes1
           doms = mkDoms (dfromR $ AstConst emptyR) (fromListDoms asts1)
           (varGlyph, astGlyph) =
             funToAstR
               (batchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS) id
           (varLabel, astLabel) =
             funToAstR (batchSize :$ sizeMnistLabelInt :$ ZS) id
           ast :: Ast 0 r
           ast = tscalar
                 $ MnistRnnRanked2.rnnMnistLossFusedR
                     batchSize (tprimalPart astGlyph, tprimalPart astLabel)
                               (parseDomains valsInit doms)
           runBatch :: (Domains r, StateAdam r)
                    -> (Int, [MnistDataR r])
                    -> IO (Domains r, StateAdam r)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADVal r) -> ADVal r
                 f (glyph, label) varInputs =
                   let env1 = foldr extendEnvD EM.empty
                              $ zip vars1 $ V.toList
                              $ V.zipWith (dDnotShared emptyADShare)
                                          (inputPrimal1 varInputs)
                                          (inputDual1 varInputs)
                       envMnist = extendEnvR varGlyph (tconst glyph)
                                  $ extendEnvR varLabel (tconst label) env1
                   in tunScalar $ snd $ interpretAst envMnist emptyMemo ast
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch >= batchSize)
                          $ chunksOf batchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (batchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf (10 * batchSize) trainDataShuffled
             !res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
       let testErrorFinal = 1 - ftest (batchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

tensorADValMnistTestsRNNI :: TestTree
tensorADValMnistTestsRNNI = testGroup "RNN Intermediate MNIST tests"
  [ mnistTestCaseRNNI "RNNI 1 epoch, 1 batch" 1 1 32 4
                       (1 :: Double)
  , mnistTestCaseRNNI "RNNI artificial 1 2 3 4 5" 2 3 4 5
                       (0.93333334 :: Float)
  , mnistTestCaseRNNI "RNNI artificial 5 4 3 2 1" 5 4 3 2
                       (0.875 :: Double)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCaseRNNO
  :: forall r.
     ( ADTensor r, ADReady r, Value r ~ r, InterpretAst r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , Primal r ~ r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNO prefix epochs maxBatches width batchSize expected =
  let nParams1 = MnistRnnRanked2.rnnMnistLenR width
      params1Init =
        imap (\i sh -> OD.fromVector sh
                       $ V.map realToFrac
                       $ (LA.randomVector (44 + product sh + i) LA.Uniform
                                          (product sh)
                          - LA.scalar 0.5) * LA.scalar 0.4)
             nParams1
      parametersInit = mkDoms (dfromR $ tconst emptyR)
                              (fromListDoms params1Init)
      emptyR = OR.fromList [0] []
      emptyR2 = OR.fromList [0, 0] []
      valsInit = ( (emptyR2, emptyR2, emptyR)
                 , (emptyR2, emptyR2, emptyR)
                 , (emptyR2, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show batchSize
                        , show (length nParams1)
                        , show (sum $ map product nParams1) ]
      ftest :: Int -> MnistDataBatchR r -> Domains r -> r
      ftest batchSize' mnist testParams =
        MnistRnnRanked2.rnnMnistTestR batchSize' mnist
          (\f -> runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           shapes1 = nParams1
           (varGlyph, astGlyph) =
             funToAstR
               (batchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS) id
           (varLabel, astLabel) =
             funToAstR (batchSize :$ sizeMnistLabelInt :$ ZS) id
           envInit = extendEnvR varGlyph (tconstant astGlyph)
                     $ extendEnvR varLabel (tconstant astLabel) EM.empty
           f = tscalar
               . MnistRnnRanked2.rnnMnistLossFusedR
                   batchSize (tprimalPart astGlyph, tprimalPart astLabel)
           (((var0Again, varDtAgain, vars1Again), gradientRaw, primal), _) =
             revAstOnDomainsFun 0 shapes1 $ revDtInterpret envInit valsInit f
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain =
             vars1Again
             ++ [AstDynamicVarName varGlyph, AstDynamicVarName varLabel]
           vars = (var0Again, varDtAgain, vars1AndInputAgain)
           go :: [MnistDataBatchR r] -> (Domains r, StateAdam r)
              -> (Domains r, StateAdam r)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (parameters, stateAdam) =
             let glyphD = dfromR $ tconst glyph
                 labelD = dfromR $ tconst label
                 parametersAndInput =
                   concatDomsR [parameters, fromListDoms [glyphD, labelD]]
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientDomain)
           runBatch :: (Domains r, StateAdam r)
                    -> (Int, [MnistDataR r])
                    -> IO (Domains r, StateAdam r)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map packBatchR
                          $ filter (\ch -> length ch >= batchSize)
                          $ chunksOf batchSize chunk
                 res@(parameters2, _) = go chunkR (parameters, stateAdam)
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (batchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf (10 * batchSize) trainDataShuffled
             !res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
       let testErrorFinal = 1 - ftest (batchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

tensorADValMnistTestsRNNO :: TestTree
tensorADValMnistTestsRNNO = testGroup "RNN Once MNIST tests"
  [ mnistTestCaseRNNO "RNNO 1 epoch, 1 batch" 1 1 32 4
                       (1.0 :: Double)
  , mnistTestCaseRNNO "RNNO artificial 1 2 3 4 5" 2 3 4 5
                       (0.93333334 :: Float)
  , mnistTestCaseRNNO "RNNO artificial 5 4 3 2 1" 5 4 3 2
                       (0.875 :: Double)
  ]
