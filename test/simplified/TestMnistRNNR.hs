module TestMnistRNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.List.Index (imap)
import qualified Data.Strict.IntMap as IM
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
import HordeAd.Core.AstTools
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
            , tensorMnistTestsPP
            ]

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCaseRNNA
  :: forall r.
     ( ADTensor r, ADReady r, ADReady (ADVal r)
     , Primal (ADVal r) ~ r, Primal r ~ r, Value r ~ r, Floating (Vector r)
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
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
                        , show width, show miniBatchSize
                        , show (length nParams1)
                        , show (sum $ map product nParams1) ]
      ftest :: Int -> MnistDataBatchR r -> Domains r -> r
      ftest miniBatchSize' mnist testParams =
        MnistRnnRanked2.rnnMnistTestR miniBatchSize' mnist
          (\f -> runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: (Domains r, StateAdam r)
                    -> (Int, [MnistDataR r])
                    -> IO (Domains r, StateAdam r)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADVal r) -> ADVal r
                 f (glyphR, labelR) adinputs =
                   MnistRnnRanked2.rnnMnistLossFusedR
                     miniBatchSize (tconst glyphR, tconst labelR)
                               (parseDomains valsInit adinputs)
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
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNA
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNA :: TestTree
tensorADValMnistTestsRNNA = testGroup "RNN ADVal MNIST tests"
  [ mnistTestCaseRNNA "RNNA 1 epoch, 1 batch" 1 1 128 5 5
                       (0.8 :: Double)
  , mnistTestCaseRNNA "RNNA artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNA "RNNA artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8775510204081632 :: Double)
  , mnistTestCaseRNNA "RNNA 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
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
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
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
                        , show width, show miniBatchSize
                        , show (length nParams1)
                        , show (sum $ map product nParams1) ]
      ftest :: Int -> MnistDataBatchR r -> Domains r -> r
      ftest miniBatchSize' mnist testParams =
        MnistRnnRanked2.rnnMnistTestR miniBatchSize' mnist
          (\f -> runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           shapes1 = nParams1
           (vars1, asts1) = unzip $ map funToAstD shapes1
           doms = mkDoms (dfromR $ AstConst emptyR) (fromListDoms asts1)
           (varGlyph, astGlyph) =
             funToAstR
               (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
               id
           (varLabel, astLabel) =
             funToAstR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
           ast :: Ast 0 r
           ast = tscalar
                 $ MnistRnnRanked2.rnnMnistLossFusedR
                     miniBatchSize (tprimalPart astGlyph, tprimalPart astLabel)
                                   (parseDomains valsInit doms)
           runBatch :: (Domains r, StateAdam r)
                    -> (Int, [MnistDataR r])
                    -> IO (Domains r, StateAdam r)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
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
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
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
                       (0.92 :: Double)
  , mnistTestCaseRNNI "RNNI artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNI "RNNI artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8775510204081632 :: Double)
  , mnistTestCaseRNNI "RNNI 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCaseRNNO
  :: forall r.
     ( ADTensor r, ADReady r, Value r ~ r, InterpretAst r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , Primal r ~ r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNO prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
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
                        , show width, show miniBatchSize
                        , show (length nParams1)
                        , show (sum $ map product nParams1) ]
      ftest :: Int -> MnistDataBatchR r -> Domains r -> r
      ftest miniBatchSize' mnist testParams =
        MnistRnnRanked2.rnnMnistTestR miniBatchSize' mnist
          (\f -> runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           shapes1 = nParams1
           (varGlyph, astGlyph) =
             funToAstR
               (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
               id
           (varLabel, astLabel) =
             funToAstR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
           envInit = extendEnvR varGlyph (tconstant astGlyph)
                     $ extendEnvR varLabel (tconstant astLabel) EM.empty
           f = tscalar
               . MnistRnnRanked2.rnnMnistLossFusedR
                   miniBatchSize (tprimalPart astGlyph, tprimalPart astLabel)
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
           go ((glyph, label) : rest) !(!parameters, !stateAdam) =
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
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
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
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNO
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNO :: TestTree
tensorADValMnistTestsRNNO = testGroup "RNN Once MNIST tests"
  [ mnistTestCaseRNNO "RNNO 1 epoch, 1 batch" 1 1 128 5 50
                       (0.92 :: Double)
  , mnistTestCaseRNNO "RNNO artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNO "RNNO artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8775510204081632 :: Double)
  , mnistTestCaseRNNO "RNNO 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for RNN MNIST tests"
  [ testCase "RNNOPP" testRNNOPP
  , testCase "RNNOPP2" testRNNOPP2
  ]

valsInitRNNOPP
  :: Int -> Int
  -> ( ( OR.Array 2 Double
       , OR.Array 2 Double
       , OR.Array 1 Double )
     , ( OR.Array 2 Double
       , OR.Array 2 Double
       , OR.Array 1 Double )
     , ( OR.Array 2 Double
       , OR.Array 1 Double )
     )
valsInitRNNOPP out_width sizeMnistHeightI =
  ( ( OR.fromList [out_width, sizeMnistHeightI]
                  (map fromIntegral [0 .. out_width * sizeMnistHeightI - 1])
    , OR.fromList [out_width, out_width]
                  (map fromIntegral [0 .. out_width * out_width - 1])
    , OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( OR.fromList [out_width, out_width]
                  (map fromIntegral [0 .. out_width * out_width - 1])
    , OR.fromList [out_width, out_width]
                  (map fromIntegral [0 .. out_width * out_width - 1])
    , OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( OR.fromList [sizeMnistLabelInt, out_width]
                  (map fromIntegral [0 .. sizeMnistLabelInt * out_width - 1])
    , OR.fromList [sizeMnistLabelInt]
                  (map fromIntegral [0 .. sizeMnistLabelInt - 1]) ) )

testRNNOPP :: Assertion
testRNNOPP = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 1
      sizeMnistWidthI = 1
      sizeMnistHeightI = 1
      blackGlyph :: AstPrimalPartRanked Double 3
      blackGlyph = AstPrimalPart
                   $ AstKonst sizeMnistWidthI
                   $ AstKonst sizeMnistHeightI
                   $ AstKonst batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (Ast0 Double)
              -> TensorOf 2 (Ast0 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifact6, _) = revDtFun afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret m3 m4 v5 m6 m7 v8 m9 v10 -> let m12 = treshape [2,1] (tkonst 2 (tconst 0.0)) ; t13 = ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0))) ! [0])) ; t14 = ttranspose [1,0] (tkonst 1 (tslice 0 1 m12)) ; m15 = tanh (ttranspose [1,0] (tkonst 1 v5) + tsum (ttranspose [2,1,0] (tkonst 1 m3) * t13) + tsum (ttranspose [2,1,0] (tkonst 1 m4) * t14)) ; t16 = ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0))) ! [0])) ; t17 = ttranspose [1,0] (tkonst 1 (tslice 0 1 m12)) ; m18 = tanh (ttranspose [1,0] (tkonst 1 v5) + tsum (ttranspose [2,1,0] (tkonst 1 m3) * t16) + tsum (ttranspose [2,1,0] (tkonst 1 m4) * t17)) ; t19 = ttranspose [1,0] (tkonst 1 (tslice 1 1 m12)) ; m20 = tanh (ttranspose [1,0] (tkonst 1 v8) + tsum (ttranspose [2,1,0] (tkonst 1 m6) * ttranspose [1,0] (tkonst 1 m18)) + tsum (ttranspose [2,1,0] (tkonst 1 m7) * t19)) ; t21 = ttranspose [1,0] (tkonst 10 (tslice 1 1 (tappend m15 m20))) ; m22 = tappend (treshape [1,1] (tkonst 1 (tconst 0.0))) (tappend (tsum (ttranspose [1,0] (ttranspose [2,1,0] (tkonst 1 m9) * tkonst 1 dret))) (treshape [0,1] (tkonst 0 (tconst 0.0)))) ; m23 = (treshape [1,1] (tkonst 1 (tconst 1.0)) - m20 * m20) * tslice 1 1 m22 ; m24 = (treshape [1,1] (tkonst 1 (tconst 1.0)) - m18 * m18) * tsum (ttranspose [1,0] (ttranspose [2,1,0] (tkonst 1 m6) * tkonst 1 m23)) ; m25 = (treshape [1,1] (tkonst 1 (tconst 1.0)) - m15 * m15) * tslice 0 1 m22 in (tfromList [], tsum (ttranspose [2,1,0] (t13 * tkonst 1 m25)) + tsum (ttranspose [2,1,0] (t16 * tkonst 1 m24)), tsum (ttranspose [2,1,0] (t14 * tkonst 1 m25)) + tsum (ttranspose [2,1,0] (t17 * tkonst 1 m24)), tsum (ttranspose [1,0] m25) + tsum (ttranspose [1,0] m24), tsum (ttranspose [2,1,0] (ttranspose [1,0] (tkonst 1 m18) * tkonst 1 m23)), tsum (ttranspose [2,1,0] (t19 * tkonst 1 m23)), tsum (ttranspose [1,0] m23), tsum (ttranspose [2,1,0] (t21 * tkonst 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 m3 m4 v5 m6 m7 v8 m9 v10 -> let m12 = treshape [2,1] (tkonst 2 (tconst 0.0)) ; m13 = ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0))) ! [0])) ; m14 = ttranspose [1,0] (tkonst 1 (tslice 0 1 m12)) ; m15 = tanh (ttranspose [1,0] (tkonst 1 v5) + tsum (ttranspose [2,1,0] (tkonst 1 m3) * t13) + tsum (ttranspose [2,1,0] (tkonst 1 m4) * t14)) ; m16 = ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0))) ! [0])) ; m17 = ttranspose [1,0] (tkonst 1 (tslice 0 1 m12)) ; m18 = tanh (ttranspose [1,0] (tkonst 1 v5) + tsum (ttranspose [2,1,0] (tkonst 1 m3) * t16) + tsum (ttranspose [2,1,0] (tkonst 1 m4) * t17)) ; m19 = ttranspose [1,0] (tkonst 1 (tslice 1 1 m12)) ; m20 = tanh (ttranspose [1,0] (tkonst 1 v8) + tsum (ttranspose [2,1,0] (tkonst 1 m6) * ttranspose [1,0] (tkonst 1 m18)) + tsum (ttranspose [2,1,0] (tkonst 1 m7) * t19)) ; m21 = ttranspose [1,0] (tkonst 10 (tslice 1 1 (tappend m15 m20))) in tsum (ttranspose [2,1,0] (tkonst 1 m9) * t21) + ttranspose [1,0] (tkonst 1 v10)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret m3 m4 v5 m6 m7 v8 m9 v10 -> let m15 = tanh (ttranspose [1,0] (tkonst 1 v5) + tsum (ttranspose [2,1,0] (tkonst 1 m3) * tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 1 m4) * tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 0.0))))))) ; m18 = tanh (ttranspose [1,0] (tkonst 1 v5) + tsum (ttranspose [2,1,0] (tkonst 1 m3) * tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 1 m4) * tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 0.0))))))) ; m20 = tanh (ttranspose [1,0] (tkonst 1 v8) + tsum (ttranspose [2,1,0] (tkonst 1 m6) * ttranspose [1,0] (tkonst 1 m18)) + tsum (ttranspose [2,1,0] (tkonst 1 m7) * tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 0.0))))))) ; m22 = tappend (tconstant (tkonst 1 (tkonst 1 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (tkonst 1 m9) * ttranspose [1,0] (tkonst 1 dret))) (tconstant (tkonst 0 (tkonst 1 (tconst 0.0))))) ; m23 = (tconstant (tkonst 1 (tkonst 1 (tconst 1.0))) - m20 * m20) * tslice 1 1 m22 ; m24 = (tconstant (tkonst 1 (tkonst 1 (tconst 1.0))) - m18 * m18) * tsum (ttranspose [1,2,0] (tkonst 1 m6) * ttranspose [1,0] (tkonst 1 m23)) ; m25 = (tconstant (tkonst 1 (tkonst 1 (tconst 1.0))) - m15 * m15) * tslice 0 1 m22 in (tfromList [], tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0))))) * tkonst 1 m25)) + tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0))))) * tkonst 1 m24)), tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 0.0))))) * tkonst 1 m25)) + tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 0.0))))) * tkonst 1 m24)), tsum (ttranspose [1,0] m25) + tsum (ttranspose [1,0] m24), tsum (ttranspose [2,0,1] (tkonst 1 m18) * ttranspose [2,1,0] (tkonst 1 m23)), tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 0.0))))) * tkonst 1 m23)), tsum (ttranspose [1,0] m23), tsum (ttranspose [2,0,1] (tkonst 10 m20) * ttranspose [2,1,0] (tkonst 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 m3 m4 v5 m6 m7 v8 m9 v10 -> tsum (ttranspose [2,1,0] (tkonst 1 m9) * ttranspose [1,0] (tkonst 10 (tanh (ttranspose [1,0] (tkonst 1 v8) + tsum (ttranspose [2,1,0] (tkonst 1 m6) * ttranspose [1,0] (tkonst 1 (tanh (ttranspose [1,0] (tkonst 1 v5) + tsum (ttranspose [2,1,0] (tkonst 1 m3) * tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 1 m4) * tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 0.0)))))))))) + tsum (ttranspose [2,1,0] (tkonst 1 m7) * tconstant (ttranspose [1,0] (tkonst 1 (tkonst 1 (tkonst 1 (tconst 0.0)))))))))) + ttranspose [1,0] (tkonst 1 v10)"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistWidthI = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstPrimalPartRanked Double 3
      blackGlyph = AstPrimalPart
                   $ AstKonst sizeMnistWidthI
                   $ AstKonst sizeMnistHeightI
                   $ AstKonst batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (Ast0 Double)
              -> TensorOf 2 (Ast0 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifact6, _) = revDtFun afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret m3 m4 v5 m6 m7 v8 m9 v10 -> let m13 = treshape [4,2] (tkonst 8 (tconst 0.0)) ; t14 = ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))) ! [0])) ; t15 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m13)) ; m16 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * t14) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t15)) ; t17 = ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))) ! [0])) ; t18 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m13)) ; m19 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * t17) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t18)) ; t20 = ttranspose [1,0] (tkonst 2 (tslice 2 2 m13)) ; m21 = tanh (ttranspose [1,0] (tkonst 2 v8) + tsum (ttranspose [2,1,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 m19)) + tsum (ttranspose [2,1,0] (tkonst 2 m7) * t20)) ; m22 = tappend m16 m21 ; t23 = ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))) ! [1])) ; t24 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m22)) ; m25 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * t23) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t24)) ; t26 = ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))) ! [1])) ; t27 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m22)) ; m28 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * t26) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t27)) ; t29 = ttranspose [1,0] (tkonst 2 (tslice 2 2 m22)) ; m30 = tanh (ttranspose [1,0] (tkonst 2 v8) + tsum (ttranspose [2,1,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 m28)) + tsum (ttranspose [2,1,0] (tkonst 2 m7) * t29)) ; t31 = ttranspose [1,0] (tkonst 10 (tslice 2 2 (tappend m25 m30))) ; m32 = tappend (treshape [2,2] (tkonst 4 (tconst 0.0))) (tappend (tsum (ttranspose [1,0] (ttranspose [2,1,0] (tkonst 2 m9) * tkonst 2 dret))) (treshape [0,2] (tkonst 0 (tconst 0.0)))) ; m33 = (treshape [2,2] (tkonst 4 (tconst 1.0)) - m30 * m30) * tslice 2 2 m32 ; m34 = (treshape [2,2] (tkonst 4 (tconst 1.0)) - m28 * m28) * tsum (ttranspose [1,0] (ttranspose [2,1,0] (tkonst 2 m6) * tkonst 2 m33)) ; m35 = (treshape [2,2] (tkonst 4 (tconst 1.0)) - m25 * m25) * tslice 0 2 m32 ; m36 = tappend (treshape [0,2] (tkonst 0 (tconst 0.0))) (tappend (tsum (ttranspose [1,0] (ttranspose [2,1,0] (tkonst 2 m4) * tkonst 2 m35))) (treshape [2,2] (tkonst 4 (tconst 0.0)))) + tappend (treshape [0,2] (tkonst 0 (tconst 0.0))) (tappend (tsum (ttranspose [1,0] (ttranspose [2,1,0] (tkonst 2 m4) * tkonst 2 m34))) (treshape [2,2] (tkonst 4 (tconst 0.0)))) + tappend (treshape [2,2] (tkonst 4 (tconst 0.0))) (tappend (tsum (ttranspose [1,0] (ttranspose [2,1,0] (tkonst 2 m7) * tkonst 2 m33))) (treshape [0,2] (tkonst 0 (tconst 0.0)))) ; m37 = (treshape [2,2] (tkonst 4 (tconst 1.0)) - m21 * m21) * tslice 2 2 m36 ; m38 = (treshape [2,2] (tkonst 4 (tconst 1.0)) - m19 * m19) * tsum (ttranspose [1,0] (ttranspose [2,1,0] (tkonst 2 m6) * tkonst 2 m37)) ; m39 = (treshape [2,2] (tkonst 4 (tconst 1.0)) - m16 * m16) * tslice 0 2 m36 in (tfromList [], tsum (ttranspose [2,1,0] (t14 * tkonst 2 m39)) + tsum (ttranspose [2,1,0] (t17 * tkonst 2 m38)) + tsum (ttranspose [2,1,0] (t23 * tkonst 2 m35)) + tsum (ttranspose [2,1,0] (t26 * tkonst 2 m34)), tsum (ttranspose [2,1,0] (t15 * tkonst 2 m39)) + tsum (ttranspose [2,1,0] (t18 * tkonst 2 m38)) + tsum (ttranspose [2,1,0] (t24 * tkonst 2 m35)) + tsum (ttranspose [2,1,0] (t27 * tkonst 2 m34)), tsum (ttranspose [1,0] m39) + tsum (ttranspose [1,0] m38) + tsum (ttranspose [1,0] m35) + tsum (ttranspose [1,0] m34), tsum (ttranspose [2,1,0] (ttranspose [1,0] (tkonst 2 m19) * tkonst 2 m37)) + tsum (ttranspose [2,1,0] (ttranspose [1,0] (tkonst 2 m28) * tkonst 2 m33)), tsum (ttranspose [2,1,0] (t20 * tkonst 2 m37)) + tsum (ttranspose [2,1,0] (t29 * tkonst 2 m33)), tsum (ttranspose [1,0] m37) + tsum (ttranspose [1,0] m33), tsum (ttranspose [2,1,0] (t31 * tkonst 2 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 m3 m4 v5 m6 m7 v8 m9 v10 -> let m13 = treshape [4,2] (tkonst 8 (tconst 0.0)) ; m14 = ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))) ! [0])) ; m15 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m13)) ; m16 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * t14) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t15)) ; m17 = ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))) ! [0])) ; m18 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m13)) ; m19 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * t17) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t18)) ; m20 = ttranspose [1,0] (tkonst 2 (tslice 2 2 m13)) ; m21 = tanh (ttranspose [1,0] (tkonst 2 v8) + tsum (ttranspose [2,1,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 m19)) + tsum (ttranspose [2,1,0] (tkonst 2 m7) * t20)) ; m22 = tappend m16 m21 ; m23 = ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))) ! [1])) ; m24 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m22)) ; m25 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * t23) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t24)) ; m26 = ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))) ! [1])) ; m27 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m22)) ; m28 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * t26) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t27)) ; m29 = ttranspose [1,0] (tkonst 2 (tslice 2 2 m22)) ; m30 = tanh (ttranspose [1,0] (tkonst 2 v8) + tsum (ttranspose [2,1,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 m28)) + tsum (ttranspose [2,1,0] (tkonst 2 m7) * t29)) ; m31 = ttranspose [1,0] (tkonst 10 (tslice 2 2 (tappend m25 m30))) in tsum (ttranspose [2,1,0] (tkonst 2 m9) * t31) + ttranspose [1,0] (tkonst 2 v10)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret m3 m4 v5 m6 m7 v8 m9 v10 -> let m16 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0))))))) ; m19 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0))))))) ; m21 = tanh (ttranspose [1,0] (tkonst 2 v8) + tsum (ttranspose [2,1,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 m19)) + tsum (ttranspose [2,1,0] (tkonst 2 m7) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0))))))) ; m22 = tappend m16 m21 ; t24 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m22)) ; m25 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t24)) ; t27 = ttranspose [1,0] (tkonst 2 (tslice 0 2 m22)) ; m28 = tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * t27)) ; t29 = ttranspose [1,0] (tkonst 2 (tslice 2 2 m22)) ; m30 = tanh (ttranspose [1,0] (tkonst 2 v8) + tsum (ttranspose [2,1,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 m28)) + tsum (ttranspose [2,1,0] (tkonst 2 m7) * t29)) ; m32 = tappend (tconstant (tkonst 2 (tkonst 2 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (tkonst 2 m9) * ttranspose [1,0] (tkonst 2 dret))) (tconstant (tkonst 0 (tkonst 2 (tconst 0.0))))) ; m33 = (tconstant (tkonst 2 (tkonst 2 (tconst 1.0))) - m30 * m30) * tslice 2 2 m32 ; m34 = (tconstant (tkonst 2 (tkonst 2 (tconst 1.0))) - m28 * m28) * tsum (ttranspose [1,2,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 m33)) ; m35 = (tconstant (tkonst 2 (tkonst 2 (tconst 1.0))) - m25 * m25) * tslice 0 2 m32 ; m36 = tappend (tconstant (tkonst 0 (tkonst 2 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (tkonst 2 m4) * ttranspose [1,0] (tkonst 2 m35))) (tconstant (tkonst 2 (tkonst 2 (tconst 0.0))))) + tappend (tconstant (tkonst 0 (tkonst 2 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (tkonst 2 m4) * ttranspose [1,0] (tkonst 2 m34))) (tconstant (tkonst 2 (tkonst 2 (tconst 0.0))))) + tappend (tconstant (tkonst 2 (tkonst 2 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (tkonst 2 m7) * ttranspose [1,0] (tkonst 2 m33))) (tconstant (tkonst 0 (tkonst 2 (tconst 0.0))))) ; m37 = (tconstant (tkonst 2 (tkonst 2 (tconst 1.0))) - m21 * m21) * tslice 2 2 m36 ; m38 = (tconstant (tkonst 2 (tkonst 2 (tconst 1.0))) - m19 * m19) * tsum (ttranspose [1,2,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 m37)) ; m39 = (tconstant (tkonst 2 (tkonst 2 (tconst 1.0))) - m16 * m16) * tslice 0 2 m36 in (tfromList [], tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))))) * tkonst 2 m39)) + tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))))) * tkonst 2 m38)) + tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))))) * tkonst 2 m35)) + tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0))))) * tkonst 2 m34)), tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0))))) * tkonst 2 m39)) + tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0))))) * tkonst 2 m38)) + tsum (ttranspose [2,1,0] (t24 * tkonst 2 m35)) + tsum (ttranspose [2,1,0] (t27 * tkonst 2 m34)), tsum (ttranspose [1,0] m39) + tsum (ttranspose [1,0] m38) + tsum (ttranspose [1,0] m35) + tsum (ttranspose [1,0] m34), tsum (ttranspose [2,0,1] (tkonst 2 m19) * ttranspose [2,1,0] (tkonst 2 m37)) + tsum (ttranspose [2,0,1] (tkonst 2 m28) * ttranspose [2,1,0] (tkonst 2 m33)), tsum (ttranspose [2,1,0] (tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0))))) * tkonst 2 m37)) + tsum (ttranspose [2,1,0] (t29 * tkonst 2 m33)), tsum (ttranspose [1,0] m37) + tsum (ttranspose [1,0] m33), tsum (ttranspose [2,0,1] (tkonst 10 m30) * ttranspose [2,1,0] (tkonst 2 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 m3 m4 v5 m6 m7 v8 m9 v10 -> let m22 = tappend (tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0)))))))) (tanh (ttranspose [1,0] (tkonst 2 v8) + tsum (ttranspose [2,1,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 (tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0)))))))))) + tsum (ttranspose [2,1,0] (tkonst 2 m7) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 0.0)))))))) in tsum (ttranspose [2,1,0] (tkonst 2 m9) * ttranspose [1,0] (tkonst 10 (tanh (ttranspose [1,0] (tkonst 2 v8) + tsum (ttranspose [2,1,0] (tkonst 2 m6) * ttranspose [1,0] (tkonst 2 (tanh (ttranspose [1,0] (tkonst 2 v5) + tsum (ttranspose [2,1,0] (tkonst 2 m3) * tconstant (ttranspose [1,0] (tkonst 2 (tkonst 2 (tkonst 2 (tconst 7.0)))))) + tsum (ttranspose [2,1,0] (tkonst 2 m4) * ttranspose [1,0] (tkonst 2 (tslice 0 2 m22))))))) + tsum (ttranspose [2,1,0] (tkonst 2 m7) * ttranspose [1,0] (tkonst 2 (tslice 2 2 m22))))))) + ttranspose [1,0] (tkonst 2 v10)"
