-- | Tests of "MnistRnnShaped2" neural networks using a few different
-- optimization pipelines.
module TestMnistRNNS
  ( testTrees
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (foldM, unless)
import qualified Data.Array.Convert
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import qualified Data.Vector.Generic as V
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
import qualified MnistRnnShaped2

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNSA
            , tensorADValMnistTestsRNNSI
            , tensorADValMnistTestsRNNSO
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseRNNSA
  :: forall shaped width batch_size r.
     ( shaped ~ Flip OS.Array, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSA prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize
                   expected =
  let valsInit :: MnistRnnShaped2.ADRnnMnistParametersShaped
                    shaped SizeMnistHeight width r
      valsInit = fst $ randomVals 0.4 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width :: Int), show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
      ftest 0 _ _ = 0
      ftest miniBatchSize' (glyphs, labels) testParams =
        assert (miniBatchSize' == rlength (Flip glyphs)) $
        withSNat miniBatchSize' $ \bs@SNat ->
          let mnist = ( Data.Array.Convert.convert glyphs
                      , Data.Array.Convert.convert labels )
          in MnistRnnShaped2.rnnMnistTestS width bs valsInit mnist testParams
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: (HVector (Flip OR.Array), StateAdam) -> (Int, [MnistDataS r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchS batch_size r
                   -> HVector (ADVal (Flip OR.Array))
                   -> ADVal shaped r '[]
                 f (glyphS, labelS) adinputs =
                   MnistRnnShaped2.rnnMnistLossFusedS
                     width batch_size (sconst glyphS, sconst labelS)
                     (parseHVector (fromDValue valsInit) adinputs)
                 chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkS parameters stateAdam
                 smnistRFromS (glyphs, labels) =
                   ( Data.Array.Convert.convert glyphs
                   , Data.Array.Convert.convert labels )
                 chunkDataR = packBatchR $ map smnistRFromS chunk
                 !trainScore =
                   ftest (length chunk) chunkDataR parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (sNatValue width < (10 :: Int)) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < (10 :: Int)) $
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

{-# SPECIALIZE mnistTestCaseRNNSA
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSA :: TestTree
tensorADValMnistTestsRNNSA = testGroup "RNNS ADVal MNIST tests"
  [ mnistTestCaseRNNSA "RNNSA 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 50
                       (0.9 :: Double)
  , mnistTestCaseRNNSA "RNNSA artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSA "RNNSA artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.9336734693877551 :: Double)
  , mnistTestCaseRNNSA "RNNSA 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseRNNSI
  :: forall shaped width batch_size r.
     ( shaped ~ Flip OS.Array, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSI prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize expected =
  let valsInit :: MnistRnnShaped2.ADRnnMnistParametersShaped
                    shaped SizeMnistHeight width r
      valsInit = fst $ randomVals 0.4 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width :: Int), show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
      ftest 0 _ _ = 0
      ftest miniBatchSize' (glyphs, labels) testParams =
        assert (miniBatchSize' == rlength (Flip glyphs)) $
        assert (miniBatchSize' == rlength (Flip labels)) $
        withSNat miniBatchSize' $ \bs@SNat ->
          let mnist = ( Data.Array.Convert.convert glyphs
                      , Data.Array.Convert.convert labels )
          in MnistRnnShaped2.rnnMnistTestS width bs valsInit mnist testParams
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, hVectorPrimal, vars, _)
         <- funToAstRevIO $ voidFromHVector hVectorInit
       let testDataR = packBatchR testData
       (varGlyph, _, astGlyph) <-
         funToAstIOS {-@'[batch_size, SizeMnistHeight, SizeMnistWidth]-} id
       (varLabel, _, astLabel) <-
         funToAstIOS {-@'[batch_size, SizeMnistLabel]-} id
       let ast :: AstShaped PrimalSpan r '[]
           ast = MnistRnnShaped2.rnnMnistLossFusedS
                   width batch_size (astGlyph, astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (unRawHVector hVectorPrimal))
           runBatch :: (HVector (Flip OR.Array), StateAdam)
                    -> (Int, [MnistDataS r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchS batch_size r
                   -> HVector (ADVal (Flip OR.Array))
                   -> ADVal shaped r '[]
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvD EM.empty
                             $ zip vars $ V.toList varInputs
                       envMnist = extendEnvS varGlyph (sconst glyph)
                                  $ extendEnvS varLabel (sconst label) env
                   in interpretAstS envMnist ast
                 chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkS parameters stateAdam
                 smnistRFromS (glyphs, labels) =
                   ( Data.Array.Convert.convert glyphs
                   , Data.Array.Convert.convert labels )
                 chunkDataR = packBatchR $ map smnistRFromS chunk
                 !trainScore =
                   ftest (length chunk) chunkDataR parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (sNatValue width < (10 :: Int)) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < (10 :: Int)) $
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

{-# SPECIALIZE mnistTestCaseRNNSI
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSI :: TestTree
tensorADValMnistTestsRNNSI = testGroup "RNNS Intermediate MNIST tests"
  [ mnistTestCaseRNNSI "RNNSI 1 epoch, 1 batch" 1 1 (SNat @32) (SNat @5) 2
                       (1 :: Double)
--  [ mnistTestCaseRNNSI "RNNSI 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 50
--                       (0.84 :: Double)
--  , mnistTestCaseRNNSI "RNNSI artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
--                       (0.8933333 :: Float)
--  , mnistTestCaseRNNSI "RNNSI artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
--                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNSI "RNNSI 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseRNNSO
  :: forall shaped width batch_size r.
     ( shaped ~ Flip OS.Array, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSO prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize
                   expected =
    let valsInit :: MnistRnnShaped2.ADRnnMnistParametersShaped
                      shaped SizeMnistHeight width r
        valsInit = fst $ randomVals 0.4 (mkStdGen 44)
        hVectorInit = toHVectorOf valsInit
        miniBatchSize = sNatValue batch_size
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show (sNatValue width :: Int), show miniBatchSize
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
        ftest 0 _ _ = 0
        ftest miniBatchSize' (glyphs, labels) testParams =
          assert (miniBatchSize' == rlength (Flip glyphs)) $
          withSNat miniBatchSize' $ \bs@SNat ->
            let mnist = ( Data.Array.Convert.convert glyphs
                        , Data.Array.Convert.convert labels )
            in MnistRnnShaped2.rnnMnistTestS width bs valsInit mnist testParams
    in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
       (varGlyph, varGlyphD, astGlyph) <-
         funToAstIOS {-@'[batch_size, SizeMnistHeight, SizeMnistWidth]-} id
       (varLabel, varLabelD, astLabel) <-
         funToAstIOS {-@'[batch_size, SizeMnistLabel]-} id
       let envInit = extendEnvS varGlyph (sconstant $ AstRawS astGlyph)
                     $ extendEnvS varLabel (sconstant $ AstRawS astLabel)
                       EM.empty
           f = MnistRnnShaped2.rnnMnistLossFusedS
                 width batch_size (astGlyph, astLabel)
           (((varDtAgain, vars1Again), gradientRaw, primal), _) =
             revProduceArtifactH False f envInit valsInit
                                 (voidFromHVector hVectorInit)
           gradient = simplifyAstHVector6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistDataBatchS batch_size r] -> (HVector (Flip OR.Array), StateAdam)
              -> (HVector (Flip OR.Array), StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicShaped $ sconst glyph
                 labelD = DynamicShaped $ sconst label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifact (vars, gradient, primal)
                                         parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientHVector)
           runBatch :: (HVector (Flip OR.Array), StateAdam) -> (Int, [MnistDataS r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = go chunkS (parameters, stateAdam)
                 smnistRFromS (glyphs, labels) =
                   ( Data.Array.Convert.convert glyphs
                   , Data.Array.Convert.convert labels )
                 chunkDataR = packBatchR $ map smnistRFromS chunk
                 !trainScore =
                   ftest (length chunk) chunkDataR parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (sNatValue width < (10 :: Int)) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < (10 :: Int)) $
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

{-# SPECIALIZE mnistTestCaseRNNSO
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSO :: TestTree
tensorADValMnistTestsRNNSO = testGroup "RNNS Once MNIST tests"
  [ mnistTestCaseRNNSO "RNNSO 1 epoch, 1 batch" 1 1 (SNat @32) (SNat @5) 2
                       (1 :: Double)
--  [ mnistTestCaseRNNSO "RNNSO 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 500
--                       (0.898 :: Double)
--  , mnistTestCaseRNNSO "RNNSO artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
--                       (0.8933333 :: Float)
--  , mnistTestCaseRNNSO "RNNSO artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
--                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNSO "RNNSO 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]
