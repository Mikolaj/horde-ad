-- | Tests of "MnistRnnShaped2" neural networks using a few different
-- optimization pipelines.
module TestMnistRNNS
  ( testTrees
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (foldM, unless)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (Nat)
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (funToAstIOS, funToAstRevIOS)
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
      domainsInit = toDomains valsInit
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width :: Int), show miniBatchSize
                        , show (V.length domainsInit)
                        , show (sizeDomainsOD domainsInit) ]
      ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
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
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataS r])
                    -> IO (DomainsOD, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchS batch_size r
                   -> Domains (ADValClown OD.Array)
                   -> ADVal shaped r '[]
                 f (glyphS, labelS) adinputs =
                   MnistRnnShaped2.rnnMnistLossFusedS
                     width batch_size (sconst glyphS, sconst labelS)
                     (parseDomains valsInit adinputs)
                 chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkS parameters stateAdam
                 smnistSToR (glyphs, labels) =
                   ( Data.Array.Convert.convert glyphs
                   , Data.Array.Convert.convert labels )
                 chunkDataR = packBatchR $ map smnistSToR chunk
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
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
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
       res <- runEpoch 1 (domainsInit, initialStateAdam domainsInit)
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
                       (0.8200000000000001 :: Double)
  , mnistTestCaseRNNSA "RNNSA artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSA "RNNSA artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.8928571428571429 :: Double)
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
      domainsInit = toDomains valsInit
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width :: Int), show miniBatchSize
                        , show (V.length domainsInit)
                        , show (sizeDomainsOD domainsInit) ]
      ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
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
       (_, domainsPrimal, vars, _) <- funToAstRevIOS domainsInit
       let testDataR = packBatchR testData
       (varGlyph, _, astGlyph) <-
         funToAstIOS {-@'[batch_size, SizeMnistHeight, SizeMnistWidth]-} id
       (varLabel, _, astLabel) <-
         funToAstIOS {-@'[batch_size, SizeMnistLabel]-} id
       let ast :: AstShaped PrimalSpan r '[]
           ast = MnistRnnShaped2.rnnMnistLossFusedS
                   width batch_size
                   ( sprimalPart @(AstShaped PrimalSpan) astGlyph
                   , sprimalPart @(AstShaped PrimalSpan) astLabel )
                   (parseDomains @(AstDynamic PrimalSpan)
                                 valsInit domainsPrimal)
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataS r])
                    -> IO (DomainsOD, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchS batch_size r
                   -> Domains (ADValClown OD.Array)
                   -> ADVal shaped r '[]
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvDS EM.empty
                             $ zip vars $ V.toList varInputs
                       envMnist = extendEnvS varGlyph (sconst glyph)
                                  $ extendEnvS varLabel (sconst label) env
                   in interpretAstS envMnist ast
                 chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkS parameters stateAdam
                 smnistSToR (glyphs, labels) =
                   ( Data.Array.Convert.convert glyphs
                   , Data.Array.Convert.convert labels )
                 chunkDataR = packBatchR $ map smnistSToR chunk
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
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
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
       res <- runEpoch 1 (domainsInit, initialStateAdam domainsInit)
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
        domainsInit = toDomains valsInit
        miniBatchSize = sNatValue batch_size
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show (sNatValue width :: Int), show miniBatchSize
                          , show (V.length domainsInit)
                          , show (sizeDomainsOD domainsInit) ]
        ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
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
       let envInit = extendEnvS varGlyph (sconstant astGlyph)
                     $ extendEnvS varLabel (sconstant astLabel)
                       EM.empty
           f = MnistRnnShaped2.rnnMnistLossFusedS
                 width batch_size (astGlyph, astLabel)
           g domains = f $ parseDomains valsInit domains
           (((varDtAgain, vars1Again), gradientRaw, primal, sh), _) =
             revProduceArtifact @[Nat] @(AstShaped FullSpan) False g envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistDataBatchS batch_size r] -> (DomainsOD, StateAdam)
              -> (DomainsOD, StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicExists $ dfromS @(Flip OR.Array) $ sconst glyph
                 labelD = DynamicExists $ dfromS @(Flip OR.Array) $ sconst label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientDomain =
                   fst $ revEvalArtifact @[Nat] @(AstShaped FullSpan)
                                         (vars, gradient, primal, sh)
                                         parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientDomain)
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataS r])
                    -> IO (DomainsOD, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = go chunkS (parameters, stateAdam)
                 smnistSToR (glyphs, labels) =
                   ( Data.Array.Convert.convert glyphs
                   , Data.Array.Convert.convert labels )
                 chunkDataR = packBatchR $ map smnistSToR chunk
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
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
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
       res <- runEpoch 1 (domainsInit, initialStateAdam domainsInit)
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
