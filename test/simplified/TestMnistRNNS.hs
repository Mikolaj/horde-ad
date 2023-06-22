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
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.External.Optimizer
import HordeAd.External.OptimizerTools

import EqEpsilon

import           MnistData
import qualified MnistRnnShaped2

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNSA
-- TODO            , tensorADValMnistTestsRNNSI
-- TODO            , tensorADValMnistTestsRNNSO
            ]

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCaseRNNSA
  :: forall shaped width batch_size r.
     ( shaped ~ Flip OS.Array
     , ADReadyS shaped r, Random r, ADReadyS (ADVal shaped) r
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
      vInit = toValue valsInit
      domainsInit = toDomains valsInit
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width :: Int), show miniBatchSize
                        , show (V.length domainsInit)
                        , show (V.sum (V.map OD.size domainsInit)) ]
      ftest :: Int -> MnistDataBatchR r -> DomainsOD r -> r
      ftest 0 _ _ = 0
      ftest miniBatchSize' (glyphs, labels) testParams =
        assert (miniBatchSize' == tlength (Flip glyphs)) $
        withSNat miniBatchSize' $ \bs@SNat ->
          let mnist = ( Data.Array.Convert.convert glyphs
                      , Data.Array.Convert.convert labels )
          in MnistRnnShaped2.rnnMnistTestS width bs mnist
               (\f -> runFlip $ f $ parseDomains vInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: (DomainsOD r, StateAdam r) -> (Int, [MnistDataS r])
                    -> IO (DomainsOD r, StateAdam r)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchS batch_size r
                   -> Domains (ADValClown OD.Array) r
                   -> ADVal shaped r '[]
                 f (glyphS, labelS) adinputs =
                   MnistRnnShaped2.rnnMnistLossFusedS
                     width batch_size (sconst glyphS, sconst labelS)
                     (parseDomains valsInit adinputs)
                 chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdamS f chunkS parameters stateAdam
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
       let runEpoch :: Int -> (DomainsOD r, StateAdam r) -> IO (DomainsOD r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
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

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCaseRNNSI
  :: forall shaped width batch_size r.
     ( shaped ~ Flip OS.Array
     , ADReadyS shaped r, Random r, InterpretAstS (ADVal shaped) r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSI prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize
                   expected =
  let valsInit :: MnistRnnShaped2.ADRnnMnistParametersShaped
                    shaped SizeMnistHeight width r
      valsInit = fst $ randomVals 0.4 (mkStdGen 44)
      vInit = toValue valsInit
      domainsInit = toDomains valsInit
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width :: Int), show miniBatchSize
                        , show (V.length domainsInit)
                        , show (V.sum (V.map OD.size domainsInit)) ]
      ftest :: Int -> MnistDataBatchR r -> DomainsOD r -> r
      ftest 0 _ _ = 0
      ftest miniBatchSize' (glyphs, labels) testParams =
        assert (miniBatchSize' == tlength (Flip glyphs)) $
        assert (miniBatchSize' == tlength (Flip labels)) $
        withSNat miniBatchSize' $ \bs@SNat ->
          let mnist = ( Data.Array.Convert.convert glyphs
                      , Data.Array.Convert.convert labels )
          in MnistRnnShaped2.rnnMnistTestS width bs mnist
               (\f -> runFlip $ f $ parseDomains vInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           shapes1 = map (dshape @(Flip OR.Array) @shaped)
                     $ V.toList domainsInit
           (vars1, asts1) = unzip $ map funToAstD shapes1
           doms = V.fromList asts1
           (varGlyph, astGlyph) =
             funToAstS
               {-@'[batch_size, SizeMnistHeight, SizeMnistWidth]-}
               id
           (varLabel, astLabel) =
             funToAstS {-@'[batch_size, SizeMnistLabel]-} id
           ast :: AstShaped r '[]
           ast = MnistRnnShaped2.rnnMnistLossFusedS
                   width batch_size (sprimalPart astGlyph, sprimalPart astLabel)
                                    (parseDomains valsInit doms)
           runBatch :: (DomainsOD r, StateAdam r) -> (Int, [MnistDataS r])
                    -> IO (DomainsOD r, StateAdam r)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchS batch_size r
                   -> Domains (ADValClown OD.Array) r
                   -> ADVal shaped r '[]
                 f (glyph, label) varInputs =
                   let env1 = foldr extendEnvD EM.empty
                              $ zip vars1 $ V.toList varInputs
                       envMnist = extendEnvS varGlyph (sconst glyph)
                                  $ extendEnvS varLabel (sconst label) env1
                   in snd $ interpretAstS envMnist emptyMemo ast
                 chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdamS f chunkS parameters stateAdam
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
       let runEpoch :: Int -> (DomainsOD r, StateAdam r) -> IO (DomainsOD r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
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

_tensorADValMnistTestsRNNSI :: TestTree
_tensorADValMnistTestsRNNSI = testGroup "RNNS Intermediate MNIST tests"
  [ mnistTestCaseRNNSI "RNNSI 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 50
                       (0.84 :: Double)
  , mnistTestCaseRNNSI "RNNSI artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSI "RNNSI artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNSI "RNNSI 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCaseRNNSO
  :: forall shaped width batch_size r.
     ( shaped ~ Flip OS.Array
     , ADReadyS shaped r, Random r, InterpretAstS shaped r
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
        vInit = toValue valsInit
        domainsInit = toDomains valsInit
        miniBatchSize = sNatValue batch_size
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show (sNatValue width :: Int), show miniBatchSize
                          , show (V.length domainsInit)
                          , show (V.sum (V.map OD.size domainsInit)) ]
        ftest :: Int -> MnistDataBatchR r -> DomainsOD r -> r
        ftest 0 _ _ = 0
        ftest miniBatchSize' (glyphs, labels) testParams =
          assert (miniBatchSize' == tlength (Flip glyphs)) $
          withSNat miniBatchSize' $ \bs@SNat ->
            let mnist = ( Data.Array.Convert.convert glyphs
                        , Data.Array.Convert.convert labels )
            in MnistRnnShaped2.rnnMnistTestS width bs mnist
                 (\f -> runFlip $ f $ parseDomains vInit testParams)
    in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           (varGlyph, astGlyph) =
             funToAstS
               {-@'[batch_size, SizeMnistHeight, SizeMnistWidth]-}
               id
           (varLabel, astLabel) =
             funToAstS {-@'[batch_size, SizeMnistLabel]-} id
           _envInit = extendEnvS @(ADVal AstRanked) @(ADVal AstShaped) @r
                                @'[batch_size, SizeMnistHeight, SizeMnistWidth]
                                varGlyph (sconstant astGlyph)
                     $ extendEnvS @(ADVal AstRanked) @(ADVal AstShaped) @r
                                  @'[batch_size, SizeMnistLabel]
                                  varLabel (sconstant astLabel) EM.empty
           _f = MnistRnnShaped2.rnnMnistLossFusedS @AstShaped
                 width batch_size (sprimalPart astGlyph, sprimalPart astLabel :: AstPrimalPartS r '[batch_size, SizeMnistLabel])
           {-
           (((varDtAgain, vars1Again), gradientRaw, primal), _) =
             revDtInit f valsInit envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain =
             vars1Again
             ++ [AstDynamicVarName varGlyph, AstDynamicVarName varLabel]
           vars = (varDtAgain, vars1AndInputAgain)
           -}
           go :: [MnistDataBatchS batch_size r] -> (DomainsOD r, StateAdam r)
              -> (DomainsOD r, StateAdam r)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) !(!parameters, !stateAdam) =
             let glyphD = dfromS @(Flip OR.Array) $ sconst glyph
                 labelD = dfromS @(Flip OR.Array) $ sconst label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientDomain =
                   fst $ revAstOnDomainsEval @r @777 undefined -- TODO
                                             parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientDomain)
           runBatch :: (DomainsOD r, StateAdam r) -> (Int, [MnistDataS r])
                    -> IO (DomainsOD r, StateAdam r)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
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
       let runEpoch :: Int -> (DomainsOD r, StateAdam r) -> IO (DomainsOD r)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
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

_tensorADValMnistTestsRNNSO :: TestTree
_tensorADValMnistTestsRNNSO = testGroup "RNNS Once MNIST tests"
  [ mnistTestCaseRNNSO "RNNSO 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 500
                       (0.898 :: Double)
  , mnistTestCaseRNNSO "RNNSO artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSO "RNNSO artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNSO "RNNSO 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]