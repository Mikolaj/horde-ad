{-# LANGUAGE ImpredicativeTypes #-}
module TestMnistFCNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.List.Index (imap)
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (SomeNat (..), someNatVal)
import qualified Numeric.LinearAlgebra as LA
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.DualNumber (ADVal)
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.External.Optimizer
import HordeAd.External.OptimizerTools

import EqEpsilon

import           MnistData
import qualified MnistFcnnRanked1
import qualified MnistFcnnRanked2

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTests
            , tensorIntermediateMnistTests
            , tensorADOnceMnistTests
            , tensorADValMnistTests2
            , tensorIntermediateMnistTests2
            , tensorADOnceMnistTests2
            , tensorMnistTestsPP
            ]


-- * Using vectors, which is rank 1

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCase2VTA
  :: forall ranked r.
     ( ranked ~ Flip OR.Array
     , ADReady ranked r, ADReady (ADVal ranked) r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTA prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV -> OD.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      emptyR = Flip $ OR.fromList [0] []
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length params1Init)
                        , show (sum (map OD.size params1Init))
                        , show gamma ]
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest mnist testParams =
        MnistFcnnRanked1.afcnnMnistTest1
          widthHidden widthHidden2 mnist
          (\f -> OR.toVector $ runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: DomainsOD -> (Int, [MnistData r]) -> IO DomainsOD
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f mnist adinputs =
                   MnistFcnnRanked1.afcnnMnistLoss1
                     widthHidden widthHidden2
                     mnist (parseDomains valsInit adinputs)
                 res = fst $ sgd gamma f chunk domains
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> DomainsOD -> IO DomainsOD
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (V.fromList
                          $ map (DynamicExists @r) params1Init)
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VTA
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADValMnistTests :: TestTree
tensorADValMnistTests = testGroup "Ranked ADVal MNIST tests"
  [ mnistTestCase2VTA "VTA 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16600000000000004 :: Double)
  , mnistTestCase2VTA "VTA artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.8972 :: Float)
  , mnistTestCase2VTA "VTA artificial 5 4 3 2 1" 5 4 3 2 1 4999
                      (0.8210999999999999 :: Double)
  , mnistTestCase2VTA "VTA 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCase2VTI
  :: forall ranked r.
     ( ranked ~ Flip OR.Array
     , ADReady ranked r, InterpretAstR (ADVal ranked)
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTI prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV -> OD.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = Flip $ OR.fromList [0] []
      domainsInit = V.fromList $ map (DynamicExists @r) params1Init
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length params1Init)
                        , show (sum (map OD.size params1Init))
                        , show gamma ]
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest mnist testParams =
        MnistFcnnRanked1.afcnnMnistTest1
          widthHidden widthHidden2 mnist
          (\f -> OR.toVector $ runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let (vars1, asts1) = funToAst2 domainsInit
           doms = V.fromList asts1
       (varGlyph, _, astGlyph) <-
         funToAstIOR (singletonShape sizeMnistGlyphInt) id
       (varLabel, _, astLabel) <-
         funToAstIOR (singletonShape sizeMnistLabelInt) id
       let ast :: AstRanked r 0
           ast = MnistFcnnRanked1.afcnnMnistLoss1TensorData
                   widthHidden widthHidden2 (astGlyph, astLabel)
                   (parseDomains valsInit doms)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: DomainsOD -> (Int, [MnistData r]) -> IO DomainsOD
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env1 = foldr extendEnvDR EM.empty
                              $ zip vars1 $ V.toList varInputs
                       envMnist =
                         extendEnvR varGlyph
                           (tconst $ OR.fromVector [sizeMnistGlyphInt] glyph)
                         $ extendEnvR varLabel
                             (tconst $ OR.fromVector [sizeMnistLabelInt] label)
                             env1
                   in interpretAst envMnist ast
                 res = fst $ sgd gamma f chunk domains
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> DomainsOD -> IO DomainsOD
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
                              -- 5000 times less data per batch
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VTI
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorIntermediateMnistTests :: TestTree
tensorIntermediateMnistTests = testGroup "Ranked Intermediate MNIST tests"
  [ mnistTestCase2VTI "VTI 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase2VTI "VTI artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase2VTI "VTI artificial 5 4 3 2 1" 5 4 3 2 1 4999
                      (0.7034 :: Double)
  , mnistTestCase2VTI "VTI 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCase2VTO
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, ADReady ranked r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTO prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV -> OD.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = Flip $ OR.fromList [0] []
      domainsInit = V.fromList $ map (DynamicExists @r) params1Init
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length params1Init)
                        , show (sum (map OD.size params1Init))
                        , show gamma ]
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest mnist testParams =
        MnistFcnnRanked1.afcnnMnistTest1
          widthHidden widthHidden2 mnist
          (\f -> OR.toVector $ runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (varGlyph, varGlyphD, astGlyph) <-
         funToAstIOR (singletonShape sizeMnistGlyphInt) id
       (varLabel, varLabelD, astLabel) <-
         funToAstIOR (singletonShape sizeMnistLabelInt) id
       let envInit = extendEnvR varGlyph (tconstant $ astPrimalPart astGlyph)
                     $ extendEnvR varLabel (tconstant $ astPrimalPart astLabel)
                     EM.empty
           f = MnistFcnnRanked1.afcnnMnistLoss1TensorData
                 widthHidden widthHidden2 (astGlyph, astLabel)
           (((varDtAgain, vars1Again), gradientRaw, primal), _) =
             revDtInit False f valsInit envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistData r] -> DomainsOD -> DomainsOD
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicExists
                          $ OD.fromVector [sizeMnistGlyphInt] glyph
                 labelD = DynamicExists
                          $ OD.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradient gamma parameters gradientDomain)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: DomainsOD -> (Int, [MnistData r]) -> IO DomainsOD
           runBatch !domains (k, chunk) = do
             let res = go chunk domains
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> DomainsOD -> IO DomainsOD
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
                              -- 5000 times less data per batch
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VTO
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADOnceMnistTests :: TestTree
tensorADOnceMnistTests = testGroup "Ranked Once MNIST tests"
  [ mnistTestCase2VTO "VTO 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase2VTO "VTO artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase2VTO "VTO artificial 5 4 3 2 1" 5 4 3 2 1 4999
                      (0.8636 :: Double)
  , mnistTestCase2VTO "VTO 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]


-- * Using matrices, which is rank 2

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCase2VT2A
  :: forall ranked r.
     ( ranked ~ Flip OR.Array
     , ADReady ranked r, Random r, ADReady (ADVal ranked) r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VT2A prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                shapedToRanked $ fst
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        (Flip OS.Array) widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      domainsInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (V.length domainsInit)
                        , show (sizeDomainsOD domainsInit)
                        , show gamma ]
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest mnist testParams =
        MnistFcnnRanked2.afcnnMnistTest2 mnist
          (\f -> OR.toVector $ runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: DomainsOD -> (Int, [MnistData r]) -> IO DomainsOD
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f mnist adinputs =
                   MnistFcnnRanked2.afcnnMnistLoss2
                     mnist (parseDomains valsInit adinputs)
                 res = fst $ sgd gamma f chunk domains
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> DomainsOD -> IO DomainsOD
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VT2A
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADValMnistTests2 :: TestTree
tensorADValMnistTests2 = testGroup "Ranked2 ADVal MNIST tests"
  [ mnistTestCase2VT2A "VT2A 1 epoch, 1 batch" 1 1 300 100 0.02 5
                       (0.8 :: Double)
  , mnistTestCase2VT2A "VT2A artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.89 :: Float)
  , mnistTestCase2VT2A "VT2A artificial 5 4 3 2 1" 5 4 3 2 1 499
                       (0.8361723446893787 :: Double)
  , mnistTestCase2VT2A "VT2A 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCase2VT2I
  :: forall ranked r.
     ( ranked ~ Flip OR.Array
     , ADReady ranked r, Random r, InterpretAstR (ADVal ranked)
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VT2I prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Nothing -> error "impossible someNatVal error"
              Just (SomeNat @widthHidden2 _) ->
                shapedToRanked $ fst
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        (Flip OS.Array) widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
      domainsInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (V.length domainsInit)
                        , show (sizeDomainsOD domainsInit)
                        , show gamma ]
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest mnist testParams =
        MnistFcnnRanked2.afcnnMnistTest2 mnist
          (\f -> OR.toVector $ runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let (vars1, asts1) = funToAst2 domainsInit
           doms = V.fromList asts1
       (varGlyph, _, astGlyph) <-
         funToAstIOR (singletonShape sizeMnistGlyphInt) id
       (varLabel, _, astLabel) <-
         funToAstIOR (singletonShape sizeMnistLabelInt) id
       let ast :: AstRanked r 0
           ast = MnistFcnnRanked2.afcnnMnistLoss2TensorData
                   (astGlyph, astLabel) (parseDomains valsInit doms)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: DomainsOD -> (Int, [MnistData r]) -> IO DomainsOD
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env1 = foldr extendEnvDR EM.empty
                              $ zip vars1 $ V.toList varInputs
                       envMnist =
                         extendEnvR varGlyph
                           (tconst $ OR.fromVector [sizeMnistGlyphInt] glyph)
                         $ extendEnvR varLabel
                             (tconst $ OR.fromVector [sizeMnistLabelInt] label)
                             env1
                   in interpretAst envMnist ast
                 res = fst $ sgd gamma f chunk domains
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> DomainsOD -> IO DomainsOD
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
                              -- 5000 times less data per batch
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected
{-# SPECIALIZE mnistTestCase2VT2I
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorIntermediateMnistTests2 :: TestTree
tensorIntermediateMnistTests2 = testGroup "Ranked2 Intermediate MNIST tests"
  [ mnistTestCase2VT2I "VT2I 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.534 :: Double)
  , mnistTestCase2VT2I "VT2I artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VT2I "VT2I artificial 5 4 3 2 1" 5 4 3 2 1 499
                       (0.7945891783567134 :: Double)
  , mnistTestCase2VT2I "VT2I 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCase2VT2O
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, ADReady ranked r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VT2O prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
 -- TODO: use withKnownNat when we no longer support GHC 9.4
 case someNatVal $ toInteger widthHidden of
  Nothing -> error "impossible someNatVal error"
  Just (SomeNat @widthHidden _) -> case someNatVal $ toInteger widthHidden2 of
   Nothing -> error "impossible someNatVal error"
   Just (SomeNat @widthHidden2 _) ->
    let valsInitShaped
          :: MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
               (Flip OS.Array) widthHidden widthHidden2 r
        valsInitShaped = fst $ randomVals 1 (mkStdGen 44)
        domainsInit = toDomains valsInitShaped  -- == toDomains valsInit
        valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
        valsInit =
          -- This almost works and I wouldn't need shapedToRanked,
          -- but there is nowhere to get aInit from.
          --   parseDomains aInit domainsInit
          shapedToRanked valsInitShaped
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show widthHidden, show widthHidden2
                          , show (V.length domainsInit)
                          , show (sizeDomainsOD domainsInit)
                          , show gamma ]
        ftest :: [MnistData r] -> DomainsOD -> r
        ftest mnist testParams =
          MnistFcnnRanked2.afcnnMnistTest2 mnist
            (\f -> OR.toVector $ runFlip $ f
                   $ parseDomains valsInit testParams)
    in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (varGlyph, varGlyphD, astGlyph) <-
         funToAstIOR (singletonShape sizeMnistGlyphInt) id
       (varLabel, varLabelD, astLabel) <-
         funToAstIOR (singletonShape sizeMnistLabelInt) id
       let envInit = extendEnvR varGlyph (tconstant $ astPrimalPart astGlyph)
                     $ extendEnvR varLabel (tconstant $ astPrimalPart astLabel)
                       EM.empty
           f = MnistFcnnRanked2.afcnnMnistLoss2TensorData
                 (astGlyph, astLabel)
           (((varDtAgain, vars1Again), gradientRaw, primal), _) =
             revDtInit False f valsInit envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistData r] -> DomainsOD -> DomainsOD
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicExists
                          $ OD.fromVector [sizeMnistGlyphInt] glyph
                 labelD = DynamicExists
                          $ OD.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradient gamma parameters gradientDomain)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: DomainsOD -> (Int, [MnistData r]) -> IO DomainsOD
           runBatch !domains (k, chunk) = do
             let res = go chunk domains
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> DomainsOD -> IO DomainsOD
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
                              -- 5000 times less data per batch
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VT2O
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADOnceMnistTests2 :: TestTree
tensorADOnceMnistTests2 = testGroup "Ranked2 Once MNIST tests"
  [ mnistTestCase2VT2O "VT2O 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.534 :: Double)
  , mnistTestCase2VT2O "VT2O artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VT2O "VT2O artificial 5 4 3 2 1" 5 4 3 2 1 499
                       (0.7945891783567134 :: Double)
  , mnistTestCase2VT2O "VT2O 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for Short Ranked MNIST tests"
  [ testCase "VTOPP" testVTOPP
  , testCase "VTOPPNonLin" testVTOPPNonLin
  , testCase "VT2OPP" testVT2OPP
  , testCase "VT2OPPNonLin" testVT2OPPNonLin
  ]

valsInitVTOPP :: MnistFcnnRanked1.ADFcnnMnist1Parameters (Flip OR.Array) Double
valsInitVTOPP =
  ( ( replicate 3 (Flip $ OR.fromList [3] [1, 2, 3])
    , Flip $ OR.fromList [3] [1, 2, 3] )
  , ( replicate 4 (Flip $ OR.fromList [4] [1, 2, 3, 4])
    , Flip $ OR.fromList [4] [1, 2, 3, 4] )
  , ( replicate 5 (Flip $ OR.fromList [5] [1, 2, 3, 4, 5])
    , Flip $ OR.fromList [5] [1, 2, 3, 4, 5] ) )

testVTOPP :: Assertion
testVTOPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate sizeMnistGlyphInt 7
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters AstRanked Double
              -> AstRanked Double 1
      afcnn2T = MnistFcnnRanked1.afcnnMnist1 id id 3 4 blackGlyph
      (artifact6, _) = revDtFun True afcnn2T valsInitVTOPP
  printGradient6Pretty renames artifact6
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = treplicate 784 (tconst 7.0) ; v20 = treplicate 784 (tconst 7.0) ; v21 = treplicate 784 (tconst 7.0) ; v22 = tfromList [tsum (v2 * v19), tsum (v3 * v20), tsum (v4 * v21)] + v5 ; v23 = tfromList [tsum (v6 * v22), tsum (v7 * v22), tsum (v8 * v22), tsum (v9 * v22)] + v10 ; x24 = dret ! [4] ; x25 = dret ! [3] ; x26 = dret ! [2] ; x27 = dret ! [1] ; x28 = dret ! [0] ; v29 = v11 * treplicate 5 x28 + v12 * treplicate 5 x27 + v13 * treplicate 5 x26 + v14 * treplicate 5 x25 + v15 * treplicate 5 x24 ; x30 = v29 ! [3] ; x31 = v29 ! [2] ; x32 = v29 ! [1] ; x33 = v29 ! [0] ; v34 = v6 * treplicate 4 x33 + v7 * treplicate 4 x32 + v8 * treplicate 4 x31 + v9 * treplicate 4 x30 ; x35 = v34 ! [2] ; x36 = v34 ! [1] ; x37 = v34 ! [0] in (v19 * treplicate 784 x37, v20 * treplicate 784 x36, v21 * treplicate 784 x35, v34, v22 * treplicate 3 x33, v22 * treplicate 3 x32, v22 * treplicate 3 x31, v22 * treplicate 3 x30, v29, v23 * treplicate 4 x28, v23 * treplicate 4 x27, v23 * treplicate 4 x26, v23 * treplicate 4 x25, v23 * treplicate 4 x24, dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = treplicate 784 (tconst 7.0) ; v20 = treplicate 784 (tconst 7.0) ; v21 = treplicate 784 (tconst 7.0) ; v22 = tfromList [tsum (v2 * v19), tsum (v3 * v20), tsum (v4 * v21)] + v5 ; v23 = tfromList [tsum (v6 * v22), tsum (v7 * v22), tsum (v8 * v22), tsum (v9 * v22)] + v10 in tfromList [tsum (v11 * v23), tsum (v12 * v23), tsum (v13 * v23), tsum (v14 * v23), tsum (v15 * v23)] + v16"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v22 = tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5 ; v23 = tfromList [tsum (v6 * v22), tsum (v7 * v22), tsum (v8 * v22), tsum (v9 * v22)] + v10 ; x24 = dret ! [4] ; x25 = dret ! [3] ; x26 = dret ! [2] ; x27 = dret ! [1] ; x28 = dret ! [0] ; v29 = v11 * treplicate 5 x28 + v12 * treplicate 5 x27 + v13 * treplicate 5 x26 + v14 * treplicate 5 x25 + v15 * treplicate 5 x24 ; x30 = v29 ! [3] ; x31 = v29 ! [2] ; x32 = v29 ! [1] ; x33 = v29 ! [0] ; v34 = v6 * treplicate 4 x33 + v7 * treplicate 4 x32 + v8 * treplicate 4 x31 + v9 * treplicate 4 x30 in (treplicate 784 (tconst 7.0) * treplicate 784 (v34 ! [0]), treplicate 784 (tconst 7.0) * treplicate 784 (v34 ! [1]), treplicate 784 (tconst 7.0) * treplicate 784 (v34 ! [2]), v34, v22 * treplicate 3 x33, v22 * treplicate 3 x32, v22 * treplicate 3 x31, v22 * treplicate 3 x30, v29, v23 * treplicate 4 x28, v23 * treplicate 4 x27, v23 * treplicate 4 x26, v23 * treplicate 4 x25, v23 * treplicate 4 x24, dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v22 = tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5 ; v23 = tfromList [tsum (v6 * v22), tsum (v7 * v22), tsum (v8 * v22), tsum (v9 * v22)] + v10 in tfromList [tsum (v11 * v23), tsum (v12 * v23), tsum (v13 * v23), tsum (v14 * v23), tsum (v15 * v23)] + v16"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters AstRanked Double
                    -> AstRanked Double 1
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMax1 3 4 blackGlyph
      (artifact6nonLin, _) = revDtFun True afcnn2TnonLin valsInitVTOPP
  printGradient6Pretty renames artifact6nonLin
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v24 = treplicate 784 (tconst 7.0) ; v25 = treplicate 784 (tconst 7.0) ; v26 = treplicate 784 (tconst 7.0) ; v27 = tfromList [tsum (v2 * v24), tsum (v3 * v25), tsum (v4 * v26)] + v5 ; v30 = let v28 = exp (negate v27) ; v29 = treplicate 3 (tconst 1.0) + v28 in recip v29 ; v31 = treplicate 3 (tconst 1.0) - v30 ; v32 = v30 * v31 ; v33 = v30 ; v34 = tfromList [tsum (v6 * v33), tsum (v7 * v33), tsum (v8 * v33), tsum (v9 * v33)] + v10 ; v37 = let v35 = exp (negate v34) ; v36 = treplicate 4 (tconst 1.0) + v35 in recip v36 ; v38 = treplicate 4 (tconst 1.0) - v37 ; v39 = v37 * v38 ; v40 = v37 ; v41 = exp (tfromList [tsum (v11 * v40), tsum (v12 * v40), tsum (v13 * v40), tsum (v14 * v40), tsum (v15 * v40)] + v16) ; x42 = tsum v41 ; v43 = treplicate 5 (recip x42) ; v44 = v41 * (treplicate 5 (negate (recip (x42 * x42)) * tsum (v41 * dret)) + v43 * dret) ; x45 = v44 ! [4] ; x46 = v44 ! [3] ; x47 = v44 ! [2] ; x48 = v44 ! [1] ; x49 = v44 ! [0] ; v50 = v11 * treplicate 5 x49 + v12 * treplicate 5 x48 + v13 * treplicate 5 x47 + v14 * treplicate 5 x46 + v15 * treplicate 5 x45 ; v51 = v37 * (v34 * v50) ; v52 = v39 * v50 ; x53 = v52 ! [3] ; x54 = v52 ! [2] ; x55 = v52 ! [1] ; x56 = v52 ! [0] ; v57 = v6 * treplicate 4 x56 + v7 * treplicate 4 x55 + v8 * treplicate 4 x54 + v9 * treplicate 4 x53 ; v58 = v30 * (v27 * v57) ; v59 = v32 * v57 ; x60 = v59 ! [2] ; x61 = v59 ! [1] ; x62 = v59 ! [0] in (v24 * treplicate 784 x62, v25 * treplicate 784 x61, v26 * treplicate 784 x60, v59, v33 * treplicate 3 x56, v33 * treplicate 3 x55, v33 * treplicate 3 x54, v33 * treplicate 3 x53, v52, v40 * treplicate 4 x49, v40 * treplicate 4 x48, v40 * treplicate 4 x47, v40 * treplicate 4 x46, v40 * treplicate 4 x45, v44)"
  printPrimal6Pretty renames artifact6nonLin
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v24 = treplicate 784 (tconst 7.0) ; v25 = treplicate 784 (tconst 7.0) ; v26 = treplicate 784 (tconst 7.0) ; v27 = tfromList [tsum (v2 * v24), tsum (v3 * v25), tsum (v4 * v26)] + v5 ; v30 = let v28 = exp (negate v27) ; v29 = treplicate 3 (tconst 1.0) + v28 in recip v29 ; v31 = treplicate 3 (tconst 1.0) - v30 ; v32 = v30 * v31 ; v33 = v30 ; v34 = tfromList [tsum (v6 * v33), tsum (v7 * v33), tsum (v8 * v33), tsum (v9 * v33)] + v10 ; v37 = let v35 = exp (negate v34) ; v36 = treplicate 4 (tconst 1.0) + v35 in recip v36 ; v38 = treplicate 4 (tconst 1.0) - v37 ; v39 = v37 * v38 ; v40 = v37 ; v41 = exp (tfromList [tsum (v11 * v40), tsum (v12 * v40), tsum (v13 * v40), tsum (v14 * v40), tsum (v15 * v40)] + v16) ; x42 = tsum v41 ; v43 = treplicate 5 (recip x42) in v43 * v41"
  printGradient6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v30 = recip (treplicate 3 (tconst 1.0) + exp (negate (tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5))) ; v37 = recip (treplicate 4 (tconst 1.0) + exp (negate (tfromList [tsum (v6 * v30), tsum (v7 * v30), tsum (v8 * v30), tsum (v9 * v30)] + v10))) ; v41 = exp (tfromList [tsum (v11 * v37), tsum (v12 * v37), tsum (v13 * v37), tsum (v14 * v37), tsum (v15 * v37)] + v16) ; x42 = tsum v41 ; v44 = v41 * (treplicate 5 (negate (recip (x42 * x42)) * tsum (v41 * dret)) + treplicate 5 (recip x42) * dret) ; x45 = v44 ! [4] ; x46 = v44 ! [3] ; x47 = v44 ! [2] ; x48 = v44 ! [1] ; x49 = v44 ! [0] ; v52 = (v37 * (treplicate 4 (tconst 1.0) - v37)) * (v11 * treplicate 5 x49 + v12 * treplicate 5 x48 + v13 * treplicate 5 x47 + v14 * treplicate 5 x46 + v15 * treplicate 5 x45) ; x53 = v52 ! [3] ; x54 = v52 ! [2] ; x55 = v52 ! [1] ; x56 = v52 ! [0] ; v59 = (v30 * (treplicate 3 (tconst 1.0) - v30)) * (v6 * treplicate 4 x56 + v7 * treplicate 4 x55 + v8 * treplicate 4 x54 + v9 * treplicate 4 x53) in (treplicate 784 (tconst 7.0) * treplicate 784 (v59 ! [0]), treplicate 784 (tconst 7.0) * treplicate 784 (v59 ! [1]), treplicate 784 (tconst 7.0) * treplicate 784 (v59 ! [2]), v59, v30 * treplicate 3 x56, v30 * treplicate 3 x55, v30 * treplicate 3 x54, v30 * treplicate 3 x53, v52, v37 * treplicate 4 x49, v37 * treplicate 4 x48, v37 * treplicate 4 x47, v37 * treplicate 4 x46, v37 * treplicate 4 x45, v44)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v30 = recip (treplicate 3 (tconst 1.0) + exp (negate (tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5))) ; v37 = recip (treplicate 4 (tconst 1.0) + exp (negate (tfromList [tsum (v6 * v30), tsum (v7 * v30), tsum (v8 * v30), tsum (v9 * v30)] + v10))) ; v41 = exp (tfromList [tsum (v11 * v37), tsum (v12 * v37), tsum (v13 * v37), tsum (v14 * v37), tsum (v15 * v37)] + v16) in treplicate 5 (recip (tsum v41)) * v41"

valsInitVT2OPP :: MnistFcnnRanked2.ADFcnnMnist2Parameters (Flip OR.Array) Double
valsInitVT2OPP =
  ( ( Flip $ OR.fromList [3, 3] (concat $ replicate 3 [1, 2, 3])
    , Flip $ OR.fromList [3] [1, 2, 3] )
  , ( Flip $ OR.fromList [4, 4] (concat $ replicate 4 [1, 2, 3, 4])
    , Flip $ OR.fromList [4] [1, 2, 3, 4] )
  , ( Flip $ OR.fromList [5, 5] (concat $ replicate 5 [1, 2, 3, 4, 5])
    , Flip $ OR.fromList [5] [1, 2, 3, 4, 5] ) )

testVT2OPP :: Assertion
testVT2OPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate sizeMnistGlyphInt 7
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters AstRanked Double
              -> AstRanked Double 1
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id blackGlyph
      (artifact6, _) = revDtFun True afcnn2T valsInitVT2OPP
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let m11 = treplicate 3 (treplicate 784 (tconst 7.0)) ; m12 = treplicate 4 (tcast (tsum (ttranspose [1,0] (m11 * m2)) + v3)) ; m13 = treplicate 5 (tcast (tsum (ttranspose [1,0] (m12 * m4))) + v5) ; v14 = tsum (m6 * ttranspose [1,0] (treplicate 4 dret)) ; m15 = ttranspose [1,0] (treplicate 3 (tcast v14)) ; v16 = tcast (tsum (m4 * m15)) in (m11 * ttranspose [1,0] (treplicate 784 v16), v16, m12 * m15, v14, m13 * ttranspose [1,0] (treplicate 4 dret), dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 v3 m4 v5 m6 v7 -> let m11 = treplicate 3 (treplicate 784 (tconst 7.0)) ; m12 = treplicate 4 (tcast (tsum (ttranspose [1,0] (m11 * m2)) + v3)) ; m13 = treplicate 5 (tcast (tsum (ttranspose [1,0] (m12 * m4))) + v5) in tsum (ttranspose [1,0] (m13 * m6)) + v7"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let m12 = treplicate 4 (tcast (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3)) ; v14 = tsum (m6 * ttranspose [1,0] (treplicate 4 dret)) ; m15 = ttranspose [1,0] (treplicate 3 (tcast v14)) ; v16 = tcast (tsum (m4 * m15)) in (treplicate 3 (treplicate 784 (tconst 7.0)) * ttranspose [1,0] (treplicate 784 v16), v16, m12 * m15, v14, treplicate 5 (tcast (tsum (ttranspose [1,0] (m12 * m4))) + v5) * ttranspose [1,0] (treplicate 4 dret), dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 v3 m4 v5 m6 v7 -> tsum (ttranspose [1,0] (treplicate 5 (tcast (tsum (ttranspose [1,0] (treplicate 4 (tcast (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3)) * m4))) + v5) * m6)) + v7"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters AstRanked Double
                    -> AstRanked Double 1
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      (artifact6nonLin, _) = revDtFun True afcnn2TnonLin valsInitVT2OPP
  printGradient6Pretty renames artifact6nonLin
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let m16 = treplicate 3 (treplicate 784 (tconst 7.0)) ; v17 = tsum (ttranspose [1,0] (m16 * m2)) + v3 ; v20 = let v18 = exp (negate v17) ; v19 = treplicate 3 (tconst 1.0) + v18 in recip v19 ; v21 = treplicate 3 (tconst 1.0) - v20 ; v22 = v20 * v21 ; m23 = treplicate 4 (tcast v20) ; v24 = tcast (tsum (ttranspose [1,0] (m23 * m4))) + v5 ; v27 = let v25 = exp (negate v24) ; v26 = treplicate 4 (tconst 1.0) + v25 in recip v26 ; v28 = treplicate 4 (tconst 1.0) - v27 ; v29 = v27 * v28 ; m30 = treplicate 5 v27 ; v31 = exp (tsum (ttranspose [1,0] (m30 * m6)) + v7) ; x32 = tsum v31 ; v33 = treplicate 5 (recip x32) ; v34 = v31 * (treplicate 5 (negate (recip (x32 * x32)) * tsum (v31 * dret)) + v33 * dret) ; v35 = tsum (m6 * ttranspose [1,0] (treplicate 4 v34)) ; v36 = v27 * (v24 * v35) ; v37 = v29 * v35 ; m38 = ttranspose [1,0] (treplicate 3 (tcast v37)) ; v39 = tcast (tsum (m4 * m38)) ; v40 = v20 * (v17 * v39) ; v41 = v22 * v39 in (m16 * ttranspose [1,0] (treplicate 784 v41), v41, m23 * m38, v37, m30 * ttranspose [1,0] (treplicate 4 v34), v34)"
  printPrimal6Pretty renames artifact6nonLin
    @?= "\\m2 v3 m4 v5 m6 v7 -> let m16 = treplicate 3 (treplicate 784 (tconst 7.0)) ; v17 = tsum (ttranspose [1,0] (m16 * m2)) + v3 ; v20 = let v18 = exp (negate v17) ; v19 = treplicate 3 (tconst 1.0) + v18 in recip v19 ; v21 = treplicate 3 (tconst 1.0) - v20 ; v22 = v20 * v21 ; m23 = treplicate 4 (tcast v20) ; v24 = tcast (tsum (ttranspose [1,0] (m23 * m4))) + v5 ; v27 = let v25 = exp (negate v24) ; v26 = treplicate 4 (tconst 1.0) + v25 in recip v26 ; v28 = treplicate 4 (tconst 1.0) - v27 ; v29 = v27 * v28 ; m30 = treplicate 5 v27 ; v31 = exp (tsum (ttranspose [1,0] (m30 * m6)) + v7) ; x32 = tsum v31 ; v33 = treplicate 5 (recip x32) in v33 * v31"
  printGradient6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let v20 = recip (treplicate 3 (tconst 1.0) + exp (negate (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3))) ; m23 = treplicate 4 (tcast v20) ; v27 = recip (treplicate 4 (tconst 1.0) + exp (negate (tcast (tsum (ttranspose [1,0] (m23 * m4))) + v5))) ; v31 = exp (tsum (ttranspose [1,0] (treplicate 5 v27 * m6)) + v7) ; x32 = tsum v31 ; v34 = v31 * (treplicate 5 (negate (recip (x32 * x32)) * tsum (v31 * dret)) + treplicate 5 (recip x32) * dret) ; v37 = (v27 * (treplicate 4 (tconst 1.0) - v27)) * tsum (m6 * ttranspose [1,0] (treplicate 4 v34)) ; m38 = ttranspose [1,0] (treplicate 3 (tcast v37)) ; v41 = (v20 * (treplicate 3 (tconst 1.0) - v20)) * tcast (tsum (m4 * m38)) in (treplicate 3 (treplicate 784 (tconst 7.0)) * ttranspose [1,0] (treplicate 784 v41), v41, m23 * m38, v37, treplicate 5 v27 * ttranspose [1,0] (treplicate 4 v34), v34)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\m2 v3 m4 v5 m6 v7 -> let v31 = exp (tsum (ttranspose [1,0] (treplicate 5 (recip (treplicate 4 (tconst 1.0) + exp (negate (tcast (tsum (ttranspose [1,0] (treplicate 4 (tcast (recip (treplicate 3 (tconst 1.0) + exp (negate (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3))))) * m4))) + v5)))) * m6)) + v7) in treplicate 5 (recip (tsum v31)) * v31"
