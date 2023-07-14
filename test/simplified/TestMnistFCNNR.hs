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
     ( ranked ~ Flip OR.Array, Differentiable r
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
     ( ranked ~ Flip OR.Array, Differentiable r
     , ADReady ranked r
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
     ( ranked ~ Flip OR.Array, Differentiable r
     , ADReady ranked r, PrintfArg r, AssertEqualUpToEpsilon r )
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
     ( ranked ~ Flip OR.Array, Differentiable r
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
     ( ranked ~ Flip OR.Array, Differentiable r
     , ADReady ranked r, Random r
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
     ( ranked ~ Flip OR.Array, Differentiable r
     , ADReady ranked r, Random r , PrintfArg r, AssertEqualUpToEpsilon r )
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
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5 ; v20 = tfromList [tsum (v6 * v19), tsum (v7 * v19), tsum (v8 * v19), tsum (v9 * v19)] + v10 ; x21 = dret ! [4] ; x22 = dret ! [3] ; x23 = dret ! [2] ; x24 = dret ! [1] ; x25 = dret ! [0] ; v26 = v11 * treplicate 5 x25 + v12 * treplicate 5 x24 + v13 * treplicate 5 x23 + v14 * treplicate 5 x22 + v15 * treplicate 5 x21 ; x27 = v26 ! [3] ; x28 = v26 ! [2] ; x29 = v26 ! [1] ; x30 = v26 ! [0] ; v31 = v6 * treplicate 4 x30 + v7 * treplicate 4 x29 + v8 * treplicate 4 x28 + v9 * treplicate 4 x27 ; x32 = v31 ! [2] ; x33 = v31 ! [1] ; x34 = v31 ! [0] in (treplicate 784 (tconst 7.0) * treplicate 784 x34, treplicate 784 (tconst 7.0) * treplicate 784 x33, treplicate 784 (tconst 7.0) * treplicate 784 x32, v31, v19 * treplicate 3 x30, v19 * treplicate 3 x29, v19 * treplicate 3 x28, v19 * treplicate 3 x27, v26, v20 * treplicate 4 x25, v20 * treplicate 4 x24, v20 * treplicate 4 x23, v20 * treplicate 4 x22, v20 * treplicate 4 x21, dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5 ; v20 = tfromList [tsum (v6 * v19), tsum (v7 * v19), tsum (v8 * v19), tsum (v9 * v19)] + v10 in tfromList [tsum (v11 * v20), tsum (v12 * v20), tsum (v13 * v20), tsum (v14 * v20), tsum (v15 * v20)] + v16"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5 ; v20 = tfromList [tsum (v6 * v19), tsum (v7 * v19), tsum (v8 * v19), tsum (v9 * v19)] + v10 ; x21 = dret ! [4] ; x22 = dret ! [3] ; x23 = dret ! [2] ; x24 = dret ! [1] ; x25 = dret ! [0] ; v26 = v11 * treplicate 5 x25 + v12 * treplicate 5 x24 + v13 * treplicate 5 x23 + v14 * treplicate 5 x22 + v15 * treplicate 5 x21 ; x27 = v26 ! [3] ; x28 = v26 ! [2] ; x29 = v26 ! [1] ; x30 = v26 ! [0] ; v31 = v6 * treplicate 4 x30 + v7 * treplicate 4 x29 + v8 * treplicate 4 x28 + v9 * treplicate 4 x27 in (treplicate 784 (tconst 7.0) * treplicate 784 (v31 ! [0]), treplicate 784 (tconst 7.0) * treplicate 784 (v31 ! [1]), treplicate 784 (tconst 7.0) * treplicate 784 (v31 ! [2]), v31, v19 * treplicate 3 x30, v19 * treplicate 3 x29, v19 * treplicate 3 x28, v19 * treplicate 3 x27, v26, v20 * treplicate 4 x25, v20 * treplicate 4 x24, v20 * treplicate 4 x23, v20 * treplicate 4 x22, v20 * treplicate 4 x21, dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5 ; v20 = tfromList [tsum (v6 * v19), tsum (v7 * v19), tsum (v8 * v19), tsum (v9 * v19)] + v10 in tfromList [tsum (v11 * v20), tsum (v12 * v20), tsum (v13 * v20), tsum (v14 * v20), tsum (v15 * v20)] + v16"

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
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v24 = tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5 ; v27 = let v25 = exp (negate v24) ; v26 = treplicate 3 (tconst 1.0) + v25 in recip v26 ; v28 = treplicate 3 (tconst 1.0) - v27 ; v29 = v27 * v28 ; v30 = v27 ; v31 = tfromList [tsum (v6 * v30), tsum (v7 * v30), tsum (v8 * v30), tsum (v9 * v30)] + v10 ; v34 = let v32 = exp (negate v31) ; v33 = treplicate 4 (tconst 1.0) + v32 in recip v33 ; v35 = treplicate 4 (tconst 1.0) - v34 ; v36 = v34 * v35 ; v37 = v34 ; v38 = exp (tfromList [tsum (v11 * v37), tsum (v12 * v37), tsum (v13 * v37), tsum (v14 * v37), tsum (v15 * v37)] + v16) ; x39 = tsum v38 ; v40 = treplicate 5 (recip x39) ; v41 = v38 * (treplicate 5 (negate (recip (x39 * x39)) * tsum (v38 * dret)) + v40 * dret) ; x42 = v41 ! [4] ; x43 = v41 ! [3] ; x44 = v41 ! [2] ; x45 = v41 ! [1] ; x46 = v41 ! [0] ; v47 = v11 * treplicate 5 x46 + v12 * treplicate 5 x45 + v13 * treplicate 5 x44 + v14 * treplicate 5 x43 + v15 * treplicate 5 x42 ; v48 = v34 * (v31 * v47) ; v49 = v36 * v47 ; x50 = v49 ! [3] ; x51 = v49 ! [2] ; x52 = v49 ! [1] ; x53 = v49 ! [0] ; v54 = v6 * treplicate 4 x53 + v7 * treplicate 4 x52 + v8 * treplicate 4 x51 + v9 * treplicate 4 x50 ; v55 = v27 * (v24 * v54) ; v56 = v29 * v54 ; x57 = v56 ! [2] ; x58 = v56 ! [1] ; x59 = v56 ! [0] in (treplicate 784 (tconst 7.0) * treplicate 784 x59, treplicate 784 (tconst 7.0) * treplicate 784 x58, treplicate 784 (tconst 7.0) * treplicate 784 x57, v56, v30 * treplicate 3 x53, v30 * treplicate 3 x52, v30 * treplicate 3 x51, v30 * treplicate 3 x50, v49, v37 * treplicate 4 x46, v37 * treplicate 4 x45, v37 * treplicate 4 x44, v37 * treplicate 4 x43, v37 * treplicate 4 x42, v41)"
  printPrimal6Pretty renames artifact6nonLin
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v24 = tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5 ; v27 = let v25 = exp (negate v24) ; v26 = treplicate 3 (tconst 1.0) + v25 in recip v26 ; v28 = treplicate 3 (tconst 1.0) - v27 ; v29 = v27 * v28 ; v30 = v27 ; v31 = tfromList [tsum (v6 * v30), tsum (v7 * v30), tsum (v8 * v30), tsum (v9 * v30)] + v10 ; v34 = let v32 = exp (negate v31) ; v33 = treplicate 4 (tconst 1.0) + v32 in recip v33 ; v35 = treplicate 4 (tconst 1.0) - v34 ; v36 = v34 * v35 ; v37 = v34 ; v38 = exp (tfromList [tsum (v11 * v37), tsum (v12 * v37), tsum (v13 * v37), tsum (v14 * v37), tsum (v15 * v37)] + v16) ; x39 = tsum v38 ; v40 = treplicate 5 (recip x39) in v40 * v38"
  printGradient6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v27 = recip (treplicate 3 (tconst 1.0) + exp (negate (tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5))) ; v34 = recip (treplicate 4 (tconst 1.0) + exp (negate (tfromList [tsum (v6 * v27), tsum (v7 * v27), tsum (v8 * v27), tsum (v9 * v27)] + v10))) ; v38 = exp (tfromList [tsum (v11 * v34), tsum (v12 * v34), tsum (v13 * v34), tsum (v14 * v34), tsum (v15 * v34)] + v16) ; x39 = tsum v38 ; v41 = v38 * (treplicate 5 (negate (recip (x39 * x39)) * tsum (v38 * dret)) + treplicate 5 (recip x39) * dret) ; x42 = v41 ! [4] ; x43 = v41 ! [3] ; x44 = v41 ! [2] ; x45 = v41 ! [1] ; x46 = v41 ! [0] ; v49 = (v34 * (treplicate 4 (tconst 1.0) - v34)) * (v11 * treplicate 5 x46 + v12 * treplicate 5 x45 + v13 * treplicate 5 x44 + v14 * treplicate 5 x43 + v15 * treplicate 5 x42) ; x50 = v49 ! [3] ; x51 = v49 ! [2] ; x52 = v49 ! [1] ; x53 = v49 ! [0] ; v56 = (v27 * (treplicate 3 (tconst 1.0) - v27)) * (v6 * treplicate 4 x53 + v7 * treplicate 4 x52 + v8 * treplicate 4 x51 + v9 * treplicate 4 x50) in (treplicate 784 (tconst 7.0) * treplicate 784 (v56 ! [0]), treplicate 784 (tconst 7.0) * treplicate 784 (v56 ! [1]), treplicate 784 (tconst 7.0) * treplicate 784 (v56 ! [2]), v56, v27 * treplicate 3 x53, v27 * treplicate 3 x52, v27 * treplicate 3 x51, v27 * treplicate 3 x50, v49, v34 * treplicate 4 x46, v34 * treplicate 4 x45, v34 * treplicate 4 x44, v34 * treplicate 4 x43, v34 * treplicate 4 x42, v41)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v27 = recip (treplicate 3 (tconst 1.0) + exp (negate (tfromList [tsum (v2 * treplicate 784 (tconst 7.0)), tsum (v3 * treplicate 784 (tconst 7.0)), tsum (v4 * treplicate 784 (tconst 7.0))] + v5))) ; v34 = recip (treplicate 4 (tconst 1.0) + exp (negate (tfromList [tsum (v6 * v27), tsum (v7 * v27), tsum (v8 * v27), tsum (v9 * v27)] + v10))) ; v38 = exp (tfromList [tsum (v11 * v34), tsum (v12 * v34), tsum (v13 * v34), tsum (v14 * v34), tsum (v15 * v34)] + v16) in treplicate 5 (recip (tsum v38)) * v38"

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
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let m11 = treplicate 4 (tcast (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3)) ; m12 = treplicate 5 (tcast (tsum (ttranspose [1,0] (m11 * m4))) + v5) ; v13 = tsum (m6 * ttranspose [1,0] (treplicate 4 dret)) ; m14 = ttranspose [1,0] (treplicate 3 (tcast v13)) ; v15 = tcast (tsum (m4 * m14)) in (treplicate 3 (treplicate 784 (tconst 7.0)) * ttranspose [1,0] (treplicate 784 v15), v15, m11 * m14, v13, m12 * ttranspose [1,0] (treplicate 4 dret), dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 v3 m4 v5 m6 v7 -> let m11 = treplicate 4 (tcast (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3)) ; m12 = treplicate 5 (tcast (tsum (ttranspose [1,0] (m11 * m4))) + v5) in tsum (ttranspose [1,0] (m12 * m6)) + v7"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let m11 = treplicate 4 (tcast (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3)) ; v13 = tsum (m6 * ttranspose [1,0] (treplicate 4 dret)) ; m14 = ttranspose [1,0] (treplicate 3 (tcast v13)) ; v15 = tcast (tsum (m4 * m14)) in (treplicate 3 (treplicate 784 (tconst 7.0)) * ttranspose [1,0] (treplicate 784 v15), v15, m11 * m14, v13, treplicate 5 (tcast (tsum (ttranspose [1,0] (m11 * m4))) + v5) * ttranspose [1,0] (treplicate 4 dret), dret)"
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
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let v16 = tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3 ; v19 = let v17 = exp (negate v16) ; v18 = treplicate 3 (tconst 1.0) + v17 in recip v18 ; v20 = treplicate 3 (tconst 1.0) - v19 ; v21 = v19 * v20 ; m22 = treplicate 4 (tcast v19) ; v23 = tcast (tsum (ttranspose [1,0] (m22 * m4))) + v5 ; v26 = let v24 = exp (negate v23) ; v25 = treplicate 4 (tconst 1.0) + v24 in recip v25 ; v27 = treplicate 4 (tconst 1.0) - v26 ; v28 = v26 * v27 ; m29 = treplicate 5 v26 ; v30 = exp (tsum (ttranspose [1,0] (m29 * m6)) + v7) ; x31 = tsum v30 ; v32 = treplicate 5 (recip x31) ; v33 = v30 * (treplicate 5 (negate (recip (x31 * x31)) * tsum (v30 * dret)) + v32 * dret) ; v34 = tsum (m6 * ttranspose [1,0] (treplicate 4 v33)) ; v35 = v26 * (v23 * v34) ; v36 = v28 * v34 ; m37 = ttranspose [1,0] (treplicate 3 (tcast v36)) ; v38 = tcast (tsum (m4 * m37)) ; v39 = v19 * (v16 * v38) ; v40 = v21 * v38 in (treplicate 3 (treplicate 784 (tconst 7.0)) * ttranspose [1,0] (treplicate 784 v40), v40, m22 * m37, v36, m29 * ttranspose [1,0] (treplicate 4 v33), v33)"
  printPrimal6Pretty renames artifact6nonLin
    @?= "\\m2 v3 m4 v5 m6 v7 -> let v16 = tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3 ; v19 = let v17 = exp (negate v16) ; v18 = treplicate 3 (tconst 1.0) + v17 in recip v18 ; v20 = treplicate 3 (tconst 1.0) - v19 ; v21 = v19 * v20 ; m22 = treplicate 4 (tcast v19) ; v23 = tcast (tsum (ttranspose [1,0] (m22 * m4))) + v5 ; v26 = let v24 = exp (negate v23) ; v25 = treplicate 4 (tconst 1.0) + v24 in recip v25 ; v27 = treplicate 4 (tconst 1.0) - v26 ; v28 = v26 * v27 ; m29 = treplicate 5 v26 ; v30 = exp (tsum (ttranspose [1,0] (m29 * m6)) + v7) ; x31 = tsum v30 ; v32 = treplicate 5 (recip x31) in v32 * v30"
  printGradient6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let v19 = recip (treplicate 3 (tconst 1.0) + exp (negate (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3))) ; m22 = treplicate 4 (tcast v19) ; v26 = recip (treplicate 4 (tconst 1.0) + exp (negate (tcast (tsum (ttranspose [1,0] (m22 * m4))) + v5))) ; v30 = exp (tsum (ttranspose [1,0] (treplicate 5 v26 * m6)) + v7) ; x31 = tsum v30 ; v33 = v30 * (treplicate 5 (negate (recip (x31 * x31)) * tsum (v30 * dret)) + treplicate 5 (recip x31) * dret) ; v36 = (v26 * (treplicate 4 (tconst 1.0) - v26)) * tsum (m6 * ttranspose [1,0] (treplicate 4 v33)) ; m37 = ttranspose [1,0] (treplicate 3 (tcast v36)) ; v40 = (v19 * (treplicate 3 (tconst 1.0) - v19)) * tcast (tsum (m4 * m37)) in (treplicate 3 (treplicate 784 (tconst 7.0)) * ttranspose [1,0] (treplicate 784 v40), v40, m22 * m37, v36, treplicate 5 v26 * ttranspose [1,0] (treplicate 4 v33), v33)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\m2 v3 m4 v5 m6 v7 -> let v30 = exp (tsum (ttranspose [1,0] (treplicate 5 (recip (treplicate 4 (tconst 1.0) + exp (negate (tcast (tsum (ttranspose [1,0] (treplicate 4 (tcast (recip (treplicate 3 (tconst 1.0) + exp (negate (tsum (ttranspose [1,0] (treplicate 3 (treplicate 784 (tconst 7.0)) * m2)) + v3))))) * m4))) + v5)))) * m6)) + v7) in treplicate 5 (recip (tsum v30)) * v30"
