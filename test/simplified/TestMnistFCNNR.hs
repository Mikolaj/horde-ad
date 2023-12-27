-- | Tests of "MnistFcnnRanked1" and "MnistFcnnRanked2" neural networks
-- using a few different optimization pipelines.
module TestMnistFCNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.List.Index (imap)
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (Nat, SomeNat (..), someNatVal)
import qualified Numeric.LinearAlgebra as LA
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
  (funToAstIOR, funToAstR, funToAstRevIO, resetVarCounter)
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


-- * Using lists of vectors, which is rank 1

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCase1VTA
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTA prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ Flip $ OR.fromVector [nPV]
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
      domainsInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length params1Init)
                        , show (sizeDomainsOD domainsInit)
                        , show gamma ]
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 valsInit widthHidden widthHidden2
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
             let f :: MnistData r -> Domains (ADVal (Flip OR.Array))
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
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase1VTA
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADValMnistTests :: TestTree
tensorADValMnistTests = testGroup "Ranked ADVal MNIST tests"
  [ mnistTestCase1VTA "VTA 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16600000000000004 :: Double)
  , mnistTestCase1VTA "VTA artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.8972 :: Float)
  , mnistTestCase1VTA "VTA artificial 5 4 3 2 1" 5 4 3 2 1 4999
                      (0.8210999999999999 :: Double)
  , mnistTestCase1VTA "VTA 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCase1VTI
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTI prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ Flip $ OR.fromVector [nPV]
          $ V.map realToFrac
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = Flip $ OR.fromList [0] []
      domainsInit = V.fromList params1Init
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
                        , show (sizeDomainsOD domainsInit)
                        , show gamma ]
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 valsInit widthHidden widthHidden2
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, domainsPrimal, vars, _) <- funToAstRevIO domainsInit
       (varGlyph, _, astGlyph) <-
         funToAstIOR (singletonShape sizeMnistGlyphInt) id
       (varLabel, _, astLabel) <-
         funToAstIOR (singletonShape sizeMnistLabelInt) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistFcnnRanked1.afcnnMnistLoss1TensorData
                   widthHidden widthHidden2 (astGlyph, astLabel)
                   (parseDomains valsInit domainsPrimal)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: DomainsOD -> (Int, [MnistData r]) -> IO DomainsOD
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADVal (Flip OR.Array))
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvD EM.empty
                             $ zip vars $ V.toList varInputs
                       envMnist =
                         extendEnvR varGlyph
                           (rconst $ OR.fromVector [sizeMnistGlyphInt] glyph)
                         $ extendEnvR varLabel
                             (rconst $ OR.fromVector [sizeMnistLabelInt] label)
                             env
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
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase1VTI
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorIntermediateMnistTests :: TestTree
tensorIntermediateMnistTests = testGroup "Ranked Intermediate MNIST tests"
  [ mnistTestCase1VTI "VTI 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase1VTI "VTI artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.902 :: Float)
  , mnistTestCase1VTI "VTI artificial 5 4 3 2 1" 5 4 3 2 1 4999
                      (0.7541 :: Double)
  , mnistTestCase1VTI "VTI 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCase1VTO
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTO prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ Flip $ OR.fromVector [nPV]
          $ V.map realToFrac
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = Flip $ OR.fromList [0] []
      domainsInit = V.fromList params1Init
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
                        , show (sizeDomainsOD domainsInit)
                        , show gamma ]
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 valsInit widthHidden widthHidden2
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
       let envInit = extendEnvR varGlyph (rconstant astGlyph)
                     $ extendEnvR varLabel (rconstant astLabel)
                     EM.empty
           f = MnistFcnnRanked1.afcnnMnistLoss1TensorData @(AstRanked FullSpan)
                 widthHidden widthHidden2
                 (rconstant astGlyph, rconstant astLabel)
           g domains = f $ parseDomains valsInit domains
           (((varDtAgain, vars1Again), gradientRaw, primal, sh), _) =
             revProduceArtifact TensorToken True False g envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistData r] -> DomainsOD -> DomainsOD
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicRanked @r @1
                          $ Flip $ OR.fromVector [sizeMnistGlyphInt] glyph
                 labelD = DynamicRanked @r @1
                          $ Flip $ OR.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientDomain =
                   fst $ revEvalArtifact @Nat @(AstRanked FullSpan)
                                         (vars, gradient, primal, sh)
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
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase1VTO
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADOnceMnistTests :: TestTree
tensorADOnceMnistTests = testGroup "Ranked Once MNIST tests"
  [ mnistTestCase1VTO "VTO 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase1VTO "VTO artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase1VTO "VTO artificial 5 4 3 2 1" 5 4 3 2 1 4999
                      (0.7034 :: Double)
  , mnistTestCase1VTO "VTO 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]


-- * Using matrices, which is rank 2

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCase2VTA
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTA prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
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
      ftest = MnistFcnnRanked2.afcnnMnistTest2 valsInit
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
             let f :: MnistData r -> Domains (ADVal (Flip OR.Array))
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

{-# SPECIALIZE mnistTestCase2VTA
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADValMnistTests2 :: TestTree
tensorADValMnistTests2 = testGroup "Ranked2 ADVal MNIST tests"
  [ mnistTestCase2VTA "VTA2 1 epoch, 1 batch" 1 1 300 100 0.02 5
                       (0.8 :: Double)
  , mnistTestCase2VTA "VTA2 artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.89 :: Float)
  , mnistTestCase2VTA "VTA2 artificial 5 4 3 2 1" 5 4 3 2 1 499
                       (0.8361723446893787 :: Double)
  , mnistTestCase2VTA "VTA2 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCase2VTI
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTI prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Nothing -> error "impossible someNatVal error"
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
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
      ftest = MnistFcnnRanked2.afcnnMnistTest2 valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, domainsPrimal, vars, _) <- funToAstRevIO domainsInit
       (varGlyph, _, astGlyph) <-
         funToAstIOR (singletonShape sizeMnistGlyphInt) id
       (varLabel, _, astLabel) <-
         funToAstIOR (singletonShape sizeMnistLabelInt) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistFcnnRanked2.afcnnMnistLoss2TensorData
                   (astGlyph, astLabel) (parseDomains valsInit domainsPrimal)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: DomainsOD -> (Int, [MnistData r]) -> IO DomainsOD
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADVal (Flip OR.Array))
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvD EM.empty
                             $ zip vars $ V.toList varInputs
                       envMnist =
                         extendEnvR varGlyph
                           (rconst $ OR.fromVector [sizeMnistGlyphInt] glyph)
                         $ extendEnvR varLabel
                             (rconst $ OR.fromVector [sizeMnistLabelInt] label)
                             env
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
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VTI
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorIntermediateMnistTests2 :: TestTree
tensorIntermediateMnistTests2 = testGroup "Ranked2 Intermediate MNIST tests"
  [ mnistTestCase2VTI "VTI2 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.534 :: Double)
  , mnistTestCase2VTI "VTI2 artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VTI "VTI2 artificial 5 4 3 2 1" 5 4 3 2 1 499
                       (0.7464929859719439 :: Double)
  , mnistTestCase2VTI "VTI2 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCase2VTO
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTO prefix epochs maxBatches widthHidden widthHidden2
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
        valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
        valsInit =
          -- This almost works and I wouldn't need forgetShape,
          -- but there is nowhere to get aInit from.
          --   parseDomains aInit domainsInit
          forgetShape valsInitShaped
        domainsInit = toDomains valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show widthHidden, show widthHidden2
                          , show (V.length domainsInit)
                          , show (sizeDomainsOD domainsInit)
                          , show gamma ]
        ftest :: [MnistData r] -> DomainsOD -> r
        ftest = MnistFcnnRanked2.afcnnMnistTest2 valsInit
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
       let envInit = extendEnvR varGlyph (rconstant astGlyph)
                     $ extendEnvR varLabel (rconstant astLabel)
                       EM.empty
           f = MnistFcnnRanked2.afcnnMnistLoss2TensorData @(AstRanked FullSpan)
                 (rconstant astGlyph, rconstant astLabel)
           g domains = f $ parseDomains valsInit domains
           (((varDtAgain, vars1Again), gradientRaw, primal, sh), _) =
             revProduceArtifact TensorToken True False g envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistData r] -> DomainsOD -> DomainsOD
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicRanked @r @1
                          $ Flip $ OR.fromVector [sizeMnistGlyphInt] glyph
                 labelD = DynamicRanked @r @1
                          $ Flip $ OR.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientDomain =
                   fst $ revEvalArtifact @Nat @(AstRanked FullSpan)
                                         (vars, gradient, primal, sh)
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
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VTO
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADOnceMnistTests2 :: TestTree
tensorADOnceMnistTests2 = testGroup "Ranked2 Once MNIST tests"
  [ mnistTestCase2VTO "VTO2 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.534 :: Double)
  , mnistTestCase2VTO "VTO2 artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VTO "VTO2 artificial 5 4 3 2 1" 5 4 3 2 1 499
                       (0.7945891783567134 :: Double)
  , mnistTestCase2VTO "VTO2 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for Short Ranked MNIST tests"
  [ testCase "VTOPP" testVTOPP
  , testCase "VTOPPNonLin" testVTOPPNonLin
  , testCase "VT2OPP" testVT2OPP
  , testCase "VT2OPPNonLin" testVT2OPPNonLin
  , testCase "VT2OPPNonLin2" testVT2OPPNonLin2
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
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters (AstRanked FullSpan)
                                                         Double
              -> AstRanked FullSpan Double 1
      afcnn2T = MnistFcnnRanked1.afcnnMnist1 id id 3 4 blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVTOPP
  printGradient6Pretty renames artifactRev
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = rfromList [rsum (v2 * rreplicate 784 (rconst 7.0)), rsum (v3 * rreplicate 784 (rconst 7.0)), rsum (v4 * rreplicate 784 (rconst 7.0))] + v5 ; v20 = rfromList [rsum (v6 * v19), rsum (v7 * v19), rsum (v8 * v19), rsum (v9 * v19)] + v10 ; x21 = dret ! [4] ; x22 = dret ! [3] ; x23 = dret ! [2] ; x24 = dret ! [1] ; x25 = dret ! [0] ; v26 = v11 * rreplicate 5 x25 + v12 * rreplicate 5 x24 + v13 * rreplicate 5 x23 + v14 * rreplicate 5 x22 + v15 * rreplicate 5 x21 ; x27 = v26 ! [3] ; x28 = v26 ! [2] ; x29 = v26 ! [1] ; x30 = v26 ! [0] ; v31 = v6 * rreplicate 4 x30 + v7 * rreplicate 4 x29 + v8 * rreplicate 4 x28 + v9 * rreplicate 4 x27 ; x32 = v31 ! [2] ; x33 = v31 ! [1] ; x34 = v31 ! [0] in (rreplicate 784 (rconst 7.0) * rreplicate 784 x34, rreplicate 784 (rconst 7.0) * rreplicate 784 x33, rreplicate 784 (rconst 7.0) * rreplicate 784 x32, v31, v19 * rreplicate 3 x30, v19 * rreplicate 3 x29, v19 * rreplicate 3 x28, v19 * rreplicate 3 x27, v26, v20 * rreplicate 4 x25, v20 * rreplicate 4 x24, v20 * rreplicate 4 x23, v20 * rreplicate 4 x22, v20 * rreplicate 4 x21, dret)"
  printPrimal6Pretty renames artifactRev
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = rfromList [rsum (v2 * rreplicate 784 (rconst 7.0)), rsum (v3 * rreplicate 784 (rconst 7.0)), rsum (v4 * rreplicate 784 (rconst 7.0))] + v5 ; v20 = rfromList [rsum (v6 * v19), rsum (v7 * v19), rsum (v8 * v19), rsum (v9 * v19)] + v10 in rfromList [rsum (v11 * v20), rsum (v12 * v20), rsum (v13 * v20), rsum (v14 * v20), rsum (v15 * v20)] + v16"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = rfromList [rsum (v2 * rreplicate 784 (rconst 7.0)), rsum (v3 * rreplicate 784 (rconst 7.0)), rsum (v4 * rreplicate 784 (rconst 7.0))] + v5 ; v20 = rfromList [rsum (v6 * v19), rsum (v7 * v19), rsum (v8 * v19), rsum (v9 * v19)] + v10 ; x21 = dret ! [4] ; x22 = dret ! [3] ; x23 = dret ! [2] ; x24 = dret ! [1] ; x25 = dret ! [0] ; v26 = v11 * rreplicate 5 x25 + v12 * rreplicate 5 x24 + v13 * rreplicate 5 x23 + v14 * rreplicate 5 x22 + v15 * rreplicate 5 x21 ; x27 = v26 ! [3] ; x28 = v26 ! [2] ; x29 = v26 ! [1] ; x30 = v26 ! [0] ; v31 = v6 * rreplicate 4 x30 + v7 * rreplicate 4 x29 + v8 * rreplicate 4 x28 + v9 * rreplicate 4 x27 in (rreplicate 784 (rconst 7.0) * rreplicate 784 (v31 ! [0]), rreplicate 784 (rconst 7.0) * rreplicate 784 (v31 ! [1]), rreplicate 784 (rconst 7.0) * rreplicate 784 (v31 ! [2]), v31, v19 * rreplicate 3 x30, v19 * rreplicate 3 x29, v19 * rreplicate 3 x28, v19 * rreplicate 3 x27, v26, v20 * rreplicate 4 x25, v20 * rreplicate 4 x24, v20 * rreplicate 4 x23, v20 * rreplicate 4 x22, v20 * rreplicate 4 x21, dret)"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v19 = rfromList [rsum (v2 * rreplicate 784 (rconst 7.0)), rsum (v3 * rreplicate 784 (rconst 7.0)), rsum (v4 * rreplicate 784 (rconst 7.0))] + v5 ; v20 = rfromList [rsum (v6 * v19), rsum (v7 * v19), rsum (v8 * v19), rsum (v9 * v19)] + v10 in rfromList [rsum (v11 * v20), rsum (v12 * v20), rsum (v13 * v20), rsum (v14 * v20), rsum (v15 * v20)] + v16"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                         (AstRanked FullSpan) Double
                    -> AstRanked FullSpan Double 1
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMax1 3 4 blackGlyph
      (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVTOPP
  printGradient6Pretty renames artifactRevnonLin
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v24 = rfromList [rsum (v2 * rreplicate 784 (rconst 7.0)), rsum (v3 * rreplicate 784 (rconst 7.0)), rsum (v4 * rreplicate 784 (rconst 7.0))] + v5 ; v25 = exp (negate v24) ; v26 = rreplicate 3 (rconst 1.0) + v25 ; v27 = recip v26 ; v28 = rreplicate 3 (rconst 1.0) - v27 ; v29 = v27 * v28 ; v30 = rfromList [rsum (v6 * v27), rsum (v7 * v27), rsum (v8 * v27), rsum (v9 * v27)] + v10 ; v31 = exp (negate v30) ; v32 = rreplicate 4 (rconst 1.0) + v31 ; v33 = recip v32 ; v34 = rreplicate 4 (rconst 1.0) - v33 ; v35 = v33 * v34 ; v36 = exp (rfromList [rsum (v11 * v33), rsum (v12 * v33), rsum (v13 * v33), rsum (v14 * v33), rsum (v15 * v33)] + v16) ; x37 = rsum v36 ; v38 = rreplicate 5 (recip x37) ; v39 = v36 * (rreplicate 5 (negate (recip (x37 * x37)) * rsum (v36 * dret)) + v38 * dret) ; x40 = v39 ! [4] ; x41 = v39 ! [3] ; x42 = v39 ! [2] ; x43 = v39 ! [1] ; x44 = v39 ! [0] ; v45 = v35 * (v11 * rreplicate 5 x44 + v12 * rreplicate 5 x43 + v13 * rreplicate 5 x42 + v14 * rreplicate 5 x41 + v15 * rreplicate 5 x40) ; x46 = v45 ! [3] ; x47 = v45 ! [2] ; x48 = v45 ! [1] ; x49 = v45 ! [0] ; v50 = v29 * (v6 * rreplicate 4 x49 + v7 * rreplicate 4 x48 + v8 * rreplicate 4 x47 + v9 * rreplicate 4 x46) ; x51 = v50 ! [2] ; x52 = v50 ! [1] ; x53 = v50 ! [0] in (rreplicate 784 (rconst 7.0) * rreplicate 784 x53, rreplicate 784 (rconst 7.0) * rreplicate 784 x52, rreplicate 784 (rconst 7.0) * rreplicate 784 x51, v50, v27 * rreplicate 3 x49, v27 * rreplicate 3 x48, v27 * rreplicate 3 x47, v27 * rreplicate 3 x46, v45, v33 * rreplicate 4 x44, v33 * rreplicate 4 x43, v33 * rreplicate 4 x42, v33 * rreplicate 4 x41, v33 * rreplicate 4 x40, v39)"
  printPrimal6Pretty renames artifactRevnonLin
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v24 = rfromList [rsum (v2 * rreplicate 784 (rconst 7.0)), rsum (v3 * rreplicate 784 (rconst 7.0)), rsum (v4 * rreplicate 784 (rconst 7.0))] + v5 ; v25 = exp (negate v24) ; v26 = rreplicate 3 (rconst 1.0) + v25 ; v27 = recip v26 ; v28 = rreplicate 3 (rconst 1.0) - v27 ; v29 = v27 * v28 ; v30 = rfromList [rsum (v6 * v27), rsum (v7 * v27), rsum (v8 * v27), rsum (v9 * v27)] + v10 ; v31 = exp (negate v30) ; v32 = rreplicate 4 (rconst 1.0) + v31 ; v33 = recip v32 ; v34 = rreplicate 4 (rconst 1.0) - v33 ; v35 = v33 * v34 ; v36 = exp (rfromList [rsum (v11 * v33), rsum (v12 * v33), rsum (v13 * v33), rsum (v14 * v33), rsum (v15 * v33)] + v16) ; x37 = rsum v36 ; v38 = rreplicate 5 (recip x37) in v38 * v36"
  printGradient6Pretty renames (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v27 = recip (rreplicate 3 (rconst 1.0) + exp (negate (rfromList [rsum (v2 * rreplicate 784 (rconst 7.0)), rsum (v3 * rreplicate 784 (rconst 7.0)), rsum (v4 * rreplicate 784 (rconst 7.0))] + v5))) ; v33 = recip (rreplicate 4 (rconst 1.0) + exp (negate (rfromList [rsum (v6 * v27), rsum (v7 * v27), rsum (v8 * v27), rsum (v9 * v27)] + v10))) ; v36 = exp (rfromList [rsum (v11 * v33), rsum (v12 * v33), rsum (v13 * v33), rsum (v14 * v33), rsum (v15 * v33)] + v16) ; x37 = rsum v36 ; v39 = v36 * (rreplicate 5 (negate (recip (x37 * x37)) * rsum (v36 * dret)) + rreplicate 5 (recip x37) * dret) ; x40 = v39 ! [4] ; x41 = v39 ! [3] ; x42 = v39 ! [2] ; x43 = v39 ! [1] ; x44 = v39 ! [0] ; v45 = (v33 * (rreplicate 4 (rconst 1.0) - v33)) * (v11 * rreplicate 5 x44 + v12 * rreplicate 5 x43 + v13 * rreplicate 5 x42 + v14 * rreplicate 5 x41 + v15 * rreplicate 5 x40) ; x46 = v45 ! [3] ; x47 = v45 ! [2] ; x48 = v45 ! [1] ; x49 = v45 ! [0] ; v50 = (v27 * (rreplicate 3 (rconst 1.0) - v27)) * (v6 * rreplicate 4 x49 + v7 * rreplicate 4 x48 + v8 * rreplicate 4 x47 + v9 * rreplicate 4 x46) in (rreplicate 784 (rconst 7.0) * rreplicate 784 (v50 ! [0]), rreplicate 784 (rconst 7.0) * rreplicate 784 (v50 ! [1]), rreplicate 784 (rconst 7.0) * rreplicate 784 (v50 ! [2]), v50, v27 * rreplicate 3 x49, v27 * rreplicate 3 x48, v27 * rreplicate 3 x47, v27 * rreplicate 3 x46, v45, v33 * rreplicate 4 x44, v33 * rreplicate 4 x43, v33 * rreplicate 4 x42, v33 * rreplicate 4 x41, v33 * rreplicate 4 x40, v39)"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRevnonLin)
    @?= "\\v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> let v27 = recip (rreplicate 3 (rconst 1.0) + exp (negate (rfromList [rsum (v2 * rreplicate 784 (rconst 7.0)), rsum (v3 * rreplicate 784 (rconst 7.0)), rsum (v4 * rreplicate 784 (rconst 7.0))] + v5))) ; v33 = recip (rreplicate 4 (rconst 1.0) + exp (negate (rfromList [rsum (v6 * v27), rsum (v7 * v27), rsum (v8 * v27), rsum (v9 * v27)] + v10))) ; v36 = exp (rfromList [rsum (v11 * v33), rsum (v12 * v33), rsum (v13 * v33), rsum (v14 * v33), rsum (v15 * v33)] + v16) in rreplicate 5 (recip (rsum v36)) * v36"

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
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                   (AstRanked FullSpan) Double
              -> AstRanked FullSpan Double 1
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVT2OPP
  printGradient6Pretty renames artifactRev
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let m11 = rreplicate 4 (rcast (rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * m2)) + v3)) ; m12 = rreplicate 5 (rcast (rsum (rtranspose [1,0] (m11 * m4))) + v5) ; v13 = rsum (m6 * rtranspose [1,0] (rreplicate 4 dret)) ; m14 = rtranspose [1,0] (rreplicate 3 (rcast v13)) ; v15 = rcast (rsum (m4 * m14)) in (rreplicate 3 (rreplicate 784 (rconst 7.0)) * rtranspose [1,0] (rreplicate 784 v15), v15, m11 * m14, v13, m12 * rtranspose [1,0] (rreplicate 4 dret), dret)"
  printPrimal6Pretty renames artifactRev
    @?= "\\m2 v3 m4 v5 m6 v7 -> let m11 = rreplicate 4 (rcast (rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * m2)) + v3)) ; m12 = rreplicate 5 (rcast (rsum (rtranspose [1,0] (m11 * m4))) + v5) in rsum (rtranspose [1,0] (m12 * m6)) + v7"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let m11 = rreplicate 4 (rcast (rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * m2)) + v3)) ; v13 = rsum (m6 * rtranspose [1,0] (rreplicate 4 dret)) ; m14 = rtranspose [1,0] (rreplicate 3 (rcast v13)) ; v15 = rcast (rsum (m4 * m14)) in (rreplicate 3 (rreplicate 784 (rconst 7.0)) * rtranspose [1,0] (rreplicate 784 v15), v15, m11 * m14, v13, rreplicate 5 (rcast (rsum (rtranspose [1,0] (m11 * m4))) + v5) * rtranspose [1,0] (rreplicate 4 dret), dret)"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m2 v3 m4 v5 m6 v7 -> rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rcast (rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * m2)) + v3)) * m4))) + v5) * m6)) + v7"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstRanked FullSpan) Float
                    -> AstRanked FullSpan Float 1
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      constant = let ((a1, a2), (a3, a4), (a5, a6)) = valsInitVT2OPP
                 in ( ( AstCast $ AstConstant $ AstConst $ runFlip a1
                      , AstCast $ AstConstant $ AstConst $ runFlip a2 )
                    , ( AstConstant $ AstCast $ AstConst $ runFlip a3
                      , AstConstant $ AstCast $ AstConst $ runFlip a4 )
                    , ( AstCast $ AstConstant $ AstConst $ runFlip a5
                      , AstConstant $ AstCast $ AstConst $ runFlip a6 ) )
      (_, ast3) = funToAstR @Float (singletonShape 0)
                                    (const $ afcnn2TnonLin constant)
  "\\dummy"
       ++ " -> " ++ printAstSimple renames ast3
    @?= "\\dummy -> rlet (exp (rsum (rtranspose [1,0] (rreplicate 5 (rlet (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rcast (rlet (rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * rconstant (rcast (rconst (fromList [3,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0]))))) + rcast (rconst (fromList [3] [1.0,2.0,3.0]))) (\\v5 -> rlet (rconstant (recip (rreplicate 3 (rconst 1.0) + exp (negate (rprimalPart v5))))) (\\v6 -> rD (rprimalPart v6) (rdualPart (rconstant (rprimalPart v6 * (rreplicate 3 (rconst 1.0) - rprimalPart v6)) * rD (rreplicate 3 (rconst 0.0)) (rdualPart v5))))))) * rconstant (rcast (rconst (fromList [4,4] [1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0])))))) + rconstant (rcast (rconst (fromList [4] [1.0,2.0,3.0,4.0])))) (\\v7 -> rlet (rconstant (recip (rreplicate 4 (rconst 1.0) + exp (negate (rprimalPart v7))))) (\\v8 -> rD (rprimalPart v8) (rdualPart (rconstant (rprimalPart v8 * (rreplicate 4 (rconst 1.0) - rprimalPart v8)) * rD (rreplicate 4 (rconst 0.0)) (rdualPart v7)))))) * rconstant (rcast (rconst (fromList [5,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))))) + rconstant (rcast (rconst (fromList [5] [1.0,2.0,3.0,4.0,5.0]))))) (\\v9 -> rreplicate 5 (recip (rsum v9)) * v9)"

testVT2OPPNonLin2 :: Assertion
testVT2OPPNonLin2 = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstRanked FullSpan) Double
                    -> AstRanked FullSpan Double 1
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
  let (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVT2OPP
  printGradient6Pretty renames artifactRevnonLin
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let v16 = rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * m2)) + v3 ; v17 = exp (negate v16) ; v18 = rreplicate 3 (rconst 1.0) + v17 ; v19 = recip v18 ; v20 = rreplicate 3 (rconst 1.0) - v19 ; v21 = v19 * v20 ; m22 = rreplicate 4 (rcast v19) ; v23 = rcast (rsum (rtranspose [1,0] (m22 * m4))) + v5 ; v24 = exp (negate v23) ; v25 = rreplicate 4 (rconst 1.0) + v24 ; v26 = recip v25 ; v27 = rreplicate 4 (rconst 1.0) - v26 ; v28 = v26 * v27 ; v29 = exp (rsum (rtranspose [1,0] (rreplicate 5 v26 * m6)) + v7) ; x30 = rsum v29 ; v31 = rreplicate 5 (recip x30) ; v32 = v29 * (rreplicate 5 (negate (recip (x30 * x30)) * rsum (v29 * dret)) + v31 * dret) ; v33 = v28 * rsum (m6 * rtranspose [1,0] (rreplicate 4 v32)) ; m34 = rtranspose [1,0] (rreplicate 3 (rcast v33)) ; v35 = v21 * rcast (rsum (m4 * m34)) in (rreplicate 3 (rreplicate 784 (rconst 7.0)) * rtranspose [1,0] (rreplicate 784 v35), v35, m22 * m34, v33, rreplicate 5 v26 * rtranspose [1,0] (rreplicate 4 v32), v32)"
  printPrimal6Pretty renames artifactRevnonLin
    @?= "\\m2 v3 m4 v5 m6 v7 -> let v16 = rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * m2)) + v3 ; v17 = exp (negate v16) ; v18 = rreplicate 3 (rconst 1.0) + v17 ; v19 = recip v18 ; v20 = rreplicate 3 (rconst 1.0) - v19 ; v21 = v19 * v20 ; m22 = rreplicate 4 (rcast v19) ; v23 = rcast (rsum (rtranspose [1,0] (m22 * m4))) + v5 ; v24 = exp (negate v23) ; v25 = rreplicate 4 (rconst 1.0) + v24 ; v26 = recip v25 ; v27 = rreplicate 4 (rconst 1.0) - v26 ; v28 = v26 * v27 ; v29 = exp (rsum (rtranspose [1,0] (rreplicate 5 v26 * m6)) + v7) ; x30 = rsum v29 ; v31 = rreplicate 5 (recip x30) in v31 * v29"
  printGradient6Pretty renames (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret m2 v3 m4 v5 m6 v7 -> let v19 = recip (rreplicate 3 (rconst 1.0) + exp (negate (rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * m2)) + v3))) ; m22 = rreplicate 4 (rcast v19) ; v26 = recip (rreplicate 4 (rconst 1.0) + exp (negate (rcast (rsum (rtranspose [1,0] (m22 * m4))) + v5))) ; v29 = exp (rsum (rtranspose [1,0] (rreplicate 5 v26 * m6)) + v7) ; x30 = rsum v29 ; v32 = v29 * (rreplicate 5 (negate (recip (x30 * x30)) * rsum (v29 * dret)) + rreplicate 5 (recip x30) * dret) ; v33 = (v26 * (rreplicate 4 (rconst 1.0) - v26)) * rsum (m6 * rtranspose [1,0] (rreplicate 4 v32)) ; m34 = rtranspose [1,0] (rreplicate 3 (rcast v33)) ; v35 = (v19 * (rreplicate 3 (rconst 1.0) - v19)) * rcast (rsum (m4 * m34)) in (rreplicate 3 (rreplicate 784 (rconst 7.0)) * rtranspose [1,0] (rreplicate 784 v35), v35, m22 * m34, v33, rreplicate 5 v26 * rtranspose [1,0] (rreplicate 4 v32), v32)"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRevnonLin)
    @?= "\\m2 v3 m4 v5 m6 v7 -> let v29 = exp (rsum (rtranspose [1,0] (rreplicate 5 (recip (rreplicate 4 (rconst 1.0) + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rcast (recip (rreplicate 3 (rconst 1.0) + exp (negate (rsum (rtranspose [1,0] (rreplicate 3 (rreplicate 784 (rconst 7.0)) * m2)) + v3))))) * m4))) + v5)))) * m6)) + v7) in rreplicate 5 (recip (rsum v29)) * v29"
