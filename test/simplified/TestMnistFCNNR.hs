module TestMnistFCNNR
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
  :: forall r.
     ( ADTensor r, ADReady r, ADReady (ADVal r)
     , Value r ~ r, Value (ADVal r) ~ r, Floating (Vector r)
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
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
      emptyR = OR.fromList [0] []
      -- valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length nParams1), show (sum nParams1)
                        , show gamma ]
      ftest :: [MnistData r] -> Domains r -> r
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
       let runBatch :: Domains r -> (Int, [MnistData r]) -> IO (Domains r)
           runBatch !domains (k, chunk) = do
             let f mnist adinputs =
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
       let runEpoch :: Int -> Domains r -> IO (Domains r)
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (mkDoms (dfromR $ Flip emptyR)
                                 (fromListDoms params1Init))
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

tensorADValMnistTests :: TestTree
tensorADValMnistTests = testGroup "Ranked ADVal MNIST tests"
  [ mnistTestCase2VTA "VTA 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16600000000000004 :: Double)
  , mnistTestCase2VTA "VTA artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.8972 :: Float)
  , mnistTestCase2VTA "VTA artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.6585 :: Double)
  , mnistTestCase2VTA "VTA 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCase2VTI
  :: forall r.
     ( ADTensor r, ADReady r, InterpretAst (ADVal r)
     , Value r ~ r, Value (ADVal r) ~ r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
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
      emptyR = OR.fromList [0] []
      domainsInit = mkDoms (dfromR $ Flip emptyR) (fromListDoms params1Init)
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      -- TODO: generate this from afcnnMnistLen1.
      -- valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length nParams1), show (sum nParams1)
                        , show gamma ]
      ftest :: [MnistData r] -> Domains r -> r
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
       let shapes1 = map (: []) nParams1
           (vars1, asts1) = unzip $ map funToAstD shapes1
           doms = mkDoms (dfromR $ AstConst emptyR) (fromListDoms asts1)
           (varGlyph, astGlyph) =
             funToAstR (singletonShape sizeMnistGlyphInt) id
           (varLabel, astLabel) =
             funToAstR (singletonShape sizeMnistLabelInt) id
           ast :: Ast 0 r
           ast = tscalar
                 $ MnistFcnnRanked1.afcnnMnistLoss1TensorData
                     widthHidden widthHidden2 (astGlyph, astLabel)
                     (parseDomains valsInit doms)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains r -> (Int, [MnistData r]) -> IO (Domains r)
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADVal r) -> ADVal r
                 f (glyph, label) varInputs =
                   let env1 = foldr extendEnvD EM.empty
                              $ zip vars1 $ V.toList
                              $ V.zipWith (dDnotShared emptyADShare)
                                          (inputPrimal1 varInputs)
                                          (inputDual1 varInputs)
                       envMnist =
                         extendEnvR varGlyph
                           (tconst $ OR.fromVector [sizeMnistGlyphInt] glyph)
                         $ extendEnvR varLabel
                             (tconst $ OR.fromVector [sizeMnistLabelInt] label)
                             env1
                   in tunScalar $ snd $ interpretAst envMnist emptyMemo ast
                 res = fst $ sgd gamma f chunk domains
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> Domains r -> IO (Domains r)
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

tensorIntermediateMnistTests :: TestTree
tensorIntermediateMnistTests = testGroup "Ranked Intermediate MNIST tests"
  [ mnistTestCase2VTI "VTI 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase2VTI "VTI artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase2VTI "VTI artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.5859 :: Double)
  , mnistTestCase2VTI "VTI 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCase2VTO
  :: forall r.
     ( ADTensor r, ADReady r, Value r ~ r, InterpretAst r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
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
      emptyR = OR.fromList [0] []
      domainsInit = mkDoms (dfromR $ Flip emptyR) (fromListDoms params1Init)
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      -- TODO: generate this from afcnnMnistLen1.
      -- valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length nParams1), show (sum nParams1)
                        , show gamma ]
      ftest :: [MnistData r] -> Domains r -> r
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
       let shapes1 = map (: []) nParams1
           (varGlyph, astGlyph) =
             funToAstR (singletonShape sizeMnistGlyphInt) id
           (varLabel, astLabel) =
             funToAstR (singletonShape sizeMnistLabelInt) id
           envInit = extendEnvR varGlyph (tconstant astGlyph)
                     $ extendEnvR varLabel (tconstant astLabel) EM.empty
           f = tscalar . MnistFcnnRanked1.afcnnMnistLoss1TensorData
                           widthHidden widthHidden2 (astGlyph, astLabel)
           (((var0Again, varDtAgain, vars1Again), gradientRaw, primal), _) =
             revAstOnDomainsFun 0 shapes1 $ revDtInterpret envInit valsInit f
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain =
             vars1Again
             ++ [AstDynamicVarName varGlyph, AstDynamicVarName varLabel]
           vars = (var0Again, varDtAgain, vars1AndInputAgain)
           go :: [MnistData r] -> Domains r -> Domains r
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = OD.fromVector [sizeMnistGlyphInt] glyph
                 labelD = OD.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   concatDomsR [parameters, fromListDoms [glyphD, labelD]]
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradientR gamma parameters gradientDomain)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains r -> (Int, [MnistData r]) -> IO (Domains r)
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
       let runEpoch :: Int -> Domains r -> IO (Domains r)
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

tensorADOnceMnistTests :: TestTree
tensorADOnceMnistTests = testGroup "Ranked Once MNIST tests"
  [ mnistTestCase2VTO "VTO 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase2VTO "VTO artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase2VTO "VTO artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.8304 :: Double)
  , mnistTestCase2VTO "VTO 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]


-- * Using matrices, which is rank 2

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCase2VT2A
  :: forall r.
     ( ADTensor r, ADReady r, ADReady (ADVal r)
     , Value r ~ r, Value (ADVal r) ~ r, Floating (Vector r)
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VT2A prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let nParams1 = MnistFcnnRanked2.afcnnMnistLen2 widthHidden widthHidden2
      params1Init =
        imap (\i sh -> OD.fromVector sh
                       $ V.map realToFrac
                       $ LA.randomVector (44 + product sh + i) LA.Uniform
                                         (product sh)
                         - LA.scalar 0.5)
             nParams1
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      emptyR = OR.fromList [0] []
      emptyR2 = OR.fromList [0, 0] []
      valsInit :: ( ( OR.Array 2 r
                    , OR.Array 1 r )
                  , ( OR.Array 2 r
                    , OR.Array 1 r )
                  , ( OR.Array 2 r
                    , OR.Array 1 r )
                  )
      valsInit = ( (emptyR2, emptyR)
                 , (emptyR2, emptyR)
                 , (emptyR2, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length nParams1)
                        , show (sum $ map product nParams1)
                        , show gamma ]
      ftest :: [MnistData r] -> Domains r -> r
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
       let runBatch :: Domains r -> (Int, [MnistData r]) -> IO (Domains r)
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADVal r) -> ADVal r
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
       let runEpoch :: Int -> Domains r -> IO (Domains r)
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (mkDoms (dfromR $ Flip emptyR)
                                 (fromListDoms params1Init))
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

tensorADValMnistTests2 :: TestTree
tensorADValMnistTests2 = testGroup "Ranked2 ADVal MNIST tests"
  [ mnistTestCase2VT2A "VT2A 1 epoch, 1 batch" 1 1 300 100 0.02 5
                       (0.8 :: Double)
  , mnistTestCase2VT2A "VT2A artificial 1 2 3 4 5" 1 2 3 4 5 5
                       (0.8 :: Float)
  , mnistTestCase2VT2A "VT2A artificial 5 4 3 2 1" 5 4 3 2 1 5
                       (0.95 :: Double)
  , mnistTestCase2VT2A "VT2A 1 epoch, 0 batch" 1 0 300 100 0.02 5
                       (1 :: Float)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCase2VT2I
  :: forall r.
     ( ADTensor r, ADReady r, InterpretAst (ADVal r)
     , Value r ~ r, Value (ADVal r) ~ r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VT2I prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let nParams1 = MnistFcnnRanked2.afcnnMnistLen2 widthHidden widthHidden2
      params1Init =
        imap (\i sh -> OD.fromVector sh
                       $ V.map realToFrac
                       $ LA.randomVector (44 + product sh + i) LA.Uniform
                                         (product sh)
                         - LA.scalar 0.5)
             nParams1
      emptyR = OR.fromList [0] []
      emptyR2 = OR.fromList [0, 0] []
      domainsInit = mkDoms (dfromR $ Flip emptyR) (fromListDoms params1Init)
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      -- TODO: generate this from afcnnMnistLen1.
      -- valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters r
      valsInit = ( (emptyR2, emptyR)
                 , (emptyR2, emptyR)
                 , (emptyR2, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length nParams1)
                        , show (sum $ map product nParams1)
                        , show gamma ]
      ftest :: [MnistData r] -> Domains r -> r
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
       let shapes1 = nParams1
           (vars1, asts1) = unzip $ map funToAstD shapes1
           doms = mkDoms (dfromR $ AstConst emptyR) (fromListDoms asts1)
           (varGlyph, astGlyph) =
             funToAstR (singletonShape sizeMnistGlyphInt) id
           (varLabel, astLabel) =
             funToAstR (singletonShape sizeMnistLabelInt) id
           ast :: Ast 0 r
           ast = tscalar
                 $ MnistFcnnRanked2.afcnnMnistLoss2TensorData
                     (astGlyph, astLabel) (parseDomains valsInit doms)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains r -> (Int, [MnistData r]) -> IO (Domains r)
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> Domains (ADVal r) -> ADVal r
                 f (glyph, label) varInputs =
                   let env1 = foldr extendEnvD EM.empty
                              $ zip vars1 $ V.toList
                              $ V.zipWith (dDnotShared emptyADShare)
                                          (inputPrimal1 varInputs)
                                          (inputDual1 varInputs)
                       envMnist =
                         extendEnvR varGlyph
                           (tconst $ OR.fromVector [sizeMnistGlyphInt] glyph)
                         $ extendEnvR varLabel
                             (tconst $ OR.fromVector [sizeMnistLabelInt] label)
                             env1
                   in tunScalar $ snd $ interpretAst envMnist emptyMemo ast
                 res = fst $ sgd gamma f chunk domains
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> Domains r -> IO (Domains r)
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

tensorIntermediateMnistTests2 :: TestTree
tensorIntermediateMnistTests2 = testGroup "Ranked2 Intermediate MNIST tests"
  [ mnistTestCase2VT2I "VT2I 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.42200000000000004 :: Double)
  , mnistTestCase2VT2I "VT2I artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VT2I "VT2I artificial 5 4 3 2 1" 5 4 3 2 1 500
                       (0.7324999999999999 :: Double)
  , mnistTestCase2VT2I "VT2I 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCase2VT2O
  :: forall r.
     ( ADTensor r, ADReady r, Value r ~ r, InterpretAst r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VT2O prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let nParams1 = MnistFcnnRanked2.afcnnMnistLen2 widthHidden widthHidden2
      params1Init =
        imap (\i sh -> OD.fromVector sh
                       $ V.map realToFrac
                       $ LA.randomVector (44 + product sh + i) LA.Uniform
                                         (product sh)
                         - LA.scalar 0.5)
             nParams1
      emptyR = OR.fromList [0] []
      emptyR2 = OR.fromList [0, 0] []
      domainsInit = mkDoms (dfromR $ Flip emptyR) (fromListDoms params1Init)
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      -- TODO: generate this from afcnnMnistLen1.
      -- valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters r
      valsInit = ( (emptyR2, emptyR)
                 , (emptyR2, emptyR)
                 , (emptyR2, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length nParams1)
                        , show (sum $ map product nParams1)
                        , show gamma ]
      ftest :: [MnistData r] -> Domains r -> r
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
       let shapes1 = nParams1
           (varGlyph, astGlyph) =
             funToAstR (singletonShape sizeMnistGlyphInt) id
           (varLabel, astLabel) =
             funToAstR (singletonShape sizeMnistLabelInt) id
           envInit = extendEnvR varGlyph (tconstant astGlyph)
                     $ extendEnvR varLabel (tconstant astLabel) EM.empty
           f = tscalar . MnistFcnnRanked2.afcnnMnistLoss2TensorData
                           (astGlyph, astLabel)
           (((var0Again, varDtAgain, vars1Again), gradientRaw, primal), _) =
             revAstOnDomainsFun 0 shapes1 $ revDtInterpret envInit valsInit f
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain =
             vars1Again
             ++ [AstDynamicVarName varGlyph, AstDynamicVarName varLabel]
           vars = (var0Again, varDtAgain, vars1AndInputAgain)
           go :: [MnistData r] -> Domains r -> Domains r
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = OD.fromVector [sizeMnistGlyphInt] glyph
                 labelD = OD.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   concatDomsR [parameters, fromListDoms [glyphD, labelD]]
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradientR gamma parameters gradientDomain)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains r -> (Int, [MnistData r]) -> IO (Domains r)
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
       let runEpoch :: Int -> Domains r -> IO (Domains r)
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

tensorADOnceMnistTests2 :: TestTree
tensorADOnceMnistTests2 = testGroup "Ranked2 Once MNIST tests"
  [ mnistTestCase2VT2O "VT2O 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.42200000000000004 :: Double)
  , mnistTestCase2VT2O "VT2O artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VT2O "VT2O artificial 5 4 3 2 1" 5 4 3 2 1 500
                       (0.7324999999999999 :: Double)
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

valsInitVTOPP ::  -- MnistFcnnRanked1.ADFcnnMnist1Parameters Double
  ( ( [OR.Array 1 Double]
    , OR.Array 1 Double )
  , ( [OR.Array 1 Double]
    , OR.Array 1 Double )
  , ( [OR.Array 1 Double]
    , OR.Array 1 Double )
  )
valsInitVTOPP =
  ( ( replicate 3 (OR.fromList [3] [1, 2, 3])
    , OR.fromList [3] [1, 2, 3] )
  , ( replicate 4 (OR.fromList [4] [1, 2, 3, 4])
    , OR.fromList [4] [1, 2, 3, 4] )
  , ( replicate 5 (OR.fromList [5] [1, 2, 3, 4, 5])
    , OR.fromList [5] [1, 2, 3, 4, 5] ) )

testVTOPP :: Assertion
testVTOPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstKonst sizeMnistGlyphInt 7
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters (Ast0 Double)
              -> TensorOf 1 (Ast0 Double)
      afcnn2T = MnistFcnnRanked1.afcnnMnist1 id id 3 4 blackGlyph
      (artifact6, _) = revDtFun afcnn2T valsInitVTOPP
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 -> let v21 = tkonst 784 (tconst 7.0) ; v22 = tfromList [tsum (v3 * v21), tsum (v4 * v21), tsum (v5 * v21)] + v6 ; v23 = tfromList [tsum (v7 * v22), tsum (v8 * v22), tsum (v9 * v22), tsum (v10 * v22)] + v11 ; x24 = dret ! [4] ; x25 = dret ! [3] ; x26 = dret ! [2] ; x27 = dret ! [1] ; x28 = dret ! [0] ; v29 = v12 * tkonst 5 x28 + v13 * tkonst 5 x27 + v14 * tkonst 5 x26 + v15 * tkonst 5 x25 + v16 * tkonst 5 x24 ; x30 = v29 ! [3] ; x31 = v29 ! [2] ; x32 = v29 ! [1] ; x33 = v29 ! [0] ; v34 = v7 * tkonst 4 x33 + v8 * tkonst 4 x32 + v9 * tkonst 4 x31 + v10 * tkonst 4 x30 ; x35 = v34 ! [2] ; x36 = v34 ! [1] ; x37 = v34 ! [0] in (tfromList [], v21 * tkonst 784 x37, v21 * tkonst 784 x36, v21 * tkonst 784 x35, v34, v22 * tkonst 3 x33, v22 * tkonst 3 x32, v22 * tkonst 3 x31, v22 * tkonst 3 x30, v29, v23 * tkonst 4 x28, v23 * tkonst 4 x27, v23 * tkonst 4 x26, v23 * tkonst 4 x25, v23 * tkonst 4 x24, dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 -> let v21 = tkonst 784 (tconst 7.0) ; v22 = tfromList [tsum (v3 * v21), tsum (v4 * v21), tsum (v5 * v21)] + v6 ; v23 = tfromList [tsum (v7 * v22), tsum (v8 * v22), tsum (v9 * v22), tsum (v10 * v22)] + v11 in tfromList [tsum (v12 * v23), tsum (v13 * v23), tsum (v14 * v23), tsum (v15 * v23), tsum (v16 * v23)] + v17"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 -> let v21 = tconstant (tkonst 784 (tconst 7.0)) ; v22 = tfromList [tsum (v3 * v21), tsum (v4 * v21), tsum (v5 * v21)] + v6 ; v23 = tfromList [tsum (v7 * v22), tsum (v8 * v22), tsum (v9 * v22), tsum (v10 * v22)] + v11 ; x24 = dret ! [4] ; x25 = dret ! [3] ; x26 = dret ! [2] ; x27 = dret ! [1] ; x28 = dret ! [0] ; v29 = v12 * tkonst 5 x28 + v13 * tkonst 5 x27 + v14 * tkonst 5 x26 + v15 * tkonst 5 x25 + v16 * tkonst 5 x24 ; x30 = v29 ! [3] ; x31 = v29 ! [2] ; x32 = v29 ! [1] ; x33 = v29 ! [0] ; v34 = v7 * tkonst 4 x33 + v8 * tkonst 4 x32 + v9 * tkonst 4 x31 + v10 * tkonst 4 x30 in (tfromList [], v21 * tkonst 784 (v34 ! [0]), v21 * tkonst 784 (v34 ! [1]), v21 * tkonst 784 (v34 ! [2]), v34, v22 * tkonst 3 x33, v22 * tkonst 3 x32, v22 * tkonst 3 x31, v22 * tkonst 3 x30, v29, v23 * tkonst 4 x28, v23 * tkonst 4 x27, v23 * tkonst 4 x26, v23 * tkonst 4 x25, v23 * tkonst 4 x24, dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 -> let v21 = tconstant (tkonst 784 (tconst 7.0)) ; v22 = tfromList [tsum (v3 * v21), tsum (v4 * v21), tsum (v5 * v21)] + v6 ; v23 = tfromList [tsum (v7 * v22), tsum (v8 * v22), tsum (v9 * v22), tsum (v10 * v22)] + v11 in tfromList [tsum (v12 * v23), tsum (v13 * v23), tsum (v14 * v23), tsum (v15 * v23), tsum (v16 * v23)] + v17"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstKonst sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters (Ast0 Double)
                    -> TensorOf 1 (Ast0 Double)
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMax1 3 4 blackGlyph
      (artifact6nonLin, _) = revDtFun afcnn2TnonLin valsInitVTOPP
  printGradient6Pretty renames artifact6nonLin
    @?= "\\s0 dret v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 -> let v26 = tkonst 784 (tconst 7.0) ; v27 = tfromList [tsum (v3 * v26), tsum (v4 * v26), tsum (v5 * v26)] + v6 ; v30 = let v28 = exp (negate v27) ; v29 = tkonst 3 (tconst 1.0) + v28 in recip v29 ; v31 = tkonst 3 (tconst 1.0) - v30 ; v32 = v30 * v31 ; v33 = v30 ; v34 = tfromList [tsum (v7 * v33), tsum (v8 * v33), tsum (v9 * v33), tsum (v10 * v33)] + v11 ; v37 = let v35 = exp (negate v34) ; v36 = tkonst 4 (tconst 1.0) + v35 in recip v36 ; v38 = tkonst 4 (tconst 1.0) - v37 ; v39 = v37 * v38 ; v40 = v37 ; v41 = exp (tfromList [tsum (v12 * v40), tsum (v13 * v40), tsum (v14 * v40), tsum (v15 * v40), tsum (v16 * v40)] + v17) ; x42 = tsum v41 ; v43 = tkonst 5 (recip x42) ; v44 = v41 * (tkonst 5 (negate (recip (x42 * x42)) * tsum (v41 * dret)) + v43 * dret) ; x45 = v44 ! [4] ; x46 = v44 ! [3] ; x47 = v44 ! [2] ; x48 = v44 ! [1] ; x49 = v44 ! [0] ; v50 = v12 * tkonst 5 x49 + v13 * tkonst 5 x48 + v14 * tkonst 5 x47 + v15 * tkonst 5 x46 + v16 * tkonst 5 x45 ; v51 = v37 * (v34 * v50) ; v52 = v39 * v50 ; x53 = v52 ! [3] ; x54 = v52 ! [2] ; x55 = v52 ! [1] ; x56 = v52 ! [0] ; v57 = v7 * tkonst 4 x56 + v8 * tkonst 4 x55 + v9 * tkonst 4 x54 + v10 * tkonst 4 x53 ; v58 = v30 * (v27 * v57) ; v59 = v32 * v57 ; x60 = v59 ! [2] ; x61 = v59 ! [1] ; x62 = v59 ! [0] in (tfromList [], v26 * tkonst 784 x62, v26 * tkonst 784 x61, v26 * tkonst 784 x60, v59, v33 * tkonst 3 x56, v33 * tkonst 3 x55, v33 * tkonst 3 x54, v33 * tkonst 3 x53, v52, v40 * tkonst 4 x49, v40 * tkonst 4 x48, v40 * tkonst 4 x47, v40 * tkonst 4 x46, v40 * tkonst 4 x45, v44)"
  printPrimal6Pretty renames artifact6nonLin
    @?= "\\s0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 -> let v26 = tkonst 784 (tconst 7.0) ; v27 = tfromList [tsum (v3 * v26), tsum (v4 * v26), tsum (v5 * v26)] + v6 ; v30 = let v28 = exp (negate v27) ; v29 = tkonst 3 (tconst 1.0) + v28 in recip v29 ; v31 = tkonst 3 (tconst 1.0) - v30 ; v32 = v30 * v31 ; v33 = v30 ; v34 = tfromList [tsum (v7 * v33), tsum (v8 * v33), tsum (v9 * v33), tsum (v10 * v33)] + v11 ; v37 = let v35 = exp (negate v34) ; v36 = tkonst 4 (tconst 1.0) + v35 in recip v36 ; v38 = tkonst 4 (tconst 1.0) - v37 ; v39 = v37 * v38 ; v40 = v37 ; v41 = exp (tfromList [tsum (v12 * v40), tsum (v13 * v40), tsum (v14 * v40), tsum (v15 * v40), tsum (v16 * v40)] + v17) ; v42 = tsum v41 ; v43 = tkonst 5 (recip x42) in v43 * v41"
  printGradient6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\s0 dret v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 -> let v26 = tconstant (tkonst 784 (tconst 7.0)) ; v30 = recip (tconstant (tkonst 3 (tconst 1.0)) + exp (negate (tfromList [tsum (v3 * v26), tsum (v4 * v26), tsum (v5 * v26)] + v6))) ; v37 = recip (tconstant (tkonst 4 (tconst 1.0)) + exp (negate (tfromList [tsum (v7 * v30), tsum (v8 * v30), tsum (v9 * v30), tsum (v10 * v30)] + v11))) ; v41 = exp (tfromList [tsum (v12 * v37), tsum (v13 * v37), tsum (v14 * v37), tsum (v15 * v37), tsum (v16 * v37)] + v17) ; x42 = tsum v41 ; v44 = v41 * (tkonst 5 (negate (recip (x42 * x42)) * tsum (v41 * dret)) + tkonst 5 (recip x42) * dret) ; x45 = v44 ! [4] ; x46 = v44 ! [3] ; x47 = v44 ! [2] ; x48 = v44 ! [1] ; x49 = v44 ! [0] ; v52 = (v37 * (tconstant (tkonst 4 (tconst 1.0)) - v37)) * (v12 * tkonst 5 x49 + v13 * tkonst 5 x48 + v14 * tkonst 5 x47 + v15 * tkonst 5 x46 + v16 * tkonst 5 x45) ; x53 = v52 ! [3] ; x54 = v52 ! [2] ; x55 = v52 ! [1] ; x56 = v52 ! [0] ; v59 = (v30 * (tconstant (tkonst 3 (tconst 1.0)) - v30)) * (v7 * tkonst 4 x56 + v8 * tkonst 4 x55 + v9 * tkonst 4 x54 + v10 * tkonst 4 x53) in (tfromList [], v26 * tkonst 784 (v59 ! [0]), v26 * tkonst 784 (v59 ! [1]), v26 * tkonst 784 (v59 ! [2]), v59, v30 * tkonst 3 x56, v30 * tkonst 3 x55, v30 * tkonst 3 x54, v30 * tkonst 3 x53, v52, v37 * tkonst 4 x49, v37 * tkonst 4 x48, v37 * tkonst 4 x47, v37 * tkonst 4 x46, v37 * tkonst 4 x45, v44)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\s0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 -> let v26 = tconstant (tkonst 784 (tconst 7.0)) ; v30 = recip (tconstant (tkonst 3 (tconst 1.0)) + exp (negate (tfromList [tsum (v3 * v26), tsum (v4 * v26), tsum (v5 * v26)] + v6))) ; v37 = recip (tconstant (tkonst 4 (tconst 1.0)) + exp (negate (tfromList [tsum (v7 * v30), tsum (v8 * v30), tsum (v9 * v30), tsum (v10 * v30)] + v11))) ; v41 = exp (tfromList [tsum (v12 * v37), tsum (v13 * v37), tsum (v14 * v37), tsum (v15 * v37), tsum (v16 * v37)] + v17) in tkonst 5 (recip (tsum v41)) * v41"

valsInitVT2OPP ::  -- MnistFcnnRanked2.ADFcnnMnist2Parameters Double
  ( ( OR.Array 2 Double
    , OR.Array 1 Double )
  , ( OR.Array 2 Double
    , OR.Array 1 Double )
  , ( OR.Array 2 Double
    , OR.Array 1 Double )
  )
valsInitVT2OPP =
  ( ( OR.fromList [3, 3] (concat $ replicate 3 [1, 2, 3])
    , OR.fromList [3] [1, 2, 3] )
  , ( OR.fromList [4, 4] (concat $ replicate 4 [1, 2, 3, 4])
    , OR.fromList [4] [1, 2, 3, 4] )
  , ( OR.fromList [5, 5] (concat $ replicate 5 [1, 2, 3, 4, 5])
    , OR.fromList [5] [1, 2, 3, 4, 5] ) )

testVT2OPP :: Assertion
testVT2OPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstKonst sizeMnistGlyphInt 7
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters (Ast0 Double)
              -> TensorOf 1 (Ast0 Double)
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id blackGlyph
      (artifact6, _) = revDtFun afcnn2T valsInitVT2OPP
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret m3 v4 m5 v6 m7 v8 -> let m12 = tkonst 3 (tkonst 784 (tconst 7.0)) ; m13 = tkonst 4 (tsum (ttranspose [1,0] (m12 * m3)) + v4) ; m14 = tkonst 5 (tsum (ttranspose [1,0] (m13 * m5)) + v6) ; m15 = ttranspose [1,0] (tkonst 4 dret) ; v16 = tsum (m7 * m15) ; m17 = ttranspose [1,0] (tkonst 3 v16) ; v18 = tsum (m5 * m17) ; m19 = ttranspose [1,0] (tkonst 784 v18) in (tfromList [], m12 * m19, v18, m13 * m17, v16, m14 * m15, dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 m3 v4 m5 v6 m7 v8 -> let v12 = tkonst 3 (tkonst 784 (tconst 7.0)) ; v13 = tkonst 4 (tsum (ttranspose [1,0] (m12 * m3)) + v4) ; v14 = tkonst 5 (tsum (ttranspose [1,0] (m13 * m5)) + v6) in tsum (ttranspose [1,0] (m14 * m7)) + v8"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret m3 v4 m5 v6 m7 v8 -> let m12 = tconstant (tkonst 3 (tkonst 784 (tconst 7.0))) ; m13 = tkonst 4 (tsum (ttranspose [1,0] (m12 * m3)) + v4) ; m15 = ttranspose [1,0] (tkonst 4 dret) ; v16 = tsum (m7 * m15) ; m17 = ttranspose [1,0] (tkonst 3 v16) ; v18 = tsum (m5 * m17) in (tfromList [], m12 * ttranspose [1,0] (tkonst 784 v18), v18, m13 * m17, v16, tkonst 5 (tsum (ttranspose [1,0] (m13 * m5)) + v6) * m15, dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 m3 v4 m5 v6 m7 v8 -> tsum (ttranspose [1,0] (tkonst 5 (tsum (ttranspose [1,0] (tkonst 4 (tsum (ttranspose [1,0] (tconstant (tkonst 3 (tkonst 784 (tconst 7.0))) * m3)) + v4) * m5)) + v6) * m7)) + v8"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstKonst sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters (Ast0 Double)
                    -> TensorOf 1 (Ast0 Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      (artifact6nonLin, _) = revDtFun afcnn2TnonLin valsInitVT2OPP
  printGradient6Pretty renames artifact6nonLin
    @?= "\\s0 dret m3 v4 m5 v6 m7 v8 -> let m17 = tkonst 3 (tkonst 784 (tconst 7.0)) ; v18 = tsum (ttranspose [1,0] (m17 * m3)) + v4 ; v21 = let v19 = exp (negate v18) ; v20 = tkonst 3 (tconst 1.0) + v19 in recip v20 ; v22 = tkonst 3 (tconst 1.0) - v21 ; v23 = v21 * v22 ; m24 = tkonst 4 v21 ; v25 = tsum (ttranspose [1,0] (m24 * m5)) + v6 ; v28 = let v26 = exp (negate v25) ; v27 = tkonst 4 (tconst 1.0) + v26 in recip v27 ; v29 = tkonst 4 (tconst 1.0) - v28 ; v30 = v28 * v29 ; m31 = tkonst 5 v28 ; v32 = exp (tsum (ttranspose [1,0] (m31 * m7)) + v8) ; x33 = tsum v32 ; v34 = tkonst 5 (recip x33) ; v35 = v32 * (tkonst 5 (negate (recip (x33 * x33)) * tsum (v32 * dret)) + v34 * dret) ; m36 = ttranspose [1,0] (tkonst 4 v35) ; v37 = tsum (m7 * m36) ; v38 = v28 * (v25 * v37) ; v39 = v30 * v37 ; m40 = ttranspose [1,0] (tkonst 3 v39) ; v41 = tsum (m5 * m40) ; v42 = v21 * (v18 * v41) ; v43 = v23 * v41 ; m44 = ttranspose [1,0] (tkonst 784 v43) in (tfromList [], m17 * m44, v43, m24 * m40, v39, m31 * m36, v35)"
  printPrimal6Pretty renames artifact6nonLin
    @?= "\\s0 m3 v4 m5 v6 m7 v8 -> let v17 = tkonst 3 (tkonst 784 (tconst 7.0)) ; v18 = tsum (ttranspose [1,0] (m17 * m3)) + v4 ; v21 = let v19 = exp (negate v18) ; v20 = tkonst 3 (tconst 1.0) + v19 in recip v20 ; v22 = tkonst 3 (tconst 1.0) - v21 ; v23 = v21 * v22 ; v24 = tkonst 4 v21 ; v25 = tsum (ttranspose [1,0] (m24 * m5)) + v6 ; v28 = let v26 = exp (negate v25) ; v27 = tkonst 4 (tconst 1.0) + v26 in recip v27 ; v29 = tkonst 4 (tconst 1.0) - v28 ; v30 = v28 * v29 ; v31 = tkonst 5 v28 ; v32 = exp (tsum (ttranspose [1,0] (m31 * m7)) + v8) ; v33 = tsum v32 ; v34 = tkonst 5 (recip x33) in v34 * v32"
  printGradient6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\s0 dret m3 v4 m5 v6 m7 v8 -> let m17 = tconstant (tkonst 3 (tkonst 784 (tconst 7.0))) ; v21 = recip (tconstant (tkonst 3 (tconst 1.0)) + exp (negate (tsum (ttranspose [1,0] (m17 * m3)) + v4))) ; m24 = tkonst 4 v21 ; v28 = recip (tconstant (tkonst 4 (tconst 1.0)) + exp (negate (tsum (ttranspose [1,0] (m24 * m5)) + v6))) ; m31 = tkonst 5 v28 ; v32 = exp (tsum (ttranspose [1,0] (m31 * m7)) + v8) ; x33 = tsum v32 ; v35 = v32 * (tkonst 5 (negate (recip (x33 * x33)) * tsum (v32 * dret)) + tkonst 5 (recip x33) * dret) ; m36 = ttranspose [1,0] (tkonst 4 v35) ; v39 = (v28 * (tconstant (tkonst 4 (tconst 1.0)) - v28)) * tsum (m7 * m36) ; m40 = ttranspose [1,0] (tkonst 3 v39) ; v43 = (v21 * (tconstant (tkonst 3 (tconst 1.0)) - v21)) * tsum (m5 * m40) in (tfromList [], m17 * ttranspose [1,0] (tkonst 784 v43), v43, m24 * m40, v39, m31 * m36, v35)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\s0 m3 v4 m5 v6 m7 v8 -> let v32 = exp (tsum (ttranspose [1,0] (tkonst 5 (recip (tconstant (tkonst 4 (tconst 1.0)) + exp (negate (tsum (ttranspose [1,0] (tkonst 4 (recip (tconstant (tkonst 3 (tconst 1.0)) + exp (negate (tsum (ttranspose [1,0] (tconstant (tkonst 3 (tkonst 784 (tconst 7.0))) * m3)) + v4)))) * m5)) + v6)))) * m7)) + v8) in tkonst 5 (recip (tsum v32)) * v32"
