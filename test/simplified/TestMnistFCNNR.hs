module TestMnistFCNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.EnumMap.Strict as EM
import           Data.List.Index (imap)
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as LA
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd.Core.Ast
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor
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
            ]


-- * Using vectors, which is rank 1

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCase2VTA
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r)
     , TensorOf 1 (ADVal r) ~ ADVal (OR.Array 1 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , Primal (ADVal r) ~ r, ScalarOf (ADVal r) ~ r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VTA prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init = V.fromList $
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
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters r
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
          (\f -> OR.toVector $ f $ parseDomains valsInit testParams)
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
                     mnist (parseADInputs valsInit adinputs)
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
           runEpoch n params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             !res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (mkDomains emptyR params1Init)
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

tensorADValMnistTests :: TestTree
tensorADValMnistTests = testGroup "ShortRanked ADVal MNIST tests"
  [ mnistTestCase2VTA "VTA 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16600000000000004 :: Double)
  , mnistTestCase2VTA "VTA artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.8972 :: Float)
  , mnistTestCase2VTA "VTA artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.6585 :: Double)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCase2VTI
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADReady (Ast0 r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , ScalarOf (ADVal r) ~ r
     , InterpretAst (ADVal r) )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VTI prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init = V.fromList $
        imap (\i nPV -> OD.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = OR.fromList [0] []
      domainsInit = mkDomains emptyR params1Init
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      -- TODO: generate this from afcnnMnistLen1.
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters r
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
          (\f -> OR.toVector $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let shapes1 = map (: []) nParams1
           (vars1, asts1) = unzip $ map funToAstD shapes1
           doms = mkDomains (AstConst emptyR) (V.fromList asts1)
           (varGlyph, astGlyph) =
             funToAstR (singletonShape sizeMnistGlyphInt) id
           (varLabel, astLabel) =
             funToAstR (singletonShape sizeMnistLabelInt) id
           ast :: Ast 0 r
           ast = tscalar
                 $ MnistFcnnRanked1.afcnnMnistLoss1TensorData
                     widthHidden widthHidden2 (astGlyph, astLabel)
                     (parseDomainsAst valsInit doms)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains r -> (Int, [MnistData r]) -> IO (Domains r)
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> ADInputs r -> ADVal r
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
           runEpoch n params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
                              -- 5000 times less data per batch
             !res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

tensorIntermediateMnistTests :: TestTree
tensorIntermediateMnistTests = testGroup "ShortRankedIntermediate MNIST tests"
  [ mnistTestCase2VTI "VTI 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase2VTI "VTI artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase2VTI "VTI artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.5859 :: Double)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCase2VTO
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADReady (Ast0 r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r), InterpretAst r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VTO prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init = V.fromList $
        imap (\i nPV -> OD.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = OR.fromList [0] []
      domainsInit = mkDomains emptyR params1Init
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      -- TODO: generate this from afcnnMnistLen1.
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters r
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
          (\f -> OR.toVector $ f $ parseDomains valsInit testParams)
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
           inputVars = [AstDynamicVarName varGlyph, AstDynamicVarName varLabel]
           fInterpret
             :: ADInputs (Ast0 r) -> Domains (Ast0 r)
             -> (ADAstVarNames n r, ADAstVars n r)
             -> ADVal (Ast 0 r)
           {-# INLINE fInterpret #-}
           fInterpret varInputs domains ((_, _, vars1), _) =
             -- TODO: with larger examples benchmark if not working in rank 0
             -- is costly (tscalar below)
             let ast :: Ast 0 r
                 ast = tscalar
                       $ MnistFcnnRanked1.afcnnMnistLoss1TensorData
                           widthHidden widthHidden2 (astGlyph, astLabel)
                           (parseDomainsAst valsInit domains)
                 vars1AndInput = vars1 ++ inputVars
                 env1 = foldr extendEnvD EM.empty
                        $ zip vars1AndInput
                        $ V.toList (V.zipWith (dDnotShared emptyADShare)
                                              (inputPrimal1 varInputs)
                                              (inputDual1 varInputs))
                          ++ [ dfromR $ tconstant astGlyph
                             , dfromR $ tconstant astLabel ]
             in snd $ interpretAst env1 emptyMemo ast
           (((var0Again, varDtAgain, vars1Again), gradient, primal), _) =
             revAstOnDomainsFun 0 shapes1 fInterpret
           vars1AndInputAgain = vars1Again ++ inputVars
           vars = (var0Again, varDtAgain, vars1AndInputAgain)
           go :: [MnistData r] -> Domains r -> Domains r
           go [] parameters = parameters
           go ((glyph, label) : rest) parameters =
             let glyphD = OD.fromVector [sizeMnistGlyphInt] glyph
                 labelD = OD.fromVector [sizeMnistLabelInt] label
                 parametersAndInput = parameters `V.snoc` glyphD `V.snoc` labelD
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradient gamma parameters gradientDomain)
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
           runEpoch n params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
                              -- 5000 times less data per batch
             !res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

tensorADOnceMnistTests :: TestTree
tensorADOnceMnistTests = testGroup "ShortRankedOnce MNIST tests"
  [ mnistTestCase2VTO "VTO 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase2VTO "VTO artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase2VTO "VTO artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.8304 :: Double)
  ]


-- * Using matrices, which is rank 2

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCase2VT2A
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r)
     , TensorOf 1 (ADVal r) ~ ADVal (OR.Array 1 r)
     , TensorOf 2 (ADVal r) ~ ADVal (OR.Array 2 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , Primal (ADVal r) ~ r, ScalarOf (ADVal r) ~ r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VT2A prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let nParams1 = MnistFcnnRanked2.afcnnMnistLen2 widthHidden widthHidden2
      params1Init = V.fromList $
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
      valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters r
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
          (\f -> OR.toVector $ f $ parseDomains valsInit testParams)
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
                   MnistFcnnRanked2.afcnnMnistLoss2
                     mnist (parseADInputs valsInit adinputs)
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
           runEpoch n params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             !res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (mkDomains emptyR params1Init)
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

tensorADValMnistTests2 :: TestTree
tensorADValMnistTests2 = testGroup "ShortRanked ADVal MNIST tests"
  [ mnistTestCase2VT2A "VT2A 1 epoch, 1 batch" 1 1 300 100 0.02 5
                       (0.8 :: Double)
  , mnistTestCase2VT2A "VT2A artificial 1 2 3 4 5" 1 2 3 4 5 5
                       (0.8 :: Float)
  , mnistTestCase2VT2A "VT2A artificial 5 4 3 2 1" 5 4 3 2 1 5
                       (0.95 :: Double)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCase2VT2I
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADReady (Ast0 r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , ScalarOf (ADVal r) ~ r
     , InterpretAst (ADVal r) )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VT2I prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let nParams1 = MnistFcnnRanked2.afcnnMnistLen2 widthHidden widthHidden2
      params1Init = V.fromList $
        imap (\i sh -> OD.fromVector sh
                       $ V.map realToFrac
                       $ LA.randomVector (44 + product sh + i) LA.Uniform
                                         (product sh)
                         - LA.scalar 0.5)
             nParams1
      emptyR = OR.fromList [0] []
      emptyR2 = OR.fromList [0, 0] []
      domainsInit = mkDomains emptyR params1Init
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      -- TODO: generate this from afcnnMnistLen1.
      valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters r
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
          (\f -> OR.toVector $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let shapes1 = nParams1
           (vars1, asts1) = unzip $ map funToAstD shapes1
           doms = mkDomains (AstConst emptyR) (V.fromList asts1)
           (varGlyph, astGlyph) =
             funToAstR (singletonShape sizeMnistGlyphInt) id
           (varLabel, astLabel) =
             funToAstR (singletonShape sizeMnistLabelInt) id
           ast :: Ast 0 r
           ast = tscalar
                 $ MnistFcnnRanked2.afcnnMnistLoss2TensorData
                     (astGlyph, astLabel) (parseDomainsAst valsInit doms)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains r -> (Int, [MnistData r]) -> IO (Domains r)
           runBatch !domains (k, chunk) = do
             let f :: MnistData r -> ADInputs r -> ADVal r
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
           runEpoch n params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
                              -- 5000 times less data per batch
             !res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

tensorIntermediateMnistTests2 :: TestTree
tensorIntermediateMnistTests2 = testGroup "ShortRankedIntermediate MNIST tests"
  [ mnistTestCase2VT2I "VT2I 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.42200000000000004 :: Double)
  , mnistTestCase2VT2I "VT2I artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VT2I "VT2I artificial 5 4 3 2 1" 5 4 3 2 1 500
                       (0.7324999999999999 :: Double)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCase2VT2O
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADReady (Ast0 r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r), InterpretAst r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VT2O prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let nParams1 = MnistFcnnRanked2.afcnnMnistLen2 widthHidden widthHidden2
      params1Init = V.fromList $
        imap (\i sh -> OD.fromVector sh
                       $ V.map realToFrac
                       $ LA.randomVector (44 + product sh + i) LA.Uniform
                                         (product sh)
                         - LA.scalar 0.5)
             nParams1
      emptyR = OR.fromList [0] []
      emptyR2 = OR.fromList [0, 0] []
      domainsInit = mkDomains emptyR params1Init
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      -- TODO: generate this from afcnnMnistLen1.
      valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters r
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
          (\f -> OR.toVector $ f $ parseDomains valsInit testParams)
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
           inputVars = [AstDynamicVarName varGlyph, AstDynamicVarName varLabel]
           fInterpret
             :: ADInputs (Ast0 r) -> Domains (Ast0 r)
             -> (ADAstVarNames n r, ADAstVars n r)
             -> ADVal (Ast 0 r)
           {-# INLINE fInterpret #-}
           fInterpret varInputs domains ((_, _, vars1), _) =
             -- TODO: with larger examples benchmark if not working in rank 0
             -- is costly (tscalar below)
             let ast :: Ast 0 r
                 ast = tscalar
                       $ MnistFcnnRanked2.afcnnMnistLoss2TensorData
                           (astGlyph, astLabel)
                           (parseDomainsAst valsInit domains)
                 vars1AndInput = vars1 ++ inputVars
                 env1 = foldr extendEnvD EM.empty
                        $ zip vars1AndInput
                        $ V.toList (V.zipWith (dDnotShared emptyADShare)
                                              (inputPrimal1 varInputs)
                                              (inputDual1 varInputs))
                          ++ [ dfromR $ tconstant astGlyph
                             , dfromR $ tconstant astLabel ]
             in snd $ interpretAst env1 emptyMemo ast
           (((var0Again, varDtAgain, vars1Again), gradient, primal), _) =
             revAstOnDomainsFun 0 shapes1 fInterpret
           vars1AndInputAgain = vars1Again ++ inputVars
           vars = (var0Again, varDtAgain, vars1AndInputAgain)
           go :: [MnistData r] -> Domains r -> Domains r
           go [] parameters = parameters
           go ((glyph, label) : rest) parameters =
             let glyphD = OD.fromVector [sizeMnistGlyphInt] glyph
                 labelD = OD.fromVector [sizeMnistLabelInt] label
                 parametersAndInput = parameters `V.snoc` glyphD `V.snoc` labelD
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradient gamma parameters gradientDomain)
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
           runEpoch n params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
                              -- 5000 times less data per batch
             !res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 domainsInit
       let testErrorFinal = 1 - ftest testData res
       testErrorFinal @?~ expected

tensorADOnceMnistTests2 :: TestTree
tensorADOnceMnistTests2 = testGroup "ShortRankedOnce MNIST tests"
  [ mnistTestCase2VT2O "VT2O 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.42200000000000004 :: Double)
  , mnistTestCase2VT2O "VT2O artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VT2O "VT2O artificial 5 4 3 2 1" 5 4 3 2 1 500
                       (0.7324999999999999 :: Double)
  ]
