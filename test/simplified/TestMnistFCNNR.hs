module TestMnistFCNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.EnumMap.Strict as EM
import           Data.List.Index (imap)
import           Data.MonoTraversable (Element)
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
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
import HordeAd.Core.DualNumber (ADVal, dDnotShared)
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal (ADTensor)
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor
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
     ( ADReady r, ADReady (ADVal r), ScalarOf r ~ r, ScalarOf (ADVal r) ~ r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r)
     , TensorOf 1 (ADVal r) ~ ADVal (OR.Array 1 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , PrintfArg r, AssertEqualUpToEpsilon r
     , Floating (Vector r), ADTensor r
     , DynamicTensor r, DomainsTensor r, Element r ~ r
     , DTensorOf r ~ OD.Array r, TensorOf 1 r ~ OR.Array 1 r
     , DomainsOf r ~ Data.Vector.Vector (OD.Array r) )
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
     ( ADReady r, ADReady (ADVal r), ScalarOf r ~ r, ScalarOf (ADVal r) ~ r
     , TensorOf 1 (ADVal r) ~ ADVal (OR.Array 1 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , InterpretAst (ADVal r)
     , PrintfArg r, AssertEqualUpToEpsilon r
     , Floating (Vector r), ADTensor r
     , DynamicTensor r, DomainsTensor r, Element r ~ r
     , DTensorOf r ~ OD.Array r, TensorOf 1 r ~ OR.Array 1 r
     , DomainsOf r ~ Data.Vector.Vector (OD.Array r) )
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
     ( ADReady r, ScalarOf r ~ r, InterpretAst r
     , PrintfArg r, AssertEqualUpToEpsilon r
     , Floating (Vector r), ADTensor r, DomainsTensor r
     , DTensorOf r ~ OD.Array r, TensorOf 1 r ~ OR.Array 1 r )
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
     ( ADReady r, ADReady (ADVal r), ScalarOf r ~ r, ScalarOf (ADVal r) ~ r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r)
     , TensorOf 1 (ADVal r) ~ ADVal (OR.Array 1 r)
     , TensorOf 2 (ADVal r) ~ ADVal (OR.Array 2 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , PrintfArg r, AssertEqualUpToEpsilon r
     , Floating (Vector r), ADTensor r
     , DynamicTensor r, DomainsTensor r, Element r ~ r
     , DTensorOf r ~ OD.Array r, DomainsOf r ~ Data.Vector.Vector (OD.Array r)
     , TensorOf 1 r ~ OR.Array 1 r, TensorOf 2 r ~ OR.Array 2 r )
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
tensorADValMnistTests2 = testGroup "ShortRanked2 ADVal MNIST tests"
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
     ( ADReady r, ADReady (ADVal r), ScalarOf r ~ r, ScalarOf (ADVal r) ~ r
     , TensorOf 1 (ADVal r) ~ ADVal (OR.Array 1 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , InterpretAst (ADVal r)
     , PrintfArg r, AssertEqualUpToEpsilon r
     , Floating (Vector r), ADTensor r
     , DynamicTensor r, DomainsTensor r, Element r ~ r
     , DTensorOf r ~ OD.Array r, DomainsOf r ~ Data.Vector.Vector (OD.Array r)
     , TensorOf 1 r ~ OR.Array 1 r, TensorOf 2 r ~ OR.Array 2 r )
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
tensorIntermediateMnistTests2 = testGroup "ShortRankedIntermediate2 MNIST tests"
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
     ( ADReady r, ScalarOf r ~ r, InterpretAst r
     , PrintfArg r, AssertEqualUpToEpsilon r
     , Floating (Vector r), ADTensor r, DomainsTensor r
     , DTensorOf r ~ OD.Array r
     , TensorOf 1 r ~ OR.Array 1 r, TensorOf 2 r ~ OR.Array 2 r )
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
tensorADOnceMnistTests2 = testGroup "ShortRankedOnce2 MNIST tests"
  [ mnistTestCase2VT2O "VT2O 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.42200000000000004 :: Double)
  , mnistTestCase2VT2O "VT2O artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VT2O "VT2O artificial 5 4 3 2 1" 5 4 3 2 1 500
                       (0.7324999999999999 :: Double)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for Short Ranked MNIST tests"
  [ testCase "VTOPP" testVTOPP
  , testCase "VTOPPNonLin" testVTOPPNonLin
  , testCase "VT2OPP" testVT2OPP
  , testCase "VT2OPPNonLin" testVT2OPPNonLin
  ]

valsInitVTOPP :: MnistFcnnRanked1.ADFcnnMnist1Parameters Double
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
    @?= "\\s0 dret x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> let x21 = tkonst 784 (tconst 7.0) ; x22 = tfromList [tsum (x3 * x21), tsum (x4 * x21), tsum (x5 * x21)] + x6 ; x23 = tfromList [tsum (x7 * x22), tsum (x8 * x22), tsum (x9 * x22), tsum (x10 * x22)] + x11 ; x24 = dret ! [4] ; x25 = dret ! [3] ; x26 = dret ! [2] ; x27 = dret ! [1] ; x28 = dret ! [0] ; x29 = x12 * tkonst 5 x28 + x13 * tkonst 5 x27 + x14 * tkonst 5 x26 + x15 * tkonst 5 x25 + x16 * tkonst 5 x24 ; x30 = x29 ! [3] ; x31 = x29 ! [2] ; x32 = x29 ! [1] ; x33 = x29 ! [0] ; x34 = x7 * tkonst 4 x33 + x8 * tkonst 4 x32 + x9 * tkonst 4 x31 + x10 * tkonst 4 x30 ; x35 = x34 ! [2] ; x36 = x34 ! [1] ; x37 = x34 ! [0] in (tfromList [], x21 * tkonst 784 x37, x21 * tkonst 784 x36, x21 * tkonst 784 x35, x34, x22 * tkonst 3 x33, x22 * tkonst 3 x32, x22 * tkonst 3 x31, x22 * tkonst 3 x30, x29, x23 * tkonst 4 x28, x23 * tkonst 4 x27, x23 * tkonst 4 x26, x23 * tkonst 4 x25, x23 * tkonst 4 x24, dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> let x21 = tkonst 784 (tconst 7.0) ; x22 = tfromList [tsum (x3 * x21), tsum (x4 * x21), tsum (x5 * x21)] + x6 ; x23 = tfromList [tsum (x7 * x22), tsum (x8 * x22), tsum (x9 * x22), tsum (x10 * x22)] + x11 in tfromList [tsum (x12 * x23), tsum (x13 * x23), tsum (x14 * x23), tsum (x15 * x23), tsum (x16 * x23)] + x17"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> let x21 = tconstant (tkonst 784 (tconst 7.0)) ; x22 = tfromList [tsum (x3 * x21), tsum (x4 * x21), tsum (x5 * x21)] + x6 ; x23 = tfromList [tsum (x7 * x22), tsum (x8 * x22), tsum (x9 * x22), tsum (x10 * x22)] + x11 ; x24 = dret ! [4] ; x25 = dret ! [3] ; x26 = dret ! [2] ; x27 = dret ! [1] ; x28 = dret ! [0] ; x29 = x12 * tkonst 5 x28 + x13 * tkonst 5 x27 + x14 * tkonst 5 x26 + x15 * tkonst 5 x25 + x16 * tkonst 5 x24 ; x30 = x29 ! [3] ; x31 = x29 ! [2] ; x32 = x29 ! [1] ; x33 = x29 ! [0] ; x34 = x7 * tkonst 4 x33 + x8 * tkonst 4 x32 + x9 * tkonst 4 x31 + x10 * tkonst 4 x30 in (tfromList [], x21 * tkonst 784 (x34 ! [0]), x21 * tkonst 784 (x34 ! [1]), x21 * tkonst 784 (x34 ! [2]), x34, x22 * tkonst 3 x33, x22 * tkonst 3 x32, x22 * tkonst 3 x31, x22 * tkonst 3 x30, x29, x23 * tkonst 4 x28, x23 * tkonst 4 x27, x23 * tkonst 4 x26, x23 * tkonst 4 x25, x23 * tkonst 4 x24, dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> let x21 = tconstant (tkonst 784 (tconst 7.0)) ; x22 = tfromList [tsum (x3 * x21), tsum (x4 * x21), tsum (x5 * x21)] + x6 ; x23 = tfromList [tsum (x7 * x22), tsum (x8 * x22), tsum (x9 * x22), tsum (x10 * x22)] + x11 in tfromList [tsum (x12 * x23), tsum (x13 * x23), tsum (x14 * x23), tsum (x15 * x23), tsum (x16 * x23)] + x17"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstKonst sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters (Ast0 Double)
                    -> TensorOf 1 (Ast0 Double)
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMaxV 3 4 blackGlyph
      (artifact6nonLin, _) = revDtFun afcnn2TnonLin valsInitVTOPP
  printGradient6Pretty renames artifact6nonLin
    @?= "\\s0 dret x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> let x26 = tkonst 784 (tconst 7.0) ; x27 = tfromList [tsum (x3 * x26), tsum (x4 * x26), tsum (x5 * x26)] + x6 ; x30 = let x28 = exp (negate x27) ; x29 = tkonst 3 (tconst 1.0) + x28 in recip x29 ; x31 = tkonst 3 (tconst 1.0) - x30 ; x32 = x30 * x31 ; x33 = tfromList [tsum (x7 * x30), tsum (x8 * x30), tsum (x9 * x30), tsum (x10 * x30)] + x11 ; x36 = let x34 = exp (negate x33) ; x35 = tkonst 4 (tconst 1.0) + x34 in recip x35 ; x37 = tkonst 4 (tconst 1.0) - x36 ; x38 = x36 * x37 ; x39 = exp (tfromList [tsum (x12 * x36), tsum (x13 * x36), tsum (x14 * x36), tsum (x15 * x36), tsum (x16 * x36)] + x17) ; x40 = tsum x39 ; x41 = tkonst 5 (recip x40) ; x42 = x39 * (tkonst 5 (negate (recip (x40 * x40)) * tsum (x39 * dret)) + x41 * dret) ; x43 = x42 ! [4] ; x44 = x42 ! [3] ; x45 = x42 ! [2] ; x46 = x42 ! [1] ; x47 = x42 ! [0] ; x48 = x12 * tkonst 5 x47 + x13 * tkonst 5 x46 + x14 * tkonst 5 x45 + x15 * tkonst 5 x44 + x16 * tkonst 5 x43 ; x49 = x36 * (x33 * x48) ; x50 = x38 * x48 ; x51 = x50 ! [3] ; x52 = x50 ! [2] ; x53 = x50 ! [1] ; x54 = x50 ! [0] ; x55 = x7 * tkonst 4 x54 + x8 * tkonst 4 x53 + x9 * tkonst 4 x52 + x10 * tkonst 4 x51 ; x56 = x30 * (x27 * x55) ; x57 = x32 * x55 ; x58 = x57 ! [2] ; x59 = x57 ! [1] ; x60 = x57 ! [0] in (tfromList [], x26 * tkonst 784 x60, x26 * tkonst 784 x59, x26 * tkonst 784 x58, x57, x30 * tkonst 3 x54, x30 * tkonst 3 x53, x30 * tkonst 3 x52, x30 * tkonst 3 x51, x50, x36 * tkonst 4 x47, x36 * tkonst 4 x46, x36 * tkonst 4 x45, x36 * tkonst 4 x44, x36 * tkonst 4 x43, x42)"
  printPrimal6Pretty renames artifact6nonLin
    @?= "\\s0 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> let x26 = tkonst 784 (tconst 7.0) ; x27 = tfromList [tsum (x3 * x26), tsum (x4 * x26), tsum (x5 * x26)] + x6 ; x30 = let x28 = exp (negate x27) ; x29 = tkonst 3 (tconst 1.0) + x28 in recip x29 ; x31 = tkonst 3 (tconst 1.0) - x30 ; x32 = x30 * x31 ; x33 = tfromList [tsum (x7 * x30), tsum (x8 * x30), tsum (x9 * x30), tsum (x10 * x30)] + x11 ; x36 = let x34 = exp (negate x33) ; x35 = tkonst 4 (tconst 1.0) + x34 in recip x35 ; x37 = tkonst 4 (tconst 1.0) - x36 ; x38 = x36 * x37 ; x39 = exp (tfromList [tsum (x12 * x36), tsum (x13 * x36), tsum (x14 * x36), tsum (x15 * x36), tsum (x16 * x36)] + x17) ; x40 = tsum x39 ; x41 = tkonst 5 (recip x40) in x41 * x39"
  printGradient6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\s0 dret x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> let x26 = tconstant (tkonst 784 (tconst 7.0)) ; x27 = tfromList [tsum (x3 * x26), tsum (x4 * x26), tsum (x5 * x26)] + x6 ; x30 = recip (tconstant (tkonst 3 (tconst 1.0)) + exp (negate x27)) ; x33 = tfromList [tsum (x7 * x30), tsum (x8 * x30), tsum (x9 * x30), tsum (x10 * x30)] + x11 ; x36 = recip (tconstant (tkonst 4 (tconst 1.0)) + exp (negate x33)) ; x39 = exp (tfromList [tsum (x12 * x36), tsum (x13 * x36), tsum (x14 * x36), tsum (x15 * x36), tsum (x16 * x36)] + x17) ; x40 = tsum x39 ; x42 = x39 * (tkonst 5 (negate (recip (x40 * x40)) * tsum (x39 * dret)) + tkonst 5 (recip x40) * dret) ; x43 = x42 ! [4] ; x44 = x42 ! [3] ; x45 = x42 ! [2] ; x46 = x42 ! [1] ; x47 = x42 ! [0] ; x48 = x12 * tkonst 5 x47 + x13 * tkonst 5 x46 + x14 * tkonst 5 x45 + x15 * tkonst 5 x44 + x16 * tkonst 5 x43 ; x50 = (x36 * (tconstant (tkonst 4 (tconst 1.0)) - x36)) * x48 ; x51 = x50 ! [3] ; x52 = x50 ! [2] ; x53 = x50 ! [1] ; x54 = x50 ! [0] ; x55 = x7 * tkonst 4 x54 + x8 * tkonst 4 x53 + x9 * tkonst 4 x52 + x10 * tkonst 4 x51 ; x57 = (x30 * (tconstant (tkonst 3 (tconst 1.0)) - x30)) * x55 in (tfromList [], x26 * tkonst 784 (x57 ! [0]), x26 * tkonst 784 (x57 ! [1]), x26 * tkonst 784 (x57 ! [2]), x57, x30 * tkonst 3 x54, x30 * tkonst 3 x53, x30 * tkonst 3 x52, x30 * tkonst 3 x51, x50, x36 * tkonst 4 x47, x36 * tkonst 4 x46, x36 * tkonst 4 x45, x36 * tkonst 4 x44, x36 * tkonst 4 x43, x42)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\s0 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> let x26 = tconstant (tkonst 784 (tconst 7.0)) ; x30 = recip (tconstant (tkonst 3 (tconst 1.0)) + exp (negate (tfromList [tsum (x3 * x26), tsum (x4 * x26), tsum (x5 * x26)] + x6))) ; x36 = recip (tconstant (tkonst 4 (tconst 1.0)) + exp (negate (tfromList [tsum (x7 * x30), tsum (x8 * x30), tsum (x9 * x30), tsum (x10 * x30)] + x11))) ; x39 = exp (tfromList [tsum (x12 * x36), tsum (x13 * x36), tsum (x14 * x36), tsum (x15 * x36), tsum (x16 * x36)] + x17) in tkonst 5 (recip (tsum x39)) * x39"

valsInitVT2OPP :: MnistFcnnRanked2.ADFcnnMnist2Parameters Double
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
    @?= "\\s0 dret x3 x4 x5 x6 x7 x8 -> let x12 = tkonst 3 (tkonst 784 (tconst 7.0)) ; x13 = tkonst 4 (tsum (ttranspose [1,0] (x12 * x3)) + x4) ; x14 = tkonst 5 (tsum (ttranspose [1,0] (x13 * x5)) + x6) ; x15 = ttranspose [1,0] (tkonst 4 dret) ; x16 = tsum (x7 * x15) ; x17 = ttranspose [1,0] (tkonst 3 x16) ; x18 = tsum (x5 * x17) ; x19 = ttranspose [1,0] (tkonst 784 x18) in (tfromList [], x12 * x19, x18, x13 * x17, x16, x14 * x15, dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 x4 x5 x6 x7 x8 -> let x12 = tkonst 3 (tkonst 784 (tconst 7.0)) ; x13 = tkonst 4 (tsum (ttranspose [1,0] (x12 * x3)) + x4) ; x14 = tkonst 5 (tsum (ttranspose [1,0] (x13 * x5)) + x6) in tsum (ttranspose [1,0] (x14 * x7)) + x8"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret x3 x4 x5 x6 x7 x8 -> let x12 = tconstant (tkonst 3 (tkonst 784 (tconst 7.0))) ; x13 = tkonst 4 (tsum (ttranspose [1,0] (x12 * x3)) + x4) ; x15 = tgather [5,4] dret (\\[i20, i21] -> [i20]) ; x16 = tsum (x7 * x15) ; x17 = tgather [5,3] x16 (\\[i22, i23] -> [i22]) ; x18 = tsum (x5 * x17) in (tfromList [], x12 * tgather [4,784] x18 (\\[i24, i25] -> [i24]), x18, x13 * x17, x16, tkonst 5 (tsum (ttranspose [1,0] (x13 * x5)) + x6) * x15, dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 x3 x4 x5 x6 x7 x8 -> tsum (ttranspose [1,0] (tkonst 5 (tsum (ttranspose [1,0] (tkonst 4 (tsum (ttranspose [1,0] (tconstant (tkonst 3 (tkonst 784 (tconst 7.0))) * x3)) + x4) * x5)) + x6) * x7)) + x8"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstKonst sizeMnistGlyphInt 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters (Ast0 Double)
                    -> TensorOf 1 (Ast0 Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMaxV blackGlyph
      (artifact6nonLin, _) = revDtFun afcnn2TnonLin valsInitVT2OPP
  printGradient6Pretty renames artifact6nonLin
    @?= "\\s0 dret x3 x4 x5 x6 x7 x8 -> let x17 = tkonst 3 (tkonst 784 (tconst 7.0)) ; x18 = tsum (ttranspose [1,0] (x17 * x3)) + x4 ; x21 = let x19 = exp (negate x18) ; x20 = tkonst 3 (tconst 1.0) + x19 in recip x20 ; x22 = tkonst 3 (tconst 1.0) - x21 ; x23 = x21 * x22 ; x24 = tkonst 4 x21 ; x25 = tsum (ttranspose [1,0] (x24 * x5)) + x6 ; x28 = let x26 = exp (negate x25) ; x27 = tkonst 4 (tconst 1.0) + x26 in recip x27 ; x29 = tkonst 4 (tconst 1.0) - x28 ; x30 = x28 * x29 ; x31 = tkonst 5 x28 ; x32 = exp (tsum (ttranspose [1,0] (x31 * x7)) + x8) ; x33 = tsum x32 ; x34 = tkonst 5 (recip x33) ; x35 = x32 * (tkonst 5 (negate (recip (x33 * x33)) * tsum (x32 * dret)) + x34 * dret) ; x36 = ttranspose [1,0] (tkonst 4 x35) ; x37 = tsum (x7 * x36) ; x38 = x28 * (x25 * x37) ; x39 = x30 * x37 ; x40 = ttranspose [1,0] (tkonst 3 x39) ; x41 = tsum (x5 * x40) ; x42 = x21 * (x18 * x41) ; x43 = x23 * x41 ; x44 = ttranspose [1,0] (tkonst 784 x43) in (tfromList [], x17 * x44, x43, x24 * x40, x39, x31 * x36, x35)"
  printPrimal6Pretty renames artifact6nonLin
    @?= "\\s0 x3 x4 x5 x6 x7 x8 -> let x17 = tkonst 3 (tkonst 784 (tconst 7.0)) ; x18 = tsum (ttranspose [1,0] (x17 * x3)) + x4 ; x21 = let x19 = exp (negate x18) ; x20 = tkonst 3 (tconst 1.0) + x19 in recip x20 ; x22 = tkonst 3 (tconst 1.0) - x21 ; x23 = x21 * x22 ; x24 = tkonst 4 x21 ; x25 = tsum (ttranspose [1,0] (x24 * x5)) + x6 ; x28 = let x26 = exp (negate x25) ; x27 = tkonst 4 (tconst 1.0) + x26 in recip x27 ; x29 = tkonst 4 (tconst 1.0) - x28 ; x30 = x28 * x29 ; x31 = tkonst 5 x28 ; x32 = exp (tsum (ttranspose [1,0] (x31 * x7)) + x8) ; x33 = tsum x32 ; x34 = tkonst 5 (recip x33) in x34 * x32"
  printGradient6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\s0 dret x3 x4 x5 x6 x7 x8 -> let x17 = tconstant (tkonst 3 (tkonst 784 (tconst 7.0))) ; x18 = tsum (ttranspose [1,0] (x17 * x3)) + x4 ; x21 = recip (tconstant (tkonst 3 (tconst 1.0)) + exp (negate x18)) ; x24 = tkonst 4 x21 ; x25 = tsum (ttranspose [1,0] (x24 * x5)) + x6 ; x28 = recip (tconstant (tkonst 4 (tconst 1.0)) + exp (negate x25)) ; x31 = tkonst 5 x28 ; x32 = exp (tsum (ttranspose [1,0] (x31 * x7)) + x8) ; x33 = tsum x32 ; x35 = x32 * (tkonst 5 (negate (recip (x33 * x33)) * tsum (x32 * dret)) + tkonst 5 (recip x33) * dret) ; x36 = tgather [5,4] x35 (\\[i45, i46] -> [i45]) ; x37 = tsum (x7 * x36) ; x39 = (x28 * (tconstant (tkonst 4 (tconst 1.0)) - x28)) * x37 ; x40 = tgather [4,3] x39 (\\[i47, i48] -> [i47]) ; x41 = tsum (x5 * x40) ; x43 = (x21 * (tconstant (tkonst 3 (tconst 1.0)) - x21)) * x41 in (tfromList [], x17 * tgather [3,784] x43 (\\[i49, i50] -> [i49]), x43, x24 * x40, x39, x31 * x36, x35)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6nonLin)
    @?= "\\s0 x3 x4 x5 x6 x7 x8 -> let x21 = recip (tconstant (tkonst 3 (tconst 1.0)) + exp (negate (tsum (ttranspose [1,0] (tconstant (tkonst 3 (tkonst 784 (tconst 7.0))) * x3)) + x4))) ; x28 = recip (tconstant (tkonst 4 (tconst 1.0)) + exp (negate (tsum (ttranspose [1,0] (tkonst 4 x21 * x5)) + x6))) ; x32 = exp (tsum (ttranspose [1,0] (tkonst 5 x28 * x7)) + x8) in tkonst 5 (recip (tsum x32)) * x32"
