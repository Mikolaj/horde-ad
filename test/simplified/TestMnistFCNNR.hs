-- | Tests of "MnistFcnnRanked1" and "MnistFcnnRanked2" neural networks
-- using a few different optimization pipelines.
module TestMnistFCNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import Data.Array.RankedS qualified as OR
import Data.IntMap.Strict qualified as IM
import Data.List.Index (imap)
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (SomeNat (..), someNatVal)
import Numeric.LinearAlgebra qualified as LA
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Text.Printf

import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.TensorAst
import HordeAd.External.OptimizerTools
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))

import EqEpsilon

import MnistData
import MnistFcnnRanked1 qualified
import MnistFcnnRanked2 qualified

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
     ( ranked ~ ORArray, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTA prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [nPV]
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
      emptyR = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [0] []
      hVectorInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length params1Init)
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector ORArray -> r
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
       let runBatch :: HVector ORArray -> (Int, [MnistData r]) -> IO (HVector ORArray)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f mnist adinputs =
                   MnistFcnnRanked1.afcnnMnistLoss1
                     widthHidden widthHidden2
                     mnist (parseHVector (fromDValue valsInit) adinputs)
                 res = fst $ sgd gamma f chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector ORArray -> IO (HVector ORArray)
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 hVectorInit
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
  , mnistTestCase1VTA "VTA 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCase1VTI
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTI prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [nPV]
          $ V.map realToFrac
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [0] []
      hVectorInit = V.fromList params1Init
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
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector ORArray -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 valsInit widthHidden widthHidden2
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, hVectorPrimal, vars, _)
         <- funToAstRevIO (voidFromHVector hVectorInit)
       (varGlyph, _, astGlyph) <-
         funToAstIO (FTKR $ singletonShape sizeMnistGlyphInt) id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ singletonShape sizeMnistLabelInt) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistFcnnRanked1.afcnnMnistLoss1TensorData
                   widthHidden widthHidden2 (AstRanked $ astGlyph, AstRanked $ astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (unRawHVector hVectorPrimal))
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector ORArray -> (Int, [MnistData r]) -> IO (HVector ORArray)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvD emptyEnv
                             $ zip vars $ V.toList varInputs
                       envMnist =
                         extendEnv varGlyph
                           (rconst $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) glyph)
                         $ extendEnv varLabel
                             (rconst $ Nested.rfromVector (fromList [sizeMnistLabelInt]) label)
                             env
                   in interpretAst envMnist $ unAstRanked ast
                 res = fst $ sgd gamma f chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector ORArray -> IO (HVector ORArray)
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 hVectorInit
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
  , mnistTestCase1VTI "VTI 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCase1VTO
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTO prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [nPV]
          $ V.map realToFrac
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [0] []
      hVectorInit = V.fromList params1Init
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
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector ORArray -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 valsInit widthHidden widthHidden2
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (varGlyph, varGlyphD, astGlyph) <-
         funToAstIO (FTKR $ singletonShape sizeMnistGlyphInt) id
       (varLabel, varLabelD, astLabel) <-
         funToAstIO (FTKR $ singletonShape sizeMnistLabelInt) id
       let envInit = extendEnv varGlyph (rconstant $ AstRaw astGlyph)
                     $ extendEnv varLabel (rconstant $ AstRaw astLabel)
                     emptyEnv
           f = MnistFcnnRanked1.afcnnMnistLoss1TensorData @(AstRanked FullSpan)
                 widthHidden widthHidden2
                 (rconstant $ AstRanked astGlyph, rconstant $ AstRanked astLabel)
           (AstArtifact varDtAgain vars1Again gradientRaw primal, _) =
             revProduceArtifactH False f envInit valsInit
                                 (voidFromHVector hVectorInit)
           gradient = simplifyInlineHVectorRaw gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           art = AstArtifact varDtAgain vars1AndInputAgain gradient primal
           go :: [MnistData r] -> HVector ORArray -> HVector ORArray
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicRanked @r @1
                          $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [sizeMnistGlyphInt] glyph
                 labelD = DynamicRanked @r @1
                          $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradient gamma parameters gradientHVector)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector ORArray -> (Int, [MnistData r]) -> IO (HVector ORArray)
           runBatch !hVector (k, chunk) = do
             let res = go chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector ORArray -> IO (HVector ORArray)
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 hVectorInit
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
  , mnistTestCase1VTO "VTO 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]


-- * Using matrices, which is rank 2

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCase2VTA
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
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
                        OSArray widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector ORArray -> r
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
       let runBatch :: HVector ORArray -> (Int, [MnistData r]) -> IO (HVector ORArray)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f mnist adinputs =
                   MnistFcnnRanked2.afcnnMnistLoss2
                     mnist (parseHVector (fromDValue valsInit) adinputs)
                 res = fst $ sgd gamma f chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector ORArray -> IO (HVector ORArray)
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 hVectorInit
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
  , mnistTestCase2VTA "VTA2 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCase2VTI
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
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
                        OSArray widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector ORArray -> r
      ftest = MnistFcnnRanked2.afcnnMnistTest2 valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, hVectorPrimal, vars, _)
         <- funToAstRevIO (voidFromHVector hVectorInit)
       (varGlyph, _, astGlyph) <-
         funToAstIO (FTKR $ singletonShape sizeMnistGlyphInt) id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ singletonShape sizeMnistLabelInt) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistFcnnRanked2.afcnnMnistLoss2TensorData
                   (AstRanked astGlyph, AstRanked astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (unRawHVector hVectorPrimal))
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector ORArray -> (Int, [MnistData r]) -> IO (HVector ORArray)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvD emptyEnv
                             $ zip vars $ V.toList varInputs
                       envMnist =
                         extendEnv varGlyph
                           (rconst $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) glyph)
                         $ extendEnv varLabel
                             (rconst $ Nested.rfromVector (fromList [sizeMnistLabelInt]) label)
                             env
                   in interpretAst envMnist $ unAstRanked ast
                 res = fst $ sgd gamma f chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector ORArray -> IO (HVector ORArray)
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 hVectorInit
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
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
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
               OSArray widthHidden widthHidden2 r
        valsInitShaped = fst $ randomVals 1 (mkStdGen 44)
        valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
        valsInit =
          -- This almost works and I wouldn't need forgetShape,
          -- but there is nowhere to get aInit from.
          --   parseHVector aInit hVectorInit
          forgetShape valsInitShaped
        hVectorInit = toHVectorOf valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show widthHidden, show widthHidden2
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit)
                          , show gamma ]
        ftest :: [MnistData r] -> HVector ORArray -> r
        ftest = MnistFcnnRanked2.afcnnMnistTest2 valsInit
    in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (varGlyph, varGlyphD, astGlyph) <-
         funToAstIO (FTKR $ singletonShape sizeMnistGlyphInt) id
       (varLabel, varLabelD, astLabel) <-
         funToAstIO (FTKR $ singletonShape sizeMnistLabelInt) id
       let envInit = extendEnv varGlyph (rconstant $ AstRaw astGlyph)
                     $ extendEnv varLabel (rconstant $ AstRaw astLabel)
                       emptyEnv
           f = MnistFcnnRanked2.afcnnMnistLoss2TensorData @(AstRanked FullSpan)
                 (rconstant $ AstRanked astGlyph, rconstant $ AstRanked astLabel)
           (AstArtifact varDtAgain vars1Again gradientRaw primal, _) =
             revProduceArtifactH False f envInit valsInit
                                 (voidFromHVector hVectorInit)
           gradient = simplifyInlineHVectorRaw gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           art = AstArtifact varDtAgain vars1AndInputAgain gradient primal
           go :: [MnistData r] -> HVector ORArray -> HVector ORArray
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicRanked @r @1
                          $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [sizeMnistGlyphInt] glyph
                 labelD = DynamicRanked @r @1
                          $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradient gamma parameters gradientHVector)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector ORArray -> (Int, [MnistData r]) -> IO (HVector ORArray)
           runBatch !hVector (k, chunk) = do
             let res = go chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector ORArray -> IO (HVector ORArray)
           runEpoch n params | n > epochs = return params
           runEpoch n !params = do
             unless (widthHidden < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf batchSize trainDataShuffled
             res <- foldM runBatch params chunks
             runEpoch (succ n) res
       res <- runEpoch 1 hVectorInit
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

valsInitVTOPP :: MnistFcnnRanked1.ADFcnnMnist1Parameters ORArray Double
valsInitVTOPP =
  ( ( replicate 3 (FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [3] [1, 2, 3])
    , FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [3] [1, 2, 3] )
  , ( replicate 4 (FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [4] [1, 2, 3, 4])
    , FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [4] [1, 2, 3, 4] )
  , ( replicate 5 (FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [5] [1, 2, 3, 4, 5])
    , FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [5] [1, 2, 3, 4, 5] ) )

testVTOPP :: Assertion
testVTOPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @SizeMnistGlyph)
                     (7 :: AstTensor FullSpan (TKR Double 0))
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters (AstRanked FullSpan)
                                                         Double
              -> AstRanked FullSpan Double 1
      afcnn2T = MnistFcnnRanked1.afcnnMnist1 id id 3 4 $ AstRanked blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVTOPP
  printArtifactPretty renames artifactRev
    @?= "\\v20 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 -> let v18 = rfromVector (fromList [rsum (rreshape [3] (v1 * rreplicate 3 7.0)), rsum (rreshape [3] (v2 * rreplicate 3 7.0)), rsum (rreshape [3] (v3 * rreplicate 3 7.0))]) + v4 ; v19 = rfromVector (fromList [rsum (rreshape [4] (v5 * v18)), rsum (rreshape [4] (v6 * v18)), rsum (rreshape [4] (v7 * v18)), rsum (rreshape [4] (v8 * v18))]) + v9 ; x21 = v20 ! [4] ; x22 = v20 ! [3] ; x23 = v20 ! [2] ; x24 = v20 ! [1] ; x25 = v20 ! [0] ; v26 = v10 * rreshape [5] (rreplicate 5 x25) + v11 * rreshape [5] (rreplicate 5 x24) + v12 * rreshape [5] (rreplicate 5 x23) + v13 * rreshape [5] (rreplicate 5 x22) + v14 * rreshape [5] (rreplicate 5 x21) ; x27 = v26 ! [3] ; x28 = v26 ! [2] ; x29 = v26 ! [1] ; x30 = v26 ! [0] ; v31 = v5 * rreshape [4] (rreplicate 4 x30) + v6 * rreshape [4] (rreplicate 4 x29) + v7 * rreshape [4] (rreplicate 4 x28) + v8 * rreshape [4] (rreplicate 4 x27) ; x32 = v31 ! [2] ; x33 = v31 ! [1] ; x34 = v31 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x34), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x33), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x32), v31, v18 * rreshape [3] (rreplicate 3 x30), v18 * rreshape [3] (rreplicate 3 x29), v18 * rreshape [3] (rreplicate 3 x28), v18 * rreshape [3] (rreplicate 3 x27), v26, v19 * rreshape [4] (rreplicate 4 x25), v19 * rreshape [4] (rreplicate 4 x24), v19 * rreshape [4] (rreplicate 4 x23), v19 * rreshape [4] (rreplicate 4 x22), v19 * rreshape [4] (rreplicate 4 x21), v20]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 -> let v18 = rfromVector (fromList [rsum (rreshape [3] (v1 * rreplicate 3 7.0)), rsum (rreshape [3] (v2 * rreplicate 3 7.0)), rsum (rreshape [3] (v3 * rreplicate 3 7.0))]) + v4 ; v19 = rfromVector (fromList [rsum (rreshape [4] (v5 * v18)), rsum (rreshape [4] (v6 * v18)), rsum (rreshape [4] (v7 * v18)), rsum (rreshape [4] (v8 * v18))]) + v9 in [rfromVector (fromList [rsum (rreshape [5] (v10 * v19)), rsum (rreshape [5] (v11 * v19)), rsum (rreshape [5] (v12 * v19)), rsum (rreshape [5] (v13 * v19)), rsum (rreshape [5] (v14 * v19))]) + v15]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v20 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 -> let v18 = rfromVector (fromList [rsum (v1 * rreplicate 3 7.0), rsum (v2 * rreplicate 3 7.0), rsum (v3 * rreplicate 3 7.0)]) + v4 ; v19 = rfromVector (fromList [rsum (v5 * v18), rsum (v6 * v18), rsum (v7 * v18), rsum (v8 * v18)]) + v9 ; x21 = v20 ! [4] ; x22 = v20 ! [3] ; x23 = v20 ! [2] ; x24 = v20 ! [1] ; x25 = v20 ! [0] ; v26 = v10 * rreplicate 5 x25 + v11 * rreplicate 5 x24 + v12 * rreplicate 5 x23 + v13 * rreplicate 5 x22 + v14 * rreplicate 5 x21 ; x27 = v26 ! [3] ; x28 = v26 ! [2] ; x29 = v26 ! [1] ; x30 = v26 ! [0] ; v31 = v5 * rreplicate 4 x30 + v6 * rreplicate 4 x29 + v7 * rreplicate 4 x28 + v8 * rreplicate 4 x27 in [rreplicate 3 7.0 * rreplicate 3 (v31 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v31 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v31 ! [2]), v31, v18 * rreplicate 3 x30, v18 * rreplicate 3 x29, v18 * rreplicate 3 x28, v18 * rreplicate 3 x27, v26, v19 * rreplicate 4 x25, v19 * rreplicate 4 x24, v19 * rreplicate 4 x23, v19 * rreplicate 4 x22, v19 * rreplicate 4 x21, v20]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 -> let v18 = rfromVector (fromList [rsum (v1 * rreplicate 3 7.0), rsum (v2 * rreplicate 3 7.0), rsum (v3 * rreplicate 3 7.0)]) + v4 ; v19 = rfromVector (fromList [rsum (v5 * v18), rsum (v6 * v18), rsum (v7 * v18), rsum (v8 * v18)]) + v9 in [rfromVector (fromList [rsum (v10 * v19), rsum (v11 * v19), rsum (v12 * v19), rsum (v13 * v19), rsum (v14 * v19)]) + v15]"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @SizeMnistGlyph)
                     (7 :: AstTensor FullSpan (TKR Double 0))
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                         (AstRanked FullSpan) Double
                    -> AstRanked FullSpan Double 1
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMax1 3 4 $ AstRanked blackGlyph
      (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVTOPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v38 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 -> let v23 = rfromVector (fromList [rsum (rreshape [3] (v1 * rreplicate 3 7.0)), rsum (rreshape [3] (v2 * rreplicate 3 7.0)), rsum (rreshape [3] (v3 * rreplicate 3 7.0))]) + v4 ; v24 = exp (negate v23) ; v25 = rreplicate 3 1.0 + v24 ; v26 = recip v25 ; v27 = rreplicate 3 1.0 - v26 ; v28 = v26 * v27 ; v29 = rfromVector (fromList [rsum (rreshape [4] (v5 * v26)), rsum (rreshape [4] (v6 * v26)), rsum (rreshape [4] (v7 * v26)), rsum (rreshape [4] (v8 * v26))]) + v9 ; v30 = exp (negate v29) ; v31 = rreplicate 4 1.0 + v30 ; v32 = recip v31 ; v33 = rreplicate 4 1.0 - v32 ; v34 = v32 * v33 ; v35 = exp (rfromVector (fromList [rsum (rreshape [5] (v10 * v32)), rsum (rreshape [5] (v11 * v32)), rsum (rreshape [5] (v12 * v32)), rsum (rreshape [5] (v13 * v32)), rsum (rreshape [5] (v14 * v32))]) + v15) ; x36 = rsum v35 ; v37 = rreplicate 5 (recip x36) ; v39 = v35 * (rreplicate 5 (negate (recip (x36 * x36)) * rsum (v35 * v38)) + v37 * v38) ; x40 = v39 ! [4] ; x41 = v39 ! [3] ; x42 = v39 ! [2] ; x43 = v39 ! [1] ; x44 = v39 ! [0] ; v45 = v34 * (v10 * rreshape [5] (rreplicate 5 x44) + v11 * rreshape [5] (rreplicate 5 x43) + v12 * rreshape [5] (rreplicate 5 x42) + v13 * rreshape [5] (rreplicate 5 x41) + v14 * rreshape [5] (rreplicate 5 x40)) ; x46 = v45 ! [3] ; x47 = v45 ! [2] ; x48 = v45 ! [1] ; x49 = v45 ! [0] ; v50 = v28 * (v5 * rreshape [4] (rreplicate 4 x49) + v6 * rreshape [4] (rreplicate 4 x48) + v7 * rreshape [4] (rreplicate 4 x47) + v8 * rreshape [4] (rreplicate 4 x46)) ; x51 = v50 ! [2] ; x52 = v50 ! [1] ; x53 = v50 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x53), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x52), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x51), v50, v26 * rreshape [3] (rreplicate 3 x49), v26 * rreshape [3] (rreplicate 3 x48), v26 * rreshape [3] (rreplicate 3 x47), v26 * rreshape [3] (rreplicate 3 x46), v45, v32 * rreshape [4] (rreplicate 4 x44), v32 * rreshape [4] (rreplicate 4 x43), v32 * rreshape [4] (rreplicate 4 x42), v32 * rreshape [4] (rreplicate 4 x41), v32 * rreshape [4] (rreplicate 4 x40), v39]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 -> let v23 = rfromVector (fromList [rsum (rreshape [3] (v1 * rreplicate 3 7.0)), rsum (rreshape [3] (v2 * rreplicate 3 7.0)), rsum (rreshape [3] (v3 * rreplicate 3 7.0))]) + v4 ; v24 = exp (negate v23) ; v25 = rreplicate 3 1.0 + v24 ; v26 = recip v25 ; v29 = rfromVector (fromList [rsum (rreshape [4] (v5 * v26)), rsum (rreshape [4] (v6 * v26)), rsum (rreshape [4] (v7 * v26)), rsum (rreshape [4] (v8 * v26))]) + v9 ; v30 = exp (negate v29) ; v31 = rreplicate 4 1.0 + v30 ; v32 = recip v31 ; v35 = exp (rfromVector (fromList [rsum (rreshape [5] (v10 * v32)), rsum (rreshape [5] (v11 * v32)), rsum (rreshape [5] (v12 * v32)), rsum (rreshape [5] (v13 * v32)), rsum (rreshape [5] (v14 * v32))]) + v15) ; x36 = rsum v35 ; v37 = rreplicate 5 (recip x36) in [v37 * v35]"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v38 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 -> let v26 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v1 * rreplicate 3 7.0), rsum (v2 * rreplicate 3 7.0), rsum (v3 * rreplicate 3 7.0)]) + v4))) ; v32 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v5 * v26), rsum (v6 * v26), rsum (v7 * v26), rsum (v8 * v26)]) + v9))) ; v35 = exp (rfromVector (fromList [rsum (v10 * v32), rsum (v11 * v32), rsum (v12 * v32), rsum (v13 * v32), rsum (v14 * v32)]) + v15) ; x36 = rsum v35 ; v39 = v35 * (rreplicate 5 (negate (recip (x36 * x36)) * rsum (v35 * v38)) + rreplicate 5 (recip x36) * v38) ; x40 = v39 ! [4] ; x41 = v39 ! [3] ; x42 = v39 ! [2] ; x43 = v39 ! [1] ; x44 = v39 ! [0] ; v45 = (v32 * (rreplicate 4 1.0 - v32)) * (v10 * rreplicate 5 x44 + v11 * rreplicate 5 x43 + v12 * rreplicate 5 x42 + v13 * rreplicate 5 x41 + v14 * rreplicate 5 x40) ; x46 = v45 ! [3] ; x47 = v45 ! [2] ; x48 = v45 ! [1] ; x49 = v45 ! [0] ; v50 = (v26 * (rreplicate 3 1.0 - v26)) * (v5 * rreplicate 4 x49 + v6 * rreplicate 4 x48 + v7 * rreplicate 4 x47 + v8 * rreplicate 4 x46) in [rreplicate 3 7.0 * rreplicate 3 (v50 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v50 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v50 ! [2]), v50, v26 * rreplicate 3 x49, v26 * rreplicate 3 x48, v26 * rreplicate 3 x47, v26 * rreplicate 3 x46, v45, v32 * rreplicate 4 x44, v32 * rreplicate 4 x43, v32 * rreplicate 4 x42, v32 * rreplicate 4 x41, v32 * rreplicate 4 x40, v39]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 -> let v26 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v1 * rreplicate 3 7.0), rsum (v2 * rreplicate 3 7.0), rsum (v3 * rreplicate 3 7.0)]) + v4))) ; v32 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v5 * v26), rsum (v6 * v26), rsum (v7 * v26), rsum (v8 * v26)]) + v9))) ; v35 = exp (rfromVector (fromList [rsum (v10 * v32), rsum (v11 * v32), rsum (v12 * v32), rsum (v13 * v32), rsum (v14 * v32)]) + v15) in [rreplicate 5 (recip (rsum v35)) * v35]"

valsInitVT2OPP :: MnistFcnnRanked2.ADFcnnMnist2Parameters (ORArray) Double
valsInitVT2OPP =
  ( ( FlipR $ Nested.rfromOrthotope SNat
      $ OR.fromList [4, 3] (concat $ replicate 4 [1, 2, 3])
    , FlipR $ Nested.rfromOrthotope SNat
      $ OR.fromList [4] [1, 2, 3, 4] )
  , ( FlipR $ Nested.rfromOrthotope SNat
      $ OR.fromList [5, 4] (concat $ replicate 5 [1, 2, 3, 4])
    , FlipR $ Nested.rfromOrthotope SNat
      $ OR.fromList [5] [1, 2, 3, 4, 5] )
  , ( FlipR $ Nested.rfromOrthotope SNat
      $ OR.fromList [2, 5] (concat $ replicate 2 [1, 2, 3, 4, 5])
    , FlipR $ Nested.rfromOrthotope SNat
      $ OR.fromList [2] [1, 2] ) )

testVT2OPP :: Assertion
testVT2OPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3)
                     (7 :: AstTensor FullSpan (TKR Double 0))
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                   (AstRanked FullSpan) Double
              -> AstRanked FullSpan Double 1
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id $ AstRanked blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVT2OPP
  printArtifactPretty renames artifactRev
    @?= "\\v12 m1 v2 m3 v4 m5 v6 -> let m10 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m1) + v2))) ; m11 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m10 * rtranspose [1,0] m3)) + v4)) ; v13 = rsum (rtranspose [1,0] (rtranspose [1,0] m5 * rreplicate 5 v12)) ; m14 = rreplicate 4 (rcast v13) ; v15 = rcast (rsum (rtranspose [1,0] (rtranspose [1,0] m3 * m14))) ; m16 = rreplicate 3 v15 in [rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m16), v15, rtranspose [1,0] (m10 * m14), v13, rtranspose [1,0] (m11 * rreplicate 5 v12), v12]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m1 v2 m3 v4 m5 v6 -> let m10 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m1) + v2))) ; m11 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m10 * rtranspose [1,0] m3)) + v4)) in [rsum (m11 * rtranspose [1,0] m5) + v6]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v12 m1 v2 m3 v4 m5 v6 -> let m10 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m1) + v2))) ; v13 = rsum (m5 * rtranspose [1,0] (rreplicate 5 v12)) ; m14 = rreplicate 4 (rcast v13) ; v15 = rcast (rsum (m3 * rtranspose [1,0] m14)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v15), v15, rtranspose [1,0] (m10 * m14), v13, rreplicate 2 (rcast (rsum (m10 * rtranspose [1,0] m3)) + v4) * rtranspose [1,0] (rreplicate 5 v12), v12]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1 v2 m3 v4 m5 v6 -> [rsum (rtranspose [1,0] (rreplicate 2 (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m1) + v2))) * rtranspose [1,0] m3)) + v4)) * rtranspose [1,0] m5) + v6]"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3)
                     (7 :: AstTensor FullSpan (TKR Float 0))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstRanked FullSpan) Float
                    -> AstRanked FullSpan Float 1
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 $ AstRanked blackGlyph
      constant = let ((a1, a2), (a3, a4), (a5, a6)) = valsInitVT2OPP
                 in ( ( AstRanked $ AstCast $ AstConstant $ AstConst $ runFlipR a1
                      , AstRanked $ AstCast $ AstConstant $ AstConst $ runFlipR a2 )
                    , ( AstRanked $ AstConstant $ AstCast $ AstConst $ runFlipR a3
                      , AstRanked $ AstConstant $ AstCast $ AstConst $ runFlipR a4 )
                    , ( AstRanked $ AstCast $ AstConstant $ AstConst $ runFlipR a5
                      , AstRanked $ AstConstant $ AstCast $ AstConst $ runFlipR a6 ) )
      (_, ast3) = funToAst (FTKR @Float $ singletonShape 0)
                           (const $ unAstRanked $ afcnn2TnonLin constant)
  "\\dummy" ++ " -> " ++ printAstSimple renames (AstRanked ast3)
    @?= "\\dummy -> rlet (exp (rsum (rtranspose [1,0] (rreplicate 2 (rlet (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rlet (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rconstant 7.0))) * rconstant (rconst (rfromListLinear [3,4] [1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0]))) + rcast (rconstant (rconst (rfromListLinear [4] [1.0,2.0,3.0,4.0])))) (\\v3 -> rlet (rconstant (recip (rreplicate 4 1.0 + exp (negate (rprimalPart v3))))) (\\v4 -> rD (rprimalPart v4) (rdualPart (rconstant (rprimalPart v4 * (rreplicate 4 1.0 - rprimalPart v4)) * rD (rreplicate 4 0.0) (rdualPart v3)))))))) * rconstant (rconst (rfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0])))) + rconstant (rcast (rconst (rfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v6 -> rlet (rconstant (recip (rreplicate 5 1.0 + exp (negate (rprimalPart v6))))) (\\v7 -> rD (rprimalPart v7) (rdualPart (rconstant (rprimalPart v7 * (rreplicate 5 1.0 - rprimalPart v7)) * rD (rreplicate 5 0.0) (rdualPart v6))))))) * rconstant (rconst (rfromListLinear [5,2] [1.0,1.0,2.0,2.0,3.0,3.0,4.0,4.0,5.0,5.0]))) + rconstant (rcast (rconst (rfromListLinear [2] [1.0,2.0]))))) (\\v9 -> rreplicate 2 (recip (rsum v9)) * v9)"

testVT2OPPNonLin2 :: Assertion
testVT2OPPNonLin2 = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3)
                     (7 :: AstTensor FullSpan (TKR Double 0))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstRanked FullSpan) Double
                    -> AstRanked FullSpan Double 1
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 $ AstRanked blackGlyph
  let (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVT2OPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v32 m1 v2 m3 v4 m5 v6 -> let v15 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m1) + v2 ; v16 = exp (negate v15) ; v17 = rreplicate 4 1.0 + v16 ; v18 = recip v17 ; v19 = rreplicate 4 1.0 - v18 ; v20 = v18 * v19 ; m21 = rtranspose [1,0] (rreplicate 5 (rcast v18)) ; v22 = rcast (rsum (m21 * rtranspose [1,0] m3)) + v4 ; v23 = exp (negate v22) ; v24 = rreplicate 5 1.0 + v23 ; v25 = recip v24 ; v26 = rreplicate 5 1.0 - v25 ; v27 = v25 * v26 ; m28 = rtranspose [1,0] (rreplicate 2 v25) ; v29 = exp (rsum (m28 * rtranspose [1,0] m5) + v6) ; x30 = rsum v29 ; v31 = rreplicate 2 (recip x30) ; v33 = v29 * (rreplicate 2 (negate (recip (x30 * x30)) * rsum (v29 * v32)) + v31 * v32) ; m34 = rreplicate 5 v33 ; v35 = v27 * rsum (rtranspose [1,0] (rtranspose [1,0] m5 * m34)) ; m36 = rreplicate 4 (rcast v35) ; v37 = v20 * rcast (rsum (rtranspose [1,0] (rtranspose [1,0] m3 * m36))) ; m38 = rreplicate 3 v37 in [rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m38), v37, rtranspose [1,0] (m21 * m36), v35, rtranspose [1,0] (m28 * m34), v33]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\m1 v2 m3 v4 m5 v6 -> let v15 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m1) + v2 ; v16 = exp (negate v15) ; v17 = rreplicate 4 1.0 + v16 ; v18 = recip v17 ; m21 = rtranspose [1,0] (rreplicate 5 (rcast v18)) ; v22 = rcast (rsum (m21 * rtranspose [1,0] m3)) + v4 ; v23 = exp (negate v22) ; v24 = rreplicate 5 1.0 + v23 ; v25 = recip v24 ; m28 = rtranspose [1,0] (rreplicate 2 v25) ; v29 = exp (rsum (m28 * rtranspose [1,0] m5) + v6) ; x30 = rsum v29 ; v31 = rreplicate 2 (recip x30) in [v31 * v29]"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v32 m1 v2 m3 v4 m5 v6 -> let v18 = recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m1) + v2))) ; m21 = rtranspose [1,0] (rreplicate 5 (rcast v18)) ; v25 = recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (m21 * rtranspose [1,0] m3)) + v4))) ; v29 = exp (rsum (rtranspose [1,0] (rreplicate 2 v25) * rtranspose [1,0] m5) + v6) ; x30 = rsum v29 ; v33 = v29 * (rreplicate 2 (negate (recip (x30 * x30)) * rsum (v29 * v32)) + rreplicate 2 (recip x30) * v32) ; v35 = (v25 * (rreplicate 5 1.0 - v25)) * rsum (m5 * rtranspose [1,0] (rreplicate 5 v33)) ; m36 = rreplicate 4 (rcast v35) ; v37 = (v18 * (rreplicate 4 1.0 - v18)) * rcast (rsum (m3 * rtranspose [1,0] m36)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v37), v37, rtranspose [1,0] (m21 * m36), v35, rreplicate 2 v25 * rtranspose [1,0] (rreplicate 5 v33), v33]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\m1 v2 m3 v4 m5 v6 -> let v29 = exp (rsum (rtranspose [1,0] (rreplicate 2 (recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m1) + v2)))))) * rtranspose [1,0] m3)) + v4))))) * rtranspose [1,0] m5) + v6) in [rreplicate 2 (recip (rsum v29)) * v29]"
