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
import HordeAd.Core.TensorAst (revProduceArtifactTKNew)
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
       let dataInit = case testData of
             d : _ -> let (dglyph, dlabel) = d
                      in ( FlipR $ Nested.rfromOrthotope SNat
                           $ OR.fromVector [sizeMnistGlyphInt] dglyph
                         , FlipR $ Nested.rfromOrthotope SNat
                           $ OR.fromVector [sizeMnistLabelInt] dlabel )
             [] -> error "empty test data"
           f = \ (pars, (glyphR, labelR)) ->
             MnistFcnnRanked1.afcnnMnistLoss1TensorData
               widthHidden widthHidden2
               (glyphR, labelR) pars
           g :: HVector (AstRanked FullSpan)
             -> InterpretationTarget (AstRanked FullSpan) TKUntyped
           g !hv = HVectorPseudoTensor
                   $ toHVectorOf $ f
                   $ parseHVector (fromValue (valsInit, dataInit)) hv
           (artRaw, _) = revProduceArtifactTKNew False g emptyEnv
                           (FTKUntyped $ voidFromHVector
                            $ hVectorInit
                              V.++ V.fromList [ DynamicRanked @r @1
                                                $ fst dataInit
                                              , DynamicRanked @r @1
                                                $ snd dataInit ])
           art = simplifyArtifactGradient artRaw
           go :: [MnistData r] -> HVector ORArray -> HVector ORArray
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicRanked @r @1
                          $ FlipR $ Nested.rfromOrthotope SNat
                          $ OR.fromVector [sizeMnistGlyphInt] glyph
                 labelD = DynamicRanked @r @1
                          $ FlipR $ Nested.rfromOrthotope SNat
                          $ OR.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifactTKNew art parametersAndInput Nothing
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
       let dataInit = case testData of
             d : _ -> let (dglyph, dlabel) = d
                      in ( FlipR $ Nested.rfromOrthotope SNat
                           $ OR.fromVector [sizeMnistGlyphInt] dglyph
                         , FlipR $ Nested.rfromOrthotope SNat
                           $ OR.fromVector [sizeMnistLabelInt] dlabel )
             [] -> error "empty test data"
           f = \ (pars, (glyphR, labelR)) ->
             MnistFcnnRanked2.afcnnMnistLoss2TensorData
               (glyphR, labelR) pars
           (artRaw, _) = revArtifactAdapt False f (valsInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistData r] -> HVector ORArray -> HVector ORArray
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicRanked @r @1
                          $ FlipR $ Nested.rfromOrthotope SNat
                          $ OR.fromVector [sizeMnistGlyphInt] glyph
                 labelD = DynamicRanked @r @1
                          $ FlipR $ Nested.rfromOrthotope SNat
                          $ OR.fromVector [sizeMnistLabelInt] label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifactTKNew art parametersAndInput Nothing
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
    @?= "\\v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 -> let v4 = rfromVector (fromList [rsum (v31 * rreplicate 3 7.0), rsum (v32 * rreplicate 3 7.0), rsum (v33 * rreplicate 3 7.0)]) + v34 ; v5 = rreshape [4] v4 ; v6 = rreshape [4] v4 ; v7 = rreshape [4] v4 ; v8 = rreshape [4] v4 ; v9 = rfromVector (fromList [rsum (v35 * v5), rsum (v36 * v6), rsum (v37 * v7), rsum (v38 * v8)]) + v39 ; v10 = rreshape [5] v9 ; v11 = rreshape [5] v9 ; v12 = rreshape [5] v9 ; v13 = rreshape [5] v9 ; v14 = rreshape [5] v9 ; x16 = v30 ! [4] ; x17 = v30 ! [3] ; x18 = v30 ! [2] ; x19 = v30 ! [1] ; x20 = v30 ! [0] ; v21 = rreshape [4] v40 * rreshape [4] (rreplicate 5 x20) + rreshape [4] v41 * rreshape [4] (rreplicate 5 x19) + rreshape [4] v42 * rreshape [4] (rreplicate 5 x18) + rreshape [4] v43 * rreshape [4] (rreplicate 5 x17) + rreshape [4] v44 * rreshape [4] (rreplicate 5 x16) ; x22 = v21 ! [3] ; x23 = v21 ! [2] ; x24 = v21 ! [1] ; x25 = v21 ! [0] ; v26 = rreshape [3] v35 * rreshape [3] (rreplicate 4 x25) + rreshape [3] v36 * rreshape [3] (rreplicate 4 x24) + rreshape [3] v37 * rreshape [3] (rreplicate 4 x23) + rreshape [3] v38 * rreshape [3] (rreplicate 4 x22) ; x27 = v26 ! [2] ; x28 = v26 ! [1] ; x29 = v26 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x29), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x28), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x27), v26, v5 * rreshape [4] (rreplicate 4 x25), v6 * rreshape [4] (rreplicate 4 x24), v7 * rreshape [4] (rreplicate 4 x23), v8 * rreshape [4] (rreplicate 4 x22), v21, v10 * rreshape [5] (rreplicate 5 x20), v11 * rreshape [5] (rreplicate 5 x19), v12 * rreshape [5] (rreplicate 5 x18), v13 * rreshape [5] (rreplicate 5 x17), v14 * rreshape [5] (rreplicate 5 x16), v30]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 -> let v4 = rfromVector (fromList [rsum (v47 * rreplicate 3 7.0), rsum (v48 * rreplicate 3 7.0), rsum (v49 * rreplicate 3 7.0)]) + v50 ; v5 = rreshape [4] v4 ; v6 = rreshape [4] v4 ; v7 = rreshape [4] v4 ; v8 = rreshape [4] v4 ; v9 = rfromVector (fromList [rsum (v51 * v5), rsum (v52 * v6), rsum (v53 * v7), rsum (v54 * v8)]) + v55 ; v10 = rreshape [5] v9 ; v11 = rreshape [5] v9 ; v12 = rreshape [5] v9 ; v13 = rreshape [5] v9 ; v14 = rreshape [5] v9 in [rfromVector (fromList [rsum (v56 * v10), rsum (v57 * v11), rsum (v58 * v12), rsum (v59 * v13), rsum (v60 * v14)]) + v61]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 -> let v4 = rfromVector (fromList [rsum (v72 * rreplicate 3 7.0), rsum (v73 * rreplicate 3 7.0), rsum (v74 * rreplicate 3 7.0)]) + v75 ; v5 = rreshape [4] v4 ; v6 = rreshape [4] v4 ; v7 = rreshape [4] v4 ; v8 = rreshape [4] v4 ; v9 = rfromVector (fromList [rsum (v76 * v5), rsum (v77 * v6), rsum (v78 * v7), rsum (v79 * v8)]) + v80 ; x16 = v71 ! [4] ; x17 = v71 ! [3] ; x18 = v71 ! [2] ; x19 = v71 ! [1] ; x20 = v71 ! [0] ; v21 = rreshape [4] v81 * rreplicate 4 x20 + rreshape [4] v82 * rreplicate 4 x19 + rreshape [4] v83 * rreplicate 4 x18 + rreshape [4] v84 * rreplicate 4 x17 + rreshape [4] v85 * rreplicate 4 x16 ; x22 = v21 ! [3] ; x23 = v21 ! [2] ; x24 = v21 ! [1] ; x25 = v21 ! [0] ; v26 = rreshape [3] v76 * rreplicate 3 x25 + rreshape [3] v77 * rreplicate 3 x24 + rreshape [3] v78 * rreplicate 3 x23 + rreshape [3] v79 * rreplicate 3 x22 in [rreplicate 3 7.0 * rreplicate 3 (v26 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v26 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v26 ! [2]), v26, v5 * rreplicate 4 x25, v6 * rreplicate 4 x24, v7 * rreplicate 4 x23, v8 * rreplicate 4 x22, v21, rreshape [5] v9 * rreplicate 5 x20, rreshape [5] v9 * rreplicate 5 x19, rreshape [5] v9 * rreplicate 5 x18, rreshape [5] v9 * rreplicate 5 x17, rreshape [5] v9 * rreplicate 5 x16, v71]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 -> let v4 = rfromVector (fromList [rsum (v88 * rreplicate 3 7.0), rsum (v89 * rreplicate 3 7.0), rsum (v90 * rreplicate 3 7.0)]) + v91 ; v9 = rfromVector (fromList [rsum (v92 * rreshape [4] v4), rsum (v93 * rreshape [4] v4), rsum (v94 * rreshape [4] v4), rsum (v95 * rreshape [4] v4)]) + v96 in [rfromVector (fromList [rsum (v97 * rreshape [5] v9), rsum (v98 * rreshape [5] v9), rsum (v99 * rreshape [5] v9), rsum (v100 * rreshape [5] v9), rsum (v101 * rreshape [5] v9)]) + v102]"

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
    @?= "\\v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 -> let v9 = rfromVector (fromList [rsum (v50 * rreplicate 3 7.0), rsum (v51 * rreplicate 3 7.0), rsum (v52 * rreplicate 3 7.0)]) + v53 ; v10 = exp (negate v9) ; v11 = rreplicate 3 1.0 + v10 ; v12 = recip v11 ; v13 = rreplicate 3 1.0 - v12 ; v14 = v12 * v13 ; v15 = rreshape [4] v12 ; v16 = rreshape [4] v12 ; v17 = rreshape [4] v12 ; v18 = rreshape [4] v12 ; v19 = rfromVector (fromList [rsum (v54 * v15), rsum (v55 * v16), rsum (v56 * v17), rsum (v57 * v18)]) + v58 ; v20 = exp (negate v19) ; v21 = rreplicate 4 1.0 + v20 ; v22 = recip v21 ; v23 = rreplicate 4 1.0 - v22 ; v24 = v22 * v23 ; v25 = rreshape [5] v22 ; v26 = rreshape [5] v22 ; v27 = rreshape [5] v22 ; v28 = rreshape [5] v22 ; v29 = rreshape [5] v22 ; v30 = exp (rfromVector (fromList [rsum (v59 * v25), rsum (v60 * v26), rsum (v61 * v27), rsum (v62 * v28), rsum (v63 * v29)]) + v64) ; x31 = rsum v30 ; v32 = rreplicate 5 (recip x31) ; v34 = v30 * (rreplicate 5 (negate (recip (x31 * x31)) * rsum (v30 * v49)) + v32 * v49) ; x35 = v34 ! [4] ; x36 = v34 ! [3] ; x37 = v34 ! [2] ; x38 = v34 ! [1] ; x39 = v34 ! [0] ; v40 = v24 * (rreshape [4] v59 * rreshape [4] (rreplicate 5 x39) + rreshape [4] v60 * rreshape [4] (rreplicate 5 x38) + rreshape [4] v61 * rreshape [4] (rreplicate 5 x37) + rreshape [4] v62 * rreshape [4] (rreplicate 5 x36) + rreshape [4] v63 * rreshape [4] (rreplicate 5 x35)) ; x41 = v40 ! [3] ; x42 = v40 ! [2] ; x43 = v40 ! [1] ; x44 = v40 ! [0] ; v45 = v14 * (rreshape [3] v54 * rreshape [3] (rreplicate 4 x44) + rreshape [3] v55 * rreshape [3] (rreplicate 4 x43) + rreshape [3] v56 * rreshape [3] (rreplicate 4 x42) + rreshape [3] v57 * rreshape [3] (rreplicate 4 x41)) ; x46 = v45 ! [2] ; x47 = v45 ! [1] ; x48 = v45 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x48), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x47), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x46), v45, v15 * rreshape [4] (rreplicate 4 x44), v16 * rreshape [4] (rreplicate 4 x43), v17 * rreshape [4] (rreplicate 4 x42), v18 * rreshape [4] (rreplicate 4 x41), v40, v25 * rreshape [5] (rreplicate 5 x39), v26 * rreshape [5] (rreplicate 5 x38), v27 * rreshape [5] (rreplicate 5 x37), v28 * rreshape [5] (rreplicate 5 x36), v29 * rreshape [5] (rreplicate 5 x35), v34]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 -> let v9 = rfromVector (fromList [rsum (v66 * rreplicate 3 7.0), rsum (v67 * rreplicate 3 7.0), rsum (v68 * rreplicate 3 7.0)]) + v69 ; v10 = exp (negate v9) ; v11 = rreplicate 3 1.0 + v10 ; v12 = recip v11 ; v15 = rreshape [4] v12 ; v16 = rreshape [4] v12 ; v17 = rreshape [4] v12 ; v18 = rreshape [4] v12 ; v19 = rfromVector (fromList [rsum (v70 * v15), rsum (v71 * v16), rsum (v72 * v17), rsum (v73 * v18)]) + v74 ; v20 = exp (negate v19) ; v21 = rreplicate 4 1.0 + v20 ; v22 = recip v21 ; v25 = rreshape [5] v22 ; v26 = rreshape [5] v22 ; v27 = rreshape [5] v22 ; v28 = rreshape [5] v22 ; v29 = rreshape [5] v22 ; v30 = exp (rfromVector (fromList [rsum (v75 * v25), rsum (v76 * v26), rsum (v77 * v27), rsum (v78 * v28), rsum (v79 * v29)]) + v80) ; x31 = rsum v30 ; v32 = rreplicate 5 (recip x31) in [v32 * v30]"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 -> let v12 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v91 * rreplicate 3 7.0), rsum (v92 * rreplicate 3 7.0), rsum (v93 * rreplicate 3 7.0)]) + v94))) ; v15 = rreshape [4] v12 ; v16 = rreshape [4] v12 ; v17 = rreshape [4] v12 ; v18 = rreshape [4] v12 ; v22 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v95 * v15), rsum (v96 * v16), rsum (v97 * v17), rsum (v98 * v18)]) + v99))) ; v25 = rreshape [5] v22 ; v26 = rreshape [5] v22 ; v27 = rreshape [5] v22 ; v28 = rreshape [5] v22 ; v29 = rreshape [5] v22 ; v30 = exp (rfromVector (fromList [rsum (v100 * v25), rsum (v101 * v26), rsum (v102 * v27), rsum (v103 * v28), rsum (v104 * v29)]) + v105) ; x31 = rsum v30 ; v34 = v30 * (rreplicate 5 (negate (recip (x31 * x31)) * rsum (v30 * v90)) + rreplicate 5 (recip x31) * v90) ; x35 = v34 ! [4] ; x36 = v34 ! [3] ; x37 = v34 ! [2] ; x38 = v34 ! [1] ; x39 = v34 ! [0] ; v40 = (v22 * (rreplicate 4 1.0 - v22)) * (rreshape [4] v100 * rreplicate 4 x39 + rreshape [4] v101 * rreplicate 4 x38 + rreshape [4] v102 * rreplicate 4 x37 + rreshape [4] v103 * rreplicate 4 x36 + rreshape [4] v104 * rreplicate 4 x35) ; x41 = v40 ! [3] ; x42 = v40 ! [2] ; x43 = v40 ! [1] ; x44 = v40 ! [0] ; v45 = (v12 * (rreplicate 3 1.0 - v12)) * (rreshape [3] v95 * rreplicate 3 x44 + rreshape [3] v96 * rreplicate 3 x43 + rreshape [3] v97 * rreplicate 3 x42 + rreshape [3] v98 * rreplicate 3 x41) in [rreplicate 3 7.0 * rreplicate 3 (v45 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v45 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v45 ! [2]), v45, v15 * rreplicate 4 x44, v16 * rreplicate 4 x43, v17 * rreplicate 4 x42, v18 * rreplicate 4 x41, v40, v25 * rreplicate 5 x39, v26 * rreplicate 5 x38, v27 * rreplicate 5 x37, v28 * rreplicate 5 x36, v29 * rreplicate 5 x35, v34]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 -> let v12 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v107 * rreplicate 3 7.0), rsum (v108 * rreplicate 3 7.0), rsum (v109 * rreplicate 3 7.0)]) + v110))) ; v22 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v111 * rreshape [4] v12), rsum (v112 * rreshape [4] v12), rsum (v113 * rreshape [4] v12), rsum (v114 * rreshape [4] v12)]) + v115))) ; v30 = exp (rfromVector (fromList [rsum (v116 * rreshape [5] v22), rsum (v117 * rreshape [5] v22), rsum (v118 * rreshape [5] v22), rsum (v119 * rreshape [5] v22), rsum (v120 * rreshape [5] v22)]) + v121) in [rreplicate 5 (recip (rsum v30)) * v30]"

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
    @?= "\\v12 m13 v14 m15 v16 m17 v18 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m13) + v14))) ; m6 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] m15)) + v16)) ; v8 = rsum (m17 * rtranspose [1,0] (rreplicate 5 v12)) ; m9 = rreplicate 4 (rcast v8) ; v10 = rcast (rsum (m15 * rtranspose [1,0] m9)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v10), v10, rtranspose [1,0] (m5 * m9), v8, rtranspose [1,0] m6 * rtranspose [1,0] (rreplicate 5 v12), v12]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m20 v21 m22 v23 m24 v25 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m20) + v21))) ; m6 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] m22)) + v23)) in [rsum (m6 * rtranspose [1,0] m24) + v25]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v26 m27 v28 m29 v30 m31 v32 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m27) + v28))) ; v8 = rsum (m31 * rtranspose [1,0] (rreplicate 5 v26)) ; m9 = rreplicate 4 (rcast v8) ; v10 = rcast (rsum (m29 * rtranspose [1,0] m9)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v10), v10, rtranspose [1,0] (m5 * m9), v8, rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] m29)) + v30) * rtranspose [1,0] (rreplicate 5 v26), v26]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m34 v35 m36 v37 m38 v39 -> [rsum (rtranspose [1,0] (rreplicate 2 (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m34) + v35))) * rtranspose [1,0] m36)) + v37)) * rtranspose [1,0] m38) + v39]"

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
    @?= "\\v34 m35 v36 m37 v38 m39 v40 -> let v10 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m35) + v36 ; v11 = exp (negate v10) ; v12 = rreplicate 4 1.0 + v11 ; v13 = recip v12 ; v14 = rreplicate 4 1.0 - v13 ; v15 = v13 * v14 ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v17 = rcast (rsum (m16 * rtranspose [1,0] m37)) + v38 ; v18 = exp (negate v17) ; v19 = rreplicate 5 1.0 + v18 ; v20 = recip v19 ; v21 = rreplicate 5 1.0 - v20 ; v22 = v20 * v21 ; v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 v20) * rtranspose [1,0] m39) + v40) ; x25 = rsum v24 ; v26 = rreplicate 2 (recip x25) ; v28 = v24 * (rreplicate 2 (negate (recip (x25 * x25)) * rsum (v24 * v34)) + v26 * v34) ; v30 = v22 * rsum (m39 * rtranspose [1,0] (rreplicate 5 v28)) ; m31 = rreplicate 4 (rcast v30) ; v32 = v15 * rcast (rsum (m37 * rtranspose [1,0] m31)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v32), v32, rtranspose [1,0] (m16 * m31), v30, rreplicate 2 v20 * rtranspose [1,0] (rreplicate 5 v28), v28]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\m42 v43 m44 v45 m46 v47 -> let v10 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m42) + v43 ; v11 = exp (negate v10) ; v12 = rreplicate 4 1.0 + v11 ; v13 = recip v12 ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v17 = rcast (rsum (m16 * rtranspose [1,0] m44)) + v45 ; v18 = exp (negate v17) ; v19 = rreplicate 5 1.0 + v18 ; v20 = recip v19 ; v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 v20) * rtranspose [1,0] m46) + v47) ; x25 = rsum v24 ; v26 = rreplicate 2 (recip x25) in [v26 * v24]"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v48 m49 v50 m51 v52 m53 v54 -> let v13 = recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m49) + v50))) ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v20 = recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (m16 * rtranspose [1,0] m51)) + v52))) ; v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 v20) * rtranspose [1,0] m53) + v54) ; x25 = rsum v24 ; v28 = v24 * (rreplicate 2 (negate (recip (x25 * x25)) * rsum (v24 * v48)) + rreplicate 2 (recip x25) * v48) ; v30 = (v20 * (rreplicate 5 1.0 - v20)) * rsum (m53 * rtranspose [1,0] (rreplicate 5 v28)) ; m31 = rreplicate 4 (rcast v30) ; v32 = (v13 * (rreplicate 4 1.0 - v13)) * rcast (rsum (m51 * rtranspose [1,0] m31)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v32), v32, rtranspose [1,0] (m16 * m31), v30, rreplicate 2 v20 * rtranspose [1,0] (rreplicate 5 v28), v28]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\m56 v57 m58 v59 m60 v61 -> let v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 (recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m56) + v57)))))) * rtranspose [1,0] m58)) + v59))))) * rtranspose [1,0] m60) + v61) in [rreplicate 2 (recip (rsum v24)) * v24]"
