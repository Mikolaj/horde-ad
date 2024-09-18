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
       (_, _, var, hVector2)
         <- funToAstRevIO $ FTKUntyped $ voidFromHVector hVectorInit
       (varGlyph, _, astGlyph) <-
         funToAstIO (FTKR $ singletonShape sizeMnistGlyphInt) id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ singletonShape sizeMnistLabelInt) id
       let ast :: AstRanked FullSpan r 0
           ast = MnistFcnnRanked1.afcnnMnistLoss1TensorData
                   widthHidden widthHidden2 (AstRanked astGlyph, AstRanked astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (dunHVector $ unHVectorPseudoTensor (rankedY (stensorKind @TKUntyped) hVector2)))
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector ORArray -> (Int, [MnistData r]) -> IO (HVector ORArray)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = extendEnv var (HVectorPseudoTensor varInputs) emptyEnv
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
                      (0.9108 :: Float)
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
           g :: InterpretationTarget (AstRanked FullSpan) TKUntyped
             -> InterpretationTarget (AstRanked FullSpan) TKUntyped
           g !hv = HVectorPseudoTensor
                   $ toHVectorOf $ f
                   $ parseHVector (fromValue (valsInit, dataInit)) $ dunHVector $ unHVectorPseudoTensor hv
           (artRaw, _) = revProduceArtifact False g emptyEnv
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
                   HVectorPseudoTensor
                   $ V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   unHVectorPseudoTensor
                   $ fst $ revEvalArtifact art parametersAndInput Nothing
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
       (_, _, var, hVector2)
         <- funToAstRevIO $ FTKUntyped $ voidFromHVector hVectorInit
       (varGlyph, _, astGlyph) <-
         funToAstIO (FTKR $ singletonShape sizeMnistGlyphInt) id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ singletonShape sizeMnistLabelInt) id
       let ast :: AstRanked FullSpan r 0
           ast = MnistFcnnRanked2.afcnnMnistLoss2TensorData
                   (AstRanked astGlyph, AstRanked astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (dunHVector $ unHVectorPseudoTensor (rankedY (stensorKind @TKUntyped) hVector2)))
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector ORArray -> (Int, [MnistData r]) -> IO (HVector ORArray)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = extendEnv var (HVectorPseudoTensor varInputs) emptyEnv
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
                       (0.7945891783567134 :: Double)
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
                   HVectorPseudoTensor
                   $ V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   unHVectorPseudoTensor
                   $ fst $ revEvalArtifact art parametersAndInput Nothing
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
                     (7 :: AstTensor AstMethodLet FullSpan (TKR Double 0))
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters (AstRanked FullSpan)
                                                         Double
              -> AstRanked FullSpan Double 1
      afcnn2T = MnistFcnnRanked1.afcnnMnist1 id id 3 4 $ AstRanked blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVTOPP
  printArtifactPretty renames artifactRev
    @?= "\\v48 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 -> let v26 = rfromVector (fromList [rsum (v63 * rreplicate 3 7.0), rsum (v64 * rreplicate 3 7.0), rsum (v65 * rreplicate 3 7.0)]) + v66 ; v36 = rfromVector (fromList [rsum (v67 * rreshape [4] v26), rsum (v68 * rreshape [4] v26), rsum (v69 * rreshape [4] v26), rsum (v70 * rreshape [4] v26)]) + v71 ; x49 = v48 ! [4] ; x50 = v48 ! [3] ; x51 = v48 ! [2] ; x52 = v48 ! [1] ; x53 = v48 ! [0] ; v54 = v72 * rreshape [5] (rreplicate 5 x53) + v73 * rreshape [5] (rreplicate 5 x52) + v74 * rreshape [5] (rreplicate 5 x51) + v75 * rreshape [5] (rreplicate 5 x50) + v76 * rreshape [5] (rreplicate 5 x49) ; x55 = v54 ! [3] ; x56 = v54 ! [2] ; x57 = v54 ! [1] ; x58 = v54 ! [0] ; v59 = v67 * rreshape [4] (rreplicate 4 x58) + v68 * rreshape [4] (rreplicate 4 x57) + v69 * rreshape [4] (rreplicate 4 x56) + v70 * rreshape [4] (rreplicate 4 x55) ; x60 = v59 ! [2] ; x61 = v59 ! [1] ; x62 = v59 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x62), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x61), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x60), v59, v26 * rreshape [3] (rreplicate 3 x58), v26 * rreshape [3] (rreplicate 3 x57), v26 * rreshape [3] (rreplicate 3 x56), v26 * rreshape [3] (rreplicate 3 x55), v54, v36 * rreshape [4] (rreplicate 4 x53), v36 * rreshape [4] (rreplicate 4 x52), v36 * rreshape [4] (rreplicate 4 x51), v36 * rreshape [4] (rreplicate 4 x50), v36 * rreshape [4] (rreplicate 4 x49), v48]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v513 v514 v515 v516 v517 v518 v519 v520 v521 v522 v523 v524 v525 v526 v527 -> let v26 = rfromVector (fromList [rsum (v513 * rreplicate 3 7.0), rsum (v514 * rreplicate 3 7.0), rsum (v515 * rreplicate 3 7.0)]) + v516 ; v36 = rfromVector (fromList [rsum (v517 * rreshape [4] v26), rsum (v518 * rreshape [4] v26), rsum (v519 * rreshape [4] v26), rsum (v520 * rreshape [4] v26)]) + v521 in rfromVector (fromList [rsum (v522 * rreshape [5] v36), rsum (v523 * rreshape [5] v36), rsum (v524 * rreshape [5] v36), rsum (v525 * rreshape [5] v36), rsum (v526 * rreshape [5] v36)]) + v527"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v48 v1398 v1399 v1400 v1401 v1402 v1403 v1404 v1405 v1406 v1407 v1408 v1409 v1410 v1411 v1412 -> let v26 = rfromVector (fromList [rsum (v1398 * rreplicate 3 7.0), rsum (v1399 * rreplicate 3 7.0), rsum (v1400 * rreplicate 3 7.0)]) + v1401 ; v36 = rfromVector (fromList [rsum (v1402 * v26), rsum (v1403 * v26), rsum (v1404 * v26), rsum (v1405 * v26)]) + v1406 ; x49 = v48 ! [4] ; x50 = v48 ! [3] ; x51 = v48 ! [2] ; x52 = v48 ! [1] ; x53 = v48 ! [0] ; v54 = v1407 * rreplicate 5 x53 + v1408 * rreplicate 5 x52 + v1409 * rreplicate 5 x51 + v1410 * rreplicate 5 x50 + v1411 * rreplicate 5 x49 ; x55 = v54 ! [3] ; x56 = v54 ! [2] ; x57 = v54 ! [1] ; x58 = v54 ! [0] ; v59 = v1402 * rreplicate 4 x58 + v1403 * rreplicate 4 x57 + v1404 * rreplicate 4 x56 + v1405 * rreplicate 4 x55 in [rreplicate 3 7.0 * rreplicate 3 (v59 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v59 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v59 ! [2]), v59, v26 * rreplicate 3 x58, v26 * rreplicate 3 x57, v26 * rreplicate 3 x56, v26 * rreplicate 3 x55, v54, v36 * rreplicate 4 x53, v36 * rreplicate 4 x52, v36 * rreplicate 4 x51, v36 * rreplicate 4 x50, v36 * rreplicate 4 x49, v48]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v1848 v1849 v1850 v1851 v1852 v1853 v1854 v1855 v1856 v1857 v1858 v1859 v1860 v1861 v1862 -> let v26 = rfromVector (fromList [rsum (v1848 * rreplicate 3 7.0), rsum (v1849 * rreplicate 3 7.0), rsum (v1850 * rreplicate 3 7.0)]) + v1851 ; v36 = rfromVector (fromList [rsum (v1852 * v26), rsum (v1853 * v26), rsum (v1854 * v26), rsum (v1855 * v26)]) + v1856 in rfromVector (fromList [rsum (v1857 * v36), rsum (v1858 * v36), rsum (v1859 * v36), rsum (v1860 * v36), rsum (v1861 * v36)]) + v1862"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @SizeMnistGlyph)
                     (7 :: AstTensor AstMethodLet FullSpan (TKR Double 0))
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                         (AstRanked FullSpan) Double
                    -> AstRanked FullSpan Double 1
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMax1 3 4 $ AstRanked blackGlyph
      (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVTOPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v66 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 -> let v31 = rfromVector (fromList [rsum (v82 * rreplicate 3 7.0), rsum (v83 * rreplicate 3 7.0), rsum (v84 * rreplicate 3 7.0)]) + v85 ; v32 = exp (negate v31) ; v33 = rreplicate 3 1.0 + v32 ; v34 = recip v33 ; v35 = rreplicate 3 1.0 - v34 ; v36 = v34 * v35 ; v46 = rfromVector (fromList [rsum (v86 * rreshape [4] v34), rsum (v87 * rreshape [4] v34), rsum (v88 * rreshape [4] v34), rsum (v89 * rreshape [4] v34)]) + v90 ; v47 = exp (negate v46) ; v48 = rreplicate 4 1.0 + v47 ; v49 = recip v48 ; v50 = rreplicate 4 1.0 - v49 ; v51 = v49 * v50 ; v63 = exp (rfromVector (fromList [rsum (v91 * rreshape [5] v49), rsum (v92 * rreshape [5] v49), rsum (v93 * rreshape [5] v49), rsum (v94 * rreshape [5] v49), rsum (v95 * rreshape [5] v49)]) + v96) ; x64 = rsum v63 ; v65 = rreplicate 5 (recip x64) ; v67 = v63 * (rreplicate 5 (negate (recip (x64 * x64)) * rsum (v63 * v66)) + v65 * v66) ; x68 = v67 ! [4] ; x69 = v67 ! [3] ; x70 = v67 ! [2] ; x71 = v67 ! [1] ; x72 = v67 ! [0] ; v73 = v51 * (v91 * rreshape [5] (rreplicate 5 x72) + v92 * rreshape [5] (rreplicate 5 x71) + v93 * rreshape [5] (rreplicate 5 x70) + v94 * rreshape [5] (rreplicate 5 x69) + v95 * rreshape [5] (rreplicate 5 x68)) ; x74 = v73 ! [3] ; x75 = v73 ! [2] ; x76 = v73 ! [1] ; x77 = v73 ! [0] ; v78 = v36 * (v86 * rreshape [4] (rreplicate 4 x77) + v87 * rreshape [4] (rreplicate 4 x76) + v88 * rreshape [4] (rreplicate 4 x75) + v89 * rreshape [4] (rreplicate 4 x74)) ; x79 = v78 ! [2] ; x80 = v78 ! [1] ; x81 = v78 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x81), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x80), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x79), v78, v34 * rreshape [3] (rreplicate 3 x77), v34 * rreshape [3] (rreplicate 3 x76), v34 * rreshape [3] (rreplicate 3 x75), v34 * rreshape [3] (rreplicate 3 x74), v73, v49 * rreshape [4] (rreplicate 4 x72), v49 * rreshape [4] (rreplicate 4 x71), v49 * rreshape [4] (rreplicate 4 x70), v49 * rreshape [4] (rreplicate 4 x69), v49 * rreshape [4] (rreplicate 4 x68), v67]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\v547 v548 v549 v550 v551 v552 v553 v554 v555 v556 v557 v558 v559 v560 v561 -> let v31 = rfromVector (fromList [rsum (v547 * rreplicate 3 7.0), rsum (v548 * rreplicate 3 7.0), rsum (v549 * rreplicate 3 7.0)]) + v550 ; v32 = exp (negate v31) ; v33 = rreplicate 3 1.0 + v32 ; v34 = recip v33 ; v46 = rfromVector (fromList [rsum (v551 * rreshape [4] v34), rsum (v552 * rreshape [4] v34), rsum (v553 * rreshape [4] v34), rsum (v554 * rreshape [4] v34)]) + v555 ; v47 = exp (negate v46) ; v48 = rreplicate 4 1.0 + v47 ; v49 = recip v48 ; v63 = exp (rfromVector (fromList [rsum (v556 * rreshape [5] v49), rsum (v557 * rreshape [5] v49), rsum (v558 * rreshape [5] v49), rsum (v559 * rreshape [5] v49), rsum (v560 * rreshape [5] v49)]) + v561) ; x64 = rsum v63 ; v65 = rreplicate 5 (recip x64) in v65 * v63"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v66 v1462 v1463 v1464 v1465 v1466 v1467 v1468 v1469 v1470 v1471 v1472 v1473 v1474 v1475 v1476 -> let v34 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v1462 * rreplicate 3 7.0), rsum (v1463 * rreplicate 3 7.0), rsum (v1464 * rreplicate 3 7.0)]) + v1465))) ; v49 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v1466 * v34), rsum (v1467 * v34), rsum (v1468 * v34), rsum (v1469 * v34)]) + v1470))) ; v63 = exp (rfromVector (fromList [rsum (v1471 * v49), rsum (v1472 * v49), rsum (v1473 * v49), rsum (v1474 * v49), rsum (v1475 * v49)]) + v1476) ; x64 = rsum v63 ; v67 = v63 * (rreplicate 5 (negate (recip (x64 * x64)) * rsum (v63 * v66)) + rreplicate 5 (recip x64) * v66) ; x68 = v67 ! [4] ; x69 = v67 ! [3] ; x70 = v67 ! [2] ; x71 = v67 ! [1] ; x72 = v67 ! [0] ; v73 = (v49 * (rreplicate 4 1.0 - v49)) * (v1471 * rreplicate 5 x72 + v1472 * rreplicate 5 x71 + v1473 * rreplicate 5 x70 + v1474 * rreplicate 5 x69 + v1475 * rreplicate 5 x68) ; x74 = v73 ! [3] ; x75 = v73 ! [2] ; x76 = v73 ! [1] ; x77 = v73 ! [0] ; v78 = (v34 * (rreplicate 3 1.0 - v34)) * (v1466 * rreplicate 4 x77 + v1467 * rreplicate 4 x76 + v1468 * rreplicate 4 x75 + v1469 * rreplicate 4 x74) in [rreplicate 3 7.0 * rreplicate 3 (v78 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v78 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v78 ! [2]), v78, v34 * rreplicate 3 x77, v34 * rreplicate 3 x76, v34 * rreplicate 3 x75, v34 * rreplicate 3 x74, v73, v49 * rreplicate 4 x72, v49 * rreplicate 4 x71, v49 * rreplicate 4 x70, v49 * rreplicate 4 x69, v49 * rreplicate 4 x68, v67]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v1927 v1928 v1929 v1930 v1931 v1932 v1933 v1934 v1935 v1936 v1937 v1938 v1939 v1940 v1941 -> let v34 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v1927 * rreplicate 3 7.0), rsum (v1928 * rreplicate 3 7.0), rsum (v1929 * rreplicate 3 7.0)]) + v1930))) ; v49 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v1931 * v34), rsum (v1932 * v34), rsum (v1933 * v34), rsum (v1934 * v34)]) + v1935))) ; v63 = exp (rfromVector (fromList [rsum (v1936 * v49), rsum (v1937 * v49), rsum (v1938 * v49), rsum (v1939 * v49), rsum (v1940 * v49)]) + v1941) in rreplicate 5 (recip (rsum v63)) * v63"

valsInitVT2OPP :: MnistFcnnRanked2.ADFcnnMnist2Parameters ORArray Double
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
                     (7 :: AstTensor AstMethodLet FullSpan (TKR Double 0))
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                   (AstRanked FullSpan) Double
              -> AstRanked FullSpan Double 1
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id $ AstRanked blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVT2OPP
  printArtifactPretty renames artifactRev
    @?= "\\v22 m27 v28 m29 v30 m31 v32 -> let m15 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m27) + v28))) ; m19 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m15 * rtranspose [1,0] m29)) + v30)) ; v23 = rsum (m31 * rtranspose [1,0] (rreplicate 5 v22)) ; m24 = rreplicate 4 (rcast v23) ; v25 = rcast (rsum (m29 * rtranspose [1,0] m24)) ; m26 = rreplicate 3 v25 in [rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m26), v25, rtranspose [1,0] (m15 * m24), v23, rtranspose [1,0] (m19 * rreplicate 5 v22), v22]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m99 v100 m101 v102 m103 v104 -> let m15 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m99) + v100))) ; m19 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m15 * rtranspose [1,0] m101)) + v102)) in rsum (m19 * rtranspose [1,0] m103) + v104"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v22 m237 v238 m239 v240 m241 v242 -> let m15 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m237) + v238))) ; v23 = rsum (m241 * rtranspose [1,0] (rreplicate 5 v22)) ; m24 = rreplicate 4 (rcast v23) ; v25 = rcast (rsum (m239 * rtranspose [1,0] m24)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v25), v25, rtranspose [1,0] (m15 * m24), v23, rreplicate 2 (rcast (rsum (m15 * rtranspose [1,0] m239)) + v240) * rtranspose [1,0] (rreplicate 5 v22), v22]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m309 v310 m311 v312 m313 v314 -> rsum (rtranspose [1,0] (rreplicate 2 (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m309) + v310))) * rtranspose [1,0] m311)) + v312)) * rtranspose [1,0] m313) + v314"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3)
                     (7 :: AstTensor AstMethodLet FullSpan (TKR Float 0))
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
                     (7 :: AstTensor AstMethodLet FullSpan (TKR Double 0))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstRanked FullSpan) Double
                    -> AstRanked FullSpan Double 1
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 $ AstRanked blackGlyph
  let (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVT2OPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v42 m49 v50 m51 v52 m53 v54 -> let v19 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m49) + v50 ; v20 = exp (negate v19) ; v21 = rreplicate 4 1.0 + v20 ; v22 = recip v21 ; v23 = rreplicate 4 1.0 - v22 ; v24 = v22 * v23 ; m26 = rtranspose [1,0] (rreplicate 5 (rcast v22)) ; v29 = rcast (rsum (m26 * rtranspose [1,0] m51)) + v52 ; v30 = exp (negate v29) ; v31 = rreplicate 5 1.0 + v30 ; v32 = recip v31 ; v33 = rreplicate 5 1.0 - v32 ; v34 = v32 * v33 ; v39 = exp (rsum (rtranspose [1,0] (rreplicate 2 v32) * rtranspose [1,0] m53) + v54) ; x40 = rsum v39 ; v41 = rreplicate 2 (recip x40) ; v43 = v39 * (rreplicate 2 (negate (recip (x40 * x40)) * rsum (v39 * v42)) + v41 * v42) ; v45 = v34 * rsum (m53 * rtranspose [1,0] (rreplicate 5 v43)) ; m46 = rreplicate 4 (rcast v45) ; v47 = v24 * rcast (rsum (m51 * rtranspose [1,0] m46)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v47), v47, rtranspose [1,0] (m26 * m46), v45, rreplicate 2 v32 * rtranspose [1,0] (rreplicate 5 v43), v43]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\m127 v128 m129 v130 m131 v132 -> let v19 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m127) + v128 ; v20 = exp (negate v19) ; v21 = rreplicate 4 1.0 + v20 ; v22 = recip v21 ; m26 = rtranspose [1,0] (rreplicate 5 (rcast v22)) ; v29 = rcast (rsum (m26 * rtranspose [1,0] m129)) + v130 ; v30 = exp (negate v29) ; v31 = rreplicate 5 1.0 + v30 ; v32 = recip v31 ; v39 = exp (rsum (rtranspose [1,0] (rreplicate 2 v32) * rtranspose [1,0] m131) + v132) ; x40 = rsum v39 ; v41 = rreplicate 2 (recip x40) in v41 * v39"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v42 m277 v278 m279 v280 m281 v282 -> let v22 = recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m277) + v278))) ; m26 = rtranspose [1,0] (rreplicate 5 (rcast v22)) ; v32 = recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (m26 * rtranspose [1,0] m279)) + v280))) ; v39 = exp (rsum (rtranspose [1,0] (rreplicate 2 v32) * rtranspose [1,0] m281) + v282) ; x40 = rsum v39 ; v43 = v39 * (rreplicate 2 (negate (recip (x40 * x40)) * rsum (v39 * v42)) + rreplicate 2 (recip x40) * v42) ; v45 = (v32 * (rreplicate 5 1.0 - v32)) * rsum (m281 * rtranspose [1,0] (rreplicate 5 v43)) ; m46 = rreplicate 4 (rcast v45) ; v47 = (v22 * (rreplicate 4 1.0 - v22)) * rcast (rsum (m279 * rtranspose [1,0] m46)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v47), v47, rtranspose [1,0] (m26 * m46), v45, rreplicate 2 v32 * rtranspose [1,0] (rreplicate 5 v43), v43]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\m355 v356 m357 v358 m359 v360 -> let v39 = exp (rsum (rtranspose [1,0] (rreplicate 2 (recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m355) + v356)))))) * rtranspose [1,0] m357)) + v358))))) * rtranspose [1,0] m359) + v360) in rreplicate 2 (recip (rsum v39)) * v39"
