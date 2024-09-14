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
    @?= "\\v21 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 -> let v19 = rfromVector (fromList [rsum (v36 * rreplicate 3 7.0), rsum (v37 * rreplicate 3 7.0), rsum (v38 * rreplicate 3 7.0)]) + v39 ; v20 = rfromVector (fromList [rsum (rreshape [4] (v40 * v19)), rsum (rreshape [4] (v41 * v19)), rsum (rreshape [4] (v42 * v19)), rsum (rreshape [4] (v43 * v19))]) + v44 ; x22 = v21 ! [4] ; x23 = v21 ! [3] ; x24 = v21 ! [2] ; x25 = v21 ! [1] ; x26 = v21 ! [0] ; v27 = v45 * rreshape [5] (rreplicate 5 x26) + v46 * rreshape [5] (rreplicate 5 x25) + v47 * rreshape [5] (rreplicate 5 x24) + v48 * rreshape [5] (rreplicate 5 x23) + v49 * rreshape [5] (rreplicate 5 x22) ; x28 = v27 ! [3] ; x29 = v27 ! [2] ; x30 = v27 ! [1] ; x31 = v27 ! [0] ; v32 = v40 * rreshape [4] (rreplicate 4 x31) + v41 * rreshape [4] (rreplicate 4 x30) + v42 * rreshape [4] (rreplicate 4 x29) + v43 * rreshape [4] (rreplicate 4 x28) ; x33 = v32 ! [2] ; x34 = v32 ! [1] ; x35 = v32 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x35), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x34), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x33), v32, v19 * rreshape [3] (rreplicate 3 x31), v19 * rreshape [3] (rreplicate 3 x30), v19 * rreshape [3] (rreplicate 3 x29), v19 * rreshape [3] (rreplicate 3 x28), v27, v20 * rreshape [4] (rreplicate 4 x26), v20 * rreshape [4] (rreplicate 4 x25), v20 * rreshape [4] (rreplicate 4 x24), v20 * rreshape [4] (rreplicate 4 x23), v20 * rreshape [4] (rreplicate 4 x22), v21]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 -> let v19 = rfromVector (fromList [rsum (v51 * rreplicate 3 7.0), rsum (v52 * rreplicate 3 7.0), rsum (v53 * rreplicate 3 7.0)]) + v54 ; v20 = rfromVector (fromList [rsum (rreshape [4] (v55 * v19)), rsum (rreshape [4] (v56 * v19)), rsum (rreshape [4] (v57 * v19)), rsum (rreshape [4] (v58 * v19))]) + v59 in rfromVector (fromList [rsum (rreshape [5] (v60 * v20)), rsum (rreshape [5] (v61 * v20)), rsum (rreshape [5] (v62 * v20)), rsum (rreshape [5] (v63 * v20)), rsum (rreshape [5] (v64 * v20))]) + v65"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v21 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 -> let v19 = rfromVector (fromList [rsum (v66 * rreplicate 3 7.0), rsum (v67 * rreplicate 3 7.0), rsum (v68 * rreplicate 3 7.0)]) + v69 ; v20 = rfromVector (fromList [rsum (v70 * rreshape [4] v19), rsum (v71 * rreshape [4] v19), rsum (v72 * rreshape [4] v19), rsum (v73 * rreshape [4] v19)]) + v74 ; x22 = v21 ! [4] ; x23 = v21 ! [3] ; x24 = v21 ! [2] ; x25 = v21 ! [1] ; x26 = v21 ! [0] ; v27 = v75 * rreplicate 5 x26 + v76 * rreplicate 5 x25 + v77 * rreplicate 5 x24 + v78 * rreplicate 5 x23 + v79 * rreplicate 5 x22 ; x28 = v27 ! [3] ; x29 = v27 ! [2] ; x30 = v27 ! [1] ; x31 = v27 ! [0] ; v32 = v70 * rreplicate 4 x31 + v71 * rreplicate 4 x30 + v72 * rreplicate 4 x29 + v73 * rreplicate 4 x28 in [rreplicate 3 7.0 * rreplicate 3 (v32 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v32 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v32 ! [2]), v32, v19 * rreplicate 3 x31, v19 * rreplicate 3 x30, v19 * rreplicate 3 x29, v19 * rreplicate 3 x28, v27, v20 * rreplicate 4 x26, v20 * rreplicate 4 x25, v20 * rreplicate 4 x24, v20 * rreplicate 4 x23, v20 * rreplicate 4 x22, v21]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 -> let v19 = rfromVector (fromList [rsum (v81 * rreplicate 3 7.0), rsum (v82 * rreplicate 3 7.0), rsum (v83 * rreplicate 3 7.0)]) + v84 ; v20 = rfromVector (fromList [rsum (v85 * rreshape [4] v19), rsum (v86 * rreshape [4] v19), rsum (v87 * rreshape [4] v19), rsum (v88 * rreshape [4] v19)]) + v89 in rfromVector (fromList [rsum (v90 * rreshape [5] v20), rsum (v91 * rreshape [5] v20), rsum (v92 * rreshape [5] v20), rsum (v93 * rreshape [5] v20), rsum (v94 * rreshape [5] v20)]) + v95"

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
    @?= "\\v39 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 -> let v24 = rfromVector (fromList [rsum (v55 * rreplicate 3 7.0), rsum (v56 * rreplicate 3 7.0), rsum (v57 * rreplicate 3 7.0)]) + v58 ; v25 = exp (negate v24) ; v26 = rreplicate 3 1.0 + v25 ; v27 = recip v26 ; v28 = rreplicate 3 1.0 - v27 ; v29 = v27 * v28 ; v30 = rfromVector (fromList [rsum (rreshape [4] (v59 * v27)), rsum (rreshape [4] (v60 * v27)), rsum (rreshape [4] (v61 * v27)), rsum (rreshape [4] (v62 * v27))]) + v63 ; v31 = exp (negate v30) ; v32 = rreplicate 4 1.0 + v31 ; v33 = recip v32 ; v34 = rreplicate 4 1.0 - v33 ; v35 = v33 * v34 ; v36 = exp (rfromVector (fromList [rsum (rreshape [5] (v64 * v33)), rsum (rreshape [5] (v65 * v33)), rsum (rreshape [5] (v66 * v33)), rsum (rreshape [5] (v67 * v33)), rsum (rreshape [5] (v68 * v33))]) + v69) ; x37 = rsum v36 ; v38 = rreplicate 5 (recip x37) ; v40 = v36 * (rreplicate 5 (negate (recip (x37 * x37)) * rsum (v36 * v39)) + v38 * v39) ; x41 = v40 ! [4] ; x42 = v40 ! [3] ; x43 = v40 ! [2] ; x44 = v40 ! [1] ; x45 = v40 ! [0] ; v46 = v35 * (v64 * rreshape [5] (rreplicate 5 x45) + v65 * rreshape [5] (rreplicate 5 x44) + v66 * rreshape [5] (rreplicate 5 x43) + v67 * rreshape [5] (rreplicate 5 x42) + v68 * rreshape [5] (rreplicate 5 x41)) ; x47 = v46 ! [3] ; x48 = v46 ! [2] ; x49 = v46 ! [1] ; x50 = v46 ! [0] ; v51 = v29 * (v59 * rreshape [4] (rreplicate 4 x50) + v60 * rreshape [4] (rreplicate 4 x49) + v61 * rreshape [4] (rreplicate 4 x48) + v62 * rreshape [4] (rreplicate 4 x47)) ; x52 = v51 ! [2] ; x53 = v51 ! [1] ; x54 = v51 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x54), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x53), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x52), v51, v27 * rreshape [3] (rreplicate 3 x50), v27 * rreshape [3] (rreplicate 3 x49), v27 * rreshape [3] (rreplicate 3 x48), v27 * rreshape [3] (rreplicate 3 x47), v46, v33 * rreshape [4] (rreplicate 4 x45), v33 * rreshape [4] (rreplicate 4 x44), v33 * rreshape [4] (rreplicate 4 x43), v33 * rreshape [4] (rreplicate 4 x42), v33 * rreshape [4] (rreplicate 4 x41), v40]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 -> let v24 = rfromVector (fromList [rsum (v70 * rreplicate 3 7.0), rsum (v71 * rreplicate 3 7.0), rsum (v72 * rreplicate 3 7.0)]) + v73 ; v25 = exp (negate v24) ; v26 = rreplicate 3 1.0 + v25 ; v27 = recip v26 ; v30 = rfromVector (fromList [rsum (rreshape [4] (v74 * v27)), rsum (rreshape [4] (v75 * v27)), rsum (rreshape [4] (v76 * v27)), rsum (rreshape [4] (v77 * v27))]) + v78 ; v31 = exp (negate v30) ; v32 = rreplicate 4 1.0 + v31 ; v33 = recip v32 ; v36 = exp (rfromVector (fromList [rsum (rreshape [5] (v79 * v33)), rsum (rreshape [5] (v80 * v33)), rsum (rreshape [5] (v81 * v33)), rsum (rreshape [5] (v82 * v33)), rsum (rreshape [5] (v83 * v33))]) + v84) ; x37 = rsum v36 ; v38 = rreplicate 5 (recip x37) in v38 * v36"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v39 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 -> let v27 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v85 * rreplicate 3 7.0), rsum (v86 * rreplicate 3 7.0), rsum (v87 * rreplicate 3 7.0)]) + v88))) ; v33 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v89 * rreshape [4] v27), rsum (v90 * rreshape [4] v27), rsum (v91 * rreshape [4] v27), rsum (v92 * rreshape [4] v27)]) + v93))) ; v36 = exp (rfromVector (fromList [rsum (v94 * rreshape [5] v33), rsum (v95 * rreshape [5] v33), rsum (v96 * rreshape [5] v33), rsum (v97 * rreshape [5] v33), rsum (v98 * rreshape [5] v33)]) + v99) ; x37 = rsum v36 ; v40 = v36 * (rreplicate 5 (negate (recip (x37 * x37)) * rsum (v36 * v39)) + rreplicate 5 (recip x37) * v39) ; x41 = v40 ! [4] ; x42 = v40 ! [3] ; x43 = v40 ! [2] ; x44 = v40 ! [1] ; x45 = v40 ! [0] ; v46 = (v33 * (rreplicate 4 1.0 - v33)) * (v94 * rreplicate 5 x45 + v95 * rreplicate 5 x44 + v96 * rreplicate 5 x43 + v97 * rreplicate 5 x42 + v98 * rreplicate 5 x41) ; x47 = v46 ! [3] ; x48 = v46 ! [2] ; x49 = v46 ! [1] ; x50 = v46 ! [0] ; v51 = (v27 * (rreplicate 3 1.0 - v27)) * (v89 * rreplicate 4 x50 + v90 * rreplicate 4 x49 + v91 * rreplicate 4 x48 + v92 * rreplicate 4 x47) in [rreplicate 3 7.0 * rreplicate 3 (v51 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v51 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v51 ! [2]), v51, v27 * rreplicate 3 x50, v27 * rreplicate 3 x49, v27 * rreplicate 3 x48, v27 * rreplicate 3 x47, v46, v33 * rreplicate 4 x45, v33 * rreplicate 4 x44, v33 * rreplicate 4 x43, v33 * rreplicate 4 x42, v33 * rreplicate 4 x41, v40]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 -> let v27 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v100 * rreplicate 3 7.0), rsum (v101 * rreplicate 3 7.0), rsum (v102 * rreplicate 3 7.0)]) + v103))) ; v33 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v104 * rreshape [4] v27), rsum (v105 * rreshape [4] v27), rsum (v106 * rreshape [4] v27), rsum (v107 * rreshape [4] v27)]) + v108))) ; v36 = exp (rfromVector (fromList [rsum (v109 * rreshape [5] v33), rsum (v110 * rreshape [5] v33), rsum (v111 * rreshape [5] v33), rsum (v112 * rreshape [5] v33), rsum (v113 * rreshape [5] v33)]) + v114) in rreplicate 5 (recip (rsum v36)) * v36"

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
    @?= "\\v13 m18 v19 m20 v21 m22 v23 -> let m11 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m18) + v19))) ; m12 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m11 * rtranspose [1,0] m20)) + v21)) ; v14 = rsum (m22 * rtranspose [1,0] (rreplicate 5 v13)) ; m15 = rreplicate 4 (rcast v14) ; v16 = rcast (rsum (m20 * rtranspose [1,0] m15)) ; m17 = rreplicate 3 v16 in [rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m17), v16, rtranspose [1,0] (m11 * m15), v14, rtranspose [1,0] (m12 * rreplicate 5 v13), v13]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m24 v25 m26 v27 m28 v29 -> let m11 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m24) + v25))) ; m12 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m11 * rtranspose [1,0] m26)) + v27)) in rsum (m12 * rtranspose [1,0] m28) + v29"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v13 m30 v31 m32 v33 m34 v35 -> let m11 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m30) + v31))) ; v14 = rsum (m34 * rtranspose [1,0] (rreplicate 5 v13)) ; m15 = rreplicate 4 (rcast v14) ; v16 = rcast (rsum (m32 * rtranspose [1,0] m15)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v16), v16, rtranspose [1,0] (m11 * m15), v14, rreplicate 2 (rcast (rsum (m11 * rtranspose [1,0] m32)) + v33) * rtranspose [1,0] (rreplicate 5 v13), v13]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m36 v37 m38 v39 m40 v41 -> rsum (rtranspose [1,0] (rreplicate 2 (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m36) + v37))) * rtranspose [1,0] m38)) + v39)) * rtranspose [1,0] m40) + v41"

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
    @?= "\\v33 m40 v41 m42 v43 m44 v45 -> let v16 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m40) + v41 ; v17 = exp (negate v16) ; v18 = rreplicate 4 1.0 + v17 ; v19 = recip v18 ; v20 = rreplicate 4 1.0 - v19 ; v21 = v19 * v20 ; m22 = rtranspose [1,0] (rreplicate 5 (rcast v19)) ; v23 = rcast (rsum (m22 * rtranspose [1,0] m42)) + v43 ; v24 = exp (negate v23) ; v25 = rreplicate 5 1.0 + v24 ; v26 = recip v25 ; v27 = rreplicate 5 1.0 - v26 ; v28 = v26 * v27 ; v30 = exp (rsum (rtranspose [1,0] (rreplicate 2 v26) * rtranspose [1,0] m44) + v45) ; x31 = rsum v30 ; v32 = rreplicate 2 (recip x31) ; v34 = v30 * (rreplicate 2 (negate (recip (x31 * x31)) * rsum (v30 * v33)) + v32 * v33) ; v36 = v28 * rsum (m44 * rtranspose [1,0] (rreplicate 5 v34)) ; m37 = rreplicate 4 (rcast v36) ; v38 = v21 * rcast (rsum (m42 * rtranspose [1,0] m37)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v38), v38, rtranspose [1,0] (m22 * m37), v36, rreplicate 2 v26 * rtranspose [1,0] (rreplicate 5 v34), v34]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\m46 v47 m48 v49 m50 v51 -> let v16 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m46) + v47 ; v17 = exp (negate v16) ; v18 = rreplicate 4 1.0 + v17 ; v19 = recip v18 ; m22 = rtranspose [1,0] (rreplicate 5 (rcast v19)) ; v23 = rcast (rsum (m22 * rtranspose [1,0] m48)) + v49 ; v24 = exp (negate v23) ; v25 = rreplicate 5 1.0 + v24 ; v26 = recip v25 ; v30 = exp (rsum (rtranspose [1,0] (rreplicate 2 v26) * rtranspose [1,0] m50) + v51) ; x31 = rsum v30 ; v32 = rreplicate 2 (recip x31) in v32 * v30"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v33 m52 v53 m54 v55 m56 v57 -> let v19 = recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m52) + v53))) ; m22 = rtranspose [1,0] (rreplicate 5 (rcast v19)) ; v26 = recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (m22 * rtranspose [1,0] m54)) + v55))) ; v30 = exp (rsum (rtranspose [1,0] (rreplicate 2 v26) * rtranspose [1,0] m56) + v57) ; x31 = rsum v30 ; v34 = v30 * (rreplicate 2 (negate (recip (x31 * x31)) * rsum (v30 * v33)) + rreplicate 2 (recip x31) * v33) ; v36 = (v26 * (rreplicate 5 1.0 - v26)) * rsum (m56 * rtranspose [1,0] (rreplicate 5 v34)) ; m37 = rreplicate 4 (rcast v36) ; v38 = (v19 * (rreplicate 4 1.0 - v19)) * rcast (rsum (m54 * rtranspose [1,0] m37)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v38), v38, rtranspose [1,0] (m22 * m37), v36, rreplicate 2 v26 * rtranspose [1,0] (rreplicate 5 v34), v34]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\m58 v59 m60 v61 m62 v63 -> let v30 = exp (rsum (rtranspose [1,0] (rreplicate 2 (recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m58) + v59)))))) * rtranspose [1,0] m60)) + v61))))) * rtranspose [1,0] m62) + v63) in rreplicate 2 (recip (rsum v30)) * v30"
