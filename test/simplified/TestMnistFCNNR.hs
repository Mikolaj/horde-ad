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
           g :: Rep (AstRanked FullSpan) TKUntyped
             -> Rep (AstRanked FullSpan) TKUntyped
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
    @?= "\\v58 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 -> let v27 = rfromVector (fromList [rsum (v73 * rreplicate 3 7.0), rsum (v74 * rreplicate 3 7.0), rsum (v75 * rreplicate 3 7.0)]) + v76 ; v30 = rreshape [4] v27 ; v33 = rreshape [4] v27 ; v36 = rreshape [4] v27 ; v39 = rreshape [4] v27 ; v41 = rfromVector (fromList [rsum (v77 * v30), rsum (v78 * v33), rsum (v79 * v36), rsum (v80 * v39)]) + v81 ; v44 = rreshape [5] v41 ; v47 = rreshape [5] v41 ; v50 = rreshape [5] v41 ; v53 = rreshape [5] v41 ; v56 = rreshape [5] v41 ; x59 = v58 ! [4] ; x60 = v58 ! [3] ; x61 = v58 ! [2] ; x62 = v58 ! [1] ; x63 = v58 ! [0] ; v64 = rreshape [4] v82 * rreshape [4] (rreplicate 5 x63) + rreshape [4] v83 * rreshape [4] (rreplicate 5 x62) + rreshape [4] v84 * rreshape [4] (rreplicate 5 x61) + rreshape [4] v85 * rreshape [4] (rreplicate 5 x60) + rreshape [4] v86 * rreshape [4] (rreplicate 5 x59) ; x65 = v64 ! [3] ; x66 = v64 ! [2] ; x67 = v64 ! [1] ; x68 = v64 ! [0] ; v69 = rreshape [3] v77 * rreshape [3] (rreplicate 4 x68) + rreshape [3] v78 * rreshape [3] (rreplicate 4 x67) + rreshape [3] v79 * rreshape [3] (rreplicate 4 x66) + rreshape [3] v80 * rreshape [3] (rreplicate 4 x65) ; x70 = v69 ! [2] ; x71 = v69 ! [1] ; x72 = v69 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x72), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x71), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x70), v69, v30 * rreshape [4] (rreplicate 4 x68), v33 * rreshape [4] (rreplicate 4 x67), v36 * rreshape [4] (rreplicate 4 x66), v39 * rreshape [4] (rreplicate 4 x65), v64, v44 * rreshape [5] (rreplicate 5 x63), v47 * rreshape [5] (rreplicate 5 x62), v50 * rreshape [5] (rreplicate 5 x61), v53 * rreshape [5] (rreplicate 5 x60), v56 * rreshape [5] (rreplicate 5 x59), v58]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v523 v524 v525 v526 v527 v528 v529 v530 v531 v532 v533 v534 v535 v536 v537 -> let v27 = rfromVector (fromList [rsum (v523 * rreplicate 3 7.0), rsum (v524 * rreplicate 3 7.0), rsum (v525 * rreplicate 3 7.0)]) + v526 ; v30 = rreshape [4] v27 ; v33 = rreshape [4] v27 ; v36 = rreshape [4] v27 ; v39 = rreshape [4] v27 ; v41 = rfromVector (fromList [rsum (v527 * v30), rsum (v528 * v33), rsum (v529 * v36), rsum (v530 * v39)]) + v531 ; v44 = rreshape [5] v41 ; v47 = rreshape [5] v41 ; v50 = rreshape [5] v41 ; v53 = rreshape [5] v41 ; v56 = rreshape [5] v41 in rfromVector (fromList [rsum (v532 * v44), rsum (v533 * v47), rsum (v534 * v50), rsum (v535 * v53), rsum (v536 * v56)]) + v537"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v58 v1417 v1418 v1419 v1420 v1421 v1422 v1423 v1424 v1425 v1426 v1427 v1428 v1429 v1430 v1431 -> let v27 = rfromVector (fromList [rsum (v1417 * rreplicate 3 7.0), rsum (v1418 * rreplicate 3 7.0), rsum (v1419 * rreplicate 3 7.0)]) + v1420 ; v30 = rreshape [4] v27 ; v33 = rreshape [4] v27 ; v36 = rreshape [4] v27 ; v39 = rreshape [4] v27 ; v41 = rfromVector (fromList [rsum (v1421 * v30), rsum (v1422 * v33), rsum (v1423 * v36), rsum (v1424 * v39)]) + v1425 ; x59 = v58 ! [4] ; x60 = v58 ! [3] ; x61 = v58 ! [2] ; x62 = v58 ! [1] ; x63 = v58 ! [0] ; v64 = rreshape [4] v1426 * rreplicate 4 x63 + rreshape [4] v1427 * rreplicate 4 x62 + rreshape [4] v1428 * rreplicate 4 x61 + rreshape [4] v1429 * rreplicate 4 x60 + rreshape [4] v1430 * rreplicate 4 x59 ; x65 = v64 ! [3] ; x66 = v64 ! [2] ; x67 = v64 ! [1] ; x68 = v64 ! [0] ; v69 = rreshape [3] v1421 * rreplicate 3 x68 + rreshape [3] v1422 * rreplicate 3 x67 + rreshape [3] v1423 * rreplicate 3 x66 + rreshape [3] v1424 * rreplicate 3 x65 in [rreplicate 3 7.0 * rreplicate 3 (v69 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v69 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v69 ! [2]), v69, v30 * rreplicate 4 x68, v33 * rreplicate 4 x67, v36 * rreplicate 4 x66, v39 * rreplicate 4 x65, v64, rreshape [5] v41 * rreplicate 5 x63, rreshape [5] v41 * rreplicate 5 x62, rreshape [5] v41 * rreplicate 5 x61, rreshape [5] v41 * rreplicate 5 x60, rreshape [5] v41 * rreplicate 5 x59, v58]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v1876 v1877 v1878 v1879 v1880 v1881 v1882 v1883 v1884 v1885 v1886 v1887 v1888 v1889 v1890 -> let v27 = rfromVector (fromList [rsum (v1876 * rreplicate 3 7.0), rsum (v1877 * rreplicate 3 7.0), rsum (v1878 * rreplicate 3 7.0)]) + v1879 ; v41 = rfromVector (fromList [rsum (v1880 * rreshape [4] v27), rsum (v1881 * rreshape [4] v27), rsum (v1882 * rreshape [4] v27), rsum (v1883 * rreshape [4] v27)]) + v1884 in rfromVector (fromList [rsum (v1885 * rreshape [5] v41), rsum (v1886 * rreshape [5] v41), rsum (v1887 * rreshape [5] v41), rsum (v1888 * rreshape [5] v41), rsum (v1889 * rreshape [5] v41)]) + v1890"

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
    @?= "\\v76 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 -> let v32 = rfromVector (fromList [rsum (v92 * rreplicate 3 7.0), rsum (v93 * rreplicate 3 7.0), rsum (v94 * rreplicate 3 7.0)]) + v95 ; v33 = exp (negate v32) ; v34 = rreplicate 3 1.0 + v33 ; v35 = recip v34 ; v36 = rreplicate 3 1.0 - v35 ; v37 = v35 * v36 ; v40 = rreshape [4] v35 ; v43 = rreshape [4] v35 ; v46 = rreshape [4] v35 ; v49 = rreshape [4] v35 ; v51 = rfromVector (fromList [rsum (v96 * v40), rsum (v97 * v43), rsum (v98 * v46), rsum (v99 * v49)]) + v100 ; v52 = exp (negate v51) ; v53 = rreplicate 4 1.0 + v52 ; v54 = recip v53 ; v55 = rreplicate 4 1.0 - v54 ; v56 = v54 * v55 ; v59 = rreshape [5] v54 ; v62 = rreshape [5] v54 ; v65 = rreshape [5] v54 ; v68 = rreshape [5] v54 ; v71 = rreshape [5] v54 ; v73 = exp (rfromVector (fromList [rsum (v101 * v59), rsum (v102 * v62), rsum (v103 * v65), rsum (v104 * v68), rsum (v105 * v71)]) + v106) ; x74 = rsum v73 ; v75 = rreplicate 5 (recip x74) ; v77 = v73 * (rreplicate 5 (negate (recip (x74 * x74)) * rsum (v73 * v76)) + v75 * v76) ; x78 = v77 ! [4] ; x79 = v77 ! [3] ; x80 = v77 ! [2] ; x81 = v77 ! [1] ; x82 = v77 ! [0] ; v83 = v56 * (rreshape [4] v101 * rreshape [4] (rreplicate 5 x82) + rreshape [4] v102 * rreshape [4] (rreplicate 5 x81) + rreshape [4] v103 * rreshape [4] (rreplicate 5 x80) + rreshape [4] v104 * rreshape [4] (rreplicate 5 x79) + rreshape [4] v105 * rreshape [4] (rreplicate 5 x78)) ; x84 = v83 ! [3] ; x85 = v83 ! [2] ; x86 = v83 ! [1] ; x87 = v83 ! [0] ; v88 = v37 * (rreshape [3] v96 * rreshape [3] (rreplicate 4 x87) + rreshape [3] v97 * rreshape [3] (rreplicate 4 x86) + rreshape [3] v98 * rreshape [3] (rreplicate 4 x85) + rreshape [3] v99 * rreshape [3] (rreplicate 4 x84)) ; x89 = v88 ! [2] ; x90 = v88 ! [1] ; x91 = v88 ! [0] in [rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x91), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x90), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x89), v88, v40 * rreshape [4] (rreplicate 4 x87), v43 * rreshape [4] (rreplicate 4 x86), v46 * rreshape [4] (rreplicate 4 x85), v49 * rreshape [4] (rreplicate 4 x84), v83, v59 * rreshape [5] (rreplicate 5 x82), v62 * rreshape [5] (rreplicate 5 x81), v65 * rreshape [5] (rreplicate 5 x80), v68 * rreshape [5] (rreplicate 5 x79), v71 * rreshape [5] (rreplicate 5 x78), v77]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\v557 v558 v559 v560 v561 v562 v563 v564 v565 v566 v567 v568 v569 v570 v571 -> let v32 = rfromVector (fromList [rsum (v557 * rreplicate 3 7.0), rsum (v558 * rreplicate 3 7.0), rsum (v559 * rreplicate 3 7.0)]) + v560 ; v33 = exp (negate v32) ; v34 = rreplicate 3 1.0 + v33 ; v35 = recip v34 ; v40 = rreshape [4] v35 ; v43 = rreshape [4] v35 ; v46 = rreshape [4] v35 ; v49 = rreshape [4] v35 ; v51 = rfromVector (fromList [rsum (v561 * v40), rsum (v562 * v43), rsum (v563 * v46), rsum (v564 * v49)]) + v565 ; v52 = exp (negate v51) ; v53 = rreplicate 4 1.0 + v52 ; v54 = recip v53 ; v59 = rreshape [5] v54 ; v62 = rreshape [5] v54 ; v65 = rreshape [5] v54 ; v68 = rreshape [5] v54 ; v71 = rreshape [5] v54 ; v73 = exp (rfromVector (fromList [rsum (v566 * v59), rsum (v567 * v62), rsum (v568 * v65), rsum (v569 * v68), rsum (v570 * v71)]) + v571) ; x74 = rsum v73 ; v75 = rreplicate 5 (recip x74) in v75 * v73"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v76 v1481 v1482 v1483 v1484 v1485 v1486 v1487 v1488 v1489 v1490 v1491 v1492 v1493 v1494 v1495 -> let v35 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v1481 * rreplicate 3 7.0), rsum (v1482 * rreplicate 3 7.0), rsum (v1483 * rreplicate 3 7.0)]) + v1484))) ; v40 = rreshape [4] v35 ; v43 = rreshape [4] v35 ; v46 = rreshape [4] v35 ; v49 = rreshape [4] v35 ; v54 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v1485 * v40), rsum (v1486 * v43), rsum (v1487 * v46), rsum (v1488 * v49)]) + v1489))) ; v59 = rreshape [5] v54 ; v62 = rreshape [5] v54 ; v65 = rreshape [5] v54 ; v68 = rreshape [5] v54 ; v71 = rreshape [5] v54 ; v73 = exp (rfromVector (fromList [rsum (v1490 * v59), rsum (v1491 * v62), rsum (v1492 * v65), rsum (v1493 * v68), rsum (v1494 * v71)]) + v1495) ; x74 = rsum v73 ; v77 = v73 * (rreplicate 5 (negate (recip (x74 * x74)) * rsum (v73 * v76)) + rreplicate 5 (recip x74) * v76) ; x78 = v77 ! [4] ; x79 = v77 ! [3] ; x80 = v77 ! [2] ; x81 = v77 ! [1] ; x82 = v77 ! [0] ; v83 = (v54 * (rreplicate 4 1.0 - v54)) * (rreshape [4] v1490 * rreplicate 4 x82 + rreshape [4] v1491 * rreplicate 4 x81 + rreshape [4] v1492 * rreplicate 4 x80 + rreshape [4] v1493 * rreplicate 4 x79 + rreshape [4] v1494 * rreplicate 4 x78) ; x84 = v83 ! [3] ; x85 = v83 ! [2] ; x86 = v83 ! [1] ; x87 = v83 ! [0] ; v88 = (v35 * (rreplicate 3 1.0 - v35)) * (rreshape [3] v1485 * rreplicate 3 x87 + rreshape [3] v1486 * rreplicate 3 x86 + rreshape [3] v1487 * rreplicate 3 x85 + rreshape [3] v1488 * rreplicate 3 x84) in [rreplicate 3 7.0 * rreplicate 3 (v88 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v88 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v88 ! [2]), v88, v40 * rreplicate 4 x87, v43 * rreplicate 4 x86, v46 * rreplicate 4 x85, v49 * rreplicate 4 x84, v83, v59 * rreplicate 5 x82, v62 * rreplicate 5 x81, v65 * rreplicate 5 x80, v68 * rreplicate 5 x79, v71 * rreplicate 5 x78, v77]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v1955 v1956 v1957 v1958 v1959 v1960 v1961 v1962 v1963 v1964 v1965 v1966 v1967 v1968 v1969 -> let v35 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (v1955 * rreplicate 3 7.0), rsum (v1956 * rreplicate 3 7.0), rsum (v1957 * rreplicate 3 7.0)]) + v1958))) ; v54 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (v1959 * rreshape [4] v35), rsum (v1960 * rreshape [4] v35), rsum (v1961 * rreshape [4] v35), rsum (v1962 * rreshape [4] v35)]) + v1963))) ; v73 = exp (rfromVector (fromList [rsum (v1964 * rreshape [5] v54), rsum (v1965 * rreshape [5] v54), rsum (v1966 * rreshape [5] v54), rsum (v1967 * rreshape [5] v54), rsum (v1968 * rreshape [5] v54)]) + v1969) in rreplicate 5 (recip (rsum v73)) * v73"

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
    @?= "\\v23 m28 v29 m30 v31 m32 v33 -> let m16 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m28) + v29))) ; m20 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m16 * rtranspose [1,0] m30)) + v31)) ; v24 = rsum (m32 * rtranspose [1,0] (rreplicate 5 v23)) ; m25 = rreplicate 4 (rcast v24) ; v26 = rcast (rsum (m30 * rtranspose [1,0] m25)) ; m27 = rreplicate 3 v26 in [rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m27), v26, rtranspose [1,0] (m16 * m25), v24, rtranspose [1,0] (m20 * rreplicate 5 v23), v23]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m100 v101 m102 v103 m104 v105 -> let m16 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m100) + v101))) ; m20 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m16 * rtranspose [1,0] m102)) + v103)) in rsum (m20 * rtranspose [1,0] m104) + v105"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v23 m238 v239 m240 v241 m242 v243 -> let m16 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m238) + v239))) ; v24 = rsum (m242 * rtranspose [1,0] (rreplicate 5 v23)) ; m25 = rreplicate 4 (rcast v24) ; v26 = rcast (rsum (m240 * rtranspose [1,0] m25)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v26), v26, rtranspose [1,0] (m16 * m25), v24, rreplicate 2 (rcast (rsum (m16 * rtranspose [1,0] m240)) + v241) * rtranspose [1,0] (rreplicate 5 v23), v23]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m310 v311 m312 v313 m314 v315 -> rsum (rtranspose [1,0] (rreplicate 2 (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m310) + v311))) * rtranspose [1,0] m312)) + v313)) * rtranspose [1,0] m314) + v315"

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
    @?= "\\v43 m50 v51 m52 v53 m54 v55 -> let v20 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m50) + v51 ; v21 = exp (negate v20) ; v22 = rreplicate 4 1.0 + v21 ; v23 = recip v22 ; v24 = rreplicate 4 1.0 - v23 ; v25 = v23 * v24 ; m27 = rtranspose [1,0] (rreplicate 5 (rcast v23)) ; v30 = rcast (rsum (m27 * rtranspose [1,0] m52)) + v53 ; v31 = exp (negate v30) ; v32 = rreplicate 5 1.0 + v31 ; v33 = recip v32 ; v34 = rreplicate 5 1.0 - v33 ; v35 = v33 * v34 ; v40 = exp (rsum (rtranspose [1,0] (rreplicate 2 v33) * rtranspose [1,0] m54) + v55) ; x41 = rsum v40 ; v42 = rreplicate 2 (recip x41) ; v44 = v40 * (rreplicate 2 (negate (recip (x41 * x41)) * rsum (v40 * v43)) + v42 * v43) ; v46 = v35 * rsum (m54 * rtranspose [1,0] (rreplicate 5 v44)) ; m47 = rreplicate 4 (rcast v46) ; v48 = v25 * rcast (rsum (m52 * rtranspose [1,0] m47)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v48), v48, rtranspose [1,0] (m27 * m47), v46, rreplicate 2 v33 * rtranspose [1,0] (rreplicate 5 v44), v44]"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\m128 v129 m130 v131 m132 v133 -> let v20 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m128) + v129 ; v21 = exp (negate v20) ; v22 = rreplicate 4 1.0 + v21 ; v23 = recip v22 ; m27 = rtranspose [1,0] (rreplicate 5 (rcast v23)) ; v30 = rcast (rsum (m27 * rtranspose [1,0] m130)) + v131 ; v31 = exp (negate v30) ; v32 = rreplicate 5 1.0 + v31 ; v33 = recip v32 ; v40 = exp (rsum (rtranspose [1,0] (rreplicate 2 v33) * rtranspose [1,0] m132) + v133) ; x41 = rsum v40 ; v42 = rreplicate 2 (recip x41) in v42 * v40"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v43 m278 v279 m280 v281 m282 v283 -> let v23 = recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m278) + v279))) ; m27 = rtranspose [1,0] (rreplicate 5 (rcast v23)) ; v33 = recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (m27 * rtranspose [1,0] m280)) + v281))) ; v40 = exp (rsum (rtranspose [1,0] (rreplicate 2 v33) * rtranspose [1,0] m282) + v283) ; x41 = rsum v40 ; v44 = v40 * (rreplicate 2 (negate (recip (x41 * x41)) * rsum (v40 * v43)) + rreplicate 2 (recip x41) * v43) ; v46 = (v33 * (rreplicate 5 1.0 - v33)) * rsum (m282 * rtranspose [1,0] (rreplicate 5 v44)) ; m47 = rreplicate 4 (rcast v46) ; v48 = (v23 * (rreplicate 4 1.0 - v23)) * rcast (rsum (m280 * rtranspose [1,0] m47)) in [rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v48), v48, rtranspose [1,0] (m27 * m47), v46, rreplicate 2 v33 * rtranspose [1,0] (rreplicate 5 v44), v44]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\m356 v357 m358 v359 m360 v361 -> let v40 = exp (rsum (rtranspose [1,0] (rreplicate 2 (recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] m356) + v357)))))) * rtranspose [1,0] m358)) + v359))))) * rtranspose [1,0] m360) + v361) in rreplicate 2 (recip (rsum v40)) * v40"
