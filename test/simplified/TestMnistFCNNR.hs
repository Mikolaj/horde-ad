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
                     mnist (unAsHVector
                            $ parseHVector (AsHVector $ fromDValue valsInit) (HVectorPseudoTensor adinputs))
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
                   (unAsHVector
                    $ parseHVector (AsHVector $ fromDValue valsInit)
                                   (rankedY (stensorKind @TKUntyped) hVector2))
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
           g !hv = toHVectorOf $ AsHVector $ f
                   $ unAsHVector $ parseHVector (AsHVector $ fromValue (valsInit, dataInit)) hv
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
      hVectorInit = unHVectorPseudoTensor $ toHVectorOf $ AsHVector valsInit
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
                     mnist (unAsHVector $ parseHVector (AsHVector $ fromDValue valsInit) (HVectorPseudoTensor adinputs))
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
      hVectorInit = unHVectorPseudoTensor $ toHVectorOf $ AsHVector valsInit
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
                   (unAsHVector
                    $ parseHVector (AsHVector $ fromDValue valsInit)
                                   (rankedY (stensorKind @TKUntyped) hVector2))
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
        hVectorInit = unHVectorPseudoTensor $ toHVectorOf $ AsHVector valsInit
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
           f = \ (AsHVector (pars, (glyphR, labelR))) ->
             MnistFcnnRanked2.afcnnMnistLoss2TensorData
               (glyphR, labelR) pars
           (artRaw, _) = revArtifactAdapt False f (AsHVector (valsInit, dataInit))
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
    @?= "\\v39 x1 -> let h4 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v5 = rproject h4 0 ; h6 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v7 = rproject h6 1 ; h8 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v9 = rproject h8 2 ; v10 = rfromVector (fromList [rsum (rreshape [3] (v5 * rreplicate 3 7.0)), rsum (rreshape [3] (v7 * rreplicate 3 7.0)), rsum (rreshape [3] (v9 * rreplicate 3 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; h11 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v12 = rproject h11 0 ; v13 = rreshape [4] v10 ; h14 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v15 = rproject h14 1 ; v16 = rreshape [4] v10 ; h17 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v18 = rproject h17 2 ; v19 = rreshape [4] v10 ; h20 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v21 = rproject h20 3 ; v22 = rreshape [4] v10 ; v23 = rfromVector (fromList [rsum (rreshape [4] (v12 * v13)), rsum (rreshape [4] (v15 * v16)), rsum (rreshape [4] (v18 * v19)), rsum (rreshape [4] (v21 * v22))]) + tproject2 (tproject2 (tproject1 v1)) ; h24 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v25 = rproject h24 0 ; v26 = rreshape [5] v23 ; h27 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v28 = rproject h27 1 ; v29 = rreshape [5] v23 ; h30 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v31 = rproject h30 2 ; v32 = rreshape [5] v23 ; h33 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v34 = rproject h33 3 ; v35 = rreshape [5] v23 ; h36 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v37 = rproject h36 4 ; v38 = rreshape [5] v23 ; x40 = v39 ! [4] ; x41 = v39 ! [3] ; x42 = v39 ! [2] ; x43 = v39 ! [1] ; x44 = v39 ! [0] ; v45 = rreshape [4] (v25 * rreshape [5] (rreplicate 5 x44)) + rreshape [4] (v28 * rreshape [5] (rreplicate 5 x43)) + rreshape [4] (v31 * rreshape [5] (rreplicate 5 x42)) + rreshape [4] (v34 * rreshape [5] (rreplicate 5 x41)) + rreshape [4] (v37 * rreshape [5] (rreplicate 5 x40)) ; x46 = v45 ! [3] ; x47 = v45 ! [2] ; x48 = v45 ! [1] ; x49 = v45 ! [0] ; v50 = rreshape [3] (v12 * rreshape [4] (rreplicate 4 x49)) + rreshape [3] (v15 * rreshape [4] (rreplicate 4 x48)) + rreshape [3] (v18 * rreshape [4] (rreplicate 4 x47)) + rreshape [3] (v21 * rreshape [4] (rreplicate 4 x46)) ; x51 = v50 ! [2] ; x52 = v50 ! [1] ; x53 = v50 ! [0] in tpair (tpair (tpair ([rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x53), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x52), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x51)], v50), tpair ([v13 * rreshape [4] (rreplicate 4 x49), v16 * rreshape [4] (rreplicate 4 x48), v19 * rreshape [4] (rreplicate 4 x47), v22 * rreshape [4] (rreplicate 4 x46)], v45)), tpair ([v26 * rreshape [5] (rreplicate 5 x44), v29 * rreshape [5] (rreplicate 5 x43), v32 * rreshape [5] (rreplicate 5 x42), v35 * rreshape [5] (rreplicate 5 x41), v38 * rreshape [5] (rreplicate 5 x40)], v39))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let h4 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v5 = rproject h4 0 ; h6 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v7 = rproject h6 1 ; h8 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v9 = rproject h8 2 ; v10 = rfromVector (fromList [rsum (rreshape [3] (v5 * rreplicate 3 7.0)), rsum (rreshape [3] (v7 * rreplicate 3 7.0)), rsum (rreshape [3] (v9 * rreplicate 3 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; h11 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v12 = rproject h11 0 ; v13 = rreshape [4] v10 ; h14 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v15 = rproject h14 1 ; v16 = rreshape [4] v10 ; h17 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v18 = rproject h17 2 ; v19 = rreshape [4] v10 ; h20 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v21 = rproject h20 3 ; v22 = rreshape [4] v10 ; v23 = rfromVector (fromList [rsum (rreshape [4] (v12 * v13)), rsum (rreshape [4] (v15 * v16)), rsum (rreshape [4] (v18 * v19)), rsum (rreshape [4] (v21 * v22))]) + tproject2 (tproject2 (tproject1 v1)) ; h24 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v25 = rproject h24 0 ; v26 = rreshape [5] v23 ; h27 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v28 = rproject h27 1 ; v29 = rreshape [5] v23 ; h30 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v31 = rproject h30 2 ; v32 = rreshape [5] v23 ; h33 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v34 = rproject h33 3 ; v35 = rreshape [5] v23 ; h36 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v37 = rproject h36 4 ; v38 = rreshape [5] v23 in rfromVector (fromList [rsum (rreshape [5] (v25 * v26)), rsum (rreshape [5] (v28 * v29)), rsum (rreshape [5] (v31 * v32)), rsum (rreshape [5] (v34 * v35)), rsum (rreshape [5] (v37 * v38))]) + tproject2 (tproject2 v1)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v39 x1 -> let v10 = rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0)]) + tproject2 (tproject1 (tproject1 v1)) ; v13 = rreshape [4] v10 ; v16 = rreshape [4] v10 ; v19 = rreshape [4] v10 ; v22 = rreshape [4] v10 ; v23 = rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v13), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v16), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v19), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v22)]) + tproject2 (tproject2 (tproject1 v1)) ; x40 = v39 ! [4] ; x41 = v39 ! [3] ; x42 = v39 ! [2] ; x43 = v39 ! [1] ; x44 = v39 ! [0] ; v45 = rgather [4] (rproject (tproject1 (tproject2 v1)) 0) (\\[i112] -> [remF i112 5]) * rreplicate 4 x44 + rgather [4] (rproject (tproject1 (tproject2 v1)) 1) (\\[i114] -> [remF i114 5]) * rreplicate 4 x43 + rgather [4] (rproject (tproject1 (tproject2 v1)) 2) (\\[i116] -> [remF i116 5]) * rreplicate 4 x42 + rgather [4] (rproject (tproject1 (tproject2 v1)) 3) (\\[i118] -> [remF i118 5]) * rreplicate 4 x41 + rgather [4] (rproject (tproject1 (tproject2 v1)) 4) (\\[i120] -> [remF i120 5]) * rreplicate 4 x40 ; x46 = v45 ! [3] ; x47 = v45 ! [2] ; x48 = v45 ! [1] ; x49 = v45 ! [0] ; v50 = rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0) (\\[i104] -> [remF i104 4]) * rreplicate 3 x49 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1) (\\[i106] -> [remF i106 4]) * rreplicate 3 x48 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2) (\\[i108] -> [remF i108 4]) * rreplicate 3 x47 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3) (\\[i110] -> [remF i110 4]) * rreplicate 3 x46 in tpair (tpair (tpair ([rreplicate 3 7.0 * rreplicate 3 (v50 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v50 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v50 ! [2])], v50), tpair ([v13 * rreplicate 4 x49, v16 * rreplicate 4 x48, v19 * rreplicate 4 x47, v22 * rreplicate 4 x46], v45)), tpair ([rreshape [5] v23 * rreplicate 5 x44, rreshape [5] v23 * rreplicate 5 x43, rreshape [5] v23 * rreplicate 5 x42, rreshape [5] v23 * rreplicate 5 x41, rreshape [5] v23 * rreplicate 5 x40], v39))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let v10 = rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0)]) + tproject2 (tproject1 (tproject1 v1)) ; v23 = rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * rreshape [4] v10), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * rreshape [4] v10), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * rreshape [4] v10), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * rreshape [4] v10)]) + tproject2 (tproject2 (tproject1 v1)) in rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * rreshape [5] v23), rsum (rproject (tproject1 (tproject2 v1)) 1 * rreshape [5] v23), rsum (rproject (tproject1 (tproject2 v1)) 2 * rreshape [5] v23), rsum (rproject (tproject1 (tproject2 v1)) 3 * rreshape [5] v23), rsum (rproject (tproject1 (tproject2 v1)) 4 * rreshape [5] v23)]) + tproject2 (tproject2 v1)"

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
    @?= "\\v57 x1 -> let h9 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v10 = rproject h9 0 ; h11 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v12 = rproject h11 1 ; h13 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v14 = rproject h13 2 ; v15 = rfromVector (fromList [rsum (rreshape [3] (v10 * rreplicate 3 7.0)), rsum (rreshape [3] (v12 * rreplicate 3 7.0)), rsum (rreshape [3] (v14 * rreplicate 3 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v16 = exp (negate v15) ; v17 = rreplicate 3 1.0 + v16 ; v18 = recip v17 ; v19 = rreplicate 3 1.0 - v18 ; v20 = v18 * v19 ; h21 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v22 = rproject h21 0 ; v23 = rreshape [4] v18 ; h24 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v25 = rproject h24 1 ; v26 = rreshape [4] v18 ; h27 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v28 = rproject h27 2 ; v29 = rreshape [4] v18 ; h30 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v31 = rproject h30 3 ; v32 = rreshape [4] v18 ; v33 = rfromVector (fromList [rsum (rreshape [4] (v22 * v23)), rsum (rreshape [4] (v25 * v26)), rsum (rreshape [4] (v28 * v29)), rsum (rreshape [4] (v31 * v32))]) + tproject2 (tproject2 (tproject1 v1)) ; v34 = exp (negate v33) ; v35 = rreplicate 4 1.0 + v34 ; v36 = recip v35 ; v37 = rreplicate 4 1.0 - v36 ; v38 = v36 * v37 ; h39 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v40 = rproject h39 0 ; v41 = rreshape [5] v36 ; h42 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v43 = rproject h42 1 ; v44 = rreshape [5] v36 ; h45 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v46 = rproject h45 2 ; v47 = rreshape [5] v36 ; h48 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v49 = rproject h48 3 ; v50 = rreshape [5] v36 ; h51 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v52 = rproject h51 4 ; v53 = rreshape [5] v36 ; v54 = exp (rfromVector (fromList [rsum (rreshape [5] (v40 * v41)), rsum (rreshape [5] (v43 * v44)), rsum (rreshape [5] (v46 * v47)), rsum (rreshape [5] (v49 * v50)), rsum (rreshape [5] (v52 * v53))]) + tproject2 (tproject2 v1)) ; x55 = rsum v54 ; v56 = rreplicate 5 (recip x55) ; v58 = v54 * (rreplicate 5 (negate (recip (x55 * x55)) * rsum (v54 * v57)) + v56 * v57) ; x59 = v58 ! [4] ; x60 = v58 ! [3] ; x61 = v58 ! [2] ; x62 = v58 ! [1] ; x63 = v58 ! [0] ; v64 = v38 * (rreshape [4] (v40 * rreshape [5] (rreplicate 5 x63)) + rreshape [4] (v43 * rreshape [5] (rreplicate 5 x62)) + rreshape [4] (v46 * rreshape [5] (rreplicate 5 x61)) + rreshape [4] (v49 * rreshape [5] (rreplicate 5 x60)) + rreshape [4] (v52 * rreshape [5] (rreplicate 5 x59))) ; x65 = v64 ! [3] ; x66 = v64 ! [2] ; x67 = v64 ! [1] ; x68 = v64 ! [0] ; v69 = v20 * (rreshape [3] (v22 * rreshape [4] (rreplicate 4 x68)) + rreshape [3] (v25 * rreshape [4] (rreplicate 4 x67)) + rreshape [3] (v28 * rreshape [4] (rreplicate 4 x66)) + rreshape [3] (v31 * rreshape [4] (rreplicate 4 x65))) ; x70 = v69 ! [2] ; x71 = v69 ! [1] ; x72 = v69 ! [0] in tpair (tpair (tpair ([rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x72), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x71), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x70)], v69), tpair ([v23 * rreshape [4] (rreplicate 4 x68), v26 * rreshape [4] (rreplicate 4 x67), v29 * rreshape [4] (rreplicate 4 x66), v32 * rreshape [4] (rreplicate 4 x65)], v64)), tpair ([v41 * rreshape [5] (rreplicate 5 x63), v44 * rreshape [5] (rreplicate 5 x62), v47 * rreshape [5] (rreplicate 5 x61), v50 * rreshape [5] (rreplicate 5 x60), v53 * rreshape [5] (rreplicate 5 x59)], v58))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\x1 -> let h9 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v10 = rproject h9 0 ; h11 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v12 = rproject h11 1 ; h13 = [rproject (tproject1 (tproject1 (tproject1 v1))) 0, rproject (tproject1 (tproject1 (tproject1 v1))) 1, rproject (tproject1 (tproject1 (tproject1 v1))) 2] ; v14 = rproject h13 2 ; v15 = rfromVector (fromList [rsum (rreshape [3] (v10 * rreplicate 3 7.0)), rsum (rreshape [3] (v12 * rreplicate 3 7.0)), rsum (rreshape [3] (v14 * rreplicate 3 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v16 = exp (negate v15) ; v17 = rreplicate 3 1.0 + v16 ; v18 = recip v17 ; h21 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v22 = rproject h21 0 ; v23 = rreshape [4] v18 ; h24 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v25 = rproject h24 1 ; v26 = rreshape [4] v18 ; h27 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v28 = rproject h27 2 ; v29 = rreshape [4] v18 ; h30 = [rproject (tproject1 (tproject2 (tproject1 v1))) 0, rproject (tproject1 (tproject2 (tproject1 v1))) 1, rproject (tproject1 (tproject2 (tproject1 v1))) 2, rproject (tproject1 (tproject2 (tproject1 v1))) 3] ; v31 = rproject h30 3 ; v32 = rreshape [4] v18 ; v33 = rfromVector (fromList [rsum (rreshape [4] (v22 * v23)), rsum (rreshape [4] (v25 * v26)), rsum (rreshape [4] (v28 * v29)), rsum (rreshape [4] (v31 * v32))]) + tproject2 (tproject2 (tproject1 v1)) ; v34 = exp (negate v33) ; v35 = rreplicate 4 1.0 + v34 ; v36 = recip v35 ; h39 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v40 = rproject h39 0 ; v41 = rreshape [5] v36 ; h42 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v43 = rproject h42 1 ; v44 = rreshape [5] v36 ; h45 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v46 = rproject h45 2 ; v47 = rreshape [5] v36 ; h48 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v49 = rproject h48 3 ; v50 = rreshape [5] v36 ; h51 = [rproject (tproject1 (tproject2 v1)) 0, rproject (tproject1 (tproject2 v1)) 1, rproject (tproject1 (tproject2 v1)) 2, rproject (tproject1 (tproject2 v1)) 3, rproject (tproject1 (tproject2 v1)) 4] ; v52 = rproject h51 4 ; v53 = rreshape [5] v36 ; v54 = exp (rfromVector (fromList [rsum (rreshape [5] (v40 * v41)), rsum (rreshape [5] (v43 * v44)), rsum (rreshape [5] (v46 * v47)), rsum (rreshape [5] (v49 * v50)), rsum (rreshape [5] (v52 * v53))]) + tproject2 (tproject2 v1)) ; x55 = rsum v54 ; v56 = rreplicate 5 (recip x55) in v56 * v54"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v57 x1 -> let v18 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0)]) + tproject2 (tproject1 (tproject1 v1))))) ; v23 = rreshape [4] v18 ; v26 = rreshape [4] v18 ; v29 = rreshape [4] v18 ; v32 = rreshape [4] v18 ; v36 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v23), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v26), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v29), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v32)]) + tproject2 (tproject2 (tproject1 v1))))) ; v41 = rreshape [5] v36 ; v44 = rreshape [5] v36 ; v47 = rreshape [5] v36 ; v50 = rreshape [5] v36 ; v53 = rreshape [5] v36 ; v54 = exp (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * v41), rsum (rproject (tproject1 (tproject2 v1)) 1 * v44), rsum (rproject (tproject1 (tproject2 v1)) 2 * v47), rsum (rproject (tproject1 (tproject2 v1)) 3 * v50), rsum (rproject (tproject1 (tproject2 v1)) 4 * v53)]) + tproject2 (tproject2 v1)) ; x55 = rsum v54 ; v58 = v54 * (rreplicate 5 (negate (recip (x55 * x55)) * rsum (v54 * v57)) + rreplicate 5 (recip x55) * v57) ; x59 = v58 ! [4] ; x60 = v58 ! [3] ; x61 = v58 ! [2] ; x62 = v58 ! [1] ; x63 = v58 ! [0] ; v64 = (v36 * (rreplicate 4 1.0 - v36)) * (rgather [4] (rproject (tproject1 (tproject2 v1)) 0) (\\[i131] -> [remF i131 5]) * rreplicate 4 x63 + rgather [4] (rproject (tproject1 (tproject2 v1)) 1) (\\[i133] -> [remF i133 5]) * rreplicate 4 x62 + rgather [4] (rproject (tproject1 (tproject2 v1)) 2) (\\[i135] -> [remF i135 5]) * rreplicate 4 x61 + rgather [4] (rproject (tproject1 (tproject2 v1)) 3) (\\[i137] -> [remF i137 5]) * rreplicate 4 x60 + rgather [4] (rproject (tproject1 (tproject2 v1)) 4) (\\[i139] -> [remF i139 5]) * rreplicate 4 x59) ; x65 = v64 ! [3] ; x66 = v64 ! [2] ; x67 = v64 ! [1] ; x68 = v64 ! [0] ; v69 = (v18 * (rreplicate 3 1.0 - v18)) * (rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0) (\\[i123] -> [remF i123 4]) * rreplicate 3 x68 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1) (\\[i125] -> [remF i125 4]) * rreplicate 3 x67 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2) (\\[i127] -> [remF i127 4]) * rreplicate 3 x66 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3) (\\[i129] -> [remF i129 4]) * rreplicate 3 x65) in tpair (tpair (tpair ([rreplicate 3 7.0 * rreplicate 3 (v69 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v69 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v69 ! [2])], v69), tpair ([v23 * rreplicate 4 x68, v26 * rreplicate 4 x67, v29 * rreplicate 4 x66, v32 * rreplicate 4 x65], v64)), tpair ([v41 * rreplicate 5 x63, v44 * rreplicate 5 x62, v47 * rreplicate 5 x61, v50 * rreplicate 5 x60, v53 * rreplicate 5 x59], v58))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x1 -> let v18 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0)]) + tproject2 (tproject1 (tproject1 v1))))) ; v36 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * rreshape [4] v18), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * rreshape [4] v18), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * rreshape [4] v18), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * rreshape [4] v18)]) + tproject2 (tproject2 (tproject1 v1))))) ; v54 = exp (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * rreshape [5] v36), rsum (rproject (tproject1 (tproject2 v1)) 1 * rreshape [5] v36), rsum (rproject (tproject1 (tproject2 v1)) 2 * rreshape [5] v36), rsum (rproject (tproject1 (tproject2 v1)) 3 * rreshape [5] v36), rsum (rproject (tproject1 (tproject2 v1)) 4 * rreshape [5] v36)]) + tproject2 (tproject2 v1)) in rreplicate 5 (recip (rsum v54)) * v54"

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
    @?= "\\v7 x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; m6 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) ; v8 = rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 m1)) * rreplicate 5 v7)) ; m9 = rreplicate 4 (rcast v8) ; v10 = rcast (rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))) * m9))) ; m11 = rreplicate 3 v10 in tpair (tpair (tpair (rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m11), v10), tpair (rtranspose [1,0] (m5 * m9), v8)), tpair (rtranspose [1,0] (m6 * rreplicate 5 v7), v7))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; m6 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) in rsum (m6 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v7 x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; v8 = rsum (tproject1 (tproject2 m1) * rtranspose [1,0] (rreplicate 5 v7)) ; m9 = rreplicate 4 (rcast v8) ; v10 = rcast (rsum (tproject1 (tproject2 (tproject1 m1)) * rtranspose [1,0] m9)) in tpair (tpair (tpair (rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v10), v10), tpair (rtranspose [1,0] (m5 * m9), v8)), tpair (rreplicate 2 (rcast (rsum (m5 * rgather [4,5] (tproject1 (tproject2 (tproject1 m1))) (\\[i12, i13] -> [i13, i12]))) + tproject2 (tproject2 (tproject1 m1))) * rtranspose [1,0] (rreplicate 5 v7), v7))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rsum (rtranspose [1,0] (rreplicate 2 (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i18, i19] -> [i19, i18])) + tproject2 (tproject2 m1)"


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
    @?= "\\dummy -> tlet (exp (rsum (rtranspose [1,0] (rreplicate 2 (tlet (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (tlet (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rconstant 7.0))) * rconstant (rconst (rfromListLinear [3,4] [1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0]))) + rcast (rconstant (rconst (rfromListLinear [4] [1.0,2.0,3.0,4.0])))) (\\v5 -> tlet (rconstant (recip (rreplicate 4 1.0 + exp (negate (rprimalPart v5))))) (\\v6 -> rD (rprimalPart v6) (rdualPart (rconstant (rprimalPart v6 * (rreplicate 4 1.0 - rprimalPart v6)) * rD (rreplicate 4 0.0) (rdualPart v5)))))))) * rconstant (rconst (rfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0])))) + rconstant (rcast (rconst (rfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v7 -> tlet (rconstant (recip (rreplicate 5 1.0 + exp (negate (rprimalPart v7))))) (\\v8 -> rD (rprimalPart v8) (rdualPart (rconstant (rprimalPart v8 * (rreplicate 5 1.0 - rprimalPart v8)) * rD (rreplicate 5 0.0) (rdualPart v7))))))) * rconstant (rconst (rfromListLinear [5,2] [1.0,1.0,2.0,2.0,3.0,3.0,4.0,4.0,5.0,5.0]))) + rconstant (rcast (rconst (rfromListLinear [2] [1.0,2.0]))))) (\\v9 -> rreplicate 2 (recip (rsum v9)) * v9)"

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
    @?= "\\v27 x1 -> let v10 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)) ; v11 = exp (negate v10) ; v12 = rreplicate 4 1.0 + v11 ; v13 = recip v12 ; v14 = rreplicate 4 1.0 - v13 ; v15 = v13 * v14 ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v17 = rcast (rsum (m16 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)) ; v18 = exp (negate v17) ; v19 = rreplicate 5 1.0 + v18 ; v20 = recip v19 ; v21 = rreplicate 5 1.0 - v20 ; v22 = v20 * v21 ; m23 = rtranspose [1,0] (rreplicate 2 v20) ; v24 = exp (rsum (m23 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v26 = rreplicate 2 (recip x25) ; v28 = v24 * (rreplicate 2 (negate (recip (x25 * x25)) * rsum (v24 * v27)) + v26 * v27) ; m29 = rreplicate 5 v28 ; v30 = v22 * rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 m1)) * m29)) ; m31 = rreplicate 4 (rcast v30) ; v32 = v15 * rcast (rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))) * m31))) ; m33 = rreplicate 3 v32 in tpair (tpair (tpair (rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m33), v32), tpair (rtranspose [1,0] (m16 * m31), v30)), tpair (rtranspose [1,0] (m23 * m29), v28))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\x1 -> let v10 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)) ; v11 = exp (negate v10) ; v12 = rreplicate 4 1.0 + v11 ; v13 = recip v12 ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v17 = rcast (rsum (m16 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)) ; v18 = exp (negate v17) ; v19 = rreplicate 5 1.0 + v18 ; v20 = recip v19 ; m23 = rtranspose [1,0] (rreplicate 2 v20) ; v24 = exp (rsum (m23 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v26 = rreplicate 2 (recip x25) in v26 * v24"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v27 x1 -> let v13 = recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rgather [3,4] (tproject1 (tproject1 (tproject1 m1))) (\\[i38, i39] -> [i39, i38])) + tproject2 (tproject1 (tproject1 m1))))) ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v20 = recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (m16 * rgather [4,5] (tproject1 (tproject2 (tproject1 m1))) (\\[i36, i37] -> [i37, i36]))) + tproject2 (tproject2 (tproject1 m1))))) ; v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 v20) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i34, i35] -> [i35, i34])) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v28 = v24 * (rreplicate 2 (negate (recip (x25 * x25)) * rsum (v24 * v27)) + rreplicate 2 (recip x25) * v27) ; v30 = (v20 * (rreplicate 5 1.0 - v20)) * rsum (tproject1 (tproject2 m1) * rtranspose [1,0] (rreplicate 5 v28)) ; m31 = rreplicate 4 (rcast v30) ; v32 = (v13 * (rreplicate 4 1.0 - v13)) * rcast (rsum (tproject1 (tproject2 (tproject1 m1)) * rtranspose [1,0] m31)) in tpair (tpair (tpair (rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v32), v32), tpair (rtranspose [1,0] (m16 * m31), v30)), tpair (rreplicate 2 v20 * rtranspose [1,0] (rreplicate 5 v28), v28))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x1 -> let v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 (recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)))))))) * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1))))))) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i48, i49] -> [i49, i48])) + tproject2 (tproject2 m1)) in rreplicate 2 (recip (rsum v24)) * v24"
