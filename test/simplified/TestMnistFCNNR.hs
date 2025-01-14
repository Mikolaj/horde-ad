{-# LANGUAGE OverloadedLists #-}
-- | Tests of "MnistFcnnRanked1" and "MnistFcnnRanked2" neural networks
-- using a few different optimization pipelines.
module TestMnistFCNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
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

import Data.Array.Nested (pattern (:$:), pattern ZSR)
import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.OpsAst
import HordeAd.External.OptimizerTools

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
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTA prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ RepN $ Nested.rfromVector (nPV :$: ZSR)
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
      emptyR = RepN $ Nested.rfromList1Prim []
      hVectorInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters target r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length params1Init)
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector RepN -> r
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
       let runBatch :: HVector RepN -> (Int, [MnistData r]) -> IO (HVector RepN)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal RepN)
                   -> ADVal target (TKR 0 r)
                 f mnist adinputs =
                   MnistFcnnRanked1.afcnnMnistLoss1
                     widthHidden widthHidden2
                     mnist (unAsHVector
                            $ parseHVector (AsHVector $ fromDValue valsInit) (dmkHVector adinputs))
                 res = fst $ sgd gamma f chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector RepN -> IO (HVector RepN)
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
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTI prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ RepN $ Nested.rfromVector (nPV :$: ZSR)
          $ V.map realToFrac
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = RepN $ Nested.rfromList1Prim []
      hVectorInit = V.fromList params1Init
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters target r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length params1Init)
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector RepN -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 valsInit widthHidden widthHidden2
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- take (batchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, _, var, hVector2)
         <- funToAstRevIO $ FTKUntyped (voidFromHVector hVectorInit)
       (varGlyph, astGlyph) <-
         funToAstIO (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar) id
       (varLabel, astLabel) <-
         funToAstIO (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar) id
       let ast :: AstTensor AstMethodLet FullSpan (TKR 0 r)
           ast = MnistFcnnRanked1.afcnnMnistLoss1TensorData
                   widthHidden widthHidden2 (astGlyph, astLabel)
                   (unAsHVector
                    $ parseHVector (AsHVector $ fromDValue valsInit)
                                   hVector2)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector RepN -> (Int, [MnistData r]) -> IO (HVector RepN)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal RepN)
                   -> ADVal target (TKR 0 r)
                 f (glyph, label) varInputs =
                   let env = extendEnv var (dmkHVector varInputs) emptyEnv
                       envMnist =
                         extendEnv varGlyph
                           (rconcrete $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) glyph)
                         $ extendEnv varLabel
                             (rconcrete $ Nested.rfromVector (fromList [sizeMnistLabelInt]) label)
                             env
                   in interpretAst envMnist ast
                 res = fst $ sgd gamma f chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector RepN -> IO (HVector RepN)
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
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTO prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ RepN $ Nested.rfromVector (nPV :$: ZSR)
          $ V.map realToFrac
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = RepN $ Nested.rfromList1Prim []
      hVectorInit = V.fromList params1Init
      -- This is a very ugly and probably unavoidable boilerplate:
      -- we have to manually define a dummy value of type ADFcnnMnist1Parameters
      -- with the correct list lengths (vector lengths can be fake)
      -- to bootstrap the adaptor machinery. Such boilerplate can be
      -- avoided only with shapely typed tensors and scalars or when
      -- not using adaptors.
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters target r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (length params1Init)
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector RepN -> r
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
                      in ( RepN $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) dglyph
                         , RepN $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR) dlabel )
             [] -> error "empty test data"
           f = \ (pars, (glyphR, labelR)) ->
             MnistFcnnRanked1.afcnnMnistLoss1TensorData
               widthHidden widthHidden2
               (glyphR, labelR) pars
           g :: AstTensor AstMethodLet FullSpan TKUntyped
             -> AstTensor AstMethodLet FullSpan TKUntyped
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
           go :: [MnistData r] -> HVector RepN -> HVector RepN
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicRanked @r @1
                          $ RepN $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) glyph
                 labelD = DynamicRanked @r @1
                          $ RepN $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR)  label
                 parametersAndInput =
                   dmkHVector
                   $ V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   dunHVector
                   $ fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradient gamma parameters gradientHVector)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector RepN -> (Int, [MnistData r]) -> IO (HVector RepN)
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
       let runEpoch :: Int -> HVector RepN -> IO (HVector RepN)
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
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTA prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters target r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        RepN widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector RepN -> r
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
       let runBatch :: HVector RepN -> (Int, [MnistData r]) -> IO (HVector RepN)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal RepN)
                   -> ADVal target (TKR 0 r)
                 f mnist adinputs =
                   MnistFcnnRanked2.afcnnMnistLoss2
                     mnist (unAsHVector $ parseHVector (AsHVector $ fromDValue valsInit) (dmkHVector adinputs))
                 res = fst $ sgd gamma f chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector RepN -> IO (HVector RepN)
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
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTI prefix epochs maxBatches widthHidden widthHidden2
                   gamma batchSize expected =
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters target r
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
                        RepN widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
      hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit)
                        , show gamma ]
      ftest :: [MnistData r] -> HVector RepN -> r
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
       (varGlyph, astGlyph) <-
         funToAstIO (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar) id
       (varLabel, astLabel) <-
         funToAstIO (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar) id
       let ast :: AstTensor AstMethodLet FullSpan (TKR 0 r)
           ast = MnistFcnnRanked2.afcnnMnistLoss2TensorData
                   (astGlyph, astLabel)
                   (unAsHVector
                    $ parseHVector (AsHVector $ fromDValue valsInit)
                                   hVector2)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector RepN -> (Int, [MnistData r]) -> IO (HVector RepN)
           runBatch !hVector (k, chunk) = do
             let f :: MnistData r -> HVector (ADVal RepN)
                   -> ADVal target (TKR 0 r)
                 f (glyph, label) varInputs =
                   let env = extendEnv var (dmkHVector varInputs) emptyEnv
                       envMnist =
                         extendEnv varGlyph
                           (rconcrete $ Nested.rfromVector (fromList [sizeMnistGlyphInt]) glyph)
                         $ extendEnv varLabel
                             (rconcrete $ Nested.rfromVector (fromList [sizeMnistLabelInt]) label)
                             env
                   in interpretAst envMnist ast
                 res = fst $ sgd gamma f chunk hVector
                 trainScore = ftest chunk res
                 testScore = ftest testData res
                 lenChunk = length chunk
             unless (widthHidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> HVector RepN -> IO (HVector RepN)
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
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Random r
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
               RepN widthHidden widthHidden2 r
        valsInitShaped = fst $ randomVals 1 (mkStdGen 44)
        valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters target r
        valsInit =
          -- This almost works and I wouldn't need forgetShape,
          -- but there is nowhere to get aInit from.
          --   parseHVector aInit hVectorInit
          forgetShape valsInitShaped
        hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show widthHidden, show widthHidden2
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit)
                          , show gamma ]
        ftest :: [MnistData r] -> HVector RepN -> r
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
                      in ( RepN $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) dglyph
                         , RepN $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR) dlabel )
             [] -> error "empty test data"
           f = \ (AsHVector (pars, (glyphR, labelR))) ->
             MnistFcnnRanked2.afcnnMnistLoss2TensorData
               (glyphR, labelR) pars
           (artRaw, _) = revArtifactAdapt False f (AsHVector (valsInit, dataInit))
           art = simplifyArtifactGradient artRaw
           go :: [MnistData r] -> HVector RepN -> HVector RepN
           go [] parameters = parameters
           go ((glyph, label) : rest) !parameters =
             let glyphD = DynamicRanked @r @1
                          $ RepN $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) glyph
                 labelD = DynamicRanked @r @1
                          $ RepN $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR)  label
                 parametersAndInput =
                   dmkHVector
                   $ V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   dunHVector
                   $ fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradient gamma parameters gradientHVector)
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: HVector RepN -> (Int, [MnistData r]) -> IO (HVector RepN)
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
       let runEpoch :: Int -> HVector RepN -> IO (HVector RepN)
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

valsInitVTOPP :: MnistFcnnRanked1.ADFcnnMnist1Parameters RepN Double
valsInitVTOPP =
  ( ( replicate 3 (RepN $ Nested.rfromList1Prim [1, 2, 3])
    , RepN $ Nested.rfromList1Prim [1, 2, 3] )
  , ( replicate 4 (RepN $ Nested.rfromList1Prim [1, 2, 3])
    , RepN $ Nested.rfromList1Prim [1, 2, 3, 4] )
  , ( replicate 5 (RepN $ Nested.rfromList1Prim [1, 2, 3, 4])
    , RepN $ Nested.rfromList1Prim [1, 2, 3, 4, 5] ) )

testVTOPP :: Assertion
testVTOPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @SizeMnistGlyph) stensorKind
                     ((fromPrimal . AstConcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters (AstTensor AstMethodLet FullSpan)
                                                         Double
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T = MnistFcnnRanked1.afcnnMnist1 id id 3 4 blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVTOPP
  printArtifactPretty renames artifactRev
    @?= "\\v18 x1 -> let v4 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v5 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v6 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v7 = rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * v4), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * v5), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * v6)]) + tproject2 (tproject1 (tproject1 v1)) ; v8 = rreshape [4] v7 ; v9 = rreshape [4] v7 ; v10 = rreshape [4] v7 ; v11 = rreshape [4] v7 ; v12 = rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v8), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v9), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v10), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v11)]) + tproject2 (tproject2 (tproject1 v1)) ; v13 = rreshape [5] v12 ; v14 = rreshape [5] v12 ; v15 = rreshape [5] v12 ; v16 = rreshape [5] v12 ; v17 = rreshape [5] v12 ; v19 = rreplicate 5 (v18 ! [4]) ; v20 = rreplicate 5 (v18 ! [3]) ; v21 = rreplicate 5 (v18 ! [2]) ; v22 = rreplicate 5 (v18 ! [1]) ; v23 = rreplicate 5 (v18 ! [0]) ; v24 = rreshape [4] (rproject (tproject1 (tproject2 v1)) 0 * v23) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 1 * v22) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 2 * v21) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 3 * v20) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 4 * v19) ; v25 = rreplicate 4 (v24 ! [3]) ; v26 = rreplicate 4 (v24 ! [2]) ; v27 = rreplicate 4 (v24 ! [1]) ; v28 = rreplicate 4 (v24 ! [0]) ; v29 = rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v28) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v27) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v26) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v25) ; v30 = rreplicate 3 (v29 ! [2]) ; v31 = rreplicate 3 (v29 ! [1]) ; v32 = rreplicate 3 (v29 ! [0]) in tpair (tpair (tpair ([v4 * v32, v5 * v31, v6 * v30], v29), tpair ([v8 * v28, v9 * v27, v10 * v26, v11 * v25], v24)), tpair ([v13 * v23, v14 * v22, v15 * v21, v16 * v20, v17 * v19], v18))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let v4 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v5 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v6 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v7 = rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * v4), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * v5), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * v6)]) + tproject2 (tproject1 (tproject1 v1)) ; v8 = rreshape [4] v7 ; v9 = rreshape [4] v7 ; v10 = rreshape [4] v7 ; v11 = rreshape [4] v7 ; v12 = rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v8), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v9), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v10), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v11)]) + tproject2 (tproject2 (tproject1 v1)) ; v13 = rreshape [5] v12 ; v14 = rreshape [5] v12 ; v15 = rreshape [5] v12 ; v16 = rreshape [5] v12 ; v17 = rreshape [5] v12 in rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * v13), rsum (rproject (tproject1 (tproject2 v1)) 1 * v14), rsum (rproject (tproject1 (tproject2 v1)) 2 * v15), rsum (rproject (tproject1 (tproject2 v1)) 3 * v16), rsum (rproject (tproject1 (tproject2 v1)) 4 * v17)]) + tproject2 (tproject2 v1)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v18 x1 -> let v7 = rfromVector (fromList [rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 0) (rreplicate 3 (rscalar 7.0)), rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 1) (rreplicate 3 (rscalar 7.0)), rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 2) (rreplicate 3 (rscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v8 = rreshape [4] v7 ; v9 = rreshape [4] v7 ; v10 = rreshape [4] v7 ; v11 = rreshape [4] v7 ; v12 = rfromVector (fromList [rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 0) v8, rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 1) v9, rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 2) v10, rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 3) v11]) + tproject2 (tproject2 (tproject1 v1)) ; v19 = rreplicate 5 (v18 ! [4]) ; v20 = rreplicate 5 (v18 ! [3]) ; v21 = rreplicate 5 (v18 ! [2]) ; v22 = rreplicate 5 (v18 ! [1]) ; v23 = rreplicate 5 (v18 ! [0]) ; v24 = rgather [4] (rproject (tproject1 (tproject2 v1)) 0) (\\[i37] -> [remF i37 5]) * rreshape [4] v23 + rgather [4] (rproject (tproject1 (tproject2 v1)) 1) (\\[i38] -> [remF i38 5]) * rreshape [4] v22 + rgather [4] (rproject (tproject1 (tproject2 v1)) 2) (\\[i39] -> [remF i39 5]) * rreshape [4] v21 + rgather [4] (rproject (tproject1 (tproject2 v1)) 3) (\\[i40] -> [remF i40 5]) * rreshape [4] v20 + rgather [4] (rproject (tproject1 (tproject2 v1)) 4) (\\[i41] -> [remF i41 5]) * rreshape [4] v19 ; v25 = rreplicate 4 (v24 ! [3]) ; v26 = rreplicate 4 (v24 ! [2]) ; v27 = rreplicate 4 (v24 ! [1]) ; v28 = rreplicate 4 (v24 ! [0]) ; v29 = rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0) (\\[i33] -> [remF i33 4]) * rreshape [3] v28 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1) (\\[i34] -> [remF i34 4]) * rreshape [3] v27 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2) (\\[i35] -> [remF i35 4]) * rreshape [3] v26 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3) (\\[i36] -> [remF i36 4]) * rreshape [3] v25 in tpair (tpair (tpair ([rreplicate 3 (rscalar 7.0) * rreplicate 3 (v29 ! [0]), rreplicate 3 (rscalar 7.0) * rreplicate 3 (v29 ! [1]), rreplicate 3 (rscalar 7.0) * rreplicate 3 (v29 ! [2])], v29), tpair ([v8 * v28, v9 * v27, v10 * v26, v11 * v25], v24)), tpair ([rreshape [5] v12 * v23, rreshape [5] v12 * v22, rreshape [5] v12 * v21, rreshape [5] v12 * v20, rreshape [5] v12 * v19], v18))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let v7 = rfromVector (fromList [rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 0) (rreplicate 3 (rscalar 7.0)), rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 1) (rreplicate 3 (rscalar 7.0)), rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 2) (rreplicate 3 (rscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v12 = rfromVector (fromList [rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 0) (rreshape [4] v7), rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 1) (rreshape [4] v7), rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 2) (rreshape [4] v7), rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 3) (rreshape [4] v7)]) + tproject2 (tproject2 (tproject1 v1)) in rfromVector (fromList [rdot0 (rproject (tproject1 (tproject2 v1)) 0) (rreshape [5] v12), rdot0 (rproject (tproject1 (tproject2 v1)) 1) (rreshape [5] v12), rdot0 (rproject (tproject1 (tproject2 v1)) 2) (rreshape [5] v12), rdot0 (rproject (tproject1 (tproject2 v1)) 3) (rreshape [5] v12), rdot0 (rproject (tproject1 (tproject2 v1)) 4) (rreshape [5] v12)]) + tproject2 (tproject2 v1)"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @SizeMnistGlyph) stensorKind
                     ((fromPrimal . AstConcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                         (AstTensor AstMethodLet FullSpan) Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMax1 3 4 blackGlyph
      (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVTOPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v36 x1 -> let v9 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v10 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v11 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v12 = rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * v9), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * v10), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * v11)]) + tproject2 (tproject1 (tproject1 v1)) ; v13 = exp (negate v12) ; v14 = rreplicate 3 (rscalar 1.0) + v13 ; v15 = recip v14 ; v16 = rreplicate 3 (rscalar 1.0) - v15 ; v17 = v15 * v16 ; v18 = rreshape [4] v15 ; v19 = rreshape [4] v15 ; v20 = rreshape [4] v15 ; v21 = rreshape [4] v15 ; v22 = rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v18), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v19), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v20), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v21)]) + tproject2 (tproject2 (tproject1 v1)) ; v23 = exp (negate v22) ; v24 = rreplicate 4 (rscalar 1.0) + v23 ; v25 = recip v24 ; v26 = rreplicate 4 (rscalar 1.0) - v25 ; v27 = v25 * v26 ; v28 = rreshape [5] v25 ; v29 = rreshape [5] v25 ; v30 = rreshape [5] v25 ; v31 = rreshape [5] v25 ; v32 = rreshape [5] v25 ; v33 = exp (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * v28), rsum (rproject (tproject1 (tproject2 v1)) 1 * v29), rsum (rproject (tproject1 (tproject2 v1)) 2 * v30), rsum (rproject (tproject1 (tproject2 v1)) 3 * v31), rsum (rproject (tproject1 (tproject2 v1)) 4 * v32)]) + tproject2 (tproject2 v1)) ; x34 = rsum v33 ; v35 = rreplicate 5 (recip x34) ; v37 = v33 * (rreplicate 5 (negate (recip (x34 * x34)) * rsum (v33 * v36)) + v35 * v36) ; v38 = rreplicate 5 (v37 ! [4]) ; v39 = rreplicate 5 (v37 ! [3]) ; v40 = rreplicate 5 (v37 ! [2]) ; v41 = rreplicate 5 (v37 ! [1]) ; v42 = rreplicate 5 (v37 ! [0]) ; v43 = v27 * (rreshape [4] (rproject (tproject1 (tproject2 v1)) 0 * v42) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 1 * v41) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 2 * v40) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 3 * v39) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 4 * v38)) ; v44 = rreplicate 4 (v43 ! [3]) ; v45 = rreplicate 4 (v43 ! [2]) ; v46 = rreplicate 4 (v43 ! [1]) ; v47 = rreplicate 4 (v43 ! [0]) ; v48 = v17 * (rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v47) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v46) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v45) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v44)) ; v49 = rreplicate 3 (v48 ! [2]) ; v50 = rreplicate 3 (v48 ! [1]) ; v51 = rreplicate 3 (v48 ! [0]) in tpair (tpair (tpair ([v9 * v51, v10 * v50, v11 * v49], v48), tpair ([v18 * v47, v19 * v46, v20 * v45, v21 * v44], v43)), tpair ([v28 * v42, v29 * v41, v30 * v40, v31 * v39, v32 * v38], v37))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\x1 -> let v9 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v10 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v11 = rreshape [3] (rreplicate 784 (rscalar 7.0)) ; v12 = rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * v9), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * v10), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * v11)]) + tproject2 (tproject1 (tproject1 v1)) ; v13 = exp (negate v12) ; v14 = rreplicate 3 (rscalar 1.0) + v13 ; v15 = recip v14 ; v18 = rreshape [4] v15 ; v19 = rreshape [4] v15 ; v20 = rreshape [4] v15 ; v21 = rreshape [4] v15 ; v22 = rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v18), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v19), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v20), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v21)]) + tproject2 (tproject2 (tproject1 v1)) ; v23 = exp (negate v22) ; v24 = rreplicate 4 (rscalar 1.0) + v23 ; v25 = recip v24 ; v28 = rreshape [5] v25 ; v29 = rreshape [5] v25 ; v30 = rreshape [5] v25 ; v31 = rreshape [5] v25 ; v32 = rreshape [5] v25 ; v33 = exp (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * v28), rsum (rproject (tproject1 (tproject2 v1)) 1 * v29), rsum (rproject (tproject1 (tproject2 v1)) 2 * v30), rsum (rproject (tproject1 (tproject2 v1)) 3 * v31), rsum (rproject (tproject1 (tproject2 v1)) 4 * v32)]) + tproject2 (tproject2 v1)) ; x34 = rsum v33 ; v35 = rreplicate 5 (recip x34) in v35 * v33"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v36 x1 -> let v15 = recip (rreplicate 3 (rscalar 1.0) + exp (negate (rfromVector (fromList [rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 0) (rreplicate 3 (rscalar 7.0)), rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 1) (rreplicate 3 (rscalar 7.0)), rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 2) (rreplicate 3 (rscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1))))) ; v18 = rreshape [4] v15 ; v19 = rreshape [4] v15 ; v20 = rreshape [4] v15 ; v21 = rreshape [4] v15 ; v25 = recip (rreplicate 4 (rscalar 1.0) + exp (negate (rfromVector (fromList [rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 0) v18, rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 1) v19, rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 2) v20, rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 3) v21]) + tproject2 (tproject2 (tproject1 v1))))) ; v28 = rreshape [5] v25 ; v29 = rreshape [5] v25 ; v30 = rreshape [5] v25 ; v31 = rreshape [5] v25 ; v32 = rreshape [5] v25 ; v33 = exp (rfromVector (fromList [rdot0 (rproject (tproject1 (tproject2 v1)) 0) v28, rdot0 (rproject (tproject1 (tproject2 v1)) 1) v29, rdot0 (rproject (tproject1 (tproject2 v1)) 2) v30, rdot0 (rproject (tproject1 (tproject2 v1)) 3) v31, rdot0 (rproject (tproject1 (tproject2 v1)) 4) v32]) + tproject2 (tproject2 v1)) ; x34 = rsum v33 ; v37 = v33 * (rreplicate 5 (negate (recip (x34 * x34)) * rdot0 v33 v36) + rreplicate 5 (recip x34) * v36) ; v38 = rreplicate 5 (v37 ! [4]) ; v39 = rreplicate 5 (v37 ! [3]) ; v40 = rreplicate 5 (v37 ! [2]) ; v41 = rreplicate 5 (v37 ! [1]) ; v42 = rreplicate 5 (v37 ! [0]) ; v43 = (v25 * (rreplicate 4 (rscalar 1.0) - v25)) * (rgather [4] (rproject (tproject1 (tproject2 v1)) 0) (\\[i56] -> [remF i56 5]) * rreshape [4] v42 + rgather [4] (rproject (tproject1 (tproject2 v1)) 1) (\\[i57] -> [remF i57 5]) * rreshape [4] v41 + rgather [4] (rproject (tproject1 (tproject2 v1)) 2) (\\[i58] -> [remF i58 5]) * rreshape [4] v40 + rgather [4] (rproject (tproject1 (tproject2 v1)) 3) (\\[i59] -> [remF i59 5]) * rreshape [4] v39 + rgather [4] (rproject (tproject1 (tproject2 v1)) 4) (\\[i60] -> [remF i60 5]) * rreshape [4] v38) ; v44 = rreplicate 4 (v43 ! [3]) ; v45 = rreplicate 4 (v43 ! [2]) ; v46 = rreplicate 4 (v43 ! [1]) ; v47 = rreplicate 4 (v43 ! [0]) ; v48 = (v15 * (rreplicate 3 (rscalar 1.0) - v15)) * (rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0) (\\[i52] -> [remF i52 4]) * rreshape [3] v47 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1) (\\[i53] -> [remF i53 4]) * rreshape [3] v46 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2) (\\[i54] -> [remF i54 4]) * rreshape [3] v45 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3) (\\[i55] -> [remF i55 4]) * rreshape [3] v44) in tpair (tpair (tpair ([rreplicate 3 (rscalar 7.0) * rreplicate 3 (v48 ! [0]), rreplicate 3 (rscalar 7.0) * rreplicate 3 (v48 ! [1]), rreplicate 3 (rscalar 7.0) * rreplicate 3 (v48 ! [2])], v48), tpair ([v18 * v47, v19 * v46, v20 * v45, v21 * v44], v43)), tpair ([v28 * v42, v29 * v41, v30 * v40, v31 * v39, v32 * v38], v37))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x1 -> let v15 = recip (rreplicate 3 (rscalar 1.0) + exp (negate (rfromVector (fromList [rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 0) (rreplicate 3 (rscalar 7.0)), rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 1) (rreplicate 3 (rscalar 7.0)), rdot0 (rproject (tproject1 (tproject1 (tproject1 v1))) 2) (rreplicate 3 (rscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1))))) ; v25 = recip (rreplicate 4 (rscalar 1.0) + exp (negate (rfromVector (fromList [rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 0) (rreshape [4] v15), rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 1) (rreshape [4] v15), rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 2) (rreshape [4] v15), rdot0 (rproject (tproject1 (tproject2 (tproject1 v1))) 3) (rreshape [4] v15)]) + tproject2 (tproject2 (tproject1 v1))))) ; v33 = exp (rfromVector (fromList [rdot0 (rproject (tproject1 (tproject2 v1)) 0) (rreshape [5] v25), rdot0 (rproject (tproject1 (tproject2 v1)) 1) (rreshape [5] v25), rdot0 (rproject (tproject1 (tproject2 v1)) 2) (rreshape [5] v25), rdot0 (rproject (tproject1 (tproject2 v1)) 3) (rreshape [5] v25), rdot0 (rproject (tproject1 (tproject2 v1)) 4) (rreshape [5] v25)]) + tproject2 (tproject2 v1)) in rreplicate 5 (recip (rsum v33)) * v33"

valsInitVT2OPP :: MnistFcnnRanked2.ADFcnnMnist2Parameters RepN Double
valsInitVT2OPP =
  ( ( RepN $ Nested.rfromListPrimLinear [4, 3] (concat $ replicate 4 [1, 2, 3])
    , RepN $ Nested.rfromListPrimLinear [4] [1, 2, 3, 4] )
  , ( RepN $ Nested.rfromListPrimLinear [5, 4] (concat $ replicate 5 [1, 2, 3, 4])
    , RepN $ Nested.rfromListPrimLinear [5] [1, 2, 3, 4, 5] )
  , ( RepN $ Nested.rfromListPrimLinear [2, 5] (concat $ replicate 2 [1, 2, 3, 4, 5])
    , RepN $ Nested.rfromListPrimLinear [2] [1, 2] ) )

testVT2OPP :: Assertion
testVT2OPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3) stensorKind
                     ((fromPrimal . AstConcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                   (AstTensor AstMethodLet FullSpan) Double
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVT2OPP
  printArtifactPretty renames artifactRev
    @?= "\\v7 x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; m6 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) ; v8 = rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 m1)) * rreplicate 5 v7)) ; m9 = rreplicate 4 (rcast v8) ; v10 = rcast (rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))) * m9))) in tpair (tpair (tpair (rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rreplicate 3 v10), v10), tpair (rtranspose [1,0] (m5 * m9), v8)), tpair (rtranspose [1,0] (m6 * rreplicate 5 v7), v7))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; m6 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) in rsum (m6 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v7 x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; v8 = rsum (tproject1 (tproject2 m1) * rtranspose [1,0] (rreplicate 5 v7)) ; m9 = rreplicate 4 (rcast v8) ; v10 = rcast (rsum (tproject1 (tproject2 (tproject1 m1)) * rtranspose [1,0] m9)) in tpair (tpair (tpair (rreplicate 4 (rreplicate 3 (rscalar 7.0)) * rtranspose [1,0] (rreplicate 3 v10), v10), tpair (rtranspose [1,0] (m5 * m9), v8)), tpair (rreplicate 2 (rcast (rsum (m5 * rgather [4,5] (tproject1 (tproject2 (tproject1 m1))) (\\[i11, i12] -> [i12, i11]))) + tproject2 (tproject2 (tproject1 m1))) * rtranspose [1,0] (rreplicate 5 v7), v7))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rsum (rtranspose [1,0] (rreplicate 2 (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i17, i18] -> [i18, i17])) + tproject2 (tproject2 m1)"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3) stensorKind
                     ((fromPrimal . AstConcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Float))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Float
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Float)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      constant = let ((a1, a2), (a3, a4), (a5, a6)) = valsInitVT2OPP
                 in ( ( AstCastR $ AstFromPrimal $ AstConcrete (FTKR [4, 3] FTKScalar) a1
                      , AstCastR $ AstFromPrimal $ AstConcrete (FTKR [4] FTKScalar) a2 )
                    , ( AstFromPrimal $ AstCastR $ AstConcrete (FTKR [5, 4] FTKScalar) a3
                      , AstFromPrimal $ AstCastR $ AstConcrete (FTKR [5] FTKScalar) a4 )
                    , ( AstCastR $ AstFromPrimal $ AstConcrete (FTKR [2, 5] FTKScalar) a5
                      , AstFromPrimal $ AstCastR $ AstConcrete (FTKR [2] FTKScalar) a6 ) )
      (_, ast3) = funToAst (FTKR (0 :$: ZSR) (FTKScalar @Float))
                           (const $ afcnn2TnonLin constant)
  "\\dummy" ++ " -> " ++ printAstSimple renames ast3
    @?= "\\dummy -> tlet (exp (rsum (rtranspose [1,0] (rreplicate 2 (tlet (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (tlet (rsum (rfromPrimal (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0)))) * rfromPrimal (tconcrete (FTKR [3,4] FTKScalar) (rfromListLinear [3,4] [1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0]))) + rcast (rfromPrimal (tconcrete (FTKR [4] FTKScalar) (rfromListLinear [4] [1.0,2.0,3.0,4.0])))) (\\v3 -> tlet (rfromPrimal (recip (rreplicate 4 (rscalar 1.0) + exp (negate (rprimalPart v3))))) (\\v4 -> rD (rprimalPart v4) (rdualPart (rfromPrimal (rprimalPart v4 * (rreplicate 4 (rscalar 1.0) - rprimalPart v4)) * rD (rreplicate 4 (rscalar 0.0)) (rdualPart v3)))))))) * rfromPrimal (tconcrete (FTKR [4,5] FTKScalar) (rfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0])))) + rfromPrimal (rcast (tconcrete (FTKR [5] FTKScalar) (rfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v6 -> tlet (rfromPrimal (recip (rreplicate 5 (rscalar 1.0) + exp (negate (rprimalPart v6))))) (\\v7 -> rD (rprimalPart v7) (rdualPart (rfromPrimal (rprimalPart v7 * (rreplicate 5 (rscalar 1.0) - rprimalPart v7)) * rD (rreplicate 5 (rscalar 0.0)) (rdualPart v6))))))) * rfromPrimal (tconcrete (FTKR [5,2] FTKScalar) (rfromListLinear [5,2] [1.0,1.0,2.0,2.0,3.0,3.0,4.0,4.0,5.0,5.0]))) + rfromPrimal (rcast (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [1.0,2.0]))))) (\\v9 -> rreplicate 2 (recip (rsum v9)) * v9)"

testVT2OPPNonLin2 :: Assertion
testVT2OPPNonLin2 = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3) stensorKind
                     ((fromPrimal . AstConcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
  let (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVT2OPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v27 x1 -> let v10 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)) ; v11 = exp (negate v10) ; v12 = rreplicate 4 (rscalar 1.0) + v11 ; v13 = recip v12 ; v14 = rreplicate 4 (rscalar 1.0) - v13 ; v15 = v13 * v14 ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v17 = rcast (rsum (m16 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)) ; v18 = exp (negate v17) ; v19 = rreplicate 5 (rscalar 1.0) + v18 ; v20 = recip v19 ; v21 = rreplicate 5 (rscalar 1.0) - v20 ; v22 = v20 * v21 ; m23 = rtranspose [1,0] (rreplicate 2 v20) ; v24 = exp (rsum (m23 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v26 = rreplicate 2 (recip x25) ; v28 = v24 * (rreplicate 2 (negate (recip (x25 * x25)) * rsum (v24 * v27)) + v26 * v27) ; m29 = rreplicate 5 v28 ; v30 = v22 * rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 m1)) * m29)) ; m31 = rreplicate 4 (rcast v30) ; v32 = v15 * rcast (rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))) * m31))) in tpair (tpair (tpair (rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rreplicate 3 v32), v32), tpair (rtranspose [1,0] (m16 * m31), v30)), tpair (rtranspose [1,0] (m23 * m29), v28))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\x1 -> let v10 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)) ; v11 = exp (negate v10) ; v12 = rreplicate 4 (rscalar 1.0) + v11 ; v13 = recip v12 ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v17 = rcast (rsum (m16 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)) ; v18 = exp (negate v17) ; v19 = rreplicate 5 (rscalar 1.0) + v18 ; v20 = recip v19 ; m23 = rtranspose [1,0] (rreplicate 2 v20) ; v24 = exp (rsum (m23 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v26 = rreplicate 2 (recip x25) in v26 * v24"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v27 x1 -> let v13 = recip (rreplicate 4 (rscalar 1.0) + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rgather [3,4] (tproject1 (tproject1 (tproject1 m1))) (\\[i37, i38] -> [i38, i37])) + tproject2 (tproject1 (tproject1 m1))))) ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v20 = recip (rreplicate 5 (rscalar 1.0) + exp (negate (rcast (rsum (m16 * rgather [4,5] (tproject1 (tproject2 (tproject1 m1))) (\\[i35, i36] -> [i36, i35]))) + tproject2 (tproject2 (tproject1 m1))))) ; v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 v20) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i33, i34] -> [i34, i33])) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v28 = v24 * (rreplicate 2 (negate (recip (x25 * x25)) * rdot0 v24 v27) + rreplicate 2 (recip x25) * v27) ; v30 = (v20 * (rreplicate 5 (rscalar 1.0) - v20)) * rsum (tproject1 (tproject2 m1) * rtranspose [1,0] (rreplicate 5 v28)) ; m31 = rreplicate 4 (rcast v30) ; v32 = (v13 * (rreplicate 4 (rscalar 1.0) - v13)) * rcast (rsum (tproject1 (tproject2 (tproject1 m1)) * rtranspose [1,0] m31)) in tpair (tpair (tpair (rreplicate 4 (rreplicate 3 (rscalar 7.0)) * rtranspose [1,0] (rreplicate 3 v32), v32), tpair (rtranspose [1,0] (m16 * m31), v30)), tpair (rreplicate 2 v20 * rtranspose [1,0] (rreplicate 5 v28), v28))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x1 -> let v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 (recip (rreplicate 5 (rscalar 1.0) + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (recip (rreplicate 4 (rscalar 1.0) + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rscalar 7.0))) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)))))))) * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1))))))) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i47, i48] -> [i48, i47])) + tproject2 (tproject2 m1)) in rreplicate 2 (recip (rsum v24)) * v24"
