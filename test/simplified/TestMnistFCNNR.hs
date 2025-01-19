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
  ( ( replicate 3 (RepN $ Nested.rfromList1Prim [1 .. fromIntegral sizeMnistGlyphInt])
    , RepN $ Nested.rfromList1Prim [1, 2, 3] )
  , ( replicate 4 (RepN $ Nested.rfromList1Prim [1, 2, 3])
    , RepN $ Nested.rfromList1Prim [1, 2, 3, 4] )
  , ( replicate 5 (RepN $ Nested.rfromList1Prim [1, 2, 3, 4])
    , RepN $ Nested.rfromList1Prim [1, 2, 3, 4, 5] ) )

testVTOPP :: Assertion
testVTOPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @SizeMnistGlyph) stensorKind
                     ((fromPrimal . tconcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters (AstTensor AstMethodLet FullSpan)
                                                         Double
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T = MnistFcnnRanked1.afcnnMnist1 id id 3 4 blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVTOPP
  printArtifactPretty renames artifactRev
    @?= "\\v6 x1 -> let v4 = sfromVector (fromList [ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 0 * sreplicate (sscalar 7.0)), ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 1 * sreplicate (sscalar 7.0)), ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 2 * sreplicate (sscalar 7.0))]) + sfromR (tproject2 (tproject1 (tproject1 v1))) ; v5 = sfromVector (fromList [ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 0 * v4), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 1 * v4), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 2 * v4), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 3 * v4)]) + sfromR (tproject2 (tproject2 (tproject1 v1))) ; v7 = sreplicate (sfromR v6 !$ [4]) ; v8 = sreplicate (sfromR v6 !$ [3]) ; v9 = sreplicate (sfromR v6 !$ [2]) ; v10 = sreplicate (sfromR v6 !$ [1]) ; v11 = sreplicate (sfromR v6 !$ [0]) ; v12 = sproject (tproject1 (tproject2 v1)) 0 * v11 + sproject (tproject1 (tproject2 v1)) 1 * v10 + sproject (tproject1 (tproject2 v1)) 2 * v9 + sproject (tproject1 (tproject2 v1)) 3 * v8 + sproject (tproject1 (tproject2 v1)) 4 * v7 ; v13 = sreplicate (v12 !$ [3]) ; v14 = sreplicate (v12 !$ [2]) ; v15 = sreplicate (v12 !$ [1]) ; v16 = sreplicate (v12 !$ [0]) ; v17 = sproject (tproject1 (tproject2 (tproject1 v1))) 0 * v16 + sproject (tproject1 (tproject2 (tproject1 v1))) 1 * v15 + sproject (tproject1 (tproject2 (tproject1 v1))) 2 * v14 + sproject (tproject1 (tproject2 (tproject1 v1))) 3 * v13 in tpair (tpair (tpair ([sreplicate (sscalar 7.0) * sreplicate (v17 !$ [0]), sreplicate (sscalar 7.0) * sreplicate (v17 !$ [1]), sreplicate (sscalar 7.0) * sreplicate (v17 !$ [2])], rfromS v17), tpair ([v4 * v16, v4 * v15, v4 * v14, v4 * v13], rfromS v12)), tpair ([v5 * v11, v5 * v10, v5 * v9, v5 * v8, v5 * v7], rfromS (sfromR v6)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let v4 = sfromVector (fromList [ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 0 * sreplicate (sscalar 7.0)), ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 1 * sreplicate (sscalar 7.0)), ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 2 * sreplicate (sscalar 7.0))]) + sfromR (tproject2 (tproject1 (tproject1 v1))) ; v5 = sfromVector (fromList [ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 0 * v4), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 1 * v4), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 2 * v4), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 3 * v4)]) + sfromR (tproject2 (tproject2 (tproject1 v1))) in rfromS (sfromVector (fromList [ssum (sproject (tproject1 (tproject2 v1)) 0 * v5), ssum (sproject (tproject1 (tproject2 v1)) 1 * v5), ssum (sproject (tproject1 (tproject2 v1)) 2 * v5), ssum (sproject (tproject1 (tproject2 v1)) 3 * v5), ssum (sproject (tproject1 (tproject2 v1)) 4 * v5)]) + sfromR (tproject2 (tproject2 v1)))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v6 x1 -> tfromS (let v4 = sfromVector (fromList [sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 0) (sreplicate (sscalar 7.0)), sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 1) (sreplicate (sscalar 7.0)), sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 2) (sreplicate (sscalar 7.0))]) + sfromR (tproject2 (tproject1 (tproject1 v1))) ; v5 = sfromVector (fromList [sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 0) v4, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 1) v4, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 2) v4, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 3) v4]) + sfromR (tproject2 (tproject2 (tproject1 v1))) ; v7 = sreplicate (sfromR v6 !$ [4]) ; v8 = sreplicate (sfromR v6 !$ [3]) ; v9 = sreplicate (sfromR v6 !$ [2]) ; v10 = sreplicate (sfromR v6 !$ [1]) ; v11 = sreplicate (sfromR v6 !$ [0]) ; v12 = sproject (tproject1 (tproject2 v1)) 0 * v11 + sproject (tproject1 (tproject2 v1)) 1 * v10 + sproject (tproject1 (tproject2 v1)) 2 * v9 + sproject (tproject1 (tproject2 v1)) 3 * v8 + sproject (tproject1 (tproject2 v1)) 4 * v7 ; v13 = sreplicate (v12 !$ [3]) ; v14 = sreplicate (v12 !$ [2]) ; v15 = sreplicate (v12 !$ [1]) ; v16 = sreplicate (v12 !$ [0]) ; v17 = sproject (tproject1 (tproject2 (tproject1 v1))) 0 * v16 + sproject (tproject1 (tproject2 (tproject1 v1))) 1 * v15 + sproject (tproject1 (tproject2 (tproject1 v1))) 2 * v14 + sproject (tproject1 (tproject2 (tproject1 v1))) 3 * v13 in tpair (tpair (tpair ([sreplicate (sscalar 7.0) * sreplicate (v17 !$ [0]), sreplicate (sscalar 7.0) * sreplicate (v17 !$ [1]), sreplicate (sscalar 7.0) * sreplicate (v17 !$ [2])], v17), tpair ([v4 * v16, v4 * v15, v4 * v14, v4 * v13], v12)), tpair ([v5 * v11, v5 * v10, v5 * v9, v5 * v8, v5 * v7], v6)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (let v4 = sfromVector (fromList [sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 0) (sreplicate (sscalar 7.0)), sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 1) (sreplicate (sscalar 7.0)), sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 2) (sreplicate (sscalar 7.0))]) + sfromR (tproject2 (tproject1 (tproject1 v1))) ; v5 = sfromVector (fromList [sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 0) v4, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 1) v4, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 2) v4, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 3) v4]) + sfromR (tproject2 (tproject2 (tproject1 v1))) in sfromVector (fromList [sdot0 (sproject (tproject1 (tproject2 v1)) 0) v5, sdot0 (sproject (tproject1 (tproject2 v1)) 1) v5, sdot0 (sproject (tproject1 (tproject2 v1)) 2) v5, sdot0 (sproject (tproject1 (tproject2 v1)) 3) v5, sdot0 (sproject (tproject1 (tproject2 v1)) 4) v5]) + sfromR (tproject2 (tproject2 v1)))"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @SizeMnistGlyph) stensorKind
                     ((fromPrimal . tconcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                         (AstTensor AstMethodLet FullSpan) Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMax1 3 4 blackGlyph
      (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVTOPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v24 x1 -> let v9 = sfromVector (fromList [ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 0 * sfromR (rreplicate 784 (rfromS (sscalar 7.0)))), ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 1 * sfromR (rreplicate 784 (rfromS (sscalar 7.0)))), ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 2 * sfromR (rreplicate 784 (rfromS (sscalar 7.0))))]) + sfromR (tproject2 (tproject1 (tproject1 v1))) ; v10 = exp (negate v9) ; v11 = sreplicate (sscalar 1.0) + v10 ; v12 = recip v11 ; v13 = sreplicate (sscalar 1.0) - v12 ; v14 = v12 * v13 ; v15 = sfromVector (fromList [ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 0 * v12), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 1 * v12), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 2 * v12), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 3 * v12)]) + sfromR (tproject2 (tproject2 (tproject1 v1))) ; v16 = exp (negate v15) ; v17 = sreplicate (sscalar 1.0) + v16 ; v18 = recip v17 ; v19 = sreplicate (sscalar 1.0) - v18 ; v20 = v18 * v19 ; v21 = exp (sfromVector (fromList [ssum (sproject (tproject1 (tproject2 v1)) 0 * v18), ssum (sproject (tproject1 (tproject2 v1)) 1 * v18), ssum (sproject (tproject1 (tproject2 v1)) 2 * v18), ssum (sproject (tproject1 (tproject2 v1)) 3 * v18), ssum (sproject (tproject1 (tproject2 v1)) 4 * v18)]) + sfromR (tproject2 (tproject2 v1))) ; x22 = ssum v21 ; v23 = sreplicate (recip x22) ; v25 = v21 * (sreplicate (negate (recip (x22 * x22)) * ssum (v21 * sfromR v24)) + v23 * sfromR v24) ; v26 = sreplicate (v25 !$ [4]) ; v27 = sreplicate (v25 !$ [3]) ; v28 = sreplicate (v25 !$ [2]) ; v29 = sreplicate (v25 !$ [1]) ; v30 = sreplicate (v25 !$ [0]) ; v31 = v20 * (sproject (tproject1 (tproject2 v1)) 0 * v30 + sproject (tproject1 (tproject2 v1)) 1 * v29 + sproject (tproject1 (tproject2 v1)) 2 * v28 + sproject (tproject1 (tproject2 v1)) 3 * v27 + sproject (tproject1 (tproject2 v1)) 4 * v26) ; v32 = sreplicate (v31 !$ [3]) ; v33 = sreplicate (v31 !$ [2]) ; v34 = sreplicate (v31 !$ [1]) ; v35 = sreplicate (v31 !$ [0]) ; v36 = v14 * (sproject (tproject1 (tproject2 (tproject1 v1))) 0 * v35 + sproject (tproject1 (tproject2 (tproject1 v1))) 1 * v34 + sproject (tproject1 (tproject2 (tproject1 v1))) 2 * v33 + sproject (tproject1 (tproject2 (tproject1 v1))) 3 * v32) ; v37 = sreplicate (v36 !$ [2]) ; v38 = sreplicate (v36 !$ [1]) ; v39 = sreplicate (v36 !$ [0]) in tpair (tpair (tpair ([sfromR (rreplicate 784 (rfromS (sscalar 7.0))) * v39, sfromR (rreplicate 784 (rfromS (sscalar 7.0))) * v38, sfromR (rreplicate 784 (rfromS (sscalar 7.0))) * v37], rfromS v36), tpair ([v12 * v35, v12 * v34, v12 * v33, v12 * v32], rfromS v31)), tpair ([v18 * v30, v18 * v29, v18 * v28, v18 * v27, v18 * v26], rfromS v25))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\x1 -> let v9 = sfromVector (fromList [ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 0 * sfromR (rreplicate 784 (rfromS (sscalar 7.0)))), ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 1 * sfromR (rreplicate 784 (rfromS (sscalar 7.0)))), ssum (sproject (tproject1 (tproject1 (tproject1 v1))) 2 * sfromR (rreplicate 784 (rfromS (sscalar 7.0))))]) + sfromR (tproject2 (tproject1 (tproject1 v1))) ; v10 = exp (negate v9) ; v11 = sreplicate (sscalar 1.0) + v10 ; v12 = recip v11 ; v15 = sfromVector (fromList [ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 0 * v12), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 1 * v12), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 2 * v12), ssum (sproject (tproject1 (tproject2 (tproject1 v1))) 3 * v12)]) + sfromR (tproject2 (tproject2 (tproject1 v1))) ; v16 = exp (negate v15) ; v17 = sreplicate (sscalar 1.0) + v16 ; v18 = recip v17 ; v21 = exp (sfromVector (fromList [ssum (sproject (tproject1 (tproject2 v1)) 0 * v18), ssum (sproject (tproject1 (tproject2 v1)) 1 * v18), ssum (sproject (tproject1 (tproject2 v1)) 2 * v18), ssum (sproject (tproject1 (tproject2 v1)) 3 * v18), ssum (sproject (tproject1 (tproject2 v1)) 4 * v18)]) + sfromR (tproject2 (tproject2 v1))) ; x22 = ssum v21 ; v23 = sreplicate (recip x22) in rfromS (v23 * v21)"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v24 x1 -> tfromS (let v12 = recip (sreplicate (sscalar 1.0) + exp (negate (sfromVector (fromList [sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 0) (sreplicate (sscalar 7.0)), sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 1) (sreplicate (sscalar 7.0)), sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 2) (sreplicate (sscalar 7.0))]) + sfromR (tproject2 (tproject1 (tproject1 v1)))))) ; v18 = recip (sreplicate (sscalar 1.0) + exp (negate (sfromVector (fromList [sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 0) v12, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 1) v12, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 2) v12, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 3) v12]) + sfromR (tproject2 (tproject2 (tproject1 v1)))))) ; v21 = exp (sfromVector (fromList [sdot0 (sproject (tproject1 (tproject2 v1)) 0) v18, sdot0 (sproject (tproject1 (tproject2 v1)) 1) v18, sdot0 (sproject (tproject1 (tproject2 v1)) 2) v18, sdot0 (sproject (tproject1 (tproject2 v1)) 3) v18, sdot0 (sproject (tproject1 (tproject2 v1)) 4) v18]) + sfromR (tproject2 (tproject2 v1))) ; x22 = ssum v21 ; v25 = v21 * (sreplicate (negate (recip (x22 * x22)) * sdot0 v21 (sfromR v24)) + sreplicate (recip x22) * sfromR v24) ; v26 = sreplicate (v25 !$ [4]) ; v27 = sreplicate (v25 !$ [3]) ; v28 = sreplicate (v25 !$ [2]) ; v29 = sreplicate (v25 !$ [1]) ; v30 = sreplicate (v25 !$ [0]) ; v31 = (v18 * (sreplicate (sscalar 1.0) - v18)) * (sproject (tproject1 (tproject2 v1)) 0 * v30 + sproject (tproject1 (tproject2 v1)) 1 * v29 + sproject (tproject1 (tproject2 v1)) 2 * v28 + sproject (tproject1 (tproject2 v1)) 3 * v27 + sproject (tproject1 (tproject2 v1)) 4 * v26) ; v32 = sreplicate (v31 !$ [3]) ; v33 = sreplicate (v31 !$ [2]) ; v34 = sreplicate (v31 !$ [1]) ; v35 = sreplicate (v31 !$ [0]) ; v36 = (v12 * (sreplicate (sscalar 1.0) - v12)) * (sproject (tproject1 (tproject2 (tproject1 v1))) 0 * v35 + sproject (tproject1 (tproject2 (tproject1 v1))) 1 * v34 + sproject (tproject1 (tproject2 (tproject1 v1))) 2 * v33 + sproject (tproject1 (tproject2 (tproject1 v1))) 3 * v32) in tpair (tpair (tpair ([sreplicate (sscalar 7.0) * sreplicate (v36 !$ [0]), sreplicate (sscalar 7.0) * sreplicate (v36 !$ [1]), sreplicate (sscalar 7.0) * sreplicate (v36 !$ [2])], v36), tpair ([v12 * v35, v12 * v34, v12 * v33, v12 * v32], v31)), tpair ([v18 * v30, v18 * v29, v18 * v28, v18 * v27, v18 * v26], v25)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x1 -> rfromS (let v12 = recip (sreplicate (sscalar 1.0) + exp (negate (sfromVector (fromList [sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 0) (sreplicate (sscalar 7.0)), sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 1) (sreplicate (sscalar 7.0)), sdot0 (sproject (tproject1 (tproject1 (tproject1 v1))) 2) (sreplicate (sscalar 7.0))]) + sfromR (tproject2 (tproject1 (tproject1 v1)))))) ; v18 = recip (sreplicate (sscalar 1.0) + exp (negate (sfromVector (fromList [sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 0) v12, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 1) v12, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 2) v12, sdot0 (sproject (tproject1 (tproject2 (tproject1 v1))) 3) v12]) + sfromR (tproject2 (tproject2 (tproject1 v1)))))) ; v21 = exp (sfromVector (fromList [sdot0 (sproject (tproject1 (tproject2 v1)) 0) v18, sdot0 (sproject (tproject1 (tproject2 v1)) 1) v18, sdot0 (sproject (tproject1 (tproject2 v1)) 2) v18, sdot0 (sproject (tproject1 (tproject2 v1)) 3) v18, sdot0 (sproject (tproject1 (tproject2 v1)) 4) v18]) + sfromR (tproject2 (tproject2 v1))) in sreplicate (recip (ssum v21)) * v21)"

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
      blackGlyph = treplicate (SNat @3) stensorKind
                     ((fromPrimal . tconcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                   (AstTensor AstMethodLet FullSpan) Double
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVT2OPP
  printArtifactPretty renames artifactRev
    @?= "\\v7 x1 -> let m5 = stranspose (sreplicate (scast (ssum (stranspose (sreplicate (sreplicate (sscalar 7.0))) * stranspose (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = stranspose (sreplicate (scast (ssum (m5 * stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v8 = ssum (stranspose (stranspose (sfromR (tproject1 (tproject2 m1))) * sreplicate (sfromR v7))) ; m9 = sreplicate (scast v8) ; v10 = scast (ssum (stranspose (stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m9))) in tpair (tpair (tpair (rfromS (stranspose (stranspose (sreplicate (sreplicate (sscalar 7.0))) * sreplicate v10)), rfromS v10), tpair (rfromS (stranspose (m5 * m9)), rfromS v8)), tpair (rfromS (stranspose (m6 * sreplicate (sfromR v7))), rfromS (sfromR v7)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let m5 = stranspose (sreplicate (scast (ssum (stranspose (sreplicate (sreplicate (sscalar 7.0))) * stranspose (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = stranspose (sreplicate (scast (ssum (m5 * stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in rfromS (ssum (m6 * stranspose (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1)))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v7 x1 -> tfromS (let m5 = stranspose (sreplicate (scast (ssum (stranspose (sreplicate (sreplicate (sscalar 7.0))) * stranspose (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v8 = ssum (sfromR (tproject1 (tproject2 m1)) * stranspose (sreplicate (sfromR v7))) ; m9 = sreplicate (scast v8) ; v10 = scast (ssum (sfromR (tproject1 (tproject2 (tproject1 m1))) * stranspose m9)) in tpair (tpair (tpair (sreplicate (sreplicate (sscalar 7.0)) * stranspose (sreplicate v10), v10), tpair (stranspose (m5 * m9), v8)), tpair (sreplicate (scast (ssum (m5 * stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * stranspose (sreplicate (sfromR v7)), v7)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (ssum (stranspose (sreplicate (scast (ssum (stranspose (sreplicate (scast (ssum (stranspose (sreplicate (sreplicate (sscalar 7.0))) * stranspose (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) * stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) * stranspose (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1)))"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @3) stensorKind
                     ((fromPrimal . tconcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Float))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Float
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Float)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      constant = let ((a1, a2), (a3, a4), (a5, a6)) = valsInitVT2OPP
                 in ( ( rcast $ fromPrimal $ tconcrete (FTKR [4, 3] FTKScalar) a1
                      , rcast $ fromPrimal $ tconcrete (FTKR [4] FTKScalar) a2 )
                    , ( fromPrimal $ rcast $ tconcrete (FTKR [5, 4] FTKScalar) a3
                      , fromPrimal $ rcast $ tconcrete (FTKR [5] FTKScalar) a4 )
                    , ( rcast $ fromPrimal $ tconcrete (FTKR [2, 5] FTKScalar) a5
                      , fromPrimal $ rcast $ tconcrete (FTKR [2] FTKScalar) a6 ) )
      (_, ast3) = funToAst (FTKR (0 :$: ZSR) (FTKScalar @Float))
                           (const $ afcnn2TnonLin constant)
  "\\dummy" ++ " -> " ++ printAstSimple renames ast3
    @?= "\\dummy -> rfromS (tlet (exp (ssum (stranspose (sreplicate (tlet (scast (ssum (stranspose (sreplicate (scast (tlet (ssum (sfromPrimal (stranspose (sreplicate (sreplicate (sscalar 7.0)))) * sfromPrimal (tconcrete (FTKS [3,4] FTKScalar) (sfromListLinear [3,4] [1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0]))) + sfromPrimal (tconcrete (FTKS [4] FTKScalar) (sfromListLinear [4] [1.0,2.0,3.0,4.0]))) (\\v3 -> tlet (sfromPrimal (recip (sreplicate (sscalar 1.0) + exp (negate (sprimalPart v3))))) (\\v4 -> sD (sprimalPart v4) (sdualPart (sfromPrimal (sprimalPart v4 * (sreplicate (sscalar 1.0) - sprimalPart v4)) * sfromR (rD (rfromS (sreplicate (sscalar 0.0))) (rfromS (sdualPart v3)))))))))) * sfromPrimal (tconcrete (FTKS [4,5] FTKScalar) (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0])))) + sfromPrimal (tconcrete (FTKS [5] FTKScalar) (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0]))) (\\v6 -> tlet (sfromPrimal (recip (sreplicate (sscalar 1.0) + exp (negate (sprimalPart v6))))) (\\v7 -> sD (sprimalPart v7) (sdualPart (sfromPrimal (sprimalPart v7 * (sreplicate (sscalar 1.0) - sprimalPart v7)) * sfromR (rD (rfromS (sreplicate (sscalar 0.0))) (rfromS (sdualPart v6))))))))) * sfromPrimal (tconcrete (FTKS [5,2] FTKScalar) (sfromListLinear [5,2] [1.0,1.0,2.0,2.0,3.0,3.0,4.0,4.0,5.0,5.0]))) + sfromPrimal (tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [1.0,2.0])))) (\\v9 -> sreplicate (recip (ssum v9)) * v9))"

testVT2OPPNonLin2 :: Assertion
testVT2OPPNonLin2 = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @3) stensorKind
                     ((fromPrimal . tconcrete (FTKR ZSR FTKScalar)) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
  let (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVT2OPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v27 x1 -> let v10 = ssum (stranspose (sreplicate (sreplicate (sscalar 7.0))) * stranspose (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sreplicate (sscalar 1.0) + v11 ; v13 = recip v12 ; v14 = sreplicate (sscalar 1.0) - v13 ; v15 = v13 * v14 ; m16 = stranspose (sreplicate (scast v13)) ; v17 = scast (ssum (m16 * stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sreplicate (sscalar 1.0) + v18 ; v20 = recip v19 ; v21 = sreplicate (sscalar 1.0) - v20 ; v22 = v20 * v21 ; m23 = stranspose (sreplicate v20) ; v24 = exp (ssum (m23 * stranspose (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum v24 ; v26 = sreplicate (recip x25) ; v28 = v24 * (sreplicate (negate (recip (x25 * x25)) * ssum (v24 * sfromR v27)) + v26 * sfromR v27) ; m29 = sreplicate v28 ; v30 = v22 * ssum (stranspose (stranspose (sfromR (tproject1 (tproject2 m1))) * m29)) ; m31 = sreplicate (scast v30) ; v32 = v15 * scast (ssum (stranspose (stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m31))) in tpair (tpair (tpair (rfromS (stranspose (stranspose (sreplicate (sreplicate (sscalar 7.0))) * sreplicate v32)), rfromS v32), tpair (rfromS (stranspose (m16 * m31)), rfromS v30)), tpair (rfromS (stranspose (m23 * m29)), rfromS v28))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\x1 -> let v10 = ssum (stranspose (sreplicate (sreplicate (sscalar 7.0))) * stranspose (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sreplicate (sscalar 1.0) + v11 ; v13 = recip v12 ; m16 = stranspose (sreplicate (scast v13)) ; v17 = scast (ssum (m16 * stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sreplicate (sscalar 1.0) + v18 ; v20 = recip v19 ; m23 = stranspose (sreplicate v20) ; v24 = exp (ssum (m23 * stranspose (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum v24 ; v26 = sreplicate (recip x25) in rfromS (v26 * v24)"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v27 x1 -> tfromS (let v13 = recip (sreplicate (sscalar 1.0) + exp (negate (ssum (stranspose (sreplicate (sreplicate (sscalar 7.0))) * stranspose (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m16 = stranspose (sreplicate (scast v13)) ; v20 = recip (sreplicate (sscalar 1.0) + exp (negate (scast (ssum (m16 * stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v24 = exp (ssum (stranspose (sreplicate v20) * stranspose (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum v24 ; v28 = v24 * (sreplicate (negate (recip (x25 * x25)) * sdot0 v24 (sfromR v27)) + sreplicate (recip x25) * sfromR v27) ; v30 = (v20 * (sreplicate (sscalar 1.0) - v20)) * ssum (sfromR (tproject1 (tproject2 m1)) * stranspose (sreplicate v28)) ; m31 = sreplicate (scast v30) ; v32 = (v13 * (sreplicate (sscalar 1.0) - v13)) * scast (ssum (sfromR (tproject1 (tproject2 (tproject1 m1))) * stranspose m31)) in tpair (tpair (tpair (sreplicate (sreplicate (sscalar 7.0)) * stranspose (sreplicate v32), v32), tpair (stranspose (m16 * m31), v30)), tpair (sreplicate v20 * stranspose (sreplicate v28), v28)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x1 -> rfromS (let v24 = exp (ssum (stranspose (sreplicate (recip (sreplicate (sscalar 1.0) + exp (negate (scast (ssum (stranspose (sreplicate (scast (recip (sreplicate (sscalar 1.0) + exp (negate (ssum (stranspose (sreplicate (sreplicate (sscalar 7.0))) * stranspose (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))))))))) * stranspose (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))))))) * stranspose (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) in sreplicate (recip (ssum v24)) * v24)"
