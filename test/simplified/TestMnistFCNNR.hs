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
         funToAstIO (FTKR (singletonShape sizeMnistGlyphInt) FTKScalar) id
       (varLabel, astLabel) <-
         funToAstIO (FTKR (singletonShape sizeMnistLabelInt) FTKScalar) id
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
         funToAstIO (FTKR (singletonShape sizeMnistGlyphInt) FTKScalar) id
       (varLabel, astLabel) <-
         funToAstIO (FTKR (singletonShape sizeMnistLabelInt) FTKScalar) id
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
  , ( replicate 4 (RepN $ Nested.rfromList1Prim [1, 2, 3, 4])
    , RepN $ Nested.rfromList1Prim [1, 2, 3, 4] )
  , ( replicate 5 (RepN $ Nested.rfromList1Prim [1, 2, 3, 4, 5])
    , RepN $ Nested.rfromList1Prim [1, 2, 3, 4, 5] ) )

testVTOPP :: Assertion
testVTOPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @SizeMnistGlyph)
                     ((fromPrimal . AstConcrete) (Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters (AstTensor AstMethodLet FullSpan)
                                                         Double
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T = MnistFcnnRanked1.afcnnMnist1 id id 3 4 blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVTOPP
  printArtifactPretty renames artifactRev
    @?= "\\v15 x1 -> let v4 = rfromVector (fromList [rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0)), rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0)), rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = rreshape [4] v4 ; v6 = rreshape [4] v4 ; v7 = rreshape [4] v4 ; v8 = rreshape [4] v4 ; v9 = rfromVector (fromList [rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v5)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v6)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v7)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v8))]) + tproject2 (tproject2 (tproject1 v1)) ; v10 = rreshape [5] v9 ; v11 = rreshape [5] v9 ; v12 = rreshape [5] v9 ; v13 = rreshape [5] v9 ; v14 = rreshape [5] v9 ; x16 = v15 ! [4] ; x17 = v15 ! [3] ; x18 = v15 ! [2] ; x19 = v15 ! [1] ; x20 = v15 ! [0] ; v21 = rreshape [4] (rproject (tproject1 (tproject2 v1)) 0 * rreshape [5] (rreplicate 5 x20)) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 1 * rreshape [5] (rreplicate 5 x19)) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 2 * rreshape [5] (rreplicate 5 x18)) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 3 * rreshape [5] (rreplicate 5 x17)) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 4 * rreshape [5] (rreplicate 5 x16)) ; x22 = v21 ! [3] ; x23 = v21 ! [2] ; x24 = v21 ! [1] ; x25 = v21 ! [0] ; v26 = rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * rreshape [4] (rreplicate 4 x25)) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * rreshape [4] (rreplicate 4 x24)) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * rreshape [4] (rreplicate 4 x23)) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * rreshape [4] (rreplicate 4 x22)) ; x27 = v26 ! [2] ; x28 = v26 ! [1] ; x29 = v26 ! [0] in tpair (tpair (tpair ([rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x29), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x28), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x27)], v26), tpair ([v5 * rreshape [4] (rreplicate 4 x25), v6 * rreshape [4] (rreplicate 4 x24), v7 * rreshape [4] (rreplicate 4 x23), v8 * rreshape [4] (rreplicate 4 x22)], v21)), tpair ([v10 * rreshape [5] (rreplicate 5 x20), v11 * rreshape [5] (rreplicate 5 x19), v12 * rreshape [5] (rreplicate 5 x18), v13 * rreshape [5] (rreplicate 5 x17), v14 * rreshape [5] (rreplicate 5 x16)], v15))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let v4 = rfromVector (fromList [rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0)), rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0)), rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = rreshape [4] v4 ; v6 = rreshape [4] v4 ; v7 = rreshape [4] v4 ; v8 = rreshape [4] v4 ; v9 = rfromVector (fromList [rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v5)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v6)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v7)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v8))]) + tproject2 (tproject2 (tproject1 v1)) ; v10 = rreshape [5] v9 ; v11 = rreshape [5] v9 ; v12 = rreshape [5] v9 ; v13 = rreshape [5] v9 ; v14 = rreshape [5] v9 in rfromVector (fromList [rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 0 * v10)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 1 * v11)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 2 * v12)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 3 * v13)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 4 * v14))]) + tproject2 (tproject2 v1)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v15 x1 -> let v4 = rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0)]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = rreshape [4] v4 ; v6 = rreshape [4] v4 ; v7 = rreshape [4] v4 ; v8 = rreshape [4] v4 ; v9 = rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v5), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v6), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v7), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v8)]) + tproject2 (tproject2 (tproject1 v1)) ; x16 = v15 ! [4] ; x17 = v15 ! [3] ; x18 = v15 ! [2] ; x19 = v15 ! [1] ; x20 = v15 ! [0] ; v21 = rgather [4] (rproject (tproject1 (tproject2 v1)) 0) (\\[i38] -> [remF i38 5]) * rreplicate 4 x20 + rgather [4] (rproject (tproject1 (tproject2 v1)) 1) (\\[i40] -> [remF i40 5]) * rreplicate 4 x19 + rgather [4] (rproject (tproject1 (tproject2 v1)) 2) (\\[i42] -> [remF i42 5]) * rreplicate 4 x18 + rgather [4] (rproject (tproject1 (tproject2 v1)) 3) (\\[i44] -> [remF i44 5]) * rreplicate 4 x17 + rgather [4] (rproject (tproject1 (tproject2 v1)) 4) (\\[i46] -> [remF i46 5]) * rreplicate 4 x16 ; x22 = v21 ! [3] ; x23 = v21 ! [2] ; x24 = v21 ! [1] ; x25 = v21 ! [0] ; v26 = rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0) (\\[i30] -> [remF i30 4]) * rreplicate 3 x25 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1) (\\[i32] -> [remF i32 4]) * rreplicate 3 x24 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2) (\\[i34] -> [remF i34 4]) * rreplicate 3 x23 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3) (\\[i36] -> [remF i36 4]) * rreplicate 3 x22 in tpair (tpair (tpair ([rreplicate 3 7.0 * rreplicate 3 (v26 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v26 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v26 ! [2])], v26), tpair ([v5 * rreplicate 4 x25, v6 * rreplicate 4 x24, v7 * rreplicate 4 x23, v8 * rreplicate 4 x22], v21)), tpair ([rreshape [5] v9 * rreplicate 5 x20, rreshape [5] v9 * rreplicate 5 x19, rreshape [5] v9 * rreplicate 5 x18, rreshape [5] v9 * rreplicate 5 x17, rreshape [5] v9 * rreplicate 5 x16], v15))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let v4 = rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0)]) + tproject2 (tproject1 (tproject1 v1)) ; v9 = rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * rreshape [4] v4), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * rreshape [4] v4), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * rreshape [4] v4), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * rreshape [4] v4)]) + tproject2 (tproject2 (tproject1 v1)) in rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * rreshape [5] v9), rsum (rproject (tproject1 (tproject2 v1)) 1 * rreshape [5] v9), rsum (rproject (tproject1 (tproject2 v1)) 2 * rreshape [5] v9), rsum (rproject (tproject1 (tproject2 v1)) 3 * rreshape [5] v9), rsum (rproject (tproject1 (tproject2 v1)) 4 * rreshape [5] v9)]) + tproject2 (tproject2 v1)"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @SizeMnistGlyph)
                     ((fromPrimal . AstConcrete) (Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                         (AstTensor AstMethodLet FullSpan) Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logistic softMax1 3 4 blackGlyph
      (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVTOPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v33 x1 -> let v9 = rfromVector (fromList [rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0)), rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0)), rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = rreplicate 3 1.0 + v10 ; v12 = recip v11 ; v13 = rreplicate 3 1.0 - v12 ; v14 = v12 * v13 ; v15 = rreshape [4] v12 ; v16 = rreshape [4] v12 ; v17 = rreshape [4] v12 ; v18 = rreshape [4] v12 ; v19 = rfromVector (fromList [rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v15)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v16)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v17)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v18))]) + tproject2 (tproject2 (tproject1 v1)) ; v20 = exp (negate v19) ; v21 = rreplicate 4 1.0 + v20 ; v22 = recip v21 ; v23 = rreplicate 4 1.0 - v22 ; v24 = v22 * v23 ; v25 = rreshape [5] v22 ; v26 = rreshape [5] v22 ; v27 = rreshape [5] v22 ; v28 = rreshape [5] v22 ; v29 = rreshape [5] v22 ; v30 = exp (rfromVector (fromList [rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 0 * v25)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 1 * v26)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 2 * v27)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 3 * v28)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 4 * v29))]) + tproject2 (tproject2 v1)) ; x31 = rsum v30 ; v32 = rreplicate 5 (recip x31) ; v34 = v30 * (rreplicate 5 (negate (recip (x31 * x31)) * rsum (v30 * v33)) + v32 * v33) ; x35 = v34 ! [4] ; x36 = v34 ! [3] ; x37 = v34 ! [2] ; x38 = v34 ! [1] ; x39 = v34 ! [0] ; v40 = v24 * (rreshape [4] (rproject (tproject1 (tproject2 v1)) 0 * rreshape [5] (rreplicate 5 x39)) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 1 * rreshape [5] (rreplicate 5 x38)) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 2 * rreshape [5] (rreplicate 5 x37)) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 3 * rreshape [5] (rreplicate 5 x36)) + rreshape [4] (rproject (tproject1 (tproject2 v1)) 4 * rreshape [5] (rreplicate 5 x35))) ; x41 = v40 ! [3] ; x42 = v40 ! [2] ; x43 = v40 ! [1] ; x44 = v40 ! [0] ; v45 = v14 * (rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * rreshape [4] (rreplicate 4 x44)) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * rreshape [4] (rreplicate 4 x43)) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * rreshape [4] (rreplicate 4 x42)) + rreshape [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * rreshape [4] (rreplicate 4 x41))) ; x46 = v45 ! [2] ; x47 = v45 ! [1] ; x48 = v45 ! [0] in tpair (tpair (tpair ([rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x48), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x47), rreplicate 3 7.0 * rreshape [3] (rreplicate 3 x46)], v45), tpair ([v15 * rreshape [4] (rreplicate 4 x44), v16 * rreshape [4] (rreplicate 4 x43), v17 * rreshape [4] (rreplicate 4 x42), v18 * rreshape [4] (rreplicate 4 x41)], v40)), tpair ([v25 * rreshape [5] (rreplicate 5 x39), v26 * rreshape [5] (rreplicate 5 x38), v27 * rreshape [5] (rreplicate 5 x37), v28 * rreshape [5] (rreplicate 5 x36), v29 * rreshape [5] (rreplicate 5 x35)], v34))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\x1 -> let v9 = rfromVector (fromList [rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0)), rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0)), rsum (rreshape [3] (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = rreplicate 3 1.0 + v10 ; v12 = recip v11 ; v15 = rreshape [4] v12 ; v16 = rreshape [4] v12 ; v17 = rreshape [4] v12 ; v18 = rreshape [4] v12 ; v19 = rfromVector (fromList [rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v15)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v16)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v17)), rsum (rreshape [4] (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v18))]) + tproject2 (tproject2 (tproject1 v1)) ; v20 = exp (negate v19) ; v21 = rreplicate 4 1.0 + v20 ; v22 = recip v21 ; v25 = rreshape [5] v22 ; v26 = rreshape [5] v22 ; v27 = rreshape [5] v22 ; v28 = rreshape [5] v22 ; v29 = rreshape [5] v22 ; v30 = exp (rfromVector (fromList [rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 0 * v25)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 1 * v26)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 2 * v27)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 3 * v28)), rsum (rreshape [5] (rproject (tproject1 (tproject2 v1)) 4 * v29))]) + tproject2 (tproject2 v1)) ; x31 = rsum v30 ; v32 = rreplicate 5 (recip x31) in v32 * v30"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v33 x1 -> let v12 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0)]) + tproject2 (tproject1 (tproject1 v1))))) ; v15 = rreshape [4] v12 ; v16 = rreshape [4] v12 ; v17 = rreshape [4] v12 ; v18 = rreshape [4] v12 ; v22 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * v15), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * v16), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * v17), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * v18)]) + tproject2 (tproject2 (tproject1 v1))))) ; v25 = rreshape [5] v22 ; v26 = rreshape [5] v22 ; v27 = rreshape [5] v22 ; v28 = rreshape [5] v22 ; v29 = rreshape [5] v22 ; v30 = exp (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * v25), rsum (rproject (tproject1 (tproject2 v1)) 1 * v26), rsum (rproject (tproject1 (tproject2 v1)) 2 * v27), rsum (rproject (tproject1 (tproject2 v1)) 3 * v28), rsum (rproject (tproject1 (tproject2 v1)) 4 * v29)]) + tproject2 (tproject2 v1)) ; x31 = rsum v30 ; v34 = v30 * (rreplicate 5 (negate (recip (x31 * x31)) * rsum (v30 * v33)) + rreplicate 5 (recip x31) * v33) ; x35 = v34 ! [4] ; x36 = v34 ! [3] ; x37 = v34 ! [2] ; x38 = v34 ! [1] ; x39 = v34 ! [0] ; v40 = (v22 * (rreplicate 4 1.0 - v22)) * (rgather [4] (rproject (tproject1 (tproject2 v1)) 0) (\\[i57] -> [remF i57 5]) * rreplicate 4 x39 + rgather [4] (rproject (tproject1 (tproject2 v1)) 1) (\\[i59] -> [remF i59 5]) * rreplicate 4 x38 + rgather [4] (rproject (tproject1 (tproject2 v1)) 2) (\\[i61] -> [remF i61 5]) * rreplicate 4 x37 + rgather [4] (rproject (tproject1 (tproject2 v1)) 3) (\\[i63] -> [remF i63 5]) * rreplicate 4 x36 + rgather [4] (rproject (tproject1 (tproject2 v1)) 4) (\\[i65] -> [remF i65 5]) * rreplicate 4 x35) ; x41 = v40 ! [3] ; x42 = v40 ! [2] ; x43 = v40 ! [1] ; x44 = v40 ! [0] ; v45 = (v12 * (rreplicate 3 1.0 - v12)) * (rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 0) (\\[i49] -> [remF i49 4]) * rreplicate 3 x44 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 1) (\\[i51] -> [remF i51 4]) * rreplicate 3 x43 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 2) (\\[i53] -> [remF i53 4]) * rreplicate 3 x42 + rgather [3] (rproject (tproject1 (tproject2 (tproject1 v1))) 3) (\\[i55] -> [remF i55 4]) * rreplicate 3 x41) in tpair (tpair (tpair ([rreplicate 3 7.0 * rreplicate 3 (v45 ! [0]), rreplicate 3 7.0 * rreplicate 3 (v45 ! [1]), rreplicate 3 7.0 * rreplicate 3 (v45 ! [2])], v45), tpair ([v15 * rreplicate 4 x44, v16 * rreplicate 4 x43, v17 * rreplicate 4 x42, v18 * rreplicate 4 x41], v40)), tpair ([v25 * rreplicate 5 x39, v26 * rreplicate 5 x38, v27 * rreplicate 5 x37, v28 * rreplicate 5 x36, v29 * rreplicate 5 x35], v34))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x1 -> let v12 = recip (rreplicate 3 1.0 + exp (negate (rfromVector (fromList [rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 0 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 1 * rreplicate 3 7.0), rsum (rproject (tproject1 (tproject1 (tproject1 v1))) 2 * rreplicate 3 7.0)]) + tproject2 (tproject1 (tproject1 v1))))) ; v22 = recip (rreplicate 4 1.0 + exp (negate (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 0 * rreshape [4] v12), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 1 * rreshape [4] v12), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 2 * rreshape [4] v12), rsum (rproject (tproject1 (tproject2 (tproject1 v1))) 3 * rreshape [4] v12)]) + tproject2 (tproject2 (tproject1 v1))))) ; v30 = exp (rfromVector (fromList [rsum (rproject (tproject1 (tproject2 v1)) 0 * rreshape [5] v22), rsum (rproject (tproject1 (tproject2 v1)) 1 * rreshape [5] v22), rsum (rproject (tproject1 (tproject2 v1)) 2 * rreshape [5] v22), rsum (rproject (tproject1 (tproject2 v1)) 3 * rreshape [5] v22), rsum (rproject (tproject1 (tproject2 v1)) 4 * rreshape [5] v22)]) + tproject2 (tproject2 v1)) in rreplicate 5 (recip (rsum v30)) * v30"

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
      blackGlyph = AstReplicate (SNat @3)
                     ((fromPrimal . AstConcrete) (Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                   (AstTensor AstMethodLet FullSpan) Double
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInitVT2OPP
  printArtifactPretty renames artifactRev
    @?= "\\v7 x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; m6 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) ; v8 = rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 m1)) * rreplicate 5 v7)) ; m9 = rreplicate 4 (rcast v8) ; v10 = rcast (rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))) * m9))) ; m11 = rreplicate 3 v10 in tpair (tpair (tpair (rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m11), v10), tpair (rtranspose [1,0] (m5 * m9), v8)), tpair (rtranspose [1,0] (m6 * rreplicate 5 v7), v7))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; m6 = rtranspose [1,0] (rreplicate 2 (rcast (rsum (m5 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) in rsum (m6 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v7 x1 -> let m5 = rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) ; v8 = rsum (tproject1 (tproject2 m1) * rtranspose [1,0] (rreplicate 5 v7)) ; m9 = rreplicate 4 (rcast v8) ; v10 = rcast (rsum (tproject1 (tproject2 (tproject1 m1)) * rtranspose [1,0] m9)) in tpair (tpair (tpair (rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v10), v10), tpair (rtranspose [1,0] (m5 * m9), v8)), tpair (rreplicate 2 (rcast (rsum (m5 * rgather [4,5] (tproject1 (tproject2 (tproject1 m1))) (\\[i14, i15] -> [i15, i14]))) + tproject2 (tproject2 (tproject1 m1))) * rtranspose [1,0] (rreplicate 5 v7), v7))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rsum (rtranspose [1,0] (rreplicate 2 (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)))) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i16, i17] -> [i17, i16])) + tproject2 (tproject2 m1)"



testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3)
                     ((fromPrimal . AstConcrete) (Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Float))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Float
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Float)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      constant = let ((a1, a2), (a3, a4), (a5, a6)) = valsInitVT2OPP
                 in ( ( AstCast $ AstFromPrimal $ AstConcrete $ unRepN a1
                      , AstCast $ AstFromPrimal $ AstConcrete $ unRepN a2 )
                    , ( AstFromPrimal $ AstCast $ AstConcrete $ unRepN a3
                      , AstFromPrimal $ AstCast $ AstConcrete $ unRepN a4 )
                    , ( AstCast $ AstFromPrimal $ AstConcrete $ unRepN a5
                      , AstFromPrimal $ AstCast $ AstConcrete $ unRepN a6 ) )
      (_, ast3) = funToAst (FTKR (singletonShape 0) (FTKScalar @Float))
                           (const $ afcnn2TnonLin constant)
  "\\dummy" ++ " -> " ++ printAstSimple renames ast3
    @?= "\\dummy -> tlet (exp (rsum (rtranspose [1,0] (rreplicate 2 (tlet (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (tlet (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 (rfromPrimal 7.0))) * rfromPrimal (rconcrete (rfromListLinear [3,4] [1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0]))) + rcast (rfromPrimal (rconcrete (rfromListLinear [4] [1.0,2.0,3.0,4.0])))) (\\v5 -> tlet (rfromPrimal (recip (rreplicate 4 1.0 + exp (negate (rprimalPart v5))))) (\\v6 -> rD (rprimalPart v6) (rdualPart (rfromPrimal (rprimalPart v6 * (rreplicate 4 1.0 - rprimalPart v6)) * rD (rreplicate 4 0.0) (rdualPart v5)))))))) * rfromPrimal (rconcrete (rfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0])))) + rfromPrimal (rcast (rconcrete (rfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v7 -> tlet (rfromPrimal (recip (rreplicate 5 1.0 + exp (negate (rprimalPart v7))))) (\\v8 -> rD (rprimalPart v8) (rdualPart (rfromPrimal (rprimalPart v8 * (rreplicate 5 1.0 - rprimalPart v8)) * rD (rreplicate 5 0.0) (rdualPart v7))))))) * rfromPrimal (rconcrete (rfromListLinear [5,2] [1.0,1.0,2.0,2.0,3.0,3.0,4.0,4.0,5.0,5.0]))) + rfromPrimal (rcast (rconcrete (rfromListLinear [2] [1.0,2.0]))))) (\\v9 -> rreplicate 2 (recip (rsum v9)) * v9)"

testVT2OPPNonLin2 :: Assertion
testVT2OPPNonLin2 = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = AstReplicate (SNat @3)
                     ((fromPrimal . AstConcrete) (Nested.rscalar 7) :: AstTensor AstMethodLet FullSpan (TKR 0 Double))
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
  let (artifactRevnonLin, _) =
        revArtifactAdapt True afcnn2TnonLin valsInitVT2OPP
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v27 x1 -> let v10 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)) ; v11 = exp (negate v10) ; v12 = rreplicate 4 1.0 + v11 ; v13 = recip v12 ; v14 = rreplicate 4 1.0 - v13 ; v15 = v13 * v14 ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v17 = rcast (rsum (m16 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)) ; v18 = exp (negate v17) ; v19 = rreplicate 5 1.0 + v18 ; v20 = recip v19 ; v21 = rreplicate 5 1.0 - v20 ; v22 = v20 * v21 ; m23 = rtranspose [1,0] (rreplicate 2 v20) ; v24 = exp (rsum (m23 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v26 = rreplicate 2 (recip x25) ; v28 = v24 * (rreplicate 2 (negate (recip (x25 * x25)) * rsum (v24 * v27)) + v26 * v27) ; m29 = rreplicate 5 v28 ; v30 = v22 * rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 m1)) * m29)) ; m31 = rreplicate 4 (rcast v30) ; v32 = v15 * rcast (rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))) * m31))) ; m33 = rreplicate 3 v32 in tpair (tpair (tpair (rtranspose [1,0] (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * m33), v32), tpair (rtranspose [1,0] (m16 * m31), v30)), tpair (rtranspose [1,0] (m23 * m29), v28))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\x1 -> let v10 = rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)) ; v11 = exp (negate v10) ; v12 = rreplicate 4 1.0 + v11 ; v13 = recip v12 ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v17 = rcast (rsum (m16 * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1)) ; v18 = exp (negate v17) ; v19 = rreplicate 5 1.0 + v18 ; v20 = recip v19 ; m23 = rtranspose [1,0] (rreplicate 2 v20) ; v24 = exp (rsum (m23 * rtranspose [1,0] (tproject1 (tproject2 m1))) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v26 = rreplicate 2 (recip x25) in v26 * v24"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v27 x1 -> let v13 = recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rgather [3,4] (tproject1 (tproject1 (tproject1 m1))) (\\[i40, i41] -> [i41, i40])) + tproject2 (tproject1 (tproject1 m1))))) ; m16 = rtranspose [1,0] (rreplicate 5 (rcast v13)) ; v20 = recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (m16 * rgather [4,5] (tproject1 (tproject2 (tproject1 m1))) (\\[i38, i39] -> [i39, i38]))) + tproject2 (tproject2 (tproject1 m1))))) ; v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 v20) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i36, i37] -> [i37, i36])) + tproject2 (tproject2 m1)) ; x25 = rsum v24 ; v28 = v24 * (rreplicate 2 (negate (recip (x25 * x25)) * rsum (v24 * v27)) + rreplicate 2 (recip x25) * v27) ; v30 = (v20 * (rreplicate 5 1.0 - v20)) * rsum (tproject1 (tproject2 m1) * rtranspose [1,0] (rreplicate 5 v28)) ; m31 = rreplicate 4 (rcast v30) ; v32 = (v13 * (rreplicate 4 1.0 - v13)) * rcast (rsum (tproject1 (tproject2 (tproject1 m1)) * rtranspose [1,0] m31)) in tpair (tpair (tpair (rreplicate 4 (rreplicate 3 7.0) * rtranspose [1,0] (rreplicate 3 v32), v32), tpair (rtranspose [1,0] (m16 * m31), v30)), tpair (rreplicate 2 v20 * rtranspose [1,0] (rreplicate 5 v28), v28))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x1 -> let v24 = exp (rsum (rtranspose [1,0] (rreplicate 2 (recip (rreplicate 5 1.0 + exp (negate (rcast (rsum (rtranspose [1,0] (rreplicate 5 (rcast (recip (rreplicate 4 1.0 + exp (negate (rsum (rtranspose [1,0] (rreplicate 4 (rreplicate 3 7.0)) * rtranspose [1,0] (tproject1 (tproject1 (tproject1 m1)))) + tproject2 (tproject1 (tproject1 m1)))))))) * rtranspose [1,0] (tproject1 (tproject2 (tproject1 m1))))) + tproject2 (tproject2 (tproject1 m1))))))) * rgather [5,2] (tproject1 (tproject2 m1)) (\\[i42, i43] -> [i43, i42])) + tproject2 (tproject2 m1)) in rreplicate 2 (recip (rsum v24)) * v24"
