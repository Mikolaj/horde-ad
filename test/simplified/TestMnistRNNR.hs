-- | Tests of "MnistRnnRanked2" neural networks using a few different
-- optimization pipelines.
--
-- *Not* LSTM.
-- Doesn't train without Adam, regardless of whether mini-batch sgd. It does
-- train with Adam, but only after very carefully tweaking initialization.
-- This is extremely sensitive to initial parameters, more than to anything
-- else. Probably, gradient is vanishing if parameters are initialized
-- with a probability distribution that doesn't have the right variance. See
-- https://stats.stackexchange.com/questions/301285/what-is-vanishing-gradient.
module TestMnistRNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import Data.Array.RankedS qualified as OR
import Data.IntMap.Strict qualified as IM
import Data.Vector.Generic qualified as V
import GHC.TypeLits (SomeNat (..), someNatVal)
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
import MnistRnnRanked2 qualified

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNA
            , tensorADValMnistTestsRNNI
            , tensorADValMnistTestsRNNO
            , tensorMnistTestsPP
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseRNNA
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            forgetShape $ fst
            $ randomVals @(MnistRnnRanked2.ADRnnMnistParametersShaped
                             OSArray width r)
                0.4 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
      ftest = MnistRnnRanked2.rnnMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyphR, labelR) adinputs =
                   MnistRnnRanked2.rnnMnistLossFusedR
                     miniBatchSize (rconst $ Nested.rfromOrthotope SNat glyphR, rconst $ Nested.rfromOrthotope SNat labelR)
                     (parseHVector (fromDValue valsInit) adinputs)
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (hVectorInit, initialStateAdam (voidFromHVector hVectorInit))
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNA
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNA :: TestTree
tensorADValMnistTestsRNNA = testGroup "RNN ADVal MNIST tests"
  [ mnistTestCaseRNNA "RNNA 1 epoch, 1 batch" 1 1 128 5 50
                       (0.9 :: Double)
  , mnistTestCaseRNNA "RNNA artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNA "RNNA artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.9336734693877551 :: Double)
  , mnistTestCaseRNNA "RNNA 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseRNNI
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            forgetShape $ fst
            $ randomVals @(MnistRnnRanked2.ADRnnMnistParametersShaped
                             OSArray width r)
                0.4 (mkStdGen 44)
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
      ftest = MnistRnnRanked2.rnnMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, _, var, hVector)
         <- funToAstRevIO $ FTKUntyped $ voidFromHVector hVectorInit
       let testDataR = packBatchR testData
       (varGlyph, _, astGlyph) <-
         funToAstIO
           (FTKR $ miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let ast :: AstRanked FullSpan r 0
           ast = MnistRnnRanked2.rnnMnistLossFusedR
                   miniBatchSize (AstRanked astGlyph, AstRanked astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (dunHVector $ unHVectorPseudoTensor (rankedY (stensorKind @TKUntyped) hVector)))
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = extendEnv var (HVectorPseudoTensor varInputs) emptyEnv
                       envMnist = extendEnv varGlyph (rconst $ Nested.rfromOrthotope SNat glyph)
                                  $ extendEnv varLabel (rconst $ Nested.rfromOrthotope SNat label) env
                   in interpretAst envMnist $ unAstRanked ast
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (hVectorInit, initialStateAdam (voidFromHVector hVectorInit))
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNI
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNI :: TestTree
tensorADValMnistTestsRNNI = testGroup "RNN Intermediate MNIST tests"
  [ mnistTestCaseRNNI "RNNI 1 epoch, 1 batch" 1 1 128 5 50
                       (0.9 :: Double)
  , mnistTestCaseRNNI "RNNI artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNI "RNNI artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.9336734693877551 :: Double)
  , mnistTestCaseRNNI "RNNI 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseRNNO
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNO prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
 -- TODO: use withKnownNat when we no longer support GHC 9.4
 case someNatVal $ toInteger width of
  Nothing -> error "impossible someNatVal error"
  Just (SomeNat @width _) ->
    let valsInitShaped
          :: MnistRnnRanked2.ADRnnMnistParametersShaped OSArray width r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
        valsInit = forgetShape valsInitShaped
        hVectorInit = toHVectorOf valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show width, show miniBatchSize
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
        ftest = MnistRnnRanked2.rnnMnistTestR valsInit
    in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           dataInit = case chunksOf miniBatchSize testData of
             d : _ -> let (dglyph, dlabel) = packBatchR d
                      in ( FlipR $ Nested.rfromOrthotope SNat dglyph
                         , FlipR $ Nested.rfromOrthotope SNat dlabel )
             [] -> error "empty test data"
           f = \ (pars, (glyphR, labelR)) ->
             MnistRnnRanked2.rnnMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           (artRaw, _) = revArtifactAdapt False f (valsInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchR r] -> (HVector ORArray, StateAdam)
              -> (HVector ORArray, StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat glyph
                 labelD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat label
                 parametersAndInput =
                   HVectorPseudoTensor
                   $ V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   unHVectorPseudoTensor
                   $ fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientHVector)
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = go chunkR (parameters, stateAdam)
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (hVectorInit, initialStateAdam (voidFromHVector hVectorInit))
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       assertEqualUpToEpsilon 1e-1 expected testErrorFinal

{-# SPECIALIZE mnistTestCaseRNNO
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNO :: TestTree
tensorADValMnistTestsRNNO = testGroup "RNN Once MNIST tests"
  [ mnistTestCaseRNNO "RNNO 1 epoch, 1 batch" 1 1 128 5 500
                       (0.898 :: Double)
  , mnistTestCaseRNNO "RNNO artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNO "RNNO artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNO "RNNO 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for RNN MNIST tests"
  [ testCase "RNNOPP" testRNNOPP
  , testCase "RNNOPP2" testRNNOPP2
  ]

valsInitRNNOPP
  :: Int -> Int -> MnistRnnRanked2.ADRnnMnistParameters ORArray Double
valsInitRNNOPP out_width sizeMnistHeightI =
  ( ( FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width, sizeMnistHeightI]
                    (map fromIntegral [0 .. out_width * sizeMnistHeightI - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( FlipR
       $ Nested.rfromOrthotope SNat
     $ OR.fromList [sizeMnistLabelInt, out_width]
                    (map fromIntegral [0 .. sizeMnistLabelInt * out_width - 1])
    , FlipR
      $ Nested.rfromOrthotope SNat
      $ OR.fromList [sizeMnistLabelInt]
                    (map fromIntegral [0 .. sizeMnistLabelInt - 1]) ) )

testRNNOPP :: Assertion
testRNNOPP = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 1
      sizeMnistHeightI = 1
      blackGlyph :: AstRanked PrimalSpan Double 3
      blackGlyph = AstRanked
                   $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @1)
                       (7 :: AstTensor AstMethodLet PrimalSpan (TKR Double 0))
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m39 m48 m49 v50 m51 m52 v53 m54 v55 -> let m12 = rreshape [2,1] (rreplicate 2 0.0) ; m19 = tanh (rtranspose [1,0] (rreplicate 1 v50) + rsum (rtranspose [2,1,0] (rreplicate 1 m48) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m49) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m12)))) ; m27 = tanh (rtranspose [1,0] (rreplicate 1 v50) + rsum (rtranspose [2,1,0] (rreplicate 1 m48) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m49) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m12)))) ; m34 = tanh (rtranspose [1,0] (rreplicate 1 v53) + rsum (rtranspose [2,1,0] (rreplicate 1 m51) * rtranspose [1,0] (rreplicate 1 m27)) + rsum (rtranspose [2,1,0] (rreplicate 1 m52) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m12)))) ; t37 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m19 m34))) ; m40 = rappend (rreshape [1,1] (rreplicate 1 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m54) * rtranspose [1,0] (rreplicate 1 m39))) (rreshape [0,1] (rreplicate 0 0.0))) ; m41 = (rconst (rfromListLinear [1,1] [1.0]) - m34 * m34) * rslice 1 1 m40 ; m44 = (rconst (rfromListLinear [1,1] [1.0]) - m27 * m27) * rsum (rtranspose [1,2,0] (rreplicate 1 m51) * rtranspose [1,0] (rreplicate 1 m41)) ; m46 = (rconst (rfromListLinear [1,1] [1.0]) - m19 * m19) * rslice 0 1 m40 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m46)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m44)), rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 0 1 m12)) * rtranspose [2,1,0] (rreplicate 1 m46)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 0 1 m12)) * rtranspose [2,1,0] (rreplicate 1 m44)), rsum (rtranspose [1,0] m46) + rsum (rtranspose [1,0] m44), rsum (rtranspose [2,0,1] (rreplicate 1 m27) * rtranspose [2,1,0] (rreplicate 1 m41)), rsum (rtranspose [2,0,1] (rreplicate 1 (rslice 1 1 m12)) * rtranspose [2,1,0] (rreplicate 1 m41)), rsum (rtranspose [1,0] m41), rsum (rtranspose [2,1,0] (t37 * rreplicate 1 m39)), rsum (rtranspose [1,0] m39)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m224 m225 v226 m227 m228 v229 m230 v231 -> let m12 = rreshape [2,1] (rreplicate 2 0.0) ; m19 = tanh (rtranspose [1,0] (rreplicate 1 v226) + rsum (rtranspose [2,1,0] (rreplicate 1 m224) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m225) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m12)))) ; m27 = tanh (rtranspose [1,0] (rreplicate 1 v226) + rsum (rtranspose [2,1,0] (rreplicate 1 m224) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m225) * rtranspose [1,0] (rreplicate 1 (rslice 0 1 m12)))) ; m34 = tanh (rtranspose [1,0] (rreplicate 1 v229) + rsum (rtranspose [2,1,0] (rreplicate 1 m227) * rtranspose [1,0] (rreplicate 1 m27)) + rsum (rtranspose [2,1,0] (rreplicate 1 m228) * rtranspose [1,0] (rreplicate 1 (rslice 1 1 m12)))) ; t37 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m19 m34))) in rsum (rtranspose [2,1,0] (rreplicate 1 m230) * t37) + rtranspose [1,0] (rreplicate 1 v231)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m39 m574 m575 v576 m577 m578 v579 m580 v581 -> let m19 = tanh (rtranspose [1,0] (rreplicate 1 v576) + rsum (rtranspose [2,1,0] (rreplicate 1 m574) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m575) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m27 = tanh (rtranspose [1,0] (rreplicate 1 v576) + rsum (rtranspose [2,1,0] (rreplicate 1 m574) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m575) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m34 = tanh (rtranspose [1,0] (rreplicate 1 v579) + rsum (rtranspose [2,1,0] (rreplicate 1 m577) * rtranspose [1,0] (rreplicate 1 m27)) + rsum (rtranspose [2,1,0] (rreplicate 1 m578) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m40 = rappend (rconst (rfromListLinear [1,1] [0.0])) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 m580) * rtranspose [1,0] (rreplicate 1 m39))) (rreplicate 0 (rreplicate 1 0.0))) ; m41 = (rconst (rfromListLinear [1,1] [1.0]) - m34 * m34) * rslice 1 1 m40 ; m44 = (rconst (rfromListLinear [1,1] [1.0]) - m27 * m27) * rsum (rtranspose [1,2,0] (rreplicate 1 m577) * rtranspose [1,0] (rreplicate 1 m41)) ; m46 = (rconst (rfromListLinear [1,1] [1.0]) - m19 * m19) * rslice 0 1 m40 in [rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m46)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m44)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m46)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m44)), rsum (rtranspose [1,0] m46) + rsum (rtranspose [1,0] m44), rsum (rtranspose [2,0,1] (rreplicate 1 m27) * rtranspose [2,1,0] (rreplicate 1 m41)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m41)), rsum (rtranspose [1,0] m41), rsum (rtranspose [2,0,1] (rreplicate 10 m34) * rtranspose [2,1,0] (rreplicate 1 m39)), rsum (rtranspose [1,0] m39)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m756 m757 v758 m759 m760 v761 m762 v763 -> rsum (rtranspose [2,1,0] (rreplicate 1 m762) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 1 v761) + rsum (rtranspose [2,1,0] (rreplicate 1 m759) * rtranspose [1,0] (rreplicate 1 (tanh (rtranspose [1,0] (rreplicate 1 v758) + rsum (rtranspose [2,1,0] (rreplicate 1 m756) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 m757) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 1 m760) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rtranspose [1,0] (rreplicate 1 v763)"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstRanked PrimalSpan Double 3
      blackGlyph = AstRanked
                   $ AstReplicate (SNat @2)
                   $ AstReplicate (SNat @2)
                   $ AstReplicate (SNat @2)
                       (7 :: AstTensor AstMethodLet PrimalSpan (TKR Double 0))
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m63 m80 m81 v82 m83 m84 v85 m86 v87 -> let m13 = rreshape [4,2] (rreplicate 8 0.0) ; m20 = tanh (rtranspose [1,0] (rreplicate 2 v82) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m13)))) ; m28 = tanh (rtranspose [1,0] (rreplicate 2 v82) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m13)))) ; m35 = tanh (rtranspose [1,0] (rreplicate 2 v85) + rsum (rtranspose [2,1,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,1,0] (rreplicate 2 m84) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m13)))) ; m36 = rappend m20 m35 ; m43 = tanh (rtranspose [1,0] (rreplicate 2 v82) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m36)))) ; m51 = tanh (rtranspose [1,0] (rreplicate 2 v82) + rsum (rtranspose [2,1,0] (rreplicate 2 m80) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m36)))) ; m58 = tanh (rtranspose [1,0] (rreplicate 2 v85) + rsum (rtranspose [2,1,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 m51)) + rsum (rtranspose [2,1,0] (rreplicate 2 m84) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m36)))) ; t61 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m43 m58))) ; m64 = rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m86) * rtranspose [1,0] (rreplicate 2 m63))) (rreshape [0,2] (rreplicate 0 0.0))) ; m65 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m58 * m58) * rslice 2 2 m64 ; m68 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m51 * m51) * rsum (rtranspose [1,2,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 m65)) ; m70 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m43 * m43) * rslice 0 2 m64 ; m72 = rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 m70))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m81) * rtranspose [1,0] (rreplicate 2 m68))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m84) * rtranspose [1,0] (rreplicate 2 m65))) (rreshape [0,2] (rreplicate 0 0.0))) ; m73 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m35 * m35) * rslice 2 2 m72 ; m76 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m28 * m28) * rsum (rtranspose [1,2,0] (rreplicate 2 m83) * rtranspose [1,0] (rreplicate 2 m73)) ; m78 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m20 * m20) * rslice 0 2 m72 in [rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m78)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m76)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m70)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m68)), rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m13)) * rtranspose [2,1,0] (rreplicate 2 m78)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m13)) * rtranspose [2,1,0] (rreplicate 2 m76)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m36)) * rtranspose [2,1,0] (rreplicate 2 m70)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m36)) * rtranspose [2,1,0] (rreplicate 2 m68)), rsum (rtranspose [1,0] m78) + rsum (rtranspose [1,0] m76) + rsum (rtranspose [1,0] m70) + rsum (rtranspose [1,0] m68), rsum (rtranspose [2,0,1] (rreplicate 2 m28) * rtranspose [2,1,0] (rreplicate 2 m73)) + rsum (rtranspose [2,0,1] (rreplicate 2 m51) * rtranspose [2,1,0] (rreplicate 2 m65)), rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m13)) * rtranspose [2,1,0] (rreplicate 2 m73)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m36)) * rtranspose [2,1,0] (rreplicate 2 m65)), rsum (rtranspose [1,0] m73) + rsum (rtranspose [1,0] m65), rsum (rtranspose [2,1,0] (t61 * rreplicate 2 m63)), rsum (rtranspose [1,0] m63)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m400 m401 v402 m403 m404 v405 m406 v407 -> let m13 = rreshape [4,2] (rreplicate 8 0.0) ; m20 = tanh (rtranspose [1,0] (rreplicate 2 v402) + rsum (rtranspose [2,1,0] (rreplicate 2 m400) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m401) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m13)))) ; m28 = tanh (rtranspose [1,0] (rreplicate 2 v402) + rsum (rtranspose [2,1,0] (rreplicate 2 m400) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m401) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m13)))) ; m35 = tanh (rtranspose [1,0] (rreplicate 2 v405) + rsum (rtranspose [2,1,0] (rreplicate 2 m403) * rtranspose [1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,1,0] (rreplicate 2 m404) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m13)))) ; m36 = rappend m20 m35 ; m43 = tanh (rtranspose [1,0] (rreplicate 2 v402) + rsum (rtranspose [2,1,0] (rreplicate 2 m400) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m401) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m36)))) ; m51 = tanh (rtranspose [1,0] (rreplicate 2 v402) + rsum (rtranspose [2,1,0] (rreplicate 2 m400) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m401) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m36)))) ; m58 = tanh (rtranspose [1,0] (rreplicate 2 v405) + rsum (rtranspose [2,1,0] (rreplicate 2 m403) * rtranspose [1,0] (rreplicate 2 m51)) + rsum (rtranspose [2,1,0] (rreplicate 2 m404) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m36)))) ; t61 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m43 m58))) in rsum (rtranspose [2,1,0] (rreplicate 2 m406) * t61) + rtranspose [1,0] (rreplicate 2 v407)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m63 m1052 m1053 v1054 m1055 m1056 v1057 m1058 v1059 -> let m20 = tanh (rtranspose [1,0] (rreplicate 2 v1054) + rsum (rtranspose [2,1,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1053) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m28 = tanh (rtranspose [1,0] (rreplicate 2 v1054) + rsum (rtranspose [2,1,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1053) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m35 = tanh (rtranspose [1,0] (rreplicate 2 v1057) + rsum (rtranspose [2,1,0] (rreplicate 2 m1055) * rtranspose [1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,1,0] (rreplicate 2 m1056) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m36 = rappend m20 m35 ; m43 = tanh (rtranspose [1,0] (rreplicate 2 v1054) + rsum (rtranspose [2,1,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1053) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m36)))) ; m51 = tanh (rtranspose [1,0] (rreplicate 2 v1054) + rsum (rtranspose [2,1,0] (rreplicate 2 m1052) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1053) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m36)))) ; m58 = tanh (rtranspose [1,0] (rreplicate 2 v1057) + rsum (rtranspose [2,1,0] (rreplicate 2 m1055) * rtranspose [1,0] (rreplicate 2 m51)) + rsum (rtranspose [2,1,0] (rreplicate 2 m1056) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m36)))) ; m64 = rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m1058) * rtranspose [1,0] (rreplicate 2 m63))) (rreplicate 0 (rreplicate 2 0.0))) ; m65 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m58 * m58) * rslice 2 2 m64 ; m68 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m51 * m51) * rsum (rtranspose [1,2,0] (rreplicate 2 m1055) * rtranspose [1,0] (rreplicate 2 m65)) ; m70 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m43 * m43) * rslice 0 2 m64 ; m72 = rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m1053) * rtranspose [1,0] (rreplicate 2 m70))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m1053) * rtranspose [1,0] (rreplicate 2 m68))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 m1056) * rtranspose [1,0] (rreplicate 2 m65))) (rreplicate 0 (rreplicate 2 0.0))) ; m73 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m35 * m35) * rslice 2 2 m72 ; m76 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m28 * m28) * rsum (rtranspose [1,2,0] (rreplicate 2 m1055) * rtranspose [1,0] (rreplicate 2 m73)) ; m78 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m20 * m20) * rslice 0 2 m72 in [rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m78)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m76)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m70)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m68)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m78)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m76)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m36)) * rtranspose [2,1,0] (rreplicate 2 m70)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m36)) * rtranspose [2,1,0] (rreplicate 2 m68)), rsum (rtranspose [1,0] m78) + rsum (rtranspose [1,0] m76) + rsum (rtranspose [1,0] m70) + rsum (rtranspose [1,0] m68), rsum (rtranspose [2,0,1] (rreplicate 2 m28) * rtranspose [2,1,0] (rreplicate 2 m73)) + rsum (rtranspose [2,0,1] (rreplicate 2 m51) * rtranspose [2,1,0] (rreplicate 2 m65)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m73)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m36)) * rtranspose [2,1,0] (rreplicate 2 m65)), rsum (rtranspose [1,0] m73) + rsum (rtranspose [1,0] m65), rsum (rtranspose [2,0,1] (rreplicate 10 m58) * rtranspose [2,1,0] (rreplicate 2 m63)), rsum (rtranspose [1,0] m63)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1392 m1393 v1394 m1395 m1396 v1397 m1398 v1399 -> let m36 = rappend (tanh (rtranspose [1,0] (rreplicate 2 v1394) + rsum (rtranspose [2,1,0] (rreplicate 2 m1392) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1393) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) (tanh (rtranspose [1,0] (rreplicate 2 v1397) + rsum (rtranspose [2,1,0] (rreplicate 2 m1395) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v1394) + rsum (rtranspose [2,1,0] (rreplicate 2 m1392) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1393) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1396) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) in rsum (rtranspose [2,1,0] (rreplicate 2 m1398) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 2 v1397) + rsum (rtranspose [2,1,0] (rreplicate 2 m1395) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 v1394) + rsum (rtranspose [2,1,0] (rreplicate 2 m1392) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1393) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m36))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 m1396) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m36))))))) + rtranspose [1,0] (rreplicate 2 v1399)"
