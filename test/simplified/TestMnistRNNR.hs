{-# LANGUAGE OverloadedLists #-}
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
import Data.IntMap.Strict qualified as IM
import GHC.TypeLits (SomeNat (..), someNatVal)
import Numeric.LinearAlgebra (Numeric)
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
import HordeAd.External.OptimizerTools

import EqEpsilon

import MnistData
import MnistRnnRanked2 (ADRnnMnistParameters, ADRnnMnistParametersShaped)
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
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: ADRnnMnistParameters target r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            forgetShape $ fst
            $ randomValue @(ADRnnMnistParametersShaped
                             RepN width r)
                0.4 (mkStdGen 44)
      hVectorInit :: RepN (X (ADRnnMnistParameters RepN r))
      hVectorInit = toTarget @RepN valsInit
      ftk = tftk @RepN (stensorKind @(X (ADRnnMnistParameters RepN r)))
                       hVectorInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize ]
--                        , show (V.length hVectorInit)
--                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> RepN (X (ADRnnMnistParameters RepN r))
            -> r
      ftest batch_size mnistData pars =
        MnistRnnRanked2.rnnMnistTestR
          batch_size mnistData (fromTarget @RepN pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( RepN (X (ADRnnMnistParameters RepN r))
                          , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r
                   -> ADVal RepN (X (ADRnnMnistParameters RepN r))
                   -> ADVal target (TKR 0 r)
                 f (glyphR, labelR) adinputs =
                   MnistRnnRanked2.rnnMnistLossFusedR
                     miniBatchSize (rconcrete glyphR, rconcrete labelR)
                     (fromTarget @(ADVal RepN) adinputs)
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdamDeep @(MnistDataBatchR r) @(X (ADRnnMnistParameters RepN r)) f chunkR parameters stateAdam
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
       let runEpoch :: Int
                    -> ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
                    -> IO (RepN (X (ADRnnMnistParameters RepN r)))
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
       res <- runEpoch 1 (hVectorInit, initialStateAdamDeep ftk)
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
                       (0.94 :: Double)
  , mnistTestCaseRNNA "RNNA artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNA "RNNA artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNA "RNNA 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseRNNI
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: ADRnnMnistParameters target r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            forgetShape $ fst
            $ randomValue @(ADRnnMnistParametersShaped
                             RepN width r)
                0.4 (mkStdGen 44)
      hVectorInit :: RepN (X (ADRnnMnistParameters RepN r))
      hVectorInit = toTarget @RepN valsInit
      ftk = tftk @RepN (stensorKind @(X (ADRnnMnistParameters RepN r)))
                       hVectorInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize ]
--                        , show (V.length hVectorInit)
--                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> RepN (X (ADRnnMnistParameters RepN r))
            -> r
      ftest batch_size mnistData pars =
        MnistRnnRanked2.rnnMnistTestR
          batch_size mnistData (fromTarget @RepN pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, _, var, hVector) <- funToAstRevIO ftk
       let testDataR = packBatchR testData
       (varGlyph, astGlyph) <-
         funToAstIO
           (FTKR (miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR) FTKScalar)
           id
       (varLabel, astLabel) <-
         funToAstIO (FTKR (miniBatchSize :$: sizeMnistLabelInt :$: ZSR) FTKScalar) id
       let ast :: AstTensor AstMethodLet FullSpan (TKR 0 r)
           ast = MnistRnnRanked2.rnnMnistLossFusedR
                   miniBatchSize (astGlyph, astLabel)
                   (fromTarget hVector)
           runBatch :: ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( RepN (X (ADRnnMnistParameters RepN r))
                          , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r
                   -> ADVal RepN (X (ADRnnMnistParameters RepN r))
                   -> ADVal target (TKR 0 r)
                 f (glyph, label) varInputs =
                   let env = extendEnv @(ADVal RepN) @_ @(X (ADRnnMnistParameters RepN r)) var varInputs emptyEnv
                       envMnist = extendEnv varGlyph (rconcrete glyph)
                                  $ extendEnv varLabel (rconcrete label) env
                   in interpretAst envMnist ast
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdamDeep @(MnistDataBatchR r) @(X (ADRnnMnistParameters RepN r)) f chunkR parameters stateAdam
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
       let runEpoch :: Int
                    -> ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
                    -> IO (RepN (X (ADRnnMnistParameters RepN r)))
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
       res <- runEpoch 1 (hVectorInit, initialStateAdamDeep ftk)
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
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNI "RNNI 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseRNNO
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
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
          :: ADRnnMnistParametersShaped RepN width r
        valsInitShaped = fst $ randomValue 0.4 (mkStdGen 44)
        valsInit :: ADRnnMnistParameters target r
        valsInit = forgetShape valsInitShaped
        hVectorInit :: RepN (X (ADRnnMnistParameters RepN r))
        hVectorInit = toTarget @RepN valsInit
        ftk = tftk @RepN (stensorKind @(X (ADRnnMnistParameters RepN r)))
                         hVectorInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show width, show miniBatchSize ]
--                          , show (V.length hVectorInit)
--                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r
              -> RepN (X (ADRnnMnistParameters RepN r))
              -> r
        ftest batch_size mnistData pars =
          MnistRnnRanked2.rnnMnistTestR
            batch_size mnistData (fromTarget @RepN pars)
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
                      in ( RepN dglyph
                         , RepN dlabel )
             [] -> error "empty test data"
           f :: ( ADRnnMnistParameters (AstTensor AstMethodLet FullSpan) r
                , (AstTensor AstMethodLet FullSpan (TKR 3 r), AstTensor AstMethodLet FullSpan (TKR 2 r)) )
             -> AstTensor AstMethodLet FullSpan (TKR 0 r)
           f = \ (pars, (glyphR, labelR)) ->
             MnistRnnRanked2.rnnMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           (artRaw, _) = revArtifactAdapt False f (valsInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchR r]
              -> ( RepN (X (ADRnnMnistParameters RepN r))
                 , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
              -> ( RepN (X (ADRnnMnistParameters RepN r))
                 , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = rconcrete glyph
                 labelD = rconcrete label
                 parametersAndInput = tpair parameters (tpair glyphD labelD)
                 gradient =
                   tproject1 $ fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdamDeep
                           @(X (ADRnnMnistParameters RepN r))
                           defaultArgsAdam stateAdam parameters gradient)
           runBatch :: ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( RepN (X (ADRnnMnistParameters RepN r))
                          , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
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
       let runEpoch :: Int
                    -> ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdamDeep (X (ADRnnMnistParameters RepN r)) )
                    -> IO (RepN (X (ADRnnMnistParameters RepN r)))
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
       res <- runEpoch 1 (hVectorInit, initialStateAdamDeep ftk)
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
  :: Int -> Int -> ADRnnMnistParameters RepN Double
valsInitRNNOPP out_width sizeMnistHeightI =
  ( ( RepN
      $ Nested.rfromListPrimLinear [out_width, sizeMnistHeightI]
                    (map fromIntegral [0 .. out_width * sizeMnistHeightI - 1])
    , RepN
      $ Nested.rfromListPrimLinear [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , RepN
      $ Nested.rfromListPrimLinear [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( RepN
      $ Nested.rfromListPrimLinear [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , RepN
      $ Nested.rfromListPrimLinear [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , RepN
      $ Nested.rfromListPrimLinear [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( RepN
       $ Nested.rfromListPrimLinear [sizeMnistLabelInt, out_width]
                    (map fromIntegral [0 .. sizeMnistLabelInt * out_width - 1])
    , RepN
      $ Nested.rfromListPrimLinear [sizeMnistLabelInt]
                    (map fromIntegral [0 .. sizeMnistLabelInt - 1]) ) )

testRNNOPP :: Assertion
testRNNOPP = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 1
      sizeMnistHeightI = 1
      blackGlyph :: AstTensor AstMethodLet PrimalSpan (TKR 3 Double)
      blackGlyph = AstReplicate (SNat @1) stensorKind
                   $ AstReplicate (SNat @1) stensorKind
                   $ AstReplicate (SNat @1) stensorKind
                       (AstConcrete (FTKR ZSR FTKScalar) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: ADRnnMnistParameters (AstTensor AstMethodLet FullSpan)
                                                      Double
              -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m12 m1 -> let m3 = tconcrete (FTKS [2,1] FTKScalar) (sfromListLinear [2,1] [0.0,0.0]) ; t4 = stranspose (sreplicate (sslice m3)) ; m5 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t4)) ; t6 = stranspose (sreplicate (sslice m3)) ; m7 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t6)) ; t8 = stranspose (sreplicate m7) ; t9 = stranspose (sreplicate (sslice m3)) ; m10 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t8) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t9)) ; t11 = stranspose (sreplicate (sslice (sappend m5 m10))) ; m13 = sappend (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0.0])) (sappend (ssum (stranspose (stranspose (sreplicate (sfromR (tproject1 (tproject2 m1)))) * sreplicate (sfromR m12)))) (tconcrete (FTKS [0,1] FTKScalar) (sfromListLinear [0,1] []))) ; m14 = (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [1.0]) - m10 * m10) * sslice m13 ; t15 = sreplicate m14 ; t16 = sreplicate m14 ; m17 = (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [1.0]) - m7 * m7) * ssum (stranspose (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t16)) ; t18 = sreplicate m17 ; m19 = (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [1.0]) - m5 * m5) * sslice m13 ; t20 = sreplicate m19 in tpair (tpair (tpair (tpair (rfromS (ssum (stranspose (stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0)))) * sreplicate m19)) + ssum (stranspose (stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0)))) * sreplicate m17))), rfromS (ssum (stranspose (t4 * t20)) + ssum (stranspose (t6 * t18)))), rfromS (ssum (stranspose m19) + ssum (stranspose m17))), tpair (tpair (rfromS (ssum (stranspose (t8 * t16))), rfromS (ssum (stranspose (t9 * t15)))), rfromS (ssum (stranspose m14)))), tpair (rfromS (ssum (stranspose (t11 * sreplicate (sfromR m12)))), rfromS (ssum (stranspose (sfromR m12)))))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m1 -> let m3 = tconcrete (FTKS [2,1] FTKScalar) (sfromListLinear [2,1] [0.0,0.0]) ; t4 = stranspose (sreplicate (sslice m3)) ; m5 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t4)) ; t6 = stranspose (sreplicate (sslice m3)) ; m7 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t6)) ; t8 = stranspose (sreplicate m7) ; t9 = stranspose (sreplicate (sslice m3)) ; m10 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t8) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t9)) ; t11 = stranspose (sreplicate (sslice (sappend m5 m10))) in rfromS (ssum (stranspose (sreplicate (sfromR (tproject1 (tproject2 m1)))) * t11) + stranspose (sreplicate (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m12 m1 -> tfromS (let m3 = tconcrete (FTKS [2,1] FTKScalar) (sfromListLinear [2,1] [0.0,0.0]) ; m5 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m3)) ; m7 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m3)) ; m10 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m7 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice m3)) ; m13 = sappend (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0.0])) (sappend (smatmul2 (stranspose (sfromR (tproject1 (tproject2 m1)))) (sfromR m12)) (tconcrete (FTKS [0,1] FTKScalar) (sfromListLinear [0,1] []))) ; m14 = (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [1.0]) - m10 * m10) * sslice m13 ; m17 = (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [1.0]) - m7 * m7) * smatmul2 (stranspose (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m14 ; m19 = (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [1.0]) - m5 * m5) * sslice m13 in tpair (tpair (tpair (tpair (smatmul2 m19 (stranspose (sreplicate (sreplicate (sscalar 7.0)))) + smatmul2 m17 (stranspose (sreplicate (sreplicate (sscalar 7.0)))), smatmul2 m19 (stranspose (sslice m3)) + smatmul2 m17 (stranspose (sslice m3))), ssum (stranspose m19) + ssum (stranspose m17)), tpair (tpair (smatmul2 m14 (stranspose m7), smatmul2 m14 (stranspose (sslice m3))), ssum (stranspose m14))), tpair (smatmul2 (sfromR m12) (stranspose m10), ssum (stranspose (sfromR m12)))))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (let m3 = tconcrete (FTKS [2,1] FTKScalar) (sfromListLinear [2,1] [0.0,0.0]) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m3))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice m3))) + stranspose (sreplicate (sfromR (tproject2 (tproject2 m1)))))"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstTensor AstMethodLet PrimalSpan (TKR 3 Double)
      blackGlyph = AstReplicate (SNat @2) stensorKind
                   $ AstReplicate (SNat @2) stensorKind
                   $ AstReplicate (SNat @2) stensorKind
                       (AstConcrete (FTKR ZSR FTKScalar) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: ADRnnMnistParameters (AstTensor AstMethodLet FullSpan)
                                                      Double
              -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m21 m1 -> let m4 = tconcrete (FTKS [4,2] FTKScalar) (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) ; t5 = stranspose (sreplicate (sslice m4)) ; m6 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t5)) ; t7 = stranspose (sreplicate (sslice m4)) ; m8 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t7)) ; t9 = stranspose (sreplicate m8) ; t10 = stranspose (sreplicate (sslice m4)) ; m11 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t9) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t10)) ; m12 = sappend m6 m11 ; t13 = stranspose (sreplicate (sslice m12)) ; m14 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t13)) ; t15 = stranspose (sreplicate (sslice m12)) ; m16 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t15)) ; t17 = stranspose (sreplicate m16) ; t18 = stranspose (sreplicate (sslice m12)) ; m19 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t17) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t18)) ; t20 = stranspose (sreplicate (sslice (sappend m14 m19))) ; m22 = sappend (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (ssum (stranspose (stranspose (sreplicate (sfromR (tproject1 (tproject2 m1)))) * sreplicate (sfromR m21)))) (tconcrete (FTKS [0,2] FTKScalar) (sfromListLinear [0,2] []))) ; m23 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * sslice m22 ; t24 = sreplicate m23 ; t25 = sreplicate m23 ; m26 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * ssum (stranspose (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t25)) ; t27 = sreplicate m26 ; m28 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * sslice m22 ; t29 = sreplicate m28 ; m30 = sappend (tconcrete (FTKS [0,2] FTKScalar) (sfromListLinear [0,2] [])) (sappend (ssum (stranspose (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t29))) (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + sappend (tconcrete (FTKS [0,2] FTKScalar) (sfromListLinear [0,2] [])) (sappend (ssum (stranspose (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t27))) (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + sappend (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (ssum (stranspose (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t24))) (tconcrete (FTKS [0,2] FTKScalar) (sfromListLinear [0,2] []))) ; m31 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m11 * m11) * sslice m30 ; t32 = sreplicate m31 ; t33 = sreplicate m31 ; m34 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m8 * m8) * ssum (stranspose (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t33)) ; t35 = sreplicate m34 ; m36 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m6 * m6) * sslice m30 ; t37 = sreplicate m36 in tpair (tpair (tpair (tpair (rfromS (ssum (stranspose (stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0)))) * sreplicate m36)) + ssum (stranspose (stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0)))) * sreplicate m34)) + ssum (stranspose (stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0)))) * sreplicate m28)) + ssum (stranspose (stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0)))) * sreplicate m26))), rfromS (ssum (stranspose (t5 * t37)) + ssum (stranspose (t7 * t35)) + ssum (stranspose (t13 * t29)) + ssum (stranspose (t15 * t27)))), rfromS (ssum (stranspose m36) + ssum (stranspose m34) + ssum (stranspose m28) + ssum (stranspose m26))), tpair (tpair (rfromS (ssum (stranspose (t9 * t33)) + ssum (stranspose (t17 * t25))), rfromS (ssum (stranspose (t10 * t32)) + ssum (stranspose (t18 * t24)))), rfromS (ssum (stranspose m31) + ssum (stranspose m23)))), tpair (rfromS (ssum (stranspose (t20 * sreplicate (sfromR m21)))), rfromS (ssum (stranspose (sfromR m21)))))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m1 -> let m4 = tconcrete (FTKS [4,2] FTKScalar) (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) ; t5 = stranspose (sreplicate (sslice m4)) ; m6 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t5)) ; t7 = stranspose (sreplicate (sslice m4)) ; m8 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t7)) ; t9 = stranspose (sreplicate m8) ; t10 = stranspose (sreplicate (sslice m4)) ; m11 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t9) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t10)) ; m12 = sappend m6 m11 ; t13 = stranspose (sreplicate (sslice m12)) ; m14 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t13)) ; t15 = stranspose (sreplicate (sslice m12)) ; m16 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * stranspose (sreplicate (sreplicate (sreplicate (sscalar 7.0))))) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t15)) ; t17 = stranspose (sreplicate m16) ; t18 = stranspose (sreplicate (sslice m12)) ; m19 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + ssum (stranspose (sreplicate (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t17) + ssum (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t18)) ; t20 = stranspose (sreplicate (sslice (sappend m14 m19))) in rfromS (ssum (stranspose (sreplicate (sfromR (tproject1 (tproject2 m1)))) * t20) + stranspose (sreplicate (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m21 m1 -> tfromS (let m4 = tconcrete (FTKS [4,2] FTKScalar) (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) ; m6 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m4)) ; m8 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m4)) ; m11 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m8 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice m4)) ; m12 = sappend m6 m11 ; m14 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m12)) ; m16 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m12)) ; m19 = tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m16 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice m12)) ; m22 = sappend (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (smatmul2 (stranspose (sfromR (tproject1 (tproject2 m1)))) (sfromR m21)) (tconcrete (FTKS [0,2] FTKScalar) (sfromListLinear [0,2] []))) ; m23 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * sslice m22 ; m26 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * smatmul2 (stranspose (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m23 ; m28 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * sslice m22 ; m30 = sappend (tconcrete (FTKS [0,2] FTKScalar) (sfromListLinear [0,2] [])) (sappend (smatmul2 (stranspose (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) m28) (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + sappend (tconcrete (FTKS [0,2] FTKScalar) (sfromListLinear [0,2] [])) (sappend (smatmul2 (stranspose (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) m26) (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + sappend (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (smatmul2 (stranspose (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) m23) (tconcrete (FTKS [0,2] FTKScalar) (sfromListLinear [0,2] []))) ; m31 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m11 * m11) * sslice m30 ; m34 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m8 * m8) * smatmul2 (stranspose (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m31 ; m36 = (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m6 * m6) * sslice m30 in tpair (tpair (tpair (tpair (smatmul2 m36 (stranspose (sreplicate (sreplicate (sscalar 7.0)))) + smatmul2 m34 (stranspose (sreplicate (sreplicate (sscalar 7.0)))) + smatmul2 m28 (stranspose (sreplicate (sreplicate (sscalar 7.0)))) + smatmul2 m26 (stranspose (sreplicate (sreplicate (sscalar 7.0)))), smatmul2 m36 (stranspose (sslice m4)) + smatmul2 m34 (stranspose (sslice m4)) + smatmul2 m28 (stranspose (sslice m12)) + smatmul2 m26 (stranspose (sslice m12))), ssum (stranspose m36) + ssum (stranspose m34) + ssum (stranspose m28) + ssum (stranspose m26)), tpair (tpair (smatmul2 m31 (stranspose m8) + smatmul2 m23 (stranspose m16), smatmul2 m31 (stranspose (sslice m4)) + smatmul2 m23 (stranspose (sslice m12))), ssum (stranspose m31) + ssum (stranspose m23))), tpair (smatmul2 (sfromR m21) (stranspose m19), ssum (stranspose (sfromR m21)))))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (let m4 = tconcrete (FTKS [4,2] FTKScalar) (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) ; m12 = sappend (tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m4))) (tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m4))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice m4))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh (stranspose (sreplicate (sfromR (tproject2 (tproject2 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh (stranspose (sreplicate (sfromR (tproject2 (tproject1 (tproject1 m1))))) + smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate (sreplicate (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m12))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice m12))) + stranspose (sreplicate (sfromR (tproject2 (tproject2 m1)))))"
