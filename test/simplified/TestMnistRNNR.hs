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
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: ADRnnMnistParameters ranked r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            forgetShape $ fst
            $ randomVals @(ADRnnMnistParametersShaped
                             OSArray width r)
                0.4 (mkStdGen 44)
      hVectorInit :: Rep ORArray (X (ADRnnMnistParameters ORArray r))
      hVectorInit = toHVector valsInit
      ftk = tshapeFull @ORArray
                       (stensorKind @(X (ADRnnMnistParameters ORArray r)))
                       hVectorInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize ]
--                        , show (V.length hVectorInit)
--                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> Rep ORArray (X (ADRnnMnistParameters ORArray r))
            -> r
      ftest batch_size mnistData pars =
        MnistRnnRanked2.rnnMnistTestR
          batch_size mnistData (parseHVector valsInit pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                       , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                          , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r
                   -> Rep (ADVal ORArray) (X (ADRnnMnistParameters ORArray r))
                   -> ADVal ranked r 0
                 f (glyphR, labelR) adinputs =
                   MnistRnnRanked2.rnnMnistLossFusedR
                     miniBatchSize (rconst $ Nested.rfromOrthotope SNat glyphR, rconst $ Nested.rfromOrthotope SNat labelR)
                     (parseHVector (fromDValue valsInit)
                      $ repDeepDuplicable stensorKind adinputs)
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdamDeep f chunkR parameters stateAdam
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
                    -> ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                       , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
                    -> IO (Rep ORArray (X (ADRnnMnistParameters ORArray r)))
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
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: ADRnnMnistParameters ranked r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            forgetShape $ fst
            $ randomVals @(ADRnnMnistParametersShaped
                             OSArray width r)
                0.4 (mkStdGen 44)
      hVectorInit :: Rep ORArray (X (ADRnnMnistParameters ORArray r))
      hVectorInit = toHVector valsInit
      ftk = tshapeFull @ORArray
                       (stensorKind @(X (ADRnnMnistParameters ORArray r)))
                       hVectorInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize ]
--                        , show (V.length hVectorInit)
--                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> Rep ORArray (X (ADRnnMnistParameters ORArray r))
            -> r
      ftest batch_size mnistData pars =
        MnistRnnRanked2.rnnMnistTestR
          batch_size mnistData (parseHVector valsInit pars)
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
                    $ repDeepDuplicable stensorKind hVector)
           runBatch :: ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                       , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                          , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r
                   -> Rep (ADVal ORArray) (X (ADRnnMnistParameters ORArray r))
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = extendEnv var varInputs emptyEnv
                       envMnist = extendEnv varGlyph (rconst $ Nested.rfromOrthotope SNat glyph)
                                  $ extendEnv varLabel (rconst $ Nested.rfromOrthotope SNat label) env
                   in interpretAst envMnist $ unAstRanked ast
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdamDeep f chunkR parameters stateAdam
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
                    -> ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                       , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
                    -> IO (Rep ORArray (X (ADRnnMnistParameters ORArray r)))
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
          :: ADRnnMnistParametersShaped OSArray width r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        valsInit :: ADRnnMnistParameters ranked r
        valsInit = forgetShape valsInitShaped
        hVectorInit = toHVector $ AsHVector valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show width, show miniBatchSize
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
        ftest batch_size mnistData pars =
          MnistRnnRanked2.rnnMnistTestR
            batch_size
            mnistData
            (unAsHVector $ parseHVector (AsHVector valsInit) pars)
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
           f = \ (AsHVector (pars, (glyphR, labelR))) ->
             MnistRnnRanked2.rnnMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           (artRaw, _) = revArtifactAdapt False f (AsHVector (valsInit, dataInit))
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

mnistTestCaseRNND
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNND prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
 -- TODO: use withKnownNat when we no longer support GHC 9.4
 case someNatVal $ toInteger width of
  Nothing -> error "impossible someNatVal error"
  Just (SomeNat @width _) ->
    let valsInitShaped
          :: ADRnnMnistParametersShaped OSArray width r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        valsInit :: ADRnnMnistParameters ranked r
        valsInit = forgetShape valsInitShaped
        hVectorInit :: Rep ORArray (X (ADRnnMnistParameters ORArray r))
--        hVectorInit = unrepDeep @ORArray @(X (ADRnnMnistParameters ORArray r))
--                      $ toHVector valsInit
        hVectorInit = toHVector valsInit
        ftk = tshapeFull @ORArray
                         (stensorKind @(X (ADRnnMnistParameters ORArray r)))
                         hVectorInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show width, show miniBatchSize ]
--                          , show (V.length hVectorInit)
--                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r
              -> Rep ORArray (X (ADRnnMnistParameters ORArray r))
              -> r
        ftest batch_size mnistData pars =
          MnistRnnRanked2.rnnMnistTestR
            batch_size mnistData (parseHVector valsInit pars)
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
           f :: ( ADRnnMnistParameters (AstRanked FullSpan) r
                , (AstRanked FullSpan r 3, AstRanked FullSpan r 2) )
             -> AstRanked FullSpan r 0
           f = \ (pars, (glyphR, labelR)) ->
             MnistRnnRanked2.rnnMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           (artRaw, _) = revArtifactAdapt False f (valsInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchR r]
              -> ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                 , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
              -> ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                 , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = rconst $ Nested.rfromOrthotope SNat glyph
                 labelD = rconst $ Nested.rfromOrthotope SNat label
                 parametersAndInput = (parameters, (glyphD, labelD))
                 (gradient, _gradientOnInput) =
                   fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdamDeep
                           @(X (ADRnnMnistParameters ORArray r))
                           defaultArgsAdam stateAdam parameters gradient)
           runBatch :: ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                       , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                          , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
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
                    -> ( Rep ORArray (X (ADRnnMnistParameters ORArray r))
                       , StateAdamDeep (X (ADRnnMnistParameters ORArray r)) )
                    -> IO (Rep ORArray (X (ADRnnMnistParameters ORArray r)))
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

{-# SPECIALIZE mnistTestCaseRNND
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
  , mnistTestCaseRNND "RNNOD 1 epoch, 1 batch" 1 1 128 5 500
                       (0.898 :: Double)
  , mnistTestCaseRNND "RNNOD artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNND "RNNOD artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNND "RNNOD 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for RNN MNIST tests"
  [ testCase "RNNOPP" testRNNOPP
  , testCase "RNNOPP2" testRNNOPP2
  ]

valsInitRNNOPP
  :: Int -> Int -> ADRnnMnistParameters ORArray Double
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
      afcnn2T :: ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m12 x1 -> let m3 = rreshape [2,1] (rreplicate 2 0.0) ; t4 = rtranspose [1,0] (rreplicate 1 (rslice 0 1 m3)) ; m5 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t4)) ; t6 = rtranspose [1,0] (rreplicate 1 (rslice 0 1 m3)) ; m7 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t6)) ; t8 = rtranspose [1,0] (rreplicate 1 m7) ; t9 = rtranspose [1,0] (rreplicate 1 (rslice 1 1 m3)) ; m10 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t8) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * t9)) ; t11 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m5 m10))) ; m13 = rappend (rreshape [1,1] (rreplicate 1 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 m1))) * rreplicate 1 m12))) (rreshape [0,1] (rreplicate 0 0.0))) ; m14 = (rconst (rfromListLinear [1,1] [1.0]) - m10 * m10) * rslice 1 1 m13 ; t15 = rreplicate 1 m14 ; t16 = rreplicate 1 m14 ; m17 = (rconst (rfromListLinear [1,1] [1.0]) - m7 * m7) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t16)) ; t18 = rreplicate 1 m17 ; m19 = (rconst (rfromListLinear [1,1] [1.0]) - m5 * m5) * rslice 0 1 m13 ; t20 = rreplicate 1 m19 in tpair (tpair (tpair (tpair (rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m19)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rreplicate 1 m17)), rsum (rtranspose [2,1,0] (t4 * t20)) + rsum (rtranspose [2,1,0] (t6 * t18))), rsum (rtranspose [1,0] m19) + rsum (rtranspose [1,0] m17)), tpair (tpair (rsum (rtranspose [2,1,0] (t8 * t16)), rsum (rtranspose [2,1,0] (t9 * t15))), rsum (rtranspose [1,0] m14))), tpair (rsum (rtranspose [2,1,0] (t11 * rreplicate 1 m12)), rsum (rtranspose [1,0] m12)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let m3 = rreshape [2,1] (rreplicate 2 0.0) ; t4 = rtranspose [1,0] (rreplicate 1 (rslice 0 1 m3)) ; m5 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t4)) ; t6 = rtranspose [1,0] (rreplicate 1 (rslice 0 1 m3)) ; m7 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t6)) ; t8 = rtranspose [1,0] (rreplicate 1 m7) ; t9 = rtranspose [1,0] (rreplicate 1 (rslice 1 1 m3)) ; m10 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t8) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * t9)) ; t11 = rtranspose [1,0] (rreplicate 10 (rslice 1 1 (rappend m5 m10))) in rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 m1))) * t11) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 m1)))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m12 x1 -> let m5 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m7 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m10 = tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 m7)) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))))) ; m13 = rappend (rconst (rfromListLinear [1,1] [0.0])) (rappend (rsum (rtranspose [1,2,0] (rreplicate 1 (tproject1 (tproject2 m1))) * rtranspose [1,0] (rreplicate 1 m12))) (rreplicate 0 (rreplicate 1 0.0))) ; m14 = (rconst (rfromListLinear [1,1] [1.0]) - m10 * m10) * rslice 1 1 m13 ; m17 = (rconst (rfromListLinear [1,1] [1.0]) - m7 * m7) * rsum (rtranspose [1,2,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 m14)) ; m19 = (rconst (rfromListLinear [1,1] [1.0]) - m5 * m5) * rslice 0 1 m13 in tpair (tpair (tpair (tpair (rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m19)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0))) * rtranspose [2,1,0] (rreplicate 1 m17)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m19)) + rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m17))), rsum (rtranspose [1,0] m19) + rsum (rtranspose [1,0] m17)), tpair (tpair (rsum (rtranspose [2,0,1] (rreplicate 1 m7) * rtranspose [2,1,0] (rreplicate 1 m14)), rsum (rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0))) * rtranspose [2,1,0] (rreplicate 1 m14))), rsum (rtranspose [1,0] m14))), tpair (rsum (rtranspose [2,0,1] (rreplicate 10 m10) * rtranspose [2,1,0] (rreplicate 1 m12)), rsum (rtranspose [1,0] m12)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 m1))) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (tanh (rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 1 (rreplicate 1 (rreplicate 1 0.0)))))))) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 m1)))"
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
      afcnn2T :: ADRnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifactRev, _) =
        revArtifactAdapt True afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printArtifactPretty renames artifactRev
    @?= "\\m21 x1 -> let m4 = rreshape [4,2] (rreplicate 8 0.0) ; t5 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m4)) ; m6 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t5)) ; t7 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m4)) ; m8 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t7)) ; t9 = rtranspose [1,0] (rreplicate 2 m8) ; t10 = rtranspose [1,0] (rreplicate 2 (rslice 2 2 m4)) ; m11 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t9) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * t10)) ; m12 = rappend m6 m11 ; t13 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)) ; m14 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t13)) ; t15 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t15)) ; t17 = rtranspose [1,0] (rreplicate 2 m16) ; t18 = rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t17) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * t18)) ; t20 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m14 m19))) ; m22 = rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject2 m1))) * rreplicate 2 m21))) (rreshape [0,2] (rreplicate 0 0.0))) ; m23 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * rslice 2 2 m22 ; t24 = rreplicate 2 m23 ; t25 = rreplicate 2 m23 ; m26 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t25)) ; t27 = rreplicate 2 m26 ; m28 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * rslice 0 2 m22 ; t29 = rreplicate 2 m28 ; m30 = rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t29))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [0,2] (rreplicate 0 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t27))) (rreshape [2,2] (rreplicate 4 0.0))) + rappend (rreshape [2,2] (rreplicate 4 0.0)) (rappend (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * t24))) (rreshape [0,2] (rreplicate 0 0.0))) ; m31 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m11 * m11) * rslice 2 2 m30 ; t32 = rreplicate 2 m31 ; t33 = rreplicate 2 m31 ; m34 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m8 * m8) * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t33)) ; t35 = rreplicate 2 m34 ; m36 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m6 * m6) * rslice 0 2 m30 ; t37 = rreplicate 2 m36 in tpair (tpair (tpair (tpair (rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m36)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m34)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m28)) + rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rreplicate 2 m26)), rsum (rtranspose [2,1,0] (t5 * t37)) + rsum (rtranspose [2,1,0] (t7 * t35)) + rsum (rtranspose [2,1,0] (t13 * t29)) + rsum (rtranspose [2,1,0] (t15 * t27))), rsum (rtranspose [1,0] m36) + rsum (rtranspose [1,0] m34) + rsum (rtranspose [1,0] m28) + rsum (rtranspose [1,0] m26)), tpair (tpair (rsum (rtranspose [2,1,0] (t9 * t33)) + rsum (rtranspose [2,1,0] (t17 * t25)), rsum (rtranspose [2,1,0] (t10 * t32)) + rsum (rtranspose [2,1,0] (t18 * t24))), rsum (rtranspose [1,0] m31) + rsum (rtranspose [1,0] m23))), tpair (rsum (rtranspose [2,1,0] (t20 * rreplicate 2 m21)), rsum (rtranspose [1,0] m21)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let m4 = rreshape [4,2] (rreplicate 8 0.0) ; t5 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m4)) ; m6 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t5)) ; t7 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m4)) ; m8 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t7)) ; t9 = rtranspose [1,0] (rreplicate 2 m8) ; t10 = rtranspose [1,0] (rreplicate 2 (rslice 2 2 m4)) ; m11 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t9) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * t10)) ; m12 = rappend m6 m11 ; t13 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)) ; m14 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t13)) ; t15 = rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * t15)) ; t17 = rtranspose [1,0] (rreplicate 2 m16) ; t18 = rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * t17) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * t18)) ; t20 = rtranspose [1,0] (rreplicate 10 (rslice 2 2 (rappend m14 m19))) in rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject2 m1))) * t20) + rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 m1)))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m21 x1 -> let m6 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m8 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m11 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 m8)) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))))) ; m12 = rappend m6 m11 ; m14 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m16 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12)))) ; m19 = tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 m16)) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12)))) ; m22 = rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 (tproject1 (tproject2 m1))) * rtranspose [1,0] (rreplicate 2 m21))) (rreplicate 0 (rreplicate 2 0.0))) ; m23 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m19 * m19) * rslice 2 2 m22 ; m26 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * rsum (rtranspose [1,2,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 m23)) ; m28 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * rslice 0 2 m22 ; m30 = rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 m28))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 0 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 m26))) (rreplicate 2 (rreplicate 2 0.0))) + rappend (rreplicate 2 (rreplicate 2 0.0)) (rappend (rsum (rtranspose [1,2,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 m23))) (rreplicate 0 (rreplicate 2 0.0))) ; m31 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m11 * m11) * rslice 2 2 m30 ; m34 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m8 * m8) * rsum (rtranspose [1,2,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 m31)) ; m36 = (rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0]) - m6 * m6) * rslice 0 2 m30 in tpair (tpair (tpair (tpair (rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m36)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m34)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0))) * rtranspose [2,1,0] (rreplicate 2 m26)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m36)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m34)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m28)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 0 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m26))), rsum (rtranspose [1,0] m36) + rsum (rtranspose [1,0] m34) + rsum (rtranspose [1,0] m28) + rsum (rtranspose [1,0] m26)), tpair (tpair (rsum (rtranspose [2,0,1] (rreplicate 2 m8) * rtranspose [2,1,0] (rreplicate 2 m31)) + rsum (rtranspose [2,0,1] (rreplicate 2 m16) * rtranspose [2,1,0] (rreplicate 2 m23)), rsum (rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0))) * rtranspose [2,1,0] (rreplicate 2 m31)) + rsum (rtranspose [2,0,1] (rreplicate 2 (rslice 2 2 m12)) * rtranspose [2,1,0] (rreplicate 2 m23))), rsum (rtranspose [1,0] m31) + rsum (rtranspose [1,0] m23))), tpair (rsum (rtranspose [2,0,1] (rreplicate 10 m19) * rtranspose [2,1,0] (rreplicate 2 m21)), rsum (rtranspose [1,0] m21)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let m12 = rappend (tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) (tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 0.0)))))) in rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject2 m1))) * rtranspose [1,0] (rreplicate 10 (tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (tanh (rtranspose [1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 m1)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rreplicate 2 7.0)))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rslice 0 2 m12))))))) + rsum (rtranspose [2,1,0] (rreplicate 2 (tproject2 (tproject1 (tproject2 (tproject1 m1))))) * rtranspose [1,0] (rreplicate 2 (rslice 2 2 m12))))))) + rtranspose [1,0] (rreplicate 2 (tproject2 (tproject2 m1)))"
