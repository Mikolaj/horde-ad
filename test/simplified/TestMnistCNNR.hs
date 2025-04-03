{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | Tests of "MnistCnnRanked2" concolutional neural network
-- using a few different optimization pipelines.
module TestMnistCNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Text.Printf

import Data.Array.Nested.Internal.Shape

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret

import EqEpsilon

import MnistCnnRanked2 qualified
import MnistData

-- TODO: optimize enough that it can run for one full epoch in reasonable time
-- and then verify it trains down to ~20% validation error in a short enough
-- time to include such a training run in tests.

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsCNNRA
            , tensorADValMnistTestsCNNRI
            , tensorADValMnistTestsCNNRO
            ]

type XParams r = X (MnistCnnRanked2.ADCnnMnistParameters Concrete r)

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseCNNRA
  :: forall r.
     (Differentiable r, GoodScalar r, PrintfArg r, AssertEqualUpToEpsilon r)
  => String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNRA prefix epochs maxBatches khInt kwInt c_outInt n_hiddenInt
                   miniBatchSize totalBatchSize expected =
  withSNat khInt $ \(_khSNat :: SNat kh) ->
  withSNat kwInt $ \(_kwSNat :: SNat kw) ->
  withSNat c_outInt $ \(_c_outSNat :: SNat c_out) ->
  withSNat n_hiddenInt $ \(_n_hiddenSNat :: SNat n_hidden) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue
            @(Concrete (X (MnistCnnRanked2.ADCnnMnistParametersShaped
                             Concrete SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)))
            0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show khInt, show kwInt
                        , show c_outInt, show n_hiddenInt
                        , show miniBatchSize
                        , show $ widthSTK $ knownSTK @(XParams r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: Int -> MnistDataBatchR r -> Concrete (XParams r) -> r
      ftest batch_size mnistData pars =
        MnistCnnRanked2.convMnistTestR
          batch_size mnistData (fromTarget @Concrete pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map mkMnistDataR
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map mkMnistDataR . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = mkMnistDataBatchR testData
           f :: MnistDataBatchR r -> ADVal Concrete (XParams r)
             -> ADVal Concrete (TKScalar r)
           f (glyphR, labelR) adinputs =
             MnistCnnRanked2.convMnistLossFusedR
               miniBatchSize (rconcrete glyphR, rconcrete labelR)
               (fromTarget adinputs)
           runBatch :: (Concrete (XParams r), StateAdam (XParams r))
                    -> (Int, [MnistDataR r])
                    -> IO (Concrete (XParams r), StateAdam (XParams r))
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map mkMnistDataBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) =
                   sgdAdam f chunkR parameters stateAdam
                 trainScore =
                   ftest (length chunk) (mkMnistDataBatchR chunk) parameters2
                 testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 lenChunk = length chunk
             unless (n_hiddenInt < 10) $ do
               hPutStrLn stderr $
                 printf "\n%s: (Batch %d with %d points)"
                        prefix k lenChunk
               hPutStrLn stderr $
                 printf "%s: Training error:   %.2f%%"
                        prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $
                 printf "%s: Validation error: %.2f%%"
                        prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> (Concrete (XParams r), StateAdam (XParams r))
                    -> IO (Concrete (XParams r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (n_hiddenInt < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
           ftk = tftk @Concrete (knownSTK @(XParams r)) targetInit
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseCNNRA
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsCNNRA :: TestTree
tensorADValMnistTestsCNNRA = testGroup "CNNR ADVal MNIST tests"
  [ mnistTestCaseCNNRA "CNNRA 1 epoch, 1 batch" 1 1 2 2 4 4 1 1
                       (1 :: Double)
  , mnistTestCaseCNNRA "CNNRA artificial 1 2 3 4 5" 1 1 2 3 4 5 1 1
                       (1 :: Float)
  , mnistTestCaseCNNRA "CNNRA artificial 5 4 3 2 1" 1 4 3 2 1 1 1 1
                       (1 :: Double)
  , mnistTestCaseCNNRA "CNNRA 1 epoch, 0 batch" 1 0 4 4 64 16 5 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseCNNRI
  :: forall r.
     (Differentiable r, GoodScalar r, PrintfArg r, AssertEqualUpToEpsilon r)
  => String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNRI prefix epochs maxBatches khInt kwInt c_outInt n_hiddenInt
                   miniBatchSize totalBatchSize expected =
  withSNat khInt $ \(_khSNat :: SNat kh) ->
  withSNat kwInt $ \(_kwSNat :: SNat kw) ->
  withSNat c_outInt $ \(_c_outSNat :: SNat c_out) ->
  withSNat n_hiddenInt $ \(_n_hiddenSNat :: SNat n_hidden) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue
            @(Concrete (X (MnistCnnRanked2.ADCnnMnistParametersShaped
                             Concrete SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)))
            0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show khInt, show kwInt
                        , show c_outInt, show n_hiddenInt
                        , show miniBatchSize
                        , show $ widthSTK $ knownSTK @(XParams r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: Int -> MnistDataBatchR r -> Concrete (XParams r) -> r
      ftest batch_size mnistData pars =
        MnistCnnRanked2.convMnistTestR
          batch_size mnistData (fromTarget @Concrete pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map mkMnistDataR
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map mkMnistDataR . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = mkMnistDataBatchR testData
           ftk = tftk @Concrete (knownSTK @(XParams r)) targetInit
       (_, _, var, varAst2) <- funToAstRevIO ftk
       (varGlyph, astGlyph) <-
         funToAstIO (FTKR (miniBatchSize
                           :$: sizeMnistHeightInt
                           :$: sizeMnistWidthInt
                           :$: ZSR) FTKScalar) id
       (varLabel, astLabel) <-
         funToAstIO (FTKR (miniBatchSize
                           :$: sizeMnistLabelInt
                           :$: ZSR) FTKScalar) id
       let ast :: AstTensor AstMethodLet FullSpan (TKScalar r)
           ast = MnistCnnRanked2.convMnistLossFusedR
                   miniBatchSize (astGlyph, astLabel)
                   (fromTarget varAst2)
           f :: MnistDataBatchR r -> ADVal Concrete (XParams r)
             -> ADVal Concrete (TKScalar r)
           f (glyph, label) varInputs =
             let env = extendEnv var varInputs emptyEnv
                 envMnist = extendEnv varGlyph (rconcrete glyph)
                            $ extendEnv varLabel (rconcrete label) env
             in interpretAstFull envMnist ast
           runBatch :: (Concrete (XParams r), StateAdam (XParams r))
                    -> (Int, [MnistDataR r])
                    -> IO (Concrete (XParams r), StateAdam (XParams r))
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map mkMnistDataBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) =
                   sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (mkMnistDataBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (n_hiddenInt < 10) $ do
               hPutStrLn stderr $
                 printf "\n%s: (Batch %d with %d points)"
                        prefix k lenChunk
               hPutStrLn stderr $
                 printf "%s: Training error:   %.2f%%"
                        prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $
                 printf "%s: Validation error: %.2f%%"
                        prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> (Concrete (XParams r), StateAdam (XParams r))
                    -> IO (Concrete (XParams r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (n_hiddenInt < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseCNNRI
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsCNNRI :: TestTree
tensorADValMnistTestsCNNRI = testGroup "CNNR Intermediate MNIST tests"
  [ mnistTestCaseCNNRI "CNNRI 1 epoch, 1 batch" 1 1 2 2 4 4 1 1
                       (1 :: Double)
  , mnistTestCaseCNNRI "CNNRI artificial 1 2 3 4 5" 1 1 2 3 4 5 1 1
                       (1 :: Float)
  , mnistTestCaseCNNRI "CNNRI artificial 5 4 3 2 1" 1 4 3 2 1 1 1 1
                       (1 :: Double)
  , mnistTestCaseCNNRI "CNNRI 1 epoch, 0 batch" 1 0 4 4 64 16 5 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseCNNRO
  :: forall r.
     ( Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNRO prefix epochs maxBatches khInt kwInt c_outInt n_hiddenInt
                   miniBatchSize totalBatchSize expected =
  withSNat khInt $ \(_khSNat :: SNat kh) ->
  withSNat kwInt $ \(_kwSNat :: SNat kw) ->
  withSNat c_outInt $ \(_c_outSNat :: SNat c_out) ->
  withSNat n_hiddenInt $ \(_n_hiddenSNat :: SNat n_hidden) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue
            @(Concrete (X (MnistCnnRanked2.ADCnnMnistParametersShaped
                             Concrete SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)))
            0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show khInt, show kwInt
                        , show c_outInt, show n_hiddenInt
                        , show miniBatchSize
                        , show $ widthSTK $ knownSTK @(XParams r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: Int -> MnistDataBatchR r -> Concrete (XParams r) -> r
      ftest batch_size mnistData pars =
        MnistCnnRanked2.convMnistTestR
          batch_size mnistData (fromTarget @Concrete pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map mkMnistDataR
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map mkMnistDataR . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = mkMnistDataBatchR testData
           dataInit = case chunksOf miniBatchSize testData of
             d : _ -> let (dglyph, dlabel) = mkMnistDataBatchR d
                      in (rconcrete dglyph, rconcrete dlabel)
             [] -> error "empty test data"
           f :: ( MnistCnnRanked2.ADCnnMnistParameters
                    (AstTensor AstMethodLet FullSpan) r
                , ( AstTensor AstMethodLet FullSpan (TKR 3 r)
                  , AstTensor AstMethodLet FullSpan (TKR 2 r) ) )
             -> AstTensor AstMethodLet FullSpan (TKScalar r)
           f = \ (pars, (glyphR, labelR)) ->
             MnistCnnRanked2.convMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           artRaw = gradArtifact f (fromTarget targetInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchR r]
              -> (Concrete (XParams r), StateAdam (XParams r))
              -> (Concrete (XParams r), StateAdam (XParams r))
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let parametersAndInput =
                   tpair parameters (tpair (rconcrete glyph) (rconcrete label))
                 gradient =
                   tproject1 $ fst
                   $ revInterpretArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdam
                           @(XParams r)
                           defaultArgsAdam stateAdam knownSTK parameters
                           gradient)
           runBatch :: (Concrete (XParams r), StateAdam (XParams r))
                    -> (Int, [MnistDataR r])
                    -> IO (Concrete (XParams r), StateAdam (XParams r))
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map mkMnistDataBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = go chunkR (parameters, stateAdam)
                 trainScore =
                   ftest (length chunk) (mkMnistDataBatchR chunk) parameters2
                 testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 lenChunk = length chunk
             unless (n_hiddenInt < 10) $ do
               hPutStrLn stderr $
                 printf "\n%s: (Batch %d with %d points)"
                        prefix k lenChunk
               hPutStrLn stderr $
                 printf "%s: Training error:   %.2f%%"
                        prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $
                 printf "%s: Validation error: %.2f%%"
                        prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> (Concrete (XParams r), StateAdam (XParams r))
                    -> IO (Concrete (XParams r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (n_hiddenInt < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
           ftk = tftk @Concrete (knownSTK @(XParams r)) targetInit
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       assertEqualUpToEpsilon 1e-1 expected testErrorFinal

{-# SPECIALIZE mnistTestCaseCNNRO
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsCNNRO :: TestTree
tensorADValMnistTestsCNNRO = testGroup "CNNR Once MNIST tests"
  [ mnistTestCaseCNNRO "CNNRO 1 epoch, 1 batch" 1 1 2 2 4 4 1 1
                       (1 :: Double)
  , mnistTestCaseCNNRO "CNNRO artificial 1 2 3 4 5" 1 1 2 3 4 5 1 1
                       (1 :: Float)
  , mnistTestCaseCNNRO "CNNRO artificial 5 4 3 2 1" 1 4 3 2 1 1 1 1
                       (1 :: Double)
  , mnistTestCaseCNNRO "CNNRO 1 epoch, 0 batch" 1 0 4 4 64 16 5 50
                       (1.0 :: Float)
  ]
