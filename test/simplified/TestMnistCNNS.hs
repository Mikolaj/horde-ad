{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Tests of "MnistCnnShaped2" concolutional neural network
-- using a few different optimization pipelines.
module TestMnistCNNS
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import GHC.TypeLits (KnownNat, type (<=))
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

import MnistCnnShaped2 qualified
import MnistData

-- TODO: optimize enough that it can run for one full epoch in reasonable time
-- and then verify it trains down to ~20% validation error in a short enough
-- time to include such a training run in tests.

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsCNNSA
            , tensorADValMnistTestsCNNSI
            , tensorADValMnistTestsCNNSO
            ]

type XParams kh kw c_out n_hidden r =
  X (MnistCnnShaped2.ADCnnMnistParametersShaped
       Concrete SizeMnistHeight SizeMnistWidth kh kw c_out n_hidden r)

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseCNNSA
  :: forall kh kw r.
     ( 1 <= kh, 1 <= kw
     , Differentiable r, GoodScalar r, PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> SNat kh -> SNat kw -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNSA prefix epochs maxBatches kh@SNat kw@SNat c_outInt n_hiddenInt
                   miniBatchSizeInt totalBatchSize expected =
  withSNat c_outInt $ \(_c_outSNat :: SNat c_out) ->
  withSNat n_hiddenInt $ \(_n_hiddenSNat :: SNat n_hidden) ->
  withSNat miniBatchSizeInt $ \(miniBatchSize :: SNat miniBatchSize) ->
  let targetInit =
        fst $ randomValue
                @(Concrete (X (MnistCnnShaped2.ADCnnMnistParametersShaped
                                 Concrete SizeMnistHeight SizeMnistWidth
                                 kh kw c_out n_hidden r)))
                0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue kh), show (sNatValue kw)
                        , show c_outInt, show n_hiddenInt
                        , show miniBatchSizeInt
                        , show $ widthSTK $ knownSTK @(XParams kh kw c_out n_hidden r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: KnownNat batch_size
            => MnistDataBatchS batch_size r
            -> Concrete (XParams kh kw c_out n_hidden r) -> r
      ftest @batch_size mnistData pars =
        MnistCnnShaped2.convMnistTestS kh kw (SNat @c_out) (SNat @n_hidden)
          (SNat @batch_size) mnistData (fromTarget @Concrete pars)
  in testCase name $ do
      hPutStrLn stderr $
        printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
               prefix epochs maxBatches
      trainData <- map mkMnistDataS
                   <$> loadMnistData trainGlyphsPath trainLabelsPath
      testData <- map mkMnistDataS . take (totalBatchSize * maxBatches)
                  <$> loadMnistData testGlyphsPath testLabelsPath
      withSNat (totalBatchSize * maxBatches) $ \(SNat @lenTestData) -> do
       let testDataS = mkMnistDataBatchS testData
           f :: MnistDataBatchS miniBatchSize r
             -> ADVal Concrete (XParams kh kw c_out n_hidden r)
             -> ADVal Concrete (TKScalar r)
           f (glyphR, labelR) adinputs =
             MnistCnnShaped2.convMnistLossFusedS
               kh kw (SNat @c_out) (SNat @n_hidden)
               miniBatchSize (sconcrete glyphR, sconcrete labelR)
               (fromTarget adinputs)
           runBatch :: (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
                    -> (Int, [MnistDataS r])
                    -> IO (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map mkMnistDataBatchS
                          $ filter (\ch -> length ch == miniBatchSizeInt)
                          $ chunksOf miniBatchSizeInt chunk
                 res@(parameters2, _) =
                   sgdAdam f chunkS parameters stateAdam
                 trainScore = withSNat (length chunk) $ \(SNat @len) ->
                   ftest @len (mkMnistDataBatchS chunk) parameters2
                 testScore = ftest @lenTestData testDataS parameters2
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
                    -> (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
                    -> IO (Concrete (XParams kh kw c_out n_hidden r))
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
           ftk = tftk @Concrete (knownSTK @(XParams kh kw c_out n_hidden r)) targetInit
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal =
             1 - ftest testDataS res
       testErrorFinal @?~ expected

tensorADValMnistTestsCNNSA :: TestTree
tensorADValMnistTestsCNNSA = testGroup "CNNS ADVal MNIST tests"
  [ mnistTestCaseCNNSA "CNNSA 1 epoch, 1 batch"
                       1 1 (SNat @2) (SNat @2) 4 4 1 1
                       (1 :: Double)
  , mnistTestCaseCNNSA "CNNSA artificial 1 2 3 4 5"
                       1 1 (SNat @2) (SNat @3) 4 5 1 1
                       (1 :: Float)
  , mnistTestCaseCNNSA "CNNSA artificial 5 4 3 2 1"
                       1 4 (SNat @3) (SNat @2) 1 1 1 1
                       (1 :: Double)
-- TODO: NaNs
--  , mnistTestCaseCNNSA "CNNSA 1 epoch, 0 batch"
--                       1 0 (SNat @4) (SNat @4) 64 16 5 50
--                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
_mnistTestCaseCNNSI
  :: forall kh kw r.
     ( 1 <= kh, 1 <= kw
     , Differentiable r, GoodScalar r, PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> SNat kh -> SNat kw -> Int -> Int -> Int -> Int -> r
  -> TestTree
_mnistTestCaseCNNSI prefix epochs maxBatches kh@SNat kw@SNat c_outInt n_hiddenInt
                   miniBatchSizeInt totalBatchSize expected =
  withSNat c_outInt $ \(_c_outSNat :: SNat c_out) ->
  withSNat n_hiddenInt $ \(_n_hiddenSNat :: SNat n_hidden) ->
  withSNat miniBatchSizeInt $ \(miniBatchSize :: SNat miniBatchSize) ->
  let targetInit =
        fst $ randomValue
                @(Concrete (X (MnistCnnShaped2.ADCnnMnistParametersShaped
                                 Concrete SizeMnistHeight SizeMnistWidth
                                 kh kw c_out n_hidden r)))
                0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue kh), show (sNatValue kw)
                        , show c_outInt, show n_hiddenInt
                        , show miniBatchSizeInt
                        , show $ widthSTK $ knownSTK @(XParams kh kw c_out n_hidden r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: KnownNat batch_size
            => MnistDataBatchS batch_size r
            -> Concrete (XParams kh kw c_out n_hidden r) -> r
      ftest @batch_size mnistData pars =
        MnistCnnShaped2.convMnistTestS kh kw (SNat @c_out) (SNat @n_hidden)
          (SNat @batch_size) mnistData (fromTarget @Concrete pars)
  in testCase name $ do
      hPutStrLn stderr $
        printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
               prefix epochs maxBatches
      trainData <- map mkMnistDataS
                   <$> loadMnistData trainGlyphsPath trainLabelsPath
      testData <- map mkMnistDataS . take (totalBatchSize * maxBatches)
                  <$> loadMnistData testGlyphsPath testLabelsPath
      withSNat (totalBatchSize * maxBatches) $ \(SNat @lenTestData) -> do
       let testDataS = mkMnistDataBatchS testData
           ftk = tftk @Concrete (knownSTK @(XParams kh kw c_out n_hidden r)) targetInit
       (_, _, var, varAst2) <- funToAstRevIO ftk
       (varGlyph, astGlyph) <-
         funToAstIO (FTKS (miniBatchSize
                           :$$ sizeMnistHeight
                           :$$ sizeMnistWidth
                           :$$ ZSS) FTKScalar) id
       (varLabel, astLabel) <-
         funToAstIO (FTKS (miniBatchSize
                           :$$ sizeMnistLabel
                           :$$ ZSS) FTKScalar) id
       let ast :: AstTensor AstMethodLet FullSpan (TKScalar r)
           ast = MnistCnnShaped2.convMnistLossFusedS
                   kh kw (SNat @c_out) (SNat @n_hidden)
                   miniBatchSize (astGlyph, astLabel)
                   (fromTarget varAst2)
           f :: MnistDataBatchS miniBatchSize r
             -> ADVal Concrete (XParams kh kw c_out n_hidden r)
             -> ADVal Concrete (TKScalar r)
           f (glyph, label) varInputs =
             let env = extendEnv var varInputs emptyEnv
                 envMnist = extendEnv varGlyph (sconcrete glyph)
                            $ extendEnv varLabel (sconcrete label) env
             in interpretAstFull envMnist ast
           runBatch :: (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
                    -> (Int, [MnistDataS r])
                    -> IO (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map mkMnistDataBatchS
                          $ filter (\ch -> length ch == miniBatchSizeInt)
                          $ chunksOf miniBatchSizeInt chunk
                 res@(parameters2, _) =
                   sgdAdam f chunkS parameters stateAdam
                 !trainScore = withSNat (length chunk) $ \(SNat @len) ->
                   ftest @len (mkMnistDataBatchS chunk) parameters2
                 !testScore = ftest @lenTestData testDataS parameters2
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
                    -> (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
                    -> IO (Concrete (XParams kh kw c_out n_hidden r))
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
             1 - ftest testDataS res
       testErrorFinal @?~ expected

tensorADValMnistTestsCNNSI :: TestTree
tensorADValMnistTestsCNNSI = testGroup "CNNS Intermediate MNIST tests"
  [
-- TODO: OOMS
--    mnistTestCaseCNNSI "CNNSI 1 epoch, 1 batch"
--                       1 1 (SNat @2) (SNat @2) 4 4 1 1
--                       (1 :: Double)
--  ,  mnistTestCaseCNNSI "CNNSI artificial 1 2 3 4 5"
--                       1 1 (SNat @2) (SNat @3) 4 5 1 1
--                       (1 :: Float)
--  , mnistTestCaseCNNSI "CNNSI artificial 5 4 3 2 1"
--                       1 4 (SNat @3) (SNat @2) 1 1 1 1
--                       (1 :: Double)
--  , mnistTestCaseCNNSI "CNNSI 1 epoch, 0 batch"
--                       1 0 (SNat @4) (SNat @4) 64 16 5 50
--                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
_mnistTestCaseCNNSO
  :: forall kh kw r.
     ( 1 <= kh, 1 <= kw
     , Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> SNat kh -> SNat kw -> Int -> Int -> Int -> Int -> r
  -> TestTree
_mnistTestCaseCNNSO prefix epochs maxBatches kh@SNat kw@SNat c_outInt n_hiddenInt
                   miniBatchSizeInt totalBatchSize expected =
  withSNat c_outInt $ \(_c_outSNat :: SNat c_out) ->
  withSNat n_hiddenInt $ \(_n_hiddenSNat :: SNat n_hidden) ->
  withSNat miniBatchSizeInt $ \(miniBatchSize :: SNat miniBatchSize) ->
  let targetInit =
        fst $ randomValue
                @(Concrete (X (MnistCnnShaped2.ADCnnMnistParametersShaped
                                 Concrete SizeMnistHeight SizeMnistWidth
                                 kh kw c_out n_hidden r)))
                0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue kh), show (sNatValue kw)
                        , show c_outInt, show n_hiddenInt
                        , show miniBatchSizeInt
                        , show $ widthSTK $ knownSTK @(XParams kh kw c_out n_hidden r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: KnownNat batch_size
            => MnistDataBatchS batch_size r
            -> Concrete (XParams kh kw c_out n_hidden r) -> r
      ftest @batch_size mnistData pars =
        MnistCnnShaped2.convMnistTestS kh kw (SNat @c_out) (SNat @n_hidden)
          (SNat @batch_size) mnistData (fromTarget @Concrete pars)
  in testCase name $ do
      hPutStrLn stderr $
        printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
               prefix epochs maxBatches
      trainData <- map mkMnistDataS
                   <$> loadMnistData trainGlyphsPath trainLabelsPath
      testData <- map mkMnistDataS . take (totalBatchSize * maxBatches)
                  <$> loadMnistData testGlyphsPath testLabelsPath
      withSNat (totalBatchSize * maxBatches) $ \(SNat @lenTestData) -> do
       let testDataS = mkMnistDataBatchS testData
           dataInit = case chunksOf miniBatchSizeInt testData of
             d : _ -> let (dglyph, dlabel) = mkMnistDataBatchS d
                      in (sconcrete dglyph, sconcrete dlabel)
             [] -> error "empty test data"
           f :: ( MnistCnnShaped2.ADCnnMnistParametersShaped
                    (AstTensor AstMethodLet FullSpan)
                    SizeMnistHeight SizeMnistWidth
                    kh kw c_out n_hidden r
                , ( AstTensor AstMethodLet FullSpan (TKS '[miniBatchSize, SizeMnistHeight, SizeMnistWidth] r)
                  , AstTensor AstMethodLet FullSpan (TKS '[miniBatchSize, SizeMnistLabel] r) ) )
             -> AstTensor AstMethodLet FullSpan (TKScalar r)
           f = \ (pars, (glyphR, labelR)) ->
             MnistCnnShaped2.convMnistLossFusedS
               kh kw (SNat @c_out) (SNat @n_hidden)
               miniBatchSize (sprimalPart glyphR, sprimalPart labelR) pars
           artRaw = gradArtifact f (fromTarget targetInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchS miniBatchSize r]
              -> (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
              -> (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let parametersAndInput =
                   tpair parameters (tpair (sconcrete glyph) (sconcrete label))
                 gradient =
                   tproject1 $ fst
                   $ revInterpretArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdam
                           @(XParams kh kw c_out n_hidden r)
                           defaultArgsAdam stateAdam knownSTK parameters
                           gradient)
           runBatch :: (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
                    -> (Int, [MnistDataS r])
                    -> IO (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map mkMnistDataBatchS
                          $ filter (\ch -> length ch == miniBatchSizeInt)
                          $ chunksOf miniBatchSizeInt chunk
                 res@(parameters2, _) = go chunkS (parameters, stateAdam)
                 trainScore = withSNat (length chunk) $ \(SNat @len) ->
                   ftest @len (mkMnistDataBatchS chunk) parameters2
                 testScore = ftest @lenTestData testDataS parameters2
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
                    -> (Concrete (XParams kh kw c_out n_hidden r), StateAdam (XParams kh kw c_out n_hidden r))
                    -> IO (Concrete (XParams kh kw c_out n_hidden r))
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
           ftk = tftk @Concrete (knownSTK @(XParams kh kw c_out n_hidden r)) targetInit
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal =
             1 - ftest testDataS res
       assertEqualUpToEpsilon 1e-1 expected testErrorFinal

tensorADValMnistTestsCNNSO :: TestTree
tensorADValMnistTestsCNNSO = testGroup "CNNS Once MNIST tests"
  [
-- TODO: OOMS
--    mnistTestCaseCNNSO "CNNSO 1 epoch, 1 batch"
--                       1 1 (SNat @2) (SNat @2) 4 4 1 1
--                       (1 :: Double)
--  , mnistTestCaseCNNSO "CNNSO artificial 1 2 3 4 5"
--                       1 1 (SNat @2) (SNat @3) 4 5 1 1
--                       (1 :: Float)
--  , mnistTestCaseCNNSO "CNNSO artificial 5 4 3 2 1"
--                       1 4 (SNat @3) (SNat @2) 1 1 1 1
--                       (1 :: Double)
--    , mnistTestCaseCNNSO "CNNSO 1 epoch, 0 batch"
--                       1 0 (SNat @4) (SNat @4) 64 16 5 50
--                       (1.0 :: Float)
  ]
