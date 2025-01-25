-- | Tests of "MnistRnnShaped2" neural networks using a few different
-- optimization pipelines.
module TestMnistRNNS
  ( testTrees
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (foldM, unless)
import Numeric.LinearAlgebra (Numeric)
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Text.Printf

import Data.Array.Nested (KnownShS (..))
import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.External.OptimizerTools

import EqEpsilon

import MnistData
import MnistRnnShaped2 (ADRnnMnistParametersShaped)
import MnistRnnShaped2 qualified

type XParams out_width r =
 X (ADRnnMnistParametersShaped RepN SizeMnistHeight out_width r)

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNSA
            , tensorADValMnistTestsRNNSI
            , tensorADValMnistTestsRNNSO
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseRNNSA
  :: forall width batch_size r.
     ( Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSA prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize
                   expected =
  let valsInit :: ADRnnMnistParametersShaped
                    RepN SizeMnistHeight width r
      valsInit = fst $ randomVals 0.4 (mkStdGen 44)
      hVectorInit :: RepN (XParams width r)
      hVectorInit = toHVectorOf @RepN valsInit
      ftk = tftk @RepN
                       (stensorKind @(XParams width r))
                       hVectorInit
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width), show miniBatchSize ]
--                        , show (V.length hVectorInit)
--                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> RepN (XParams width r)
            -> r
      ftest 0 _ _ = 0
      ftest miniBatchSize' (glyphs, labels) testParams =
        assert (miniBatchSize' == rlength @_ @(TKScalar r) (RepN glyphs)) $
        withSNat miniBatchSize' $ \bs@SNat ->
          let mnist = ( Nested.rcastToShaped glyphs knownShS
                      , Nested.rcastToShaped labels knownShS )
          in MnistRnnShaped2.rnnMnistTestS
               width bs mnist (parseHVector @RepN testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: ( RepN (XParams width r)
                       , StateAdamDeep (XParams width r) )
                    -> (Int, [MnistDataS r])
                    -> IO ( RepN (XParams width r)
                          , StateAdamDeep (XParams width r) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchS batch_size r
                   -> ADVal RepN (XParams width r)
                   -> ADVal RepN (TKS '[] r)
                 f (glyphS, labelS) adinputs =
                   MnistRnnShaped2.rnnMnistLossFusedS
                     width batch_size (sconcrete glyphS, sconcrete labelS)
                     (parseHVector @(ADVal RepN) adinputs)
                 chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdamDeep @(MnistDataBatchS batch_size r) @(XParams width r) f chunkS parameters stateAdam
                 smnistRFromS (glyphs, labels) =
                   ( Nested.stoRanked glyphs
                   , Nested.stoRanked labels )
                 chunkDataR = packBatchR $ map smnistRFromS chunk
                 !trainScore =
                   ftest (length chunk) chunkDataR parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (sNatValue width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> ( RepN (XParams width r)
                       , StateAdamDeep (XParams width r) )
                    -> IO (RepN (XParams width r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < 10) $
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

{-# SPECIALIZE mnistTestCaseRNNSA
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSA :: TestTree
tensorADValMnistTestsRNNSA = testGroup "RNNS ADVal MNIST tests"
  [ mnistTestCaseRNNSA "RNNSA 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 50
                       (0.94 :: Double)
  , mnistTestCaseRNNSA "RNNSA artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSA "RNNSA artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNSA "RNNSA 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseRNNSI
  :: forall width batch_size r.
     ( Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSI prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize expected =
  let valsInit :: ADRnnMnistParametersShaped
                    RepN SizeMnistHeight width r
      valsInit = fst $ randomVals 0.4 (mkStdGen 44)
      hVectorInit :: RepN (XParams width r)
      hVectorInit = toHVectorOf @RepN valsInit
      ftk = tftk @RepN (stensorKind @(XParams width r))
                       hVectorInit
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width), show miniBatchSize ]
--                        , show (V.length hVectorInit)
--                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> RepN (XParams width r)
            -> r
      ftest 0 _ _ = 0
      ftest miniBatchSize' (glyphs, labels) testParams =
        assert (miniBatchSize' == rlength @_ @(TKScalar r) (RepN glyphs)) $
        assert (miniBatchSize' == rlength @_ @(TKScalar r) (RepN labels)) $
        withSNat miniBatchSize' $ \bs@SNat ->
          let mnist = ( Nested.rcastToShaped glyphs knownShS
                      , Nested.rcastToShaped labels knownShS )
          in MnistRnnShaped2.rnnMnistTestS
               width bs mnist (parseHVector @RepN testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, _, var, hVector) <- funToAstRevIO ftk
       let testDataR = packBatchR testData
       (varGlyph, astGlyph) <-
         funToAstIO (FTKS knownShS FTKScalar {-@'[batch_size, SizeMnistHeight, SizeMnistWidth]-}) id
       (varLabel, astLabel) <-
         funToAstIO (FTKS knownShS FTKScalar {-@'[batch_size, SizeMnistLabel]-}) id
       let ast :: AstTensor AstMethodLet FullSpan (TKS '[] r)
           ast = MnistRnnShaped2.rnnMnistLossFusedS
                   width batch_size (astGlyph, astLabel)
                   (parseHVector hVector)
           runBatch :: ( RepN (XParams width r)
                       , StateAdamDeep (XParams width r) )
                    -> (Int, [MnistDataS r])
                    -> IO ( RepN (XParams width r)
                          , StateAdamDeep (XParams width r) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchS batch_size r
                   -> ADVal RepN (XParams width r)
                   -> ADVal RepN (TKS '[] r)
                 f (glyph, label) varInputs =
                   let env = extendEnv @(ADVal RepN) @_ @(XParams width r) var varInputs emptyEnv
                       envMnist = extendEnv varGlyph (sconcrete glyph)
                                  $ extendEnv varLabel (sconcrete label) env
                   in interpretAst envMnist ast
                 chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdamDeep @(MnistDataBatchS batch_size r) @(XParams width r) f chunkS parameters stateAdam
                 smnistRFromS (glyphs, labels) =
                   ( Nested.stoRanked glyphs
                   , Nested.stoRanked labels )
                 chunkDataR = packBatchR $ map smnistRFromS chunk
                 !trainScore =
                   ftest (length chunk) chunkDataR parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (sNatValue width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> ( RepN (XParams width r)
                       , StateAdamDeep (XParams width r) )
                    -> IO (RepN (XParams width r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < 10) $
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

{-# SPECIALIZE mnistTestCaseRNNSI
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSI :: TestTree
tensorADValMnistTestsRNNSI = testGroup "RNNS Intermediate MNIST tests"
  [ mnistTestCaseRNNSI "RNNSI 1 epoch, 1 batch" 1 1 (SNat @32) (SNat @5) 2
                       (1 :: Double)
--  [ mnistTestCaseRNNSI "RNNSI 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 50
--                       (0.84 :: Double)
  , mnistTestCaseRNNSI "RNNSI artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSI "RNNSI artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNSI "RNNSI 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseRNNSO
  :: forall width batch_size r.
     ( Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSO prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize
                   expected =
    let valsInit :: ADRnnMnistParametersShaped
                      RepN SizeMnistHeight width r
        valsInit = fst $ randomVals 0.4 (mkStdGen 44)
        hVectorInit :: RepN (XParams width r)
        hVectorInit = toHVectorOf @RepN valsInit
        ftk = tftk @RepN (stensorKind @(XParams width r))
                         hVectorInit
        miniBatchSize = sNatValue batch_size
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show (sNatValue width), show miniBatchSize ]
--                          , show (V.length hVectorInit)
--                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r
              -> RepN (XParams width r)
              -> r
        ftest 0 _ _ = 0
        ftest miniBatchSize' (glyphs, labels) testParams =
          assert (miniBatchSize' == rlength @_ @(TKScalar r) (RepN glyphs)) $
          withSNat miniBatchSize' $ \bs@SNat ->
            let mnist = ( Nested.rcastToShaped glyphs knownShS
                        , Nested.rcastToShaped labels knownShS )
            in MnistRnnShaped2.rnnMnistTestS
                 width bs mnist
                 (parseHVector @RepN testParams)
    in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map shapeBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           dataInit = case chunksOf miniBatchSize trainData of
             d : _ -> let (dglyph, dlabel) = packBatch d
                      in ( RepN dglyph
                         , RepN dlabel )
             [] -> error "empty train data"
           f :: ( ADRnnMnistParametersShaped (AstTensor AstMethodLet FullSpan)
                    SizeMnistHeight width r
                , ( AstTensor AstMethodLet FullSpan
                      (TKS '[batch_size, SizeMnistHeight, SizeMnistWidth] r)
                  , AstTensor AstMethodLet FullSpan
                      (TKS '[batch_size, SizeMnistLabel] r) ) )
             -> AstTensor AstMethodLet FullSpan (TKS '[] r)
           f = \ (pars, (glyphS, labelS)) ->
             MnistRnnShaped2.rnnMnistLossFusedS
               width batch_size (sprimalPart glyphS, sprimalPart labelS) pars
           (artRaw, _) = revArtifactAdapt False f (valsInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchS batch_size r]
              -> ( RepN (XParams width r)
                 , StateAdamDeep (XParams width r) )
              -> ( RepN (XParams width r)
                 , StateAdamDeep (XParams width r) )
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = sconcrete glyph
                 labelD = sconcrete label
                 parametersAndInput = tpair parameters (tpair glyphD labelD)
                 gradient =
                   tproject1 $ fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdamDeep
                           @(XParams width r)
                           defaultArgsAdam stateAdam parameters gradient)
           runBatch :: ( RepN (XParams width r)
                       , StateAdamDeep (XParams width r) )
                    -> (Int, [MnistDataS r])
                    -> IO ( RepN (XParams width r)
                          , StateAdamDeep (XParams width r) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map packBatch
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = go chunkS (parameters, stateAdam)
                 smnistRFromS (glyphs, labels) =
                   ( Nested.stoRanked glyphs
                   , Nested.stoRanked labels )
                 chunkDataR = packBatchR $ map smnistRFromS chunk
                 !trainScore =
                   ftest (length chunk) chunkDataR parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (sNatValue width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> ( RepN (XParams width r)
                       , StateAdamDeep (XParams width r) )
                    -> IO (RepN (XParams width r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < 10) $
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

{-# SPECIALIZE mnistTestCaseRNNSO
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSO :: TestTree
tensorADValMnistTestsRNNSO = testGroup "RNNS Once MNIST tests"
  [ mnistTestCaseRNNSO "RNNSO 1 epoch, 1 batch" 1 1 (SNat @32) (SNat @5) 2
                       (1 :: Double)
  , mnistTestCaseRNNSO "RNNSO artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSO "RNNSO artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.9336734693877551 :: Double)
  , mnistTestCaseRNNSO "RNNSO 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]
