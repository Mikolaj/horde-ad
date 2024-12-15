{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | Tests of "MnistCnnRanked2" neural networks using a few different
-- optimization pipelines.
module TestMnistCNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import Data.IntMap.Strict qualified as IM
import Data.Vector.Generic qualified as V
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
import HordeAd.Core.OpsAst
import HordeAd.External.OptimizerTools

import EqEpsilon

import MnistCnnRanked2 qualified
import MnistData

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsCNNA
            , tensorADValMnistTestsCNNI
            , tensorADValMnistTestsCNNO
            , tensorMnistTestsPP
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseCNNA
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNA prefix epochs maxBatches kh kw c_out n_hidden
                  miniBatchSize totalBatchSize expected =
  let valsInit :: MnistCnnRanked2.ADCnnMnistParameters target r
      valsInit =
        case ( someNatVal $ toInteger kh
             , someNatVal $ toInteger kw
             , someNatVal $ toInteger c_out
             , someNatVal $ toInteger n_hidden ) of
          ( Just (SomeNat @kh _), Just (SomeNat @kw _)
           ,Just (SomeNat @c_out _), Just (SomeNat @n_hidden _) ) ->
            forgetShape $ fst
            $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                             RepN SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)
                0.4 (mkStdGen 44)
          _ -> error "impossible someNatVal error"
      hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show kh, show kw, show c_out, show n_hidden
                        , show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector RepN -> r
      ftest = MnistCnnRanked2.convMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = packBatchR testData
           runBatch :: (HVector RepN, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector RepN, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal RepN)
                   -> ADVal target (TKR 0 r)
                 f (glyphR, labelR) adinputs =
                   MnistCnnRanked2.convMnistLossFusedR
                     miniBatchSize (rconcrete glyphR, rconcrete labelR)
                     (unAsHVector $ parseHVector (AsHVector $ fromDValue valsInit) (dmkHVector adinputs))
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (n_hidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector RepN, StateAdam) -> IO (HVector RepN)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (n_hidden < 10) $
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

{-# SPECIALIZE mnistTestCaseCNNA
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsCNNA :: TestTree
tensorADValMnistTestsCNNA = testGroup "CNN ADVal MNIST tests"
  [ mnistTestCaseCNNA "CNNA 1 epoch, 1 batch" 1 1 2 2 4 4 1 1
                       (1 :: Double)
  , mnistTestCaseCNNA "CNNA artificial 1 2 3 4 5" 1 1 2 3 4 5 1 1
                       (1 :: Float)
  , mnistTestCaseCNNA "CNNA artificial 5 4 3 2 1" 1 4 3 2 1 1 1 1
                       (1 :: Double)
  , mnistTestCaseCNNA "CNNA 1 epoch, 0 batch" 1 0 4 4 64 16 5 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseCNNI
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNI prefix epochs maxBatches kh kw c_out n_hidden
                  miniBatchSize totalBatchSize expected =
  let valsInit :: MnistCnnRanked2.ADCnnMnistParameters target r
      valsInit =
        case ( someNatVal $ toInteger kh
             , someNatVal $ toInteger kw
             , someNatVal $ toInteger c_out
             , someNatVal $ toInteger n_hidden ) of
          ( Just (SomeNat @kh _), Just (SomeNat @kw _)
           ,Just (SomeNat @c_out _), Just (SomeNat @n_hidden _) ) ->
            forgetShape $ fst
            $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                             RepN SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)
                0.4 (mkStdGen 44)
          _ -> error "impossible someNatVal error"
      hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show kh, show kw, show c_out, show n_hidden
                        , show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector RepN -> r
      ftest = MnistCnnRanked2.convMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, _, var, hVector2)
         <- funToAstRevIO $ FTKUntyped $ voidFromHVector hVectorInit
       let testDataR = packBatchR testData
       (varGlyph, astGlyph) <-
         funToAstIO
           (FTKR (miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR) FTKScalar)
           id
       (varLabel, astLabel) <-
         funToAstIO (FTKR (miniBatchSize :$: sizeMnistLabelInt :$: ZSR) FTKScalar) id
       let ast :: AstTensor AstMethodLet FullSpan (TKR 0 r)
           ast = MnistCnnRanked2.convMnistLossFusedR
                   miniBatchSize (astGlyph, astLabel)
                   (unAsHVector
                    $ parseHVector (AsHVector $ fromDValue valsInit)
                                   hVector2)
           runBatch :: (HVector RepN, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector RepN, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal RepN)
                   -> ADVal target (TKR 0 r)
                 f (glyph, label) varInputs =
                   let env = extendEnv var (dmkHVector varInputs) emptyEnv
                       envMnist = extendEnv varGlyph (rconcrete glyph)
                                  $ extendEnv varLabel (rconcrete label) env
                   in interpretAst envMnist ast
                 chunkR = map packBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = sgdAdam f chunkR parameters stateAdam
                 !trainScore =
                   ftest (length chunk) (packBatchR chunk) parameters2
                 !testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 !lenChunk = length chunk
             unless (n_hidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector RepN, StateAdam) -> IO (HVector RepN)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (n_hidden < 10) $
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

{-# SPECIALIZE mnistTestCaseCNNI
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsCNNI :: TestTree
tensorADValMnistTestsCNNI = testGroup "CNN Intermediate MNIST tests"
  [ mnistTestCaseCNNI "CNNI 1 epoch, 1 batch" 1 1 2 2 4 4 1 1
                       (1 :: Double)
  , mnistTestCaseCNNI "CNNI artificial 1 2 3 4 5" 1 1 2 3 4 5 1 1
                       (1 :: Float)
  , mnistTestCaseCNNI "CNNI artificial 5 4 3 2 1" 1 4 3 2 1 1 1 1
                       (1 :: Double)
  , mnistTestCaseCNNI "CNNI 1 epoch, 0 batch" 1 0 4 4 64 16 5 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseCNNO
  :: forall target r.
     ( target ~ RepN, Differentiable r, GoodScalar r, Numeric r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNO prefix epochs maxBatches kh kw c_out n_hidden
                  miniBatchSize totalBatchSize expected =
 -- TODO: use withKnownNat when we no longer support GHC 9.4
 case ( someNatVal $ toInteger kh
      , someNatVal $ toInteger kw
      , someNatVal $ toInteger c_out
      , someNatVal $ toInteger n_hidden ) of
   ( Just (SomeNat @kh _), Just (SomeNat @kw _)
    ,Just (SomeNat @c_out _), Just (SomeNat @n_hidden _) ) ->
    let valsInitShaped
          :: MnistCnnRanked2.ADCnnMnistParametersShaped
               RepN SizeMnistHeight SizeMnistWidth
               kh kw c_out n_hidden r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        valsInit :: MnistCnnRanked2.ADCnnMnistParameters target r
        valsInit = forgetShape valsInitShaped
        hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show kh, show kw, show c_out, show n_hidden
                          , show miniBatchSize
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r -> HVector RepN -> r
        ftest = MnistCnnRanked2.convMnistTestR valsInit
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
           f :: (AsHVector
                  ( MnistCnnRanked2.ADCnnMnistParameters (AstTensor AstMethodLet FullSpan) r
                  , ( AstTensor AstMethodLet FullSpan
                        (TKR 3 r)
                    , AstTensor AstMethodLet FullSpan
                        (TKR 2 r) ) ))
             -> AstTensor AstMethodLet FullSpan (TKR 0 r)
           f = \ (AsHVector (pars, (glyphR, labelR))) ->
             MnistCnnRanked2.convMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           (artRaw, _) = revArtifactAdapt False f (AsHVector (valsInit, dataInit))
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchR r] -> (HVector RepN, StateAdam)
              -> (HVector RepN, StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconcrete glyph
                 labelD = DynamicRanked $ rconcrete label
                 parametersAndInput =
                   dmkHVector
                   $ V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   dunHVector
                   $ fst $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientHVector)
           runBatch :: (HVector RepN, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector RepN, StateAdam)
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
             unless (n_hidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector RepN, StateAdam) -> IO (HVector RepN)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (n_hidden < 10) $
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
   _ -> error "impossible someNatVal error"

{-# SPECIALIZE mnistTestCaseCNNO
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsCNNO :: TestTree
tensorADValMnistTestsCNNO = testGroup "CNN Once MNIST tests"
  [ mnistTestCaseCNNO "CNNO 1 epoch, 1 batch" 1 1 2 2 4 4 1 1
                       (1 :: Double)
  , mnistTestCaseCNNO "CNNO artificial 1 2 3 4 5" 1 1 2 3 4 5 1 1
                       (1 :: Float)
  , mnistTestCaseCNNO "CNNO artificial 5 4 3 2 1" 1 4 3 2 1 1 1 1
                       (1 :: Double)
  , mnistTestCaseCNNO "CNNO 1 epoch, 0 batch" 1 0 4 4 64 16 5 50
                       (1.0 :: Float)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for CNN MNIST tests"
  [ testCase "CNNOPP" testCNNOPP
  ]

testCNNOPP :: Assertion
testCNNOPP = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 1
      sizeMnistWidthI = 4  -- 4; to make weightsDense empty and so speedup
      sizeMnistHeightI = 4  -- 4; to make weightsDense empty and so speedup
      blackGlyph :: AstTensor AstMethodLet PrimalSpan (TKR 4 Double)
      blackGlyph = AstReplicate (SNat @1)
                   $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @4)
                   $ AstReplicate (SNat @4)
                       (AstConcrete (FTKR ZSR FTKScalar) (RepN $ Nested.rscalar 7) :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      valsInit :: MnistCnnRanked2.ADCnnMnistParameters RepN Double
      valsInit =
        forgetShape $ fst
        $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                         RepN 4 4  -- see sizeMnistWidthI, etc.
                         1 1 1 1 Double)
                     0.4 (mkStdGen 44)
      afcnn2T :: MnistCnnRanked2.ADCnnMnistParameters (AstTensor AstMethodLet FullSpan)
                                                      Double
              -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      afcnn2T = MnistCnnRanked2.convMnistTwoR sizeMnistHeightI sizeMnistWidthI
                                              batch_size blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInit
  printArtifactPretty renames artifactRev
    @?= "\\m362 x1 -> let w269 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i255, i256, i257, i258, i259, i260, i261] -> [ifF ((0 <=. i255 + i258 &&* 1 >. i255 + i258) &&* ((0 <=. i259 &&* 1 >. i259) &&* ((0 <=. i256 + i260 &&* 4 >. i256 + i260) &&* (0 <=. i257 + i261 &&* 4 >. i257 + i261)))) 0 1])))) ; w270 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i262, i263] -> [i262 + i263]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i264, i265, i266, i267, i268] -> [ifF ((0 <=. i264 + i265 &&* 1 >. i264 + i265) &&* ((0 <=. i266 &&* 1 >. i266) &&* ((0 <=. i267 &&* 2 >. i267) &&* (0 <=. i268 &&* 2 >. i268)))) 0 1, i264, i265, i266, i267, i268])))))) ; w271 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w269 * w270) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w288 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i272, i273, i274, i275, i276, i277, i278, i279] -> [ifF (w271 ! [i272, i273, i274, i275, i276, i277, i278, i279, i272, i273, 0, 0] <=. rscalar 0.0) 0 1]) ; w289 = rgather [1,1,2,2,1,1,2,2] w271 (\\[i280, i281, i282, i283, i284, i285, i286, i287] -> [i280, i281, i282, i283, i284, i285, i286, i287, i280, i281, 0, 0]) ; w298 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w288 * w289, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF ((0 <=. i290 + i294 &&* 1 >. i290 + i294) &&* ((0 <=. i291 + i295 &&* 1 >. i291 + i295) &&* ((0 <=. 2 * i292 + i296 &&* 4 >. 2 * i292 + i296) &&* (0 <=. 2 * i293 + i297 &&* 4 >. 2 * i293 + i297)))) 0 1, i290, i291, i292, i293, i294, i295, i296, i297])))))))) ; x306 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w321 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w298 (\\[i299, i300, i301, i302, i303, i304, i305] -> [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2) * i306)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i307, i308, i309, i310, i311, i312, i313] -> [ifF ((0 <=. i307 + i310 &&* 1 >. i307 + i310) &&* ((0 <=. i311 &&* 1 >. i311) &&* ((0 <=. i308 + i312 &&* 2 >. i308 + i312) &&* (0 <=. i309 + i313 &&* 2 >. i309 + i313)))) 0 1, i307, i308, i309, i310, i311, i312, i313])))) ; w322 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i314, i315] -> [i314 + i315]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i316, i317, i318, i319, i320] -> [ifF ((0 <=. i316 + i317 &&* 1 >. i316 + i317) &&* ((0 <=. i318 &&* 1 >. i318) &&* ((0 <=. i319 &&* 2 >. i319) &&* (0 <=. i320 &&* 2 >. i320)))) 0 1, i316, i317, i318, i319, i320])))))) ; w323 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w321 * w322) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w340 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i324, i325, i326, i327, i328, i329, i330, i331] -> [ifF (w323 ! [i324, i325, i326, i327, i328, i329, i330, i331, i324, i325, 0, 0] <=. rscalar 0.0) 0 1]) ; w341 = rgather [1,1,1,1,1,1,2,2] w323 (\\[i332, i333, i334, i335, i336, i337, i338, i339] -> [i332, i333, i334, i335, i336, i337, i338, i339, i332, i333, 0, 0]) ; w350 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w340 * w341, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i342, i343, i344, i345, i346, i347, i348, i349] -> [ifF ((0 <=. i342 + i346 &&* 1 >. i342 + i346) &&* ((0 <=. i343 + i347 &&* 1 >. i343 + i347) &&* ((0 <=. 2 * i344 + i348 &&* 2 >. 2 * i344 + i348) &&* (0 <=. 2 * i345 + i349 &&* 2 >. 2 * i345 + i349)))) 0 1, i342, i343, i344, i345, i346, i347, i348, i349]) ; x355 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; t356 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w350 (\\[i351, i352, i353, i354] -> [i351, i352, i353, i354, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2) * i355)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2))]))))) ; m357 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t356) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m360 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i358, i359] -> [ifF (m357 ! [i358, i359] <=. rscalar 0.0) 0 1]) ; t361 = rtranspose [1,0] (rreplicate 10 (m360 * m357)) ; m363 = m360 * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rreplicate 1 m362)) ; t364 = rreplicate 1 m363 ; x369 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w378 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rtranspose [1,0] (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t364))))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i365, i366, i367, i368]))))) (stoScalar (sscalar 2) * i369)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i365, i366, i367, i368]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i365, i366, i367, i368]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i365, i366, i367, i368]))))) (stoScalar (sscalar 2))])) (\\[i370, i371, i372, i373, i374, i375, i376, i377] -> [ifF ((0 <=. i370 + i374 &&* 1 >. i370 + i374) &&* ((0 <=. i371 + i375 &&* 1 >. i371 + i375) &&* ((0 <=. 2 * i372 + i376 &&* 2 >. 2 * i372 + i376) &&* (0 <=. 2 * i373 + i377 &&* 2 >. 2 * i373 + i377)))) 0 1, i370, i371, i372, i373, i374, i375, i376, i377]) ; u387 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w340 * w378 ! [0]) (\\[i379, i380, i381, i382, i383, i384, i385, i386] -> [i379, i380, i381, i382, i383, i384, i385, i386, i379, i380, 0, 0]))))))))) ; w388 = rreplicate 4 u387 ; w394 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w321 * w388)))))) (\\[i389, i390, i391, i392, i393] -> [ifF ((0 <=. i389 + i390 &&* 1 >. i389 + i390) &&* ((0 <=. i391 &&* 1 >. i391) &&* ((0 <=. i392 &&* 2 >. i392) &&* (0 <=. i393 &&* 2 >. i393)))) 0 1, i389, i390, i391, i392, i393]) ; w404 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] (w322 * w388)))) (\\[i397, i398, i399, i400, i401, i402, i403] -> [ifF ((0 <=. i397 + i400 &&* 1 >. i397 + i400) &&* ((0 <=. i401 &&* 1 >. i401) &&* ((0 <=. i398 + i402 &&* 2 >. i398 + i402) &&* (0 <=. i399 + i403 &&* 2 >. i399 + i403)))) 0 1, i397, i398, i399, i400, i401, i402, i403]) ; x412 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w421 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w404 ! [0]) (\\[i405, i406, i407, i408, i409, i410, i411] -> [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407]))))) (stoScalar (sscalar 2) * i412)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407]))))) (stoScalar (sscalar 2))]))))))))) (\\[i413, i414, i415, i416, i417, i418, i419, i420] -> [ifF ((0 <=. i413 + i417 &&* 1 >. i413 + i417) &&* ((0 <=. i414 + i418 &&* 1 >. i414 + i418) &&* ((0 <=. 2 * i415 + i419 &&* 4 >. 2 * i415 + i419) &&* (0 <=. 2 * i416 + i420 &&* 4 >. 2 * i416 + i420)))) 0 1, i413, i414, i415, i416, i417, i418, i419, i420]) ; u430 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w288 * w421 ! [0]) (\\[i422, i423, i424, i425, i426, i427, i428, i429] -> [i422, i423, i424, i425, i426, i427, i428, i429, i422, i423, 0, 0]))))))))) ; w436 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w269 * rreplicate 4 u430)))))) (\\[i431, i432, i433, i434, i435] -> [ifF ((0 <=. i431 + i432 &&* 1 >. i431 + i432) &&* ((0 <=. i433 &&* 1 >. i433) &&* ((0 <=. i434 &&* 2 >. i434) &&* (0 <=. i435 &&* 2 >. i435)))) 0 1, i431, i432, i433, i434, i435]) in tpair (tpair (tpair (rscatter [1,1,2,2] (w436 ! [0]) (\\[i437, i438] -> [i437 + i438]), rsum (rsum (rsum (rtranspose [0,2,3,1] u430)))), tpair (rscatter [1,1,2,2] (w394 ! [0]) (\\[i395, i396] -> [i395 + i396]), rsum (rsum (rsum (rtranspose [0,2,3,1] u387))))), tpair (tpair (rsum (rtranspose [2,1,0] (t356 * t364)), rsum (rtranspose [1,0] m363)), tpair (rsum (rtranspose [2,1,0] (t361 * rreplicate 1 m362)), rsum (rtranspose [1,0] m362))))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let w269 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i255, i256, i257, i258, i259, i260, i261] -> [ifF ((0 <=. i255 + i258 &&* 1 >. i255 + i258) &&* ((0 <=. i259 &&* 1 >. i259) &&* ((0 <=. i256 + i260 &&* 4 >. i256 + i260) &&* (0 <=. i257 + i261 &&* 4 >. i257 + i261)))) 0 1])))) ; w270 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i262, i263] -> [i262 + i263]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i264, i265, i266, i267, i268] -> [ifF ((0 <=. i264 + i265 &&* 1 >. i264 + i265) &&* ((0 <=. i266 &&* 1 >. i266) &&* ((0 <=. i267 &&* 2 >. i267) &&* (0 <=. i268 &&* 2 >. i268)))) 0 1, i264, i265, i266, i267, i268])))))) ; w271 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w269 * w270) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w288 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i272, i273, i274, i275, i276, i277, i278, i279] -> [ifF (w271 ! [i272, i273, i274, i275, i276, i277, i278, i279, i272, i273, 0, 0] <=. rscalar 0.0) 0 1]) ; w289 = rgather [1,1,2,2,1,1,2,2] w271 (\\[i280, i281, i282, i283, i284, i285, i286, i287] -> [i280, i281, i282, i283, i284, i285, i286, i287, i280, i281, 0, 0]) ; w298 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w288 * w289, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF ((0 <=. i290 + i294 &&* 1 >. i290 + i294) &&* ((0 <=. i291 + i295 &&* 1 >. i291 + i295) &&* ((0 <=. 2 * i292 + i296 &&* 4 >. 2 * i292 + i296) &&* (0 <=. 2 * i293 + i297 &&* 4 >. 2 * i293 + i297)))) 0 1, i290, i291, i292, i293, i294, i295, i296, i297])))))))) ; x306 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w321 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w298 (\\[i299, i300, i301, i302, i303, i304, i305] -> [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2) * i306)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i307, i308, i309, i310, i311, i312, i313] -> [ifF ((0 <=. i307 + i310 &&* 1 >. i307 + i310) &&* ((0 <=. i311 &&* 1 >. i311) &&* ((0 <=. i308 + i312 &&* 2 >. i308 + i312) &&* (0 <=. i309 + i313 &&* 2 >. i309 + i313)))) 0 1, i307, i308, i309, i310, i311, i312, i313])))) ; w322 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i314, i315] -> [i314 + i315]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i316, i317, i318, i319, i320] -> [ifF ((0 <=. i316 + i317 &&* 1 >. i316 + i317) &&* ((0 <=. i318 &&* 1 >. i318) &&* ((0 <=. i319 &&* 2 >. i319) &&* (0 <=. i320 &&* 2 >. i320)))) 0 1, i316, i317, i318, i319, i320])))))) ; w323 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w321 * w322) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w340 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i324, i325, i326, i327, i328, i329, i330, i331] -> [ifF (w323 ! [i324, i325, i326, i327, i328, i329, i330, i331, i324, i325, 0, 0] <=. rscalar 0.0) 0 1]) ; w341 = rgather [1,1,1,1,1,1,2,2] w323 (\\[i332, i333, i334, i335, i336, i337, i338, i339] -> [i332, i333, i334, i335, i336, i337, i338, i339, i332, i333, 0, 0]) ; w350 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w340 * w341, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i342, i343, i344, i345, i346, i347, i348, i349] -> [ifF ((0 <=. i342 + i346 &&* 1 >. i342 + i346) &&* ((0 <=. i343 + i347 &&* 1 >. i343 + i347) &&* ((0 <=. 2 * i344 + i348 &&* 2 >. 2 * i344 + i348) &&* (0 <=. 2 * i345 + i349 &&* 2 >. 2 * i345 + i349)))) 0 1, i342, i343, i344, i345, i346, i347, i348, i349]) ; x355 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; t356 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w350 (\\[i351, i352, i353, i354] -> [i351, i352, i353, i354, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2) * i355)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2))]))))) ; m357 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t356) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m360 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i358, i359] -> [ifF (m357 ! [i358, i359] <=. rscalar 0.0) 0 1]) ; t361 = rtranspose [1,0] (rreplicate 10 (m360 * m357)) in rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * t361) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m362 x1 -> let w269 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i255, i256, i257, i258, i259, i260, i261] -> [ifF ((0 <=. i255 + i258 &&* 1 >. i255 + i258) &&* ((0 <=. i259 &&* 1 >. i259) &&* ((0 <=. i256 + i260 &&* 4 >. i256 + i260) &&* (0 <=. i257 + i261 &&* 4 >. i257 + i261)))) 0 1])))) ; w271 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w269 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i262, i263] -> [i262 + i263]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i264, i265, i266, i267, i268] -> [ifF ((0 <=. i264 + i265 &&* 1 >. i264 + i265) &&* ((0 <=. i266 &&* 1 >. i266) &&* ((0 <=. i267 &&* 2 >. i267) &&* (0 <=. i268 &&* 2 >. i268)))) 0 1, i264, i265, i266, i267, i268]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w288 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i272, i273, i274, i275, i276, i277, i278, i279] -> [ifF (w271 ! [i272, i273, i274, i275, i276, i277, i278, i279, i272, i273, 0, 0] <=. rscalar 0.0) 0 1]) ; w298 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w288 * rgather [1,1,2,2,1,1,2,2] w271 (\\[i280, i281, i282, i283, i284, i285, i286, i287] -> [i280, i281, i282, i283, i284, i285, i286, i287, i280, i281, 0, 0]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF ((0 <=. i290 + i294 &&* 1 >. i290 + i294) &&* ((0 <=. i291 + i295 &&* 1 >. i291 + i295) &&* ((0 <=. 2 * i292 + i296 &&* 4 >. 2 * i292 + i296) &&* (0 <=. 2 * i293 + i297 &&* 4 >. 2 * i293 + i297)))) 0 1, i290, i291, i292, i293, i294, i295, i296, i297])))))))) ; w321 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w298 (\\[i299, i300, i301, i302, i303, i304, i305] -> [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i307, i308, i309, i310, i311, i312, i313] -> [ifF ((0 <=. i307 + i310 &&* 1 >. i307 + i310) &&* ((0 <=. i311 &&* 1 >. i311) &&* ((0 <=. i308 + i312 &&* 2 >. i308 + i312) &&* (0 <=. i309 + i313 &&* 2 >. i309 + i313)))) 0 1, i307, i308, i309, i310, i311, i312, i313])))) ; w322 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i314, i315] -> [i314 + i315]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i316, i317, i318, i319, i320] -> [ifF ((0 <=. i316 + i317 &&* 1 >. i316 + i317) &&* ((0 <=. i318 &&* 1 >. i318) &&* ((0 <=. i319 &&* 2 >. i319) &&* (0 <=. i320 &&* 2 >. i320)))) 0 1, i316, i317, i318, i319, i320])))))) ; w323 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w321 * w322) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w340 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i324, i325, i326, i327, i328, i329, i330, i331] -> [ifF (w323 ! [i324, i325, i326, i327, i328, i329, i330, i331, i324, i325, 0, 0] <=. rscalar 0.0) 0 1]) ; w350 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w340 * rgather [1,1,1,1,1,1,2,2] w323 (\\[i332, i333, i334, i335, i336, i337, i338, i339] -> [i332, i333, i334, i335, i336, i337, i338, i339, i332, i333, 0, 0]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i342, i343, i344, i345, i346, i347, i348, i349] -> [ifF ((0 <=. i342 + i346 &&* 1 >. i342 + i346) &&* ((0 <=. i343 + i347 &&* 1 >. i343 + i347) &&* ((0 <=. 2 * i344 + i348 &&* 2 >. 2 * i344 + i348) &&* (0 <=. 2 * i345 + i349 &&* 2 >. 2 * i345 + i349)))) 0 1, i342, i343, i344, i345, i346, i347, i348, i349]) ; t356 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w350 (\\[i351, i352, i353, i354] -> [i351, i352, i353, i354, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2))])))) ; m357 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t356) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m360 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i358, i359] -> [ifF (m357 ! [i358, i359] <=. rscalar 0.0) 0 1]) ; m363 = m360 * rsum (rtranspose [1,2,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rtranspose [1,0] (rreplicate 1 m362)) ; u387 = rscatter [1,1,2,2] (w340 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] (tproject1 (tproject1 (tproject2 u1))) (\\[i634] -> [i634, 0]) * rgather [1] m363 (\\[i631] -> [i631, 0]))))))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w350 ! [i365, i366, i367, i368, 0, 0]) (\\[i622] -> [remF (quotF i622 2) 2, remF i622 2]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w350 ! [i365, i366, i367, i368, 0, 0]) (\\[i623] -> [remF (quotF i623 2) 2, remF i623 2]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w350 ! [i365, i366, i367, i368, 0, 0]) (\\[i624] -> [remF (quotF i624 2) 2, remF i624 2]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rgather [4] (w350 ! [i365, i366, i367, i368, 0, 0]) (\\[i625] -> [remF (quotF i625 2) 2, remF i625 2]))))) (stoScalar (sscalar 2))])) (\\[i370, i371, i372, i373, i374, i375, i376, i377] -> [ifF ((0 <=. i370 + i374 &&* 1 >. i370 + i374) &&* ((0 <=. i371 + i375 &&* 1 >. i371 + i375) &&* ((0 <=. 2 * i372 + i376 &&* 2 >. 2 * i372 + i376) &&* (0 <=. 2 * i373 + i377 &&* 2 >. 2 * i373 + i377)))) 0 1, i370, i371, i372, i373, i374, i375, i376, i377]) ! [0]) (\\[i379, i380, i381, i382, i383, i384, i385, i386] -> [i379, i380, 0, 0]) ; u430 = rscatter [1,1,4,4] (w288 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w322 (\\[i606, i607, i608, i605] -> [i608, 0, i605, i606, i607]) * rgather [2,2,4,1] (u387 ! [0]) (\\[i611, i612, i613, i610] -> [i610, i611, i612])) (\\[i614, i615, i616, i617, i618, i619, i620, i621] -> [remF (quotF (i621 + 2 * i620 + 4 * i619 + 4 * i618 + 4 * i617 + 16 * i615 + 8 * i616) 8) 2, remF (quotF (i621 + 2 * i620 + 4 * i619 + 4 * i618 + 4 * i617 + 16 * i615 + 8 * i616) 4) 2, remF (i621 + 2 * i620 + 4 * i619 + 4 * i618 + 4 * i617 + 16 * i615 + 8 * i616) 4, i614]))) (\\[i397, i398, i399, i400, i401, i402, i403] -> [ifF ((0 <=. i397 + i400 &&* 1 >. i397 + i400) &&* ((0 <=. i401 &&* 1 >. i401) &&* ((0 <=. i398 + i402 &&* 2 >. i398 + i402) &&* (0 <=. i399 + i403 &&* 2 >. i399 + i403)))) 0 1, i397, i398, i399, i400, i401, i402, i403]) ! [0]) (\\[i405, i406, i407, i408, i409, i410, i411] -> [i405, i409, i406, i407, remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w298 ! [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407, 0, 0]) (\\[i593] -> [remF (quotF i593 2) 2, remF i593 2]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w298 ! [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407, 0, 0]) (\\[i594] -> [remF (quotF i594 2) 2, remF i594 2]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w298 ! [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407, 0, 0]) (\\[i595] -> [remF (quotF i595 2) 2, remF i595 2]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rgather [4] (w298 ! [i405, i406, i407, i408, i409, i410, i411, i405, i409, i406, i407, 0, 0]) (\\[i596] -> [remF (quotF i596 2) 2, remF i596 2]))))) (stoScalar (sscalar 2))])) (\\[i413, i414, i415, i416, i417, i418, i419, i420] -> [ifF ((0 <=. i413 + i417 &&* 1 >. i413 + i417) &&* ((0 <=. i414 + i418 &&* 1 >. i414 + i418) &&* ((0 <=. 2 * i415 + i419 &&* 4 >. 2 * i415 + i419) &&* (0 <=. 2 * i416 + i420 &&* 4 >. 2 * i416 + i420)))) 0 1, i413, i414, i415, i416, i417, i418, i419, i420]) ! [0]) (\\[i422, i423, i424, i425, i426, i427, i428, i429] -> [i422, i423, 0, 0]) in tpair (tpair (tpair (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w269 (\\[i525, i522] -> [i525, i522, 0]) * rreplicate 4 (rgather [1,4,4] u430 (\\[i527] -> [i527, 0]))) (\\[i585, i586, i587, i588, i589, i590, i591, i592] -> [remF (i592 + 2 * i591 + 4 * i590 + 4 * i588 + 4 * i589) 4, i585, i586, i587]))))) (\\[i431, i432, i433, i434, i435] -> [ifF ((0 <=. i431 + i432 &&* 1 >. i431 + i432) &&* ((0 <=. i433 &&* 1 >. i433) &&* ((0 <=. i434 &&* 2 >. i434) &&* (0 <=. i435 &&* 2 >. i435)))) 0 1, i431, i432, i433, i434, i435]) ! [0]) (\\[i437, i438] -> [i437 + i438]), rsum (rsum (rsum (rtranspose [0,2,3,1] u430)))), tpair (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w321 (\\[i448, i445] -> [i448, i445, 0]) * rreplicate 4 (rgather [1,2,2] u387 (\\[i450] -> [i450, 0]))) (\\[i508, i509, i510, i511, i512, i513, i514, i515] -> [remF (i515 + 2 * i514 + 4 * i513 + 4 * i511 + 4 * i512) 4, i508, i509, i510]))))) (\\[i389, i390, i391, i392, i393] -> [ifF ((0 <=. i389 + i390 &&* 1 >. i389 + i390) &&* ((0 <=. i391 &&* 1 >. i391) &&* ((0 <=. i392 &&* 2 >. i392) &&* (0 <=. i393 &&* 2 >. i393)))) 0 1, i389, i390, i391, i392, i393]) ! [0]) (\\[i395, i396] -> [i395 + i396]), rsum (rsum (rsum (rtranspose [0,2,3,1] u387))))), tpair (tpair (rsum (rtranspose [2,1,0] t356 * rtranspose [2,1,0] (rreplicate 1 m363)), rsum (rtranspose [1,0] m363)), tpair (rsum (rtranspose [2,0,1] (rreplicate 10 (m360 * m357)) * rtranspose [2,1,0] (rreplicate 1 m362)), rsum (rtranspose [1,0] m362))))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let w271 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i255, i256, i257, i258, i259, i260, i261] -> [ifF ((0 <=. i255 + i258 &&* 1 >. i255 + i258) &&* ((0 <=. i259 &&* 1 >. i259) &&* ((0 <=. i256 + i260 &&* 4 >. i256 + i260) &&* (0 <=. i257 + i261 &&* 4 >. i257 + i261)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i262, i263] -> [i262 + i263]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i264, i265, i266, i267, i268] -> [ifF ((0 <=. i264 + i265 &&* 1 >. i264 + i265) &&* ((0 <=. i266 &&* 1 >. i266) &&* ((0 <=. i267 &&* 2 >. i267) &&* (0 <=. i268 &&* 2 >. i268)))) 0 1, i264, i265, i266, i267, i268]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w298 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i272, i273, i274, i275, i276, i277, i278, i279] -> [ifF (w271 ! [i272, i273, i274, i275, i276, i277, i278, i279, i272, i273, 0, 0] <=. rscalar 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w271 (\\[i280, i281, i282, i283, i284, i285, i286, i287] -> [i280, i281, i282, i283, i284, i285, i286, i287, i280, i281, 0, 0]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF ((0 <=. i290 + i294 &&* 1 >. i290 + i294) &&* ((0 <=. i291 + i295 &&* 1 >. i291 + i295) &&* ((0 <=. 2 * i292 + i296 &&* 4 >. 2 * i292 + i296) &&* (0 <=. 2 * i293 + i297 &&* 4 >. 2 * i293 + i297)))) 0 1, i290, i291, i292, i293, i294, i295, i296, i297])))))))) ; w323 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w298 (\\[i299, i300, i301, i302, i303, i304, i305] -> [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w298 ! [i299, i300, i301, i302, i303, i304, i305, i299, i303, i300, i301]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i307, i308, i309, i310, i311, i312, i313] -> [ifF ((0 <=. i307 + i310 &&* 1 >. i307 + i310) &&* ((0 <=. i311 &&* 1 >. i311) &&* ((0 <=. i308 + i312 &&* 2 >. i308 + i312) &&* (0 <=. i309 + i313 &&* 2 >. i309 + i313)))) 0 1, i307, i308, i309, i310, i311, i312, i313])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i314, i315] -> [i314 + i315]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i316, i317, i318, i319, i320] -> [ifF ((0 <=. i316 + i317 &&* 1 >. i316 + i317) &&* ((0 <=. i318 &&* 1 >. i318) &&* ((0 <=. i319 &&* 2 >. i319) &&* (0 <=. i320 &&* 2 >. i320)))) 0 1, i316, i317, i318, i319, i320]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w350 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i324, i325, i326, i327, i328, i329, i330, i331] -> [ifF (w323 ! [i324, i325, i326, i327, i328, i329, i330, i331, i324, i325, 0, 0] <=. rscalar 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w323 (\\[i332, i333, i334, i335, i336, i337, i338, i339] -> [i332, i333, i334, i335, i336, i337, i338, i339, i332, i333, 0, 0]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i342, i343, i344, i345, i346, i347, i348, i349] -> [ifF ((0 <=. i342 + i346 &&* 1 >. i342 + i346) &&* ((0 <=. i343 + i347 &&* 1 >. i343 + i347) &&* ((0 <=. 2 * i344 + i348 &&* 2 >. 2 * i344 + i348) &&* (0 <=. 2 * i345 + i349 &&* 2 >. 2 * i345 + i349)))) 0 1, i342, i343, i344, i345, i346, i347, i348, i349]) ; m357 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w350 (\\[i351, i352, i353, i354] -> [i351, i352, i353, i354, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w350 ! [i351, i352, i353, i354]))))) (stoScalar (sscalar 2))]))))) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) in rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i358, i359] -> [ifF (m357 ! [i358, i359] <=. rscalar 0.0) 0 1]) * m357))) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject2 u1))))"
