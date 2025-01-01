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
      blackGlyph = AstReplicate (SNat @1) stensorKind
                   $ AstReplicate (SNat @1) stensorKind
                   $ AstReplicate (SNat @4) stensorKind
                   $ AstReplicate (SNat @4) stensorKind
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
    @?= "\\m387 x1 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. i269 + i272 &&* 1 >. i269 + i272) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. i270 + i274 &&* 4 >. i270 + i274) &&* (0 <=. i271 + i275 &&* 4 >. i271 + i275)))) 0 1])))) ; w284 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i276, i277] -> [i276 + i277]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. i278 + i279 &&* 1 >. i278 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282])))))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * w284) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; x286 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x287 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x288 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x289 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w306 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF (w285 ! [i290, i291, i292, i293, i294, i295, i296, i297, i286, i287, i288, i289] <=. rscalar 0.0) 0 1]) ; w307 = rgather [1,1,2,2,1,1,2,2] w285 (\\[i298, i299, i300, i301, i302, i303, i304, i305] -> [i298, i299, i300, i301, i302, i303, i304, i305, i286, i287, i288, i289]) ; w316 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w306 * w307, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [ifF ((0 <=. i308 + i312 &&* 1 >. i308 + i312) &&* ((0 <=. i309 + i313 &&* 1 >. i309 + i313) &&* ((0 <=. 2 * i310 + i314 &&* 4 >. 2 * i310 + i314) &&* (0 <=. 2 * i311 + i315 &&* 4 >. 2 * i311 + i315)))) 0 1, i308, i309, i310, i311, i312, i313, i314, i315])))))))) ; x317 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x318 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x319 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x327 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w342 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w316 (\\[i320, i321, i322, i323, i324, i325, i326] -> [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2) * i327)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i328, i329, i330, i331, i332, i333, i334] -> [ifF ((0 <=. i328 + i331 &&* 1 >. i328 + i331) &&* ((0 <=. i332 &&* 1 >. i332) &&* ((0 <=. i329 + i333 &&* 2 >. i329 + i333) &&* (0 <=. i330 + i334 &&* 2 >. i330 + i334)))) 0 1, i328, i329, i330, i331, i332, i333, i334])))) ; w343 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i335, i336] -> [i335 + i336]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i337, i338, i339, i340, i341] -> [ifF ((0 <=. i337 + i338 &&* 1 >. i337 + i338) &&* ((0 <=. i339 &&* 1 >. i339) &&* ((0 <=. i340 &&* 2 >. i340) &&* (0 <=. i341 &&* 2 >. i341)))) 0 1, i337, i338, i339, i340, i341])))))) ; w344 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w342 * w343) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; x345 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x346 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x347 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x348 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w365 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354, i355, i356] -> [ifF (w344 ! [i349, i350, i351, i352, i353, i354, i355, i356, i345, i346, i347, i348] <=. rscalar 0.0) 0 1]) ; w366 = rgather [1,1,1,1,1,1,2,2] w344 (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [i357, i358, i359, i360, i361, i362, i363, i364, i345, i346, i347, i348]) ; w375 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w365 * w366, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i367, i368, i369, i370, i371, i372, i373, i374] -> [ifF ((0 <=. i367 + i371 &&* 1 >. i367 + i371) &&* ((0 <=. i368 + i372 &&* 1 >. i368 + i372) &&* ((0 <=. 2 * i369 + i373 &&* 2 >. 2 * i369 + i373) &&* (0 <=. 2 * i370 + i374 &&* 2 >. 2 * i370 + i374)))) 0 1, i367, i368, i369, i370, i371, i372, i373, i374]) ; x380 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; t381 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w375 (\\[i376, i377, i378, i379] -> [i376, i377, i378, i379, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2) * i380)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2))]))))) ; m382 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t381) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m385 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i383, i384] -> [ifF (m382 ! [i383, i384] <=. rscalar 0.0) 0 1]) ; t386 = rtranspose [1,0] (rreplicate 10 (m385 * m382)) ; m388 = m385 * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rreplicate 1 m387)) ; t389 = rreplicate 1 m388 ; x394 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w403 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rtranspose [1,0] (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t389))))) (\\[i390, i391, i392, i393] -> [i390, i391, i392, i393, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i390, i391, i392, i393]))))) (stoScalar (sscalar 2) * i394)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i390, i391, i392, i393]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i390, i391, i392, i393]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i390, i391, i392, i393]))))) (stoScalar (sscalar 2))])) (\\[i395, i396, i397, i398, i399, i400, i401, i402] -> [ifF ((0 <=. i395 + i399 &&* 1 >. i395 + i399) &&* ((0 <=. i396 + i400 &&* 1 >. i396 + i400) &&* ((0 <=. 2 * i397 + i401 &&* 2 >. 2 * i397 + i401) &&* (0 <=. 2 * i398 + i402 &&* 2 >. 2 * i398 + i402)))) 0 1, i395, i396, i397, i398, i399, i400, i401, i402]) ; u412 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w365 * w403 ! [0]) (\\[i404, i405, i406, i407, i408, i409, i410, i411] -> [i404, i405, i406, i407, i408, i409, i410, i411, i345, i346, i347, i348]))))))))) ; w413 = rreplicate 4 u412 ; w419 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w342 * w413)))))) (\\[i414, i415, i416, i417, i418] -> [ifF ((0 <=. i414 + i415 &&* 1 >. i414 + i415) &&* ((0 <=. i416 &&* 1 >. i416) &&* ((0 <=. i417 &&* 2 >. i417) &&* (0 <=. i418 &&* 2 >. i418)))) 0 1, i414, i415, i416, i417, i418]) ; w429 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] (w343 * w413)))) (\\[i422, i423, i424, i425, i426, i427, i428] -> [ifF ((0 <=. i422 + i425 &&* 1 >. i422 + i425) &&* ((0 <=. i426 &&* 1 >. i426) &&* ((0 <=. i423 + i427 &&* 2 >. i423 + i427) &&* (0 <=. i424 + i428 &&* 2 >. i424 + i428)))) 0 1, i422, i423, i424, i425, i426, i427, i428]) ; x437 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w446 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w429 ! [0]) (\\[i430, i431, i432, i433, i434, i435, i436] -> [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319]))))) (stoScalar (sscalar 2) * i437)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319]))))) (stoScalar (sscalar 2))]))))))))) (\\[i438, i439, i440, i441, i442, i443, i444, i445] -> [ifF ((0 <=. i438 + i442 &&* 1 >. i438 + i442) &&* ((0 <=. i439 + i443 &&* 1 >. i439 + i443) &&* ((0 <=. 2 * i440 + i444 &&* 4 >. 2 * i440 + i444) &&* (0 <=. 2 * i441 + i445 &&* 4 >. 2 * i441 + i445)))) 0 1, i438, i439, i440, i441, i442, i443, i444, i445]) ; u455 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w306 * w446 ! [0]) (\\[i447, i448, i449, i450, i451, i452, i453, i454] -> [i447, i448, i449, i450, i451, i452, i453, i454, i286, i287, i288, i289]))))))))) ; w461 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w283 * rreplicate 4 u455)))))) (\\[i456, i457, i458, i459, i460] -> [ifF ((0 <=. i456 + i457 &&* 1 >. i456 + i457) &&* ((0 <=. i458 &&* 1 >. i458) &&* ((0 <=. i459 &&* 2 >. i459) &&* (0 <=. i460 &&* 2 >. i460)))) 0 1, i456, i457, i458, i459, i460]) in tpair (tpair (tpair (rscatter [1,1,2,2] (w461 ! [0]) (\\[i462, i463] -> [i462 + i463]), rsum (rsum (rsum (rtranspose [0,2,3,1] u455)))), tpair (rscatter [1,1,2,2] (w419 ! [0]) (\\[i420, i421] -> [i420 + i421]), rsum (rsum (rsum (rtranspose [0,2,3,1] u412))))), tpair (tpair (rsum (rtranspose [2,1,0] (t381 * t389)), rsum (rtranspose [1,0] m388)), tpair (rsum (rtranspose [2,1,0] (t386 * rreplicate 1 m387)), rsum (rtranspose [1,0] m387))))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. i269 + i272 &&* 1 >. i269 + i272) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. i270 + i274 &&* 4 >. i270 + i274) &&* (0 <=. i271 + i275 &&* 4 >. i271 + i275)))) 0 1])))) ; w284 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i276, i277] -> [i276 + i277]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. i278 + i279 &&* 1 >. i278 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282])))))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * w284) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; x286 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x287 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x288 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x289 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w306 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF (w285 ! [i290, i291, i292, i293, i294, i295, i296, i297, i286, i287, i288, i289] <=. rscalar 0.0) 0 1]) ; w307 = rgather [1,1,2,2,1,1,2,2] w285 (\\[i298, i299, i300, i301, i302, i303, i304, i305] -> [i298, i299, i300, i301, i302, i303, i304, i305, i286, i287, i288, i289]) ; w316 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w306 * w307, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [ifF ((0 <=. i308 + i312 &&* 1 >. i308 + i312) &&* ((0 <=. i309 + i313 &&* 1 >. i309 + i313) &&* ((0 <=. 2 * i310 + i314 &&* 4 >. 2 * i310 + i314) &&* (0 <=. 2 * i311 + i315 &&* 4 >. 2 * i311 + i315)))) 0 1, i308, i309, i310, i311, i312, i313, i314, i315])))))))) ; x317 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x318 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x319 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x327 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w342 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w316 (\\[i320, i321, i322, i323, i324, i325, i326] -> [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2) * i327)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i328, i329, i330, i331, i332, i333, i334] -> [ifF ((0 <=. i328 + i331 &&* 1 >. i328 + i331) &&* ((0 <=. i332 &&* 1 >. i332) &&* ((0 <=. i329 + i333 &&* 2 >. i329 + i333) &&* (0 <=. i330 + i334 &&* 2 >. i330 + i334)))) 0 1, i328, i329, i330, i331, i332, i333, i334])))) ; w343 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i335, i336] -> [i335 + i336]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i337, i338, i339, i340, i341] -> [ifF ((0 <=. i337 + i338 &&* 1 >. i337 + i338) &&* ((0 <=. i339 &&* 1 >. i339) &&* ((0 <=. i340 &&* 2 >. i340) &&* (0 <=. i341 &&* 2 >. i341)))) 0 1, i337, i338, i339, i340, i341])))))) ; w344 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w342 * w343) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; x345 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x346 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x347 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x348 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w365 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354, i355, i356] -> [ifF (w344 ! [i349, i350, i351, i352, i353, i354, i355, i356, i345, i346, i347, i348] <=. rscalar 0.0) 0 1]) ; w366 = rgather [1,1,1,1,1,1,2,2] w344 (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [i357, i358, i359, i360, i361, i362, i363, i364, i345, i346, i347, i348]) ; w375 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w365 * w366, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i367, i368, i369, i370, i371, i372, i373, i374] -> [ifF ((0 <=. i367 + i371 &&* 1 >. i367 + i371) &&* ((0 <=. i368 + i372 &&* 1 >. i368 + i372) &&* ((0 <=. 2 * i369 + i373 &&* 2 >. 2 * i369 + i373) &&* (0 <=. 2 * i370 + i374 &&* 2 >. 2 * i370 + i374)))) 0 1, i367, i368, i369, i370, i371, i372, i373, i374]) ; x380 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; t381 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w375 (\\[i376, i377, i378, i379] -> [i376, i377, i378, i379, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2) * i380)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2))]))))) ; m382 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t381) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m385 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i383, i384] -> [ifF (m382 ! [i383, i384] <=. rscalar 0.0) 0 1]) ; t386 = rtranspose [1,0] (rreplicate 10 (m385 * m382)) in rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * t386) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m387 x1 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. i269 + i272 &&* 1 >. i269 + i272) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. i270 + i274 &&* 4 >. i270 + i274) &&* (0 <=. i271 + i275 &&* 4 >. i271 + i275)))) 0 1])))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i276, i277] -> [i276 + i277]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. i278 + i279 &&* 1 >. i278 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; x286 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x287 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x288 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x289 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w306 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF (w285 ! [i290, i291, i292, i293, i294, i295, i296, i297, i286, i287, i288, i289] <=. rscalar 0.0) 0 1]) ; w316 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w306 * rgather [1,1,2,2,1,1,2,2] w285 (\\[i298, i299, i300, i301, i302, i303, i304, i305] -> [i298, i299, i300, i301, i302, i303, i304, i305, i286, i287, i288, i289]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [ifF ((0 <=. i308 + i312 &&* 1 >. i308 + i312) &&* ((0 <=. i309 + i313 &&* 1 >. i309 + i313) &&* ((0 <=. 2 * i310 + i314 &&* 4 >. 2 * i310 + i314) &&* (0 <=. 2 * i311 + i315 &&* 4 >. 2 * i311 + i315)))) 0 1, i308, i309, i310, i311, i312, i313, i314, i315])))))))) ; x317 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x318 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x319 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w342 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w316 (\\[i320, i321, i322, i323, i324, i325, i326] -> [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i328, i329, i330, i331, i332, i333, i334] -> [ifF ((0 <=. i328 + i331 &&* 1 >. i328 + i331) &&* ((0 <=. i332 &&* 1 >. i332) &&* ((0 <=. i329 + i333 &&* 2 >. i329 + i333) &&* (0 <=. i330 + i334 &&* 2 >. i330 + i334)))) 0 1, i328, i329, i330, i331, i332, i333, i334])))) ; w343 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i335, i336] -> [i335 + i336]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i337, i338, i339, i340, i341] -> [ifF ((0 <=. i337 + i338 &&* 1 >. i337 + i338) &&* ((0 <=. i339 &&* 1 >. i339) &&* ((0 <=. i340 &&* 2 >. i340) &&* (0 <=. i341 &&* 2 >. i341)))) 0 1, i337, i338, i339, i340, i341])))))) ; w344 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w342 * w343) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; x345 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x346 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x347 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x348 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w365 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354, i355, i356] -> [ifF (w344 ! [i349, i350, i351, i352, i353, i354, i355, i356, i345, i346, i347, i348] <=. rscalar 0.0) 0 1]) ; w375 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w365 * rgather [1,1,1,1,1,1,2,2] w344 (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [i357, i358, i359, i360, i361, i362, i363, i364, i345, i346, i347, i348]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i367, i368, i369, i370, i371, i372, i373, i374] -> [ifF ((0 <=. i367 + i371 &&* 1 >. i367 + i371) &&* ((0 <=. i368 + i372 &&* 1 >. i368 + i372) &&* ((0 <=. 2 * i369 + i373 &&* 2 >. 2 * i369 + i373) &&* (0 <=. 2 * i370 + i374 &&* 2 >. 2 * i370 + i374)))) 0 1, i367, i368, i369, i370, i371, i372, i373, i374]) ; t381 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w375 (\\[i376, i377, i378, i379] -> [i376, i377, i378, i379, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2))])))) ; m382 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t381) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m385 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i383, i384] -> [ifF (m382 ! [i383, i384] <=. rscalar 0.0) 0 1]) ; m388 = m385 * rmatmul2 (rtranspose [1,0] (tproject1 (tproject2 (tproject2 u1)))) m387 ; u412 = roneHot [] (rsum0 (rsum (rsum (rsum (rsum (rsum (rsum (w365 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rdot0 (rgather [1] (tproject1 (tproject1 (tproject2 u1))) (\\[i659] -> [i659, 0])) (rgather [1] m388 (\\[i656] -> [i656, 0]))))))) (\\[i390, i391, i392, i393] -> [i390, i391, i392, i393, remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w375 ! [i390, i391, i392, i393, 0, 0]) (\\[i647] -> [remF (quotF i647 2) 2, remF i647 2]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w375 ! [i390, i391, i392, i393, 0, 0]) (\\[i648] -> [remF (quotF i648 2) 2, remF i648 2]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w375 ! [i390, i391, i392, i393, 0, 0]) (\\[i649] -> [remF (quotF i649 2) 2, remF i649 2]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rgather [4] (w375 ! [i390, i391, i392, i393, 0, 0]) (\\[i650] -> [remF (quotF i650 2) 2, remF i650 2]))))) (stoScalar (sscalar 2))])) (\\[i395, i396, i397, i398, i399, i400, i401, i402] -> [ifF ((0 <=. i395 + i399 &&* 1 >. i395 + i399) &&* ((0 <=. i396 + i400 &&* 1 >. i396 + i400) &&* ((0 <=. 2 * i397 + i401 &&* 2 >. 2 * i397 + i401) &&* (0 <=. 2 * i398 + i402 &&* 2 >. 2 * i398 + i402)))) 0 1, i395, i396, i397, i398, i399, i400, i401, i402]) ! [0])))))))) [i345, i346, i347, i348] ; u455 = roneHot [] (rsum0 (rsum (rsum (rsum (rsum (rsum (rsum (w306 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w343 (\\[i631, i632, i633, i630] -> [i633, 0, i630, i631, i632]) * rgather [2,2,4,1] (u412 ! [0]) (\\[i636, i637, i638, i635] -> [i635, i636, i637])) (\\[i639, i640, i641, i642, i643, i644, i645, i646] -> [remF (quotF (i646 + 2 * i645 + 4 * i644 + 4 * i643 + 4 * i642 + 16 * i640 + 8 * i641) 8) 2, remF (quotF (i646 + 2 * i645 + 4 * i644 + 4 * i643 + 4 * i642 + 16 * i640 + 8 * i641) 4) 2, remF (i646 + 2 * i645 + 4 * i644 + 4 * i643 + 4 * i642 + 16 * i640 + 8 * i641) 4, i639]))) (\\[i422, i423, i424, i425, i426, i427, i428] -> [ifF ((0 <=. i422 + i425 &&* 1 >. i422 + i425) &&* ((0 <=. i426 &&* 1 >. i426) &&* ((0 <=. i423 + i427 &&* 2 >. i423 + i427) &&* (0 <=. i424 + i428 &&* 2 >. i424 + i428)))) 0 1, i422, i423, i424, i425, i426, i427, i428]) ! [0]) (\\[i430, i431, i432, i433, i434, i435, i436] -> [i317, i434, i318, i319, remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w316 ! [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319, 0, 0]) (\\[i618] -> [remF (quotF i618 2) 2, remF i618 2]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w316 ! [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319, 0, 0]) (\\[i619] -> [remF (quotF i619 2) 2, remF i619 2]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w316 ! [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319, 0, 0]) (\\[i620] -> [remF (quotF i620 2) 2, remF i620 2]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rgather [4] (w316 ! [i430, i431, i432, i433, i434, i435, i436, i317, i434, i318, i319, 0, 0]) (\\[i621] -> [remF (quotF i621 2) 2, remF i621 2]))))) (stoScalar (sscalar 2))])) (\\[i438, i439, i440, i441, i442, i443, i444, i445] -> [ifF ((0 <=. i438 + i442 &&* 1 >. i438 + i442) &&* ((0 <=. i439 + i443 &&* 1 >. i439 + i443) &&* ((0 <=. 2 * i440 + i444 &&* 4 >. 2 * i440 + i444) &&* (0 <=. 2 * i441 + i445 &&* 4 >. 2 * i441 + i445)))) 0 1, i438, i439, i440, i441, i442, i443, i444, i445]) ! [0])))))))) [i286, i287, i288, i289] in tpair (tpair (tpair (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w283 (\\[i550, i547] -> [i550, i547, 0]) * rreplicate 4 (rgather [1,4,4] u455 (\\[i552] -> [i552, 0]))) (\\[i610, i611, i612, i613, i614, i615, i616, i617] -> [remF (i617 + 2 * i616 + 4 * i615 + 4 * i613 + 4 * i614) 4, i610, i611, i612]))))) (\\[i456, i457, i458, i459, i460] -> [ifF ((0 <=. i456 + i457 &&* 1 >. i456 + i457) &&* ((0 <=. i458 &&* 1 >. i458) &&* ((0 <=. i459 &&* 2 >. i459) &&* (0 <=. i460 &&* 2 >. i460)))) 0 1, i456, i457, i458, i459, i460]) ! [0]) (\\[i462, i463] -> [i462 + i463]), rsum (rsum (rsum (rtranspose [0,2,3,1] u455)))), tpair (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w342 (\\[i473, i470] -> [i473, i470, 0]) * rreplicate 4 (rgather [1,2,2] u412 (\\[i475] -> [i475, 0]))) (\\[i533, i534, i535, i536, i537, i538, i539, i540] -> [remF (i540 + 2 * i539 + 4 * i538 + 4 * i536 + 4 * i537) 4, i533, i534, i535]))))) (\\[i414, i415, i416, i417, i418] -> [ifF ((0 <=. i414 + i415 &&* 1 >. i414 + i415) &&* ((0 <=. i416 &&* 1 >. i416) &&* ((0 <=. i417 &&* 2 >. i417) &&* (0 <=. i418 &&* 2 >. i418)))) 0 1, i414, i415, i416, i417, i418]) ! [0]) (\\[i420, i421] -> [i420 + i421]), rsum (rsum (rsum (rtranspose [0,2,3,1] u412))))), tpair (tpair (rsum (rtranspose [2,1,0] t381 * rtranspose [2,1,0] (rreplicate 1 m388)), rsum (rtranspose [1,0] m388)), tpair (rmatmul2 m387 (rtranspose [1,0] (m385 * m382)), rsum (rtranspose [1,0] m387))))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. i269 + i272 &&* 1 >. i269 + i272) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. i270 + i274 &&* 4 >. i270 + i274) &&* (0 <=. i271 + i275 &&* 4 >. i271 + i275)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i276, i277] -> [i276 + i277]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. i278 + i279 &&* 1 >. i278 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; x286 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x287 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x288 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x289 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w316 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF (w285 ! [i290, i291, i292, i293, i294, i295, i296, i297, i286, i287, i288, i289] <=. rscalar 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w285 (\\[i298, i299, i300, i301, i302, i303, i304, i305] -> [i298, i299, i300, i301, i302, i303, i304, i305, i286, i287, i288, i289]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [ifF ((0 <=. i308 + i312 &&* 1 >. i308 + i312) &&* ((0 <=. i309 + i313 &&* 1 >. i309 + i313) &&* ((0 <=. 2 * i310 + i314 &&* 4 >. 2 * i310 + i314) &&* (0 <=. 2 * i311 + i315 &&* 4 >. 2 * i311 + i315)))) 0 1, i308, i309, i310, i311, i312, i313, i314, i315])))))))) ; x317 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x318 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x319 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w344 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w316 (\\[i320, i321, i322, i323, i324, i325, i326] -> [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, i317, i324, i318, i319]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i328, i329, i330, i331, i332, i333, i334] -> [ifF ((0 <=. i328 + i331 &&* 1 >. i328 + i331) &&* ((0 <=. i332 &&* 1 >. i332) &&* ((0 <=. i329 + i333 &&* 2 >. i329 + i333) &&* (0 <=. i330 + i334 &&* 2 >. i330 + i334)))) 0 1, i328, i329, i330, i331, i332, i333, i334])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i335, i336] -> [i335 + i336]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i337, i338, i339, i340, i341] -> [ifF ((0 <=. i337 + i338 &&* 1 >. i337 + i338) &&* ((0 <=. i339 &&* 1 >. i339) &&* ((0 <=. i340 &&* 2 >. i340) &&* (0 <=. i341 &&* 2 >. i341)))) 0 1, i337, i338, i339, i340, i341]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; x345 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x346 = stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x347 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; x348 = 2 * stoScalar (sscalar 0) + stoScalar (sscalar 0) ; w375 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354, i355, i356] -> [ifF (w344 ! [i349, i350, i351, i352, i353, i354, i355, i356, i345, i346, i347, i348] <=. rscalar 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w344 (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [i357, i358, i359, i360, i361, i362, i363, i364, i345, i346, i347, i348]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i367, i368, i369, i370, i371, i372, i373, i374] -> [ifF ((0 <=. i367 + i371 &&* 1 >. i367 + i371) &&* ((0 <=. i368 + i372 &&* 1 >. i368 + i372) &&* ((0 <=. 2 * i369 + i373 &&* 2 >. 2 * i369 + i373) &&* (0 <=. 2 * i370 + i374 &&* 2 >. 2 * i370 + i374)))) 0 1, i367, i368, i369, i370, i371, i372, i373, i374]) ; m382 = rmatmul2 (tproject1 (tproject1 (tproject2 u1))) (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w375 (\\[i376, i377, i378, i379] -> [i376, i377, i378, i379, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w375 ! [i376, i377, i378, i379]))))) (stoScalar (sscalar 2))])))) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) in rmatmul2 (tproject1 (tproject2 (tproject2 u1))) (rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i383, i384] -> [ifF (m382 ! [i383, i384] <=. rscalar 0.0) 0 1]) * m382) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject2 u1))))"
