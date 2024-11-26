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
    @?= "\\m385 x1 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. 0 + i272 + i269 &&* 1 >. 0 + i272 + i269) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. 0 + i274 + i270 &&* 4 >. 0 + i274 + i270) &&* (0 <=. 0 + i275 + i271 &&* 4 >. 0 + i275 + i271)))) 0 1])))) ; w284 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i276, i277] -> [0 + i277 + i276]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. 0 + i279 + i278 &&* 1 >. 0 + i279 + i278) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282])))))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * w284) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w286 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w287 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w288 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w289 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w306 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF (w285 ! [i290, i291, i292, i293, i294, i295, i296, i297, w286 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w287 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w288 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w289 !$ [i290, i291, i292, i293, i294, i295, i296, i297]] <=. rscalar 0.0) 0 1]) ; w307 = rgather [1,1,2,2,1,1,2,2] w285 (\\[i298, i299, i300, i301, i302, i303, i304, i305] -> [i298, i299, i300, i301, i302, i303, i304, i305, w286 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w287 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w288 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w289 !$ [i298, i299, i300, i301, i302, i303, i304, i305]]) ; w316 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w306 * w307, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [ifF ((0 <=. 0 + i312 + i308 &&* 1 >. 0 + i312 + i308) &&* ((0 <=. 0 + i313 + i309 &&* 1 >. 0 + i313 + i309) &&* ((0 <=. 0 + i314 + 2 * i310 &&* 4 >. 0 + i314 + 2 * i310) &&* (0 <=. 0 + i315 + 2 * i311 &&* 4 >. 0 + i315 + 2 * i311)))) 0 1, i308, i309, i310, i311, i312, i313, i314, i315])))))))) ; w317 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w318 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w319 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w341 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w316 (\\[i320, i321, i322, i323, i324, i325, i326] -> [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326], 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326]])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326]])))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i327, i328, i329, i330, i331, i332, i333] -> [ifF ((0 <=. 0 + i330 + i327 &&* 1 >. 0 + i330 + i327) &&* ((0 <=. i331 &&* 1 >. i331) &&* ((0 <=. 0 + i332 + i328 &&* 2 >. 0 + i332 + i328) &&* (0 <=. 0 + i333 + i329 &&* 2 >. 0 + i333 + i329)))) 0 1, i327, i328, i329, i330, i331, i332, i333])))) ; w342 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i334, i335] -> [0 + i335 + i334]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i336, i337, i338, i339, i340] -> [ifF ((0 <=. 0 + i337 + i336 &&* 1 >. 0 + i337 + i336) &&* ((0 <=. i338 &&* 1 >. i338) &&* ((0 <=. i339 &&* 2 >. i339) &&* (0 <=. i340 &&* 2 >. i340)))) 0 1, i336, i337, i338, i339, i340])))))) ; w343 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w341 * w342) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w344 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w345 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w346 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,2] FTKScalar) (sfromListLinear [1,2] [0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w347 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,2] FTKScalar) (sfromListLinear [1,2] [0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w364 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i348, i349, i350, i351, i352, i353, i354, i355] -> [ifF (w343 ! [i348, i349, i350, i351, i352, i353, i354, i355, w344 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w345 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w346 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w347 !$ [i348, i349, i350, i351, i352, i353, i354, i355]] <=. rscalar 0.0) 0 1]) ; w365 = rgather [1,1,1,1,1,1,2,2] w343 (\\[i356, i357, i358, i359, i360, i361, i362, i363] -> [i356, i357, i358, i359, i360, i361, i362, i363, w344 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w345 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w346 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w347 !$ [i356, i357, i358, i359, i360, i361, i362, i363]]) ; w374 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w364 * w365, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i366, i367, i368, i369, i370, i371, i372, i373] -> [ifF ((0 <=. 0 + i370 + i366 &&* 1 >. 0 + i370 + i366) &&* ((0 <=. 0 + i371 + i367 &&* 1 >. 0 + i371 + i367) &&* ((0 <=. 0 + i372 + 2 * i368 &&* 2 >. 0 + i372 + 2 * i368) &&* (0 <=. 0 + i373 + 2 * i369 &&* 2 >. 0 + i373 + 2 * i369)))) 0 1, i366, i367, i368, i369, i370, i371, i372, i373]) ; t379 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w374 (\\[i375, i376, i377, i378] -> [i375, i376, i377, i378, 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i375, i376, i377, i378])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i375, i376, i377, i378])))) 2]))))) ; m380 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t379) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m383 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i381, i382] -> [ifF (m380 ! [i381, i382] <=. rscalar 0.0) 0 1]) ; t384 = rtranspose [1,0] (rreplicate 10 (m383 * m380)) ; m386 = m383 * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rreplicate 1 m385)) ; t387 = rreplicate 1 m386 ; w400 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rtranspose [1,0] (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t387))))) (\\[i388, i389, i390, i391] -> [i388, i389, i390, i391, 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i388, i389, i390, i391])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i388, i389, i390, i391])))) 2])) (\\[i392, i393, i394, i395, i396, i397, i398, i399] -> [ifF ((0 <=. 0 + i396 + i392 &&* 1 >. 0 + i396 + i392) &&* ((0 <=. 0 + i397 + i393 &&* 1 >. 0 + i397 + i393) &&* ((0 <=. 0 + i398 + 2 * i394 &&* 2 >. 0 + i398 + 2 * i394) &&* (0 <=. 0 + i399 + 2 * i395 &&* 2 >. 0 + i399 + 2 * i395)))) 0 1, i392, i393, i394, i395, i396, i397, i398, i399]) ; u409 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w364 * w400 ! [0]) (\\[i401, i402, i403, i404, i405, i406, i407, i408] -> [i401, i402, i403, i404, i405, i406, i407, i408, w344 !$ [i401, i402, i403, i404, i405, i406, i407, i408], w345 !$ [i401, i402, i403, i404, i405, i406, i407, i408], w346 !$ [i401, i402, i403, i404, i405, i406, i407, i408], w347 !$ [i401, i402, i403, i404, i405, i406, i407, i408]]))))))))) ; w410 = rreplicate 4 u409 ; w416 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w341 * w410)))))) (\\[i411, i412, i413, i414, i415] -> [ifF ((0 <=. 0 + i412 + i411 &&* 1 >. 0 + i412 + i411) &&* ((0 <=. i413 &&* 1 >. i413) &&* ((0 <=. i414 &&* 2 >. i414) &&* (0 <=. i415 &&* 2 >. i415)))) 0 1, i411, i412, i413, i414, i415]) ; w426 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] (w342 * w410)))) (\\[i419, i420, i421, i422, i423, i424, i425] -> [ifF ((0 <=. 0 + i422 + i419 &&* 1 >. 0 + i422 + i419) &&* ((0 <=. i423 &&* 1 >. i423) &&* ((0 <=. 0 + i424 + i420 &&* 2 >. 0 + i424 + i420) &&* (0 <=. 0 + i425 + i421 &&* 2 >. 0 + i425 + i421)))) 0 1, i419, i420, i421, i422, i423, i424, i425]) ; w442 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w426 ! [0]) (\\[i427, i428, i429, i430, i431, i432, i433] -> [i427, i428, i429, i430, i431, i432, i433, w317 !$ [i427, i428, i429, i430, i431, i432, i433], i431, w318 !$ [i427, i428, i429, i430, i431, i432, i433], w319 !$ [i427, i428, i429, i430, i431, i432, i433], 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i427, i428, i429, i430, i431, i432, i433, w317 !$ [i427, i428, i429, i430, i431, i432, i433], i431, w318 !$ [i427, i428, i429, i430, i431, i432, i433], w319 !$ [i427, i428, i429, i430, i431, i432, i433]])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i427, i428, i429, i430, i431, i432, i433, w317 !$ [i427, i428, i429, i430, i431, i432, i433], i431, w318 !$ [i427, i428, i429, i430, i431, i432, i433], w319 !$ [i427, i428, i429, i430, i431, i432, i433]])))) 2]))))))))) (\\[i434, i435, i436, i437, i438, i439, i440, i441] -> [ifF ((0 <=. 0 + i438 + i434 &&* 1 >. 0 + i438 + i434) &&* ((0 <=. 0 + i439 + i435 &&* 1 >. 0 + i439 + i435) &&* ((0 <=. 0 + i440 + 2 * i436 &&* 4 >. 0 + i440 + 2 * i436) &&* (0 <=. 0 + i441 + 2 * i437 &&* 4 >. 0 + i441 + 2 * i437)))) 0 1, i434, i435, i436, i437, i438, i439, i440, i441]) ; u451 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w306 * w442 ! [0]) (\\[i443, i444, i445, i446, i447, i448, i449, i450] -> [i443, i444, i445, i446, i447, i448, i449, i450, w286 !$ [i443, i444, i445, i446, i447, i448, i449, i450], w287 !$ [i443, i444, i445, i446, i447, i448, i449, i450], w288 !$ [i443, i444, i445, i446, i447, i448, i449, i450], w289 !$ [i443, i444, i445, i446, i447, i448, i449, i450]]))))))))) ; w457 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w283 * rreplicate 4 u451)))))) (\\[i452, i453, i454, i455, i456] -> [ifF ((0 <=. 0 + i453 + i452 &&* 1 >. 0 + i453 + i452) &&* ((0 <=. i454 &&* 1 >. i454) &&* ((0 <=. i455 &&* 2 >. i455) &&* (0 <=. i456 &&* 2 >. i456)))) 0 1, i452, i453, i454, i455, i456]) in tpair (tpair (tpair (rscatter [1,1,2,2] (w457 ! [0]) (\\[i458, i459] -> [0 + i459 + i458]), rsum (rsum (rsum (rtranspose [0,2,3,1] u451)))), tpair (rscatter [1,1,2,2] (w416 ! [0]) (\\[i417, i418] -> [0 + i418 + i417]), rsum (rsum (rsum (rtranspose [0,2,3,1] u409))))), tpair (tpair (rsum (rtranspose [2,1,0] (t379 * t387)), rsum (rtranspose [1,0] m386)), tpair (rsum (rtranspose [2,1,0] (t384 * rreplicate 1 m385)), rsum (rtranspose [1,0] m385))))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. 0 + i272 + i269 &&* 1 >. 0 + i272 + i269) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. 0 + i274 + i270 &&* 4 >. 0 + i274 + i270) &&* (0 <=. 0 + i275 + i271 &&* 4 >. 0 + i275 + i271)))) 0 1])))) ; w284 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i276, i277] -> [0 + i277 + i276]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. 0 + i279 + i278 &&* 1 >. 0 + i279 + i278) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282])))))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * w284) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w286 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w287 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w288 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w289 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w306 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF (w285 ! [i290, i291, i292, i293, i294, i295, i296, i297, w286 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w287 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w288 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w289 !$ [i290, i291, i292, i293, i294, i295, i296, i297]] <=. rscalar 0.0) 0 1]) ; w307 = rgather [1,1,2,2,1,1,2,2] w285 (\\[i298, i299, i300, i301, i302, i303, i304, i305] -> [i298, i299, i300, i301, i302, i303, i304, i305, w286 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w287 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w288 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w289 !$ [i298, i299, i300, i301, i302, i303, i304, i305]]) ; w316 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w306 * w307, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [ifF ((0 <=. 0 + i312 + i308 &&* 1 >. 0 + i312 + i308) &&* ((0 <=. 0 + i313 + i309 &&* 1 >. 0 + i313 + i309) &&* ((0 <=. 0 + i314 + 2 * i310 &&* 4 >. 0 + i314 + 2 * i310) &&* (0 <=. 0 + i315 + 2 * i311 &&* 4 >. 0 + i315 + 2 * i311)))) 0 1, i308, i309, i310, i311, i312, i313, i314, i315])))))))) ; w317 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w318 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w319 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w341 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w316 (\\[i320, i321, i322, i323, i324, i325, i326] -> [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326], 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326]])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326]])))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i327, i328, i329, i330, i331, i332, i333] -> [ifF ((0 <=. 0 + i330 + i327 &&* 1 >. 0 + i330 + i327) &&* ((0 <=. i331 &&* 1 >. i331) &&* ((0 <=. 0 + i332 + i328 &&* 2 >. 0 + i332 + i328) &&* (0 <=. 0 + i333 + i329 &&* 2 >. 0 + i333 + i329)))) 0 1, i327, i328, i329, i330, i331, i332, i333])))) ; w342 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i334, i335] -> [0 + i335 + i334]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i336, i337, i338, i339, i340] -> [ifF ((0 <=. 0 + i337 + i336 &&* 1 >. 0 + i337 + i336) &&* ((0 <=. i338 &&* 1 >. i338) &&* ((0 <=. i339 &&* 2 >. i339) &&* (0 <=. i340 &&* 2 >. i340)))) 0 1, i336, i337, i338, i339, i340])))))) ; w343 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w341 * w342) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w344 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w345 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w346 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,2] FTKScalar) (sfromListLinear [1,2] [0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w347 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,2] FTKScalar) (sfromListLinear [1,2] [0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w364 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i348, i349, i350, i351, i352, i353, i354, i355] -> [ifF (w343 ! [i348, i349, i350, i351, i352, i353, i354, i355, w344 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w345 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w346 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w347 !$ [i348, i349, i350, i351, i352, i353, i354, i355]] <=. rscalar 0.0) 0 1]) ; w365 = rgather [1,1,1,1,1,1,2,2] w343 (\\[i356, i357, i358, i359, i360, i361, i362, i363] -> [i356, i357, i358, i359, i360, i361, i362, i363, w344 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w345 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w346 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w347 !$ [i356, i357, i358, i359, i360, i361, i362, i363]]) ; w374 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w364 * w365, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i366, i367, i368, i369, i370, i371, i372, i373] -> [ifF ((0 <=. 0 + i370 + i366 &&* 1 >. 0 + i370 + i366) &&* ((0 <=. 0 + i371 + i367 &&* 1 >. 0 + i371 + i367) &&* ((0 <=. 0 + i372 + 2 * i368 &&* 2 >. 0 + i372 + 2 * i368) &&* (0 <=. 0 + i373 + 2 * i369 &&* 2 >. 0 + i373 + 2 * i369)))) 0 1, i366, i367, i368, i369, i370, i371, i372, i373]) ; t379 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w374 (\\[i375, i376, i377, i378] -> [i375, i376, i377, i378, 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i375, i376, i377, i378])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i375, i376, i377, i378])))) 2]))))) ; m380 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t379) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m383 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i381, i382] -> [ifF (m380 ! [i381, i382] <=. rscalar 0.0) 0 1]) ; t384 = rtranspose [1,0] (rreplicate 10 (m383 * m380)) in rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * t384) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m385 x1 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. 0 + i272 + i269 &&* 1 >. 0 + i272 + i269) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. 0 + i274 + i270 &&* 4 >. 0 + i274 + i270) &&* (0 <=. 0 + i275 + i271 &&* 4 >. 0 + i275 + i271)))) 0 1])))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i276, i277] -> [0 + i277 + i276]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. 0 + i279 + i278 &&* 1 >. 0 + i279 + i278) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w286 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w287 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w288 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w289 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w306 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF (w285 ! [i290, i291, i292, i293, i294, i295, i296, i297, w286 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w287 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w288 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w289 !$ [i290, i291, i292, i293, i294, i295, i296, i297]] <=. rscalar 0.0) 0 1]) ; w316 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w306 * rgather [1,1,2,2,1,1,2,2] w285 (\\[i298, i299, i300, i301, i302, i303, i304, i305] -> [i298, i299, i300, i301, i302, i303, i304, i305, w286 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w287 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w288 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w289 !$ [i298, i299, i300, i301, i302, i303, i304, i305]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [ifF ((0 <=. 0 + i312 + i308 &&* 1 >. 0 + i312 + i308) &&* ((0 <=. 0 + i313 + i309 &&* 1 >. 0 + i313 + i309) &&* ((0 <=. 0 + i314 + 2 * i310 &&* 4 >. 0 + i314 + 2 * i310) &&* (0 <=. 0 + i315 + 2 * i311 &&* 4 >. 0 + i315 + 2 * i311)))) 0 1, i308, i309, i310, i311, i312, i313, i314, i315])))))))) ; w317 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w318 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w319 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w341 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w316 (\\[i320, i321, i322, i323, i324, i325, i326] -> [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326], 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326]])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326]])))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i327, i328, i329, i330, i331, i332, i333] -> [ifF ((0 <=. 0 + i330 + i327 &&* 1 >. 0 + i330 + i327) &&* ((0 <=. i331 &&* 1 >. i331) &&* ((0 <=. 0 + i332 + i328 &&* 2 >. 0 + i332 + i328) &&* (0 <=. 0 + i333 + i329 &&* 2 >. 0 + i333 + i329)))) 0 1, i327, i328, i329, i330, i331, i332, i333])))) ; w342 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i334, i335] -> [0 + i335 + i334]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i336, i337, i338, i339, i340] -> [ifF ((0 <=. 0 + i337 + i336 &&* 1 >. 0 + i337 + i336) &&* ((0 <=. i338 &&* 1 >. i338) &&* ((0 <=. i339 &&* 2 >. i339) &&* (0 <=. i340 &&* 2 >. i340)))) 0 1, i336, i337, i338, i339, i340])))))) ; w343 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w341 * w342) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w344 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w345 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w346 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,2] FTKScalar) (sfromListLinear [1,2] [0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w347 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,2] FTKScalar) (sfromListLinear [1,2] [0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w364 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i348, i349, i350, i351, i352, i353, i354, i355] -> [ifF (w343 ! [i348, i349, i350, i351, i352, i353, i354, i355, w344 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w345 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w346 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w347 !$ [i348, i349, i350, i351, i352, i353, i354, i355]] <=. rscalar 0.0) 0 1]) ; w374 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w364 * rgather [1,1,1,1,1,1,2,2] w343 (\\[i356, i357, i358, i359, i360, i361, i362, i363] -> [i356, i357, i358, i359, i360, i361, i362, i363, w344 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w345 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w346 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w347 !$ [i356, i357, i358, i359, i360, i361, i362, i363]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i366, i367, i368, i369, i370, i371, i372, i373] -> [ifF ((0 <=. 0 + i370 + i366 &&* 1 >. 0 + i370 + i366) &&* ((0 <=. 0 + i371 + i367 &&* 1 >. 0 + i371 + i367) &&* ((0 <=. 0 + i372 + 2 * i368 &&* 2 >. 0 + i372 + 2 * i368) &&* (0 <=. 0 + i373 + 2 * i369 &&* 2 >. 0 + i373 + 2 * i369)))) 0 1, i366, i367, i368, i369, i370, i371, i372, i373]) ; t379 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w374 (\\[i375, i376, i377, i378] -> [i375, i376, i377, i378, 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i375, i376, i377, i378])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i375, i376, i377, i378])))) 2])))) ; m380 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t379) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m383 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i381, i382] -> [ifF (m380 ! [i381, i382] <=. rscalar 0.0) 0 1]) ; m386 = m383 * rsum (rtranspose [1,2,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rtranspose [1,0] (rreplicate 1 m385)) ; u409 = rscatter [1,1,2,2] (w364 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] (tproject1 (tproject1 (tproject2 u1))) (\\[i651] -> [i651, 0]) * rgather [1] m386 (\\[i648] -> [i648, 0]))))))) (\\[i388, i389, i390, i391] -> [i388, i389, i390, i391, 0, 0, remF (quotF (sfromR (rmaxIndex (rgather [4] (w374 ! [i388, i389, i390, i391, 0, 0]) (\\[i641] -> [remF (quotF i641 2) 2, remF i641 2])))) 2) 2, remF (sfromR (rmaxIndex (rgather [4] (w374 ! [i388, i389, i390, i391, 0, 0]) (\\[i642] -> [remF (quotF i642 2) 2, remF i642 2])))) 2])) (\\[i392, i393, i394, i395, i396, i397, i398, i399] -> [ifF ((0 <=. 0 + i396 + i392 &&* 1 >. 0 + i396 + i392) &&* ((0 <=. 0 + i397 + i393 &&* 1 >. 0 + i397 + i393) &&* ((0 <=. 0 + i398 + 2 * i394 &&* 2 >. 0 + i398 + 2 * i394) &&* (0 <=. 0 + i399 + 2 * i395 &&* 2 >. 0 + i399 + 2 * i395)))) 0 1, i392, i393, i394, i395, i396, i397, i398, i399]) ! [0]) (\\[i401, i402, i403, i404, i405, i406, i407, i408] -> [w344 !$ [i401, i402, i403, i404, i405, i406, i407, i408], w345 !$ [i401, i402, i403, i404, i405, i406, i407, i408], w346 !$ [i401, i402, i403, i404, i405, i406, i407, i408], w347 !$ [i401, i402, i403, i404, i405, i406, i407, i408]]) ; u451 = rscatter [1,1,4,4] (w306 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w342 (\\[i625, i626, i627, i624] -> [i627, 0, i624, i625, i626]) * rgather [2,2,4,1] (u409 ! [0]) (\\[i630, i631, i632, i629] -> [i629, i630, i631])) (\\[i633, i634, i635, i636, i637, i638, i639, i640] -> [remF (quotF (i640 + 2 * i639 + 4 * i638 + 4 * i637 + 4 * i636 + 16 * i634 + 8 * i635) 8) 2, remF (quotF (i640 + 2 * i639 + 4 * i638 + 4 * i637 + 4 * i636 + 16 * i634 + 8 * i635) 4) 2, remF (i640 + 2 * i639 + 4 * i638 + 4 * i637 + 4 * i636 + 16 * i634 + 8 * i635) 4, i633]))) (\\[i419, i420, i421, i422, i423, i424, i425] -> [ifF ((0 <=. 0 + i422 + i419 &&* 1 >. 0 + i422 + i419) &&* ((0 <=. i423 &&* 1 >. i423) &&* ((0 <=. 0 + i424 + i420 &&* 2 >. 0 + i424 + i420) &&* (0 <=. 0 + i425 + i421 &&* 2 >. 0 + i425 + i421)))) 0 1, i419, i420, i421, i422, i423, i424, i425]) ! [0]) (\\[i427, i428, i429, i430, i431, i432, i433] -> [w317 !$ [i427, i428, i429, i430, i431, i432, i433], i431, w318 !$ [i427, i428, i429, i430, i431, i432, i433], w319 !$ [i427, i428, i429, i430, i431, i432, i433], 0, 0, remF (quotF (sfromR (rmaxIndex (rgather [4] (w316 ! [i427, i428, i429, i430, i431, i432, i433, w317 !$ [i427, i428, i429, i430, i431, i432, i433], i431, w318 !$ [i427, i428, i429, i430, i431, i432, i433], w319 !$ [i427, i428, i429, i430, i431, i432, i433], 0, 0]) (\\[i614] -> [remF (quotF i614 2) 2, remF i614 2])))) 2) 2, remF (sfromR (rmaxIndex (rgather [4] (w316 ! [i427, i428, i429, i430, i431, i432, i433, w317 !$ [i427, i428, i429, i430, i431, i432, i433], i431, w318 !$ [i427, i428, i429, i430, i431, i432, i433], w319 !$ [i427, i428, i429, i430, i431, i432, i433], 0, 0]) (\\[i615] -> [remF (quotF i615 2) 2, remF i615 2])))) 2])) (\\[i434, i435, i436, i437, i438, i439, i440, i441] -> [ifF ((0 <=. 0 + i438 + i434 &&* 1 >. 0 + i438 + i434) &&* ((0 <=. 0 + i439 + i435 &&* 1 >. 0 + i439 + i435) &&* ((0 <=. 0 + i440 + 2 * i436 &&* 4 >. 0 + i440 + 2 * i436) &&* (0 <=. 0 + i441 + 2 * i437 &&* 4 >. 0 + i441 + 2 * i437)))) 0 1, i434, i435, i436, i437, i438, i439, i440, i441]) ! [0]) (\\[i443, i444, i445, i446, i447, i448, i449, i450] -> [w286 !$ [i443, i444, i445, i446, i447, i448, i449, i450], w287 !$ [i443, i444, i445, i446, i447, i448, i449, i450], w288 !$ [i443, i444, i445, i446, i447, i448, i449, i450], w289 !$ [i443, i444, i445, i446, i447, i448, i449, i450]]) in tpair (tpair (tpair (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w283 (\\[i546, i543] -> [i546, i543, 0]) * rreplicate 4 (rgather [1,4,4] u451 (\\[i548] -> [i548, 0]))) (\\[i606, i607, i608, i609, i610, i611, i612, i613] -> [remF (i613 + 2 * i612 + 4 * i611 + 4 * i609 + 4 * i610) 4, i606, i607, i608]))))) (\\[i452, i453, i454, i455, i456] -> [ifF ((0 <=. 0 + i453 + i452 &&* 1 >. 0 + i453 + i452) &&* ((0 <=. i454 &&* 1 >. i454) &&* ((0 <=. i455 &&* 2 >. i455) &&* (0 <=. i456 &&* 2 >. i456)))) 0 1, i452, i453, i454, i455, i456]) ! [0]) (\\[i458, i459] -> [0 + i459 + i458]), rsum (rsum (rsum (rtranspose [0,2,3,1] u451)))), tpair (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w341 (\\[i469, i466] -> [i469, i466, 0]) * rreplicate 4 (rgather [1,2,2] u409 (\\[i471] -> [i471, 0]))) (\\[i529, i530, i531, i532, i533, i534, i535, i536] -> [remF (i536 + 2 * i535 + 4 * i534 + 4 * i532 + 4 * i533) 4, i529, i530, i531]))))) (\\[i411, i412, i413, i414, i415] -> [ifF ((0 <=. 0 + i412 + i411 &&* 1 >. 0 + i412 + i411) &&* ((0 <=. i413 &&* 1 >. i413) &&* ((0 <=. i414 &&* 2 >. i414) &&* (0 <=. i415 &&* 2 >. i415)))) 0 1, i411, i412, i413, i414, i415]) ! [0]) (\\[i417, i418] -> [0 + i418 + i417]), rsum (rsum (rsum (rtranspose [0,2,3,1] u409))))), tpair (tpair (rsum (rtranspose [2,1,0] t379 * rtranspose [2,1,0] (rreplicate 1 m386)), rsum (rtranspose [1,0] m386)), tpair (rsum (rtranspose [2,0,1] (rreplicate 10 (m383 * m380)) * rtranspose [2,1,0] (rreplicate 1 m385)), rsum (rtranspose [1,0] m385))))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. 0 + i272 + i269 &&* 1 >. 0 + i272 + i269) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. 0 + i274 + i270 &&* 4 >. 0 + i274 + i270) &&* (0 <=. 0 + i275 + i271 &&* 4 >. 0 + i275 + i271)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i276, i277] -> [0 + i277 + i276]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. 0 + i279 + i278 &&* 1 >. 0 + i279 + i278) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w286 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w287 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w288 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w289 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w316 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i290, i291, i292, i293, i294, i295, i296, i297] -> [ifF (w285 ! [i290, i291, i292, i293, i294, i295, i296, i297, w286 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w287 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w288 !$ [i290, i291, i292, i293, i294, i295, i296, i297], w289 !$ [i290, i291, i292, i293, i294, i295, i296, i297]] <=. rscalar 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w285 (\\[i298, i299, i300, i301, i302, i303, i304, i305] -> [i298, i299, i300, i301, i302, i303, i304, i305, w286 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w287 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w288 !$ [i298, i299, i300, i301, i302, i303, i304, i305], w289 !$ [i298, i299, i300, i301, i302, i303, i304, i305]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [ifF ((0 <=. 0 + i312 + i308 &&* 1 >. 0 + i312 + i308) &&* ((0 <=. 0 + i313 + i309 &&* 1 >. 0 + i313 + i309) &&* ((0 <=. 0 + i314 + 2 * i310 &&* 4 >. 0 + i314 + 2 * i310) &&* (0 <=. 0 + i315 + 2 * i311 &&* 4 >. 0 + i315 + 2 * i311)))) 0 1, i308, i309, i310, i311, i312, i313, i314, i315])))))))) ; w317 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w318 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w319 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))))))) ; w343 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w316 (\\[i320, i321, i322, i323, i324, i325, i326] -> [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326], 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326]])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w316 ! [i320, i321, i322, i323, i324, i325, i326, w317 !$ [i320, i321, i322, i323, i324, i325, i326], i324, w318 !$ [i320, i321, i322, i323, i324, i325, i326], w319 !$ [i320, i321, i322, i323, i324, i325, i326]])))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i327, i328, i329, i330, i331, i332, i333] -> [ifF ((0 <=. 0 + i330 + i327 &&* 1 >. 0 + i330 + i327) &&* ((0 <=. i331 &&* 1 >. i331) &&* ((0 <=. 0 + i332 + i328 &&* 2 >. 0 + i332 + i328) &&* (0 <=. 0 + i333 + i329 &&* 2 >. 0 + i333 + i329)))) 0 1, i327, i328, i329, i330, i331, i332, i333])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i334, i335] -> [0 + i335 + i334]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i336, i337, i338, i339, i340] -> [ifF ((0 <=. 0 + i337 + i336 &&* 1 >. 0 + i337 + i336) &&* ((0 <=. i338 &&* 1 >. i338) &&* ((0 <=. i339 &&* 2 >. i339) &&* (0 <=. i340 &&* 2 >. i340)))) 0 1, i336, i337, i338, i339, i340]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w344 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w345 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,1] FTKScalar) (sfromListLinear [1,1] [0]) + sreplicate siota + stranspose (sreplicate siota)))))))) ; w346 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,2] FTKScalar) (sfromListLinear [1,2] [0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w347 = stranspose (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (tconcrete (FTKS [1,2] FTKScalar) (sfromListLinear [1,2] [0,0]) + sreplicate siota + stranspose (sreplicate (sreplicate (sscalar 2) * siota))))))))) ; w374 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i348, i349, i350, i351, i352, i353, i354, i355] -> [ifF (w343 ! [i348, i349, i350, i351, i352, i353, i354, i355, w344 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w345 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w346 !$ [i348, i349, i350, i351, i352, i353, i354, i355], w347 !$ [i348, i349, i350, i351, i352, i353, i354, i355]] <=. rscalar 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w343 (\\[i356, i357, i358, i359, i360, i361, i362, i363] -> [i356, i357, i358, i359, i360, i361, i362, i363, w344 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w345 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w346 !$ [i356, i357, i358, i359, i360, i361, i362, i363], w347 !$ [i356, i357, i358, i359, i360, i361, i362, i363]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i366, i367, i368, i369, i370, i371, i372, i373] -> [ifF ((0 <=. 0 + i370 + i366 &&* 1 >. 0 + i370 + i366) &&* ((0 <=. 0 + i371 + i367 &&* 1 >. 0 + i371 + i367) &&* ((0 <=. 0 + i372 + 2 * i368 &&* 2 >. 0 + i372 + 2 * i368) &&* (0 <=. 0 + i373 + 2 * i369 &&* 2 >. 0 + i373 + 2 * i369)))) 0 1, i366, i367, i368, i369, i370, i371, i372, i373]) ; m380 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w374 (\\[i375, i376, i377, i378] -> [i375, i376, i377, i378, 0, 0, remF (quotF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i375, i376, i377, i378])))) 2) 2, remF (sfromR (rmaxIndex (rreshape [4] (w374 ! [i375, i376, i377, i378])))) 2]))))) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) in rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i381, i382] -> [ifF (m380 ! [i381, i382] <=. rscalar 0.0) 0 1]) * m380))) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject2 u1))))"
