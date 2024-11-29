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
    @?= "\\m345 x1 -> let w252 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i238, i239, i240, i241, i242, i243, i244] -> [ifF ((0 <=. i238 + i241 &&* 1 >. i238 + i241) &&* ((0 <=. i242 &&* 1 >. i242) &&* ((0 <=. i239 + i243 &&* 4 >. i239 + i243) &&* (0 <=. i240 + i244 &&* 4 >. i240 + i244)))) 0 1])))) ; w253 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i245, i246] -> [i245 + i246]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i247, i248, i249, i250, i251] -> [ifF ((0 <=. i247 + i248 &&* 1 >. i247 + i248) &&* ((0 <=. i249 &&* 1 >. i249) &&* ((0 <=. i250 &&* 2 >. i250) &&* (0 <=. i251 &&* 2 >. i251)))) 0 1, i247, i248, i249, i250, i251])))))) ; w254 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w252 * w253) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w271 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i255, i256, i257, i258, i259, i260, i261, i262] -> [ifF (w254 ! [i255, i256, i257, i258, i259, i260, i261, i262, i255, i256, 0, 0] <=. rscalar 0.0) 0 1]) ; w272 = rgather [1,1,2,2,1,1,2,2] w254 (\\[i263, i264, i265, i266, i267, i268, i269, i270] -> [i263, i264, i265, i266, i267, i268, i269, i270, i263, i264, 0, 0]) ; w281 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w271 * w272, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i273, i274, i275, i276, i277, i278, i279, i280] -> [ifF ((0 <=. i273 + i277 &&* 1 >. i273 + i277) &&* ((0 <=. i274 + i278 &&* 1 >. i274 + i278) &&* ((0 <=. 2 * i275 + i279 &&* 4 >. 2 * i275 + i279) &&* (0 <=. 2 * i276 + i280 &&* 4 >. 2 * i276 + i280)))) 0 1, i273, i274, i275, i276, i277, i278, i279, i280])))))))) ; x289 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w304 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w281 (\\[i282, i283, i284, i285, i286, i287, i288] -> [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2) * i289)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i290, i291, i292, i293, i294, i295, i296] -> [ifF ((0 <=. i290 + i293 &&* 1 >. i290 + i293) &&* ((0 <=. i294 &&* 1 >. i294) &&* ((0 <=. i291 + i295 &&* 2 >. i291 + i295) &&* (0 <=. i292 + i296 &&* 2 >. i292 + i296)))) 0 1, i290, i291, i292, i293, i294, i295, i296])))) ; w305 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i297, i298] -> [i297 + i298]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i299, i300, i301, i302, i303] -> [ifF ((0 <=. i299 + i300 &&* 1 >. i299 + i300) &&* ((0 <=. i301 &&* 1 >. i301) &&* ((0 <=. i302 &&* 2 >. i302) &&* (0 <=. i303 &&* 2 >. i303)))) 0 1, i299, i300, i301, i302, i303])))))) ; w306 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w304 * w305) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w323 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [ifF (w306 ! [i307, i308, i309, i310, i311, i312, i313, i314, i307, i308, 0, 0] <=. rscalar 0.0) 0 1]) ; w324 = rgather [1,1,1,1,1,1,2,2] w306 (\\[i315, i316, i317, i318, i319, i320, i321, i322] -> [i315, i316, i317, i318, i319, i320, i321, i322, i315, i316, 0, 0]) ; w333 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w323 * w324, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i325, i326, i327, i328, i329, i330, i331, i332] -> [ifF ((0 <=. i325 + i329 &&* 1 >. i325 + i329) &&* ((0 <=. i326 + i330 &&* 1 >. i326 + i330) &&* ((0 <=. 2 * i327 + i331 &&* 2 >. 2 * i327 + i331) &&* (0 <=. 2 * i328 + i332 &&* 2 >. 2 * i328 + i332)))) 0 1, i325, i326, i327, i328, i329, i330, i331, i332]) ; x338 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; t339 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w333 (\\[i334, i335, i336, i337] -> [i334, i335, i336, i337, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2) * i338)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2))]))))) ; m340 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t339) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m343 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i341, i342] -> [ifF (m340 ! [i341, i342] <=. rscalar 0.0) 0 1]) ; t344 = rtranspose [1,0] (rreplicate 10 (m343 * m340)) ; m346 = m343 * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rreplicate 1 m345)) ; t347 = rreplicate 1 m346 ; x352 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w361 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rtranspose [1,0] (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t347))))) (\\[i348, i349, i350, i351] -> [i348, i349, i350, i351, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i348, i349, i350, i351]))))) (stoScalar (sscalar 2) * i352)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i348, i349, i350, i351]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i348, i349, i350, i351]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i348, i349, i350, i351]))))) (stoScalar (sscalar 2))])) (\\[i353, i354, i355, i356, i357, i358, i359, i360] -> [ifF ((0 <=. i353 + i357 &&* 1 >. i353 + i357) &&* ((0 <=. i354 + i358 &&* 1 >. i354 + i358) &&* ((0 <=. 2 * i355 + i359 &&* 2 >. 2 * i355 + i359) &&* (0 <=. 2 * i356 + i360 &&* 2 >. 2 * i356 + i360)))) 0 1, i353, i354, i355, i356, i357, i358, i359, i360]) ; u370 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w323 * w361 ! [0]) (\\[i362, i363, i364, i365, i366, i367, i368, i369] -> [i362, i363, i364, i365, i366, i367, i368, i369, i362, i363, 0, 0]))))))))) ; w371 = rreplicate 4 u370 ; w377 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w304 * w371)))))) (\\[i372, i373, i374, i375, i376] -> [ifF ((0 <=. i372 + i373 &&* 1 >. i372 + i373) &&* ((0 <=. i374 &&* 1 >. i374) &&* ((0 <=. i375 &&* 2 >. i375) &&* (0 <=. i376 &&* 2 >. i376)))) 0 1, i372, i373, i374, i375, i376]) ; w387 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] (w305 * w371)))) (\\[i380, i381, i382, i383, i384, i385, i386] -> [ifF ((0 <=. i380 + i383 &&* 1 >. i380 + i383) &&* ((0 <=. i384 &&* 1 >. i384) &&* ((0 <=. i381 + i385 &&* 2 >. i381 + i385) &&* (0 <=. i382 + i386 &&* 2 >. i382 + i386)))) 0 1, i380, i381, i382, i383, i384, i385, i386]) ; x395 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w404 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w387 ! [0]) (\\[i388, i389, i390, i391, i392, i393, i394] -> [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390]))))) (stoScalar (sscalar 2) * i395)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390]))))) (stoScalar (sscalar 2))]))))))))) (\\[i396, i397, i398, i399, i400, i401, i402, i403] -> [ifF ((0 <=. i396 + i400 &&* 1 >. i396 + i400) &&* ((0 <=. i397 + i401 &&* 1 >. i397 + i401) &&* ((0 <=. 2 * i398 + i402 &&* 4 >. 2 * i398 + i402) &&* (0 <=. 2 * i399 + i403 &&* 4 >. 2 * i399 + i403)))) 0 1, i396, i397, i398, i399, i400, i401, i402, i403]) ; u413 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w271 * w404 ! [0]) (\\[i405, i406, i407, i408, i409, i410, i411, i412] -> [i405, i406, i407, i408, i409, i410, i411, i412, i405, i406, 0, 0]))))))))) ; w419 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w252 * rreplicate 4 u413)))))) (\\[i414, i415, i416, i417, i418] -> [ifF ((0 <=. i414 + i415 &&* 1 >. i414 + i415) &&* ((0 <=. i416 &&* 1 >. i416) &&* ((0 <=. i417 &&* 2 >. i417) &&* (0 <=. i418 &&* 2 >. i418)))) 0 1, i414, i415, i416, i417, i418]) in tpair (tpair (tpair (rscatter [1,1,2,2] (w419 ! [0]) (\\[i420, i421] -> [i420 + i421]), rsum (rsum (rsum (rtranspose [0,2,3,1] u413)))), tpair (rscatter [1,1,2,2] (w377 ! [0]) (\\[i378, i379] -> [i378 + i379]), rsum (rsum (rsum (rtranspose [0,2,3,1] u370))))), tpair (tpair (rsum (rtranspose [2,1,0] (t339 * t347)), rsum (rtranspose [1,0] m346)), tpair (rsum (rtranspose [2,1,0] (t344 * rreplicate 1 m345)), rsum (rtranspose [1,0] m345))))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let w252 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i238, i239, i240, i241, i242, i243, i244] -> [ifF ((0 <=. i238 + i241 &&* 1 >. i238 + i241) &&* ((0 <=. i242 &&* 1 >. i242) &&* ((0 <=. i239 + i243 &&* 4 >. i239 + i243) &&* (0 <=. i240 + i244 &&* 4 >. i240 + i244)))) 0 1])))) ; w253 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i245, i246] -> [i245 + i246]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i247, i248, i249, i250, i251] -> [ifF ((0 <=. i247 + i248 &&* 1 >. i247 + i248) &&* ((0 <=. i249 &&* 1 >. i249) &&* ((0 <=. i250 &&* 2 >. i250) &&* (0 <=. i251 &&* 2 >. i251)))) 0 1, i247, i248, i249, i250, i251])))))) ; w254 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w252 * w253) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w271 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i255, i256, i257, i258, i259, i260, i261, i262] -> [ifF (w254 ! [i255, i256, i257, i258, i259, i260, i261, i262, i255, i256, 0, 0] <=. rscalar 0.0) 0 1]) ; w272 = rgather [1,1,2,2,1,1,2,2] w254 (\\[i263, i264, i265, i266, i267, i268, i269, i270] -> [i263, i264, i265, i266, i267, i268, i269, i270, i263, i264, 0, 0]) ; w281 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w271 * w272, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i273, i274, i275, i276, i277, i278, i279, i280] -> [ifF ((0 <=. i273 + i277 &&* 1 >. i273 + i277) &&* ((0 <=. i274 + i278 &&* 1 >. i274 + i278) &&* ((0 <=. 2 * i275 + i279 &&* 4 >. 2 * i275 + i279) &&* (0 <=. 2 * i276 + i280 &&* 4 >. 2 * i276 + i280)))) 0 1, i273, i274, i275, i276, i277, i278, i279, i280])))))))) ; x289 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; w304 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w281 (\\[i282, i283, i284, i285, i286, i287, i288] -> [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2) * i289)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i290, i291, i292, i293, i294, i295, i296] -> [ifF ((0 <=. i290 + i293 &&* 1 >. i290 + i293) &&* ((0 <=. i294 &&* 1 >. i294) &&* ((0 <=. i291 + i295 &&* 2 >. i291 + i295) &&* (0 <=. i292 + i296 &&* 2 >. i292 + i296)))) 0 1, i290, i291, i292, i293, i294, i295, i296])))) ; w305 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i297, i298] -> [i297 + i298]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i299, i300, i301, i302, i303] -> [ifF ((0 <=. i299 + i300 &&* 1 >. i299 + i300) &&* ((0 <=. i301 &&* 1 >. i301) &&* ((0 <=. i302 &&* 2 >. i302) &&* (0 <=. i303 &&* 2 >. i303)))) 0 1, i299, i300, i301, i302, i303])))))) ; w306 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w304 * w305) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w323 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [ifF (w306 ! [i307, i308, i309, i310, i311, i312, i313, i314, i307, i308, 0, 0] <=. rscalar 0.0) 0 1]) ; w324 = rgather [1,1,1,1,1,1,2,2] w306 (\\[i315, i316, i317, i318, i319, i320, i321, i322] -> [i315, i316, i317, i318, i319, i320, i321, i322, i315, i316, 0, 0]) ; w333 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w323 * w324, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i325, i326, i327, i328, i329, i330, i331, i332] -> [ifF ((0 <=. i325 + i329 &&* 1 >. i325 + i329) &&* ((0 <=. i326 + i330 &&* 1 >. i326 + i330) &&* ((0 <=. 2 * i327 + i331 &&* 2 >. 2 * i327 + i331) &&* (0 <=. 2 * i328 + i332 &&* 2 >. 2 * i328 + i332)))) 0 1, i325, i326, i327, i328, i329, i330, i331, i332]) ; x338 = stoScalar (sscalar 2) * stoScalar (sscalar 1) ; t339 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w333 (\\[i334, i335, i336, i337] -> [i334, i335, i336, i337, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2) * i338)) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2))]))))) ; m340 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t339) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m343 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i341, i342] -> [ifF (m340 ! [i341, i342] <=. rscalar 0.0) 0 1]) ; t344 = rtranspose [1,0] (rreplicate 10 (m343 * m340)) in rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * t344) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m345 x1 -> let w252 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i238, i239, i240, i241, i242, i243, i244] -> [ifF ((0 <=. i238 + i241 &&* 1 >. i238 + i241) &&* ((0 <=. i242 &&* 1 >. i242) &&* ((0 <=. i239 + i243 &&* 4 >. i239 + i243) &&* (0 <=. i240 + i244 &&* 4 >. i240 + i244)))) 0 1])))) ; w254 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w252 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i245, i246] -> [i245 + i246]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i247, i248, i249, i250, i251] -> [ifF ((0 <=. i247 + i248 &&* 1 >. i247 + i248) &&* ((0 <=. i249 &&* 1 >. i249) &&* ((0 <=. i250 &&* 2 >. i250) &&* (0 <=. i251 &&* 2 >. i251)))) 0 1, i247, i248, i249, i250, i251]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w271 = rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i255, i256, i257, i258, i259, i260, i261, i262] -> [ifF (w254 ! [i255, i256, i257, i258, i259, i260, i261, i262, i255, i256, 0, 0] <=. rscalar 0.0) 0 1]) ; w281 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w271 * rgather [1,1,2,2,1,1,2,2] w254 (\\[i263, i264, i265, i266, i267, i268, i269, i270] -> [i263, i264, i265, i266, i267, i268, i269, i270, i263, i264, 0, 0]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i273, i274, i275, i276, i277, i278, i279, i280] -> [ifF ((0 <=. i273 + i277 &&* 1 >. i273 + i277) &&* ((0 <=. i274 + i278 &&* 1 >. i274 + i278) &&* ((0 <=. 2 * i275 + i279 &&* 4 >. 2 * i275 + i279) &&* (0 <=. 2 * i276 + i280 &&* 4 >. 2 * i276 + i280)))) 0 1, i273, i274, i275, i276, i277, i278, i279, i280])))))))) ; w304 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w281 (\\[i282, i283, i284, i285, i286, i287, i288] -> [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i290, i291, i292, i293, i294, i295, i296] -> [ifF ((0 <=. i290 + i293 &&* 1 >. i290 + i293) &&* ((0 <=. i294 &&* 1 >. i294) &&* ((0 <=. i291 + i295 &&* 2 >. i291 + i295) &&* (0 <=. i292 + i296 &&* 2 >. i292 + i296)))) 0 1, i290, i291, i292, i293, i294, i295, i296])))) ; w305 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i297, i298] -> [i297 + i298]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i299, i300, i301, i302, i303] -> [ifF ((0 <=. i299 + i300 &&* 1 >. i299 + i300) &&* ((0 <=. i301 &&* 1 >. i301) &&* ((0 <=. i302 &&* 2 >. i302) &&* (0 <=. i303 &&* 2 >. i303)))) 0 1, i299, i300, i301, i302, i303])))))) ; w306 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w304 * w305) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w323 = rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [ifF (w306 ! [i307, i308, i309, i310, i311, i312, i313, i314, i307, i308, 0, 0] <=. rscalar 0.0) 0 1]) ; w333 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w323 * rgather [1,1,1,1,1,1,2,2] w306 (\\[i315, i316, i317, i318, i319, i320, i321, i322] -> [i315, i316, i317, i318, i319, i320, i321, i322, i315, i316, 0, 0]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i325, i326, i327, i328, i329, i330, i331, i332] -> [ifF ((0 <=. i325 + i329 &&* 1 >. i325 + i329) &&* ((0 <=. i326 + i330 &&* 1 >. i326 + i330) &&* ((0 <=. 2 * i327 + i331 &&* 2 >. 2 * i327 + i331) &&* (0 <=. 2 * i328 + i332 &&* 2 >. 2 * i328 + i332)))) 0 1, i325, i326, i327, i328, i329, i330, i331, i332]) ; t339 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w333 (\\[i334, i335, i336, i337] -> [i334, i335, i336, i337, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2))])))) ; m340 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * t339) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) ; m343 = rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i341, i342] -> [ifF (m340 ! [i341, i342] <=. rscalar 0.0) 0 1]) ; m346 = m343 * rsum (rtranspose [1,2,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rtranspose [1,0] (rreplicate 1 m345)) ; u370 = rscatter [1,1,2,2] (w323 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] (tproject1 (tproject1 (tproject2 u1))) (\\[i617] -> [i617, 0]) * rgather [1] m346 (\\[i614] -> [i614, 0]))))))) (\\[i348, i349, i350, i351] -> [i348, i349, i350, i351, remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w333 ! [i348, i349, i350, i351, 0, 0]) (\\[i605] -> [remF (quotF i605 2) 2, remF i605 2]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w333 ! [i348, i349, i350, i351, 0, 0]) (\\[i606] -> [remF (quotF i606 2) 2, remF i606 2]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w333 ! [i348, i349, i350, i351, 0, 0]) (\\[i607] -> [remF (quotF i607 2) 2, remF i607 2]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rgather [4] (w333 ! [i348, i349, i350, i351, 0, 0]) (\\[i608] -> [remF (quotF i608 2) 2, remF i608 2]))))) (stoScalar (sscalar 2))])) (\\[i353, i354, i355, i356, i357, i358, i359, i360] -> [ifF ((0 <=. i353 + i357 &&* 1 >. i353 + i357) &&* ((0 <=. i354 + i358 &&* 1 >. i354 + i358) &&* ((0 <=. 2 * i355 + i359 &&* 2 >. 2 * i355 + i359) &&* (0 <=. 2 * i356 + i360 &&* 2 >. 2 * i356 + i360)))) 0 1, i353, i354, i355, i356, i357, i358, i359, i360]) ! [0]) (\\[i362, i363, i364, i365, i366, i367, i368, i369] -> [i362, i363, 0, 0]) ; u413 = rscatter [1,1,4,4] (w271 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w305 (\\[i589, i590, i591, i588] -> [i591, 0, i588, i589, i590]) * rgather [2,2,4,1] (u370 ! [0]) (\\[i594, i595, i596, i593] -> [i593, i594, i595])) (\\[i597, i598, i599, i600, i601, i602, i603, i604] -> [remF (quotF (i604 + 2 * i603 + 4 * i602 + 4 * i601 + 4 * i600 + 16 * i598 + 8 * i599) 8) 2, remF (quotF (i604 + 2 * i603 + 4 * i602 + 4 * i601 + 4 * i600 + 16 * i598 + 8 * i599) 4) 2, remF (i604 + 2 * i603 + 4 * i602 + 4 * i601 + 4 * i600 + 16 * i598 + 8 * i599) 4, i597]))) (\\[i380, i381, i382, i383, i384, i385, i386] -> [ifF ((0 <=. i380 + i383 &&* 1 >. i380 + i383) &&* ((0 <=. i384 &&* 1 >. i384) &&* ((0 <=. i381 + i385 &&* 2 >. i381 + i385) &&* (0 <=. i382 + i386 &&* 2 >. i382 + i386)))) 0 1, i380, i381, i382, i383, i384, i385, i386]) ! [0]) (\\[i388, i389, i390, i391, i392, i393, i394] -> [i388, i392, i389, i390, remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w281 ! [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390, 0, 0]) (\\[i576] -> [remF (quotF i576 2) 2, remF i576 2]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w281 ! [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390, 0, 0]) (\\[i577] -> [remF (quotF i577 2) 2, remF i577 2]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rgather [4] (w281 ! [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390, 0, 0]) (\\[i578] -> [remF (quotF i578 2) 2, remF i578 2]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rgather [4] (w281 ! [i388, i389, i390, i391, i392, i393, i394, i388, i392, i389, i390, 0, 0]) (\\[i579] -> [remF (quotF i579 2) 2, remF i579 2]))))) (stoScalar (sscalar 2))])) (\\[i396, i397, i398, i399, i400, i401, i402, i403] -> [ifF ((0 <=. i396 + i400 &&* 1 >. i396 + i400) &&* ((0 <=. i397 + i401 &&* 1 >. i397 + i401) &&* ((0 <=. 2 * i398 + i402 &&* 4 >. 2 * i398 + i402) &&* (0 <=. 2 * i399 + i403 &&* 4 >. 2 * i399 + i403)))) 0 1, i396, i397, i398, i399, i400, i401, i402, i403]) ! [0]) (\\[i405, i406, i407, i408, i409, i410, i411, i412] -> [i405, i406, 0, 0]) in tpair (tpair (tpair (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w252 (\\[i508, i505] -> [i508, i505, 0]) * rreplicate 4 (rgather [1,4,4] u413 (\\[i510] -> [i510, 0]))) (\\[i568, i569, i570, i571, i572, i573, i574, i575] -> [remF (i575 + 2 * i574 + 4 * i573 + 4 * i571 + 4 * i572) 4, i568, i569, i570]))))) (\\[i414, i415, i416, i417, i418] -> [ifF ((0 <=. i414 + i415 &&* 1 >. i414 + i415) &&* ((0 <=. i416 &&* 1 >. i416) &&* ((0 <=. i417 &&* 2 >. i417) &&* (0 <=. i418 &&* 2 >. i418)))) 0 1, i414, i415, i416, i417, i418]) ! [0]) (\\[i420, i421] -> [i420 + i421]), rsum (rsum (rsum (rtranspose [0,2,3,1] u413)))), tpair (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w304 (\\[i431, i428] -> [i431, i428, 0]) * rreplicate 4 (rgather [1,2,2] u370 (\\[i433] -> [i433, 0]))) (\\[i491, i492, i493, i494, i495, i496, i497, i498] -> [remF (i498 + 2 * i497 + 4 * i496 + 4 * i494 + 4 * i495) 4, i491, i492, i493]))))) (\\[i372, i373, i374, i375, i376] -> [ifF ((0 <=. i372 + i373 &&* 1 >. i372 + i373) &&* ((0 <=. i374 &&* 1 >. i374) &&* ((0 <=. i375 &&* 2 >. i375) &&* (0 <=. i376 &&* 2 >. i376)))) 0 1, i372, i373, i374, i375, i376]) ! [0]) (\\[i378, i379] -> [i378 + i379]), rsum (rsum (rsum (rtranspose [0,2,3,1] u370))))), tpair (tpair (rsum (rtranspose [2,1,0] t339 * rtranspose [2,1,0] (rreplicate 1 m346)), rsum (rtranspose [1,0] m346)), tpair (rsum (rtranspose [2,0,1] (rreplicate 10 (m343 * m340)) * rtranspose [2,1,0] (rreplicate 1 m345)), rsum (rtranspose [1,0] m345))))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let w254 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [7.0,0.0])) (\\[i238, i239, i240, i241, i242, i243, i244] -> [ifF ((0 <=. i238 + i241 &&* 1 >. i238 + i241) &&* ((0 <=. i242 &&* 1 >. i242) &&* ((0 <=. i239 + i243 &&* 4 >. i239 + i243) &&* (0 <=. i240 + i244 &&* 4 >. i240 + i244)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject1 (tproject1 u1))) (\\[i245, i246] -> [i245 + i246]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i247, i248, i249, i250, i251] -> [ifF ((0 <=. i247 + i248 &&* 1 >. i247 + i248) &&* ((0 <=. i249 &&* 1 >. i249) &&* ((0 <=. i250 &&* 2 >. i250) &&* (0 <=. i251 &&* 2 >. i251)))) 0 1, i247, i248, i249, i250, i251]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (tproject2 (tproject1 (tproject1 u1)))))))))))))) ; w281 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i255, i256, i257, i258, i259, i260, i261, i262] -> [ifF (w254 ! [i255, i256, i257, i258, i259, i260, i261, i262, i255, i256, 0, 0] <=. rscalar 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w254 (\\[i263, i264, i265, i266, i267, i268, i269, i270] -> [i263, i264, i265, i266, i267, i268, i269, i270, i263, i264, 0, 0]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i273, i274, i275, i276, i277, i278, i279, i280] -> [ifF ((0 <=. i273 + i277 &&* 1 >. i273 + i277) &&* ((0 <=. i274 + i278 &&* 1 >. i274 + i278) &&* ((0 <=. 2 * i275 + i279 &&* 4 >. 2 * i275 + i279) &&* (0 <=. 2 * i276 + i280 &&* 4 >. 2 * i276 + i280)))) 0 1, i273, i274, i275, i276, i277, i278, i279, i280])))))))) ; w306 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w281 (\\[i282, i283, i284, i285, i286, i287, i288] -> [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w281 ! [i282, i283, i284, i285, i286, i287, i288, i282, i286, i283, i284]))))) (stoScalar (sscalar 2))]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))))])) (\\[i290, i291, i292, i293, i294, i295, i296] -> [ifF ((0 <=. i290 + i293 &&* 1 >. i290 + i293) &&* ((0 <=. i294 &&* 1 >. i294) &&* ((0 <=. i291 + i295 &&* 2 >. i291 + i295) &&* (0 <=. i292 + i296 &&* 2 >. i292 + i296)))) 0 1, i290, i291, i292, i293, i294, i295, i296])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] (tproject1 (tproject2 (tproject1 u1))) (\\[i297, i298] -> [i297 + i298]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0)))))])) (\\[i299, i300, i301, i302, i303] -> [ifF ((0 <=. i299 + i300 &&* 1 >. i299 + i300) &&* ((0 <=. i301 &&* 1 >. i301) &&* ((0 <=. i302 &&* 2 >. i302) &&* (0 <=. i303 &&* 2 >. i303)))) 0 1, i299, i300, i301, i302, i303]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (tproject2 (tproject2 (tproject1 u1)))))))))))))) ; w333 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [ifF (w306 ! [i307, i308, i309, i310, i311, i312, i313, i314, i307, i308, 0, 0] <=. rscalar 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w306 (\\[i315, i316, i317, i318, i319, i320, i321, i322] -> [i315, i316, i317, i318, i319, i320, i321, i322, i315, i316, 0, 0]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rscalar 0.0))))))))])) (\\[i325, i326, i327, i328, i329, i330, i331, i332] -> [ifF ((0 <=. i325 + i329 &&* 1 >. i325 + i329) &&* ((0 <=. i326 + i330 &&* 1 >. i326 + i330) &&* ((0 <=. 2 * i327 + i331 &&* 2 >. 2 * i327 + i331) &&* (0 <=. 2 * i328 + i332 &&* 2 >. 2 * i328 + i332)))) 0 1, i325, i326, i327, i328, i329, i330, i331, i332]) ; m340 = rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject1 (tproject2 u1)))) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w333 (\\[i334, i335, i336, i337] -> [i334, i335, i336, i337, remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2) * (stoScalar (sscalar 2) * stoScalar (sscalar 1)))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2) * stoScalar (sscalar 2))) (stoScalar (sscalar 1)), remF (quotF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2))) (stoScalar (sscalar 2)), remF (stoScalar (sfromR (rmaxIndex (rreshape [4] (w333 ! [i334, i335, i336, i337]))))) (stoScalar (sscalar 2))]))))) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject1 (tproject2 u1)))) in rsum (rtranspose [2,1,0] (rreplicate 1 (tproject1 (tproject2 (tproject2 u1)))) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (tconcrete (FTKR [2] FTKScalar) (rfromListLinear [2] [0.0,1.0])) (\\[i341, i342] -> [ifF (m340 ! [i341, i342] <=. rscalar 0.0) 0 1]) * m340))) + rtranspose [1,0] (rreplicate 1 (tproject2 (tproject2 (tproject2 u1))))"
