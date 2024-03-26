{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | Tests of "MnistCnnRanked2" neural networks using a few different
-- optimization pipelines.
module TestMnistCNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (SomeNat (..), someNatVal)
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.TensorAst
import HordeAd.External.OptimizerTools

import EqEpsilon

import qualified MnistCnnRanked2
import           MnistData

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsCNNA
            , tensorADValMnistTestsCNNI
            , tensorADValMnistTestsCNNO
            , tensorMnistTestsPP
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseCNNA
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNA prefix epochs maxBatches kh kw c_out n_hidden
                  miniBatchSize totalBatchSize expected =
  let valsInit :: MnistCnnRanked2.ADCnnMnistParameters ranked r
      valsInit =
        case ( someNatVal $ toInteger kh
             , someNatVal $ toInteger kw
             , someNatVal $ toInteger c_out
             , someNatVal $ toInteger n_hidden ) of
          ( Just (SomeNat @kh _), Just (SomeNat @kw _)
           ,Just (SomeNat @c_out _), Just (SomeNat @n_hidden _) ) ->
            forgetShape $ fst
            $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                             (Flip OS.Array) SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)
                0.4 (mkStdGen 44)
          _ -> error "impossible someNatVal error"
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show kh, show kw, show c_out, show n_hidden
                        , show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
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
           runBatch :: (HVector (Flip OR.Array), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal (Flip OR.Array))
                   -> ADVal ranked r 0
                 f (glyphR, labelR) adinputs =
                   MnistCnnRanked2.convMnistLossFusedR
                     miniBatchSize (rconst glyphR, rconst labelR)
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
             unless (n_hidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
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
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseCNNI prefix epochs maxBatches kh kw c_out n_hidden
                  miniBatchSize totalBatchSize expected =
  let valsInit :: MnistCnnRanked2.ADCnnMnistParameters ranked r
      valsInit =
        case ( someNatVal $ toInteger kh
             , someNatVal $ toInteger kw
             , someNatVal $ toInteger c_out
             , someNatVal $ toInteger n_hidden ) of
          ( Just (SomeNat @kh _), Just (SomeNat @kw _)
           ,Just (SomeNat @c_out _), Just (SomeNat @n_hidden _) ) ->
            forgetShape $ fst
            $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                             (Flip OS.Array) SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)
                0.4 (mkStdGen 44)
          _ -> error "impossible someNatVal error"
      hVectorInit = toHVectorOf valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show kh, show kw, show c_out, show n_hidden
                        , show miniBatchSize
                        , show (V.length hVectorInit)
                        , show (sizeHVector hVectorInit) ]
      ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
      ftest = MnistCnnRanked2.convMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, hVectorPrimal, vars, _)
         <- funToAstRevIO (voidFromHVector hVectorInit)
       let testDataR = packBatchR testData
       (varGlyph, _, astGlyph) <-
         funToAstIOR
           (miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, _, astLabel) <-
         funToAstIOR (miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistCnnRanked2.convMnistLossFusedR
                   miniBatchSize (astGlyph, astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (unRawHVector hVectorPrimal))
           runBatch :: (HVector (Flip OR.Array), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal (Flip OR.Array))
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvD EM.empty
                             $ zip vars $ V.toList varInputs
                       envMnist = extendEnvR varGlyph (rconst glyph)
                                  $ extendEnvR varLabel (rconst label) env
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
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
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
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r, GoodScalar r, Random r
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
               (Flip OS.Array) SizeMnistHeight SizeMnistWidth
               kh kw c_out n_hidden r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        valsInit :: MnistCnnRanked2.ADCnnMnistParameters ranked r
        valsInit = forgetShape valsInitShaped
        hVectorInit = toHVectorOf valsInit
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show kh, show kw, show c_out, show n_hidden
                          , show miniBatchSize
                          , show (V.length hVectorInit)
                          , show (sizeHVector hVectorInit) ]
        ftest :: Int -> MnistDataBatchR r -> HVector (Flip OR.Array) -> r
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
       (varGlyph, varGlyphD, astGlyph) <-
         funToAstIOR
           (miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, varLabelD, astLabel) <-
         funToAstIOR (miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let envInit = extendEnvR varGlyph (rconstant $ AstRaw astGlyph)
                     $ extendEnvR varLabel (rconstant $ AstRaw astLabel)
                       EM.empty
           f = MnistCnnRanked2.convMnistLossFusedR
                 miniBatchSize (astGlyph, astLabel)
           (((varDtAgain, vars1Again), gradientRaw, primal), _) =
             revProduceArtifactH False f envInit valsInit
                                 (voidFromHVector hVectorInit)
           gradient = simplifyAstHVector6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistDataBatchR r] -> (HVector (Flip OR.Array), StateAdam)
              -> (HVector (Flip OR.Array), StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconst glyph
                 labelD = DynamicRanked $ rconst label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifact (vars, gradient, primal)
                                         parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientHVector)
           runBatch :: (HVector (Flip OR.Array), StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector (Flip OR.Array), StateAdam)
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
       let runEpoch :: Int -> (HVector (Flip OR.Array), StateAdam) -> IO (HVector (Flip OR.Array))
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
      blackGlyph :: AstRanked PrimalSpan Double 4
      blackGlyph = AstReplicate batch_size
                   $ AstReplicate 1
                   $ AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI 7
      valsInit :: MnistCnnRanked2.ADCnnMnistParameters (Flip OR.Array) Double
      valsInit =
        forgetShape $ fst
        $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                         (Flip OS.Array) 4 4  -- see sizeMnistWidthI, etc.
                         1 1 1 1 Double)
                     0.4 (mkStdGen 44)
      afcnn2T :: MnistCnnRanked2.ADCnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistCnnRanked2.convMnistTwoR sizeMnistHeightI sizeMnistWidthI
                                              batch_size blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInit
  printGradient6Pretty renames artifactRev
    @?= "\\m394 u1 v2 u3 v4 m5 v6 m7 v8 -> let w290 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (fromList [2] [7.0,0.0])) (\\[i276, i277, i278, i279, i280, i281, i282] -> [ifF ((0 <=. i276 + i279 &&* 1 >. i276 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i277 + i281 &&* 4 >. i277 + i281) &&* (0 <=. i278 + i282 &&* 4 >. i278 + i282)))) 0 1])))) ; w291 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i283, i284] -> [i283 + i284]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i285, i286, i287, i288, i289] -> [ifF ((0 <=. i285 + i286 &&* 1 >. i285 + i286) &&* ((0 <=. i287 &&* 1 >. i287) &&* ((0 <=. i288 &&* 2 >. i288) &&* (0 <=. i289 &&* 2 >. i289)))) 0 1, i285, i286, i287, i288, i289])))))) ; w292 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w290 * w291) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2))))))))))) ; w315 = rgather [1,1,2,2,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303, i304, i305, i306] -> [ifF (w292 ! [i299, i300, i301, i302, i303, i304, i305, i306, let w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w293 ! [i299, i300, i301, i302, i303, i304, i305, i306], let w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w294 ! [i299, i300, i301, i302, i303, i304, i305, i306], let v295 = rconst (fromList [2] [0,1]) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v295)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w296 ! [i299, i300, i301, i302, i303, i304, i305, i306], let v297 = rconst (fromList [2] [0,1]) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v297)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w298 ! [i299, i300, i301, i302, i303, i304, i305, i306]] <=. 0.0) 0 1]) ; w316 = rgather [1,1,2,2,1,1,2,2] w292 (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [i307, i308, i309, i310, i311, i312, i313, i314, let w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w293 ! [i307, i308, i309, i310, i311, i312, i313, i314], let w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w294 ! [i307, i308, i309, i310, i311, i312, i313, i314], let v295 = rconst (fromList [2] [0,1]) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v295)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w296 ! [i307, i308, i309, i310, i311, i312, i313, i314], let v297 = rconst (fromList [2] [0,1]) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v297)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w298 ! [i307, i308, i309, i310, i311, i312, i313, i314]]) ; w325 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [w315 * w316, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i317, i318, i319, i320, i321, i322, i323, i324] -> [ifF ((0 <=. i317 + i321 &&* 1 >. i317 + i321) &&* ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. 2 * i319 + i323 &&* 4 >. 2 * i319 + i323) &&* (0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324)))) 0 1, i317, i318, i319, i320, i321, i322, i323, i324])))))))) ; w350 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w325 (\\[i329, i330, i331, i332, i333, i334, i335] -> [i329, i330, i331, i332, i333, i334, i335, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i329, i330, i331, i332, i333, i334, i335], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i329, i330, i331, i332, i333, i334, i335], 0, 0, rem (quot (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i329, i330, i331, i332, i333, i334, i335], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2) 2, rem (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i329, i330, i331, i332, i333, i334, i335], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i336, i337, i338, i339, i340, i341, i342] -> [ifF ((0 <=. i336 + i339 &&* 1 >. i336 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i337 + i341 &&* 2 >. i337 + i341) &&* (0 <=. i338 + i342 &&* 2 >. i338 + i342)))) 0 1, i336, i337, i338, i339, i340, i341, i342])))) ; w351 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i343, i344] -> [i343 + i344]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i345, i346, i347, i348, i349] -> [ifF ((0 <=. i345 + i346 &&* 1 >. i345 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i348 &&* 2 >. i348) &&* (0 <=. i349 &&* 2 >. i349)))) 0 1, i345, i346, i347, i348, i349])))))) ; w352 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w350 * w351) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4))))))))))) ; w373 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [ifF (w352 ! [i357, i358, i359, i360, i361, i362, i363, i364, let w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w353 ! [i357, i358, i359, i360, i361, i362, i363, i364], let w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w354 ! [i357, i358, i359, i360, i361, i362, i363, i364], let w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w355 ! [i357, i358, i359, i360, i361, i362, i363, i364], let w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w356 ! [i357, i358, i359, i360, i361, i362, i363, i364]] <=. 0.0) 0 1]) ; w374 = rgather [1,1,1,1,1,1,2,2] w352 (\\[i365, i366, i367, i368, i369, i370, i371, i372] -> [i365, i366, i367, i368, i369, i370, i371, i372, let w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w353 ! [i365, i366, i367, i368, i369, i370, i371, i372], let w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w354 ! [i365, i366, i367, i368, i369, i370, i371, i372], let w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w355 ! [i365, i366, i367, i368, i369, i370, i371, i372], let w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w356 ! [i365, i366, i367, i368, i369, i370, i371, i372]]) ; w383 = rgather [1,1,1,1,1,1,2,2] (rfromList [w373 * w374, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i375, i376, i377, i378, i379, i380, i381, i382] -> [ifF ((0 <=. i375 + i379 &&* 1 >. i375 + i379) &&* ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. 2 * i377 + i381 &&* 2 >. 2 * i377 + i381) &&* (0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382)))) 0 1, i375, i376, i377, i378, i379, i380, i381, i382]) ; t388 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w383 (\\[i384, i385, i386, i387] -> [i384, i385, i386, i387, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2) 2, rem (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2]))))) ; m389 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t388) + rtranspose [1,0] (rreplicate 1 v6) ; m392 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i390, i391] -> [ifF (m389 ! [i390, i391] <=. 0.0) 0 1]) ; t393 = rtranspose [1,0] (rreplicate 10 (m392 * m389)) ; m395 = m392 * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 m7) * rreplicate 1 m394)) ; w408 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rtranspose [1,0] (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 m5) * rreplicate 1 m395))))) (\\[i396, i397, i398, i399] -> [i396, i397, i398, i399, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w383 ! [i396, i397, i398, i399]))) 2) 2, rem (rmaxIndex (rreshape [4] (w383 ! [i396, i397, i398, i399]))) 2])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifF ((0 <=. i400 + i404 &&* 1 >. i400 + i404) &&* ((0 <=. i401 + i405 &&* 1 >. i401 + i405) &&* ((0 <=. 2 * i402 + i406 &&* 2 >. 2 * i402 + i406) &&* (0 <=. 2 * i403 + i407 &&* 2 >. 2 * i403 + i407)))) 0 1, i400, i401, i402, i403, i404, i405, i406, i407]) ; u417 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w373 * w408 ! [0]) (\\[i409, i410, i411, i412, i413, i414, i415, i416] -> [i409, i410, i411, i412, i413, i414, i415, i416, let w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w353 ! [i409, i410, i411, i412, i413, i414, i415, i416], let w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w354 ! [i409, i410, i411, i412, i413, i414, i415, i416], let w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w355 ! [i409, i410, i411, i412, i413, i414, i415, i416], let w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w356 ! [i409, i410, i411, i412, i413, i414, i415, i416]]))))))))) ; w423 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w350 * rreplicate 4 u417)))))) (\\[i418, i419, i420, i421, i422] -> [ifF ((0 <=. i418 + i419 &&* 1 >. i418 + i419) &&* ((0 <=. i420 &&* 1 >. i420) &&* ((0 <=. i421 &&* 2 >. i421) &&* (0 <=. i422 &&* 2 >. i422)))) 0 1, i418, i419, i420, i421, i422]) ; w433 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] (w351 * rreplicate 4 u417)))) (\\[i426, i427, i428, i429, i430, i431, i432] -> [ifF ((0 <=. i426 + i429 &&* 1 >. i426 + i429) &&* ((0 <=. i430 &&* 1 >. i430) &&* ((0 <=. i427 + i431 &&* 2 >. i427 + i431) &&* (0 <=. i428 + i432 &&* 2 >. i428 + i432)))) 0 1, i426, i427, i428, i429, i430, i431, i432]) ; w449 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w433 ! [0]) (\\[i434, i435, i436, i437, i438, i439, i440] -> [i434, i435, i436, i437, i438, i439, i440, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i434, i435, i436, i437, i438, i439, i440], i438, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i434, i435, i436, i437, i438, i439, i440], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i434, i435, i436, i437, i438, i439, i440], 0, 0, rem (quot (rmaxIndex (rreshape [4] (w325 ! [i434, i435, i436, i437, i438, i439, i440, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i434, i435, i436, i437, i438, i439, i440], i438, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i434, i435, i436, i437, i438, i439, i440], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i434, i435, i436, i437, i438, i439, i440]]))) 2) 2, rem (rmaxIndex (rreshape [4] (w325 ! [i434, i435, i436, i437, i438, i439, i440, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i434, i435, i436, i437, i438, i439, i440], i438, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i434, i435, i436, i437, i438, i439, i440], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i434, i435, i436, i437, i438, i439, i440]]))) 2]))))))))) (\\[i441, i442, i443, i444, i445, i446, i447, i448] -> [ifF ((0 <=. i441 + i445 &&* 1 >. i441 + i445) &&* ((0 <=. i442 + i446 &&* 1 >. i442 + i446) &&* ((0 <=. 2 * i443 + i447 &&* 4 >. 2 * i443 + i447) &&* (0 <=. 2 * i444 + i448 &&* 4 >. 2 * i444 + i448)))) 0 1, i441, i442, i443, i444, i445, i446, i447, i448]) ; u458 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w315 * w449 ! [0]) (\\[i450, i451, i452, i453, i454, i455, i456, i457] -> [i450, i451, i452, i453, i454, i455, i456, i457, let w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w293 ! [i450, i451, i452, i453, i454, i455, i456, i457], let w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w294 ! [i450, i451, i452, i453, i454, i455, i456, i457], let v295 = rconst (fromList [2] [0,1]) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v295)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w296 ! [i450, i451, i452, i453, i454, i455, i456, i457], let v297 = rconst (fromList [2] [0,1]) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v297)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w298 ! [i450, i451, i452, i453, i454, i455, i456, i457]]))))))))) ; w464 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w290 * rreplicate 4 u458)))))) (\\[i459, i460, i461, i462, i463] -> [ifF ((0 <=. i459 + i460 &&* 1 >. i459 + i460) &&* ((0 <=. i461 &&* 1 >. i461) &&* ((0 <=. i462 &&* 2 >. i462) &&* (0 <=. i463 &&* 2 >. i463)))) 0 1, i459, i460, i461, i462, i463]) in [rscatter [1,1,2,2] (w464 ! [0]) (\\[i465, i466] -> [i465 + i466]), rsum (rsum (rsum (rtranspose [0,2,3,1] u458))), rscatter [1,1,2,2] (w423 ! [0]) (\\[i424, i425] -> [i424 + i425]), rsum (rsum (rsum (rtranspose [0,2,3,1] u417))), rsum (rtranspose [2,1,0] (t388 * rreplicate 1 m395)), rsum (rtranspose [1,0] m395), rsum (rtranspose [2,1,0] (t393 * rreplicate 1 m394)), rsum (rtranspose [1,0] m394)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w290 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (fromList [2] [7.0,0.0])) (\\[i276, i277, i278, i279, i280, i281, i282] -> [ifF ((0 <=. i276 + i279 &&* 1 >. i276 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i277 + i281 &&* 4 >. i277 + i281) &&* (0 <=. i278 + i282 &&* 4 >. i278 + i282)))) 0 1])))) ; w291 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i283, i284] -> [i283 + i284]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i285, i286, i287, i288, i289] -> [ifF ((0 <=. i285 + i286 &&* 1 >. i285 + i286) &&* ((0 <=. i287 &&* 1 >. i287) &&* ((0 <=. i288 &&* 2 >. i288) &&* (0 <=. i289 &&* 2 >. i289)))) 0 1, i285, i286, i287, i288, i289])))))) ; w292 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w290 * w291) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2))))))))))) ; w315 = rgather [1,1,2,2,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303, i304, i305, i306] -> [ifF (w292 ! [i299, i300, i301, i302, i303, i304, i305, i306, let w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w293 ! [i299, i300, i301, i302, i303, i304, i305, i306], let w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w294 ! [i299, i300, i301, i302, i303, i304, i305, i306], let v295 = rconst (fromList [2] [0,1]) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v295)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w296 ! [i299, i300, i301, i302, i303, i304, i305, i306], let v297 = rconst (fromList [2] [0,1]) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v297)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w298 ! [i299, i300, i301, i302, i303, i304, i305, i306]] <=. 0.0) 0 1]) ; w316 = rgather [1,1,2,2,1,1,2,2] w292 (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [i307, i308, i309, i310, i311, i312, i313, i314, let w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w293 ! [i307, i308, i309, i310, i311, i312, i313, i314], let w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w294 ! [i307, i308, i309, i310, i311, i312, i313, i314], let v295 = rconst (fromList [2] [0,1]) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v295)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w296 ! [i307, i308, i309, i310, i311, i312, i313, i314], let v297 = rconst (fromList [2] [0,1]) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v297)) + rreplicate 2 (rconst (fromList [2] [0,1]))))))))) in w298 ! [i307, i308, i309, i310, i311, i312, i313, i314]]) ; w325 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [w315 * w316, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i317, i318, i319, i320, i321, i322, i323, i324] -> [ifF ((0 <=. i317 + i321 &&* 1 >. i317 + i321) &&* ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. 2 * i319 + i323 &&* 4 >. 2 * i319 + i323) &&* (0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324)))) 0 1, i317, i318, i319, i320, i321, i322, i323, i324])))))))) ; w350 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w325 (\\[i329, i330, i331, i332, i333, i334, i335] -> [i329, i330, i331, i332, i333, i334, i335, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i329, i330, i331, i332, i333, i334, i335], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i329, i330, i331, i332, i333, i334, i335], 0, 0, rem (quot (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i329, i330, i331, i332, i333, i334, i335], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2) 2, rem (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, let w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, let w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w327 ! [i329, i330, i331, i332, i333, i334, i335], let w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i336, i337, i338, i339, i340, i341, i342] -> [ifF ((0 <=. i336 + i339 &&* 1 >. i336 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i337 + i341 &&* 2 >. i337 + i341) &&* (0 <=. i338 + i342 &&* 2 >. i338 + i342)))) 0 1, i336, i337, i338, i339, i340, i341, i342])))) ; w351 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i343, i344] -> [i343 + i344]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i345, i346, i347, i348, i349] -> [ifF ((0 <=. i345 + i346 &&* 1 >. i345 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i348 &&* 2 >. i348) &&* (0 <=. i349 &&* 2 >. i349)))) 0 1, i345, i346, i347, i348, i349])))))) ; w352 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w350 * w351) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4))))))))))) ; w373 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [ifF (w352 ! [i357, i358, i359, i360, i361, i362, i363, i364, let w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w353 ! [i357, i358, i359, i360, i361, i362, i363, i364], let w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w354 ! [i357, i358, i359, i360, i361, i362, i363, i364], let w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w355 ! [i357, i358, i359, i360, i361, i362, i363, i364], let w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w356 ! [i357, i358, i359, i360, i361, i362, i363, i364]] <=. 0.0) 0 1]) ; w374 = rgather [1,1,1,1,1,1,2,2] w352 (\\[i365, i366, i367, i368, i369, i370, i371, i372] -> [i365, i366, i367, i368, i369, i370, i371, i372, let w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w353 ! [i365, i366, i367, i368, i369, i370, i371, i372], let w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))))) in w354 ! [i365, i366, i367, i368, i369, i370, i371, i372], let w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w355 ! [i365, i366, i367, i368, i369, i370, i371, i372], let w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1]))))))))) in w356 ! [i365, i366, i367, i368, i369, i370, i371, i372]]) ; w383 = rgather [1,1,1,1,1,1,2,2] (rfromList [w373 * w374, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i375, i376, i377, i378, i379, i380, i381, i382] -> [ifF ((0 <=. i375 + i379 &&* 1 >. i375 + i379) &&* ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. 2 * i377 + i381 &&* 2 >. 2 * i377 + i381) &&* (0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382)))) 0 1, i375, i376, i377, i378, i379, i380, i381, i382]) ; t388 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w383 (\\[i384, i385, i386, i387] -> [i384, i385, i386, i387, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2) 2, rem (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2]))))) ; m389 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t388) + rtranspose [1,0] (rreplicate 1 v6) ; m392 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i390, i391] -> [ifF (m389 ! [i390, i391] <=. 0.0) 0 1]) ; t393 = rtranspose [1,0] (rreplicate 10 (m392 * m389)) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * t393) + rtranspose [1,0] (rreplicate 1 v8)]"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m394 u1 v2 u3 v4 m5 v6 m7 v8 -> let w290 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (fromList [2] [7.0,0.0])) (\\[i276, i277, i278, i279, i280, i281, i282] -> [ifF ((0 <=. i276 + i279 &&* 1 >. i276 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i277 + i281 &&* 4 >. i277 + i281) &&* (0 <=. i278 + i282 &&* 4 >. i278 + i282)))) 0 1])))) ; w292 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w290 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i283, i284] -> [i283 + i284]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i285, i286, i287, i288, i289] -> [ifF ((0 <=. i285 + i286 &&* 1 >. i285 + i286) &&* ((0 <=. i287 &&* 1 >. i287) &&* ((0 <=. i288 &&* 2 >. i288) &&* (0 <=. i289 &&* 2 >. i289)))) 0 1, i285, i286, i287, i288, i289]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2))))))))))) ; w315 = rgather [1,1,2,2,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303, i304, i305, i306] -> [ifF (w292 ! [i299, i300, i301, i302, i303, i304, i305, i306, rconst (fromList [1] [0]) ! [i299] + rconst (fromList [1] [0]) ! [i303], rconst (fromList [1] [0]) ! [i300] + rconst (fromList [1] [0]) ! [i304], 2 * rconst (fromList [2] [0,1]) ! [i301] + rconst (fromList [2] [0,1]) ! [i305], 2 * rconst (fromList [2] [0,1]) ! [i302] + rconst (fromList [2] [0,1]) ! [i306]] <=. 0.0) 0 1]) ; w325 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [w315 * rgather [1,1,2,2,1,1,2,2] w292 (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [i307, i308, i309, i310, i311, i312, i313, i314, rconst (fromList [1] [0]) ! [i307] + rconst (fromList [1] [0]) ! [i311], rconst (fromList [1] [0]) ! [i308] + rconst (fromList [1] [0]) ! [i312], 2 * rconst (fromList [2] [0,1]) ! [i309] + rconst (fromList [2] [0,1]) ! [i313], 2 * rconst (fromList [2] [0,1]) ! [i310] + rconst (fromList [2] [0,1]) ! [i314]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i317, i318, i319, i320, i321, i322, i323, i324] -> [ifF ((0 <=. i317 + i321 &&* 1 >. i317 + i321) &&* ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. 2 * i319 + i323 &&* 4 >. 2 * i319 + i323) &&* (0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324)))) 0 1, i317, i318, i319, i320, i321, i322, i323, i324])))))))) ; w350 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w325 (\\[i329, i330, i331, i332, i333, i334, i335] -> [i329, i330, i331, i332, i333, i334, i335, rconst (fromList [1] [0]) ! [i329] + rconst (fromList [1] [0]) ! [i332], i333, rconst (fromList [2] [0,1]) ! [i330] + rconst (fromList [2] [0,1]) ! [i334], rconst (fromList [2] [0,1]) ! [i331] + rconst (fromList [2] [0,1]) ! [i335], 0, 0, rem (quot (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, rconst (fromList [1] [0]) ! [i329] + rconst (fromList [1] [0]) ! [i332], i333, rconst (fromList [2] [0,1]) ! [i330] + rconst (fromList [2] [0,1]) ! [i334], rconst (fromList [2] [0,1]) ! [i331] + rconst (fromList [2] [0,1]) ! [i335]]))) 2) 2, rem (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, rconst (fromList [1] [0]) ! [i329] + rconst (fromList [1] [0]) ! [i332], i333, rconst (fromList [2] [0,1]) ! [i330] + rconst (fromList [2] [0,1]) ! [i334], rconst (fromList [2] [0,1]) ! [i331] + rconst (fromList [2] [0,1]) ! [i335]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i336, i337, i338, i339, i340, i341, i342] -> [ifF ((0 <=. i336 + i339 &&* 1 >. i336 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i337 + i341 &&* 2 >. i337 + i341) &&* (0 <=. i338 + i342 &&* 2 >. i338 + i342)))) 0 1, i336, i337, i338, i339, i340, i341, i342])))) ; w351 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i343, i344] -> [i343 + i344]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i345, i346, i347, i348, i349] -> [ifF ((0 <=. i345 + i346 &&* 1 >. i345 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i348 &&* 2 >. i348) &&* (0 <=. i349 &&* 2 >. i349)))) 0 1, i345, i346, i347, i348, i349])))))) ; w352 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w350 * w351) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4))))))))))) ; w373 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [ifF (w352 ! [i357, i358, i359, i360, i361, i362, i363, i364, rconst (fromList [1] [0]) ! [i357] + rconst (fromList [1] [0]) ! [i361], rconst (fromList [1] [0]) ! [i358] + rconst (fromList [1] [0]) ! [i362], 2 * rconst (fromList [1] [0]) ! [i359] + rconst (fromList [2] [0,1]) ! [i363], 2 * rconst (fromList [1] [0]) ! [i360] + rconst (fromList [2] [0,1]) ! [i364]] <=. 0.0) 0 1]) ; w383 = rgather [1,1,1,1,1,1,2,2] (rfromList [w373 * rgather [1,1,1,1,1,1,2,2] w352 (\\[i365, i366, i367, i368, i369, i370, i371, i372] -> [i365, i366, i367, i368, i369, i370, i371, i372, rconst (fromList [1] [0]) ! [i365] + rconst (fromList [1] [0]) ! [i369], rconst (fromList [1] [0]) ! [i366] + rconst (fromList [1] [0]) ! [i370], 2 * rconst (fromList [1] [0]) ! [i367] + rconst (fromList [2] [0,1]) ! [i371], 2 * rconst (fromList [1] [0]) ! [i368] + rconst (fromList [2] [0,1]) ! [i372]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i375, i376, i377, i378, i379, i380, i381, i382] -> [ifF ((0 <=. i375 + i379 &&* 1 >. i375 + i379) &&* ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. 2 * i377 + i381 &&* 2 >. 2 * i377 + i381) &&* (0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382)))) 0 1, i375, i376, i377, i378, i379, i380, i381, i382]) ; t388 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w383 (\\[i384, i385, i386, i387] -> [i384, i385, i386, i387, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2) 2, rem (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2])))) ; m389 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t388) + rtranspose [1,0] (rreplicate 1 v6) ; m392 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i390, i391] -> [ifF (m389 ! [i390, i391] <=. 0.0) 0 1]) ; m395 = m392 * rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m394)) ; u417 = rscatter [1,1,2,2] (w373 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] m5 (\\[i658] -> [i658, 0]) * rgather [1] m395 (\\[i655] -> [i655, 0]))))))) (\\[i396, i397, i398, i399] -> [i396, i397, i398, i399, 0, 0, rem (quot (rmaxIndex (rgather [4] (w383 ! [i396, i397, i398, i399, 0, 0]) (\\[i648] -> [rem (quot i648 2) 2, rem i648 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w383 ! [i396, i397, i398, i399, 0, 0]) (\\[i649] -> [rem (quot i649 2) 2, rem i649 2]))) 2])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifF ((0 <=. i400 + i404 &&* 1 >. i400 + i404) &&* ((0 <=. i401 + i405 &&* 1 >. i401 + i405) &&* ((0 <=. 2 * i402 + i406 &&* 2 >. 2 * i402 + i406) &&* (0 <=. 2 * i403 + i407 &&* 2 >. 2 * i403 + i407)))) 0 1, i400, i401, i402, i403, i404, i405, i406, i407]) ! [0]) (\\[i409, i410, i411, i412, i413, i414, i415, i416] -> [rconst (fromList [1] [0]) ! [i409] + rconst (fromList [1] [0]) ! [i413], rconst (fromList [1] [0]) ! [i410] + rconst (fromList [1] [0]) ! [i414], 2 * rconst (fromList [1] [0]) ! [i411] + rconst (fromList [2] [0,1]) ! [i415], 2 * rconst (fromList [1] [0]) ! [i412] + rconst (fromList [2] [0,1]) ! [i416]]) ; u458 = rscatter [1,1,4,4] (w315 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w351 (\\[i632, i633, i634, i631] -> [i634, 0, i631, i632, i633]) * rgather [2,2,4,1] (u417 ! [0]) (\\[i637, i638, i639, i636] -> [i636, i637, i638])) (\\[i640, i641, i642, i643, i644, i645, i646, i647] -> [rem (quot (i647 + 2 * i646 + 4 * i645 + 4 * i644 + 4 * i643 + 16 * i641 + 8 * i642) 8) 2, rem (quot (i647 + 2 * i646 + 4 * i645 + 4 * i644 + 4 * i643 + 16 * i641 + 8 * i642) 4) 2, rem (i647 + 2 * i646 + 4 * i645 + 4 * i644 + 4 * i643 + 16 * i641 + 8 * i642) 4, i640]))) (\\[i426, i427, i428, i429, i430, i431, i432] -> [ifF ((0 <=. i426 + i429 &&* 1 >. i426 + i429) &&* ((0 <=. i430 &&* 1 >. i430) &&* ((0 <=. i427 + i431 &&* 2 >. i427 + i431) &&* (0 <=. i428 + i432 &&* 2 >. i428 + i432)))) 0 1, i426, i427, i428, i429, i430, i431, i432]) ! [0]) (\\[i434, i435, i436, i437, i438, i439, i440] -> [rconst (fromList [1] [0]) ! [i434] + rconst (fromList [1] [0]) ! [i437], i438, rconst (fromList [2] [0,1]) ! [i435] + rconst (fromList [2] [0,1]) ! [i439], rconst (fromList [2] [0,1]) ! [i436] + rconst (fromList [2] [0,1]) ! [i440], 0, 0, rem (quot (rmaxIndex (rgather [4] (w325 ! [i434, i435, i436, i437, i438, i439, i440, rconst (fromList [1] [0]) ! [i434] + rconst (fromList [1] [0]) ! [i437], i438, rconst (fromList [2] [0,1]) ! [i435] + rconst (fromList [2] [0,1]) ! [i439], rconst (fromList [2] [0,1]) ! [i436] + rconst (fromList [2] [0,1]) ! [i440], 0, 0]) (\\[i621] -> [rem (quot i621 2) 2, rem i621 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w325 ! [i434, i435, i436, i437, i438, i439, i440, rconst (fromList [1] [0]) ! [i434] + rconst (fromList [1] [0]) ! [i437], i438, rconst (fromList [2] [0,1]) ! [i435] + rconst (fromList [2] [0,1]) ! [i439], rconst (fromList [2] [0,1]) ! [i436] + rconst (fromList [2] [0,1]) ! [i440], 0, 0]) (\\[i622] -> [rem (quot i622 2) 2, rem i622 2]))) 2])) (\\[i441, i442, i443, i444, i445, i446, i447, i448] -> [ifF ((0 <=. i441 + i445 &&* 1 >. i441 + i445) &&* ((0 <=. i442 + i446 &&* 1 >. i442 + i446) &&* ((0 <=. 2 * i443 + i447 &&* 4 >. 2 * i443 + i447) &&* (0 <=. 2 * i444 + i448 &&* 4 >. 2 * i444 + i448)))) 0 1, i441, i442, i443, i444, i445, i446, i447, i448]) ! [0]) (\\[i450, i451, i452, i453, i454, i455, i456, i457] -> [rconst (fromList [1] [0]) ! [i450] + rconst (fromList [1] [0]) ! [i454], rconst (fromList [1] [0]) ! [i451] + rconst (fromList [1] [0]) ! [i455], 2 * rconst (fromList [2] [0,1]) ! [i452] + rconst (fromList [2] [0,1]) ! [i456], 2 * rconst (fromList [2] [0,1]) ! [i453] + rconst (fromList [2] [0,1]) ! [i457]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w290 (\\[i476, i473] -> [i476, i473, 0]) * rreplicate 4 (rgather [1,4,4] u458 (\\[i478] -> [i478, 0]))) (\\[i536, i537, i538, i539, i540, i541, i542, i543] -> [rem (i543 + 2 * i542 + 4 * i541 + 4 * i539 + 4 * i540) 4, i536, i537, i538]))))) (\\[i459, i460, i461, i462, i463] -> [ifF ((0 <=. i459 + i460 &&* 1 >. i459 + i460) &&* ((0 <=. i461 &&* 1 >. i461) &&* ((0 <=. i462 &&* 2 >. i462) &&* (0 <=. i463 &&* 2 >. i463)))) 0 1, i459, i460, i461, i462, i463]) ! [0]) (\\[i465, i466] -> [i465 + i466]), rsum (rsum (rsum (rtranspose [0,2,3,1] u458))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w350 (\\[i553, i550] -> [i553, i550, 0]) * rreplicate 4 (rgather [1,2,2] u417 (\\[i555] -> [i555, 0]))) (\\[i613, i614, i615, i616, i617, i618, i619, i620] -> [rem (i620 + 2 * i619 + 4 * i618 + 4 * i616 + 4 * i617) 4, i613, i614, i615]))))) (\\[i418, i419, i420, i421, i422] -> [ifF ((0 <=. i418 + i419 &&* 1 >. i418 + i419) &&* ((0 <=. i420 &&* 1 >. i420) &&* ((0 <=. i421 &&* 2 >. i421) &&* (0 <=. i422 &&* 2 >. i422)))) 0 1, i418, i419, i420, i421, i422]) ! [0]) (\\[i424, i425] -> [i424 + i425]), rsum (rsum (rsum (rtranspose [0,2,3,1] u417))), rsum (rtranspose [2,1,0] t388 * rtranspose [2,1,0] (rreplicate 1 m395)), rsum (rtranspose [1,0] m395), rsum (rtranspose [2,0,1] (rreplicate 10 (m392 * m389)) * rtranspose [2,1,0] (rreplicate 1 m394)), rsum (rtranspose [1,0] m394)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w292 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (fromList [2] [7.0,0.0])) (\\[i276, i277, i278, i279, i280, i281, i282] -> [ifF ((0 <=. i276 + i279 &&* 1 >. i276 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i277 + i281 &&* 4 >. i277 + i281) &&* (0 <=. i278 + i282 &&* 4 >. i278 + i282)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i283, i284] -> [i283 + i284]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i285, i286, i287, i288, i289] -> [ifF ((0 <=. i285 + i286 &&* 1 >. i285 + i286) &&* ((0 <=. i287 &&* 1 >. i287) &&* ((0 <=. i288 &&* 2 >. i288) &&* (0 <=. i289 &&* 2 >. i289)))) 0 1, i285, i286, i287, i288, i289]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2))))))))))) ; w325 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303, i304, i305, i306] -> [ifF (w292 ! [i299, i300, i301, i302, i303, i304, i305, i306, rconst (fromList [1] [0]) ! [i299] + rconst (fromList [1] [0]) ! [i303], rconst (fromList [1] [0]) ! [i300] + rconst (fromList [1] [0]) ! [i304], 2 * rconst (fromList [2] [0,1]) ! [i301] + rconst (fromList [2] [0,1]) ! [i305], 2 * rconst (fromList [2] [0,1]) ! [i302] + rconst (fromList [2] [0,1]) ! [i306]] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w292 (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [i307, i308, i309, i310, i311, i312, i313, i314, rconst (fromList [1] [0]) ! [i307] + rconst (fromList [1] [0]) ! [i311], rconst (fromList [1] [0]) ! [i308] + rconst (fromList [1] [0]) ! [i312], 2 * rconst (fromList [2] [0,1]) ! [i309] + rconst (fromList [2] [0,1]) ! [i313], 2 * rconst (fromList [2] [0,1]) ! [i310] + rconst (fromList [2] [0,1]) ! [i314]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i317, i318, i319, i320, i321, i322, i323, i324] -> [ifF ((0 <=. i317 + i321 &&* 1 >. i317 + i321) &&* ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. 2 * i319 + i323 &&* 4 >. 2 * i319 + i323) &&* (0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324)))) 0 1, i317, i318, i319, i320, i321, i322, i323, i324])))))))) ; w352 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w325 (\\[i329, i330, i331, i332, i333, i334, i335] -> [i329, i330, i331, i332, i333, i334, i335, rconst (fromList [1] [0]) ! [i329] + rconst (fromList [1] [0]) ! [i332], i333, rconst (fromList [2] [0,1]) ! [i330] + rconst (fromList [2] [0,1]) ! [i334], rconst (fromList [2] [0,1]) ! [i331] + rconst (fromList [2] [0,1]) ! [i335], 0, 0, rem (quot (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, rconst (fromList [1] [0]) ! [i329] + rconst (fromList [1] [0]) ! [i332], i333, rconst (fromList [2] [0,1]) ! [i330] + rconst (fromList [2] [0,1]) ! [i334], rconst (fromList [2] [0,1]) ! [i331] + rconst (fromList [2] [0,1]) ! [i335]]))) 2) 2, rem (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, rconst (fromList [1] [0]) ! [i329] + rconst (fromList [1] [0]) ! [i332], i333, rconst (fromList [2] [0,1]) ! [i330] + rconst (fromList [2] [0,1]) ! [i334], rconst (fromList [2] [0,1]) ! [i331] + rconst (fromList [2] [0,1]) ! [i335]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i336, i337, i338, i339, i340, i341, i342] -> [ifF ((0 <=. i336 + i339 &&* 1 >. i336 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i337 + i341 &&* 2 >. i337 + i341) &&* (0 <=. i338 + i342 &&* 2 >. i338 + i342)))) 0 1, i336, i337, i338, i339, i340, i341, i342])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i343, i344] -> [i343 + i344]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i345, i346, i347, i348, i349] -> [ifF ((0 <=. i345 + i346 &&* 1 >. i345 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i348 &&* 2 >. i348) &&* (0 <=. i349 &&* 2 >. i349)))) 0 1, i345, i346, i347, i348, i349]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4))))))))))) ; w383 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [ifF (w352 ! [i357, i358, i359, i360, i361, i362, i363, i364, rconst (fromList [1] [0]) ! [i357] + rconst (fromList [1] [0]) ! [i361], rconst (fromList [1] [0]) ! [i358] + rconst (fromList [1] [0]) ! [i362], 2 * rconst (fromList [1] [0]) ! [i359] + rconst (fromList [2] [0,1]) ! [i363], 2 * rconst (fromList [1] [0]) ! [i360] + rconst (fromList [2] [0,1]) ! [i364]] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w352 (\\[i365, i366, i367, i368, i369, i370, i371, i372] -> [i365, i366, i367, i368, i369, i370, i371, i372, rconst (fromList [1] [0]) ! [i365] + rconst (fromList [1] [0]) ! [i369], rconst (fromList [1] [0]) ! [i366] + rconst (fromList [1] [0]) ! [i370], 2 * rconst (fromList [1] [0]) ! [i367] + rconst (fromList [2] [0,1]) ! [i371], 2 * rconst (fromList [1] [0]) ! [i368] + rconst (fromList [2] [0,1]) ! [i372]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i375, i376, i377, i378, i379, i380, i381, i382] -> [ifF ((0 <=. i375 + i379 &&* 1 >. i375 + i379) &&* ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. 2 * i377 + i381 &&* 2 >. 2 * i377 + i381) &&* (0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382)))) 0 1, i375, i376, i377, i378, i379, i380, i381, i382]) ; m389 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w383 (\\[i384, i385, i386, i387] -> [i384, i385, i386, i387, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2) 2, rem (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v6) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i390, i391] -> [ifF (m389 ! [i390, i391] <=. 0.0) 0 1]) * m389))) + rtranspose [1,0] (rreplicate 1 v8)]"
