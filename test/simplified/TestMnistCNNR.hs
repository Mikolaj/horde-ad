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
  :: forall ranked r.
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
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
                             OSArray SizeMnistHeight SizeMnistWidth
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
      ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
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
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyphR, labelR) adinputs =
                   MnistCnnRanked2.convMnistLossFusedR
                     miniBatchSize (rconst $ Nested.rfromOrthotope SNat glyphR, rconst $ Nested.rfromOrthotope SNat labelR)
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
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
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
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
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
                             OSArray SizeMnistHeight SizeMnistWidth
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
      ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
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
         funToAstIO
           (FTKR $ miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistCnnRanked2.convMnistLossFusedR
                   miniBatchSize (AstRanked astGlyph, AstRanked astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (unRawHVector hVectorPrimal))
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvD emptyEnv
                             $ zip vars $ V.toList varInputs
                       envMnist = extendEnv varGlyph (rconst $ Nested.rfromOrthotope SNat glyph)
                                  $ extendEnv varLabel (rconst $ Nested.rfromOrthotope SNat label) env
                   in interpretAst envMnist $ unAstRanked ast
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
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
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
     ( ranked ~ ORArray, Differentiable r, GoodScalar r, Random r
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
               OSArray SizeMnistHeight SizeMnistWidth
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
        ftest :: Int -> MnistDataBatchR r -> HVector ORArray -> r
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
         funToAstIO
           (FTKR $ miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, varLabelD, astLabel) <-
         funToAstIO (FTKR $ miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let envInit = extendEnv varGlyph (rconstant $ AstRaw astGlyph)
                     $ extendEnv varLabel (rconstant $ AstRaw astLabel)
                       emptyEnv
           f = MnistCnnRanked2.convMnistLossFusedR
                 miniBatchSize (AstRanked astGlyph, AstRanked astLabel)
           (AstArtifact varDtAgain vars1Again gradientRaw primal, _) =
             revProduceArtifactH False f envInit valsInit
                                 (voidFromHVector hVectorInit)
           gradient = simplifyInlineHVectorRaw gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           art = AstArtifact varDtAgain vars1AndInputAgain gradient primal
           go :: [MnistDataBatchR r] -> (HVector ORArray, StateAdam)
              -> (HVector ORArray, StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat glyph
                 labelD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   fst $ revEvalArtifact art parametersAndInput Nothing
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
             unless (n_hidden < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (HVector ORArray, StateAdam) -> IO (HVector ORArray)
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
      blackGlyph = AstRanked
                   $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @4)
                   $ AstReplicate (SNat @4)
                       (7 :: AstTensor PrimalSpan (TKR Double 0))
      valsInit :: MnistCnnRanked2.ADCnnMnistParameters ORArray Double
      valsInit =
        forgetShape $ fst
        $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                         OSArray 4 4  -- see sizeMnistWidthI, etc.
                         1 1 1 1 Double)
                     0.4 (mkStdGen 44)
      afcnn2T :: MnistCnnRanked2.ADCnnMnistParameters (AstRanked FullSpan)
                                                      Double
              -> AstRanked FullSpan Double 2
      afcnn2T = MnistCnnRanked2.convMnistTwoR sizeMnistHeightI sizeMnistWidthI
                                              batch_size blackGlyph
      (artifactRev, _) = revArtifactAdapt True afcnn2T valsInit
  printArtifactPretty renames artifactRev
    @?= "\\m394 u1 v2 u3 v4 m5 v6 m7 v8 -> let w290 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i276, i277, i278, i279, i280, i281, i282] -> [ifF ((0 <=. i276 + i279 &&* 1 >. i276 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i277 + i281 &&* 4 >. i277 + i281) &&* (0 <=. i278 + i282 &&* 4 >. i278 + i282)))) 0 1])))) ; w291 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1 (\\[i283, i284] -> [i283 + i284]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i285, i286, i287, i288, i289] -> [ifF ((0 <=. i285 + i286 &&* 1 >. i285 + i286) &&* ((0 <=. i287 &&* 1 >. i287) &&* ((0 <=. i288 &&* 2 >. i288) &&* (0 <=. i289 &&* 2 >. i289)))) 0 1, i285, i286, i287, i288, i289])))))) ; w292 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w290 * w291) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2))))))))))) ; w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v295 = rconst (rfromListLinear [2] [0,1]) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v295)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v297 = rconst (rfromListLinear [2] [0,1]) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v297)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w315 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303, i304, i305, i306] -> [ifF (w292 ! [i299, i300, i301, i302, i303, i304, i305, i306, w293 ! [i299, i300, i301, i302, i303, i304, i305, i306], w294 ! [i299, i300, i301, i302, i303, i304, i305, i306], w296 ! [i299, i300, i301, i302, i303, i304, i305, i306], w298 ! [i299, i300, i301, i302, i303, i304, i305, i306]] <=. 0.0) 0 1]) ; w316 = rgather [1,1,2,2,1,1,2,2] w292 (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [i307, i308, i309, i310, i311, i312, i313, i314, w293 ! [i307, i308, i309, i310, i311, i312, i313, i314], w294 ! [i307, i308, i309, i310, i311, i312, i313, i314], w296 ! [i307, i308, i309, i310, i311, i312, i313, i314], w298 ! [i307, i308, i309, i310, i311, i312, i313, i314]]) ; w325 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w315 * w316, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i317, i318, i319, i320, i321, i322, i323, i324] -> [ifF ((0 <=. i317 + i321 &&* 1 >. i317 + i321) &&* ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. 2 * i319 + i323 &&* 4 >. 2 * i319 + i323) &&* (0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324)))) 0 1, i317, i318, i319, i320, i321, i322, i323, i324])))))))) ; w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w350 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w325 (\\[i329, i330, i331, i332, i333, i334, i335] -> [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i336, i337, i338, i339, i340, i341, i342] -> [ifF ((0 <=. i336 + i339 &&* 1 >. i336 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i337 + i341 &&* 2 >. i337 + i341) &&* (0 <=. i338 + i342 &&* 2 >. i338 + i342)))) 0 1, i336, i337, i338, i339, i340, i341, i342])))) ; w351 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u3 (\\[i343, i344] -> [i343 + i344]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i345, i346, i347, i348, i349] -> [ifF ((0 <=. i345 + i346 &&* 1 >. i345 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i348 &&* 2 >. i348) &&* (0 <=. i349 &&* 2 >. i349)))) 0 1, i345, i346, i347, i348, i349])))))) ; w352 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w350 * w351) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4))))))))))) ; w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w373 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [ifF (w352 ! [i357, i358, i359, i360, i361, i362, i363, i364, w353 ! [i357, i358, i359, i360, i361, i362, i363, i364], w354 ! [i357, i358, i359, i360, i361, i362, i363, i364], w355 ! [i357, i358, i359, i360, i361, i362, i363, i364], w356 ! [i357, i358, i359, i360, i361, i362, i363, i364]] <=. 0.0) 0 1]) ; w374 = rgather [1,1,1,1,1,1,2,2] w352 (\\[i365, i366, i367, i368, i369, i370, i371, i372] -> [i365, i366, i367, i368, i369, i370, i371, i372, w353 ! [i365, i366, i367, i368, i369, i370, i371, i372], w354 ! [i365, i366, i367, i368, i369, i370, i371, i372], w355 ! [i365, i366, i367, i368, i369, i370, i371, i372], w356 ! [i365, i366, i367, i368, i369, i370, i371, i372]]) ; w383 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w373 * w374, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i375, i376, i377, i378, i379, i380, i381, i382] -> [ifF ((0 <=. i375 + i379 &&* 1 >. i375 + i379) &&* ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. 2 * i377 + i381 &&* 2 >. 2 * i377 + i381) &&* (0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382)))) 0 1, i375, i376, i377, i378, i379, i380, i381, i382]) ; t388 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w383 (\\[i384, i385, i386, i387] -> [i384, i385, i386, i387, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2) 2, remF (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2]))))) ; m389 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t388) + rtranspose [1,0] (rreplicate 1 v6) ; m392 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i390, i391] -> [ifF (m389 ! [i390, i391] <=. 0.0) 0 1]) ; t393 = rtranspose [1,0] (rreplicate 10 (m392 * m389)) ; m395 = m392 * rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 m7) * rreplicate 1 m394)) ; t396 = rreplicate 1 m395 ; w409 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rtranspose [1,0] (rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 1 m5) * t396))))) (\\[i397, i398, i399, i400] -> [i397, i398, i399, i400, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w383 ! [i397, i398, i399, i400]))) 2) 2, remF (rmaxIndex (rreshape [4] (w383 ! [i397, i398, i399, i400]))) 2])) (\\[i401, i402, i403, i404, i405, i406, i407, i408] -> [ifF ((0 <=. i401 + i405 &&* 1 >. i401 + i405) &&* ((0 <=. i402 + i406 &&* 1 >. i402 + i406) &&* ((0 <=. 2 * i403 + i407 &&* 2 >. 2 * i403 + i407) &&* (0 <=. 2 * i404 + i408 &&* 2 >. 2 * i404 + i408)))) 0 1, i401, i402, i403, i404, i405, i406, i407, i408]) ; u418 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w373 * w409 ! [0]) (\\[i410, i411, i412, i413, i414, i415, i416, i417] -> [i410, i411, i412, i413, i414, i415, i416, i417, w353 ! [i410, i411, i412, i413, i414, i415, i416, i417], w354 ! [i410, i411, i412, i413, i414, i415, i416, i417], w355 ! [i410, i411, i412, i413, i414, i415, i416, i417], w356 ! [i410, i411, i412, i413, i414, i415, i416, i417]]))))))))) ; w419 = rreplicate 4 u418 ; w425 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w350 * w419)))))) (\\[i420, i421, i422, i423, i424] -> [ifF ((0 <=. i420 + i421 &&* 1 >. i420 + i421) &&* ((0 <=. i422 &&* 1 >. i422) &&* ((0 <=. i423 &&* 2 >. i423) &&* (0 <=. i424 &&* 2 >. i424)))) 0 1, i420, i421, i422, i423, i424]) ; w435 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] (w351 * w419)))) (\\[i428, i429, i430, i431, i432, i433, i434] -> [ifF ((0 <=. i428 + i431 &&* 1 >. i428 + i431) &&* ((0 <=. i432 &&* 1 >. i432) &&* ((0 <=. i429 + i433 &&* 2 >. i429 + i433) &&* (0 <=. i430 + i434 &&* 2 >. i430 + i434)))) 0 1, i428, i429, i430, i431, i432, i433, i434]) ; w451 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w435 ! [0]) (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, w326 ! [i436, i437, i438, i439, i440, i441, i442], i440, w327 ! [i436, i437, i438, i439, i440, i441, i442], w328 ! [i436, i437, i438, i439, i440, i441, i442], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w325 ! [i436, i437, i438, i439, i440, i441, i442, w326 ! [i436, i437, i438, i439, i440, i441, i442], i440, w327 ! [i436, i437, i438, i439, i440, i441, i442], w328 ! [i436, i437, i438, i439, i440, i441, i442]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w325 ! [i436, i437, i438, i439, i440, i441, i442, w326 ! [i436, i437, i438, i439, i440, i441, i442], i440, w327 ! [i436, i437, i438, i439, i440, i441, i442], w328 ! [i436, i437, i438, i439, i440, i441, i442]]))) 2]))))))))) (\\[i443, i444, i445, i446, i447, i448, i449, i450] -> [ifF ((0 <=. i443 + i447 &&* 1 >. i443 + i447) &&* ((0 <=. i444 + i448 &&* 1 >. i444 + i448) &&* ((0 <=. 2 * i445 + i449 &&* 4 >. 2 * i445 + i449) &&* (0 <=. 2 * i446 + i450 &&* 4 >. 2 * i446 + i450)))) 0 1, i443, i444, i445, i446, i447, i448, i449, i450]) ; u460 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w315 * w451 ! [0]) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [i452, i453, i454, i455, i456, i457, i458, i459, w293 ! [i452, i453, i454, i455, i456, i457, i458, i459], w294 ! [i452, i453, i454, i455, i456, i457, i458, i459], w296 ! [i452, i453, i454, i455, i456, i457, i458, i459], w298 ! [i452, i453, i454, i455, i456, i457, i458, i459]]))))))))) ; w466 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w290 * rreplicate 4 u460)))))) (\\[i461, i462, i463, i464, i465] -> [ifF ((0 <=. i461 + i462 &&* 1 >. i461 + i462) &&* ((0 <=. i463 &&* 1 >. i463) &&* ((0 <=. i464 &&* 2 >. i464) &&* (0 <=. i465 &&* 2 >. i465)))) 0 1, i461, i462, i463, i464, i465]) in [rscatter [1,1,2,2] (w466 ! [0]) (\\[i467, i468] -> [i467 + i468]), rsum (rsum (rsum (rtranspose [0,2,3,1] u460))), rscatter [1,1,2,2] (w425 ! [0]) (\\[i426, i427] -> [i426 + i427]), rsum (rsum (rsum (rtranspose [0,2,3,1] u418))), rsum (rtranspose [2,1,0] (t388 * t396)), rsum (rtranspose [1,0] m395), rsum (rtranspose [2,1,0] (t393 * rreplicate 1 m394)), rsum (rtranspose [1,0] m394)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w290 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i276, i277, i278, i279, i280, i281, i282] -> [ifF ((0 <=. i276 + i279 &&* 1 >. i276 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i277 + i281 &&* 4 >. i277 + i281) &&* (0 <=. i278 + i282 &&* 4 >. i278 + i282)))) 0 1])))) ; w291 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1 (\\[i283, i284] -> [i283 + i284]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i285, i286, i287, i288, i289] -> [ifF ((0 <=. i285 + i286 &&* 1 >. i285 + i286) &&* ((0 <=. i287 &&* 1 >. i287) &&* ((0 <=. i288 &&* 2 >. i288) &&* (0 <=. i289 &&* 2 >. i289)))) 0 1, i285, i286, i287, i288, i289])))))) ; w292 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w290 * w291) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2))))))))))) ; w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v295 = rconst (rfromListLinear [2] [0,1]) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v295)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v297 = rconst (rfromListLinear [2] [0,1]) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v297)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w315 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303, i304, i305, i306] -> [ifF (w292 ! [i299, i300, i301, i302, i303, i304, i305, i306, w293 ! [i299, i300, i301, i302, i303, i304, i305, i306], w294 ! [i299, i300, i301, i302, i303, i304, i305, i306], w296 ! [i299, i300, i301, i302, i303, i304, i305, i306], w298 ! [i299, i300, i301, i302, i303, i304, i305, i306]] <=. 0.0) 0 1]) ; w316 = rgather [1,1,2,2,1,1,2,2] w292 (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [i307, i308, i309, i310, i311, i312, i313, i314, w293 ! [i307, i308, i309, i310, i311, i312, i313, i314], w294 ! [i307, i308, i309, i310, i311, i312, i313, i314], w296 ! [i307, i308, i309, i310, i311, i312, i313, i314], w298 ! [i307, i308, i309, i310, i311, i312, i313, i314]]) ; w325 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w315 * w316, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i317, i318, i319, i320, i321, i322, i323, i324] -> [ifF ((0 <=. i317 + i321 &&* 1 >. i317 + i321) &&* ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. 2 * i319 + i323 &&* 4 >. 2 * i319 + i323) &&* (0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324)))) 0 1, i317, i318, i319, i320, i321, i322, i323, i324])))))))) ; w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w350 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w325 (\\[i329, i330, i331, i332, i333, i334, i335] -> [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i336, i337, i338, i339, i340, i341, i342] -> [ifF ((0 <=. i336 + i339 &&* 1 >. i336 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i337 + i341 &&* 2 >. i337 + i341) &&* (0 <=. i338 + i342 &&* 2 >. i338 + i342)))) 0 1, i336, i337, i338, i339, i340, i341, i342])))) ; w351 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u3 (\\[i343, i344] -> [i343 + i344]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i345, i346, i347, i348, i349] -> [ifF ((0 <=. i345 + i346 &&* 1 >. i345 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i348 &&* 2 >. i348) &&* (0 <=. i349 &&* 2 >. i349)))) 0 1, i345, i346, i347, i348, i349])))))) ; w352 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w350 * w351) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4))))))))))) ; w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w373 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [ifF (w352 ! [i357, i358, i359, i360, i361, i362, i363, i364, w353 ! [i357, i358, i359, i360, i361, i362, i363, i364], w354 ! [i357, i358, i359, i360, i361, i362, i363, i364], w355 ! [i357, i358, i359, i360, i361, i362, i363, i364], w356 ! [i357, i358, i359, i360, i361, i362, i363, i364]] <=. 0.0) 0 1]) ; w374 = rgather [1,1,1,1,1,1,2,2] w352 (\\[i365, i366, i367, i368, i369, i370, i371, i372] -> [i365, i366, i367, i368, i369, i370, i371, i372, w353 ! [i365, i366, i367, i368, i369, i370, i371, i372], w354 ! [i365, i366, i367, i368, i369, i370, i371, i372], w355 ! [i365, i366, i367, i368, i369, i370, i371, i372], w356 ! [i365, i366, i367, i368, i369, i370, i371, i372]]) ; w383 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w373 * w374, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i375, i376, i377, i378, i379, i380, i381, i382] -> [ifF ((0 <=. i375 + i379 &&* 1 >. i375 + i379) &&* ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. 2 * i377 + i381 &&* 2 >. 2 * i377 + i381) &&* (0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382)))) 0 1, i375, i376, i377, i378, i379, i380, i381, i382]) ; t388 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w383 (\\[i384, i385, i386, i387] -> [i384, i385, i386, i387, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2) 2, remF (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2]))))) ; m389 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t388) + rtranspose [1,0] (rreplicate 1 v6) ; m392 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i390, i391] -> [ifF (m389 ! [i390, i391] <=. 0.0) 0 1]) ; t393 = rtranspose [1,0] (rreplicate 10 (m392 * m389)) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * t393) + rtranspose [1,0] (rreplicate 1 v8)]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m394 u1 v2 u3 v4 m5 v6 m7 v8 -> let w290 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i276, i277, i278, i279, i280, i281, i282] -> [ifF ((0 <=. i276 + i279 &&* 1 >. i276 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i277 + i281 &&* 4 >. i277 + i281) &&* (0 <=. i278 + i282 &&* 4 >. i278 + i282)))) 0 1])))) ; w292 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w290 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1 (\\[i283, i284] -> [i283 + i284]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i285, i286, i287, i288, i289] -> [ifF ((0 <=. i285 + i286 &&* 1 >. i285 + i286) &&* ((0 <=. i287 &&* 1 >. i287) &&* ((0 <=. i288 &&* 2 >. i288) &&* (0 <=. i289 &&* 2 >. i289)))) 0 1, i285, i286, i287, i288, i289]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2))))))))))) ; w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w315 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303, i304, i305, i306] -> [ifF (w292 ! [i299, i300, i301, i302, i303, i304, i305, i306, w293 ! [i299, i300, i301, i302, i303, i304, i305, i306], w294 ! [i299, i300, i301, i302, i303, i304, i305, i306], w296 ! [i299, i300, i301, i302, i303, i304, i305, i306], w298 ! [i299, i300, i301, i302, i303, i304, i305, i306]] <=. 0.0) 0 1]) ; w325 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w315 * rgather [1,1,2,2,1,1,2,2] w292 (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [i307, i308, i309, i310, i311, i312, i313, i314, w293 ! [i307, i308, i309, i310, i311, i312, i313, i314], w294 ! [i307, i308, i309, i310, i311, i312, i313, i314], w296 ! [i307, i308, i309, i310, i311, i312, i313, i314], w298 ! [i307, i308, i309, i310, i311, i312, i313, i314]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i317, i318, i319, i320, i321, i322, i323, i324] -> [ifF ((0 <=. i317 + i321 &&* 1 >. i317 + i321) &&* ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. 2 * i319 + i323 &&* 4 >. 2 * i319 + i323) &&* (0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324)))) 0 1, i317, i318, i319, i320, i321, i322, i323, i324])))))))) ; w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w350 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w325 (\\[i329, i330, i331, i332, i333, i334, i335] -> [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i336, i337, i338, i339, i340, i341, i342] -> [ifF ((0 <=. i336 + i339 &&* 1 >. i336 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i337 + i341 &&* 2 >. i337 + i341) &&* (0 <=. i338 + i342 &&* 2 >. i338 + i342)))) 0 1, i336, i337, i338, i339, i340, i341, i342])))) ; w351 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u3 (\\[i343, i344] -> [i343 + i344]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i345, i346, i347, i348, i349] -> [ifF ((0 <=. i345 + i346 &&* 1 >. i345 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i348 &&* 2 >. i348) &&* (0 <=. i349 &&* 2 >. i349)))) 0 1, i345, i346, i347, i348, i349])))))) ; w352 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w350 * w351) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4))))))))))) ; w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w373 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [ifF (w352 ! [i357, i358, i359, i360, i361, i362, i363, i364, w353 ! [i357, i358, i359, i360, i361, i362, i363, i364], w354 ! [i357, i358, i359, i360, i361, i362, i363, i364], w355 ! [i357, i358, i359, i360, i361, i362, i363, i364], w356 ! [i357, i358, i359, i360, i361, i362, i363, i364]] <=. 0.0) 0 1]) ; w383 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w373 * rgather [1,1,1,1,1,1,2,2] w352 (\\[i365, i366, i367, i368, i369, i370, i371, i372] -> [i365, i366, i367, i368, i369, i370, i371, i372, w353 ! [i365, i366, i367, i368, i369, i370, i371, i372], w354 ! [i365, i366, i367, i368, i369, i370, i371, i372], w355 ! [i365, i366, i367, i368, i369, i370, i371, i372], w356 ! [i365, i366, i367, i368, i369, i370, i371, i372]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i375, i376, i377, i378, i379, i380, i381, i382] -> [ifF ((0 <=. i375 + i379 &&* 1 >. i375 + i379) &&* ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. 2 * i377 + i381 &&* 2 >. 2 * i377 + i381) &&* (0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382)))) 0 1, i375, i376, i377, i378, i379, i380, i381, i382]) ; t388 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w383 (\\[i384, i385, i386, i387] -> [i384, i385, i386, i387, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2) 2, remF (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2])))) ; m389 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t388) + rtranspose [1,0] (rreplicate 1 v6) ; m392 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i390, i391] -> [ifF (m389 ! [i390, i391] <=. 0.0) 0 1]) ; m395 = m392 * rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m394)) ; u418 = rscatter [1,1,2,2] (w373 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] m5 (\\[i660] -> [i660, 0]) * rgather [1] m395 (\\[i657] -> [i657, 0]))))))) (\\[i397, i398, i399, i400] -> [i397, i398, i399, i400, 0, 0, remF (quotF (rmaxIndex (rgather [4] (w383 ! [i397, i398, i399, i400, 0, 0]) (\\[i650] -> [remF (quotF i650 2) 2, remF i650 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w383 ! [i397, i398, i399, i400, 0, 0]) (\\[i651] -> [remF (quotF i651 2) 2, remF i651 2]))) 2])) (\\[i401, i402, i403, i404, i405, i406, i407, i408] -> [ifF ((0 <=. i401 + i405 &&* 1 >. i401 + i405) &&* ((0 <=. i402 + i406 &&* 1 >. i402 + i406) &&* ((0 <=. 2 * i403 + i407 &&* 2 >. 2 * i403 + i407) &&* (0 <=. 2 * i404 + i408 &&* 2 >. 2 * i404 + i408)))) 0 1, i401, i402, i403, i404, i405, i406, i407, i408]) ! [0]) (\\[i410, i411, i412, i413, i414, i415, i416, i417] -> [w353 ! [i410, i411, i412, i413, i414, i415, i416, i417], w354 ! [i410, i411, i412, i413, i414, i415, i416, i417], w355 ! [i410, i411, i412, i413, i414, i415, i416, i417], w356 ! [i410, i411, i412, i413, i414, i415, i416, i417]]) ; u460 = rscatter [1,1,4,4] (w315 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w351 (\\[i634, i635, i636, i633] -> [i636, 0, i633, i634, i635]) * rgather [2,2,4,1] (u418 ! [0]) (\\[i639, i640, i641, i638] -> [i638, i639, i640])) (\\[i642, i643, i644, i645, i646, i647, i648, i649] -> [remF (quotF (i649 + 2 * i648 + 4 * i647 + 4 * i646 + 4 * i645 + 16 * i643 + 8 * i644) 8) 2, remF (quotF (i649 + 2 * i648 + 4 * i647 + 4 * i646 + 4 * i645 + 16 * i643 + 8 * i644) 4) 2, remF (i649 + 2 * i648 + 4 * i647 + 4 * i646 + 4 * i645 + 16 * i643 + 8 * i644) 4, i642]))) (\\[i428, i429, i430, i431, i432, i433, i434] -> [ifF ((0 <=. i428 + i431 &&* 1 >. i428 + i431) &&* ((0 <=. i432 &&* 1 >. i432) &&* ((0 <=. i429 + i433 &&* 2 >. i429 + i433) &&* (0 <=. i430 + i434 &&* 2 >. i430 + i434)))) 0 1, i428, i429, i430, i431, i432, i433, i434]) ! [0]) (\\[i436, i437, i438, i439, i440, i441, i442] -> [w326 ! [i436, i437, i438, i439, i440, i441, i442], i440, w327 ! [i436, i437, i438, i439, i440, i441, i442], w328 ! [i436, i437, i438, i439, i440, i441, i442], 0, 0, remF (quotF (rmaxIndex (rgather [4] (w325 ! [i436, i437, i438, i439, i440, i441, i442, w326 ! [i436, i437, i438, i439, i440, i441, i442], i440, w327 ! [i436, i437, i438, i439, i440, i441, i442], w328 ! [i436, i437, i438, i439, i440, i441, i442], 0, 0]) (\\[i623] -> [remF (quotF i623 2) 2, remF i623 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w325 ! [i436, i437, i438, i439, i440, i441, i442, w326 ! [i436, i437, i438, i439, i440, i441, i442], i440, w327 ! [i436, i437, i438, i439, i440, i441, i442], w328 ! [i436, i437, i438, i439, i440, i441, i442], 0, 0]) (\\[i624] -> [remF (quotF i624 2) 2, remF i624 2]))) 2])) (\\[i443, i444, i445, i446, i447, i448, i449, i450] -> [ifF ((0 <=. i443 + i447 &&* 1 >. i443 + i447) &&* ((0 <=. i444 + i448 &&* 1 >. i444 + i448) &&* ((0 <=. 2 * i445 + i449 &&* 4 >. 2 * i445 + i449) &&* (0 <=. 2 * i446 + i450 &&* 4 >. 2 * i446 + i450)))) 0 1, i443, i444, i445, i446, i447, i448, i449, i450]) ! [0]) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [w293 ! [i452, i453, i454, i455, i456, i457, i458, i459], w294 ! [i452, i453, i454, i455, i456, i457, i458, i459], w296 ! [i452, i453, i454, i455, i456, i457, i458, i459], w298 ! [i452, i453, i454, i455, i456, i457, i458, i459]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w290 (\\[i478, i475] -> [i478, i475, 0]) * rreplicate 4 (rgather [1,4,4] u460 (\\[i480] -> [i480, 0]))) (\\[i538, i539, i540, i541, i542, i543, i544, i545] -> [remF (i545 + 2 * i544 + 4 * i543 + 4 * i541 + 4 * i542) 4, i538, i539, i540]))))) (\\[i461, i462, i463, i464, i465] -> [ifF ((0 <=. i461 + i462 &&* 1 >. i461 + i462) &&* ((0 <=. i463 &&* 1 >. i463) &&* ((0 <=. i464 &&* 2 >. i464) &&* (0 <=. i465 &&* 2 >. i465)))) 0 1, i461, i462, i463, i464, i465]) ! [0]) (\\[i467, i468] -> [i467 + i468]), rsum (rsum (rsum (rtranspose [0,2,3,1] u460))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w350 (\\[i555, i552] -> [i555, i552, 0]) * rreplicate 4 (rgather [1,2,2] u418 (\\[i557] -> [i557, 0]))) (\\[i615, i616, i617, i618, i619, i620, i621, i622] -> [remF (i622 + 2 * i621 + 4 * i620 + 4 * i618 + 4 * i619) 4, i615, i616, i617]))))) (\\[i420, i421, i422, i423, i424] -> [ifF ((0 <=. i420 + i421 &&* 1 >. i420 + i421) &&* ((0 <=. i422 &&* 1 >. i422) &&* ((0 <=. i423 &&* 2 >. i423) &&* (0 <=. i424 &&* 2 >. i424)))) 0 1, i420, i421, i422, i423, i424]) ! [0]) (\\[i426, i427] -> [i426 + i427]), rsum (rsum (rsum (rtranspose [0,2,3,1] u418))), rsum (rtranspose [2,1,0] t388 * rtranspose [2,1,0] (rreplicate 1 m395)), rsum (rtranspose [1,0] m395), rsum (rtranspose [2,0,1] (rreplicate 10 (m392 * m389)) * rtranspose [2,1,0] (rreplicate 1 m394)), rsum (rtranspose [1,0] m394)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w292 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i276, i277, i278, i279, i280, i281, i282] -> [ifF ((0 <=. i276 + i279 &&* 1 >. i276 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i277 + i281 &&* 4 >. i277 + i281) &&* (0 <=. i278 + i282 &&* 4 >. i278 + i282)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1 (\\[i283, i284] -> [i283 + i284]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i285, i286, i287, i288, i289] -> [ifF ((0 <=. i285 + i286 &&* 1 >. i285 + i286) &&* ((0 <=. i287 &&* 1 >. i287) &&* ((0 <=. i288 &&* 2 >. i288) &&* (0 <=. i289 &&* 2 >. i289)))) 0 1, i285, i286, i287, i288, i289]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2))))))))))) ; w293 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w294 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w296 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w298 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w325 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303, i304, i305, i306] -> [ifF (w292 ! [i299, i300, i301, i302, i303, i304, i305, i306, w293 ! [i299, i300, i301, i302, i303, i304, i305, i306], w294 ! [i299, i300, i301, i302, i303, i304, i305, i306], w296 ! [i299, i300, i301, i302, i303, i304, i305, i306], w298 ! [i299, i300, i301, i302, i303, i304, i305, i306]] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w292 (\\[i307, i308, i309, i310, i311, i312, i313, i314] -> [i307, i308, i309, i310, i311, i312, i313, i314, w293 ! [i307, i308, i309, i310, i311, i312, i313, i314], w294 ! [i307, i308, i309, i310, i311, i312, i313, i314], w296 ! [i307, i308, i309, i310, i311, i312, i313, i314], w298 ! [i307, i308, i309, i310, i311, i312, i313, i314]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i317, i318, i319, i320, i321, i322, i323, i324] -> [ifF ((0 <=. i317 + i321 &&* 1 >. i317 + i321) &&* ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. 2 * i319 + i323 &&* 4 >. 2 * i319 + i323) &&* (0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324)))) 0 1, i317, i318, i319, i320, i321, i322, i323, i324])))))))) ; w326 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w327 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w328 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w352 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w325 (\\[i329, i330, i331, i332, i333, i334, i335] -> [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w325 ! [i329, i330, i331, i332, i333, i334, i335, w326 ! [i329, i330, i331, i332, i333, i334, i335], i333, w327 ! [i329, i330, i331, i332, i333, i334, i335], w328 ! [i329, i330, i331, i332, i333, i334, i335]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i336, i337, i338, i339, i340, i341, i342] -> [ifF ((0 <=. i336 + i339 &&* 1 >. i336 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i337 + i341 &&* 2 >. i337 + i341) &&* (0 <=. i338 + i342 &&* 2 >. i338 + i342)))) 0 1, i336, i337, i338, i339, i340, i341, i342])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u3 (\\[i343, i344] -> [i343 + i344]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i345, i346, i347, i348, i349] -> [ifF ((0 <=. i345 + i346 &&* 1 >. i345 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i348 &&* 2 >. i348) &&* (0 <=. i349 &&* 2 >. i349)))) 0 1, i345, i346, i347, i348, i349]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4))))))))))) ; w353 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w354 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w355 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w356 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w383 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i357, i358, i359, i360, i361, i362, i363, i364] -> [ifF (w352 ! [i357, i358, i359, i360, i361, i362, i363, i364, w353 ! [i357, i358, i359, i360, i361, i362, i363, i364], w354 ! [i357, i358, i359, i360, i361, i362, i363, i364], w355 ! [i357, i358, i359, i360, i361, i362, i363, i364], w356 ! [i357, i358, i359, i360, i361, i362, i363, i364]] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w352 (\\[i365, i366, i367, i368, i369, i370, i371, i372] -> [i365, i366, i367, i368, i369, i370, i371, i372, w353 ! [i365, i366, i367, i368, i369, i370, i371, i372], w354 ! [i365, i366, i367, i368, i369, i370, i371, i372], w355 ! [i365, i366, i367, i368, i369, i370, i371, i372], w356 ! [i365, i366, i367, i368, i369, i370, i371, i372]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i375, i376, i377, i378, i379, i380, i381, i382] -> [ifF ((0 <=. i375 + i379 &&* 1 >. i375 + i379) &&* ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. 2 * i377 + i381 &&* 2 >. 2 * i377 + i381) &&* (0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382)))) 0 1, i375, i376, i377, i378, i379, i380, i381, i382]) ; m389 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w383 (\\[i384, i385, i386, i387] -> [i384, i385, i386, i387, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2) 2, remF (rmaxIndex (rreshape [4] (w383 ! [i384, i385, i386, i387]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v6) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i390, i391] -> [ifF (m389 ! [i390, i391] <=. 0.0) 0 1]) * m389))) + rtranspose [1,0] (rreplicate 1 v8)]"
