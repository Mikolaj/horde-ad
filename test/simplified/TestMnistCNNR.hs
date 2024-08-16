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
             revProduceArtifactHOld False f envInit valsInit
                                 (voidFromHVector hVectorInit)
           gradient = HVectorPseudoTensor $ simplifyInlineHVectorRaw
                      $ unHVectorPseudoTensor gradientRaw
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
    @?= "\\m462 u463 v464 u465 v466 m467 v468 m469 v470 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. i269 + i272 &&* 1 >. i269 + i272) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. i270 + i274 &&* 4 >. i270 + i274) &&* (0 <=. i271 + i275 &&* 4 >. i271 + i275)))) 0 1])))) ; w284 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u463 (\\[i276, i277] -> [i276 + i277]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. i278 + i279 &&* 1 >. i278 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282])))))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * w284) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v464))))))))))) ; w286 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w287 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v288 = rconst (rfromListLinear [2] [0,1]) ; w289 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v288)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v290 = rconst (rfromListLinear [2] [0,1]) ; w291 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v290)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w308 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i292, i293, i294, i295, i296, i297, i298, i299] -> [ifF (w285 ! [i292, i293, i294, i295, i296, i297, i298, i299, w286 ! [i292, i293, i294, i295, i296, i297, i298, i299], w287 ! [i292, i293, i294, i295, i296, i297, i298, i299], w289 ! [i292, i293, i294, i295, i296, i297, i298, i299], w291 ! [i292, i293, i294, i295, i296, i297, i298, i299]] <=. 0.0) 0 1]) ; w309 = rgather [1,1,2,2,1,1,2,2] w285 (\\[i300, i301, i302, i303, i304, i305, i306, i307] -> [i300, i301, i302, i303, i304, i305, i306, i307, w286 ! [i300, i301, i302, i303, i304, i305, i306, i307], w287 ! [i300, i301, i302, i303, i304, i305, i306, i307], w289 ! [i300, i301, i302, i303, i304, i305, i306, i307], w291 ! [i300, i301, i302, i303, i304, i305, i306, i307]]) ; w318 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w308 * w309, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i310, i311, i312, i313, i314, i315, i316, i317] -> [ifF ((0 <=. i310 + i314 &&* 1 >. i310 + i314) &&* ((0 <=. i311 + i315 &&* 1 >. i311 + i315) &&* ((0 <=. 2 * i312 + i316 &&* 4 >. 2 * i312 + i316) &&* (0 <=. 2 * i313 + i317 &&* 4 >. 2 * i313 + i317)))) 0 1, i310, i311, i312, i313, i314, i315, i316, i317])))))))) ; w319 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w320 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w321 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w343 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w318 (\\[i322, i323, i324, i325, i326, i327, i328] -> [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w318 ! [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w318 ! [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i329, i330, i331, i332, i333, i334, i335] -> [ifF ((0 <=. i329 + i332 &&* 1 >. i329 + i332) &&* ((0 <=. i333 &&* 1 >. i333) &&* ((0 <=. i330 + i334 &&* 2 >. i330 + i334) &&* (0 <=. i331 + i335 &&* 2 >. i331 + i335)))) 0 1, i329, i330, i331, i332, i333, i334, i335])))) ; w344 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u465 (\\[i336, i337] -> [i336 + i337]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i338, i339, i340, i341, i342] -> [ifF ((0 <=. i338 + i339 &&* 1 >. i338 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i341 &&* 2 >. i341) &&* (0 <=. i342 &&* 2 >. i342)))) 0 1, i338, i339, i340, i341, i342])))))) ; w345 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w343 * w344) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v466))))))))))) ; w346 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w347 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w348 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w349 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w366 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i350, i351, i352, i353, i354, i355, i356, i357] -> [ifF (w345 ! [i350, i351, i352, i353, i354, i355, i356, i357, w346 ! [i350, i351, i352, i353, i354, i355, i356, i357], w347 ! [i350, i351, i352, i353, i354, i355, i356, i357], w348 ! [i350, i351, i352, i353, i354, i355, i356, i357], w349 ! [i350, i351, i352, i353, i354, i355, i356, i357]] <=. 0.0) 0 1]) ; w367 = rgather [1,1,1,1,1,1,2,2] w345 (\\[i358, i359, i360, i361, i362, i363, i364, i365] -> [i358, i359, i360, i361, i362, i363, i364, i365, w346 ! [i358, i359, i360, i361, i362, i363, i364, i365], w347 ! [i358, i359, i360, i361, i362, i363, i364, i365], w348 ! [i358, i359, i360, i361, i362, i363, i364, i365], w349 ! [i358, i359, i360, i361, i362, i363, i364, i365]]) ; w376 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w366 * w367, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i368, i369, i370, i371, i372, i373, i374, i375] -> [ifF ((0 <=. i368 + i372 &&* 1 >. i368 + i372) &&* ((0 <=. i369 + i373 &&* 1 >. i369 + i373) &&* ((0 <=. 2 * i370 + i374 &&* 2 >. 2 * i370 + i374) &&* (0 <=. 2 * i371 + i375 &&* 2 >. 2 * i371 + i375)))) 0 1, i368, i369, i370, i371, i372, i373, i374, i375]) ; t381 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w376 (\\[i377, i378, i379, i380] -> [i377, i378, i379, i380, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w376 ! [i377, i378, i379, i380]))) 2) 2, remF (rmaxIndex (rreshape [4] (w376 ! [i377, i378, i379, i380]))) 2]))))) ; m382 = rsum (rtranspose [2,1,0] (rreplicate 1 m467) * t381) + rtranspose [1,0] (rreplicate 1 v468) ; m385 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i383, i384] -> [ifF (m382 ! [i383, i384] <=. 0.0) 0 1]) ; t386 = rtranspose [1,0] (rreplicate 10 (m385 * m382)) ; m388 = m385 * rsum (rtranspose [1,2,0] (rreplicate 1 m469) * rtranspose [1,0] (rreplicate 1 m462)) ; w402 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rsum (rtranspose [1,0] (rreplicate 1 m467) * rtranspose [1,2,0] (rreplicate 1 m388)))) (\\[i390, i391, i392, i393] -> [i390, i391, i392, i393, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w376 ! [i390, i391, i392, i393]))) 2) 2, remF (rmaxIndex (rreshape [4] (w376 ! [i390, i391, i392, i393]))) 2])) (\\[i394, i395, i396, i397, i398, i399, i400, i401] -> [ifF ((0 <=. i394 + i398 &&* 1 >. i394 + i398) &&* ((0 <=. i395 + i399 &&* 1 >. i395 + i399) &&* ((0 <=. 2 * i396 + i400 &&* 2 >. 2 * i396 + i400) &&* (0 <=. 2 * i397 + i401 &&* 2 >. 2 * i397 + i401)))) 0 1, i394, i395, i396, i397, i398, i399, i400, i401]) ; u411 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w366 * w402 ! [0]) (\\[i403, i404, i405, i406, i407, i408, i409, i410] -> [i403, i404, i405, i406, i407, i408, i409, i410, w346 ! [i403, i404, i405, i406, i407, i408, i409, i410], w347 ! [i403, i404, i405, i406, i407, i408, i409, i410], w348 ! [i403, i404, i405, i406, i407, i408, i409, i410], w349 ! [i403, i404, i405, i406, i407, i408, i409, i410]]))))))))) ; w418 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] w343 * rtranspose [1,3,4,2,0] (rreplicate 4 u411)))))) (\\[i413, i414, i415, i416, i417] -> [ifF ((0 <=. i413 + i414 &&* 1 >. i413 + i414) &&* ((0 <=. i415 &&* 1 >. i415) &&* ((0 <=. i416 &&* 2 >. i416) &&* (0 <=. i417 &&* 2 >. i417)))) 0 1, i413, i414, i415, i416, i417]) ; w428 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] w344 * rtranspose [2,1,3,4,0] (rreplicate 4 u411)))) (\\[i421, i422, i423, i424, i425, i426, i427] -> [ifF ((0 <=. i421 + i424 &&* 1 >. i421 + i424) &&* ((0 <=. i425 &&* 1 >. i425) &&* ((0 <=. i422 + i426 &&* 2 >. i422 + i426) &&* (0 <=. i423 + i427 &&* 2 >. i423 + i427)))) 0 1, i421, i422, i423, i424, i425, i426, i427]) ; w444 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w428 ! [0]) (\\[i429, i430, i431, i432, i433, i434, i435] -> [i429, i430, i431, i432, i433, i434, i435, w319 ! [i429, i430, i431, i432, i433, i434, i435], i433, w320 ! [i429, i430, i431, i432, i433, i434, i435], w321 ! [i429, i430, i431, i432, i433, i434, i435], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w318 ! [i429, i430, i431, i432, i433, i434, i435, w319 ! [i429, i430, i431, i432, i433, i434, i435], i433, w320 ! [i429, i430, i431, i432, i433, i434, i435], w321 ! [i429, i430, i431, i432, i433, i434, i435]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w318 ! [i429, i430, i431, i432, i433, i434, i435, w319 ! [i429, i430, i431, i432, i433, i434, i435], i433, w320 ! [i429, i430, i431, i432, i433, i434, i435], w321 ! [i429, i430, i431, i432, i433, i434, i435]]))) 2]))))))))) (\\[i436, i437, i438, i439, i440, i441, i442, i443] -> [ifF ((0 <=. i436 + i440 &&* 1 >. i436 + i440) &&* ((0 <=. i437 + i441 &&* 1 >. i437 + i441) &&* ((0 <=. 2 * i438 + i442 &&* 4 >. 2 * i438 + i442) &&* (0 <=. 2 * i439 + i443 &&* 4 >. 2 * i439 + i443)))) 0 1, i436, i437, i438, i439, i440, i441, i442, i443]) ; u453 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w308 * w444 ! [0]) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, i452, w286 ! [i445, i446, i447, i448, i449, i450, i451, i452], w287 ! [i445, i446, i447, i448, i449, i450, i451, i452], w289 ! [i445, i446, i447, i448, i449, i450, i451, i452], w291 ! [i445, i446, i447, i448, i449, i450, i451, i452]]))))))))) ; w459 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w283 * rreplicate 4 u453)))))) (\\[i454, i455, i456, i457, i458] -> [ifF ((0 <=. i454 + i455 &&* 1 >. i454 + i455) &&* ((0 <=. i456 &&* 1 >. i456) &&* ((0 <=. i457 &&* 2 >. i457) &&* (0 <=. i458 &&* 2 >. i458)))) 0 1, i454, i455, i456, i457, i458]) in [rscatter [1,1,2,2] (w459 ! [0]) (\\[i460, i461] -> [i460 + i461]), rsum (rsum (rsum (rtranspose [0,2,3,1] u453))), rscatter [1,1,2,2] (w418 ! [0]) (\\[i419, i420] -> [i419 + i420]), rsum (rsum (rsum (rtranspose [0,2,3,1] u411))), rsum (rtranspose [2,1,0] t381 * rtranspose [2,1,0] (rreplicate 1 m388)), rsum (rtranspose [1,0] m388), rsum (rtranspose [2,1,0] t386 * rtranspose [2,1,0] (rreplicate 1 m462)), rsum (rtranspose [1,0] m462)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\u472 v473 u474 v475 m476 v477 m478 v479 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. i269 + i272 &&* 1 >. i269 + i272) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. i270 + i274 &&* 4 >. i270 + i274) &&* (0 <=. i271 + i275 &&* 4 >. i271 + i275)))) 0 1])))) ; w284 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u472 (\\[i276, i277] -> [i276 + i277]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. i278 + i279 &&* 1 >. i278 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282])))))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * w284) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v473))))))))))) ; w286 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w287 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v288 = rconst (rfromListLinear [2] [0,1]) ; w289 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v288)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v290 = rconst (rfromListLinear [2] [0,1]) ; w291 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v290)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w308 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i292, i293, i294, i295, i296, i297, i298, i299] -> [ifF (w285 ! [i292, i293, i294, i295, i296, i297, i298, i299, w286 ! [i292, i293, i294, i295, i296, i297, i298, i299], w287 ! [i292, i293, i294, i295, i296, i297, i298, i299], w289 ! [i292, i293, i294, i295, i296, i297, i298, i299], w291 ! [i292, i293, i294, i295, i296, i297, i298, i299]] <=. 0.0) 0 1]) ; w309 = rgather [1,1,2,2,1,1,2,2] w285 (\\[i300, i301, i302, i303, i304, i305, i306, i307] -> [i300, i301, i302, i303, i304, i305, i306, i307, w286 ! [i300, i301, i302, i303, i304, i305, i306, i307], w287 ! [i300, i301, i302, i303, i304, i305, i306, i307], w289 ! [i300, i301, i302, i303, i304, i305, i306, i307], w291 ! [i300, i301, i302, i303, i304, i305, i306, i307]]) ; w318 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w308 * w309, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i310, i311, i312, i313, i314, i315, i316, i317] -> [ifF ((0 <=. i310 + i314 &&* 1 >. i310 + i314) &&* ((0 <=. i311 + i315 &&* 1 >. i311 + i315) &&* ((0 <=. 2 * i312 + i316 &&* 4 >. 2 * i312 + i316) &&* (0 <=. 2 * i313 + i317 &&* 4 >. 2 * i313 + i317)))) 0 1, i310, i311, i312, i313, i314, i315, i316, i317])))))))) ; w319 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w320 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w321 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w343 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w318 (\\[i322, i323, i324, i325, i326, i327, i328] -> [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w318 ! [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w318 ! [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i329, i330, i331, i332, i333, i334, i335] -> [ifF ((0 <=. i329 + i332 &&* 1 >. i329 + i332) &&* ((0 <=. i333 &&* 1 >. i333) &&* ((0 <=. i330 + i334 &&* 2 >. i330 + i334) &&* (0 <=. i331 + i335 &&* 2 >. i331 + i335)))) 0 1, i329, i330, i331, i332, i333, i334, i335])))) ; w344 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u474 (\\[i336, i337] -> [i336 + i337]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i338, i339, i340, i341, i342] -> [ifF ((0 <=. i338 + i339 &&* 1 >. i338 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i341 &&* 2 >. i341) &&* (0 <=. i342 &&* 2 >. i342)))) 0 1, i338, i339, i340, i341, i342])))))) ; w345 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w343 * w344) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v475))))))))))) ; w346 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w347 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w348 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w349 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w366 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i350, i351, i352, i353, i354, i355, i356, i357] -> [ifF (w345 ! [i350, i351, i352, i353, i354, i355, i356, i357, w346 ! [i350, i351, i352, i353, i354, i355, i356, i357], w347 ! [i350, i351, i352, i353, i354, i355, i356, i357], w348 ! [i350, i351, i352, i353, i354, i355, i356, i357], w349 ! [i350, i351, i352, i353, i354, i355, i356, i357]] <=. 0.0) 0 1]) ; w367 = rgather [1,1,1,1,1,1,2,2] w345 (\\[i358, i359, i360, i361, i362, i363, i364, i365] -> [i358, i359, i360, i361, i362, i363, i364, i365, w346 ! [i358, i359, i360, i361, i362, i363, i364, i365], w347 ! [i358, i359, i360, i361, i362, i363, i364, i365], w348 ! [i358, i359, i360, i361, i362, i363, i364, i365], w349 ! [i358, i359, i360, i361, i362, i363, i364, i365]]) ; w376 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w366 * w367, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i368, i369, i370, i371, i372, i373, i374, i375] -> [ifF ((0 <=. i368 + i372 &&* 1 >. i368 + i372) &&* ((0 <=. i369 + i373 &&* 1 >. i369 + i373) &&* ((0 <=. 2 * i370 + i374 &&* 2 >. 2 * i370 + i374) &&* (0 <=. 2 * i371 + i375 &&* 2 >. 2 * i371 + i375)))) 0 1, i368, i369, i370, i371, i372, i373, i374, i375]) ; t381 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w376 (\\[i377, i378, i379, i380] -> [i377, i378, i379, i380, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w376 ! [i377, i378, i379, i380]))) 2) 2, remF (rmaxIndex (rreshape [4] (w376 ! [i377, i378, i379, i380]))) 2]))))) ; m382 = rsum (rtranspose [2,1,0] (rreplicate 1 m476) * t381) + rtranspose [1,0] (rreplicate 1 v477) ; m385 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i383, i384] -> [ifF (m382 ! [i383, i384] <=. 0.0) 0 1]) ; t386 = rtranspose [1,0] (rreplicate 10 (m385 * m382)) in [rsum (rtranspose [2,1,0] (rreplicate 1 m478) * t386) + rtranspose [1,0] (rreplicate 1 v479)]"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m674 u675 v676 u677 v678 m679 v680 m681 v682 -> let w283 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. i269 + i272 &&* 1 >. i269 + i272) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. i270 + i274 &&* 4 >. i270 + i274) &&* (0 <=. i271 + i275 &&* 4 >. i271 + i275)))) 0 1])))) ; w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w283 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u675 (\\[i276, i277] -> [i276 + i277]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. i278 + i279 &&* 1 >. i278 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v676))))))))))) ; w286 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w287 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w289 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w291 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w308 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i292, i293, i294, i295, i296, i297, i298, i299] -> [ifF (w285 ! [i292, i293, i294, i295, i296, i297, i298, i299, w286 ! [i292, i293, i294, i295, i296, i297, i298, i299], w287 ! [i292, i293, i294, i295, i296, i297, i298, i299], w289 ! [i292, i293, i294, i295, i296, i297, i298, i299], w291 ! [i292, i293, i294, i295, i296, i297, i298, i299]] <=. 0.0) 0 1]) ; w318 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w308 * rgather [1,1,2,2,1,1,2,2] w285 (\\[i300, i301, i302, i303, i304, i305, i306, i307] -> [i300, i301, i302, i303, i304, i305, i306, i307, w286 ! [i300, i301, i302, i303, i304, i305, i306, i307], w287 ! [i300, i301, i302, i303, i304, i305, i306, i307], w289 ! [i300, i301, i302, i303, i304, i305, i306, i307], w291 ! [i300, i301, i302, i303, i304, i305, i306, i307]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i310, i311, i312, i313, i314, i315, i316, i317] -> [ifF ((0 <=. i310 + i314 &&* 1 >. i310 + i314) &&* ((0 <=. i311 + i315 &&* 1 >. i311 + i315) &&* ((0 <=. 2 * i312 + i316 &&* 4 >. 2 * i312 + i316) &&* (0 <=. 2 * i313 + i317 &&* 4 >. 2 * i313 + i317)))) 0 1, i310, i311, i312, i313, i314, i315, i316, i317])))))))) ; w319 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w320 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w321 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w343 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w318 (\\[i322, i323, i324, i325, i326, i327, i328] -> [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w318 ! [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w318 ! [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i329, i330, i331, i332, i333, i334, i335] -> [ifF ((0 <=. i329 + i332 &&* 1 >. i329 + i332) &&* ((0 <=. i333 &&* 1 >. i333) &&* ((0 <=. i330 + i334 &&* 2 >. i330 + i334) &&* (0 <=. i331 + i335 &&* 2 >. i331 + i335)))) 0 1, i329, i330, i331, i332, i333, i334, i335])))) ; w344 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u677 (\\[i336, i337] -> [i336 + i337]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i338, i339, i340, i341, i342] -> [ifF ((0 <=. i338 + i339 &&* 1 >. i338 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i341 &&* 2 >. i341) &&* (0 <=. i342 &&* 2 >. i342)))) 0 1, i338, i339, i340, i341, i342])))))) ; w345 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w343 * w344) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v678))))))))))) ; w346 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w347 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w348 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w349 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w366 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i350, i351, i352, i353, i354, i355, i356, i357] -> [ifF (w345 ! [i350, i351, i352, i353, i354, i355, i356, i357, w346 ! [i350, i351, i352, i353, i354, i355, i356, i357], w347 ! [i350, i351, i352, i353, i354, i355, i356, i357], w348 ! [i350, i351, i352, i353, i354, i355, i356, i357], w349 ! [i350, i351, i352, i353, i354, i355, i356, i357]] <=. 0.0) 0 1]) ; w376 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w366 * rgather [1,1,1,1,1,1,2,2] w345 (\\[i358, i359, i360, i361, i362, i363, i364, i365] -> [i358, i359, i360, i361, i362, i363, i364, i365, w346 ! [i358, i359, i360, i361, i362, i363, i364, i365], w347 ! [i358, i359, i360, i361, i362, i363, i364, i365], w348 ! [i358, i359, i360, i361, i362, i363, i364, i365], w349 ! [i358, i359, i360, i361, i362, i363, i364, i365]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i368, i369, i370, i371, i372, i373, i374, i375] -> [ifF ((0 <=. i368 + i372 &&* 1 >. i368 + i372) &&* ((0 <=. i369 + i373 &&* 1 >. i369 + i373) &&* ((0 <=. 2 * i370 + i374 &&* 2 >. 2 * i370 + i374) &&* (0 <=. 2 * i371 + i375 &&* 2 >. 2 * i371 + i375)))) 0 1, i368, i369, i370, i371, i372, i373, i374, i375]) ; t381 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w376 (\\[i377, i378, i379, i380] -> [i377, i378, i379, i380, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w376 ! [i377, i378, i379, i380]))) 2) 2, remF (rmaxIndex (rreshape [4] (w376 ! [i377, i378, i379, i380]))) 2])))) ; m382 = rsum (rtranspose [2,1,0] (rreplicate 1 m679) * t381) + rtranspose [1,0] (rreplicate 1 v680) ; m385 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i383, i384] -> [ifF (m382 ! [i383, i384] <=. 0.0) 0 1]) ; m388 = m385 * rsum (rtranspose [1,2,0] (rreplicate 1 m681) * rtranspose [1,0] (rreplicate 1 m674)) ; u411 = rscatter [1,1,2,2] (w366 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] m679 (\\[i673] -> [i673, 0]) * rgather [1] m388 (\\[i670] -> [i670, 0]))))))) (\\[i390, i391, i392, i393] -> [i390, i391, i392, i393, 0, 0, remF (quotF (rmaxIndex (rgather [4] (w376 ! [i390, i391, i392, i393, 0, 0]) (\\[i663] -> [remF (quotF i663 2) 2, remF i663 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w376 ! [i390, i391, i392, i393, 0, 0]) (\\[i664] -> [remF (quotF i664 2) 2, remF i664 2]))) 2])) (\\[i394, i395, i396, i397, i398, i399, i400, i401] -> [ifF ((0 <=. i394 + i398 &&* 1 >. i394 + i398) &&* ((0 <=. i395 + i399 &&* 1 >. i395 + i399) &&* ((0 <=. 2 * i396 + i400 &&* 2 >. 2 * i396 + i400) &&* (0 <=. 2 * i397 + i401 &&* 2 >. 2 * i397 + i401)))) 0 1, i394, i395, i396, i397, i398, i399, i400, i401]) ! [0]) (\\[i403, i404, i405, i406, i407, i408, i409, i410] -> [w346 ! [i403, i404, i405, i406, i407, i408, i409, i410], w347 ! [i403, i404, i405, i406, i407, i408, i409, i410], w348 ! [i403, i404, i405, i406, i407, i408, i409, i410], w349 ! [i403, i404, i405, i406, i407, i408, i409, i410]]) ; u453 = rscatter [1,1,4,4] (w308 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w344 (\\[i647, i648, i649, i646] -> [i649, 0, i646, i647, i648]) * rgather [2,2,4,1] (u411 ! [0]) (\\[i652, i653, i654, i651] -> [i651, i652, i653])) (\\[i655, i656, i657, i658, i659, i660, i661, i662] -> [remF (quotF (i662 + 2 * i661 + 4 * i660 + 4 * i659 + 4 * i658 + 16 * i656 + 8 * i657) 8) 2, remF (quotF (i662 + 2 * i661 + 4 * i660 + 4 * i659 + 4 * i658 + 16 * i656 + 8 * i657) 4) 2, remF (i662 + 2 * i661 + 4 * i660 + 4 * i659 + 4 * i658 + 16 * i656 + 8 * i657) 4, i655]))) (\\[i421, i422, i423, i424, i425, i426, i427] -> [ifF ((0 <=. i421 + i424 &&* 1 >. i421 + i424) &&* ((0 <=. i425 &&* 1 >. i425) &&* ((0 <=. i422 + i426 &&* 2 >. i422 + i426) &&* (0 <=. i423 + i427 &&* 2 >. i423 + i427)))) 0 1, i421, i422, i423, i424, i425, i426, i427]) ! [0]) (\\[i429, i430, i431, i432, i433, i434, i435] -> [w319 ! [i429, i430, i431, i432, i433, i434, i435], i433, w320 ! [i429, i430, i431, i432, i433, i434, i435], w321 ! [i429, i430, i431, i432, i433, i434, i435], 0, 0, remF (quotF (rmaxIndex (rgather [4] (w318 ! [i429, i430, i431, i432, i433, i434, i435, w319 ! [i429, i430, i431, i432, i433, i434, i435], i433, w320 ! [i429, i430, i431, i432, i433, i434, i435], w321 ! [i429, i430, i431, i432, i433, i434, i435], 0, 0]) (\\[i636] -> [remF (quotF i636 2) 2, remF i636 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w318 ! [i429, i430, i431, i432, i433, i434, i435, w319 ! [i429, i430, i431, i432, i433, i434, i435], i433, w320 ! [i429, i430, i431, i432, i433, i434, i435], w321 ! [i429, i430, i431, i432, i433, i434, i435], 0, 0]) (\\[i637] -> [remF (quotF i637 2) 2, remF i637 2]))) 2])) (\\[i436, i437, i438, i439, i440, i441, i442, i443] -> [ifF ((0 <=. i436 + i440 &&* 1 >. i436 + i440) &&* ((0 <=. i437 + i441 &&* 1 >. i437 + i441) &&* ((0 <=. 2 * i438 + i442 &&* 4 >. 2 * i438 + i442) &&* (0 <=. 2 * i439 + i443 &&* 4 >. 2 * i439 + i443)))) 0 1, i436, i437, i438, i439, i440, i441, i442, i443]) ! [0]) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [w286 ! [i445, i446, i447, i448, i449, i450, i451, i452], w287 ! [i445, i446, i447, i448, i449, i450, i451, i452], w289 ! [i445, i446, i447, i448, i449, i450, i451, i452], w291 ! [i445, i446, i447, i448, i449, i450, i451, i452]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w283 (\\[i489, i486] -> [i489, i486, 0]) * rreplicate 4 (rgather [1,4,4] u453 (\\[i491] -> [i491, 0]))) (\\[i549, i550, i551, i552, i553, i554, i555, i556] -> [remF (i556 + 2 * i555 + 4 * i554 + 4 * i552 + 4 * i553) 4, i549, i550, i551]))))) (\\[i454, i455, i456, i457, i458] -> [ifF ((0 <=. i454 + i455 &&* 1 >. i454 + i455) &&* ((0 <=. i456 &&* 1 >. i456) &&* ((0 <=. i457 &&* 2 >. i457) &&* (0 <=. i458 &&* 2 >. i458)))) 0 1, i454, i455, i456, i457, i458]) ! [0]) (\\[i460, i461] -> [i460 + i461]), rsum (rsum (rsum (rtranspose [0,2,3,1] u453))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w343 (\\[i566, i563] -> [i566, i563, 0]) * rreplicate 4 (rgather [1,2,2] u411 (\\[i568] -> [i568, 0]))) (\\[i626, i627, i628, i629, i630, i631, i632, i633] -> [remF (i633 + 2 * i632 + 4 * i631 + 4 * i629 + 4 * i630) 4, i626, i627, i628]))))) (\\[i413, i414, i415, i416, i417] -> [ifF ((0 <=. i413 + i414 &&* 1 >. i413 + i414) &&* ((0 <=. i415 &&* 1 >. i415) &&* ((0 <=. i416 &&* 2 >. i416) &&* (0 <=. i417 &&* 2 >. i417)))) 0 1, i413, i414, i415, i416, i417]) ! [0]) (\\[i419, i420] -> [i419 + i420]), rsum (rsum (rsum (rtranspose [0,2,3,1] u411))), rsum (rtranspose [2,1,0] t381 * rtranspose [2,1,0] (rreplicate 1 m388)), rsum (rtranspose [1,0] m388), rsum (rtranspose [2,0,1] (rreplicate 10 (m385 * m382)) * rtranspose [2,1,0] (rreplicate 1 m674)), rsum (rgather [1,10] m674 (\\[i634, i635] -> [i635, i634]))]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\u684 v685 u686 v687 m688 v689 m690 v691 -> let w285 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i269, i270, i271, i272, i273, i274, i275] -> [ifF ((0 <=. i269 + i272 &&* 1 >. i269 + i272) &&* ((0 <=. i273 &&* 1 >. i273) &&* ((0 <=. i270 + i274 &&* 4 >. i270 + i274) &&* (0 <=. i271 + i275 &&* 4 >. i271 + i275)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u684 (\\[i276, i277] -> [i276 + i277]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i278, i279, i280, i281, i282] -> [ifF ((0 <=. i278 + i279 &&* 1 >. i278 + i279) &&* ((0 <=. i280 &&* 1 >. i280) &&* ((0 <=. i281 &&* 2 >. i281) &&* (0 <=. i282 &&* 2 >. i282)))) 0 1, i278, i279, i280, i281, i282]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v685))))))))))) ; w286 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w287 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w289 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w291 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w318 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i292, i293, i294, i295, i296, i297, i298, i299] -> [ifF (w285 ! [i292, i293, i294, i295, i296, i297, i298, i299, w286 ! [i292, i293, i294, i295, i296, i297, i298, i299], w287 ! [i292, i293, i294, i295, i296, i297, i298, i299], w289 ! [i292, i293, i294, i295, i296, i297, i298, i299], w291 ! [i292, i293, i294, i295, i296, i297, i298, i299]] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w285 (\\[i300, i301, i302, i303, i304, i305, i306, i307] -> [i300, i301, i302, i303, i304, i305, i306, i307, w286 ! [i300, i301, i302, i303, i304, i305, i306, i307], w287 ! [i300, i301, i302, i303, i304, i305, i306, i307], w289 ! [i300, i301, i302, i303, i304, i305, i306, i307], w291 ! [i300, i301, i302, i303, i304, i305, i306, i307]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i310, i311, i312, i313, i314, i315, i316, i317] -> [ifF ((0 <=. i310 + i314 &&* 1 >. i310 + i314) &&* ((0 <=. i311 + i315 &&* 1 >. i311 + i315) &&* ((0 <=. 2 * i312 + i316 &&* 4 >. 2 * i312 + i316) &&* (0 <=. 2 * i313 + i317 &&* 4 >. 2 * i313 + i317)))) 0 1, i310, i311, i312, i313, i314, i315, i316, i317])))))))) ; w319 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w320 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w321 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w345 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w318 (\\[i322, i323, i324, i325, i326, i327, i328] -> [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w318 ! [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w318 ! [i322, i323, i324, i325, i326, i327, i328, w319 ! [i322, i323, i324, i325, i326, i327, i328], i326, w320 ! [i322, i323, i324, i325, i326, i327, i328], w321 ! [i322, i323, i324, i325, i326, i327, i328]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i329, i330, i331, i332, i333, i334, i335] -> [ifF ((0 <=. i329 + i332 &&* 1 >. i329 + i332) &&* ((0 <=. i333 &&* 1 >. i333) &&* ((0 <=. i330 + i334 &&* 2 >. i330 + i334) &&* (0 <=. i331 + i335 &&* 2 >. i331 + i335)))) 0 1, i329, i330, i331, i332, i333, i334, i335])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u686 (\\[i336, i337] -> [i336 + i337]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i338, i339, i340, i341, i342] -> [ifF ((0 <=. i338 + i339 &&* 1 >. i338 + i339) &&* ((0 <=. i340 &&* 1 >. i340) &&* ((0 <=. i341 &&* 2 >. i341) &&* (0 <=. i342 &&* 2 >. i342)))) 0 1, i338, i339, i340, i341, i342]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v687))))))))))) ; w346 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w347 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w348 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w349 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w376 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i350, i351, i352, i353, i354, i355, i356, i357] -> [ifF (w345 ! [i350, i351, i352, i353, i354, i355, i356, i357, w346 ! [i350, i351, i352, i353, i354, i355, i356, i357], w347 ! [i350, i351, i352, i353, i354, i355, i356, i357], w348 ! [i350, i351, i352, i353, i354, i355, i356, i357], w349 ! [i350, i351, i352, i353, i354, i355, i356, i357]] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w345 (\\[i358, i359, i360, i361, i362, i363, i364, i365] -> [i358, i359, i360, i361, i362, i363, i364, i365, w346 ! [i358, i359, i360, i361, i362, i363, i364, i365], w347 ! [i358, i359, i360, i361, i362, i363, i364, i365], w348 ! [i358, i359, i360, i361, i362, i363, i364, i365], w349 ! [i358, i359, i360, i361, i362, i363, i364, i365]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i368, i369, i370, i371, i372, i373, i374, i375] -> [ifF ((0 <=. i368 + i372 &&* 1 >. i368 + i372) &&* ((0 <=. i369 + i373 &&* 1 >. i369 + i373) &&* ((0 <=. 2 * i370 + i374 &&* 2 >. 2 * i370 + i374) &&* (0 <=. 2 * i371 + i375 &&* 2 >. 2 * i371 + i375)))) 0 1, i368, i369, i370, i371, i372, i373, i374, i375]) ; m382 = rsum (rtranspose [2,1,0] (rreplicate 1 m688) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w376 (\\[i377, i378, i379, i380] -> [i377, i378, i379, i380, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w376 ! [i377, i378, i379, i380]))) 2) 2, remF (rmaxIndex (rreshape [4] (w376 ! [i377, i378, i379, i380]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v689) in [rsum (rtranspose [2,1,0] (rreplicate 1 m690) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i383, i384] -> [ifF (m382 ! [i383, i384] <=. 0.0) 0 1]) * m382))) + rtranspose [1,0] (rreplicate 1 v691)]"
