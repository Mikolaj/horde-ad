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
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))

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
       (_, _, var, hVector2)
         <- funToAstRevIO $ FTKUntyped $ voidFromHVector hVectorInit
       let testDataR = packBatchR testData
       (varGlyph, _, astGlyph) <-
         funToAstIO
           (FTKR $ miniBatchSize :$: sizeMnistHeightInt :$: sizeMnistWidthInt :$: ZSR)
           id
       (varLabel, _, astLabel) <-
         funToAstIO (FTKR $ miniBatchSize :$: sizeMnistLabelInt :$: ZSR) id
       let ast :: AstRanked FullSpan r 0
           ast = MnistCnnRanked2.convMnistLossFusedR
                   miniBatchSize (AstRanked astGlyph, AstRanked astLabel)
                   (parseHVector (fromDValue valsInit)
                                 (dunHVector $ unHVectorPseudoTensor (rankedY (stensorKind @TKUntyped) hVector2)))
           runBatch :: (HVector ORArray, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (HVector ORArray, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> HVector (ADVal ORArray)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = extendEnv var (HVectorPseudoTensor varInputs) emptyEnv
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
           dataInit = case chunksOf miniBatchSize testData of
             d : _ -> let (dglyph, dlabel) = packBatchR d
                      in ( FlipR $ Nested.rfromOrthotope SNat dglyph
                         , FlipR $ Nested.rfromOrthotope SNat dlabel )
             [] -> error "empty test data"
           f = \ (pars, (glyphR, labelR)) ->
             MnistCnnRanked2.convMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           (artRaw, _) = revArtifactAdapt False f (valsInit, dataInit)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchR r] -> (HVector ORArray, StateAdam)
              -> (HVector ORArray, StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat glyph
                 labelD = DynamicRanked $ rconst $ Nested.rfromOrthotope SNat label
                 parametersAndInput =
                   HVectorPseudoTensor
                   $ V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientHVector =
                   unHVectorPseudoTensor
                   $ fst $ revEvalArtifact art parametersAndInput Nothing
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
                       (7 :: AstTensor AstMethodLet PrimalSpan (TKR Double 0))
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
    @?= "\\m395 u470 v471 u472 v473 m474 v475 m476 v477 -> let w291 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i277, i278, i279, i280, i281, i282, i283] -> [ifF ((0 <=. i277 + i280 &&* 1 >. i277 + i280) &&* ((0 <=. i281 &&* 1 >. i281) &&* ((0 <=. i278 + i282 &&* 4 >. i278 + i282) &&* (0 <=. i279 + i283 &&* 4 >. i279 + i283)))) 0 1])))) ; w292 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u470 (\\[i284, i285] -> [i284 + i285]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i286, i287, i288, i289, i290] -> [ifF ((0 <=. i286 + i287 &&* 1 >. i286 + i287) &&* ((0 <=. i288 &&* 1 >. i288) &&* ((0 <=. i289 &&* 2 >. i289) &&* (0 <=. i290 &&* 2 >. i290)))) 0 1, i286, i287, i288, i289, i290])))))) ; w293 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w291 * w292) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v471))))))))))) ; w294 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w295 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v296 = rconst (rfromListLinear [2] [0,1]) ; w297 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v296)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v298 = rconst (rfromListLinear [2] [0,1]) ; w299 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v298)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w316 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i300, i301, i302, i303, i304, i305, i306, i307] -> [ifF (w293 ! [i300, i301, i302, i303, i304, i305, i306, i307, w294 ! [i300, i301, i302, i303, i304, i305, i306, i307], w295 ! [i300, i301, i302, i303, i304, i305, i306, i307], w297 ! [i300, i301, i302, i303, i304, i305, i306, i307], w299 ! [i300, i301, i302, i303, i304, i305, i306, i307]] <=. 0.0) 0 1]) ; w317 = rgather [1,1,2,2,1,1,2,2] w293 (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [i308, i309, i310, i311, i312, i313, i314, i315, w294 ! [i308, i309, i310, i311, i312, i313, i314, i315], w295 ! [i308, i309, i310, i311, i312, i313, i314, i315], w297 ! [i308, i309, i310, i311, i312, i313, i314, i315], w299 ! [i308, i309, i310, i311, i312, i313, i314, i315]]) ; w326 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w316 * w317, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i318, i319, i320, i321, i322, i323, i324, i325] -> [ifF ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. i319 + i323 &&* 1 >. i319 + i323) &&* ((0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324) &&* (0 <=. 2 * i321 + i325 &&* 4 >. 2 * i321 + i325)))) 0 1, i318, i319, i320, i321, i322, i323, i324, i325])))))))) ; w327 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w328 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w329 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w351 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w326 (\\[i330, i331, i332, i333, i334, i335, i336] -> [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w326 ! [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w326 ! [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i337, i338, i339, i340, i341, i342, i343] -> [ifF ((0 <=. i337 + i340 &&* 1 >. i337 + i340) &&* ((0 <=. i341 &&* 1 >. i341) &&* ((0 <=. i338 + i342 &&* 2 >. i338 + i342) &&* (0 <=. i339 + i343 &&* 2 >. i339 + i343)))) 0 1, i337, i338, i339, i340, i341, i342, i343])))) ; w352 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u472 (\\[i344, i345] -> [i344 + i345]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i346, i347, i348, i349, i350] -> [ifF ((0 <=. i346 + i347 &&* 1 >. i346 + i347) &&* ((0 <=. i348 &&* 1 >. i348) &&* ((0 <=. i349 &&* 2 >. i349) &&* (0 <=. i350 &&* 2 >. i350)))) 0 1, i346, i347, i348, i349, i350])))))) ; w353 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w351 * w352) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v473))))))))))) ; w354 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w355 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w356 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w357 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w374 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i358, i359, i360, i361, i362, i363, i364, i365] -> [ifF (w353 ! [i358, i359, i360, i361, i362, i363, i364, i365, w354 ! [i358, i359, i360, i361, i362, i363, i364, i365], w355 ! [i358, i359, i360, i361, i362, i363, i364, i365], w356 ! [i358, i359, i360, i361, i362, i363, i364, i365], w357 ! [i358, i359, i360, i361, i362, i363, i364, i365]] <=. 0.0) 0 1]) ; w375 = rgather [1,1,1,1,1,1,2,2] w353 (\\[i366, i367, i368, i369, i370, i371, i372, i373] -> [i366, i367, i368, i369, i370, i371, i372, i373, w354 ! [i366, i367, i368, i369, i370, i371, i372, i373], w355 ! [i366, i367, i368, i369, i370, i371, i372, i373], w356 ! [i366, i367, i368, i369, i370, i371, i372, i373], w357 ! [i366, i367, i368, i369, i370, i371, i372, i373]]) ; w384 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w374 * w375, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i376, i377, i378, i379, i380, i381, i382, i383] -> [ifF ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. i377 + i381 &&* 1 >. i377 + i381) &&* ((0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382) &&* (0 <=. 2 * i379 + i383 &&* 2 >. 2 * i379 + i383)))) 0 1, i376, i377, i378, i379, i380, i381, i382, i383]) ; t389 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w384 (\\[i385, i386, i387, i388] -> [i385, i386, i387, i388, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w384 ! [i385, i386, i387, i388]))) 2) 2, remF (rmaxIndex (rreshape [4] (w384 ! [i385, i386, i387, i388]))) 2]))))) ; m390 = rsum (rtranspose [2,1,0] (rreplicate 1 m474) * t389) + rtranspose [1,0] (rreplicate 1 v475) ; m393 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i391, i392] -> [ifF (m390 ! [i391, i392] <=. 0.0) 0 1]) ; t394 = rtranspose [1,0] (rreplicate 10 (m393 * m390)) ; m396 = m393 * rsum (rtranspose [1,2,0] (rreplicate 1 m476) * rtranspose [1,0] (rreplicate 1 m395)) ; w410 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rsum (rtranspose [1,0] (rreplicate 1 m474) * rtranspose [1,2,0] (rreplicate 1 m396)))) (\\[i398, i399, i400, i401] -> [i398, i399, i400, i401, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w384 ! [i398, i399, i400, i401]))) 2) 2, remF (rmaxIndex (rreshape [4] (w384 ! [i398, i399, i400, i401]))) 2])) (\\[i402, i403, i404, i405, i406, i407, i408, i409] -> [ifF ((0 <=. i402 + i406 &&* 1 >. i402 + i406) &&* ((0 <=. i403 + i407 &&* 1 >. i403 + i407) &&* ((0 <=. 2 * i404 + i408 &&* 2 >. 2 * i404 + i408) &&* (0 <=. 2 * i405 + i409 &&* 2 >. 2 * i405 + i409)))) 0 1, i402, i403, i404, i405, i406, i407, i408, i409]) ; u419 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w374 * w410 ! [0]) (\\[i411, i412, i413, i414, i415, i416, i417, i418] -> [i411, i412, i413, i414, i415, i416, i417, i418, w354 ! [i411, i412, i413, i414, i415, i416, i417, i418], w355 ! [i411, i412, i413, i414, i415, i416, i417, i418], w356 ! [i411, i412, i413, i414, i415, i416, i417, i418], w357 ! [i411, i412, i413, i414, i415, i416, i417, i418]]))))))))) ; w426 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] w351 * rtranspose [1,3,4,2,0] (rreplicate 4 u419)))))) (\\[i421, i422, i423, i424, i425] -> [ifF ((0 <=. i421 + i422 &&* 1 >. i421 + i422) &&* ((0 <=. i423 &&* 1 >. i423) &&* ((0 <=. i424 &&* 2 >. i424) &&* (0 <=. i425 &&* 2 >. i425)))) 0 1, i421, i422, i423, i424, i425]) ; w436 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] w352 * rtranspose [2,1,3,4,0] (rreplicate 4 u419)))) (\\[i429, i430, i431, i432, i433, i434, i435] -> [ifF ((0 <=. i429 + i432 &&* 1 >. i429 + i432) &&* ((0 <=. i433 &&* 1 >. i433) &&* ((0 <=. i430 + i434 &&* 2 >. i430 + i434) &&* (0 <=. i431 + i435 &&* 2 >. i431 + i435)))) 0 1, i429, i430, i431, i432, i433, i434, i435]) ; w452 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w436 ! [0]) (\\[i437, i438, i439, i440, i441, i442, i443] -> [i437, i438, i439, i440, i441, i442, i443, w327 ! [i437, i438, i439, i440, i441, i442, i443], i441, w328 ! [i437, i438, i439, i440, i441, i442, i443], w329 ! [i437, i438, i439, i440, i441, i442, i443], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w326 ! [i437, i438, i439, i440, i441, i442, i443, w327 ! [i437, i438, i439, i440, i441, i442, i443], i441, w328 ! [i437, i438, i439, i440, i441, i442, i443], w329 ! [i437, i438, i439, i440, i441, i442, i443]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w326 ! [i437, i438, i439, i440, i441, i442, i443, w327 ! [i437, i438, i439, i440, i441, i442, i443], i441, w328 ! [i437, i438, i439, i440, i441, i442, i443], w329 ! [i437, i438, i439, i440, i441, i442, i443]]))) 2]))))))))) (\\[i444, i445, i446, i447, i448, i449, i450, i451] -> [ifF ((0 <=. i444 + i448 &&* 1 >. i444 + i448) &&* ((0 <=. i445 + i449 &&* 1 >. i445 + i449) &&* ((0 <=. 2 * i446 + i450 &&* 4 >. 2 * i446 + i450) &&* (0 <=. 2 * i447 + i451 &&* 4 >. 2 * i447 + i451)))) 0 1, i444, i445, i446, i447, i448, i449, i450, i451]) ; u461 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w316 * w452 ! [0]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [i453, i454, i455, i456, i457, i458, i459, i460, w294 ! [i453, i454, i455, i456, i457, i458, i459, i460], w295 ! [i453, i454, i455, i456, i457, i458, i459, i460], w297 ! [i453, i454, i455, i456, i457, i458, i459, i460], w299 ! [i453, i454, i455, i456, i457, i458, i459, i460]]))))))))) ; w467 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w291 * rreplicate 4 u461)))))) (\\[i462, i463, i464, i465, i466] -> [ifF ((0 <=. i462 + i463 &&* 1 >. i462 + i463) &&* ((0 <=. i464 &&* 1 >. i464) &&* ((0 <=. i465 &&* 2 >. i465) &&* (0 <=. i466 &&* 2 >. i466)))) 0 1, i462, i463, i464, i465, i466]) in [rscatter [1,1,2,2] (w467 ! [0]) (\\[i468, i469] -> [i468 + i469]), rsum (rsum (rsum (rtranspose [0,2,3,1] u461))), rscatter [1,1,2,2] (w426 ! [0]) (\\[i427, i428] -> [i427 + i428]), rsum (rsum (rsum (rtranspose [0,2,3,1] u419))), rsum (rtranspose [2,1,0] t389 * rtranspose [2,1,0] (rreplicate 1 m396)), rsum (rtranspose [1,0] m396), rsum (rtranspose [2,1,0] (t394 * rreplicate 1 m395)), rsum (rtranspose [1,0] m395)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\u478 v479 u480 v481 m482 v483 m484 v485 -> let w291 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i277, i278, i279, i280, i281, i282, i283] -> [ifF ((0 <=. i277 + i280 &&* 1 >. i277 + i280) &&* ((0 <=. i281 &&* 1 >. i281) &&* ((0 <=. i278 + i282 &&* 4 >. i278 + i282) &&* (0 <=. i279 + i283 &&* 4 >. i279 + i283)))) 0 1])))) ; w292 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u478 (\\[i284, i285] -> [i284 + i285]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i286, i287, i288, i289, i290] -> [ifF ((0 <=. i286 + i287 &&* 1 >. i286 + i287) &&* ((0 <=. i288 &&* 1 >. i288) &&* ((0 <=. i289 &&* 2 >. i289) &&* (0 <=. i290 &&* 2 >. i290)))) 0 1, i286, i287, i288, i289, i290])))))) ; w293 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w291 * w292) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v479))))))))))) ; w294 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w295 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v296 = rconst (rfromListLinear [2] [0,1]) ; w297 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v296)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v298 = rconst (rfromListLinear [2] [0,1]) ; w299 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v298)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w316 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i300, i301, i302, i303, i304, i305, i306, i307] -> [ifF (w293 ! [i300, i301, i302, i303, i304, i305, i306, i307, w294 ! [i300, i301, i302, i303, i304, i305, i306, i307], w295 ! [i300, i301, i302, i303, i304, i305, i306, i307], w297 ! [i300, i301, i302, i303, i304, i305, i306, i307], w299 ! [i300, i301, i302, i303, i304, i305, i306, i307]] <=. 0.0) 0 1]) ; w317 = rgather [1,1,2,2,1,1,2,2] w293 (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [i308, i309, i310, i311, i312, i313, i314, i315, w294 ! [i308, i309, i310, i311, i312, i313, i314, i315], w295 ! [i308, i309, i310, i311, i312, i313, i314, i315], w297 ! [i308, i309, i310, i311, i312, i313, i314, i315], w299 ! [i308, i309, i310, i311, i312, i313, i314, i315]]) ; w326 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w316 * w317, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i318, i319, i320, i321, i322, i323, i324, i325] -> [ifF ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. i319 + i323 &&* 1 >. i319 + i323) &&* ((0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324) &&* (0 <=. 2 * i321 + i325 &&* 4 >. 2 * i321 + i325)))) 0 1, i318, i319, i320, i321, i322, i323, i324, i325])))))))) ; w327 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w328 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w329 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w351 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w326 (\\[i330, i331, i332, i333, i334, i335, i336] -> [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w326 ! [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w326 ! [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i337, i338, i339, i340, i341, i342, i343] -> [ifF ((0 <=. i337 + i340 &&* 1 >. i337 + i340) &&* ((0 <=. i341 &&* 1 >. i341) &&* ((0 <=. i338 + i342 &&* 2 >. i338 + i342) &&* (0 <=. i339 + i343 &&* 2 >. i339 + i343)))) 0 1, i337, i338, i339, i340, i341, i342, i343])))) ; w352 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u480 (\\[i344, i345] -> [i344 + i345]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i346, i347, i348, i349, i350] -> [ifF ((0 <=. i346 + i347 &&* 1 >. i346 + i347) &&* ((0 <=. i348 &&* 1 >. i348) &&* ((0 <=. i349 &&* 2 >. i349) &&* (0 <=. i350 &&* 2 >. i350)))) 0 1, i346, i347, i348, i349, i350])))))) ; w353 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w351 * w352) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v481))))))))))) ; w354 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w355 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w356 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w357 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w374 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i358, i359, i360, i361, i362, i363, i364, i365] -> [ifF (w353 ! [i358, i359, i360, i361, i362, i363, i364, i365, w354 ! [i358, i359, i360, i361, i362, i363, i364, i365], w355 ! [i358, i359, i360, i361, i362, i363, i364, i365], w356 ! [i358, i359, i360, i361, i362, i363, i364, i365], w357 ! [i358, i359, i360, i361, i362, i363, i364, i365]] <=. 0.0) 0 1]) ; w375 = rgather [1,1,1,1,1,1,2,2] w353 (\\[i366, i367, i368, i369, i370, i371, i372, i373] -> [i366, i367, i368, i369, i370, i371, i372, i373, w354 ! [i366, i367, i368, i369, i370, i371, i372, i373], w355 ! [i366, i367, i368, i369, i370, i371, i372, i373], w356 ! [i366, i367, i368, i369, i370, i371, i372, i373], w357 ! [i366, i367, i368, i369, i370, i371, i372, i373]]) ; w384 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w374 * w375, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i376, i377, i378, i379, i380, i381, i382, i383] -> [ifF ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. i377 + i381 &&* 1 >. i377 + i381) &&* ((0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382) &&* (0 <=. 2 * i379 + i383 &&* 2 >. 2 * i379 + i383)))) 0 1, i376, i377, i378, i379, i380, i381, i382, i383]) ; t389 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w384 (\\[i385, i386, i387, i388] -> [i385, i386, i387, i388, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w384 ! [i385, i386, i387, i388]))) 2) 2, remF (rmaxIndex (rreshape [4] (w384 ! [i385, i386, i387, i388]))) 2]))))) ; m390 = rsum (rtranspose [2,1,0] (rreplicate 1 m482) * t389) + rtranspose [1,0] (rreplicate 1 v483) ; m393 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i391, i392] -> [ifF (m390 ! [i391, i392] <=. 0.0) 0 1]) ; t394 = rtranspose [1,0] (rreplicate 10 (m393 * m390)) in rsum (rtranspose [2,1,0] (rreplicate 1 m484) * t394) + rtranspose [1,0] (rreplicate 1 v485)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m395 u678 v679 u680 v681 m682 v683 m684 v685 -> let w291 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i277, i278, i279, i280, i281, i282, i283] -> [ifF ((0 <=. i277 + i280 &&* 1 >. i277 + i280) &&* ((0 <=. i281 &&* 1 >. i281) &&* ((0 <=. i278 + i282 &&* 4 >. i278 + i282) &&* (0 <=. i279 + i283 &&* 4 >. i279 + i283)))) 0 1])))) ; w293 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w291 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u678 (\\[i284, i285] -> [i284 + i285]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i286, i287, i288, i289, i290] -> [ifF ((0 <=. i286 + i287 &&* 1 >. i286 + i287) &&* ((0 <=. i288 &&* 1 >. i288) &&* ((0 <=. i289 &&* 2 >. i289) &&* (0 <=. i290 &&* 2 >. i290)))) 0 1, i286, i287, i288, i289, i290]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v679))))))))))) ; w294 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w295 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w297 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w299 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w316 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i300, i301, i302, i303, i304, i305, i306, i307] -> [ifF (w293 ! [i300, i301, i302, i303, i304, i305, i306, i307, w294 ! [i300, i301, i302, i303, i304, i305, i306, i307], w295 ! [i300, i301, i302, i303, i304, i305, i306, i307], w297 ! [i300, i301, i302, i303, i304, i305, i306, i307], w299 ! [i300, i301, i302, i303, i304, i305, i306, i307]] <=. 0.0) 0 1]) ; w326 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w316 * rgather [1,1,2,2,1,1,2,2] w293 (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [i308, i309, i310, i311, i312, i313, i314, i315, w294 ! [i308, i309, i310, i311, i312, i313, i314, i315], w295 ! [i308, i309, i310, i311, i312, i313, i314, i315], w297 ! [i308, i309, i310, i311, i312, i313, i314, i315], w299 ! [i308, i309, i310, i311, i312, i313, i314, i315]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i318, i319, i320, i321, i322, i323, i324, i325] -> [ifF ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. i319 + i323 &&* 1 >. i319 + i323) &&* ((0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324) &&* (0 <=. 2 * i321 + i325 &&* 4 >. 2 * i321 + i325)))) 0 1, i318, i319, i320, i321, i322, i323, i324, i325])))))))) ; w327 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w328 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w329 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w351 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w326 (\\[i330, i331, i332, i333, i334, i335, i336] -> [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w326 ! [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w326 ! [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i337, i338, i339, i340, i341, i342, i343] -> [ifF ((0 <=. i337 + i340 &&* 1 >. i337 + i340) &&* ((0 <=. i341 &&* 1 >. i341) &&* ((0 <=. i338 + i342 &&* 2 >. i338 + i342) &&* (0 <=. i339 + i343 &&* 2 >. i339 + i343)))) 0 1, i337, i338, i339, i340, i341, i342, i343])))) ; w352 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u680 (\\[i344, i345] -> [i344 + i345]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i346, i347, i348, i349, i350] -> [ifF ((0 <=. i346 + i347 &&* 1 >. i346 + i347) &&* ((0 <=. i348 &&* 1 >. i348) &&* ((0 <=. i349 &&* 2 >. i349) &&* (0 <=. i350 &&* 2 >. i350)))) 0 1, i346, i347, i348, i349, i350])))))) ; w353 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w351 * w352) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v681))))))))))) ; w354 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w355 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w356 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w357 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w374 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i358, i359, i360, i361, i362, i363, i364, i365] -> [ifF (w353 ! [i358, i359, i360, i361, i362, i363, i364, i365, w354 ! [i358, i359, i360, i361, i362, i363, i364, i365], w355 ! [i358, i359, i360, i361, i362, i363, i364, i365], w356 ! [i358, i359, i360, i361, i362, i363, i364, i365], w357 ! [i358, i359, i360, i361, i362, i363, i364, i365]] <=. 0.0) 0 1]) ; w384 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w374 * rgather [1,1,1,1,1,1,2,2] w353 (\\[i366, i367, i368, i369, i370, i371, i372, i373] -> [i366, i367, i368, i369, i370, i371, i372, i373, w354 ! [i366, i367, i368, i369, i370, i371, i372, i373], w355 ! [i366, i367, i368, i369, i370, i371, i372, i373], w356 ! [i366, i367, i368, i369, i370, i371, i372, i373], w357 ! [i366, i367, i368, i369, i370, i371, i372, i373]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i376, i377, i378, i379, i380, i381, i382, i383] -> [ifF ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. i377 + i381 &&* 1 >. i377 + i381) &&* ((0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382) &&* (0 <=. 2 * i379 + i383 &&* 2 >. 2 * i379 + i383)))) 0 1, i376, i377, i378, i379, i380, i381, i382, i383]) ; t389 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w384 (\\[i385, i386, i387, i388] -> [i385, i386, i387, i388, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w384 ! [i385, i386, i387, i388]))) 2) 2, remF (rmaxIndex (rreshape [4] (w384 ! [i385, i386, i387, i388]))) 2])))) ; m390 = rsum (rtranspose [2,1,0] (rreplicate 1 m682) * t389) + rtranspose [1,0] (rreplicate 1 v683) ; m393 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i391, i392] -> [ifF (m390 ! [i391, i392] <=. 0.0) 0 1]) ; m396 = m393 * rsum (rtranspose [1,2,0] (rreplicate 1 m684) * rtranspose [1,0] (rreplicate 1 m395)) ; u419 = rscatter [1,1,2,2] (w374 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] m682 (\\[i677] -> [i677, 0]) * rgather [1] m396 (\\[i674] -> [i674, 0]))))))) (\\[i398, i399, i400, i401] -> [i398, i399, i400, i401, 0, 0, remF (quotF (rmaxIndex (rgather [4] (w384 ! [i398, i399, i400, i401, 0, 0]) (\\[i667] -> [remF (quotF i667 2) 2, remF i667 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w384 ! [i398, i399, i400, i401, 0, 0]) (\\[i668] -> [remF (quotF i668 2) 2, remF i668 2]))) 2])) (\\[i402, i403, i404, i405, i406, i407, i408, i409] -> [ifF ((0 <=. i402 + i406 &&* 1 >. i402 + i406) &&* ((0 <=. i403 + i407 &&* 1 >. i403 + i407) &&* ((0 <=. 2 * i404 + i408 &&* 2 >. 2 * i404 + i408) &&* (0 <=. 2 * i405 + i409 &&* 2 >. 2 * i405 + i409)))) 0 1, i402, i403, i404, i405, i406, i407, i408, i409]) ! [0]) (\\[i411, i412, i413, i414, i415, i416, i417, i418] -> [w354 ! [i411, i412, i413, i414, i415, i416, i417, i418], w355 ! [i411, i412, i413, i414, i415, i416, i417, i418], w356 ! [i411, i412, i413, i414, i415, i416, i417, i418], w357 ! [i411, i412, i413, i414, i415, i416, i417, i418]]) ; u461 = rscatter [1,1,4,4] (w316 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w352 (\\[i651, i652, i653, i650] -> [i653, 0, i650, i651, i652]) * rgather [2,2,4,1] (u419 ! [0]) (\\[i656, i657, i658, i655] -> [i655, i656, i657])) (\\[i659, i660, i661, i662, i663, i664, i665, i666] -> [remF (quotF (i666 + 2 * i665 + 4 * i664 + 4 * i663 + 4 * i662 + 16 * i660 + 8 * i661) 8) 2, remF (quotF (i666 + 2 * i665 + 4 * i664 + 4 * i663 + 4 * i662 + 16 * i660 + 8 * i661) 4) 2, remF (i666 + 2 * i665 + 4 * i664 + 4 * i663 + 4 * i662 + 16 * i660 + 8 * i661) 4, i659]))) (\\[i429, i430, i431, i432, i433, i434, i435] -> [ifF ((0 <=. i429 + i432 &&* 1 >. i429 + i432) &&* ((0 <=. i433 &&* 1 >. i433) &&* ((0 <=. i430 + i434 &&* 2 >. i430 + i434) &&* (0 <=. i431 + i435 &&* 2 >. i431 + i435)))) 0 1, i429, i430, i431, i432, i433, i434, i435]) ! [0]) (\\[i437, i438, i439, i440, i441, i442, i443] -> [w327 ! [i437, i438, i439, i440, i441, i442, i443], i441, w328 ! [i437, i438, i439, i440, i441, i442, i443], w329 ! [i437, i438, i439, i440, i441, i442, i443], 0, 0, remF (quotF (rmaxIndex (rgather [4] (w326 ! [i437, i438, i439, i440, i441, i442, i443, w327 ! [i437, i438, i439, i440, i441, i442, i443], i441, w328 ! [i437, i438, i439, i440, i441, i442, i443], w329 ! [i437, i438, i439, i440, i441, i442, i443], 0, 0]) (\\[i640] -> [remF (quotF i640 2) 2, remF i640 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w326 ! [i437, i438, i439, i440, i441, i442, i443, w327 ! [i437, i438, i439, i440, i441, i442, i443], i441, w328 ! [i437, i438, i439, i440, i441, i442, i443], w329 ! [i437, i438, i439, i440, i441, i442, i443], 0, 0]) (\\[i641] -> [remF (quotF i641 2) 2, remF i641 2]))) 2])) (\\[i444, i445, i446, i447, i448, i449, i450, i451] -> [ifF ((0 <=. i444 + i448 &&* 1 >. i444 + i448) &&* ((0 <=. i445 + i449 &&* 1 >. i445 + i449) &&* ((0 <=. 2 * i446 + i450 &&* 4 >. 2 * i446 + i450) &&* (0 <=. 2 * i447 + i451 &&* 4 >. 2 * i447 + i451)))) 0 1, i444, i445, i446, i447, i448, i449, i450, i451]) ! [0]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [w294 ! [i453, i454, i455, i456, i457, i458, i459, i460], w295 ! [i453, i454, i455, i456, i457, i458, i459, i460], w297 ! [i453, i454, i455, i456, i457, i458, i459, i460], w299 ! [i453, i454, i455, i456, i457, i458, i459, i460]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w291 (\\[i495, i492] -> [i495, i492, 0]) * rreplicate 4 (rgather [1,4,4] u461 (\\[i497] -> [i497, 0]))) (\\[i555, i556, i557, i558, i559, i560, i561, i562] -> [remF (i562 + 2 * i561 + 4 * i560 + 4 * i558 + 4 * i559) 4, i555, i556, i557]))))) (\\[i462, i463, i464, i465, i466] -> [ifF ((0 <=. i462 + i463 &&* 1 >. i462 + i463) &&* ((0 <=. i464 &&* 1 >. i464) &&* ((0 <=. i465 &&* 2 >. i465) &&* (0 <=. i466 &&* 2 >. i466)))) 0 1, i462, i463, i464, i465, i466]) ! [0]) (\\[i468, i469] -> [i468 + i469]), rsum (rsum (rsum (rtranspose [0,2,3,1] u461))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w351 (\\[i572, i569] -> [i572, i569, 0]) * rreplicate 4 (rgather [1,2,2] u419 (\\[i574] -> [i574, 0]))) (\\[i632, i633, i634, i635, i636, i637, i638, i639] -> [remF (i639 + 2 * i638 + 4 * i637 + 4 * i635 + 4 * i636) 4, i632, i633, i634]))))) (\\[i421, i422, i423, i424, i425] -> [ifF ((0 <=. i421 + i422 &&* 1 >. i421 + i422) &&* ((0 <=. i423 &&* 1 >. i423) &&* ((0 <=. i424 &&* 2 >. i424) &&* (0 <=. i425 &&* 2 >. i425)))) 0 1, i421, i422, i423, i424, i425]) ! [0]) (\\[i427, i428] -> [i427 + i428]), rsum (rsum (rsum (rtranspose [0,2,3,1] u419))), rsum (rtranspose [2,1,0] t389 * rtranspose [2,1,0] (rreplicate 1 m396)), rsum (rtranspose [1,0] m396), rsum (rtranspose [2,0,1] (rreplicate 10 (m393 * m390)) * rtranspose [2,1,0] (rreplicate 1 m395)), rsum (rtranspose [1,0] m395)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\u878 v879 u880 v881 m882 v883 m884 v885 -> let w293 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i277, i278, i279, i280, i281, i282, i283] -> [ifF ((0 <=. i277 + i280 &&* 1 >. i277 + i280) &&* ((0 <=. i281 &&* 1 >. i281) &&* ((0 <=. i278 + i282 &&* 4 >. i278 + i282) &&* (0 <=. i279 + i283 &&* 4 >. i279 + i283)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u878 (\\[i284, i285] -> [i284 + i285]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i286, i287, i288, i289, i290] -> [ifF ((0 <=. i286 + i287 &&* 1 >. i286 + i287) &&* ((0 <=. i288 &&* 1 >. i288) &&* ((0 <=. i289 &&* 2 >. i289) &&* (0 <=. i290 &&* 2 >. i290)))) 0 1, i286, i287, i288, i289, i290]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v879))))))))))) ; w294 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w295 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w297 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w299 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w326 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i300, i301, i302, i303, i304, i305, i306, i307] -> [ifF (w293 ! [i300, i301, i302, i303, i304, i305, i306, i307, w294 ! [i300, i301, i302, i303, i304, i305, i306, i307], w295 ! [i300, i301, i302, i303, i304, i305, i306, i307], w297 ! [i300, i301, i302, i303, i304, i305, i306, i307], w299 ! [i300, i301, i302, i303, i304, i305, i306, i307]] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w293 (\\[i308, i309, i310, i311, i312, i313, i314, i315] -> [i308, i309, i310, i311, i312, i313, i314, i315, w294 ! [i308, i309, i310, i311, i312, i313, i314, i315], w295 ! [i308, i309, i310, i311, i312, i313, i314, i315], w297 ! [i308, i309, i310, i311, i312, i313, i314, i315], w299 ! [i308, i309, i310, i311, i312, i313, i314, i315]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i318, i319, i320, i321, i322, i323, i324, i325] -> [ifF ((0 <=. i318 + i322 &&* 1 >. i318 + i322) &&* ((0 <=. i319 + i323 &&* 1 >. i319 + i323) &&* ((0 <=. 2 * i320 + i324 &&* 4 >. 2 * i320 + i324) &&* (0 <=. 2 * i321 + i325 &&* 4 >. 2 * i321 + i325)))) 0 1, i318, i319, i320, i321, i322, i323, i324, i325])))))))) ; w327 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w328 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w329 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w353 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w326 (\\[i330, i331, i332, i333, i334, i335, i336] -> [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w326 ! [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w326 ! [i330, i331, i332, i333, i334, i335, i336, w327 ! [i330, i331, i332, i333, i334, i335, i336], i334, w328 ! [i330, i331, i332, i333, i334, i335, i336], w329 ! [i330, i331, i332, i333, i334, i335, i336]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i337, i338, i339, i340, i341, i342, i343] -> [ifF ((0 <=. i337 + i340 &&* 1 >. i337 + i340) &&* ((0 <=. i341 &&* 1 >. i341) &&* ((0 <=. i338 + i342 &&* 2 >. i338 + i342) &&* (0 <=. i339 + i343 &&* 2 >. i339 + i343)))) 0 1, i337, i338, i339, i340, i341, i342, i343])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u880 (\\[i344, i345] -> [i344 + i345]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i346, i347, i348, i349, i350] -> [ifF ((0 <=. i346 + i347 &&* 1 >. i346 + i347) &&* ((0 <=. i348 &&* 1 >. i348) &&* ((0 <=. i349 &&* 2 >. i349) &&* (0 <=. i350 &&* 2 >. i350)))) 0 1, i346, i347, i348, i349, i350]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v881))))))))))) ; w354 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w355 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w356 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w357 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w384 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i358, i359, i360, i361, i362, i363, i364, i365] -> [ifF (w353 ! [i358, i359, i360, i361, i362, i363, i364, i365, w354 ! [i358, i359, i360, i361, i362, i363, i364, i365], w355 ! [i358, i359, i360, i361, i362, i363, i364, i365], w356 ! [i358, i359, i360, i361, i362, i363, i364, i365], w357 ! [i358, i359, i360, i361, i362, i363, i364, i365]] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w353 (\\[i366, i367, i368, i369, i370, i371, i372, i373] -> [i366, i367, i368, i369, i370, i371, i372, i373, w354 ! [i366, i367, i368, i369, i370, i371, i372, i373], w355 ! [i366, i367, i368, i369, i370, i371, i372, i373], w356 ! [i366, i367, i368, i369, i370, i371, i372, i373], w357 ! [i366, i367, i368, i369, i370, i371, i372, i373]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i376, i377, i378, i379, i380, i381, i382, i383] -> [ifF ((0 <=. i376 + i380 &&* 1 >. i376 + i380) &&* ((0 <=. i377 + i381 &&* 1 >. i377 + i381) &&* ((0 <=. 2 * i378 + i382 &&* 2 >. 2 * i378 + i382) &&* (0 <=. 2 * i379 + i383 &&* 2 >. 2 * i379 + i383)))) 0 1, i376, i377, i378, i379, i380, i381, i382, i383]) ; m390 = rsum (rtranspose [2,1,0] (rreplicate 1 m882) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w384 (\\[i385, i386, i387, i388] -> [i385, i386, i387, i388, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w384 ! [i385, i386, i387, i388]))) 2) 2, remF (rmaxIndex (rreshape [4] (w384 ! [i385, i386, i387, i388]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v883) in rsum (rtranspose [2,1,0] (rreplicate 1 m884) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i391, i392] -> [ifF (m390 ! [i391, i392] <=. 0.0) 0 1]) * m390))) + rtranspose [1,0] (rreplicate 1 v885)"
