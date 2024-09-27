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
    @?= "\\m406 u481 v482 u483 v484 m485 v486 m487 v488 -> let w293 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i278, i279, i280, i281, i282, i283, i284] -> [ifF ((0 <=. i278 + i281 &&* 1 >. i278 + i281) &&* ((0 <=. i282 &&* 1 >. i282) &&* ((0 <=. i279 + i283 &&* 4 >. i279 + i283) &&* (0 <=. i280 + i284 &&* 4 >. i280 + i284)))) 0 1])))) ; w294 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u481 (\\[i286, i287] -> [i286 + i287]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i288, i289, i290, i291, i292] -> [ifF ((0 <=. i288 + i289 &&* 1 >. i288 + i289) &&* ((0 <=. i290 &&* 1 >. i290) &&* ((0 <=. i291 &&* 2 >. i291) &&* (0 <=. i292 &&* 2 >. i292)))) 0 1, i288, i289, i290, i291, i292])))))) ; w296 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w293 * w294) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v482))))))))))) ; w297 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w298 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v299 = rconst (rfromListLinear [2] [0,1]) ; w300 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v299)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v301 = rconst (rfromListLinear [2] [0,1]) ; w302 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v301)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w319 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i303, i304, i305, i306, i307, i308, i309, i310] -> [ifF (w296 ! [i303, i304, i305, i306, i307, i308, i309, i310, w297 ! [i303, i304, i305, i306, i307, i308, i309, i310], w298 ! [i303, i304, i305, i306, i307, i308, i309, i310], w300 ! [i303, i304, i305, i306, i307, i308, i309, i310], w302 ! [i303, i304, i305, i306, i307, i308, i309, i310]] <=. 0.0) 0 1]) ; w320 = rgather [1,1,2,2,1,1,2,2] w296 (\\[i311, i312, i313, i314, i315, i316, i317, i318] -> [i311, i312, i313, i314, i315, i316, i317, i318, w297 ! [i311, i312, i313, i314, i315, i316, i317, i318], w298 ! [i311, i312, i313, i314, i315, i316, i317, i318], w300 ! [i311, i312, i313, i314, i315, i316, i317, i318], w302 ! [i311, i312, i313, i314, i315, i316, i317, i318]]) ; w329 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w319 * w320, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i321, i322, i323, i324, i325, i326, i327, i328] -> [ifF ((0 <=. i321 + i325 &&* 1 >. i321 + i325) &&* ((0 <=. i322 + i326 &&* 1 >. i322 + i326) &&* ((0 <=. 2 * i323 + i327 &&* 4 >. 2 * i323 + i327) &&* (0 <=. 2 * i324 + i328 &&* 4 >. 2 * i324 + i328)))) 0 1, i321, i322, i323, i324, i325, i326, i327, i328])))))))) ; w330 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w331 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w332 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w355 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w329 (\\[i333, i334, i335, i336, i337, i338, i339] -> [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w329 ! [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w329 ! [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i340, i341, i342, i343, i344, i345, i346] -> [ifF ((0 <=. i340 + i343 &&* 1 >. i340 + i343) &&* ((0 <=. i344 &&* 1 >. i344) &&* ((0 <=. i341 + i345 &&* 2 >. i341 + i345) &&* (0 <=. i342 + i346 &&* 2 >. i342 + i346)))) 0 1, i340, i341, i342, i343, i344, i345, i346])))) ; w356 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u483 (\\[i348, i349] -> [i348 + i349]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i350, i351, i352, i353, i354] -> [ifF ((0 <=. i350 + i351 &&* 1 >. i350 + i351) &&* ((0 <=. i352 &&* 1 >. i352) &&* ((0 <=. i353 &&* 2 >. i353) &&* (0 <=. i354 &&* 2 >. i354)))) 0 1, i350, i351, i352, i353, i354])))))) ; w358 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w355 * w356) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v484))))))))))) ; w359 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w360 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w361 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w362 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w379 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i363, i364, i365, i366, i367, i368, i369, i370] -> [ifF (w358 ! [i363, i364, i365, i366, i367, i368, i369, i370, w359 ! [i363, i364, i365, i366, i367, i368, i369, i370], w360 ! [i363, i364, i365, i366, i367, i368, i369, i370], w361 ! [i363, i364, i365, i366, i367, i368, i369, i370], w362 ! [i363, i364, i365, i366, i367, i368, i369, i370]] <=. 0.0) 0 1]) ; w380 = rgather [1,1,1,1,1,1,2,2] w358 (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [i371, i372, i373, i374, i375, i376, i377, i378, w359 ! [i371, i372, i373, i374, i375, i376, i377, i378], w360 ! [i371, i372, i373, i374, i375, i376, i377, i378], w361 ! [i371, i372, i373, i374, i375, i376, i377, i378], w362 ! [i371, i372, i373, i374, i375, i376, i377, i378]]) ; w389 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w379 * w380, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [ifF ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. i382 + i386 &&* 1 >. i382 + i386) &&* ((0 <=. 2 * i383 + i387 &&* 2 >. 2 * i383 + i387) &&* (0 <=. 2 * i384 + i388 &&* 2 >. 2 * i384 + i388)))) 0 1, i381, i382, i383, i384, i385, i386, i387, i388]) ; t396 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w389 (\\[i390, i391, i392, i393] -> [i390, i391, i392, i393, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w389 ! [i390, i391, i392, i393]))) 2) 2, remF (rmaxIndex (rreshape [4] (w389 ! [i390, i391, i392, i393]))) 2]))))) ; m398 = rsum (rtranspose [2,1,0] (rreplicate 1 m485) * t396) + rtranspose [1,0] (rreplicate 1 v486) ; m401 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i399, i400] -> [ifF (m398 ! [i399, i400] <=. 0.0) 0 1]) ; t404 = rtranspose [1,0] (rreplicate 10 (m401 * m398)) ; m407 = m401 * rsum (rtranspose [1,2,0] (rreplicate 1 m487) * rtranspose [1,0] (rreplicate 1 m406)) ; w421 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rsum (rtranspose [1,0] (rreplicate 1 m485) * rtranspose [1,2,0] (rreplicate 1 m407)))) (\\[i409, i410, i411, i412] -> [i409, i410, i411, i412, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w389 ! [i409, i410, i411, i412]))) 2) 2, remF (rmaxIndex (rreshape [4] (w389 ! [i409, i410, i411, i412]))) 2])) (\\[i413, i414, i415, i416, i417, i418, i419, i420] -> [ifF ((0 <=. i413 + i417 &&* 1 >. i413 + i417) &&* ((0 <=. i414 + i418 &&* 1 >. i414 + i418) &&* ((0 <=. 2 * i415 + i419 &&* 2 >. 2 * i415 + i419) &&* (0 <=. 2 * i416 + i420 &&* 2 >. 2 * i416 + i420)))) 0 1, i413, i414, i415, i416, i417, i418, i419, i420]) ; u430 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w379 * w421 ! [0]) (\\[i422, i423, i424, i425, i426, i427, i428, i429] -> [i422, i423, i424, i425, i426, i427, i428, i429, w359 ! [i422, i423, i424, i425, i426, i427, i428, i429], w360 ! [i422, i423, i424, i425, i426, i427, i428, i429], w361 ! [i422, i423, i424, i425, i426, i427, i428, i429], w362 ! [i422, i423, i424, i425, i426, i427, i428, i429]]))))))))) ; w437 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] w355 * rtranspose [1,3,4,2,0] (rreplicate 4 u430)))))) (\\[i432, i433, i434, i435, i436] -> [ifF ((0 <=. i432 + i433 &&* 1 >. i432 + i433) &&* ((0 <=. i434 &&* 1 >. i434) &&* ((0 <=. i435 &&* 2 >. i435) &&* (0 <=. i436 &&* 2 >. i436)))) 0 1, i432, i433, i434, i435, i436]) ; w447 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] w356 * rtranspose [2,1,3,4,0] (rreplicate 4 u430)))) (\\[i440, i441, i442, i443, i444, i445, i446] -> [ifF ((0 <=. i440 + i443 &&* 1 >. i440 + i443) &&* ((0 <=. i444 &&* 1 >. i444) &&* ((0 <=. i441 + i445 &&* 2 >. i441 + i445) &&* (0 <=. i442 + i446 &&* 2 >. i442 + i446)))) 0 1, i440, i441, i442, i443, i444, i445, i446]) ; w463 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w447 ! [0]) (\\[i448, i449, i450, i451, i452, i453, i454] -> [i448, i449, i450, i451, i452, i453, i454, w330 ! [i448, i449, i450, i451, i452, i453, i454], i452, w331 ! [i448, i449, i450, i451, i452, i453, i454], w332 ! [i448, i449, i450, i451, i452, i453, i454], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w329 ! [i448, i449, i450, i451, i452, i453, i454, w330 ! [i448, i449, i450, i451, i452, i453, i454], i452, w331 ! [i448, i449, i450, i451, i452, i453, i454], w332 ! [i448, i449, i450, i451, i452, i453, i454]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w329 ! [i448, i449, i450, i451, i452, i453, i454, w330 ! [i448, i449, i450, i451, i452, i453, i454], i452, w331 ! [i448, i449, i450, i451, i452, i453, i454], w332 ! [i448, i449, i450, i451, i452, i453, i454]]))) 2]))))))))) (\\[i455, i456, i457, i458, i459, i460, i461, i462] -> [ifF ((0 <=. i455 + i459 &&* 1 >. i455 + i459) &&* ((0 <=. i456 + i460 &&* 1 >. i456 + i460) &&* ((0 <=. 2 * i457 + i461 &&* 4 >. 2 * i457 + i461) &&* (0 <=. 2 * i458 + i462 &&* 4 >. 2 * i458 + i462)))) 0 1, i455, i456, i457, i458, i459, i460, i461, i462]) ; u472 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w319 * w463 ! [0]) (\\[i464, i465, i466, i467, i468, i469, i470, i471] -> [i464, i465, i466, i467, i468, i469, i470, i471, w297 ! [i464, i465, i466, i467, i468, i469, i470, i471], w298 ! [i464, i465, i466, i467, i468, i469, i470, i471], w300 ! [i464, i465, i466, i467, i468, i469, i470, i471], w302 ! [i464, i465, i466, i467, i468, i469, i470, i471]]))))))))) ; w478 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w293 * rreplicate 4 u472)))))) (\\[i473, i474, i475, i476, i477] -> [ifF ((0 <=. i473 + i474 &&* 1 >. i473 + i474) &&* ((0 <=. i475 &&* 1 >. i475) &&* ((0 <=. i476 &&* 2 >. i476) &&* (0 <=. i477 &&* 2 >. i477)))) 0 1, i473, i474, i475, i476, i477]) in [rscatter [1,1,2,2] (w478 ! [0]) (\\[i479, i480] -> [i479 + i480]), rsum (rsum (rsum (rtranspose [0,2,3,1] u472))), rscatter [1,1,2,2] (w437 ! [0]) (\\[i438, i439] -> [i438 + i439]), rsum (rsum (rsum (rtranspose [0,2,3,1] u430))), rsum (rtranspose [2,1,0] t396 * rtranspose [2,1,0] (rreplicate 1 m407)), rsum (rtranspose [1,0] m407), rsum (rtranspose [2,1,0] (t404 * rreplicate 1 m406)), rsum (rtranspose [1,0] m406)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\u609 v610 u611 v612 m613 v614 m615 v616 -> let w293 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i278, i279, i280, i281, i282, i283, i284] -> [ifF ((0 <=. i278 + i281 &&* 1 >. i278 + i281) &&* ((0 <=. i282 &&* 1 >. i282) &&* ((0 <=. i279 + i283 &&* 4 >. i279 + i283) &&* (0 <=. i280 + i284 &&* 4 >. i280 + i284)))) 0 1])))) ; w294 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u609 (\\[i286, i287] -> [i286 + i287]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i288, i289, i290, i291, i292] -> [ifF ((0 <=. i288 + i289 &&* 1 >. i288 + i289) &&* ((0 <=. i290 &&* 1 >. i290) &&* ((0 <=. i291 &&* 2 >. i291) &&* (0 <=. i292 &&* 2 >. i292)))) 0 1, i288, i289, i290, i291, i292])))))) ; w296 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w293 * w294) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v610))))))))))) ; w297 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w298 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v299 = rconst (rfromListLinear [2] [0,1]) ; w300 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v299)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v301 = rconst (rfromListLinear [2] [0,1]) ; w302 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v301)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w319 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i303, i304, i305, i306, i307, i308, i309, i310] -> [ifF (w296 ! [i303, i304, i305, i306, i307, i308, i309, i310, w297 ! [i303, i304, i305, i306, i307, i308, i309, i310], w298 ! [i303, i304, i305, i306, i307, i308, i309, i310], w300 ! [i303, i304, i305, i306, i307, i308, i309, i310], w302 ! [i303, i304, i305, i306, i307, i308, i309, i310]] <=. 0.0) 0 1]) ; w320 = rgather [1,1,2,2,1,1,2,2] w296 (\\[i311, i312, i313, i314, i315, i316, i317, i318] -> [i311, i312, i313, i314, i315, i316, i317, i318, w297 ! [i311, i312, i313, i314, i315, i316, i317, i318], w298 ! [i311, i312, i313, i314, i315, i316, i317, i318], w300 ! [i311, i312, i313, i314, i315, i316, i317, i318], w302 ! [i311, i312, i313, i314, i315, i316, i317, i318]]) ; w329 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w319 * w320, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i321, i322, i323, i324, i325, i326, i327, i328] -> [ifF ((0 <=. i321 + i325 &&* 1 >. i321 + i325) &&* ((0 <=. i322 + i326 &&* 1 >. i322 + i326) &&* ((0 <=. 2 * i323 + i327 &&* 4 >. 2 * i323 + i327) &&* (0 <=. 2 * i324 + i328 &&* 4 >. 2 * i324 + i328)))) 0 1, i321, i322, i323, i324, i325, i326, i327, i328])))))))) ; w330 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w331 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w332 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w355 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w329 (\\[i333, i334, i335, i336, i337, i338, i339] -> [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w329 ! [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w329 ! [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i340, i341, i342, i343, i344, i345, i346] -> [ifF ((0 <=. i340 + i343 &&* 1 >. i340 + i343) &&* ((0 <=. i344 &&* 1 >. i344) &&* ((0 <=. i341 + i345 &&* 2 >. i341 + i345) &&* (0 <=. i342 + i346 &&* 2 >. i342 + i346)))) 0 1, i340, i341, i342, i343, i344, i345, i346])))) ; w356 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u611 (\\[i348, i349] -> [i348 + i349]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i350, i351, i352, i353, i354] -> [ifF ((0 <=. i350 + i351 &&* 1 >. i350 + i351) &&* ((0 <=. i352 &&* 1 >. i352) &&* ((0 <=. i353 &&* 2 >. i353) &&* (0 <=. i354 &&* 2 >. i354)))) 0 1, i350, i351, i352, i353, i354])))))) ; w358 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w355 * w356) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v612))))))))))) ; w359 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w360 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w361 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w362 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w379 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i363, i364, i365, i366, i367, i368, i369, i370] -> [ifF (w358 ! [i363, i364, i365, i366, i367, i368, i369, i370, w359 ! [i363, i364, i365, i366, i367, i368, i369, i370], w360 ! [i363, i364, i365, i366, i367, i368, i369, i370], w361 ! [i363, i364, i365, i366, i367, i368, i369, i370], w362 ! [i363, i364, i365, i366, i367, i368, i369, i370]] <=. 0.0) 0 1]) ; w380 = rgather [1,1,1,1,1,1,2,2] w358 (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [i371, i372, i373, i374, i375, i376, i377, i378, w359 ! [i371, i372, i373, i374, i375, i376, i377, i378], w360 ! [i371, i372, i373, i374, i375, i376, i377, i378], w361 ! [i371, i372, i373, i374, i375, i376, i377, i378], w362 ! [i371, i372, i373, i374, i375, i376, i377, i378]]) ; w389 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w379 * w380, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [ifF ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. i382 + i386 &&* 1 >. i382 + i386) &&* ((0 <=. 2 * i383 + i387 &&* 2 >. 2 * i383 + i387) &&* (0 <=. 2 * i384 + i388 &&* 2 >. 2 * i384 + i388)))) 0 1, i381, i382, i383, i384, i385, i386, i387, i388]) ; t396 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w389 (\\[i390, i391, i392, i393] -> [i390, i391, i392, i393, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w389 ! [i390, i391, i392, i393]))) 2) 2, remF (rmaxIndex (rreshape [4] (w389 ! [i390, i391, i392, i393]))) 2]))))) ; m398 = rsum (rtranspose [2,1,0] (rreplicate 1 m613) * t396) + rtranspose [1,0] (rreplicate 1 v614) ; m401 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i399, i400] -> [ifF (m398 ! [i399, i400] <=. 0.0) 0 1]) ; t404 = rtranspose [1,0] (rreplicate 10 (m401 * m398)) in rsum (rtranspose [2,1,0] (rreplicate 1 m615) * t404) + rtranspose [1,0] (rreplicate 1 v616)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m406 u1049 v1050 u1051 v1052 m1053 v1054 m1055 v1056 -> let w293 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i278, i279, i280, i281, i282, i283, i284] -> [ifF ((0 <=. i278 + i281 &&* 1 >. i278 + i281) &&* ((0 <=. i282 &&* 1 >. i282) &&* ((0 <=. i279 + i283 &&* 4 >. i279 + i283) &&* (0 <=. i280 + i284 &&* 4 >. i280 + i284)))) 0 1])))) ; w296 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w293 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1049 (\\[i286, i287] -> [i286 + i287]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i288, i289, i290, i291, i292] -> [ifF ((0 <=. i288 + i289 &&* 1 >. i288 + i289) &&* ((0 <=. i290 &&* 1 >. i290) &&* ((0 <=. i291 &&* 2 >. i291) &&* (0 <=. i292 &&* 2 >. i292)))) 0 1, i288, i289, i290, i291, i292]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v1050))))))))))) ; w297 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w298 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w300 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w302 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w319 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i303, i304, i305, i306, i307, i308, i309, i310] -> [ifF (w296 ! [i303, i304, i305, i306, i307, i308, i309, i310, w297 ! [i303, i304, i305, i306, i307, i308, i309, i310], w298 ! [i303, i304, i305, i306, i307, i308, i309, i310], w300 ! [i303, i304, i305, i306, i307, i308, i309, i310], w302 ! [i303, i304, i305, i306, i307, i308, i309, i310]] <=. 0.0) 0 1]) ; w329 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w319 * rgather [1,1,2,2,1,1,2,2] w296 (\\[i311, i312, i313, i314, i315, i316, i317, i318] -> [i311, i312, i313, i314, i315, i316, i317, i318, w297 ! [i311, i312, i313, i314, i315, i316, i317, i318], w298 ! [i311, i312, i313, i314, i315, i316, i317, i318], w300 ! [i311, i312, i313, i314, i315, i316, i317, i318], w302 ! [i311, i312, i313, i314, i315, i316, i317, i318]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i321, i322, i323, i324, i325, i326, i327, i328] -> [ifF ((0 <=. i321 + i325 &&* 1 >. i321 + i325) &&* ((0 <=. i322 + i326 &&* 1 >. i322 + i326) &&* ((0 <=. 2 * i323 + i327 &&* 4 >. 2 * i323 + i327) &&* (0 <=. 2 * i324 + i328 &&* 4 >. 2 * i324 + i328)))) 0 1, i321, i322, i323, i324, i325, i326, i327, i328])))))))) ; w330 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w331 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w332 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w355 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w329 (\\[i333, i334, i335, i336, i337, i338, i339] -> [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w329 ! [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w329 ! [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i340, i341, i342, i343, i344, i345, i346] -> [ifF ((0 <=. i340 + i343 &&* 1 >. i340 + i343) &&* ((0 <=. i344 &&* 1 >. i344) &&* ((0 <=. i341 + i345 &&* 2 >. i341 + i345) &&* (0 <=. i342 + i346 &&* 2 >. i342 + i346)))) 0 1, i340, i341, i342, i343, i344, i345, i346])))) ; w356 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1051 (\\[i348, i349] -> [i348 + i349]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i350, i351, i352, i353, i354] -> [ifF ((0 <=. i350 + i351 &&* 1 >. i350 + i351) &&* ((0 <=. i352 &&* 1 >. i352) &&* ((0 <=. i353 &&* 2 >. i353) &&* (0 <=. i354 &&* 2 >. i354)))) 0 1, i350, i351, i352, i353, i354])))))) ; w358 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w355 * w356) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v1052))))))))))) ; w359 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w360 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w361 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w362 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w379 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i363, i364, i365, i366, i367, i368, i369, i370] -> [ifF (w358 ! [i363, i364, i365, i366, i367, i368, i369, i370, w359 ! [i363, i364, i365, i366, i367, i368, i369, i370], w360 ! [i363, i364, i365, i366, i367, i368, i369, i370], w361 ! [i363, i364, i365, i366, i367, i368, i369, i370], w362 ! [i363, i364, i365, i366, i367, i368, i369, i370]] <=. 0.0) 0 1]) ; w389 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w379 * rgather [1,1,1,1,1,1,2,2] w358 (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [i371, i372, i373, i374, i375, i376, i377, i378, w359 ! [i371, i372, i373, i374, i375, i376, i377, i378], w360 ! [i371, i372, i373, i374, i375, i376, i377, i378], w361 ! [i371, i372, i373, i374, i375, i376, i377, i378], w362 ! [i371, i372, i373, i374, i375, i376, i377, i378]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [ifF ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. i382 + i386 &&* 1 >. i382 + i386) &&* ((0 <=. 2 * i383 + i387 &&* 2 >. 2 * i383 + i387) &&* (0 <=. 2 * i384 + i388 &&* 2 >. 2 * i384 + i388)))) 0 1, i381, i382, i383, i384, i385, i386, i387, i388]) ; t396 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w389 (\\[i390, i391, i392, i393] -> [i390, i391, i392, i393, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w389 ! [i390, i391, i392, i393]))) 2) 2, remF (rmaxIndex (rreshape [4] (w389 ! [i390, i391, i392, i393]))) 2])))) ; m398 = rsum (rtranspose [2,1,0] (rreplicate 1 m1053) * t396) + rtranspose [1,0] (rreplicate 1 v1054) ; m401 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i399, i400] -> [ifF (m398 ! [i399, i400] <=. 0.0) 0 1]) ; m407 = m401 * rsum (rtranspose [1,2,0] (rreplicate 1 m1055) * rtranspose [1,0] (rreplicate 1 m406)) ; u430 = rscatter [1,1,2,2] (w379 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] m1053 (\\[i984] -> [i984, 0]) * rgather [1] m407 (\\[i981] -> [i981, 0]))))))) (\\[i409, i410, i411, i412] -> [i409, i410, i411, i412, 0, 0, remF (quotF (rmaxIndex (rgather [4] (w389 ! [i409, i410, i411, i412, 0, 0]) (\\[i974] -> [remF (quotF i974 2) 2, remF i974 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w389 ! [i409, i410, i411, i412, 0, 0]) (\\[i975] -> [remF (quotF i975 2) 2, remF i975 2]))) 2])) (\\[i413, i414, i415, i416, i417, i418, i419, i420] -> [ifF ((0 <=. i413 + i417 &&* 1 >. i413 + i417) &&* ((0 <=. i414 + i418 &&* 1 >. i414 + i418) &&* ((0 <=. 2 * i415 + i419 &&* 2 >. 2 * i415 + i419) &&* (0 <=. 2 * i416 + i420 &&* 2 >. 2 * i416 + i420)))) 0 1, i413, i414, i415, i416, i417, i418, i419, i420]) ! [0]) (\\[i422, i423, i424, i425, i426, i427, i428, i429] -> [w359 ! [i422, i423, i424, i425, i426, i427, i428, i429], w360 ! [i422, i423, i424, i425, i426, i427, i428, i429], w361 ! [i422, i423, i424, i425, i426, i427, i428, i429], w362 ! [i422, i423, i424, i425, i426, i427, i428, i429]]) ; u472 = rscatter [1,1,4,4] (w319 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w356 (\\[i958, i959, i960, i957] -> [i960, 0, i957, i958, i959]) * rgather [2,2,4,1] (u430 ! [0]) (\\[i963, i964, i965, i962] -> [i962, i963, i964])) (\\[i966, i967, i968, i969, i970, i971, i972, i973] -> [remF (quotF (i973 + 2 * i972 + 4 * i971 + 4 * i970 + 4 * i969 + 16 * i967 + 8 * i968) 8) 2, remF (quotF (i973 + 2 * i972 + 4 * i971 + 4 * i970 + 4 * i969 + 16 * i967 + 8 * i968) 4) 2, remF (i973 + 2 * i972 + 4 * i971 + 4 * i970 + 4 * i969 + 16 * i967 + 8 * i968) 4, i966]))) (\\[i440, i441, i442, i443, i444, i445, i446] -> [ifF ((0 <=. i440 + i443 &&* 1 >. i440 + i443) &&* ((0 <=. i444 &&* 1 >. i444) &&* ((0 <=. i441 + i445 &&* 2 >. i441 + i445) &&* (0 <=. i442 + i446 &&* 2 >. i442 + i446)))) 0 1, i440, i441, i442, i443, i444, i445, i446]) ! [0]) (\\[i448, i449, i450, i451, i452, i453, i454] -> [w330 ! [i448, i449, i450, i451, i452, i453, i454], i452, w331 ! [i448, i449, i450, i451, i452, i453, i454], w332 ! [i448, i449, i450, i451, i452, i453, i454], 0, 0, remF (quotF (rmaxIndex (rgather [4] (w329 ! [i448, i449, i450, i451, i452, i453, i454, w330 ! [i448, i449, i450, i451, i452, i453, i454], i452, w331 ! [i448, i449, i450, i451, i452, i453, i454], w332 ! [i448, i449, i450, i451, i452, i453, i454], 0, 0]) (\\[i947] -> [remF (quotF i947 2) 2, remF i947 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w329 ! [i448, i449, i450, i451, i452, i453, i454, w330 ! [i448, i449, i450, i451, i452, i453, i454], i452, w331 ! [i448, i449, i450, i451, i452, i453, i454], w332 ! [i448, i449, i450, i451, i452, i453, i454], 0, 0]) (\\[i948] -> [remF (quotF i948 2) 2, remF i948 2]))) 2])) (\\[i455, i456, i457, i458, i459, i460, i461, i462] -> [ifF ((0 <=. i455 + i459 &&* 1 >. i455 + i459) &&* ((0 <=. i456 + i460 &&* 1 >. i456 + i460) &&* ((0 <=. 2 * i457 + i461 &&* 4 >. 2 * i457 + i461) &&* (0 <=. 2 * i458 + i462 &&* 4 >. 2 * i458 + i462)))) 0 1, i455, i456, i457, i458, i459, i460, i461, i462]) ! [0]) (\\[i464, i465, i466, i467, i468, i469, i470, i471] -> [w297 ! [i464, i465, i466, i467, i468, i469, i470, i471], w298 ! [i464, i465, i466, i467, i468, i469, i470, i471], w300 ! [i464, i465, i466, i467, i468, i469, i470, i471], w302 ! [i464, i465, i466, i467, i468, i469, i470, i471]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w293 (\\[i802, i799] -> [i802, i799, 0]) * rreplicate 4 (rgather [1,4,4] u472 (\\[i804] -> [i804, 0]))) (\\[i862, i863, i864, i865, i866, i867, i868, i869] -> [remF (i869 + 2 * i868 + 4 * i867 + 4 * i865 + 4 * i866) 4, i862, i863, i864]))))) (\\[i473, i474, i475, i476, i477] -> [ifF ((0 <=. i473 + i474 &&* 1 >. i473 + i474) &&* ((0 <=. i475 &&* 1 >. i475) &&* ((0 <=. i476 &&* 2 >. i476) &&* (0 <=. i477 &&* 2 >. i477)))) 0 1, i473, i474, i475, i476, i477]) ! [0]) (\\[i479, i480] -> [i479 + i480]), rsum (rsum (rsum (rtranspose [0,2,3,1] u472))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w355 (\\[i879, i876] -> [i879, i876, 0]) * rreplicate 4 (rgather [1,2,2] u430 (\\[i881] -> [i881, 0]))) (\\[i939, i940, i941, i942, i943, i944, i945, i946] -> [remF (i946 + 2 * i945 + 4 * i944 + 4 * i942 + 4 * i943) 4, i939, i940, i941]))))) (\\[i432, i433, i434, i435, i436] -> [ifF ((0 <=. i432 + i433 &&* 1 >. i432 + i433) &&* ((0 <=. i434 &&* 1 >. i434) &&* ((0 <=. i435 &&* 2 >. i435) &&* (0 <=. i436 &&* 2 >. i436)))) 0 1, i432, i433, i434, i435, i436]) ! [0]) (\\[i438, i439] -> [i438 + i439]), rsum (rsum (rsum (rtranspose [0,2,3,1] u430))), rsum (rtranspose [2,1,0] t396 * rtranspose [2,1,0] (rreplicate 1 m407)), rsum (rtranspose [1,0] m407), rsum (rtranspose [2,0,1] (rreplicate 10 (m401 * m398)) * rtranspose [2,1,0] (rreplicate 1 m406)), rsum (rtranspose [1,0] m406)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\u1369 v1370 u1371 v1372 m1373 v1374 m1375 v1376 -> let w296 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i278, i279, i280, i281, i282, i283, i284] -> [ifF ((0 <=. i278 + i281 &&* 1 >. i278 + i281) &&* ((0 <=. i282 &&* 1 >. i282) &&* ((0 <=. i279 + i283 &&* 4 >. i279 + i283) &&* (0 <=. i280 + i284 &&* 4 >. i280 + i284)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1369 (\\[i286, i287] -> [i286 + i287]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i288, i289, i290, i291, i292] -> [ifF ((0 <=. i288 + i289 &&* 1 >. i288 + i289) &&* ((0 <=. i290 &&* 1 >. i290) &&* ((0 <=. i291 &&* 2 >. i291) &&* (0 <=. i292 &&* 2 >. i292)))) 0 1, i288, i289, i290, i291, i292]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v1370))))))))))) ; w297 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w298 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w300 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w302 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w329 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i303, i304, i305, i306, i307, i308, i309, i310] -> [ifF (w296 ! [i303, i304, i305, i306, i307, i308, i309, i310, w297 ! [i303, i304, i305, i306, i307, i308, i309, i310], w298 ! [i303, i304, i305, i306, i307, i308, i309, i310], w300 ! [i303, i304, i305, i306, i307, i308, i309, i310], w302 ! [i303, i304, i305, i306, i307, i308, i309, i310]] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w296 (\\[i311, i312, i313, i314, i315, i316, i317, i318] -> [i311, i312, i313, i314, i315, i316, i317, i318, w297 ! [i311, i312, i313, i314, i315, i316, i317, i318], w298 ! [i311, i312, i313, i314, i315, i316, i317, i318], w300 ! [i311, i312, i313, i314, i315, i316, i317, i318], w302 ! [i311, i312, i313, i314, i315, i316, i317, i318]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i321, i322, i323, i324, i325, i326, i327, i328] -> [ifF ((0 <=. i321 + i325 &&* 1 >. i321 + i325) &&* ((0 <=. i322 + i326 &&* 1 >. i322 + i326) &&* ((0 <=. 2 * i323 + i327 &&* 4 >. 2 * i323 + i327) &&* (0 <=. 2 * i324 + i328 &&* 4 >. 2 * i324 + i328)))) 0 1, i321, i322, i323, i324, i325, i326, i327, i328])))))))) ; w330 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w331 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w332 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w358 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w329 (\\[i333, i334, i335, i336, i337, i338, i339] -> [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w329 ! [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w329 ! [i333, i334, i335, i336, i337, i338, i339, w330 ! [i333, i334, i335, i336, i337, i338, i339], i337, w331 ! [i333, i334, i335, i336, i337, i338, i339], w332 ! [i333, i334, i335, i336, i337, i338, i339]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i340, i341, i342, i343, i344, i345, i346] -> [ifF ((0 <=. i340 + i343 &&* 1 >. i340 + i343) &&* ((0 <=. i344 &&* 1 >. i344) &&* ((0 <=. i341 + i345 &&* 2 >. i341 + i345) &&* (0 <=. i342 + i346 &&* 2 >. i342 + i346)))) 0 1, i340, i341, i342, i343, i344, i345, i346])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1371 (\\[i348, i349] -> [i348 + i349]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i350, i351, i352, i353, i354] -> [ifF ((0 <=. i350 + i351 &&* 1 >. i350 + i351) &&* ((0 <=. i352 &&* 1 >. i352) &&* ((0 <=. i353 &&* 2 >. i353) &&* (0 <=. i354 &&* 2 >. i354)))) 0 1, i350, i351, i352, i353, i354]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v1372))))))))))) ; w359 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w360 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w361 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w362 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w389 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i363, i364, i365, i366, i367, i368, i369, i370] -> [ifF (w358 ! [i363, i364, i365, i366, i367, i368, i369, i370, w359 ! [i363, i364, i365, i366, i367, i368, i369, i370], w360 ! [i363, i364, i365, i366, i367, i368, i369, i370], w361 ! [i363, i364, i365, i366, i367, i368, i369, i370], w362 ! [i363, i364, i365, i366, i367, i368, i369, i370]] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w358 (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [i371, i372, i373, i374, i375, i376, i377, i378, w359 ! [i371, i372, i373, i374, i375, i376, i377, i378], w360 ! [i371, i372, i373, i374, i375, i376, i377, i378], w361 ! [i371, i372, i373, i374, i375, i376, i377, i378], w362 ! [i371, i372, i373, i374, i375, i376, i377, i378]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [ifF ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. i382 + i386 &&* 1 >. i382 + i386) &&* ((0 <=. 2 * i383 + i387 &&* 2 >. 2 * i383 + i387) &&* (0 <=. 2 * i384 + i388 &&* 2 >. 2 * i384 + i388)))) 0 1, i381, i382, i383, i384, i385, i386, i387, i388]) ; m398 = rsum (rtranspose [2,1,0] (rreplicate 1 m1373) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w389 (\\[i390, i391, i392, i393] -> [i390, i391, i392, i393, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w389 ! [i390, i391, i392, i393]))) 2) 2, remF (rmaxIndex (rreshape [4] (w389 ! [i390, i391, i392, i393]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v1374) in rsum (rtranspose [2,1,0] (rreplicate 1 m1375) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i399, i400] -> [ifF (m398 ! [i399, i400] <=. 0.0) 0 1]) * m398))) + rtranspose [1,0] (rreplicate 1 v1376)"
