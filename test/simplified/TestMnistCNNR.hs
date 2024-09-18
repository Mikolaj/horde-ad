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
    @?= "\\m405 u480 v481 u482 v483 m484 v485 m486 v487 -> let w292 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i277, i278, i279, i280, i281, i282, i283] -> [ifF ((0 <=. i277 + i280 &&* 1 >. i277 + i280) &&* ((0 <=. i281 &&* 1 >. i281) &&* ((0 <=. i278 + i282 &&* 4 >. i278 + i282) &&* (0 <=. i279 + i283 &&* 4 >. i279 + i283)))) 0 1])))) ; w293 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u480 (\\[i285, i286] -> [i285 + i286]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i287, i288, i289, i290, i291] -> [ifF ((0 <=. i287 + i288 &&* 1 >. i287 + i288) &&* ((0 <=. i289 &&* 1 >. i289) &&* ((0 <=. i290 &&* 2 >. i290) &&* (0 <=. i291 &&* 2 >. i291)))) 0 1, i287, i288, i289, i290, i291])))))) ; w295 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w292 * w293) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v481))))))))))) ; w296 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w297 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v298 = rconst (rfromListLinear [2] [0,1]) ; w299 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v298)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v300 = rconst (rfromListLinear [2] [0,1]) ; w301 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v300)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w318 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i302, i303, i304, i305, i306, i307, i308, i309] -> [ifF (w295 ! [i302, i303, i304, i305, i306, i307, i308, i309, w296 ! [i302, i303, i304, i305, i306, i307, i308, i309], w297 ! [i302, i303, i304, i305, i306, i307, i308, i309], w299 ! [i302, i303, i304, i305, i306, i307, i308, i309], w301 ! [i302, i303, i304, i305, i306, i307, i308, i309]] <=. 0.0) 0 1]) ; w319 = rgather [1,1,2,2,1,1,2,2] w295 (\\[i310, i311, i312, i313, i314, i315, i316, i317] -> [i310, i311, i312, i313, i314, i315, i316, i317, w296 ! [i310, i311, i312, i313, i314, i315, i316, i317], w297 ! [i310, i311, i312, i313, i314, i315, i316, i317], w299 ! [i310, i311, i312, i313, i314, i315, i316, i317], w301 ! [i310, i311, i312, i313, i314, i315, i316, i317]]) ; w328 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w318 * w319, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i320, i321, i322, i323, i324, i325, i326, i327] -> [ifF ((0 <=. i320 + i324 &&* 1 >. i320 + i324) &&* ((0 <=. i321 + i325 &&* 1 >. i321 + i325) &&* ((0 <=. 2 * i322 + i326 &&* 4 >. 2 * i322 + i326) &&* (0 <=. 2 * i323 + i327 &&* 4 >. 2 * i323 + i327)))) 0 1, i320, i321, i322, i323, i324, i325, i326, i327])))))))) ; w329 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w330 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w331 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w354 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w328 (\\[i332, i333, i334, i335, i336, i337, i338] -> [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w328 ! [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w328 ! [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 2 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 2 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345])))) ; w355 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u482 (\\[i347, i348] -> [i347 + i348]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i349, i350, i351, i352, i353] -> [ifF ((0 <=. i349 + i350 &&* 1 >. i349 + i350) &&* ((0 <=. i351 &&* 1 >. i351) &&* ((0 <=. i352 &&* 2 >. i352) &&* (0 <=. i353 &&* 2 >. i353)))) 0 1, i349, i350, i351, i352, i353])))))) ; w357 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w354 * w355) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v483))))))))))) ; w358 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w359 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w360 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w361 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w378 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i362, i363, i364, i365, i366, i367, i368, i369] -> [ifF (w357 ! [i362, i363, i364, i365, i366, i367, i368, i369, w358 ! [i362, i363, i364, i365, i366, i367, i368, i369], w359 ! [i362, i363, i364, i365, i366, i367, i368, i369], w360 ! [i362, i363, i364, i365, i366, i367, i368, i369], w361 ! [i362, i363, i364, i365, i366, i367, i368, i369]] <=. 0.0) 0 1]) ; w379 = rgather [1,1,1,1,1,1,2,2] w357 (\\[i370, i371, i372, i373, i374, i375, i376, i377] -> [i370, i371, i372, i373, i374, i375, i376, i377, w358 ! [i370, i371, i372, i373, i374, i375, i376, i377], w359 ! [i370, i371, i372, i373, i374, i375, i376, i377], w360 ! [i370, i371, i372, i373, i374, i375, i376, i377], w361 ! [i370, i371, i372, i373, i374, i375, i376, i377]]) ; w388 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w378 * w379, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i380, i381, i382, i383, i384, i385, i386, i387] -> [ifF ((0 <=. i380 + i384 &&* 1 >. i380 + i384) &&* ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. 2 * i382 + i386 &&* 2 >. 2 * i382 + i386) &&* (0 <=. 2 * i383 + i387 &&* 2 >. 2 * i383 + i387)))) 0 1, i380, i381, i382, i383, i384, i385, i386, i387]) ; t395 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w388 (\\[i389, i390, i391, i392] -> [i389, i390, i391, i392, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w388 ! [i389, i390, i391, i392]))) 2) 2, remF (rmaxIndex (rreshape [4] (w388 ! [i389, i390, i391, i392]))) 2]))))) ; m397 = rsum (rtranspose [2,1,0] (rreplicate 1 m484) * t395) + rtranspose [1,0] (rreplicate 1 v485) ; m400 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i398, i399] -> [ifF (m397 ! [i398, i399] <=. 0.0) 0 1]) ; t403 = rtranspose [1,0] (rreplicate 10 (m400 * m397)) ; m406 = m400 * rsum (rtranspose [1,2,0] (rreplicate 1 m486) * rtranspose [1,0] (rreplicate 1 m405)) ; w420 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rsum (rtranspose [1,0] (rreplicate 1 m484) * rtranspose [1,2,0] (rreplicate 1 m406)))) (\\[i408, i409, i410, i411] -> [i408, i409, i410, i411, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w388 ! [i408, i409, i410, i411]))) 2) 2, remF (rmaxIndex (rreshape [4] (w388 ! [i408, i409, i410, i411]))) 2])) (\\[i412, i413, i414, i415, i416, i417, i418, i419] -> [ifF ((0 <=. i412 + i416 &&* 1 >. i412 + i416) &&* ((0 <=. i413 + i417 &&* 1 >. i413 + i417) &&* ((0 <=. 2 * i414 + i418 &&* 2 >. 2 * i414 + i418) &&* (0 <=. 2 * i415 + i419 &&* 2 >. 2 * i415 + i419)))) 0 1, i412, i413, i414, i415, i416, i417, i418, i419]) ; u429 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,1,1,1,1,2,2,1,1,2,2] (w378 * w420 ! [0]) (\\[i421, i422, i423, i424, i425, i426, i427, i428] -> [i421, i422, i423, i424, i425, i426, i427, i428, w358 ! [i421, i422, i423, i424, i425, i426, i427, i428], w359 ! [i421, i422, i423, i424, i425, i426, i427, i428], w360 ! [i421, i422, i423, i424, i425, i426, i427, i428], w361 ! [i421, i422, i423, i424, i425, i426, i427, i428]]))))))))) ; w436 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] w354 * rtranspose [1,3,4,2,0] (rreplicate 4 u429)))))) (\\[i431, i432, i433, i434, i435] -> [ifF ((0 <=. i431 + i432 &&* 1 >. i431 + i432) &&* ((0 <=. i433 &&* 1 >. i433) &&* ((0 <=. i434 &&* 2 >. i434) &&* (0 <=. i435 &&* 2 >. i435)))) 0 1, i431, i432, i433, i434, i435]) ; w446 = rscatter [2,1,2,2,1,1,2,2] (rreshape [1,2,2,1,1,2,2] (rsum (rtranspose [2,1,3,4,0] w355 * rtranspose [2,1,3,4,0] (rreplicate 4 u429)))) (\\[i439, i440, i441, i442, i443, i444, i445] -> [ifF ((0 <=. i439 + i442 &&* 1 >. i439 + i442) &&* ((0 <=. i443 &&* 1 >. i443) &&* ((0 <=. i440 + i444 &&* 2 >. i440 + i444) &&* (0 <=. i441 + i445 &&* 2 >. i441 + i445)))) 0 1, i439, i440, i441, i442, i443, i444, i445]) ; w462 = rscatter [2,1,1,2,2,1,1,2,2] (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,2,2,1,1,2,2,1,1,2,2,1,1,2,2] (w446 ! [0]) (\\[i447, i448, i449, i450, i451, i452, i453] -> [i447, i448, i449, i450, i451, i452, i453, w329 ! [i447, i448, i449, i450, i451, i452, i453], i451, w330 ! [i447, i448, i449, i450, i451, i452, i453], w331 ! [i447, i448, i449, i450, i451, i452, i453], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w328 ! [i447, i448, i449, i450, i451, i452, i453, w329 ! [i447, i448, i449, i450, i451, i452, i453], i451, w330 ! [i447, i448, i449, i450, i451, i452, i453], w331 ! [i447, i448, i449, i450, i451, i452, i453]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w328 ! [i447, i448, i449, i450, i451, i452, i453, w329 ! [i447, i448, i449, i450, i451, i452, i453], i451, w330 ! [i447, i448, i449, i450, i451, i452, i453], w331 ! [i447, i448, i449, i450, i451, i452, i453]]))) 2]))))))))) (\\[i454, i455, i456, i457, i458, i459, i460, i461] -> [ifF ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. i455 + i459 &&* 1 >. i455 + i459) &&* ((0 <=. 2 * i456 + i460 &&* 4 >. 2 * i456 + i460) &&* (0 <=. 2 * i457 + i461 &&* 4 >. 2 * i457 + i461)))) 0 1, i454, i455, i456, i457, i458, i459, i460, i461]) ; u471 = rsum (rsum (rsum (rsum (rsum (rsum (rsum (rsum (rscatter [1,1,2,2,1,1,2,2,1,1,4,4] (w318 * w462 ! [0]) (\\[i463, i464, i465, i466, i467, i468, i469, i470] -> [i463, i464, i465, i466, i467, i468, i469, i470, w296 ! [i463, i464, i465, i466, i467, i468, i469, i470], w297 ! [i463, i464, i465, i466, i467, i468, i469, i470], w299 ! [i463, i464, i465, i466, i467, i468, i469, i470], w301 ! [i463, i464, i465, i466, i467, i468, i469, i470]]))))))))) ; w477 = rscatter [2,1,1,1,2,2] (rreshape [1,1,1,2,2] (rsum (rsum (rsum (rtranspose [1,3,4,2,0] (w292 * rreplicate 4 u471)))))) (\\[i472, i473, i474, i475, i476] -> [ifF ((0 <=. i472 + i473 &&* 1 >. i472 + i473) &&* ((0 <=. i474 &&* 1 >. i474) &&* ((0 <=. i475 &&* 2 >. i475) &&* (0 <=. i476 &&* 2 >. i476)))) 0 1, i472, i473, i474, i475, i476]) in [rscatter [1,1,2,2] (w477 ! [0]) (\\[i478, i479] -> [i478 + i479]), rsum (rsum (rsum (rtranspose [0,2,3,1] u471))), rscatter [1,1,2,2] (w436 ! [0]) (\\[i437, i438] -> [i437 + i438]), rsum (rsum (rsum (rtranspose [0,2,3,1] u429))), rsum (rtranspose [2,1,0] t395 * rtranspose [2,1,0] (rreplicate 1 m406)), rsum (rtranspose [1,0] m406), rsum (rtranspose [2,1,0] (t403 * rreplicate 1 m405)), rsum (rtranspose [1,0] m405)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\u608 v609 u610 v611 m612 v613 m614 v615 -> let w292 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i277, i278, i279, i280, i281, i282, i283] -> [ifF ((0 <=. i277 + i280 &&* 1 >. i277 + i280) &&* ((0 <=. i281 &&* 1 >. i281) &&* ((0 <=. i278 + i282 &&* 4 >. i278 + i282) &&* (0 <=. i279 + i283 &&* 4 >. i279 + i283)))) 0 1])))) ; w293 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u608 (\\[i285, i286] -> [i285 + i286]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i287, i288, i289, i290, i291] -> [ifF ((0 <=. i287 + i288 &&* 1 >. i287 + i288) &&* ((0 <=. i289 &&* 1 >. i289) &&* ((0 <=. i290 &&* 2 >. i290) &&* (0 <=. i291 &&* 2 >. i291)))) 0 1, i287, i288, i289, i290, i291])))))) ; w295 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w292 * w293) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v609))))))))))) ; w296 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w297 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; v298 = rconst (rfromListLinear [2] [0,1]) ; w299 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v298)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; v300 = rconst (rfromListLinear [2] [0,1]) ; w301 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v300)) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w318 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i302, i303, i304, i305, i306, i307, i308, i309] -> [ifF (w295 ! [i302, i303, i304, i305, i306, i307, i308, i309, w296 ! [i302, i303, i304, i305, i306, i307, i308, i309], w297 ! [i302, i303, i304, i305, i306, i307, i308, i309], w299 ! [i302, i303, i304, i305, i306, i307, i308, i309], w301 ! [i302, i303, i304, i305, i306, i307, i308, i309]] <=. 0.0) 0 1]) ; w319 = rgather [1,1,2,2,1,1,2,2] w295 (\\[i310, i311, i312, i313, i314, i315, i316, i317] -> [i310, i311, i312, i313, i314, i315, i316, i317, w296 ! [i310, i311, i312, i313, i314, i315, i316, i317], w297 ! [i310, i311, i312, i313, i314, i315, i316, i317], w299 ! [i310, i311, i312, i313, i314, i315, i316, i317], w301 ! [i310, i311, i312, i313, i314, i315, i316, i317]]) ; w328 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w318 * w319, rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i320, i321, i322, i323, i324, i325, i326, i327] -> [ifF ((0 <=. i320 + i324 &&* 1 >. i320 + i324) &&* ((0 <=. i321 + i325 &&* 1 >. i321 + i325) &&* ((0 <=. 2 * i322 + i326 &&* 4 >. 2 * i322 + i326) &&* (0 <=. 2 * i323 + i327 &&* 4 >. 2 * i323 + i327)))) 0 1, i320, i321, i322, i323, i324, i325, i326, i327])))))))) ; w329 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w330 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w331 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w354 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w328 (\\[i332, i333, i334, i335, i336, i337, i338] -> [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w328 ! [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w328 ! [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 2 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 2 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345])))) ; w355 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u610 (\\[i347, i348] -> [i347 + i348]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i349, i350, i351, i352, i353] -> [ifF ((0 <=. i349 + i350 &&* 1 >. i349 + i350) &&* ((0 <=. i351 &&* 1 >. i351) &&* ((0 <=. i352 &&* 2 >. i352) &&* (0 <=. i353 &&* 2 >. i353)))) 0 1, i349, i350, i351, i352, i353])))))) ; w357 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w354 * w355) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v611))))))))))) ; w358 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w359 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w360 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w361 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w378 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i362, i363, i364, i365, i366, i367, i368, i369] -> [ifF (w357 ! [i362, i363, i364, i365, i366, i367, i368, i369, w358 ! [i362, i363, i364, i365, i366, i367, i368, i369], w359 ! [i362, i363, i364, i365, i366, i367, i368, i369], w360 ! [i362, i363, i364, i365, i366, i367, i368, i369], w361 ! [i362, i363, i364, i365, i366, i367, i368, i369]] <=. 0.0) 0 1]) ; w379 = rgather [1,1,1,1,1,1,2,2] w357 (\\[i370, i371, i372, i373, i374, i375, i376, i377] -> [i370, i371, i372, i373, i374, i375, i376, i377, w358 ! [i370, i371, i372, i373, i374, i375, i376, i377], w359 ! [i370, i371, i372, i373, i374, i375, i376, i377], w360 ! [i370, i371, i372, i373, i374, i375, i376, i377], w361 ! [i370, i371, i372, i373, i374, i375, i376, i377]]) ; w388 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w378 * w379, rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i380, i381, i382, i383, i384, i385, i386, i387] -> [ifF ((0 <=. i380 + i384 &&* 1 >. i380 + i384) &&* ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. 2 * i382 + i386 &&* 2 >. 2 * i382 + i386) &&* (0 <=. 2 * i383 + i387 &&* 2 >. 2 * i383 + i387)))) 0 1, i380, i381, i382, i383, i384, i385, i386, i387]) ; t395 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w388 (\\[i389, i390, i391, i392] -> [i389, i390, i391, i392, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w388 ! [i389, i390, i391, i392]))) 2) 2, remF (rmaxIndex (rreshape [4] (w388 ! [i389, i390, i391, i392]))) 2]))))) ; m397 = rsum (rtranspose [2,1,0] (rreplicate 1 m612) * t395) + rtranspose [1,0] (rreplicate 1 v613) ; m400 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i398, i399] -> [ifF (m397 ! [i398, i399] <=. 0.0) 0 1]) ; t403 = rtranspose [1,0] (rreplicate 10 (m400 * m397)) in rsum (rtranspose [2,1,0] (rreplicate 1 m614) * t403) + rtranspose [1,0] (rreplicate 1 v615)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m405 u1048 v1049 u1050 v1051 m1052 v1053 m1054 v1055 -> let w292 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i277, i278, i279, i280, i281, i282, i283] -> [ifF ((0 <=. i277 + i280 &&* 1 >. i277 + i280) &&* ((0 <=. i281 &&* 1 >. i281) &&* ((0 <=. i278 + i282 &&* 4 >. i278 + i282) &&* (0 <=. i279 + i283 &&* 4 >. i279 + i283)))) 0 1])))) ; w295 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w292 * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1048 (\\[i285, i286] -> [i285 + i286]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i287, i288, i289, i290, i291] -> [ifF ((0 <=. i287 + i288 &&* 1 >. i287 + i288) &&* ((0 <=. i289 &&* 1 >. i289) &&* ((0 <=. i290 &&* 2 >. i290) &&* (0 <=. i291 &&* 2 >. i291)))) 0 1, i287, i288, i289, i290, i291]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v1049))))))))))) ; w296 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w297 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w299 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w301 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w318 = rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i302, i303, i304, i305, i306, i307, i308, i309] -> [ifF (w295 ! [i302, i303, i304, i305, i306, i307, i308, i309, w296 ! [i302, i303, i304, i305, i306, i307, i308, i309], w297 ! [i302, i303, i304, i305, i306, i307, i308, i309], w299 ! [i302, i303, i304, i305, i306, i307, i308, i309], w301 ! [i302, i303, i304, i305, i306, i307, i308, i309]] <=. 0.0) 0 1]) ; w328 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [w318 * rgather [1,1,2,2,1,1,2,2] w295 (\\[i310, i311, i312, i313, i314, i315, i316, i317] -> [i310, i311, i312, i313, i314, i315, i316, i317, w296 ! [i310, i311, i312, i313, i314, i315, i316, i317], w297 ! [i310, i311, i312, i313, i314, i315, i316, i317], w299 ! [i310, i311, i312, i313, i314, i315, i316, i317], w301 ! [i310, i311, i312, i313, i314, i315, i316, i317]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i320, i321, i322, i323, i324, i325, i326, i327] -> [ifF ((0 <=. i320 + i324 &&* 1 >. i320 + i324) &&* ((0 <=. i321 + i325 &&* 1 >. i321 + i325) &&* ((0 <=. 2 * i322 + i326 &&* 4 >. 2 * i322 + i326) &&* (0 <=. 2 * i323 + i327 &&* 4 >. 2 * i323 + i327)))) 0 1, i320, i321, i322, i323, i324, i325, i326, i327])))))))) ; w329 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w330 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w331 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w354 = rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w328 (\\[i332, i333, i334, i335, i336, i337, i338] -> [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w328 ! [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w328 ! [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 2 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 2 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345])))) ; w355 = rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1050 (\\[i347, i348] -> [i347 + i348]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i349, i350, i351, i352, i353] -> [ifF ((0 <=. i349 + i350 &&* 1 >. i349 + i350) &&* ((0 <=. i351 &&* 1 >. i351) &&* ((0 <=. i352 &&* 2 >. i352) &&* (0 <=. i353 &&* 2 >. i353)))) 0 1, i349, i350, i351, i352, i353])))))) ; w357 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (w354 * w355) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v1051))))))))))) ; w358 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w359 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w360 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w361 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w378 = rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i362, i363, i364, i365, i366, i367, i368, i369] -> [ifF (w357 ! [i362, i363, i364, i365, i366, i367, i368, i369, w358 ! [i362, i363, i364, i365, i366, i367, i368, i369], w359 ! [i362, i363, i364, i365, i366, i367, i368, i369], w360 ! [i362, i363, i364, i365, i366, i367, i368, i369], w361 ! [i362, i363, i364, i365, i366, i367, i368, i369]] <=. 0.0) 0 1]) ; w388 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [w378 * rgather [1,1,1,1,1,1,2,2] w357 (\\[i370, i371, i372, i373, i374, i375, i376, i377] -> [i370, i371, i372, i373, i374, i375, i376, i377, w358 ! [i370, i371, i372, i373, i374, i375, i376, i377], w359 ! [i370, i371, i372, i373, i374, i375, i376, i377], w360 ! [i370, i371, i372, i373, i374, i375, i376, i377], w361 ! [i370, i371, i372, i373, i374, i375, i376, i377]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i380, i381, i382, i383, i384, i385, i386, i387] -> [ifF ((0 <=. i380 + i384 &&* 1 >. i380 + i384) &&* ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. 2 * i382 + i386 &&* 2 >. 2 * i382 + i386) &&* (0 <=. 2 * i383 + i387 &&* 2 >. 2 * i383 + i387)))) 0 1, i380, i381, i382, i383, i384, i385, i386, i387]) ; t395 = rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w388 (\\[i389, i390, i391, i392] -> [i389, i390, i391, i392, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w388 ! [i389, i390, i391, i392]))) 2) 2, remF (rmaxIndex (rreshape [4] (w388 ! [i389, i390, i391, i392]))) 2])))) ; m397 = rsum (rtranspose [2,1,0] (rreplicate 1 m1052) * t395) + rtranspose [1,0] (rreplicate 1 v1053) ; m400 = rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i398, i399] -> [ifF (m397 ! [i398, i399] <=. 0.0) 0 1]) ; m406 = m400 * rsum (rtranspose [1,2,0] (rreplicate 1 m1054) * rtranspose [1,0] (rreplicate 1 m405)) ; u429 = rscatter [1,1,2,2] (w378 * rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] m1052 (\\[i983] -> [i983, 0]) * rgather [1] m406 (\\[i980] -> [i980, 0]))))))) (\\[i408, i409, i410, i411] -> [i408, i409, i410, i411, 0, 0, remF (quotF (rmaxIndex (rgather [4] (w388 ! [i408, i409, i410, i411, 0, 0]) (\\[i973] -> [remF (quotF i973 2) 2, remF i973 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w388 ! [i408, i409, i410, i411, 0, 0]) (\\[i974] -> [remF (quotF i974 2) 2, remF i974 2]))) 2])) (\\[i412, i413, i414, i415, i416, i417, i418, i419] -> [ifF ((0 <=. i412 + i416 &&* 1 >. i412 + i416) &&* ((0 <=. i413 + i417 &&* 1 >. i413 + i417) &&* ((0 <=. 2 * i414 + i418 &&* 2 >. 2 * i414 + i418) &&* (0 <=. 2 * i415 + i419 &&* 2 >. 2 * i415 + i419)))) 0 1, i412, i413, i414, i415, i416, i417, i418, i419]) ! [0]) (\\[i421, i422, i423, i424, i425, i426, i427, i428] -> [w358 ! [i421, i422, i423, i424, i425, i426, i427, i428], w359 ! [i421, i422, i423, i424, i425, i426, i427, i428], w360 ! [i421, i422, i423, i424, i425, i426, i427, i428], w361 ! [i421, i422, i423, i424, i425, i426, i427, i428]]) ; u471 = rscatter [1,1,4,4] (w318 * rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rgather [1,1,2,2,1,1,2,2] (rgather [2,2,4,1] w355 (\\[i957, i958, i959, i956] -> [i959, 0, i956, i957, i958]) * rgather [2,2,4,1] (u429 ! [0]) (\\[i962, i963, i964, i961] -> [i961, i962, i963])) (\\[i965, i966, i967, i968, i969, i970, i971, i972] -> [remF (quotF (i972 + 2 * i971 + 4 * i970 + 4 * i969 + 4 * i968 + 16 * i966 + 8 * i967) 8) 2, remF (quotF (i972 + 2 * i971 + 4 * i970 + 4 * i969 + 4 * i968 + 16 * i966 + 8 * i967) 4) 2, remF (i972 + 2 * i971 + 4 * i970 + 4 * i969 + 4 * i968 + 16 * i966 + 8 * i967) 4, i965]))) (\\[i439, i440, i441, i442, i443, i444, i445] -> [ifF ((0 <=. i439 + i442 &&* 1 >. i439 + i442) &&* ((0 <=. i443 &&* 1 >. i443) &&* ((0 <=. i440 + i444 &&* 2 >. i440 + i444) &&* (0 <=. i441 + i445 &&* 2 >. i441 + i445)))) 0 1, i439, i440, i441, i442, i443, i444, i445]) ! [0]) (\\[i447, i448, i449, i450, i451, i452, i453] -> [w329 ! [i447, i448, i449, i450, i451, i452, i453], i451, w330 ! [i447, i448, i449, i450, i451, i452, i453], w331 ! [i447, i448, i449, i450, i451, i452, i453], 0, 0, remF (quotF (rmaxIndex (rgather [4] (w328 ! [i447, i448, i449, i450, i451, i452, i453, w329 ! [i447, i448, i449, i450, i451, i452, i453], i451, w330 ! [i447, i448, i449, i450, i451, i452, i453], w331 ! [i447, i448, i449, i450, i451, i452, i453], 0, 0]) (\\[i946] -> [remF (quotF i946 2) 2, remF i946 2]))) 2) 2, remF (rmaxIndex (rgather [4] (w328 ! [i447, i448, i449, i450, i451, i452, i453, w329 ! [i447, i448, i449, i450, i451, i452, i453], i451, w330 ! [i447, i448, i449, i450, i451, i452, i453], w331 ! [i447, i448, i449, i450, i451, i452, i453], 0, 0]) (\\[i947] -> [remF (quotF i947 2) 2, remF i947 2]))) 2])) (\\[i454, i455, i456, i457, i458, i459, i460, i461] -> [ifF ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. i455 + i459 &&* 1 >. i455 + i459) &&* ((0 <=. 2 * i456 + i460 &&* 4 >. 2 * i456 + i460) &&* (0 <=. 2 * i457 + i461 &&* 4 >. 2 * i457 + i461)))) 0 1, i454, i455, i456, i457, i458, i459, i460, i461]) ! [0]) (\\[i463, i464, i465, i466, i467, i468, i469, i470] -> [w296 ! [i463, i464, i465, i466, i467, i468, i469, i470], w297 ! [i463, i464, i465, i466, i467, i468, i469, i470], w299 ! [i463, i464, i465, i466, i467, i468, i469, i470], w301 ! [i463, i464, i465, i466, i467, i468, i469, i470]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,4,4,1,1,1,2,2] (rgather [4,1,4,4] w292 (\\[i801, i798] -> [i801, i798, 0]) * rreplicate 4 (rgather [1,4,4] u471 (\\[i803] -> [i803, 0]))) (\\[i861, i862, i863, i864, i865, i866, i867, i868] -> [remF (i868 + 2 * i867 + 4 * i866 + 4 * i864 + 4 * i865) 4, i861, i862, i863]))))) (\\[i472, i473, i474, i475, i476] -> [ifF ((0 <=. i472 + i473 &&* 1 >. i472 + i473) &&* ((0 <=. i474 &&* 1 >. i474) &&* ((0 <=. i475 &&* 2 >. i475) &&* (0 <=. i476 &&* 2 >. i476)))) 0 1, i472, i473, i474, i475, i476]) ! [0]) (\\[i478, i479] -> [i478 + i479]), rsum (rsum (rsum (rtranspose [0,2,3,1] u471))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rgather [1,2,2,1,1,1,2,2] (rgather [4,1,2,2] w354 (\\[i878, i875] -> [i878, i875, 0]) * rreplicate 4 (rgather [1,2,2] u429 (\\[i880] -> [i880, 0]))) (\\[i938, i939, i940, i941, i942, i943, i944, i945] -> [remF (i945 + 2 * i944 + 4 * i943 + 4 * i941 + 4 * i942) 4, i938, i939, i940]))))) (\\[i431, i432, i433, i434, i435] -> [ifF ((0 <=. i431 + i432 &&* 1 >. i431 + i432) &&* ((0 <=. i433 &&* 1 >. i433) &&* ((0 <=. i434 &&* 2 >. i434) &&* (0 <=. i435 &&* 2 >. i435)))) 0 1, i431, i432, i433, i434, i435]) ! [0]) (\\[i437, i438] -> [i437 + i438]), rsum (rsum (rsum (rtranspose [0,2,3,1] u429))), rsum (rtranspose [2,1,0] t395 * rtranspose [2,1,0] (rreplicate 1 m406)), rsum (rtranspose [1,0] m406), rsum (rtranspose [2,0,1] (rreplicate 10 (m400 * m397)) * rtranspose [2,1,0] (rreplicate 1 m405)), rsum (rtranspose [1,0] m405)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\u1368 v1369 u1370 v1371 m1372 v1373 m1374 v1375 -> let w295 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,4,4,4] (rgather [1,4,4,1,1,2,2] (rconst (rfromListLinear [2] [7.0,0.0])) (\\[i277, i278, i279, i280, i281, i282, i283] -> [ifF ((0 <=. i277 + i280 &&* 1 >. i277 + i280) &&* ((0 <=. i281 &&* 1 >. i281) &&* ((0 <=. i278 + i282 &&* 4 >. i278 + i282) &&* (0 <=. i279 + i283 &&* 4 >. i279 + i283)))) 0 1])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1368 (\\[i285, i286] -> [i285 + i286]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i287, i288, i289, i290, i291] -> [ifF ((0 <=. i287 + i288 &&* 1 >. i287 + i288) &&* ((0 <=. i289 &&* 1 >. i289) &&* ((0 <=. i290 &&* 2 >. i290) &&* (0 <=. i291 &&* 2 >. i291)))) 0 1, i287, i288, i289, i290, i291]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v1369))))))))))) ; w296 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w297 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w299 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w301 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))))))) ; w328 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,1,2,2,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i302, i303, i304, i305, i306, i307, i308, i309] -> [ifF (w295 ! [i302, i303, i304, i305, i306, i307, i308, i309, w296 ! [i302, i303, i304, i305, i306, i307, i308, i309], w297 ! [i302, i303, i304, i305, i306, i307, i308, i309], w299 ! [i302, i303, i304, i305, i306, i307, i308, i309], w301 ! [i302, i303, i304, i305, i306, i307, i308, i309]] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,2] w295 (\\[i310, i311, i312, i313, i314, i315, i316, i317] -> [i310, i311, i312, i313, i314, i315, i316, i317, w296 ! [i310, i311, i312, i313, i314, i315, i316, i317], w297 ! [i310, i311, i312, i313, i314, i315, i316, i317], w299 ! [i310, i311, i312, i313, i314, i315, i316, i317], w301 ! [i310, i311, i312, i313, i314, i315, i316, i317]]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i320, i321, i322, i323, i324, i325, i326, i327] -> [ifF ((0 <=. i320 + i324 &&* 1 >. i320 + i324) &&* ((0 <=. i321 + i325 &&* 1 >. i321 + i325) &&* ((0 <=. 2 * i322 + i326 &&* 4 >. 2 * i322 + i326) &&* (0 <=. 2 * i323 + i327 &&* 4 >. 2 * i323 + i327)))) 0 1, i320, i321, i322, i323, i324, i325, i326, i327])))))))) ; w329 = rtranspose [5,0,1,6,2,3,4] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0])))))))) ; w330 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w331 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))))))) ; w357 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rsum (rtranspose [4,1,0,2,3] (rreplicate 1 (rreshape [1,2,2,4] (rgather [1,2,2,1,1,2,2] (rfromVector (fromList [rgather [1,2,2,1,1,2,2] w328 (\\[i332, i333, i334, i335, i336, i337, i338] -> [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338], 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w328 ! [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338]]))) 2) 2, remF (rmaxIndex (rreshape [4] (w328 ! [i332, i333, i334, i335, i336, i337, i338, w329 ! [i332, i333, i334, i335, i336, i337, i338], i336, w330 ! [i332, i333, i334, i335, i336, i337, i338], w331 ! [i332, i333, i334, i335, i336, i337, i338]]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))])) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 2 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 2 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345])))) * rtranspose [4,0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreshape [1,4] (rgather [1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,2,2] u1370 (\\[i347, i348] -> [i347 + i348]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))])) (\\[i349, i350, i351, i352, i353] -> [ifF ((0 <=. i349 + i350 &&* 1 >. i349 + i350) &&* ((0 <=. i351 &&* 1 >. i351) &&* ((0 <=. i352 &&* 2 >. i352) &&* (0 <=. i353 &&* 2 >. i353)))) 0 1, i349, i350, i351, i352, i353]))))))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v1371))))))))))) ; w358 = rtranspose [6,0,1,2,7,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w359 = rtranspose [0,6,1,2,3,7,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [1] [0]))))))))) ; w360 = rtranspose [0,1,6,2,3,4,7,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w361 = rtranspose [0,1,2,6,3,4,5] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (rfromListLinear [1] [0]))) + rreplicate 1 (rconst (rfromListLinear [2] [0,1]))))))))) ; w388 = rgather [1,1,1,1,1,1,2,2] (rfromVector (fromList [rgather [1,1,1,1,1,1,2,2] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i362, i363, i364, i365, i366, i367, i368, i369] -> [ifF (w357 ! [i362, i363, i364, i365, i366, i367, i368, i369, w358 ! [i362, i363, i364, i365, i366, i367, i368, i369], w359 ! [i362, i363, i364, i365, i366, i367, i368, i369], w360 ! [i362, i363, i364, i365, i366, i367, i368, i369], w361 ! [i362, i363, i364, i365, i366, i367, i368, i369]] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w357 (\\[i370, i371, i372, i373, i374, i375, i376, i377] -> [i370, i371, i372, i373, i374, i375, i376, i377, w358 ! [i370, i371, i372, i373, i374, i375, i376, i377], w359 ! [i370, i371, i372, i373, i374, i375, i376, i377], w360 ! [i370, i371, i372, i373, i374, i375, i376, i377], w361 ! [i370, i371, i372, i373, i374, i375, i376, i377]]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))])) (\\[i380, i381, i382, i383, i384, i385, i386, i387] -> [ifF ((0 <=. i380 + i384 &&* 1 >. i380 + i384) &&* ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. 2 * i382 + i386 &&* 2 >. 2 * i382 + i386) &&* (0 <=. 2 * i383 + i387 &&* 2 >. 2 * i383 + i387)))) 0 1, i380, i381, i382, i383, i384, i385, i386, i387]) ; m397 = rsum (rtranspose [2,1,0] (rreplicate 1 m1372) * rtranspose [2,0,1] (rreplicate 1 (rreshape [1,1] (rgather [1,1,1,1] w388 (\\[i389, i390, i391, i392] -> [i389, i390, i391, i392, 0, 0, remF (quotF (rmaxIndex (rreshape [4] (w388 ! [i389, i390, i391, i392]))) 2) 2, remF (rmaxIndex (rreshape [4] (w388 ! [i389, i390, i391, i392]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v1373) in rsum (rtranspose [2,1,0] (rreplicate 1 m1374) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i398, i399] -> [ifF (m397 ! [i398, i399] <=. 0.0) 0 1]) * m397))) + rtranspose [1,0] (rreplicate 1 v1375)"
