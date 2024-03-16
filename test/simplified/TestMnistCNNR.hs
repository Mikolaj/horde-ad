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
import HordeAd.Core.AstFreshId (funToAstIOR, funToAstRevIO, resetVarCounter)
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
       (_, hVectorPrimal, vars, _) <- funToAstRevIO (voidFromHVector hVectorInit)
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
                   (parseHVector (fromDValue valsInit) hVectorPrimal)
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
       let envInit = extendEnvR varGlyph (rconstant astGlyph)
                     $ extendEnvR varLabel (rconstant astLabel)
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
    @?= "\\m464 u1 v2 u3 v4 m5 v6 m7 v8 -> let w348 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 7.0) (\\[i280, i281] -> [i281])) (\\[i282, i283, i284] -> [i283, i284])) (\\[i285, i286, i287, i288] -> [i286, i287, i288])) (\\[i289, i290, i291, i292, i293] -> [i290, i291, i292, i293])) (\\[i294, i295, i296, i297, i298, i299] -> [i295, i296, i297, i298, i299])) (\\[i300, i301, i302, i303, i304, i305, i306] -> [i301, i302, i303, i304, i305, i306]), rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 0.0) (\\[i307, i308] -> [i308])) (\\[i309, i310, i311] -> [i310, i311])) (\\[i312, i313, i314, i315] -> [i313, i314, i315])) (\\[i316, i317, i318, i319, i320] -> [i317, i318, i319, i320])) (\\[i321, i322, i323, i324, i325, i326] -> [i322, i323, i324, i325, i326])) (\\[i327, i328, i329, i330, i331, i332, i333] -> [i328, i329, i330, i331, i332, i333])]) (\\[i334, i335, i336, i337, i338, i339, i340] -> [ifF ((0 <=. i334 + i337 &&* 1 >. i334 + i337) &&* ((0 <=. i338 &&* 1 >. i338) &&* ((0 <=. i335 + i339 &&* 4 >. i335 + i339) &&* (0 <=. i336 + i340 &&* 4 >. i336 + i340)))) 0 1, i334, i335, i336, i337, i338, i339, i340]))) ; w349 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i341, i342] -> [i341 + i342]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i343, i344, i345, i346, i347] -> [ifF ((0 <=. i343 + i344 &&* 1 >. i343 + i344) &&* ((0 <=. i345 &&* 1 >. i345) &&* ((0 <=. i346 &&* 2 >. i346) &&* (0 <=. i347 &&* 2 >. i347)))) 0 1, i343, i344, i345, i346, i347]))))) ; w350 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,4,4,4] (w348 * w349))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w370 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i355, i356, i357, i358, i359, i360, i361, i362] -> [ifF (w350 ! [i355, i356, i357, i358, i359, i360, i361, let w351 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w351 ! [i355, i356, i357, i358, i359, i360, i361], let w352 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i355, i356, i357, i358, i359, i360, i361], let v353 = rconst (fromList [2] [0,1]) ; w354 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v353)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w354 ! [i355, i356, i357, i358, i359, i360, i361], i362] <=. 0.0) 0 1]) ; w371 = rgather [1,1,2,2,1,1,2,4] w350 (\\[i363, i364, i365, i366, i367, i368, i369] -> [i363, i364, i365, i366, i367, i368, i369, let w351 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w351 ! [i363, i364, i365, i366, i367, i368, i369], let w352 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i363, i364, i365, i366, i367, i368, i369], let v353 = rconst (fromList [2] [0,1]) ; w354 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v353)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w354 ! [i363, i364, i365, i366, i367, i368, i369]]) ; w388 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w370 * w371) (\\[i372, i373, i374, i375, i376, i377, i378, i379] -> [i372, i373, i374, i375, i376, i377, i378, 2 * i375 + i379]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i380, i381, i382, i383, i384, i385, i386, i387] -> [ifF ((0 <=. i380 + i384 &&* 1 >. i380 + i384) &&* ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. 2 * i382 + i386 &&* 4 >. 2 * i382 + i386) &&* (0 <=. 2 * i383 + i387 &&* 4 >. 2 * i383 + i387)))) 0 1, i380, i381, i382, i383, i384, i385, i386, i387]))))))) ; w414 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w388 (\\[i391, i392, i393, i394, i395, i396, i397] -> [i391, i392, i393, i394, i395, i396, let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i391, i392, i393, i394, i395, i396], i395, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i391, i392, i393, i394, i395, i396], i393 + i397, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w388 ! [i391, i392, i393, i394, i395, i396, let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i391, i392, i393, i394, i395, i396], i395, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i391, i392, i393, i394, i395, i396], let i398 = i393 + i397 in i398]))) 2) 2, rem (rmaxIndex (rreshape [4] (w388 ! [i391, i392, i393, i394, i395, i396, let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i391, i392, i393, i394, i395, i396], i395, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i391, i392, i393, i394, i395, i396], let i399 = i393 + i397 in i399]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i400, i401, i402, i403, i404, i405, i406] -> [ifF ((0 <=. i400 + i403 &&* 1 >. i400 + i403) &&* ((0 <=. i404 &&* 1 >. i404) &&* ((0 <=. i401 + i405 &&* 2 >. i401 + i405) &&* (0 <=. i402 + i406 &&* 2 >. i402 + i406)))) 0 1, i400, i401, i402, i403, i404, i405, i406]))) ; w415 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i407, i408] -> [i407 + i408]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i409, i410, i411, i412, i413] -> [ifF ((0 <=. i409 + i410 &&* 1 >. i409 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i412 &&* 2 >. i412) &&* (0 <=. i413 &&* 2 >. i413)))) 0 1, i409, i410, i411, i412, i413]))))) ; w416 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,2,2,4] (w414 * w415))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w435 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i420, i421, i422, i423, i424, i425, i426, i427] -> [ifF (w416 ! [i420, i421, i422, i423, i424, i425, i426, let w417 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w417 ! [i420, i421, i422, i423, i424, i425, i426], let w418 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i420, i421, i422, i423, i424, i425, i426], let w419 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w419 ! [i420, i421, i422, i423, i424, i425, i426], i427] <=. 0.0) 0 1]) ; w436 = rgather [1,1,1,1,1,1,2,2] w416 (\\[i428, i429, i430, i431, i432, i433, i434] -> [i428, i429, i430, i431, i432, i433, i434, let w417 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w417 ! [i428, i429, i430, i431, i432, i433, i434], let w418 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i428, i429, i430, i431, i432, i433, i434], let w419 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w419 ! [i428, i429, i430, i431, i432, i433, i434]]) ; w453 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w435 * w436) (\\[i437, i438, i439, i440, i441, i442, i443, i444] -> [i437, i438, i439, i440, i441, i442, i443, 2 * i440 + i444]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [ifF ((0 <=. i445 + i449 &&* 1 >. i445 + i449) &&* ((0 <=. i446 + i450 &&* 1 >. i446 + i450) &&* ((0 <=. 2 * i447 + i451 &&* 2 >. 2 * i447 + i451) &&* (0 <=. 2 * i448 + i452 &&* 2 >. 2 * i448 + i452)))) 0 1, i445, i446, i447, i448, i449, i450, i451, i452]) ; t458 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w453 (\\[i454, i455, i456, i457] -> [i454, i455, i456, i457, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w453 ! [i454, i455, i456, i457]))) 2) 2, rem (rmaxIndex (rreshape [4] (w453 ! [i454, i455, i456, i457]))) 2]))))) ; m459 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t458) + rtranspose [1,0] (rreplicate 1 v6) ; m462 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i460, i461] -> [ifF (m459 ! [i460, i461] <=. 0.0) 0 1]) ; t463 = rtranspose [1,0] (rreplicate 10 (m462 * m459)) in let [m465 @Natural @Double @[10,1]] = [m464] in let m466 = m462 * rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m465)) ; w479 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rsum (rtranspose [1,0] (rreplicate 1 m5) * rtranspose [1,2,0] (rreplicate 1 m466)))) (\\[i467, i468, i469, i470] -> [i467, i468, i469, i470, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w453 ! [i467, i468, i469, i470]))) 2) 2, rem (rmaxIndex (rreshape [4] (w453 ! [i467, i468, i469, i470]))) 2])) (\\[i471, i472, i473, i474, i475, i476, i477, i478] -> [ifF ((0 <=. i471 + i475 &&* 1 >. i471 + i475) &&* ((0 <=. i472 + i476 &&* 1 >. i472 + i476) &&* ((0 <=. 2 * i473 + i477 &&* 2 >. 2 * i473 + i477) &&* (0 <=. 2 * i474 + i478 &&* 2 >. 2 * i474 + i478)))) 0 1, i471, i472, i473, i474, i475, i476, i477, i478]) ; u495 = rscatter [1,1,2,2] (w435 * rscatter [1,1,1,1,1,1,2,2] (w479 ! [0]) (\\[i480, i481, i482, i483, i484, i485, i486, i487] -> [i480, i481, i482, i483, i484, i485, i486, 2 * i483 + i487])) (\\[i488, i489, i490, i491, i492, i493, i494] -> [let w417 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w417 ! [i488, i489, i490, i491, i492, i493, i494], let w418 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i488, i489, i490, i491, i492, i493, i494], let w419 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w419 ! [i488, i489, i490, i491, i492, i493, i494]]) ; w496 = rreshape [1,1,2,2,1,1,2,2] (rtranspose [1,2,3,4,0] (rreplicate 4 u495)) ; w502 = rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w414 * w496))))) (\\[i497, i498, i499, i500, i501] -> [ifF ((0 <=. i497 + i498 &&* 1 >. i497 + i498) &&* ((0 <=. i499 &&* 1 >. i499) &&* ((0 <=. i500 &&* 2 >. i500) &&* (0 <=. i501 &&* 2 >. i501)))) 0 1, i497, i498, i499, i500, i501]) ; w512 = rscatter [2,1,2,2,1,1,2,2] (rsum (rtranspose [1,0] (w415 * w496))) (\\[i505, i506, i507, i508, i509, i510, i511] -> [ifF ((0 <=. i505 + i508 &&* 1 >. i505 + i508) &&* ((0 <=. i509 &&* 1 >. i509) &&* ((0 <=. i506 + i510 &&* 2 >. i506 + i510) &&* (0 <=. i507 + i511 &&* 2 >. i507 + i511)))) 0 1, i505, i506, i507, i508, i509, i510, i511]) ; w530 = rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (w512 ! [0]) (\\[i513, i514, i515, i516, i517, i518, i519] -> [let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i513, i514, i515, i516, i517, i518], i517, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i513, i514, i515, i516, i517, i518], i515 + i519, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w388 ! [i513, i514, i515, i516, i517, i518, let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i513, i514, i515, i516, i517, i518], i517, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i513, i514, i515, i516, i517, i518], let i520 = i515 + i519 in i520]))) 2) 2, rem (rmaxIndex (rreshape [4] (w388 ! [i513, i514, i515, i516, i517, i518, let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i513, i514, i515, i516, i517, i518], i517, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i513, i514, i515, i516, i517, i518], let i521 = i515 + i519 in i521]))) 2])) (\\[i522, i523, i524, i525, i526, i527, i528, i529] -> [ifF ((0 <=. i522 + i526 &&* 1 >. i522 + i526) &&* ((0 <=. i523 + i527 &&* 1 >. i523 + i527) &&* ((0 <=. 2 * i524 + i528 &&* 4 >. 2 * i524 + i528) &&* (0 <=. 2 * i525 + i529 &&* 4 >. 2 * i525 + i529)))) 0 1, i522, i523, i524, i525, i526, i527, i528, i529]) ; u546 = rscatter [1,1,4,4] (w370 * rscatter [1,1,2,2,1,1,2,4] (w530 ! [0]) (\\[i531, i532, i533, i534, i535, i536, i537, i538] -> [i531, i532, i533, i534, i535, i536, i537, 2 * i534 + i538])) (\\[i539, i540, i541, i542, i543, i544, i545] -> [let w351 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w351 ! [i539, i540, i541, i542, i543, i544, i545], let w352 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i539, i540, i541, i542, i543, i544, i545], let v353 = rconst (fromList [2] [0,1]) ; w354 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v353)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w354 ! [i539, i540, i541, i542, i543, i544, i545]]) ; w552 = rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w348 * rreshape [1,1,4,4,1,1,2,2] (rtranspose [1,2,3,4,0] (rreplicate 4 u546))))))) (\\[i547, i548, i549, i550, i551] -> [ifF ((0 <=. i547 + i548 &&* 1 >. i547 + i548) &&* ((0 <=. i549 &&* 1 >. i549) &&* ((0 <=. i550 &&* 2 >. i550) &&* (0 <=. i551 &&* 2 >. i551)))) 0 1, i547, i548, i549, i550, i551]) in [rscatter [1,1,2,2] (w552 ! [0]) (\\[i553, i554] -> [i553 + i554]), rsum (rsum (rsum (rtranspose [0,2,3,1] u546))), rscatter [1,1,2,2] (w502 ! [0]) (\\[i503, i504] -> [i503 + i504]), rsum (rsum (rsum (rtranspose [0,2,3,1] u495))), rsum (rtranspose [2,1,0] (t458 * rreplicate 1 m466)), rsum (rtranspose [1,0] m466), rsum (rtranspose [2,1,0] (t463 * rreplicate 1 m465)), rsum (rtranspose [1,0] m465)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w348 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 7.0) (\\[i280, i281] -> [i281])) (\\[i282, i283, i284] -> [i283, i284])) (\\[i285, i286, i287, i288] -> [i286, i287, i288])) (\\[i289, i290, i291, i292, i293] -> [i290, i291, i292, i293])) (\\[i294, i295, i296, i297, i298, i299] -> [i295, i296, i297, i298, i299])) (\\[i300, i301, i302, i303, i304, i305, i306] -> [i301, i302, i303, i304, i305, i306]), rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 0.0) (\\[i307, i308] -> [i308])) (\\[i309, i310, i311] -> [i310, i311])) (\\[i312, i313, i314, i315] -> [i313, i314, i315])) (\\[i316, i317, i318, i319, i320] -> [i317, i318, i319, i320])) (\\[i321, i322, i323, i324, i325, i326] -> [i322, i323, i324, i325, i326])) (\\[i327, i328, i329, i330, i331, i332, i333] -> [i328, i329, i330, i331, i332, i333])]) (\\[i334, i335, i336, i337, i338, i339, i340] -> [ifF ((0 <=. i334 + i337 &&* 1 >. i334 + i337) &&* ((0 <=. i338 &&* 1 >. i338) &&* ((0 <=. i335 + i339 &&* 4 >. i335 + i339) &&* (0 <=. i336 + i340 &&* 4 >. i336 + i340)))) 0 1, i334, i335, i336, i337, i338, i339, i340]))) ; w349 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i341, i342] -> [i341 + i342]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i343, i344, i345, i346, i347] -> [ifF ((0 <=. i343 + i344 &&* 1 >. i343 + i344) &&* ((0 <=. i345 &&* 1 >. i345) &&* ((0 <=. i346 &&* 2 >. i346) &&* (0 <=. i347 &&* 2 >. i347)))) 0 1, i343, i344, i345, i346, i347]))))) ; w350 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,4,4,4] (w348 * w349))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w370 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i355, i356, i357, i358, i359, i360, i361, i362] -> [ifF (w350 ! [i355, i356, i357, i358, i359, i360, i361, let w351 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w351 ! [i355, i356, i357, i358, i359, i360, i361], let w352 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i355, i356, i357, i358, i359, i360, i361], let v353 = rconst (fromList [2] [0,1]) ; w354 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v353)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w354 ! [i355, i356, i357, i358, i359, i360, i361], i362] <=. 0.0) 0 1]) ; w371 = rgather [1,1,2,2,1,1,2,4] w350 (\\[i363, i364, i365, i366, i367, i368, i369] -> [i363, i364, i365, i366, i367, i368, i369, let w351 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w351 ! [i363, i364, i365, i366, i367, i368, i369], let w352 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i363, i364, i365, i366, i367, i368, i369], let v353 = rconst (fromList [2] [0,1]) ; w354 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v353)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w354 ! [i363, i364, i365, i366, i367, i368, i369]]) ; w388 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w370 * w371) (\\[i372, i373, i374, i375, i376, i377, i378, i379] -> [i372, i373, i374, i375, i376, i377, i378, 2 * i375 + i379]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i380, i381, i382, i383, i384, i385, i386, i387] -> [ifF ((0 <=. i380 + i384 &&* 1 >. i380 + i384) &&* ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. 2 * i382 + i386 &&* 4 >. 2 * i382 + i386) &&* (0 <=. 2 * i383 + i387 &&* 4 >. 2 * i383 + i387)))) 0 1, i380, i381, i382, i383, i384, i385, i386, i387]))))))) ; w414 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w388 (\\[i391, i392, i393, i394, i395, i396, i397] -> [i391, i392, i393, i394, i395, i396, let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i391, i392, i393, i394, i395, i396], i395, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i391, i392, i393, i394, i395, i396], i393 + i397, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w388 ! [i391, i392, i393, i394, i395, i396, let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i391, i392, i393, i394, i395, i396], i395, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i391, i392, i393, i394, i395, i396], let i398 = i393 + i397 in i398]))) 2) 2, rem (rmaxIndex (rreshape [4] (w388 ! [i391, i392, i393, i394, i395, i396, let w389 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w389 ! [i391, i392, i393, i394, i395, i396], i395, let w390 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w390 ! [i391, i392, i393, i394, i395, i396], let i399 = i393 + i397 in i399]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i400, i401, i402, i403, i404, i405, i406] -> [ifF ((0 <=. i400 + i403 &&* 1 >. i400 + i403) &&* ((0 <=. i404 &&* 1 >. i404) &&* ((0 <=. i401 + i405 &&* 2 >. i401 + i405) &&* (0 <=. i402 + i406 &&* 2 >. i402 + i406)))) 0 1, i400, i401, i402, i403, i404, i405, i406]))) ; w415 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i407, i408] -> [i407 + i408]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i409, i410, i411, i412, i413] -> [ifF ((0 <=. i409 + i410 &&* 1 >. i409 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i412 &&* 2 >. i412) &&* (0 <=. i413 &&* 2 >. i413)))) 0 1, i409, i410, i411, i412, i413]))))) ; w416 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,2,2,4] (w414 * w415))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w435 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i420, i421, i422, i423, i424, i425, i426, i427] -> [ifF (w416 ! [i420, i421, i422, i423, i424, i425, i426, let w417 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w417 ! [i420, i421, i422, i423, i424, i425, i426], let w418 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i420, i421, i422, i423, i424, i425, i426], let w419 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w419 ! [i420, i421, i422, i423, i424, i425, i426], i427] <=. 0.0) 0 1]) ; w436 = rgather [1,1,1,1,1,1,2,2] w416 (\\[i428, i429, i430, i431, i432, i433, i434] -> [i428, i429, i430, i431, i432, i433, i434, let w417 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w417 ! [i428, i429, i430, i431, i432, i433, i434], let w418 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i428, i429, i430, i431, i432, i433, i434], let w419 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w419 ! [i428, i429, i430, i431, i432, i433, i434]]) ; w453 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w435 * w436) (\\[i437, i438, i439, i440, i441, i442, i443, i444] -> [i437, i438, i439, i440, i441, i442, i443, 2 * i440 + i444]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [ifF ((0 <=. i445 + i449 &&* 1 >. i445 + i449) &&* ((0 <=. i446 + i450 &&* 1 >. i446 + i450) &&* ((0 <=. 2 * i447 + i451 &&* 2 >. 2 * i447 + i451) &&* (0 <=. 2 * i448 + i452 &&* 2 >. 2 * i448 + i452)))) 0 1, i445, i446, i447, i448, i449, i450, i451, i452]) ; t458 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w453 (\\[i454, i455, i456, i457] -> [i454, i455, i456, i457, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w453 ! [i454, i455, i456, i457]))) 2) 2, rem (rmaxIndex (rreshape [4] (w453 ! [i454, i455, i456, i457]))) 2]))))) ; m459 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t458) + rtranspose [1,0] (rreplicate 1 v6) ; m462 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i460, i461] -> [ifF (m459 ! [i460, i461] <=. 0.0) 0 1]) ; t463 = rtranspose [1,0] (rreplicate 10 (m462 * m459)) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * t463) + rtranspose [1,0] (rreplicate 1 v8)]"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m464 u1 v2 u3 v4 m5 v6 m7 v8 -> let w348 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rreplicate 1 (rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 7.0)))))), rreplicate 1 (rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i334, i335, i336, i337, i338, i339, i340] -> [ifF ((0 <=. i334 + i337 &&* 1 >. i334 + i337) &&* ((0 <=. i338 &&* 1 >. i338) &&* ((0 <=. i335 + i339 &&* 4 >. i335 + i339) &&* (0 <=. i336 + i340 &&* 4 >. i336 + i340)))) 0 1, i334, i335, i336, i337, i338, i339, i340]))) ; w350 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,4,4] (w348 ! [0, 0] * rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 u1), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i631, i632, i633, i634, i635, i636] -> [ifF ((0 <=. i633 &&* 1 >. i633) &&* ((0 <=. i634 &&* 1 >. i634) &&* ((0 <=. i635 &&* 2 >. i635) &&* (0 <=. i636 &&* 2 >. i636)))) 0 1, i631, i632, i633, i634, i635, i636])) (\\[i610, i611, i612, i613, i614] -> [rem (quot (i610 + 4 * i614 + 16 * i613 + 64 * i611 + 64 * i612) 16) 4, rem (quot (i610 + 4 * i614 + 16 * i613 + 64 * i611 + 64 * i612) 4) 4, 0, 0, rem (quot (i610 + 4 * i614 + 16 * i613 + 64 * i611 + 64 * i612) 2) 2, rem (i610 + 4 * i614 + 16 * i613 + 64 * i611 + 64 * i612) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w370 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i355, i356, i357, i358, i359, i360, i361, i362] -> [ifF (w350 ! [i355, i356, i357, i358, i359, i360, i361, rconst (fromList [1] [0]) ! [i355] + rconst (fromList [1] [0]) ! [i359], rconst (fromList [1] [0]) ! [i356] + rconst (fromList [1] [0]) ! [i360], 2 * rconst (fromList [2] [0,1]) ! [i357] + rconst (fromList [2] [0,1]) ! [i361], i362] <=. 0.0) 0 1]) ; w388 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w370 * rgather [1,1,2,2,1,1,2,4] w350 (\\[i363, i364, i365, i366, i367, i368, i369] -> [i363, i364, i365, i366, i367, i368, i369, rconst (fromList [1] [0]) ! [i363] + rconst (fromList [1] [0]) ! [i367], rconst (fromList [1] [0]) ! [i364] + rconst (fromList [1] [0]) ! [i368], 2 * rconst (fromList [2] [0,1]) ! [i365] + rconst (fromList [2] [0,1]) ! [i369]])) (\\[i372, i373, i374, i375, i376, i377, i378, i379] -> [i372, i373, i374, i375, i376, i377, i378, 2 * i375 + i379]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i380, i381, i382, i383, i384, i385, i386, i387] -> [ifF ((0 <=. i380 + i384 &&* 1 >. i380 + i384) &&* ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. 2 * i382 + i386 &&* 4 >. 2 * i382 + i386) &&* (0 <=. 2 * i383 + i387 &&* 4 >. 2 * i383 + i387)))) 0 1, i380, i381, i382, i383, i384, i385, i386, i387]))))))) ; w414 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w388 (\\[i391, i392, i393, i394, i395, i396, i397] -> [i391, i392, i393, i394, i395, i396, rconst (fromList [1] [0]) ! [i391] + rconst (fromList [1] [0]) ! [i394], i395, rconst (fromList [2] [0,1]) ! [i392] + rconst (fromList [2] [0,1]) ! [i396], i393 + i397, 0, 0, rem (quot (rmaxIndex (rgather [4] (w388 ! [i391, i392, i393, i394, i395, i396, rconst (fromList [1] [0]) ! [i391] + rconst (fromList [1] [0]) ! [i394], i395, rconst (fromList [2] [0,1]) ! [i392] + rconst (fromList [2] [0,1]) ! [i396], i393 + i397, 0, 0]) (\\[i608] -> [rem (quot i608 2) 2, rem i608 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w388 ! [i391, i392, i393, i394, i395, i396, rconst (fromList [1] [0]) ! [i391] + rconst (fromList [1] [0]) ! [i394], i395, rconst (fromList [2] [0,1]) ! [i392] + rconst (fromList [2] [0,1]) ! [i396], i393 + i397, 0, 0]) (\\[i609] -> [rem (quot i609 2) 2, rem i609 2]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i400, i401, i402, i403, i404, i405, i406] -> [ifF ((0 <=. i400 + i403 &&* 1 >. i400 + i403) &&* ((0 <=. i404 &&* 1 >. i404) &&* ((0 <=. i401 + i405 &&* 2 >. i401 + i405) &&* (0 <=. i402 + i406 &&* 2 >. i402 + i406)))) 0 1, i400, i401, i402, i403, i404, i405, i406]))) ; w415 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i407, i408] -> [i407 + i408]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i409, i410, i411, i412, i413] -> [ifF ((0 <=. i409 + i410 &&* 1 >. i409 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i412 &&* 2 >. i412) &&* (0 <=. i413 &&* 2 >. i413)))) 0 1, i409, i410, i411, i412, i413]))))) ; w416 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,2,2] (w414 ! [0, 0] * w415 ! [0, 0]) (\\[i598, i599, i600, i601, i602] -> [rem (quot (i598 + 4 * i602 + 8 * i601 + 16 * i599 + 16 * i600) 8) 2, rem (quot (i598 + 4 * i602 + 8 * i601 + 16 * i599 + 16 * i600) 4) 2, 0, 0, rem (quot (i598 + 4 * i602 + 8 * i601 + 16 * i599 + 16 * i600) 2) 2, rem (i598 + 4 * i602 + 8 * i601 + 16 * i599 + 16 * i600) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w435 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i420, i421, i422, i423, i424, i425, i426, i427] -> [ifF (w416 ! [i420, i421, i422, i423, i424, i425, i426, rconst (fromList [1] [0]) ! [i420] + rconst (fromList [1] [0]) ! [i424], rconst (fromList [1] [0]) ! [i421] + rconst (fromList [1] [0]) ! [i425], 2 * rconst (fromList [1] [0]) ! [i422] + rconst (fromList [2] [0,1]) ! [i426], i427] <=. 0.0) 0 1]) ; w453 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w435 * rgather [1,1,1,1,1,1,2,2] w416 (\\[i428, i429, i430, i431, i432, i433, i434] -> [i428, i429, i430, i431, i432, i433, i434, rconst (fromList [1] [0]) ! [i428] + rconst (fromList [1] [0]) ! [i432], rconst (fromList [1] [0]) ! [i429] + rconst (fromList [1] [0]) ! [i433], 2 * rconst (fromList [1] [0]) ! [i430] + rconst (fromList [2] [0,1]) ! [i434]])) (\\[i437, i438, i439, i440, i441, i442, i443, i444] -> [i437, i438, i439, i440, i441, i442, i443, 2 * i440 + i444]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [ifF ((0 <=. i445 + i449 &&* 1 >. i445 + i449) &&* ((0 <=. i446 + i450 &&* 1 >. i446 + i450) &&* ((0 <=. 2 * i447 + i451 &&* 2 >. 2 * i447 + i451) &&* (0 <=. 2 * i448 + i452 &&* 2 >. 2 * i448 + i452)))) 0 1, i445, i446, i447, i448, i449, i450, i451, i452]) ; t458 = rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 (w453 ! [0, 0, 0, 0, 0, 0, rem (quot (rmaxIndex (rgather [4] (w453 ! [0, 0, 0, 0, 0, 0]) (\\[i594] -> [rem (quot i594 2) 2, rem i594 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w453 ! [0, 0, 0, 0, 0, 0]) (\\[i595] -> [rem (quot i595 2) 2, rem i595 2]))) 2])))) ; m459 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t458) + rtranspose [1,0] (rreplicate 1 v6) ; m462 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i460, i461] -> [ifF (m459 ! [i460, i461] <=. 0.0) 0 1]) ; m466 = m462 * rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m464)) ; u495 = rscatter [1,1,2,2] (w435 * rscatter [1,1,1,1,1,1,2,2] (rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] (m5 * rgather [1,1] m466 (\\[i590, i591] -> [i590, 0])) (\\[i593] -> [i593, 0]))))))) (\\[i467, i468, i469, i470] -> [i467, i468, i469, i470, 0, 0, rem (quot (rmaxIndex (rgather [4] (w453 ! [i467, i468, i469, i470, 0, 0]) (\\[i583] -> [rem (quot i583 2) 2, rem i583 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w453 ! [i467, i468, i469, i470, 0, 0]) (\\[i584] -> [rem (quot i584 2) 2, rem i584 2]))) 2])) (\\[i471, i472, i473, i474, i475, i476, i477, i478] -> [ifF ((0 <=. i471 + i475 &&* 1 >. i471 + i475) &&* ((0 <=. i472 + i476 &&* 1 >. i472 + i476) &&* ((0 <=. 2 * i473 + i477 &&* 2 >. 2 * i473 + i477) &&* (0 <=. 2 * i474 + i478 &&* 2 >. 2 * i474 + i478)))) 0 1, i471, i472, i473, i474, i475, i476, i477, i478]) ! [0]) (\\[i480, i481, i482, i483, i484, i485, i486, i487] -> [i480, i481, i482, i483, i484, i485, i486, 2 * i483 + i487])) (\\[i488, i489, i490, i491, i492, i493, i494] -> [rconst (fromList [1] [0]) ! [i488] + rconst (fromList [1] [0]) ! [i492], rconst (fromList [1] [0]) ! [i489] + rconst (fromList [1] [0]) ! [i493], 2 * rconst (fromList [1] [0]) ! [i490] + rconst (fromList [2] [0,1]) ! [i494]]) ; w496 = rgather [1,1,2,2,1,1,2,2] (u495 ! [0, 0]) (\\[i570, i571, i572, i573, i574, i575, i576, i577] -> [rem (quot (i577 + 2 * i576 + 4 * i575 + 4 * i574 + 4 * i573 + 8 * i572 + 16 * i570 + 16 * i571) 8) 2, rem (quot (i577 + 2 * i576 + 4 * i575 + 4 * i574 + 4 * i573 + 8 * i572 + 16 * i570 + 16 * i571) 4) 2]) ; u546 = rscatter [1,1,4,4] (w370 * rscatter [1,1,2,2,1,1,2,4] (rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rtranspose [1,0] (w415 * w496))) (\\[i505, i506, i507, i508, i509, i510, i511] -> [ifF ((0 <=. i505 + i508 &&* 1 >. i505 + i508) &&* ((0 <=. i509 &&* 1 >. i509) &&* ((0 <=. i506 + i510 &&* 2 >. i506 + i510) &&* (0 <=. i507 + i511 &&* 2 >. i507 + i511)))) 0 1, i505, i506, i507, i508, i509, i510, i511]) ! [0]) (\\[i513, i514, i515, i516, i517, i518, i519] -> [rconst (fromList [1] [0]) ! [i513] + rconst (fromList [1] [0]) ! [i516], i517, rconst (fromList [2] [0,1]) ! [i514] + rconst (fromList [2] [0,1]) ! [i518], i515 + i519, 0, 0, rem (quot (rmaxIndex (rgather [4] (w388 ! [i513, i514, i515, i516, i517, i518, rconst (fromList [1] [0]) ! [i513] + rconst (fromList [1] [0]) ! [i516], i517, rconst (fromList [2] [0,1]) ! [i514] + rconst (fromList [2] [0,1]) ! [i518], i515 + i519, 0, 0]) (\\[i568] -> [rem (quot i568 2) 2, rem i568 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w388 ! [i513, i514, i515, i516, i517, i518, rconst (fromList [1] [0]) ! [i513] + rconst (fromList [1] [0]) ! [i516], i517, rconst (fromList [2] [0,1]) ! [i514] + rconst (fromList [2] [0,1]) ! [i518], i515 + i519, 0, 0]) (\\[i569] -> [rem (quot i569 2) 2, rem i569 2]))) 2])) (\\[i522, i523, i524, i525, i526, i527, i528, i529] -> [ifF ((0 <=. i522 + i526 &&* 1 >. i522 + i526) &&* ((0 <=. i523 + i527 &&* 1 >. i523 + i527) &&* ((0 <=. 2 * i524 + i528 &&* 4 >. 2 * i524 + i528) &&* (0 <=. 2 * i525 + i529 &&* 4 >. 2 * i525 + i529)))) 0 1, i522, i523, i524, i525, i526, i527, i528, i529]) ! [0]) (\\[i531, i532, i533, i534, i535, i536, i537, i538] -> [i531, i532, i533, i534, i535, i536, i537, 2 * i534 + i538])) (\\[i539, i540, i541, i542, i543, i544, i545] -> [rconst (fromList [1] [0]) ! [i539] + rconst (fromList [1] [0]) ! [i543], rconst (fromList [1] [0]) ! [i540] + rconst (fromList [1] [0]) ! [i544], 2 * rconst (fromList [2] [0,1]) ! [i541] + rconst (fromList [2] [0,1]) ! [i545]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w348 * rgather [1,1,4,4,1,1,2,2] (u546 ! [0, 0]) (\\[i555, i556, i557, i558, i559, i560, i561, i562] -> [rem (quot (i562 + 2 * i561 + 4 * i560 + 4 * i559 + 4 * i558 + 16 * i557 + 64 * i555 + 64 * i556) 16) 4, rem (quot (i562 + 2 * i561 + 4 * i560 + 4 * i559 + 4 * i558 + 16 * i557 + 64 * i555 + 64 * i556) 4) 4])))))) (\\[i547, i548, i549, i550, i551] -> [ifF ((0 <=. i547 + i548 &&* 1 >. i547 + i548) &&* ((0 <=. i549 &&* 1 >. i549) &&* ((0 <=. i550 &&* 2 >. i550) &&* (0 <=. i551 &&* 2 >. i551)))) 0 1, i547, i548, i549, i550, i551]) ! [0]) (\\[i553, i554] -> [i553 + i554]), rsum (rsum (rsum (rtranspose [0,2,3,1] u546))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w414 * w496))))) (\\[i497, i498, i499, i500, i501] -> [ifF ((0 <=. i497 + i498 &&* 1 >. i497 + i498) &&* ((0 <=. i499 &&* 1 >. i499) &&* ((0 <=. i500 &&* 2 >. i500) &&* (0 <=. i501 &&* 2 >. i501)))) 0 1, i497, i498, i499, i500, i501]) ! [0]) (\\[i503, i504] -> [i503 + i504]), rsum (rsum (rsum (rtranspose [0,2,3,1] u495))), rsum (rtranspose [2,1,0] (t458 * rreplicate 1 m466)), rsum (rtranspose [1,0] m466), rsum (rtranspose [2,0,1] (rreplicate 10 (m462 * m459)) * rtranspose [2,1,0] (rreplicate 1 m464)), rsum (rtranspose [1,0] m464)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w350 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,4,4] (rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 7.0))))), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i731, i732, i733, i734, i735, i736] -> [ifF ((0 <=. i733 &&* 1 >. i733) &&* ((0 <=. i734 &&* 1 >. i734) &&* ((0 <=. i731 + i735 &&* 4 >. i731 + i735) &&* (0 <=. i732 + i736 &&* 4 >. i732 + i736)))) 0 1, i731, i732, i733, i734, i735, i736]) * rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 u1), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i737, i738, i739, i740, i741, i742] -> [ifF ((0 <=. i739 &&* 1 >. i739) &&* ((0 <=. i740 &&* 1 >. i740) &&* ((0 <=. i741 &&* 2 >. i741) &&* (0 <=. i742 &&* 2 >. i742)))) 0 1, i737, i738, i739, i740, i741, i742])) (\\[i693, i694, i695, i696, i697] -> [rem (quot (i693 + 4 * i697 + 16 * i696 + 64 * i694 + 64 * i695) 16) 4, rem (quot (i693 + 4 * i697 + 16 * i696 + 64 * i694 + 64 * i695) 4) 4, 0, 0, rem (quot (i693 + 4 * i697 + 16 * i696 + 64 * i694 + 64 * i695) 2) 2, rem (i693 + 4 * i697 + 16 * i696 + 64 * i694 + 64 * i695) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w388 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i355, i356, i357, i358, i359, i360, i361, i362] -> [ifF (w350 ! [i355, i356, i357, i358, i359, i360, i361, rconst (fromList [1] [0]) ! [i355] + rconst (fromList [1] [0]) ! [i359], rconst (fromList [1] [0]) ! [i356] + rconst (fromList [1] [0]) ! [i360], 2 * rconst (fromList [2] [0,1]) ! [i357] + rconst (fromList [2] [0,1]) ! [i361], i362] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,4] w350 (\\[i363, i364, i365, i366, i367, i368, i369] -> [i363, i364, i365, i366, i367, i368, i369, rconst (fromList [1] [0]) ! [i363] + rconst (fromList [1] [0]) ! [i367], rconst (fromList [1] [0]) ! [i364] + rconst (fromList [1] [0]) ! [i368], 2 * rconst (fromList [2] [0,1]) ! [i365] + rconst (fromList [2] [0,1]) ! [i369]])) (\\[i372, i373, i374, i375, i376, i377, i378, i379] -> [i372, i373, i374, i375, i376, i377, i378, 2 * i375 + i379]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i380, i381, i382, i383, i384, i385, i386, i387] -> [ifF ((0 <=. i380 + i384 &&* 1 >. i380 + i384) &&* ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. 2 * i382 + i386 &&* 4 >. 2 * i382 + i386) &&* (0 <=. 2 * i383 + i387 &&* 4 >. 2 * i383 + i387)))) 0 1, i380, i381, i382, i383, i384, i385, i386, i387]))))))) ; w416 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,2,2] (rgather [2,2,1,1,2,2] (rfromList [rgather [2,2,1,1,2,2] (w388 ! [0]) (\\[i392, i393, i394, i395, i396, i397] -> [i392, i393, i394, i395, i396, rconst (fromList [1] [0]) ! [i394], i395, rconst (fromList [2] [0,1]) ! [i392] + rconst (fromList [2] [0,1]) ! [i396], i393 + i397, 0, 0, rem (quot (rmaxIndex (rgather [4] (w388 ! [0, i392, i393, i394, i395, i396, rconst (fromList [1] [0]) ! [i394], i395, rconst (fromList [2] [0,1]) ! [i392] + rconst (fromList [2] [0,1]) ! [i396], i393 + i397, 0, 0]) (\\[i641] -> [rem (quot i641 2) 2, rem i641 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w388 ! [0, i392, i393, i394, i395, i396, rconst (fromList [1] [0]) ! [i394], i395, rconst (fromList [2] [0,1]) ! [i392] + rconst (fromList [2] [0,1]) ! [i396], i393 + i397, 0, 0]) (\\[i642] -> [rem (quot i642 2) 2, rem i642 2]))) 2]), rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i681, i682, i683, i684, i685, i686] -> [ifF ((0 <=. i683 &&* 1 >. i683) &&* ((0 <=. i684 &&* 1 >. i684) &&* ((0 <=. i681 + i685 &&* 2 >. i681 + i685) &&* (0 <=. i682 + i686 &&* 2 >. i682 + i686)))) 0 1, i681, i682, i683, i684, i685, i686]) * rgather [2,2,1,1,2,2] (rfromList [rreplicate 2 (rreplicate 2 u3), rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i687, i688, i689, i690, i691, i692] -> [ifF ((0 <=. i689 &&* 1 >. i689) &&* ((0 <=. i690 &&* 1 >. i690) &&* ((0 <=. i691 &&* 2 >. i691) &&* (0 <=. i692 &&* 2 >. i692)))) 0 1, i687, i688, i689, i690, i691, i692])) (\\[i643, i644, i645, i646, i647] -> [rem (quot (i643 + 4 * i647 + 8 * i646 + 16 * i644 + 16 * i645) 8) 2, rem (quot (i643 + 4 * i647 + 8 * i646 + 16 * i644 + 16 * i645) 4) 2, 0, 0, rem (quot (i643 + 4 * i647 + 8 * i646 + 16 * i644 + 16 * i645) 2) 2, rem (i643 + 4 * i647 + 8 * i646 + 16 * i644 + 16 * i645) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w453 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i420, i421, i422, i423, i424, i425, i426, i427] -> [ifF (w416 ! [i420, i421, i422, i423, i424, i425, i426, rconst (fromList [1] [0]) ! [i420] + rconst (fromList [1] [0]) ! [i424], rconst (fromList [1] [0]) ! [i421] + rconst (fromList [1] [0]) ! [i425], 2 * rconst (fromList [1] [0]) ! [i422] + rconst (fromList [2] [0,1]) ! [i426], i427] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w416 (\\[i428, i429, i430, i431, i432, i433, i434] -> [i428, i429, i430, i431, i432, i433, i434, rconst (fromList [1] [0]) ! [i428] + rconst (fromList [1] [0]) ! [i432], rconst (fromList [1] [0]) ! [i429] + rconst (fromList [1] [0]) ! [i433], 2 * rconst (fromList [1] [0]) ! [i430] + rconst (fromList [2] [0,1]) ! [i434]])) (\\[i437, i438, i439, i440, i441, i442, i443, i444] -> [i437, i438, i439, i440, i441, i442, i443, 2 * i440 + i444]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [ifF ((0 <=. i445 + i449 &&* 1 >. i445 + i449) &&* ((0 <=. i446 + i450 &&* 1 >. i446 + i450) &&* ((0 <=. 2 * i447 + i451 &&* 2 >. 2 * i447 + i451) &&* (0 <=. 2 * i448 + i452 &&* 2 >. 2 * i448 + i452)))) 0 1, i445, i446, i447, i448, i449, i450, i451, i452]) ; m459 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 (w453 ! [0, 0, 0, 0, 0, 0, rem (quot (rmaxIndex (rgather [4] (w453 ! [0, 0, 0, 0, 0, 0]) (\\[i637] -> [rem (quot i637 2) 2, rem i637 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w453 ! [0, 0, 0, 0, 0, 0]) (\\[i638] -> [rem (quot i638 2) 2, rem i638 2]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v6) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i460, i461] -> [ifF (m459 ! [i460, i461] <=. 0.0) 0 1]) * m459))) + rtranspose [1,0] (rreplicate 1 v8)]"
