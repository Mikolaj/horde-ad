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
      hVectorInit = toHVector valsInit
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
      hVectorInit = toHVector valsInit
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
           (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
           id
       (varLabel, _, astLabel) <-
         funToAstIOR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
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
        hVectorInit = toHVector valsInit
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
           (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
           id
       (varLabel, varLabelD, astLabel) <-
         funToAstIOR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
       let envInit = extendEnvR varGlyph (rconstant astGlyph)
                     $ extendEnvR varLabel (rconstant astLabel)
                       EM.empty
           f = MnistCnnRanked2.convMnistLossFusedR
                 miniBatchSize (astGlyph, astLabel)
           (((varDtAgain, vars1Again), gradientRaw, primal, sh), _) =
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
                   fst $ revEvalArtifact (vars, gradient, primal, sh)
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
    @?= "\\m473 u1 v2 u3 v4 m5 v6 m7 v8 -> let w352 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 7.0) (\\[i284, i285] -> [i285])) (\\[i286, i287, i288] -> [i287, i288])) (\\[i289, i290, i291, i292] -> [i290, i291, i292])) (\\[i293, i294, i295, i296, i297] -> [i294, i295, i296, i297])) (\\[i298, i299, i300, i301, i302, i303] -> [i299, i300, i301, i302, i303])) (\\[i304, i305, i306, i307, i308, i309, i310] -> [i305, i306, i307, i308, i309, i310]), rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 0.0) (\\[i311, i312] -> [i312])) (\\[i313, i314, i315] -> [i314, i315])) (\\[i316, i317, i318, i319] -> [i317, i318, i319])) (\\[i320, i321, i322, i323, i324] -> [i321, i322, i323, i324])) (\\[i325, i326, i327, i328, i329, i330] -> [i326, i327, i328, i329, i330])) (\\[i331, i332, i333, i334, i335, i336, i337] -> [i332, i333, i334, i335, i336, i337])]) (\\[i338, i339, i340, i341, i342, i343, i344] -> [ifF ((0 <=. i338 + i341 &&* 1 >. i338 + i341) &&* ((0 <=. i342 &&* 1 >. i342) &&* ((0 <=. i339 + i343 &&* 4 >. i339 + i343) &&* (0 <=. i340 + i344 &&* 4 >. i340 + i344)))) 0 1, i338, i339, i340, i341, i342, i343, i344]))) ; w353 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i345, i346] -> [i345 + i346]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i347, i348, i349, i350, i351] -> [ifF ((0 <=. i347 + i348 &&* 1 >. i347 + i348) &&* ((0 <=. i349 &&* 1 >. i349) &&* ((0 <=. i350 &&* 2 >. i350) &&* (0 <=. i351 &&* 2 >. i351)))) 0 1, i347, i348, i349, i350, i351]))))) ; w354 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,4,4,4] (w352 * w353))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w374 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i359, i360, i361, i362, i363, i364, i365, i366] -> [ifF (w354 ! [i359, i360, i361, i362, i363, i364, i365, let w355 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w355 ! [i359, i360, i361, i362, i363, i364, i365], let w356 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i359, i360, i361, i362, i363, i364, i365], let v357 = rconst (fromList [2] [0,1]) ; w358 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v357)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w358 ! [i359, i360, i361, i362, i363, i364, i365], i366] <=. 0.0) 0 1]) ; w375 = rgather [1,1,2,2,1,1,2,4] w354 (\\[i367, i368, i369, i370, i371, i372, i373] -> [i367, i368, i369, i370, i371, i372, i373, let w355 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w355 ! [i367, i368, i369, i370, i371, i372, i373], let w356 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i367, i368, i369, i370, i371, i372, i373], let v357 = rconst (fromList [2] [0,1]) ; w358 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v357)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w358 ! [i367, i368, i369, i370, i371, i372, i373]]) ; w392 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w374 * w375) (\\[i376, i377, i378, i379, i380, i381, i382, i383] -> [i376, i377, i378, i379, i380, i381, i382, 2 * i379 + i383]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i384, i385, i386, i387, i388, i389, i390, i391] -> [ifF ((0 <=. i384 + i388 &&* 1 >. i384 + i388) &&* ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. 2 * i386 + i390 &&* 4 >. 2 * i386 + i390) &&* (0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391)))) 0 1, i384, i385, i386, i387, i388, i389, i390, i391]))))))) ; w420 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w392 (\\[i395, i396, i397, i398, i399, i400, i401] -> [i395, i396, i397, i398, i399, i400, let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i395, i396, i397, i398, i399, i400], i399, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i395, i396, i397, i398, i399, i400], i397 + i401, 0, 0, rem (quot (rmaxIndex (rgather [4] (w392 ! [i395, i396, i397, i398, i399, i400, let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i395, i396, i397, i398, i399, i400], i399, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i395, i396, i397, i398, i399, i400], let i402 = i397 + i401 in i402, 0, 0]) (\\[i403] -> [rem (quot i403 2) 2, rem i403 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w392 ! [i395, i396, i397, i398, i399, i400, let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i395, i396, i397, i398, i399, i400], i399, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i395, i396, i397, i398, i399, i400], let i404 = i397 + i401 in i404, 0, 0]) (\\[i405] -> [rem (quot i405 2) 2, rem i405 2]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i406, i407, i408, i409, i410, i411, i412] -> [ifF ((0 <=. i406 + i409 &&* 1 >. i406 + i409) &&* ((0 <=. i410 &&* 1 >. i410) &&* ((0 <=. i407 + i411 &&* 2 >. i407 + i411) &&* (0 <=. i408 + i412 &&* 2 >. i408 + i412)))) 0 1, i406, i407, i408, i409, i410, i411, i412]))) ; w421 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i413, i414] -> [i413 + i414]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i415, i416, i417, i418, i419] -> [ifF ((0 <=. i415 + i416 &&* 1 >. i415 + i416) &&* ((0 <=. i417 &&* 1 >. i417) &&* ((0 <=. i418 &&* 2 >. i418) &&* (0 <=. i419 &&* 2 >. i419)))) 0 1, i415, i416, i417, i418, i419]))))) ; w422 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,2,2,4] (w420 * w421))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w442 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i427, i428, i429, i430, i431, i432, i433, i434] -> [ifF (w422 ! [i427, i428, i429, i430, i431, i432, i433, let w423 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w423 ! [i427, i428, i429, i430, i431, i432, i433], let w424 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i427, i428, i429, i430, i431, i432, i433], let v425 = rconst (fromList [1] [0]) ; w426 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * v425)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w426 ! [i427, i428, i429, i430, i431, i432, i433], i434] <=. 0.0) 0 1]) ; w443 = rgather [1,1,1,1,1,1,2,2] w422 (\\[i435, i436, i437, i438, i439, i440, i441] -> [i435, i436, i437, i438, i439, i440, i441, let w423 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w423 ! [i435, i436, i437, i438, i439, i440, i441], let w424 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i435, i436, i437, i438, i439, i440, i441], let v425 = rconst (fromList [1] [0]) ; w426 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * v425)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w426 ! [i435, i436, i437, i438, i439, i440, i441]]) ; w460 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w442 * w443) (\\[i444, i445, i446, i447, i448, i449, i450, i451] -> [i444, i445, i446, i447, i448, i449, i450, 2 * i447 + i451]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [ifF ((0 <=. i452 + i456 &&* 1 >. i452 + i456) &&* ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. 2 * i454 + i458 &&* 2 >. 2 * i454 + i458) &&* (0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459)))) 0 1, i452, i453, i454, i455, i456, i457, i458, i459]) ; t467 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w460 (\\[i461, i462, i463, i464] -> [i461, i462, i463, i464, 0, 0, rem (quot (rmaxIndex (rgather [4] (w460 ! [i461, i462, i463, i464, 0, 0]) (\\[i465] -> [rem (quot i465 2) 2, rem i465 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w460 ! [i461, i462, i463, i464, 0, 0]) (\\[i466] -> [rem (quot i466 2) 2, rem i466 2]))) 2]))))) ; m468 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t467) + rtranspose [1,0] (rreplicate 1 v6) ; m471 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i469, i470] -> [ifF (m468 ! [i469, i470] <=. 0.0) 0 1]) ; t472 = rtranspose [1,0] (rreplicate 10 (m471 * m468)) in let [m474 @Natural @Double @[10,1]] = [m473] in let m475 = m471 * rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m474)) ; w490 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rsum (rtranspose [1,0] (rreplicate 1 m5) * rtranspose [1,2,0] (rreplicate 1 m475)))) (\\[i476, i477, i478, i479] -> [i476, i477, i478, i479, 0, 0, rem (quot (rmaxIndex (rgather [4] (w460 ! [i476, i477, i478, i479, 0, 0]) (\\[i480] -> [rem (quot i480 2) 2, rem i480 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w460 ! [i476, i477, i478, i479, 0, 0]) (\\[i481] -> [rem (quot i481 2) 2, rem i481 2]))) 2])) (\\[i482, i483, i484, i485, i486, i487, i488, i489] -> [ifF ((0 <=. i482 + i486 &&* 1 >. i482 + i486) &&* ((0 <=. i483 + i487 &&* 1 >. i483 + i487) &&* ((0 <=. 2 * i484 + i488 &&* 2 >. 2 * i484 + i488) &&* (0 <=. 2 * i485 + i489 &&* 2 >. 2 * i485 + i489)))) 0 1, i482, i483, i484, i485, i486, i487, i488, i489]) ; u506 = rscatter [1,1,2,2] (w442 * rscatter [1,1,1,1,1,1,2,2] (w490 ! [0]) (\\[i491, i492, i493, i494, i495, i496, i497, i498] -> [i491, i492, i493, i494, i495, i496, i497, 2 * i494 + i498])) (\\[i499, i500, i501, i502, i503, i504, i505] -> [let w423 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w423 ! [i499, i500, i501, i502, i503, i504, i505], let w424 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i499, i500, i501, i502, i503, i504, i505], let v425 = rconst (fromList [1] [0]) ; w426 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * v425)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w426 ! [i499, i500, i501, i502, i503, i504, i505]]) ; w507 = rreshape [1,1,2,2,1,1,2,2] (rtranspose [1,2,3,4,0] (rreplicate 4 u506)) ; w513 = rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w420 * w507))))) (\\[i508, i509, i510, i511, i512] -> [ifF ((0 <=. i508 + i509 &&* 1 >. i508 + i509) &&* ((0 <=. i510 &&* 1 >. i510) &&* ((0 <=. i511 &&* 2 >. i511) &&* (0 <=. i512 &&* 2 >. i512)))) 0 1, i508, i509, i510, i511, i512]) ; w523 = rscatter [2,1,2,2,1,1,2,2] (rsum (rtranspose [1,0] (w421 * w507))) (\\[i516, i517, i518, i519, i520, i521, i522] -> [ifF ((0 <=. i516 + i519 &&* 1 >. i516 + i519) &&* ((0 <=. i520 &&* 1 >. i520) &&* ((0 <=. i517 + i521 &&* 2 >. i517 + i521) &&* (0 <=. i518 + i522 &&* 2 >. i518 + i522)))) 0 1, i516, i517, i518, i519, i520, i521, i522]) ; w543 = rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (w523 ! [0]) (\\[i524, i525, i526, i527, i528, i529, i530] -> [let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i524, i525, i526, i527, i528, i529], i528, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i524, i525, i526, i527, i528, i529], i526 + i530, 0, 0, rem (quot (rmaxIndex (rgather [4] (w392 ! [i524, i525, i526, i527, i528, i529, let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i524, i525, i526, i527, i528, i529], i528, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i524, i525, i526, i527, i528, i529], let i531 = i526 + i530 in i531, 0, 0]) (\\[i532] -> [rem (quot i532 2) 2, rem i532 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w392 ! [i524, i525, i526, i527, i528, i529, let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i524, i525, i526, i527, i528, i529], i528, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i524, i525, i526, i527, i528, i529], let i533 = i526 + i530 in i533, 0, 0]) (\\[i534] -> [rem (quot i534 2) 2, rem i534 2]))) 2])) (\\[i535, i536, i537, i538, i539, i540, i541, i542] -> [ifF ((0 <=. i535 + i539 &&* 1 >. i535 + i539) &&* ((0 <=. i536 + i540 &&* 1 >. i536 + i540) &&* ((0 <=. 2 * i537 + i541 &&* 4 >. 2 * i537 + i541) &&* (0 <=. 2 * i538 + i542 &&* 4 >. 2 * i538 + i542)))) 0 1, i535, i536, i537, i538, i539, i540, i541, i542]) ; u559 = rscatter [1,1,4,4] (w374 * rscatter [1,1,2,2,1,1,2,4] (w543 ! [0]) (\\[i544, i545, i546, i547, i548, i549, i550, i551] -> [i544, i545, i546, i547, i548, i549, i550, 2 * i547 + i551])) (\\[i552, i553, i554, i555, i556, i557, i558] -> [let w355 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w355 ! [i552, i553, i554, i555, i556, i557, i558], let w356 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i552, i553, i554, i555, i556, i557, i558], let v357 = rconst (fromList [2] [0,1]) ; w358 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v357)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w358 ! [i552, i553, i554, i555, i556, i557, i558]]) ; w565 = rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w352 * rreshape [1,1,4,4,1,1,2,2] (rtranspose [1,2,3,4,0] (rreplicate 4 u559))))))) (\\[i560, i561, i562, i563, i564] -> [ifF ((0 <=. i560 + i561 &&* 1 >. i560 + i561) &&* ((0 <=. i562 &&* 1 >. i562) &&* ((0 <=. i563 &&* 2 >. i563) &&* (0 <=. i564 &&* 2 >. i564)))) 0 1, i560, i561, i562, i563, i564]) in [rscatter [1,1,2,2] (w565 ! [0]) (\\[i566, i567] -> [i566 + i567]), rsum (rsum (rsum (rtranspose [0,2,3,1] u559))), rscatter [1,1,2,2] (w513 ! [0]) (\\[i514, i515] -> [i514 + i515]), rsum (rsum (rsum (rtranspose [0,2,3,1] u506))), rsum (rtranspose [2,1,0] (t467 * rreplicate 1 m475)), rsum (rtranspose [1,0] m475), rsum (rtranspose [2,1,0] (t472 * rreplicate 1 m474)), rsum (rtranspose [1,0] m474)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w352 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 7.0) (\\[i284, i285] -> [i285])) (\\[i286, i287, i288] -> [i287, i288])) (\\[i289, i290, i291, i292] -> [i290, i291, i292])) (\\[i293, i294, i295, i296, i297] -> [i294, i295, i296, i297])) (\\[i298, i299, i300, i301, i302, i303] -> [i299, i300, i301, i302, i303])) (\\[i304, i305, i306, i307, i308, i309, i310] -> [i305, i306, i307, i308, i309, i310]), rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 0.0) (\\[i311, i312] -> [i312])) (\\[i313, i314, i315] -> [i314, i315])) (\\[i316, i317, i318, i319] -> [i317, i318, i319])) (\\[i320, i321, i322, i323, i324] -> [i321, i322, i323, i324])) (\\[i325, i326, i327, i328, i329, i330] -> [i326, i327, i328, i329, i330])) (\\[i331, i332, i333, i334, i335, i336, i337] -> [i332, i333, i334, i335, i336, i337])]) (\\[i338, i339, i340, i341, i342, i343, i344] -> [ifF ((0 <=. i338 + i341 &&* 1 >. i338 + i341) &&* ((0 <=. i342 &&* 1 >. i342) &&* ((0 <=. i339 + i343 &&* 4 >. i339 + i343) &&* (0 <=. i340 + i344 &&* 4 >. i340 + i344)))) 0 1, i338, i339, i340, i341, i342, i343, i344]))) ; w353 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i345, i346] -> [i345 + i346]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i347, i348, i349, i350, i351] -> [ifF ((0 <=. i347 + i348 &&* 1 >. i347 + i348) &&* ((0 <=. i349 &&* 1 >. i349) &&* ((0 <=. i350 &&* 2 >. i350) &&* (0 <=. i351 &&* 2 >. i351)))) 0 1, i347, i348, i349, i350, i351]))))) ; w354 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,4,4,4] (w352 * w353))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w374 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i359, i360, i361, i362, i363, i364, i365, i366] -> [ifF (w354 ! [i359, i360, i361, i362, i363, i364, i365, let w355 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w355 ! [i359, i360, i361, i362, i363, i364, i365], let w356 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i359, i360, i361, i362, i363, i364, i365], let v357 = rconst (fromList [2] [0,1]) ; w358 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v357)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w358 ! [i359, i360, i361, i362, i363, i364, i365], i366] <=. 0.0) 0 1]) ; w375 = rgather [1,1,2,2,1,1,2,4] w354 (\\[i367, i368, i369, i370, i371, i372, i373] -> [i367, i368, i369, i370, i371, i372, i373, let w355 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w355 ! [i367, i368, i369, i370, i371, i372, i373], let w356 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i367, i368, i369, i370, i371, i372, i373], let v357 = rconst (fromList [2] [0,1]) ; w358 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v357)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w358 ! [i367, i368, i369, i370, i371, i372, i373]]) ; w392 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w374 * w375) (\\[i376, i377, i378, i379, i380, i381, i382, i383] -> [i376, i377, i378, i379, i380, i381, i382, 2 * i379 + i383]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i384, i385, i386, i387, i388, i389, i390, i391] -> [ifF ((0 <=. i384 + i388 &&* 1 >. i384 + i388) &&* ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. 2 * i386 + i390 &&* 4 >. 2 * i386 + i390) &&* (0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391)))) 0 1, i384, i385, i386, i387, i388, i389, i390, i391]))))))) ; w420 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w392 (\\[i395, i396, i397, i398, i399, i400, i401] -> [i395, i396, i397, i398, i399, i400, let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i395, i396, i397, i398, i399, i400], i399, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i395, i396, i397, i398, i399, i400], i397 + i401, 0, 0, rem (quot (rmaxIndex (rgather [4] (w392 ! [i395, i396, i397, i398, i399, i400, let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i395, i396, i397, i398, i399, i400], i399, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i395, i396, i397, i398, i399, i400], let i402 = i397 + i401 in i402, 0, 0]) (\\[i403] -> [rem (quot i403 2) 2, rem i403 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w392 ! [i395, i396, i397, i398, i399, i400, let w393 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w393 ! [i395, i396, i397, i398, i399, i400], i399, let w394 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w394 ! [i395, i396, i397, i398, i399, i400], let i404 = i397 + i401 in i404, 0, 0]) (\\[i405] -> [rem (quot i405 2) 2, rem i405 2]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i406, i407, i408, i409, i410, i411, i412] -> [ifF ((0 <=. i406 + i409 &&* 1 >. i406 + i409) &&* ((0 <=. i410 &&* 1 >. i410) &&* ((0 <=. i407 + i411 &&* 2 >. i407 + i411) &&* (0 <=. i408 + i412 &&* 2 >. i408 + i412)))) 0 1, i406, i407, i408, i409, i410, i411, i412]))) ; w421 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i413, i414] -> [i413 + i414]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i415, i416, i417, i418, i419] -> [ifF ((0 <=. i415 + i416 &&* 1 >. i415 + i416) &&* ((0 <=. i417 &&* 1 >. i417) &&* ((0 <=. i418 &&* 2 >. i418) &&* (0 <=. i419 &&* 2 >. i419)))) 0 1, i415, i416, i417, i418, i419]))))) ; w422 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,2,2,4] (w420 * w421))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w442 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i427, i428, i429, i430, i431, i432, i433, i434] -> [ifF (w422 ! [i427, i428, i429, i430, i431, i432, i433, let w423 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w423 ! [i427, i428, i429, i430, i431, i432, i433], let w424 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i427, i428, i429, i430, i431, i432, i433], let v425 = rconst (fromList [1] [0]) ; w426 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * v425)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w426 ! [i427, i428, i429, i430, i431, i432, i433], i434] <=. 0.0) 0 1]) ; w443 = rgather [1,1,1,1,1,1,2,2] w422 (\\[i435, i436, i437, i438, i439, i440, i441] -> [i435, i436, i437, i438, i439, i440, i441, let w423 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w423 ! [i435, i436, i437, i438, i439, i440, i441], let w424 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i435, i436, i437, i438, i439, i440, i441], let v425 = rconst (fromList [1] [0]) ; w426 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * v425)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w426 ! [i435, i436, i437, i438, i439, i440, i441]]) ; w460 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w442 * w443) (\\[i444, i445, i446, i447, i448, i449, i450, i451] -> [i444, i445, i446, i447, i448, i449, i450, 2 * i447 + i451]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [ifF ((0 <=. i452 + i456 &&* 1 >. i452 + i456) &&* ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. 2 * i454 + i458 &&* 2 >. 2 * i454 + i458) &&* (0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459)))) 0 1, i452, i453, i454, i455, i456, i457, i458, i459]) ; t467 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w460 (\\[i461, i462, i463, i464] -> [i461, i462, i463, i464, 0, 0, rem (quot (rmaxIndex (rgather [4] (w460 ! [i461, i462, i463, i464, 0, 0]) (\\[i465] -> [rem (quot i465 2) 2, rem i465 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w460 ! [i461, i462, i463, i464, 0, 0]) (\\[i466] -> [rem (quot i466 2) 2, rem i466 2]))) 2]))))) ; m468 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t467) + rtranspose [1,0] (rreplicate 1 v6) ; m471 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i469, i470] -> [ifF (m468 ! [i469, i470] <=. 0.0) 0 1]) ; t472 = rtranspose [1,0] (rreplicate 10 (m471 * m468)) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * t472) + rtranspose [1,0] (rreplicate 1 v8)]"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m473 u1 v2 u3 v4 m5 v6 m7 v8 -> let w352 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rreplicate 1 (rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 7.0)))))), rreplicate 1 (rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i338, i339, i340, i341, i342, i343, i344] -> [ifF ((0 <=. i338 + i341 &&* 1 >. i338 + i341) &&* ((0 <=. i342 &&* 1 >. i342) &&* ((0 <=. i339 + i343 &&* 4 >. i339 + i343) &&* (0 <=. i340 + i344 &&* 4 >. i340 + i344)))) 0 1, i338, i339, i340, i341, i342, i343, i344]))) ; w354 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,4,4] (w352 ! [0, 0] * rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 u1), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i636, i637, i638, i639, i640, i641] -> [ifF ((0 <=. i638 &&* 1 >. i638) &&* ((0 <=. i639 &&* 1 >. i639) &&* ((0 <=. i640 &&* 2 >. i640) &&* (0 <=. i641 &&* 2 >. i641)))) 0 1, i636, i637, i638, i639, i640, i641])) (\\[i615, i616, i617, i618, i619] -> [rem (quot (i615 + 4 * i619 + 16 * i618 + 64 * i616 + 64 * i617) 16) 4, rem (quot (i615 + 4 * i619 + 16 * i618 + 64 * i616 + 64 * i617) 4) 4, 0, 0, rem (quot (i615 + 4 * i619 + 16 * i618 + 64 * i616 + 64 * i617) 2) 2, rem (i615 + 4 * i619 + 16 * i618 + 64 * i616 + 64 * i617) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w374 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i359, i360, i361, i362, i363, i364, i365, i366] -> [ifF (w354 ! [i359, i360, i361, i362, i363, i364, i365, rconst (fromList [1] [0]) ! [i359] + rconst (fromList [1] [0]) ! [i363], rconst (fromList [1] [0]) ! [i360] + rconst (fromList [1] [0]) ! [i364], 2 * rconst (fromList [2] [0,1]) ! [i361] + rconst (fromList [2] [0,1]) ! [i365], i366] <=. 0.0) 0 1]) ; w392 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w374 * rgather [1,1,2,2,1,1,2,4] w354 (\\[i367, i368, i369, i370, i371, i372, i373] -> [i367, i368, i369, i370, i371, i372, i373, rconst (fromList [1] [0]) ! [i367] + rconst (fromList [1] [0]) ! [i371], rconst (fromList [1] [0]) ! [i368] + rconst (fromList [1] [0]) ! [i372], 2 * rconst (fromList [2] [0,1]) ! [i369] + rconst (fromList [2] [0,1]) ! [i373]])) (\\[i376, i377, i378, i379, i380, i381, i382, i383] -> [i376, i377, i378, i379, i380, i381, i382, 2 * i379 + i383]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i384, i385, i386, i387, i388, i389, i390, i391] -> [ifF ((0 <=. i384 + i388 &&* 1 >. i384 + i388) &&* ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. 2 * i386 + i390 &&* 4 >. 2 * i386 + i390) &&* (0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391)))) 0 1, i384, i385, i386, i387, i388, i389, i390, i391]))))))) ; w420 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w392 (\\[i395, i396, i397, i398, i399, i400, i401] -> [i395, i396, i397, i398, i399, i400, rconst (fromList [1] [0]) ! [i395] + rconst (fromList [1] [0]) ! [i398], i399, rconst (fromList [2] [0,1]) ! [i396] + rconst (fromList [2] [0,1]) ! [i400], i397 + i401, 0, 0, rem (quot (rmaxIndex (rgather [4] (w392 ! [i395, i396, i397, i398, i399, i400, rconst (fromList [1] [0]) ! [i395] + rconst (fromList [1] [0]) ! [i398], i399, rconst (fromList [2] [0,1]) ! [i396] + rconst (fromList [2] [0,1]) ! [i400], i397 + i401, 0, 0]) (\\[i403] -> [rem (quot i403 2) 2, rem i403 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w392 ! [i395, i396, i397, i398, i399, i400, rconst (fromList [1] [0]) ! [i395] + rconst (fromList [1] [0]) ! [i398], i399, rconst (fromList [2] [0,1]) ! [i396] + rconst (fromList [2] [0,1]) ! [i400], i397 + i401, 0, 0]) (\\[i405] -> [rem (quot i405 2) 2, rem i405 2]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i406, i407, i408, i409, i410, i411, i412] -> [ifF ((0 <=. i406 + i409 &&* 1 >. i406 + i409) &&* ((0 <=. i410 &&* 1 >. i410) &&* ((0 <=. i407 + i411 &&* 2 >. i407 + i411) &&* (0 <=. i408 + i412 &&* 2 >. i408 + i412)))) 0 1, i406, i407, i408, i409, i410, i411, i412]))) ; w421 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i413, i414] -> [i413 + i414]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i415, i416, i417, i418, i419] -> [ifF ((0 <=. i415 + i416 &&* 1 >. i415 + i416) &&* ((0 <=. i417 &&* 1 >. i417) &&* ((0 <=. i418 &&* 2 >. i418) &&* (0 <=. i419 &&* 2 >. i419)))) 0 1, i415, i416, i417, i418, i419]))))) ; w422 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,2,2] (w420 ! [0, 0] * w421 ! [0, 0]) (\\[i605, i606, i607, i608, i609] -> [rem (quot (i605 + 4 * i609 + 8 * i608 + 16 * i606 + 16 * i607) 8) 2, rem (quot (i605 + 4 * i609 + 8 * i608 + 16 * i606 + 16 * i607) 4) 2, 0, 0, rem (quot (i605 + 4 * i609 + 8 * i608 + 16 * i606 + 16 * i607) 2) 2, rem (i605 + 4 * i609 + 8 * i608 + 16 * i606 + 16 * i607) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w442 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i427, i428, i429, i430, i431, i432, i433, i434] -> [ifF (w422 ! [i427, i428, i429, i430, i431, i432, i433, rconst (fromList [1] [0]) ! [i427] + rconst (fromList [1] [0]) ! [i431], rconst (fromList [1] [0]) ! [i428] + rconst (fromList [1] [0]) ! [i432], 2 * rconst (fromList [1] [0]) ! [i429] + rconst (fromList [2] [0,1]) ! [i433], i434] <=. 0.0) 0 1]) ; w460 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w442 * rgather [1,1,1,1,1,1,2,2] w422 (\\[i435, i436, i437, i438, i439, i440, i441] -> [i435, i436, i437, i438, i439, i440, i441, rconst (fromList [1] [0]) ! [i435] + rconst (fromList [1] [0]) ! [i439], rconst (fromList [1] [0]) ! [i436] + rconst (fromList [1] [0]) ! [i440], 2 * rconst (fromList [1] [0]) ! [i437] + rconst (fromList [2] [0,1]) ! [i441]])) (\\[i444, i445, i446, i447, i448, i449, i450, i451] -> [i444, i445, i446, i447, i448, i449, i450, 2 * i447 + i451]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [ifF ((0 <=. i452 + i456 &&* 1 >. i452 + i456) &&* ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. 2 * i454 + i458 &&* 2 >. 2 * i454 + i458) &&* (0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459)))) 0 1, i452, i453, i454, i455, i456, i457, i458, i459]) ; t467 = rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 (w460 ! [0, 0, 0, 0, 0, 0, rem (quot (rmaxIndex (rgather [4] (w460 ! [0, 0, 0, 0, 0, 0]) (\\[i465] -> [rem (quot i465 2) 2, rem i465 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w460 ! [0, 0, 0, 0, 0, 0]) (\\[i466] -> [rem (quot i466 2) 2, rem i466 2]))) 2])))) ; m468 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t467) + rtranspose [1,0] (rreplicate 1 v6) ; m471 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i469, i470] -> [ifF (m468 ! [i469, i470] <=. 0.0) 0 1]) ; m475 = m471 * rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m473)) ; u506 = rscatter [1,1,2,2] (w442 * rscatter [1,1,1,1,1,1,2,2] (rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] (m5 * rgather [1,1] m475 (\\[i599, i600] -> [i599, 0])) (\\[i602] -> [i602, 0]))))))) (\\[i476, i477, i478, i479] -> [i476, i477, i478, i479, 0, 0, rem (quot (rmaxIndex (rgather [4] (w460 ! [i476, i477, i478, i479, 0, 0]) (\\[i480] -> [rem (quot i480 2) 2, rem i480 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w460 ! [i476, i477, i478, i479, 0, 0]) (\\[i481] -> [rem (quot i481 2) 2, rem i481 2]))) 2])) (\\[i482, i483, i484, i485, i486, i487, i488, i489] -> [ifF ((0 <=. i482 + i486 &&* 1 >. i482 + i486) &&* ((0 <=. i483 + i487 &&* 1 >. i483 + i487) &&* ((0 <=. 2 * i484 + i488 &&* 2 >. 2 * i484 + i488) &&* (0 <=. 2 * i485 + i489 &&* 2 >. 2 * i485 + i489)))) 0 1, i482, i483, i484, i485, i486, i487, i488, i489]) ! [0]) (\\[i491, i492, i493, i494, i495, i496, i497, i498] -> [i491, i492, i493, i494, i495, i496, i497, 2 * i494 + i498])) (\\[i499, i500, i501, i502, i503, i504, i505] -> [rconst (fromList [1] [0]) ! [i499] + rconst (fromList [1] [0]) ! [i503], rconst (fromList [1] [0]) ! [i500] + rconst (fromList [1] [0]) ! [i504], 2 * rconst (fromList [1] [0]) ! [i501] + rconst (fromList [2] [0,1]) ! [i505]]) ; w507 = rgather [1,1,2,2,1,1,2,2] (u506 ! [0, 0]) (\\[i581, i582, i583, i584, i585, i586, i587, i588] -> [rem (quot (i588 + 2 * i587 + 4 * i586 + 4 * i585 + 4 * i584 + 8 * i583 + 16 * i581 + 16 * i582) 8) 2, rem (quot (i588 + 2 * i587 + 4 * i586 + 4 * i585 + 4 * i584 + 8 * i583 + 16 * i581 + 16 * i582) 4) 2]) ; u559 = rscatter [1,1,4,4] (w374 * rscatter [1,1,2,2,1,1,2,4] (rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rtranspose [1,0] (w421 * w507))) (\\[i516, i517, i518, i519, i520, i521, i522] -> [ifF ((0 <=. i516 + i519 &&* 1 >. i516 + i519) &&* ((0 <=. i520 &&* 1 >. i520) &&* ((0 <=. i517 + i521 &&* 2 >. i517 + i521) &&* (0 <=. i518 + i522 &&* 2 >. i518 + i522)))) 0 1, i516, i517, i518, i519, i520, i521, i522]) ! [0]) (\\[i524, i525, i526, i527, i528, i529, i530] -> [rconst (fromList [1] [0]) ! [i524] + rconst (fromList [1] [0]) ! [i527], i528, rconst (fromList [2] [0,1]) ! [i525] + rconst (fromList [2] [0,1]) ! [i529], i526 + i530, 0, 0, rem (quot (rmaxIndex (rgather [4] (w392 ! [i524, i525, i526, i527, i528, i529, rconst (fromList [1] [0]) ! [i524] + rconst (fromList [1] [0]) ! [i527], i528, rconst (fromList [2] [0,1]) ! [i525] + rconst (fromList [2] [0,1]) ! [i529], i526 + i530, 0, 0]) (\\[i532] -> [rem (quot i532 2) 2, rem i532 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w392 ! [i524, i525, i526, i527, i528, i529, rconst (fromList [1] [0]) ! [i524] + rconst (fromList [1] [0]) ! [i527], i528, rconst (fromList [2] [0,1]) ! [i525] + rconst (fromList [2] [0,1]) ! [i529], i526 + i530, 0, 0]) (\\[i534] -> [rem (quot i534 2) 2, rem i534 2]))) 2])) (\\[i535, i536, i537, i538, i539, i540, i541, i542] -> [ifF ((0 <=. i535 + i539 &&* 1 >. i535 + i539) &&* ((0 <=. i536 + i540 &&* 1 >. i536 + i540) &&* ((0 <=. 2 * i537 + i541 &&* 4 >. 2 * i537 + i541) &&* (0 <=. 2 * i538 + i542 &&* 4 >. 2 * i538 + i542)))) 0 1, i535, i536, i537, i538, i539, i540, i541, i542]) ! [0]) (\\[i544, i545, i546, i547, i548, i549, i550, i551] -> [i544, i545, i546, i547, i548, i549, i550, 2 * i547 + i551])) (\\[i552, i553, i554, i555, i556, i557, i558] -> [rconst (fromList [1] [0]) ! [i552] + rconst (fromList [1] [0]) ! [i556], rconst (fromList [1] [0]) ! [i553] + rconst (fromList [1] [0]) ! [i557], 2 * rconst (fromList [2] [0,1]) ! [i554] + rconst (fromList [2] [0,1]) ! [i558]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w352 * rgather [1,1,4,4,1,1,2,2] (u559 ! [0, 0]) (\\[i568, i569, i570, i571, i572, i573, i574, i575] -> [rem (quot (i575 + 2 * i574 + 4 * i573 + 4 * i572 + 4 * i571 + 16 * i570 + 64 * i568 + 64 * i569) 16) 4, rem (quot (i575 + 2 * i574 + 4 * i573 + 4 * i572 + 4 * i571 + 16 * i570 + 64 * i568 + 64 * i569) 4) 4])))))) (\\[i560, i561, i562, i563, i564] -> [ifF ((0 <=. i560 + i561 &&* 1 >. i560 + i561) &&* ((0 <=. i562 &&* 1 >. i562) &&* ((0 <=. i563 &&* 2 >. i563) &&* (0 <=. i564 &&* 2 >. i564)))) 0 1, i560, i561, i562, i563, i564]) ! [0]) (\\[i566, i567] -> [i566 + i567]), rsum (rsum (rsum (rtranspose [0,2,3,1] u559))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w420 * w507))))) (\\[i508, i509, i510, i511, i512] -> [ifF ((0 <=. i508 + i509 &&* 1 >. i508 + i509) &&* ((0 <=. i510 &&* 1 >. i510) &&* ((0 <=. i511 &&* 2 >. i511) &&* (0 <=. i512 &&* 2 >. i512)))) 0 1, i508, i509, i510, i511, i512]) ! [0]) (\\[i514, i515] -> [i514 + i515]), rsum (rsum (rsum (rtranspose [0,2,3,1] u506))), rsum (rtranspose [2,1,0] (t467 * rreplicate 1 m475)), rsum (rtranspose [1,0] m475), rsum (rtranspose [2,0,1] (rreplicate 10 (m471 * m468)) * rtranspose [2,1,0] (rreplicate 1 m473)), rsum (rtranspose [1,0] m473)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w354 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,4,4] (rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 7.0))))), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i704, i705, i706, i707, i708, i709] -> [ifF ((0 <=. i706 &&* 1 >. i706) &&* ((0 <=. i707 &&* 1 >. i707) &&* ((0 <=. i704 + i708 &&* 4 >. i704 + i708) &&* (0 <=. i705 + i709 &&* 4 >. i705 + i709)))) 0 1, i704, i705, i706, i707, i708, i709]) * rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 u1), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i698, i699, i700, i701, i702, i703] -> [ifF ((0 <=. i700 &&* 1 >. i700) &&* ((0 <=. i701 &&* 1 >. i701) &&* ((0 <=. i702 &&* 2 >. i702) &&* (0 <=. i703 &&* 2 >. i703)))) 0 1, i698, i699, i700, i701, i702, i703])) (\\[i654, i655, i656, i657, i658] -> [rem (quot (i654 + 4 * i658 + 16 * i657 + 64 * i655 + 64 * i656) 16) 4, rem (quot (i654 + 4 * i658 + 16 * i657 + 64 * i655 + 64 * i656) 4) 4, 0, 0, rem (quot (i654 + 4 * i658 + 16 * i657 + 64 * i655 + 64 * i656) 2) 2, rem (i654 + 4 * i658 + 16 * i657 + 64 * i655 + 64 * i656) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w392 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i359, i360, i361, i362, i363, i364, i365, i366] -> [ifF (w354 ! [i359, i360, i361, i362, i363, i364, i365, rconst (fromList [1] [0]) ! [i359] + rconst (fromList [1] [0]) ! [i363], rconst (fromList [1] [0]) ! [i360] + rconst (fromList [1] [0]) ! [i364], 2 * rconst (fromList [2] [0,1]) ! [i361] + rconst (fromList [2] [0,1]) ! [i365], i366] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,4] w354 (\\[i367, i368, i369, i370, i371, i372, i373] -> [i367, i368, i369, i370, i371, i372, i373, rconst (fromList [1] [0]) ! [i367] + rconst (fromList [1] [0]) ! [i371], rconst (fromList [1] [0]) ! [i368] + rconst (fromList [1] [0]) ! [i372], 2 * rconst (fromList [2] [0,1]) ! [i369] + rconst (fromList [2] [0,1]) ! [i373]])) (\\[i376, i377, i378, i379, i380, i381, i382, i383] -> [i376, i377, i378, i379, i380, i381, i382, 2 * i379 + i383]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i384, i385, i386, i387, i388, i389, i390, i391] -> [ifF ((0 <=. i384 + i388 &&* 1 >. i384 + i388) &&* ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. 2 * i386 + i390 &&* 4 >. 2 * i386 + i390) &&* (0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391)))) 0 1, i384, i385, i386, i387, i388, i389, i390, i391]))))))) ; w422 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,2,2] (rgather [2,2,1,1,2,2] (rfromList [rgather [2,2,1,1,2,2] (w392 ! [0]) (\\[i396, i397, i398, i399, i400, i401] -> [i396, i397, i398, i399, i400, rconst (fromList [1] [0]) ! [i398], i399, rconst (fromList [2] [0,1]) ! [i396] + rconst (fromList [2] [0,1]) ! [i400], i397 + i401, 0, 0, rem (quot (rmaxIndex (rgather [4] (w392 ! [0, i396, i397, i398, i399, i400, rconst (fromList [1] [0]) ! [i398], i399, rconst (fromList [2] [0,1]) ! [i396] + rconst (fromList [2] [0,1]) ! [i400], i397 + i401, 0, 0]) (\\[i403] -> [rem (quot i403 2) 2, rem i403 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w392 ! [0, i396, i397, i398, i399, i400, rconst (fromList [1] [0]) ! [i398], i399, rconst (fromList [2] [0,1]) ! [i396] + rconst (fromList [2] [0,1]) ! [i400], i397 + i401, 0, 0]) (\\[i405] -> [rem (quot i405 2) 2, rem i405 2]))) 2]), rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i681, i682, i683, i684, i685, i686] -> [ifF ((0 <=. i683 &&* 1 >. i683) &&* ((0 <=. i684 &&* 1 >. i684) &&* ((0 <=. i681 + i685 &&* 2 >. i681 + i685) &&* (0 <=. i682 + i686 &&* 2 >. i682 + i686)))) 0 1, i681, i682, i683, i684, i685, i686]) * rgather [2,2,1,1,2,2] (rfromList [rreplicate 2 (rreplicate 2 u3), rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i675, i676, i677, i678, i679, i680] -> [ifF ((0 <=. i677 &&* 1 >. i677) &&* ((0 <=. i678 &&* 1 >. i678) &&* ((0 <=. i679 &&* 2 >. i679) &&* (0 <=. i680 &&* 2 >. i680)))) 0 1, i675, i676, i677, i678, i679, i680])) (\\[i644, i645, i646, i647, i648] -> [rem (quot (i644 + 4 * i648 + 8 * i647 + 16 * i645 + 16 * i646) 8) 2, rem (quot (i644 + 4 * i648 + 8 * i647 + 16 * i645 + 16 * i646) 4) 2, 0, 0, rem (quot (i644 + 4 * i648 + 8 * i647 + 16 * i645 + 16 * i646) 2) 2, rem (i644 + 4 * i648 + 8 * i647 + 16 * i645 + 16 * i646) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w460 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i427, i428, i429, i430, i431, i432, i433, i434] -> [ifF (w422 ! [i427, i428, i429, i430, i431, i432, i433, rconst (fromList [1] [0]) ! [i427] + rconst (fromList [1] [0]) ! [i431], rconst (fromList [1] [0]) ! [i428] + rconst (fromList [1] [0]) ! [i432], 2 * rconst (fromList [1] [0]) ! [i429] + rconst (fromList [2] [0,1]) ! [i433], i434] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w422 (\\[i435, i436, i437, i438, i439, i440, i441] -> [i435, i436, i437, i438, i439, i440, i441, rconst (fromList [1] [0]) ! [i435] + rconst (fromList [1] [0]) ! [i439], rconst (fromList [1] [0]) ! [i436] + rconst (fromList [1] [0]) ! [i440], 2 * rconst (fromList [1] [0]) ! [i437] + rconst (fromList [2] [0,1]) ! [i441]])) (\\[i444, i445, i446, i447, i448, i449, i450, i451] -> [i444, i445, i446, i447, i448, i449, i450, 2 * i447 + i451]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [ifF ((0 <=. i452 + i456 &&* 1 >. i452 + i456) &&* ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. 2 * i454 + i458 &&* 2 >. 2 * i454 + i458) &&* (0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459)))) 0 1, i452, i453, i454, i455, i456, i457, i458, i459]) ; m468 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 (w460 ! [0, 0, 0, 0, 0, 0, rem (quot (rmaxIndex (rgather [4] (w460 ! [0, 0, 0, 0, 0, 0]) (\\[i465] -> [rem (quot i465 2) 2, rem i465 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w460 ! [0, 0, 0, 0, 0, 0]) (\\[i466] -> [rem (quot i466 2) 2, rem i466 2]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v6) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i469, i470] -> [ifF (m468 ! [i469, i470] <=. 0.0) 0 1]) * m468))) + rtranspose [1,0] (rreplicate 1 v8)]"
