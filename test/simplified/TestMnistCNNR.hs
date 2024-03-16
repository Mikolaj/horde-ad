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
    @?= "\\m465 u1 v2 u3 v4 m5 v6 m7 v8 -> let w349 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rgather [2] 7.0 (\\[i280] -> [])) (\\[i281, i282] -> [i282])) (\\[i283, i284, i285] -> [i284, i285])) (\\[i286, i287, i288, i289] -> [i287, i288, i289])) (\\[i290, i291, i292, i293, i294] -> [i291, i292, i293, i294])) (\\[i295, i296, i297, i298, i299, i300] -> [i296, i297, i298, i299, i300])) (\\[i301, i302, i303, i304, i305, i306, i307] -> [i302, i303, i304, i305, i306, i307]), rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 0.0) (\\[i308, i309] -> [i309])) (\\[i310, i311, i312] -> [i311, i312])) (\\[i313, i314, i315, i316] -> [i314, i315, i316])) (\\[i317, i318, i319, i320, i321] -> [i318, i319, i320, i321])) (\\[i322, i323, i324, i325, i326, i327] -> [i323, i324, i325, i326, i327])) (\\[i328, i329, i330, i331, i332, i333, i334] -> [i329, i330, i331, i332, i333, i334])]) (\\[i335, i336, i337, i338, i339, i340, i341] -> [ifF ((0 <=. i335 + i338 &&* 1 >. i335 + i338) &&* ((0 <=. i339 &&* 1 >. i339) &&* ((0 <=. i336 + i340 &&* 4 >. i336 + i340) &&* (0 <=. i337 + i341 &&* 4 >. i337 + i341)))) 0 1, i335, i336, i337, i338, i339, i340, i341]))) ; w350 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i342, i343] -> [i342 + i343]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i344, i345, i346, i347, i348] -> [ifF ((0 <=. i344 + i345 &&* 1 >. i344 + i345) &&* ((0 <=. i346 &&* 1 >. i346) &&* ((0 <=. i347 &&* 2 >. i347) &&* (0 <=. i348 &&* 2 >. i348)))) 0 1, i344, i345, i346, i347, i348]))))) ; w351 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,4,4,4] (w349 * w350))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w371 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i356, i357, i358, i359, i360, i361, i362, i363] -> [ifF (w351 ! [i356, i357, i358, i359, i360, i361, i362, let w352 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i356, i357, i358, i359, i360, i361, i362], let w353 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w353 ! [i356, i357, i358, i359, i360, i361, i362], let v354 = rconst (fromList [2] [0,1]) ; w355 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v354)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w355 ! [i356, i357, i358, i359, i360, i361, i362], i363] <=. 0.0) 0 1]) ; w372 = rgather [1,1,2,2,1,1,2,4] w351 (\\[i364, i365, i366, i367, i368, i369, i370] -> [i364, i365, i366, i367, i368, i369, i370, let w352 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i364, i365, i366, i367, i368, i369, i370], let w353 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w353 ! [i364, i365, i366, i367, i368, i369, i370], let v354 = rconst (fromList [2] [0,1]) ; w355 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v354)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w355 ! [i364, i365, i366, i367, i368, i369, i370]]) ; w389 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w371 * w372) (\\[i373, i374, i375, i376, i377, i378, i379, i380] -> [i373, i374, i375, i376, i377, i378, i379, 2 * i376 + i380]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [ifF ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. i382 + i386 &&* 1 >. i382 + i386) &&* ((0 <=. 2 * i383 + i387 &&* 4 >. 2 * i383 + i387) &&* (0 <=. 2 * i384 + i388 &&* 4 >. 2 * i384 + i388)))) 0 1, i381, i382, i383, i384, i385, i386, i387, i388]))))))) ; w415 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w389 (\\[i392, i393, i394, i395, i396, i397, i398] -> [i392, i393, i394, i395, i396, i397, let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i392, i393, i394, i395, i396, i397], i396, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i392, i393, i394, i395, i396, i397], i394 + i398, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w389 ! [i392, i393, i394, i395, i396, i397, let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i392, i393, i394, i395, i396, i397], i396, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i392, i393, i394, i395, i396, i397], let i399 = i394 + i398 in i399]))) 2) 2, rem (rmaxIndex (rreshape [4] (w389 ! [i392, i393, i394, i395, i396, i397, let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i392, i393, i394, i395, i396, i397], i396, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i392, i393, i394, i395, i396, i397], let i400 = i394 + i398 in i400]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i401, i402, i403, i404, i405, i406, i407] -> [ifF ((0 <=. i401 + i404 &&* 1 >. i401 + i404) &&* ((0 <=. i405 &&* 1 >. i405) &&* ((0 <=. i402 + i406 &&* 2 >. i402 + i406) &&* (0 <=. i403 + i407 &&* 2 >. i403 + i407)))) 0 1, i401, i402, i403, i404, i405, i406, i407]))) ; w416 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i408, i409] -> [i408 + i409]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i410, i411, i412, i413, i414] -> [ifF ((0 <=. i410 + i411 &&* 1 >. i410 + i411) &&* ((0 <=. i412 &&* 1 >. i412) &&* ((0 <=. i413 &&* 2 >. i413) &&* (0 <=. i414 &&* 2 >. i414)))) 0 1, i410, i411, i412, i413, i414]))))) ; w417 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,2,2,4] (w415 * w416))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w436 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i421, i422, i423, i424, i425, i426, i427, i428] -> [ifF (w417 ! [i421, i422, i423, i424, i425, i426, i427, let w418 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i421, i422, i423, i424, i425, i426, i427], let w419 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w419 ! [i421, i422, i423, i424, i425, i426, i427], let w420 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w420 ! [i421, i422, i423, i424, i425, i426, i427], i428] <=. 0.0) 0 1]) ; w437 = rgather [1,1,1,1,1,1,2,2] w417 (\\[i429, i430, i431, i432, i433, i434, i435] -> [i429, i430, i431, i432, i433, i434, i435, let w418 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i429, i430, i431, i432, i433, i434, i435], let w419 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w419 ! [i429, i430, i431, i432, i433, i434, i435], let w420 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w420 ! [i429, i430, i431, i432, i433, i434, i435]]) ; w454 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w436 * w437) (\\[i438, i439, i440, i441, i442, i443, i444, i445] -> [i438, i439, i440, i441, i442, i443, i444, 2 * i441 + i445]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i446, i447, i448, i449, i450, i451, i452, i453] -> [ifF ((0 <=. i446 + i450 &&* 1 >. i446 + i450) &&* ((0 <=. i447 + i451 &&* 1 >. i447 + i451) &&* ((0 <=. 2 * i448 + i452 &&* 2 >. 2 * i448 + i452) &&* (0 <=. 2 * i449 + i453 &&* 2 >. 2 * i449 + i453)))) 0 1, i446, i447, i448, i449, i450, i451, i452, i453]) ; t459 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w454 (\\[i455, i456, i457, i458] -> [i455, i456, i457, i458, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w454 ! [i455, i456, i457, i458]))) 2) 2, rem (rmaxIndex (rreshape [4] (w454 ! [i455, i456, i457, i458]))) 2]))))) ; m460 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t459) + rtranspose [1,0] (rreplicate 1 v6) ; m463 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i461, i462] -> [ifF (m460 ! [i461, i462] <=. 0.0) 0 1]) ; t464 = rtranspose [1,0] (rreplicate 10 (m463 * m460)) in let [m466 @Natural @Double @[10,1]] = [m465] in let m467 = m463 * rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m466)) ; w480 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rsum (rtranspose [1,0] (rreplicate 1 m5) * rtranspose [1,2,0] (rreplicate 1 m467)))) (\\[i468, i469, i470, i471] -> [i468, i469, i470, i471, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w454 ! [i468, i469, i470, i471]))) 2) 2, rem (rmaxIndex (rreshape [4] (w454 ! [i468, i469, i470, i471]))) 2])) (\\[i472, i473, i474, i475, i476, i477, i478, i479] -> [ifF ((0 <=. i472 + i476 &&* 1 >. i472 + i476) &&* ((0 <=. i473 + i477 &&* 1 >. i473 + i477) &&* ((0 <=. 2 * i474 + i478 &&* 2 >. 2 * i474 + i478) &&* (0 <=. 2 * i475 + i479 &&* 2 >. 2 * i475 + i479)))) 0 1, i472, i473, i474, i475, i476, i477, i478, i479]) ; u496 = rscatter [1,1,2,2] (w436 * rscatter [1,1,1,1,1,1,2,2] (w480 ! [0]) (\\[i481, i482, i483, i484, i485, i486, i487, i488] -> [i481, i482, i483, i484, i485, i486, i487, 2 * i484 + i488])) (\\[i489, i490, i491, i492, i493, i494, i495] -> [let w418 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i489, i490, i491, i492, i493, i494, i495], let w419 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w419 ! [i489, i490, i491, i492, i493, i494, i495], let w420 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w420 ! [i489, i490, i491, i492, i493, i494, i495]]) ; w497 = rreshape [1,1,2,2,1,1,2,2] (rtranspose [1,2,3,4,0] (rreplicate 4 u496)) ; w503 = rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w415 * w497))))) (\\[i498, i499, i500, i501, i502] -> [ifF ((0 <=. i498 + i499 &&* 1 >. i498 + i499) &&* ((0 <=. i500 &&* 1 >. i500) &&* ((0 <=. i501 &&* 2 >. i501) &&* (0 <=. i502 &&* 2 >. i502)))) 0 1, i498, i499, i500, i501, i502]) ; w513 = rscatter [2,1,2,2,1,1,2,2] (rsum (rtranspose [1,0] (w416 * w497))) (\\[i506, i507, i508, i509, i510, i511, i512] -> [ifF ((0 <=. i506 + i509 &&* 1 >. i506 + i509) &&* ((0 <=. i510 &&* 1 >. i510) &&* ((0 <=. i507 + i511 &&* 2 >. i507 + i511) &&* (0 <=. i508 + i512 &&* 2 >. i508 + i512)))) 0 1, i506, i507, i508, i509, i510, i511, i512]) ; w531 = rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (w513 ! [0]) (\\[i514, i515, i516, i517, i518, i519, i520] -> [let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i514, i515, i516, i517, i518, i519], i518, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i514, i515, i516, i517, i518, i519], i516 + i520, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w389 ! [i514, i515, i516, i517, i518, i519, let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i514, i515, i516, i517, i518, i519], i518, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i514, i515, i516, i517, i518, i519], let i521 = i516 + i520 in i521]))) 2) 2, rem (rmaxIndex (rreshape [4] (w389 ! [i514, i515, i516, i517, i518, i519, let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i514, i515, i516, i517, i518, i519], i518, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i514, i515, i516, i517, i518, i519], let i522 = i516 + i520 in i522]))) 2])) (\\[i523, i524, i525, i526, i527, i528, i529, i530] -> [ifF ((0 <=. i523 + i527 &&* 1 >. i523 + i527) &&* ((0 <=. i524 + i528 &&* 1 >. i524 + i528) &&* ((0 <=. 2 * i525 + i529 &&* 4 >. 2 * i525 + i529) &&* (0 <=. 2 * i526 + i530 &&* 4 >. 2 * i526 + i530)))) 0 1, i523, i524, i525, i526, i527, i528, i529, i530]) ; u547 = rscatter [1,1,4,4] (w371 * rscatter [1,1,2,2,1,1,2,4] (w531 ! [0]) (\\[i532, i533, i534, i535, i536, i537, i538, i539] -> [i532, i533, i534, i535, i536, i537, i538, 2 * i535 + i539])) (\\[i540, i541, i542, i543, i544, i545, i546] -> [let w352 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i540, i541, i542, i543, i544, i545, i546], let w353 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w353 ! [i540, i541, i542, i543, i544, i545, i546], let v354 = rconst (fromList [2] [0,1]) ; w355 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v354)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w355 ! [i540, i541, i542, i543, i544, i545, i546]]) ; w553 = rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w349 * rreshape [1,1,4,4,1,1,2,2] (rtranspose [1,2,3,4,0] (rreplicate 4 u547))))))) (\\[i548, i549, i550, i551, i552] -> [ifF ((0 <=. i548 + i549 &&* 1 >. i548 + i549) &&* ((0 <=. i550 &&* 1 >. i550) &&* ((0 <=. i551 &&* 2 >. i551) &&* (0 <=. i552 &&* 2 >. i552)))) 0 1, i548, i549, i550, i551, i552]) in [rscatter [1,1,2,2] (w553 ! [0]) (\\[i554, i555] -> [i554 + i555]), rsum (rsum (rsum (rtranspose [0,2,3,1] u547))), rscatter [1,1,2,2] (w503 ! [0]) (\\[i504, i505] -> [i504 + i505]), rsum (rsum (rsum (rtranspose [0,2,3,1] u496))), rsum (rtranspose [2,1,0] (t459 * rreplicate 1 m467)), rsum (rtranspose [1,0] m467), rsum (rtranspose [2,1,0] (t464 * rreplicate 1 m466)), rsum (rtranspose [1,0] m466)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w349 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rgather [2] 7.0 (\\[i280] -> [])) (\\[i281, i282] -> [i282])) (\\[i283, i284, i285] -> [i284, i285])) (\\[i286, i287, i288, i289] -> [i287, i288, i289])) (\\[i290, i291, i292, i293, i294] -> [i291, i292, i293, i294])) (\\[i295, i296, i297, i298, i299, i300] -> [i296, i297, i298, i299, i300])) (\\[i301, i302, i303, i304, i305, i306, i307] -> [i302, i303, i304, i305, i306, i307]), rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 0.0) (\\[i308, i309] -> [i309])) (\\[i310, i311, i312] -> [i311, i312])) (\\[i313, i314, i315, i316] -> [i314, i315, i316])) (\\[i317, i318, i319, i320, i321] -> [i318, i319, i320, i321])) (\\[i322, i323, i324, i325, i326, i327] -> [i323, i324, i325, i326, i327])) (\\[i328, i329, i330, i331, i332, i333, i334] -> [i329, i330, i331, i332, i333, i334])]) (\\[i335, i336, i337, i338, i339, i340, i341] -> [ifF ((0 <=. i335 + i338 &&* 1 >. i335 + i338) &&* ((0 <=. i339 &&* 1 >. i339) &&* ((0 <=. i336 + i340 &&* 4 >. i336 + i340) &&* (0 <=. i337 + i341 &&* 4 >. i337 + i341)))) 0 1, i335, i336, i337, i338, i339, i340, i341]))) ; w350 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u1 (\\[i342, i343] -> [i342 + i343]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i344, i345, i346, i347, i348] -> [ifF ((0 <=. i344 + i345 &&* 1 >. i344 + i345) &&* ((0 <=. i346 &&* 1 >. i346) &&* ((0 <=. i347 &&* 2 >. i347) &&* (0 <=. i348 &&* 2 >. i348)))) 0 1, i344, i345, i346, i347, i348]))))) ; w351 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,4,4,4] (w349 * w350))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w371 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i356, i357, i358, i359, i360, i361, i362, i363] -> [ifF (w351 ! [i356, i357, i358, i359, i360, i361, i362, let w352 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i356, i357, i358, i359, i360, i361, i362], let w353 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w353 ! [i356, i357, i358, i359, i360, i361, i362], let v354 = rconst (fromList [2] [0,1]) ; w355 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v354)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w355 ! [i356, i357, i358, i359, i360, i361, i362], i363] <=. 0.0) 0 1]) ; w372 = rgather [1,1,2,2,1,1,2,4] w351 (\\[i364, i365, i366, i367, i368, i369, i370] -> [i364, i365, i366, i367, i368, i369, i370, let w352 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w352 ! [i364, i365, i366, i367, i368, i369, i370], let w353 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w353 ! [i364, i365, i366, i367, i368, i369, i370], let v354 = rconst (fromList [2] [0,1]) ; w355 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 2 * v354)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w355 ! [i364, i365, i366, i367, i368, i369, i370]]) ; w389 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w371 * w372) (\\[i373, i374, i375, i376, i377, i378, i379, i380] -> [i373, i374, i375, i376, i377, i378, i379, 2 * i376 + i380]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [ifF ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. i382 + i386 &&* 1 >. i382 + i386) &&* ((0 <=. 2 * i383 + i387 &&* 4 >. 2 * i383 + i387) &&* (0 <=. 2 * i384 + i388 &&* 4 >. 2 * i384 + i388)))) 0 1, i381, i382, i383, i384, i385, i386, i387, i388]))))))) ; w415 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w389 (\\[i392, i393, i394, i395, i396, i397, i398] -> [i392, i393, i394, i395, i396, i397, let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i392, i393, i394, i395, i396, i397], i396, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i392, i393, i394, i395, i396, i397], i394 + i398, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w389 ! [i392, i393, i394, i395, i396, i397, let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i392, i393, i394, i395, i396, i397], i396, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i392, i393, i394, i395, i396, i397], let i399 = i394 + i398 in i399]))) 2) 2, rem (rmaxIndex (rreshape [4] (w389 ! [i392, i393, i394, i395, i396, i397, let w390 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w390 ! [i392, i393, i394, i395, i396, i397], i396, let w391 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w391 ! [i392, i393, i394, i395, i396, i397], let i400 = i394 + i398 in i400]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i401, i402, i403, i404, i405, i406, i407] -> [ifF ((0 <=. i401 + i404 &&* 1 >. i401 + i404) &&* ((0 <=. i405 &&* 1 >. i405) &&* ((0 <=. i402 + i406 &&* 2 >. i402 + i406) &&* (0 <=. i403 + i407 &&* 2 >. i403 + i407)))) 0 1, i401, i402, i403, i404, i405, i406, i407]))) ; w416 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i408, i409] -> [i408 + i409]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i410, i411, i412, i413, i414] -> [ifF ((0 <=. i410 + i411 &&* 1 >. i410 + i411) &&* ((0 <=. i412 &&* 1 >. i412) &&* ((0 <=. i413 &&* 2 >. i413) &&* (0 <=. i414 &&* 2 >. i414)))) 0 1, i410, i411, i412, i413, i414]))))) ; w417 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,2,2,4] (w415 * w416))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w436 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i421, i422, i423, i424, i425, i426, i427, i428] -> [ifF (w417 ! [i421, i422, i423, i424, i425, i426, i427, let w418 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i421, i422, i423, i424, i425, i426, i427], let w419 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w419 ! [i421, i422, i423, i424, i425, i426, i427], let w420 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w420 ! [i421, i422, i423, i424, i425, i426, i427], i428] <=. 0.0) 0 1]) ; w437 = rgather [1,1,1,1,1,1,2,2] w417 (\\[i429, i430, i431, i432, i433, i434, i435] -> [i429, i430, i431, i432, i433, i434, i435, let w418 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w418 ! [i429, i430, i431, i432, i433, i434, i435], let w419 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w419 ! [i429, i430, i431, i432, i433, i434, i435], let w420 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 2 * rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w420 ! [i429, i430, i431, i432, i433, i434, i435]]) ; w454 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w436 * w437) (\\[i438, i439, i440, i441, i442, i443, i444, i445] -> [i438, i439, i440, i441, i442, i443, i444, 2 * i441 + i445]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i446, i447, i448, i449, i450, i451, i452, i453] -> [ifF ((0 <=. i446 + i450 &&* 1 >. i446 + i450) &&* ((0 <=. i447 + i451 &&* 1 >. i447 + i451) &&* ((0 <=. 2 * i448 + i452 &&* 2 >. 2 * i448 + i452) &&* (0 <=. 2 * i449 + i453 &&* 2 >. 2 * i449 + i453)))) 0 1, i446, i447, i448, i449, i450, i451, i452, i453]) ; t459 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w454 (\\[i455, i456, i457, i458] -> [i455, i456, i457, i458, 0, 0, rem (quot (rmaxIndex (rreshape [4] (w454 ! [i455, i456, i457, i458]))) 2) 2, rem (rmaxIndex (rreshape [4] (w454 ! [i455, i456, i457, i458]))) 2]))))) ; m460 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t459) + rtranspose [1,0] (rreplicate 1 v6) ; m463 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i461, i462] -> [ifF (m460 ! [i461, i462] <=. 0.0) 0 1]) ; t464 = rtranspose [1,0] (rreplicate 10 (m463 * m460)) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * t464) + rtranspose [1,0] (rreplicate 1 v8)]"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m465 u1 v2 u3 v4 m5 v6 m7 v8 -> let w349 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rreplicate 1 (rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 7.0)))))), rreplicate 1 (rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i335, i336, i337, i338, i339, i340, i341] -> [ifF ((0 <=. i335 + i338 &&* 1 >. i335 + i338) &&* ((0 <=. i339 &&* 1 >. i339) &&* ((0 <=. i336 + i340 &&* 4 >. i336 + i340) &&* (0 <=. i337 + i341 &&* 4 >. i337 + i341)))) 0 1, i335, i336, i337, i338, i339, i340, i341]))) ; w351 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,4,4] (w349 ! [0, 0] * rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 u1), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i632, i633, i634, i635, i636, i637] -> [ifF ((0 <=. i634 &&* 1 >. i634) &&* ((0 <=. i635 &&* 1 >. i635) &&* ((0 <=. i636 &&* 2 >. i636) &&* (0 <=. i637 &&* 2 >. i637)))) 0 1, i632, i633, i634, i635, i636, i637])) (\\[i611, i612, i613, i614, i615] -> [rem (quot (i611 + 4 * i615 + 16 * i614 + 64 * i612 + 64 * i613) 16) 4, rem (quot (i611 + 4 * i615 + 16 * i614 + 64 * i612 + 64 * i613) 4) 4, 0, 0, rem (quot (i611 + 4 * i615 + 16 * i614 + 64 * i612 + 64 * i613) 2) 2, rem (i611 + 4 * i615 + 16 * i614 + 64 * i612 + 64 * i613) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w371 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i356, i357, i358, i359, i360, i361, i362, i363] -> [ifF (w351 ! [i356, i357, i358, i359, i360, i361, i362, rconst (fromList [1] [0]) ! [i356] + rconst (fromList [1] [0]) ! [i360], rconst (fromList [1] [0]) ! [i357] + rconst (fromList [1] [0]) ! [i361], 2 * rconst (fromList [2] [0,1]) ! [i358] + rconst (fromList [2] [0,1]) ! [i362], i363] <=. 0.0) 0 1]) ; w389 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w371 * rgather [1,1,2,2,1,1,2,4] w351 (\\[i364, i365, i366, i367, i368, i369, i370] -> [i364, i365, i366, i367, i368, i369, i370, rconst (fromList [1] [0]) ! [i364] + rconst (fromList [1] [0]) ! [i368], rconst (fromList [1] [0]) ! [i365] + rconst (fromList [1] [0]) ! [i369], 2 * rconst (fromList [2] [0,1]) ! [i366] + rconst (fromList [2] [0,1]) ! [i370]])) (\\[i373, i374, i375, i376, i377, i378, i379, i380] -> [i373, i374, i375, i376, i377, i378, i379, 2 * i376 + i380]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [ifF ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. i382 + i386 &&* 1 >. i382 + i386) &&* ((0 <=. 2 * i383 + i387 &&* 4 >. 2 * i383 + i387) &&* (0 <=. 2 * i384 + i388 &&* 4 >. 2 * i384 + i388)))) 0 1, i381, i382, i383, i384, i385, i386, i387, i388]))))))) ; w415 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w389 (\\[i392, i393, i394, i395, i396, i397, i398] -> [i392, i393, i394, i395, i396, i397, rconst (fromList [1] [0]) ! [i392] + rconst (fromList [1] [0]) ! [i395], i396, rconst (fromList [2] [0,1]) ! [i393] + rconst (fromList [2] [0,1]) ! [i397], i394 + i398, 0, 0, rem (quot (rmaxIndex (rgather [4] (w389 ! [i392, i393, i394, i395, i396, i397, rconst (fromList [1] [0]) ! [i392] + rconst (fromList [1] [0]) ! [i395], i396, rconst (fromList [2] [0,1]) ! [i393] + rconst (fromList [2] [0,1]) ! [i397], i394 + i398, 0, 0]) (\\[i609] -> [rem (quot i609 2) 2, rem i609 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w389 ! [i392, i393, i394, i395, i396, i397, rconst (fromList [1] [0]) ! [i392] + rconst (fromList [1] [0]) ! [i395], i396, rconst (fromList [2] [0,1]) ! [i393] + rconst (fromList [2] [0,1]) ! [i397], i394 + i398, 0, 0]) (\\[i610] -> [rem (quot i610 2) 2, rem i610 2]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))))]) (\\[i401, i402, i403, i404, i405, i406, i407] -> [ifF ((0 <=. i401 + i404 &&* 1 >. i401 + i404) &&* ((0 <=. i405 &&* 1 >. i405) &&* ((0 <=. i402 + i406 &&* 2 >. i402 + i406) &&* (0 <=. i403 + i407 &&* 2 >. i403 + i407)))) 0 1, i401, i402, i403, i404, i405, i406, i407]))) ; w416 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u3 (\\[i408, i409] -> [i408 + i409]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0))))]) (\\[i410, i411, i412, i413, i414] -> [ifF ((0 <=. i410 + i411 &&* 1 >. i410 + i411) &&* ((0 <=. i412 &&* 1 >. i412) &&* ((0 <=. i413 &&* 2 >. i413) &&* (0 <=. i414 &&* 2 >. i414)))) 0 1, i410, i411, i412, i413, i414]))))) ; w417 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,2,2] (w415 ! [0, 0] * w416 ! [0, 0]) (\\[i599, i600, i601, i602, i603] -> [rem (quot (i599 + 4 * i603 + 8 * i602 + 16 * i600 + 16 * i601) 8) 2, rem (quot (i599 + 4 * i603 + 8 * i602 + 16 * i600 + 16 * i601) 4) 2, 0, 0, rem (quot (i599 + 4 * i603 + 8 * i602 + 16 * i600 + 16 * i601) 2) 2, rem (i599 + 4 * i603 + 8 * i602 + 16 * i600 + 16 * i601) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w436 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i421, i422, i423, i424, i425, i426, i427, i428] -> [ifF (w417 ! [i421, i422, i423, i424, i425, i426, i427, rconst (fromList [1] [0]) ! [i421] + rconst (fromList [1] [0]) ! [i425], rconst (fromList [1] [0]) ! [i422] + rconst (fromList [1] [0]) ! [i426], 2 * rconst (fromList [1] [0]) ! [i423] + rconst (fromList [2] [0,1]) ! [i427], i428] <=. 0.0) 0 1]) ; w454 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w436 * rgather [1,1,1,1,1,1,2,2] w417 (\\[i429, i430, i431, i432, i433, i434, i435] -> [i429, i430, i431, i432, i433, i434, i435, rconst (fromList [1] [0]) ! [i429] + rconst (fromList [1] [0]) ! [i433], rconst (fromList [1] [0]) ! [i430] + rconst (fromList [1] [0]) ! [i434], 2 * rconst (fromList [1] [0]) ! [i431] + rconst (fromList [2] [0,1]) ! [i435]])) (\\[i438, i439, i440, i441, i442, i443, i444, i445] -> [i438, i439, i440, i441, i442, i443, i444, 2 * i441 + i445]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i446, i447, i448, i449, i450, i451, i452, i453] -> [ifF ((0 <=. i446 + i450 &&* 1 >. i446 + i450) &&* ((0 <=. i447 + i451 &&* 1 >. i447 + i451) &&* ((0 <=. 2 * i448 + i452 &&* 2 >. 2 * i448 + i452) &&* (0 <=. 2 * i449 + i453 &&* 2 >. 2 * i449 + i453)))) 0 1, i446, i447, i448, i449, i450, i451, i452, i453]) ; t459 = rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 (w454 ! [0, 0, 0, 0, 0, 0, rem (quot (rmaxIndex (rgather [4] (w454 ! [0, 0, 0, 0, 0, 0]) (\\[i595] -> [rem (quot i595 2) 2, rem i595 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w454 ! [0, 0, 0, 0, 0, 0]) (\\[i596] -> [rem (quot i596 2) 2, rem i596 2]))) 2])))) ; m460 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * t459) + rtranspose [1,0] (rreplicate 1 v6) ; m463 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i461, i462] -> [ifF (m460 ! [i461, i462] <=. 0.0) 0 1]) ; m467 = m463 * rsum (rtranspose [1,2,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 1 m465)) ; u496 = rscatter [1,1,2,2] (w436 * rscatter [1,1,1,1,1,1,2,2] (rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] (m5 * rgather [1,1] m467 (\\[i591, i592] -> [i591, 0])) (\\[i594] -> [i594, 0]))))))) (\\[i468, i469, i470, i471] -> [i468, i469, i470, i471, 0, 0, rem (quot (rmaxIndex (rgather [4] (w454 ! [i468, i469, i470, i471, 0, 0]) (\\[i584] -> [rem (quot i584 2) 2, rem i584 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w454 ! [i468, i469, i470, i471, 0, 0]) (\\[i585] -> [rem (quot i585 2) 2, rem i585 2]))) 2])) (\\[i472, i473, i474, i475, i476, i477, i478, i479] -> [ifF ((0 <=. i472 + i476 &&* 1 >. i472 + i476) &&* ((0 <=. i473 + i477 &&* 1 >. i473 + i477) &&* ((0 <=. 2 * i474 + i478 &&* 2 >. 2 * i474 + i478) &&* (0 <=. 2 * i475 + i479 &&* 2 >. 2 * i475 + i479)))) 0 1, i472, i473, i474, i475, i476, i477, i478, i479]) ! [0]) (\\[i481, i482, i483, i484, i485, i486, i487, i488] -> [i481, i482, i483, i484, i485, i486, i487, 2 * i484 + i488])) (\\[i489, i490, i491, i492, i493, i494, i495] -> [rconst (fromList [1] [0]) ! [i489] + rconst (fromList [1] [0]) ! [i493], rconst (fromList [1] [0]) ! [i490] + rconst (fromList [1] [0]) ! [i494], 2 * rconst (fromList [1] [0]) ! [i491] + rconst (fromList [2] [0,1]) ! [i495]]) ; w497 = rgather [1,1,2,2,1,1,2,2] (u496 ! [0, 0]) (\\[i571, i572, i573, i574, i575, i576, i577, i578] -> [rem (quot (i578 + 2 * i577 + 4 * i576 + 4 * i575 + 4 * i574 + 8 * i573 + 16 * i571 + 16 * i572) 8) 2, rem (quot (i578 + 2 * i577 + 4 * i576 + 4 * i575 + 4 * i574 + 8 * i573 + 16 * i571 + 16 * i572) 4) 2]) ; u547 = rscatter [1,1,4,4] (w371 * rscatter [1,1,2,2,1,1,2,4] (rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rtranspose [1,0] (w416 * w497))) (\\[i506, i507, i508, i509, i510, i511, i512] -> [ifF ((0 <=. i506 + i509 &&* 1 >. i506 + i509) &&* ((0 <=. i510 &&* 1 >. i510) &&* ((0 <=. i507 + i511 &&* 2 >. i507 + i511) &&* (0 <=. i508 + i512 &&* 2 >. i508 + i512)))) 0 1, i506, i507, i508, i509, i510, i511, i512]) ! [0]) (\\[i514, i515, i516, i517, i518, i519, i520] -> [rconst (fromList [1] [0]) ! [i514] + rconst (fromList [1] [0]) ! [i517], i518, rconst (fromList [2] [0,1]) ! [i515] + rconst (fromList [2] [0,1]) ! [i519], i516 + i520, 0, 0, rem (quot (rmaxIndex (rgather [4] (w389 ! [i514, i515, i516, i517, i518, i519, rconst (fromList [1] [0]) ! [i514] + rconst (fromList [1] [0]) ! [i517], i518, rconst (fromList [2] [0,1]) ! [i515] + rconst (fromList [2] [0,1]) ! [i519], i516 + i520, 0, 0]) (\\[i569] -> [rem (quot i569 2) 2, rem i569 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w389 ! [i514, i515, i516, i517, i518, i519, rconst (fromList [1] [0]) ! [i514] + rconst (fromList [1] [0]) ! [i517], i518, rconst (fromList [2] [0,1]) ! [i515] + rconst (fromList [2] [0,1]) ! [i519], i516 + i520, 0, 0]) (\\[i570] -> [rem (quot i570 2) 2, rem i570 2]))) 2])) (\\[i523, i524, i525, i526, i527, i528, i529, i530] -> [ifF ((0 <=. i523 + i527 &&* 1 >. i523 + i527) &&* ((0 <=. i524 + i528 &&* 1 >. i524 + i528) &&* ((0 <=. 2 * i525 + i529 &&* 4 >. 2 * i525 + i529) &&* (0 <=. 2 * i526 + i530 &&* 4 >. 2 * i526 + i530)))) 0 1, i523, i524, i525, i526, i527, i528, i529, i530]) ! [0]) (\\[i532, i533, i534, i535, i536, i537, i538, i539] -> [i532, i533, i534, i535, i536, i537, i538, 2 * i535 + i539])) (\\[i540, i541, i542, i543, i544, i545, i546] -> [rconst (fromList [1] [0]) ! [i540] + rconst (fromList [1] [0]) ! [i544], rconst (fromList [1] [0]) ! [i541] + rconst (fromList [1] [0]) ! [i545], 2 * rconst (fromList [2] [0,1]) ! [i542] + rconst (fromList [2] [0,1]) ! [i546]]) in [rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w349 * rgather [1,1,4,4,1,1,2,2] (u547 ! [0, 0]) (\\[i556, i557, i558, i559, i560, i561, i562, i563] -> [rem (quot (i563 + 2 * i562 + 4 * i561 + 4 * i560 + 4 * i559 + 16 * i558 + 64 * i556 + 64 * i557) 16) 4, rem (quot (i563 + 2 * i562 + 4 * i561 + 4 * i560 + 4 * i559 + 16 * i558 + 64 * i556 + 64 * i557) 4) 4])))))) (\\[i548, i549, i550, i551, i552] -> [ifF ((0 <=. i548 + i549 &&* 1 >. i548 + i549) &&* ((0 <=. i550 &&* 1 >. i550) &&* ((0 <=. i551 &&* 2 >. i551) &&* (0 <=. i552 &&* 2 >. i552)))) 0 1, i548, i549, i550, i551, i552]) ! [0]) (\\[i554, i555] -> [i554 + i555]), rsum (rsum (rsum (rtranspose [0,2,3,1] u547))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w415 * w497))))) (\\[i498, i499, i500, i501, i502] -> [ifF ((0 <=. i498 + i499 &&* 1 >. i498 + i499) &&* ((0 <=. i500 &&* 1 >. i500) &&* ((0 <=. i501 &&* 2 >. i501) &&* (0 <=. i502 &&* 2 >. i502)))) 0 1, i498, i499, i500, i501, i502]) ! [0]) (\\[i504, i505] -> [i504 + i505]), rsum (rsum (rsum (rtranspose [0,2,3,1] u496))), rsum (rtranspose [2,1,0] (t459 * rreplicate 1 m467)), rsum (rtranspose [1,0] m467), rsum (rtranspose [2,0,1] (rreplicate 10 (m463 * m460)) * rtranspose [2,1,0] (rreplicate 1 m465)), rsum (rtranspose [1,0] m465)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\u1 v2 u3 v4 m5 v6 m7 v8 -> let w351 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,4,4] (rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 7.0))))), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i732, i733, i734, i735, i736, i737] -> [ifF ((0 <=. i734 &&* 1 >. i734) &&* ((0 <=. i735 &&* 1 >. i735) &&* ((0 <=. i732 + i736 &&* 4 >. i732 + i736) &&* (0 <=. i733 + i737 &&* 4 >. i733 + i737)))) 0 1, i732, i733, i734, i735, i736, i737]) * rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 u1), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i738, i739, i740, i741, i742, i743] -> [ifF ((0 <=. i740 &&* 1 >. i740) &&* ((0 <=. i741 &&* 1 >. i741) &&* ((0 <=. i742 &&* 2 >. i742) &&* (0 <=. i743 &&* 2 >. i743)))) 0 1, i738, i739, i740, i741, i742, i743])) (\\[i694, i695, i696, i697, i698] -> [rem (quot (i694 + 4 * i698 + 16 * i697 + 64 * i695 + 64 * i696) 16) 4, rem (quot (i694 + 4 * i698 + 16 * i697 + 64 * i695 + 64 * i696) 4) 4, 0, 0, rem (quot (i694 + 4 * i698 + 16 * i697 + 64 * i695 + 64 * i696) 2) 2, rem (i694 + 4 * i698 + 16 * i697 + 64 * i695 + 64 * i696) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v2)))))))))) ; w389 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i356, i357, i358, i359, i360, i361, i362, i363] -> [ifF (w351 ! [i356, i357, i358, i359, i360, i361, i362, rconst (fromList [1] [0]) ! [i356] + rconst (fromList [1] [0]) ! [i360], rconst (fromList [1] [0]) ! [i357] + rconst (fromList [1] [0]) ! [i361], 2 * rconst (fromList [2] [0,1]) ! [i358] + rconst (fromList [2] [0,1]) ! [i362], i363] <=. 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,4] w351 (\\[i364, i365, i366, i367, i368, i369, i370] -> [i364, i365, i366, i367, i368, i369, i370, rconst (fromList [1] [0]) ! [i364] + rconst (fromList [1] [0]) ! [i368], rconst (fromList [1] [0]) ! [i365] + rconst (fromList [1] [0]) ! [i369], 2 * rconst (fromList [2] [0,1]) ! [i366] + rconst (fromList [2] [0,1]) ! [i370]])) (\\[i373, i374, i375, i376, i377, i378, i379, i380] -> [i373, i374, i375, i376, i377, i378, i379, 2 * i376 + i380]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [ifF ((0 <=. i381 + i385 &&* 1 >. i381 + i385) &&* ((0 <=. i382 + i386 &&* 1 >. i382 + i386) &&* ((0 <=. 2 * i383 + i387 &&* 4 >. 2 * i383 + i387) &&* (0 <=. 2 * i384 + i388 &&* 4 >. 2 * i384 + i388)))) 0 1, i381, i382, i383, i384, i385, i386, i387, i388]))))))) ; w417 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,2,2] (rgather [2,2,1,1,2,2] (rfromList [rgather [2,2,1,1,2,2] (w389 ! [0]) (\\[i393, i394, i395, i396, i397, i398] -> [i393, i394, i395, i396, i397, rconst (fromList [1] [0]) ! [i395], i396, rconst (fromList [2] [0,1]) ! [i393] + rconst (fromList [2] [0,1]) ! [i397], i394 + i398, 0, 0, rem (quot (rmaxIndex (rgather [4] (w389 ! [0, i393, i394, i395, i396, i397, rconst (fromList [1] [0]) ! [i395], i396, rconst (fromList [2] [0,1]) ! [i393] + rconst (fromList [2] [0,1]) ! [i397], i394 + i398, 0, 0]) (\\[i642] -> [rem (quot i642 2) 2, rem i642 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w389 ! [0, i393, i394, i395, i396, i397, rconst (fromList [1] [0]) ! [i395], i396, rconst (fromList [2] [0,1]) ! [i393] + rconst (fromList [2] [0,1]) ! [i397], i394 + i398, 0, 0]) (\\[i643] -> [rem (quot i643 2) 2, rem i643 2]))) 2]), rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i682, i683, i684, i685, i686, i687] -> [ifF ((0 <=. i684 &&* 1 >. i684) &&* ((0 <=. i685 &&* 1 >. i685) &&* ((0 <=. i682 + i686 &&* 2 >. i682 + i686) &&* (0 <=. i683 + i687 &&* 2 >. i683 + i687)))) 0 1, i682, i683, i684, i685, i686, i687]) * rgather [2,2,1,1,2,2] (rfromList [rreplicate 2 (rreplicate 2 u3), rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))]) (\\[i688, i689, i690, i691, i692, i693] -> [ifF ((0 <=. i690 &&* 1 >. i690) &&* ((0 <=. i691 &&* 1 >. i691) &&* ((0 <=. i692 &&* 2 >. i692) &&* (0 <=. i693 &&* 2 >. i693)))) 0 1, i688, i689, i690, i691, i692, i693])) (\\[i644, i645, i646, i647, i648] -> [rem (quot (i644 + 4 * i648 + 8 * i647 + 16 * i645 + 16 * i646) 8) 2, rem (quot (i644 + 4 * i648 + 8 * i647 + 16 * i645 + 16 * i646) 4) 2, 0, 0, rem (quot (i644 + 4 * i648 + 8 * i647 + 16 * i645 + 16 * i646) 2) 2, rem (i644 + 4 * i648 + 8 * i647 + 16 * i645 + 16 * i646) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v4)))))))))) ; w454 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i421, i422, i423, i424, i425, i426, i427, i428] -> [ifF (w417 ! [i421, i422, i423, i424, i425, i426, i427, rconst (fromList [1] [0]) ! [i421] + rconst (fromList [1] [0]) ! [i425], rconst (fromList [1] [0]) ! [i422] + rconst (fromList [1] [0]) ! [i426], 2 * rconst (fromList [1] [0]) ! [i423] + rconst (fromList [2] [0,1]) ! [i427], i428] <=. 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w417 (\\[i429, i430, i431, i432, i433, i434, i435] -> [i429, i430, i431, i432, i433, i434, i435, rconst (fromList [1] [0]) ! [i429] + rconst (fromList [1] [0]) ! [i433], rconst (fromList [1] [0]) ! [i430] + rconst (fromList [1] [0]) ! [i434], 2 * rconst (fromList [1] [0]) ! [i431] + rconst (fromList [2] [0,1]) ! [i435]])) (\\[i438, i439, i440, i441, i442, i443, i444, i445] -> [i438, i439, i440, i441, i442, i443, i444, 2 * i441 + i445]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 0.0)))))))]) (\\[i446, i447, i448, i449, i450, i451, i452, i453] -> [ifF ((0 <=. i446 + i450 &&* 1 >. i446 + i450) &&* ((0 <=. i447 + i451 &&* 1 >. i447 + i451) &&* ((0 <=. 2 * i448 + i452 &&* 2 >. 2 * i448 + i452) &&* (0 <=. 2 * i449 + i453 &&* 2 >. 2 * i449 + i453)))) 0 1, i446, i447, i448, i449, i450, i451, i452, i453]) ; m460 = rsum (rtranspose [2,1,0] (rreplicate 1 m5) * rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 (w454 ! [0, 0, 0, 0, 0, 0, rem (quot (rmaxIndex (rgather [4] (w454 ! [0, 0, 0, 0, 0, 0]) (\\[i638] -> [rem (quot i638 2) 2, rem i638 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w454 ! [0, 0, 0, 0, 0, 0]) (\\[i639] -> [rem (quot i639 2) 2, rem i639 2]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v6) in [rsum (rtranspose [2,1,0] (rreplicate 1 m7) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i461, i462] -> [ifF (m460 ! [i461, i462] <=. 0.0) 0 1]) * m460))) + rtranspose [1,0] (rreplicate 1 v8)]"
