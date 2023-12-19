{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | Tests of "MnistCnnRanked2" neural networks using a few different
-- optimization pipelines.
module TestMnistCNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (Nat, SomeNat (..), someNatVal)
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (funToAstIOR, funToAstRevIO, resetVarCounter)
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
            shapedToRanked $ fst
            $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                             (Flip OS.Array) SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)
                0.4 (mkStdGen 44)
          _ -> error "impossible someNatVal error"
      domainsInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show kh, show kw, show c_out, show n_hidden
                        , show miniBatchSize
                        , show (V.length domainsInit)
                        , show (sizeDomainsOD domainsInit) ]
      ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
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
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (DomainsOD, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f (glyphR, labelR) adinputs =
                   MnistCnnRanked2.convMnistLossFusedR
                     miniBatchSize (rconst glyphR, rconst labelR)
                     (parseDomains valsInit adinputs)
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
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
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
       res <- runEpoch 1 (domainsInit, initialStateAdam domainsInit)
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
            shapedToRanked $ fst
            $ randomVals @(MnistCnnRanked2.ADCnnMnistParametersShaped
                             (Flip OS.Array) SizeMnistHeight SizeMnistWidth
                             kh kw c_out n_hidden r)
                0.4 (mkStdGen 44)
          _ -> error "impossible someNatVal error"
      domainsInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show kh, show kw, show c_out, show n_hidden
                        , show miniBatchSize
                        , show (V.length domainsInit)
                        , show (sizeDomainsOD domainsInit) ]
      ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
      ftest = MnistCnnRanked2.convMnistTestR valsInit
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, domainsPrimal, vars, _) <- funToAstRevIO domainsInit
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
                   (parseDomains valsInit domainsPrimal)
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (DomainsOD, StateAdam)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvDR EM.empty
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
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
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
       res <- runEpoch 1 (domainsInit, initialStateAdam domainsInit)
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
        domainsInit = toDomains valsInitShaped  -- == toDomains valsInit
        valsInit :: MnistCnnRanked2.ADCnnMnistParameters ranked r
        valsInit = shapedToRanked valsInitShaped
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show kh, show kw, show c_out, show n_hidden
                          , show miniBatchSize
                          , show (V.length domainsInit)
                          , show (sizeDomainsOD domainsInit) ]
        ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
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
           g domains = f $ parseDomains valsInit domains
           (((varDtAgain, vars1Again), gradientRaw, primal, sh), _) =
             revProduceArtifact @Nat @(AstRanked FullSpan)
                                True False g envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistDataBatchR r] -> (DomainsOD, StateAdam)
              -> (DomainsOD, StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let glyphD = DynamicExists $ dfromR @(Flip OR.Array) $ rconst glyph
                 labelD = DynamicExists $ dfromR @(Flip OR.Array) $ rconst label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientDomain =
                   fst $ revEvalArtifact @Nat @(AstRanked FullSpan)
                                         (vars, gradient, primal, sh)
                                         parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientDomain)
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (DomainsOD, StateAdam)
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
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
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
       res <- runEpoch 1 (domainsInit, initialStateAdam domainsInit)
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
        shapedToRanked $ fst
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
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w353 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 (rconst 7.0)) (\\[i285, i286] -> [i286])) (\\[i287, i288, i289] -> [i288, i289])) (\\[i290, i291, i292, i293] -> [i291, i292, i293])) (\\[i294, i295, i296, i297, i298] -> [i295, i296, i297, i298])) (\\[i299, i300, i301, i302, i303, i304] -> [i300, i301, i302, i303, i304])) (\\[i305, i306, i307, i308, i309, i310, i311] -> [i306, i307, i308, i309, i310, i311]), rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 (rconst 0.0)) (\\[i312, i313] -> [i313])) (\\[i314, i315, i316] -> [i315, i316])) (\\[i317, i318, i319, i320] -> [i318, i319, i320])) (\\[i321, i322, i323, i324, i325] -> [i322, i323, i324, i325])) (\\[i326, i327, i328, i329, i330, i331] -> [i327, i328, i329, i330, i331])) (\\[i332, i333, i334, i335, i336, i337, i338] -> [i333, i334, i335, i336, i337, i338])]) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 4 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 4 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345]))) ; w354 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u2 (\\[i346, i347] -> [i346 + i347]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))]) (\\[i348, i349, i350, i351, i352] -> [ifF ((0 <=. i348 + i349 &&* 1 >. i348 + i349) &&* ((0 <=. i350 &&* 1 >. i350) &&* ((0 <=. i351 &&* 2 >. i351) &&* (0 <=. i352 &&* 2 >. i352)))) 0 1, i348, i349, i350, i351, i352]))))) ; w355 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,4,4,4] (w353 * w354))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v3)))))))))) ; w375 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i360, i361, i362, i363, i364, i365, i366, i367] -> [ifF (w355 ! [i360, i361, i362, i363, i364, i365, i366, let w356 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i360, i361, i362, i363, i364, i365, i366], let w357 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w357 ! [i360, i361, i362, i363, i364, i365, i366], let v358 = rconst (fromList [2] [0,1]) ; w359 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rconst 2) * v358)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w359 ! [i360, i361, i362, i363, i364, i365, i366], i367] <=. rconst 0.0) 0 1]) ; w376 = rgather [1,1,2,2,1,1,2,4] w355 (\\[i368, i369, i370, i371, i372, i373, i374] -> [i368, i369, i370, i371, i372, i373, i374, let w356 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i368, i369, i370, i371, i372, i373, i374], let w357 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w357 ! [i368, i369, i370, i371, i372, i373, i374], let v358 = rconst (fromList [2] [0,1]) ; w359 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rconst 2) * v358)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w359 ! [i368, i369, i370, i371, i372, i373, i374]]) ; w393 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w375 * w376) (\\[i377, i378, i379, i380, i381, i382, i383, i384] -> [i377, i378, i379, i380, i381, i382, i383, 2 * i380 + i384]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))))]) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [ifF ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. i386 + i390 &&* 1 >. i386 + i390) &&* ((0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391) &&* (0 <=. 2 * i388 + i392 &&* 4 >. 2 * i388 + i392)))) 0 1, i385, i386, i387, i388, i389, i390, i391, i392]))))))) ; w421 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w393 (\\[i396, i397, i398, i399, i400, i401, i402] -> [i396, i397, i398, i399, i400, i401, let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], i398 + i402, 0, 0, rem (quot (rmaxIndex (rgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], let i403 = i398 + i402 in i403, 0, 0]) (\\[i404] -> [rem (quot i404 2) 2, rem i404 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], let i405 = i398 + i402 in i405, 0, 0]) (\\[i406] -> [rem (quot i406 2) 2, rem i406 2]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))))]) (\\[i407, i408, i409, i410, i411, i412, i413] -> [ifF ((0 <=. i407 + i410 &&* 1 >. i407 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i408 + i412 &&* 2 >. i408 + i412) &&* (0 <=. i409 + i413 &&* 2 >. i409 + i413)))) 0 1, i407, i408, i409, i410, i411, i412, i413]))) ; w422 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u4 (\\[i414, i415] -> [i414 + i415]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))]) (\\[i416, i417, i418, i419, i420] -> [ifF ((0 <=. i416 + i417 &&* 1 >. i416 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i419 &&* 2 >. i419) &&* (0 <=. i420 &&* 2 >. i420)))) 0 1, i416, i417, i418, i419, i420]))))) ; w423 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,2,2,4] (w421 * w422))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v5)))))))))) ; w443 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i428, i429, i430, i431, i432, i433, i434, i435] -> [ifF (w423 ! [i428, i429, i430, i431, i432, i433, i434, let w424 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i428, i429, i430, i431, i432, i433, i434], let w425 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w425 ! [i428, i429, i430, i431, i432, i433, i434], let v426 = rconst (fromList [1] [0]) ; w427 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 (rconst 2) * v426)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w427 ! [i428, i429, i430, i431, i432, i433, i434], i435] <=. rconst 0.0) 0 1]) ; w444 = rgather [1,1,1,1,1,1,2,2] w423 (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, let w424 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i436, i437, i438, i439, i440, i441, i442], let w425 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w425 ! [i436, i437, i438, i439, i440, i441, i442], let v426 = rconst (fromList [1] [0]) ; w427 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 (rconst 2) * v426)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w427 ! [i436, i437, i438, i439, i440, i441, i442]]) ; w461 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w443 * w444) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, 2 * i448 + i452]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))))]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [ifF ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459) &&* (0 <=. 2 * i456 + i460 &&* 2 >. 2 * i456 + i460)))) 0 1, i453, i454, i455, i456, i457, i458, i459, i460]) ; t468 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w461 (\\[i462, i463, i464, i465] -> [i462, i463, i464, i465, 0, 0, rem (quot (rmaxIndex (rgather [4] (w461 ! [i462, i463, i464, i465, 0, 0]) (\\[i466] -> [rem (quot i466 2) 2, rem i466 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w461 ! [i462, i463, i464, i465, 0, 0]) (\\[i467] -> [rem (quot i467 2) 2, rem i467 2]))) 2]))))) ; m469 = rsum (rtranspose [2,1,0] (rreplicate 1 m6) * t468) + rtranspose [1,0] (rreplicate 1 v7) ; m472 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i470, i471] -> [ifF (m469 ! [i470, i471] <=. rconst 0.0) 0 1]) ; t473 = rtranspose [1,0] (rreplicate 10 (m472 * m469)) ; m474 = m472 * rsum (rtranspose [1,2,0] (rreplicate 1 m8) * rtranspose [1,0] (rreplicate 1 dret)) ; w489 = rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreshape [1,1,1,1] (rsum (rtranspose [1,0] (rreplicate 1 m6) * rtranspose [1,2,0] (rreplicate 1 m474)))) (\\[i475, i476, i477, i478] -> [i475, i476, i477, i478, 0, 0, rem (quot (rmaxIndex (rgather [4] (w461 ! [i475, i476, i477, i478, 0, 0]) (\\[i479] -> [rem (quot i479 2) 2, rem i479 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w461 ! [i475, i476, i477, i478, 0, 0]) (\\[i480] -> [rem (quot i480 2) 2, rem i480 2]))) 2])) (\\[i481, i482, i483, i484, i485, i486, i487, i488] -> [ifF ((0 <=. i481 + i485 &&* 1 >. i481 + i485) &&* ((0 <=. i482 + i486 &&* 1 >. i482 + i486) &&* ((0 <=. 2 * i483 + i487 &&* 2 >. 2 * i483 + i487) &&* (0 <=. 2 * i484 + i488 &&* 2 >. 2 * i484 + i488)))) 0 1, i481, i482, i483, i484, i485, i486, i487, i488]) ; u505 = rscatter [1,1,2,2] (w443 * rscatter [1,1,1,1,1,1,2,2] (w489 ! [0]) (\\[i490, i491, i492, i493, i494, i495, i496, i497] -> [i490, i491, i492, i493, i494, i495, i496, 2 * i493 + i497])) (\\[i498, i499, i500, i501, i502, i503, i504] -> [let w424 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i498, i499, i500, i501, i502, i503, i504], let w425 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w425 ! [i498, i499, i500, i501, i502, i503, i504], let v426 = rconst (fromList [1] [0]) ; w427 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 (rconst 2) * v426)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w427 ! [i498, i499, i500, i501, i502, i503, i504]]) ; w506 = rreshape [1,1,2,2,1,1,2,2] (rtranspose [1,2,3,4,0] (rreplicate 4 u505)) ; w512 = rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w421 * w506))))) (\\[i507, i508, i509, i510, i511] -> [ifF ((0 <=. i507 + i508 &&* 1 >. i507 + i508) &&* ((0 <=. i509 &&* 1 >. i509) &&* ((0 <=. i510 &&* 2 >. i510) &&* (0 <=. i511 &&* 2 >. i511)))) 0 1, i507, i508, i509, i510, i511]) ; w522 = rscatter [2,1,2,2,1,1,2,2] (rsum (rtranspose [1,0] (w422 * w506))) (\\[i515, i516, i517, i518, i519, i520, i521] -> [ifF ((0 <=. i515 + i518 &&* 1 >. i515 + i518) &&* ((0 <=. i519 &&* 1 >. i519) &&* ((0 <=. i516 + i520 &&* 2 >. i516 + i520) &&* (0 <=. i517 + i521 &&* 2 >. i517 + i521)))) 0 1, i515, i516, i517, i518, i519, i520, i521]) ; w542 = rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (w522 ! [0]) (\\[i523, i524, i525, i526, i527, i528, i529] -> [let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i523, i524, i525, i526, i527, i528], i527, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i523, i524, i525, i526, i527, i528], i525 + i529, 0, 0, rem (quot (rmaxIndex (rgather [4] (w393 ! [i523, i524, i525, i526, i527, i528, let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i523, i524, i525, i526, i527, i528], i527, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i523, i524, i525, i526, i527, i528], let i530 = i525 + i529 in i530, 0, 0]) (\\[i531] -> [rem (quot i531 2) 2, rem i531 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w393 ! [i523, i524, i525, i526, i527, i528, let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i523, i524, i525, i526, i527, i528], i527, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i523, i524, i525, i526, i527, i528], let i532 = i525 + i529 in i532, 0, 0]) (\\[i533] -> [rem (quot i533 2) 2, rem i533 2]))) 2])) (\\[i534, i535, i536, i537, i538, i539, i540, i541] -> [ifF ((0 <=. i534 + i538 &&* 1 >. i534 + i538) &&* ((0 <=. i535 + i539 &&* 1 >. i535 + i539) &&* ((0 <=. 2 * i536 + i540 &&* 4 >. 2 * i536 + i540) &&* (0 <=. 2 * i537 + i541 &&* 4 >. 2 * i537 + i541)))) 0 1, i534, i535, i536, i537, i538, i539, i540, i541]) ; u558 = rscatter [1,1,4,4] (w375 * rscatter [1,1,2,2,1,1,2,4] (w542 ! [0]) (\\[i543, i544, i545, i546, i547, i548, i549, i550] -> [i543, i544, i545, i546, i547, i548, i549, 2 * i546 + i550])) (\\[i551, i552, i553, i554, i555, i556, i557] -> [let w356 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i551, i552, i553, i554, i555, i556, i557], let w357 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w357 ! [i551, i552, i553, i554, i555, i556, i557], let v358 = rconst (fromList [2] [0,1]) ; w359 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rconst 2) * v358)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w359 ! [i551, i552, i553, i554, i555, i556, i557]]) ; w564 = rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w353 * rreshape [1,1,4,4,1,1,2,2] (rtranspose [1,2,3,4,0] (rreplicate 4 u558))))))) (\\[i559, i560, i561, i562, i563] -> [ifF ((0 <=. i559 + i560 &&* 1 >. i559 + i560) &&* ((0 <=. i561 &&* 1 >. i561) &&* ((0 <=. i562 &&* 2 >. i562) &&* (0 <=. i563 &&* 2 >. i563)))) 0 1, i559, i560, i561, i562, i563]) in (rscatter [1,1,2,2] (w564 ! [0]) (\\[i565, i566] -> [i565 + i566]), rsum (rsum (rsum (rtranspose [0,2,3,1] u558))), rscatter [1,1,2,2] (w512 ! [0]) (\\[i513, i514] -> [i513 + i514]), rsum (rsum (rsum (rtranspose [0,2,3,1] u505))), rsum (rtranspose [2,1,0] (t468 * rreplicate 1 m474)), rsum (rtranspose [1,0] m474), rsum (rtranspose [2,1,0] (t473 * rreplicate 1 dret)), rsum (rtranspose [1,0] dret))"
  printPrimal6Pretty renames artifactRev
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w353 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 (rconst 7.0)) (\\[i285, i286] -> [i286])) (\\[i287, i288, i289] -> [i288, i289])) (\\[i290, i291, i292, i293] -> [i291, i292, i293])) (\\[i294, i295, i296, i297, i298] -> [i295, i296, i297, i298])) (\\[i299, i300, i301, i302, i303, i304] -> [i300, i301, i302, i303, i304])) (\\[i305, i306, i307, i308, i309, i310, i311] -> [i306, i307, i308, i309, i310, i311]), rgather [1,4,4,1,1,2,2] (rgather [4,4,1,1,2,2] (rgather [4,1,1,2,2] (rgather [1,1,2,2] (rgather [1,2,2] (rgather [2,2] (rreplicate 2 (rconst 0.0)) (\\[i312, i313] -> [i313])) (\\[i314, i315, i316] -> [i315, i316])) (\\[i317, i318, i319, i320] -> [i318, i319, i320])) (\\[i321, i322, i323, i324, i325] -> [i322, i323, i324, i325])) (\\[i326, i327, i328, i329, i330, i331] -> [i327, i328, i329, i330, i331])) (\\[i332, i333, i334, i335, i336, i337, i338] -> [i333, i334, i335, i336, i337, i338])]) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 4 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 4 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345]))) ; w354 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u2 (\\[i346, i347] -> [i346 + i347]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))]) (\\[i348, i349, i350, i351, i352] -> [ifF ((0 <=. i348 + i349 &&* 1 >. i348 + i349) &&* ((0 <=. i350 &&* 1 >. i350) &&* ((0 <=. i351 &&* 2 >. i351) &&* (0 <=. i352 &&* 2 >. i352)))) 0 1, i348, i349, i350, i351, i352]))))) ; w355 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,4,4,4] (w353 * w354))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v3)))))))))) ; w375 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i360, i361, i362, i363, i364, i365, i366, i367] -> [ifF (w355 ! [i360, i361, i362, i363, i364, i365, i366, let w356 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i360, i361, i362, i363, i364, i365, i366], let w357 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w357 ! [i360, i361, i362, i363, i364, i365, i366], let v358 = rconst (fromList [2] [0,1]) ; w359 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rconst 2) * v358)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w359 ! [i360, i361, i362, i363, i364, i365, i366], i367] <=. rconst 0.0) 0 1]) ; w376 = rgather [1,1,2,2,1,1,2,4] w355 (\\[i368, i369, i370, i371, i372, i373, i374] -> [i368, i369, i370, i371, i372, i373, i374, let w356 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w356 ! [i368, i369, i370, i371, i372, i373, i374], let w357 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w357 ! [i368, i369, i370, i371, i372, i373, i374], let v358 = rconst (fromList [2] [0,1]) ; w359 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rconst 2) * v358)) + rreplicate 2 (rconst (fromList [2] [0,1])))))))) in w359 ! [i368, i369, i370, i371, i372, i373, i374]]) ; w393 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w375 * w376) (\\[i377, i378, i379, i380, i381, i382, i383, i384] -> [i377, i378, i379, i380, i381, i382, i383, 2 * i380 + i384]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))))]) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [ifF ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. i386 + i390 &&* 1 >. i386 + i390) &&* ((0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391) &&* (0 <=. 2 * i388 + i392 &&* 4 >. 2 * i388 + i392)))) 0 1, i385, i386, i387, i388, i389, i390, i391, i392]))))))) ; w421 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w393 (\\[i396, i397, i398, i399, i400, i401, i402] -> [i396, i397, i398, i399, i400, i401, let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], i398 + i402, 0, 0, rem (quot (rmaxIndex (rgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], let i403 = i398 + i402 in i403, 0, 0]) (\\[i404] -> [rem (quot i404 2) 2, rem i404 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, let w394 = rtranspose [4,0,1,5,2,3] (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = rtranspose [0,4,1,2,3] (rreplicate 1 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], let i405 = i398 + i402 in i405, 0, 0]) (\\[i406] -> [rem (quot i406 2) 2, rem i406 2]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))))]) (\\[i407, i408, i409, i410, i411, i412, i413] -> [ifF ((0 <=. i407 + i410 &&* 1 >. i407 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i408 + i412 &&* 2 >. i408 + i412) &&* (0 <=. i409 + i413 &&* 2 >. i409 + i413)))) 0 1, i407, i408, i409, i410, i411, i412, i413]))) ; w422 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u4 (\\[i414, i415] -> [i414 + i415]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))]) (\\[i416, i417, i418, i419, i420] -> [ifF ((0 <=. i416 + i417 &&* 1 >. i416 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i419 &&* 2 >. i419) &&* (0 <=. i420 &&* 2 >. i420)))) 0 1, i416, i417, i418, i419, i420]))))) ; w423 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rtranspose [4,0,1,2,3] (rreshape [1,1,2,2,4] (w421 * w422))) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v5)))))))))) ; w443 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i428, i429, i430, i431, i432, i433, i434, i435] -> [ifF (w423 ! [i428, i429, i430, i431, i432, i433, i434, let w424 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i428, i429, i430, i431, i432, i433, i434], let w425 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w425 ! [i428, i429, i430, i431, i432, i433, i434], let v426 = rconst (fromList [1] [0]) ; w427 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 (rconst 2) * v426)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w427 ! [i428, i429, i430, i431, i432, i433, i434], i435] <=. rconst 0.0) 0 1]) ; w444 = rgather [1,1,1,1,1,1,2,2] w423 (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, let w424 = rtranspose [5,0,1,2,6,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w424 ! [i436, i437, i438, i439, i440, i441, i442], let w425 = rtranspose [0,5,1,2,3,6,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rtranspose [1,0] (rreplicate 1 (rconst (fromList [1] [0]))) + rreplicate 1 (rconst (fromList [1] [0])))))))) in w425 ! [i436, i437, i438, i439, i440, i441, i442], let v426 = rconst (fromList [1] [0]) ; w427 = rtranspose [0,1,5,2,3,4] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rtranspose [1,0] (rreplicate 2 (rreplicate 1 (rconst 2) * v426)) + rreplicate 1 (rconst (fromList [2] [0,1])))))))) in w427 ! [i436, i437, i438, i439, i440, i441, i442]]) ; w461 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w443 * w444) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, 2 * i448 + i452]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))))]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [ifF ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459) &&* (0 <=. 2 * i456 + i460 &&* 2 >. 2 * i456 + i460)))) 0 1, i453, i454, i455, i456, i457, i458, i459, i460]) ; t468 = rtranspose [1,0] (rreplicate 1 (rtranspose [1,0] (rreshape [1,1] (rgather [1,1,1,1] w461 (\\[i462, i463, i464, i465] -> [i462, i463, i464, i465, 0, 0, rem (quot (rmaxIndex (rgather [4] (w461 ! [i462, i463, i464, i465, 0, 0]) (\\[i466] -> [rem (quot i466 2) 2, rem i466 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w461 ! [i462, i463, i464, i465, 0, 0]) (\\[i467] -> [rem (quot i467 2) 2, rem i467 2]))) 2]))))) ; m469 = rsum (rtranspose [2,1,0] (rreplicate 1 m6) * t468) + rtranspose [1,0] (rreplicate 1 v7) ; m472 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i470, i471] -> [ifF (m469 ! [i470, i471] <=. rconst 0.0) 0 1]) ; t473 = rtranspose [1,0] (rreplicate 10 (m472 * m469)) in rsum (rtranspose [2,1,0] (rreplicate 1 m8) * t473) + rtranspose [1,0] (rreplicate 1 v9)"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w353 = rtranspose [1,0] (rreplicate 1 (rgather [1,4,4,1,1,2,2] (rfromList [rreplicate 1 (rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 7.0))))))), rreplicate 1 (rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))))]) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 4 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 4 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345]))) ; w355 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,4,4] (w353 ! [0, 0] * rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 u2), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))]) (\\[i635, i636, i637, i638, i639, i640] -> [ifF ((0 <=. i637 &&* 1 >. i637) &&* ((0 <=. i638 &&* 1 >. i638) &&* ((0 <=. i639 &&* 2 >. i639) &&* (0 <=. i640 &&* 2 >. i640)))) 0 1, i635, i636, i637, i638, i639, i640])) (\\[i614, i615, i616, i617, i618] -> [rem (quot (i614 + 4 * i618 + 16 * i617 + 64 * i615 + 64 * i616) 16) 4, rem (quot (i614 + 4 * i618 + 16 * i617 + 64 * i615 + 64 * i616) 4) 4, 0, 0, rem (quot (i614 + 4 * i618 + 16 * i617 + 64 * i615 + 64 * i616) 2) 2, rem (i614 + 4 * i618 + 16 * i617 + 64 * i615 + 64 * i616) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v3)))))))))) ; w375 = rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i360, i361, i362, i363, i364, i365, i366, i367] -> [ifF (w355 ! [i360, i361, i362, i363, i364, i365, i366, rconst (fromList [1] [0]) ! [i360] + rconst (fromList [1] [0]) ! [i364], rconst (fromList [1] [0]) ! [i361] + rconst (fromList [1] [0]) ! [i365], 2 * rconst (fromList [2] [0,1]) ! [i362] + rconst (fromList [2] [0,1]) ! [i366], i367] <=. rconst 0.0) 0 1]) ; w393 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (w375 * rgather [1,1,2,2,1,1,2,4] w355 (\\[i368, i369, i370, i371, i372, i373, i374] -> [i368, i369, i370, i371, i372, i373, i374, rconst (fromList [1] [0]) ! [i368] + rconst (fromList [1] [0]) ! [i372], rconst (fromList [1] [0]) ! [i369] + rconst (fromList [1] [0]) ! [i373], 2 * rconst (fromList [2] [0,1]) ! [i370] + rconst (fromList [2] [0,1]) ! [i374]])) (\\[i377, i378, i379, i380, i381, i382, i383, i384] -> [i377, i378, i379, i380, i381, i382, i383, 2 * i380 + i384]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))))]) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [ifF ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. i386 + i390 &&* 1 >. i386 + i390) &&* ((0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391) &&* (0 <=. 2 * i388 + i392 &&* 4 >. 2 * i388 + i392)))) 0 1, i385, i386, i387, i388, i389, i390, i391, i392]))))))) ; w421 = rtranspose [1,0] (rreplicate 1 (rgather [1,2,2,1,1,2,2] (rfromList [rgather [1,2,2,1,1,2,2] w393 (\\[i396, i397, i398, i399, i400, i401, i402] -> [i396, i397, i398, i399, i400, i401, rconst (fromList [1] [0]) ! [i396] + rconst (fromList [1] [0]) ! [i399], i400, rconst (fromList [2] [0,1]) ! [i397] + rconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0, rem (quot (rmaxIndex (rgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, rconst (fromList [1] [0]) ! [i396] + rconst (fromList [1] [0]) ! [i399], i400, rconst (fromList [2] [0,1]) ! [i397] + rconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0]) (\\[i404] -> [rem (quot i404 2) 2, rem i404 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, rconst (fromList [1] [0]) ! [i396] + rconst (fromList [1] [0]) ! [i399], i400, rconst (fromList [2] [0,1]) ! [i397] + rconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0]) (\\[i406] -> [rem (quot i406 2) 2, rem i406 2]))) 2]), rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))))]) (\\[i407, i408, i409, i410, i411, i412, i413] -> [ifF ((0 <=. i407 + i410 &&* 1 >. i407 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i408 + i412 &&* 2 >. i408 + i412) &&* (0 <=. i409 + i413 &&* 2 >. i409 + i413)))) 0 1, i407, i408, i409, i410, i411, i412, i413]))) ; w422 = rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 (rgather [1,1,1,2,2] (rfromList [rgather [1,1,1,2,2] u4 (\\[i414, i415] -> [i414 + i415]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0)))))]) (\\[i416, i417, i418, i419, i420] -> [ifF ((0 <=. i416 + i417 &&* 1 >. i416 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i419 &&* 2 >. i419) &&* (0 <=. i420 &&* 2 >. i420)))) 0 1, i416, i417, i418, i419, i420]))))) ; w423 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,2,2] (w421 ! [0, 0] * w422 ! [0, 0]) (\\[i604, i605, i606, i607, i608] -> [rem (quot (i604 + 4 * i608 + 8 * i607 + 16 * i605 + 16 * i606) 8) 2, rem (quot (i604 + 4 * i608 + 8 * i607 + 16 * i605 + 16 * i606) 4) 2, 0, 0, rem (quot (i604 + 4 * i608 + 8 * i607 + 16 * i605 + 16 * i606) 2) 2, rem (i604 + 4 * i608 + 8 * i607 + 16 * i605 + 16 * i606) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v5)))))))))) ; w443 = rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i428, i429, i430, i431, i432, i433, i434, i435] -> [ifF (w423 ! [i428, i429, i430, i431, i432, i433, i434, rconst (fromList [1] [0]) ! [i428] + rconst (fromList [1] [0]) ! [i432], rconst (fromList [1] [0]) ! [i429] + rconst (fromList [1] [0]) ! [i433], 2 * rconst (fromList [1] [0]) ! [i430] + rconst (fromList [2] [0,1]) ! [i434], i435] <=. rconst 0.0) 0 1]) ; w461 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (w443 * rgather [1,1,1,1,1,1,2,2] w423 (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, rconst (fromList [1] [0]) ! [i436] + rconst (fromList [1] [0]) ! [i440], rconst (fromList [1] [0]) ! [i437] + rconst (fromList [1] [0]) ! [i441], 2 * rconst (fromList [1] [0]) ! [i438] + rconst (fromList [2] [0,1]) ! [i442]])) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, 2 * i448 + i452]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))))]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [ifF ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459) &&* (0 <=. 2 * i456 + i460 &&* 2 >. 2 * i456 + i460)))) 0 1, i453, i454, i455, i456, i457, i458, i459, i460]) ; t468 = rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 (w461 ! [0, 0, 0, 0, 0, 0, rem (quot (rmaxIndex (rgather [4] (w461 ! [0, 0, 0, 0, 0, 0]) (\\[i466] -> [rem (quot i466 2) 2, rem i466 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w461 ! [0, 0, 0, 0, 0, 0]) (\\[i467] -> [rem (quot i467 2) 2, rem i467 2]))) 2])))) ; m469 = rsum (rtranspose [2,1,0] (rreplicate 1 m6) * t468) + rtranspose [1,0] (rreplicate 1 v7) ; m472 = rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i470, i471] -> [ifF (m469 ! [i470, i471] <=. rconst 0.0) 0 1]) ; m474 = m472 * rsum (rtranspose [1,2,0] (rreplicate 1 m8) * rtranspose [1,0] (rreplicate 1 dret)) ; u505 = rscatter [1,1,2,2] (w443 * rscatter [1,1,1,1,1,1,2,2] (rscatter [2,1,1,1,1,1,1,2,2] (rscatter [1,1,1,1,1,1,2,2] (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rsum (rgather [1] (m6 * rgather [1,1] m474 (\\[i598, i599] -> [i598, 0])) (\\[i601] -> [i601, 0]))))))) (\\[i475, i476, i477, i478] -> [i475, i476, i477, i478, 0, 0, rem (quot (rmaxIndex (rgather [4] (w461 ! [i475, i476, i477, i478, 0, 0]) (\\[i479] -> [rem (quot i479 2) 2, rem i479 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w461 ! [i475, i476, i477, i478, 0, 0]) (\\[i480] -> [rem (quot i480 2) 2, rem i480 2]))) 2])) (\\[i481, i482, i483, i484, i485, i486, i487, i488] -> [ifF ((0 <=. i481 + i485 &&* 1 >. i481 + i485) &&* ((0 <=. i482 + i486 &&* 1 >. i482 + i486) &&* ((0 <=. 2 * i483 + i487 &&* 2 >. 2 * i483 + i487) &&* (0 <=. 2 * i484 + i488 &&* 2 >. 2 * i484 + i488)))) 0 1, i481, i482, i483, i484, i485, i486, i487, i488]) ! [0]) (\\[i490, i491, i492, i493, i494, i495, i496, i497] -> [i490, i491, i492, i493, i494, i495, i496, 2 * i493 + i497])) (\\[i498, i499, i500, i501, i502, i503, i504] -> [rconst (fromList [1] [0]) ! [i498] + rconst (fromList [1] [0]) ! [i502], rconst (fromList [1] [0]) ! [i499] + rconst (fromList [1] [0]) ! [i503], 2 * rconst (fromList [1] [0]) ! [i500] + rconst (fromList [2] [0,1]) ! [i504]]) ; w506 = rgather [1,1,2,2,1,1,2,2] (u505 ! [0, 0]) (\\[i580, i581, i582, i583, i584, i585, i586, i587] -> [rem (quot (i587 + 2 * i586 + 4 * i585 + 4 * i584 + 4 * i583 + 8 * i582 + 16 * i580 + 16 * i581) 8) 2, rem (quot (i587 + 2 * i586 + 4 * i585 + 4 * i584 + 4 * i583 + 8 * i582 + 16 * i580 + 16 * i581) 4) 2]) ; u558 = rscatter [1,1,4,4] (w375 * rscatter [1,1,2,2,1,1,2,4] (rscatter [2,1,1,2,2,1,1,2,2] (rscatter [1,1,2,2,1,1,2,2] (rscatter [2,1,2,2,1,1,2,2] (rsum (rtranspose [1,0] (w422 * w506))) (\\[i515, i516, i517, i518, i519, i520, i521] -> [ifF ((0 <=. i515 + i518 &&* 1 >. i515 + i518) &&* ((0 <=. i519 &&* 1 >. i519) &&* ((0 <=. i516 + i520 &&* 2 >. i516 + i520) &&* (0 <=. i517 + i521 &&* 2 >. i517 + i521)))) 0 1, i515, i516, i517, i518, i519, i520, i521]) ! [0]) (\\[i523, i524, i525, i526, i527, i528, i529] -> [rconst (fromList [1] [0]) ! [i523] + rconst (fromList [1] [0]) ! [i526], i527, rconst (fromList [2] [0,1]) ! [i524] + rconst (fromList [2] [0,1]) ! [i528], i525 + i529, 0, 0, rem (quot (rmaxIndex (rgather [4] (w393 ! [i523, i524, i525, i526, i527, i528, rconst (fromList [1] [0]) ! [i523] + rconst (fromList [1] [0]) ! [i526], i527, rconst (fromList [2] [0,1]) ! [i524] + rconst (fromList [2] [0,1]) ! [i528], i525 + i529, 0, 0]) (\\[i531] -> [rem (quot i531 2) 2, rem i531 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w393 ! [i523, i524, i525, i526, i527, i528, rconst (fromList [1] [0]) ! [i523] + rconst (fromList [1] [0]) ! [i526], i527, rconst (fromList [2] [0,1]) ! [i524] + rconst (fromList [2] [0,1]) ! [i528], i525 + i529, 0, 0]) (\\[i533] -> [rem (quot i533 2) 2, rem i533 2]))) 2])) (\\[i534, i535, i536, i537, i538, i539, i540, i541] -> [ifF ((0 <=. i534 + i538 &&* 1 >. i534 + i538) &&* ((0 <=. i535 + i539 &&* 1 >. i535 + i539) &&* ((0 <=. 2 * i536 + i540 &&* 4 >. 2 * i536 + i540) &&* (0 <=. 2 * i537 + i541 &&* 4 >. 2 * i537 + i541)))) 0 1, i534, i535, i536, i537, i538, i539, i540, i541]) ! [0]) (\\[i543, i544, i545, i546, i547, i548, i549, i550] -> [i543, i544, i545, i546, i547, i548, i549, 2 * i546 + i550])) (\\[i551, i552, i553, i554, i555, i556, i557] -> [rconst (fromList [1] [0]) ! [i551] + rconst (fromList [1] [0]) ! [i555], rconst (fromList [1] [0]) ! [i552] + rconst (fromList [1] [0]) ! [i556], 2 * rconst (fromList [2] [0,1]) ! [i553] + rconst (fromList [2] [0,1]) ! [i557]]) in (rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w353 * rgather [1,1,4,4,1,1,2,2] (u558 ! [0, 0]) (\\[i567, i568, i569, i570, i571, i572, i573, i574] -> [rem (quot (i574 + 2 * i573 + 4 * i572 + 4 * i571 + 4 * i570 + 16 * i569 + 64 * i567 + 64 * i568) 16) 4, rem (quot (i574 + 2 * i573 + 4 * i572 + 4 * i571 + 4 * i570 + 16 * i569 + 64 * i567 + 64 * i568) 4) 4])))))) (\\[i559, i560, i561, i562, i563] -> [ifF ((0 <=. i559 + i560 &&* 1 >. i559 + i560) &&* ((0 <=. i561 &&* 1 >. i561) &&* ((0 <=. i562 &&* 2 >. i562) &&* (0 <=. i563 &&* 2 >. i563)))) 0 1, i559, i560, i561, i562, i563]) ! [0]) (\\[i565, i566] -> [i565 + i566]), rsum (rsum (rsum (rtranspose [0,2,3,1] u558))), rscatter [1,1,2,2] (rscatter [2,1,1,1,2,2] (rsum (rsum (rsum (rtranspose [0,2,3,1] (w421 * w506))))) (\\[i507, i508, i509, i510, i511] -> [ifF ((0 <=. i507 + i508 &&* 1 >. i507 + i508) &&* ((0 <=. i509 &&* 1 >. i509) &&* ((0 <=. i510 &&* 2 >. i510) &&* (0 <=. i511 &&* 2 >. i511)))) 0 1, i507, i508, i509, i510, i511]) ! [0]) (\\[i513, i514] -> [i513 + i514]), rsum (rsum (rsum (rtranspose [0,2,3,1] u505))), rsum (rtranspose [2,1,0] (t468 * rreplicate 1 m474)), rsum (rtranspose [1,0] m474), rsum (rtranspose [2,0,1] (rreplicate 10 (m472 * m469)) * rtranspose [2,1,0] (rreplicate 1 dret)), rsum (rtranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w355 = rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,4,4] (rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 7.0)))))), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))]) (\\[i703, i704, i705, i706, i707, i708] -> [ifF ((0 <=. i705 &&* 1 >. i705) &&* ((0 <=. i706 &&* 1 >. i706) &&* ((0 <=. i703 + i707 &&* 4 >. i703 + i707) &&* (0 <=. i704 + i708 &&* 4 >. i704 + i708)))) 0 1, i703, i704, i705, i706, i707, i708]) * rgather [4,4,1,1,2,2] (rfromList [rreplicate 4 (rreplicate 4 u2), rreplicate 4 (rreplicate 4 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))]) (\\[i697, i698, i699, i700, i701, i702] -> [ifF ((0 <=. i699 &&* 1 >. i699) &&* ((0 <=. i700 &&* 1 >. i700) &&* ((0 <=. i701 &&* 2 >. i701) &&* (0 <=. i702 &&* 2 >. i702)))) 0 1, i697, i698, i699, i700, i701, i702])) (\\[i641, i642, i643, i644, i645] -> [rem (quot (i641 + 4 * i645 + 16 * i644 + 64 * i642 + 64 * i643) 16) 4, rem (quot (i641 + 4 * i645 + 16 * i644 + 64 * i642 + 64 * i643) 4) 4, 0, 0, rem (quot (i641 + 4 * i645 + 16 * i644 + 64 * i642 + 64 * i643) 2) 2, rem (i641 + 4 * i645 + 16 * i644 + 64 * i642 + 64 * i643) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 4 (rreplicate 4 v3)))))))))) ; w393 = rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rgather [1,1,2,2,1,1,2,2] (rfromList [rgather [1,1,2,2,1,1,2,2] (rgather [1,1,2,2,1,1,2,4] (rconst (fromList [2] [0.0,1.0])) (\\[i360, i361, i362, i363, i364, i365, i366, i367] -> [ifF (w355 ! [i360, i361, i362, i363, i364, i365, i366, rconst (fromList [1] [0]) ! [i360] + rconst (fromList [1] [0]) ! [i364], rconst (fromList [1] [0]) ! [i361] + rconst (fromList [1] [0]) ! [i365], 2 * rconst (fromList [2] [0,1]) ! [i362] + rconst (fromList [2] [0,1]) ! [i366], i367] <=. rconst 0.0) 0 1]) * rgather [1,1,2,2,1,1,2,4] w355 (\\[i368, i369, i370, i371, i372, i373, i374] -> [i368, i369, i370, i371, i372, i373, i374, rconst (fromList [1] [0]) ! [i368] + rconst (fromList [1] [0]) ! [i372], rconst (fromList [1] [0]) ! [i369] + rconst (fromList [1] [0]) ! [i373], 2 * rconst (fromList [2] [0,1]) ! [i370] + rconst (fromList [2] [0,1]) ! [i374]])) (\\[i377, i378, i379, i380, i381, i382, i383, i384] -> [i377, i378, i379, i380, i381, i382, i383, 2 * i380 + i384]), rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))))]) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [ifF ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. i386 + i390 &&* 1 >. i386 + i390) &&* ((0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391) &&* (0 <=. 2 * i388 + i392 &&* 4 >. 2 * i388 + i392)))) 0 1, i385, i386, i387, i388, i389, i390, i391, i392]))))))) ; w423 = rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rsum (rgather [4,1,1,2,2] (rgather [2,2,1,1,2,2] (rfromList [rgather [2,2,1,1,2,2] (w393 ! [0]) (\\[i397, i398, i399, i400, i401, i402] -> [i397, i398, i399, i400, i401, rconst (fromList [1] [0]) ! [i399], i400, rconst (fromList [2] [0,1]) ! [i397] + rconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0, rem (quot (rmaxIndex (rgather [4] (w393 ! [0, i397, i398, i399, i400, i401, rconst (fromList [1] [0]) ! [i399], i400, rconst (fromList [2] [0,1]) ! [i397] + rconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0]) (\\[i404] -> [rem (quot i404 2) 2, rem i404 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w393 ! [0, i397, i398, i399, i400, i401, rconst (fromList [1] [0]) ! [i399], i400, rconst (fromList [2] [0,1]) ! [i397] + rconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0]) (\\[i406] -> [rem (quot i406 2) 2, rem i406 2]))) 2]), rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))]) (\\[i680, i681, i682, i683, i684, i685] -> [ifF ((0 <=. i682 &&* 1 >. i682) &&* ((0 <=. i683 &&* 1 >. i683) &&* ((0 <=. i680 + i684 &&* 2 >. i680 + i684) &&* (0 <=. i681 + i685 &&* 2 >. i681 + i685)))) 0 1, i680, i681, i682, i683, i684, i685]) * rgather [2,2,1,1,2,2] (rfromList [rreplicate 2 (rreplicate 2 u4), rreplicate 2 (rreplicate 2 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))]) (\\[i674, i675, i676, i677, i678, i679] -> [ifF ((0 <=. i676 &&* 1 >. i676) &&* ((0 <=. i677 &&* 1 >. i677) &&* ((0 <=. i678 &&* 2 >. i678) &&* (0 <=. i679 &&* 2 >. i679)))) 0 1, i674, i675, i676, i677, i678, i679])) (\\[i651, i652, i653, i654, i655] -> [rem (quot (i651 + 4 * i655 + 8 * i654 + 16 * i652 + 16 * i653) 8) 2, rem (quot (i651 + 4 * i655 + 8 * i654 + 16 * i652 + 16 * i653) 4) 2, 0, 0, rem (quot (i651 + 4 * i655 + 8 * i654 + 16 * i652 + 16 * i653) 2) 2, rem (i651 + 4 * i655 + 8 * i654 + 16 * i652 + 16 * i653) 2])) + rtranspose [0,3,1,2] (rreplicate 1 (rreplicate 2 (rreplicate 2 v5)))))))))) ; w461 = rgather [1,1,1,1,1,1,2,2] (rfromList [rgather [1,1,1,1,1,1,2,2] (rgather [1,1,1,1,1,1,2,2] (rconst (fromList [2] [0.0,1.0])) (\\[i428, i429, i430, i431, i432, i433, i434, i435] -> [ifF (w423 ! [i428, i429, i430, i431, i432, i433, i434, rconst (fromList [1] [0]) ! [i428] + rconst (fromList [1] [0]) ! [i432], rconst (fromList [1] [0]) ! [i429] + rconst (fromList [1] [0]) ! [i433], 2 * rconst (fromList [1] [0]) ! [i430] + rconst (fromList [2] [0,1]) ! [i434], i435] <=. rconst 0.0) 0 1]) * rgather [1,1,1,1,1,1,2,2] w423 (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, rconst (fromList [1] [0]) ! [i436] + rconst (fromList [1] [0]) ! [i440], rconst (fromList [1] [0]) ! [i437] + rconst (fromList [1] [0]) ! [i441], 2 * rconst (fromList [1] [0]) ! [i438] + rconst (fromList [2] [0,1]) ! [i442]])) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, 2 * i448 + i452]), rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 1 (rreplicate 2 (rreplicate 2 (rconst 0.0))))))))]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [ifF ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459) &&* (0 <=. 2 * i456 + i460 &&* 2 >. 2 * i456 + i460)))) 0 1, i453, i454, i455, i456, i457, i458, i459, i460]) ; m469 = rsum (rtranspose [2,1,0] (rreplicate 1 m6) * rtranspose [2,0,1] (rreplicate 1 (rreplicate 1 (rreplicate 1 (w461 ! [0, 0, 0, 0, 0, 0, rem (quot (rmaxIndex (rgather [4] (w461 ! [0, 0, 0, 0, 0, 0]) (\\[i466] -> [rem (quot i466 2) 2, rem i466 2]))) 2) 2, rem (rmaxIndex (rgather [4] (w461 ! [0, 0, 0, 0, 0, 0]) (\\[i467] -> [rem (quot i467 2) 2, rem i467 2]))) 2]))))) + rtranspose [1,0] (rreplicate 1 v7) in rsum (rtranspose [2,1,0] (rreplicate 1 m8) * rtranspose [1,0] (rreplicate 10 (rgather [1,1] (rconst (fromList [2] [0.0,1.0])) (\\[i470, i471] -> [ifF (m469 ! [i470, i471] <=. rconst 0.0) 0 1]) * m469))) + rtranspose [1,0] (rreplicate 1 v9)"
