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
import HordeAd.Core.AstFreshId (funToAstIOR, funToAstRevIO, resetVarCounter)
import HordeAd.Core.TensorADVal
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
      ftest miniBatchSize' mnist testParams =
        MnistCnnRanked2.convMnistTestR miniBatchSize' mnist
          (\f -> runFlip $ f $ parseDomains valsInit testParams)
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
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f (glyphR, labelR) adinputs =
                   MnistCnnRanked2.convMnistLossFusedR
                     miniBatchSize (tconst glyphR, tconst labelR)
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
           runEpoch n !paramsStateAdam@(!_, !_) = do
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
      ftest miniBatchSize' mnist testParams =
        MnistCnnRanked2.convMnistTestR miniBatchSize' mnist
          (\f -> runFlip $ f $ parseDomains valsInit testParams)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map rankBatch
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rankBatch . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       (_, astsPrimal, vars, _) <- funToAstRevIO domainsInit
       let testDataR = packBatchR testData
           domainsPrimal = V.fromList astsPrimal
       (varGlyph, _, astGlyph) <-
         funToAstIOR
           (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
           id
       (varLabel, _, astLabel) <-
         funToAstIOR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
       let ast :: AstRanked PrimalSpan r 0
           ast = MnistCnnRanked2.convMnistLossFusedR
                   miniBatchSize
                     ( tprimalPart @(AstRanked PrimalSpan) astGlyph
                     , tprimalPart @(AstRanked PrimalSpan) astLabel )
                     (parseDomains @(AstDynamic PrimalSpan)
                                   valsInit domainsPrimal)
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (DomainsOD, StateAdam)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env = foldr extendEnvDR EM.empty
                             $ zip vars $ V.toList varInputs
                       envMnist = extendEnvR varGlyph (tconst glyph)
                                  $ extendEnvR varLabel (tconst label) env
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
           runEpoch n !paramsStateAdam@(!_, !_) = do
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
        ftest miniBatchSize' mnist testParams =
          MnistCnnRanked2.convMnistTestR miniBatchSize' mnist
            (\f -> runFlip $ f $ parseDomains valsInit testParams)
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
       let envInit = extendEnvR varGlyph (tconstant astGlyph)
                     $ extendEnvR varLabel (tconstant astLabel)
                       EM.empty
           f = MnistCnnRanked2.convMnistLossFusedR
                 miniBatchSize (astGlyph, astLabel)
           (((varDtAgain, vars1Again), gradientRaw, primal), _) =
             revDtInit @Nat @AstRanked
                       False f valsInit envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
           vars = (varDtAgain, vars1AndInputAgain)
           go :: [MnistDataBatchR r] -> (DomainsOD, StateAdam)
              -> (DomainsOD, StateAdam)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) !(!parameters, !stateAdam) =
             let glyphD = DynamicExists $ dfromR @(Flip OR.Array) $ tconst glyph
                 labelD = DynamicExists $ dfromR @(Flip OR.Array) $ tconst label
                 parametersAndInput =
                   V.concat [parameters, V.fromList [glyphD, labelD]]
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientDomain)
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (DomainsOD, StateAdam)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
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
           runEpoch n !paramsStateAdam@(!_, !_) = do
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
      (artifact6, _) = revDtFun True afcnn2T valsInit
  printGradient6Pretty renames artifact6
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w353 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 7.0)) (\\[i285, i286] -> [i286])) (\\[i287, i288, i289] -> [i288, i289])) (\\[i290, i291, i292, i293] -> [i291, i292, i293])) (\\[i294, i295, i296, i297, i298] -> [i295, i296, i297, i298])) (\\[i299, i300, i301, i302, i303, i304] -> [i300, i301, i302, i303, i304])) (\\[i305, i306, i307, i308, i309, i310, i311] -> [i306, i307, i308, i309, i310, i311]), tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 0.0)) (\\[i312, i313] -> [i313])) (\\[i314, i315, i316] -> [i315, i316])) (\\[i317, i318, i319, i320] -> [i318, i319, i320])) (\\[i321, i322, i323, i324, i325] -> [i322, i323, i324, i325])) (\\[i326, i327, i328, i329, i330, i331] -> [i327, i328, i329, i330, i331])) (\\[i332, i333, i334, i335, i336, i337, i338] -> [i333, i334, i335, i336, i337, i338])]) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 4 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 4 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345]))) ; w354 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u2 (\\[i346, i347] -> [i346 + i347]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i348, i349, i350, i351, i352] -> [ifF ((0 <=. i348 + i349 &&* 1 >. i348 + i349) &&* ((0 <=. i350 &&* 1 >. i350) &&* ((0 <=. i351 &&* 2 >. i351) &&* (0 <=. i352 &&* 2 >. i352)))) 0 1, i348, i349, i350, i351, i352]))))) ; w355 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,4,4,4] (w353 * w354))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w375 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i360, i361, i362, i363, i364, i365, i366, i367] -> [ifF (w355 ! [i360, i361, i362, i363, i364, i365, i366, let w356 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w356 ! [i360, i361, i362, i363, i364, i365, i366], let w357 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w357 ! [i360, i361, i362, i363, i364, i365, i366], let v358 = tconst (fromList [2] [0,1]) ; w359 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v358)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w359 ! [i360, i361, i362, i363, i364, i365, i366], i367] <=. tconst 0.0) 0 1]) ; w376 = tgather [1,1,2,2,1,1,2,4] w355 (\\[i368, i369, i370, i371, i372, i373, i374] -> [i368, i369, i370, i371, i372, i373, i374, let w356 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w356 ! [i368, i369, i370, i371, i372, i373, i374], let w357 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w357 ! [i368, i369, i370, i371, i372, i373, i374], let v358 = tconst (fromList [2] [0,1]) ; w359 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v358)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w359 ! [i368, i369, i370, i371, i372, i373, i374]]) ; w393 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w375 * w376) (\\[i377, i378, i379, i380, i381, i382, i383, i384] -> [i377, i378, i379, i380, i381, i382, i383, 2 * i380 + i384]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [ifF ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. i386 + i390 &&* 1 >. i386 + i390) &&* ((0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391) &&* (0 <=. 2 * i388 + i392 &&* 4 >. 2 * i388 + i392)))) 0 1, i385, i386, i387, i388, i389, i390, i391, i392]))))))) ; w417 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w393 (\\[i396, i397, i398, i399, i400, i401, i402] -> [i396, i397, i398, i399, i400, i401, let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], i398 + i402, 0, 0, rem (quot (tmaxIndex (tgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], let i561 = i398 + i402 in i561, 0, 0]) (\\[i562] -> [rem (quot i562 2) 2, rem i562 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], let i563 = i398 + i402 in i563, 0, 0]) (\\[i564] -> [rem (quot i564 2) 2, rem i564 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i403, i404, i405, i406, i407, i408, i409] -> [ifF ((0 <=. i403 + i406 &&* 1 >. i403 + i406) &&* ((0 <=. i407 &&* 1 >. i407) &&* ((0 <=. i404 + i408 &&* 2 >. i404 + i408) &&* (0 <=. i405 + i409 &&* 2 >. i405 + i409)))) 0 1, i403, i404, i405, i406, i407, i408, i409]))) ; w418 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i410, i411] -> [i410 + i411]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i412, i413, i414, i415, i416] -> [ifF ((0 <=. i412 + i413 &&* 1 >. i412 + i413) &&* ((0 <=. i414 &&* 1 >. i414) &&* ((0 <=. i415 &&* 2 >. i415) &&* (0 <=. i416 &&* 2 >. i416)))) 0 1, i412, i413, i414, i415, i416]))))) ; w419 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,2,2,4] (w417 * w418))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w439 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i424, i425, i426, i427, i428, i429, i430, i431] -> [ifF (w419 ! [i424, i425, i426, i427, i428, i429, i430, let w420 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w420 ! [i424, i425, i426, i427, i428, i429, i430], let w421 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w421 ! [i424, i425, i426, i427, i428, i429, i430], let v422 = tconst (fromList [1] [0]) ; w423 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v422)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w423 ! [i424, i425, i426, i427, i428, i429, i430], i431] <=. tconst 0.0) 0 1]) ; w440 = tgather [1,1,1,1,1,1,2,2] w419 (\\[i432, i433, i434, i435, i436, i437, i438] -> [i432, i433, i434, i435, i436, i437, i438, let w420 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w420 ! [i432, i433, i434, i435, i436, i437, i438], let w421 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w421 ! [i432, i433, i434, i435, i436, i437, i438], let v422 = tconst (fromList [1] [0]) ; w423 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v422)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w423 ! [i432, i433, i434, i435, i436, i437, i438]]) ; w457 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w439 * w440) (\\[i441, i442, i443, i444, i445, i446, i447, i448] -> [i441, i442, i443, i444, i445, i446, i447, 2 * i444 + i448]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i449, i450, i451, i452, i453, i454, i455, i456] -> [ifF ((0 <=. i449 + i453 &&* 1 >. i449 + i453) &&* ((0 <=. i450 + i454 &&* 1 >. i450 + i454) &&* ((0 <=. 2 * i451 + i455 &&* 2 >. 2 * i451 + i455) &&* (0 <=. 2 * i452 + i456 &&* 2 >. 2 * i452 + i456)))) 0 1, i449, i450, i451, i452, i453, i454, i455, i456]) ; t462 = ttranspose [1,0] (treplicate 1 (ttranspose [1,0] (treshape [1,1] (tgather [1,1,1,1] w457 (\\[i458, i459, i460, i461] -> [i458, i459, i460, i461, 0, 0, rem (quot (tmaxIndex (tgather [4] (w457 ! [i458, i459, i460, i461, 0, 0]) (\\[i565] -> [rem (quot i565 2) 2, rem i565 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w457 ! [i458, i459, i460, i461, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2]))))) ; m463 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t462) + ttranspose [1,0] (treplicate 1 v7) ; m466 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i464, i465] -> [ifF (m463 ! [i464, i465] <=. tconst 0.0) 0 1]) ; t467 = ttranspose [1,0] (treplicate 10 (m466 * m463)) ; m468 = m466 * tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret)) ; w483 = tscatter [2,1,1,1,1,1,1,2,2] (tscatter [1,1,1,1,1,1,2,2] (treshape [1,1,1,1] (tsum (ttranspose [1,0] (treplicate 1 m6) * ttranspose [1,2,0] (treplicate 1 m468)))) (\\[i469, i470, i471, i472] -> [i469, i470, i471, i472, 0, 0, rem (quot (tmaxIndex (tgather [4] (w457 ! [i469, i470, i471, i472, 0, 0]) (\\[i473] -> [rem (quot i473 2) 2, rem i473 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w457 ! [i469, i470, i471, i472, 0, 0]) (\\[i474] -> [rem (quot i474 2) 2, rem i474 2]))) 2])) (\\[i475, i476, i477, i478, i479, i480, i481, i482] -> [ifF ((0 <=. i475 + i479 &&* 1 >. i475 + i479) &&* ((0 <=. i476 + i480 &&* 1 >. i476 + i480) &&* ((0 <=. 2 * i477 + i481 &&* 2 >. 2 * i477 + i481) &&* (0 <=. 2 * i478 + i482 &&* 2 >. 2 * i478 + i482)))) 0 1, i475, i476, i477, i478, i479, i480, i481, i482]) ; u499 = tscatter [1,1,2,2] (w439 * tscatter [1,1,1,1,1,1,2,2] (w483 ! [0]) (\\[i484, i485, i486, i487, i488, i489, i490, i491] -> [i484, i485, i486, i487, i488, i489, i490, 2 * i487 + i491])) (\\[i492, i493, i494, i495, i496, i497, i498] -> [let w420 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w420 ! [i492, i493, i494, i495, i496, i497, i498], let w421 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w421 ! [i492, i493, i494, i495, i496, i497, i498], let v422 = tconst (fromList [1] [0]) ; w423 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v422)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w423 ! [i492, i493, i494, i495, i496, i497, i498]]) ; w500 = treshape [1,1,2,2,1,1,2,2] (ttranspose [1,2,3,4,0] (treplicate 4 u499)) ; w506 = tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w417 * w500))))) (\\[i501, i502, i503, i504, i505] -> [ifF ((0 <=. i501 + i502 &&* 1 >. i501 + i502) &&* ((0 <=. i503 &&* 1 >. i503) &&* ((0 <=. i504 &&* 2 >. i504) &&* (0 <=. i505 &&* 2 >. i505)))) 0 1, i501, i502, i503, i504, i505]) ; w516 = tscatter [2,1,2,2,1,1,2,2] (tsum (ttranspose [1,0] (w418 * w500))) (\\[i509, i510, i511, i512, i513, i514, i515] -> [ifF ((0 <=. i509 + i512 &&* 1 >. i509 + i512) &&* ((0 <=. i513 &&* 1 >. i513) &&* ((0 <=. i510 + i514 &&* 2 >. i510 + i514) &&* (0 <=. i511 + i515 &&* 2 >. i511 + i515)))) 0 1, i509, i510, i511, i512, i513, i514, i515]) ; w536 = tscatter [2,1,1,2,2,1,1,2,2] (tscatter [1,1,2,2,1,1,2,2] (w516 ! [0]) (\\[i517, i518, i519, i520, i521, i522, i523] -> [let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i517, i518, i519, i520, i521, i522], i521, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i517, i518, i519, i520, i521, i522], i519 + i523, 0, 0, rem (quot (tmaxIndex (tgather [4] (w393 ! [i517, i518, i519, i520, i521, i522, let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i517, i518, i519, i520, i521, i522], i521, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i517, i518, i519, i520, i521, i522], let i524 = i519 + i523 in i524, 0, 0]) (\\[i525] -> [rem (quot i525 2) 2, rem i525 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w393 ! [i517, i518, i519, i520, i521, i522, let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i517, i518, i519, i520, i521, i522], i521, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i517, i518, i519, i520, i521, i522], let i526 = i519 + i523 in i526, 0, 0]) (\\[i527] -> [rem (quot i527 2) 2, rem i527 2]))) 2])) (\\[i528, i529, i530, i531, i532, i533, i534, i535] -> [ifF ((0 <=. i528 + i532 &&* 1 >. i528 + i532) &&* ((0 <=. i529 + i533 &&* 1 >. i529 + i533) &&* ((0 <=. 2 * i530 + i534 &&* 4 >. 2 * i530 + i534) &&* (0 <=. 2 * i531 + i535 &&* 4 >. 2 * i531 + i535)))) 0 1, i528, i529, i530, i531, i532, i533, i534, i535]) ; u552 = tscatter [1,1,4,4] (w375 * tscatter [1,1,2,2,1,1,2,4] (w536 ! [0]) (\\[i537, i538, i539, i540, i541, i542, i543, i544] -> [i537, i538, i539, i540, i541, i542, i543, 2 * i540 + i544])) (\\[i545, i546, i547, i548, i549, i550, i551] -> [let w356 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w356 ! [i545, i546, i547, i548, i549, i550, i551], let w357 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w357 ! [i545, i546, i547, i548, i549, i550, i551], let v358 = tconst (fromList [2] [0,1]) ; w359 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v358)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w359 ! [i545, i546, i547, i548, i549, i550, i551]]) ; w558 = tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w353 * treshape [1,1,4,4,1,1,2,2] (ttranspose [1,2,3,4,0] (treplicate 4 u552))))))) (\\[i553, i554, i555, i556, i557] -> [ifF ((0 <=. i553 + i554 &&* 1 >. i553 + i554) &&* ((0 <=. i555 &&* 1 >. i555) &&* ((0 <=. i556 &&* 2 >. i556) &&* (0 <=. i557 &&* 2 >. i557)))) 0 1, i553, i554, i555, i556, i557]) in (tscatter [1,1,2,2] (w558 ! [0]) (\\[i559, i560] -> [i559 + i560]), tsum (tsum (tsum (ttranspose [0,2,3,1] u552))), tscatter [1,1,2,2] (w506 ! [0]) (\\[i507, i508] -> [i507 + i508]), tsum (tsum (tsum (ttranspose [0,2,3,1] u499))), tsum (ttranspose [2,1,0] (t462 * treplicate 1 m468)), tsum (ttranspose [1,0] m468), tsum (ttranspose [2,1,0] (t467 * treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w353 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 7.0)) (\\[i285, i286] -> [i286])) (\\[i287, i288, i289] -> [i288, i289])) (\\[i290, i291, i292, i293] -> [i291, i292, i293])) (\\[i294, i295, i296, i297, i298] -> [i295, i296, i297, i298])) (\\[i299, i300, i301, i302, i303, i304] -> [i300, i301, i302, i303, i304])) (\\[i305, i306, i307, i308, i309, i310, i311] -> [i306, i307, i308, i309, i310, i311]), tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 0.0)) (\\[i312, i313] -> [i313])) (\\[i314, i315, i316] -> [i315, i316])) (\\[i317, i318, i319, i320] -> [i318, i319, i320])) (\\[i321, i322, i323, i324, i325] -> [i322, i323, i324, i325])) (\\[i326, i327, i328, i329, i330, i331] -> [i327, i328, i329, i330, i331])) (\\[i332, i333, i334, i335, i336, i337, i338] -> [i333, i334, i335, i336, i337, i338])]) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 4 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 4 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345]))) ; w354 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u2 (\\[i346, i347] -> [i346 + i347]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i348, i349, i350, i351, i352] -> [ifF ((0 <=. i348 + i349 &&* 1 >. i348 + i349) &&* ((0 <=. i350 &&* 1 >. i350) &&* ((0 <=. i351 &&* 2 >. i351) &&* (0 <=. i352 &&* 2 >. i352)))) 0 1, i348, i349, i350, i351, i352]))))) ; w355 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,4,4,4] (w353 * w354))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w375 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i360, i361, i362, i363, i364, i365, i366, i367] -> [ifF (w355 ! [i360, i361, i362, i363, i364, i365, i366, let w356 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w356 ! [i360, i361, i362, i363, i364, i365, i366], let w357 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w357 ! [i360, i361, i362, i363, i364, i365, i366], let v358 = tconst (fromList [2] [0,1]) ; w359 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v358)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w359 ! [i360, i361, i362, i363, i364, i365, i366], i367] <=. tconst 0.0) 0 1]) ; w376 = tgather [1,1,2,2,1,1,2,4] w355 (\\[i368, i369, i370, i371, i372, i373, i374] -> [i368, i369, i370, i371, i372, i373, i374, let w356 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w356 ! [i368, i369, i370, i371, i372, i373, i374], let w357 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w357 ! [i368, i369, i370, i371, i372, i373, i374], let v358 = tconst (fromList [2] [0,1]) ; w359 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v358)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w359 ! [i368, i369, i370, i371, i372, i373, i374]]) ; w393 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w375 * w376) (\\[i377, i378, i379, i380, i381, i382, i383, i384] -> [i377, i378, i379, i380, i381, i382, i383, 2 * i380 + i384]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [ifF ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. i386 + i390 &&* 1 >. i386 + i390) &&* ((0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391) &&* (0 <=. 2 * i388 + i392 &&* 4 >. 2 * i388 + i392)))) 0 1, i385, i386, i387, i388, i389, i390, i391, i392]))))))) ; w417 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w393 (\\[i396, i397, i398, i399, i400, i401, i402] -> [i396, i397, i398, i399, i400, i401, let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], i398 + i402, 0, 0, rem (quot (tmaxIndex (tgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], let i561 = i398 + i402 in i561, 0, 0]) (\\[i562] -> [rem (quot i562 2) 2, rem i562 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, let w394 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w394 ! [i396, i397, i398, i399, i400, i401], i400, let w395 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w395 ! [i396, i397, i398, i399, i400, i401], let i563 = i398 + i402 in i563, 0, 0]) (\\[i564] -> [rem (quot i564 2) 2, rem i564 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i403, i404, i405, i406, i407, i408, i409] -> [ifF ((0 <=. i403 + i406 &&* 1 >. i403 + i406) &&* ((0 <=. i407 &&* 1 >. i407) &&* ((0 <=. i404 + i408 &&* 2 >. i404 + i408) &&* (0 <=. i405 + i409 &&* 2 >. i405 + i409)))) 0 1, i403, i404, i405, i406, i407, i408, i409]))) ; w418 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i410, i411] -> [i410 + i411]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i412, i413, i414, i415, i416] -> [ifF ((0 <=. i412 + i413 &&* 1 >. i412 + i413) &&* ((0 <=. i414 &&* 1 >. i414) &&* ((0 <=. i415 &&* 2 >. i415) &&* (0 <=. i416 &&* 2 >. i416)))) 0 1, i412, i413, i414, i415, i416]))))) ; w419 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,2,2,4] (w417 * w418))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w439 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i424, i425, i426, i427, i428, i429, i430, i431] -> [ifF (w419 ! [i424, i425, i426, i427, i428, i429, i430, let w420 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w420 ! [i424, i425, i426, i427, i428, i429, i430], let w421 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w421 ! [i424, i425, i426, i427, i428, i429, i430], let v422 = tconst (fromList [1] [0]) ; w423 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v422)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w423 ! [i424, i425, i426, i427, i428, i429, i430], i431] <=. tconst 0.0) 0 1]) ; w440 = tgather [1,1,1,1,1,1,2,2] w419 (\\[i432, i433, i434, i435, i436, i437, i438] -> [i432, i433, i434, i435, i436, i437, i438, let w420 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w420 ! [i432, i433, i434, i435, i436, i437, i438], let w421 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w421 ! [i432, i433, i434, i435, i436, i437, i438], let v422 = tconst (fromList [1] [0]) ; w423 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v422)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w423 ! [i432, i433, i434, i435, i436, i437, i438]]) ; w457 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w439 * w440) (\\[i441, i442, i443, i444, i445, i446, i447, i448] -> [i441, i442, i443, i444, i445, i446, i447, 2 * i444 + i448]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i449, i450, i451, i452, i453, i454, i455, i456] -> [ifF ((0 <=. i449 + i453 &&* 1 >. i449 + i453) &&* ((0 <=. i450 + i454 &&* 1 >. i450 + i454) &&* ((0 <=. 2 * i451 + i455 &&* 2 >. 2 * i451 + i455) &&* (0 <=. 2 * i452 + i456 &&* 2 >. 2 * i452 + i456)))) 0 1, i449, i450, i451, i452, i453, i454, i455, i456]) ; t462 = ttranspose [1,0] (treplicate 1 (ttranspose [1,0] (treshape [1,1] (tgather [1,1,1,1] w457 (\\[i458, i459, i460, i461] -> [i458, i459, i460, i461, 0, 0, rem (quot (tmaxIndex (tgather [4] (w457 ! [i458, i459, i460, i461, 0, 0]) (\\[i565] -> [rem (quot i565 2) 2, rem i565 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w457 ! [i458, i459, i460, i461, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2]))))) ; m463 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t462) + ttranspose [1,0] (treplicate 1 v7) ; m466 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i464, i465] -> [ifF (m463 ! [i464, i465] <=. tconst 0.0) 0 1]) ; t467 = ttranspose [1,0] (treplicate 10 (m466 * m463)) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * t467) + ttranspose [1,0] (treplicate 1 v9)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w353 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [treplicate 1 (treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 7.0))))))), treplicate 1 (treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i339, i340, i341, i342, i343, i344, i345] -> [ifF ((0 <=. i339 + i342 &&* 1 >. i339 + i342) &&* ((0 <=. i343 &&* 1 >. i343) &&* ((0 <=. i340 + i344 &&* 4 >. i340 + i344) &&* (0 <=. i341 + i345 &&* 4 >. i341 + i345)))) 0 1, i339, i340, i341, i342, i343, i344, i345]))) ; w355 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,4,4] (w353 ! [0, 0] * tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 u2), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i635, i636, i637, i638, i639, i640] -> [ifF ((0 <=. i637 &&* 1 >. i637) &&* ((0 <=. i638 &&* 1 >. i638) &&* ((0 <=. i639 &&* 2 >. i639) &&* (0 <=. i640 &&* 2 >. i640)))) 0 1, i635, i636, i637, i638, i639, i640])) (\\[i614, i615, i616, i617, i618] -> [rem (quot (i614 + 64 * i615 + 16 * i617 + 4 * i618 + 64 * i616) 16) 4, rem (quot (i614 + 64 * i615 + 16 * i617 + 4 * i618 + 64 * i616) 4) 4, 0, 0, rem (quot (i614 + 64 * i615 + 16 * i617 + 4 * i618 + 64 * i616) 2) 2, rem (i614 + 64 * i615 + 16 * i617 + 4 * i618 + 64 * i616) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w375 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i360, i361, i362, i363, i364, i365, i366, i367] -> [ifF (w355 ! [i360, i361, i362, i363, i364, i365, i366, tconst (fromList [1] [0]) ! [i360] + tconst (fromList [1] [0]) ! [i364], tconst (fromList [1] [0]) ! [i361] + tconst (fromList [1] [0]) ! [i365], 2 * tconst (fromList [2] [0,1]) ! [i362] + tconst (fromList [2] [0,1]) ! [i366], i367] <=. tconst 0.0) 0 1]) ; w393 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w375 * tgather [1,1,2,2,1,1,2,4] w355 (\\[i368, i369, i370, i371, i372, i373, i374] -> [i368, i369, i370, i371, i372, i373, i374, tconst (fromList [1] [0]) ! [i368] + tconst (fromList [1] [0]) ! [i372], tconst (fromList [1] [0]) ! [i369] + tconst (fromList [1] [0]) ! [i373], 2 * tconst (fromList [2] [0,1]) ! [i370] + tconst (fromList [2] [0,1]) ! [i374]])) (\\[i377, i378, i379, i380, i381, i382, i383, i384] -> [i377, i378, i379, i380, i381, i382, i383, 2 * i380 + i384]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [ifF ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. i386 + i390 &&* 1 >. i386 + i390) &&* ((0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391) &&* (0 <=. 2 * i388 + i392 &&* 4 >. 2 * i388 + i392)))) 0 1, i385, i386, i387, i388, i389, i390, i391, i392]))))))) ; w417 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w393 (\\[i396, i397, i398, i399, i400, i401, i402] -> [i396, i397, i398, i399, i400, i401, tconst (fromList [1] [0]) ! [i396] + tconst (fromList [1] [0]) ! [i399], i400, tconst (fromList [2] [0,1]) ! [i397] + tconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0, rem (quot (tmaxIndex (tgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, tconst (fromList [1] [0]) ! [i396] + tconst (fromList [1] [0]) ! [i399], i400, tconst (fromList [2] [0,1]) ! [i397] + tconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0]) (\\[i562] -> [rem (quot i562 2) 2, rem i562 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w393 ! [i396, i397, i398, i399, i400, i401, tconst (fromList [1] [0]) ! [i396] + tconst (fromList [1] [0]) ! [i399], i400, tconst (fromList [2] [0,1]) ! [i397] + tconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0]) (\\[i564] -> [rem (quot i564 2) 2, rem i564 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i403, i404, i405, i406, i407, i408, i409] -> [ifF ((0 <=. i403 + i406 &&* 1 >. i403 + i406) &&* ((0 <=. i407 &&* 1 >. i407) &&* ((0 <=. i404 + i408 &&* 2 >. i404 + i408) &&* (0 <=. i405 + i409 &&* 2 >. i405 + i409)))) 0 1, i403, i404, i405, i406, i407, i408, i409]))) ; w418 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i410, i411] -> [i410 + i411]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i412, i413, i414, i415, i416] -> [ifF ((0 <=. i412 + i413 &&* 1 >. i412 + i413) &&* ((0 <=. i414 &&* 1 >. i414) &&* ((0 <=. i415 &&* 2 >. i415) &&* (0 <=. i416 &&* 2 >. i416)))) 0 1, i412, i413, i414, i415, i416]))))) ; w419 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,2,2] (w417 ! [0, 0] * w418 ! [0, 0]) (\\[i604, i605, i606, i607, i608] -> [rem (quot (i604 + 16 * i605 + 8 * i607 + 4 * i608 + 16 * i606) 8) 2, rem (quot (i604 + 16 * i605 + 8 * i607 + 4 * i608 + 16 * i606) 4) 2, 0, 0, rem (quot (i604 + 16 * i605 + 8 * i607 + 4 * i608 + 16 * i606) 2) 2, rem (i604 + 16 * i605 + 8 * i607 + 4 * i608 + 16 * i606) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w439 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i424, i425, i426, i427, i428, i429, i430, i431] -> [ifF (w419 ! [i424, i425, i426, i427, i428, i429, i430, tconst (fromList [1] [0]) ! [i424] + tconst (fromList [1] [0]) ! [i428], tconst (fromList [1] [0]) ! [i425] + tconst (fromList [1] [0]) ! [i429], 2 * tconst (fromList [1] [0]) ! [i426] + tconst (fromList [2] [0,1]) ! [i430], i431] <=. tconst 0.0) 0 1]) ; w457 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w439 * tgather [1,1,1,1,1,1,2,2] w419 (\\[i432, i433, i434, i435, i436, i437, i438] -> [i432, i433, i434, i435, i436, i437, i438, tconst (fromList [1] [0]) ! [i432] + tconst (fromList [1] [0]) ! [i436], tconst (fromList [1] [0]) ! [i433] + tconst (fromList [1] [0]) ! [i437], 2 * tconst (fromList [1] [0]) ! [i434] + tconst (fromList [2] [0,1]) ! [i438]])) (\\[i441, i442, i443, i444, i445, i446, i447, i448] -> [i441, i442, i443, i444, i445, i446, i447, 2 * i444 + i448]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i449, i450, i451, i452, i453, i454, i455, i456] -> [ifF ((0 <=. i449 + i453 &&* 1 >. i449 + i453) &&* ((0 <=. i450 + i454 &&* 1 >. i450 + i454) &&* ((0 <=. 2 * i451 + i455 &&* 2 >. 2 * i451 + i455) &&* (0 <=. 2 * i452 + i456 &&* 2 >. 2 * i452 + i456)))) 0 1, i449, i450, i451, i452, i453, i454, i455, i456]) ; t462 = ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (w457 ! [0, 0, 0, 0, 0, 0, rem (quot (tmaxIndex (tgather [4] (w457 ! [0, 0, 0, 0, 0, 0]) (\\[i565] -> [rem (quot i565 2) 2, rem i565 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w457 ! [0, 0, 0, 0, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2])))) ; m463 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t462) + ttranspose [1,0] (treplicate 1 v7) ; m466 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i464, i465] -> [ifF (m463 ! [i464, i465] <=. tconst 0.0) 0 1]) ; m468 = m466 * tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret)) ; u499 = tscatter [1,1,2,2] (w439 * tscatter [1,1,1,1,1,1,2,2] (tscatter [2,1,1,1,1,1,1,2,2] (tscatter [1,1,1,1,1,1,2,2] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tsum (tgather [1] (m6 * tgather [1,1] m468 (\\[i598, i599] -> [i598, 0])) (\\[i601] -> [i601, 0]))))))) (\\[i469, i470, i471, i472] -> [i469, i470, i471, i472, 0, 0, rem (quot (tmaxIndex (tgather [4] (w457 ! [i469, i470, i471, i472, 0, 0]) (\\[i473] -> [rem (quot i473 2) 2, rem i473 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w457 ! [i469, i470, i471, i472, 0, 0]) (\\[i474] -> [rem (quot i474 2) 2, rem i474 2]))) 2])) (\\[i475, i476, i477, i478, i479, i480, i481, i482] -> [ifF ((0 <=. i475 + i479 &&* 1 >. i475 + i479) &&* ((0 <=. i476 + i480 &&* 1 >. i476 + i480) &&* ((0 <=. 2 * i477 + i481 &&* 2 >. 2 * i477 + i481) &&* (0 <=. 2 * i478 + i482 &&* 2 >. 2 * i478 + i482)))) 0 1, i475, i476, i477, i478, i479, i480, i481, i482]) ! [0]) (\\[i484, i485, i486, i487, i488, i489, i490, i491] -> [i484, i485, i486, i487, i488, i489, i490, 2 * i487 + i491])) (\\[i492, i493, i494, i495, i496, i497, i498] -> [tconst (fromList [1] [0]) ! [i492] + tconst (fromList [1] [0]) ! [i496], tconst (fromList [1] [0]) ! [i493] + tconst (fromList [1] [0]) ! [i497], 2 * tconst (fromList [1] [0]) ! [i494] + tconst (fromList [2] [0,1]) ! [i498]]) ; w500 = tgather [1,1,2,2,1,1,2,2] (u499 ! [0, 0]) (\\[i580, i581, i582, i583, i584, i585, i586, i587] -> [rem (quot (i587 + 4 * i584 + 4 * i585 + 4 * i583 + 16 * i581 + 8 * i582 + 2 * i586 + 16 * i580) 8) 2, rem (quot (i587 + 4 * i584 + 4 * i585 + 4 * i583 + 16 * i581 + 8 * i582 + 2 * i586 + 16 * i580) 4) 2]) ; u552 = tscatter [1,1,4,4] (w375 * tscatter [1,1,2,2,1,1,2,4] (tscatter [2,1,1,2,2,1,1,2,2] (tscatter [1,1,2,2,1,1,2,2] (tscatter [2,1,2,2,1,1,2,2] (tsum (ttranspose [1,0] (w418 * w500))) (\\[i509, i510, i511, i512, i513, i514, i515] -> [ifF ((0 <=. i509 + i512 &&* 1 >. i509 + i512) &&* ((0 <=. i513 &&* 1 >. i513) &&* ((0 <=. i510 + i514 &&* 2 >. i510 + i514) &&* (0 <=. i511 + i515 &&* 2 >. i511 + i515)))) 0 1, i509, i510, i511, i512, i513, i514, i515]) ! [0]) (\\[i517, i518, i519, i520, i521, i522, i523] -> [tconst (fromList [1] [0]) ! [i517] + tconst (fromList [1] [0]) ! [i520], i521, tconst (fromList [2] [0,1]) ! [i518] + tconst (fromList [2] [0,1]) ! [i522], i519 + i523, 0, 0, rem (quot (tmaxIndex (tgather [4] (w393 ! [i517, i518, i519, i520, i521, i522, tconst (fromList [1] [0]) ! [i517] + tconst (fromList [1] [0]) ! [i520], i521, tconst (fromList [2] [0,1]) ! [i518] + tconst (fromList [2] [0,1]) ! [i522], i519 + i523, 0, 0]) (\\[i525] -> [rem (quot i525 2) 2, rem i525 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w393 ! [i517, i518, i519, i520, i521, i522, tconst (fromList [1] [0]) ! [i517] + tconst (fromList [1] [0]) ! [i520], i521, tconst (fromList [2] [0,1]) ! [i518] + tconst (fromList [2] [0,1]) ! [i522], i519 + i523, 0, 0]) (\\[i527] -> [rem (quot i527 2) 2, rem i527 2]))) 2])) (\\[i528, i529, i530, i531, i532, i533, i534, i535] -> [ifF ((0 <=. i528 + i532 &&* 1 >. i528 + i532) &&* ((0 <=. i529 + i533 &&* 1 >. i529 + i533) &&* ((0 <=. 2 * i530 + i534 &&* 4 >. 2 * i530 + i534) &&* (0 <=. 2 * i531 + i535 &&* 4 >. 2 * i531 + i535)))) 0 1, i528, i529, i530, i531, i532, i533, i534, i535]) ! [0]) (\\[i537, i538, i539, i540, i541, i542, i543, i544] -> [i537, i538, i539, i540, i541, i542, i543, 2 * i540 + i544])) (\\[i545, i546, i547, i548, i549, i550, i551] -> [tconst (fromList [1] [0]) ! [i545] + tconst (fromList [1] [0]) ! [i549], tconst (fromList [1] [0]) ! [i546] + tconst (fromList [1] [0]) ! [i550], 2 * tconst (fromList [2] [0,1]) ! [i547] + tconst (fromList [2] [0,1]) ! [i551]]) in (tscatter [1,1,2,2] (tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w353 * tgather [1,1,4,4,1,1,2,2] (u552 ! [0, 0]) (\\[i567, i568, i569, i570, i571, i572, i573, i574] -> [rem (quot (i574 + 4 * i571 + 4 * i572 + 4 * i570 + 64 * i568 + 16 * i569 + 2 * i573 + 64 * i567) 16) 4, rem (quot (i574 + 4 * i571 + 4 * i572 + 4 * i570 + 64 * i568 + 16 * i569 + 2 * i573 + 64 * i567) 4) 4])))))) (\\[i553, i554, i555, i556, i557] -> [ifF ((0 <=. i553 + i554 &&* 1 >. i553 + i554) &&* ((0 <=. i555 &&* 1 >. i555) &&* ((0 <=. i556 &&* 2 >. i556) &&* (0 <=. i557 &&* 2 >. i557)))) 0 1, i553, i554, i555, i556, i557]) ! [0]) (\\[i559, i560] -> [i559 + i560]), tsum (tsum (tsum (ttranspose [0,2,3,1] u552))), tscatter [1,1,2,2] (tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w417 * w500))))) (\\[i501, i502, i503, i504, i505] -> [ifF ((0 <=. i501 + i502 &&* 1 >. i501 + i502) &&* ((0 <=. i503 &&* 1 >. i503) &&* ((0 <=. i504 &&* 2 >. i504) &&* (0 <=. i505 &&* 2 >. i505)))) 0 1, i501, i502, i503, i504, i505]) ! [0]) (\\[i507, i508] -> [i507 + i508]), tsum (tsum (tsum (ttranspose [0,2,3,1] u499))), tsum (ttranspose [2,1,0] (t462 * treplicate 1 m468)), tsum (ttranspose [1,0] m468), tsum (ttranspose [2,0,1] (treplicate 10 (m466 * m463)) * ttranspose [2,1,0] (treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w355 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,4,4] (tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 7.0)))))), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i703, i704, i705, i706, i707, i708] -> [ifF ((0 <=. i705 &&* 1 >. i705) &&* ((0 <=. i706 &&* 1 >. i706) &&* ((0 <=. i703 + i707 &&* 4 >. i703 + i707) &&* (0 <=. i704 + i708 &&* 4 >. i704 + i708)))) 0 1, i703, i704, i705, i706, i707, i708]) * tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 u2), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i697, i698, i699, i700, i701, i702] -> [ifF ((0 <=. i699 &&* 1 >. i699) &&* ((0 <=. i700 &&* 1 >. i700) &&* ((0 <=. i701 &&* 2 >. i701) &&* (0 <=. i702 &&* 2 >. i702)))) 0 1, i697, i698, i699, i700, i701, i702])) (\\[i641, i642, i643, i644, i645] -> [rem (quot (i641 + 64 * i642 + 16 * i644 + 4 * i645 + 64 * i643) 16) 4, rem (quot (i641 + 64 * i642 + 16 * i644 + 4 * i645 + 64 * i643) 4) 4, 0, 0, rem (quot (i641 + 64 * i642 + 16 * i644 + 4 * i645 + 64 * i643) 2) 2, rem (i641 + 64 * i642 + 16 * i644 + 4 * i645 + 64 * i643) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w393 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i360, i361, i362, i363, i364, i365, i366, i367] -> [ifF (w355 ! [i360, i361, i362, i363, i364, i365, i366, tconst (fromList [1] [0]) ! [i360] + tconst (fromList [1] [0]) ! [i364], tconst (fromList [1] [0]) ! [i361] + tconst (fromList [1] [0]) ! [i365], 2 * tconst (fromList [2] [0,1]) ! [i362] + tconst (fromList [2] [0,1]) ! [i366], i367] <=. tconst 0.0) 0 1]) * tgather [1,1,2,2,1,1,2,4] w355 (\\[i368, i369, i370, i371, i372, i373, i374] -> [i368, i369, i370, i371, i372, i373, i374, tconst (fromList [1] [0]) ! [i368] + tconst (fromList [1] [0]) ! [i372], tconst (fromList [1] [0]) ! [i369] + tconst (fromList [1] [0]) ! [i373], 2 * tconst (fromList [2] [0,1]) ! [i370] + tconst (fromList [2] [0,1]) ! [i374]])) (\\[i377, i378, i379, i380, i381, i382, i383, i384] -> [i377, i378, i379, i380, i381, i382, i383, 2 * i380 + i384]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [ifF ((0 <=. i385 + i389 &&* 1 >. i385 + i389) &&* ((0 <=. i386 + i390 &&* 1 >. i386 + i390) &&* ((0 <=. 2 * i387 + i391 &&* 4 >. 2 * i387 + i391) &&* (0 <=. 2 * i388 + i392 &&* 4 >. 2 * i388 + i392)))) 0 1, i385, i386, i387, i388, i389, i390, i391, i392]))))))) ; w419 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,2,2] (tgather [2,2,1,1,2,2] (tfromList [tgather [2,2,1,1,2,2] (w393 ! [0]) (\\[i397, i398, i399, i400, i401, i402] -> [i397, i398, i399, i400, i401, tconst (fromList [1] [0]) ! [i399], i400, tconst (fromList [2] [0,1]) ! [i397] + tconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0, rem (quot (tmaxIndex (tgather [4] (w393 ! [0, i397, i398, i399, i400, i401, tconst (fromList [1] [0]) ! [i399], i400, tconst (fromList [2] [0,1]) ! [i397] + tconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0]) (\\[i562] -> [rem (quot i562 2) 2, rem i562 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w393 ! [0, i397, i398, i399, i400, i401, tconst (fromList [1] [0]) ! [i399], i400, tconst (fromList [2] [0,1]) ! [i397] + tconst (fromList [2] [0,1]) ! [i401], i398 + i402, 0, 0]) (\\[i564] -> [rem (quot i564 2) 2, rem i564 2]))) 2]), treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i680, i681, i682, i683, i684, i685] -> [ifF ((0 <=. i682 &&* 1 >. i682) &&* ((0 <=. i683 &&* 1 >. i683) &&* ((0 <=. i680 + i684 &&* 2 >. i680 + i684) &&* (0 <=. i681 + i685 &&* 2 >. i681 + i685)))) 0 1, i680, i681, i682, i683, i684, i685]) * tgather [2,2,1,1,2,2] (tfromList [treplicate 2 (treplicate 2 u4), treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i674, i675, i676, i677, i678, i679] -> [ifF ((0 <=. i676 &&* 1 >. i676) &&* ((0 <=. i677 &&* 1 >. i677) &&* ((0 <=. i678 &&* 2 >. i678) &&* (0 <=. i679 &&* 2 >. i679)))) 0 1, i674, i675, i676, i677, i678, i679])) (\\[i651, i652, i653, i654, i655] -> [rem (quot (i651 + 16 * i652 + 8 * i654 + 4 * i655 + 16 * i653) 8) 2, rem (quot (i651 + 16 * i652 + 8 * i654 + 4 * i655 + 16 * i653) 4) 2, 0, 0, rem (quot (i651 + 16 * i652 + 8 * i654 + 4 * i655 + 16 * i653) 2) 2, rem (i651 + 16 * i652 + 8 * i654 + 4 * i655 + 16 * i653) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w457 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i424, i425, i426, i427, i428, i429, i430, i431] -> [ifF (w419 ! [i424, i425, i426, i427, i428, i429, i430, tconst (fromList [1] [0]) ! [i424] + tconst (fromList [1] [0]) ! [i428], tconst (fromList [1] [0]) ! [i425] + tconst (fromList [1] [0]) ! [i429], 2 * tconst (fromList [1] [0]) ! [i426] + tconst (fromList [2] [0,1]) ! [i430], i431] <=. tconst 0.0) 0 1]) * tgather [1,1,1,1,1,1,2,2] w419 (\\[i432, i433, i434, i435, i436, i437, i438] -> [i432, i433, i434, i435, i436, i437, i438, tconst (fromList [1] [0]) ! [i432] + tconst (fromList [1] [0]) ! [i436], tconst (fromList [1] [0]) ! [i433] + tconst (fromList [1] [0]) ! [i437], 2 * tconst (fromList [1] [0]) ! [i434] + tconst (fromList [2] [0,1]) ! [i438]])) (\\[i441, i442, i443, i444, i445, i446, i447, i448] -> [i441, i442, i443, i444, i445, i446, i447, 2 * i444 + i448]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i449, i450, i451, i452, i453, i454, i455, i456] -> [ifF ((0 <=. i449 + i453 &&* 1 >. i449 + i453) &&* ((0 <=. i450 + i454 &&* 1 >. i450 + i454) &&* ((0 <=. 2 * i451 + i455 &&* 2 >. 2 * i451 + i455) &&* (0 <=. 2 * i452 + i456 &&* 2 >. 2 * i452 + i456)))) 0 1, i449, i450, i451, i452, i453, i454, i455, i456]) ; m463 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (w457 ! [0, 0, 0, 0, 0, 0, rem (quot (tmaxIndex (tgather [4] (w457 ! [0, 0, 0, 0, 0, 0]) (\\[i565] -> [rem (quot i565 2) 2, rem i565 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w457 ! [0, 0, 0, 0, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2]))))) + ttranspose [1,0] (treplicate 1 v7) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 10 (tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i464, i465] -> [ifF (m463 ! [i464, i465] <=. tconst 0.0) 0 1]) * m463))) + ttranspose [1,0] (treplicate 1 v9)"
