{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
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

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInline
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.DualNumber (ADVal)
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.Optimizer
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

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCaseCNNA
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r
     , ADReady ranked r, Random r, ADReady (ADVal ranked) r
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

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCaseCNNI
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r
     , ADReady ranked r, Random r
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
       (vars1, _, asts1) <- funToAstAllIO domainsInit
       let testDataR = packBatchR testData
           doms = V.fromList asts1
       (varGlyph, _, astGlyph) <-
         funToAstIOR
           (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
           id
       (varLabel, _, astLabel) <-
         funToAstIOR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
       let ast :: AstRanked AstPrimal r 0
           ast = MnistCnnRanked2.convMnistLossFusedR
                   miniBatchSize (tprimalPart @(AstRanked AstPrimal) astGlyph, tprimalPart @(AstRanked AstPrimal) astLabel)
                                 (parseDomains @(AstDynamic AstPrimal) valsInit doms)
           runBatch :: (DomainsOD, StateAdam) -> (Int, [MnistDataR r])
                    -> IO (DomainsOD, StateAdam)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADValClown OD.Array)
                   -> ADVal ranked r 0
                 f (glyph, label) varInputs =
                   let env1 = foldr extendEnvDR EM.empty
                              $ zip vars1 $ V.toList varInputs
                       envMnist = extendEnvR varGlyph (tconst glyph)
                                  $ extendEnvR varLabel (tconst label) env1
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
mnistTestCaseCNNO
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, Differentiable r
     , ADReady ranked r, Random r, PrintfArg r, AssertEqualUpToEpsilon r )
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
      blackGlyph :: AstRanked AstPrimal Double 4
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
      afcnn2T :: MnistCnnRanked2.ADCnnMnistParameters (AstRanked AstFull) Double
              -> AstRanked AstFull Double 2
      afcnn2T = MnistCnnRanked2.convMnistTwoR sizeMnistHeightI sizeMnistWidthI
                                              batch_size blackGlyph
      (artifact6, _) = revDtFun True afcnn2T valsInit
  printGradient6Pretty renames artifact6
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w357 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 7.0)) (\\[i289, i290] -> [i290])) (\\[i291, i292, i293] -> [i292, i293])) (\\[i294, i295, i296, i297] -> [i295, i296, i297])) (\\[i298, i299, i300, i301, i302] -> [i299, i300, i301, i302])) (\\[i303, i304, i305, i306, i307, i308] -> [i304, i305, i306, i307, i308])) (\\[i309, i310, i311, i312, i313, i314, i315] -> [i310, i311, i312, i313, i314, i315]), tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 0.0)) (\\[i316, i317] -> [i317])) (\\[i318, i319, i320] -> [i319, i320])) (\\[i321, i322, i323, i324] -> [i322, i323, i324])) (\\[i325, i326, i327, i328, i329] -> [i326, i327, i328, i329])) (\\[i330, i331, i332, i333, i334, i335] -> [i331, i332, i333, i334, i335])) (\\[i336, i337, i338, i339, i340, i341, i342] -> [i337, i338, i339, i340, i341, i342])]) (\\[i343, i344, i345, i346, i347, i348, i349] -> [ifF ((0 <=. i343 + i346 &&* 1 >. i343 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i344 + i348 &&* 4 >. i344 + i348) &&* (0 <=. i345 + i349 &&* 4 >. i345 + i349)))) 0 1, i343, i344, i345, i346, i347, i348, i349]))) ; w358 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u2 (\\[i350, i351] -> [i350 + i351]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i352, i353, i354, i355, i356] -> [ifF ((0 <=. i352 + i353 &&* 1 >. i352 + i353) &&* ((0 <=. i354 &&* 1 >. i354) &&* ((0 <=. i355 &&* 2 >. i355) &&* (0 <=. i356 &&* 2 >. i356)))) 0 1, i352, i353, i354, i355, i356]))))) ; w359 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,4,4,4] (w357 * w358))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w379 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i364, i365, i366, i367, i368, i369, i370, i371] -> [ifF (w359 ! [i364, i365, i366, i367, i368, i369, i370, let w360 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w360 ! [i364, i365, i366, i367, i368, i369, i370], let w361 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w361 ! [i364, i365, i366, i367, i368, i369, i370], let v362 = tconst (fromList [2] [0,1]) ; w363 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v362)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w363 ! [i364, i365, i366, i367, i368, i369, i370], i371] <=. tconst 0.0) 0 1]) ; w380 = tgather [1,1,2,2,1,1,2,4] w359 (\\[i372, i373, i374, i375, i376, i377, i378] -> [i372, i373, i374, i375, i376, i377, i378, let w360 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w360 ! [i372, i373, i374, i375, i376, i377, i378], let w361 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w361 ! [i372, i373, i374, i375, i376, i377, i378], let v362 = tconst (fromList [2] [0,1]) ; w363 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v362)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w363 ! [i372, i373, i374, i375, i376, i377, i378]]) ; w397 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w379 * w380) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [i381, i382, i383, i384, i385, i386, i387, 2 * i384 + i388]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i389, i390, i391, i392, i393, i394, i395, i396] -> [ifF ((0 <=. i389 + i393 &&* 1 >. i389 + i393) &&* ((0 <=. i390 + i394 &&* 1 >. i390 + i394) &&* ((0 <=. 2 * i391 + i395 &&* 4 >. 2 * i391 + i395) &&* (0 <=. 2 * i392 + i396 &&* 4 >. 2 * i392 + i396)))) 0 1, i389, i390, i391, i392, i393, i394, i395, i396]))))))) ; w421 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w397 (\\[i400, i401, i402, i403, i404, i405, i406] -> [i400, i401, i402, i403, i404, i405, let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i400, i401, i402, i403, i404, i405], i404, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i400, i401, i402, i403, i404, i405], i402 + i406, 0, 0, rem (quot (tmaxIndex (tgather [4] (w397 ! [i400, i401, i402, i403, i404, i405, let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i400, i401, i402, i403, i404, i405], i404, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i400, i401, i402, i403, i404, i405], i402 + i406, 0, 0]) (\\[i563] -> [rem (quot i563 2) 2, rem i563 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w397 ! [i400, i401, i402, i403, i404, i405, let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i400, i401, i402, i403, i404, i405], i404, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i400, i401, i402, i403, i404, i405], i402 + i406, 0, 0]) (\\[i564] -> [rem (quot i564 2) 2, rem i564 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i407, i408, i409, i410, i411, i412, i413] -> [ifF ((0 <=. i407 + i410 &&* 1 >. i407 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i408 + i412 &&* 2 >. i408 + i412) &&* (0 <=. i409 + i413 &&* 2 >. i409 + i413)))) 0 1, i407, i408, i409, i410, i411, i412, i413]))) ; w422 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i414, i415] -> [i414 + i415]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i416, i417, i418, i419, i420] -> [ifF ((0 <=. i416 + i417 &&* 1 >. i416 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i419 &&* 2 >. i419) &&* (0 <=. i420 &&* 2 >. i420)))) 0 1, i416, i417, i418, i419, i420]))))) ; w423 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,2,2,4] (w421 * w422))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w443 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i428, i429, i430, i431, i432, i433, i434, i435] -> [ifF (w423 ! [i428, i429, i430, i431, i432, i433, i434, let w424 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w424 ! [i428, i429, i430, i431, i432, i433, i434], let w425 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w425 ! [i428, i429, i430, i431, i432, i433, i434], let v426 = tconst (fromList [1] [0]) ; w427 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v426)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w427 ! [i428, i429, i430, i431, i432, i433, i434], i435] <=. tconst 0.0) 0 1]) ; w444 = tgather [1,1,1,1,1,1,2,2] w423 (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, let w424 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w424 ! [i436, i437, i438, i439, i440, i441, i442], let w425 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w425 ! [i436, i437, i438, i439, i440, i441, i442], let v426 = tconst (fromList [1] [0]) ; w427 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v426)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w427 ! [i436, i437, i438, i439, i440, i441, i442]]) ; w461 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w443 * w444) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, 2 * i448 + i452]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [ifF ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459) &&* (0 <=. 2 * i456 + i460 &&* 2 >. 2 * i456 + i460)))) 0 1, i453, i454, i455, i456, i457, i458, i459, i460]) ; t466 = ttranspose [1,0] (treplicate 1 (ttranspose [1,0] (treshape [1,1] (tgather [1,1,1,1] w461 (\\[i462, i463, i464, i465] -> [i462, i463, i464, i465, 0, 0, rem (quot (tmaxIndex (tgather [4] (w461 ! [i462, i463, i464, i465, 0, 0]) (\\[i565] -> [rem (quot i565 2) 2, rem i565 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w461 ! [i462, i463, i464, i465, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2]))))) ; m467 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t466) + ttranspose [1,0] (treplicate 1 v7) ; m470 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i468, i469] -> [ifF (m467 ! [i468, i469] <=. tconst 0.0) 0 1]) ; t471 = ttranspose [1,0] (treplicate 10 (m470 * m467)) ; m472 = m470 * tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret)) ; w487 = tscatter [2,1,1,1,1,1,1,2,2] (tscatter [1,1,1,1,1,1,2,2] (treshape [1,1,1,1] (tsum (ttranspose [1,0] (treplicate 1 m6) * ttranspose [1,2,0] (treplicate 1 m472)))) (\\[i473, i474, i475, i476] -> [i473, i474, i475, i476, 0, 0, rem (quot (tmaxIndex (tgather [4] (w461 ! [i473, i474, i475, i476, 0, 0]) (\\[i477] -> [rem (quot i477 2) 2, rem i477 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w461 ! [i473, i474, i475, i476, 0, 0]) (\\[i478] -> [rem (quot i478 2) 2, rem i478 2]))) 2])) (\\[i479, i480, i481, i482, i483, i484, i485, i486] -> [ifF ((0 <=. i479 + i483 &&* 1 >. i479 + i483) &&* ((0 <=. i480 + i484 &&* 1 >. i480 + i484) &&* ((0 <=. 2 * i481 + i485 &&* 2 >. 2 * i481 + i485) &&* (0 <=. 2 * i482 + i486 &&* 2 >. 2 * i482 + i486)))) 0 1, i479, i480, i481, i482, i483, i484, i485, i486]) ; u503 = tscatter [1,1,2,2] (w443 * tscatter [1,1,1,1,1,1,2,2] (w487 ! [0]) (\\[i488, i489, i490, i491, i492, i493, i494, i495] -> [i488, i489, i490, i491, i492, i493, i494, 2 * i491 + i495])) (\\[i496, i497, i498, i499, i500, i501, i502] -> [let w424 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w424 ! [i496, i497, i498, i499, i500, i501, i502], let w425 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w425 ! [i496, i497, i498, i499, i500, i501, i502], let v426 = tconst (fromList [1] [0]) ; w427 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v426)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w427 ! [i496, i497, i498, i499, i500, i501, i502]]) ; w504 = treshape [1,1,2,2,1,1,2,2] (ttranspose [1,2,3,4,0] (treplicate 4 u503)) ; w510 = tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w421 * w504))))) (\\[i505, i506, i507, i508, i509] -> [ifF ((0 <=. i505 + i506 &&* 1 >. i505 + i506) &&* ((0 <=. i507 &&* 1 >. i507) &&* ((0 <=. i508 &&* 2 >. i508) &&* (0 <=. i509 &&* 2 >. i509)))) 0 1, i505, i506, i507, i508, i509]) ; w520 = tscatter [2,1,2,2,1,1,2,2] (tsum (ttranspose [1,0] (w422 * w504))) (\\[i513, i514, i515, i516, i517, i518, i519] -> [ifF ((0 <=. i513 + i516 &&* 1 >. i513 + i516) &&* ((0 <=. i517 &&* 1 >. i517) &&* ((0 <=. i514 + i518 &&* 2 >. i514 + i518) &&* (0 <=. i515 + i519 &&* 2 >. i515 + i519)))) 0 1, i513, i514, i515, i516, i517, i518, i519]) ; w538 = tscatter [2,1,1,2,2,1,1,2,2] (tscatter [1,1,2,2,1,1,2,2] (w520 ! [0]) (\\[i521, i522, i523, i524, i525, i526, i527] -> [let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i521, i522, i523, i524, i525, i526], i525, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i521, i522, i523, i524, i525, i526], i523 + i527, 0, 0, rem (quot (tmaxIndex (tgather [4] (w397 ! [i521, i522, i523, i524, i525, i526, let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i521, i522, i523, i524, i525, i526], i525, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i521, i522, i523, i524, i525, i526], i523 + i527, 0, 0]) (\\[i528] -> [rem (quot i528 2) 2, rem i528 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w397 ! [i521, i522, i523, i524, i525, i526, let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i521, i522, i523, i524, i525, i526], i525, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i521, i522, i523, i524, i525, i526], i523 + i527, 0, 0]) (\\[i529] -> [rem (quot i529 2) 2, rem i529 2]))) 2])) (\\[i530, i531, i532, i533, i534, i535, i536, i537] -> [ifF ((0 <=. i530 + i534 &&* 1 >. i530 + i534) &&* ((0 <=. i531 + i535 &&* 1 >. i531 + i535) &&* ((0 <=. 2 * i532 + i536 &&* 4 >. 2 * i532 + i536) &&* (0 <=. 2 * i533 + i537 &&* 4 >. 2 * i533 + i537)))) 0 1, i530, i531, i532, i533, i534, i535, i536, i537]) ; u554 = tscatter [1,1,4,4] (w379 * tscatter [1,1,2,2,1,1,2,4] (w538 ! [0]) (\\[i539, i540, i541, i542, i543, i544, i545, i546] -> [i539, i540, i541, i542, i543, i544, i545, 2 * i542 + i546])) (\\[i547, i548, i549, i550, i551, i552, i553] -> [let w360 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w360 ! [i547, i548, i549, i550, i551, i552, i553], let w361 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w361 ! [i547, i548, i549, i550, i551, i552, i553], let v362 = tconst (fromList [2] [0,1]) ; w363 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v362)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w363 ! [i547, i548, i549, i550, i551, i552, i553]]) ; w560 = tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w357 * treshape [1,1,4,4,1,1,2,2] (ttranspose [1,2,3,4,0] (treplicate 4 u554))))))) (\\[i555, i556, i557, i558, i559] -> [ifF ((0 <=. i555 + i556 &&* 1 >. i555 + i556) &&* ((0 <=. i557 &&* 1 >. i557) &&* ((0 <=. i558 &&* 2 >. i558) &&* (0 <=. i559 &&* 2 >. i559)))) 0 1, i555, i556, i557, i558, i559]) in (tscatter [1,1,2,2] (w560 ! [0]) (\\[i561, i562] -> [i561 + i562]), tsum (tsum (tsum (ttranspose [0,2,3,1] u554))), tscatter [1,1,2,2] (w510 ! [0]) (\\[i511, i512] -> [i511 + i512]), tsum (tsum (tsum (ttranspose [0,2,3,1] u503))), tsum (ttranspose [2,1,0] (t466 * treplicate 1 m472)), tsum (ttranspose [1,0] m472), tsum (ttranspose [2,1,0] (t471 * treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w357 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 7.0)) (\\[i289, i290] -> [i290])) (\\[i291, i292, i293] -> [i292, i293])) (\\[i294, i295, i296, i297] -> [i295, i296, i297])) (\\[i298, i299, i300, i301, i302] -> [i299, i300, i301, i302])) (\\[i303, i304, i305, i306, i307, i308] -> [i304, i305, i306, i307, i308])) (\\[i309, i310, i311, i312, i313, i314, i315] -> [i310, i311, i312, i313, i314, i315]), tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 0.0)) (\\[i316, i317] -> [i317])) (\\[i318, i319, i320] -> [i319, i320])) (\\[i321, i322, i323, i324] -> [i322, i323, i324])) (\\[i325, i326, i327, i328, i329] -> [i326, i327, i328, i329])) (\\[i330, i331, i332, i333, i334, i335] -> [i331, i332, i333, i334, i335])) (\\[i336, i337, i338, i339, i340, i341, i342] -> [i337, i338, i339, i340, i341, i342])]) (\\[i343, i344, i345, i346, i347, i348, i349] -> [ifF ((0 <=. i343 + i346 &&* 1 >. i343 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i344 + i348 &&* 4 >. i344 + i348) &&* (0 <=. i345 + i349 &&* 4 >. i345 + i349)))) 0 1, i343, i344, i345, i346, i347, i348, i349]))) ; w358 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u2 (\\[i350, i351] -> [i350 + i351]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i352, i353, i354, i355, i356] -> [ifF ((0 <=. i352 + i353 &&* 1 >. i352 + i353) &&* ((0 <=. i354 &&* 1 >. i354) &&* ((0 <=. i355 &&* 2 >. i355) &&* (0 <=. i356 &&* 2 >. i356)))) 0 1, i352, i353, i354, i355, i356]))))) ; w359 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,4,4,4] (w357 * w358))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w379 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i364, i365, i366, i367, i368, i369, i370, i371] -> [ifF (w359 ! [i364, i365, i366, i367, i368, i369, i370, let w360 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w360 ! [i364, i365, i366, i367, i368, i369, i370], let w361 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w361 ! [i364, i365, i366, i367, i368, i369, i370], let v362 = tconst (fromList [2] [0,1]) ; w363 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v362)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w363 ! [i364, i365, i366, i367, i368, i369, i370], i371] <=. tconst 0.0) 0 1]) ; w380 = tgather [1,1,2,2,1,1,2,4] w359 (\\[i372, i373, i374, i375, i376, i377, i378] -> [i372, i373, i374, i375, i376, i377, i378, let w360 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w360 ! [i372, i373, i374, i375, i376, i377, i378], let w361 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w361 ! [i372, i373, i374, i375, i376, i377, i378], let v362 = tconst (fromList [2] [0,1]) ; w363 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v362)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w363 ! [i372, i373, i374, i375, i376, i377, i378]]) ; w397 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w379 * w380) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [i381, i382, i383, i384, i385, i386, i387, 2 * i384 + i388]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i389, i390, i391, i392, i393, i394, i395, i396] -> [ifF ((0 <=. i389 + i393 &&* 1 >. i389 + i393) &&* ((0 <=. i390 + i394 &&* 1 >. i390 + i394) &&* ((0 <=. 2 * i391 + i395 &&* 4 >. 2 * i391 + i395) &&* (0 <=. 2 * i392 + i396 &&* 4 >. 2 * i392 + i396)))) 0 1, i389, i390, i391, i392, i393, i394, i395, i396]))))))) ; w421 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w397 (\\[i400, i401, i402, i403, i404, i405, i406] -> [i400, i401, i402, i403, i404, i405, let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i400, i401, i402, i403, i404, i405], i404, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i400, i401, i402, i403, i404, i405], i402 + i406, 0, 0, rem (quot (tmaxIndex (tgather [4] (w397 ! [i400, i401, i402, i403, i404, i405, let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i400, i401, i402, i403, i404, i405], i404, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i400, i401, i402, i403, i404, i405], i402 + i406, 0, 0]) (\\[i563] -> [rem (quot i563 2) 2, rem i563 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w397 ! [i400, i401, i402, i403, i404, i405, let w398 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w398 ! [i400, i401, i402, i403, i404, i405], i404, let w399 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w399 ! [i400, i401, i402, i403, i404, i405], i402 + i406, 0, 0]) (\\[i564] -> [rem (quot i564 2) 2, rem i564 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i407, i408, i409, i410, i411, i412, i413] -> [ifF ((0 <=. i407 + i410 &&* 1 >. i407 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i408 + i412 &&* 2 >. i408 + i412) &&* (0 <=. i409 + i413 &&* 2 >. i409 + i413)))) 0 1, i407, i408, i409, i410, i411, i412, i413]))) ; w422 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i414, i415] -> [i414 + i415]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i416, i417, i418, i419, i420] -> [ifF ((0 <=. i416 + i417 &&* 1 >. i416 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i419 &&* 2 >. i419) &&* (0 <=. i420 &&* 2 >. i420)))) 0 1, i416, i417, i418, i419, i420]))))) ; w423 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,2,2,4] (w421 * w422))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w443 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i428, i429, i430, i431, i432, i433, i434, i435] -> [ifF (w423 ! [i428, i429, i430, i431, i432, i433, i434, let w424 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w424 ! [i428, i429, i430, i431, i432, i433, i434], let w425 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w425 ! [i428, i429, i430, i431, i432, i433, i434], let v426 = tconst (fromList [1] [0]) ; w427 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v426)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w427 ! [i428, i429, i430, i431, i432, i433, i434], i435] <=. tconst 0.0) 0 1]) ; w444 = tgather [1,1,1,1,1,1,2,2] w423 (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, let w424 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w424 ! [i436, i437, i438, i439, i440, i441, i442], let w425 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w425 ! [i436, i437, i438, i439, i440, i441, i442], let v426 = tconst (fromList [1] [0]) ; w427 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v426)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w427 ! [i436, i437, i438, i439, i440, i441, i442]]) ; w461 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w443 * w444) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, 2 * i448 + i452]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [ifF ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459) &&* (0 <=. 2 * i456 + i460 &&* 2 >. 2 * i456 + i460)))) 0 1, i453, i454, i455, i456, i457, i458, i459, i460]) ; t466 = ttranspose [1,0] (treplicate 1 (ttranspose [1,0] (treshape [1,1] (tgather [1,1,1,1] w461 (\\[i462, i463, i464, i465] -> [i462, i463, i464, i465, 0, 0, rem (quot (tmaxIndex (tgather [4] (w461 ! [i462, i463, i464, i465, 0, 0]) (\\[i565] -> [rem (quot i565 2) 2, rem i565 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w461 ! [i462, i463, i464, i465, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2]))))) ; m467 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t466) + ttranspose [1,0] (treplicate 1 v7) ; m470 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i468, i469] -> [ifF (m467 ! [i468, i469] <=. tconst 0.0) 0 1]) ; t471 = ttranspose [1,0] (treplicate 10 (m470 * m467)) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * t471) + ttranspose [1,0] (treplicate 1 v9)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w357 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [treplicate 1 (treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 7.0))))))), treplicate 1 (treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i343, i344, i345, i346, i347, i348, i349] -> [ifF ((0 <=. i343 + i346 &&* 1 >. i343 + i346) &&* ((0 <=. i347 &&* 1 >. i347) &&* ((0 <=. i344 + i348 &&* 4 >. i344 + i348) &&* (0 <=. i345 + i349 &&* 4 >. i345 + i349)))) 0 1, i343, i344, i345, i346, i347, i348, i349]))) ; w359 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,4,4] (w357 ! [0, 0] * tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 u2), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i635, i636, i637, i638, i639, i640] -> [ifF ((0 <=. i637 &&* 1 >. i637) &&* ((0 <=. i638 &&* 1 >. i638) &&* ((0 <=. i639 &&* 2 >. i639) &&* (0 <=. i640 &&* 2 >. i640)))) 0 1, i635, i636, i637, i638, i639, i640])) (\\[i614, i615, i616, i617, i618] -> [rem (quot (i614 + 64 * i615 + 16 * i617 + 4 * i618 + 64 * i616) 16) 4, rem (quot (i614 + 64 * i615 + 16 * i617 + 4 * i618 + 64 * i616) 4) 4, 0, 0, rem (quot (i614 + 64 * i615 + 16 * i617 + 4 * i618 + 64 * i616) 2) 2, rem (i614 + 64 * i615 + 16 * i617 + 4 * i618 + 64 * i616) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w379 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i364, i365, i366, i367, i368, i369, i370, i371] -> [ifF (w359 ! [i364, i365, i366, i367, i368, i369, i370, tconst (fromList [1] [0]) ! [i364] + tconst (fromList [1] [0]) ! [i368], tconst (fromList [1] [0]) ! [i365] + tconst (fromList [1] [0]) ! [i369], 2 * tconst (fromList [2] [0,1]) ! [i366] + tconst (fromList [2] [0,1]) ! [i370], i371] <=. tconst 0.0) 0 1]) ; w397 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w379 * tgather [1,1,2,2,1,1,2,4] w359 (\\[i372, i373, i374, i375, i376, i377, i378] -> [i372, i373, i374, i375, i376, i377, i378, tconst (fromList [1] [0]) ! [i372] + tconst (fromList [1] [0]) ! [i376], tconst (fromList [1] [0]) ! [i373] + tconst (fromList [1] [0]) ! [i377], 2 * tconst (fromList [2] [0,1]) ! [i374] + tconst (fromList [2] [0,1]) ! [i378]])) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [i381, i382, i383, i384, i385, i386, i387, 2 * i384 + i388]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i389, i390, i391, i392, i393, i394, i395, i396] -> [ifF ((0 <=. i389 + i393 &&* 1 >. i389 + i393) &&* ((0 <=. i390 + i394 &&* 1 >. i390 + i394) &&* ((0 <=. 2 * i391 + i395 &&* 4 >. 2 * i391 + i395) &&* (0 <=. 2 * i392 + i396 &&* 4 >. 2 * i392 + i396)))) 0 1, i389, i390, i391, i392, i393, i394, i395, i396]))))))) ; w421 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w397 (\\[i400, i401, i402, i403, i404, i405, i406] -> [i400, i401, i402, i403, i404, i405, tconst (fromList [1] [0]) ! [i400] + tconst (fromList [1] [0]) ! [i403], i404, tconst (fromList [2] [0,1]) ! [i401] + tconst (fromList [2] [0,1]) ! [i405], i402 + i406, 0, 0, rem (quot (tmaxIndex (tgather [4] (w397 ! [i400, i401, i402, i403, i404, i405, tconst (fromList [1] [0]) ! [i400] + tconst (fromList [1] [0]) ! [i403], i404, tconst (fromList [2] [0,1]) ! [i401] + tconst (fromList [2] [0,1]) ! [i405], i402 + i406, 0, 0]) (\\[i563] -> [rem (quot i563 2) 2, rem i563 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w397 ! [i400, i401, i402, i403, i404, i405, tconst (fromList [1] [0]) ! [i400] + tconst (fromList [1] [0]) ! [i403], i404, tconst (fromList [2] [0,1]) ! [i401] + tconst (fromList [2] [0,1]) ! [i405], i402 + i406, 0, 0]) (\\[i564] -> [rem (quot i564 2) 2, rem i564 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i407, i408, i409, i410, i411, i412, i413] -> [ifF ((0 <=. i407 + i410 &&* 1 >. i407 + i410) &&* ((0 <=. i411 &&* 1 >. i411) &&* ((0 <=. i408 + i412 &&* 2 >. i408 + i412) &&* (0 <=. i409 + i413 &&* 2 >. i409 + i413)))) 0 1, i407, i408, i409, i410, i411, i412, i413]))) ; w422 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i414, i415] -> [i414 + i415]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i416, i417, i418, i419, i420] -> [ifF ((0 <=. i416 + i417 &&* 1 >. i416 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i419 &&* 2 >. i419) &&* (0 <=. i420 &&* 2 >. i420)))) 0 1, i416, i417, i418, i419, i420]))))) ; w423 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,2,2] (w421 ! [0, 0] * w422 ! [0, 0]) (\\[i604, i605, i606, i607, i608] -> [rem (quot (i604 + 16 * i605 + 8 * i607 + 4 * i608 + 16 * i606) 8) 2, rem (quot (i604 + 16 * i605 + 8 * i607 + 4 * i608 + 16 * i606) 4) 2, 0, 0, rem (quot (i604 + 16 * i605 + 8 * i607 + 4 * i608 + 16 * i606) 2) 2, rem (i604 + 16 * i605 + 8 * i607 + 4 * i608 + 16 * i606) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w443 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i428, i429, i430, i431, i432, i433, i434, i435] -> [ifF (w423 ! [i428, i429, i430, i431, i432, i433, i434, tconst (fromList [1] [0]) ! [i428] + tconst (fromList [1] [0]) ! [i432], tconst (fromList [1] [0]) ! [i429] + tconst (fromList [1] [0]) ! [i433], 2 * tconst (fromList [1] [0]) ! [i430] + tconst (fromList [2] [0,1]) ! [i434], i435] <=. tconst 0.0) 0 1]) ; w461 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w443 * tgather [1,1,1,1,1,1,2,2] w423 (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, tconst (fromList [1] [0]) ! [i436] + tconst (fromList [1] [0]) ! [i440], tconst (fromList [1] [0]) ! [i437] + tconst (fromList [1] [0]) ! [i441], 2 * tconst (fromList [1] [0]) ! [i438] + tconst (fromList [2] [0,1]) ! [i442]])) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, 2 * i448 + i452]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [ifF ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459) &&* (0 <=. 2 * i456 + i460 &&* 2 >. 2 * i456 + i460)))) 0 1, i453, i454, i455, i456, i457, i458, i459, i460]) ; t466 = ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (w461 ! [0, 0, 0, 0, 0, 0, rem (quot (tmaxIndex (tgather [4] (w461 ! [0, 0, 0, 0, 0, 0]) (\\[i565] -> [rem (quot i565 2) 2, rem i565 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w461 ! [0, 0, 0, 0, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2])))) ; m467 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t466) + ttranspose [1,0] (treplicate 1 v7) ; m470 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i468, i469] -> [ifF (m467 ! [i468, i469] <=. tconst 0.0) 0 1]) ; m472 = m470 * tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret)) ; u503 = tscatter [1,1,2,2] (w443 * tscatter [1,1,1,1,1,1,2,2] (tscatter [2,1,1,1,1,1,1,2,2] (tscatter [1,1,1,1,1,1,2,2] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tsum (tgather [1] (m6 * tgather [1,1] m472 (\\[i598, i599] -> [i598, 0])) (\\[i601] -> [i601, 0]))))))) (\\[i473, i474, i475, i476] -> [i473, i474, i475, i476, 0, 0, rem (quot (tmaxIndex (tgather [4] (w461 ! [i473, i474, i475, i476, 0, 0]) (\\[i477] -> [rem (quot i477 2) 2, rem i477 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w461 ! [i473, i474, i475, i476, 0, 0]) (\\[i478] -> [rem (quot i478 2) 2, rem i478 2]))) 2])) (\\[i479, i480, i481, i482, i483, i484, i485, i486] -> [ifF ((0 <=. i479 + i483 &&* 1 >. i479 + i483) &&* ((0 <=. i480 + i484 &&* 1 >. i480 + i484) &&* ((0 <=. 2 * i481 + i485 &&* 2 >. 2 * i481 + i485) &&* (0 <=. 2 * i482 + i486 &&* 2 >. 2 * i482 + i486)))) 0 1, i479, i480, i481, i482, i483, i484, i485, i486]) ! [0]) (\\[i488, i489, i490, i491, i492, i493, i494, i495] -> [i488, i489, i490, i491, i492, i493, i494, 2 * i491 + i495])) (\\[i496, i497, i498, i499, i500, i501, i502] -> [tconst (fromList [1] [0]) ! [i496] + tconst (fromList [1] [0]) ! [i500], tconst (fromList [1] [0]) ! [i497] + tconst (fromList [1] [0]) ! [i501], 2 * tconst (fromList [1] [0]) ! [i498] + tconst (fromList [2] [0,1]) ! [i502]]) ; w504 = tgather [1,1,2,2,1,1,2,2] (u503 ! [0, 0]) (\\[i580, i581, i582, i583, i584, i585, i586, i587] -> [rem (quot (i587 + 4 * i584 + 4 * i585 + 4 * i583 + 16 * i581 + 8 * i582 + 2 * i586 + 16 * i580) 8) 2, rem (quot (i587 + 4 * i584 + 4 * i585 + 4 * i583 + 16 * i581 + 8 * i582 + 2 * i586 + 16 * i580) 4) 2]) ; u554 = tscatter [1,1,4,4] (w379 * tscatter [1,1,2,2,1,1,2,4] (tscatter [2,1,1,2,2,1,1,2,2] (tscatter [1,1,2,2,1,1,2,2] (tscatter [2,1,2,2,1,1,2,2] (tsum (ttranspose [1,0] (w422 * w504))) (\\[i513, i514, i515, i516, i517, i518, i519] -> [ifF ((0 <=. i513 + i516 &&* 1 >. i513 + i516) &&* ((0 <=. i517 &&* 1 >. i517) &&* ((0 <=. i514 + i518 &&* 2 >. i514 + i518) &&* (0 <=. i515 + i519 &&* 2 >. i515 + i519)))) 0 1, i513, i514, i515, i516, i517, i518, i519]) ! [0]) (\\[i521, i522, i523, i524, i525, i526, i527] -> [tconst (fromList [1] [0]) ! [i521] + tconst (fromList [1] [0]) ! [i524], i525, tconst (fromList [2] [0,1]) ! [i522] + tconst (fromList [2] [0,1]) ! [i526], i523 + i527, 0, 0, rem (quot (tmaxIndex (tgather [4] (w397 ! [i521, i522, i523, i524, i525, i526, tconst (fromList [1] [0]) ! [i521] + tconst (fromList [1] [0]) ! [i524], i525, tconst (fromList [2] [0,1]) ! [i522] + tconst (fromList [2] [0,1]) ! [i526], i523 + i527, 0, 0]) (\\[i528] -> [rem (quot i528 2) 2, rem i528 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w397 ! [i521, i522, i523, i524, i525, i526, tconst (fromList [1] [0]) ! [i521] + tconst (fromList [1] [0]) ! [i524], i525, tconst (fromList [2] [0,1]) ! [i522] + tconst (fromList [2] [0,1]) ! [i526], i523 + i527, 0, 0]) (\\[i529] -> [rem (quot i529 2) 2, rem i529 2]))) 2])) (\\[i530, i531, i532, i533, i534, i535, i536, i537] -> [ifF ((0 <=. i530 + i534 &&* 1 >. i530 + i534) &&* ((0 <=. i531 + i535 &&* 1 >. i531 + i535) &&* ((0 <=. 2 * i532 + i536 &&* 4 >. 2 * i532 + i536) &&* (0 <=. 2 * i533 + i537 &&* 4 >. 2 * i533 + i537)))) 0 1, i530, i531, i532, i533, i534, i535, i536, i537]) ! [0]) (\\[i539, i540, i541, i542, i543, i544, i545, i546] -> [i539, i540, i541, i542, i543, i544, i545, 2 * i542 + i546])) (\\[i547, i548, i549, i550, i551, i552, i553] -> [tconst (fromList [1] [0]) ! [i547] + tconst (fromList [1] [0]) ! [i551], tconst (fromList [1] [0]) ! [i548] + tconst (fromList [1] [0]) ! [i552], 2 * tconst (fromList [2] [0,1]) ! [i549] + tconst (fromList [2] [0,1]) ! [i553]]) in (tscatter [1,1,2,2] (tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w357 * tgather [1,1,4,4,1,1,2,2] (u554 ! [0, 0]) (\\[i567, i568, i569, i570, i571, i572, i573, i574] -> [rem (quot (i574 + 4 * i571 + 4 * i572 + 4 * i570 + 64 * i568 + 16 * i569 + 2 * i573 + 64 * i567) 16) 4, rem (quot (i574 + 4 * i571 + 4 * i572 + 4 * i570 + 64 * i568 + 16 * i569 + 2 * i573 + 64 * i567) 4) 4])))))) (\\[i555, i556, i557, i558, i559] -> [ifF ((0 <=. i555 + i556 &&* 1 >. i555 + i556) &&* ((0 <=. i557 &&* 1 >. i557) &&* ((0 <=. i558 &&* 2 >. i558) &&* (0 <=. i559 &&* 2 >. i559)))) 0 1, i555, i556, i557, i558, i559]) ! [0]) (\\[i561, i562] -> [i561 + i562]), tsum (tsum (tsum (ttranspose [0,2,3,1] u554))), tscatter [1,1,2,2] (tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w421 * w504))))) (\\[i505, i506, i507, i508, i509] -> [ifF ((0 <=. i505 + i506 &&* 1 >. i505 + i506) &&* ((0 <=. i507 &&* 1 >. i507) &&* ((0 <=. i508 &&* 2 >. i508) &&* (0 <=. i509 &&* 2 >. i509)))) 0 1, i505, i506, i507, i508, i509]) ! [0]) (\\[i511, i512] -> [i511 + i512]), tsum (tsum (tsum (ttranspose [0,2,3,1] u503))), tsum (ttranspose [2,1,0] (t466 * treplicate 1 m472)), tsum (ttranspose [1,0] m472), tsum (ttranspose [2,0,1] (treplicate 10 (m470 * m467)) * ttranspose [2,1,0] (treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w359 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,4,4] (tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 7.0)))))), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i703, i704, i705, i706, i707, i708] -> [ifF ((0 <=. i705 &&* 1 >. i705) &&* ((0 <=. i706 &&* 1 >. i706) &&* ((0 <=. i703 + i707 &&* 4 >. i703 + i707) &&* (0 <=. i704 + i708 &&* 4 >. i704 + i708)))) 0 1, i703, i704, i705, i706, i707, i708]) * tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 u2), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i697, i698, i699, i700, i701, i702] -> [ifF ((0 <=. i699 &&* 1 >. i699) &&* ((0 <=. i700 &&* 1 >. i700) &&* ((0 <=. i701 &&* 2 >. i701) &&* (0 <=. i702 &&* 2 >. i702)))) 0 1, i697, i698, i699, i700, i701, i702])) (\\[i641, i642, i643, i644, i645] -> [rem (quot (i641 + 64 * i642 + 16 * i644 + 4 * i645 + 64 * i643) 16) 4, rem (quot (i641 + 64 * i642 + 16 * i644 + 4 * i645 + 64 * i643) 4) 4, 0, 0, rem (quot (i641 + 64 * i642 + 16 * i644 + 4 * i645 + 64 * i643) 2) 2, rem (i641 + 64 * i642 + 16 * i644 + 4 * i645 + 64 * i643) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w397 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i364, i365, i366, i367, i368, i369, i370, i371] -> [ifF (w359 ! [i364, i365, i366, i367, i368, i369, i370, tconst (fromList [1] [0]) ! [i364] + tconst (fromList [1] [0]) ! [i368], tconst (fromList [1] [0]) ! [i365] + tconst (fromList [1] [0]) ! [i369], 2 * tconst (fromList [2] [0,1]) ! [i366] + tconst (fromList [2] [0,1]) ! [i370], i371] <=. tconst 0.0) 0 1]) * tgather [1,1,2,2,1,1,2,4] w359 (\\[i372, i373, i374, i375, i376, i377, i378] -> [i372, i373, i374, i375, i376, i377, i378, tconst (fromList [1] [0]) ! [i372] + tconst (fromList [1] [0]) ! [i376], tconst (fromList [1] [0]) ! [i373] + tconst (fromList [1] [0]) ! [i377], 2 * tconst (fromList [2] [0,1]) ! [i374] + tconst (fromList [2] [0,1]) ! [i378]])) (\\[i381, i382, i383, i384, i385, i386, i387, i388] -> [i381, i382, i383, i384, i385, i386, i387, 2 * i384 + i388]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i389, i390, i391, i392, i393, i394, i395, i396] -> [ifF ((0 <=. i389 + i393 &&* 1 >. i389 + i393) &&* ((0 <=. i390 + i394 &&* 1 >. i390 + i394) &&* ((0 <=. 2 * i391 + i395 &&* 4 >. 2 * i391 + i395) &&* (0 <=. 2 * i392 + i396 &&* 4 >. 2 * i392 + i396)))) 0 1, i389, i390, i391, i392, i393, i394, i395, i396]))))))) ; w423 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,2,2] (tgather [2,2,1,1,2,2] (tfromList [tgather [2,2,1,1,2,2] (w397 ! [0]) (\\[i401, i402, i403, i404, i405, i406] -> [i401, i402, i403, i404, i405, tconst (fromList [1] [0]) ! [i403], i404, tconst (fromList [2] [0,1]) ! [i401] + tconst (fromList [2] [0,1]) ! [i405], i402 + i406, 0, 0, rem (quot (tmaxIndex (tgather [4] (w397 ! [0, i401, i402, i403, i404, i405, tconst (fromList [1] [0]) ! [i403], i404, tconst (fromList [2] [0,1]) ! [i401] + tconst (fromList [2] [0,1]) ! [i405], i402 + i406, 0, 0]) (\\[i563] -> [rem (quot i563 2) 2, rem i563 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w397 ! [0, i401, i402, i403, i404, i405, tconst (fromList [1] [0]) ! [i403], i404, tconst (fromList [2] [0,1]) ! [i401] + tconst (fromList [2] [0,1]) ! [i405], i402 + i406, 0, 0]) (\\[i564] -> [rem (quot i564 2) 2, rem i564 2]))) 2]), treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i680, i681, i682, i683, i684, i685] -> [ifF ((0 <=. i682 &&* 1 >. i682) &&* ((0 <=. i683 &&* 1 >. i683) &&* ((0 <=. i680 + i684 &&* 2 >. i680 + i684) &&* (0 <=. i681 + i685 &&* 2 >. i681 + i685)))) 0 1, i680, i681, i682, i683, i684, i685]) * tgather [2,2,1,1,2,2] (tfromList [treplicate 2 (treplicate 2 u4), treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i674, i675, i676, i677, i678, i679] -> [ifF ((0 <=. i676 &&* 1 >. i676) &&* ((0 <=. i677 &&* 1 >. i677) &&* ((0 <=. i678 &&* 2 >. i678) &&* (0 <=. i679 &&* 2 >. i679)))) 0 1, i674, i675, i676, i677, i678, i679])) (\\[i651, i652, i653, i654, i655] -> [rem (quot (i651 + 16 * i652 + 8 * i654 + 4 * i655 + 16 * i653) 8) 2, rem (quot (i651 + 16 * i652 + 8 * i654 + 4 * i655 + 16 * i653) 4) 2, 0, 0, rem (quot (i651 + 16 * i652 + 8 * i654 + 4 * i655 + 16 * i653) 2) 2, rem (i651 + 16 * i652 + 8 * i654 + 4 * i655 + 16 * i653) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w461 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i428, i429, i430, i431, i432, i433, i434, i435] -> [ifF (w423 ! [i428, i429, i430, i431, i432, i433, i434, tconst (fromList [1] [0]) ! [i428] + tconst (fromList [1] [0]) ! [i432], tconst (fromList [1] [0]) ! [i429] + tconst (fromList [1] [0]) ! [i433], 2 * tconst (fromList [1] [0]) ! [i430] + tconst (fromList [2] [0,1]) ! [i434], i435] <=. tconst 0.0) 0 1]) * tgather [1,1,1,1,1,1,2,2] w423 (\\[i436, i437, i438, i439, i440, i441, i442] -> [i436, i437, i438, i439, i440, i441, i442, tconst (fromList [1] [0]) ! [i436] + tconst (fromList [1] [0]) ! [i440], tconst (fromList [1] [0]) ! [i437] + tconst (fromList [1] [0]) ! [i441], 2 * tconst (fromList [1] [0]) ! [i438] + tconst (fromList [2] [0,1]) ! [i442]])) (\\[i445, i446, i447, i448, i449, i450, i451, i452] -> [i445, i446, i447, i448, i449, i450, i451, 2 * i448 + i452]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i453, i454, i455, i456, i457, i458, i459, i460] -> [ifF ((0 <=. i453 + i457 &&* 1 >. i453 + i457) &&* ((0 <=. i454 + i458 &&* 1 >. i454 + i458) &&* ((0 <=. 2 * i455 + i459 &&* 2 >. 2 * i455 + i459) &&* (0 <=. 2 * i456 + i460 &&* 2 >. 2 * i456 + i460)))) 0 1, i453, i454, i455, i456, i457, i458, i459, i460]) ; m467 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (w461 ! [0, 0, 0, 0, 0, 0, rem (quot (tmaxIndex (tgather [4] (w461 ! [0, 0, 0, 0, 0, 0]) (\\[i565] -> [rem (quot i565 2) 2, rem i565 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w461 ! [0, 0, 0, 0, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2]))))) + ttranspose [1,0] (treplicate 1 v7) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 10 (tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i468, i469] -> [ifF (m467 ! [i468, i469] <=. tconst 0.0) 0 1]) * m467))) + ttranspose [1,0] (treplicate 1 v9)"
