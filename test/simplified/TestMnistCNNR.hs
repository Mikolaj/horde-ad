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
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w364 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 7.0)) (\\[i296, i297] -> [i297])) (\\[i298, i299, i300] -> [i299, i300])) (\\[i301, i302, i303, i304] -> [i302, i303, i304])) (\\[i305, i306, i307, i308, i309] -> [i306, i307, i308, i309])) (\\[i310, i311, i312, i313, i314, i315] -> [i311, i312, i313, i314, i315])) (\\[i316, i317, i318, i319, i320, i321, i322] -> [i317, i318, i319, i320, i321, i322]), tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 0.0)) (\\[i323, i324] -> [i324])) (\\[i325, i326, i327] -> [i326, i327])) (\\[i328, i329, i330, i331] -> [i329, i330, i331])) (\\[i332, i333, i334, i335, i336] -> [i333, i334, i335, i336])) (\\[i337, i338, i339, i340, i341, i342] -> [i338, i339, i340, i341, i342])) (\\[i343, i344, i345, i346, i347, i348, i349] -> [i344, i345, i346, i347, i348, i349])]) (\\[i350, i351, i352, i353, i354, i355, i356] -> [ifF ((0 <=. i350 + i353 &&* 1 >. i350 + i353) &&* ((0 <=. i354 &&* 1 >. i354) &&* ((0 <=. i351 + i355 &&* 4 >. i351 + i355) &&* (0 <=. i352 + i356 &&* 4 >. i352 + i356)))) 0 1, i350, i351, i352, i353, i354, i355, i356]))) ; w365 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u2 (\\[i357, i358] -> [i357 + i358]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i359, i360, i361, i362, i363] -> [ifF ((0 <=. i359 + i360 &&* 1 >. i359 + i360) &&* ((0 <=. i361 &&* 1 >. i361) &&* ((0 <=. i362 &&* 2 >. i362) &&* (0 <=. i363 &&* 2 >. i363)))) 0 1, i359, i360, i361, i362, i363]))))) ; w366 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,4,4,4] (w364 * w365))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w386 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [ifF (w366 ! [i371, i372, i373, i374, i375, i376, i377, let w367 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w367 ! [i371, i372, i373, i374, i375, i376, i377], let w368 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w368 ! [i371, i372, i373, i374, i375, i376, i377], let v369 = tconst (fromList [2] [0,1]) ; w370 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v369)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w370 ! [i371, i372, i373, i374, i375, i376, i377], i378] <=. tconst 0.0) 0 1]) ; w387 = tgather [1,1,2,2,1,1,2,4] w366 (\\[i379, i380, i381, i382, i383, i384, i385] -> [i379, i380, i381, i382, i383, i384, i385, let w367 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w367 ! [i379, i380, i381, i382, i383, i384, i385], let w368 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w368 ! [i379, i380, i381, i382, i383, i384, i385], let v369 = tconst (fromList [2] [0,1]) ; w370 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v369)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w370 ! [i379, i380, i381, i382, i383, i384, i385]]) ; w404 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w386 * w387) (\\[i388, i389, i390, i391, i392, i393, i394, i395] -> [i388, i389, i390, i391, i392, i393, i394, 2 * i391 + i395]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i396, i397, i398, i399, i400, i401, i402, i403] -> [ifF ((0 <=. i396 + i400 &&* 1 >. i396 + i400) &&* ((0 <=. i397 + i401 &&* 1 >. i397 + i401) &&* ((0 <=. 2 * i398 + i402 &&* 4 >. 2 * i398 + i402) &&* (0 <=. 2 * i399 + i403 &&* 4 >. 2 * i399 + i403)))) 0 1, i396, i397, i398, i399, i400, i401, i402, i403]))))))) ; w428 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w404 (\\[i407, i408, i409, i410, i411, i412, i413] -> [i407, i408, i409, i410, i411, i412, let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i407, i408, i409, i410, i411, i412], i411, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i407, i408, i409, i410, i411, i412], i409 + i413, 0, 0, rem (quot (tmaxIndex (tgather [4] (w404 ! [i407, i408, i409, i410, i411, i412, let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i407, i408, i409, i410, i411, i412], i411, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i407, i408, i409, i410, i411, i412], i409 + i413, 0, 0]) (\\[i570] -> [rem (quot i570 2) 2, rem i570 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w404 ! [i407, i408, i409, i410, i411, i412, let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i407, i408, i409, i410, i411, i412], i411, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i407, i408, i409, i410, i411, i412], i409 + i413, 0, 0]) (\\[i571] -> [rem (quot i571 2) 2, rem i571 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i414, i415, i416, i417, i418, i419, i420] -> [ifF ((0 <=. i414 + i417 &&* 1 >. i414 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i415 + i419 &&* 2 >. i415 + i419) &&* (0 <=. i416 + i420 &&* 2 >. i416 + i420)))) 0 1, i414, i415, i416, i417, i418, i419, i420]))) ; w429 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i421, i422] -> [i421 + i422]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i423, i424, i425, i426, i427] -> [ifF ((0 <=. i423 + i424 &&* 1 >. i423 + i424) &&* ((0 <=. i425 &&* 1 >. i425) &&* ((0 <=. i426 &&* 2 >. i426) &&* (0 <=. i427 &&* 2 >. i427)))) 0 1, i423, i424, i425, i426, i427]))))) ; w430 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,2,2,4] (w428 * w429))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w450 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i435, i436, i437, i438, i439, i440, i441, i442] -> [ifF (w430 ! [i435, i436, i437, i438, i439, i440, i441, let w431 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w431 ! [i435, i436, i437, i438, i439, i440, i441], let w432 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w432 ! [i435, i436, i437, i438, i439, i440, i441], let v433 = tconst (fromList [1] [0]) ; w434 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v433)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w434 ! [i435, i436, i437, i438, i439, i440, i441], i442] <=. tconst 0.0) 0 1]) ; w451 = tgather [1,1,1,1,1,1,2,2] w430 (\\[i443, i444, i445, i446, i447, i448, i449] -> [i443, i444, i445, i446, i447, i448, i449, let w431 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w431 ! [i443, i444, i445, i446, i447, i448, i449], let w432 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w432 ! [i443, i444, i445, i446, i447, i448, i449], let v433 = tconst (fromList [1] [0]) ; w434 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v433)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w434 ! [i443, i444, i445, i446, i447, i448, i449]]) ; w468 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w450 * w451) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [i452, i453, i454, i455, i456, i457, i458, 2 * i455 + i459]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i460, i461, i462, i463, i464, i465, i466, i467] -> [ifF ((0 <=. i460 + i464 &&* 1 >. i460 + i464) &&* ((0 <=. i461 + i465 &&* 1 >. i461 + i465) &&* ((0 <=. 2 * i462 + i466 &&* 2 >. 2 * i462 + i466) &&* (0 <=. 2 * i463 + i467 &&* 2 >. 2 * i463 + i467)))) 0 1, i460, i461, i462, i463, i464, i465, i466, i467]) ; t473 = ttranspose [1,0] (treplicate 1 (ttranspose [1,0] (treshape [1,1] (tgather [1,1,1,1] w468 (\\[i469, i470, i471, i472] -> [i469, i470, i471, i472, 0, 0, rem (quot (tmaxIndex (tgather [4] (w468 ! [i469, i470, i471, i472, 0, 0]) (\\[i572] -> [rem (quot i572 2) 2, rem i572 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w468 ! [i469, i470, i471, i472, 0, 0]) (\\[i573] -> [rem (quot i573 2) 2, rem i573 2]))) 2]))))) ; m474 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t473) + ttranspose [1,0] (treplicate 1 v7) ; m477 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i475, i476] -> [ifF (m474 ! [i475, i476] <=. tconst 0.0) 0 1]) ; t478 = ttranspose [1,0] (treplicate 10 (m477 * m474)) ; m479 = m477 * tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret)) ; w494 = tscatter [2,1,1,1,1,1,1,2,2] (tscatter [1,1,1,1,1,1,2,2] (treshape [1,1,1,1] (tsum (ttranspose [1,0] (treplicate 1 m6) * ttranspose [1,2,0] (treplicate 1 m479)))) (\\[i480, i481, i482, i483] -> [i480, i481, i482, i483, 0, 0, rem (quot (tmaxIndex (tgather [4] (w468 ! [i480, i481, i482, i483, 0, 0]) (\\[i484] -> [rem (quot i484 2) 2, rem i484 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w468 ! [i480, i481, i482, i483, 0, 0]) (\\[i485] -> [rem (quot i485 2) 2, rem i485 2]))) 2])) (\\[i486, i487, i488, i489, i490, i491, i492, i493] -> [ifF ((0 <=. i486 + i490 &&* 1 >. i486 + i490) &&* ((0 <=. i487 + i491 &&* 1 >. i487 + i491) &&* ((0 <=. 2 * i488 + i492 &&* 2 >. 2 * i488 + i492) &&* (0 <=. 2 * i489 + i493 &&* 2 >. 2 * i489 + i493)))) 0 1, i486, i487, i488, i489, i490, i491, i492, i493]) ; u510 = tscatter [1,1,2,2] (w450 * tscatter [1,1,1,1,1,1,2,2] (w494 ! [0]) (\\[i495, i496, i497, i498, i499, i500, i501, i502] -> [i495, i496, i497, i498, i499, i500, i501, 2 * i498 + i502])) (\\[i503, i504, i505, i506, i507, i508, i509] -> [let w431 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w431 ! [i503, i504, i505, i506, i507, i508, i509], let w432 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w432 ! [i503, i504, i505, i506, i507, i508, i509], let v433 = tconst (fromList [1] [0]) ; w434 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v433)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w434 ! [i503, i504, i505, i506, i507, i508, i509]]) ; w511 = treshape [1,1,2,2,1,1,2,2] (ttranspose [1,2,3,4,0] (treplicate 4 u510)) ; w517 = tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w428 * w511))))) (\\[i512, i513, i514, i515, i516] -> [ifF ((0 <=. i512 + i513 &&* 1 >. i512 + i513) &&* ((0 <=. i514 &&* 1 >. i514) &&* ((0 <=. i515 &&* 2 >. i515) &&* (0 <=. i516 &&* 2 >. i516)))) 0 1, i512, i513, i514, i515, i516]) ; w527 = tscatter [2,1,2,2,1,1,2,2] (tsum (ttranspose [1,0] (w429 * w511))) (\\[i520, i521, i522, i523, i524, i525, i526] -> [ifF ((0 <=. i520 + i523 &&* 1 >. i520 + i523) &&* ((0 <=. i524 &&* 1 >. i524) &&* ((0 <=. i521 + i525 &&* 2 >. i521 + i525) &&* (0 <=. i522 + i526 &&* 2 >. i522 + i526)))) 0 1, i520, i521, i522, i523, i524, i525, i526]) ; w545 = tscatter [2,1,1,2,2,1,1,2,2] (tscatter [1,1,2,2,1,1,2,2] (w527 ! [0]) (\\[i528, i529, i530, i531, i532, i533, i534] -> [let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i528, i529, i530, i531, i532, i533], i532, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i528, i529, i530, i531, i532, i533], i530 + i534, 0, 0, rem (quot (tmaxIndex (tgather [4] (w404 ! [i528, i529, i530, i531, i532, i533, let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i528, i529, i530, i531, i532, i533], i532, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i528, i529, i530, i531, i532, i533], i530 + i534, 0, 0]) (\\[i535] -> [rem (quot i535 2) 2, rem i535 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w404 ! [i528, i529, i530, i531, i532, i533, let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i528, i529, i530, i531, i532, i533], i532, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i528, i529, i530, i531, i532, i533], i530 + i534, 0, 0]) (\\[i536] -> [rem (quot i536 2) 2, rem i536 2]))) 2])) (\\[i537, i538, i539, i540, i541, i542, i543, i544] -> [ifF ((0 <=. i537 + i541 &&* 1 >. i537 + i541) &&* ((0 <=. i538 + i542 &&* 1 >. i538 + i542) &&* ((0 <=. 2 * i539 + i543 &&* 4 >. 2 * i539 + i543) &&* (0 <=. 2 * i540 + i544 &&* 4 >. 2 * i540 + i544)))) 0 1, i537, i538, i539, i540, i541, i542, i543, i544]) ; u561 = tscatter [1,1,4,4] (w386 * tscatter [1,1,2,2,1,1,2,4] (w545 ! [0]) (\\[i546, i547, i548, i549, i550, i551, i552, i553] -> [i546, i547, i548, i549, i550, i551, i552, 2 * i549 + i553])) (\\[i554, i555, i556, i557, i558, i559, i560] -> [let w367 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w367 ! [i554, i555, i556, i557, i558, i559, i560], let w368 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w368 ! [i554, i555, i556, i557, i558, i559, i560], let v369 = tconst (fromList [2] [0,1]) ; w370 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v369)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w370 ! [i554, i555, i556, i557, i558, i559, i560]]) ; w567 = tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w364 * treshape [1,1,4,4,1,1,2,2] (ttranspose [1,2,3,4,0] (treplicate 4 u561))))))) (\\[i562, i563, i564, i565, i566] -> [ifF ((0 <=. i562 + i563 &&* 1 >. i562 + i563) &&* ((0 <=. i564 &&* 1 >. i564) &&* ((0 <=. i565 &&* 2 >. i565) &&* (0 <=. i566 &&* 2 >. i566)))) 0 1, i562, i563, i564, i565, i566]) in (tscatter [1,1,2,2] (w567 ! [0]) (\\[i568, i569] -> [i568 + i569]), tsum (tsum (tsum (ttranspose [0,2,3,1] u561))), tscatter [1,1,2,2] (w517 ! [0]) (\\[i518, i519] -> [i518 + i519]), tsum (tsum (tsum (ttranspose [0,2,3,1] u510))), tsum (ttranspose [2,1,0] (t473 * treplicate 1 m479)), tsum (ttranspose [1,0] m479), tsum (ttranspose [2,1,0] (t478 * treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w364 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 7.0)) (\\[i296, i297] -> [i297])) (\\[i298, i299, i300] -> [i299, i300])) (\\[i301, i302, i303, i304] -> [i302, i303, i304])) (\\[i305, i306, i307, i308, i309] -> [i306, i307, i308, i309])) (\\[i310, i311, i312, i313, i314, i315] -> [i311, i312, i313, i314, i315])) (\\[i316, i317, i318, i319, i320, i321, i322] -> [i317, i318, i319, i320, i321, i322]), tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 0.0)) (\\[i323, i324] -> [i324])) (\\[i325, i326, i327] -> [i326, i327])) (\\[i328, i329, i330, i331] -> [i329, i330, i331])) (\\[i332, i333, i334, i335, i336] -> [i333, i334, i335, i336])) (\\[i337, i338, i339, i340, i341, i342] -> [i338, i339, i340, i341, i342])) (\\[i343, i344, i345, i346, i347, i348, i349] -> [i344, i345, i346, i347, i348, i349])]) (\\[i350, i351, i352, i353, i354, i355, i356] -> [ifF ((0 <=. i350 + i353 &&* 1 >. i350 + i353) &&* ((0 <=. i354 &&* 1 >. i354) &&* ((0 <=. i351 + i355 &&* 4 >. i351 + i355) &&* (0 <=. i352 + i356 &&* 4 >. i352 + i356)))) 0 1, i350, i351, i352, i353, i354, i355, i356]))) ; w365 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u2 (\\[i357, i358] -> [i357 + i358]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i359, i360, i361, i362, i363] -> [ifF ((0 <=. i359 + i360 &&* 1 >. i359 + i360) &&* ((0 <=. i361 &&* 1 >. i361) &&* ((0 <=. i362 &&* 2 >. i362) &&* (0 <=. i363 &&* 2 >. i363)))) 0 1, i359, i360, i361, i362, i363]))))) ; w366 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,4,4,4] (w364 * w365))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w386 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [ifF (w366 ! [i371, i372, i373, i374, i375, i376, i377, let w367 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w367 ! [i371, i372, i373, i374, i375, i376, i377], let w368 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w368 ! [i371, i372, i373, i374, i375, i376, i377], let v369 = tconst (fromList [2] [0,1]) ; w370 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v369)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w370 ! [i371, i372, i373, i374, i375, i376, i377], i378] <=. tconst 0.0) 0 1]) ; w387 = tgather [1,1,2,2,1,1,2,4] w366 (\\[i379, i380, i381, i382, i383, i384, i385] -> [i379, i380, i381, i382, i383, i384, i385, let w367 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w367 ! [i379, i380, i381, i382, i383, i384, i385], let w368 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w368 ! [i379, i380, i381, i382, i383, i384, i385], let v369 = tconst (fromList [2] [0,1]) ; w370 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 2 (tconst 2) * v369)) + treplicate 2 (tconst (fromList [2] [0,1])))))))) in w370 ! [i379, i380, i381, i382, i383, i384, i385]]) ; w404 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w386 * w387) (\\[i388, i389, i390, i391, i392, i393, i394, i395] -> [i388, i389, i390, i391, i392, i393, i394, 2 * i391 + i395]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i396, i397, i398, i399, i400, i401, i402, i403] -> [ifF ((0 <=. i396 + i400 &&* 1 >. i396 + i400) &&* ((0 <=. i397 + i401 &&* 1 >. i397 + i401) &&* ((0 <=. 2 * i398 + i402 &&* 4 >. 2 * i398 + i402) &&* (0 <=. 2 * i399 + i403 &&* 4 >. 2 * i399 + i403)))) 0 1, i396, i397, i398, i399, i400, i401, i402, i403]))))))) ; w428 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w404 (\\[i407, i408, i409, i410, i411, i412, i413] -> [i407, i408, i409, i410, i411, i412, let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i407, i408, i409, i410, i411, i412], i411, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i407, i408, i409, i410, i411, i412], i409 + i413, 0, 0, rem (quot (tmaxIndex (tgather [4] (w404 ! [i407, i408, i409, i410, i411, i412, let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i407, i408, i409, i410, i411, i412], i411, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i407, i408, i409, i410, i411, i412], i409 + i413, 0, 0]) (\\[i570] -> [rem (quot i570 2) 2, rem i570 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w404 ! [i407, i408, i409, i410, i411, i412, let w405 = ttranspose [4,0,1,5,2,3] (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0]))))))) in w405 ! [i407, i408, i409, i410, i411, i412], i411, let w406 = ttranspose [0,4,1,2,3] (treplicate 1 (treplicate 2 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (tconst (fromList [2] [0,1]))) + treplicate 2 (tconst (fromList [2] [0,1]))))))) in w406 ! [i407, i408, i409, i410, i411, i412], i409 + i413, 0, 0]) (\\[i571] -> [rem (quot i571 2) 2, rem i571 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i414, i415, i416, i417, i418, i419, i420] -> [ifF ((0 <=. i414 + i417 &&* 1 >. i414 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i415 + i419 &&* 2 >. i415 + i419) &&* (0 <=. i416 + i420 &&* 2 >. i416 + i420)))) 0 1, i414, i415, i416, i417, i418, i419, i420]))) ; w429 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i421, i422] -> [i421 + i422]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i423, i424, i425, i426, i427] -> [ifF ((0 <=. i423 + i424 &&* 1 >. i423 + i424) &&* ((0 <=. i425 &&* 1 >. i425) &&* ((0 <=. i426 &&* 2 >. i426) &&* (0 <=. i427 &&* 2 >. i427)))) 0 1, i423, i424, i425, i426, i427]))))) ; w430 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,2,2,4] (w428 * w429))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w450 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i435, i436, i437, i438, i439, i440, i441, i442] -> [ifF (w430 ! [i435, i436, i437, i438, i439, i440, i441, let w431 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w431 ! [i435, i436, i437, i438, i439, i440, i441], let w432 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w432 ! [i435, i436, i437, i438, i439, i440, i441], let v433 = tconst (fromList [1] [0]) ; w434 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v433)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w434 ! [i435, i436, i437, i438, i439, i440, i441], i442] <=. tconst 0.0) 0 1]) ; w451 = tgather [1,1,1,1,1,1,2,2] w430 (\\[i443, i444, i445, i446, i447, i448, i449] -> [i443, i444, i445, i446, i447, i448, i449, let w431 = ttranspose [5,0,1,2,6,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w431 ! [i443, i444, i445, i446, i447, i448, i449], let w432 = ttranspose [0,5,1,2,3,6,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (ttranspose [1,0] (treplicate 1 (tconst (fromList [1] [0]))) + treplicate 1 (tconst (fromList [1] [0])))))))) in w432 ! [i443, i444, i445, i446, i447, i448, i449], let v433 = tconst (fromList [1] [0]) ; w434 = ttranspose [0,1,5,2,3,4] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (ttranspose [1,0] (treplicate 2 (treplicate 1 (tconst 2) * v433)) + treplicate 1 (tconst (fromList [2] [0,1])))))))) in w434 ! [i443, i444, i445, i446, i447, i448, i449]]) ; w468 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w450 * w451) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [i452, i453, i454, i455, i456, i457, i458, 2 * i455 + i459]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i460, i461, i462, i463, i464, i465, i466, i467] -> [ifF ((0 <=. i460 + i464 &&* 1 >. i460 + i464) &&* ((0 <=. i461 + i465 &&* 1 >. i461 + i465) &&* ((0 <=. 2 * i462 + i466 &&* 2 >. 2 * i462 + i466) &&* (0 <=. 2 * i463 + i467 &&* 2 >. 2 * i463 + i467)))) 0 1, i460, i461, i462, i463, i464, i465, i466, i467]) ; t473 = ttranspose [1,0] (treplicate 1 (ttranspose [1,0] (treshape [1,1] (tgather [1,1,1,1] w468 (\\[i469, i470, i471, i472] -> [i469, i470, i471, i472, 0, 0, rem (quot (tmaxIndex (tgather [4] (w468 ! [i469, i470, i471, i472, 0, 0]) (\\[i572] -> [rem (quot i572 2) 2, rem i572 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w468 ! [i469, i470, i471, i472, 0, 0]) (\\[i573] -> [rem (quot i573 2) 2, rem i573 2]))) 2]))))) ; m474 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t473) + ttranspose [1,0] (treplicate 1 v7) ; m477 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i475, i476] -> [ifF (m474 ! [i475, i476] <=. tconst 0.0) 0 1]) ; t478 = ttranspose [1,0] (treplicate 10 (m477 * m474)) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * t478) + ttranspose [1,0] (treplicate 1 v9)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w364 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [treplicate 1 (treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 7.0))))))), treplicate 1 (treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i350, i351, i352, i353, i354, i355, i356] -> [ifF ((0 <=. i350 + i353 &&* 1 >. i350 + i353) &&* ((0 <=. i354 &&* 1 >. i354) &&* ((0 <=. i351 + i355 &&* 4 >. i351 + i355) &&* (0 <=. i352 + i356 &&* 4 >. i352 + i356)))) 0 1, i350, i351, i352, i353, i354, i355, i356]))) ; w366 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,4,4] (w364 ! [0, 0] * tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 (tgather [1,1,2,2] u2 (\\[i358] -> [0 + i358]))), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i642, i643, i644, i645, i646, i647] -> [ifF ((0 <=. 0 + i644 &&* 1 >. 0 + i644) &&* ((0 <=. i645 &&* 1 >. i645) &&* ((0 <=. i646 &&* 2 >. i646) &&* (0 <=. i647 &&* 2 >. i647)))) 0 1, i642, i643, i644, i645, i646, i647])) (\\[i621, i622, i623, i624, i625] -> [rem (quot (i621 + 64 * i622 + 16 * i624 + 4 * i625 + 64 * i623) 16) 4, rem (quot (i621 + 64 * i622 + 16 * i624 + 4 * i625 + 64 * i623) 4) 4, 0, 0, rem (quot (i621 + 64 * i622 + 16 * i624 + 4 * i625 + 64 * i623) 2) 2, rem (i621 + 64 * i622 + 16 * i624 + 4 * i625 + 64 * i623) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w386 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [ifF (w366 ! [i371, i372, i373, i374, i375, i376, i377, tconst (fromList [1] [0]) ! [i371] + tconst (fromList [1] [0]) ! [i375], tconst (fromList [1] [0]) ! [i372] + tconst (fromList [1] [0]) ! [i376], 2 * tconst (fromList [2] [0,1]) ! [i373] + tconst (fromList [2] [0,1]) ! [i377], i378] <=. tconst 0.0) 0 1]) ; w404 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w386 * tgather [1,1,2,2,1,1,2,4] w366 (\\[i379, i380, i381, i382, i383, i384, i385] -> [i379, i380, i381, i382, i383, i384, i385, tconst (fromList [1] [0]) ! [i379] + tconst (fromList [1] [0]) ! [i383], tconst (fromList [1] [0]) ! [i380] + tconst (fromList [1] [0]) ! [i384], 2 * tconst (fromList [2] [0,1]) ! [i381] + tconst (fromList [2] [0,1]) ! [i385]])) (\\[i388, i389, i390, i391, i392, i393, i394, i395] -> [i388, i389, i390, i391, i392, i393, i394, 2 * i391 + i395]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i396, i397, i398, i399, i400, i401, i402, i403] -> [ifF ((0 <=. i396 + i400 &&* 1 >. i396 + i400) &&* ((0 <=. i397 + i401 &&* 1 >. i397 + i401) &&* ((0 <=. 2 * i398 + i402 &&* 4 >. 2 * i398 + i402) &&* (0 <=. 2 * i399 + i403 &&* 4 >. 2 * i399 + i403)))) 0 1, i396, i397, i398, i399, i400, i401, i402, i403]))))))) ; w428 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w404 (\\[i407, i408, i409, i410, i411, i412, i413] -> [i407, i408, i409, i410, i411, i412, tconst (fromList [1] [0]) ! [i407] + tconst (fromList [1] [0]) ! [i410], i411, tconst (fromList [2] [0,1]) ! [i408] + tconst (fromList [2] [0,1]) ! [i412], i409 + i413, 0, 0, rem (quot (tmaxIndex (tgather [4] (w404 ! [i407, i408, i409, i410, i411, i412, tconst (fromList [1] [0]) ! [i407] + tconst (fromList [1] [0]) ! [i410], i411, tconst (fromList [2] [0,1]) ! [i408] + tconst (fromList [2] [0,1]) ! [i412], i409 + i413, 0, 0]) (\\[i570] -> [rem (quot i570 2) 2, rem i570 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w404 ! [i407, i408, i409, i410, i411, i412, tconst (fromList [1] [0]) ! [i407] + tconst (fromList [1] [0]) ! [i410], i411, tconst (fromList [2] [0,1]) ! [i408] + tconst (fromList [2] [0,1]) ! [i412], i409 + i413, 0, 0]) (\\[i571] -> [rem (quot i571 2) 2, rem i571 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i414, i415, i416, i417, i418, i419, i420] -> [ifF ((0 <=. i414 + i417 &&* 1 >. i414 + i417) &&* ((0 <=. i418 &&* 1 >. i418) &&* ((0 <=. i415 + i419 &&* 2 >. i415 + i419) &&* (0 <=. i416 + i420 &&* 2 >. i416 + i420)))) 0 1, i414, i415, i416, i417, i418, i419, i420]))) ; w429 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i421, i422] -> [i421 + i422]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i423, i424, i425, i426, i427] -> [ifF ((0 <=. i423 + i424 &&* 1 >. i423 + i424) &&* ((0 <=. i425 &&* 1 >. i425) &&* ((0 <=. i426 &&* 2 >. i426) &&* (0 <=. i427 &&* 2 >. i427)))) 0 1, i423, i424, i425, i426, i427]))))) ; w430 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,2,2] (w428 ! [0, 0] * w429 ! [0, 0]) (\\[i611, i612, i613, i614, i615] -> [rem (quot (i611 + 16 * i612 + 8 * i614 + 4 * i615 + 16 * i613) 8) 2, rem (quot (i611 + 16 * i612 + 8 * i614 + 4 * i615 + 16 * i613) 4) 2, 0, 0, rem (quot (i611 + 16 * i612 + 8 * i614 + 4 * i615 + 16 * i613) 2) 2, rem (i611 + 16 * i612 + 8 * i614 + 4 * i615 + 16 * i613) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w450 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i435, i436, i437, i438, i439, i440, i441, i442] -> [ifF (w430 ! [i435, i436, i437, i438, i439, i440, i441, tconst (fromList [1] [0]) ! [i435] + tconst (fromList [1] [0]) ! [i439], tconst (fromList [1] [0]) ! [i436] + tconst (fromList [1] [0]) ! [i440], 2 * tconst (fromList [1] [0]) ! [i437] + tconst (fromList [2] [0,1]) ! [i441], i442] <=. tconst 0.0) 0 1]) ; w468 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w450 * tgather [1,1,1,1,1,1,2,2] w430 (\\[i443, i444, i445, i446, i447, i448, i449] -> [i443, i444, i445, i446, i447, i448, i449, tconst (fromList [1] [0]) ! [i443] + tconst (fromList [1] [0]) ! [i447], tconst (fromList [1] [0]) ! [i444] + tconst (fromList [1] [0]) ! [i448], 2 * tconst (fromList [1] [0]) ! [i445] + tconst (fromList [2] [0,1]) ! [i449]])) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [i452, i453, i454, i455, i456, i457, i458, 2 * i455 + i459]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i460, i461, i462, i463, i464, i465, i466, i467] -> [ifF ((0 <=. i460 + i464 &&* 1 >. i460 + i464) &&* ((0 <=. i461 + i465 &&* 1 >. i461 + i465) &&* ((0 <=. 2 * i462 + i466 &&* 2 >. 2 * i462 + i466) &&* (0 <=. 2 * i463 + i467 &&* 2 >. 2 * i463 + i467)))) 0 1, i460, i461, i462, i463, i464, i465, i466, i467]) ; t473 = ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (w468 ! [0, 0, 0, 0, 0, 0, rem (quot (tmaxIndex (tgather [4] (w468 ! [0, 0, 0, 0, 0, 0]) (\\[i572] -> [rem (quot i572 2) 2, rem i572 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w468 ! [0, 0, 0, 0, 0, 0]) (\\[i573] -> [rem (quot i573 2) 2, rem i573 2]))) 2])))) ; m474 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t473) + ttranspose [1,0] (treplicate 1 v7) ; m477 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i475, i476] -> [ifF (m474 ! [i475, i476] <=. tconst 0.0) 0 1]) ; m479 = m477 * tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret)) ; u510 = tscatter [1,1,2,2] (w450 * tscatter [1,1,1,1,1,1,2,2] (tscatter [2,1,1,1,1,1,1,2,2] (tscatter [1,1,1,1,1,1,2,2] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tsum (tgather [1] (m6 * tgather [1,1] m479 (\\[i605, i606] -> [i605, 0])) (\\[i608] -> [i608, 0]))))))) (\\[i480, i481, i482, i483] -> [i480, i481, i482, i483, 0, 0, rem (quot (tmaxIndex (tgather [4] (w468 ! [i480, i481, i482, i483, 0, 0]) (\\[i484] -> [rem (quot i484 2) 2, rem i484 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w468 ! [i480, i481, i482, i483, 0, 0]) (\\[i485] -> [rem (quot i485 2) 2, rem i485 2]))) 2])) (\\[i486, i487, i488, i489, i490, i491, i492, i493] -> [ifF ((0 <=. i486 + i490 &&* 1 >. i486 + i490) &&* ((0 <=. i487 + i491 &&* 1 >. i487 + i491) &&* ((0 <=. 2 * i488 + i492 &&* 2 >. 2 * i488 + i492) &&* (0 <=. 2 * i489 + i493 &&* 2 >. 2 * i489 + i493)))) 0 1, i486, i487, i488, i489, i490, i491, i492, i493]) ! [0]) (\\[i495, i496, i497, i498, i499, i500, i501, i502] -> [i495, i496, i497, i498, i499, i500, i501, 2 * i498 + i502])) (\\[i503, i504, i505, i506, i507, i508, i509] -> [tconst (fromList [1] [0]) ! [i503] + tconst (fromList [1] [0]) ! [i507], tconst (fromList [1] [0]) ! [i504] + tconst (fromList [1] [0]) ! [i508], 2 * tconst (fromList [1] [0]) ! [i505] + tconst (fromList [2] [0,1]) ! [i509]]) ; w511 = tgather [1,1,2,2,1,1,2,2] (u510 ! [0, 0]) (\\[i587, i588, i589, i590, i591, i592, i593, i594] -> [rem (quot (i594 + 4 * i591 + 4 * i592 + 4 * i590 + 16 * i588 + 8 * i589 + 2 * i593 + 16 * i587) 8) 2, rem (quot (i594 + 4 * i591 + 4 * i592 + 4 * i590 + 16 * i588 + 8 * i589 + 2 * i593 + 16 * i587) 4) 2]) ; u561 = tscatter [1,1,4,4] (w386 * tscatter [1,1,2,2,1,1,2,4] (tscatter [2,1,1,2,2,1,1,2,2] (tscatter [1,1,2,2,1,1,2,2] (tscatter [2,1,2,2,1,1,2,2] (tsum (ttranspose [1,0] (w429 * w511))) (\\[i520, i521, i522, i523, i524, i525, i526] -> [ifF ((0 <=. i520 + i523 &&* 1 >. i520 + i523) &&* ((0 <=. i524 &&* 1 >. i524) &&* ((0 <=. i521 + i525 &&* 2 >. i521 + i525) &&* (0 <=. i522 + i526 &&* 2 >. i522 + i526)))) 0 1, i520, i521, i522, i523, i524, i525, i526]) ! [0]) (\\[i528, i529, i530, i531, i532, i533, i534] -> [tconst (fromList [1] [0]) ! [i528] + tconst (fromList [1] [0]) ! [i531], i532, tconst (fromList [2] [0,1]) ! [i529] + tconst (fromList [2] [0,1]) ! [i533], i530 + i534, 0, 0, rem (quot (tmaxIndex (tgather [4] (w404 ! [i528, i529, i530, i531, i532, i533, tconst (fromList [1] [0]) ! [i528] + tconst (fromList [1] [0]) ! [i531], i532, tconst (fromList [2] [0,1]) ! [i529] + tconst (fromList [2] [0,1]) ! [i533], i530 + i534, 0, 0]) (\\[i535] -> [rem (quot i535 2) 2, rem i535 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w404 ! [i528, i529, i530, i531, i532, i533, tconst (fromList [1] [0]) ! [i528] + tconst (fromList [1] [0]) ! [i531], i532, tconst (fromList [2] [0,1]) ! [i529] + tconst (fromList [2] [0,1]) ! [i533], i530 + i534, 0, 0]) (\\[i536] -> [rem (quot i536 2) 2, rem i536 2]))) 2])) (\\[i537, i538, i539, i540, i541, i542, i543, i544] -> [ifF ((0 <=. i537 + i541 &&* 1 >. i537 + i541) &&* ((0 <=. i538 + i542 &&* 1 >. i538 + i542) &&* ((0 <=. 2 * i539 + i543 &&* 4 >. 2 * i539 + i543) &&* (0 <=. 2 * i540 + i544 &&* 4 >. 2 * i540 + i544)))) 0 1, i537, i538, i539, i540, i541, i542, i543, i544]) ! [0]) (\\[i546, i547, i548, i549, i550, i551, i552, i553] -> [i546, i547, i548, i549, i550, i551, i552, 2 * i549 + i553])) (\\[i554, i555, i556, i557, i558, i559, i560] -> [tconst (fromList [1] [0]) ! [i554] + tconst (fromList [1] [0]) ! [i558], tconst (fromList [1] [0]) ! [i555] + tconst (fromList [1] [0]) ! [i559], 2 * tconst (fromList [2] [0,1]) ! [i556] + tconst (fromList [2] [0,1]) ! [i560]]) in (tscatter [1,1,2,2] (tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w364 * tgather [1,1,4,4,1,1,2,2] (u561 ! [0, 0]) (\\[i574, i575, i576, i577, i578, i579, i580, i581] -> [rem (quot (i581 + 4 * i578 + 4 * i579 + 4 * i577 + 64 * i575 + 16 * i576 + 2 * i580 + 64 * i574) 16) 4, rem (quot (i581 + 4 * i578 + 4 * i579 + 4 * i577 + 64 * i575 + 16 * i576 + 2 * i580 + 64 * i574) 4) 4])))))) (\\[i562, i563, i564, i565, i566] -> [ifF ((0 <=. i562 + i563 &&* 1 >. i562 + i563) &&* ((0 <=. i564 &&* 1 >. i564) &&* ((0 <=. i565 &&* 2 >. i565) &&* (0 <=. i566 &&* 2 >. i566)))) 0 1, i562, i563, i564, i565, i566]) ! [0]) (\\[i568, i569] -> [i568 + i569]), tsum (tsum (tsum (ttranspose [0,2,3,1] u561))), tscatter [1,1,2,2] (tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w428 * w511))))) (\\[i512, i513, i514, i515, i516] -> [ifF ((0 <=. i512 + i513 &&* 1 >. i512 + i513) &&* ((0 <=. i514 &&* 1 >. i514) &&* ((0 <=. i515 &&* 2 >. i515) &&* (0 <=. i516 &&* 2 >. i516)))) 0 1, i512, i513, i514, i515, i516]) ! [0]) (\\[i518, i519] -> [i518 + i519]), tsum (tsum (tsum (ttranspose [0,2,3,1] u510))), tsum (ttranspose [2,1,0] (t473 * treplicate 1 m479)), tsum (ttranspose [1,0] m479), tsum (ttranspose [2,0,1] (treplicate 10 (m477 * m474)) * ttranspose [2,1,0] (treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w366 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,4,4] (tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 7.0)))))), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i670, i671, i672, i673, i674, i675] -> [ifF ((0 <=. 0 + i672 &&* 1 >. 0 + i672) &&* ((0 <=. i673 &&* 1 >. i673) &&* ((0 <=. i670 + i674 &&* 4 >. i670 + i674) &&* (0 <=. i671 + i675 &&* 4 >. i671 + i675)))) 0 1, i670, i671, i672, i673, i674, i675]) * tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 (tgather [1,1,2,2] u2 (\\[i358] -> [0 + i358]))), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i687, i688, i689, i690, i691, i692] -> [ifF ((0 <=. 0 + i689 &&* 1 >. 0 + i689) &&* ((0 <=. i690 &&* 1 >. i690) &&* ((0 <=. i691 &&* 2 >. i691) &&* (0 <=. i692 &&* 2 >. i692)))) 0 1, i687, i688, i689, i690, i691, i692])) (\\[i648, i649, i650, i651, i652] -> [rem (quot (i648 + 64 * i649 + 16 * i651 + 4 * i652 + 64 * i650) 16) 4, rem (quot (i648 + 64 * i649 + 16 * i651 + 4 * i652 + 64 * i650) 4) 4, 0, 0, rem (quot (i648 + 64 * i649 + 16 * i651 + 4 * i652 + 64 * i650) 2) 2, rem (i648 + 64 * i649 + 16 * i651 + 4 * i652 + 64 * i650) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w404 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [ifF (w366 ! [i371, i372, i373, i374, i375, i376, i377, tconst (fromList [1] [0]) ! [i371] + tconst (fromList [1] [0]) ! [i375], tconst (fromList [1] [0]) ! [i372] + tconst (fromList [1] [0]) ! [i376], 2 * tconst (fromList [2] [0,1]) ! [i373] + tconst (fromList [2] [0,1]) ! [i377], i378] <=. tconst 0.0) 0 1]) * tgather [1,1,2,2,1,1,2,4] w366 (\\[i379, i380, i381, i382, i383, i384, i385] -> [i379, i380, i381, i382, i383, i384, i385, tconst (fromList [1] [0]) ! [i379] + tconst (fromList [1] [0]) ! [i383], tconst (fromList [1] [0]) ! [i380] + tconst (fromList [1] [0]) ! [i384], 2 * tconst (fromList [2] [0,1]) ! [i381] + tconst (fromList [2] [0,1]) ! [i385]])) (\\[i388, i389, i390, i391, i392, i393, i394, i395] -> [i388, i389, i390, i391, i392, i393, i394, 2 * i391 + i395]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i396, i397, i398, i399, i400, i401, i402, i403] -> [ifF ((0 <=. i396 + i400 &&* 1 >. i396 + i400) &&* ((0 <=. i397 + i401 &&* 1 >. i397 + i401) &&* ((0 <=. 2 * i398 + i402 &&* 4 >. 2 * i398 + i402) &&* (0 <=. 2 * i399 + i403 &&* 4 >. 2 * i399 + i403)))) 0 1, i396, i397, i398, i399, i400, i401, i402, i403]))))))) ; w430 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,2,2] (tgather [2,2,1,1,2,2] (tfromList [tgather [2,2,1,1,2,2] (w404 ! [0]) (\\[i408, i409, i410, i411, i412, i413] -> [i408, i409, i410, i411, i412, tconst (fromList [1] [0]) ! [0] + tconst (fromList [1] [0]) ! [i410], i411, tconst (fromList [2] [0,1]) ! [i408] + tconst (fromList [2] [0,1]) ! [i412], i409 + i413, 0, 0, rem (quot (tmaxIndex (tgather [4] (w404 ! [0, i408, i409, i410, i411, i412, tconst (fromList [1] [0]) ! [0] + tconst (fromList [1] [0]) ! [i410], i411, tconst (fromList [2] [0,1]) ! [i408] + tconst (fromList [2] [0,1]) ! [i412], i409 + i413, 0, 0]) (\\[i570] -> [rem (quot i570 2) 2, rem i570 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w404 ! [0, i408, i409, i410, i411, i412, tconst (fromList [1] [0]) ! [0] + tconst (fromList [1] [0]) ! [i410], i411, tconst (fromList [2] [0,1]) ! [i408] + tconst (fromList [2] [0,1]) ! [i412], i409 + i413, 0, 0]) (\\[i571] -> [rem (quot i571 2) 2, rem i571 2]))) 2]), treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i693, i694, i695, i696, i697, i698] -> [ifF ((0 <=. 0 + i695 &&* 1 >. 0 + i695) &&* ((0 <=. i696 &&* 1 >. i696) &&* ((0 <=. i693 + i697 &&* 2 >. i693 + i697) &&* (0 <=. i694 + i698 &&* 2 >. i694 + i698)))) 0 1, i693, i694, i695, i696, i697, i698]) * tgather [2,2,1,1,2,2] (tfromList [treplicate 2 (treplicate 2 (tgather [1,1,2,2] u4 (\\[i422] -> [0 + i422]))), treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i710, i711, i712, i713, i714, i715] -> [ifF ((0 <=. 0 + i712 &&* 1 >. 0 + i712) &&* ((0 <=. i713 &&* 1 >. i713) &&* ((0 <=. i714 &&* 2 >. i714) &&* (0 <=. i715 &&* 2 >. i715)))) 0 1, i710, i711, i712, i713, i714, i715])) (\\[i658, i659, i660, i661, i662] -> [rem (quot (i658 + 16 * i659 + 8 * i661 + 4 * i662 + 16 * i660) 8) 2, rem (quot (i658 + 16 * i659 + 8 * i661 + 4 * i662 + 16 * i660) 4) 2, 0, 0, rem (quot (i658 + 16 * i659 + 8 * i661 + 4 * i662 + 16 * i660) 2) 2, rem (i658 + 16 * i659 + 8 * i661 + 4 * i662 + 16 * i660) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w468 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i435, i436, i437, i438, i439, i440, i441, i442] -> [ifF (w430 ! [i435, i436, i437, i438, i439, i440, i441, tconst (fromList [1] [0]) ! [i435] + tconst (fromList [1] [0]) ! [i439], tconst (fromList [1] [0]) ! [i436] + tconst (fromList [1] [0]) ! [i440], 2 * tconst (fromList [1] [0]) ! [i437] + tconst (fromList [2] [0,1]) ! [i441], i442] <=. tconst 0.0) 0 1]) * tgather [1,1,1,1,1,1,2,2] w430 (\\[i443, i444, i445, i446, i447, i448, i449] -> [i443, i444, i445, i446, i447, i448, i449, tconst (fromList [1] [0]) ! [i443] + tconst (fromList [1] [0]) ! [i447], tconst (fromList [1] [0]) ! [i444] + tconst (fromList [1] [0]) ! [i448], 2 * tconst (fromList [1] [0]) ! [i445] + tconst (fromList [2] [0,1]) ! [i449]])) (\\[i452, i453, i454, i455, i456, i457, i458, i459] -> [i452, i453, i454, i455, i456, i457, i458, 2 * i455 + i459]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i460, i461, i462, i463, i464, i465, i466, i467] -> [ifF ((0 <=. i460 + i464 &&* 1 >. i460 + i464) &&* ((0 <=. i461 + i465 &&* 1 >. i461 + i465) &&* ((0 <=. 2 * i462 + i466 &&* 2 >. 2 * i462 + i466) &&* (0 <=. 2 * i463 + i467 &&* 2 >. 2 * i463 + i467)))) 0 1, i460, i461, i462, i463, i464, i465, i466, i467]) ; m474 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (w468 ! [0, 0, 0, 0, 0, 0, rem (quot (tmaxIndex (tgather [4] (w468 ! [0, 0, 0, 0, 0, 0]) (\\[i572] -> [rem (quot i572 2) 2, rem i572 2]))) 2) 2, rem (tmaxIndex (tgather [4] (w468 ! [0, 0, 0, 0, 0, 0]) (\\[i573] -> [rem (quot i573 2) 2, rem i573 2]))) 2]))))) + ttranspose [1,0] (treplicate 1 v7) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 10 (tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i475, i476] -> [ifF (m474 ! [i475, i476] <=. tconst 0.0) 0 1]) * m474))) + ttranspose [1,0] (treplicate 1 v9)"
