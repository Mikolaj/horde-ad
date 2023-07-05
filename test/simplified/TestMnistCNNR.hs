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
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
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
     ( ranked ~ Flip OR.Array
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
     ( ranked ~ Flip OR.Array
     , ADReady ranked r, Random r, InterpretAstR (ADVal ranked)
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
       let testDataR = packBatchR testData
           (vars1, asts1) = funToAst2 domainsInit
           doms = V.fromList asts1
       (varGlyph, _, astGlyph) <-
         funToAstIOR
           (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
           id
       (varLabel, _, astLabel) <-
         funToAstIOR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
       let ast :: AstRanked r 0
           ast = MnistCnnRanked2.convMnistLossFusedR
                   miniBatchSize (tprimalPart astGlyph, tprimalPart astLabel)
                                 (parseDomains valsInit doms)
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
     ( ranked ~ Flip OR.Array, ADReady ranked r, Random r
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
                     $ extendEnvR varLabel (tconstant astLabel) EM.empty
           f = MnistCnnRanked2.convMnistLossFusedR
                 miniBatchSize (tprimalPart astGlyph, tprimalPart astLabel)
           (((varDtAgain, vars1Again), gradientRaw, primal), _) =
             revDtInit @Nat @(Flip OR.Array)
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
      blackGlyph :: AstPrimalPart Double 4
      blackGlyph = AstPrimalPart
                   $ AstReplicate batch_size
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
      afcnn2T :: MnistCnnRanked2.ADCnnMnistParameters AstRanked Double
              -> AstRanked Double 2
      afcnn2T = MnistCnnRanked2.convMnistTwoR sizeMnistHeightI sizeMnistWidthI
                                              batch_size blackGlyph
      (artifact6, _) = revDtFun True afcnn2T valsInit
  printGradient6Pretty renames artifact6
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w306 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 7.0)) (\\[i238, i239] -> [i239])) (\\[i240, i241, i242] -> [i241, i242])) (\\[i243, i244, i245, i246] -> [i244, i245, i246])) (\\[i247, i248, i249, i250, i251] -> [i248, i249, i250, i251])) (\\[i252, i253, i254, i255, i256, i257] -> [i253, i254, i255, i256, i257])) (\\[i258, i259, i260, i261, i262, i263, i264] -> [i259, i260, i261, i262, i263, i264]), tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 0.0)) (\\[i265, i266] -> [i266])) (\\[i267, i268, i269] -> [i268, i269])) (\\[i270, i271, i272, i273] -> [i271, i272, i273])) (\\[i274, i275, i276, i277, i278] -> [i275, i276, i277, i278])) (\\[i279, i280, i281, i282, i283, i284] -> [i280, i281, i282, i283, i284])) (\\[i285, i286, i287, i288, i289, i290, i291] -> [i286, i287, i288, i289, i290, i291])]) (\\[i292, i293, i294, i295, i296, i297, i298] -> [ifB ((0 <=* i292 + i295 &&* 1 >* i292 + i295) &&* ((0 <=* i296 &&* 1 >* i296) &&* ((0 <=* i293 + i297 &&* 4 >* i293 + i297) &&* (0 <=* i294 + i298 &&* 4 >* i294 + i298)))) 0 1, i292, i293, i294, i295, i296, i297, i298]))) ; w307 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u2 (\\[i299, i300] -> [i299 + i300]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i301, i302, i303, i304, i305] -> [ifB ((0 <=* i301 + i302 &&* 1 >* i301 + i302) &&* ((0 <=* i303 &&* 1 >* i303) &&* ((0 <=* i304 &&* 2 >* i304) &&* (0 <=* i305 &&* 2 >* i305)))) 0 1, i301, i302, i303, i304, i305]))))) ; w308 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,4,4,4] (w306 * w307))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w324 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i309, i310, i311, i312, i313, i314, i315, i316] -> [ifB (w308 ! [i309, i310, i311, i312, i313, i314, i315, i309 + i313, i310 + i314, 2 * i311 + i315, i316] <=* tconst 0.0) 0 1]) ; w325 = tgather [1,1,2,2,1,1,2,4] w308 (\\[i317, i318, i319, i320, i321, i322, i323] -> [i317, i318, i319, i320, i321, i322, i323, i317 + i321, i318 + i322, 2 * i319 + i323]) ; w342 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w324 * w325) (\\[i326, i327, i328, i329, i330, i331, i332, i333] -> [i326, i327, i328, i329, i330, i331, i332, 2 * i329 + i333]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i334, i335, i336, i337, i338, i339, i340, i341] -> [ifB ((0 <=* i334 + i338 &&* 1 >* i334 + i338) &&* ((0 <=* i335 + i339 &&* 1 >* i335 + i339) &&* ((0 <=* 2 * i336 + i340 &&* 4 >* 2 * i336 + i340) &&* (0 <=* 2 * i337 + i341 &&* 4 >* 2 * i337 + i341)))) 0 1, i334, i335, i336, i337, i338, i339, i340, i341]))))))) ; w365 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w342 (\\[i344, i345, i346, i347, i348, i349, i350] -> [i344, i345, i346, i347, i348, i349, i344 + i347, i348, i345 + i349, i346 + i350, 0, 0, rem (quot (tmaxIndex0 (let w343 = treshape [1,2,2,1,1,2,1,1,2,2,4] w342 in w343 ! [i344, i345, i346, i347, i348, i349, i344 + i347, i348, i345 + i349, i346 + i350])) 2) 2, rem (tmaxIndex0 (let w343 = treshape [1,2,2,1,1,2,1,1,2,2,4] w342 in w343 ! [i344, i345, i346, i347, i348, i349, i344 + i347, i348, i345 + i349, i346 + i350])) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i351, i352, i353, i354, i355, i356, i357] -> [ifB ((0 <=* i351 + i354 &&* 1 >* i351 + i354) &&* ((0 <=* i355 &&* 1 >* i355) &&* ((0 <=* i352 + i356 &&* 2 >* i352 + i356) &&* (0 <=* i353 + i357 &&* 2 >* i353 + i357)))) 0 1, i351, i352, i353, i354, i355, i356, i357]))) ; w366 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i358, i359] -> [i358 + i359]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i360, i361, i362, i363, i364] -> [ifB ((0 <=* i360 + i361 &&* 1 >* i360 + i361) &&* ((0 <=* i362 &&* 1 >* i362) &&* ((0 <=* i363 &&* 2 >* i363) &&* (0 <=* i364 &&* 2 >* i364)))) 0 1, i360, i361, i362, i363, i364]))))) ; w367 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,2,2,4] (w365 * w366))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w383 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i368, i369, i370, i371, i372, i373, i374, i375] -> [ifB (w367 ! [i368, i369, i370, i371, i372, i373, i374, i368 + i372, i369 + i373, 2 * i370 + i374, i375] <=* tconst 0.0) 0 1]) ; w384 = tgather [1,1,1,1,1,1,2,2] w367 (\\[i376, i377, i378, i379, i380, i381, i382] -> [i376, i377, i378, i379, i380, i381, i382, i376 + i380, i377 + i381, 2 * i378 + i382]) ; w401 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w383 * w384) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [i385, i386, i387, i388, i389, i390, i391, 2 * i388 + i392]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i393, i394, i395, i396, i397, i398, i399, i400] -> [ifB ((0 <=* i393 + i397 &&* 1 >* i393 + i397) &&* ((0 <=* i394 + i398 &&* 1 >* i394 + i398) &&* ((0 <=* 2 * i395 + i399 &&* 2 >* 2 * i395 + i399) &&* (0 <=* 2 * i396 + i400 &&* 2 >* 2 * i396 + i400)))) 0 1, i393, i394, i395, i396, i397, i398, i399, i400]) ; t407 = ttranspose [1,0] (treplicate 1 (ttranspose [1,0] (treshape [1,1] (tgather [1,1,1,1] w401 (\\[i403, i404, i405, i406] -> [i403, i404, i405, i406, 0, 0, rem (quot (tmaxIndex0 (let w402 = treshape [1,1,1,1,4] w401 in w402 ! [i403, i404, i405, i406])) 2) 2, rem (tmaxIndex0 (let w402 = treshape [1,1,1,1,4] w401 in w402 ! [i403, i404, i405, i406])) 2]))))) ; m408 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t407) + ttranspose [1,0] (treplicate 1 v7) ; m411 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i409, i410] -> [ifB (m408 ! [i409, i410] <=* tconst 0.0) 0 1]) ; t412 = ttranspose [1,0] (treplicate 10 (m411 * m408)) ; m413 = m411 * tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret)) ; w426 = tscatter [2,1,1,1,1,1,1,2,2] (tscatter [1,1,1,1,1,1,2,2] (treshape [1,1,1,1] (tsum (ttranspose [1,0] (treplicate 1 m6) * ttranspose [1,2,0] (treplicate 1 m413)))) (\\[i414, i415, i416, i417] -> [i414, i415, i416, i417, 0, 0, rem (quot (tmaxIndex0 (let w402 = treshape [1,1,1,1,4] w401 in w402 ! [i414, i415, i416, i417])) 2) 2, rem (tmaxIndex0 (let w402 = treshape [1,1,1,1,4] w401 in w402 ! [i414, i415, i416, i417])) 2])) (\\[i418, i419, i420, i421, i422, i423, i424, i425] -> [ifB ((0 <=* i418 + i422 &&* 1 >* i418 + i422) &&* ((0 <=* i419 + i423 &&* 1 >* i419 + i423) &&* ((0 <=* 2 * i420 + i424 &&* 2 >* 2 * i420 + i424) &&* (0 <=* 2 * i421 + i425 &&* 2 >* 2 * i421 + i425)))) 0 1, i418, i419, i420, i421, i422, i423, i424, i425]) ; u442 = tsum (tsum (tsum (tsum (tsum (tsum (tsum (tscatter [1,1,1,1,1,1,2,1,1,2,2] (w383 * tscatter [1,1,1,1,1,1,2,2] (w426 ! [0]) (\\[i427, i428, i429, i430, i431, i432, i433, i434] -> [i427, i428, i429, i430, i431, i432, i433, 2 * i430 + i434])) (\\[i435, i436, i437, i438, i439, i440, i441] -> [i435, i436, i437, i438, i439, i440, i441, i435 + i439, i436 + i440, 2 * i437 + i441])))))))) ; w443 = treshape [1,1,2,2,1,1,2,2] (ttranspose [1,2,3,4,0] (treplicate 4 u442)) ; w449 = tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w365 * w443))))) (\\[i444, i445, i446, i447, i448] -> [ifB ((0 <=* i444 + i445 &&* 1 >* i444 + i445) &&* ((0 <=* i446 &&* 1 >* i446) &&* ((0 <=* i447 &&* 2 >* i447) &&* (0 <=* i448 &&* 2 >* i448)))) 0 1, i444, i445, i446, i447, i448]) ; w459 = tscatter [2,1,2,2,1,1,2,2] (tsum (ttranspose [1,0] (w366 * w443))) (\\[i452, i453, i454, i455, i456, i457, i458] -> [ifB ((0 <=* i452 + i455 &&* 1 >* i452 + i455) &&* ((0 <=* i456 &&* 1 >* i456) &&* ((0 <=* i453 + i457 &&* 2 >* i453 + i457) &&* (0 <=* i454 + i458 &&* 2 >* i454 + i458)))) 0 1, i452, i453, i454, i455, i456, i457, i458]) ; w475 = tscatter [2,1,1,2,2,1,1,2,2] (tsum (tsum (tsum (tsum (tsum (tsum (tscatter [1,2,2,1,1,2,1,1,2,2,1,1,2,2] (w459 ! [0]) (\\[i460, i461, i462, i463, i464, i465, i466] -> [i460, i461, i462, i463, i464, i465, i460 + i463, i464, i461 + i465, i462 + i466, 0, 0, rem (quot (tmaxIndex0 (let w343 = treshape [1,2,2,1,1,2,1,1,2,2,4] w342 in w343 ! [i460, i461, i462, i463, i464, i465, i460 + i463, i464, i461 + i465, i462 + i466])) 2) 2, rem (tmaxIndex0 (let w343 = treshape [1,2,2,1,1,2,1,1,2,2,4] w342 in w343 ! [i460, i461, i462, i463, i464, i465, i460 + i463, i464, i461 + i465, i462 + i466])) 2])))))))) (\\[i467, i468, i469, i470, i471, i472, i473, i474] -> [ifB ((0 <=* i467 + i471 &&* 1 >* i467 + i471) &&* ((0 <=* i468 + i472 &&* 1 >* i468 + i472) &&* ((0 <=* 2 * i469 + i473 &&* 4 >* 2 * i469 + i473) &&* (0 <=* 2 * i470 + i474 &&* 4 >* 2 * i470 + i474)))) 0 1, i467, i468, i469, i470, i471, i472, i473, i474]) ; u491 = tsum (tsum (tsum (tsum (tsum (tsum (tsum (tscatter [1,1,2,2,1,1,2,1,1,4,4] (w324 * tscatter [1,1,2,2,1,1,2,4] (w475 ! [0]) (\\[i476, i477, i478, i479, i480, i481, i482, i483] -> [i476, i477, i478, i479, i480, i481, i482, 2 * i479 + i483])) (\\[i484, i485, i486, i487, i488, i489, i490] -> [i484, i485, i486, i487, i488, i489, i490, i484 + i488, i485 + i489, 2 * i486 + i490])))))))) ; w497 = tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w306 * treshape [1,1,4,4,1,1,2,2] (ttranspose [1,2,3,4,0] (treplicate 4 u491))))))) (\\[i492, i493, i494, i495, i496] -> [ifB ((0 <=* i492 + i493 &&* 1 >* i492 + i493) &&* ((0 <=* i494 &&* 1 >* i494) &&* ((0 <=* i495 &&* 2 >* i495) &&* (0 <=* i496 &&* 2 >* i496)))) 0 1, i492, i493, i494, i495, i496]) in (tscatter [1,1,2,2] (w497 ! [0]) (\\[i498, i499] -> [i498 + i499]), tsum (tsum (tsum (ttranspose [0,2,3,1] u491))), tscatter [1,1,2,2] (w449 ! [0]) (\\[i450, i451] -> [i450 + i451]), tsum (tsum (tsum (ttranspose [0,2,3,1] u442))), tsum (ttranspose [2,1,0] (t407 * treplicate 1 m413)), tsum (ttranspose [1,0] m413), tsum (ttranspose [2,1,0] (t412 * treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w306 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 7.0)) (\\[i238, i239] -> [i239])) (\\[i240, i241, i242] -> [i241, i242])) (\\[i243, i244, i245, i246] -> [i244, i245, i246])) (\\[i247, i248, i249, i250, i251] -> [i248, i249, i250, i251])) (\\[i252, i253, i254, i255, i256, i257] -> [i253, i254, i255, i256, i257])) (\\[i258, i259, i260, i261, i262, i263, i264] -> [i259, i260, i261, i262, i263, i264]), tgather [1,4,4,1,1,2,2] (tgather [4,4,1,1,2,2] (tgather [4,1,1,2,2] (tgather [1,1,2,2] (tgather [1,2,2] (tgather [2,2] (treplicate 2 (tconst 0.0)) (\\[i265, i266] -> [i266])) (\\[i267, i268, i269] -> [i268, i269])) (\\[i270, i271, i272, i273] -> [i271, i272, i273])) (\\[i274, i275, i276, i277, i278] -> [i275, i276, i277, i278])) (\\[i279, i280, i281, i282, i283, i284] -> [i280, i281, i282, i283, i284])) (\\[i285, i286, i287, i288, i289, i290, i291] -> [i286, i287, i288, i289, i290, i291])]) (\\[i292, i293, i294, i295, i296, i297, i298] -> [ifB ((0 <=* i292 + i295 &&* 1 >* i292 + i295) &&* ((0 <=* i296 &&* 1 >* i296) &&* ((0 <=* i293 + i297 &&* 4 >* i293 + i297) &&* (0 <=* i294 + i298 &&* 4 >* i294 + i298)))) 0 1, i292, i293, i294, i295, i296, i297, i298]))) ; w307 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u2 (\\[i299, i300] -> [i299 + i300]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i301, i302, i303, i304, i305] -> [ifB ((0 <=* i301 + i302 &&* 1 >* i301 + i302) &&* ((0 <=* i303 &&* 1 >* i303) &&* ((0 <=* i304 &&* 2 >* i304) &&* (0 <=* i305 &&* 2 >* i305)))) 0 1, i301, i302, i303, i304, i305]))))) ; w308 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,4,4,4] (w306 * w307))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w324 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i309, i310, i311, i312, i313, i314, i315, i316] -> [ifB (w308 ! [i309, i310, i311, i312, i313, i314, i315, i309 + i313, i310 + i314, 2 * i311 + i315, i316] <=* tconst 0.0) 0 1]) ; w325 = tgather [1,1,2,2,1,1,2,4] w308 (\\[i317, i318, i319, i320, i321, i322, i323] -> [i317, i318, i319, i320, i321, i322, i323, i317 + i321, i318 + i322, 2 * i319 + i323]) ; w342 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w324 * w325) (\\[i326, i327, i328, i329, i330, i331, i332, i333] -> [i326, i327, i328, i329, i330, i331, i332, 2 * i329 + i333]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i334, i335, i336, i337, i338, i339, i340, i341] -> [ifB ((0 <=* i334 + i338 &&* 1 >* i334 + i338) &&* ((0 <=* i335 + i339 &&* 1 >* i335 + i339) &&* ((0 <=* 2 * i336 + i340 &&* 4 >* 2 * i336 + i340) &&* (0 <=* 2 * i337 + i341 &&* 4 >* 2 * i337 + i341)))) 0 1, i334, i335, i336, i337, i338, i339, i340, i341]))))))) ; w365 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w342 (\\[i344, i345, i346, i347, i348, i349, i350] -> [i344, i345, i346, i347, i348, i349, i344 + i347, i348, i345 + i349, i346 + i350, 0, 0, rem (quot (tmaxIndex0 (let w343 = treshape [1,2,2,1,1,2,1,1,2,2,4] w342 in w343 ! [i344, i345, i346, i347, i348, i349, i344 + i347, i348, i345 + i349, i346 + i350])) 2) 2, rem (tmaxIndex0 (let w343 = treshape [1,2,2,1,1,2,1,1,2,2,4] w342 in w343 ! [i344, i345, i346, i347, i348, i349, i344 + i347, i348, i345 + i349, i346 + i350])) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i351, i352, i353, i354, i355, i356, i357] -> [ifB ((0 <=* i351 + i354 &&* 1 >* i351 + i354) &&* ((0 <=* i355 &&* 1 >* i355) &&* ((0 <=* i352 + i356 &&* 2 >* i352 + i356) &&* (0 <=* i353 + i357 &&* 2 >* i353 + i357)))) 0 1, i351, i352, i353, i354, i355, i356, i357]))) ; w366 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i358, i359] -> [i358 + i359]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i360, i361, i362, i363, i364] -> [ifB ((0 <=* i360 + i361 &&* 1 >* i360 + i361) &&* ((0 <=* i362 &&* 1 >* i362) &&* ((0 <=* i363 &&* 2 >* i363) &&* (0 <=* i364 &&* 2 >* i364)))) 0 1, i360, i361, i362, i363, i364]))))) ; w367 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (ttranspose [4,0,1,2,3] (treshape [1,1,2,2,4] (w365 * w366))) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w383 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i368, i369, i370, i371, i372, i373, i374, i375] -> [ifB (w367 ! [i368, i369, i370, i371, i372, i373, i374, i368 + i372, i369 + i373, 2 * i370 + i374, i375] <=* tconst 0.0) 0 1]) ; w384 = tgather [1,1,1,1,1,1,2,2] w367 (\\[i376, i377, i378, i379, i380, i381, i382] -> [i376, i377, i378, i379, i380, i381, i382, i376 + i380, i377 + i381, 2 * i378 + i382]) ; w401 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w383 * w384) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [i385, i386, i387, i388, i389, i390, i391, 2 * i388 + i392]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i393, i394, i395, i396, i397, i398, i399, i400] -> [ifB ((0 <=* i393 + i397 &&* 1 >* i393 + i397) &&* ((0 <=* i394 + i398 &&* 1 >* i394 + i398) &&* ((0 <=* 2 * i395 + i399 &&* 2 >* 2 * i395 + i399) &&* (0 <=* 2 * i396 + i400 &&* 2 >* 2 * i396 + i400)))) 0 1, i393, i394, i395, i396, i397, i398, i399, i400]) ; t407 = ttranspose [1,0] (treplicate 1 (ttranspose [1,0] (treshape [1,1] (tgather [1,1,1,1] w401 (\\[i403, i404, i405, i406] -> [i403, i404, i405, i406, 0, 0, rem (quot (tmaxIndex0 (let w402 = treshape [1,1,1,1,4] w401 in w402 ! [i403, i404, i405, i406])) 2) 2, rem (tmaxIndex0 (let w402 = treshape [1,1,1,1,4] w401 in w402 ! [i403, i404, i405, i406])) 2]))))) ; m408 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t407) + ttranspose [1,0] (treplicate 1 v7) ; m411 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i409, i410] -> [ifB (m408 ! [i409, i410] <=* tconst 0.0) 0 1]) ; t412 = ttranspose [1,0] (treplicate 10 (m411 * m408)) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * t412) + ttranspose [1,0] (treplicate 1 v9)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret u2 v3 u4 v5 m6 v7 m8 v9 -> let w306 = ttranspose [1,0] (treplicate 1 (tgather [1,4,4,1,1,2,2] (tfromList [treplicate 1 (treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 7.0))))))), treplicate 1 (treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i292, i293, i294, i295, i296, i297, i298] -> [ifB ((0 <=* i292 + i295 &&* 1 >* i292 + i295) &&* ((0 <=* i296 &&* 1 >* i296) &&* ((0 <=* i293 + i297 &&* 4 >* i293 + i297) &&* (0 <=* i294 + i298 &&* 4 >* i294 + i298)))) 0 1, i292, i293, i294, i295, i296, i297, i298]))) ; w308 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,4,4] (w306 ! [0, 0] * tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 u2), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i600, i601, i602, i603, i604, i605] -> [ifB ((0 <=* i602 &&* 1 >* i602) &&* ((0 <=* i603 &&* 1 >* i603) &&* ((0 <=* i604 &&* 2 >* i604) &&* (0 <=* i605 &&* 2 >* i605)))) 0 1, i600, i601, i602, i603, i604, i605])) (\\[i547, i548, i549, i550, i551] -> [rem (quot (64 * i548 + (64 * i549 + (16 * i550 + (4 * i551 + i547)))) 16) 4, rem (quot (64 * i548 + (64 * i549 + (16 * i550 + (4 * i551 + i547)))) 4) 4, 0, 0, rem (quot (64 * i548 + (64 * i549 + (16 * i550 + (4 * i551 + i547)))) 2) 2, rem (64 * i548 + (64 * i549 + (16 * i550 + (4 * i551 + i547)))) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w324 = tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i309, i310, i311, i312, i313, i314, i315, i316] -> [ifB (w308 ! [i309, i310, i311, i312, i313, i314, i315, i309 + i313, i310 + i314, 2 * i311 + i315, i316] <=* tconst 0.0) 0 1]) ; w342 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (w324 * tgather [1,1,2,2,1,1,2,4] w308 (\\[i317, i318, i319, i320, i321, i322, i323] -> [i317, i318, i319, i320, i321, i322, i323, i317 + i321, i318 + i322, 2 * i319 + i323])) (\\[i326, i327, i328, i329, i330, i331, i332, i333] -> [i326, i327, i328, i329, i330, i331, i332, 2 * i329 + i333]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i334, i335, i336, i337, i338, i339, i340, i341] -> [ifB ((0 <=* i334 + i338 &&* 1 >* i334 + i338) &&* ((0 <=* i335 + i339 &&* 1 >* i335 + i339) &&* ((0 <=* 2 * i336 + i340 &&* 4 >* 2 * i336 + i340) &&* (0 <=* 2 * i337 + i341 &&* 4 >* 2 * i337 + i341)))) 0 1, i334, i335, i336, i337, i338, i339, i340, i341]))))))) ; w365 = ttranspose [1,0] (treplicate 1 (tgather [1,2,2,1,1,2,2] (tfromList [tgather [1,2,2,1,1,2,2] w342 (\\[i344, i345, i346, i347, i348, i349, i350] -> [i344, i345, i346, i347, i348, i349, i344 + i347, i348, i345 + i349, i346 + i350, 0, 0, rem (quot (tmaxIndex0 (tgather [4] (w342 ! [0]) (\\[i577] -> [rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i577))))))))))))) 64) 2, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i577))))))))))))) 32) 2, 0, 0, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i577))))))))))))) 16) 2, 0, 0, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i577))))))))))))) 8) 2, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i577))))))))))))) 4) 2, 0, 0, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i577))))))))))))) 2) 2, rem (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i577))))))))))))) 2]))) 2) 2, rem (tmaxIndex0 (tgather [4] (w342 ! [0]) (\\[i588] -> [rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i588))))))))))))) 64) 2, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i588))))))))))))) 32) 2, 0, 0, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i588))))))))))))) 16) 2, 0, 0, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i588))))))))))))) 8) 2, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i588))))))))))))) 4) 2, 0, 0, rem (quot (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i588))))))))))))) 2) 2, rem (128 * i344 + (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i344 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i588))))))))))))) 2]))) 2]), treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))))]) (\\[i351, i352, i353, i354, i355, i356, i357] -> [ifB ((0 <=* i351 + i354 &&* 1 >* i351 + i354) &&* ((0 <=* i355 &&* 1 >* i355) &&* ((0 <=* i352 + i356 &&* 2 >* i352 + i356) &&* (0 <=* i353 + i357 &&* 2 >* i353 + i357)))) 0 1, i351, i352, i353, i354, i355, i356, i357]))) ; w366 = ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 (tgather [1,1,1,2,2] (tfromList [tgather [1,1,1,2,2] u4 (\\[i358, i359] -> [i358 + i359]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0)))))]) (\\[i360, i361, i362, i363, i364] -> [ifB ((0 <=* i360 + i361 &&* 1 >* i360 + i361) &&* ((0 <=* i362 &&* 1 >* i362) &&* ((0 <=* i363 &&* 2 >* i363) &&* (0 <=* i364 &&* 2 >* i364)))) 0 1, i360, i361, i362, i363, i364]))))) ; w367 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,2,2] (w365 ! [0, 0] * w366 ! [0, 0]) (\\[i537, i538, i539, i540, i541] -> [rem (quot (16 * i538 + (16 * i539 + (8 * i540 + (4 * i541 + i537)))) 8) 2, rem (quot (16 * i538 + (16 * i539 + (8 * i540 + (4 * i541 + i537)))) 4) 2, 0, 0, rem (quot (16 * i538 + (16 * i539 + (8 * i540 + (4 * i541 + i537)))) 2) 2, rem (16 * i538 + (16 * i539 + (8 * i540 + (4 * i541 + i537)))) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w383 = tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i368, i369, i370, i371, i372, i373, i374, i375] -> [ifB (w367 ! [i368, i369, i370, i371, i372, i373, i374, i368 + i372, i369 + i373, 2 * i370 + i374, i375] <=* tconst 0.0) 0 1]) ; w401 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (w383 * tgather [1,1,1,1,1,1,2,2] w367 (\\[i376, i377, i378, i379, i380, i381, i382] -> [i376, i377, i378, i379, i380, i381, i382, i376 + i380, i377 + i381, 2 * i378 + i382])) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [i385, i386, i387, i388, i389, i390, i391, 2 * i388 + i392]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i393, i394, i395, i396, i397, i398, i399, i400] -> [ifB ((0 <=* i393 + i397 &&* 1 >* i393 + i397) &&* ((0 <=* i394 + i398 &&* 1 >* i394 + i398) &&* ((0 <=* 2 * i395 + i399 &&* 2 >* 2 * i395 + i399) &&* (0 <=* 2 * i396 + i400 &&* 2 >* 2 * i396 + i400)))) 0 1, i393, i394, i395, i396, i397, i398, i399, i400]) ; t407 = ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (w401 ! [0, 0, 0, 0, 0, 0, rem (quot (tmaxIndex0 (tgather [4] (w401 ! [0, 0, 0, 0, 0, 0]) (\\[i561] -> [rem (quot i561 2) 2, rem i561 2]))) 2) 2, rem (tmaxIndex0 (tgather [4] (w401 ! [0, 0, 0, 0, 0, 0]) (\\[i566] -> [rem (quot i566 2) 2, rem i566 2]))) 2])))) ; m408 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * t407) + ttranspose [1,0] (treplicate 1 v7) ; m411 = tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i409, i410] -> [ifB (m408 ! [i409, i410] <=* tconst 0.0) 0 1]) ; m413 = m411 * tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret)) ; u442 = tscatter [1,1,2,2] (w383 * tscatter [1,1,1,1,1,1,2,2] (tscatter [2,1,1,1,1,1,1,2,2] (tscatter [1,1,1,1,1,1,2,2] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tsum (tgather [1] (m6 * tgather [1,1] m413 (\\[i531, i532] -> [i531, 0])) (\\[i534] -> [i534, 0]))))))) (\\[i414, i415, i416, i417] -> [i414, i415, i416, i417, 0, 0, rem (quot (tmaxIndex0 (tgather [4] (w401 ! [0, 0, 0, 0, 0, 0]) (\\[i610] -> [rem (quot (4 * i414 + (4 * i415 + (4 * i416 + (4 * i417 + i610)))) 2) 2, rem (4 * i414 + (4 * i415 + (4 * i416 + (4 * i417 + i610)))) 2]))) 2) 2, rem (tmaxIndex0 (tgather [4] (w401 ! [0, 0, 0, 0, 0, 0]) (\\[i615] -> [rem (quot (4 * i414 + (4 * i415 + (4 * i416 + (4 * i417 + i615)))) 2) 2, rem (4 * i414 + (4 * i415 + (4 * i416 + (4 * i417 + i615)))) 2]))) 2])) (\\[i418, i419, i420, i421, i422, i423, i424, i425] -> [ifB ((0 <=* i418 + i422 &&* 1 >* i418 + i422) &&* ((0 <=* i419 + i423 &&* 1 >* i419 + i423) &&* ((0 <=* 2 * i420 + i424 &&* 2 >* 2 * i420 + i424) &&* (0 <=* 2 * i421 + i425 &&* 2 >* 2 * i421 + i425)))) 0 1, i418, i419, i420, i421, i422, i423, i424, i425]) ! [0]) (\\[i427, i428, i429, i430, i431, i432, i433, i434] -> [i427, i428, i429, i430, i431, i432, i433, 2 * i430 + i434])) (\\[i435, i436, i437, i438, i439, i440, i441] -> [i435 + i439, i436 + i440, 2 * i437 + i441]) ; w443 = tgather [1,1,2,2,1,1,2,2] (u442 ! [0, 0]) (\\[i513, i514, i515, i516, i517, i518, i519, i520] -> [rem (quot (16 * i513 + (16 * i514 + (8 * i515 + (4 * i516 + (4 * i517 + (4 * i518 + (2 * i519 + i520))))))) 8) 2, rem (quot (16 * i513 + (16 * i514 + (8 * i515 + (4 * i516 + (4 * i517 + (4 * i518 + (2 * i519 + i520))))))) 4) 2]) ; u491 = tscatter [1,1,4,4] (w324 * tscatter [1,1,2,2,1,1,2,4] (tscatter [2,1,1,2,2,1,1,2,2] (tscatter [1,1,2,2,1,1,2,2] (tscatter [2,1,2,2,1,1,2,2] (tsum (ttranspose [1,0] (w366 * w443))) (\\[i452, i453, i454, i455, i456, i457, i458] -> [ifB ((0 <=* i452 + i455 &&* 1 >* i452 + i455) &&* ((0 <=* i456 &&* 1 >* i456) &&* ((0 <=* i453 + i457 &&* 2 >* i453 + i457) &&* (0 <=* i454 + i458 &&* 2 >* i454 + i458)))) 0 1, i452, i453, i454, i455, i456, i457, i458]) ! [0]) (\\[i460, i461, i462, i463, i464, i465, i466] -> [i460 + i463, i464, i461 + i465, i462 + i466, 0, 0, rem (quot (tmaxIndex0 (tgather [4] (w342 ! [0]) (\\[i626] -> [rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i626))))))))))))) 64) 2, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i626))))))))))))) 32) 2, 0, 0, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i626))))))))))))) 16) 2, 0, 0, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i626))))))))))))) 8) 2, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i626))))))))))))) 4) 2, 0, 0, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i626))))))))))))) 2) 2, rem (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i626))))))))))))) 2]))) 2) 2, rem (tmaxIndex0 (tgather [4] (w342 ! [0]) (\\[i637] -> [rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i637))))))))))))) 64) 2, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i637))))))))))))) 32) 2, 0, 0, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i637))))))))))))) 16) 2, 0, 0, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i637))))))))))))) 8) 2, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i637))))))))))))) 4) 2, 0, 0, rem (quot (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i637))))))))))))) 2) 2, rem (128 * i460 + (64 * i461 + (32 * i462 + (32 * i463 + (32 * i464 + (16 * i465 + (16 * i460 + (16 * i463 + (16 * i464 + (8 * i461 + (8 * i465 + (4 * i462 + (4 * i466 + i637))))))))))))) 2]))) 2])) (\\[i467, i468, i469, i470, i471, i472, i473, i474] -> [ifB ((0 <=* i467 + i471 &&* 1 >* i467 + i471) &&* ((0 <=* i468 + i472 &&* 1 >* i468 + i472) &&* ((0 <=* 2 * i469 + i473 &&* 4 >* 2 * i469 + i473) &&* (0 <=* 2 * i470 + i474 &&* 4 >* 2 * i470 + i474)))) 0 1, i467, i468, i469, i470, i471, i472, i473, i474]) ! [0]) (\\[i476, i477, i478, i479, i480, i481, i482, i483] -> [i476, i477, i478, i479, i480, i481, i482, 2 * i479 + i483])) (\\[i484, i485, i486, i487, i488, i489, i490] -> [i484 + i488, i485 + i489, 2 * i486 + i490]) in (tscatter [1,1,2,2] (tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w306 * tgather [1,1,4,4,1,1,2,2] (u491 ! [0, 0]) (\\[i500, i501, i502, i503, i504, i505, i506, i507] -> [rem (quot (64 * i500 + (64 * i501 + (16 * i502 + (4 * i503 + (4 * i504 + (4 * i505 + (2 * i506 + i507))))))) 16) 4, rem (quot (64 * i500 + (64 * i501 + (16 * i502 + (4 * i503 + (4 * i504 + (4 * i505 + (2 * i506 + i507))))))) 4) 4])))))) (\\[i492, i493, i494, i495, i496] -> [ifB ((0 <=* i492 + i493 &&* 1 >* i492 + i493) &&* ((0 <=* i494 &&* 1 >* i494) &&* ((0 <=* i495 &&* 2 >* i495) &&* (0 <=* i496 &&* 2 >* i496)))) 0 1, i492, i493, i494, i495, i496]) ! [0]) (\\[i498, i499] -> [i498 + i499]), tsum (tsum (tsum (ttranspose [0,2,3,1] u491))), tscatter [1,1,2,2] (tscatter [2,1,1,1,2,2] (tsum (tsum (tsum (ttranspose [0,2,3,1] (w365 * w443))))) (\\[i444, i445, i446, i447, i448] -> [ifB ((0 <=* i444 + i445 &&* 1 >* i444 + i445) &&* ((0 <=* i446 &&* 1 >* i446) &&* ((0 <=* i447 &&* 2 >* i447) &&* (0 <=* i448 &&* 2 >* i448)))) 0 1, i444, i445, i446, i447, i448]) ! [0]) (\\[i450, i451] -> [i450 + i451]), tsum (tsum (tsum (ttranspose [0,2,3,1] u442))), tsum (ttranspose [2,1,0] (t407 * treplicate 1 m413)), tsum (ttranspose [1,0] m413), tsum (ttranspose [2,0,1] (treplicate 10 (m411 * m408)) * ttranspose [2,1,0] (treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\u2 v3 u4 v5 m6 v7 m8 v9 -> let w308 = treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,4,4] (tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 7.0)))))), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i660, i661, i662, i663, i664, i665] -> [ifB ((0 <=* i662 &&* 1 >* i662) &&* ((0 <=* i663 &&* 1 >* i663) &&* ((0 <=* i660 + i664 &&* 4 >* i660 + i664) &&* (0 <=* i661 + i665 &&* 4 >* i661 + i665)))) 0 1, i660, i661, i662, i663, i664, i665]) * tgather [4,4,1,1,2,2] (tfromList [treplicate 4 (treplicate 4 u2), treplicate 4 (treplicate 4 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i677, i678, i679, i680, i681, i682] -> [ifB ((0 <=* i679 &&* 1 >* i679) &&* ((0 <=* i680 &&* 1 >* i680) &&* ((0 <=* i681 &&* 2 >* i681) &&* (0 <=* i682 &&* 2 >* i682)))) 0 1, i677, i678, i679, i680, i681, i682])) (\\[i650, i651, i652, i653, i654] -> [rem (quot (64 * i651 + (64 * i652 + (16 * i653 + (4 * i654 + i650)))) 16) 4, rem (quot (64 * i651 + (64 * i652 + (16 * i653 + (4 * i654 + i650)))) 4) 4, 0, 0, rem (quot (64 * i651 + (64 * i652 + (16 * i653 + (4 * i654 + i650)))) 2) 2, rem (64 * i651 + (64 * i652 + (16 * i653 + (4 * i654 + i650)))) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 4 (treplicate 4 v3)))))))))) ; w342 = treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (tgather [1,1,2,2,1,1,2,2] (tfromList [tgather [1,1,2,2,1,1,2,2] (tgather [1,1,2,2,1,1,2,4] (tconst (fromList [2] [0.0,1.0])) (\\[i309, i310, i311, i312, i313, i314, i315, i316] -> [ifB (w308 ! [i309, i310, i311, i312, i313, i314, i315, i309 + i313, i310 + i314, 2 * i311 + i315, i316] <=* tconst 0.0) 0 1]) * tgather [1,1,2,2,1,1,2,4] w308 (\\[i317, i318, i319, i320, i321, i322, i323] -> [i317, i318, i319, i320, i321, i322, i323, i317 + i321, i318 + i322, 2 * i319 + i323])) (\\[i326, i327, i328, i329, i330, i331, i332, i333] -> [i326, i327, i328, i329, i330, i331, i332, 2 * i329 + i333]), treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i334, i335, i336, i337, i338, i339, i340, i341] -> [ifB ((0 <=* i334 + i338 &&* 1 >* i334 + i338) &&* ((0 <=* i335 + i339 &&* 1 >* i335 + i339) &&* ((0 <=* 2 * i336 + i340 &&* 4 >* 2 * i336 + i340) &&* (0 <=* 2 * i337 + i341 &&* 4 >* 2 * i337 + i341)))) 0 1, i334, i335, i336, i337, i338, i339, i340, i341]))))))) ; w367 = treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (tsum (tgather [4,1,1,2,2] (tgather [2,2,1,1,2,2] (tfromList [tgather [2,2,1,1,2,2] (w342 ! [0]) (\\[i345, i346, i347, i348, i349, i350] -> [i345, i346, i347, i348, i349, i347, i348, i345 + i349, i346 + i350, 0, 0, rem (quot (tmaxIndex0 (tgather [4] (w342 ! [0]) (\\[i693] -> [rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i693))))))))))) 64) 2, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i693))))))))))) 32) 2, 0, 0, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i693))))))))))) 16) 2, 0, 0, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i693))))))))))) 8) 2, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i693))))))))))) 4) 2, 0, 0, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i693))))))))))) 2) 2, rem (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i693))))))))))) 2]))) 2) 2, rem (tmaxIndex0 (tgather [4] (w342 ! [0]) (\\[i704] -> [rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i704))))))))))) 64) 2, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i704))))))))))) 32) 2, 0, 0, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i704))))))))))) 16) 2, 0, 0, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i704))))))))))) 8) 2, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i704))))))))))) 4) 2, 0, 0, rem (quot (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i704))))))))))) 2) 2, rem (64 * i345 + (32 * i346 + (32 * i347 + (32 * i348 + (16 * i349 + (16 * i347 + (16 * i348 + (8 * i345 + (8 * i349 + (4 * i346 + (4 * i350 + i704))))))))))) 2]))) 2]), treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i705, i706, i707, i708, i709, i710] -> [ifB ((0 <=* i707 &&* 1 >* i707) &&* ((0 <=* i708 &&* 1 >* i708) &&* ((0 <=* i705 + i709 &&* 2 >* i705 + i709) &&* (0 <=* i706 + i710 &&* 2 >* i706 + i710)))) 0 1, i705, i706, i707, i708, i709, i710]) * tgather [2,2,1,1,2,2] (tfromList [treplicate 2 (treplicate 2 u4), treplicate 2 (treplicate 2 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))]) (\\[i722, i723, i724, i725, i726, i727] -> [ifB ((0 <=* i724 &&* 1 >* i724) &&* ((0 <=* i725 &&* 1 >* i725) &&* ((0 <=* i726 &&* 2 >* i726) &&* (0 <=* i727 &&* 2 >* i727)))) 0 1, i722, i723, i724, i725, i726, i727])) (\\[i640, i641, i642, i643, i644] -> [rem (quot (16 * i641 + (16 * i642 + (8 * i643 + (4 * i644 + i640)))) 8) 2, rem (quot (16 * i641 + (16 * i642 + (8 * i643 + (4 * i644 + i640)))) 4) 2, 0, 0, rem (quot (16 * i641 + (16 * i642 + (8 * i643 + (4 * i644 + i640)))) 2) 2, rem (16 * i641 + (16 * i642 + (8 * i643 + (4 * i644 + i640)))) 2])) + ttranspose [0,3,1,2] (treplicate 1 (treplicate 2 (treplicate 2 v5)))))))))) ; w401 = tgather [1,1,1,1,1,1,2,2] (tfromList [tgather [1,1,1,1,1,1,2,2] (tgather [1,1,1,1,1,1,2,2] (tconst (fromList [2] [0.0,1.0])) (\\[i368, i369, i370, i371, i372, i373, i374, i375] -> [ifB (w367 ! [i368, i369, i370, i371, i372, i373, i374, i368 + i372, i369 + i373, 2 * i370 + i374, i375] <=* tconst 0.0) 0 1]) * tgather [1,1,1,1,1,1,2,2] w367 (\\[i376, i377, i378, i379, i380, i381, i382] -> [i376, i377, i378, i379, i380, i381, i382, i376 + i380, i377 + i381, 2 * i378 + i382])) (\\[i385, i386, i387, i388, i389, i390, i391, i392] -> [i385, i386, i387, i388, i389, i390, i391, 2 * i388 + i392]), treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 2 (treplicate 2 (tconst 0.0))))))))]) (\\[i393, i394, i395, i396, i397, i398, i399, i400] -> [ifB ((0 <=* i393 + i397 &&* 1 >* i393 + i397) &&* ((0 <=* i394 + i398 &&* 1 >* i394 + i398) &&* ((0 <=* 2 * i395 + i399 &&* 2 >* 2 * i395 + i399) &&* (0 <=* 2 * i396 + i400 &&* 2 >* 2 * i396 + i400)))) 0 1, i393, i394, i395, i396, i397, i398, i399, i400]) ; m408 = tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (w401 ! [0, 0, 0, 0, 0, 0, rem (quot (tmaxIndex0 (tgather [4] (w401 ! [0, 0, 0, 0, 0, 0]) (\\[i732] -> [rem (quot i732 2) 2, rem i732 2]))) 2) 2, rem (tmaxIndex0 (tgather [4] (w401 ! [0, 0, 0, 0, 0, 0]) (\\[i737] -> [rem (quot i737 2) 2, rem i737 2]))) 2]))))) + ttranspose [1,0] (treplicate 1 v7) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 10 (tgather [1,1] (tconst (fromList [2] [0.0,1.0])) (\\[i409, i410] -> [ifB (m408 ! [i409, i410] <=* tconst 0.0) 0 1]) * m408))) + ttranspose [1,0] (treplicate 1 v9)"
