{-# LANGUAGE ImpredicativeTypes #-}
module TestMnistRNNR
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

import           MnistData
import qualified MnistRnnRanked2

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNA
            , tensorADValMnistTestsRNNI
            , tensorADValMnistTestsRNNO
            , tensorMnistTestsPP
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor
mnistTestCaseRNNA
  :: forall ranked r.
     ( ranked ~ Flip OR.Array
     , ADReady ranked r, Random r, ADReady (ADVal ranked) r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            shapedToRanked $ fst
            $ randomVals @(MnistRnnRanked2.ADRnnMnistParametersShaped
                             (Flip OS.Array) width r)
                0.4 (mkStdGen 44)
      domainsInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (V.length domainsInit)
                        , show (sizeDomainsOD domainsInit) ]
      ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
      ftest miniBatchSize' mnist testParams =
        MnistRnnRanked2.rnnMnistTestR miniBatchSize' mnist
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
                   MnistRnnRanked2.rnnMnistLossFusedR
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
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
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

{-# SPECIALIZE mnistTestCaseRNNA
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNA :: TestTree
tensorADValMnistTestsRNNA = testGroup "RNN ADVal MNIST tests"
  [ mnistTestCaseRNNA "RNNA 1 epoch, 1 batch" 1 1 128 5 50
                       (0.8200000000000001 :: Double)
  , mnistTestCaseRNNA "RNNA artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNA "RNNA artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNA "RNNA 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCaseRNNI
  :: forall ranked r.
     ( ranked ~ Flip OR.Array
     , ADReady ranked r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            shapedToRanked $ fst
            $ randomVals @(MnistRnnRanked2.ADRnnMnistParametersShaped
                             (Flip OS.Array) width r)
                0.4 (mkStdGen 44)
      domainsInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (V.length domainsInit)
                        , show (sizeDomainsOD domainsInit) ]
      ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
      ftest miniBatchSize' mnist testParams =
        MnistRnnRanked2.rnnMnistTestR miniBatchSize' mnist
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
           ast = MnistRnnRanked2.rnnMnistLossFusedR
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
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
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

{-# SPECIALIZE mnistTestCaseRNNI
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNI :: TestTree
tensorADValMnistTestsRNNI = testGroup "RNN Intermediate MNIST tests"
  [ mnistTestCaseRNNI "RNNI 1 epoch, 1 batch" 1 1 128 5 50
                       (0.84 :: Double)
  , mnistTestCaseRNNI "RNNI artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNI "RNNI artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNI "RNNI 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCaseRNNO
  :: forall ranked r.
     ( ranked ~ Flip OR.Array, ADReady ranked r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNO prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
 -- TODO: use withKnownNat when we no longer support GHC 9.4
 case someNatVal $ toInteger width of
  Nothing -> error "impossible someNatVal error"
  Just (SomeNat @width _) ->
    let valsInitShaped
          :: MnistRnnRanked2.ADRnnMnistParametersShaped (Flip OS.Array) width r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        domainsInit = toDomains valsInitShaped  -- == toDomains valsInit
        valsInit :: MnistRnnRanked2.ADRnnMnistParameters ranked r
        valsInit = shapedToRanked valsInitShaped
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show width, show miniBatchSize
                          , show (V.length domainsInit)
                          , show (sizeDomainsOD domainsInit) ]
        ftest :: Int -> MnistDataBatchR r -> DomainsOD -> r
        ftest miniBatchSize' mnist testParams =
          MnistRnnRanked2.rnnMnistTestR miniBatchSize' mnist
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
       let envInit = extendEnvR varGlyph (tconstant $ astPrimalPart astGlyph)
                     $ extendEnvR varLabel (tconstant $ astPrimalPart astLabel)
                       EM.empty
           f = MnistRnnRanked2.rnnMnistLossFusedR
                 miniBatchSize (astPrimalPart astGlyph, astPrimalPart astLabel)
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
             unless (width < 10) $ do
               hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
               hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (DomainsOD, StateAdam) -> IO DomainsOD
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n !paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
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

{-# SPECIALIZE mnistTestCaseRNNO
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNO :: TestTree
tensorADValMnistTestsRNNO = testGroup "RNN Once MNIST tests"
  [ mnistTestCaseRNNO "RNNO 1 epoch, 1 batch" 1 1 128 5 500
                       (0.898 :: Double)
  , mnistTestCaseRNNO "RNNO artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNO "RNNO artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNO "RNNO 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for RNN MNIST tests"
  [ testCase "RNNOPP" testRNNOPP
  , testCase "RNNOPP2" testRNNOPP2
  ]

valsInitRNNOPP
  :: Int -> Int -> MnistRnnRanked2.ADRnnMnistParameters (Flip OR.Array) Double
valsInitRNNOPP out_width sizeMnistHeightI =
  ( ( Flip
      $ OR.fromList [out_width, sizeMnistHeightI]
                    (map fromIntegral [0 .. out_width * sizeMnistHeightI - 1])
    , Flip
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , Flip
      $ OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( Flip
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , Flip
      $ OR.fromList [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , Flip $ OR.fromList [out_width] (map fromIntegral [0 .. out_width - 1]) )
  , ( Flip
      $ OR.fromList [sizeMnistLabelInt, out_width]
                    (map fromIntegral [0 .. sizeMnistLabelInt * out_width - 1])
    , Flip
      $ OR.fromList [sizeMnistLabelInt]
                    (map fromIntegral [0 .. sizeMnistLabelInt - 1]) ) )

testRNNOPP :: Assertion
testRNNOPP = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 1
      sizeMnistWidthI = 1
      sizeMnistHeightI = 1
      blackGlyph :: AstPrimalPart Double 3
      blackGlyph = astPrimalPart
                   $ AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI
                   $ AstReplicate batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters AstRanked Double
              -> AstRanked Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifact6, _) = revDtFun True afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 m3 v4 m5 m6 v7 m8 v9 -> let m11 = treshape [2,1] (treplicate 2 (tconst 0.0)) ; t12 = ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))) ! [0])) ; m13 = tanh (ttranspose [1,0] (treplicate 1 v4) + tsum (ttranspose [2,1,0] (treplicate 1 m2) * t12) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (tslice 0 1 m11)))) ; t14 = ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))) ! [0])) ; m15 = tanh (ttranspose [1,0] (treplicate 1 v4) + tsum (ttranspose [2,1,0] (treplicate 1 m2) * t14) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (tslice 0 1 m11)))) ; m16 = tanh (ttranspose [1,0] (treplicate 1 v7) + tsum (ttranspose [2,1,0] (treplicate 1 m5) * ttranspose [1,0] (treplicate 1 m15)) + tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 (tslice 1 1 m11)))) ; t17 = ttranspose [1,0] (treplicate 10 (tslice 1 1 (tappend m13 m16))) ; m18 = tappend (treshape [1,1] (treplicate 1 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret))) (treshape [0,1] (treplicate 0 (tconst 0.0)))) ; m19 = (tconst (fromList [1,1] [1.0]) - m16 * m16) * tslice 1 1 m18 ; m20 = (tconst (fromList [1,1] [1.0]) - m15 * m15) * tsum (ttranspose [1,2,0] (treplicate 1 m5) * ttranspose [1,0] (treplicate 1 m19)) ; m21 = (tconst (fromList [1,1] [1.0]) - m13 * m13) * tslice 0 1 m18 in (tsum (ttranspose [2,1,0] (t12 * treplicate 1 m21)) + tsum (ttranspose [2,1,0] (t14 * treplicate 1 m20)), tsum (ttranspose [2,0,1] (treplicate 1 (tslice 0 1 m11)) * ttranspose [2,1,0] (treplicate 1 m21)) + tsum (ttranspose [2,0,1] (treplicate 1 (tslice 0 1 m11)) * ttranspose [2,1,0] (treplicate 1 m20)), tsum (ttranspose [1,0] m21) + tsum (ttranspose [1,0] m20), tsum (ttranspose [2,0,1] (treplicate 1 m15) * ttranspose [2,1,0] (treplicate 1 m19)), tsum (ttranspose [2,0,1] (treplicate 1 (tslice 1 1 m11)) * ttranspose [2,1,0] (treplicate 1 m19)), tsum (ttranspose [1,0] m19), tsum (ttranspose [2,1,0] (t17 * treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 m3 v4 m5 m6 v7 m8 v9 -> let m11 = treshape [2,1] (treplicate 2 (tconst 0.0)) ; t12 = ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))) ! [0])) ; m13 = tanh (ttranspose [1,0] (treplicate 1 v4) + tsum (ttranspose [2,1,0] (treplicate 1 m2) * t12) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (tslice 0 1 m11)))) ; t14 = ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))) ! [0])) ; m15 = tanh (ttranspose [1,0] (treplicate 1 v4) + tsum (ttranspose [2,1,0] (treplicate 1 m2) * t14) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (tslice 0 1 m11)))) ; m16 = tanh (ttranspose [1,0] (treplicate 1 v7) + tsum (ttranspose [2,1,0] (treplicate 1 m5) * ttranspose [1,0] (treplicate 1 m15)) + tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 (tslice 1 1 m11)))) ; t17 = ttranspose [1,0] (treplicate 10 (tslice 1 1 (tappend m13 m16))) in tsum (ttranspose [2,1,0] (treplicate 1 m8) * t17) + ttranspose [1,0] (treplicate 1 v9)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 m3 v4 m5 m6 v7 m8 v9 -> let m13 = tanh (ttranspose [1,0] (treplicate 1 v4) + tsum (ttranspose [2,1,0] (treplicate 1 m2) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))))) ; m15 = tanh (ttranspose [1,0] (treplicate 1 v4) + tsum (ttranspose [2,1,0] (treplicate 1 m2) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))))) ; m16 = tanh (ttranspose [1,0] (treplicate 1 v7) + tsum (ttranspose [2,1,0] (treplicate 1 m5) * ttranspose [1,0] (treplicate 1 m15)) + tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))))) ; m18 = tappend (treplicate 1 (treplicate 1 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 1 dret))) (treplicate 0 (treplicate 1 (tconst 0.0)))) ; m19 = (tconst (fromList [1,1] [1.0]) - m16 * m16) * tslice 1 1 m18 ; m20 = (tconst (fromList [1,1] [1.0]) - m15 * m15) * tsum (ttranspose [1,2,0] (treplicate 1 m5) * ttranspose [1,0] (treplicate 1 m19)) ; m21 = (tconst (fromList [1,1] [1.0]) - m13 * m13) * tslice 0 1 m18 in (tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 1 m21)) + tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 1 m20)), tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 1 m21)) + tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 1 m20)), tsum (ttranspose [1,0] m21) + tsum (ttranspose [1,0] m20), tsum (ttranspose [2,0,1] (treplicate 1 m15) * ttranspose [2,1,0] (treplicate 1 m19)), tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 1 m19)), tsum (ttranspose [1,0] m19), tsum (ttranspose [2,0,1] (treplicate 10 m16) * ttranspose [2,1,0] (treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 m3 v4 m5 m6 v7 m8 v9 -> tsum (ttranspose [2,1,0] (treplicate 1 m8) * ttranspose [1,0] (treplicate 10 (tanh (ttranspose [1,0] (treplicate 1 v7) + tsum (ttranspose [2,1,0] (treplicate 1 m5) * ttranspose [1,0] (treplicate 1 (tanh (ttranspose [1,0] (treplicate 1 v4) + tsum (ttranspose [2,1,0] (treplicate 1 m2) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0))))))))) + tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0))))))))) + ttranspose [1,0] (treplicate 1 v9)"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistWidthI = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstPrimalPart Double 3
      blackGlyph = astPrimalPart
                   $ AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI
                   $ AstReplicate batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters AstRanked Double
              -> AstRanked Double 2
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifact6, _) = revDtFun True afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 m3 v4 m5 m6 v7 m8 v9 -> let m12 = treshape [4,2] (treplicate 8 (tconst 0.0)) ; t13 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [0])) ; m14 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * t13) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m12)))) ; t15 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [0])) ; m16 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * t15) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m12)))) ; m17 = tanh (ttranspose [1,0] (treplicate 2 v7) + tsum (ttranspose [2,1,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m16)) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m12)))) ; m18 = tappend m14 m17 ; t19 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [1])) ; m20 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * t19) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m18)))) ; t21 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [1])) ; m22 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * t21) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m18)))) ; m23 = tanh (ttranspose [1,0] (treplicate 2 v7) + tsum (ttranspose [2,1,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m22)) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m18)))) ; t24 = ttranspose [1,0] (treplicate 10 (tslice 2 2 (tappend m20 m23))) ; m25 = tappend (treshape [2,2] (treplicate 4 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m8) * ttranspose [1,0] (treplicate 2 dret))) (treshape [0,2] (treplicate 0 (tconst 0.0)))) ; m26 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m23 * m23) * tslice 2 2 m25 ; m27 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m22 * m22) * tsum (ttranspose [1,2,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m26)) ; m28 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m20 * m20) * tslice 0 2 m25 ; m29 = tappend (treshape [0,2] (treplicate 0 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 m28))) (treshape [2,2] (treplicate 4 (tconst 0.0)))) + tappend (treshape [0,2] (treplicate 0 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 m27))) (treshape [2,2] (treplicate 4 (tconst 0.0)))) + tappend (treshape [2,2] (treplicate 4 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m26))) (treshape [0,2] (treplicate 0 (tconst 0.0)))) ; m30 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m17 * m17) * tslice 2 2 m29 ; m31 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * tsum (ttranspose [1,2,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m30)) ; m32 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * tslice 0 2 m29 in (tsum (ttranspose [2,1,0] (t13 * treplicate 2 m32)) + tsum (ttranspose [2,1,0] (t15 * treplicate 2 m31)) + tsum (ttranspose [2,1,0] (t19 * treplicate 2 m28)) + tsum (ttranspose [2,1,0] (t21 * treplicate 2 m27)), tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m12)) * ttranspose [2,1,0] (treplicate 2 m32)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m12)) * ttranspose [2,1,0] (treplicate 2 m31)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m18)) * ttranspose [2,1,0] (treplicate 2 m28)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m18)) * ttranspose [2,1,0] (treplicate 2 m27)), tsum (ttranspose [1,0] m32) + tsum (ttranspose [1,0] m31) + tsum (ttranspose [1,0] m28) + tsum (ttranspose [1,0] m27), tsum (ttranspose [2,0,1] (treplicate 2 m16) * ttranspose [2,1,0] (treplicate 2 m30)) + tsum (ttranspose [2,0,1] (treplicate 2 m22) * ttranspose [2,1,0] (treplicate 2 m26)), tsum (ttranspose [2,0,1] (treplicate 2 (tslice 2 2 m12)) * ttranspose [2,1,0] (treplicate 2 m30)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 2 2 m18)) * ttranspose [2,1,0] (treplicate 2 m26)), tsum (ttranspose [1,0] m30) + tsum (ttranspose [1,0] m26), tsum (ttranspose [2,1,0] (t24 * treplicate 2 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 m3 v4 m5 m6 v7 m8 v9 -> let m12 = treshape [4,2] (treplicate 8 (tconst 0.0)) ; t13 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [0])) ; m14 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * t13) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m12)))) ; t15 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [0])) ; m16 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * t15) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m12)))) ; m17 = tanh (ttranspose [1,0] (treplicate 2 v7) + tsum (ttranspose [2,1,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m16)) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m12)))) ; m18 = tappend m14 m17 ; t19 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [1])) ; m20 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * t19) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m18)))) ; t21 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [1])) ; m22 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * t21) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m18)))) ; m23 = tanh (ttranspose [1,0] (treplicate 2 v7) + tsum (ttranspose [2,1,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m22)) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m18)))) ; t24 = ttranspose [1,0] (treplicate 10 (tslice 2 2 (tappend m20 m23))) in tsum (ttranspose [2,1,0] (treplicate 2 m8) * t24) + ttranspose [1,0] (treplicate 2 v9)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 m3 v4 m5 m6 v7 m8 v9 -> let m14 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))))) ; m16 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))))) ; m17 = tanh (ttranspose [1,0] (treplicate 2 v7) + tsum (ttranspose [2,1,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m16)) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))))) ; m18 = tappend m14 m17 ; m20 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m18)))) ; m22 = tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m18)))) ; m23 = tanh (ttranspose [1,0] (treplicate 2 v7) + tsum (ttranspose [2,1,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m22)) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m18)))) ; m25 = tappend (treplicate 2 (treplicate 2 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m8) * ttranspose [1,0] (treplicate 2 dret))) (treplicate 0 (treplicate 2 (tconst 0.0)))) ; m26 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m23 * m23) * tslice 2 2 m25 ; m27 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m22 * m22) * tsum (ttranspose [1,2,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m26)) ; m28 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m20 * m20) * tslice 0 2 m25 ; m29 = tappend (treplicate 0 (treplicate 2 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 m28))) (treplicate 2 (treplicate 2 (tconst 0.0)))) + tappend (treplicate 0 (treplicate 2 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 m27))) (treplicate 2 (treplicate 2 (tconst 0.0)))) + tappend (treplicate 2 (treplicate 2 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m26))) (treplicate 0 (treplicate 2 (tconst 0.0)))) ; m30 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m17 * m17) * tslice 2 2 m29 ; m31 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m16 * m16) * tsum (ttranspose [1,2,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 m30)) ; m32 = (tconst (fromList [2,2] [1.0,1.0,1.0,1.0]) - m14 * m14) * tslice 0 2 m29 in (tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 2 m32)) + tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 2 m31)) + tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 2 m28)) + tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 2 m27)), tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 2 m32)) + tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 2 m31)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m18)) * ttranspose [2,1,0] (treplicate 2 m28)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m18)) * ttranspose [2,1,0] (treplicate 2 m27)), tsum (ttranspose [1,0] m32) + tsum (ttranspose [1,0] m31) + tsum (ttranspose [1,0] m28) + tsum (ttranspose [1,0] m27), tsum (ttranspose [2,0,1] (treplicate 2 m16) * ttranspose [2,1,0] (treplicate 2 m30)) + tsum (ttranspose [2,0,1] (treplicate 2 m22) * ttranspose [2,1,0] (treplicate 2 m26)), tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 2 m30)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 2 2 m18)) * ttranspose [2,1,0] (treplicate 2 m26)), tsum (ttranspose [1,0] m30) + tsum (ttranspose [1,0] m26), tsum (ttranspose [2,0,1] (treplicate 10 m23) * ttranspose [2,1,0] (treplicate 2 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 m3 v4 m5 m6 v7 m8 v9 -> let m18 = tappend (tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0))))))) (tanh (ttranspose [1,0] (treplicate 2 v7) + tsum (ttranspose [2,1,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 (tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0))))))))) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0))))))) in tsum (ttranspose [2,1,0] (treplicate 2 m8) * ttranspose [1,0] (treplicate 10 (tanh (ttranspose [1,0] (treplicate 2 v7) + tsum (ttranspose [2,1,0] (treplicate 2 m5) * ttranspose [1,0] (treplicate 2 (tanh (ttranspose [1,0] (treplicate 2 v4) + tsum (ttranspose [2,1,0] (treplicate 2 m2) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m18))))))) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m18))))))) + ttranspose [1,0] (treplicate 2 v9)"
