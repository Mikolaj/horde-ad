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
import           GHC.TypeLits (SomeNat (..), someNatVal)
import           Numeric.LinearAlgebra (Vector)
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.Domains
import HordeAd.Core.DualNumber (ADTensor, ADVal, dDnotShared)
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
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

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCaseRNNA
  :: forall r.
     ( ADTensor r, ADReady r, Random r, ADReady (ADVal r)
     , Primal (ADVal r) ~ r, Primal r ~ r, Value r ~ r, Floating (Vector r)
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , Shaped r ~ Flip OS.Array r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: MnistRnnRanked2.ADRnnMnistParameters r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            toRanked $ fst
            $ randomVals
                @(MnistRnnRanked2.ADRnnMnistParametersShaped width r)
                0.4 (mkStdGen 44)
      domainsInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (nParams valsInit)
                        , show (nScalars valsInit) ]
      ftest :: Int -> MnistDataBatchR r -> Domains r -> r
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
           runBatch :: (Domains r, StateAdam r)
                    -> (Int, [MnistDataR r])
                    -> IO (Domains r, StateAdam r)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADVal r) -> ADVal r
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
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
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
  :: forall r.
     ( ADTensor r, ADReady r, Random r, InterpretAst (ADVal r)
     , Value r ~ r, Value (ADVal r) ~ r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , Shaped r ~ Flip OS.Array r
     , Primal r ~ r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  let valsInit :: MnistRnnRanked2.ADRnnMnistParameters r
      valsInit =
        case someNatVal $ toInteger width of
          Nothing -> error "impossible someNatVal error"
          Just (SomeNat @width _) ->
            toRanked $ fst
            $ randomVals
                @(MnistRnnRanked2.ADRnnMnistParametersShaped width r)
                0.4 (mkStdGen 44)
      domainsInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show (nParams valsInit)
                        , show (nScalars valsInit) ]
      ftest :: Int -> MnistDataBatchR r -> Domains r -> r
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
           shapes1 = map dshape $ toListDoms $ domsR domainsInit
           (vars1, asts1) = unzip $ map funToAstD shapes1
           doms = mkDoms (dfromR $ AstConst $ OR.fromList @r @1 [0] [])
                         (fromListDoms asts1)
           (varGlyph, astGlyph) =
             funToAstR
               (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
               id
           (varLabel, astLabel) =
             funToAstR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
           ast :: Ast 0 r
           ast = tscalar
                 $ MnistRnnRanked2.rnnMnistLossFusedR
                     miniBatchSize (tprimalPart astGlyph, tprimalPart astLabel)
                                   (parseDomains valsInit doms)
           runBatch :: (Domains r, StateAdam r)
                    -> (Int, [MnistDataR r])
                    -> IO (Domains r, StateAdam r)
           runBatch !(!parameters, !stateAdam) (k, chunk) = do
             let f :: MnistDataBatchR r -> Domains (ADVal r) -> ADVal r
                 f (glyph, label) varInputs =
                   let env1 = foldr extendEnvD EM.empty
                              $ zip vars1 $ V.toList
                              $ V.zipWith (dDnotShared emptyADShare)
                                          (inputPrimal1 varInputs)
                                          (inputDual1 varInputs)
                       envMnist = extendEnvR varGlyph (tconst glyph)
                                  $ extendEnvR varLabel (tconst label) env1
                   in tunScalar $ snd $ interpretAst envMnist emptyMemo ast
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
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
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
  :: forall r.
     ( ADTensor r, ADReady r, Random r, Value r ~ r, InterpretAst r
     , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r
     , Shaped r ~ Flip OS.Array r
     , Primal r ~ r
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
          :: MnistRnnRanked2.ADRnnMnistParametersShaped width r
        valsInitShaped = fst $ randomVals 0.4 (mkStdGen 44)
        domainsInit = toDomains valsInitShaped  -- == toDomains valsInit
        valsInit :: MnistRnnRanked2.ADRnnMnistParameters r
        valsInit = toRanked valsInitShaped
        name = prefix ++ ": "
               ++ unwords [ show epochs, show maxBatches
                          , show width, show miniBatchSize
                          , show (nParams valsInit)
                          , show (nScalars valsInit) ]
        ftest :: Int -> MnistDataBatchR r -> Domains r -> r
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
           (varGlyph, astGlyph) =
             funToAstR
               (miniBatchSize :$ sizeMnistHeightInt :$ sizeMnistWidthInt :$ ZS)
               id
           (varLabel, astLabel) =
             funToAstR (miniBatchSize :$ sizeMnistLabelInt :$ ZS) id
           envInit = extendEnvR varGlyph (tconstant astGlyph)
                     $ extendEnvR varLabel (tconstant astLabel) EM.empty
           f = tscalar
               . MnistRnnRanked2.rnnMnistLossFusedR
                   miniBatchSize (tprimalPart astGlyph, tprimalPart astLabel)
           (((var0Again, varDtAgain, vars1Again), gradientRaw, primal), _) =
             revDtInit f valsInit envInit domainsInit
           gradient = simplifyAstDomains6 gradientRaw
           vars1AndInputAgain =
             vars1Again
             ++ [AstDynamicVarName varGlyph, AstDynamicVarName varLabel]
           vars = (var0Again, varDtAgain, vars1AndInputAgain)
           go :: [MnistDataBatchR r] -> (Domains r, StateAdam r)
              -> (Domains r, StateAdam r)
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) !(!parameters, !stateAdam) =
             let glyphD = dfromR $ tconst glyph
                 labelD = dfromR $ tconst label
                 parametersAndInput =
                   concatDomsR [parameters, fromListDoms [glyphD, labelD]]
                 gradientDomain =
                   fst $ revAstOnDomainsEval (vars, gradient, primal)
                                             parametersAndInput Nothing
             in go rest (updateWithGradientAdam defaultArgsAdam stateAdam
                                                parameters gradientDomain)
           runBatch :: (Domains r, StateAdam r)
                    -> (Int, [MnistDataR r])
                    -> IO (Domains r, StateAdam r)
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
       let runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
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
  :: Int -> Int -> MnistRnnRanked2.ADRnnMnistParameters Double
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
      blackGlyph :: AstPrimalPartRanked Double 3
      blackGlyph = AstPrimalPart
                   $ AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI
                   $ AstReplicate batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (Ast0 Double)
              -> TensorOf 2 (Ast0 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifact6, _) = revDtFun afcnn2T (valsInitRNNOPP 1 sizeMnistHeightI)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret m3 m4 v5 m6 m7 v8 m9 v10 -> let m12 = treshape [2,1] (treplicate 2 (tconst 0.0)) ; t13 = ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))) ! [0])) ; m14 = tanh (ttranspose [1,0] (treplicate 1 v5) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * t13) + tsum (ttranspose [2,1,0] (treplicate 1 m4) * ttranspose [1,0] (treplicate 1 (tslice 0 1 m12)))) ; t15 = ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))) ! [0])) ; m16 = tanh (ttranspose [1,0] (treplicate 1 v5) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * t15) + tsum (ttranspose [2,1,0] (treplicate 1 m4) * ttranspose [1,0] (treplicate 1 (tslice 0 1 m12)))) ; m17 = tanh (ttranspose [1,0] (treplicate 1 v8) + tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 m16)) + tsum (ttranspose [2,1,0] (treplicate 1 m7) * ttranspose [1,0] (treplicate 1 (tslice 1 1 m12)))) ; t18 = ttranspose [1,0] (treplicate 10 (tslice 1 1 (tappend m14 m17))) ; m19 = tappend (treshape [1,1] (treplicate 1 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 1 m9) * ttranspose [1,0] (treplicate 1 dret))) (treshape [0,1] (treplicate 0 (tconst 0.0)))) ; m20 = (treshape [1,1] (treplicate 1 (tconst 1.0)) - m17 * m17) * tslice 1 1 m19 ; m21 = (treshape [1,1] (treplicate 1 (tconst 1.0)) - m16 * m16) * tsum (ttranspose [1,2,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 m20)) ; m22 = (treshape [1,1] (treplicate 1 (tconst 1.0)) - m14 * m14) * tslice 0 1 m19 in (tfromList [], tsum (ttranspose [2,1,0] (t13 * treplicate 1 m22)) + tsum (ttranspose [2,1,0] (t15 * treplicate 1 m21)), tsum (ttranspose [2,0,1] (treplicate 1 (tslice 0 1 m12)) * ttranspose [2,1,0] (treplicate 1 m22)) + tsum (ttranspose [2,0,1] (treplicate 1 (tslice 0 1 m12)) * ttranspose [2,1,0] (treplicate 1 m21)), tsum (ttranspose [1,0] m22) + tsum (ttranspose [1,0] m21), tsum (ttranspose [2,0,1] (treplicate 1 m16) * ttranspose [2,1,0] (treplicate 1 m20)), tsum (ttranspose [2,0,1] (treplicate 1 (tslice 1 1 m12)) * ttranspose [2,1,0] (treplicate 1 m20)), tsum (ttranspose [1,0] m20), tsum (ttranspose [2,1,0] (t18 * treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 m3 m4 v5 m6 m7 v8 m9 v10 -> let m12 = treshape [2,1] (treplicate 2 (tconst 0.0)) ; m13 = ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))) ! [0])) ; m14 = tanh (ttranspose [1,0] (treplicate 1 v5) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * t13) + tsum (ttranspose [2,1,0] (treplicate 1 m4) * ttranspose [1,0] (treplicate 1 (tslice 0 1 m12)))) ; m15 = ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))) ! [0])) ; m16 = tanh (ttranspose [1,0] (treplicate 1 v5) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * t15) + tsum (ttranspose [2,1,0] (treplicate 1 m4) * ttranspose [1,0] (treplicate 1 (tslice 0 1 m12)))) ; m17 = tanh (ttranspose [1,0] (treplicate 1 v8) + tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 m16)) + tsum (ttranspose [2,1,0] (treplicate 1 m7) * ttranspose [1,0] (treplicate 1 (tslice 1 1 m12)))) ; m18 = ttranspose [1,0] (treplicate 10 (tslice 1 1 (tappend m14 m17))) in tsum (ttranspose [2,1,0] (treplicate 1 m9) * t18) + ttranspose [1,0] (treplicate 1 v10)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret m3 m4 v5 m6 m7 v8 m9 v10 -> let m14 = tanh (ttranspose [1,0] (treplicate 1 v5) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 1 m4) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))))) ; m16 = tanh (ttranspose [1,0] (treplicate 1 v5) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 1 m4) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))))) ; m17 = tanh (ttranspose [1,0] (treplicate 1 v8) + tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 m16)) + tsum (ttranspose [2,1,0] (treplicate 1 m7) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))))) ; m19 = tappend (tconstant (treplicate 1 (treplicate 1 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (treplicate 1 m9) * ttranspose [1,0] (treplicate 1 dret))) (tconstant (treplicate 0 (treplicate 1 (tconst 0.0))))) ; m20 = (tconstant (treplicate 1 (treplicate 1 (tconst 1.0))) - m17 * m17) * tslice 1 1 m19 ; m21 = (tconstant (treplicate 1 (treplicate 1 (tconst 1.0))) - m16 * m16) * tsum (ttranspose [1,2,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 m20)) ; m22 = (tconstant (treplicate 1 (treplicate 1 (tconst 1.0))) - m14 * m14) * tslice 0 1 m19 in (tfromList [], tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 1 m22)) + tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 1 m21)), tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 1 m22)) + tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 1 m21)), tsum (ttranspose [1,0] m22) + tsum (ttranspose [1,0] m21), tsum (ttranspose [2,0,1] (treplicate 1 m16) * ttranspose [2,1,0] (treplicate 1 m20)), tsum (ttranspose [2,0,1] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 1 m20)), tsum (ttranspose [1,0] m20), tsum (ttranspose [2,0,1] (treplicate 10 m17) * ttranspose [2,1,0] (treplicate 1 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 m3 m4 v5 m6 m7 v8 m9 v10 -> tsum (ttranspose [2,1,0] (treplicate 1 m9) * ttranspose [1,0] (treplicate 10 (tanh (ttranspose [1,0] (treplicate 1 v8) + tsum (ttranspose [2,1,0] (treplicate 1 m6) * ttranspose [1,0] (treplicate 1 (tanh (ttranspose [1,0] (treplicate 1 v5) + tsum (ttranspose [2,1,0] (treplicate 1 m3) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 1 m4) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0))))))))) + tsum (ttranspose [2,1,0] (treplicate 1 m7) * ttranspose [1,0] (treplicate 1 (treplicate 1 (treplicate 1 (tconst 0.0))))))))) + ttranspose [1,0] (treplicate 1 v10)"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistWidthI = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstPrimalPartRanked Double 3
      blackGlyph = AstPrimalPart
                   $ AstReplicate sizeMnistWidthI
                   $ AstReplicate sizeMnistHeightI
                   $ AstReplicate batch_size 7
      afcnn2T :: MnistRnnRanked2.ADRnnMnistParameters (Ast0 Double)
              -> TensorOf 2 (Ast0 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      (artifact6, _) = revDtFun afcnn2T (valsInitRNNOPP 2 sizeMnistHeightI)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret m3 m4 v5 m6 m7 v8 m9 v10 -> let m13 = treshape [4,2] (treplicate 8 (tconst 0.0)) ; t14 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [0])) ; m15 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * t14) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m13)))) ; t16 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [0])) ; m17 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * t16) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m13)))) ; m18 = tanh (ttranspose [1,0] (treplicate 2 v8) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m17)) + tsum (ttranspose [2,1,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m13)))) ; m19 = tappend m15 m18 ; t20 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [1])) ; m21 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * t20) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m19)))) ; t22 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [1])) ; m23 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * t22) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m19)))) ; m24 = tanh (ttranspose [1,0] (treplicate 2 v8) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m23)) + tsum (ttranspose [2,1,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m19)))) ; t25 = ttranspose [1,0] (treplicate 10 (tslice 2 2 (tappend m21 m24))) ; m26 = tappend (treshape [2,2] (treplicate 4 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m9) * ttranspose [1,0] (treplicate 2 dret))) (treshape [0,2] (treplicate 0 (tconst 0.0)))) ; m27 = (treshape [2,2] (treplicate 4 (tconst 1.0)) - m24 * m24) * tslice 2 2 m26 ; m28 = (treshape [2,2] (treplicate 4 (tconst 1.0)) - m23 * m23) * tsum (ttranspose [1,2,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m27)) ; m29 = (treshape [2,2] (treplicate 4 (tconst 1.0)) - m21 * m21) * tslice 0 2 m26 ; m30 = tappend (treshape [0,2] (treplicate 0 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 m29))) (treshape [2,2] (treplicate 4 (tconst 0.0)))) + tappend (treshape [0,2] (treplicate 0 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 m28))) (treshape [2,2] (treplicate 4 (tconst 0.0)))) + tappend (treshape [2,2] (treplicate 4 (tconst 0.0))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 m27))) (treshape [0,2] (treplicate 0 (tconst 0.0)))) ; m31 = (treshape [2,2] (treplicate 4 (tconst 1.0)) - m18 * m18) * tslice 2 2 m30 ; m32 = (treshape [2,2] (treplicate 4 (tconst 1.0)) - m17 * m17) * tsum (ttranspose [1,2,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m31)) ; m33 = (treshape [2,2] (treplicate 4 (tconst 1.0)) - m15 * m15) * tslice 0 2 m30 in (tfromList [], tsum (ttranspose [2,1,0] (t14 * treplicate 2 m33)) + tsum (ttranspose [2,1,0] (t16 * treplicate 2 m32)) + tsum (ttranspose [2,1,0] (t20 * treplicate 2 m29)) + tsum (ttranspose [2,1,0] (t22 * treplicate 2 m28)), tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m13)) * ttranspose [2,1,0] (treplicate 2 m33)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m13)) * ttranspose [2,1,0] (treplicate 2 m32)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m19)) * ttranspose [2,1,0] (treplicate 2 m29)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m19)) * ttranspose [2,1,0] (treplicate 2 m28)), tsum (ttranspose [1,0] m33) + tsum (ttranspose [1,0] m32) + tsum (ttranspose [1,0] m29) + tsum (ttranspose [1,0] m28), tsum (ttranspose [2,0,1] (treplicate 2 m17) * ttranspose [2,1,0] (treplicate 2 m31)) + tsum (ttranspose [2,0,1] (treplicate 2 m23) * ttranspose [2,1,0] (treplicate 2 m27)), tsum (ttranspose [2,0,1] (treplicate 2 (tslice 2 2 m13)) * ttranspose [2,1,0] (treplicate 2 m31)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 2 2 m19)) * ttranspose [2,1,0] (treplicate 2 m27)), tsum (ttranspose [1,0] m31) + tsum (ttranspose [1,0] m27), tsum (ttranspose [2,1,0] (t25 * treplicate 2 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 m3 m4 v5 m6 m7 v8 m9 v10 -> let m13 = treshape [4,2] (treplicate 8 (tconst 0.0)) ; m14 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [0])) ; m15 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * t14) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m13)))) ; m16 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [0])) ; m17 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * t16) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m13)))) ; m18 = tanh (ttranspose [1,0] (treplicate 2 v8) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m17)) + tsum (ttranspose [2,1,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m13)))) ; m19 = tappend m15 m18 ; m20 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [1])) ; m21 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * t20) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m19)))) ; m22 = ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))) ! [1])) ; m23 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * t22) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m19)))) ; m24 = tanh (ttranspose [1,0] (treplicate 2 v8) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m23)) + tsum (ttranspose [2,1,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m19)))) ; m25 = ttranspose [1,0] (treplicate 10 (tslice 2 2 (tappend m21 m24))) in tsum (ttranspose [2,1,0] (treplicate 2 m9) * t25) + ttranspose [1,0] (treplicate 2 v10)"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret m3 m4 v5 m6 m7 v8 m9 v10 -> let m15 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))))) ; m17 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))))) ; m18 = tanh (ttranspose [1,0] (treplicate 2 v8) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m17)) + tsum (ttranspose [2,1,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))))) ; m19 = tappend m15 m18 ; m21 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m19)))) ; m23 = tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m19)))) ; m24 = tanh (ttranspose [1,0] (treplicate 2 v8) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m23)) + tsum (ttranspose [2,1,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m19)))) ; m26 = tappend (tconstant (treplicate 2 (treplicate 2 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m9) * ttranspose [1,0] (treplicate 2 dret))) (tconstant (treplicate 0 (treplicate 2 (tconst 0.0))))) ; m27 = (tconstant (treplicate 2 (treplicate 2 (tconst 1.0))) - m24 * m24) * tslice 2 2 m26 ; m28 = (tconstant (treplicate 2 (treplicate 2 (tconst 1.0))) - m23 * m23) * tsum (ttranspose [1,2,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m27)) ; m29 = (tconstant (treplicate 2 (treplicate 2 (tconst 1.0))) - m21 * m21) * tslice 0 2 m26 ; m30 = tappend (tconstant (treplicate 0 (treplicate 2 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 m29))) (tconstant (treplicate 2 (treplicate 2 (tconst 0.0))))) + tappend (tconstant (treplicate 0 (treplicate 2 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 m28))) (tconstant (treplicate 2 (treplicate 2 (tconst 0.0))))) + tappend (tconstant (treplicate 2 (treplicate 2 (tconst 0.0)))) (tappend (tsum (ttranspose [1,2,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 m27))) (tconstant (treplicate 0 (treplicate 2 (tconst 0.0))))) ; m31 = (tconstant (treplicate 2 (treplicate 2 (tconst 1.0))) - m18 * m18) * tslice 2 2 m30 ; m32 = (tconstant (treplicate 2 (treplicate 2 (tconst 1.0))) - m17 * m17) * tsum (ttranspose [1,2,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 m31)) ; m33 = (tconstant (treplicate 2 (treplicate 2 (tconst 1.0))) - m15 * m15) * tslice 0 2 m30 in (tfromList [], tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 2 m33)) + tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 2 m32)) + tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 2 m29)) + tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0)))) * ttranspose [2,1,0] (treplicate 2 m28)), tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 2 m33)) + tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 2 m32)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m19)) * ttranspose [2,1,0] (treplicate 2 m29)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 0 2 m19)) * ttranspose [2,1,0] (treplicate 2 m28)), tsum (ttranspose [1,0] m33) + tsum (ttranspose [1,0] m32) + tsum (ttranspose [1,0] m29) + tsum (ttranspose [1,0] m28), tsum (ttranspose [2,0,1] (treplicate 2 m17) * ttranspose [2,1,0] (treplicate 2 m31)) + tsum (ttranspose [2,0,1] (treplicate 2 m23) * ttranspose [2,1,0] (treplicate 2 m27)), tsum (ttranspose [2,0,1] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0)))) * ttranspose [2,1,0] (treplicate 2 m31)) + tsum (ttranspose [2,0,1] (treplicate 2 (tslice 2 2 m19)) * ttranspose [2,1,0] (treplicate 2 m27)), tsum (ttranspose [1,0] m31) + tsum (ttranspose [1,0] m27), tsum (ttranspose [2,0,1] (treplicate 10 m24) * ttranspose [2,1,0] (treplicate 2 dret)), tsum (ttranspose [1,0] dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 m3 m4 v5 m6 m7 v8 m9 v10 -> let m19 = tappend (tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0))))))) (tanh (ttranspose [1,0] (treplicate 2 v8) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0))))))))) + tsum (ttranspose [2,1,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 0.0))))))) in tsum (ttranspose [2,1,0] (treplicate 2 m9) * ttranspose [1,0] (treplicate 10 (tanh (ttranspose [1,0] (treplicate 2 v8) + tsum (ttranspose [2,1,0] (treplicate 2 m6) * ttranspose [1,0] (treplicate 2 (tanh (ttranspose [1,0] (treplicate 2 v5) + tsum (ttranspose [2,1,0] (treplicate 2 m3) * ttranspose [1,0] (treplicate 2 (treplicate 2 (treplicate 2 (tconst 7.0))))) + tsum (ttranspose [2,1,0] (treplicate 2 m4) * ttranspose [1,0] (treplicate 2 (tslice 0 2 m19))))))) + tsum (ttranspose [2,1,0] (treplicate 2 m7) * ttranspose [1,0] (treplicate 2 (tslice 2 2 m19))))))) + ttranspose [1,0] (treplicate 2 v10)"
