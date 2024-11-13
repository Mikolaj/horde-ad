module TestMnistFCNNR ( testTrees ) where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (Nat, SomeNat (..), someNatVal)

import           HordeAd
import           HordeAd.Core.Adaptor
import           HordeAd.Core.AstEnv
import           HordeAd.Core.AstFreshId (funToAstIOR)
import           HordeAd.Core.TensorADVal (ADValClown)
import           HordeAd.External.OptimizerTools
import           MnistData
import qualified MnistFcnnRanked2

testTrees :: [IO ()]
testTrees = [ mnistTestCase2VTA
            , mnistTestCase2VTA
            , mnistTestCase2VTI 2 5 500
                       (0.884 :: Float)
            , mnistTestCase2VTI 4 1 499
                       (0.7464929859719439 :: Double)
            , mnistTestCase2VTI 0 0.02 500
                       (1 :: Float)
            , mnistTestCase2VTO 4 2 1 499
            , mnistTestCase2VTO 0 100 0.02 500
            ]

mnistTestCase2VTA :: forall ranked. IO ()
mnistTestCase2VTA = do
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters (Flip OR.Array) Double
      valsInit = undefined
      runBatch :: DomainsOD -> [MnistData Double] -> IO DomainsOD
      runBatch _ chunk = do
        let f :: MnistData Double -> Domains (ADValClown OD.Array)
              -> ADVal (Flip OR.Array) Double 0
            f _ adinputs =
              MnistFcnnRanked2.afcnnMnistLoss2
                undefined (parseDomains valsInit adinputs)
        return $ fst $ sgd undefined f chunk undefined
      chunks = chunksOf undefined undefined
  res <- foldM runBatch undefined chunks
  return ()

mnistTestCase2VTI
  :: forall ranked r. ranked ~ Flip OR.Array
  => Int -> Double -> Int -> r -> IO ()
mnistTestCase2VTI maxBatches gamma batchSize _ = do
  (varGlyph, _, _) <-
    funToAstIOR (singletonShape sizeMnistGlyphInt) id
  (varLabel, _, _) <-
    funToAstIOR (singletonShape sizeMnistLabelInt) id
  let ast :: AstRanked PrimalSpan Double 0
      ast = undefined
  let runBatch :: DomainsOD -> [MnistData Double] -> IO DomainsOD
      runBatch !domains chunk = do
        let f :: MnistData Double -> Domains (ADValClown OD.Array)
              -> ADVal ranked Double 0
            f (glyph, label) varInputs =
              let env = foldr extendEnvDR EM.empty
                        $ zip undefined $ V.toList varInputs
                  envMnist =
                    extendEnvR varGlyph
                      (tconst $ OR.fromVector [sizeMnistGlyphInt] glyph)
                    $ extendEnvR varLabel
                        (tconst $ OR.fromVector [sizeMnistLabelInt] label)
                        env
              in interpretAst envMnist ast
            res = fst $ sgd gamma f chunk domains
        return res
      chunks = take maxBatches $ chunksOf batchSize undefined
  res <- foldM runBatch undefined chunks
  return ()

mnistTestCase2VTO
  :: Int -> Int -> Double -> Int -> IO ()
mnistTestCase2VTO maxBatches widthHidden2 gamma batchSize =
 case someNatVal $ toInteger widthHidden2 of
   Nothing -> error "impossible someNatVal error"
   Just (SomeNat _) -> do
    let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters (Flip OR.Array) Double
        valsInit = undefined
        ftest :: [MnistData Double] -> DomainsOD -> Double
        ftest = MnistFcnnRanked2.afcnnMnistTest2 undefined
    (varGlyph, varGlyphD, astGlyph) <-
      funToAstIOR (singletonShape sizeMnistGlyphInt) id
    (varLabel, varLabelD, astLabel) <-
      funToAstIOR (singletonShape sizeMnistLabelInt) id
    let envInit = extendEnvR varGlyph (tconstant astGlyph)
                  $ extendEnvR varLabel (tconstant astLabel)
                    EM.empty
        f = MnistFcnnRanked2.afcnnMnistLoss2TensorData @(AstRanked FullSpan)
              (tconstant astGlyph, tconstant astLabel)
        g domains = f $ parseDomains valsInit domains
        (((varDtAgain, vars1Again), gradientRaw, primal, sh), _) =
          revProduceArtifact False g envInit undefined
        gradient = simplifyAstDomains6 gradientRaw
        vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
        vars = (varDtAgain, vars1AndInputAgain)
        go :: [MnistData Double] -> DomainsOD -> DomainsOD
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let glyphD = DynamicExists
                       $ OD.fromVector [sizeMnistGlyphInt] glyph
              labelD = DynamicExists
                       $ OD.fromVector [sizeMnistLabelInt] label
              parametersAndInput =
                V.concat [parameters, V.fromList [glyphD, labelD]]
              gradientDomain =
                fst $ revEvalArtifact @Nat @AstRanked
                                      (vars, gradient, primal, sh)
                                      parametersAndInput Nothing
          in go rest (updateWithGradient gamma parameters gradientDomain)
    let runBatch :: DomainsOD -> [MnistData Double] -> IO DomainsOD
        runBatch !domains chunk =
          return $ go chunk domains
        chunks = take maxBatches $ chunksOf batchSize undefined
    res <- foldM runBatch undefined chunks
    let !testErrorFinal = ftest undefined res
    return ()
