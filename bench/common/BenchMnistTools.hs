{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | A set of benchmarks using fully connected MNIST neural networks.
module BenchMnistTools where

import Prelude

import Criterion.Main
import Data.List.Index (imap)
import Data.Vector.Generic qualified as V
import GHC.TypeLits (SomeNat (..), someNatVal)
import Numeric.LinearAlgebra qualified as LA
import System.Random

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.OpsAst (revProduceArtifact)
import HordeAd.Core.OpsConcrete ()
import HordeAd.External.OptimizerTools

import Data.Array.Nested (pattern (:$:), pattern ZSR)
import Data.Array.Nested qualified as Nested

import MnistData
import MnistFcnnRanked1 qualified
import MnistFcnnRanked2 qualified
-- * Using lists of vectors, which is rank 1

type XParams widthHidden widthHidden2 r =
  X (MnistFcnnRanked1.ADFcnnMnist1Parameters RepN widthHidden widthHidden2 r)

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTrainBench1VTA
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTrainBench1VTA prefix widthHiddenInt widthHidden2Int
                    gamma batchSize xs =
  withSNat widthHiddenInt $ \(widthHiddenSNat :: SNat widthHidden) ->
  withSNat widthHidden2Int $ \(widthHidden2SNat :: SNat widthHidden2) ->
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r)) (SNat @widthHidden)) $
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[widthHidden] r)) (SNat @widthHidden2)) $
  withKnownSTK
    (adSTK $ stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r))
                        (SNat @widthHidden)) $
  withKnownSTK
    (adSTK $ stkOfListR (knownSTK @(TKS '[widthHidden] r))
                        (SNat @widthHidden2)) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    RepN widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: RepN (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @RepN valsInit
  in do
    let f :: MnistDataLinearR r
          -> ADVal RepN (XParams widthHidden widthHidden2 r)
          -> ADVal RepN (TKR 0 r)
        f mnist adinputs =
          MnistFcnnRanked1.afcnnMnistLoss1
            widthHiddenSNat widthHidden2SNat
            mnist (fromTarget adinputs)
        chunk = take batchSize xs
        grad c = fst $ sgd gamma f c targetInit
        name =
          prefix
          ++ unwords
               [ "v" ++ show (twidth @RepN
                              $ knownSTK @(XParams widthHidden widthHidden2 r))
               , "m0" ++ " =" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf grad chunk

mnistTestBench1VTA
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTestBench1VTA prefix widthHiddenInt widthHidden2Int
                   _gamma batchSize xs =
  withSNat widthHiddenInt $ \(widthHiddenSNat :: SNat widthHidden) ->
  withSNat widthHidden2Int $ \(widthHidden2SNat :: SNat widthHidden2) ->
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r)) (SNat @widthHidden)) $
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[widthHidden] r)) (SNat @widthHidden2)) $
  withKnownSTK
    (adSTK $ stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r))
                        (SNat @widthHidden)) $
  withKnownSTK
    (adSTK $ stkOfListR (knownSTK @(TKS '[widthHidden] r))
                        (SNat @widthHidden2)) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    RepN widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: RepN (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @RepN valsInit
      ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters
                 RepN widthHidden widthHidden2 r
            -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 widthHiddenSNat widthHidden2SNat
  in do
    let chunk = take batchSize xs
        score c = ftest c valsInit
        name =
          "test " ++ prefix
          ++ unwords
               [ "v" ++ show (twidth @RepN
                              $ knownSTK @(XParams widthHidden widthHidden2 r))
               , "m0" ++ " =" ++ show (tsize knownSTK targetInit) ]
    bench name $ whnf score chunk

mnistBGroup1VTA :: [MnistData Double] -> Int -> Benchmark
mnistBGroup1VTA xs0 chunkLength =
  env (return $ map mkMnistDataLinearR $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 1 VTA MNIST nn with samples: "
          ++ show chunkLength) $
    (if chunkLength <= 1000
     then
       [ mnistTestBench1VTA "30|10 " 30 10 0.02 chunkLength xs
           -- toy width
       , mnistTrainBench1VTA "30|10 " 30 10 0.02 chunkLength xs
       , mnistTestBench1VTA "300|100 " 300 100 0.02 chunkLength xs
           -- ordinary width
       , mnistTrainBench1VTA "300|100 " 300 100 0.02 chunkLength xs
       ]
     else
       [])
    ++ [ mnistTestBench1VTA "500|150 " 500 150 0.02 chunkLength xs
           -- another common width
       , mnistTrainBench1VTA "500|150 " 500 150 0.02 chunkLength xs
       ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTrainBench1VTO
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTrainBench1VTO prefix widthHiddenInt widthHidden2Int
                    gamma batchSize xs =
  withSNat widthHiddenInt $ \(widthHiddenSNat :: SNat widthHidden) ->
  withSNat widthHidden2Int $ \(widthHidden2SNat :: SNat widthHidden2) ->
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r)) (SNat @widthHidden)) $
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[widthHidden] r)) (SNat @widthHidden2)) $
  withKnownSTK
    (adSTK $ stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r))
                        (SNat @widthHidden)) $
  withKnownSTK
    (adSTK $ stkOfListR (knownSTK @(TKS '[widthHidden] r))
                        (SNat @widthHidden2)) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    RepN widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: RepN (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @RepN valsInit
      ftk = tftk @RepN (knownSTK @(XParams widthHidden widthHidden2 r))
                       targetInit
  in do
    let ftkData = FTKProduct (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar)
                             (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar)
        f :: ( MnistFcnnRanked1.ADFcnnMnist1Parameters
                 (AstTensor AstMethodLet FullSpan)
                 widthHidden widthHidden2 r
             , ( AstTensor AstMethodLet FullSpan (TKR 1 r)
               , AstTensor AstMethodLet FullSpan (TKR 1 r) ) )
          -> AstTensor AstMethodLet FullSpan (TKR 0 r)
        f = \ (pars, (glyphR, labelR)) ->
          MnistFcnnRanked1.afcnnMnistLoss1TensorData
            widthHiddenSNat widthHidden2SNat
            (glyphR, labelR) pars
        (artRaw, _) = revArtifactAdapt False f (FTKProduct ftk ftkData)
        art = simplifyArtifactGradient artRaw
        go :: [MnistDataLinearR r]
           -> RepN (XParams widthHidden widthHidden2 r)
           -> RepN (XParams widthHidden widthHidden2 r)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ fst
                         $ revEvalArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma parameters gradient)
        chunk = take batchSize xs
        grad c = go c targetInit
        name =
          prefix
          ++ unwords
               [ "v" ++ show (twidth @RepN
                              $ knownSTK @(XParams widthHidden widthHidden2 r))
               , "m0" ++ " =" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf grad chunk

mnistTestBench1VTO
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTestBench1VTO = mnistTestBench1VTA

mnistBGroup1VTO :: [MnistData Double] -> Int -> Benchmark
mnistBGroup1VTO xs0 chunkLength =
  env (return $ map mkMnistDataLinearR $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 1 VTO MNIST nn with samples: "
          ++ show chunkLength) $
    (if chunkLength <= 1000
     then
       [ mnistTestBench1VTO "30|10 " 30 10 0.02 chunkLength xs
           -- toy width
       , mnistTrainBench1VTO "30|10 " 30 10 0.02 chunkLength xs
       , mnistTestBench1VTO "300|100 " 300 100 0.02 chunkLength xs
           -- ordinary width
       , mnistTrainBench1VTO "300|100 " 300 100 0.02 chunkLength xs
       ]
     else
       [])
    ++ [ mnistTestBench1VTO "500|150 " 500 150 0.02 chunkLength xs
           -- another common width
       , mnistTrainBench1VTO "500|150 " 500 150 0.02 chunkLength xs
       ]

{-
-- * Using matrices, which is rank 2

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTrainBench2VTA :: forall target r. (target ~ RepN, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench2VTA extraPrefix chunkLength testData widthHidden widthHidden2
                    gamma = do
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters target r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
                $ randomValue
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        RepN widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = dunHVector $ toTarget $ AsHVector valsInit
      f :: MnistData r -> ADVal RepN TKUntyped
        -> ADVal target (TKR 0 r)
      f mnist adinputs =
        MnistFcnnRanked2.afcnnMnistLoss2
          mnist (unAsHVector $ fromTarget (AsHVector $ fromDValue valsInit) adinputs)
      chunk = take chunkLength testData
      grad c = tunvector $ fst $ sgd gamma f c (dmkHVector hVectorInit)
      name = extraPrefix
             ++ unwords [ "v0 m" ++ show (V.length hVectorInit)
                        , " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nf grad chunk

mnistTestBench2VTA :: forall target r. (target ~ RepN, r ~ Double)
                   => String -> Int -> [MnistData r] -> Int -> Int
                   -> Benchmark
mnistTestBench2VTA extraPrefix chunkLength testData widthHidden widthHidden2 = do
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters target r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
                $ randomValue
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        RepN widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = dunHVector $ toTarget $ AsHVector valsInit
      ftest :: [MnistData r] -> HVector RepN -> r
      ftest = MnistFcnnRanked2.afcnnMnistTest2 valsInit
      chunk = take chunkLength testData
      score c = ftest c hVectorInit
      name = "test " ++ extraPrefix
             ++ unwords [ "v0 m" ++ show (V.length hVectorInit)
                        , " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ whnf score chunk
-}
mnistBGroup2VTA :: [MnistData Double] -> Int -> Benchmark
mnistBGroup2VTA xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 2 VTA MNIST nn with samples: "
          ++ show chunkLength)
    []
{-    (if chunkLength <= 1000
     then
       [ mnistTestBench2VTA "30|10 " chunkLength xs 30 10  -- toy width
       , mnistTrainBench2VTA "30|10 " chunkLength xs 30 10 0.02
       {- This is completely obliterated by the lack of vectorization:
       , mnistTestBench2VTA "300|100 " chunkLength xs 300 100  -- ordinary width
       , mnistTrainBench2VTA "300|100 " chunkLength xs 300 100 0.02
       -}
       ]
     else
       [])
       {- This is completely obliterated by the lack of vectorization:
    ++ [ mnistTestBench2VTA "500|150 " chunkLength xs 500 150
           -- another common width
       , mnistTrainBench2VTA "500|150 " chunkLength xs 500 150 0.02
       ]
       -}

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTrainBench2VTO :: forall target r. (target ~ RepN, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench2VTO extraPrefix chunkLength testData widthHidden widthHidden2
                    gamma = do
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters target r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
                $ randomValue
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        RepN widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = dunHVector $ toTarget $ AsHVector valsInit
      name = extraPrefix
             ++ unwords [ "v0 m" ++ show (V.length hVectorInit)
                        , " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nfIO $ do
    let dataInit = case testData of
          d : _ -> let (dglyph, dlabel) = d
                   in ( RepN $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) dglyph
                      , RepN $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR) dlabel )
          [] -> error "empty test data"
        f = \ (AsHVector (pars, (glyphR, labelR))) ->
          MnistFcnnRanked2.afcnnMnistLoss2TensorData
            (glyphR, labelR) pars
        (artRaw, _) = revArtifactAdapt False f (AsHVector (valsInit, dataInit))
        art = simplifyArtifactGradient artRaw
        go :: [MnistData r] -> HVector RepN -> HVector RepN
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let glyphD = DynamicRanked @r @1
                       $ RepN $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) glyph
              labelD = DynamicRanked @r @1
                       $ RepN $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR) label
              parametersAndInput =
                dmkHVector
                $ V.concat [parameters, V.fromList [glyphD, labelD]]
              gradientHVector =
                fst $ revEvalArtifact art parametersAndInput Nothing
          in go rest (tunvector $ updateWithGradient gamma (dmkHVector parameters) gradientHVector)
        chunk = take chunkLength testData
        grad c = go c hVectorInit
    return $! grad chunk

mnistTestBench2VTO :: forall r. r ~ Double
                   => String -> Int -> [MnistData r] -> Int -> Int
                   -> Benchmark
mnistTestBench2VTO = mnistTestBench2VTA
-}
mnistBGroup2VTO :: [MnistData Double] -> Int -> Benchmark
mnistBGroup2VTO xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 2 VTO MNIST nn with samples: "
          ++ show chunkLength) $
    []
{-    (if chunkLength <= 1000
     then
       [ mnistTestBench2VTO "30|10 " chunkLength xs 30 10  -- toy width
       , mnistTrainBench2VTO "30|10 " chunkLength xs 30 10 0.02
       , mnistTestBench2VTO "300|100 " chunkLength xs 300 100  -- ordinary width
       , mnistTrainBench2VTO "300|100 " chunkLength xs 300 100 0.02
       ]
     else
       [])
    ++ [ mnistTestBench2VTO "500|150 " chunkLength xs 500 150
           -- another common width
       , mnistTrainBench2VTO "500|150 " chunkLength xs 500 150 0.02
       ]
-}
