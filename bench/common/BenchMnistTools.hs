{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | A set of benchmarks using fully connected MNIST neural networks.
module BenchMnistTools where

import Prelude

import Criterion.Main
import System.Random

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.OpsConcrete ()
import HordeAd.External.OptimizerTools

import Data.Array.Nested (pattern (:$:), pattern ZSR)

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

-- * Using matrices, which is rank 2

type XParams2 r = X (MnistFcnnRanked2.ADFcnnMnist2Parameters RepN r)

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTrainBench2VTA
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTrainBench2VTA prefix widthHidden widthHidden2
                    gamma batchSize xs =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                                   RepN widthHidden widthHidden2 r)))
                      1 (mkStdGen 44)
  in do
    let f :: MnistDataLinearR r -> ADVal RepN (XParams2 r)
          -> ADVal RepN (TKR 0 r)
        f mnist adinputs = MnistFcnnRanked2.afcnnMnistLoss2
                             mnist (fromTarget adinputs)
        chunk = take batchSize xs
        grad c = fst $ sgd gamma f c targetInit
        name =
          prefix
          ++ unwords
               [ "v0 m" ++ show (twidth @RepN $ knownSTK @(XParams2 r))
               , "=" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf grad chunk

mnistTestBench2VTA
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTestBench2VTA prefix widthHidden widthHidden2
                   _gamma batchSize xs =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                                   RepN widthHidden widthHidden2 r)))
                      1 (mkStdGen 44)
  in do
    let chunk = take batchSize xs
        score c = MnistFcnnRanked2.afcnnMnistTest2 c (fromTarget targetInit)
        name =
          "test " ++ prefix
          ++ unwords
               [ "v0 m" ++ show (twidth @RepN $ knownSTK @(XParams2 r))
               , "=" ++ show (tsize knownSTK targetInit) ]
    bench name $ whnf score chunk

mnistBGroup2VTA :: [MnistData Double] -> Int -> Benchmark
mnistBGroup2VTA xs0 chunkLength =
  env (return $ map mkMnistDataLinearR $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 2 VTA MNIST nn with samples: "
          ++ show chunkLength)
    (if chunkLength <= 1000
     then
       [ mnistTestBench2VTA "30|10 "30 10 0.02 chunkLength xs
           -- toy width
       , mnistTrainBench2VTA "30|10 " 30 10 0.02 chunkLength xs
       {- This is completely obliterated by the lack of vectorization: ???
       , mnistTestBench2VTA "300|100 " 300 100 0.02 chunkLength xs
           -- ordinary width
       , mnistTrainBench2VTA "300|100 " 300 100 0.02 chunkLength xs
       -}
       ]
     else
       [])
       {- This is completely obliterated by the lack of vectorization:
    ++ [ mnistTestBench2VTA "500|150 " 500 150 0.02 chunkLength xs
           -- another common width
       , mnistTrainBench2VTA "500|150 " 500 150 0.02 chunkLength xs
       ]
       -}

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTrainBench2VTO
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTrainBench2VTO prefix widthHidden widthHidden2
                    gamma batchSize xs =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                                   RepN widthHidden widthHidden2 r)))
                      1 (mkStdGen 44)
  in do
    let ftk = tftk @RepN (knownSTK @(XParams2 r)) targetInit
        ftkData = FTKProduct (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar)
                             (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar)
        f :: ( MnistFcnnRanked2.ADFcnnMnist2Parameters
                 (AstTensor AstMethodLet FullSpan) r
             , ( AstTensor AstMethodLet FullSpan (TKR 1 r)
               , AstTensor AstMethodLet FullSpan (TKR 1 r) ) )
          -> AstTensor AstMethodLet FullSpan (TKR 0 r)
        f (pars, (glyphR, labelR)) =
          MnistFcnnRanked2.afcnnMnistLoss2TensorData
            (glyphR, labelR) pars
        (artRaw, _) = revArtifactAdapt False f (FTKProduct ftk ftkData)
        art = simplifyArtifactGradient artRaw
        go :: [MnistDataLinearR r] -> RepN (XParams2 r) -> RepN (XParams2 r)
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
               [ "v0 m" ++ show (twidth @RepN $ knownSTK @(XParams2 r))
               , "=" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf grad chunk

mnistTestBench2VTO
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTestBench2VTO = mnistTestBench2VTA

mnistBGroup2VTO :: [MnistData Double] -> Int -> Benchmark
mnistBGroup2VTO xs0 chunkLength =
  env (return $ map mkMnistDataLinearR $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 2 VTO MNIST nn with samples: "
          ++ show chunkLength) $
    (if chunkLength <= 1000
     then
       [ mnistTestBench2VTO "30|10 " 30 10 0.02 chunkLength xs
           -- toy width
       , mnistTrainBench2VTO "30|10 " 30 10 0.02 chunkLength xs
       , mnistTestBench2VTO "300|100 " 300 100 0.02 chunkLength xs
           -- ordinary width
       , mnistTrainBench2VTO "300|100 " 300 100 0.02 chunkLength xs
       ]
     else
       [])
    ++ [ mnistTestBench2VTO "500|150 " 500 150 0.02 chunkLength xs
           -- another common width
       , mnistTrainBench2VTO "500|150 " 500 150 0.02 chunkLength xs
       ]
