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
import HordeAd.Core.CarriersConcrete
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))

import Data.Array.Nested qualified as Nested

import MnistData
import MnistFcnnRanked1 qualified
import MnistFcnnRanked2 qualified

-- * Using lists of vectors, which is rank 1

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTrainBench1VTA :: forall target r. (target ~ RepN, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench1VTA extraPrefix chunkLength xs widthHidden widthHidden2
                    gamma = do
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ RepN $ FlipR $ Nested.rfromVector (nPV :$: ZSR)
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = RepN $ FlipR $ Nested.rfromList1Prim []
      hVectorInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters target r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      f :: MnistData r -> HVector (ADVal RepN)
        -> ADVal target (TKR r 0)
      f mnist adinputs =
        MnistFcnnRanked1.afcnnMnistLoss1
          widthHidden widthHidden2
          mnist (unAsHVector
                 $ parseHVector (AsHVector $ fromDValue valsInit) (dmkHVector adinputs))
      chunk = take chunkLength xs
      grad c = fst $ sgd gamma f c hVectorInit
      name = extraPrefix
             ++ unwords [ "v" ++ show (length nParams1)
                        , "m0" ++ " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nf grad chunk

mnistTestBench1VTA :: forall target r. (target ~ RepN, r ~ Double)
                   => String -> Int -> [MnistData r] -> Int -> Int
                   -> Benchmark
mnistTestBench1VTA extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ RepN $ FlipR $ Nested.rfromVector (nPV :$: ZSR)
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = RepN $ FlipR $ Nested.rfromList1Prim []
      hVectorInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters target r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      ftest :: [MnistData r] -> HVector RepN -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 valsInit widthHidden widthHidden2
      chunk = take chunkLength xs
      score c = ftest c hVectorInit
      name = "test " ++ extraPrefix
             ++ unwords [ "v" ++ show (length nParams1)
                        , "m0" ++ " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ whnf score chunk

mnistBGroup1VTA :: [MnistData Double] -> Int -> Benchmark
mnistBGroup1VTA xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 1 VTA MNIST nn with samples: "
          ++ show chunkLength) $
    (if chunkLength <= 1000
     then
       [ mnistTestBench1VTA "30|10 " chunkLength xs 30 10  -- toy width
       , mnistTrainBench1VTA "30|10 " chunkLength xs 30 10 0.02
       , mnistTestBench1VTA "300|100 " chunkLength xs 300 100  -- ordinary width
       , mnistTrainBench1VTA "300|100 " chunkLength xs 300 100 0.02
       ]
     else
       [])
    ++ [ mnistTestBench1VTA "500|150 " chunkLength xs 500 150
           -- another common width
       , mnistTrainBench1VTA "500|150 " chunkLength xs 500 150 0.02
       ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTrainBench1VTO :: forall target r. (target ~ RepN, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench1VTO extraPrefix chunkLength testData widthHidden widthHidden2
                    gamma = do
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV ->
          DynamicRanked @r @1 $ RepN $ FlipR $ Nested.rfromVector (nPV :$: ZSR)
          $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
            - LA.scalar 0.5)
          nParams1
      emptyR = RepN $ FlipR $ Nested.rfromList1Prim []
      hVectorInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters target r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = extraPrefix
             ++ unwords [ "v" ++ show (length nParams1)
                        , "m0" ++ " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nfIO $ do
    let dataInit = case testData of
          d : _ -> let (dglyph, dlabel) = d
                   in ( RepN $ FlipR $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) dglyph
                      , RepN $ FlipR $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR) dlabel )
          [] -> error "empty test data"
        f = \ (pars, (glyphR, labelR)) ->
          MnistFcnnRanked1.afcnnMnistLoss1TensorData
            widthHidden widthHidden2
            (glyphR, labelR) pars
        g :: AstTensor AstMethodLet FullSpan TKUntyped
          -> AstTensor AstMethodLet FullSpan TKUntyped
        g !hv = toHVectorOf $ AsHVector $ f
                $ unAsHVector $ parseHVector (AsHVector $ fromValue (valsInit, dataInit)) hv
        (artRaw, _) = revProduceArtifact False g emptyEnv
                        (FTKUntyped $ voidFromHVector
                         $ hVectorInit
                           V.++ V.fromList [ DynamicRanked @r @1
                                             $ fst dataInit
                                           , DynamicRanked @r @1
                                             $ snd dataInit ])
        art = simplifyArtifactGradient artRaw
        go :: [MnistData r] -> HVector RepN -> HVector RepN
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let glyphD = DynamicRanked @r @1
                       $ RepN $ FlipR $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) glyph
              labelD = DynamicRanked @r @1
                       $ RepN $ FlipR $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR)  label
              parametersAndInput =
                dmkHVector
                $ V.concat [parameters, V.fromList [glyphD, labelD]]
              gradientHVector =
                dunHVector
                $ fst $ revEvalArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma parameters gradientHVector)
        chunk = take chunkLength testData
        grad c = go c hVectorInit
    return $! grad chunk

mnistTestBench1VTO :: forall r. r ~ Double
                   => String -> Int -> [MnistData r] -> Int -> Int
                   -> Benchmark
mnistTestBench1VTO = mnistTestBench1VTA

mnistBGroup1VTO :: [MnistData Double] -> Int -> Benchmark
mnistBGroup1VTO xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 1 VTO MNIST nn with samples: "
          ++ show chunkLength) $
    (if chunkLength <= 1000
     then
       [ mnistTestBench1VTO "30|10 " chunkLength xs 30 10  -- toy width
       , mnistTrainBench1VTO "30|10 " chunkLength xs 30 10 0.02
       , mnistTestBench1VTO "300|100 " chunkLength xs 300 100  -- ordinary width
       , mnistTrainBench1VTO "300|100 " chunkLength xs 300 100 0.02
       ]
     else
       [])
    ++ [ mnistTestBench1VTO "500|150 " chunkLength xs 500 150
           -- another common width
       , mnistTrainBench1VTO "500|150 " chunkLength xs 500 150 0.02
       ]


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
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        RepN widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
      f :: MnistData r -> HVector (ADVal RepN)
        -> ADVal target (TKR r 0)
      f mnist adinputs =
        MnistFcnnRanked2.afcnnMnistLoss2
          mnist (unAsHVector $ parseHVector (AsHVector $ fromDValue valsInit) (dmkHVector adinputs))
      chunk = take chunkLength testData
      grad c = fst $ sgd gamma f c hVectorInit
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
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        RepN widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
      ftest :: [MnistData r] -> HVector RepN -> r
      ftest = MnistFcnnRanked2.afcnnMnistTest2 valsInit
      chunk = take chunkLength testData
      score c = ftest c hVectorInit
      name = "test " ++ extraPrefix
             ++ unwords [ "v0 m" ++ show (V.length hVectorInit)
                        , " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ whnf score chunk

mnistBGroup2VTA :: [MnistData Double] -> Int -> Benchmark
mnistBGroup2VTA xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 2 VTA MNIST nn with samples: "
          ++ show chunkLength)
    (if chunkLength <= 1000
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
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        RepN widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = dunHVector $ toHVectorOf $ AsHVector valsInit
      name = extraPrefix
             ++ unwords [ "v0 m" ++ show (V.length hVectorInit)
                        , " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nfIO $ do
    let dataInit = case testData of
          d : _ -> let (dglyph, dlabel) = d
                   in ( RepN $ FlipR $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) dglyph
                      , RepN $ FlipR $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR) dlabel )
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
                       $ RepN $ FlipR $ Nested.rfromVector (sizeMnistGlyphInt :$: ZSR) glyph
              labelD = DynamicRanked @r @1
                       $ RepN $ FlipR $ Nested.rfromVector (sizeMnistLabelInt :$: ZSR)  label
              parametersAndInput =
                dmkHVector
                $ V.concat [parameters, V.fromList [glyphD, labelD]]
              gradientHVector =
                dunHVector
                $ fst $ revEvalArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma parameters gradientHVector)
        chunk = take chunkLength testData
        grad c = go c hVectorInit
    return $! grad chunk

mnistTestBench2VTO :: forall r. r ~ Double
                   => String -> Int -> [MnistData r] -> Int -> Int
                   -> Benchmark
mnistTestBench2VTO = mnistTestBench2VTA

mnistBGroup2VTO :: [MnistData Double] -> Int -> Benchmark
mnistBGroup2VTO xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 2 VTO MNIST nn with samples: "
          ++ show chunkLength) $
    (if chunkLength <= 1000
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
