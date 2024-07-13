{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | A set of benchmarks using fully connected MNIST neural networks.
module BenchMnistTools where

import Prelude

import Criterion.Main
import Data.Array.RankedS qualified as OR
import Data.EnumMap.Strict qualified as EM
import Data.List.Index (imap)
import Data.Vector.Generic qualified as V
import GHC.TypeLits (SomeNat (..), someNatVal)
import Numeric.LinearAlgebra qualified as LA
import System.Random

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (funToAstIOR)
import HordeAd.Core.TensorAst
import HordeAd.Core.TensorConcrete ()
import HordeAd.External.OptimizerTools
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))

import Data.Array.Nested qualified as Nested

import MnistData
import MnistFcnnRanked1 qualified
import MnistFcnnRanked2 qualified

-- * Using lists of vectors, which is rank 1

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTrainBench1VTA :: forall ranked r. (ranked ~ ORArray, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench1VTA extraPrefix chunkLength xs widthHidden widthHidden2
                    gamma = do
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV -> DynamicRanked @r @1 $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [0] []
      hVectorInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      f :: MnistData r -> HVector (ADVal ranked)
        -> ADVal ranked r 0
      f mnist adinputs =
        MnistFcnnRanked1.afcnnMnistLoss1
          widthHidden widthHidden2
          mnist (parseHVector (fromDValue valsInit) adinputs)
      chunk = take chunkLength xs
      grad c = fst $ sgd gamma f c hVectorInit
      name = extraPrefix
             ++ unwords [ "v" ++ show (length nParams1)
                        , "m0" ++ " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nf grad chunk

mnistTestBench1VTA :: forall ranked r. (ranked ~ ORArray, r ~ Double)
                   => String -> Int -> [MnistData r] -> Int -> Int
                   -> Benchmark
mnistTestBench1VTA extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV -> DynamicRanked @r @1 $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [0] []
      hVectorInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      ftest :: [MnistData r] -> HVector (ORArray) -> r
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
mnistTrainBench1VTO :: forall ranked r. (ranked ~ ORArray, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench1VTO extraPrefix chunkLength xs widthHidden widthHidden2
                    gamma = do
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV -> DynamicRanked @r @1 $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [0] []
      hVectorInit = V.fromList params1Init
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      name = extraPrefix
             ++ unwords [ "v" ++ show (length nParams1)
                        , "m0" ++ " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nfIO $ do
    (varGlyph, varGlyphD, astGlyph) <-
      funToAstIOR (singletonShape sizeMnistGlyphInt) id
    (varLabel, varLabelD, astLabel) <-
      funToAstIOR (singletonShape sizeMnistLabelInt) id
    let envInit = extendEnvR varGlyph (rconstant $ AstRaw astGlyph)
                  $ extendEnvR varLabel (rconstant $ AstRaw astLabel)
                  EM.empty
        f = MnistFcnnRanked1.afcnnMnistLoss1TensorData @(AstRanked FullSpan)
              widthHidden widthHidden2
              (rconstant $ AstRanked astGlyph, rconstant $ AstRanked astLabel)
        (AstArtifact varDtAgain vars1Again gradientRaw primal, _) =
           revProduceArtifactH False f envInit valsInit
                               (voidFromHVector hVectorInit)
        gradient = simplifyInlineHVectorRaw gradientRaw
        vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
        art = AstArtifact varDtAgain vars1AndInputAgain gradient primal
        go :: [MnistData r] -> HVector (ORArray) -> HVector (ORArray)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let glyphD = DynamicRanked @r @1
                       $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [sizeMnistGlyphInt] glyph
              labelD = DynamicRanked @r @1
                       $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [sizeMnistLabelInt] label
              parametersAndInput =
                V.concat [parameters, V.fromList [glyphD, labelD]]
              gradientHVector =
                fst $ revEvalArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma parameters gradientHVector)
        chunk = take chunkLength xs
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
mnistTrainBench2VTA :: forall ranked r. (ranked ~ ORArray, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench2VTA extraPrefix chunkLength xs widthHidden widthHidden2
                    gamma = do
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        (OSArray) widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = toHVectorOf valsInit
      f :: MnistData r -> HVector (ADVal ranked)
        -> ADVal ranked r 0
      f mnist adinputs =
        MnistFcnnRanked2.afcnnMnistLoss2
          mnist (parseHVector (fromDValue valsInit) adinputs)
      chunk = take chunkLength xs
      grad c = fst $ sgd gamma f c hVectorInit
      name = extraPrefix
             ++ unwords [ "v0 m" ++ show (V.length hVectorInit)
                        , " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nf grad chunk

mnistTestBench2VTA :: forall ranked r. (ranked ~ ORArray, r ~ Double)
                   => String -> Int -> [MnistData r] -> Int -> Int
                   -> Benchmark
mnistTestBench2VTA extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        (OSArray) widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = toHVectorOf valsInit
      ftest :: [MnistData r] -> HVector (ORArray) -> r
      ftest = MnistFcnnRanked2.afcnnMnistTest2 valsInit
      chunk = take chunkLength xs
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
mnistTrainBench2VTO :: forall ranked r. (ranked ~ ORArray, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench2VTO extraPrefix chunkLength xs widthHidden widthHidden2
                    gamma = do
  let valsInit :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
      valsInit =
        case someNatVal $ toInteger widthHidden of
          Just (SomeNat @widthHidden _) ->
            case someNatVal $ toInteger widthHidden2 of
              Just (SomeNat @widthHidden2 _) ->
                forgetShape $ fst
                $ randomVals
                    @(MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                        (OSArray) widthHidden widthHidden2 r)
                    1 (mkStdGen 44)
              Nothing -> error "valsInit: impossible someNatVal error"
          Nothing -> error "valsInit: impossible someNatVal error"
      hVectorInit = toHVectorOf valsInit
      name = extraPrefix
             ++ unwords [ "v0 m" ++ show (V.length hVectorInit)
                        , " =" ++ show (sizeHVector hVectorInit) ]
  bench name $ nfIO $ do
    (varGlyph, varGlyphD, astGlyph) <-
      funToAstIOR (singletonShape sizeMnistGlyphInt) id
    (varLabel, varLabelD, astLabel) <-
      funToAstIOR (singletonShape sizeMnistLabelInt) id
    let envInit = extendEnvR varGlyph (rconstant $ AstRaw astGlyph)
                  $ extendEnvR varLabel (rconstant $ AstRaw astLabel)
                  EM.empty
        f = MnistFcnnRanked2.afcnnMnistLoss2TensorData @(AstRanked FullSpan)
              (rconstant $ AstRanked astGlyph, rconstant $ AstRanked astLabel)
        (AstArtifact varDtAgain vars1Again gradientRaw primal, _) =
           revProduceArtifactH False f envInit valsInit
                               (voidFromHVector hVectorInit)
        gradient = simplifyInlineHVectorRaw gradientRaw
        vars1AndInputAgain = vars1Again ++ [varGlyphD, varLabelD]
        art = AstArtifact varDtAgain vars1AndInputAgain gradient primal
        go :: [MnistData r] -> HVector (ORArray) -> HVector (ORArray)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let glyphD = DynamicRanked @r @1
                       $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [sizeMnistGlyphInt] glyph
              labelD = DynamicRanked @r @1
                       $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromVector [sizeMnistLabelInt] label
              parametersAndInput =
                V.concat [parameters, V.fromList [glyphD, labelD]]
              gradientHVector =
                fst $ revEvalArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma parameters gradientHVector)
        chunk = take chunkLength xs
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
