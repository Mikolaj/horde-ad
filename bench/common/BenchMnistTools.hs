{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | A set of benchmarks using fully connected MNIST neural networks.
module BenchMnistTools where

import Prelude

import           Criterion.Main
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.List.Index (imap)
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as LA

import           HordeAd
import           HordeAd.Core.Adaptor
import           HordeAd.Core.TensorADVal (ADValClown)
import           MnistData
import qualified MnistFcnnRanked1
import qualified MnistFcnnRanked2

-- * Using lists of vectors, which is rank 1

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTrainBench1VTA :: forall ranked r. (ranked ~ Flip OR.Array, r ~ Double)
                    => String -> Int -> [MnistData r]
                    -> Int -> Int -> r
                    -> Benchmark
mnistTrainBench1VTA extraPrefix chunkLength xs widthHidden widthHidden2
                    gamma = do
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV -> OD.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = Flip $ OR.fromList [0] []
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      f :: MnistData r -> Domains (ADValClown OD.Array)
        -> ADVal ranked r 0
      f mnist adinputs =
        MnistFcnnRanked1.afcnnMnistLoss1
          widthHidden widthHidden2
          mnist (parseDomains valsInit adinputs)
      chunk = take chunkLength xs
      grad c =
        fst $ sgd gamma f c $ V.fromList $ map (DynamicExists @r) params1Init
      name = extraPrefix
             ++ unwords [ "v" ++ show (length nParams1)
                        , "m0" ++ " =" ++ show (sum (map OD.size params1Init)) ]
  bench name $ nf grad chunk

mnistTestBench1VTA :: forall ranked r. (ranked ~ Flip OR.Array, r ~ Double)
                   => String -> Int -> [MnistData r] -> Int -> Int
                   -> Benchmark
mnistTestBench1VTA extraPrefix chunkLength xs widthHidden widthHidden2 = do
  let nParams1 = MnistFcnnRanked1.afcnnMnistLen1 widthHidden widthHidden2
      params1Init =
        imap (\i nPV -> OD.fromVector [nPV]
                        $ V.map realToFrac
                        $ LA.randomVector (44 + nPV + i) LA.Uniform nPV
                          - LA.scalar 0.5)
             nParams1
      emptyR = Flip $ OR.fromList [0] []
      valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters ranked r
      valsInit = ( (replicate widthHidden emptyR, emptyR)
                 , (replicate widthHidden2 emptyR, emptyR)
                 , (replicate sizeMnistLabelInt emptyR, emptyR) )
      ftest :: [MnistData r] -> DomainsOD -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 valsInit widthHidden widthHidden2
      chunk = take chunkLength xs
      score c = ftest c $ V.fromList $ map (DynamicExists @r) params1Init
      name = "test " ++ extraPrefix
             ++ unwords [ "v" ++ show (length nParams1)
                        , "m0" ++ " =" ++ show (sum (map OD.size params1Init)) ]
  bench name $ whnf score chunk

mnistBGroup1VTA :: [MnistData Double] -> Int -> Benchmark
mnistBGroup1VTA xs0 chunkLength =
  env (return $ take chunkLength xs0) $
  \ xs ->
  bgroup ("2-hidden-layer rank 1 VA MNIST nn with samples: "
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
