{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | A set of benchmarks using fully connected MNIST neural networks.
module BenchMnistTools where

import Prelude

import Control.Arrow ((***))
import Control.DeepSeq (NFData (..))
import Criterion.Main
import Data.Default qualified as Default
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:))
import GHC.Exts (WithDict)
import GHC.TypeLits (KnownNat, type (<=?))
import System.Random
import Test.Inspection
import Type.Reflection (Typeable)

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.OpsConcrete ()
import HordeAd.External.OptimizerTools

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import MnistData
import MnistFcnnRanked1 qualified
import MnistFcnnRanked2 (XParams2)
import MnistFcnnRanked2 qualified

-- * Using lists of vectors, which is rank 1

type XParams widthHidden widthHidden2 r =
  X (MnistFcnnRanked1.ADFcnnMnist1Parameters
       Concrete widthHidden widthHidden2 r)

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
    (stkOfListR (knownSTK @(TKS '[widthHidden] Float)) (SNat @widthHidden2)) $
  gcastWith (unsafeCoerceRefl :: (1 <=? widthHidden) :~: True) $
  gcastWith (unsafeCoerceRefl :: (1 <=? widthHidden2) :~: True) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    Concrete widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: Concrete (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @Concrete valsInit
  in do
    let f :: MnistDataLinearR Double
          -> ADVal Concrete (XParams widthHidden widthHidden2 Double)
          -> ADVal Concrete (TKScalar Double)
        f (glyph, label) adinputs =
          MnistFcnnRanked1.afcnnMnistLoss1
            widthHiddenSNat widthHidden2SNat
            (rconcrete glyph, rconcrete label) (fromTarget adinputs)
        chunk = take batchSize xs
        gradf c = fst $ sgdSTK knownSTK gamma f c targetInit
        name =
          prefix
          ++ unwords
               [ "v" ++ show (widthSTK
                              $ knownSTK @(XParams widthHidden widthHidden2 r))
               , "m0" ++ " =" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf gradf chunk

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
    (stkOfListR (knownSTK @(TKS '[widthHidden] Float)) (SNat @widthHidden2)) $
  gcastWith (unsafeCoerceRefl :: (1 <=? widthHidden) :~: True) $
  gcastWith (unsafeCoerceRefl :: (1 <=? widthHidden2) :~: True) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    Concrete widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: Concrete (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @Concrete valsInit
      ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters
                 Concrete widthHidden widthHidden2 r
            -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 widthHiddenSNat widthHidden2SNat
  in do
    let chunk = take batchSize xs
        score c = ftest c valsInit
        name =
          "test " ++ prefix
          ++ unwords
               [ "v" ++ show (widthSTK
                              $ knownSTK @(XParams widthHidden widthHidden2 r))
               , "m0" ++ " =" ++ show (tsize knownSTK targetInit) ]
    bench name $ whnf score chunk

mnistBGroup1VTA :: Int -> Benchmark
mnistBGroup1VTA chunkLength =
  env (do
    testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
    let testData = shuffle (mkStdGen 42) testData0
    return $! map mkMnistDataLinearR $ take chunkLength testData) $
  \ xs ->
  bgroup ("2-hidden-layer rank 1 VTA MNIST nn with samples: "
          ++ show chunkLength)
       [ mnistTestBench1VTA "30|10 " 30 10 0.02 chunkLength xs
       , mnistTrainBench1VTA "30|10 " 30 10 0.02 chunkLength xs
           -- toy width
       , mnistTestBench1VTA "300|100 " 300 100 0.02 chunkLength xs
       , mnistTrainBench1VTA "300|100 " 300 100 0.02 chunkLength xs
           -- ordinary width
       , mnistTestBench1VTA "500|150 " 500 150 0.02 chunkLength xs
       , mnistTrainBench1VTA "500|150 " 500 150 0.02 chunkLength xs
           -- another common width
       , mnistTrainBench1VTA "1500|500 " 1500 500 0.02 chunkLength xs
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
    (stkOfListR (knownSTK @(TKS '[widthHidden] Float)) (SNat @widthHidden2)) $
  gcastWith (unsafeCoerceRefl :: (1 <=? widthHidden) :~: True) $
  gcastWith (unsafeCoerceRefl :: (1 <=? widthHidden2) :~: True) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    Concrete widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: Concrete (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @Concrete valsInit
  in do
{-      -- g is not enough to specialize to Double instead of to r,
        -- despite the declaration of r ~ Double above
        f :: ( MnistFcnnRanked1.ADFcnnMnist1Parameters
                 (AstTensor AstMethodLet FullSpan)
                 widthHidden widthHidden2 r
             , ( AstTensor AstMethodLet FullSpan (TKR 1 r)
               , AstTensor AstMethodLet FullSpan (TKR 1 r) ) )
          -> AstTensor AstMethodLet FullSpan (TKScalar r)
        f = \ (pars, (glyphR, labelR)) ->
          MnistFcnnRanked1.afcnnMnistLoss1
            widthHiddenSNat widthHidden2SNat
            (glyphR, labelR) pars
        g :: ( MnistFcnnRanked1.ADFcnnMnist1Parameters (AstTensor AstMethodLet FullSpan) widthHidden widthHidden2 Double, ( AstTensor AstMethodLet FullSpan (TKR 1 Double), AstTensor AstMethodLet FullSpan (TKR 1 Double) ) ) -> AstTensor AstMethodLet FullSpan (TKScalar Double)
        g = f
-}
    let dataInit = case xs of
          d : _ -> (rconcrete *** rconcrete) d
          [] -> error "empty test data"
        f :: ( MnistFcnnRanked1.ADFcnnMnist1Parameters
                 (AstTensor AstMethodLet FullSpan)
                 widthHidden widthHidden2 Double
             , ( AstTensor AstMethodLet FullSpan (TKR 1 Double)
               , AstTensor AstMethodLet FullSpan (TKR 1 Double) ) )
          -> AstTensor AstMethodLet FullSpan (TKScalar Double)
        f = \ (pars, (glyphR, labelR)) ->
          MnistFcnnRanked1.afcnnMnistLoss1 @_ @Double
            widthHiddenSNat widthHidden2SNat
            (glyphR, labelR) pars
        artRaw = gradArtifact f (valsInit, dataInit)
        art = simplifyArtifactRev artRaw
        go :: [MnistDataLinearR r]
           -> Concrete (XParams widthHidden widthHidden2 r)
           -> Concrete (XParams widthHidden widthHidden2 r)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ snd
                         $ revInterpretArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma knownSTK parameters gradient)
        chunk = take batchSize xs
        gradf c = go c targetInit
        name =
          prefix
          ++ unwords
               [ "v" ++ show (widthSTK
                              $ knownSTK @(XParams widthHidden widthHidden2 r))
               , "m0" ++ " =" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf gradf chunk

mnistTestBench1VTO
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTestBench1VTO = mnistTestBench1VTA

mnistBGroup1VTO :: Int -> Benchmark
mnistBGroup1VTO chunkLength =
  env (do
    testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
    let testData = shuffle (mkStdGen 42) testData0
    return $! map mkMnistDataLinearR $ take chunkLength testData) $
  \ xs ->
  bgroup ("2-hidden-layer rank 1 VTO MNIST nn with samples: "
          ++ show chunkLength)
       [ mnistTestBench1VTO "30|10 " 30 10 0.02 chunkLength xs
       , mnistTrainBench1VTO "30|10 " 30 10 0.02 chunkLength xs
       , mnistTestBench1VTO "300|100 " 300 100 0.02 chunkLength xs
       , mnistTrainBench1VTO "300|100 " 300 100 0.02 chunkLength xs
       , mnistTestBench1VTO "500|150 " 500 150 0.02 chunkLength xs
       , mnistTrainBench1VTO "500|150 " 500 150 0.02 chunkLength xs
       , mnistTrainBench1VTO "1500|500 " 1500 500 0.02 chunkLength xs
       ]


-- * Using matrices, which is rank 2

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
        $ randomValue
            @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                             Concrete widthHidden widthHidden2 r Float)))
            1 (mkStdGen 44)
  in do
{-    let f :: MnistDataLinearR r -> ADVal Concrete (XParams2 r Float)
          -> ADVal Concrete (TKScalar r)
        f (glyph, label) adinputs =
          MnistFcnnRanked2.afcnnMnistLoss2
            (rconcrete glyph, rconcrete label) (fromTarget adinputs) -}
    let f :: MnistDataLinearR Double -> ADVal Concrete (XParams2 Double Float)
          -> ADVal Concrete (TKScalar Double)
        f (glyph, label) adinputs =
          MnistFcnnRanked2.afcnnMnistLoss2
            (rconcrete glyph, rconcrete label) (fromTarget adinputs)
        chunk = take batchSize xs
        gradf c = fst $ sgd gamma f c targetInit
        name =
          prefix
          ++ unwords
               [ "v0 m" ++ show (widthSTK $ knownSTK @(XParams2 r Float))
               , "=" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf gradf chunk

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
        $ randomValue
            @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                             Concrete widthHidden widthHidden2 r Float)))
            1 (mkStdGen 44)
  in do
    let chunk = take batchSize xs
        score c = MnistFcnnRanked2.afcnnMnistTest2 c (fromTarget targetInit)
        name =
          "test " ++ prefix
          ++ unwords
               [ "v0 m" ++ show (widthSTK $ knownSTK @(XParams2 r Float))
               , "=" ++ show (tsize knownSTK targetInit) ]
    bench name $ whnf score chunk

mnistBGroup2VTA :: Int -> Benchmark
mnistBGroup2VTA chunkLength =
  env (do
    testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
    let testData = shuffle (mkStdGen 42) testData0
    return $! map mkMnistDataLinearR $ take chunkLength testData) $
  \ xs ->
  bgroup ("2-hidden-layer rank 2 VTA MNIST nn with samples: "
          ++ show chunkLength)
       [ mnistTestBench2VTA "30|10 " 30 10 0.02 chunkLength xs
       , mnistTrainBench2VTA "30|10 " 30 10 0.02 chunkLength xs
       , mnistTestBench2VTA "300|100 " 300 100 0.02 chunkLength xs
       , mnistTrainBench2VTA "300|100 " 300 100 0.02 chunkLength xs
       , mnistTestBench2VTA "500|150 " 500 150 0.02 chunkLength xs
       , mnistTrainBench2VTA "500|150 " 500 150 0.02 chunkLength xs
       , mnistTrainBench2VTA "1500|500 " 1500 500 0.02 chunkLength xs
       ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.

-- Only compilation time.
mnistTrainBench2VTC
  :: String
  -> Int -> Int
  -> Benchmark
mnistTrainBench2VTC prefix widthHidden widthHidden2 =
  bench prefix
  $ whnf (simplifyArtifactRev . snd
          . MnistFcnnRanked2.mnistTrainBench2VTOGradient
              @Double (Proxy @Float) IgnoreIncomingCotangent
              1 (mkStdGen 44) widthHidden)
         widthHidden2

mnistBGroup2VTC :: Int -> Benchmark
mnistBGroup2VTC chunkLength =
  bgroup ("2-hidden-layer rank 2 VTC compilation MNIST nn with samples: "
          ++ show chunkLength)
       [ mnistTrainBench2VTC "30|10 " 30 10
       , mnistTrainBench2VTC "300|100 " 300 100
       , mnistTrainBench2VTC "500|150 " 500 150
       , mnistTrainBench2VTC "1500|500 " 1500 500
       ]

-- The same as above, but only runtime.
mnistTrainBench2VTOO
  :: forall r. r ~ Double
  => String
  -> Double -> Int -> [MnistDataLinearR r]
  -> ( Concrete (XParams2 r Float)
     , AstArtifactRev
         (TKProduct
            (XParams2 r Float)
            (TKProduct (TKR2 1 (TKScalar Double))
                       (TKR2 1 (TKScalar Double))))
         (TKScalar r) )
  -> Benchmark
mnistTrainBench2VTOO prefix gamma batchSize xs (targetInit, art) = do
    let go :: [MnistDataLinearR r] -> Concrete (XParams2 r Float)
           -> Concrete (XParams2 r Float)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ snd
                         $ revInterpretArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma knownSTK parameters gradient)
        chunk = take batchSize xs
        gradf c = go c targetInit
        name =
          prefix
          ++ unwords
               [ "v0 m" ++ show (widthSTK $ knownSTK @(XParams2 r Float))
               , "=" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf gradf chunk

-- The same as above, but both compilation time and only runtime.
mnistTrainBench2VTO
  :: forall r. r ~ Double
  => String
  -> Int -> Int -> Double -> Int -> [MnistDataLinearR r]
  -> Benchmark
mnistTrainBench2VTO prefix widthHidden widthHidden2
                    gamma batchSize xs =
  let (!targetInit, !artRaw) =
        MnistFcnnRanked2.mnistTrainBench2VTOGradient
          @Double (Proxy @Float) IgnoreIncomingCotangent
          1 (mkStdGen 44) widthHidden widthHidden2
      !art = simplifyArtifactRev artRaw
  in mnistTrainBench2VTOO prefix gamma batchSize xs (targetInit, art)

mnistBGroup2VTO :: Int -> Benchmark
mnistBGroup2VTO chunkLength =
  let (!targetInit, !artRaw) =
        MnistFcnnRanked2.mnistTrainBench2VTOGradient
          @Double (Proxy @Float) IgnoreIncomingCotangent
          1 (mkStdGen 44) 1500 500
      !art = simplifyArtifactRev artRaw  -- no NFData for AST
  in env (do
    testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
    let testData = shuffle (mkStdGen 42) testData0
    return $! map mkMnistDataLinearR $ take chunkLength testData) $
  \ xs ->
   bgroup ("2-hidden-layer rank 2 VTO runtime MNIST nn with samples: "
           ++ show chunkLength)
     [ mnistTrainBench2VTOO "1500|500 " 0.02 chunkLength xs (targetInit, art)
     ]

-- The same as above, but without simplifying the gradient.
mnistTrainBench2VTOZ
  :: forall r. r ~ Double
  => String
  -> Double -> Int -> [MnistDataLinearR r]
  -> ( Concrete (XParams2 r Float)
     , AstArtifactRev
         (TKProduct
            (XParams2 r Float)
            (TKProduct (TKR2 1 (TKScalar Double))
                       (TKR2 1 (TKScalar Double))))
         (TKScalar r) )
  -> Benchmark
mnistTrainBench2VTOZ prefix gamma batchSize xs (targetInit, art) = do
    let go :: [MnistDataLinearR r] -> Concrete (XParams2 r Float)
           -> Concrete (XParams2 r Float)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ snd
                         $ revInterpretArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma knownSTK parameters gradient)
        chunk = take batchSize xs
        gradf c = go c targetInit
        name =
          prefix
          ++ unwords
               [ "v0 m" ++ show (widthSTK $ knownSTK @(XParams2 r Float))
               , "=" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf gradf chunk

mnistBGroup2VTOZ :: Int -> Benchmark
mnistBGroup2VTOZ chunkLength =
  let (!targetInit, !art) =
        MnistFcnnRanked2.mnistTrainBench2VTOGradient
          @Double (Proxy @Float) IgnoreIncomingCotangent
          1 (mkStdGen 44) 1500 500
  in env (do
    testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
    let testData = shuffle (mkStdGen 42) testData0
    return $! map mkMnistDataLinearR $ take chunkLength testData) $
  \ xs ->
   bgroup ("2-hidden-layer rank 2 VTOZ runtime MNIST nn with samples: "
           ++ show chunkLength)
     [ mnistTrainBench2VTOO "1500|500 " 0.02 chunkLength xs (targetInit, art)
     ]

-- The same as above, but without any simplification, even the smart
-- constructors.
mnistTrainBench2VTOX
  :: forall r. r ~ Double
  => String
  -> Double -> Int -> [MnistDataLinearR r]
  -> ( Concrete (XParams2 r Float)
     , AstArtifactRev
         (TKProduct
            (XParams2 r Float)
            (TKProduct (TKR2 1 (TKScalar Double))
                       (TKR2 1 (TKScalar Double))))
         (TKScalar r) )
  -> Benchmark
mnistTrainBench2VTOX prefix gamma batchSize xs (targetInit, art) = do
    let go :: [MnistDataLinearR r] -> Concrete (XParams2 r Float)
           -> Concrete (XParams2 r Float)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ snd
                         $ revInterpretArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma knownSTK parameters gradient)
        chunk = take batchSize xs
        gradf c = go c targetInit
        name =
          prefix
          ++ unwords
               [ "v0 m" ++ show (widthSTK $ knownSTK @(XParams2 r Float))
               , "=" ++ show (tsize knownSTK targetInit) ]
    bench name $ nf gradf chunk

mnistBGroup2VTOX :: Int -> Benchmark
mnistBGroup2VTOX chunkLength =
  let (!targetInit, !art) =
        MnistFcnnRanked2.mnistTrainBench2VTOGradientX
          @Double (Proxy @Float) IgnoreIncomingCotangent
          1 (mkStdGen 44) 1500 500
  in env (do
    testData0 <- loadMnistData testGlyphsPath testLabelsPath  -- 10k total
    let testData = shuffle (mkStdGen 42) testData0
    return $! map mkMnistDataLinearR $ take chunkLength testData) $
  \ xs ->
   bgroup ("2-hidden-layer rank 2 VTOX runtime MNIST nn with samples: "
           ++ show chunkLength)
     [ mnistTrainBench2VTOO "1500|500 " 0.02 chunkLength xs (targetInit, art)
     ]

{- TODO: re-enable once -fpolymorphic-specialisation works

-- This is expected to fail with -O0 and to pass with -O1
-- and -fpolymorphic-specialisation.
-- This prevents running benchmarks without optimization, which is a good thing.
--
-- The `Storable` is only needed for overloaded profiling, e.g., with
-- cabal bench longMnistBench -ftest_seq -w /home/mikolaj/r/ghc.HEAD/ghc/_build/stage1/bin/ghc --allow-newer --enable-optimization --enable-profiling --profiling-detail=none --ghc-options="-fprof-late-overloaded -fpolymorphic-specialisation" --benchmark-options='-n1 -m pattern "1 VTA MNIST nn with samples: 400/500|150 v" +RTS -pj'
inspect $ hasNoTypeClassesExcept 'mnistTrainBench1VTA [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''NFData, ''Default.Default, ''Nested.Storable]
inspect $ hasNoTypeClassesExcept 'mnistTrainBench1VTO [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''NFData, ''Default.Default, ''Nested.Storable,      ''AstSpan, ''RealFloatH, ''Nested.FloatElt, ''Fractional, ''Floating, ''IntegralH, ''RealFrac, ''Real, ''Nested.Elt, ''Integral]
inspect $ hasNoTypeClassesExcept 'mnistTrainBench2VTA [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''NFData, ''Default.Default, ''Nested.Storable]
inspect $ hasNoTypeClassesExcept 'mnistTrainBench2VTC [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''NFData, ''Default.Default]
inspect $ hasNoTypeClassesExcept 'mnistTrainBench2VTO [''(~), ''GoodScalar, ''Show, ''Num, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''NFData, ''Default.Default,       ''AstSpan, ''RealFloatH, ''Nested.FloatElt, ''Fractional, ''Floating, ''IntegralH, ''RealFrac, ''Real, ''Nested.Storable, ''WithDict, ''KnownShS, ''KnownSTK, ''KnownNat, ''Nested.Elt, ''Integral]
-- inspect $ coreOf 'mnistTrainBench1VTA
-}
