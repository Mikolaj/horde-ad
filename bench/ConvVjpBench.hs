{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
-- | Diagnostic benchmarks for issue #123: separate the cost of producing
-- a gradient program (tracing, differentiation, simplification) from the
-- cost of executing it, for the two pipelines that produce one — symbolic
-- AD and the vectorized handwritten gradient.
--
-- The groups @6x6@ to @192x192@ sweep the gradient of conv2dSameS with
-- respect to the kernels across those image sizes; the @inp-*@ groups run
-- the same variants and sizes for the gradient with respect to the input
-- image (the @sscatter@ path). Each group holds the variants below in
-- @S-@/@H-@ pairs — @S@ for Symbolic and @H@ for Handwritten, the issue's
-- names for the two pipelines — each @H-@ variant measuring the same
-- stage as its adjacent @S-@ partner, with the incoming cotangent kept as
-- a variable on both sides (only @H-fullpipe@ embeds it as a constant,
-- because the tasty benchmark it mirrors does). The pairs decompose the
-- costs that the QuickCheck poor man's benchmarks in TestConvQuickCheck
-- conflate:
--
-- * @S-fullpipe-honest@ and @H-fullpipe@: the full per-call pipelines
--   those tasty benchmarks time (the issue's Symbolic and
--   HandwrittenVectorized) — @vjp@, i.e., tracing + AD + simplification +
--   interpretation, with the per-call-varying input baked into the
--   objective so the artifact is genuinely rebuilt every call, vs
--   building + vectorizing + interpreting the handwritten term, never
--   contracted.
-- * @S-artifact@ and @H-term@: the compilation cost only — building and
--   simplifying the gradient artifact vs building and contracting the
--   handwritten term, forced to WHNF (StrictData makes that a full
--   build), as in mnistTrainBench2VTC in BenchMnistTools.
-- * @S-exec@ and @H-exec@: execution only — interpreting the pre-built
--   simplified artifact vs the pre-built contracted term (the cotangent
--   bound in the environment).
-- * @S-exec-raw@ and @H-exec-raw@: execution of the unsimplified
--   artifact vs the uncontracted term, to see what simplifyArtifactRev
--   and simplifyInlineContract buy at runtime.
--
-- The @cnn-*@ groups run the @S-*@ variants for a real (shaped) two-layer
-- convolutional net (@MnistCnnShaped2.convMnistTwoS@, each layer with
-- maxpool), differentiated with respect to its full parameter tuple, at
-- image sizes 6x6, 12x12 and 24x24. Unlike the synthetic conv2dSame
-- benchmarks they also exercise the maxpool and reshape gathers of a full
-- net; they have no @H-*@ variants, as there is no handwritten CNN gradient
-- to compare against.
--
-- The @gather48@ and @scatter48@ groups isolate the dominant cost: the
-- interpreted im2col gather chains of the 48x48 gradients and their
-- scatter adjoints (see 'gatherBenches' and 'scatterBenches'). The
-- @pitfalls@ group holds the suite's single recorder of each known
-- measurement trap (see 'pitfallBenches'), so the sweep groups contain
-- only honest, pairwise-comparable variants.
--
-- Setting @PRINT_TERMS=1@ prints the compared gradient programs instead
-- of benchmarking (see 'printTerms').
module Main (main) where

import Prelude

import Control.Exception (evaluate)
import Criterion.Main
import GHC.TypeLits (Div, KnownNat, type (*))
import System.Environment (lookupEnv)
import System.Random (mkStdGen)

import Data.Array.Nested.Shaped.Shape (KnownShS, knownShS)

import HordeAd
import HordeAd.Core.Adaptor (randomValue, toTarget)
import HordeAd.Core.AstEnv (emptyEnv, extendEnv)
import HordeAd.Core.AstInterpret (interpretAstFull)

import MnistCnnShaped2 qualified
import MnistData (SizeMnistLabel)
import TestConvQuickCheck (conv2dSame_dInp, conv2dSame_dKrn)
import TestMnistPP (cnnObjective)

forceGrad :: Concrete (TKS sh Double) -> Double
forceGrad = unConcrete . ssum0

-- | The full set of timing variants for the gradient with respect to the
-- kernels, as described in the module haddock.
benchesAt
  :: forall nImgs nCinp nCout nAh nAw nKh nKw.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh, KnownNat nKw )
  => IO [Benchmark]
benchesAt = do
  let (arrK, seed2) =
        randomValue @(Concrete (TKS '[nCout, nCinp, nKh, nKw] Double))
                    0.5 (mkStdGen 42)
      (arrA, seed3) =
        randomValue @(Concrete (TKS '[nImgs, nCinp, nAh, nAw] Double))
                    0.5 seed2
      (arrB, _) =
        randomValue @(Concrete (TKS '[nImgs, nCout, nAh, nAw] Double))
                    0.5 seed3
      f :: AstTensor AstMethodLet FullSpan
                     (TKS '[nCout, nCinp, nKh, nKw] Double)
        -> AstTensor AstMethodLet FullSpan
                     (TKS '[nImgs, nCout, nAh, nAw] Double)
      f k = conv2dSameS k (sconcrete (unConcrete arrA))
      -- The cotangent variable shared by the handwritten-term variants.
      varNameB = mkAstVarName (FTKS (knownShS @'[nImgs, nCout, nAh, nAw])
                                    (FTKScalar @Double))
                              (intToAstVarId 100000099)
      artifactRaw = vjpArtifact f arrK
      artifact = simplifyArtifactRev artifactRaw
      -- The handwritten gradient built as an AST term — constructing it
      -- runs vectorization (sbuild at the AST target) — with the incoming
      -- cotangent kept as a variable, like in the artifact.
      hTermVar :: AstTensor AstMethodLet FullSpan
                            (TKS '[nCout, nCinp, nKh, nKw] Double)
      hTermVar = conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                 (sconcrete (unConcrete arrA))
                                 (AstVar varNameB)
      hTermVarSimplified = simplifyInlineContract hTermVar
  -- Force the shared terms to WHNF (StrictData makes that a full build)
  -- before benchmarking the exec-only variants. WHNF suffices and avoids the
  -- string-formatting work of forcing via printArtifactSimple.
  _ <- evaluate artifactRaw
  _ <- evaluate artifact
  _ <- evaluate hTermVar
  _ <- evaluate hTermVarSimplified
  return
    [ -- vjp per call with the (per-call-varying) input baked into the
      -- objective function, exactly as the tasty poor man's benchmark does:
      -- the artifact genuinely depends on the varying input, so it is
      -- rebuilt every iteration and the full pipeline is honestly measured
      -- (see 'pitfallBenches' for the hoisted variant that secretly isn't).
      bench "S-fullpipe-honest" $ whnf
        (\a -> forceGrad
               $ vjp (\k -> conv2dSameS k (sconcrete (unConcrete a))) arrK arrB)
        arrA
      -- The handwritten counterpart: build + vectorize + interpret per
      -- call; like the tasty benchmark it mirrors, the cotangent is an
      -- embedded constant and the term is never contracted.
    , bench "H-fullpipe" $ whnf
        (\b -> forceGrad $ interpretAstFull emptyEnv
                 $ conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                   (sconcrete (unConcrete arrA))
                                   (sconcrete (unConcrete b))) arrB
      -- Building + simplifying the artifact only (the "compilation" cost),
      -- forced to WHNF as in mnistTrainBench2VTC (BenchMnistTools): with
      -- StrictData that suffices to force the build, and unlike forcing via
      -- printArtifactSimple it does not time string formatting (which grows
      -- with AST size and dwarfs the actual build). The input is the whnf
      -- argument so the body depends on it and criterion re-runs it per call.
    , bench "S-artifact" $ whnf
        (\k -> simplifyArtifactRev (vjpArtifact f k)) arrK
      -- The handwritten counterpart: building + contracting the term only.
    , bench "H-term" $ whnf
        (\a -> simplifyInlineContract
               $ conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                 (sconcrete (unConcrete a))
                                 (AstVar varNameB)) arrA
    , bench "S-exec" $ whnf
        (\dt -> forceGrad
                  (vjpInterpretArtifact artifact arrK dt
                   :: Concrete (TKS '[nCout, nCinp, nKh, nKw] Double))) arrB
      -- The handwritten counterpart: interpret the pre-built contracted
      -- term, the cotangent bound in the environment like in the artifact.
    , bench "H-exec" $ whnf
        (\b -> forceGrad
               $ interpretAstFull (extendEnv varNameB b emptyEnv)
                                  hTermVarSimplified) arrB
    , bench "S-exec-raw" $ whnf
        (\dt -> forceGrad
                  (vjpInterpretArtifact artifactRaw arrK dt
                   :: Concrete (TKS '[nCout, nCinp, nKh, nKw] Double))) arrB
      -- The handwritten counterpart: interpret the uncontracted term.
    , bench "H-exec-raw" $ whnf
        (\b -> forceGrad
               $ interpretAstFull (extendEnv varNameB b emptyEnv)
                                  hTermVar) arrB
    ]

-- | The full set of timing variants for the gradient with respect to the
-- input image (the @sscatter@ path), the analogue of 'benchesAt' for dInp.
benchesInpAt
  :: forall nImgs nCinp nCout nAh nAw nKh nKw.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh, KnownNat nKw )
  => IO [Benchmark]
benchesInpAt = do
  let (arrK, seed2) =
        randomValue @(Concrete (TKS '[nCout, nCinp, nKh, nKw] Double))
                    0.5 (mkStdGen 42)
      (arrA, seed3) =
        randomValue @(Concrete (TKS '[nImgs, nCinp, nAh, nAw] Double))
                    0.5 seed2
      (arrB, _) =
        randomValue @(Concrete (TKS '[nImgs, nCout, nAh, nAw] Double))
                    0.5 seed3
      -- Differentiate with respect to the input, with the kernel baked in.
      g :: AstTensor AstMethodLet FullSpan
                     (TKS '[nImgs, nCinp, nAh, nAw] Double)
        -> AstTensor AstMethodLet FullSpan
                     (TKS '[nImgs, nCout, nAh, nAw] Double)
      g a = conv2dSameS (sconcrete (unConcrete arrK)) a
      varNameB = mkAstVarName (FTKS (knownShS @'[nImgs, nCout, nAh, nAw])
                                    (FTKScalar @Double))
                              (intToAstVarId 100000099)
      artifactRaw = vjpArtifact g arrA
      artifact = simplifyArtifactRev artifactRaw
      hTermVar :: AstTensor AstMethodLet FullSpan
                            (TKS '[nImgs, nCinp, nAh, nAw] Double)
      hTermVar = conv2dSame_dInp @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                 (sconcrete (unConcrete arrK))
                                 (AstVar varNameB)
      hTermVarSimplified = simplifyInlineContract hTermVar
  -- Force to WHNF (a full build under StrictData) before benchmarking.
  _ <- evaluate artifactRaw
  _ <- evaluate artifact
  _ <- evaluate hTermVar
  _ <- evaluate hTermVarSimplified
  -- The same variant pairs as in 'benchesAt', for dInp; see the comments
  -- there.
  return
    [ bench "S-fullpipe-honest" $ whnf
        (\k -> forceGrad
               $ vjp (\a -> conv2dSameS (sconcrete (unConcrete k)) a) arrA arrB)
        arrK
    , bench "H-fullpipe" $ whnf
        (\b -> forceGrad $ interpretAstFull emptyEnv
                 $ conv2dSame_dInp @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                   (sconcrete (unConcrete arrK))
                                   (sconcrete (unConcrete b))) arrB
    , bench "S-artifact" $ whnf
        (\a -> simplifyArtifactRev (vjpArtifact g a)) arrA
    , bench "H-term" $ whnf
        (\k -> simplifyInlineContract
               $ conv2dSame_dInp @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                 (sconcrete (unConcrete k))
                                 (AstVar varNameB)) arrK
    , bench "S-exec" $ whnf
        (\dt -> forceGrad
                  (vjpInterpretArtifact artifact arrA dt
                   :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] Double))) arrB
    , bench "H-exec" $ whnf
        (\b -> forceGrad
               $ interpretAstFull (extendEnv varNameB b emptyEnv)
                                  hTermVarSimplified) arrB
    , bench "S-exec-raw" $ whnf
        (\dt -> forceGrad
                  (vjpInterpretArtifact artifactRaw arrA dt
                   :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] Double))) arrB
    , bench "H-exec-raw" $ whnf
        (\b -> forceGrad
               $ interpretAstFull (extendEnv varNameB b emptyEnv)
                                  hTermVar) arrB
    ]

-- | The @S-*@ variants of 'benchesAt', but for a real (shaped) two-layer
-- convolutional net (@convMnistTwoS@, each layer with maxpool), differentiated
-- with respect to its full parameter tuple. The input image is embedded as a
-- constant — a *random* one, since a constant broadcast folds the convolution
-- gathers away — exactly as 'benchesAt' embeds the input in the conv2dSame
-- objective. The objective is shared with @testCNNOPP2S@ via 'cnnObjective'.
-- There are no @H-*@ variants, as there is no handwritten CNN gradient to
-- compare against.
benchesCnnAt
  :: forall h w. (KnownNat h, KnownNat w, KnownNat (4 * Div h 4 * Div w 4))
  => IO [Benchmark]
benchesCnnAt = do
  let (valsInit, seed2) =
        randomValue @(MnistCnnShaped2.ADCnnMnistParametersShaped
                        Concrete h w 2 3 4 5 Double)
                    0.4 (mkStdGen 44)
      (arrGlyph, seed3) =
        randomValue @(Concrete (TKS '[7, 1, h, w] Double)) 0.5 seed2
      (arrDt, _) =
        randomValue @(Concrete (TKS '[SizeMnistLabel, 7] Double)) 0.5 seed3
      valsInitT = toTarget @Concrete valsInit
      -- Force the full parameter gradient (a tuple) by summing all leaves,
      -- reusing forceGrad (unConcrete . ssum0) on each.
      forceCnnGrad ((k1, b1), (k2, b2), (wd, bd), (wr, br)) =
        forceGrad k1 + forceGrad b1 + forceGrad k2 + forceGrad b2
        + forceGrad wd + forceGrad bd + forceGrad wr + forceGrad br
      f = cnnObjective arrGlyph
      artifactRaw = vjpArtifact f valsInit
      artifact = simplifyArtifactRev artifactRaw
  _ <- evaluate artifactRaw
  _ <- evaluate artifact
  return
    [ bench "S-fullpipe-honest" $ whnf
        (\glyph -> forceCnnGrad $ vjp (cnnObjective glyph) valsInit arrDt)
        arrGlyph
    , bench "S-artifact" $ whnf
        (\v -> simplifyArtifactRev (vjpArtifact f v)) valsInit
    , bench "S-exec" $ whnf
        (\dt -> forceCnnGrad
                  (vjpInterpretArtifact artifact valsInitT dt
                   :: MnistCnnShaped2.ADCnnMnistParametersShaped
                        Concrete h w 2 3 4 5 Double)) arrDt
    , bench "S-exec-raw" $ whnf
        (\dt -> forceCnnGrad
                  (vjpInterpretArtifact artifactRaw valsInitT dt
                   :: MnistCnnShaped2.ADCnnMnistParametersShaped
                        Concrete h w 2 3 4 5 Double)) arrDt
    ]

-- | Micro-benchmarks for the dominant cost found by profiling: the
-- interpreted im2col gather chains. Four comparisons: the AD-produced
-- orientation (large dim first in the gather output, small dims
-- innermost in the copied slices) vs the vectorization-produced one
-- (small dim first, large dim innermost in slices); the AD orientation
-- vs its two candidate canonicalizations (shm dims sorted vs shn dims
-- sorted); both orientations vs a single fused gather that avoids the
-- intermediate array entirely; and the fused gather vs itself with its
-- shm dims sorted, ascending and descending — its shn, @[3, 3]@, is
-- already sorted, fusion having consumed the large dims into the index
-- function, so shm is the fused form's only sortable knob.
-- interpretAstFull does not run contractAst, so each variant times
-- exactly the orientation written.
gatherBenches :: IO [Benchmark]
gatherBenches = do
  let (arr1, seed2) =
        randomValue @(Concrete (TKS '[50, 3, 3, 50] Double))
                    0.5 (mkStdGen 42)
      (arr2, _) =
        randomValue @(Concrete (TKS '[50, 50, 3, 3] Double))
                    0.5 seed2
      src1, src1'
        :: AstTensor AstMethodLet FullSpan (TKS '[50, 3, 3, 50] Double)
      src1 = sconcrete (unConcrete arr1)
      src1' = sconcrete (unConcrete arr1)
      src2 :: AstTensor AstMethodLet FullSpan (TKS '[50, 50, 3, 3] Double)
      src2 = sconcrete (unConcrete arr2)
      -- The AD orientation: sgather @[48,3], big dim first.
      twoAd :: AstTensor AstMethodLet FullSpan
                        (TKS '[48, 3, 3, 48, 3, 3] Double)
      twoAd =
        sgather @'[48, 3] @'[3, 48, 3, 3] @'[50]
                (stranspose @'[4, 2, 0, 3, 1]
                   (sgather @'[48, 3] @'[3, 3, 50] @'[50]
                            src1
                            (\case [a, b] -> [a + b]
                                   _ -> error "twoAd")))
                (\case [c, d] -> [c + d]
                       _ -> error "twoAd")
      -- The vectorization orientation: sgather @[3,48], small dim first.
      twoVec :: AstTensor AstMethodLet FullSpan
                        (TKS '[3, 48, 3, 3, 3, 48] Double)
      twoVec =
        sgather @'[3, 48] @'[3, 3, 3, 48] @'[50]
                (stranspose @'[4, 2, 0, 3, 1]
                   (sgather @'[3, 48] @'[3, 3, 50] @'[50]
                            src1'
                            (\case [b, a] -> [a + b]
                                   _ -> error "twoVec")))
                (\case [d, c] -> [c + d]
                       _ -> error "twoVec")
      -- The AD chain with each gather's shm dims sorted ascending and a
      -- compensating transpose above that restores the original dim order —
      -- a canonicalization considered for contractAst and refuted by this
      -- measurement: the concrete gather's cost is per output position,
      -- so reordering the shm dims changes nothing.
      canonShm :: AstTensor AstMethodLet FullSpan
                          (TKS '[48, 3, 3, 48, 3, 3] Double)
      canonShm =
        stranspose @'[1, 0]
          (sgather @'[3, 48] @'[3, 48, 3, 3] @'[50]
                   (stranspose @'[4, 2, 0, 3, 1]
                      (stranspose @'[1, 0]
                         (sgather @'[3, 48] @'[3, 3, 50] @'[50]
                                  src1
                                  (\case [b, a] -> [a + b]
                                         _ -> error "canonShm"))))
                   (\case [d, c] -> [c + d]
                          _ -> error "canonShm"))
      -- The AD chain with the second gather's shn dims sorted ascending
      -- instead (large dims innermost in the copied slices), by a
      -- transpose below the gather (merges into the existing view)
      -- and a compensating transpose above — the rewrite the shn-sort
      -- rule in contractAst now performs on such chains (the first
      -- gather's shn is already sorted, so it is left alone).
      canonShn :: AstTensor AstMethodLet FullSpan
                           (TKS '[48, 3, 3, 48, 3, 3] Double)
      canonShn =
        stranspose @'[0, 1, 2, 5, 3, 4]
          (sgather @'[48, 3] @'[3, 3, 3, 48] @'[50]
                   (stranspose @'[0, 1, 3, 4, 2]
                      (stranspose @'[4, 2, 0, 3, 1]
                         (sgather @'[48, 3] @'[3, 3, 50] @'[50]
                                  src1
                                  (\case [a, b] -> [a + b]
                                         _ -> error "canonShn"))))
                   (\case [c, d] -> [c + d]
                          _ -> error "canonShn"))
      -- One fused gather, AD orientation of the output dims.
      fusedAd :: AstTensor AstMethodLet FullSpan
                          (TKS '[48, 3, 48, 3, 3, 3] Double)
      fusedAd =
        sgather @'[48, 3, 48, 3] @'[3, 3] @'[50, 50]
                src2
                (\case [h, kh, w, kw] -> [h + kh, w + kw]
                       _ -> error "fusedAd")
      -- One fused gather, vectorization orientation of the output dims.
      fusedVec :: AstTensor AstMethodLet FullSpan
                          (TKS '[3, 48, 3, 48, 3, 3] Double)
      fusedVec =
        sgather @'[3, 48, 3, 48] @'[3, 3] @'[50, 50]
                src2
                (\case [kh, h, kw, w] -> [h + kh, w + kw]
                       _ -> error "fusedVec")
      -- The fused gather with its shm dims sorted ascending and a
      -- compensating transpose above restoring the AD output order.
      -- Its shn is [3, 3] — already sorted, fusion having consumed the
      -- large dims into the index function — so shm order is the only
      -- sortable knob of the fused form; it is benchmarked in both
      -- directions to record that sorting cannot rescue fusion: the
      -- cost is per output position, and the position count is exactly
      -- what fusion inflates.
      fusedShmAsc :: AstTensor AstMethodLet FullSpan
                              (TKS '[48, 3, 48, 3, 3, 3] Double)
      fusedShmAsc =
        stranspose @'[2, 0, 3, 1, 4, 5]
          (sgather @'[3, 3, 48, 48] @'[3, 3] @'[50, 50]
                   src2
                   (\case [kh, kw, h, w] -> [h + kh, w + kw]
                          _ -> error "fusedShmAsc"))
      -- The same with the shm dims sorted descending.
      fusedShmDesc :: AstTensor AstMethodLet FullSpan
                               (TKS '[48, 3, 48, 3, 3, 3] Double)
      fusedShmDesc =
        stranspose @'[0, 2, 1, 3, 4, 5]
          (sgather @'[48, 48, 3, 3] @'[3, 3] @'[50, 50]
                   src2
                   (\case [h, w, kh, kw] -> [h + kh, w + kw]
                          _ -> error "fusedShmDesc"))
  -- Force to WHNF (a full build under StrictData) before benchmarking.
  _ <- evaluate twoAd
  _ <- evaluate twoVec
  _ <- evaluate canonShm
  _ <- evaluate canonShn
  _ <- evaluate fusedAd
  _ <- evaluate fusedVec
  _ <- evaluate fusedShmAsc
  _ <- evaluate fusedShmDesc
  return
    [ bench "two-gathers-ad-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoAd
    , bench "two-gathers-vec-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoVec
    , bench "two-gathers-ad-shm-sorted" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) canonShm
    , bench "two-gathers-ad-shn-sorted" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) canonShn
    , bench "fused-gather-ad-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedAd
    , bench "fused-gather-vec-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedVec
    , bench "fused-gather-shm-sorted-asc" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedShmAsc
    , bench "fused-gather-shm-sorted-desc" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedShmDesc
    ]

-- | Verify that a hand-built scatter chain is the adjoint (transpose) of the
-- corresponding gather chain, via the adjoint law that holds iff scatter is
-- gather's transpose: for all index functions @f@, sources @x@ and
-- cotangents @y@, @sdot0 (sgather x f) y == sdot0 x (sscatter y f)@. Errors
-- loudly if the scatter chain was built with wrong shapes or index
-- directions.
checkAdjoint
  :: (KnownShS shSrc, KnownShS shOut)
  => String
  -> AstTensor AstMethodLet FullSpan (TKS shOut Double)
       -- ^ gather chain, over @src@
  -> Concrete (TKS shSrc Double)
       -- ^ the source @x@
  -> AstTensor AstMethodLet FullSpan (TKS shSrc Double)
       -- ^ scatter chain, over @y@
  -> Concrete (TKS shOut Double)
       -- ^ the cotangent @y@
  -> IO ()
checkAdjoint name gatherChain src scatterChain y =
  let gOut = interpretAstFull emptyEnv gatherChain
      sOut = interpretAstFull emptyEnv scatterChain
      lhs = unConcrete (sdot0 gOut y)
      rhs = unConcrete (sdot0 src sOut)
  in if abs (lhs - rhs) <= 1e-6 * (1 + abs lhs)
     then pure ()
     else error $ name ++ ": scatter is not the adjoint of gather: "
                  ++ "sdot0 (sgather x f) y=" ++ show lhs
                  ++ " sdot0 x (sscatter y f)=" ++ show rhs

-- | The scatter analogue of 'gatherBenches': the interpreted scatter chains
-- that appear in the input-image gradient (the @sscatter@ path). Each chain
-- is the exact adjoint (transpose) of the corresponding gather chain above —
-- verified at startup by 'checkAdjoint' — so this isolates the scatter cost
-- the way 'gatherBenches' isolates the gather cost. The correspondence is
-- deliberately partial: the shn-sorted chain's adjoint is included — it
-- measures the ruling that the shn-sort must not be extended to scatter
-- (a ~4x pessimization: scatter adds each slice as one flat vector, so a
-- sorted shn has no per-shn-dim loop to amortize, while the compensating
-- transposes leave the slice views strided) — but there are no shm-sorted
-- or fused-sorted adjoints, which would only re-measure knobs
-- 'gatherBenches' already shows dead.
scatterBenches :: IO [Benchmark]
scatterBenches = do
  let (arrX1, seedb) =
        randomValue @(Concrete (TKS '[50, 3, 3, 50] Double)) 0.5 (mkStdGen 43)
      (arrX2, seedc) =
        randomValue @(Concrete (TKS '[50, 50, 3, 3] Double)) 0.5 seedb
      (arrY1, seedd) =
        randomValue @(Concrete (TKS '[48, 3, 3, 48, 3, 3] Double)) 0.5 seedc
      (arrY2, seede) =
        randomValue @(Concrete (TKS '[3, 48, 3, 3, 3, 48] Double)) 0.5 seedd
      (arrY3, seedf) =
        randomValue @(Concrete (TKS '[48, 3, 48, 3, 3, 3] Double)) 0.5 seede
      (arrY4, _) =
        randomValue @(Concrete (TKS '[3, 48, 3, 48, 3, 3] Double)) 0.5 seedf
      x1 :: AstTensor AstMethodLet FullSpan (TKS '[50, 3, 3, 50] Double)
      x1 = sconcrete (unConcrete arrX1)
      x2 :: AstTensor AstMethodLet FullSpan (TKS '[50, 50, 3, 3] Double)
      x2 = sconcrete (unConcrete arrX2)
      y1 :: AstTensor AstMethodLet FullSpan (TKS '[48, 3, 3, 48, 3, 3] Double)
      y1 = sconcrete (unConcrete arrY1)
      y2 :: AstTensor AstMethodLet FullSpan (TKS '[3, 48, 3, 3, 3, 48] Double)
      y2 = sconcrete (unConcrete arrY2)
      y3 :: AstTensor AstMethodLet FullSpan (TKS '[48, 3, 48, 3, 3, 3] Double)
      y3 = sconcrete (unConcrete arrY3)
      y4 :: AstTensor AstMethodLet FullSpan (TKS '[3, 48, 3, 48, 3, 3] Double)
      y4 = sconcrete (unConcrete arrY4)
      -- The gather chains from 'gatherBenches', rebuilt over x1/x2 as
      -- checkAdjoint fixtures only — benchmarked there, not here (gather
      -- cost is structural, so timing these copies would just duplicate
      -- those benches).
      gTwoAd :: AstTensor AstMethodLet FullSpan
                         (TKS '[48, 3, 3, 48, 3, 3] Double)
      gTwoAd =
        sgather @'[48, 3] @'[3, 48, 3, 3] @'[50]
                (stranspose @'[4, 2, 0, 3, 1]
                   (sgather @'[48, 3] @'[3, 3, 50] @'[50] x1
                            (\case [a, b] -> [a + b]
                                   _ -> error "gTwoAd")))
                (\case [c, d] -> [c + d]
                       _ -> error "gTwoAd")
      gTwoVec :: AstTensor AstMethodLet FullSpan
                         (TKS '[3, 48, 3, 3, 3, 48] Double)
      gTwoVec =
        sgather @'[3, 48] @'[3, 3, 3, 48] @'[50]
                (stranspose @'[4, 2, 0, 3, 1]
                   (sgather @'[3, 48] @'[3, 3, 50] @'[50] x1
                            (\case [b, a] -> [a + b]
                                   _ -> error "gTwoVec")))
                (\case [d, c] -> [c + d]
                       _ -> error "gTwoVec")
      gCanonShn :: AstTensor AstMethodLet FullSpan
                            (TKS '[48, 3, 3, 48, 3, 3] Double)
      gCanonShn =
        stranspose @'[0, 1, 2, 5, 3, 4]
          (sgather @'[48, 3] @'[3, 3, 3, 48] @'[50]
                   (stranspose @'[0, 1, 3, 4, 2]
                      (stranspose @'[4, 2, 0, 3, 1]
                         (sgather @'[48, 3] @'[3, 3, 50] @'[50]
                                  x1
                                  (\case [a, b] -> [a + b]
                                         _ -> error "gCanonShn"))))
                   (\case [c, d] -> [c + d]
                          _ -> error "gCanonShn"))
      gFusedAd :: AstTensor AstMethodLet FullSpan
                           (TKS '[48, 3, 48, 3, 3, 3] Double)
      gFusedAd =
        sgather @'[48, 3, 48, 3] @'[3, 3] @'[50, 50] x2
                (\case [h, kh, w, kw] -> [h + kh, w + kw]
                       _ -> error "gFusedAd")
      gFusedVec :: AstTensor AstMethodLet FullSpan
                           (TKS '[3, 48, 3, 48, 3, 3] Double)
      gFusedVec =
        sgather @'[3, 48, 3, 48] @'[3, 3] @'[50, 50] x2
                (\case [kh, h, kw, w] -> [h + kh, w + kw]
                       _ -> error "gFusedVec")
      -- The scatter chains: exact adjoints of the gather chains above.
      -- The two-op chains reverse the composition order and invert the
      -- connecting transpose (@[4,2,0,3,1]@ becomes @[2,4,1,3,0]@).
      twoScatterAd :: AstTensor AstMethodLet FullSpan
                               (TKS '[50, 3, 3, 50] Double)
      twoScatterAd =
        sscatter @'[48, 3] @'[3, 3, 50] @'[50]
                 (stranspose @'[2, 4, 1, 3, 0]
                    (sscatter @'[48, 3] @'[3, 48, 3, 3] @'[50] y1
                              (\case [c, d] -> [c + d]
                                     _ -> error "twoScatterAd")))
                 (\case [a, b] -> [a + b]
                        _ -> error "twoScatterAd")
      twoScatterVec :: AstTensor AstMethodLet FullSpan
                               (TKS '[50, 3, 3, 50] Double)
      twoScatterVec =
        sscatter @'[3, 48] @'[3, 3, 50] @'[50]
                 (stranspose @'[2, 4, 1, 3, 0]
                    (sscatter @'[3, 48] @'[3, 3, 3, 48] @'[50] y2
                              (\case [d, c] -> [c + d]
                                     _ -> error "twoScatterVec")))
                 (\case [b, a] -> [a + b]
                        _ -> error "twoScatterVec")
      -- The adjoint of the shn-sorted chain ('canonShn' in 'gatherBenches'),
      -- on the same cotangent as twoScatterAd: measures the ruling that the
      -- shn-sort must not be extended to scatter — and strengthens it from
      -- "cannot pay" to a measured ~4x pessimization: scatter adds each
      -- slice as one flat vector, so a sorted shn has no per-shn-dim loop
      -- to amortize, while the compensating transposes leave the slice
      -- views strided.
      twoScatterShnSorted :: AstTensor AstMethodLet FullSpan
                                       (TKS '[50, 3, 3, 50] Double)
      twoScatterShnSorted =
        sscatter @'[48, 3] @'[3, 3, 50] @'[50]
                 (stranspose @'[2, 4, 1, 3, 0]
                    (stranspose @'[0, 1, 4, 2, 3]
                       (sscatter @'[48, 3] @'[3, 3, 3, 48] @'[50]
                                 (stranspose @'[0, 1, 2, 4, 5, 3] y1)
                                 (\case [c, d] -> [c + d]
                                        _ -> error "twoScatterShnSorted"))))
                 (\case [a, b] -> [a + b]
                        _ -> error "twoScatterShnSorted")
      fusedScatterAd :: AstTensor AstMethodLet FullSpan
                                 (TKS '[50, 50, 3, 3] Double)
      fusedScatterAd =
        sscatter @'[48, 3, 48, 3] @'[3, 3] @'[50, 50] y3
                 (\case [h, kh, w, kw] -> [h + kh, w + kw]
                        _ -> error "fusedScatterAd")
      fusedScatterVec :: AstTensor AstMethodLet FullSpan
                                 (TKS '[50, 50, 3, 3] Double)
      fusedScatterVec =
        sscatter @'[3, 48, 3, 48] @'[3, 3] @'[50, 50] y4
                 (\case [kh, h, kw, w] -> [h + kh, w + kw]
                        _ -> error "fusedScatterVec")
  checkAdjoint "two-scatters-ad-orient" gTwoAd arrX1 twoScatterAd arrY1
  checkAdjoint "two-scatters-vec-orient" gTwoVec arrX1 twoScatterVec arrY2
  checkAdjoint "two-scatters-ad-shn-sorted"
               gCanonShn arrX1 twoScatterShnSorted arrY1
  checkAdjoint "fused-scatter-ad-orient" gFusedAd arrX2 fusedScatterAd arrY3
  checkAdjoint "fused-scatter-vec-orient" gFusedVec arrX2 fusedScatterVec arrY4
  -- Force to WHNF (a full build under StrictData) before benchmarking.
  _ <- evaluate twoScatterAd
  _ <- evaluate twoScatterVec
  _ <- evaluate twoScatterShnSorted
  _ <- evaluate fusedScatterAd
  _ <- evaluate fusedScatterVec
  return
    [ bench "two-scatters-ad-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoScatterAd
    , bench "two-scatters-vec-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoScatterVec
    , bench "two-scatters-ad-shn-sorted" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoScatterShnSorted
    , bench "fused-scatter-ad-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedScatterAd
    , bench "fused-scatter-vec-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedScatterVec
    ]

-- | The suite's single recorder of each known benchmarking pitfall, one
-- variant at one size apiece, kept out of the sweep groups so those
-- contain only honest, pairwise-comparable variants. The data matches
-- the corresponding 'benchesAt' group (same seed chain), so each bench
-- is directly comparable against its honest counterparts there.
pitfallBenches :: IO [Benchmark]
pitfallBenches = do
  let -- The dKrn data of 'benchesAt'; the kernel shape is size-independent,
      -- so seed2 continues both the 6x6 and the 48x48 chain.
      (arrK, seed2) =
        randomValue @(Concrete (TKS '[3, 3, 3, 3] Double)) 0.5 (mkStdGen 42)
      (arrA6, seed3) =
        randomValue @(Concrete (TKS '[3, 3, 6, 6] Double)) 0.5 seed2
      (arrB6, _) =
        randomValue @(Concrete (TKS '[3, 3, 6, 6] Double)) 0.5 seed3
      (arrA48, seed3') =
        randomValue @(Concrete (TKS '[3, 3, 48, 48] Double)) 0.5 seed2
      (arrB48, _) =
        randomValue @(Concrete (TKS '[3, 3, 48, 48] Double)) 0.5 seed3'
      f6 :: AstTensor AstMethodLet FullSpan (TKS '[3, 3, 3, 3] Double)
         -> AstTensor AstMethodLet FullSpan (TKS '[3, 3, 6, 6] Double)
      f6 k = conv2dSameS k (sconcrete (unConcrete arrA6))
      -- The handwritten term with the cotangent embedded as a constant,
      -- as in the term the tasty poor man's benchmark interprets.
      hTermConst :: AstTensor AstMethodLet FullSpan (TKS '[3, 3, 3, 3] Double)
      hTermConst = conv2dSame_dKrn @3 @3 @3 @48 @48 @3 @3
                                   (sconcrete (unConcrete arrA48))
                                   (sconcrete (unConcrete arrB48))
      hTermConstSimplified = simplifyInlineContract hTermConst
  -- Force to WHNF (a full build under StrictData) before benchmarking.
  _ <- evaluate hTermConstSimplified
  return
    [ -- vjp per call, but with the objective and its input fixed and only
      -- the cotangent varying. The artifact does not depend on the
      -- cotangent, so full laziness floats its construction out of the
      -- timed loop and the artifact tax — the bulk of an honest 6x6 call —
      -- goes unmeasured. Compare against S-fullpipe-honest (the tax
      -- included) and S-exec in the 6x6 group.
      bench "S-fullpipe-hoisted-6x6" $ whnf
        (\dt -> forceGrad $ vjp f6 arrK dt) arrB6
      -- As H-exec in the 48x48 group, but with the cotangent embedded as
      -- a random concrete constant. Records that the embedding is
      -- harmless: this measures the same as H-exec, i.e., simplification
      -- does not constant-fold a random embedded constant through the
      -- gathers — a broadcast constant it would fold, which is why
      -- benchmark inputs are random.
    , bench "H-exec-const-48x48" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) hTermConstSimplified
    ]

-- | Print the two gradient programs being compared instead of benchmarking,
-- for structural comparison.
printTerms
  :: forall nImgs nCinp nCout nAh nAw nKh nKw.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh, KnownNat nKw )
  => IO ()
printTerms = do
  let (arrK, seed2) =
        randomValue @(Concrete (TKS '[nCout, nCinp, nKh, nKw] Double))
                    0.5 (mkStdGen 42)
      (arrA, seed3) =
        randomValue @(Concrete (TKS '[nImgs, nCinp, nAh, nAw] Double))
                    0.5 seed2
      (arrB, _) =
        randomValue @(Concrete (TKS '[nImgs, nCout, nAh, nAw] Double))
                    0.5 seed3
      f :: AstTensor AstMethodLet FullSpan
                     (TKS '[nCout, nCinp, nKh, nKw] Double)
        -> AstTensor AstMethodLet FullSpan
                     (TKS '[nImgs, nCout, nAh, nAw] Double)
      f k = conv2dSameS k (sconcrete (unConcrete arrA))
      artifact = simplifyArtifactRev (vjpArtifact f arrK)
      hTerm :: AstTensor AstMethodLet FullSpan
                         (TKS '[nCout, nCinp, nKh, nKw] Double)
      hTerm = conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                              (sconcrete (unConcrete arrA))
                              (sconcrete (unConcrete arrB))
      hTermSimplified = simplifyInlineContract hTerm
      varNameB = mkAstVarName (FTKS (knownShS @'[nImgs, nCout, nAh, nAw])
                                    (FTKScalar @Double))
                              (intToAstVarId 100000099)
      hTermVar :: AstTensor AstMethodLet FullSpan
                            (TKS '[nCout, nCinp, nKh, nKw] Double)
      hTermVar = conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                 (sconcrete (unConcrete arrA))
                                 (AstVar varNameB)
  putStrLn "=== S: simplified artifact (derivative) ==="
  putStrLn $ printArtifactPretty artifact
  putStrLn "=== H: contracted handwritten-vectorized term ==="
  putStrLn $ printAstPretty hTermSimplified
  putStrLn "=== H-var: contracted handwritten term, symbolic dret ==="
  putStrLn $ printAstPretty (simplifyInlineContract hTermVar)

main :: IO ()
main = do
  printMode <- lookupEnv "PRINT_TERMS"
  case printMode of
    Just _ -> printTerms @3 @3 @3 @6 @6 @3 @3
    Nothing -> do
      b6 <- benchesAt @3 @3 @3 @6 @6 @3 @3
      b24 <- benchesAt @3 @3 @3 @24 @24 @3 @3
      b48 <- benchesAt @3 @3 @3 @48 @48 @3 @3
      b96 <- benchesAt @3 @3 @3 @96 @96 @3 @3
      b192 <- benchesAt @3 @3 @3 @192 @192 @3 @3
      i6 <- benchesInpAt @3 @3 @3 @6 @6 @3 @3
      i24 <- benchesInpAt @3 @3 @3 @24 @24 @3 @3
      i48 <- benchesInpAt @3 @3 @3 @48 @48 @3 @3
      i96 <- benchesInpAt @3 @3 @3 @96 @96 @3 @3
      i192 <- benchesInpAt @3 @3 @3 @192 @192 @3 @3
      cnn6 <- benchesCnnAt @6 @6
      cnn12 <- benchesCnnAt @12 @12
      cnn24 <- benchesCnnAt @24 @24
      bg <- gatherBenches
      bs <- scatterBenches
      pf <- pitfallBenches
      defaultMain
        [ bgroup "6x6" b6
        , bgroup "24x24" b24
        , bgroup "48x48" b48
        , bgroup "96x96" b96
        , bgroup "192x192" b192
        , bgroup "inp-6x6" i6
        , bgroup "inp-24x24" i24
        , bgroup "inp-48x48" i48
        , bgroup "inp-96x96" i96
        , bgroup "inp-192x192" i192
        , bgroup "cnn-6x6" cnn6
        , bgroup "cnn-12x12" cnn12
        , bgroup "cnn-24x24" cnn24
        , bgroup "gather48" bg
        , bgroup "scatter48" bs
        , bgroup "pitfalls" pf
        ]
