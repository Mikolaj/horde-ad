{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
-- | Diagnostic benchmarks for issue #123: separate the cost of the
-- symbolic AD pipeline (tracing, differentiation, simplification)
-- from the cost of executing the resulting gradient program,
-- for the gradient of conv2dSameS with respect to the kernels,
-- at several array sizes.
--
-- Variants, mirroring the QuickCheck poor man's benchmarks
-- in TestConvQuickCheck:
--
-- * @S-fullpipe@: @vjp@ per call, i.e., tracing + AD + simplification
--   + interpretation every time (this is what the issue calls Symbolic),
--   in a @-hoisted@ variant (artifact floated out of the timed loop) and a
--   @-honest@ variant (artifact rebuilt every call).
-- * @S-artifact@: building + simplifying the gradient artifact only (the
--   compilation cost), forced to WHNF (StrictData suffices), as in
--   mnistTrainBench2VTC in BenchMnistTools.
-- * @S-exec@: interpreting a pre-computed simplified artifact only.
-- * @S-exec-raw@: interpreting a pre-computed unsimplified artifact,
--   to see what simplifyArtifactRev buys at runtime.
-- * @H-fullpipe@: building + vectorizing + interpreting the handwritten
--   gradient term per call (what the issue calls HandwrittenVectorized).
-- * @H-exec@: interpreting the pre-built handwritten gradient term only.
-- * @H-exec-contracted@: as @H-exec@, but after @simplifyInlineContract@.
-- * @H-exec-var@: as @H-exec-contracted@, but with the cotangent kept as a
--   variable (like in the artifact); the apples-to-apples comparison
--   against @S-exec@.
--
-- The @inp-*@ groups run the same variants for the gradient with respect
-- to the input image (the @sscatter@ path) instead of the kernels, and the
-- size sweep goes up to 192x192 images.
module Main (main) where

import Prelude

import Control.Exception (evaluate)
import Criterion.Main
import GHC.TypeLits (KnownNat)
import System.Environment (lookupEnv)
import System.Random (mkStdGen)

import Data.Array.Nested.Shaped.Shape (KnownShS, knownShS)

import HordeAd
import HordeAd.Core.Adaptor (randomValue)
import HordeAd.Core.AstEnv (emptyEnv, extendEnv)
import HordeAd.Core.AstInterpret (interpretAstFull)

import TestConvQuickCheck (conv2dSame_dInp, conv2dSame_dKrn)

forceGrad :: Concrete (TKS sh Double) -> Double
forceGrad = unConcrete . ssum0

-- | Verify that a hand-built scatter chain is the adjoint (transpose) of the
-- corresponding gather chain, via the identity @<gather(x), y> = <x,
-- scatter(y)>@ that holds iff scatter is gather's transpose. Errors loudly
-- if the scatter chain was built with wrong shapes or index directions.
checkAdjoint
  :: (KnownShS shSrc, KnownShS shOut)
  => String
  -> AstTensor AstMethodLet FullSpan (TKS shOut Double)  -- ^ gather chain, over @src@
  -> Concrete (TKS shSrc Double)                         -- ^ the source @x@
  -> AstTensor AstMethodLet FullSpan (TKS shSrc Double)  -- ^ scatter chain, over @y@
  -> Concrete (TKS shOut Double)                         -- ^ the cotangent @y@
  -> IO ()
checkAdjoint name gatherChain src scatterChain y =
  let gOut = interpretAstFull emptyEnv gatherChain
      sOut = interpretAstFull emptyEnv scatterChain
      lhs = unConcrete (sdot0 gOut y)
      rhs = unConcrete (sdot0 src sOut)
  in if abs (lhs - rhs) <= 1e-6 * (1 + abs lhs)
     then pure ()
     else error $ name ++ ": scatter is not the adjoint of gather: "
                  ++ "<gather(x),y>=" ++ show lhs ++ " <x,scatter(y)>=" ++ show rhs

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
      f :: AstTensor AstMethodLet FullSpan (TKS '[nCout, nCinp, nKh, nKw] Double)
        -> AstTensor AstMethodLet FullSpan (TKS '[nImgs, nCout, nAh, nAw] Double)
      f k = conv2dSameS k (sconcrete (unConcrete arrA))
      -- The handwritten gradient built as an AST term; constructing it
      -- runs vectorization (sbuild at the AST target).
      hTerm :: AstTensor AstMethodLet FullSpan (TKS '[nCout, nCinp, nKh, nKw] Double)
      hTerm = conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                              (sconcrete (unConcrete arrA))
                              (sconcrete (unConcrete arrB))
      hTermSimplified = simplifyInlineContract hTerm
      -- The handwritten gradient with the incoming cotangent kept
      -- as a variable, like in the artifact, so that simplification
      -- can't constant-fold the cotangent side of the term.
      varNameB = mkAstVarName (FTKS (knownShS @'[nImgs, nCout, nAh, nAw])
                                    (FTKScalar @Double))
                              (intToAstVarId 100000099)
      hTermVar :: AstTensor AstMethodLet FullSpan (TKS '[nCout, nCinp, nKh, nKw] Double)
      hTermVar = conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                 (sconcrete (unConcrete arrA))
                                 (AstVar varNameB)
      hTermVarSimplified = simplifyInlineContract hTermVar
      artifactRaw = vjpArtifact f arrK
      artifact = simplifyArtifactRev artifactRaw
  -- Force the shared terms to WHNF (StrictData makes that a full build)
  -- before benchmarking the exec-only variants. WHNF suffices and avoids the
  -- string-formatting work of forcing via printArtifactSimple.
  _ <- evaluate hTerm
  _ <- evaluate hTermSimplified
  _ <- evaluate hTermVarSimplified
  _ <- evaluate artifact
  _ <- evaluate artifactRaw
  return
    [ -- vjp per call, but with f and arrK fixed and only dt varying.
      -- The artifact does not depend on dt, so full-laziness floats its
      -- construction out of the timed loop: this secretly measures ~exec.
      bench "S-fullpipe-hoisted" $ whnf
        (\dt -> forceGrad $ vjp f arrK dt) arrB
      -- vjp per call with the (per-call-varying) input baked into the
      -- objective function, exactly as the tasty poor man's benchmark does.
      -- Now the artifact genuinely depends on the varying input, so it is
      -- rebuilt every iteration: this honestly measures the full pipeline.
    , bench "S-fullpipe-honest" $ whnf
        (\a -> forceGrad
               $ vjp (\k -> conv2dSameS k (sconcrete (unConcrete a))) arrK arrB)
        arrA
      -- Building + simplifying the artifact only (the "compilation" cost),
      -- forced to WHNF as in mnistTrainBench2VTC (BenchMnistTools): with
      -- StrictData that suffices to force the build, and unlike forcing via
      -- printArtifactSimple it does not time string formatting (which grows
      -- with AST size and dwarfs the actual build). The input is the whnf
      -- argument so the body depends on it and criterion re-runs it per call.
    , bench "S-artifact" $ whnf
        (\k -> simplifyArtifactRev (vjpArtifact f k)) arrK
    , bench "S-exec" $ whnf
        (\dt -> forceGrad
                  (vjpInterpretArtifact artifact arrK dt
                   :: Concrete (TKS '[nCout, nCinp, nKh, nKw] Double))) arrB
    , bench "S-exec-raw" $ whnf
        (\dt -> forceGrad
                  (vjpInterpretArtifact artifactRaw arrK dt
                   :: Concrete (TKS '[nCout, nCinp, nKh, nKw] Double))) arrB
    , bench "H-fullpipe" $ whnf
        (\b -> forceGrad $ interpretAstFull emptyEnv
                 $ conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                   (sconcrete (unConcrete arrA))
                                   (sconcrete (unConcrete b))) arrB
    , bench "H-exec" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) hTerm
    , bench "H-exec-contracted" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) hTermSimplified
    , bench "H-exec-var" $ whnf
        (\b -> forceGrad
               $ interpretAstFull (extendEnv varNameB b emptyEnv)
                                  hTermVarSimplified) arrB
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
      g :: AstTensor AstMethodLet FullSpan (TKS '[nImgs, nCinp, nAh, nAw] Double)
        -> AstTensor AstMethodLet FullSpan (TKS '[nImgs, nCout, nAh, nAw] Double)
      g a = conv2dSameS (sconcrete (unConcrete arrK)) a
      hTerm :: AstTensor AstMethodLet FullSpan (TKS '[nImgs, nCinp, nAh, nAw] Double)
      hTerm = conv2dSame_dInp @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                              (sconcrete (unConcrete arrK))
                              (sconcrete (unConcrete arrB))
      hTermSimplified = simplifyInlineContract hTerm
      varNameB = mkAstVarName (FTKS (knownShS @'[nImgs, nCout, nAh, nAw])
                                    (FTKScalar @Double))
                              (intToAstVarId 100000099)
      hTermVar :: AstTensor AstMethodLet FullSpan (TKS '[nImgs, nCinp, nAh, nAw] Double)
      hTermVar = conv2dSame_dInp @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                 (sconcrete (unConcrete arrK))
                                 (AstVar varNameB)
      hTermVarSimplified = simplifyInlineContract hTermVar
      artifactRaw = vjpArtifact g arrA
      artifact = simplifyArtifactRev artifactRaw
  -- Force to WHNF (a full build under StrictData) before benchmarking.
  _ <- evaluate hTerm
  _ <- evaluate hTermSimplified
  _ <- evaluate hTermVarSimplified
  _ <- evaluate artifact
  _ <- evaluate artifactRaw
  return
    [ bench "S-fullpipe-hoisted" $ whnf
        (\dt -> forceGrad $ vjp g arrA dt) arrB
    , bench "S-fullpipe-honest" $ whnf
        (\k -> forceGrad
               $ vjp (\a -> conv2dSameS (sconcrete (unConcrete k)) a) arrA arrB)
        arrK
      -- Artifact build+simplify only, WHNF-forced; see 'benchesAt'.
    , bench "S-artifact" $ whnf
        (\a -> simplifyArtifactRev (vjpArtifact g a)) arrA
    , bench "S-exec" $ whnf
        (\dt -> forceGrad
                  (vjpInterpretArtifact artifact arrA dt
                   :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] Double))) arrB
    , bench "S-exec-raw" $ whnf
        (\dt -> forceGrad
                  (vjpInterpretArtifact artifactRaw arrA dt
                   :: Concrete (TKS '[nImgs, nCinp, nAh, nAw] Double))) arrB
    , bench "H-fullpipe" $ whnf
        (\b -> forceGrad $ interpretAstFull emptyEnv
                 $ conv2dSame_dInp @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                   (sconcrete (unConcrete arrK))
                                   (sconcrete (unConcrete b))) arrB
    , bench "H-exec" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) hTerm
    , bench "H-exec-contracted" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) hTermSimplified
    , bench "H-exec-var" $ whnf
        (\b -> forceGrad
               $ interpretAstFull (extendEnv varNameB b emptyEnv)
                                  hTermVarSimplified) arrB
    ]

-- | Micro-benchmarks for the dominant cost found by profiling: the
-- interpreted im2col gather chains. Compares the AD-produced orientation
-- (large dim first in the gather output, small dims innermost in the
-- copied slices) against the vectorization-produced orientation
-- (small dim first, large dim innermost in slices), and both against
-- a single fused gather that avoids the intermediate array entirely.
gatherBenches :: IO [Benchmark]
gatherBenches = do
  let (arr1, seed2) =
        randomValue @(Concrete (TKS '[50, 3, 3, 50] Double))
                    0.5 (mkStdGen 42)
      (arr2, _) =
        randomValue @(Concrete (TKS '[50, 50, 3, 3] Double))
                    0.5 seed2
      s1, s1' :: AstTensor AstMethodLet FullSpan (TKS '[50, 3, 3, 50] Double)
      s1 = sconcrete (unConcrete arr1)
      s1' = sconcrete (unConcrete arr1)
      s2 :: AstTensor AstMethodLet FullSpan (TKS '[50, 50, 3, 3] Double)
      s2 = sconcrete (unConcrete arr2)
      -- S orientation: sgather @[48,3], big dim first.
      twoS :: AstTensor AstMethodLet FullSpan (TKS '[48, 3, 3, 48, 3, 3] Double)
      twoS =
        sgather @'[48, 3] @'[3, 48, 3, 3] @'[50]
                (stranspose @'[4, 2, 0, 3, 1]
                   (sgather @'[48, 3] @'[3, 3, 50] @'[50]
                            s1
                            (\case [a, b] -> [a + b]
                                   _ -> error "twoS")))
                (\case [c, d] -> [c + d]
                       _ -> error "twoS")
      -- H orientation: sgather @[3,48], small dim first.
      twoH :: AstTensor AstMethodLet FullSpan (TKS '[3, 48, 3, 3, 3, 48] Double)
      twoH =
        sgather @'[3, 48] @'[3, 3, 3, 48] @'[50]
                (stranspose @'[4, 2, 0, 3, 1]
                   (sgather @'[3, 48] @'[3, 3, 50] @'[50]
                            s1'
                            (\case [b, a] -> [a + b]
                                   _ -> error "twoH")))
                (\case [d, c] -> [c + d]
                       _ -> error "twoH")
      -- One fused gather, S orientation of the output dims.
      fusedS :: AstTensor AstMethodLet FullSpan (TKS '[48, 3, 48, 3, 3, 3] Double)
      fusedS =
        sgather @'[48, 3, 48, 3] @'[3, 3] @'[50, 50]
                s2
                (\case [h, kh, w, kw] -> [h + kh, w + kw]
                       _ -> error "fusedS")
      -- One fused gather, H orientation of the output dims.
      fusedH :: AstTensor AstMethodLet FullSpan (TKS '[3, 48, 3, 48, 3, 3] Double)
      fusedH =
        sgather @'[3, 48, 3, 48] @'[3, 3] @'[50, 50]
                s2
                (\case [kh, h, kw, w] -> [h + kh, w + kw]
                       _ -> error "fusedH")
      -- The S chain as the contemplated canonicalization rule would
      -- rewrite it: each gather's shm dims sorted ascending, with a
      -- compensating transpose above that restores the original dim order.
      canonS :: AstTensor AstMethodLet FullSpan (TKS '[48, 3, 3, 48, 3, 3] Double)
      canonS =
        stranspose @'[1, 0]
          (sgather @'[3, 48] @'[3, 48, 3, 3] @'[50]
                   (stranspose @'[4, 2, 0, 3, 1]
                      (stranspose @'[1, 0]
                         (sgather @'[3, 48] @'[3, 3, 50] @'[50]
                                  s1
                                  (\case [b, a] -> [a + b]
                                         _ -> error "canonS"))))
                   (\case [d, c] -> [c + d]
                          _ -> error "canonS"))
      -- The S chain with the second gather's shn dims sorted ascending
      -- instead (large dims innermost in the copied slices), by a
      -- transpose below the gather (merges into the existing view)
      -- and a compensating transpose above.
      canonS2 :: AstTensor AstMethodLet FullSpan (TKS '[48, 3, 3, 48, 3, 3] Double)
      canonS2 =
        stranspose @'[0, 1, 2, 5, 3, 4]
          (sgather @'[48, 3] @'[3, 3, 3, 48] @'[50]
                   (stranspose @'[0, 1, 3, 4, 2]
                      (stranspose @'[4, 2, 0, 3, 1]
                         (sgather @'[48, 3] @'[3, 3, 50] @'[50]
                                  s1
                                  (\case [a, b] -> [a + b]
                                         _ -> error "canonS2"))))
                   (\case [c, d] -> [c + d]
                          _ -> error "canonS2"))
  -- Force to WHNF (a full build under StrictData) before benchmarking.
  _ <- evaluate twoS
  _ <- evaluate twoH
  _ <- evaluate fusedS
  _ <- evaluate fusedH
  _ <- evaluate canonS
  _ <- evaluate canonS2
  return
    [ bench "two-gathers-S-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoS
    , bench "two-gathers-H-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoH
    , bench "two-gathers-S-canonicalized" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) canonS
    , bench "two-gathers-S-shn-sorted" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) canonS2
    , bench "fused-gather-S-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedS
    , bench "fused-gather-H-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedH
    ]

-- | The scatter analogue of 'gatherBenches': the interpreted scatter chains
-- that appear in the input-image gradient (the @sscatter@ path). Each chain
-- is the exact adjoint (transpose) of the corresponding gather chain above —
-- verified at startup by 'checkAdjoint' — so this isolates the scatter cost
-- the way 'gatherBenches' isolates the gather cost.
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
      -- The gather chains from 'gatherBenches' (over x1/x2), for verification.
      gTwoS :: AstTensor AstMethodLet FullSpan (TKS '[48, 3, 3, 48, 3, 3] Double)
      gTwoS =
        sgather @'[48, 3] @'[3, 48, 3, 3] @'[50]
                (stranspose @'[4, 2, 0, 3, 1]
                   (sgather @'[48, 3] @'[3, 3, 50] @'[50] x1
                            (\case [a, b] -> [a + b]
                                   _ -> error "gTwoS")))
                (\case [c, d] -> [c + d]
                       _ -> error "gTwoS")
      gTwoH :: AstTensor AstMethodLet FullSpan (TKS '[3, 48, 3, 3, 3, 48] Double)
      gTwoH =
        sgather @'[3, 48] @'[3, 3, 3, 48] @'[50]
                (stranspose @'[4, 2, 0, 3, 1]
                   (sgather @'[3, 48] @'[3, 3, 50] @'[50] x1
                            (\case [b, a] -> [a + b]
                                   _ -> error "gTwoH")))
                (\case [d, c] -> [c + d]
                       _ -> error "gTwoH")
      gFusedS :: AstTensor AstMethodLet FullSpan (TKS '[48, 3, 48, 3, 3, 3] Double)
      gFusedS =
        sgather @'[48, 3, 48, 3] @'[3, 3] @'[50, 50] x2
                (\case [h, kh, w, kw] -> [h + kh, w + kw]
                       _ -> error "gFusedS")
      gFusedH :: AstTensor AstMethodLet FullSpan (TKS '[3, 48, 3, 48, 3, 3] Double)
      gFusedH =
        sgather @'[3, 48, 3, 48] @'[3, 3] @'[50, 50] x2
                (\case [kh, h, kw, w] -> [h + kh, w + kw]
                       _ -> error "gFusedH")
      -- The scatter chains: exact adjoints of the gather chains above.
      -- The two-op chains reverse the composition order and invert the
      -- connecting transpose (@[4,2,0,3,1]@ becomes @[2,4,1,3,0]@).
      twoScatterS :: AstTensor AstMethodLet FullSpan (TKS '[50, 3, 3, 50] Double)
      twoScatterS =
        sscatter @'[48, 3] @'[3, 3, 50] @'[50]
                 (stranspose @'[2, 4, 1, 3, 0]
                    (sscatter @'[48, 3] @'[3, 48, 3, 3] @'[50] y1
                              (\case [c, d] -> [c + d]
                                     _ -> error "twoScatterS")))
                 (\case [a, b] -> [a + b]
                        _ -> error "twoScatterS")
      twoScatterH :: AstTensor AstMethodLet FullSpan (TKS '[50, 3, 3, 50] Double)
      twoScatterH =
        sscatter @'[3, 48] @'[3, 3, 50] @'[50]
                 (stranspose @'[2, 4, 1, 3, 0]
                    (sscatter @'[3, 48] @'[3, 3, 3, 48] @'[50] y2
                              (\case [d, c] -> [c + d]
                                     _ -> error "twoScatterH")))
                 (\case [b, a] -> [a + b]
                        _ -> error "twoScatterH")
      fusedScatterS :: AstTensor AstMethodLet FullSpan (TKS '[50, 50, 3, 3] Double)
      fusedScatterS =
        sscatter @'[48, 3, 48, 3] @'[3, 3] @'[50, 50] y3
                 (\case [h, kh, w, kw] -> [h + kh, w + kw]
                        _ -> error "fusedScatterS")
      fusedScatterH :: AstTensor AstMethodLet FullSpan (TKS '[50, 50, 3, 3] Double)
      fusedScatterH =
        sscatter @'[3, 48, 3, 48] @'[3, 3] @'[50, 50] y4
                 (\case [kh, h, kw, w] -> [h + kh, w + kw]
                        _ -> error "fusedScatterH")
  checkAdjoint "two-scatters-S-orient" gTwoS arrX1 twoScatterS arrY1
  checkAdjoint "two-scatters-H-orient" gTwoH arrX1 twoScatterH arrY2
  checkAdjoint "fused-scatter-S-orient" gFusedS arrX2 fusedScatterS arrY3
  checkAdjoint "fused-scatter-H-orient" gFusedH arrX2 fusedScatterH arrY4
  -- Force to WHNF (a full build under StrictData) before benchmarking.
  _ <- evaluate twoScatterS
  _ <- evaluate twoScatterH
  _ <- evaluate fusedScatterS
  _ <- evaluate fusedScatterH
  return
    [ bench "two-scatters-S-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoScatterS
    , bench "two-scatters-H-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) twoScatterH
    , bench "fused-scatter-S-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedScatterS
    , bench "fused-scatter-H-orient" $ whnf
        (\t -> forceGrad $ interpretAstFull emptyEnv t) fusedScatterH
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
      f :: AstTensor AstMethodLet FullSpan (TKS '[nCout, nCinp, nKh, nKw] Double)
        -> AstTensor AstMethodLet FullSpan (TKS '[nImgs, nCout, nAh, nAw] Double)
      f k = conv2dSameS k (sconcrete (unConcrete arrA))
      hTerm :: AstTensor AstMethodLet FullSpan (TKS '[nCout, nCinp, nKh, nKw] Double)
      hTerm = conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                              (sconcrete (unConcrete arrA))
                              (sconcrete (unConcrete arrB))
      hTermSimplified = simplifyInlineContract hTerm
      varNameB = mkAstVarName (FTKS (knownShS @'[nImgs, nCout, nAh, nAw])
                                    (FTKScalar @Double))
                              (intToAstVarId 100000099)
      hTermVar :: AstTensor AstMethodLet FullSpan (TKS '[nCout, nCinp, nKh, nKw] Double)
      hTermVar = conv2dSame_dKrn @nImgs @nCinp @nCout @nAh @nAw @nKh @nKw
                                 (sconcrete (unConcrete arrA))
                                 (AstVar varNameB)
      artifact = simplifyArtifactRev (vjpArtifact f arrK)
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
      bg <- gatherBenches
      bs <- scatterBenches
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
        , bgroup "gather48" bg
        , bgroup "scatter48" bs
        ]
