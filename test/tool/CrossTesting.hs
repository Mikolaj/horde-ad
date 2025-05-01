-- | Testing harness that differentiates a single objective function using
-- over a twenty different pipeline variants and cross-checks the results.
module CrossTesting
  ( rev', assertEqualUpToEpsilon'
  , t16, t16b, t48, t128, t128b, t128c
  , rrev1, rfwd1, srev1, sfwd1
  ) where

import Prelude

import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)
import System.IO.Unsafe (unsafePerformIO)
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested.Internal.Shape

import HordeAd.ADEngine
  ( IncomingCotangentHandling (..)
  , cjvp
  , jvp
  , revInterpretArtifact
  , revProduceArtifactWithoutInterpretation
  )
import HordeAd.AstEngine
import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersAst
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor (kfromR, kfromS)
import HordeAd.Core.Ops
import HordeAd.Core.OpsADVal
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind
import HordeAd.OpsTensor

import EqEpsilon

crevMaybeBoth
  :: forall r y f advals.
     ( f ~ Concrete, X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget (ADVal Concrete) (ADVal f (TKR y r))
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal f (TKR y r)) -> DValue advals
  -> (f (ADTensorKind (X advals)), f (TKR y r))
{-# INLINE crevMaybeBoth #-}
crevMaybeBoth f vals =
  let g :: ADVal Concrete (X advals) -> ADVal Concrete (TKR y r)
      g = toTarget . f . fromTarget
      valsH = toTarget vals
  in crevOnParams Nothing g (tftk knownSTK valsH) valsH

rev' :: forall r m n v a w.
        ( KnownNat m, KnownNat n, GoodScalar r
        , v ~ Concrete (TKR m r)
        , w ~ Concrete (ADTensorKind (TKR m r))
        , a ~ Concrete (ADTensorKind (TKR n r)) )
     => (forall f. ADReady f => f (TKR n r) -> f (TKR m r))
     -> Concrete (TKR n r)
     -> ( ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
          , AstTensor AstMethodLet PrimalSpan (TKR m r), AstTensor AstMethodLet PrimalSpan (TKR m r)
          , v, v, v, v, v, v, v, v, v, v, v, v, v, v
          , a, a, a, a, a, a, a, a, a, a, a, a, a, a
          , Concrete (TKR n r), w, w, w )
        , ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
          , AstTensor AstMethodLet PrimalSpan (TKR m r), AstTensor AstMethodLet PrimalSpan (TKR m r)
          , v, v, v, v, v, v, v, v, v, v, v, v, v, v
          , a, a, a, a, a, a, a, a, a, a, a, a, a, a
          , Concrete (TKR n r), w, w, w ) )
{-# NOINLINE rev' #-}
rev' f vals = unsafePerformIO $ do
  setTotalSharing False
  !resNormalSharing <- rev1 f vals
  setTotalSharing True
  !resTotalSharing <- rev1 f vals
  setTotalSharing False
  return (resNormalSharing, resTotalSharing)

rev1 :: forall r m n v a w.
        ( KnownNat m, KnownNat n, GoodScalar r
        , v ~ Concrete (TKR m r)
        , w ~ Concrete (ADTensorKind (TKR m r))
        , a ~ Concrete (ADTensorKind (TKR n r)) )
     => (forall f. ADReady f => f (TKR n r) -> f (TKR m r))
     -> Concrete (TKR n r)
     -> IO ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
           , AstTensor AstMethodLet PrimalSpan (TKR m r), AstTensor AstMethodLet PrimalSpan (TKR m r)
           , v, v, v, v, v, v, v, v, v, v, v, v, v, v
           , a, a, a, a, a, a, a, a, a, a, a, a, a, a
           , Concrete (TKR n r), w, w, w )
{-# NOINLINE rev1 #-}
rev1 f !vals = do
  let !value0 = f vals
      ftk = tftk knownSTK vals
      g :: ADVal Concrete (TKR n r)
        -> ADVal Concrete (TKR m r)
      g inputs = f $ fromTarget inputs
      !(!gradient1, !value1) = crevMaybeBoth g vals
      gradientRrev1 = rrev1 @Concrete @r @n @m f vals
      g9 :: ADVal (AstRaw PrimalSpan) (TKR n r)
         -> ADVal (AstRaw PrimalSpan) (TKR m r)
      g9 inputs = f @(ADVal (AstRaw PrimalSpan))
                  $ fromTarget inputs
        -- fromTarget is fine, because primal of inputs is a variable,
        -- hence it's duplicable
      artifactsGradAst9 =
        fst $ revProduceArtifactWithoutInterpretation
                IgnoreIncomingCotangent g9 ftk
      !(!gradient9, !value9) = revInterpretArtifact7 artifactsGradAst9
      revInterpretArtifact7
        :: AstArtifactRev (TKR n r) (TKR m r)
        -> (Concrete (ADTensorKind (TKR n r)), Concrete (TKR m r))
      revInterpretArtifact7 a1 = revInterpretArtifact a1 vals Nothing
      hGeneral
        :: (ADReady fgen, ADReady f1)
        => (f1 (TKR m r) -> AstTensor AstMethodLet FullSpan (TKR m r))
        -> (AstTensor AstMethodLet FullSpan (TKR n r) -> f1 (TKR n r))
        -> (AstTensor AstMethodLet FullSpan (TKR m r) -> AstTensor AstMethodLet FullSpan (TKR m r))
        -> fgen (TKR n r)
        -> fgen (TKR m r)
      hGeneral fx1 fx2 gx inputs =
        let (var, ast) =
              funToAst (FTKR (rshape vals) FTKScalar) Nothing (fx1 . f . fx2)
            env = extendEnv var inputs emptyEnv
        in interpretAstFull env (gx ast)
      h :: ADReady f1
        => (f1 (TKR m r) -> AstTensor AstMethodLet FullSpan (TKR m r))
        -> (AstTensor AstMethodLet FullSpan (TKR n r) -> f1 (TKR n r))
        -> (AstTensor AstMethodLet FullSpan (TKR m r) -> AstTensor AstMethodLet FullSpan (TKR m r))
        -> ADVal Concrete (TKR n r)
        -> ADVal Concrete (TKR m r)
      h fx1 fx2 gx inputs =
        hGeneral @(ADVal Concrete) fx1 fx2 gx
                 (fromTarget inputs)
      !(!gradient2, !value2) =
        crevMaybeBoth (h id id id) vals
      !(!gradient3, !value3) =
        crevMaybeBoth (h id id simplifyInlineContract) vals
      !(!gradient2UnSimp, !value2UnSimp) =
        crevMaybeBoth (h unAstNoSimplify AstNoSimplify id) vals
      gradientRrev2UnSimp =
        rrev1 @Concrete @r @n @m @r
              (hGeneral unAstNoSimplify AstNoSimplify id) vals
      !(!gradient3UnSimp, !value3UnSimp) =
        crevMaybeBoth (h (simplifyInline . unAstNoSimplify) AstNoSimplify simplifyInlineContract)
                      vals
      gradientRrev3UnSimp =
        rrev1 @Concrete @r @n @m @r
              (hGeneral unAstNoSimplify AstNoSimplify simplifyInlineContract) vals
      !(!gradient4, !value4) =
        crevMaybeBoth (h unAstNoVectorize AstNoVectorize id)
                      vals
          -- use the AstNoVectorize instance that does no vectorization
          -- and then interpret the results as the Ast instance
      gradientRrev4 =
        rrev1 @Concrete @r @n @m @r
              (hGeneral unAstNoVectorize AstNoVectorize id) vals
      !(!gradient5, !value5) =
        crevMaybeBoth (h unAstNoVectorize AstNoVectorize simplifyInlineContract)
                      vals
      gradientRrev5 =
        rrev1 @Concrete @r @n @m @r
              (hGeneral unAstNoVectorize AstNoVectorize simplifyInlineContract) vals
      astVectSimp = simplifyInlineContract $ snd $ funToAst (FTKR (rshape vals) FTKScalar) Nothing f
      astSimp =
        simplifyInlineContract $ simplifyInlineContract $ snd  -- builds simplify with difficulty
        $ funToAst (FTKR (rshape vals) FTKScalar) Nothing (unAstNoVectorize . f . AstNoVectorize)
      -- Here comes the part with Ast gradients.
      hAst :: ADReady f1
           => (f1 (TKR m r) -> AstTensor AstMethodLet FullSpan (TKR m r))
           -> (AstTensor AstMethodLet FullSpan (TKR n r) -> f1 (TKR n r))
           -> (AstTensor AstMethodLet FullSpan (TKR m r) -> AstTensor AstMethodLet FullSpan (TKR m r))
           -> ADVal (AstRaw PrimalSpan) (TKR n r)
           -> ADVal (AstRaw PrimalSpan) (TKR m r)
      hAst fx1 fx2 gx inputs
        = hGeneral @(ADVal (AstRaw PrimalSpan))
                   fx1 fx2 gx (fromTarget inputs)
        -- fromTarget is fine, because primal of inputs is a variable,
        -- hence it's duplicable
      artifactsGradAst =
        fst $ revProduceArtifactWithoutInterpretation
                IgnoreIncomingCotangent (hAst id id id) ftk
      !(!gradient2Ast, !value2Ast) =
        revInterpretArtifact7 artifactsGradAst
      !(!gradient2AstS, !value2AstS) =
        revInterpretArtifact7 (simplifyArtifact artifactsGradAst)
      artifactsGradAstT =
        fst $ revProduceArtifactWithoutInterpretation
                UseIncomingCotangent (hAst simplifyInline id id) ftk
      !(!gradient2AstST, !value2AstST) =
        revInterpretArtifact7 (simplifyArtifact artifactsGradAstT)
      artifactsSimpleAst =
        fst $ revProduceArtifactWithoutInterpretation
                IgnoreIncomingCotangent (hAst id id simplifyInlineContract) ftk
      !(!gradient3Ast, !value3Ast) =
        revInterpretArtifact7 artifactsSimpleAst
      !(!gradient3AstS, !value3AstS) =
        revInterpretArtifact7 (simplifyArtifact artifactsSimpleAst)
      artifactsGradAstUnSimp =
        fst $ revProduceArtifactWithoutInterpretation
                IgnoreIncomingCotangent (hAst unAstNoSimplify AstNoSimplify id) ftk
      !(!gradient2AstUnSimp, !value2AstUnSimp) =
        revInterpretArtifact7 artifactsGradAstUnSimp
      !(!gradient2AstSUnSimp, !value2AstSUnSimp) =
        revInterpretArtifact7 (simplifyArtifact artifactsGradAstUnSimp)
      artifactsSimpleAstUnSimp =
        fst $ revProduceArtifactWithoutInterpretation
                IgnoreIncomingCotangent (hAst unAstNoSimplify AstNoSimplify simplifyInlineContract)
                ftk
      !(!gradient3AstUnSimp, !value3AstUnSimp) =
        revInterpretArtifact7 artifactsSimpleAstUnSimp
      !(!gradient3AstSUnSimp, !value3AstSUnSimp) =
        revInterpretArtifact7 (simplifyArtifact artifactsSimpleAstUnSimp)
      artifactsPrimalAst =
        fst $ revProduceArtifactWithoutInterpretation
                IgnoreIncomingCotangent (hAst unAstNoVectorize AstNoVectorize id) ftk
      !(!gradient4Ast, !value4Ast) =
        revInterpretArtifact7 artifactsPrimalAst
      !(!gradient4AstS, !value4AstS) =
        revInterpretArtifact7 (simplifyArtifact artifactsPrimalAst)
      artifactsPSimpleAst =
        fst $ revProduceArtifactWithoutInterpretation
                IgnoreIncomingCotangent (hAst unAstNoVectorize AstNoVectorize simplifyInlineContract)
                ftk
      !(!gradient5Ast, !value5Ast) =
        revInterpretArtifact7 artifactsPSimpleAst
      -- Due to no vectorization this may result in huge terms,
      -- which then take forever to inline into (substitution into huge term)
      -- and to simplify, so we ignore this test for now.
      (gradient5AstS, value5AstS) =
        revInterpretArtifact7 (simplifyArtifact artifactsPSimpleAst)
      !cderivative = cjvp f vals vals
      !derivative = jvp f vals vals
      !derivativeRfwd1 = rfwd1ds @Concrete @r @n @m @r f vals
                         $ toADTensorKindShared ftk vals
  return
    ( value0, value1, value2, value3, value2UnSimp, value3UnSimp
    , value4, value5
    , gradient1, gradientRrev1, gradient2, gradient3
    , gradient2UnSimp, gradientRrev2UnSimp
    , gradient3UnSimp, gradientRrev3UnSimp
    , gradient4, gradientRrev4, gradient5, gradientRrev5
    , astVectSimp, astSimp
    , value9, value2Ast, value2AstS, value2AstST, value3Ast, value3AstS
    , value2AstUnSimp, value2AstSUnSimp, value3AstUnSimp, value3AstSUnSimp
    , value4Ast, value4AstS, value5Ast, value5AstS
    , gradient9, gradient2Ast, gradient2AstS, gradient2AstST
    , gradient3Ast, gradient3AstS
    , gradient2AstUnSimp, gradient2AstSUnSimp
    , gradient3AstUnSimp, gradient3AstSUnSimp
    , gradient4Ast, gradient4AstS, gradient5Ast, gradient5AstS
    , vals, cderivative, derivative, derivativeRfwd1 )

assertEqualUpToEpsilon'
    :: ( KnownNat n, KnownNat m
       , v ~ Concrete (TKR m r)
       , w ~ Concrete (ADTensorKind (TKR m r))
       , a ~ Concrete (ADTensorKind (TKR n r))
       , AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon v
       , AssertEqualUpToEpsilon (ADTensorScalar r)
       , GoodScalar r, GoodScalar (ADTensorScalar r), HasCallStack)
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> Concrete (TKR n r)  -- ^ expected reverse derivative value
    -> ( ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
         , AstTensor AstMethodLet PrimalSpan (TKR m r), AstTensor AstMethodLet PrimalSpan (TKR m r)
         , v, v, v, v, v, v, v, v, v, v, v, v, v, v
         , a, a, a, a, a, a, a, a, a, a, a, a, a, a
         , Concrete (TKR n r), w, w, w )
       ,  ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
         , AstTensor AstMethodLet PrimalSpan (TKR m r), AstTensor AstMethodLet PrimalSpan (TKR m r)
         , v, v, v, v, v, v, v, v, v, v, v, v, v, v
         , a, a, a, a, a, a, a, a, a, a, a, a, a, a
         , Concrete (TKR n r), w, w, w ) )
    -> Assertion
assertEqualUpToEpsilon' errMargin expected' (tup1, tup2) = do
  assertEqualUpToEpsilon1 errMargin expected' tup1
  assertEqualUpToEpsilon1 errMargin expected' tup2

assertEqualUpToEpsilon1
    :: ( KnownNat n, KnownNat m
       , v ~ Concrete (TKR m r)
       , w ~ Concrete (ADTensorKind (TKR m r))
       , a ~ Concrete (ADTensorKind (TKR n r))
       , AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon v
       , AssertEqualUpToEpsilon (ADTensorScalar r)
       , GoodScalar r, GoodScalar (ADTensorScalar r), HasCallStack)
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> Concrete (TKR n r)  -- ^ expected reverse derivative value
    -> ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
       , AstTensor AstMethodLet PrimalSpan (TKR m r), AstTensor AstMethodLet PrimalSpan (TKR m r)
       , v, v, v, v, v, v, v, v, v, v, v, v, v, v
       , a, a, a, a, a, a, a, a, a, a, a, a, a, a
       , Concrete (TKR n r), w, w, w )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon1
    errMargin expected'
    ( value0, value1, value2, value3, value2UnSimp, value3UnSimp
    , value4, value5
    , gradient1, gradientRrev1, gradient2, gradient3
    , gradient2UnSimp, gradientRrev2UnSimp
    , gradient3UnSimp, gradientRrev3UnSimp
    , gradient4, gradientRrev4, gradient5, gradientRrev5
    , _astVectSimp, _astSimp
    , value9, value2Ast, value2AstS, value2AstST, value3Ast, value3AstS
    , value2AstUnSimp, value2AstSUnSimp, value3AstUnSimp, value3AstSUnSimp
    , value4Ast, value4AstS, value5Ast, _value5AstS
    , gradient9, gradient2Ast, gradient2AstS, gradient2AstST
    , gradient3Ast, gradient3AstS
    , gradient2AstUnSimp, gradient2AstSUnSimp
    , gradient3AstUnSimp, gradient3AstSUnSimp
    , gradient4Ast, gradient4AstS, gradient5Ast, _gradient5AstS
    , vals, cderivative, derivative, derivativeRfwd1 ) = do
  let ftk = tftk knownSTK vals
      expected = toADTensorKindShared ftk expected'
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val V UnS" errMargin value0 value2UnSimp
  assertEqualUpToEpsilonWithMark "Val V+S UnS" errMargin value0 value3UnSimp
  assertEqualUpToEpsilonWithMark "Val NotVect" errMargin value0 value4
  assertEqualUpToEpsilonWithMark "Val Simplified" errMargin value0 value5
  assertEqualUpToEpsilonWithMark "Grad ADVal" errMargin expected gradient1
  assertEqualUpToEpsilonWithMark "Grad ADVal rrev"
                                 errMargin expected gradientRrev1
  assertEqualUpToEpsilonWithMark "Grad Vectorized" errMargin expected gradient2
  assertEqualUpToEpsilonWithMark "Grad Vect+Simp" errMargin expected gradient3
  assertEqualUpToEpsilonWithMark "Grad V UnS" errMargin expected gradient2UnSimp
  assertEqualUpToEpsilonWithMark "Grad V UnS rrev2"
                                 errMargin expected gradientRrev2UnSimp
  assertEqualUpToEpsilonWithMark "Grad V+S UnS"
                                 errMargin expected gradient3UnSimp
  assertEqualUpToEpsilonWithMark "Grad V+S UnS rrev"
                                 errMargin expected gradientRrev3UnSimp
  assertEqualUpToEpsilonWithMark "Grad NotVect" errMargin expected gradient4
  assertEqualUpToEpsilonWithMark "Grad NotVect rrev"
                                 errMargin expected gradientRrev4
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  assertEqualUpToEpsilonWithMark "Grad Simplified rrev2"
                                 errMargin expected gradientRrev5
  assertEqualUpToEpsilonWithMark "Val Ast Vectorized" errMargin value0 value2Ast
  assertEqualUpToEpsilonWithMark "Val Ast V S" errMargin value0 value2AstS
  assertEqualUpToEpsilonWithMark "Val Ast V ST" errMargin value0 value2AstST
  assertEqualUpToEpsilonWithMark "Val Ast Vect+Simp" errMargin value0 value3Ast
  assertEqualUpToEpsilonWithMark "Val Ast V+S S" errMargin value0 value3AstS
  assertEqualUpToEpsilonWithMark "Val Ast V UnS" errMargin value0
                                                 value2AstUnSimp
  assertEqualUpToEpsilonWithMark "Val Ast V S UnS" errMargin value0
                                                   value2AstSUnSimp
  assertEqualUpToEpsilonWithMark "Val Ast Vect+Simp UnS" errMargin value0
                                                         value3AstUnSimp
  assertEqualUpToEpsilonWithMark "Val Ast V+S S UnS" errMargin value0
                                                     value3AstSUnSimp
  assertEqualUpToEpsilonWithMark "Val Ast NotVect" errMargin value0 value4Ast
  assertEqualUpToEpsilonWithMark "Val Ast NotVect S" errMargin value0 value4AstS
  assertEqualUpToEpsilonWithMark "Val Ast Simplified" errMargin value0 value5Ast
--  assertEqualUpToEpsilonWithMark "Val Ast S S" errMargin value0 value5AstS
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized"
                                 errMargin expected gradient2Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized S"
                                 errMargin expected gradient2AstS
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized ST"
                                 errMargin expected gradient2AstST
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp"
                                 errMargin expected gradient3Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp S"
                                 errMargin expected gradient3AstS
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized UnS"
                                 errMargin expected gradient2AstUnSimp
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized S UnS"
                                 errMargin expected gradient2AstSUnSimp
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp UnS"
                                 errMargin expected gradient3AstUnSimp
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp S UnS"
                                 errMargin expected gradient3AstSUnSimp
  assertEqualUpToEpsilonWithMark "Grad Ast NotVect"
                                 errMargin expected gradient4Ast
  assertEqualUpToEpsilonWithMark "Grad Ast NotVect S"
                                 errMargin expected gradient4AstS
  assertEqualUpToEpsilonWithMark "Grad Ast Simplified"
                                 errMargin expected gradient5Ast
--  assertEqualUpToEpsilonWithMark "Grad Ast Simplified S"
--                                 errMargin expected gradient5AstS
  assertEqualUpToEpsilonWithMark "Val ADVal Ast" errMargin value0 value9
  assertEqualUpToEpsilonWithMark "Grad ADVal Ast" errMargin expected gradient9
  assertEqualUpToEpsilonWithMark "Derivatives" errMargin cderivative derivative
  assertEqualUpToEpsilonWithMark "Derivatives rjvp"
                                 errMargin cderivative derivativeRfwd1
  -- The formula for comparing derivative and gradient is due to @awf
  -- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
  -- and a similar property stated mathematically is in Lemma 1 in
  -- https://www.microsoft.com/en-us/research/uploads/prod/2021/08/higher-order-ad.pdf
  assertEqualUpToEpsilonWithMark "Reverse vs forward"
                                 1e-5 (rsum0 derivative) (rdot0 expected (toADTensorKindShared ftk vals))
  {- TODO: this most probably leaks gigabytes of strings from one test case
  -- to another in -O0 mode, leading to OOMs, so it's disabled for now.
  -- We could also try to stream the strings and compare on the fly.
  --
  -- No Eq instance, so let's compare the text.
  assertEqual "Idempotence of simplification of non-vectorized AST"
              (show astSimp)
              (show (simplifyInlineContract astSimp))
  assertEqual "Idempotence of simplification of vectorized AST"
              (show astVectSimp)
              (show (simplifyInlineContract astVectSimp))
  -}

t16 :: (GoodScalar r, Fractional r) => Concrete (TKR 5 r)
t16 = ringestData (fromList [2, 2, 1, 2, 2]) [5, 2, 6, 1, -2, 0.000001, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26]

t16b :: (GoodScalar r, Fractional r) => Concrete (TKR 4 r)
t16b = ringestData (fromList [2, 2, 2, 2]) [5, 2, 6, 1, -2, 0, 0.1, -0.2, 13.1, 9, 8, -4, 582934, 2.99432, -335, 26]

t48 :: (GoodScalar r, Fractional r) => Concrete (TKR 7 r)
t48 = ringestData (fromList [3, 1, 2, 2, 1, 2, 2]) [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

t128 :: (GoodScalar r, Fractional r) => Concrete (TKR 10 r)
t128 = ringestData (fromList [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]) [29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6, 1, -2, 97.1,58.8943200001,97.1,55.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,32.1,40.1,53.0,53.99432, -0.00001, 0.1, -0.2, 13.1, 9, 8, -4, 29, 2.99432, -335, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,40.1,8.0,11.0,-3.0,25.89432,28.79432,-39.09999999999997,25.8,40.1,8.0,11.0,-3.0,25.89432,28.79432,-19.09999999999997,25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432,97.1,55.8943200001,97.1,85.8943200001,97.1,85.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001,97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,89.0,53.99432,97.1,56.8943200001,97.1,52.8943200001,97.1,55.8943200001]

t128b :: (GoodScalar r, Fractional r) => Concrete (TKR 4 r)
t128b = rreshape (4 :$: 2 :$: 4 :$: 4 :$: ZSR) t128

t128c :: (GoodScalar r, Fractional r) => Concrete (TKR 4 r)
t128c = rreshape (2 :$: 2 :$: 8 :$: 4 :$: ZSR) t128

rrev1 :: forall g r n m r3.
         (ADReady g, GoodScalar r, KnownNat n, GoodScalar r3, KnownNat m)
      => (forall f. ADReady f => f (TKR n r) -> f (TKR m r3)) -> g (TKR n r)
      -> g (ADTensorKind (TKR n r))
rrev1 f u = kgrad (kfromR . rsum0 . f) (tftk knownSTK u) u

rfwd1ds :: forall g r n m r3.
           (ADReady g, GoodScalar r, KnownNat n)
        => (forall f. ADReady f => f (TKR n r) -> f (TKR m r3)) -> g (TKR n r)
        -> g (ADTensorKind (TKR n r))
        -> g (ADTensorKind (TKR m r3))
rfwd1ds f u = rjvp f (tftk knownSTK u) u

rfwd1 :: forall g r n m r3.
         (ADReady g, GoodScalar r, GoodScalar (ADTensorScalar r), KnownNat n)
      => (forall f. ADReady f => f (TKR n r) -> f (TKR m r3)) -> g (TKR n r)
      -> g (ADTensorKind (TKR m r3))
rfwd1 f u = rfwd1ds f u (rrepl (rshape u) 1)

srev1 :: forall g r sh sh2 r3.
         (ADReady g, GoodScalar r, KnownShS sh, GoodScalar r3, KnownShS sh2)
      => (forall f. ADReady f => f (TKS sh r) -> f (TKS sh2 r3)) -> g (TKS sh r)
      -> g (ADTensorKind (TKS sh r))
srev1 f u = kgrad (kfromS. ssum0 . f) (tftk knownSTK u) u

sfwd1 :: forall g r sh sh2 r3.
         (ADReady g, GoodScalar r, GoodScalar (ADTensorScalar r), KnownShS sh)
      => (forall f. ADReady f => f (TKS sh r) -> f (TKS sh2 r3)) -> g (TKS sh r)
      -> g (ADTensorKind (TKS sh2 r3))
sfwd1 f u = sjvp f (tftk knownSTK u) u (srepl @_ @(ADTensorScalar r) 1)
