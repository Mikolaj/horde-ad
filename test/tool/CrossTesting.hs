-- | Testing harness that differentiates a single objective function using
-- over a twenty different pipeline variants and compares the results.
module CrossTesting
  ( assertEqualUpToEpsilon1
  , rev', assertEqualUpToEpsilon', assertEqualUpToEpsilonShort
  , t16, t16OR, t16b, t48, t48OR, t128, t128OR, t128b, t128c
  , rrev1, rrev2, rfwd1, srev1, sfwd1
  , treplicateR, tfromListR, tfromList0NR, tsumR
  ) where

import Prelude

import Data.Array.Ranked qualified as ORB
import Data.Array.RankedS qualified as OR
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Storable qualified as VS
import GHC.TypeLits (KnownNat, sameNat, type (+))
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInline
import HordeAd.Core.AstInterpret
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
  (cfwd, fwd, revEvalArtifact, revProduceArtifactWithoutInterpretation)
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray, tdot0R, tsum0R)
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))
import HordeAd.Util.SizedList

import EqEpsilon

assertEqualUpToEpsilon1
  :: (GoodScalar r, AssertEqualUpToEpsilon (OR.Array n r), HasCallStack)
  => Rational
  -> OR.Array n r
  -> ORArray r n
  -> Assertion
assertEqualUpToEpsilon1 eps expected result =
  assertEqualUpToEpsilon eps expected (Nested.rtoOrthotope $ runFlipR result)

crevDtMaybeBoth
  :: forall r y f advals.
     ( f ~ ORArray, X advals ~ X (DValue advals), TensorKind (X advals)
     , GoodScalar r, KnownNat y
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector (ADVal ORArray) (ADVal f r y)
     , AdaptableHVector ORArray (DValue advals)
     , DualNumberValue advals )
  => Maybe (Rep f (ADTensorKind (TKR r y)))
  -> (advals -> ADVal f r y) -> DValue advals
  -> (Rep f (ADTensorKind (X advals)), RankedOf f r y)
{-# INLINE crevDtMaybeBoth #-}
crevDtMaybeBoth mdt f vals =
  let g :: Rep (ADVal ORArray) (X advals) -> Rep (ADVal ORArray) (TKR r y)
      g = toHVector (Proxy @(ADVal ORArray)) . f . parseHVector (Proxy @(ADVal ORArray)) (fromDValue vals) . repDeepDuplicable @(ADVal ORArray) (stensorKind @(X advals))
      valsH = toHVectorOf (Proxy @ORArray) vals
  in crevOnHVector (Proxy @ORArray) (stensorKind @(X advals))
                                    (stensorKind @(TKR r y))
                   mdt g valsH

rev' :: forall r m n v a w.
        ( KnownNat n, KnownNat m, GoodScalar r
        , v ~ Rep ORArray (TKR r m)
        , w ~ Rep ORArray (ADTensorKind (TKR r m))
        , a ~ Rep ORArray (ADTensorKind (TKR r n)) )
     => (forall f. ADReady f => f r n -> f r m)
     -> FlipR OR.Array r n
     -> ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
        , AstRanked PrimalSpan r m, AstRanked PrimalSpan r m
        , v, v, v, v, v, v, v, v, v, v, v, v, v, v
        , a, a, a, a, a, a, a, a, a, a, a, a, a, a
        , Rep ORArray (TKR r n), w, w, w )
rev' f valsOR =
  let vals :: FlipR Nested.Ranked r n
      vals = fromORArray valsOR
      value0 = f vals
      ftk = tshapeFull stensorKind vals
      dt = Nothing
      valsFrom = fromDValue vals
      g :: ADVal ORArray r n
        -> ADVal ORArray r m
      g inputs = f $ parseHVector Proxy valsFrom inputs
      (gradient1, value1) = crevDtMaybeBoth dt g vals
      gradientRrev1 = rrev1 @ORArray @r @n @r @m f vals
      g9 :: ADVal (AstRaw PrimalSpan) r n
         -> ADVal (AstRaw PrimalSpan) r m
      g9 inputs = f @(ADVal (AstRaw PrimalSpan))
                  $ parseHVector Proxy (fromDValue vals) inputs
      artifactsGradAst9 =
        fst $ revProduceArtifactWithoutInterpretation
                False g9 ftk
      (gradient9, value9) = revEvalArtifact7 artifactsGradAst9
      revEvalArtifact7
        :: AstArtifactRev (TKR r n) (TKR r m)
        -> (Rep ORArray (ADTensorKind (TKR r n)), ORArray r m)
      revEvalArtifact7 a1 = revEvalArtifact a1 vals Nothing
      hGeneral
        :: (ADReady fgen, ADReady f1)
        => (f1 r m -> AstRanked PrimalSpan r m)
        -> (AstRanked PrimalSpan r n -> f1 r n)
        -> (AstRanked PrimalSpan r m -> AstRanked PrimalSpan r m)
        -> fgen r n
        -> fgen r m
      hGeneral fx1 fx2 gx inputs =
        let (var, ast) = funToAst (FTKR $ rshape vals) (unAstRanked . fx1 . f . fx2 . AstRanked)
            env = extendEnv var inputs emptyEnv
        in interpretAst env (unAstRanked $ gx $ AstRanked ast)
      h :: ADReady f1
        => (f1 r m -> AstRanked PrimalSpan r m)
        -> (AstRanked PrimalSpan r n -> f1 r n)
        -> (AstRanked PrimalSpan r m -> AstRanked PrimalSpan r m)
        -> ADVal ORArray r n
        -> ADVal ORArray r m
      h fx1 fx2 gx inputs =
        hGeneral @(ADVal ORArray) fx1 fx2 gx
                 (parseHVector Proxy valsFrom inputs)
      (gradient2, value2) =
        crevDtMaybeBoth dt (h id id id) vals
      (gradient3, value3) =
        crevDtMaybeBoth dt (h id id simplifyInlineAst) vals
      (gradient2UnSimp, value2UnSimp) =
        crevDtMaybeBoth dt (h (AstRanked . unAstNoSimplify) (AstNoSimplify . unAstRanked) id) vals
      gradientRrev2UnSimp =
        rrev1 @ORArray @r @n @r @m
              (hGeneral (AstRanked . unAstNoSimplify) (AstNoSimplify . unAstRanked) id) vals
      (gradient3UnSimp, value3UnSimp) =
        crevDtMaybeBoth dt (h (AstRanked . unAstNoSimplify) (AstNoSimplify . unAstRanked) simplifyInlineAst)
                      vals
      gradientRrev3UnSimp =
        rrev1 @ORArray @r @n @r @m
              (hGeneral (AstRanked . unAstNoSimplify) (AstNoSimplify . unAstRanked) simplifyInlineAst) vals
      (gradient4, value4) =
        crevDtMaybeBoth dt (h (AstRanked . unAstNoVectorize) (AstNoVectorize . unAstRanked) id)
                      vals
          -- use the AstNoVectorize instance that does no vectorization
          -- and then interpret the results as the Ast instance
      gradientRrev4 =
        rrev1 @ORArray @r @n @r @m
              (hGeneral (AstRanked . unAstNoVectorize) (AstNoVectorize . unAstRanked) id) vals
      (gradient5, value5) =
        crevDtMaybeBoth dt (h (AstRanked . unAstNoVectorize) (AstNoVectorize . unAstRanked) simplifyInlineAst)
                      vals
      gradientRrev5 =
        rrev1 @ORArray @r @n @r @m
              (hGeneral (AstRanked . unAstNoVectorize) (AstNoVectorize . unAstRanked) simplifyInlineAst) vals
      astVectSimp = simplifyInlineAst $ AstRanked $ snd $ funToAst (FTKR $ rshape vals) (unAstRanked . f . AstRanked)
      astSimp =
        simplifyInlineAst $ simplifyInlineAst $ AstRanked $ snd  -- builds simplify with difficulty
        $ funToAst (FTKR $ rshape vals) (unAstNoVectorize . f . AstNoVectorize)
      -- Here comes the part with Ast gradients.
      hAst :: ADReady f1
           => (f1 r m -> AstRanked PrimalSpan r m)
           -> (AstRanked PrimalSpan r n -> f1 r n)
           -> (AstRanked PrimalSpan r m -> AstRanked PrimalSpan r m)
           -> ADVal (AstRaw PrimalSpan) r n
           -> ADVal (AstRaw PrimalSpan) r m
      hAst fx1 fx2 gx inputs
        = hGeneral @(ADVal (AstRaw PrimalSpan))
                   fx1 fx2 gx (parseHVector Proxy (fromDValue vals) inputs)
      artifactsGradAst =
        fst $ revProduceArtifactWithoutInterpretation
                False (hAst id id id) ftk
      (gradient2Ast, value2Ast) =
        revEvalArtifact7 artifactsGradAst
      (gradient2AstS, value2AstS) =
        revEvalArtifact7 (simplifyArtifact artifactsGradAst)
      artifactsGradAstT =
        fst $ revProduceArtifactWithoutInterpretation
                True (hAst id id id) ftk
      (gradient2AstST, value2AstST) =
        revEvalArtifact7 (simplifyArtifact artifactsGradAstT)
      artifactsSimpleAst =
        fst $ revProduceArtifactWithoutInterpretation
                False (hAst id id simplifyInlineAst) ftk
      (gradient3Ast, value3Ast) =
        revEvalArtifact7 artifactsSimpleAst
      (gradient3AstS, value3AstS) =
        revEvalArtifact7 (simplifyArtifact artifactsSimpleAst)
      artifactsGradAstUnSimp =
        fst $ revProduceArtifactWithoutInterpretation
                False (hAst (AstRanked . unAstNoSimplify) (AstNoSimplify . unAstRanked) id) ftk
      (gradient2AstUnSimp, value2AstUnSimp) =
        revEvalArtifact7 artifactsGradAstUnSimp
      (gradient2AstSUnSimp, value2AstSUnSimp) =
        revEvalArtifact7 (simplifyArtifact artifactsGradAstUnSimp)
      artifactsSimpleAstUnSimp =
        fst $ revProduceArtifactWithoutInterpretation
                False (hAst (AstRanked . unAstNoSimplify) (AstNoSimplify . unAstRanked) simplifyInlineAst)
                ftk
      (gradient3AstUnSimp, value3AstUnSimp) =
        revEvalArtifact7 artifactsSimpleAstUnSimp
      (gradient3AstSUnSimp, value3AstSUnSimp) =
        revEvalArtifact7 (simplifyArtifact artifactsSimpleAstUnSimp)
      artifactsPrimalAst =
        fst $ revProduceArtifactWithoutInterpretation
                False (hAst (AstRanked . unAstNoVectorize) (AstNoVectorize . unAstRanked) id) ftk
      (gradient4Ast, value4Ast) =
        revEvalArtifact7 artifactsPrimalAst
      (gradient4AstS, value4AstS) =
        revEvalArtifact7 (simplifyArtifact artifactsPrimalAst)
      artifactsPSimpleAst =
        fst $ revProduceArtifactWithoutInterpretation
                False (hAst (AstRanked . unAstNoVectorize) (AstNoVectorize . unAstRanked) simplifyInlineAst)
                ftk
      (gradient5Ast, value5Ast) =
        revEvalArtifact7 artifactsPSimpleAst
      (gradient5AstS, value5AstS) =
        revEvalArtifact7 (simplifyArtifact artifactsPSimpleAst)
      cderivative = cfwd @_ @(TKR r m) f vals vals
      derivative = fwd @_ @(TKR r m) f vals vals
      derivativeRfwd1 = rfwd1ds @ORArray @r @n @r @m f vals
                        $ toADTensorKindShared
                            (Proxy @ORArray) (stensorKind @(TKR r n)) vals
      fromORArray (FlipR t) = FlipR $ Nested.rfromOrthotope SNat t
  in ( value0, value1, value2, value3, value2UnSimp, value3UnSimp
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
    :: forall r m n v a w.
       ( KnownNat n
       , v ~ Rep ORArray (TKR r m)
       , w ~ Rep ORArray (ADTensorKind (TKR r m))
       , a ~ Rep ORArray (ADTensorKind (TKR r n))
       , AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon v
       , AssertEqualUpToEpsilon (ADTensorScalar r)
       , GoodScalar r, GoodScalar (ADTensorScalar r), HasCallStack)
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> OR.Array n r  -- ^ expected reverse derivative value
    -> ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
       , AstRanked PrimalSpan r m, AstRanked PrimalSpan r m
       , v, v, v, v, v, v, v, v, v, v, v, v, v, v
       , a, a, a, a, a, a, a, a, a, a, a, a, a, a
       , Rep ORArray (TKR r n), w, w, w )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon'
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
    , value4Ast, value4AstS, value5Ast, value5AstS
    , gradient9, gradient2Ast, gradient2AstS, gradient2AstST
    , gradient3Ast, gradient3AstS
    , gradient2AstUnSimp, gradient2AstSUnSimp
    , gradient3AstUnSimp, gradient3AstSUnSimp
    , gradient4Ast, gradient4AstS, gradient5Ast, gradient5AstS
    , vals, cderivative, derivative, derivativeRfwd1 ) = do
  let fromORArray t = Nested.rfromOrthotope SNat t
      expected = toADTensorKindShared (Proxy @ORArray) (stensorKind @(TKR r n))
                 $ FlipR $ fromORArray expected'
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
  assertEqualUpToEpsilonWithMark "Val Ast S S" errMargin value0 value5AstS
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
  assertEqualUpToEpsilonWithMark "Grad Ast Simplified S"
                                 errMargin expected gradient5AstS
  assertEqualUpToEpsilonWithMark "Val ADVal Ast" errMargin value0 value9
  assertEqualUpToEpsilonWithMark "Grad ADVal Ast" errMargin expected gradient9
  assertEqualUpToEpsilonWithMark "Derivatives" errMargin cderivative derivative
  assertEqualUpToEpsilonWithMark "Derivatives rfwd"
                                 errMargin cderivative derivativeRfwd1
  -- The formula for comparing derivative and gradient is due to @awf
  -- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
  -- and a similar property stated mathematically is in Lemma 1 in
  -- https://www.microsoft.com/en-us/research/uploads/prod/2021/08/higher-order-ad.pdf
  assertEqualUpToEpsilonWithMark "Reverse vs forward"
                                 1e-5 (tsum0R $ runFlipR derivative) (tdot0R (runFlipR expected) (runFlipR $ toADTensorKindShared (Proxy @ORArray) (stensorKind @(TKR r n)) vals))
  {- TODO: this most probably leaks gigabytes of strings from one test case
  -- to another in -O0 mode, leading to OOMs, so it's disabled for now.
  -- We could also try to stream the strings and compare on the fly.
  --
  -- No Eq instance, so let's compare the text.
  assertEqual "Idempotence of simplification of non-vectorized AST"
              (show astSimp)
              (show (simplifyInlineAst astSimp))
  assertEqual "Idempotence of simplification of vectorized AST"
              (show astVectSimp)
              (show (simplifyInlineAst astVectSimp))
  -}

assertEqualUpToEpsilonShort
    :: forall r m n v a w.
       ( KnownNat n
       , v ~ Rep ORArray (TKR r m)
       , w ~ Rep ORArray (ADTensorKind (TKR r m))
       , a ~ Rep ORArray (ADTensorKind (TKR r n))
       , AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon v
       , AssertEqualUpToEpsilon (ADTensorScalar r)
       , GoodScalar r, GoodScalar (ADTensorScalar r), HasCallStack)
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> OR.Array n r  -- ^ expected reverse derivative value
    -> ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
       , AstRanked PrimalSpan r m, AstRanked PrimalSpan r m
       , v, v, v, v, v, v, v, v, v, v, v, v, v, v
       , a, a, a, a, a, a, a, a, a, a, a, a, a, a
       , Rep ORArray (TKR r n), w, w, w )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilonShort
    errMargin expected'
    ( value0, value1, value2, value3, value2UnSimp, value3UnSimp
    , _value4, value5
    , gradient1, gradientRrev1, gradient2, gradient3
    , gradient2UnSimp, gradientRrev2UnSimp
    , gradient3UnSimp, gradientRrev3UnSimp
    , _gradient4, _gradientRrev4, gradient5, gradientRrev5
    , _astVectSimp, _astSimp
    , _value9, value2Ast, value2AstS, value2AstST, value3Ast, value3AstS
    , value2AstUnSimp, value2AstSUnSimp, value3AstUnSimp, value3AstSUnSimp
    , _value4Ast, _value4AstS, _value5Ast, _value5AstS
    , _gradient9, gradient2Ast, gradient2AstS, gradient2AstST
    , gradient3Ast, gradient3AstS
    , gradient2AstUnSimp, gradient2AstSUnSimp
    , gradient3AstUnSimp, gradient3AstSUnSimp
    , _gradient4Ast, _gradient4AstS, _gradient5Ast, _gradient5AstS
    , vals, cderivative, derivative, derivativeRfwd1 ) = do
  let fromORArray t = Nested.rfromOrthotope SNat t
      expected = toADTensorKindShared (Proxy @ORArray) (stensorKind @(TKR r n))
                 $ FlipR $ fromORArray expected'
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val V UnS" errMargin value0 value2UnSimp
  assertEqualUpToEpsilonWithMark "Val V+S UnS" errMargin value0 value3UnSimp
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
  assertEqualUpToEpsilonWithMark "Derivatives" errMargin cderivative derivative
  assertEqualUpToEpsilonWithMark "Derivatives rfwd"
                                 errMargin cderivative derivativeRfwd1
  assertEqualUpToEpsilonWithMark "Forward vs reverse"
                                 1e-5 (tsum0R $ runFlipR derivative) (tdot0R (runFlipR expected) (runFlipR $ toADTensorKindShared (Proxy @ORArray) (stensorKind @(TKR r n)) vals))
  {- disabled, see above
  -- No Eq instance, so let's compare the text.
  assertEqual "Idempotence of primal simplification"
              (show astSimp)
              (show (simplifyInlineAst astSimp))
  assertEqual "Idempotence of gradient simplification"
              (show astVectSimp)
              (show (simplifyInlineAst astVectSimp))
  -}

t16 :: (Fractional r, Nested.PrimElt r) => ORArray r 5
t16 = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [2, 2, 1, 2, 2] [5, 2, 6, 1, -2, 0.000001, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26]

t16OR :: (VS.Storable r, Fractional r) => FlipR OR.Array r 5
t16OR = FlipR $ OR.fromList [2, 2, 1, 2, 2] [5, 2, 6, 1, -2, 0.000001, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26]

t16b :: (Fractional r, Nested.PrimElt r) => ORArray r 4
t16b = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [2, 2, 2, 2] [5, 2, 6, 1, -2, 0, 0.1, -0.2, 13.1, 9, 8, -4, 582934, 2.99432, -335, 26]

t48 :: (Fractional r, Nested.PrimElt r) => ORArray r 7
t48 = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [3, 1, 2, 2, 1, 2, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

t48OR :: (VS.Storable r, Fractional r) => FlipR OR.Array r 7
t48OR = FlipR $ OR.fromList [3, 1, 2, 2, 1, 2, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

t128 :: (Fractional r, Nested.PrimElt r) => ORArray r 10
t128 = FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] [29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6, 1, -2, 97.1,58.8943200001,97.1,55.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,32.1,40.1,53.0,53.99432, -0.00001, 0.1, -0.2, 13.1, 9, 8, -4, 29, 2.99432, -335, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,40.1,8.0,11.0,-3.0,25.89432,28.79432,-39.09999999999997,25.8,40.1,8.0,11.0,-3.0,25.89432,28.79432,-19.09999999999997,25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432,97.1,55.8943200001,97.1,85.8943200001,97.1,85.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001,97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,89.0,53.99432,97.1,56.8943200001,97.1,52.8943200001,97.1,55.8943200001]

t128OR :: (VS.Storable r, Fractional r) => FlipR OR.Array r 10
t128OR = FlipR $ OR.fromList [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] [29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6, 1, -2, 97.1,58.8943200001,97.1,55.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,32.1,40.1,53.0,53.99432, -0.00001, 0.1, -0.2, 13.1, 9, 8, -4, 29, 2.99432, -335, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,40.1,8.0,11.0,-3.0,25.89432,28.79432,-39.09999999999997,25.8,40.1,8.0,11.0,-3.0,25.89432,28.79432,-19.09999999999997,25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432,97.1,55.8943200001,97.1,85.8943200001,97.1,85.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001,97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,89.0,53.99432,97.1,56.8943200001,97.1,52.8943200001,97.1,55.8943200001]

t128b :: (VS.Storable r, Fractional r) => FlipR OR.Array r 4
t128b = FlipR $ OR.reshape [4, 2, 4, 4] $ runFlipR t128OR

t128c :: (VS.Storable r, Fractional r) => FlipR OR.Array r 4
t128c = FlipR $ OR.reshape [2, 2, 8, 4] $ runFlipR t128OR

rrev1 :: forall g r n r3 m.
         (ADReady g, GoodScalar r, GoodScalar r3, KnownNat n, KnownNat m)
      => (forall f. ADReady f => f r n -> f r3 m) -> g r n
      -> Rep g (ADTensorKind (TKR r n))
rrev1 f u = rrev @g @_ @(TKR r n) @r3 @m
                 f (tshapeFull stensorKind u) u

rrev2 :: forall g r n r3 m.
         (ADReady g, GoodScalar r, GoodScalar r3, KnownNat n, KnownNat m)
      => (forall f. ADReady f => f r n -> f r3 m) -> g r n -> g r n
rrev2 f u =
  let fHVector :: forall f. ADReady f => HVector f -> f r3 m
      fHVector v = f (rfromD $ v V.! 0)
      sh = rshape u
      zero = voidFromSh @r @n sh
      shapes = V.fromList [zero]
      domsOf =
        unHVectorPseudoTensor
        $ rrev @g fHVector (FTKUntyped shapes) (V.singleton $ DynamicRanked u)
  in rletHVectorIn domsOf (\v -> rfromD $ v V.! 0)

rfwd1ds :: forall g r n r3 m.
           (ADReady g, GoodScalar r, GoodScalar r3, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f r n -> f r3 m) -> g r n
        -> Rep g (ADTensorKind (TKR r n))
        -> Rep g (ADTensorKind (TKR r3 m))
rfwd1ds f u ds = rfwd @g @_ @(TKR r n) @r3 @m
                      f (tshapeFull @g stensorKind u) u ds

rfwd1 :: forall g r n r3 m.
         ( ADReady g, GoodScalar r, GoodScalar (ADTensorScalar r)
         , GoodScalar r3, KnownNat n, KnownNat m )
      => (forall f. ADReady f => f r n -> f r3 m) -> g r n
      -> Rep g (ADTensorKind (TKR r3 m))
rfwd1 f u = rfwd1ds @g @r @n @r3 @m
                    f u (rreplicate0N @g @(ADTensorScalar r) (rshape u) 1)

srev1 :: forall g r sh r3 sh2.
         ( ADReadyS g, GoodScalar r, GoodScalar r3, KnownShS sh, KnownShS sh2
         , ADTensorKind (TKS r3 sh2) ~ TKS r3 sh2 )
      => (forall f. ADReadyS f => f r sh -> f r3 sh2) -> g r sh
      -> Rep (RankedOf g) (ADTensorKind (TKS r sh))
srev1 f u = srev @_ @g @(TKS r sh) @r3 @sh2
                 f (tshapeFull @(RankedOf g) stensorKind u) u

sfwd1 :: forall g r sh r3 sh2.
         ( ADReadyS g, GoodScalar r, GoodScalar (ADTensorScalar r)
         , GoodScalar r3, KnownShS sh, KnownShS sh2 )
      => (forall f. ADReadyS f => f r sh -> f r3 sh2) -> g r sh
      -> Rep (RankedOf g) (ADTensorKind (TKS r3 sh2))
sfwd1 f u = sfwd @_ @g @(TKS r sh) @r3 @sh2
                 f (tshapeFull @(RankedOf g) stensorKind u)
                 u (srepl @_ @(ADTensorScalar r) 1)

treplicateR
  :: forall n r. (KnownNat n, KnownNat (1 + n), VS.Storable r)
  => Int -> OR.Array n r -> OR.Array (1 + n) r
treplicateR 0 u = OR.fromList (0 : OR.shapeL u) []
treplicateR s u = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> OR.constant [s] (OR.unScalar u)
  _ -> OR.ravel $ ORB.constant [s] u

tfromListR
  :: forall n r. (KnownNat (1 + n), VS.Storable r)
  => NonEmpty (OR.Array n r) -> OR.Array (1 + n) r
tfromListR l = OR.ravel . ORB.fromList [NonEmpty.length l] . NonEmpty.toList $ l

tfromList0NR
  :: (KnownNat n, VS.Storable r)
  => IShR n -> [r] -> OR.Array n r
tfromList0NR sh = OR.fromList (shapeToList sh)

tsumR
  :: forall n r. (KnownNat (n + 1), GoodScalar r)
  => OR.Array (n + 1) r -> OR.Array n r
tsumR t = Nested.rtoOrthotope $ Nested.rsumOuter1 $ Nested.rfromOrthotope SNat t
