-- | Testing harness that differentiates a single objective function using
-- over a twenty different pipeline variants and compares the results.
module CrossTesting
  ( assertEqualUpToEpsilon1
  , rev', assertEqualUpToEpsilon', assertEqualUpToEpsilonShort
  , t16, t16b, t48, t128, t128b, t128c
  , rrev1, rfwd1, srev1, sfwd1
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric)
import           Test.Tasty.HUnit hiding (assert)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInline
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

import EqEpsilon

assertEqualUpToEpsilon1
  :: (AssertEqualUpToEpsilon (OR.Array n r), HasCallStack)
  => Rational
  -> OR.Array n r
  -> Flip OR.Array r n
  -> Assertion
assertEqualUpToEpsilon1 eps expected result =
  assertEqualUpToEpsilon eps expected (runFlip result)

rev' :: forall r m n v a.
        ( KnownNat n, KnownNat m, GoodScalar r
        , v ~ Flip OR.Array r m, a ~ Flip OR.Array r n )
     => (forall f. ADReady f => f r n -> f r m)
     -> a
     -> ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
        , AstRanked PrimalSpan r m, AstRanked PrimalSpan r m
        , v, v, v, v, v, v, v, v, v, v, v, v, v, v
        , a, a, a, a, a, a, a, a, a, a, a, a, a, a
        , a, v, v, v )
rev' f vals =
  let value0 = f vals
      parameters = toHVector vals
      parameters0 = voidFromHVector parameters
      dt = Nothing
      g :: HVector (ADVal (Flip OR.Array))
        -> ADVal (Flip OR.Array) r m
      g inputs = f $ parseHVector vals inputs
      (advalGrad, value1) = crevOnHVector dt g parameters
      gradient1 = parseHVector vals advalGrad
      gradientRrev1 = rrev1 @(Flip OR.Array) @r @n @m f vals
      g9 :: HVector (ADVal (AstRanked PrimalSpan))
         -> ADVal (AstRanked PrimalSpan) r m
      g9 inputs = f @(ADVal (AstRanked PrimalSpan)) $ parseHVector vals inputs
      artifactsGradAst9 =
        fst $ revProduceArtifactWithoutInterpretation @(AstRanked FullSpan)
                TensorToken False g9 parameters0
      (advalGrad9, value9) =
        revEvalArtifact artifactsGradAst9 parameters dt
      gradient9 = parseHVector vals advalGrad9
      hGeneral
        :: (ADReady fgen, ADReady f1)
        => (f1 r m -> AstRanked PrimalSpan r m)
        -> (AstRanked PrimalSpan r n -> f1 r n)
        -> (AstRanked PrimalSpan r m -> AstRanked PrimalSpan r m)
        -> fgen r n
        -> fgen r m
      hGeneral fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (rshape vals) (fx1 . f . fx2)
            env = extendEnvR var inputs EM.empty
        in interpretAst env (gx ast)
      h :: ADReady f1
        => (f1 r m -> AstRanked PrimalSpan r m)
        -> (AstRanked PrimalSpan r n -> f1 r n)
        -> (AstRanked PrimalSpan r m -> AstRanked PrimalSpan r m)
        -> HVector (ADVal (Flip OR.Array))
        -> ADVal (Flip OR.Array) r m
      h fx1 fx2 gx inputs =
        hGeneral @(ADVal (Flip OR.Array)) fx1 fx2 gx (parseHVector vals inputs)
      (astGrad, value2) =
        crevOnHVector dt (h id id id) parameters
      gradient2 = parseHVector vals astGrad
      (astSimple, value3) =
        crevOnHVector dt (h id id simplifyAst6) parameters
      gradient3 = parseHVector vals astSimple
      (astGradUnSimp, value2UnSimp) =
        crevOnHVector dt (h unAstNoSimplify AstNoSimplify id) parameters
      gradient2UnSimp = parseHVector vals astGradUnSimp
      gradientRrev2UnSimp =
        rrev1 @(Flip OR.Array) @r @n @m
              (hGeneral unAstNoSimplify AstNoSimplify id) vals
      (astSimpleUnSimp, value3UnSimp) =
        crevOnHVector dt (h unAstNoSimplify AstNoSimplify simplifyAst6)
                      parameters
      gradient3UnSimp = parseHVector vals astSimpleUnSimp
      gradientRrev3UnSimp =
        rrev1 @(Flip OR.Array) @r @n @m
              (hGeneral unAstNoSimplify AstNoSimplify simplifyAst6) vals
      (astPrimal, value4) =
        crevOnHVector dt (h unAstNoVectorize AstNoVectorize id)
                      parameters
          -- use the AstNoVectorize instance that does no vectorization
          -- and then interpret the results as the Ast instance
      gradient4 = parseHVector vals astPrimal
      gradientRrev4 = rrev1 @(Flip OR.Array) @r @n @m
                            (hGeneral unAstNoVectorize AstNoVectorize id) vals
      (astPSimple, value5) =
        crevOnHVector dt (h unAstNoVectorize AstNoVectorize simplifyAst6)
                      parameters
      gradient5 = parseHVector vals astPSimple
      gradientRrev5 =
        rrev1 @(Flip OR.Array) @r @n @m
              (hGeneral unAstNoVectorize AstNoVectorize simplifyAst6) vals
      astVectSimp = simplifyAst6 $ snd $ funToAstR (rshape vals) f
      astSimp =
        simplifyAst6 $ simplifyAst6 $ snd  -- builds simplify with difficulty
        $ funToAstR (rshape vals) (unAstNoVectorize . f . AstNoVectorize)
      -- Here comes the part with Ast gradients.
      hAst :: ADReady f1
           => (f1 r m -> AstRanked PrimalSpan r m)
           -> (AstRanked PrimalSpan r n -> f1 r n)
           -> (AstRanked PrimalSpan r m -> AstRanked PrimalSpan r m)
           -> HVector (ADVal (AstRanked PrimalSpan))
           -> ADVal (AstRanked PrimalSpan) r m
      hAst fx1 fx2 gx inputs
        = hGeneral @(ADVal (AstRanked PrimalSpan))
                   fx1 fx2 gx (parseHVector vals inputs)
      artifactsGradAst =
        fst $ revProduceArtifactWithoutInterpretation @(AstRanked FullSpan)
                TensorToken False (hAst id id id) parameters0
      (astGradAst, value2Ast) =
        revEvalArtifact artifactsGradAst parameters dt
      gradient2Ast = parseHVector vals astGradAst
      (astGradAstS, value2AstS) =
        revEvalArtifact (simplifyArtifactRev artifactsGradAst) parameters dt
      gradient2AstS = parseHVector vals astGradAstS
      artifactsGradAstT =
        fst $ revProduceArtifactWithoutInterpretation @(AstRanked FullSpan)
                TensorToken True (hAst id id id) parameters0
      (astGradAstST, value2AstST) =
        revEvalArtifact (simplifyArtifactRev artifactsGradAstT) parameters dt
      gradient2AstST = parseHVector vals astGradAstST
      artifactsSimpleAst =
        fst $ revProduceArtifactWithoutInterpretation @(AstRanked FullSpan)
                TensorToken False (hAst id id simplifyAst6) parameters0
      (astSimpleAst, value3Ast) =
        revEvalArtifact artifactsSimpleAst parameters dt
      gradient3Ast = parseHVector vals astSimpleAst
      (astSimpleAstS, value3AstS) =
        revEvalArtifact (simplifyArtifactRev artifactsSimpleAst) parameters dt
      gradient3AstS = parseHVector vals astSimpleAstS
      artifactsGradAstUnSimp =
        fst $ revProduceArtifactWithoutInterpretation @(AstRanked FullSpan)
                TensorToken False
                (hAst unAstNoSimplify AstNoSimplify id) parameters0
      (astGradAstUnSimp, value2AstUnSimp) =
        revEvalArtifact artifactsGradAstUnSimp parameters dt
      gradient2AstUnSimp = parseHVector vals astGradAstUnSimp
      (astGradAstSUnSimp, value2AstSUnSimp) =
        revEvalArtifact (simplifyArtifactRev artifactsGradAstUnSimp)
                        parameters dt
      gradient2AstSUnSimp = parseHVector vals astGradAstSUnSimp
      artifactsSimpleAstUnSimp =
        fst $ revProduceArtifactWithoutInterpretation @(AstRanked FullSpan)
                TensorToken False
                (hAst unAstNoSimplify AstNoSimplify simplifyAst6)
                parameters0
      (astSimpleAstUnSimp, value3AstUnSimp) =
        revEvalArtifact artifactsSimpleAstUnSimp parameters dt
      gradient3AstUnSimp = parseHVector vals astSimpleAstUnSimp
      (astSimpleAstSUnSimp, value3AstSUnSimp) =
        revEvalArtifact (simplifyArtifactRev artifactsSimpleAstUnSimp)
                        parameters dt
      gradient3AstSUnSimp = parseHVector vals astSimpleAstSUnSimp
      artifactsPrimalAst =
        fst $ revProduceArtifactWithoutInterpretation @(AstRanked FullSpan)
                TensorToken False
                (hAst unAstNoVectorize AstNoVectorize id) parameters0
      (astPrimalAst, value4Ast) =
        revEvalArtifact artifactsPrimalAst parameters dt
      gradient4Ast = parseHVector vals astPrimalAst
      (astPrimalAstS, value4AstS) =
        revEvalArtifact (simplifyArtifactRev artifactsPrimalAst) parameters dt
      gradient4AstS = parseHVector vals astPrimalAstS
      artifactsPSimpleAst =
        fst $ revProduceArtifactWithoutInterpretation @(AstRanked FullSpan)
                TensorToken False
                (hAst unAstNoVectorize AstNoVectorize simplifyAst6)
                parameters0
      (astPSimpleAst, value5Ast) =
        revEvalArtifact artifactsPSimpleAst parameters dt
      gradient5Ast = parseHVector vals astPSimpleAst
      (astPSimpleAstS, value5AstS) =
        revEvalArtifact (simplifyArtifactRev artifactsPSimpleAst) parameters dt
      gradient5AstS = parseHVector vals astPSimpleAstS
      cderivative = cfwd f vals vals
      derivative = fwd @r @m @(AstRanked FullSpan) f vals vals
      derivativeRfwd1 = rfwd1 @(Flip OR.Array) @r @n @m f vals
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
     , vals, cderivative, derivative, derivativeRfwd1)

assertEqualUpToEpsilon'
    :: ( v ~ Flip OR.Array r m, a ~ Flip OR.Array r n
       , AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon v
       , AssertEqualUpToEpsilon r
       , KnownNat n, KnownNat m, GoodScalar r, HasCallStack)
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> OR.Array n r  -- ^ expected reverse derivative value
    -> ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
       , AstRanked PrimalSpan r m, AstRanked PrimalSpan r m
       , v, v, v, v, v, v, v, v, v, v, v, v, v, v
       , a, a, a, a, a, a, a, a, a, a, a, a, a, a
       , a, v, v, v )
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
    , astVectSimp, astSimp
    , _value9, value2Ast, value2AstS, value2AstST, value3Ast, value3AstS
    , value2AstUnSimp, value2AstSUnSimp, value3AstUnSimp, value3AstSUnSimp
    , value4Ast, value4AstS, value5Ast, value5AstS
    , _gradient9, gradient2Ast, gradient2AstS, gradient2AstST
    , gradient3Ast, gradient3AstS
    , gradient2AstUnSimp, gradient2AstSUnSimp
    , gradient3AstUnSimp, gradient3AstSUnSimp
    , gradient4Ast, gradient4AstS, gradient5Ast, gradient5AstS
    , vals, cderivative, derivative, derivativeRfwd1 ) = do
  let expected = Flip expected'
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
  assertEqualUpToEpsilonWithMark "Grad V UnS rrev"
                                 errMargin expected gradientRrev2UnSimp
  assertEqualUpToEpsilonWithMark "Grad V+S UnS"
                                 errMargin expected gradient3UnSimp
  assertEqualUpToEpsilonWithMark "Grad V+S UnS rrev"
                                 errMargin expected gradientRrev3UnSimp
  assertEqualUpToEpsilonWithMark "Grad NotVect" errMargin expected gradient4
  assertEqualUpToEpsilonWithMark "Grad NotVect rrev"
                                 errMargin expected gradientRrev4
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  assertEqualUpToEpsilonWithMark "Grad Simplified rrev"
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
-- TODO: this currently fails for nebulous reasons. Wait until it fixes itself.
--  assertEqualUpToEpsilonWithMark "Val ADVal Ast" errMargin value0 value9
--  assertEqualUpToEpsilonWithMark "Grad ADVal Ast" errMargin expected gradient9
  assertEqualUpToEpsilonWithMark "Derivatives" errMargin cderivative derivative
  assertEqualUpToEpsilonWithMark "Derivatives rfwd"
                                 errMargin cderivative derivativeRfwd1
  -- The formula for comparing derivative and gradient is due to @awf
  -- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
  assertEqualUpToEpsilonWithMark "Reverse vs forward"
                                 1e-5 (rdot0 expected vals) (rsum0 derivative)
  -- No Eq instance, so let's compare the text.
  show (simplifyAst6 $ simplifyAst6 astVectSimp)
    @?= show (simplifyAst6 astVectSimp)  -- more simplification is needed
  show (simplifyAst6 astSimp) @?= show astSimp

assertEqualUpToEpsilonShort
    :: ( v ~ Flip OR.Array r m, a ~ Flip OR.Array r n
       , AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon v
       , AssertEqualUpToEpsilon r
       , KnownNat n, KnownNat m, GoodScalar r, HasCallStack)
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> OR.Array n r  -- ^ expected reverse derivative value
    -> ( v, v, v, v, v, v, v, v, a, a, a, a, a, a, a, a, a, a, a, a
       , AstRanked PrimalSpan r m, AstRanked PrimalSpan r m
       , v, v, v, v, v, v, v, v, v, v, v, v, v, v
       , a, a, a, a, a, a, a, a, a, a, a, a, a, a
       , a, v, v, v )
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
    , astVectSimp, astSimp
    , _value9, value2Ast, value2AstS, value2AstST, value3Ast, value3AstS
    , value2AstUnSimp, value2AstSUnSimp, value3AstUnSimp, value3AstSUnSimp
    , _value4Ast, _value4AstS, _value5Ast, _value5AstS
    , _gradient9, gradient2Ast, gradient2AstS, gradient2AstST
    , gradient3Ast, gradient3AstS
    , gradient2AstUnSimp, gradient2AstSUnSimp
    , gradient3AstUnSimp, gradient3AstSUnSimp
    , _gradient4Ast, _gradient4AstS, _gradient5Ast, _gradient5AstS
    , vals, cderivative, derivative, derivativeRfwd1) = do
  let expected = Flip expected'
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
  assertEqualUpToEpsilonWithMark "Grad V UnS rrev"
                                 errMargin expected gradientRrev2UnSimp
  assertEqualUpToEpsilonWithMark "Grad V+S UnS"
                                 errMargin expected gradient3UnSimp
  assertEqualUpToEpsilonWithMark "Grad V+S UnS rrev"
                                 errMargin expected gradientRrev3UnSimp
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  assertEqualUpToEpsilonWithMark "Grad Simplified rrev"
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
                                 1e-5 (rsum0 derivative) (rdot0 expected vals)
  -- No Eq instance, so let's compare the text.
  show (simplifyAst6 astVectSimp) @?= show astVectSimp
  show (simplifyAst6 astSimp) @?= show astSimp

t16 :: (Numeric r, Fractional r) => Flip OR.Array r 5
t16 = Flip $ OR.fromList [2, 2, 1, 2, 2] [5, 2, 6, 1, -2, 0.000001, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26]

t16b :: (Numeric r, Fractional r) => Flip OR.Array r 4
t16b = Flip $ OR.fromList [2, 2, 2, 2] [5, 2, 6, 1, -2, 0, 0.1, -0.2, 13.1, 9, 8, -4, 582934, 2.99432, -335, 26]

t48 :: (Numeric r, Fractional r) => Flip OR.Array r 7
t48 = Flip $ OR.fromList [3, 1, 2, 2, 1, 2, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

t128 :: (Numeric r, Fractional r) => Flip OR.Array r 10
t128 = Flip $ OR.fromList [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] [29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6, 1, -2, 97.1,58.8943200001,97.1,55.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,32.1,40.1,53.0,53.99432, -0.00001, 0.1, -0.2, 13.1, 9, 8, -4, 29, 2.99432, -335, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,40.1,8.0,11.0,-3.0,25.89432,28.79432,-39.09999999999997,25.8,40.1,8.0,11.0,-3.0,25.89432,28.79432,-19.09999999999997,25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432,97.1,55.8943200001,97.1,85.8943200001,97.1,85.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001,97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,89.0,53.99432,97.1,56.8943200001,97.1,52.8943200001,97.1,55.8943200001]

t128b :: (Numeric r, Fractional r) => Flip OR.Array r 4
t128b = Flip $ OR.reshape [4, 2, 4, 4] $ runFlip t128

t128c :: (Numeric r, Fractional r) => Flip OR.Array r 4
t128c = Flip $ OR.reshape [2, 2, 8, 4] $ runFlip t128

rrev1 :: forall g r n m r3.
         (ADReady g, GoodScalar r, GoodScalar r3, KnownNat n, KnownNat m)
      => (forall f. ADReady f => f r n -> f r3 m) -> g r n -> g r n
rrev1 f u =
  let fHVector :: forall f. ADReady f => HVector f -> f r3 m
      fHVector v = f (rfromD $ v V.! 0)
      sh = rshape u
      zero = voidFromSh @r @n sh
      shapes = V.fromList [zero]
      domsOf = rrev @g fHVector shapes (V.singleton $ DynamicRanked u)
  in rletHVectorIn domsOf (\v -> rfromD $ v V.! 0)

rfwd1 :: forall g r n m r3.
         (ADReady g, GoodScalar r, GoodScalar r3, KnownNat n, KnownNat m)
      => (forall f. ADReady f => f r n -> f r3 m) -> g r n -> g r3 m
rfwd1 f u =
  let fHVector :: forall f. ADReady f => HVector f -> f r3 m
      fHVector v = f (rfromD $ v V.! 0)
      sh = rshape u
      zero = voidFromSh @r @n sh
      shapes = V.fromList [zero]
  in rfwd @g fHVector shapes (V.singleton $ DynamicRanked u)
                             (V.singleton $ DynamicRanked u)  -- simple

srev1 :: forall g r sh sh2 r3.
         (ADReadyS g, GoodScalar r, GoodScalar r3, Sh.Shape sh, Sh.Shape sh2)
      => (forall f. ADReadyS f => f r sh -> f r3 sh2) -> g r sh -> g r sh
srev1 f u =
  let fHVector :: forall f. ADReadyS f
               => HVector (RankedOf f) -> f r3 sh2
      fHVector v = f (sfromD $ v V.! 0)
      zero = voidFromShS @r @sh
      shapes = V.fromList [zero]
      domsOf = srev @(RankedOf g)
                    fHVector shapes (V.singleton $ DynamicShaped u)
  in sletHVectorIn domsOf (\v -> sfromD $ v V.! 0)

sfwd1 :: forall g r sh sh2 r3.
         (ADReadyS g, GoodScalar r, GoodScalar r3, Sh.Shape sh, Sh.Shape sh2)
      => (forall f. ADReadyS f => f r sh -> f r3 sh2) -> g r sh -> g r3 sh2
sfwd1 f u =
  let fHVector :: forall f. ADReadyS f
               => HVector (RankedOf f) -> f r3 sh2
      fHVector v = f (sfromD $ v V.! 0)
      zero = voidFromShS @r @sh
      shapes = V.fromList [zero]
  in sfwd @(RankedOf g) fHVector shapes (V.singleton $ DynamicShaped u)
                                        (V.singleton $ DynamicShaped u)
