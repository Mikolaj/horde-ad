module CrossTesting
  ( rev', assertEqualUpToEpsilon', assertEqualUpToEpsilonShort
  , t16, t16b, t48, t128, t128b, t128c
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import qualified Data.EnumMap.Strict as EM
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty.HUnit hiding (assert)

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.TensorADVal (ADTensor)
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor

import EqEpsilon

rev' :: forall a r n m.
        ( KnownNat n, KnownNat m, Floating (Vector r), ADTensor r, ADReady r
        , InterpretAst (ADVal r), InterpretAst r, DomainsTensor r
        , a ~ TensorOf m r, ScalarOf r ~ r, ScalarOf (ADVal r) ~ r
        , IsPrimalWithScalar (TensorOf m r) r, DomainsOf r ~ Domains r
        , Adaptable (ADVal (TensorOf n r))
        , TensorOf n (ADVal r) ~ ADVal (TensorOf n r)
        , TensorOf m (ADVal r) ~ ADVal (TensorOf m r)
        , ADReady (ADVal r), TensorOf n r ~ OR.Array n r )
     => (forall x. ADReady x => TensorOf n x -> TensorOf m x)
     -> TensorOf n r
     -> ( TensorOf m r, a, a, a, a, a
        , TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r
        , Ast m r, Ast m r
        , a, a, a, a, a, a, a, a, a
        , TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r
        , TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r )
rev' f vals =
  let value0 = f vals
      parameters = toDomains vals
      dt = Nothing
      g inputs = f $ parseADInputs vals inputs
      (advalGrad, value1) = revOnDomains dt g parameters
      gradient1 = parseDomains vals advalGrad
      g9 inputs = f $ parseADInputs vals inputs
      (advalGrad9, value9) = revAstOnDomains g9 parameters dt
      gradient9 = parseDomains vals advalGrad9
      h :: ADReady x
        => (TensorOf m x -> Ast m r) -> (Ast n r -> TensorOf n x)
        -> (Ast m r -> Ast m r) -> ADInputs r
        -> ADVal (TensorOf m r)
      h fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (tshape vals) (fx1 . f . fx2)
            env = extendEnvR var (parseADInputs vals inputs) EM.empty
        in snd $ interpretAst env emptyMemo (gx ast)
      (astGrad, value2) = revOnDomains dt (h id id id) parameters
      gradient2 = parseDomains vals astGrad
      (astSimple, value3) =
        revOnDomains dt (h id id simplifyAst6) parameters
      gradient3 = parseDomains vals astSimple
      (astPrimal, value4) =
        revOnDomains dt (h unAstNoVectorize AstNoVectorize id)
                        parameters
          -- use the AstNoVectorize instance that does no vectorization
          -- and then interpret the results as the Ast instance
      gradient4 = parseDomains vals astPrimal
      (astPSimple, value5) =
        revOnDomains dt (h unAstNoVectorize AstNoVectorize simplifyAst6)
                        parameters
      gradient5 = parseDomains vals astPSimple
      astVectSimp = simplifyAst6 $ snd $ funToAstR (tshape vals) f
      astSimp =
        simplifyAst6 $ snd
        $ funToAstR (tshape vals) (unAstNoVectorize . f . AstNoVectorize)
      -- Here comes the part with Ast gradients.
      hAst :: ADReady x
           => (TensorOf m x -> Ast m r) -> (Ast n r -> TensorOf n x)
           -> (Ast m r -> Ast m r) -> ADInputs (Ast0 r)
           -> ADVal (Ast m r)
      hAst fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (tshape vals) (fx1 . f . fx2)
            env = extendEnvR var (parseADInputs vals inputs) EM.empty
        in snd $ interpretAst env emptyMemo (gx ast)
      artifactsGradAst =
        revAstOnDomainsF (hAst id id id) parameters
      (astGradAst, value2Ast) =
        revAstOnDomainsEval artifactsGradAst parameters dt
      gradient2Ast = parseDomains vals astGradAst
      (astGradAstS, value2AstS) =
        revAstOnDomainsEval (simplifyArtifact6 artifactsGradAst) parameters dt
      gradient2AstS = parseDomains vals astGradAstS
      artifactsSimpleAst =
        revAstOnDomainsF (hAst id id simplifyAst6) parameters
      (astSimpleAst, value3Ast) =
        revAstOnDomainsEval artifactsSimpleAst parameters dt
      gradient3Ast = parseDomains vals astSimpleAst
      (astSimpleAstS, value3AstS) =
        revAstOnDomainsEval (simplifyArtifact6 artifactsSimpleAst) parameters dt
      gradient3AstS = parseDomains vals astSimpleAstS
      artifactsPrimalAst =
        revAstOnDomainsF (hAst unAstNoVectorize AstNoVectorize id) parameters
      (astPrimalAst, value4Ast) =
        revAstOnDomainsEval artifactsPrimalAst parameters dt
      gradient4Ast = parseDomains vals astPrimalAst
      (astPrimalAstS, value4AstS) =
        revAstOnDomainsEval (simplifyArtifact6 artifactsPrimalAst) parameters dt
      gradient4AstS = parseDomains vals astPrimalAstS
      artifactsPSimpleAst =
        revAstOnDomainsF (hAst unAstNoVectorize AstNoVectorize simplifyAst6)
                         parameters
      (astPSimpleAst, value5Ast) =
        revAstOnDomainsEval artifactsPSimpleAst parameters dt
      gradient5Ast = parseDomains vals astPSimpleAst
      (astPSimpleAstS, value5AstS) =
        revAstOnDomainsEval (simplifyArtifact6 artifactsPSimpleAst)
                            parameters dt
      gradient5AstS = parseDomains vals astPSimpleAstS
  in ( value0, value1, value2, value3, value4, value5
     , gradient1, gradient2, gradient3, gradient4, gradient5
     , astVectSimp, astSimp
     , value9, value2Ast, value2AstS, value3Ast, value3AstS
     , value4Ast, value4AstS, value5Ast, value5AstS
     , gradient9, gradient2Ast, gradient2AstS, gradient3Ast, gradient3AstS
     , gradient4Ast, gradient4AstS, gradient5Ast, gradient5AstS )

assertEqualUpToEpsilon'
    :: ( AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon b
       , KnownNat m, ShowAstSimplify r, HasCallStack )
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> a  -- ^ expected value
    -> ( b, b, b, b, b, b, a, a, a, a, a, Ast m r, Ast m r
       , b, b, b, b, b, b, b, b, b, a, a, a, a, a, a, a, a, a )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon'
    errMargin expected
    ( value0, value1, value2, value3, value4, value5
    , gradient1, gradient2, gradient3, gradient4, gradient5
    , astVectSimp, astSimp
    , value9, value2Ast, value2AstS, value3Ast, value3AstS
    , value4Ast, value4AstS, value5Ast, value5AstS
    , gradient9, gradient2Ast, gradient2AstS, gradient3Ast, gradient3AstS
    , gradient4Ast, gradient4AstS, gradient5Ast, gradient5AstS ) = do
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val NotVect" errMargin value0 value4
  assertEqualUpToEpsilonWithMark "Val Simplified" errMargin value0 value5
  assertEqualUpToEpsilonWithMark "Grad ADVal" errMargin expected gradient1
  assertEqualUpToEpsilonWithMark "Grad Vectorized" errMargin expected gradient2
  assertEqualUpToEpsilonWithMark "Grad Vect+Simp" errMargin expected gradient3
  assertEqualUpToEpsilonWithMark "Grad NotVect" errMargin expected gradient4
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  assertEqualUpToEpsilonWithMark "Val Ast Vectorized" errMargin value0 value2Ast
  assertEqualUpToEpsilonWithMark "Val Ast V S" errMargin value0 value2AstS
  assertEqualUpToEpsilonWithMark "Val Ast Vect+Simp" errMargin value0 value3Ast
  assertEqualUpToEpsilonWithMark "Val Ast V+S S" errMargin value0 value3AstS
  assertEqualUpToEpsilonWithMark "Val Ast NotVect" errMargin value0 value4Ast
  assertEqualUpToEpsilonWithMark "Val Ast NotVect S" errMargin value0 value4AstS
  assertEqualUpToEpsilonWithMark "Val Ast Simplified" errMargin value0 value5Ast
  assertEqualUpToEpsilonWithMark "Val Ast S S" errMargin value0 value5AstS
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized"
                                 errMargin expected gradient2Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized S"
                                 errMargin expected gradient2AstS
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp"
                                 errMargin expected gradient3Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp S"
                                 errMargin expected gradient3AstS
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
  -- No Eq instance, so let's compare the text.
  show (simplifyAst6 astVectSimp) @?= show astVectSimp
  show (simplifyAst6 astSimp) @?= show astSimp

assertEqualUpToEpsilonShort
    :: ( AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon b
       , KnownNat m, ShowAstSimplify r, HasCallStack )
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> a  -- ^ expected value
    -> ( b, b, b, b, b, b, a, a, a, a, a, Ast m r, Ast m r
       , b, b, b, b, b, b, b, b, b, a, a, a, a, a, a, a, a, a )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilonShort
    errMargin expected
    ( value0, value1, value2, value3, _value4, value5
    , gradient1, gradient2, gradient3, _gradient4, gradient5
    , astVectSimp, astSimp
    , _value9, value2Ast, value2AstS, value3Ast, value3AstS
    , _value4Ast, _value4AstS, _value5Ast, _value5AstS
    , _gradient9, gradient2Ast, gradient2AstS, gradient3Ast, gradient3AstS
    , _gradient4Ast, _gradient4AstS, _gradient5Ast, _gradient5AstS ) = do
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val Simplified" errMargin value0 value5
  assertEqualUpToEpsilonWithMark "Grad ADVal" errMargin expected gradient1
  assertEqualUpToEpsilonWithMark "Grad Vectorized" errMargin expected gradient2
  assertEqualUpToEpsilonWithMark "Grad Vect+Simp" errMargin expected gradient3
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  assertEqualUpToEpsilonWithMark "Val Ast Vectorized" errMargin value0 value2Ast
  assertEqualUpToEpsilonWithMark "Val Ast V S" errMargin value0 value2AstS
  assertEqualUpToEpsilonWithMark "Val Ast Vect+Simp" errMargin value0 value3Ast
  assertEqualUpToEpsilonWithMark "Val Ast V+S S" errMargin value0 value3AstS
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized"
                                 errMargin expected gradient2Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized S"
                                 errMargin expected gradient2AstS
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp"
                                 errMargin expected gradient3Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp S"
                                 errMargin expected gradient3AstS
  -- No Eq instance, so let's compare the text.
  show (simplifyAst6 astVectSimp) @?= show astVectSimp
  show (simplifyAst6 astSimp) @?= show astSimp

t16 :: (Numeric r, Fractional r) => OR.Array 5 r
t16 = OR.fromList [2, 2, 1, 2, 2] [5, 2, 6, 1, -2, 0.000001, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26]

t16b :: (Numeric r, Fractional r) => OR.Array 4 r
t16b = OR.fromList [2, 2, 2, 2] [5, 2, 6, 1, -2, 0, 0.1, -0.2, 13.1, 9, 8, -4, 582934, 2.99432, -335, 26]

t48 :: (Numeric r, Fractional r) => OR.Array 7 r
t48 = OR.fromList [3, 1, 2, 2, 1, 2, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

t128 :: (Numeric r, Fractional r) => OR.Array 10 r
t128 = OR.fromList [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] [29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6, 1, -2, 97.1,58.8943200001,97.1,55.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,32.1,40.1,53.0,53.99432, -0.00001, 0.1, -0.2, 13.1, 9, 8, -4, 29, 2.99432, -335, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,40.1,8.0,11.0,-3.0,25.89432,28.79432,-39.09999999999997,25.8,40.1,8.0,11.0,-3.0,25.89432,28.79432,-19.09999999999997,25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432,97.1,55.8943200001,97.1,85.8943200001,97.1,85.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001,97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,89.0,53.99432,97.1,56.8943200001,97.1,52.8943200001,97.1,55.8943200001]

t128b :: (Numeric r, Fractional r) => OR.Array 4 r
t128b = OR.reshape [4, 2, 4, 4] t128

t128c :: (Numeric r, Fractional r) => OR.Array 4 r
t128c = OR.reshape [2, 2, 8, 4] t128