module CrossTesting
  ( assertEqualUpToEpsilon1
  , rev', assertEqualUpToEpsilon', assertEqualUpToEpsilonShort
  , t16, t16b, t48, t128, t128b, t128c
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Tannen
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Compose
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric)
import           Test.Tasty.HUnit hiding (assert)

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Domains
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.TensorClass

import EqEpsilon

assertEqualUpToEpsilon1
  :: (AssertEqualUpToEpsilon (OR.Array n r), HasCallStack)
  => Rational
  -> OR.Array n r
  -> Flip OR.Array r n
  -> Assertion
assertEqualUpToEpsilon1 eps expected result =
  assertEqualUpToEpsilon eps expected (runFlip result)

rev' :: forall r m n v g.
        ( KnownNat n, KnownNat m, ADReady AstRanked r
        , InterpretAstA (Flip OR.Array) r
        , InterpretAstA (Tannen ADVal (Flip OR.Array)) r
        , v ~ Flip OR.Array r m, g ~ Flip OR.Array r n )
     => (forall f x. ADReady f x => f x n -> f x m)
     -> g
     -> ( v, v, v, v, v, v, v, v, g, g, g, g, g, g, g, Ast m r, Ast m r
        , v, v, v, v, v, v, v, v, v, v, v, v, v
        , g, g, g, g, g, g, g, g, g, g, g, g, g )
rev' f vals =
  let value0 = f vals
      parameters = toDomains vals
      dt = Nothing
      g :: Domains (Compose ADVal OD.Array) r
        -> Tannen ADVal (Flip OR.Array) r m
      g inputs = f $ Tannen $ parseDomains vals inputs
      (advalGrad, value1) = revOnDomains dt (runTannen . g) parameters
      gradient1 = parseDomains vals advalGrad
      g9 :: Domains (Compose ADVal AstDynamic) r
         -> Tannen ADVal AstRanked r m
      g9 inputs = f $ Tannen $ parseDomains vals inputs
      (advalGrad9, value9) = revAstOnDomains g9 parameters dt
      gradient9 = parseDomains vals advalGrad9
      h :: ADReady f1 r
        => (f1 r m -> Ast m r) -> (Ast n r -> f1 r n)
        -> (Ast m r -> Ast m r) -> Domains (Compose ADVal OD.Array) r
        -> ADVal (Flip OR.Array r m)
      h fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (tshape vals) (fx1 . f . fx2)
            env = extendEnvR var (Tannen $ parseDomains vals inputs) EM.empty
        in runTannen $ snd $ interpretAst env emptyMemo (gx ast)
      (astGrad, value2) =
        revOnDomains dt (h id id id) parameters
      gradient2 = parseDomains vals astGrad
      (astSimple, value3) =
        revOnDomains dt (h id id simplifyAst6) parameters
      gradient3 = parseDomains vals astSimple
      (astGradUnSimp, value2UnSimp) =
        revOnDomains dt (h unAstNoSimplify AstNoSimplify id) parameters
      gradient2UnSimp = parseDomains vals astGradUnSimp
      (astSimpleUnSimp, value3UnSimp) =
        revOnDomains dt (h unAstNoSimplify AstNoSimplify simplifyAst6)
                     parameters
      gradient3UnSimp = parseDomains vals astSimpleUnSimp
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
      hAst :: ADReady f1 r
           => (f1 r m -> Ast m r) -> (Ast n r -> f1 r n)
           -> (Ast m r -> Ast m r) -> Domains (Compose ADVal AstDynamic) r
           -> Tannen ADVal AstRanked r m
      hAst fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (tshape vals) (fx1 . f . fx2)
            env = extendEnvR var (Tannen $ parseDomains vals inputs) EM.empty
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
      artifactsGradAstUnSimp =
        revAstOnDomainsF (hAst unAstNoSimplify AstNoSimplify id) parameters
      (astGradAstUnSimp, value2AstUnSimp) =
        revAstOnDomainsEval artifactsGradAstUnSimp parameters dt
      gradient2AstUnSimp = parseDomains vals astGradAstUnSimp
      (astGradAstSUnSimp, value2AstSUnSimp) =
        revAstOnDomainsEval (simplifyArtifact6 artifactsGradAstUnSimp)
                            parameters dt
      gradient2AstSUnSimp = parseDomains vals astGradAstSUnSimp
      artifactsSimpleAstUnSimp =
        revAstOnDomainsF (hAst unAstNoSimplify AstNoSimplify simplifyAst6)
                         parameters
      (astSimpleAstUnSimp, value3AstUnSimp) =
        revAstOnDomainsEval artifactsSimpleAstUnSimp parameters dt
      gradient3AstUnSimp = parseDomains vals astSimpleAstUnSimp
      (astSimpleAstSUnSimp, value3AstSUnSimp) =
        revAstOnDomainsEval (simplifyArtifact6 artifactsSimpleAstUnSimp)
                            parameters dt
      gradient3AstSUnSimp = parseDomains vals astSimpleAstSUnSimp
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
  in ( value0, value1, value2, value3, value2UnSimp, value3UnSimp
     , value4, value5
     , gradient1, gradient2, gradient3, gradient2UnSimp, gradient3UnSimp
     , gradient4, gradient5
     , astVectSimp, astSimp
     , value9, value2Ast, value2AstS, value3Ast, value3AstS
     , value2AstUnSimp, value2AstSUnSimp, value3AstUnSimp, value3AstSUnSimp
     , value4Ast, value4AstS, value5Ast, value5AstS
     , gradient9, gradient2Ast, gradient2AstS, gradient3Ast, gradient3AstS
     , gradient2AstUnSimp, gradient2AstSUnSimp
     , gradient3AstUnSimp, gradient3AstSUnSimp
     , gradient4Ast, gradient4AstS, gradient5Ast, gradient5AstS )

assertEqualUpToEpsilon'
    :: ( v ~ Flip OR.Array r m, g ~ Flip OR.Array r n
       , AssertEqualUpToEpsilon g, AssertEqualUpToEpsilon v
       , KnownNat m, GoodScalar r, HasCallStack)
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> OR.Array n r  -- ^ expected value
    -> ( v, v, v, v, v, v, v, v, g, g, g, g, g, g, g, Ast m r, Ast m r
       , v, v, v, v, v, v, v, v, v, v, v, v, v
       , g, g, g, g, g, g, g, g, g, g, g, g, g )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon'
    errMargin expected'
    ( value0, value1, value2, value3, value2UnSimp, value3UnSimp
    , value4, value5
    , gradient1, gradient2, gradient3, gradient2UnSimp, gradient3UnSimp
    , gradient4, gradient5
    , astVectSimp, astSimp
    , value9, value2Ast, value2AstS, value3Ast, value3AstS
    , value2AstUnSimp, value2AstSUnSimp, value3AstUnSimp, value3AstSUnSimp
    , value4Ast, value4AstS, value5Ast, value5AstS
    , gradient9, gradient2Ast, gradient2AstS, gradient3Ast, gradient3AstS
    , gradient2AstUnSimp, gradient2AstSUnSimp
    , gradient3AstUnSimp, gradient3AstSUnSimp
    , gradient4Ast, gradient4AstS, gradient5Ast, gradient5AstS ) = do
  let expected = Flip expected'
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val V UnS" errMargin value0 value2UnSimp
  assertEqualUpToEpsilonWithMark "Val V+S UnS" errMargin value0 value3UnSimp
  assertEqualUpToEpsilonWithMark "Val NotVect" errMargin value0 value4
  assertEqualUpToEpsilonWithMark "Val Simplified" errMargin value0 value5
  assertEqualUpToEpsilonWithMark "Grad ADVal" errMargin expected gradient1
  assertEqualUpToEpsilonWithMark "Grad Vectorized" errMargin expected gradient2
  assertEqualUpToEpsilonWithMark "Grad Vect+Simp" errMargin expected gradient3
  assertEqualUpToEpsilonWithMark "Grad V UnS" errMargin expected gradient2UnSimp
  assertEqualUpToEpsilonWithMark "Grad V+S UnS" errMargin expected
                                                gradient3UnSimp
  assertEqualUpToEpsilonWithMark "Grad NotVect" errMargin expected gradient4
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  assertEqualUpToEpsilonWithMark "Val Ast Vectorized" errMargin value0 value2Ast
  assertEqualUpToEpsilonWithMark "Val Ast V S" errMargin value0 value2AstS
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
  -- No Eq instance, so let's compare the text.
  show (simplifyAst6 astVectSimp) @?= show astVectSimp
  show (simplifyAst6 astSimp) @?= show astSimp

assertEqualUpToEpsilonShort
    :: ( v ~ Flip OR.Array r m, g ~ Flip OR.Array r n
       , AssertEqualUpToEpsilon g, AssertEqualUpToEpsilon v
       , KnownNat m, GoodScalar r, HasCallStack)
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> OR.Array n r  -- ^ expected value
    -> ( v, v, v, v, v, v, v, v, g, g, g, g, g, g, g, Ast m r, Ast m r
       , v, v, v, v, v, v, v, v, v, v, v, v, v
       , g, g, g, g, g, g, g, g, g, g, g, g, g )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilonShort
    errMargin expected'
    ( value0, value1, value2, value3, value2UnSimp, value3UnSimp
    , _value4, value5
    , gradient1, gradient2, gradient3, gradient2UnSimp, gradient3UnSimp
    , _gradient4, gradient5
    , astVectSimp, astSimp
    , _value9, value2Ast, value2AstS, value3Ast, value3AstS
    , value2AstUnSimp, value2AstSUnSimp, value3AstUnSimp, value3AstSUnSimp
    , _value4Ast, _value4AstS, _value5Ast, _value5AstS
    , _gradient9, gradient2Ast, gradient2AstS, gradient3Ast, gradient3AstS
    , gradient2AstUnSimp, gradient2AstSUnSimp
    , gradient3AstUnSimp, gradient3AstSUnSimp
    , _gradient4Ast, _gradient4AstS, _gradient5Ast, _gradient5AstS ) = do
  let expected = Flip expected'
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val V UnS" errMargin value0 value2UnSimp
  assertEqualUpToEpsilonWithMark "Val V+S UnS" errMargin value0 value3UnSimp
  assertEqualUpToEpsilonWithMark "Val Simplified" errMargin value0 value5
  assertEqualUpToEpsilonWithMark "Grad ADVal" errMargin expected gradient1
  assertEqualUpToEpsilonWithMark "Grad Vectorized" errMargin expected gradient2
  assertEqualUpToEpsilonWithMark "Grad Vect+Simp" errMargin expected gradient3
  assertEqualUpToEpsilonWithMark "Grad V UnS" errMargin expected gradient2UnSimp
  assertEqualUpToEpsilonWithMark "Grad V+S UnS" errMargin expected
                                                gradient3UnSimp
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  assertEqualUpToEpsilonWithMark "Val Ast Vectorized" errMargin value0 value2Ast
  assertEqualUpToEpsilonWithMark "Val Ast V S" errMargin value0 value2AstS
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
