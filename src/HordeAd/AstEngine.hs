-- | Predefined common functions for simplification and pretty-printing of AST.
module HordeAd.AstEngine
  ( -- * The joint inlining and simplification term transformations
    simplifyArtifact, simplifyArtifactGradient, simplifyArtifactDerivative
  , simplifyInline, simplifyInlineContract
    -- * Pretty-printing terms in a few useful configurations
  , printAstVarName
  , printAstSimple, printAstPretty, printAstPrettyButNested
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty
  ) where

import Prelude

import Data.EnumMap.Strict qualified as EM
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM

import HordeAd.Core.Ast
import HordeAd.Core.AstInline
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify

-- * The joint inlining and simplification term transformation

-- | A mixture of simplification and inlining to use when the resultng
-- term is not yet supposed to be interpreted using a computational backed,
-- but rather to be stored and later composed with other terms.
simplifyInline
  :: forall z s. AstSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInline =
  simplifyAst . snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst

-- | A mixture of simplification, inlining and recognition of additional
-- backend-specific primitives, to use before a term
-- is interpreted as a value in the computational backend.
simplifyInlineContract
  :: forall z s. AstSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInlineContract =
  contractAst . simplifyInline

simplifyArtifact :: forall x z.
                    AstArtifactRev x z -> AstArtifactRev x z
simplifyArtifact art =
  let !der = simplifyInlineContract $ artDerivativeRev art in
  let !prim = simplifyInlineContract $ artPrimalRev art
  in art {artDerivativeRev = der, artPrimalRev = prim}

simplifyArtifactGradient :: forall x z.
                            AstArtifactRev x z -> AstArtifactRev x z
simplifyArtifactGradient art =
  art { artDerivativeRev =
        simplifyInlineContract $ artDerivativeRev art }

simplifyArtifactDerivative :: forall x z.
                              AstArtifactFwd x z -> AstArtifactFwd x z
simplifyArtifactDerivative art =
  art { artDerivativeFwd =
        simplifyInlineContract $ artDerivativeFwd art }


-- * Pretty-printing terms in a few useful configurations

printAstVarReName :: IntMap String -> AstVarName s y -> String
printAstVarReName renames var =
  printAstVar (defaulPrintConfig False renames) var ""

printAstSimpleRe :: AstSpan s
                 => IntMap String -> AstTensor ms s y -> String
printAstSimpleRe renames t = printAst (defaulPrintConfig False renames) 0 t ""

printAstPrettyRe :: AstSpan s
                 => IntMap String -> AstTensor ms s y -> String
printAstPrettyRe renames t = printAst (defaulPrintConfig True renames) 0 t ""

printAstVarName :: AstVarName s y -> String
printAstVarName var =
  let renames = IM.empty
  in printAstVar (defaulPrintConfig False renames) var ""

printAstSimple :: AstSpan s
               => AstTensor ms s y -> String
printAstSimple t =
  let renames = IM.empty
  in printAst (defaulPrintConfig False renames) 0 t ""

printAstPretty :: AstSpan s
               => AstTensor ms s y -> String
printAstPretty t =
  let renames = IM.empty
  in printAst (defaulPrintConfig True renames) 0 t ""

printAstPrettyButNested :: AstSpan s
                        => AstTensor ms s y -> String
printAstPrettyButNested t =
  let renames = IM.empty
  in printAst (defaulPrintConfig2 True False renames) 0 t ""

printArtifactSimple :: AstArtifactRev x z -> String
printArtifactSimple !AstArtifactRev{..} =
  let nDt = fromEnum (varNameToAstVarId artVarDtRev) - 100000000
      renames = IM.singleton nDt "dret"
      varsPP = [ printAstVarReName renames artVarDtRev
               , printAstVarReName renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimpleRe renames artDerivativeRev

printArtifactPretty :: AstArtifactRev x z -> String
printArtifactPretty !AstArtifactRev{..} =
  let nDt = fromEnum (varNameToAstVarId artVarDtRev) - 100000000
      renames = IM.singleton nDt "dret"
      varsPP = [ printAstVarReName renames artVarDtRev
               , printAstVarReName renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPrettyRe renames artDerivativeRev

printArtifactPrimalSimple :: AstArtifactRev x z -> String
printArtifactPrimalSimple !AstArtifactRev{..} =
  "\\" ++ printAstVarName artVarDomainRev
       ++ " -> " ++ printAstSimple artPrimalRev

printArtifactPrimalPretty :: AstArtifactRev x z -> String
printArtifactPrimalPretty !AstArtifactRev{..} =
  "\\" ++ printAstVarName artVarDomainRev
       ++ " -> " ++ printAstPretty artPrimalRev
