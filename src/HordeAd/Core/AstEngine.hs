-- | Predefined basic variants of  functions for simplification
-- and pretty-printing of AST.
module HordeAd.Core.AstEngine
  ( -- * The joint inlining and simplification term transformation
    simplifyArtifact, simplifyArtifactGradient
  , simplifyInline, simplifyInlineContract
    -- * Pretty-printing terms in a few useful configurations
  , printAstVarName
  , printAstSimple, printAstPretty, printAstPrettyButNested
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty, printArtifactGradient  ) where

import Prelude

import Data.EnumMap.Strict qualified as EM
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM

import HordeAd.Core.Ast
import HordeAd.Core.AstInline
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify

-- * The joint inlining and simplification term transformation

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

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyInline
  :: forall z s. AstSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInline =
  snd . inlineAst EM.empty
  . simplifyAst . expandAst
  . snd . inlineAst EM.empty . simplifyAst
    -- no specialization possible except for the tag type s

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyInlineContract
  :: forall z s. AstSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInlineContract =
  snd . inlineAst EM.empty
  . contractAst . expandAst  -- TODO: when/if contractAst does less simplification, add simplifyAst in-between
  . snd . inlineAst EM.empty . simplifyAst
    -- no specialization possible except for the tag type s


-- * Pretty-printing terms in a few useful configurations

printAstVarName :: IntMap String -> AstVarName s y -> String
printAstVarName renames var =
  printAstVar (defaulPrintConfig False renames) var ""

printAstSimple :: AstSpan s
               => IntMap String -> AstTensor ms s y -> String
printAstSimple renames t = printAst (defaulPrintConfig False renames) 0 t ""

printAstPretty :: AstSpan s
               => IntMap String -> AstTensor ms s y -> String
printAstPretty renames t = printAst (defaulPrintConfig True renames) 0 t ""

printAstPrettyButNested :: AstSpan s
                        => IntMap String -> AstTensor ms s y -> String
printAstPrettyButNested renames t =
  printAst (defaulPrintConfig2 True False renames) 0 t ""

printArtifactSimple
  :: forall x z.
     IntMap String -> AstArtifactRev x z -> String
printArtifactSimple renames !AstArtifactRev{..} =
  let !varsPP =
        [ printAstVarName renames artVarDtRev
        , printAstVarName renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimple renames artDerivativeRev

printArtifactPretty
  :: forall x z.
     IntMap String -> AstArtifactRev x z -> String
printArtifactPretty renames !AstArtifactRev{..} =
  let varsPP =
        [ printAstVarName renames artVarDtRev
        , printAstVarName renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPretty renames artDerivativeRev

printArtifactPrimalSimple
  :: forall x z.
     IntMap String -> AstArtifactRev x z -> String
printArtifactPrimalSimple renames !AstArtifactRev{..} =
  "\\" ++ printAstVarName renames artVarDomainRev
       ++ " -> " ++ printAstSimple renames artPrimalRev

printArtifactPrimalPretty
  :: forall x z.
     IntMap String -> AstArtifactRev x z -> String
printArtifactPrimalPretty renames !AstArtifactRev{..} =
  "\\" ++ printAstVarName renames artVarDomainRev
       ++ " -> " ++ printAstPretty renames artPrimalRev

printArtifactGradient
  :: AstArtifactRev x z -> String
printArtifactGradient = printArtifactPretty IM.empty
