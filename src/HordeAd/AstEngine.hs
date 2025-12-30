-- | Predefined common functions for simplification and pretty-printing of AST.
module HordeAd.AstEngine
  ( -- * The joint inlining and simplification term transformations
    simplifyArtifactRev, simplifyArtifactFwd
  , simplifyInline, simplifyInlineContract, simplifyInlineContractNoExpand
    -- * Pretty-printing terms in a few useful configurations
  , printAstVarName
  , printAstSimple, printAstPretty, printAstPrettyButNested
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty
  ) where

import Prelude

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM

import HordeAd.Core.Ast
import HordeAd.Core.AstInline
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstTraverse

-- * The joint inlining and simplification term transformation

-- | Simplify the whole reverse derivative artifact (which includes
-- also the primal value computed during the differentiation process).
{-# INLINE simplifyArtifactRev #-}
simplifyArtifactRev :: AstArtifactRev x z -> AstArtifactRev x z
simplifyArtifactRev art =
  let !der = simplifyInlineContract $ artDerivativeRev art in
  let prim = simplifyInlineContract $ artPrimalRev art
  in art {artDerivativeRev = der, artPrimalRev = prim}

-- | Simplify the whole forward derivative artifact (which includes
-- also the primal value computed during the differentiation process).
{-# INLINE simplifyArtifactFwd #-}
simplifyArtifactFwd :: AstArtifactFwd x z -> AstArtifactFwd x z
simplifyArtifactFwd art =
  let !der = simplifyInlineContract $ artDerivativeFwd art in
  let prim = simplifyInlineContract $ artPrimalFwd art
  in art {artDerivativeFwd = der, artPrimalFwd = prim}

-- | A mixture of simplification and inlining to use when the resultng
-- term is not yet supposed to be interpreted using a computational backed,
-- but rather to be stored and later composed with other terms.
{-# INLINE simplifyInline #-}
simplifyInline
  :: forall z s. AstSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInline =
  simplifyAst . expandAst . inlineAstTensor
  . simplifyAst . expandAst . inlineAstTensor
  . simplifyAst

-- | A mixture of simplification, inlining and recognition of additional
-- backend-specific primitives, to be used just before a term
-- is interpreted as a value in the computational backend.
{-# INLINE simplifyInlineContract #-}
simplifyInlineContract
  :: forall z s. AstSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInlineContract =
  contractAst . expandAst . inlineAstTensor
  . simplifyAst . expandAst . inlineAstTensor
  . simplifyAst

{-# INLINE simplifyInlineContractNoExpand #-}
simplifyInlineContractNoExpand
  :: forall z s. AstSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInlineContractNoExpand =
  contractAst . simplifyAst . inlineAstTensor
  . simplifyAst . inlineAstTensor
  . simplifyAst


-- * Pretty-printing terms in a few useful configurations

{-# INLINE printAstVarRename #-}
printAstVarRename :: AstSpan s
                  => IntMap String -> AstVarName s y -> String
printAstVarRename renames var =
  printAstVar (defaulPrintConfig {varRenames = renames}) var ""

{-# INLINE printAstSimpleRename #-}
printAstSimpleRename :: AstSpan s
                     => IntMap String -> AstTensor ms s y -> String
printAstSimpleRename renames t =
  printAst
    (defaulPrintConfig {loseRoudtrip = False, varRenames = renames}) 0 t ""

{-# INLINE printAstPrettyRename #-}
printAstPrettyRename :: AstSpan s
                     => IntMap String -> AstTensor ms s y -> String
printAstPrettyRename renames t =
  printAst (defaulPrintConfig {varRenames = renames}) 0 t ""

{-# INLINE printAstVarName #-}
printAstVarName :: AstSpan s
                => AstVarName s y -> String
printAstVarName var =
  printAstVar defaulPrintConfig var ""

-- | Print an AST term in a form close to being able to roundtrip,
-- including explicit sharing preservation.
{-# INLINE printAstSimple #-}
printAstSimple :: AstSpan s
               => AstTensor ms s y -> String
printAstSimple t =
  printAst (defaulPrintConfig {loseRoudtrip = False}) 0 t ""

-- | Print an AST term in a readable form that does not roundtrip,
-- and where Haskell @let@ (sharing on Haskell heap) is used instead
-- of explicit sharing of subterms.
{-# INLINE printAstPretty #-}
printAstPretty :: AstSpan s
               => AstTensor ms s y -> String
printAstPretty t =
  printAst defaulPrintConfig 0 t ""

{-# INLINE printAstPrettyButNested #-}
printAstPrettyButNested :: AstSpan s
                        => AstTensor ms s y -> String
printAstPrettyButNested t =
  printAst (defaulPrintConfig {ignoreNestedLambdas = False}) 0 t ""

{-# INLINE printArtifactSimple #-}
printArtifactSimple :: AstArtifactRev x z -> String
printArtifactSimple AstArtifactRev{..} =
  let nDt = fromEnum (varNameToAstVarId artVarDtRev) - 100000000
      renames = IM.singleton nDt "dret"
      varsPP = [ printAstVarRename renames artVarDtRev
               , printAstVarRename renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimpleRename renames artDerivativeRev

{-# INLINE printArtifactPretty #-}
printArtifactPretty :: AstArtifactRev x z -> String
printArtifactPretty AstArtifactRev{..} =
  let nDt = fromEnum (varNameToAstVarId artVarDtRev) - 100000000
      renames = IM.singleton nDt "dret"
      varsPP = [ printAstVarRename renames artVarDtRev
               , printAstVarRename renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPrettyRename renames artDerivativeRev

{-# INLINE printArtifactPrimalSimple #-}
printArtifactPrimalSimple :: AstArtifactRev x z -> String
printArtifactPrimalSimple AstArtifactRev{..} =
  "\\" ++ printAstVarName artVarDomainRev
       ++ " -> " ++ printAstSimple artPrimalRev

{-# INLINE printArtifactPrimalPretty #-}
printArtifactPrimalPretty :: AstArtifactRev x z -> String
printArtifactPrimalPretty AstArtifactRev{..} =
  "\\" ++ printAstVarName artVarDomainRev
       ++ " -> " ++ printAstPretty artPrimalRev
