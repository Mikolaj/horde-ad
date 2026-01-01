-- | Predefined common functions for the joint inlining and simplification
-- of AST terms.
module HordeAd.Core.AstEngine
  ( simplifyArtifactRev, simplifyArtifactFwd
  , simplifyInline, simplifyInlineContract, simplifyInlineContractNoExpand
  ) where

import Prelude

import HordeAd.Core.Ast
import HordeAd.Core.AstInline
import HordeAd.Core.AstTraverse

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
