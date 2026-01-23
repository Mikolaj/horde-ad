-- | Predefined common functions for the joint inlining and simplification
-- of AST terms.
module HordeAd.Core.AstEngine
  ( simplifyArtifactRev, simplifyArtifactFwd
  , simplifyUserCode, simplifyInlineContract
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
-- A typical example is user code to be differentiated afterwards.
{-# INLINE simplifyUserCode #-}
simplifyUserCode
  :: forall z s. KnownSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyUserCode =
  simplifyAst . expandAst . inlineAstTensor
  . simplifyAst . expandAst . inlineAstTensor
  . simplifyAst
    -- no need to start with letDown, because either the user writes
    -- good lets or unsharing happens just before this simplification

-- | A mixture of simplification, inlining and recognition of additional
-- backend-specific primitives, to be used just before a term
-- is interpreted as a value in the computational backend.
{-# INLINE simplifyInlineContract #-}
simplifyInlineContract
  :: forall z s. KnownSpan s
  => AstTensor AstMethodLet s z -> AstTensor AstMethodLet s z
simplifyInlineContract =
  letDownAst . contractAst . expandAst . inlineAstTensor
  . simplifyAst . expandAst . inlineAstTensor
  . simplifyAst
    -- this usually starts with letDown from unsharing
