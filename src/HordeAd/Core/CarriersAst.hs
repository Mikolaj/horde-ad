{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Definitions, mostly class instances, needed to make AST a valid
-- carrier for a tensor class algebra (instance) defined
-- in "HordeAd.Core.OpsAst".
-- This algebra permits user programs to be instantiated as AST terms,
-- as well as to be interpreted into AST terms and it also permits derivatives
-- to be expressed as AST terms.
module HordeAd.Core.CarriersAst
  ( AstRaw(..), AstNoVectorize(..), AstNoSimplify(..)
  ) where

import Prelude

import HordeAd.Core.Ast
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.Types

-- * Type family instances for AstTensor

-- This can't be just HFun, because they need to be vectorized
-- and vectorization applies such functions to the variable from build1
-- and the variable has to be eliminated via vectorization to preserve
-- the closed form of the function. Just applying a Haskell closure
-- to the build1 variable and then duplicating the result of the function
-- would not eliminate the variable and also would likely results
-- in more costly computations. Also, that would prevent simplification
-- of the instances, especially after applied to arguments that are terms.
type instance HFunOf (AstTensor AstMethodLet s) = AstHFun s

-- This can't be defined only for FullSpan, because the BaseTensor instance
-- for @AstTensor ms PrimalSpan@ needs it and we need the instance
-- to satisfy ADReady constraints for AST.
type instance PrimalOf (AstTensor ms s) = AstTensor ms (PrimalStepSpan s)
type instance DualOf (AstTensor ms s) = AstTensor ms DualSpan
type instance PlainOf (AstTensor ms s) = AstTensor ms PlainSpan
type instance ShareOf (AstTensor ms s) = AstRaw s

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstTensor ms s y) where
  (==) = error "Eq is not defined for AST; please use EqH instead"
  (/=) = error "Eq is not defined for AST; please use EqH instead"

instance Ord (AstTensor ms s y) where
  (<=) = error "Ord is not defined for AST; please use OrdH instead"


-- * AstRaw, AstNoVectorize and AstNoSimplify definitions

-- | An AST variant that doesn't vectorize terms and also builds them
-- with ordinary, non-simplifying constructors. It's based on sharing
-- rather than lets and commonly used as the instance for primals
-- inside ADVal and, consequently, used for evaluating delta expressions.
type role AstRaw nominal nominal
newtype AstRaw s y =
  AstRaw {unAstRaw :: AstTensor AstMethodShare s y}
 deriving Show

-- | An AST variant for testing that doesn't vectorize terms, but still
-- builds them using simplifying smart constructors.
type role AstNoVectorize nominal nominal
newtype AstNoVectorize s y =
  AstNoVectorize {unAstNoVectorize :: AstTensor AstMethodLet s y}
 deriving Show

-- | An AST variant for testing that vectorizes terms, but builds them
-- with ordinary, non-simplifying constructors.
type role AstNoSimplify nominal nominal
newtype AstNoSimplify s y =
  AstNoSimplify {unAstNoSimplify :: AstTensor AstMethodLet s y}
 deriving Show


-- * AstRaw, AstNoVectorize and AstNoSimplify type family instances

type instance PrimalOf (AstRaw s) = AstRaw (PrimalStepSpan s)
type instance DualOf (AstRaw s) = AstTensor AstMethodShare DualSpan
type instance PlainOf (AstRaw s) = AstRaw PlainSpan
type instance ShareOf (AstRaw s) = AstRaw s
type instance HFunOf (AstRaw s) = AstHFun s

type instance PrimalOf (AstNoVectorize s) = AstNoVectorize (PrimalStepSpan s)
type instance DualOf (AstNoVectorize s) = AstTensor AstMethodLet DualSpan
type instance PlainOf (AstNoVectorize s) = AstNoVectorize PlainSpan
type instance ShareOf (AstNoVectorize s) = AstRaw s
type instance HFunOf (AstNoVectorize s) = AstHFun s

type instance PrimalOf (AstNoSimplify s) = AstNoSimplify (PrimalStepSpan s)
type instance DualOf (AstNoSimplify s) = AstTensor AstMethodLet DualSpan
type instance PlainOf (AstNoSimplify s) = AstNoSimplify PlainSpan
type instance ShareOf (AstNoSimplify s) = AstRaw s
type instance HFunOf (AstNoSimplify s) = AstHFun s
