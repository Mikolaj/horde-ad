-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of it escapes.
{-# OPTIONS_GHC -ddump-stg-final #-}
module HordeAd.Core.AstFreshId where

import Prelude

import GHC.TypeLits (KnownNat)
import System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.Types

astIsSmall :: forall n s r. KnownNat n
           => Bool -> AstRanked s r n -> Bool
{-# NOINLINE astIsSmall #-}
astIsSmall relaxed !v = relaxed && astIsSmall relaxed v

astRegisterFun
  :: AstRanked PrimalSpan Double 0 -> [DynamicExists (AstDynamic PrimalSpan)]
  -> [DynamicExists (AstDynamic PrimalSpan)]
{-# NOINLINE astRegisterFun #-}
astRegisterFun !r _ | astIsSmall True r = undefined
astRegisterFun !r !l = unsafePerformIO $ do
  let !d = DynamicExists $ AstRToD (r{-42-} :: AstRanked PrimalSpan Double 0)
  return $! d : l
