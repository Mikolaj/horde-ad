-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of it escapes.
{-# OPTIONS_GHC -ddump-stg-final #-}
module HordeAd.Core.AstFreshId where

import Prelude

import HordeAd.Core.Ast
import HordeAd.Core.Types

astIsSmall :: Bool -> AstRanked PrimalSpan Double 0 -> Bool
astIsSmall relaxed !r = relaxed && astIsSmall relaxed r

astRegisterFun
  :: AstRanked PrimalSpan Double 0 -> [Int]
  -> DynamicExists (AstDynamic PrimalSpan)
astRegisterFun !r !_ | astIsSmall True r = undefined
astRegisterFun !r !_ =
  DynamicExists $ AstRToD (r :: AstRanked PrimalSpan Double 0)
