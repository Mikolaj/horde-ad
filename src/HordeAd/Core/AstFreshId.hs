-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of it escapes.
{-# OPTIONS_GHC -ddump-stg-final #-}
module HordeAd.Core.AstFreshId where

import Prelude

import Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import GHC.TypeLits (KnownNat)
import System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.AstTools
import HordeAd.Core.Types

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 100000001)

unsafeGetFreshAstId :: IO AstId
{-# INLINE unsafeGetFreshAstId #-}
unsafeGetFreshAstId =
  intToAstId <$> atomicAddCounter_ unsafeAstVarCounter 1

astRegisterFun
  :: (GoodScalar r, KnownNat n)
  => AstRanked s r n -> AstBindings (AstRanked s)
  -> (AstBindings (AstRanked s), AstRanked s r n)
{-# NOINLINE astRegisterFun #-}
astRegisterFun !r !l | astIsSmall True r = (l, r)
astRegisterFun !r !l = unsafePerformIO $ do
  !freshId <- unsafeGetFreshAstId
  let !r2 = AstVar (shapeAst r) $ AstVarName $ astIdToAstVarId freshId
      !d = DynamicExists $ AstRToD r
  return ((freshId, d) : l, r2)
