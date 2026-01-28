-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This module encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of the impurity escapes
-- and is encapsulated elsewhere.
module HordeAd.Core.AstFreshId
  ( funToAstIO, funToAst, funToAstAutoBoundsIO, funToAstNoBoundsIO
  , funToAstRevIO, funToAstFwdIO
  , funToAstIntVarMaybeIO, funToAstIntVar, funToAstIntVarIO, funToAstI
  , funToVarsIxS
    -- * Low level counter manipulation to be used only in sequential tests
  , resetVarCounter
  ) where

import Prelude

import Control.Concurrent.Counter (Counter, add, new, set)
import Data.Type.Equality (testEquality, (:~:) (Refl))
import GHC.Exts (IsList (..))
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)

import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstTools
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- | A counter that is impure but only in the most trivial way
-- (only ever incremented by one).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (new 100000001)

-- | Only for tests, e.g., to ensure `show` applied to terms has stable length.
-- Tests that use this tool need to be run sequentially
-- to avoid variable confusion.
resetVarCounter :: IO ()
resetVarCounter = set unsafeAstVarCounter 100000001

unsafeGetFreshAstVarId :: IO AstVarId
{-# INLINE unsafeGetFreshAstVarId #-}
unsafeGetFreshAstVarId =
  intToAstVarId <$> add unsafeAstVarCounter 1

funVarToAstIO :: forall y z s s2 ms. KnownSpan s
              => FullShapeTK y -> Maybe (Int, Int)
              -> (AstVarName '(s, y) -> AstTensor ms s2 z)
              -> IO (AstVarName '(s, y), AstTensor ms s2 z)
{-# INLINE funVarToAstIO  #-}
funVarToAstIO ftk mbounds f = do
  !freshId <- unsafeGetFreshAstVarId
  let !var = mkAstVarName ftk mbounds freshId
      !x = f var
  return (var, x)

funToAstIO :: forall y z s s2 ms. KnownSpan s
           => FullShapeTK y -> Maybe (Int, Int)
           -> (AstTensor ms s y -> AstTensor ms s2 z)
           -> IO (AstVarName '(s, y), AstTensor ms s2 z)
{-# INLINE funToAstIO #-}
funToAstIO ftk mbounds f = funVarToAstIO ftk mbounds (f . astVar)

funToAst :: KnownSpan s
         => FullShapeTK y
         -> (AstTensor ms s y -> AstTensor ms s2 z)
         -> (AstVarName '(s, y), AstTensor ms s2 z)
{-# NOINLINE funToAst #-}
funToAst ftk = unsafePerformIO . funToAstIO ftk Nothing

funToAstAutoBoundsIO :: forall r s ms. KnownSpan s
                     => FullShapeTK (TKScalar r) -> AstTensor ms s (TKScalar r)
                     -> IO (AstVarName '(s, TKScalar r))
{-# INLINE funToAstAutoBoundsIO #-}
funToAstAutoBoundsIO ftk@FTKScalar a = do
  !freshId <- unsafeGetFreshAstVarId
  case knownSpan @s of
    SPlainSpan | Just Refl <- testEquality (typeRep @r) (typeRep @Int)
               , Just (lb, ub) <- intBounds a ->
      pure $! AstVarName freshId $ FtkAndBoundsBounds lb ub
    _ -> pure $! mkAstVarName ftk Nothing freshId

funToAstNoBoundsIO :: KnownSpan s
                   => FullShapeTK y -> IO (AstVarName '(s, y))
{-# INLINE funToAstNoBoundsIO #-}
funToAstNoBoundsIO ftk = do
  !freshId <- unsafeGetFreshAstVarId
  pure $! mkAstVarName ftk Nothing freshId

funToAstRevIO :: forall x.
                 FullShapeTK x
              -> IO ( AstTensor AstMethodShare FullSpan x
                    , AstVarName '(FullSpan, x)
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstRevIO #-}
funToAstRevIO ftk = do
  !freshId <- unsafeGetFreshAstVarId
  let var :: AstVarName '(FullSpan, x)
      var = AstVarName freshId $ FtkAndBoundsFull ftk
      astVarPrimal :: AstTensor AstMethodShare FullSpan x
      !astVarPrimal = astVar var
      astVarD :: AstTensor AstMethodLet FullSpan x
      !astVarD = astVar var
  return (astVarPrimal, var, astVarD)

funToAstFwdIO :: forall x.
                 FullShapeTK x
              -> IO ( AstVarName '(FullSpan, ADTensorKind x)
                    , AstTensor AstMethodShare FullSpan (ADTensorKind x)
                    , AstTensor AstMethodShare FullSpan x
                    , AstVarName '(FullSpan, x)
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstFwdIO #-}
funToAstFwdIO ftk = do
  !freshIdD <- unsafeGetFreshAstVarId
  !freshId <- unsafeGetFreshAstVarId
  let varPrimalD :: AstVarName '(FullSpan, ADTensorKind x)
      varPrimalD = AstVarName freshIdD $ FtkAndBoundsFull (adFTK ftk)
      var :: AstVarName '(FullSpan, x)
      var = AstVarName freshId $ FtkAndBoundsFull ftk
      astVarPrimalD :: AstTensor AstMethodShare FullSpan (ADTensorKind x)
      !astVarPrimalD = astVar varPrimalD
      astVarPrimal :: AstTensor AstMethodShare FullSpan x
      !astVarPrimal = astVar var
      astVarD :: AstTensor AstMethodLet FullSpan x
      !astVarD = astVar var
  return (varPrimalD, astVarPrimalD, astVarPrimal, var, astVarD)

funToAstIntVarMaybeIO :: Maybe (Int, Int) -> ((IntVarName, AstInt ms) -> a)
                      -> IO a
{-# INLINE funToAstIntVarMaybeIO #-}
funToAstIntVarMaybeIO mbounds f = do
  !freshId <- unsafeGetFreshAstVarId
  let !var = case mbounds of
        Nothing -> AstVarName freshId $ FtkAndBoundsPlain FTKScalar
        Just (lb, ub) -> AstVarName freshId $ FtkAndBoundsBounds lb ub
  return $! f (var, astVar var)

funToAstIntVar :: Maybe (Int, Int) -> ((IntVarName, AstInt ms) -> a) -> a
{-# NOINLINE funToAstIntVar #-}
funToAstIntVar mbounds = unsafePerformIO . funToAstIntVarMaybeIO mbounds

funToAstIntVarIO :: (Int, Int) -> ((IntVarName, AstInt ms) -> a)-> IO a
{-# INLINE funToAstIntVarIO #-}
funToAstIntVarIO (lb, ub) f = do
  !freshId <- unsafeGetFreshAstVarId
  let !var = AstVarName freshId $ FtkAndBoundsBounds lb ub
  return $! f (var, astVar var)

funToAstI :: (Int, Int) -> (AstInt ms -> t) -> (IntVarName, t)
{-# NOINLINE funToAstI #-}
funToAstI bds f = unsafePerformIO . funToAstIntVarIO bds
                  $ \ (!var, !i) -> let !x = f i in (var, x)

funToVarsIxIOS
  :: forall sh a ms.
     ShS sh -> (AstVarListS sh -> AstIxS ms sh -> a) -> IO a
{-# INLINE funToVarsIxIOS #-}
funToVarsIxIOS sh f = withKnownShS sh $ do
  let unsafeGetFreshIntVarName :: Int -> IO IntVarName
      unsafeGetFreshIntVarName n = do
        freshId <- unsafeGetFreshAstVarId
        return $! AstVarName freshId $ FtkAndBoundsBounds 0 (n - 1)
  varList <- mapM unsafeGetFreshIntVarName $ shsToList sh
  let !vars = fromList varList
  let !ix = fmap astVar $ IxS vars
  return $! f vars ix

funToVarsIxS
  :: ShS sh -> (AstVarListS sh -> AstIxS ms sh -> a) -> a
{-# NOINLINE funToVarsIxS #-}
funToVarsIxS sh = unsafePerformIO . funToVarsIxIOS sh
