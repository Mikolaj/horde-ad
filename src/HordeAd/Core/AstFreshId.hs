-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This module encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of the impurity escapes
-- and is encapsulated elsewhere.
module HordeAd.Core.AstFreshId
  ( funToAstIO, funToAst
  , funToAstIntIO, funToAstInt
  , funToAstIntMaybeIO, funToAstIntMaybe
  , funToAstAutoBoundsIO, funToAstNoBoundsIO
  , funToAstRevIO, funToAstFwdIO
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

funToAstIO :: KnownSpan s
           => FullShapeTK y -> (AstTensor ms s y -> AstTensor ms s2 z)
           -> IO (AstVarName '(s, y), AstTensor ms s2 z)
{-# INLINE funToAstIO  #-}
funToAstIO ftk f = do
  !freshId <- unsafeGetFreshAstVarId
  let !var = mkAstVarName ftk freshId
      x = f $ astVar var
  return (var, x)

funToAst :: KnownSpan s
         => FullShapeTK y -> (AstTensor ms s y -> AstTensor ms s2 z)
         -> (AstVarName '(s, y), AstTensor ms s2 z)
{-# NOINLINE funToAst #-}
funToAst ftk = unsafePerformIO . funToAstIO ftk

funToAstIntIO :: (Int, Int) -> (AstInt ms -> AstTensor ms s2 z)
              -> IO (IntVarName, AstTensor ms s2 z)
{-# INLINE funToAstIntIO #-}
funToAstIntIO bds f = do
  !freshId <- unsafeGetFreshAstVarId
  let !var = mkAstVarNameBounds bds freshId
      x = f $ astVar var
  return (var, x)

funToAstInt :: (Int, Int) -> (AstInt ms -> AstTensor ms s2 z)
            -> (IntVarName, AstTensor ms s2 z)
{-# NOINLINE funToAstInt #-}
funToAstInt bds = unsafePerformIO . funToAstIntIO bds

funToAstIntMaybeIO :: Maybe (Int, Int) -> ((IntVarName, AstInt ms) -> a)
                   -> IO a
{-# INLINE funToAstIntMaybeIO #-}
funToAstIntMaybeIO mbounds f = do
  !freshId <- unsafeGetFreshAstVarId
  let !var = case mbounds of
        Nothing -> mkAstVarName FTKScalar freshId
        Just bds -> mkAstVarNameBounds bds freshId
      x = astVar var
  return $! f (var, x)

funToAstIntMaybe :: Maybe (Int, Int) -> ((IntVarName, AstInt ms) -> a) -> a
{-# NOINLINE funToAstIntMaybe #-}
funToAstIntMaybe mbounds = unsafePerformIO . funToAstIntMaybeIO mbounds

funToAstAutoBoundsIO :: forall r s ms. KnownSpan s
                     => FullShapeTK (TKScalar r) -> AstTensor ms s (TKScalar r)
                     -> IO (AstVarName '(s, TKScalar r))
{-# INLINE funToAstAutoBoundsIO #-}
funToAstAutoBoundsIO ftk@FTKScalar a = do
  !freshId <- unsafeGetFreshAstVarId
  case knownSpan @s of
    SPlainSpan | Just Refl <- testEquality (typeRep @r) (typeRep @Int)
               , Just bds <- intBounds a ->
      pure $! mkAstVarNameBounds bds freshId
    _ -> pure $! mkAstVarName ftk freshId

funToAstNoBoundsIO :: KnownSpan s
                   => FullShapeTK y -> IO (AstVarName '(s, y))
{-# INLINE funToAstNoBoundsIO #-}
funToAstNoBoundsIO ftk = do
  !freshId <- unsafeGetFreshAstVarId
  pure $! mkAstVarName ftk freshId

funToAstRevIO :: forall x.
                 FullShapeTK x
              -> IO ( AstTensor AstMethodShare FullSpan x
                    , AstVarName '(FullSpan, x)
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstRevIO #-}
funToAstRevIO ftk = do
  !freshId <- unsafeGetFreshAstVarId
  let var :: AstVarName '(FullSpan, x)
      var = mkAstVarName ftk freshId
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
      varPrimalD = mkAstVarName (adFTK ftk) freshIdD
      var :: AstVarName '(FullSpan, x)
      var = mkAstVarName ftk freshId
      astVarPrimalD :: AstTensor AstMethodShare FullSpan (ADTensorKind x)
      !astVarPrimalD = astVar varPrimalD
      astVarPrimal :: AstTensor AstMethodShare FullSpan x
      !astVarPrimal = astVar var
      astVarD :: AstTensor AstMethodLet FullSpan x
      !astVarD = astVar var
  return (varPrimalD, astVarPrimalD, astVarPrimal, var, astVarD)

funToVarsIxIOS
  :: ShS sh -> (AstVarListS sh -> AstIxS ms sh -> AstTensor ms s2 z)
  -> IO (AstTensor ms s2 z)
{-# INLINE funToVarsIxIOS #-}
funToVarsIxIOS sh f = withKnownShS sh $ do
  let unsafeGetFreshIntVarName :: Int -> IO IntVarName
      unsafeGetFreshIntVarName n = do
        freshId <- unsafeGetFreshAstVarId
        return $! mkAstVarNameBounds (0, n - 1) freshId
  varList <- mapM unsafeGetFreshIntVarName $ shsToList sh
  let !vars = fromList varList
      ix = fmap astVar $ IxS vars
  return $! f vars ix

funToVarsIxS
  :: ShS sh -> (AstVarListS sh -> AstIxS ms sh -> AstTensor ms s2 z)
  -> AstTensor ms s2 z
{-# NOINLINE funToVarsIxS #-}
funToVarsIxS sh = unsafePerformIO . funToVarsIxIOS sh
