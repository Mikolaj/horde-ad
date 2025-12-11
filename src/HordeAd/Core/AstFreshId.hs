-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This module encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of the impurity escapes
-- and is encapsulated elsewhere.
module HordeAd.Core.AstFreshId
  ( funToAstIO, funToAst, fun1ToAst
  , funToAstRevIO, funToAstFwdIO
  , funToAstIntVarIO, funToAstIntVar, funToAstI
  , funToVarsIxS, funToAstIxS
    -- * Low level counter manipulation to be used only in sequential tests
  , resetVarCounter
  ) where

import Prelude

import Control.Concurrent.Counter (Counter, add, new, set)
import GHC.Exts (IsList (..))
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
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

unsafeGetFreshAstVarName :: FullShapeTK y -> Maybe (Int, Int)
                         -> IO (AstVarName s y)
{-# INLINE unsafeGetFreshAstVarName #-}
unsafeGetFreshAstVarName ftk bounds =
  mkAstVarName ftk bounds
  . intToAstVarId <$> add unsafeAstVarCounter 1

funToAstIOGeneric :: forall y z s s2 ms.
                     FullShapeTK y -> Maybe (Int, Int)
                  -> (AstVarName s y -> AstTensor ms s2 z)
                  -> IO (AstVarName s y, AstTensor ms s2 z)
{-# INLINE funToAstIOGeneric  #-}
funToAstIOGeneric ftk bounds f = do
  !freshId <- unsafeGetFreshAstVarName ftk bounds
  let !x = f freshId
  return (freshId, x)
-- Warning: adding a bang before freshId breaks fragile tests.
-- Probably GHC then optimizes differently and less predictably
-- and so changes results between -O0 vs -O1 and possibly also
-- between different GHC versions and between local vs CI setup.

funToAstIO :: forall y z s s2 ms. AstSpan s
           => FullShapeTK y -> Maybe (Int, Int)
           -> (AstTensor ms s y -> AstTensor ms s2 z)
           -> IO (AstVarName s y, AstTensor ms s2 z)
{-# INLINE funToAstIO #-}
funToAstIO ftk bounds f = funToAstIOGeneric ftk bounds (f . astVar)

funToAst :: AstSpan s
         => FullShapeTK y -> Maybe (Int, Int)
         -> (AstTensor ms s y -> AstTensor ms s2 z)
         -> (AstVarName s y, AstTensor ms s2 z)
{-# NOINLINE funToAst #-}
funToAst ftk bounds = unsafePerformIO . funToAstIO ftk bounds

fun1ToAst :: FullShapeTK y -> (AstVarName s y -> AstTensor ms s y)
          -> AstTensor ms s y
{-# NOINLINE fun1ToAst #-}
fun1ToAst ftk f = unsafePerformIO $ do
  (_, t) <- funToAstIOGeneric ftk Nothing f
  return $! t

funToAstRevIO :: forall x.
                 FullShapeTK x
              -> IO ( AstVarName PrimalSpan x
                    , AstTensor AstMethodShare PrimalSpan x
                    , AstVarName FullSpan x
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstRevIO #-}
funToAstRevIO ftk = do
  !freshId <- unsafeGetFreshAstVarId
  let varPrimal :: AstVarName PrimalSpan x
      varPrimal = mkAstVarName ftk Nothing freshId
      var :: AstVarName FullSpan x
      var = mkAstVarName ftk Nothing freshId
      astVarPrimal :: AstTensor AstMethodShare PrimalSpan x
      !astVarPrimal = astVar varPrimal
      astVarD :: AstTensor AstMethodLet FullSpan x
      !astVarD = astVar var
  return (varPrimal, astVarPrimal, var, astVarD)

funToAstFwdIO :: forall x.
                 FullShapeTK x
              -> IO ( AstVarName PrimalSpan (ADTensorKind x)
                    , AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
                    , AstVarName PrimalSpan x
                    , AstTensor AstMethodShare PrimalSpan x
                    , AstVarName FullSpan x
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstFwdIO #-}
funToAstFwdIO ftk = do
  !freshIdDs <- unsafeGetFreshAstVarId
  !freshId <- unsafeGetFreshAstVarId
  let varPrimalD :: AstVarName PrimalSpan (ADTensorKind x)
      varPrimalD = mkAstVarName (adFTK ftk) Nothing freshIdDs
      varPrimal :: AstVarName PrimalSpan x
      varPrimal = mkAstVarName ftk Nothing freshId
      var :: AstVarName FullSpan x
      var = mkAstVarName ftk Nothing freshId
      astVarPrimalD :: AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
      !astVarPrimalD = astVar varPrimalD
      astVarPrimal :: AstTensor AstMethodShare PrimalSpan x
      !astVarPrimal = astVar varPrimal
      astVarD :: AstTensor AstMethodLet FullSpan x
      !astVarD = astVar var
  return (varPrimalD, astVarPrimalD, varPrimal, astVarPrimal, var, astVarD)

funToAstIntVarIO :: Maybe (Int, Int) -> ((IntVarName, AstInt ms) -> a)
                 -> IO a
{-# INLINE funToAstIntVarIO #-}
funToAstIntVarIO bounds f = do
  !varName <- unsafeGetFreshAstVarName (FTKScalar @Int) bounds
  return $! f (varName, astVar varName)

funToAstIntVar :: Maybe (Int, Int) -> ((IntVarName, AstInt ms) -> a) -> a
{-# NOINLINE funToAstIntVar #-}
funToAstIntVar bounds = unsafePerformIO . funToAstIntVarIO bounds

funToAstI :: Maybe (Int, Int) -> (AstInt ms -> t) -> (IntVarName, t)
{-# NOINLINE funToAstI #-}
funToAstI bounds f = unsafePerformIO . funToAstIntVarIO bounds
                     $ \ (!var, !i) -> let !x = f i in (var, x)

funToVarsIxIOS
  :: forall sh a ms.
     ShS sh -> ((AstVarListS sh, AstIxS ms sh) -> a) -> IO a
{-# INLINE funToVarsIxIOS #-}
funToVarsIxIOS sh f = withKnownShS sh $ do
  let freshBound n = unsafeGetFreshAstVarName (FTKScalar @Int) (Just (0, n - 1))
  !varList <- mapM freshBound $ shsToList sh
  let !vars = fromList varList
  let !ix = fromList $ map astVar varList
  return $! f (vars, ix)

funToVarsIxS
  :: ShS sh -> ((AstVarListS sh, AstIxS ms sh) -> a) -> a
{-# NOINLINE funToVarsIxS #-}
funToVarsIxS sh = unsafePerformIO . funToVarsIxIOS sh

funToAstIxS
  :: ShS sh -> (AstIxS ms sh -> AstIxS ms sh2)
  -> (AstVarListS sh, AstIxS ms sh2)
{-# NOINLINE funToAstIxS #-}
funToAstIxS sh f = unsafePerformIO $ funToVarsIxIOS sh
                   $ \ (!vars, !ix) -> let !x = f ix in (vars, x)
