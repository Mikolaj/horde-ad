-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of the impurity escapes.
module HordeAd.Core.AstFreshId
  ( funToAstIO, funToAst, fun1ToAst
  , funToAstRevIO, funToAstRev
  , funToAstFwdIO, funToAstFwd
  , funToAstIOI, funToAstI, funToAstIntVarIO, funToAstIntVar
  , funToVarsIxS, funToAstIxS
  , resetVarCounter
  ) where

import Prelude

import Control.Monad (replicateM)
import Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter, writeIORefU)
import GHC.Exts (IsList (..))
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested (KnownShS (..))
import Data.Array.Nested.Internal.Shape (shsRank)

import HordeAd.Core.Ast
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 100000001)

-- | Only for tests, e.g., to ensure show applied to terms has stable length.
-- Tests using this need to be run with -ftest_seq to avoid variable confusion.
resetVarCounter :: IO ()
resetVarCounter = writeIORefU unsafeAstVarCounter 100000001

unsafeGetFreshAstVarId :: IO AstVarId
{-# INLINE unsafeGetFreshAstVarId #-}
unsafeGetFreshAstVarId =
  intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

unsafeGetFreshAstVarName :: KnownSTK y => IO (AstVarName s y)
{-# INLINE unsafeGetFreshAstVarName #-}
unsafeGetFreshAstVarName =
  mkAstVarName . intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

funToAstIO :: forall y z s s2 ms.
              FullTensorKind y
           -> (AstTensor ms s y -> AstTensor ms s2 z)
           -> IO (AstVarName s y, AstTensor ms s2 z)
{-# INLINE funToAstIO #-}
funToAstIO ftk f | Dict <- lemKnownSTK (ftkToStk ftk) = do
  freshId <- unsafeGetFreshAstVarId
  let varName = mkAstVarName freshId
      !x = f (AstVar ftk varName)
  return (varName, x)

funToAst :: FullTensorKind y
         -> (AstTensor ms s y -> AstTensor ms s2 z)
         -> (AstVarName s y, AstTensor ms s2 z)
{-# NOINLINE funToAst #-}
funToAst ftk f = unsafePerformIO $ funToAstIO ftk f

fun1ToAstIO :: KnownSTK y
            => (AstVarName s y -> AstTensor ms s y)
            -> IO (AstTensor ms s y)
{-# INLINE fun1ToAstIO #-}
fun1ToAstIO f = do
  !freshId <- unsafeGetFreshAstVarName
  return $! f freshId

fun1ToAst :: KnownSTK y
          => (AstVarName s y -> AstTensor ms s y)
          -> AstTensor ms s y
{-# NOINLINE fun1ToAst #-}
fun1ToAst f = unsafePerformIO $ fun1ToAstIO f

funToAstRevIO :: forall x. FullTensorKind x
              -> IO ( AstVarName PrimalSpan x
                    , AstTensor AstMethodShare PrimalSpan x
                    , AstVarName FullSpan x
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstRevIO #-}
funToAstRevIO ftk | Dict <- lemKnownSTK (ftkToStk ftk) = do
  freshId <- unsafeGetFreshAstVarId
  let varPrimal :: AstVarName PrimalSpan x
      varPrimal = mkAstVarName freshId
      var :: AstVarName FullSpan x
      var = mkAstVarName freshId
      astVarPrimal :: AstTensor AstMethodShare PrimalSpan x
      !astVarPrimal = AstVar ftk varPrimal
      astVar :: AstTensor AstMethodLet FullSpan x
      !astVar = AstVar ftk var
  return (varPrimal, astVarPrimal, var, astVar)

funToAstRev :: FullTensorKind x
            -> ( AstVarName PrimalSpan x
               , AstTensor AstMethodShare PrimalSpan x
               , AstVarName FullSpan x
               , AstTensor AstMethodLet FullSpan x )
{-# NOINLINE funToAstRev #-}
funToAstRev = unsafePerformIO . funToAstRevIO

funToAstFwdIO :: forall x. FullTensorKind x
              -> IO ( AstVarName PrimalSpan (ADTensorKind x)
                    , AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
                    , AstVarName PrimalSpan x
                    , AstTensor AstMethodShare PrimalSpan x
                    , AstVarName FullSpan x
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstFwdIO #-}
funToAstFwdIO ftk | Dict <- lemKnownSTK (ftkToStk ftk)
                  , Dict <- lemKnownSTKOfAD (ftkToStk ftk) = do
  freshIdDs <- unsafeGetFreshAstVarId
  freshId <- unsafeGetFreshAstVarId
  let varPrimalD :: AstVarName PrimalSpan (ADTensorKind x)
      varPrimalD = mkAstVarName freshIdDs
      varPrimal :: AstVarName PrimalSpan x
      varPrimal = mkAstVarName freshId
      var :: AstVarName FullSpan x
      var = mkAstVarName freshId
      astVarPrimalD :: AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
      !astVarPrimalD = AstVar (aDFTK ftk) varPrimalD
      astVarPrimal :: AstTensor AstMethodShare PrimalSpan x
      !astVarPrimal = AstVar ftk varPrimal
      astVar :: AstTensor AstMethodLet FullSpan x
      !astVar = AstVar ftk var
  return (varPrimalD, astVarPrimalD, varPrimal, astVarPrimal, var, astVar)

funToAstFwd :: FullTensorKind x
            -> ( AstVarName PrimalSpan (ADTensorKind x)
               , AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
               , AstVarName PrimalSpan x
               , AstTensor AstMethodShare PrimalSpan x
               , AstVarName FullSpan x
               , AstTensor AstMethodLet FullSpan x )
{-# NOINLINE funToAstFwd #-}
funToAstFwd = unsafePerformIO . funToAstFwdIO

funToAstIOI :: (AstInt ms -> t) -> IO (IntVarName, t)
{-# INLINE funToAstIOI #-}
funToAstIOI f = do
  !varName <- unsafeGetFreshAstVarName
  let !x = f (AstIntVar varName)
  return (varName, x)

funToAstI :: (AstInt ms -> t) -> (IntVarName, t)
{-# NOINLINE funToAstI #-}
funToAstI = unsafePerformIO . funToAstIOI

funToAstIntVarIO :: ((IntVarName, AstInt ms) -> a) -> IO a
{-# INLINE funToAstIntVarIO #-}
funToAstIntVarIO f = do
  !varName <- unsafeGetFreshAstVarName
  let !ast = AstIntVar varName
  return $! f (varName, ast)

funToAstIntVar :: ((IntVarName, AstInt ms) -> a) -> a
{-# NOINLINE funToAstIntVar #-}
funToAstIntVar = unsafePerformIO . funToAstIntVarIO

funToVarsIxIOS
  :: forall sh a ms. KnownShS sh
  => ((AstVarListS sh, AstIxS ms sh) -> a) -> IO a
{-# INLINE funToVarsIxIOS #-}
funToVarsIxIOS f = do
  let p = sNatValue $ shsRank $ knownShS @sh
  varList <- replicateM p unsafeGetFreshAstVarName
  let !vars = fromList varList
      !ix = fromList $ map AstIntVar varList
  return $! f (vars, ix)

funToVarsIxS
  :: KnownShS sh
  => ((AstVarListS sh, AstIxS ms sh) -> a) -> a
{-# NOINLINE funToVarsIxS #-}
funToVarsIxS = unsafePerformIO . funToVarsIxIOS

funToAstIxS
  :: KnownShS sh
  => (AstIxS ms sh -> AstIxS ms sh2) -> (AstVarListS sh, AstIxS ms sh2)
{-# NOINLINE funToAstIxS #-}
funToAstIxS f = unsafePerformIO $ funToVarsIxIOS
                   $ \ (!vars, !ix) -> let !x = f ix in (vars, x)
