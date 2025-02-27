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
import Data.Int (Int64)
import Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter, writeIORefU)
import GHC.Exts (IsList (..))
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested (ShS (..))
import Data.Array.Nested.Internal.Shape (shsRank, withKnownShS)

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

unsafeGetFreshAstVarName :: FullTensorKind y -> IO (AstVarName s y)
{-# INLINE unsafeGetFreshAstVarName #-}
unsafeGetFreshAstVarName ftk =
  mkAstVarName ftk . intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

funToAstIO :: forall y z s s2 ms.
              FullTensorKind y
           -> (AstTensor ms s y -> AstTensor ms s2 z)
           -> IO (AstVarName s y, AstTensor ms s2 z)
{-# INLINE funToAstIO #-}
funToAstIO ftk f = do
  freshId <- unsafeGetFreshAstVarId
  let varName = mkAstVarName ftk freshId
      !x = f (AstVar ftk varName)
  return (varName, x)

funToAst :: FullTensorKind y
         -> (AstTensor ms s y -> AstTensor ms s2 z)
         -> (AstVarName s y, AstTensor ms s2 z)
{-# NOINLINE funToAst #-}
funToAst ftk f = unsafePerformIO $ funToAstIO ftk f

fun1ToAstIO :: FullTensorKind y -> (AstVarName s y -> AstTensor ms s y)
            -> IO (AstTensor ms s y)
{-# INLINE fun1ToAstIO #-}
fun1ToAstIO ftk f = do
  !freshId <- unsafeGetFreshAstVarName ftk
  return $! f freshId

fun1ToAst :: FullTensorKind y -> (AstVarName s y -> AstTensor ms s y)
          -> AstTensor ms s y
{-# NOINLINE fun1ToAst #-}
fun1ToAst ftk f = unsafePerformIO $ fun1ToAstIO ftk f

funToAstRevIO :: forall x. FullTensorKind x
              -> IO ( AstVarName PrimalSpan x
                    , AstTensor AstMethodShare PrimalSpan x
                    , AstVarName FullSpan x
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstRevIO #-}
funToAstRevIO ftk = do
  freshId <- unsafeGetFreshAstVarId
  let varPrimal :: AstVarName PrimalSpan x
      varPrimal = mkAstVarName ftk freshId
      var :: AstVarName FullSpan x
      var = mkAstVarName ftk freshId
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
funToAstFwdIO ftk = do
  freshIdDs <- unsafeGetFreshAstVarId
  freshId <- unsafeGetFreshAstVarId
  let varPrimalD :: AstVarName PrimalSpan (ADTensorKind x)
      varPrimalD = mkAstVarName (adFTK ftk) freshIdDs
      varPrimal :: AstVarName PrimalSpan x
      varPrimal = mkAstVarName ftk freshId
      var :: AstVarName FullSpan x
      var = mkAstVarName ftk freshId
      astVarPrimalD :: AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
      !astVarPrimalD = AstVar (adFTK ftk) varPrimalD
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
  !varName <- unsafeGetFreshAstVarName (FTKScalar @Int64)
  let !x = f (AstIntVar varName)
  return (varName, x)

funToAstI :: (AstInt ms -> t) -> (IntVarName, t)
{-# NOINLINE funToAstI #-}
funToAstI = unsafePerformIO . funToAstIOI

funToAstIntVarIO :: ((IntVarName, AstInt ms) -> a) -> IO a
{-# INLINE funToAstIntVarIO #-}
funToAstIntVarIO f = do
  !varName <- unsafeGetFreshAstVarName (FTKScalar @Int64)
  let !ast = AstIntVar varName
  return $! f (varName, ast)

funToAstIntVar :: ((IntVarName, AstInt ms) -> a) -> a
{-# NOINLINE funToAstIntVar #-}
funToAstIntVar = unsafePerformIO . funToAstIntVarIO

funToVarsIxIOS
  :: forall sh a ms.
     ShS sh -> ((AstVarListS sh, AstIxS ms sh) -> a) -> IO a
{-# INLINE funToVarsIxIOS #-}
funToVarsIxIOS sh f = do
  let p = sNatValue $ shsRank sh
  varList <- replicateM p $ unsafeGetFreshAstVarName (FTKScalar @Int64)
  let !vars = withKnownShS sh $ fromList varList
      !ix = withKnownShS sh $ fromList $ map AstIntVar varList
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
