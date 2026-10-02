-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This module encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of the impurity escapes
-- and is encapsulated elsewhere.
--
-- Every fresh identifier, here and in "HordeAd.Core.DeltaFreshId", is drawn
-- under @unsafePerformIO@ and never under @unsafeDupablePerformIO@, and
-- @tools/check-fresh-draws.py@, one of the checks @check-all tools@ runs,
-- keeps it so: it permits the latter only in the definitions it lists,
-- which draw nothing and compute the same result however often they run
-- (@astIsSmall@ and @mkTraceRule@).
--
-- The reason is what a duplicated evaluation does. GHC claims a thunk under
-- evaluation only when the evaluating thread next pauses, so two threads on
-- different capabilities can both evaluate one thunk. @unsafePerformIO@ first
-- runs @noDuplicate#@, which claims every thunk then under evaluation on the
-- thread's stack, the enclosing ones as well as the innermost, so a second
-- thread blocks and receives the first one's value: any value whose evaluation
-- draws an identifier has one value, whoever forces it and however. Under
-- @unsafeDupablePerformIO@ both copies run, the atomic counter gives each its
-- own identifiers, and the thunk ends up updated with either copy's result,
-- so a result read in two parts can mix the copies: a binder from one with
-- a body from the other, which binds a different variable. @tlambda@ in
-- "HordeAd.Core.OpsAst" stores the two halves of a @funToAst@ pair in the
-- lazy fields of @AstLambda@, and @interpretAstHFun@ reads the binder and the
-- body at different times, so a lambda that two threads force would come out
-- binding one variable and using another. The library itself never evaluates
-- one term from two threads; user code that interprets one artifact from
-- several would, whenever the objective holds a fold, a scan, a mapAccum or a
-- nested derivative.
--
-- A standalone mirror of @tlambda@, two threads on separate capabilities
-- forcing a freshly built lazy pair 2,000,000 times at @-N3@, one reading
-- the binder first and the other the body, tore 17520, 30213 and 35038
-- lambdas under @unsafeDupablePerformIO@ and none under @unsafePerformIO@
-- (2026-10-02). With the impure call behind a pure wrapper, as the body of
-- @tgrad@'s lambda reaches its artifact, it tore 1177106 and 164623 times in
-- 1,000,000 under the former, counted per thread, and never under the latter,
-- which is the claim about enclosing thunks above. A duplicated evaluation
-- does not always survive: work allocating some 10^5 list cells or more always
-- lost one copy at the next pause, while short work, a draw among it, finished
-- twice.
--
-- What this costs is @noDuplicate#@. With one capability it returns at
-- once, a few nanoseconds per draw, which is the state of the criterion
-- benchmarks, whose RTS options set no @-N@. With more it walks the stack
-- down to the first frame already claimed, some 20 nanoseconds on a
-- shallow stack and far more in deep non-tail recursion: tasty raises the
-- capability count to the number of processors even for the sequential
-- suites, and GHC https://gitlab.haskell.org/ghc/ghc/-/work_items/27885
-- makes the backward-pass loop @evalRevFromnMap@ non-tail recursive under
-- @-flate-dmd-anal@. Interpreting an artifact into @Concrete@ draws nothing,
-- so only building, simplifying and differentiating terms pay, and the
-- non-symbolic pipeline pays once per operation, in @shareDelta@.
--
-- Do not move the draws to @unsafeDupablePerformIO@ again. That was done
-- on 2026-10-01 and measured, by the mutator time of the CAFlessTest suite
-- under tasty, at 1.9% faster by default (two runs each) and 12.0% faster
-- with @-flate-dmd-anal@ (four runs each), most of it the stack walks of that
-- issue's deep stack; it made the lambdas above tearable and was reverted
-- on 2026-10-02. A narrower variant, dupable only where an identifier
-- merely names an existing term for sharing (@shareDelta@'s node ids and
-- @astShareNoSimplify@'s variables), where any mix of copies only loses
-- sharing, was considered and not adopted: its safety rests on the backward
-- pass being linear and on one variable never naming two terms, which later
-- code can break with nothing to notice. If the walks cost too much again,
-- remove the deep stack, as the fix proposed in that issue does, or keep the
-- sequential suites on one capability with tasty's @NumThreads 1@.
--
-- The counters are top-level constants created with @unsafePerformIO@, since
-- two copies of one would hand out duplicate identifiers.
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
  let !ix = fromList varList
      vars = AstVarListS ix
      asts = fmap astVar ix
  return $! f vars asts

funToVarsIxS
  :: ShS sh -> (AstVarListS sh -> AstIxS ms sh -> AstTensor ms s2 z)
  -> AstTensor ms s2 z
{-# NOINLINE funToVarsIxS #-}
funToVarsIxS sh = unsafePerformIO . funToVarsIxIOS sh
