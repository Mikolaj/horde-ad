{-# LANGUAGE DataKinds, GADTs #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Vectorization of the build operation in Ast.
module HordeAd.Core.AstVectorize
  ( build1Vectorize
    -- * Rule tracing machinery
  , traceRuleEnabledRef
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (when)
import           Data.IORef
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+), type (-))
import           Numeric.LinearAlgebra (Numeric)
import           System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- TODO: due to 2 missing cases, it still sometimes fails, that is, produces
-- the main @AstBuild1@, perhaps in many copies nested in other terms.
-- But there is hope it can always succeed for terms that shaped tensors
-- would type-check (ranked tensors are not fussy enough).
-- | The application @build1Vectorize k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, that is, rewrites it to a term
-- with the same value, but not containing the outermost @AstBuild1@
-- constructor and not increasing (and potentially decreasing)
-- the total number of @AstBuild1@ occuring in the term.
build1Vectorize
  :: (KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1Vectorize k (var, v0) = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = 1000 * traceWidth
      startTerm = AstBuild1 k (var, v0)
  when enabled $ do
    writeIORef traceNestingLevel 0
    hPutStrLnFlush stderr $
      "\n"
      ++ "START of vectorization for term "
      ++ ellipsisString width (show startTerm)
      ++ "\n"
  let !endTerm = build1VOccurenceUnknown k (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (show endTerm)
      ++ "\n"
  let !_A = assert (shapeAst startTerm == shapeAst endTerm
                   `blame` "build1Vectorize: term shape changed"
                   `swith`(shapeAst startTerm, shapeAst endTerm)) ()
  return endTerm

-- This abbreviation is used a lot below.
astTr :: forall n r. KnownNat n => Ast (2 + n) r -> Ast (2 + n) r
astTr = astTranspose [1, 0]

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: (KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1VOccurenceUnknown k (var, v0) =
  let traceRule = mkTraceRule "build1VOcc" (AstBuild1 k (var, v0)) v0 1
  in if intVarInAst var v0
     then build1V k (var, v0)
     else traceRule $
       astKonst k v0

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1V
  :: (KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1V k (var, v0) =
  let bv = AstBuild1 k (var, v0)
      traceRule = mkTraceRule "build1V" bv v0 1
  in case v0 of
    AstVar{} ->
      error "build1V: AstVar can't have free int variables"

    AstOp opCode args -> traceRule $
      AstOp opCode $ map (\v -> build1VOccurenceUnknown k (var, v)) args

    AstConst{} ->
      error "build1V: AstConst can't have free int variables"
    AstConstant{} -> traceRule $
      AstConstant $ AstPrimalPart bv
      -- this is very fast when interpreted in a smart way, but constant
      -- character needs to be exposed for nested cases;
      -- TODO: similarly propagate AstConstant upwards elsewhere

    AstConstInt{} -> traceRule $
      AstConstant $ AstPrimalPart bv

    AstIndexZ v is -> traceRule $
      build1VIxOccurenceUnknown k (var, v, is)
      -- @var@ is in @v@ or @is@; TODO: simplify is first or even fully
      -- evaluate (may involve huge data processing) if contains no vars
      -- and then some things simplify a lot, e.g., if constant index,
      -- we may just pick the right element of a AstFromList
    AstSum v -> traceRule $
      AstSum $ astTr $ build1V k (var, v)
    AstFromList l -> traceRule $
      astTr $ AstFromList (map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstFromVector l -> traceRule $
      astTr $ AstFromVector (V.map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstKonst s v -> traceRule $
      astTr $ astKonst s $ build1V k (var, v)
    AstAppend v w -> traceRule $
      astTr $ AstAppend (astTr $ build1VOccurenceUnknown k (var, v))
                        (astTr $ build1VOccurenceUnknown k (var, w))
    AstSlice i s v -> traceRule $
      astTr $ AstSlice i s $ astTr $ build1V k (var, v)
    AstReverse v -> traceRule $
      astTr $ AstReverse $ astTr $ build1V k (var, v)
      -- that's because @build1 k (f . g) == map1 f (build1 k g)@
      -- and @map1 f == transpose . f . transpose@
      -- TODO: though only for some f; check and fail early;
      -- probably only f that don't change shapes or ranks at least
    AstTranspose perm v -> traceRule $
      astTranspose (0 : map succ perm) $ build1V k (var, v)
    AstReshape sh v -> traceRule $
      AstReshape (k :$ sh) $ build1V k (var, v)
    AstBuild1{} -> error "build1V: impossible case of AstBuild1"
    AstGather1 k2 v (var2, ix2 :: Index p (AstInt r)) -> traceRule $
      astGatherN (k :$ k2 :$ dropShape @p (shapeAst v))
                 (build1VOccurenceUnknown k (var, v))
                 (var ::: var2 ::: Z, AstIntVar var :. ix2)
      -- AstScatter (var2, ix2) v sh -> ...
      -- no idea how to vectorize AstScatter, so let's not add prematurely
    AstGatherN sh v (vars, ix2) -> traceRule $
      astGatherN (k :$ sh)
                 (build1VOccurenceUnknown k (var, v))
                 (var ::: vars, AstIntVar var :. ix2)

-- | The application @build1VIxOccurenceUnknown k (var, v, ix)@ vectorizes
-- the term @AstBuild1 k (var, AstIndexZ v ix)@, where it's unknown whether
-- @var@ occurs in any of @v@, @ix@.
--
-- We try to push indexing down as far as needed to eliminate any occurences
-- of @var@ from @v@ (but not necessarily from @ix@), which is enough
-- to replace @AstBuild1@ with @AstGather1@ and so complete
-- the vectorization. If @var@ occurs only in the first (outermost)
-- element of @ix@, we attempt to simplify the term even more than that.
build1VIxOccurenceUnknown
  :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast (m + n) r, AstIndex m r)
  -> Ast (1 + n) r
build1VIxOccurenceUnknown k (var, v0, ZI) = build1VOccurenceUnknown k (var, v0)
build1VIxOccurenceUnknown k (var, v0, ix@(_ :. _)) =
  let traceRule = mkTraceRule "build1VIndex"
                              (AstBuild1 k (var, AstIndexZ v0 ix))
                              v0 1
  in if intVarInAst var v0
     then case astIndexStep v0 ix of  -- push deeper
       AstIndexZ v1 (i1 :. ZI) | intVarInAst var v1 -> traceRule $
         build1VIndexNormalForm k (var, v1, i1)
       v -> traceRule $
         build1VOccurenceUnknown k (var, v)  -- peel off yet another constructor
     else traceRule $
            astGather1 k v0 (var, ix)

-- I analyze here all the possible normal forms with indexing on top
-- in the hard case where the build variable appears in v1
-- (in the easy case they are covered by general rules).
build1VIndexNormalForm
  :: forall n r. (KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast n r, AstInt r)  -- n + 1 breaks plugins
  -> Ast n r
build1VIndexNormalForm k (var, v1, i1) = case v1 of
  AstFromList l ->
    if intVarInAstInt var i1
    then -- This is pure desperation. I build separately for each list element,
         -- instead of picking the right element for each build iteration
         -- (which to pick depends on the build variable).
         -- There's no other reduction left to perform and hope the build
         -- vanishes. The AstGather1 is applicable via a trick based
         -- on making the variable not occur freely in its argument term
         -- by binding the variable in nested gathers (or by reducing it away).
         -- By the inductive invariant, this succeeds.
         let f :: Ast (n - 1) r -> Ast n r
             f v = build1VOccurenceUnknown k (var, v)
             t :: Ast (1 + n) r
             t = astFromList $ map f l
         in astGather1 k t (var, i1 :. AstIntVar var :. ZI)
    else
      AstIndexZ (astFromList $ map (\v ->
        build1VOccurenceUnknown k (var, v)) l) (singletonIndex i1)
  AstFromVector l ->
    if intVarInAstInt var i1
    then let f :: Ast (n - 1) r -> Ast n r
             f v = build1VOccurenceUnknown k (var, v)
             t :: Ast (1 + n) r
             t = astFromVector $ V.map f l
         in astGather1 k t (var, i1 :. AstIntVar var :. ZI)
    else
      AstIndexZ (astFromVector $ V.map (\v ->
        build1VOccurenceUnknown k (var, v)) l) (singletonIndex i1)
  _ -> error $ "build1VIndexNormalForm: not a normal form"
               ++ show (k, var, v1, i1)


-- * Rule tracing machinery

-- TODO: set from the testing commandline, just as eqEpsilonRef in EqEpsilon.hs
traceRuleEnabledRef :: IORef Bool
{-# NOINLINE traceRuleEnabledRef #-}
traceRuleEnabledRef = unsafePerformIO $ newIORef False

traceNestingLevel :: IORef Int
{-# NOINLINE traceNestingLevel #-}
traceNestingLevel = unsafePerformIO $ newIORef 0

traceWidth :: Int
traceWidth = 80

padString :: Int -> String -> String
padString width full = let cropped = take width full
                       in if length full <= width
                          then take width $ cropped ++ repeat ' '
                          else take (width - 3) cropped ++ "..."

ellipsisString :: Int -> String -> String
ellipsisString width full = let cropped = take width full
                            in if length full <= width
                               then cropped
                               else take (width - 3) cropped ++ "..."

mkTraceRule :: (KnownNat n, Show r, Numeric r, Show ca)
            => String -> Ast n r -> ca -> Int -> Ast n r -> Ast n r
mkTraceRule prefix from caseAnalysed nwords to = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = traceWidth
      constructorName =
        unwords $ take nwords $ words $ take 20 $ show caseAnalysed
      ruleName = prefix ++ "." ++ constructorName
      ruleNamePadded = take 20 $ ruleName ++ repeat ' '
  when enabled $ do
    nestingLevel <- readIORef traceNestingLevel
    modifyIORef' traceNestingLevel succ
    let paddedNesting = take 3 $ show nestingLevel ++ repeat ' '
    -- Force in the correct order:
    let !stringFrom = show from
    let !stringTo = show to
    hPutStrLnFlush stderr $ paddedNesting ++ "rule " ++ ruleNamePadded
                            ++ " sends " ++ padString width stringFrom
                            ++ " to " ++ padString width stringTo
    let !_A = assert (shapeAst from == shapeAst to
                     `blame` "mkTraceRule: term shape changed"
                     `swith`(shapeAst from, shapeAst to, from, to)) ()
    modifyIORef' traceNestingLevel pred
  return $! to

hPutStrLnFlush :: Handle -> String -> IO ()
hPutStrLnFlush target s = do
  hFlush stdout >> hFlush stderr
  hPutStrLn target s
  hFlush stdout >> hFlush stderr
