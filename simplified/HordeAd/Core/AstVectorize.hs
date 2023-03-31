{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Vectorization of the build operation in Ast.
module HordeAd.Core.AstVectorize
  ( build1Vectorize, traceRuleEnabledRef
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (when)
import qualified Data.Array.RankedS as OR
import           Data.IORef
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- * Vectorization

-- | The application @build1Vectorize k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, that is, rewrites it to a term
-- with the same value, but not containing the outermost @AstBuild1@
-- constructor and not increasing (and potentially decreasing)
-- the total number of @AstBuild1@ occuring in the term.
build1Vectorize
  :: (KnownNat n, ShowAstSimplify r)
  => Int -> (AstVarId, Ast n r) -> Ast (1 + n) r
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
astTr :: forall n r. Ast (2 + n) r -> Ast (2 + n) r
astTr = AstTranspose [1, 0]

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: (KnownNat n, ShowAstSimplify r)
  => Int -> (AstVarId, Ast n r) -> Ast (1 + n) r
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
  :: (KnownNat n, ShowAstSimplify r)
  => Int -> (AstVarId, Ast n r) -> Ast (1 + n) r
build1V k (var, v00) =
  let v0 = simplifyStepNonIndex v00
      bv = AstBuild1 k (var, v0)
      traceRule = mkTraceRule "build1V" bv v0 1
  -- Almost surely the term will be transformed, so it can just as well
  -- we one-step simplified first (many steps if guaranteed net beneficial).
  in case v0 of
    AstVar{} ->
      error "build1V: AstVar can't have free int variables"
    AstLet{} -> error "TODO"

    AstOp opCode args -> traceRule $
      AstOp opCode $ map (\v -> build1VOccurenceUnknown k (var, v)) args

    AstConst{} ->
      error "build1V: AstConst can't have free int variables"
    AstConstant (AstPrimalPart v) -> traceRule $
      astConstant $ AstPrimalPart $ build1V k (var, v)
    AstIndexZ v ix -> traceRule $
      build1VIndex k (var, v, ix)  -- @var@ is in @v@ or @ix@
    AstSum v -> traceRule $
      astSum $ astTr $ build1V k (var, v)
    AstConstInt0 (AstIntVar var2) -> traceRule $
      if var == var2
      then AstConst $ OR.mapA fromIntegral $ OR.iota @Int k  -- TODO: Enum r
      else error "build1V: AstConstInt0 contains no free int variables"
    AstConstInt0{} ->
      error "build1V: only tfromIndex0 of variables is supported at this time"
    AstScatter sh v (vars, ix) -> traceRule $
      astScatter (k :$ sh)
                 (build1VOccurenceUnknown k (var, v))
                 (var ::: vars, AstIntVar var :. ix)
        -- note that this is only the easier half of vectorization of scatter;
        -- the harder half requires simplification and probably a new
        -- normal form

    AstFromList l -> traceRule $
      astTr $ astFromList (map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstFromVector l -> traceRule $
      astTr $ astFromVector (V.map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstKonst s v -> traceRule $
      astTr $ astKonst s $ build1V k (var, v)
    AstAppend v w -> traceRule $
      astTr $ astAppend (astTr $ build1VOccurenceUnknown k (var, v))
                        (astTr $ build1VOccurenceUnknown k (var, w))
    AstSlice i s v -> traceRule $
      astTr $ astSlice i s $ astTr $ build1V k (var, v)
    AstReverse v -> traceRule $
      astTr $ astReverse $ astTr $ build1V k (var, v)
    AstTranspose perm v -> traceRule $
      astTranspose (simplifyPermutation $ 0 : map succ perm)
                   (build1V k (var, v))
    AstReshape sh v -> traceRule $
      astReshape (k :$ sh) $ build1V k (var, v)
    AstBuild1{} -> error "build1V: impossible case of AstBuild1"
    AstGatherZ sh v (vars, ix) -> traceRule $
      astGatherStep (k :$ sh)
                    (build1VOccurenceUnknown k (var, v))
                    (var ::: vars, AstIntVar var :. ix)
    AstD (AstPrimalPart u) (AstDualPart u') ->
      AstD (AstPrimalPart $ build1VOccurenceUnknown k (var, u))
           (AstDualPart $ build1VOccurenceUnknown k (var, u'))

-- | The application @build1VIndex k (var, v, ix)@ vectorizes
-- the term @AstBuild1 k (var, AstIndexZ v ix)@, where it's unknown whether
-- @var@ occurs in any of @v@, @ix@.
--
-- We try to push indexing down as far as needed to eliminate any occurences
-- of @var@ from @v@ (but not necessarily from @ix@), which is enough
-- to replace @AstBuild1@ with @AstGatherZ@ and so complete
-- the vectorization.
--
-- This pushing down is performed by alternating steps of simplification,
-- in @astIndexStep@, that eliminated indexing from the top of a term
-- position (except two permissible normal forms) and vectorization,
-- @build1VOccurenceUnknown@, that recursively goes down under constructors
-- until it encounter indexing again. We have to do this in lockstep
-- so that we simplify terms only as much as needed to vectorize.
--
-- If simplification can't proceed, which means that we reached one of the few
-- normal forms wrt simplification, we invoke the pure desperation rule (D)
-- which produces large tensors, which are hard to simplify even when
-- eventually proven unnecessary. The rule changes the index to a gather
-- and pushes the build down the gather, getting the vectorization unstuck.
build1VIndex
  :: forall m n r. (KnownNat m, KnownNat n, ShowAstSimplify r)
  => Int -> (AstVarId, Ast (m + n) r, AstIndex m r)
  -> Ast (1 + n) r
build1VIndex k (var, v0, ZI) = build1VOccurenceUnknown k (var, v0)
build1VIndex k (var, v0, ix@(_ :. _)) =
  let traceRule = mkTraceRule "build1VIndex"
                              (AstBuild1 k (var, AstIndexZ v0 ix))
                              v0 1
  in if intVarInAst var v0
     then case astIndexStep v0 ix of  -- push deeper
       AstIndexZ v1 ZI -> traceRule $
         build1VOccurenceUnknown k (var, v1)
       v@(AstIndexZ v1 ix1) -> traceRule $
         let ruleD = astGatherStep (k :$ dropShape (shapeAst v1))
                                   (build1V k (var, v1))
                                   (var ::: Z, AstIntVar var :. ix1)
         in if intVarInAst var v1
            then case (v1, ix1) of  -- try to avoid ruleD if not a normal form
              (AstFromList{}, _ :. ZI) -> ruleD
              (AstFromVector{}, _ :. ZI) -> ruleD
              (AstScatter{}, _) -> ruleD
              _ -> build1VOccurenceUnknown k (var, v)  -- not a normal form
            else build1VOccurenceUnknown k (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurenceUnknown k (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStep (k :$ dropShape (shapeAst v0)) v0 (var ::: Z, ix)


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

mkTraceRule :: (KnownNat n, ShowAstSimplify r)
            => String -> Ast n r -> Ast m r -> Int -> Ast n r -> Ast n r
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
