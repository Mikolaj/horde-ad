{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Vectorization of @Ast@, eliminating the @build1@ operation.
module HordeAd.Core.AstVectorize
  ( build1Vectorize, traceRuleEnabledRef
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (when)
import           Data.IORef
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import           System.IO.Unsafe (unsafePerformIO)

import           HordeAd.Core.Ast hiding
  (AstBool (..), AstDomains (..), AstInt (..), AstRanked (..))
import           HordeAd.Core.Ast (AstDomains, AstInt, AstRanked)
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorClass
import           HordeAd.Internal.SizedList

-- * Vectorization

-- | The application @build1Vectorize k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, that is, rewrites it to a term
-- with the same value, but not containing the outermost @AstBuild1@
-- constructor and not increasing (and potentially decreasing)
-- the total number of @AstBuild1@ occuring in the term.
build1Vectorize
  :: (KnownNat n, GoodScalar r)
  => Int -> (AstVarId, AstRanked r n) -> AstRanked r (1 + n)
{-# NOINLINE build1Vectorize #-}
build1Vectorize k (var, v0) = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = 1000 * traceWidth
      startTerm = Ast.AstBuild1 k (var, v0)
      renames = IM.fromList [(1, ""), (2, "")]
  when enabled $ do
    writeIORef traceNestingLevel 0
    hPutStrLnFlush stderr $
      "\n"
      ++ "START of vectorization for term "
      ++ ellipsisString width (printAstSimple renames startTerm)
      ++ "\n"
  let !endTerm = build1VOccurenceUnknown k (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (printAstSimple renames endTerm)
      ++ "\n"
  let !_A = assert (shapeAst startTerm == shapeAst endTerm
                   `blame` "build1Vectorize: term shape changed"
                   `swith`(shapeAst startTerm, shapeAst endTerm)) ()
  return endTerm

-- This abbreviation is used a lot below.
astTr :: forall n r. (KnownNat n, GoodScalar r)
      => AstRanked r (2 + n) -> AstRanked r (2 + n)
astTr = astTranspose [1, 0]

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: (KnownNat n, GoodScalar r)
  => Int -> (AstVarId, AstRanked r n) -> AstRanked r (1 + n)
build1VOccurenceUnknown k (var, v0) =
  let traceRule = mkTraceRule "build1VOcc" (Ast.AstBuild1 k (var, v0)) v0 1
  in if intVarInAst var v0
     then build1V k (var, v0)
     else traceRule $
       astReplicate k v0

build1VOccurenceUnknownRefresh
  :: (KnownNat n, GoodScalar r)
  => Int -> (AstVarId, AstRanked r n) -> AstRanked r (1 + n)
{-# NOINLINE build1VOccurenceUnknownRefresh #-}
build1VOccurenceUnknownRefresh k (var, v0) = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIIO id
  let v2 = substitute1Ast @0 (Right astVarFresh) var v0
  return $! build1VOccurenceUnknown k (varFresh, v2)

intBindingRefresh
  :: GoodScalar r
  => AstVarId -> AstIndex n r -> (AstVarId, AstInt r, AstIndex n r)
{-# NOINLINE intBindingRefresh #-}
intBindingRefresh var ix = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIIO id
  let ix2 = fmap (substituteAstInt @0 (Right astVarFresh) var) ix
  return $! (varFresh, astVarFresh, ix2)

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1V
  :: (KnownNat n, GoodScalar r)
  => Int -> (AstVarId, AstRanked r n) -> AstRanked r (1 + n)
build1V k (var, v00) =
  let v0 = simplifyStepNonIndex v00
        -- Almost surely the term will be transformed, so it can just
        -- as well we one-step simplified first (many steps if redexes
        -- get uncovered and so the simplification requires only constant
        -- look-ahead, but has a guaranteed net benefit).
      bv = Ast.AstBuild1 k (var, v0)
      traceRule = mkTraceRule "build1V" bv v0 1
  in case v0 of
    Ast.AstVar{} ->
      error "build1V: AstVar can't have free int variables"
    Ast.AstLet var2 u v ->
      let sh = shapeAst u
          projection = Ast.AstIndexZ (Ast.AstVar (k :$ sh) var2)
                                     (Ast.AstIntVar var :. ZI)
          v2 = substitute1Ast (Left projection) var2 v
            -- we use the substitution that does not simplify, which is sad,
            -- because very low hanging fruits may be left hanging, but we
            -- don't want to simplify the whole term; a better alternative
            -- would be a substitution that only simplifies the touched
            -- terms with one step lookahead, as normally when vectorizing
      in astLet var2 (build1VOccurenceUnknown k (var, u))
                     (build1VOccurenceUnknownRefresh k (var, v2))
                        -- ensure no duplicated bindings; this is stronger
                        -- than what we need for simple substitution, etc.
    Ast.AstLetADShare{} -> error "build1V: AstLetADShare"

    Ast.AstOp opCode args -> traceRule $
      Ast.AstOp opCode $ map (\v -> build1VOccurenceUnknown k (var, v)) args
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another, unlike inside a let,
        -- which may get inlined
    Ast.AstSumOfList args -> traceRule $
      Ast.AstSumOfList $ map (\v -> build1VOccurenceUnknown k (var, v)) args
    Ast.AstIota ->
      error "build1V: AstIota can't have free int variables"

    Ast.AstIndexZ v ix -> traceRule $
      build1VIndex k (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstSum v -> traceRule $
      astSum $ astTr $ build1V k (var, v)
    Ast.AstScatter sh v (vars, ix) -> traceRule $
      let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix
      in astScatter (k :$ sh)
                    (build1VOccurenceUnknown k (var, v))
                    (varFresh ::: vars, astVarFresh :. ix2)

    Ast.AstFromList l -> traceRule $
      astTr $ astFromList (map (\v -> build1VOccurenceUnknown k (var, v)) l)
    Ast.AstFromVector l -> traceRule $
      astTr $ astFromVector (V.map (\v -> build1VOccurenceUnknown k (var, v)) l)
    Ast.AstReplicate s v -> traceRule $
      astTr $ astReplicate s $ build1V k (var, v)
    Ast.AstAppend v w -> traceRule $
      astTr $ astAppend (astTr $ build1VOccurenceUnknown k (var, v))
                        (astTr $ build1VOccurenceUnknown k (var, w))
    Ast.AstSlice i s v -> traceRule $
      astTr $ astSlice i s $ astTr $ build1V k (var, v)
    Ast.AstReverse v -> traceRule $
      astTr $ astReverse $ astTr $ build1V k (var, v)
    Ast.AstTranspose perm v -> traceRule $
      astTranspose (simplifyPermutation $ 0 : map succ perm)
                   (build1V k (var, v))
    Ast.AstReshape sh v -> traceRule $
      astReshape (k :$ sh) $ build1V k (var, v)
    Ast.AstBuild1{} -> error "build1V: impossible case of AstBuild1"
    Ast.AstGatherZ sh v (vars, ix) -> traceRule $
      let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix
      in astGatherStep (k :$ sh)
                       (build1VOccurenceUnknown k (var, v))
                       (varFresh ::: vars, astVarFresh :. ix2)

    Ast.AstConst{} ->
      error "build1V: AstConst can't have free int variables"
    Ast.AstConstant (AstPrimalPart v) -> traceRule $
      astConstant $ AstPrimalPart $ build1V k (var, v)
    Ast.AstD (AstPrimalPart u) (AstDualPart u') ->
      Ast.AstD (AstPrimalPart $ build1VOccurenceUnknown k (var, u))
               (AstDualPart $ build1VOccurenceUnknown k (var, u'))
    Ast.AstLetDomains vars l v ->
      -- Here substitution traverses @v@ term tree @length vars@ times.
      let subst (var1, AstDynamic u1) =
            let sh = shapeAst u1
                projection = Ast.AstIndexZ (Ast.AstVar (k :$ sh) var1)
                                           (Ast.AstIntVar var :. ZI)
            in substitute1Ast (Left projection) var1
          v2 = V.foldr subst v (V.zip vars (unwrapAstDomains l))
            -- we use the substitution that does not simplify
      in Ast.AstLetDomains vars (build1VOccurenceUnknownDomains k (var, l))
                                (build1VOccurenceUnknownRefresh k (var, v2))

build1VOccurenceUnknownDynamic
  :: GoodScalar r
  => Int -> (AstVarId, AstDynamic r) -> AstDynamic r
build1VOccurenceUnknownDynamic k (var, AstDynamic u) =
  AstDynamic $ build1VOccurenceUnknown k (var, u)

build1VOccurenceUnknownDomains
  :: GoodScalar r
  => Int -> (AstVarId, AstDomains r) -> AstDomains r
build1VOccurenceUnknownDomains k (var, v0) = case v0 of
  Ast.AstDomains l ->
    Ast.AstDomains $ V.map (\u -> build1VOccurenceUnknownDynamic k (var, u)) l
  Ast.AstDomainsLet var2 u v ->
    let sh = shapeAst u
        projection = Ast.AstIndexZ (Ast.AstVar (k :$ sh) var2)
                                   (Ast.AstIntVar var :. ZI)
        v2 = substitute1AstDomains (Left projection) var2 v
          -- we use the substitution that does not simplify
    in astDomainsLet var2 (build1VOccurenceUnknownRefresh k (var, u))
                          (build1VOccurenceUnknownDomains k (var, v2))

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
  :: forall m n r. (KnownNat m, KnownNat n, GoodScalar r)
  => Int -> (AstVarId, AstRanked r (m + n), AstIndex m r)
  -> AstRanked r (1 + n)
build1VIndex k (var, v0, ZI) = build1VOccurenceUnknown k (var, v0)
build1VIndex k (var, v0, ix@(_ :. _)) =
  let traceRule = mkTraceRule "build1VIndex"
                              (Ast.AstBuild1 k (var, Ast.AstIndexZ v0 ix))
                              v0 1
  in if intVarInAst var v0
     then case astIndexStep v0 ix of  -- push deeper
       Ast.AstIndexZ v1 ZI -> traceRule $
         build1VOccurenceUnknown k (var, v1)
       v@(Ast.AstIndexZ v1 ix1) -> traceRule $
         let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix1
             ruleD = astGatherStep
                       (k :$ dropShape (shapeAst v1))
                       (build1V k (var, v1))
                       (varFresh ::: Z, astVarFresh :. ix2)
         in if intVarInAst var v1
            then case (v1, ix1) of  -- try to avoid ruleD if not a normal form
              (Ast.AstFromList{}, _ :. ZI) -> ruleD
              (Ast.AstFromVector{}, _ :. ZI) -> ruleD
              (Ast.AstScatter{}, _) -> ruleD
              (Ast.AstAppend{}, _) -> ruleD
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

mkTraceRule :: (KnownNat n, KnownNat m, GoodScalar r)
            => String -> AstRanked r n -> AstRanked r m -> Int -> AstRanked r n -> AstRanked r n
{-# NOINLINE mkTraceRule #-}
mkTraceRule prefix from caseAnalysed nwords to = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = traceWidth
      renames = IM.fromList [(1, ""), (2, "")]
      constructorName =
        unwords $ take nwords $ words $ take 20
        $ printAstSimple renames caseAnalysed
      ruleName = prefix ++ "." ++ constructorName
      ruleNamePadded = take 20 $ ruleName ++ repeat ' '
  when enabled $ do
    nestingLevel <- readIORef traceNestingLevel
    modifyIORef' traceNestingLevel succ
    let paddedNesting = take 3 $ show nestingLevel ++ repeat ' '
    -- Force in the correct order:
    let !stringFrom = printAstSimple renames from
    let !stringTo = printAstSimple renames to
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
