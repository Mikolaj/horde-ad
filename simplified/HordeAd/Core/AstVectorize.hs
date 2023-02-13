{-# LANGUAGE DataKinds, GADTs #-}
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
import           Data.Array.Internal (valueOf)
import           Data.IORef
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import           System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
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
  let traceRule = mkTraceRule "build1V" (AstBuild1 k (var, v0)) v0 1
  in case v0 of
    AstVar{} ->
      error "build1V: AstVar can't have free int variables"

    AstOp opCode args -> traceRule $
      AstOp opCode $ map (\v -> build1VOccurenceUnknown k (var, v)) args

    AstConst{} ->
      error "build1V: AstConst can't have free int variables"
    AstConstant{} -> traceRule $
      AstConstant $ AstPrimalPart $ AstBuild1 k (var, v0)
      -- this is very fast when interpreted in a smart way, but constant
      -- character needs to be exposed for nested cases;
      -- TODO: similarly propagate AstConstant upwards elsewhere

    AstConstInt{} -> traceRule $
      AstConstant $ AstPrimalPart $ AstBuild1 k (var, v0)
    AstIndexZ v is -> traceRule $
      build1VIxOccurenceUnknown k (var, v, is)
      -- @var@ is in @v@ or @is@; TODO: simplify is first or even fully
      -- evaluate (may involve huge data processing) if contains no vars
      -- and then some things simplify a lot, e.g., if constant index,
      -- we may just pick the right element of a AstFromList
    AstSum v -> traceRule $
      AstSum $ astTranspose $ build1V k (var, v)
    AstFromList l -> traceRule $
      astTranspose
      $ AstFromList (map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstFromVector l -> traceRule $
      astTranspose
      $ AstFromVector (V.map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstKonst s v -> traceRule $
      astTranspose $ astKonst s $ build1V k (var, v)
    AstAppend v w -> traceRule $
      astTranspose $ AstAppend
                       (astTranspose $ build1VOccurenceUnknown k (var, v))
                       (astTranspose $ build1VOccurenceUnknown k (var, w))
    AstSlice i s v -> traceRule $
      astTranspose $ AstSlice i s $ astTranspose $ build1V k (var, v)
    AstReverse v -> traceRule $
      astTranspose $ AstReverse $ astTranspose $ build1V k (var, v)
      -- that's because @build1 k (f . g) == map1 f (build1 k g)@
      -- and @map1 f == transpose . f . transpose@
      -- TODO: though only for some f; check and fail early;
      -- probably only f that don't change shapes or ranks at least
    AstTransposeGeneral perm v -> traceRule $
      astTransposeGeneral (0 : map succ perm) $ build1V k (var, v)
    AstFlatten v -> traceRule $
      build1V k (var, AstReshape (flattenShape $ shapeAst v0) v)
        -- TODO: alternatively we could introduce a subtler operation than
        -- AstReshape that just flattens n levels down; it probably
        -- vectorizes to itself just fine; however AstReshape is too useful
    AstReshape sh v -> traceRule $
      AstReshape (k :$ sh) $ build1V k (var, v)
    AstBuild1{} -> traceRule $
      AstBuild1 k (var, v0)
      -- This is a recoverable problem because, e.g., this may be nested
      -- inside projections. So we add to the term and wait for rescue.
      -- It probably speeds up vectorization a tiny bit if we nest
      -- AstBuild1 instead of rewriting into AstBuild.
    AstGather1 (var2, ix2 :: Index p (AstInt r)) v k2 -> traceRule $
      astGatherN (var ::: var2 ::: Z, AstIntVar var :. ix2)
                 (build1VOccurenceUnknown k (var, v))
                 (k :$ k2 :$ dropShape @p (shapeAst v))
      -- AstScatter (var2, ix2) v sh -> ...
      -- no idea how to vectorize AstScatter, so let's not add prematurely
    AstGatherN (vars, ix2) v sh -> traceRule $
      astGatherN (var ::: vars, AstIntVar var :. ix2)
                 (build1VOccurenceUnknown k (var, v))
                 (k :$ sh)

    AstOMap{} -> traceRule $
      AstConstant $ AstPrimalPart $ AstBuild1 k (var, v0)
    -- All other patterns are redundant due to GADT typing.

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
  let traceRule = mkTraceRule "build1VIxOcc"
                              (AstBuild1 k (var, AstIndexZ v0 ix))
                              v0 1
  in if intVarInAst var v0
     then build1VIx k (var, v0, ix)  -- push deeper
     else traceRule $
            astGather1 (var, ix) v0 k

-- | The application @build1VIx k (var, v, is)@ vectorizes
-- the term @AstBuild1 k (var, AstIndexZ v is)@, where it's known that
-- @var@ occurs in @v@. It may or may not additionally occur in @is@.
--
-- We try to push indexing down as far as needed to eliminate any occurences
-- of @var@ from @v@ (but not necessarily from @is@), which is enough
-- to replace @AstBuild1@ with @AstGather1@ and so complete
-- the vectorization. We also partially evaluate/simplify the terms,
-- if possible in constant time.
build1VIx
  :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast (m + n) r, AstIndex m r)
  -> Ast (1 + n) r
build1VIx k (var, v0, ZI) = build1V k (var, v0)
build1VIx k (var, v0, is@(i1 :. rest1)) =
  let traceRule = mkTraceRule "build1VIx"
                              (AstBuild1 k (var, AstIndexZ v0 is))
                              v0 1
  in case v0 of
    AstVar{} ->
      error "build1VIx: AstVar can't have free int variables"

    AstOp opCode args -> traceRule $
      AstOp opCode $ map (\v -> build1VIxOccurenceUnknown k (var, v, is)) args

    AstConst{} ->
      error "build1VIx: AstConst can't have free int variables"
    AstConstant{} -> traceRule $
      AstConstant $ AstPrimalPart $ AstBuild1 k (var, AstIndexZ v0 is)

    AstConstInt{} -> traceRule $
      AstConstant $ AstPrimalPart $ AstBuild1 @n k (var, AstIndexZ v0 is)

    AstIndexZ v is2 -> traceRule $
      build1VIxOccurenceUnknown k (var, v, appendIndex is is2)
    AstSum v -> traceRule $
      build1V k
        (var, AstSum (AstIndexZ (astTranspose v) is))
          -- that's because @index (sum v) i == sum (map (index i) v)@
    AstFromList l | intVarInAstInt var i1 -> traceRule $
      -- This is pure desperation. I build separately for each list element,
      -- instead of picking the right element for each build iteration
      -- (which to pick depends on the build variable).
      -- @build1VSimplify@ is not applicable, because var is in v0.
      -- The only thing to do is constructing a AstGather1 via a trick.
      -- There's no other reduction left to perform and hope the build vanishes.
      let t = AstFromList $ map (\v ->
            build1VOccurenceUnknown k (var, AstIndexZ v rest1)) l
      in astGather1 (var, i1 :. AstIntVar var :. ZI) t k
    AstFromList l -> traceRule $
      AstIndexZ (AstFromList $ map (\v ->
        build1VOccurenceUnknown k (var, AstIndexZ v rest1)) l)
                                  (singletonIndex i1)
    AstFromVector l | intVarInAstInt var i1 -> traceRule $
      let t = AstFromVector $ V.map (\v ->
            build1VOccurenceUnknown k (var, AstIndexZ v rest1)) l
      in astGather1 (var, i1 :. AstIntVar var :. ZI) t k
    AstFromVector l -> traceRule $
      AstIndexZ (AstFromVector $ V.map (\v ->
        build1VOccurenceUnknown k (var, AstIndexZ v rest1)) l)
                                  (singletonIndex i1)
    -- Partially evaluate in constant time:
    AstKonst _k v -> traceRule $
      build1VIx k (var, v, rest1)
        -- this is an example term for which vectorization changes
        -- the value of index out of bounds (from 0 to v in this case));
        -- fixing this would complicate terms greatly at no value
        -- for the common case where out of bound does not appear,
        -- as well as for the case where value other than 0 is desired
    AstAppend v w -> traceRule $
      let vlen = AstIntConst $ lengthAst v
          is2 = fmap (\i -> AstIntOp PlusIntOp [i, vlen]) is
      in build1V k (var, astCond (AstRelInt LsOp [i1, vlen])
                                 (AstIndexZ v is)
                                 (AstIndexZ w is2))
           -- this is basically partial evaluation, but in constant
           -- time unlike evaluating AstFromList, etc.
    AstSlice i2 _k v -> traceRule $
      build1VIx k (var, v, fmap (\i ->
        AstIntOp PlusIntOp [i, AstIntConst i2]) is)
    AstReverse v -> traceRule $
      let revIs = AstIntOp MinusIntOp [AstIntConst (lengthAst v - 1), i1]
                  :. rest1
      in build1VIx k (var, v, revIs)
    AstTransposeGeneral perm v -> traceRule $
      if valueOf @m < length perm
      then AstBuild1 k (var, AstIndexZ v0 is)  -- we give up
             -- TODO: for this we really need generalized indexes that
             -- first project, then transpose and so generalized gather;
             -- or instead push down transpose, but it may be expensive
             -- or get stuck as well (transpose of a list of lists
             -- would need to shuffle all the individual elements);
             -- or perhaps it's enough to pass a permutation
             -- in build1VIx and wrap the argument
             -- to gather in AstTransposeGeneral with the permutation
      else build1VIx k (var, v, permutePrefixIndex perm is)
    AstFlatten v -> traceRule $
      case rest1 of
        ZI ->
          let ixs2 = fromLinearIdx (fmap AstIntConst (shapeAst v)) i1
          in build1VIx k (var, v, ixs2)
        _ ->
          error "build1VIx: AstFlatten: impossible pattern needlessly required"
    AstReshape{} -> traceRule $
      AstBuild1 k (var, AstIndexZ v0 is)  -- we give up
      {- TODO: This angle of attack fails, because AstSlice with variable
         first argument doesn't vectorize in build1VOccurenceUnknown. For it
         to vectorize, we'd need a new operation, akin to gather,
         with the semantics of build (slice), a gradient, a way to vectorize
         it, in turn, normally and with indexing applied, etc.;
         vectorizing this operation would probably force a generalization
         that acts like gatherN, but produces not a 1-element from the spot
         an index points at, but some fixed k elements and then, unlike gatherN,
         does not flatten the segments, but makes a tensor out of them intact;
         or, if that helps, the operation may just drop a variable
         initial segment of subtensors (of different length in each)
      let i = toLinearIdx2 (fmap AstIntConst sh) is
          -- This converts indexing into a slice and flatten, which in general
          -- is avoided, because it causes costly linearlization, but here
          -- we are going to reshape outside, anyway, and also we are desperate.
          -- BTW, slice has to accept variable first argument precisely
          -- to be usable for convering indexing into. Note that this argument
          -- does not affect shape, so shapes remain static.
          u = AstSlice i (product $ drop (length is) sh) $ AstFlatten v
      in AstReshape (n : sh) $ build1V k (var, u)
      -}
    AstBuild1 _n2 (var2, v) -> traceRule $
      -- Here we seize the chance to recover earlier failed vectorization,
      -- by choosing only one element of this whole build, eliminating it.
      build1VIx k (var, substituteAst i1 var2 v, rest1)
    AstGather1 (var2, ix2) v _n2 -> traceRule $
      let ix3 = fmap (substituteAstInt i1 var2) ix2
      in build1VIxOccurenceUnknown k (var, v, appendIndex rest1 ix3)
           -- we don't know if var occurs in v; it could have been in ix2
    AstGatherN (Z, ix2) v _sh -> traceRule $
      build1VIx k (var, AstIndexZ v ix2, is)
    AstGatherN (var2 ::: vars, ix2) v (_ :$ sh') -> traceRule $
      let ix3 = fmap (substituteAstInt i1 var2) ix2
      in build1VIx
           k (var, unsafeCoerce $ astGatherN (vars, ix3) v sh', rest1)
          -- GHC with the plugin doesn't cope with this
          -- (https://github.com/clash-lang/ghc-typelits-natnormalise/issues/71)
          -- so unsafeCoerce is back
    AstGatherN{} ->
      error "build1VIx: AstGatherN: impossible pattern needlessly required"

    AstOMap{} -> traceRule $
      AstConstant $ AstPrimalPart $ AstBuild1 k (var, AstIndexZ v0 is)
    -- All other patterns are redundant due to GADT typing.


-- * Rule tracing machinery

-- TODO: set from the testing commandline, just as eqEpsilonRef in EqEpsilon.hs
traceRuleEnabledRef :: IORef Bool
{-# NOINLINE traceRuleEnabledRef #-}
traceRuleEnabledRef = unsafePerformIO $ newIORef True

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
