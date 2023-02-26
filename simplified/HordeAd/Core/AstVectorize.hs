{-# LANGUAGE DataKinds, GADTs #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
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
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, OrderingI (..), cmpNat, sameNat, type (+), type (-), type (<=))
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
      build1VIxOccurenceUnknown k (var, v, is) []
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

-- | The application @build1VIxOccurenceUnknown k (var, v, ix) perm@ vectorizes
-- the term @AstBuild1 k (var, AstIndexZ (AstTranspose perm v) ix)@,
-- where it's unknown whether @var@ occurs in any of @v@, @ix@.
-- Always @perm@ is empty or longer than @ix@.
--
-- We try to push indexing (and transposing) down as far as needed
-- to eliminate any occurences of @var@ from @v@ (but not necessarily
-- from @ix@), which is enough to replace @AstBuild1@ with @AstGather1@
-- and so complete the vectorization. If @var@ occurs only in the first
-- (outermost) element of @ix@, we attempt to simplify the term even more
-- than that.
build1VIxOccurenceUnknown
  :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast (m + n) r, AstIndex m r) -> Permutation
  -> Ast (1 + n) r
build1VIxOccurenceUnknown k (var, v0, ZI) perm0 =
  build1VOccurenceUnknown k (var, AstTranspose perm0 v0)
build1VIxOccurenceUnknown k (var, v0, ix@(_ :. _)) perm0 =
 assert (null perm0 || length perm0 > valueOf @m) $
  let traceRule = mkTraceRule "build1VIxOcc"
                    (AstBuild1 k (var, AstIndexZ (AstTranspose perm0 v0) ix))
                    v0 1
  in if intVarInAst var v0
     then build1VIx k (var, v0, ix) perm0  -- push deeper
     else traceRule $
            astGather1 k (AstTranspose perm0 v0) (var, ix)

-- | The application @build1VIx k (var, v, ix) perm@ vectorizes
-- the term @AstBuild1 k (var, AstIndexZ (AstTranspose perm v) ix)@,
-- where it's known that @var@ occurs in @v@. It may or may not
-- additionally occur in @ix@.
-- Always @perm@ is empty or longer than @ix@.
--
-- We try to push indexing (and transposing) down as far as needed
-- to eliminate any occurences of @var@ from @v@ (but not necessarily
-- from @ix@), which is enough to replace @AstBuild1@ with @AstGather1@
-- and so complete the vectorization. We also partially evaluate/simplify
-- the terms, if possible in constant time.
build1VIx
  :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast (m + n) r, AstIndex m r) -> Permutation
  -> Ast (1 + n) r
build1VIx k (var, v0, ZI) perm0 = build1V k (var, AstTranspose perm0 v0)
build1VIx k (var, v0, is@(i1 :. rest1)) perm0 =
 assert (null perm0 || length perm0 > valueOf @m) $
  let bv = AstBuild1 k (var, AstIndexZ (AstTranspose perm0 v0) is)
      traceRule = mkTraceRule "build1VIx" bv v0 1
  in case v0 of
    AstVar{} ->
      error "build1VIx: AstVar can't have free int variables"

    AstOp opCode args -> traceRule $
      AstOp opCode $ map (\v ->
        build1VIxOccurenceUnknown k (var, v, is) perm0) args

    AstConst{} ->
      error "build1VIx: AstConst can't have free int variables"
    AstConstant{} -> traceRule $
      AstConstant $ AstPrimalPart bv

    AstConstInt{} -> traceRule $
      AstConstant $ AstPrimalPart bv

    AstIndexZ v (ix2 :: AstIndex p r) -> traceRule $
      let p = valueOf @p
          perm2 = [0 .. p - 1] ++ map (+ p) perm0
      in build1VIxOccurenceUnknown
           k (var, astTranspose perm2 v, appendIndex ix2 is) []
    AstSum v -> traceRule $
      let perm2 = 0 : map succ perm0
          perm3 = permCycle $ valueOf @m + 1
          tv = astTranspose perm3 $ astTranspose perm2 v
      in build1V k (var, AstSum (AstIndexZ tv is))
    AstFromList l -> traceRule $
      -- The first case is pure desperation. I build separately for each list
      -- element instead of picking the right element for each build function
      -- application (which to pick depends on the build variable).
      -- @gatherSimplify@ is not applicable, because var is in v0.
      -- The only thing to do is constructing a AstGather1 via a trick.
      -- There's no other reduction left to perform and hope the build vanishes.
      case permSwapSplit perm0 of
        Nothing ->
          if intVarInAstInt var i1
          then let t = AstFromList $ map (\v ->
                     build1VOccurenceUnknown
                       k (var, AstIndexZ v rest1)) l
               in astGather1 k t (var, i1 :. AstIntVar var :. ZI)
          else AstIndexZ (AstFromList $ map (\v ->
                 build1VOccurenceUnknown
                   k (var, AstIndexZ v rest1)) l) (singletonIndex i1)
        Just (j, permRest) ->
          build1V k (var, t)
         where
          t = case splitAtInt_Index j is of
            (_ :: AstIndex m r, ZI) ->
              let j1 = j - valueOf @m
              in astTranspose ([j1] ++ [1 .. j1 - 1] ++ [0])  -- the swap
                 $ case cmpNat (Proxy @1) (Proxy @n) of
                     EQI -> AstFromList @(n - 1) $ map (\v ->
                              AstIndexZ (astTranspose permRest v) is) l
                     LTI -> AstFromList @(n - 1) $ map (\v ->
                              AstIndexZ (astTranspose permRest v) is) l
                     _ -> error "build1VIx: violattion of an assumption about rank deduced from transposition that deflects a projection"
            (ix2, i :. ixRest2) ->
              -- The swap consumed in getting index i to the first position.
              AstIndexZ (AstFromList $ map (\v ->
                AstIndexZ (astTranspose permRest v)
                          (appendIndex ix2 ixRest2)) l)
                (singletonIndex i)
    AstFromVector l -> traceRule $
      case permSwapSplit perm0 of
        Nothing ->
          if intVarInAstInt var i1
          then let t = AstFromVector $ V.map (\v ->
                     build1VOccurenceUnknown
                       k (var, AstIndexZ v rest1)) l
               in astGather1 k t (var, i1 :. AstIntVar var :. ZI)
          else AstIndexZ (AstFromVector $ V.map (\v ->
                 build1VOccurenceUnknown
                   k (var, AstIndexZ v rest1)) l) (singletonIndex i1)
        Just (j, permRest) ->
          build1V k (var, t)
         where
          t = case splitAtInt_Index j is of
            (_ :: AstIndex m r, ZI) ->
              let j1 = j - valueOf @m
              in astTranspose ([j1] ++ [1 .. j1 - 1] ++ [0])  -- the swap
                 $ case cmpNat (Proxy @1) (Proxy @n) of
                     EQI -> AstFromVector @(n - 1) $ V.map (\v ->
                              AstIndexZ (astTranspose permRest v) is) l
                     LTI -> AstFromVector @(n - 1) $ V.map (\v ->
                              AstIndexZ (astTranspose permRest v) is) l
                     _ -> error "build1VIx: violattion of an assumption about rank deduced from transposition that deflects a projection"
            (ix2, i :. ixRest2) ->
              -- The swap consumed in getting index i to the first position.
              AstIndexZ (AstFromVector $ V.map (\v ->
                AstIndexZ (astTranspose permRest v)
                          (appendIndex ix2 ixRest2)) l)
                (singletonIndex i)
    AstKonst k2 v -> traceRule $
      -- this is an example term for which vectorization changes
      -- the value of index out of bounds (from 0 to v in this case));
      -- fixing this would complicate terms greatly at no value
      -- for the common case where out of bound does not appear,
      -- as well as for the case where value other than 0 is desired
      case permSwapSplit perm0 of
        Nothing -> build1VIx k (var, v, rest1) []
        Just (j, permRest) ->
          build1V k (var, t)
         where
          t = case splitAtInt_Index j is of
            (_ :: AstIndex m r, ZI) ->
              let j1 = j - valueOf @m
              in astTranspose ([j1] ++ [1 .. j1 - 1] ++ [0])  -- the swap
                 $ case cmpNat (Proxy @1) (Proxy @n) of
                     EQI -> AstKonst @(n - 1) k2
                              (AstIndexZ (astTranspose permRest v) is)
                     LTI -> AstKonst @(n - 1) k2
                              (AstIndexZ (astTranspose permRest v) is)
                     _ -> error "build1VIx: violattion of an assumption about rank deduced from transposition that deflects a projection"
            (ix2, _ :. ixRest2) ->  -- the _ index beta-reduced the konst
              AstIndexZ (astTranspose permRest v) (appendIndex ix2 ixRest2)
                -- this is basically partial evaluation, but in constant
                -- time, unlike evaluating AstFromList, etc.
    AstAppend v w -> traceRule $
      case permSwapSplit perm0 of
        Nothing ->
          let vlen = AstIntConst $ lengthAst v
              is2 = AstIntOp MinusIntOp [i1, vlen] :. rest1
          in build1V k (var, astCond (AstRelInt LsOp [i1, vlen])
                                     (AstIndexZ v is)
                                     (AstIndexZ w is2))
        Just (j, permRest) ->
          build1V k (var, t)
         where
          t = case splitAtInt_Index j is of
            (_ :: AstIndex m r, ZI) ->
              let j1 = j - valueOf @m
              in astTranspose ([j1] ++ [1 .. j1 - 1] ++ [0])  -- the swap
                 $ case cmpNat (Proxy @1) (Proxy @n) of
                     EQI -> AstAppend @(n - 1)
                              (AstIndexZ (astTranspose permRest v) is)
                              (AstIndexZ (astTranspose permRest w) is)
                     LTI -> AstAppend @(n - 1)
                              (AstIndexZ (astTranspose permRest v) is)
                              (AstIndexZ (astTranspose permRest w) is)
                     _ -> error "build1VIx: violattion of an assumption about rank deduced from transposition that deflects a projection"
            (ix2, i :. ixRest2) ->
              -- The swap consumed in getting index i to the first position.
              AstIndexZ
                (AstAppend
                   (AstIndexZ (astTranspose permRest v)
                              (appendIndex ix2 ixRest2))
                   (AstIndexZ (astTranspose permRest w)
                              (appendIndex ix2 ixRest2)))
                (singletonIndex i)
    AstSlice i2 k2 v -> traceRule $
      case permSwapSplit perm0 of
        Nothing ->
          build1VIx
            k (var, v, AstIntOp PlusIntOp [i1, AstIntConst i2] :. rest1) []
        Just (j, permRest) ->
          build1V k (var, t)
         where
          t = case splitAtInt_Index j is of
            (_ :: AstIndex m r, ZI) ->
              let j1 = j - valueOf @m
              in astTranspose ([j1] ++ [1 .. j1 - 1] ++ [0])  -- the swap
                 $ case cmpNat (Proxy @1) (Proxy @n) of
                     EQI -> AstSlice @(n - 1) i2 k2
                              (AstIndexZ (astTranspose permRest v) is)
                     LTI -> AstSlice @(n - 1) i2 k2
                              (AstIndexZ (astTranspose permRest v) is)
                     _ -> error "build1VIx: violattion of an assumption about rank deduced from transposition that deflects a projection"
            (ix2, i :. ixRest2) ->
              -- The swap consumed in getting index i to the first position.
              AstIndexZ
                (AstSlice i2 k2
                   (AstIndexZ (astTranspose permRest v)
                              (appendIndex ix2 ixRest2)))
                (singletonIndex i)
    AstReverse v -> traceRule $
      case permSwapSplit perm0 of
        Nothing ->
          let revIs = AstIntOp MinusIntOp [AstIntConst (lengthAst v - 1), i1]
                      :. rest1
          in build1VIx k (var, v, revIs) []
        Just (j, permRest) ->
          build1V k (var, t)
         where
          t = case splitAtInt_Index j is of
            (_ :: AstIndex m r, ZI) ->
              let j1 = j - valueOf @m
              in astTranspose ([j1] ++ [1 .. j1 - 1] ++ [0])  -- the swap
                 $ case cmpNat (Proxy @1) (Proxy @n) of
                     EQI -> AstReverse @(n - 1)
                              (AstIndexZ (astTranspose permRest v) is)
                     LTI -> AstReverse @(n - 1)
                              (AstIndexZ (astTranspose permRest v) is)
                     _ -> error "build1VIx: violattion of an assumption about rank deduced from transposition that deflects a projection"
            (ix2, i :. ixRest2) ->
              -- The swap consumed in getting index i to the first position.
              AstIndexZ
                (AstReverse
                   (AstIndexZ (astTranspose permRest v)
                              (appendIndex ix2 ixRest2)))
                (singletonIndex i)
    AstTranspose{} -> traceRule $
      case astTranspose perm0 v0 of
        AstTranspose perm v ->
          if length perm > valueOf @m
          then build1VIx k (var, v, is) perm
          else let ix2 = permutePrefixIndex perm is
               in build1VIx k (var, v, ix2) []
        v -> build1VIx k (var, v, is) []
    AstReshape sh v -> traceRule $
      build1VIx k (var, astReshape sh v, is) perm0
    AstBuild1{} -> error "build1VIx: impossible case: AstBuild1"
    AstGather1 @p7 n2  v (var2, ix4) -> traceRule $
      case permSwapSplit perm0 of
        Nothing ->
          let ix3 = fmap (substituteAstInt i1 var2) ix4
          in build1VIxOccurenceUnknown k (var, v, appendIndex ix3 rest1) []
            -- we don't know if var occurs in v; it could have been in ix4
        Just (j, permRest) ->
          build1V k (var, t)
         where
          t = case splitAtInt_Index j is of
            (_ :: AstIndex m r, ZI) ->
              let j1 = j - valueOf @m
                  p = valueOf @p7
                  permRest2 = [0 .. p - 1] ++ map (+ p) permRest
              in astTranspose ([j1] ++ [1 .. j1 - 1] ++ [0])  -- the swap
                 $ case cmpNat (Proxy @1) (Proxy @n) of
                     EQI -> AstGather1 @(p7 + m) @(n - 1)
                                        n2 (astTranspose permRest2 v)
                                       (var2, appendIndex ix4 is)
                     LTI -> AstGather1 @(p7 + m) @(n - 1)
                                       n2 (astTranspose permRest2 v)
                                       (var2, appendIndex ix4 is)
                     _ -> error "build1VIx: violattion of an assumption about rank deduced from transposition that deflects a projection"
            (ix2, i :. ixRest2) ->
              -- The swap consumed in getting index i to the first position.
              -- The index is beta-reduced with the gather's variable.
              let ix3 = fmap (substituteAstInt i var2) ix4
                  v2 = AstIndexZ v ix3
              in AstIndexZ (astTranspose permRest v2)
                           (appendIndex ix2 ixRest2)
    AstGatherN _sh v (Z, ix4) -> traceRule $
      build1VIx k (var, AstIndexZ v ix4, is) perm0
    AstGatherN @m7 @n7 sh v (vars, ix4) -> traceRule $
      let v2 = case cmpNat (Proxy @m) (Proxy @(m7 + n7)) of
            EQI ->
              projectGatherN perm0 is (Z, vars, ix4) v sh []
            LTI -> case sameNat (Proxy @(m7 + n7 - m)) (Proxy @n) of
              Just Refl ->
                projectGatherN perm0 is (Z, vars, ix4) v sh []
              _ -> error "build1VIx: AstGatherN: impossible lack of equality"
            _ ->
              error "build1VIx: AstGatherN: impossible inequality"

      in build1V k (var, v2)

projectGatherN
  :: forall k m1 m2 p n r.
     ( k <= m1 + m2 + n, Show r, Numeric r
     , KnownNat k, KnownNat m1, KnownNat m2, KnownNat p, KnownNat n )
  => Permutation -> AstIndex k r
  -> (AstVarList m1, AstVarList m2, AstIndex p r)
  -> Ast (p + n) r -> ShapeInt (m1 + m2 + n)
  -> [Permutation]
  -> Ast (m1 + m2 + n - k) r
projectGatherN perm0 ZI (varsRev, vars, ix4) v sh permsOuter =
  let vars3 = reverseSized varsRev `appendSized` vars
      v2 = astGatherN sh v (vars3, ix4)
  in foldl' (flip astTranspose) v2 (perm0 : permsOuter)
projectGatherN perm0 ix@(_ :. _) (varsRev, Z, ix4) v sh permsOuter =
  let p = valueOf @p
      permRest2 = [0 .. p - 1] ++ map (+ p) perm0
      v2 = astGatherN sh (astTranspose permRest2 v)
                      (reverseSized varsRev, ix4)
      v3 = AstIndexZ v2 ix  -- this will get recursively reduced elsewhere
  in foldl' (flip astTranspose) v3 permsOuter
projectGatherN perm0 ix@(i1 :. rest1)
               (varsRev, var2 ::: vars, ix4)
               v sh@(_ :$ (sh' :: ShapeInt ksh)) permsOuter =
  case permSwapSplit perm0 of
    Nothing ->
      let ix3 = fmap (substituteAstInt i1 var2) ix4
          vars3 = reverseSized varsRev `appendSized` vars
          v2 = astGatherN sh' v (vars3, ix3)
          v3 = AstIndexZ v2 rest1
                 -- this will get recursively reduced elsewhere
      in foldl' (flip astTranspose) v3 permsOuter
    Just (j, permRest) -> case splitAtInt_Index j ix of
      (_ :: AstIndex k r, ZI) ->
        let j1 = j - valueOf @k
            swap = [j1] ++ [1 .. j1 - 1] ++ [0]
        in projectGatherN permRest ix
                          (var2 ::: varsRev, vars, ix4) v sh (swap : permsOuter)
      (ix2, i :. ixRest2) ->
        -- The swap consumed in getting index i to the first position.
        -- The index is beta-reduced with the first of gather's variables.
        let ix3 = fmap (substituteAstInt i var2) ix4
            ix5 :: AstIndex (k - 1) r
            ix5 = appendIndex ix2 ixRest2
        -- Here the plugin can't derive k - 1 <= m1 + m2 - 1 + n
        -- nor can link the latter to ksh.
        in case cmpNat (Proxy @(k - 1)) (Proxy @ksh) of
          EQI ->
            projectGatherN permRest ix5 (varsRev, vars, ix3) v sh' permsOuter
          LTI ->
            projectGatherN permRest ix5 (varsRev, vars, ix3) v sh' permsOuter
          _ ->
            error "projectGatherN: impossible inequality"
projectGatherN _ _ _ _ _ _ =
  error "projectGatherN: impossible pattern needlessly required"


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
