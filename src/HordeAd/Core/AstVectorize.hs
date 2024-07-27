{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Vectorization of the AST, eliminating the build operation.
module HordeAd.Core.AstVectorize
  ( build1Vectorize, build1VectorizeS, build1VectorizeHVector
  , traceRuleEnabledRef
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (when)
import Data.Array.Internal (valueOf)
import Data.Array.Shape qualified as Sh
import Data.Functor.Const
import Data.Int (Int64)
import Data.IntMap.Strict qualified as IM
import Data.IORef
import Data.List (mapAccumR)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , SomeNat (..)
  , cmpNat
  , someNatVal
  , type (+)
  , type (-)
  )
import System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape qualified as X
import Data.Array.Mixed.Types qualified as X

import HordeAd.Core.Ast hiding (AstBool (..), AstHVector (..), AstTensor (..))
import HordeAd.Core.Ast (AstHVector, AstTensor)
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.Types
import HordeAd.Util.ShapedList
  (pattern (:.$), pattern (::$), pattern ZIS, pattern ZS)
import HordeAd.Util.SizedList

-- * Vectorization of AstRanked

-- This abbreviation is used a lot below.
astTr :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
      => AstTensor s (TKR r (2 + n)) -> AstTensor s (TKR r (2 + n))
astTr = astTranspose [1, 0]

-- | The application @build1Vectorize k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, that is, rewrites it to a term
-- with the same value, but not containing the outermost @AstBuild1@
-- constructor and not increasing (and potentially decreasing)
-- the total number of @AstBuild1@ occuring in the term.
-- If no @AstBuild1@ terms occur in @v@, the resulting term won't
-- have any, either.
build1Vectorize
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => Int -> (IntVarName, AstTensor s (TKR r n)) -> AstTensor s (TKR r (1 + n))
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
      ++ ellipsisString width (printAstSimple renames (AstRanked startTerm))
      ++ "\n"
  let !endTerm = build1VOccurenceUnknown k (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (printAstSimple renames (AstRanked endTerm))
      ++ "\n"
  let !_A = assert (shapeAst startTerm == shapeAst endTerm
                   `blame` "build1Vectorize: term shape changed"
                   `swith`(shapeAst startTerm, shapeAst endTerm)) ()
  return endTerm

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => Int -> (IntVarName, AstTensor s (TKR r n)) -> AstTensor s (TKR r (1 + n))
build1VOccurenceUnknown k (var, v0) =
  let traceRule = mkTraceRule "build1VOcc" (Ast.AstBuild1 k (var, v0)) v0 1
  in if varNameInAst var v0
     then build1V k (var, v0)
     else traceRule $
       astReplicate k v0

-- This is used to avoid biding the same variable twice in the code,
-- (unless in very safe situations, e.g., different branches
-- of an arithmetic expression) which may end up as nested bindings eventually
-- and break our invariants that we need for simplified handling of bindings
-- when rewriting terms.
build1VOccurenceUnknownRefresh
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => Int -> (IntVarName, AstTensor s (TKR r n)) -> AstTensor s (TKR r (1 + n))
{-# NOINLINE build1VOccurenceUnknownRefresh #-}
build1VOccurenceUnknownRefresh k (var, v0) =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !v2 = substituteAst  -- cheap subst, because only a renaming
                (SubstitutionPayload @PrimalSpan astVarFresh) var v0
    in build1VOccurenceUnknown k (varFresh, v2)

intBindingRefresh
  :: IntVarName -> AstIndex n -> (IntVarName, AstInt, AstIndex n)
{-# NOINLINE intBindingRefresh #-}
intBindingRefresh var ix =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !ix2 = substituteAstIndex  -- cheap subst, because only a renaming
                 (SubstitutionPayload @PrimalSpan astVarFresh)
                 var ix
    in (varFresh, astVarFresh, ix2)

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1V
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => Int -> (IntVarName, AstTensor s (TKR r n)) -> AstTensor s (TKR r (1 + n))
build1V k (var, v00) =
  let v0 = astNonIndexStep v00
        -- Almost surely the term will be transformed, so it can just
        -- as well we one-step simplified first (many steps if redexes
        -- get uncovered and so the simplification requires only constant
        -- look-ahead, but has a guaranteed net benefit).
      bv = Ast.AstBuild1 k (var, v0)
      traceRule = mkTraceRule "build1V" bv v0 1
  in case v0 of
    Ast.AstVar _ var2 | varNameToAstVarId var2 == varNameToAstVarId var ->
      case isRankedInt v0 of
        Just Refl -> fromPrimal @s @Int64 $ astSlice 0 k Ast.AstIota
        _ -> error "build1V: build variable is not an index variable"
    Ast.AstVar{} ->
      error "build1V: AstVar can't contain other free index variables"
    Ast.AstPrimalPart v -> traceRule $
      astPrimalPart $ build1V k (var, v)
    Ast.AstDualPart v -> traceRule $
      astDualPart $ build1V k (var, v)
    Ast.AstConstant v -> traceRule $
      Ast.AstConstant $ build1V k (var, v)
    Ast.AstD u u' -> traceRule $
      Ast.AstD (build1VOccurenceUnknown k (var, u))
               (build1VOccurenceUnknown k (var, u'))
    Ast.AstCond b (Ast.AstConstant v) (Ast.AstConstant w) ->
      let t = Ast.AstConstant
              $ astIndexStep (astFromVector $ V.fromList [v, w])
                             (singletonIndex (astCond b 0 1))
      in build1V k (var, t)
    Ast.AstCond b v w ->
      let t = astIndexStep (astFromVector $ V.fromList [v, w])
                           (singletonIndex (astCond b 0 1))
      in build1V k (var, t)

    Ast.AstLetTupleIn var1 var2 p v -> undefined  -- TODO: doable, but complex
{-
      -- See the AstLet and AstLetHVectorIn cases for comments.
      let var1' = mkAstVarName (varNameToAstVarId var1)
          var2' = mkAstVarName (varNameToAstVarId var2)
          sh = shapeAst u
          projection = Ast.AstIndex (Ast.AstVar (k :$: sh) var2)
                                    (Ast.AstIntVar var :.: ZIR)
          -- The subsitutions of projections don't break sharing,
          -- because they don't duplicate variables and the added var
          -- is eventually being eliminated instead of substituted for.
          v2 = substituteAst
                 (SubstitutionPayload @s1 projection) var1 v
      in Ast.AstLetTupleIn var1 var2
                          (build1VOccurenceUnknown k (var, u))
                          (build1VOccurenceUnknownRefresh k (var, v2))
                            -- ensure no duplicated bindings, see below
-}
    Ast.AstLet @_ @_ @y var1 u v | STKR{} <- stensorKind @y ->
      let var2 = mkAstVarName (varNameToAstVarId var1)
          sh = shapeAst u
          v2 = substProjRanked k var sh var1 v
      in astLet var2 (build1VOccurenceUnknown k (var, u))
                     (build1VOccurenceUnknownRefresh k (var, v2))
                        -- ensures no duplicated bindings, see below
    Ast.AstLet{} -> error "TODO"
    Ast.AstShare{} -> error "build1V: AstShare"

    Ast.AstMinIndex v -> Ast.AstMinIndex $ build1V k (var, v)
    Ast.AstMaxIndex v -> Ast.AstMaxIndex $ build1V k (var, v)
    Ast.AstFloor v -> Ast.AstFloor $ build1V k (var, v)
    Ast.AstIota ->
      error "build1V: AstIota can't have free index variables"

    Ast.AstN1 opCode u -> traceRule $
      Ast.AstN1 opCode (build1VOccurenceUnknown k (var, u))
    Ast.AstN2 opCode u v -> traceRule $
      Ast.AstN2 opCode (build1VOccurenceUnknown k (var, u))
                       (build1VOccurenceUnknown k (var, v))
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstR1 opCode u -> traceRule $
      Ast.AstR1 opCode (build1VOccurenceUnknown k (var, u))
    Ast.AstR2 opCode u v -> traceRule $
      Ast.AstR2 opCode (build1VOccurenceUnknown k (var, u))
                       (build1VOccurenceUnknown k (var, v))
    Ast.AstI2 opCode u v -> traceRule $
      Ast.AstI2 opCode (build1VOccurenceUnknown k (var, u))
                       (build1VOccurenceUnknown k (var, v))
    Ast.AstSumOfList args -> traceRule $
      astSumOfList $ map (\v -> build1VOccurenceUnknown k (var, v)) args

    Ast.AstIndex v ix -> traceRule $
      build1VIndex k (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstSum v -> traceRule $
      astSum $ astTr $ build1V k (var, v)
    Ast.AstScatter sh v (vars, ix) -> traceRule $
      -- We use a refreshed var binding in the new scatter expression so as
      -- not to duplicate the var binding from build1VOccurenceUnknown call.
      let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix
      in astScatter (k :$: sh)
                    (build1VOccurenceUnknown k (var, v))
                    (varFresh ::: vars, astVarFresh :.: ix2)

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
      astTranspose (normalizePermutation $ 0 : map succ perm)
                   (build1V k (var, v))
    Ast.AstReshape sh v -> traceRule $
      astReshape (k :$: sh) $ build1V k (var, v)
    Ast.AstBuild1{} -> error "build1V: impossible case of AstBuild1"
    Ast.AstGather sh v (vars, ix) -> traceRule $
      let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix
      in astGatherStep (k :$: sh)
                       (build1VOccurenceUnknown k (var, v))
                       (varFresh ::: vars, astVarFresh :.: ix2)
    Ast.AstCast v -> astCast $ build1V k (var, v)
    Ast.AstFromIntegral v -> astFromIntegral $ build1V k (var, v)
    Ast.AstConst{} ->
      error "build1V: AstConst can't have free index variables"

    Ast.AstProject l p -> case someNatVal $ toInteger k of
      Just (SomeNat @k3 _) ->
        astProject (build1VOccurenceUnknownHVector (SNat @k3) (var, l)) p
      _ -> error "build1V: impossible someNatVal"
    Ast.AstLetHVectorIn vars1 l v -> case someNatVal $ toInteger k of
      Just (SomeNat @k3 _) ->
        -- Here substitution traverses @v@ term tree @length vars@ times.
        --
        -- We lose the type information surrounding var1 twice: first,
        -- because we create a variable with one more dimension,
        -- again, because the original variables might have been marked
        -- with AstShaped and here we require AstRanked.
        let (vOut, varsOut) = substProjVars @k3 var vars1 v
        in astLetHVectorIn
             varsOut (build1VOccurenceUnknownHVector (SNat @k3) (var, l))
                     (build1VOccurenceUnknownRefresh k (var, vOut))
      _ -> error "build1V: impossible someNatVal"
    Ast.AstLetHFunIn var1 f v ->
      -- We take advantage of the fact that f contains no free index
      -- variables (it may contain function variables, though).
      -- If it could contain index variables, e.g., in a conditional
      -- expression, we might need to add projections as above.
      withSNat k $ \snat ->
        astLetHFunIn var1 (build1VHFun snat (var, f)) (build1V k (var, v))
    Ast.AstRFromS @sh1 v -> case someNatVal $ toInteger k of
      Just (SomeNat @k _proxy) ->
        astRFromS @(k ': sh1) $ build1VS (var, v)
      Nothing ->
        error "build1V: impossible someNatVal error"

-- | The application @build1VIndex k (var, v, ix)@ vectorizes
-- the term @AstBuild1 k (var, AstIndex v ix)@, where it's unknown whether
-- @var@ occurs in any of @v@, @ix@.
--
-- We try to push indexing down as far as needed to eliminate any occurrences
-- of @var@ from @v@ (but not necessarily from @ix@), which is enough
-- to replace @AstBuild1@ with @AstGather@ and so complete
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
  :: forall m n s r. (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => Int -> (IntVarName, AstTensor s (TKR r (m + n)), AstIndex m)
  -> AstTensor s (TKR r (1 + n))
build1VIndex k (var, v0, ZIR) = build1VOccurenceUnknown k (var, v0)
build1VIndex k (var, v0, ix@(_ :.: _)) =
  let traceRule = mkTraceRule "build1VIndex"
                              (Ast.AstBuild1 k (var, Ast.AstIndex v0 ix))
                              v0 1
  in if varNameInAst var v0
     then case astIndexStep v0 ix of  -- push deeper
       Ast.AstIndex v1 ZIR -> traceRule $
         build1VOccurenceUnknown k (var, v1)
       v@(Ast.AstIndex @p v1 ix1) -> traceRule $
         let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix1
             ruleD = astGatherStep
                       (k :$: dropShape (shapeAst v1))
                       (build1V k (var, v1))
                       (varFresh ::: ZR, astVarFresh :.: ix2)
         in if varNameInAst var v1
            then case v1 of  -- try to avoid ruleD if not a normal form
              Ast.AstFromVector{} | valueOf @p == (1 :: Int) -> ruleD
              Ast.AstScatter{} -> ruleD
              _ -> build1VOccurenceUnknown k (var, v)  -- not a normal form
            else build1VOccurenceUnknown k (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurenceUnknown k (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStep (k :$: dropShape (shapeAst v0)) v0 (var ::: ZR, ix)


-- * Vectorization of AstShaped

-- TODO: we avoid constraint KnownNat (X.Rank sh) that would infect
-- a lot of AstShaped constructor and from there a lot of the codebase.
-- This should be solved in a cleaner way.
--
-- This abbreviation is used a lot below.
astTrS :: forall n m sh s r.
          (KnownNat n, KnownNat m, KnownShS sh, GoodScalar r, AstSpan s)
       => AstTensor s (TKS r (n ': m ': sh)) -> AstTensor s (TKS r (m ': n ': sh))
astTrS = withListSh (Proxy @sh) $ \_ -> astTransposeS (Permutation.makePerm @'[1, 0])

-- | This works analogously to @build1Vectorize@m.
build1VectorizeS
  :: forall k sh s r. (GoodScalar r, KnownNat k, KnownShS sh, AstSpan s)
  => (IntVarName, AstTensor s (TKS r sh)) -> AstTensor s (TKS r (k ': sh))
{-# NOINLINE build1VectorizeS #-}
build1VectorizeS (var, v0) = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = 1000 * traceWidth
      startTerm = Ast.AstBuild1S @_ @k (var, v0)
      renames = IM.fromList [(1, ""), (2, "")]
  when enabled $ do
    writeIORef traceNestingLevel 0
    hPutStrLnFlush stderr $
      "\n"
      ++ "START of vectorization for term "
      ++ ellipsisString width (printAstSimpleS renames (AstShaped startTerm))
      ++ "\n"
  let !endTerm = build1VOccurenceUnknownS (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (printAstSimpleS renames (AstShaped endTerm))
      ++ "\n"
  return endTerm

build1VOccurenceUnknownS
  :: forall k sh s r. (GoodScalar r, KnownNat k, KnownShS sh, AstSpan s)
  => (IntVarName, AstTensor s (TKS r sh)) -> AstTensor s (TKS r (k ': sh))
build1VOccurenceUnknownS (var, v0) =
  let traceRule = mkTraceRuleS "build1VOccS" (Ast.AstBuild1S (var, v0)) v0 1
  in if varNameInAstS var v0
     then build1VS (var, v0)
     else traceRule $
       astReplicateS v0

build1VOccurenceUnknownRefreshS
  :: forall k sh s r. (GoodScalar r, KnownNat k, KnownShS sh, AstSpan s)
  => (IntVarName, AstTensor s (TKS r sh)) -> AstTensor s (TKS r (k ': sh))
{-# NOINLINE build1VOccurenceUnknownRefreshS #-}
build1VOccurenceUnknownRefreshS (var, v0) =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !v2 = substituteAst  -- cheap subst, because only a renaming
                (SubstitutionPayload @PrimalSpan astVarFresh)
                var v0
    in build1VOccurenceUnknownS (varFresh, v2)

intBindingRefreshS
  :: IntVarName -> AstIndexS sh -> (IntVarName, AstInt, AstIndexS sh)
{-# NOINLINE intBindingRefreshS #-}
intBindingRefreshS var ix =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !ix2 = substituteAstIndexS  -- cheap subst, because only a renaming
                 (SubstitutionPayload @PrimalSpan astVarFresh)
                 var ix
    in (varFresh, astVarFresh, ix2)

build1VS
  :: forall k sh s r. (GoodScalar r, KnownNat k, KnownShS sh, AstSpan s)
  => (IntVarName, AstTensor s (TKS r sh)) -> AstTensor s (TKS r (k ': sh))
build1VS (var, v00) =
  let v0 = astNonIndexStepS v00
        -- Almost surely the term will be transformed, so it can just
        -- as well we one-step simplified first (many steps if redexes
        -- get uncovered and so the simplification requires only constant
        -- look-ahead, but has a guaranteed net benefit).
      bv = Ast.AstBuild1S (var, v0)
      traceRule = mkTraceRuleS "build1VS" bv v0 1
  in case v0 of
    Ast.AstVar{} ->
      error "build1VS: AstVar can't contain free index variables"
    Ast.AstPrimalPart v -> traceRule $
      astPrimalPart $ build1VS (var, v)
    Ast.AstDualPart v -> traceRule $
      astDualPart $ build1VS (var, v)
    Ast.AstConstant v -> traceRule $
      Ast.AstConstant $ build1VS (var, v)
    Ast.AstD u u' -> traceRule $
      Ast.AstD (build1VOccurenceUnknownS (var, u))
               (build1VOccurenceUnknownS (var, u'))
    Ast.AstCond b (Ast.AstConstant v) (Ast.AstConstant w) ->
      let t = Ast.AstConstant
              $ astIndexStepS @'[2] (astFromVectorS $ V.fromList [v, w])
                                    (astCond b 0 1 :.$ ZIS)
      in build1VS (var, t)
    Ast.AstCond b v w ->
      let t = astIndexStepS @'[2] (astFromVectorS $ V.fromList [v, w])
                                  (astCond b 0 1 :.$ ZIS)
      in build1VS (var, t)

    Ast.AstLetTupleInS var1 var2 p v -> undefined  -- TODO: doable, but complex
    Ast.AstLetS @_ @_ @y var1 u v | STKS{} <- stensorKind @y ->
      let var2 = mkAstVarName (varNameToAstVarId var1)
          v2 = substProjShaped @k var var1 v
      in astLetS var2 (build1VOccurenceUnknownS @k (var, u))
                      (build1VOccurenceUnknownRefreshS (var, v2))
    Ast.AstLetS{} -> error "TODO"
    Ast.AstShareS{} -> error "build1VS: AstShareS"

    Ast.AstMinIndexS v -> Ast.AstMinIndexS $ build1VS (var, v)
    Ast.AstMaxIndexS v -> Ast.AstMaxIndexS $ build1VS (var, v)
    Ast.AstFloorS v -> Ast.AstFloorS $ build1VS (var, v)
    Ast.AstIotaS ->
      error "build1VS: AstIotaS can't have free index variables"

    Ast.AstN1S opCode u -> traceRule $
      Ast.AstN1S opCode (build1VOccurenceUnknownS (var, u))
    Ast.AstN2S opCode u v -> traceRule $
      Ast.AstN2S opCode (build1VOccurenceUnknownS (var, u))
                        (build1VOccurenceUnknownS (var, v))
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstR1S opCode u -> traceRule $
      Ast.AstR1S opCode (build1VOccurenceUnknownS (var, u))
    Ast.AstR2S opCode u v -> traceRule $
      Ast.AstR2S opCode (build1VOccurenceUnknownS (var, u))
                        (build1VOccurenceUnknownS (var, v))
    Ast.AstI2S opCode u v -> traceRule $
      Ast.AstI2S opCode (build1VOccurenceUnknownS (var, u))
                        (build1VOccurenceUnknownS (var, v))
    Ast.AstSumOfListS args -> traceRule $
      astSumOfListS $ map (\v -> build1VOccurenceUnknownS (var, v)) args

    Ast.AstIndexS @sh1 v ix -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Take (X.Rank sh1) (sh1 X.++ sh) :~: sh1) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop (X.Rank sh1) (sh1 X.++ sh) :~: sh) $
      withListSh (Proxy @sh1) $ \(_ :: IShR rankSh1) ->
      gcastWith (unsafeCoerce Refl :: rankSh1 :~: X.Rank sh1) $
      build1VIndexS @k @(X.Rank sh1) (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstSumS v -> traceRule $
      astSumS $ astTrS $ build1VS (var, v)
    Ast.AstScatterS @sh2 @p @sh3 v (vars, ix) -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Take (1 + p) (k : sh3) :~: (k : Sh.Take p sh3)) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop (1 + p) (k : sh3) :~: Sh.Drop p sh3) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astScatterS @(k ': sh2) @(1 + p)
                     (build1VOccurenceUnknownS (var, v))
                     (Const varFresh ::$ vars, astVarFresh :.$ ix2)

    Ast.AstFromVectorS l -> traceRule $
      astTrS
      $ astFromVectorS (V.map (\v -> build1VOccurenceUnknownS (var, v)) l)
    Ast.AstReplicateS v -> traceRule $
      astTrS $ astReplicateS $ build1VS (var, v)
    Ast.AstAppendS v w -> traceRule $
      astTrS $ astAppendS (astTrS $ build1VOccurenceUnknownS (var, v))
                          (astTrS $ build1VOccurenceUnknownS (var, w))
    Ast.AstSliceS @i v -> traceRule $
      astTrS $ astSliceS @i $ astTrS $ build1VS (var, v)
    Ast.AstReverseS v -> traceRule $
      astTrS $ astReverseS $ astTrS $ build1VS (var, v)
    Ast.AstTransposeS @perm @sh1 perm v -> traceRule $
      let zsuccPerm :: Permutation.Perm (0 : Permutation.MapSucc perm)
          zsuccPerm = Permutation.permShift1 perm
      in
        gcastWith (unsafeCoerce Refl
                   :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm) (k : sh1) :~: k : sh) $
        gcastWith (unsafeCoerce Refl
                   :: X.Rank (0 : Permutation.MapSucc perm) :~: 1 + X.Rank perm) $
        trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm)
        $ astTransposeS zsuccPerm $ build1VS @k (var, v)
    Ast.AstReshapeS @sh2 v -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Size (k ': sh) :~: Sh.Size (k ': sh2)) $
      astReshapeS $ build1VS (var, v)
    Ast.AstBuild1S{} -> error "build1VS: impossible case of AstBuild1S"
    Ast.AstGatherS @sh2 @p @sh3 v (vars, ix) -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Take (1 + p) (k : sh3) :~: (k : Sh.Take p sh3)) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop (1 + p) (k : sh3) :~: Sh.Drop p sh3) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astGatherStepS @(k ': sh2) @(1 + p)
                        (build1VOccurenceUnknownS @k (var, v))
                        (Const varFresh ::$ vars, astVarFresh :.$ ix2)
    Ast.AstCastS v -> astCastS $ build1VS (var, v)
    Ast.AstFromIntegralS v -> astFromIntegralS $ build1VS (var, v)
    Ast.AstConstS{} ->
      error "build1VS: AstConstS can't have free index variables"

    Ast.AstProjectS l p ->
      astProjectS (build1VOccurenceUnknownHVector (SNat @k) (var, l)) p
    Ast.AstLetHVectorInS vars1 l v ->
      -- See the AstLetHVectorIn case for comments.
      let (vOut, varsOut) = substProjVarsS @k var vars1 v
      in astLetHVectorInS
           varsOut (build1VOccurenceUnknownHVector (SNat @k) (var, l))
                   (build1VOccurenceUnknownRefreshS (var, vOut))
    Ast.AstLetHFunInS var1 f v ->
      -- We take advantage of the fact that f contains no free index vars.
      astLetHFunInS var1 (build1VHFun (SNat @k) (var, f)) (build1VS (var, v))
    Ast.AstSFromR v -> astSFromR $ build1V (valueOf @k) (var, v)

build1VIndexS
  :: forall k p sh s r.
     ( GoodScalar r, KnownNat k, KnownNat p, KnownShS sh, KnownShS (Sh.Take p sh)
     , KnownShS (Sh.Drop p (Sh.Take p sh X.++ Sh.Drop p sh)), AstSpan s )
  => (IntVarName, AstTensor s (TKS r sh), AstIndexS (Sh.Take p sh))
  -> AstTensor s (TKS r (k ': Sh.Drop p sh))
build1VIndexS (var, v0, ZIS) =
  gcastWith (unsafeCoerce Refl :: p :~: 0)
    -- otherwise sh would need to be empty, but then Take gets stuck
    -- so the application of this function wouldn't type-check
  $ build1VOccurenceUnknownS (var, v0)
build1VIndexS (var, v0, ix@(_ :.$ _)) =
  gcastWith (unsafeCoerce Refl :: sh :~: Sh.Take p sh X.++ Sh.Drop p sh) $
  let vTrace = Ast.AstBuild1S (var, Ast.AstIndexS v0 ix)
      traceRule = mkTraceRuleS "build1VIndexS" vTrace v0 1
  in if varNameInAstS var v0
     then case astIndexStepS v0 ix of  -- push deeper
       Ast.AstIndexS v1 ZIS -> traceRule $
         build1VOccurenceUnknownS (var, v1)
       v@(Ast.AstIndexS @sh1 v1 ix1) -> traceRule $
         gcastWith (unsafeCoerce Refl
                    :: k ': sh1 :~: Sh.Take (1 + X.Rank sh1)
                                            (k ': sh1 X.++ Sh.Drop p sh)) $
         gcastWith (unsafeCoerce Refl
                    :: Sh.Drop p sh
                       :~: Sh.Drop (1 + X.Rank sh1)
                                   (k ': sh1 X.++ Sh.Drop p sh)) $
         withListSh (Proxy @sh1) $ \(_ :: IShR rankSh1Plus1) ->
         gcastWith (unsafeCoerce Refl :: rankSh1Plus1 :~: 1 + X.Rank sh1) $
         let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix1
             ruleD = astGatherStepS @'[k] @(1 + X.Rank sh1)
                                    (build1VS @k (var, v1))
                                    (Const varFresh ::$ ZS, astVarFresh :.$ ix2)
             len = length $ shapeT @sh1
         in if varNameInAstS var v1
            then case v1 of  -- try to avoid ruleD if not a normal form
              Ast.AstFromVectorS{} | len == 1 -> ruleD
              Ast.AstScatterS{} -> ruleD
              _ -> build1VOccurenceUnknownS (var, v)  -- not a normal form
            else build1VOccurenceUnknownS (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurenceUnknownS (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStepS v0 (Const var ::$ ZS, ix)


-- * Vectorization of AstHVector

build1VectorizeHVector
  :: forall k s. AstSpan s
  => SNat k -> (IntVarName, AstHVector s) -> AstHVector s
{-# NOINLINE build1VectorizeHVector #-}
build1VectorizeHVector k (var, v0) = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = 1000 * traceWidth
      startTerm = Ast.AstBuildHVector1 k (var, v0)
      renames = IM.fromList [(1, ""), (2, "")]
  when enabled $ do
    writeIORef traceNestingLevel 0
    hPutStrLnFlush stderr $
      "\n"
      ++ "START of vectorization for term "
      ++ ellipsisString width (printAstHVectorSimple renames startTerm)
      ++ "\n"
  let !endTerm = build1VOccurenceUnknownHVector k (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (printAstHVectorSimple renames endTerm)
      ++ "\n"
  let !_A =
        assert (voidHVectorsMatch (shapeAstHVector startTerm)
                                  (shapeAstHVector endTerm)
                `blame` "build1VectorizeHVector: term shape changed"
                `swith` ( shapeVoidHVector (shapeAstHVector startTerm)
                        , shapeVoidHVector (shapeAstHVector endTerm) )) ()
  return endTerm

build1VOccurenceUnknownHVector
  :: forall k s. AstSpan s
  => SNat k -> (IntVarName, AstHVector s) -> AstHVector s
build1VOccurenceUnknownHVector k (var, v0) =
 let traceRule = mkTraceRuleHVector v0 k var
 in if varNameInAstHVector var v0
    then build1VHVector k (var, v0)
    else traceRule $
      fun1DToAst (shapeAstHVector v0) $ \ !vars !asts ->
        astLetHVectorInHVector
          vars v0 (Ast.AstMkHVector
                   $ replicate1HVectorF
                       (\n (AstRanked t) -> AstRanked $ astReplicate n t)
                       (\(AstShaped t) -> AstShaped $ astReplicateS t)
                       k asts)

build1VHVector
  :: forall k s. AstSpan s
  => SNat k -> (IntVarName, AstHVector s) -> AstHVector s
build1VHVector k@SNat (var, v0) =
 let traceRule = mkTraceRuleHVector v0 k var
 in traceRule $ case v0 of
  Ast.AstMkHVector l ->
    Ast.AstMkHVector $ V.map (\u -> build1VOccurenceUnknownDynamic k (var, u)) l
  Ast.AstHApply t ll ->
    astHApply
      (build1VHFun k (var, t))
      (map (V.map (\u -> build1VOccurenceUnknownDynamic k (var, u))) ll)
  Ast.AstLetHVectorInHVector vars1 u v ->
    let (vOut, varsOut) = substProjVarsHVector @k var vars1 v
    in astLetHVectorInHVector
         varsOut (build1VOccurenceUnknownHVector k (var, u))
                 (build1VOccurenceUnknownHVectorRefresh k (var, vOut))
  Ast.AstLetHFunInHVector var1 f v ->
    -- We take advantage of the fact that f contains no free index vars.
    astLetHFunInHVector var1 (build1VHFun k (var, f))
                             (build1VHVector k (var, v))
  Ast.AstLetInHVector @_ @_ @s1 var1 u v ->
    let var2 = mkAstVarName (varNameToAstVarId var1)  -- changed shape; TODO: shall we rename?
        sh = shapeAst u
        projection = Ast.AstIndex (Ast.AstVar (FTKR $ sNatValue k :$: sh) var2)
                                  (Ast.AstIntVar var :.: ZIR)
        v2 = substituteAstHVector
               (SubstitutionPayload @s1 projection) var1 v
    in astLetInHVector var2 (build1VOccurenceUnknown (sNatValue k) (var, u))
                            (build1VOccurenceUnknownHVectorRefresh
                               k (var, v2))
  Ast.AstLetInHVectorS @sh2 @r @s1 var1 u v ->
      let var2 = mkAstVarName (varNameToAstVarId var1)  -- changed shape; TODO: shall we rename?
          projection = Ast.AstIndexS (Ast.AstVar @(TKS r (k ': sh2)) FTKS var2)
                                     (Ast.AstIntVar var :.$ ZIS)
          v2 = substituteAstHVector
                 (SubstitutionPayload @s1 projection) var1 v
      in astLetInHVectorS var2 (build1VOccurenceUnknownS @k (var, u))
                               (build1VOccurenceUnknownHVectorRefresh
                                  k (var, v2))
  Ast.AstShareHVector{} ->
    error "build1VHVector: impossible case of AstShareHVector"
  Ast.AstBuildHVector1{} ->
    error "build1VHVector: impossible case of AstBuildHVector1"
  Ast.AstMapAccumRDer k5 accShs bShs eShs f df rf acc0 es ->
      astTrAstHVectorTail (V.length accShs)
      $ Ast.AstMapAccumRDer
          k5
          (replicate1VoidHVector k accShs)
          (replicate1VoidHVector k bShs)
          (replicate1VoidHVector k eShs)
          (build1VHFun k (var, f))
          (build1VHFun k (var, df))
          (build1VHFun k (var, rf))
          (build1VOccurenceUnknownHVector k (var, acc0))
          (astTrAstHVector $ build1VOccurenceUnknownHVector k (var, es))
  Ast.AstMapAccumLDer k5 accShs bShs eShs f df rf acc0 es ->
      astTrAstHVectorTail (V.length accShs)
      $ Ast.AstMapAccumLDer
          k5
          (replicate1VoidHVector k accShs)
          (replicate1VoidHVector k bShs)
          (replicate1VoidHVector k eShs)
          (build1VHFun k (var, f))
          (build1VHFun k (var, df))
          (build1VHFun k (var, rf))
          (build1VOccurenceUnknownHVector k (var, acc0))
          (astTrAstHVector $ build1VOccurenceUnknownHVector k (var, es))

build1VHFun
  :: forall k. SNat k -> (IntVarName, AstHFun) -> AstHFun
build1VHFun k@SNat (var, v0) = case v0 of
  Ast.AstLambda ~(vvars, l) ->
    -- This handles the case of l having free variable beyond vvars,
    -- which is not possible for lambdas used in folds, etc.
    -- But note that, due to substProjVarsHVector, l2 has var occurences,
    -- so build1VOccurenceUnknownHVectorRefresh is neccessary to handle
    -- them and to eliminate them so that the function is closed again.
    let f acc vars = substProjVarsHVector @k var vars acc
        (l2, vvars2) = mapAccumR f l vvars
    in Ast.AstLambda
         (vvars2, build1VOccurenceUnknownHVectorRefresh k (var, l2))
  Ast.AstVarHFun shss shs var2 ->
    Ast.AstVarHFun (map (replicate1VoidHVector k) shss)
                   (replicate1VoidHVector k shs)
                   var2

build1VOccurenceUnknownDynamic
  :: forall k s. AstSpan s
  => SNat k -> (IntVarName, AstDynamic s) -> AstDynamic s
build1VOccurenceUnknownDynamic k@SNat (var, d) = case d of
  DynamicRanked (AstRanked u) ->
    DynamicRanked $ AstRanked $ build1VOccurenceUnknown (sNatValue k) (var, u)
  DynamicShaped (AstShaped u) ->
    DynamicShaped $ AstShaped $ build1VOccurenceUnknownS @k (var, u)
  DynamicRankedDummy @r @sh _ _ -> DynamicRankedDummy @r @(k ': sh) Proxy Proxy
  DynamicShapedDummy @r @sh _ _ -> DynamicShapedDummy @r @(k ': sh) Proxy Proxy
{- TODO: is this faster? but fromInteger has to be avoided
  DynamicRankedDummy @r @sh _ _ ->
    withListSh (Proxy @sh) $ \_ ->
      DynamicRanked @r (Ast.AstRFromS @(k ': sh) @s @r 0)
  DynamicShapedDummy @r @sh _ _ -> DynamicShaped @r @(k ': sh) 0
-}

build1VOccurenceUnknownHVectorRefresh
  :: forall k s. AstSpan s
  => SNat k -> (IntVarName, AstHVector s) -> AstHVector s
{-# NOINLINE build1VOccurenceUnknownHVectorRefresh #-}
build1VOccurenceUnknownHVectorRefresh k (var, v0) =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !v2 = substituteAstHVector  -- cheap subst, because only a renaming
                (SubstitutionPayload @PrimalSpan astVarFresh)
                var v0
    in build1VOccurenceUnknownHVector k (varFresh, v2)


-- * Auxiliary machinery

substProjRanked :: forall n1 r1 s1 s y.
                   ( KnownNat n1, GoodScalar r1, AstSpan s, AstSpan s1 )
                => Int -> IntVarName -> IShR n1
                -> AstVarName s1 (TKR r1 n1)
                -> AstTensor s y -> AstTensor s y
substProjRanked k var sh1 var1 =
  let var2 = mkAstVarName @s1 @(TKR r1 (1 + n1)) (varNameToAstVarId var1)  -- changed shape; TODO: shall we rename?
      projection =
        Ast.AstIndex (Ast.AstVar (FTKR $ k :$: sh1) var2)
                     (Ast.AstIntVar var :.: ZIR)
  in substituteAst
       (SubstitutionPayload @s1 projection) var1
         -- The subsitutions of projections don't break sharing,
         -- because they don't duplicate variables and the added var
         -- is eventually being eliminated instead of substituted for.

substProjShaped :: forall k sh1 r1 s1 s y.
                   ( KnownNat k, KnownShS sh1, GoodScalar r1
                   , AstSpan s, AstSpan s1 )
                => IntVarName -> AstVarName s1 (TKS r1 sh1)
                -> AstTensor s y -> AstTensor s y
substProjShaped var var1 =
  let var2 = mkAstVarName @s1 @(TKS r1 (k : sh1)) (varNameToAstVarId var1)
      projection =
        Ast.AstIndexS (Ast.AstVar @(TKS r1 (k ': sh1)) FTKS var2)
                      (Ast.AstIntVar var :.$ ZIS)
  in substituteAst
       (SubstitutionPayload @s1 projection) var1

substProjHVector :: forall n1 r1 s1 s.
                    (KnownNat n1, GoodScalar r1, AstSpan s, AstSpan s1)
                 => Int -> IntVarName -> IShR n1
                 -> AstVarName s1 (TKR r1 n1)
                 -> AstHVector s -> AstHVector s
substProjHVector k var sh1 var1 =
  let var2 = mkAstVarName @s1 @(TKR r1 (1 + n1)) (varNameToAstVarId var1)
      projection =
        Ast.AstIndex (Ast.AstVar (FTKR $ k :$: sh1) var2)
                     (Ast.AstIntVar var :.: ZIR)
  in substituteAstHVector
       (SubstitutionPayload @s1 projection) var1

substProjHVectorS :: forall k sh1 r1 s1 s.
                     ( KnownNat k, KnownShS sh1, GoodScalar r1
                     , AstSpan s, AstSpan s1 )
                  => IntVarName -> AstVarName s1 (TKS r1 sh1)
                  -> AstHVector s -> AstHVector s
substProjHVectorS var var1 =
  let var2 = mkAstVarName @s1 @(TKS r1 (k : sh1)) (varNameToAstVarId var1)
      projection =
        Ast.AstIndexS (Ast.AstVar @(TKS r1 (k ': sh1)) FTKS var2)
                      (Ast.AstIntVar var :.$ ZIS)
  in substituteAstHVector
       (SubstitutionPayload @s1 projection) var1

substProjDynamic :: forall k n r s. (KnownNat k, AstSpan s)
                 => IntVarName -> AstTensor s (TKR r n)
                 -> AstDynamicVarName
                 -> (AstTensor s (TKR r n), AstDynamicVarName)
substProjDynamic var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat) =
    ( withListSh (Proxy @sh3) $ \sh1 ->
        substProjRanked @_ @r3 @s
                        (valueOf @k) var sh1 (mkAstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamic var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat]) =
    ( substProjShaped @k @sh3 @r3 @s var (mkAstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamic _ _ _ = error "substProjDynamic: unexpected type"

substProjDynamicS :: forall k sh r s. (KnownNat k, AstSpan s)
                  => IntVarName -> AstTensor s (TKS r sh)
                  -> AstDynamicVarName
                  -> (AstTensor s (TKS r sh), AstDynamicVarName)
substProjDynamicS var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat) =
    ( withListSh (Proxy @sh3) $ \sh1 ->
        substProjRanked @_ @r3 @s
                        (valueOf @k) var sh1 (mkAstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamicS var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat]) =
    ( substProjShaped @k @sh3 @r3 @s var (mkAstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamicS _ _ _ = error "substProjDynamicS: unexpected type"

substProjVars :: forall k n r s. (KnownNat k, AstSpan s)
              => IntVarName -> [AstDynamicVarName]
              -> AstTensor s (TKR r n)
              -> (AstTensor s (TKR r n), [AstDynamicVarName])
substProjVars var vars v3 = mapAccumR (substProjDynamic @k var) v3 vars

substProjVarsS :: forall k sh r s. (KnownNat k, AstSpan s)
               => IntVarName -> [AstDynamicVarName]
               -> AstTensor s (TKS r sh)
               -> (AstTensor s (TKS r sh), [AstDynamicVarName])
substProjVarsS var vars v3 = mapAccumR (substProjDynamicS @k var) v3 vars

substProjDynamicHVector :: forall k s. (KnownNat k, AstSpan s)
                        => IntVarName -> AstHVector s -> AstDynamicVarName
                        -> (AstHVector s, AstDynamicVarName)
substProjDynamicHVector var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat) =
    ( withListSh (Proxy @sh3) $ \sh1 ->
        substProjHVector @_ @r3 @s (valueOf @k) var sh1 (mkAstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamicHVector var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat]) =
    ( substProjHVectorS @k @sh3 @r3 @s var (mkAstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamicHVector _ _ _ =
  error "substProjDynamicHVector: unexpected type"

substProjVarsHVector :: forall k s. (KnownNat k, AstSpan s)
                     => IntVarName -> [AstDynamicVarName]
                     -> AstHVector s
                     -> (AstHVector s, [AstDynamicVarName])
substProjVarsHVector var vars v3 =
  mapAccumR (substProjDynamicHVector @k var) v3 vars

astTrDynamic :: AstSpan s
             => DynamicTensor (AstRanked s) -> DynamicTensor (AstRanked s)
astTrDynamic t@(DynamicRanked @_ @n1 (AstRanked u)) =
  case cmpNat (Proxy @2) (Proxy @n1) of
    EQI -> DynamicRanked $ AstRanked $ astTr @(n1 - 2) u
    LTI -> DynamicRanked $ AstRanked $ astTr @(n1 - 2) u
    _ -> t
astTrDynamic t@(DynamicShaped @_ @sh (AstShaped u)) =
  let sh1 = shapeT @sh
      permute10 (m0 : m1 : ms) = m1 : m0 : ms
      permute10 ms = ms
      sh1Permuted = permute10 sh1
  in withShapeP sh1Permuted $ \(Proxy @shPermuted) ->
       withListSh (Proxy @sh) $ \_ ->
         case cmpNat (Proxy @2) (Proxy @(X.Rank sh)) of
           EQI -> case astTransposeS (Permutation.makePerm @'[1, 0]) u of
             (w :: AstTensor s4 (TKS r4 sh4)) ->
               gcastWith (unsafeCoerce Refl :: sh4 :~: shPermuted) $
               DynamicShaped $ AstShaped w
           LTI -> case astTransposeS (Permutation.makePerm @'[1, 0]) u of
             (w :: AstTensor s4 (TKS r4 sh4)) ->
               gcastWith (unsafeCoerce Refl :: sh4 :~: shPermuted) $
               DynamicShaped $ AstShaped w
           _ -> t
astTrDynamic (DynamicRankedDummy p1 (Proxy @sh1)) =
  let permute10 (m0 : m1 : ms) = m1 : m0 : ms
      permute10 ms = ms
      sh1Permuted = permute10 $ shapeT @sh1
  in withShapeP sh1Permuted $ \proxy ->
       DynamicRankedDummy p1 proxy
astTrDynamic (DynamicShapedDummy p1 (Proxy @sh1)) =
  let permute10 (m0 : m1 : ms) = m1 : m0 : ms
      permute10 ms = ms
      sh1Permuted = permute10 $ shapeT @sh1
  in withShapeP sh1Permuted $ \proxy ->
       DynamicShapedDummy p1 proxy

astTrAstHVector :: forall s. AstSpan s
                => AstHVector s -> AstHVector s
astTrAstHVector t = fun1DToAst (shapeAstHVector t) $ \ !vars !asts ->
  Ast.AstLetHVectorInHVector
    vars
    t
    (Ast.AstMkHVector @s $ V.map astTrDynamic asts)

astTrAstHVectorTail :: forall s. AstSpan s
                    => Int -> AstHVector s -> AstHVector s
astTrAstHVectorTail i t = fun1DToAst (shapeAstHVector t) $ \ !vars !asts ->
  Ast.AstLetHVectorInHVector
    vars
    t
    (Ast.AstMkHVector @s $ V.take i asts
                           V.++ V.map astTrDynamic (V.drop i asts))


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

mkTraceRule :: (KnownNat n, GoodScalar r, AstSpan s)
            => String -> AstTensor s (TKR r n) -> AstTensor s (TKR r m) -> Int
            -> AstTensor s (TKR r n)
            -> AstTensor s (TKR r n)
{-# NOINLINE mkTraceRule #-}
mkTraceRule prefix from caseAnalysed nwords to = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = traceWidth
      renames = IM.fromList [(1, ""), (2, "")]
      constructorName =
        unwords $ take nwords $ words $ take 20
        $ printAstSimple renames (AstRanked caseAnalysed)
      ruleName = prefix ++ "." ++ constructorName
      ruleNamePadded = take 20 $ ruleName ++ repeat ' '
  when enabled $ do
    nestingLevel <- readIORef traceNestingLevel
    modifyIORef' traceNestingLevel succ
    let paddedNesting = take 3 $ show nestingLevel ++ repeat ' '
    -- Force in the correct order:
    let !stringFrom = printAstSimple renames (AstRanked from)
    let !stringTo = printAstSimple renames (AstRanked to)
    hPutStrLnFlush stderr $ paddedNesting ++ "rule " ++ ruleNamePadded
                            ++ " sends " ++ padString width stringFrom
                            ++ " to " ++ padString width stringTo
    modifyIORef' traceNestingLevel pred
  let !_A = assert (shapeAst from == shapeAst to
                    `blame` "mkTraceRule: term shape changed"
                    `swith`(shapeAst from, shapeAst to, from, to)) ()
  return $! to

mkTraceRuleS :: forall sh sh2 s r. AstSpan s
             => String -> AstTensor s (TKS r sh) -> AstTensor s (TKS r sh2) -> Int
             -> AstTensor s (TKS r sh) -> AstTensor s (TKS r sh)
{-# NOINLINE mkTraceRuleS #-}
mkTraceRuleS prefix from caseAnalysed nwords to = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = traceWidth
      renames = IM.fromList [(1, ""), (2, "")]
      constructorName =
        unwords $ take nwords $ words $ take 20
        $ printAstSimpleS renames (AstShaped caseAnalysed)
      ruleName = prefix ++ "." ++ constructorName
      ruleNamePadded = take 20 $ ruleName ++ repeat ' '
  when enabled $ do
    nestingLevel <- readIORef traceNestingLevel
    modifyIORef' traceNestingLevel succ
    let paddedNesting = take 3 $ show nestingLevel ++ repeat ' '
    -- Force in the correct order:
    let !stringFrom = printAstSimpleS renames (AstShaped from)
    let !stringTo = printAstSimpleS renames (AstShaped to)
    hPutStrLnFlush stderr $ paddedNesting ++ "rule " ++ ruleNamePadded
                            ++ " sends " ++ padString width stringFrom
                            ++ " to " ++ padString width stringTo
    modifyIORef' traceNestingLevel pred
  return $! to

mkTraceRuleHVector :: AstSpan s
                   => AstHVector s -> SNat k -> IntVarName -> AstHVector s
                   -> AstHVector s
{-# NOINLINE mkTraceRuleHVector #-}
mkTraceRuleHVector from k var to = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = traceWidth
      renames = IM.fromList [(1, ""), (2, "")]
      ruleName = "build1VHVector"
      ruleNamePadded = take 20 $ ruleName ++ repeat ' '
  when enabled $ do
    nestingLevel <- readIORef traceNestingLevel
    modifyIORef' traceNestingLevel succ
    let paddedNesting = take 3 $ show nestingLevel ++ repeat ' '
    let !stringFrom = printAstHVectorSimple renames from
    let !stringTo = printAstHVectorSimple renames to
    hPutStrLnFlush stderr $ paddedNesting ++ "rule " ++ ruleNamePadded
                            ++ " sends "
                            ++ padString width
                                 ("build " ++ show (sNatValue k) ++ " ("
                                  ++ printAstIntVarName renames var ++ ") "
                                  ++  stringFrom)
                            ++ " to " ++ padString width stringTo
  modifyIORef' traceNestingLevel pred
  return $! to

hPutStrLnFlush :: Handle -> String -> IO ()
hPutStrLnFlush target s = do
  hFlush stdout >> hFlush stderr
  hPutStrLn target s
  hFlush stdout >> hFlush stderr
