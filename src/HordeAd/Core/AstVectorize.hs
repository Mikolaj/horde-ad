{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Vectorization of the AST, eliminating the build operation.
module HordeAd.Core.AstVectorize
  ( build1Vectorize, traceRuleEnabledRef
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (when)
import Data.Functor.Const
import Data.IntMap.Strict qualified as IM
import Data.IORef
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Type.Ord (Compare)
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, type (+))
import System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  ( IShX
  , IxS (..)
  , KnownShS (..)
  , KnownShX (..)
  , ListS (..)
  , Rank
  , ShS (..)
  , type (++)
  )
import Data.Array.Nested.Internal.Shape
  (shrRank, shsAppend, shsLength, shsPermutePrefix, shsRank, withKnownShS)

import HordeAd.Core.Ast (AstTensor)
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The top-level wrapper

-- | The application @build1Vectorize k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, that is, rewrites it to a term
-- with the same value, but not containing the outermost @AstBuild1@
-- constructor and not increasing (and potentially decreasing)
-- the total number of @AstBuild1@ occuring in the term.
-- If no @AstBuild1@ terms occur in @v@, the resulting term won't
-- have any, either.
build1Vectorize
  :: forall y k s. (TensorKind y, AstSpan s)
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y) -> AstTensor AstMethodLet s (BuildTensorKind k y)
{-# NOINLINE build1Vectorize #-}
build1Vectorize snat@SNat (var, v0)
 | Dict <- lemTensorKindOfBuild snat (stensorKind @y) = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = 1000 * traceWidth
      startTerm = Ast.AstBuild1 snat (var, v0)
      renames = IM.fromList [(1, ""), (2, "")]
  when enabled $ do
    writeIORef traceNestingLevel 0
    hPutStrLnFlush stderr $
      "\n"
      ++ "START of vectorization for term "
      ++ ellipsisString width (printAstSimple renames startTerm)
      ++ "\n"
  let !endTerm = build1VOccurenceUnknown snat (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (printAstSimple renames endTerm)
      ++ "\n"
  let !_A = assert (ftkAst startTerm == ftkAst endTerm
                   `blame` "build1Vectorize: term shape changed"
                   `swith`( ftkAst startTerm
                          , ftkAst endTerm) ) ()
  return endTerm


-- * Vectorization

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: forall y k s. (TensorKind y, AstSpan s)
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y) -> AstTensor AstMethodLet s (BuildTensorKind k y)
build1VOccurenceUnknown snat@SNat (var, v00)
  | Dict <- lemTensorKindOfBuild snat (stensorKind @y) =
    let v0 = astNonIndexStep v00
          -- Almost surely the term will be transformed, so it can just
          -- as well we one-step simplified first (many steps if redexes
          -- get uncovered and so the simplification requires only constant
          -- look-ahead, but has a guaranteed net benefit).
        traceRule = mkTraceRule "build1VOcc" (Ast.AstBuild1 snat (var, v0)) v0 1
    in if varNameInAst var v0
       then build1V snat (var, v0)
       else traceRule $
         astReplicate snat stensorKind v0

-- This is used to avoid biding the same variable twice in the code,
-- (unless in very safe situations, e.g., different branches
-- of an arithmetic expression) which may end up as nested bindings eventually
-- and break our invariants that we need for simplified handling of bindings
-- when rewriting terms.
build1VOccurenceUnknownRefresh
  :: forall y k s. (TensorKind y, AstSpan s)
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y) -> AstTensor AstMethodLet s (BuildTensorKind k y)
{-# NOINLINE build1VOccurenceUnknownRefresh #-}
build1VOccurenceUnknownRefresh snat@SNat (var, v0) =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !v2 = substituteAst  -- cheap subst, because only a renaming
                astVarFresh var v0
    in build1VOccurenceUnknown snat (varFresh, v2)

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
--
-- We can't simplify the argument term here, because it may eliminate
-- the index variable. We simplify only in 'build1VOccurenceUnknown'.
build1V
  :: forall y k s. (TensorKind y, AstSpan s)
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
build1V snat@SNat (var, v0) =
  let bv = Ast.AstBuild1 snat (var, v0)
      traceRule | Dict <- lemTensorKindOfBuild snat (stensorKind @y) =
        mkTraceRule "build1V" bv v0 1
  in case v0 of
    Ast.AstPair @x @z t1 t2
      | Dict <- lemTensorKindOfBuild snat (stensorKind @x)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z) -> traceRule $
        astPair (build1VOccurenceUnknown snat (var, t1))
                (build1VOccurenceUnknown snat (var, t2))
    Ast.AstProject1 @_ @z t
      | Dict <- lemTensorKindOfBuild snat (stensorKind @z)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @y) -> traceRule $
        astProject1 (build1V snat (var, t))
    Ast.AstProject2 @x t
      | Dict <- lemTensorKindOfBuild snat (stensorKind @x)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @y) -> traceRule $
        astProject2 (build1V snat (var, t))
    Ast.AstFromVector @y2 snat1@(SNat @k1) l
     | Dict <- lemTensorKindOfBuild snat (stensorKind @y2) -> traceRule $
      astTrBuild @k1 @k (stensorKind @y2)
      $ astFromVector snat1 (V.map (\v ->
          build1VOccurenceUnknown snat (var, v)) l)
    Ast.AstSum (SNat @k1) stk v
      | Dict <- lemTensorKindOfBuild (SNat @k1) stk
      , Dict <- lemTensorKindOfBuild (SNat @k) stk -> traceRule $
         astSum (SNat @k1) stensorKind
         $ astTrBuild @k @k1 stk $ build1V snat (var, v)
    Ast.AstReplicate snat2@(SNat @k2) stk v
      | Dict <- lemTensorKindOfSTK stk
      , Dict <- lemTensorKindOfBuild snat stk -> traceRule $
        astTrBuild @k2 stk
        $ astReplicate snat2 stensorKind $ build1V snat (var, v)
    Ast.AstMapAccumRDer @accShs @bShs @eShs @k5
                        k5@SNat bShs eShs f df rf acc0 es
     | Dict <- lemTensorKindOfBuild snat (stensorKind @accShs)
     , Dict <- lemTensorKindOfBuild snat (stensorKind @eShs)
     , Dict <- lemTensorKindOfBuild (SNat @k5) (stensorKind @eShs)
     , Dict <- lemTensorKindOfBuild snat (stensorKind @bShs)
     , Dict <- lemTensorKindOfBuild (SNat @k5) (stensorKind @bShs)
     , Dict <- lemTensorKindOfBuild
                         snat (stensorKind @(BuildTensorKind k5 bShs))
     , Dict <- lemTensorKindOfBuild
                         (SNat @k5) (stensorKind @(BuildTensorKind k bShs))
     , Dict <- lemTensorKindOfAD (stensorKind @accShs)
     , Dict <- lemTensorKindOfAD (stensorKind @bShs)
     , Dict <- lemTensorKindOfAD (stensorKind @eShs)
     , Refl <- lemBuildOfAD snat (stensorKind @accShs)
     , Refl <- lemBuildOfAD snat (stensorKind @bShs)
     , Refl <- lemBuildOfAD snat (stensorKind @eShs) -> traceRule $
      astLetFun
        (astMapAccumRDer
           k5
           (buildFTK snat bShs)
           (buildFTK snat eShs)
           (build1VHFun snat (var, f))
           (build1VHFun snat (var, df))
           (build1VHFun snat (var, rf))
           (build1VOccurenceUnknown snat (var, acc0))
           (astTrBuild @k @k5 (stensorKind @eShs)
            $ build1VOccurenceUnknown snat (var, es)))
        (\x1bs1 -> astPair (astProject1 x1bs1)
                           (astTrBuild @k5 @k
                                       (stensorKind @bShs) (astProject2 x1bs1)))
    Ast.AstMapAccumLDer @accShs @bShs @eShs @k5
                        k5@SNat bShs eShs f df rf acc0 es
     | Dict <- lemTensorKindOfBuild snat (stensorKind @accShs)
     , Dict <- lemTensorKindOfBuild snat (stensorKind @eShs)
     , Dict <- lemTensorKindOfBuild (SNat @k5) (stensorKind @eShs)
     , Dict <- lemTensorKindOfBuild snat (stensorKind @bShs)
     , Dict <- lemTensorKindOfBuild (SNat @k5) (stensorKind @bShs)
     , Dict <- lemTensorKindOfBuild
                         snat (stensorKind @(BuildTensorKind k5 bShs))
     , Dict <- lemTensorKindOfBuild
                         (SNat @k5) (stensorKind @(BuildTensorKind k bShs))
     , Dict <- lemTensorKindOfAD (stensorKind @accShs)
     , Dict <- lemTensorKindOfAD (stensorKind @bShs)
     , Dict <- lemTensorKindOfAD (stensorKind @eShs)
     , Refl <- lemBuildOfAD snat (stensorKind @accShs)
     , Refl <- lemBuildOfAD snat (stensorKind @bShs)
     , Refl <- lemBuildOfAD snat (stensorKind @eShs) -> traceRule $
      astLetFun
        (astMapAccumLDer
           k5
           (buildFTK snat bShs)
           (buildFTK snat eShs)
           (build1VHFun snat (var, f))
           (build1VHFun snat (var, df))
           (build1VHFun snat (var, rf))
           (build1VOccurenceUnknown snat (var, acc0))
           (astTrBuild @k @k5 (stensorKind @eShs)
            $ build1VOccurenceUnknown snat (var, es)))
        (\x1bs1 -> astPair (astProject1 x1bs1)
                           (astTrBuild @k5 @k
                                       (stensorKind @bShs) (astProject2 x1bs1)))
    Ast.AstApply @x @z t ll
      | Dict <- lemTensorKindOfBuild snat (stensorKind @x)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z) -> traceRule $
        astApply
          (build1VHFun snat (var, t))
          (build1VOccurenceUnknown snat (var, ll))
    Ast.AstVar _ var2 -> traceRule $
      if varNameToAstVarId var2 == varNameToAstVarId var
      then case isTensorInt v0 of
        Just Refl -> fromPrimal @s $ Ast.AstIotaS @k
        _ -> error "build1V: build variable is not an index variable"
      else error "build1V: AstVar can't contain other free variables"
    Ast.AstCond b u v -> traceRule $
      let uv = astFromVector (SNat @2) (V.fromList [u, v])
          t = astIndexBuild (SNat @2) (stensorKind @y) uv (astCond b 0 1)
      in build1VOccurenceUnknown snat (var, t)
    Ast.AstBuild1 snat2 (var2, v2) -> traceRule $
      assert (var2 /= var) $
      build1VOccurenceUnknown snat (var, build1VOccurenceUnknown snat2 (var2, v2))
        -- happens only when testing and mixing different pipelines
    Ast.AstConcrete{} ->
      error "build1V: AstConcrete can't have free index variables"

    Ast.AstLet @y2 var1 u v
      | Dict <- lemTensorKindOfBuild snat (stensorKind @y2)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @y) -> traceRule $
        let ftk2 = ftkAst u
            (var3, _ftk3, v2) =
              substProjRep snat var ftk2 var1 v
        in astLet var3 (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknownRefresh snat (var, v2))
             -- ensures no duplicated bindings, see below

    Ast.AstPrimalPart v
      | Dict <- lemTensorKindOfBuild snat (stensorKind @y) -> traceRule $
        astPrimalPart $ build1V snat (var, v)
    Ast.AstDualPart v
      | Dict <- lemTensorKindOfBuild snat (stensorKind @y) -> traceRule $
        astDualPart $ build1V snat (var, v)
    Ast.AstFromPrimal v | Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
      traceRule $
        Ast.AstFromPrimal $ build1V snat (var, v)
    Ast.AstFromDual v | Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
      traceRule $
        Ast.AstFromDual $ build1V snat (var, v)

    Ast.AstSumOfList stk args
     | Dict <- lemTensorKindOfBuild snat stk -> traceRule $
      astSumOfList stensorKind
      $ map (\v -> build1VOccurenceUnknown snat (var, v)) args

    Ast.AstN1K opCode u -> traceRule $
      Ast.AstN1S opCode (build1V snat (var, u))
    Ast.AstN2K opCode u v -> traceRule $
      Ast.AstN2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstR1K opCode u -> traceRule $
      Ast.AstR1S opCode (build1V snat (var, u))
    Ast.AstR2K opCode u v -> traceRule $
      Ast.AstR2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
    Ast.AstI2K opCode u v -> traceRule $
      Ast.AstI2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
    Ast.AstFloorK v -> traceRule $
     Ast.AstFloorS $ build1V snat (var, v)
    Ast.AstFromIntegralK v -> traceRule $
      astFromIntegralS $ build1V snat (var, v)
    Ast.AstCastK v -> traceRule $
      astCastS $ build1V snat (var, v)

    Ast.AstN1S opCode u -> traceRule $
      Ast.AstN1S opCode (build1V snat (var, u))
    Ast.AstN2S opCode u v -> traceRule $
      Ast.AstN2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstR1S opCode u -> traceRule $
      Ast.AstR1S opCode (build1V snat (var, u))
    Ast.AstR2S opCode u v -> traceRule $
      Ast.AstR2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
    Ast.AstI2S opCode u v -> traceRule $
      Ast.AstI2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
    Ast.AstFloorS v -> traceRule $
      Ast.AstFloorS $ build1V snat (var, v)
    Ast.AstFromIntegralS v -> traceRule $
      astFromIntegralS $ build1V snat (var, v)
    Ast.AstCastS v -> traceRule $
      astCastS $ build1V snat (var, v)

    Ast.AstIndexS @sh1 @sh2 v ix -> traceRule $ case stensorKind @y of
     STKS @sh _ _ | SNat <- shsRank (knownShS @sh1) ->
      withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
      gcastWith (unsafeCoerceRefl
                 :: Take (Rank sh1) (sh1 ++ sh) :~: sh1) $
      gcastWith (unsafeCoerceRefl
                 :: Drop (Rank sh1) (sh1 ++ sh) :~: sh) $
      build1VIndexS @k @(Rank sh1) (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstScatterS @shm @shn @shp v (vars, ix) -> traceRule $
      withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astScatterS @(k ': shm) @shn @(k ': shp)
                     (build1VOccurenceUnknown snat (var, v))
                     (Const varFresh ::$ vars, astVarFresh :.$ ix2)
    Ast.AstGatherS @shm @shn @shp v (vars, ix) -> traceRule $
      withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astGatherStepS @(k ': shm) @shn @(k ': shp)
                        (build1VOccurenceUnknown snat (var, v))
                        (Const varFresh ::$ vars, astVarFresh :.$ ix2)
    Ast.AstMinIndexS v -> traceRule $
      Ast.AstMinIndexS $ build1V snat (var, v)
    Ast.AstMaxIndexS v -> traceRule $
      Ast.AstMaxIndexS $ build1V snat (var, v)
    Ast.AstIotaS ->
      error "build1V: AstIotaS can't have free index variables"
    Ast.AstAppendS v w -> traceRule $
      astTrS $ astAppendS (astTrS $ build1VOccurenceUnknown snat (var, v))
                          (astTrS $ build1VOccurenceUnknown snat (var, w))
    Ast.AstSliceS @i v -> traceRule $
      astTrS $ astSliceS @i $ astTrS $ build1V snat (var, v)
    Ast.AstReverseS v -> traceRule $
      astTrS $ astReverseS $ astTrS $ build1V snat (var, v)
    Ast.AstTransposeS @perm @sh1 perm v -> traceRule $ case stensorKind @y of
     STKS @sh _ _ ->
      let zsuccPerm :: Permutation.Perm (0 : Permutation.MapSucc perm)
          zsuccPerm = Permutation.permShift1 perm
      in
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm) (k : sh1) :~: k : sh) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (0 : Permutation.MapSucc perm) :~: 1 + Rank perm) $
        trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm)
        $ astTransposeS zsuccPerm $ build1V snat (var, v)
    Ast.AstReshapeS v -> traceRule $
      astReshapeS $ build1V snat (var, v)
    Ast.AstZipS v -> traceRule $
      Ast.AstZipS $ build1V snat (var, v)
    Ast.AstUnzipS v -> traceRule $
      Ast.AstUnzipS $ build1V snat (var, v)
    Ast.AstNestS @sh1 @sh2 v -> traceRule $
      withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
      astNestS $ build1V snat (var, v)
    Ast.AstUnNestS v -> traceRule $ astUnNestS $ build1V snat (var, v)

    Ast.AstFromS stkz v
      | Dict <- lemTensorKindOfSTK (ftkToStk (ftkAst v)) -> traceRule $
        astFromS (buildSTK snat stkz) $ build1V snat (var, v)
    Ast.AstSFromK t -> build1V snat (var, t)
    Ast.AstSFromR v -> traceRule $ astSFromR $ build1V snat (var, v)
    Ast.AstSFromX v -> traceRule $ astSFromX $ build1V snat (var, v)

    Ast.AstReplicate0NS{} -> error "build1V: term not accessible from user API"
    Ast.AstSum0S{} -> error "build1V: term not accessible from user API"
    Ast.AstDot0S{} -> error "build1V: term not accessible from user API"
    Ast.AstDot1InS{} -> error "build1V: term not accessible from user API"
    Ast.AstMatvecmulS{} -> error "build1V: term not accessible from user API"
    Ast.AstMatmul2S{} -> error "build1V: term not accessible from user API"

intBindingRefreshS
  :: IntVarName -> AstIxS AstMethodLet sh
  -> (IntVarName, AstInt AstMethodLet, AstIxS AstMethodLet sh)
{-# NOINLINE intBindingRefreshS #-}
intBindingRefreshS var ix =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !ix2 = substituteAstIxS  -- cheap subst, because only a renaming
                 astVarFresh
                 var ix
    in (varFresh, astVarFresh, ix2)

-- | The application @build1VIndex snat (var, v, ix)@ vectorizes
-- the term @AstBuild1 snat (var, AstIndex v ix)@, where it's unknown whether
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
build1VIndexS
  :: forall k p sh s r.
     ( TensorKind r, KnownNat k, KnownShS sh, KnownShS (Take p sh)
     , KnownShS (Drop p (Take p sh ++ Drop p sh)), AstSpan s )
  => ( IntVarName
     , AstTensor AstMethodLet s (TKS2 sh r)
     , AstIxS AstMethodLet (Take p sh) )
  -> AstTensor AstMethodLet s (TKS2 (k ': Drop p sh) r)
build1VIndexS (var, v0, ZIS) =
  gcastWith (unsafeCoerceRefl :: p :~: 0)
    -- otherwise sh would need to be empty, but then Take gets stuck
    -- so the application of this function wouldn't type-check
  $ build1VOccurenceUnknown (SNat @k) (var, v0)
build1VIndexS (var, v0, ix@(_ :.$ _)) =
  gcastWith (unsafeCoerceRefl :: sh :~: Take p sh ++ Drop p sh) $
  let vTrace = Ast.AstBuild1 (SNat @k) (var, Ast.AstIndexS v0 ix)
      traceRule = mkTraceRule "build1VIndexS" vTrace v0 1
  in if varNameInAst var v0
     then case astIndexStepS v0 ix of  -- push deeper
       Ast.AstIndexS v1 ZIS -> traceRule $
         build1VOccurenceUnknown (SNat @k) (var, v1)
       v@(Ast.AstIndexS @sh1 @sh2 v1 ix1) -> traceRule $
         withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
         let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix1
             ruleD = astGatherStepS @'[k] @sh2 @(k ': sh1)
                                    (build1VOccurenceUnknown (SNat @k) (var, v1))
                                    (Const varFresh ::$ ZS, astVarFresh :.$ ix2)
             len = shsLength $ knownShS @sh1
         in if varNameInAst var v1
            then case v1 of  -- try to avoid ruleD if not a normal form
              Ast.AstFromVector{} | len == 1 -> ruleD
              Ast.AstScatterS{} -> ruleD
              Ast.AstSFromR{} -> ruleD
              Ast.AstSFromX{} -> ruleD
              _ -> build1VOccurenceUnknown (SNat @k) (var, v)  -- not a normal form
            else build1VOccurenceUnknown (SNat @k) (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurenceUnknown (SNat @k) (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStepS v0 (Const var ::$ ZS, ix)

build1VHFun
  :: forall k x y. (TensorKind x, TensorKind y)
  => SNat k -> (IntVarName, AstHFun x y)
  -> AstHFun (BuildTensorKind k x) (BuildTensorKind k y)
build1VHFun snat@SNat (var, v0) = case v0 of
  Ast.AstLambda ~(var1, ftk, l)
    | Dict <- lemTensorKindOfBuild snat (stensorKind @x) ->
      -- This handles the case of l having free variables beyond var1,
      -- which is not possible for lambdas used in folds, etc.
      -- But note that, due to substProjVars, l2 has var occurences,
      -- so build1VOccurenceUnknownRefresh is neccessary to handle
      -- them and to eliminate them so that the function is closed again.
      let (var2, ftk2, l2) = substProjRep snat var ftk var1 l
      in Ast.AstLambda
           (var2, ftk2, build1VOccurenceUnknownRefresh snat (var, l2))


-- * Auxiliary operations

astTr :: forall n s r. (TensorKind r, AstSpan s)
      => AstTensor AstMethodLet s (TKR2 (2 + n) r)
      -> AstTensor AstMethodLet s (TKR2 (2 + n) r)
astTr a = case ftkAst a of
  FTKR @_ @x sh' _  | SNat <- shrRank sh' ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      Permutation.permFromList [1, 0] $ \(perm :: Permutation.Perm perm) ->
        gcastWith (unsafeCoerceRefl :: Compare (Rank perm) (Rank sh) :~: LT) $
        trustMeThisIsAPermutation @perm $
        case shsPermutePrefix perm sh of
          (_ :: ShS sh2) ->
            withKnownShS sh $
            gcastWith (unsafeCoerceRefl :: Rank sh2 :~: Rank sh) $
            astFromS @(TKS2 sh2 x) (stensorKind @(TKR2 (2 + n) r))
            . astTransposeS perm . astSFromR @sh $ a

astTrS :: forall n m sh s r.
          (KnownNat n, KnownNat m, KnownShS sh, TensorKind r, AstSpan s)
       => AstTensor AstMethodLet s (TKS2 (n ': m ': sh) r)
       -> AstTensor AstMethodLet s (TKS2 (m ': n ': sh) r)
astTrS | SNat <- shsRank (knownShS @sh) =
  astTransposeS (Permutation.makePerm @'[1, 0])

astTrX :: forall n m shx s r.
          (KnownNat n, KnownNat m, KnownShX shx, TensorKind r, AstSpan s)
       => AstTensor AstMethodLet s (TKX2 (Just n ': Just m ': shx) r)
       -> AstTensor AstMethodLet s (TKX2 (Just m ': Just n ': shx) r)
astTrX a = case Permutation.makePerm @'[1, 0] of
  (perm :: Permutation.Perm perm) -> case ftkAst a of
    FTKX @sh' @x sh' _ -> case shxPermutePrefix perm sh' of
      (sh2' :: IShX sh2') ->
        withKnownShX (ssxFromShape sh2') $
        withCastXS sh' $ \(sh :: ShS sh) ->
        withCastXS sh2' $ \(_ :: ShS sh2) ->
          gcastWith (unsafeCoerceRefl :: Compare (Rank perm) (Rank sh) :~: LT) $
          withKnownShS sh $
          gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm sh :~: sh2) $
          astFromS @(TKS2 sh2 x)
                   (stensorKind @(TKX2 (Just m ': Just n ': shx) r))
          . astTransposeS perm . astSFromX @sh @sh' $ a

astTrBuild
  :: forall k1 k2 s y. (AstSpan s, KnownNat k1, KnownNat k2)
  => STensorKind y
  -> AstTensor AstMethodLet s (BuildTensorKind k1 (BuildTensorKind k2 y))
  -> AstTensor AstMethodLet s (BuildTensorKind k2 (BuildTensorKind k1 y))
astTrBuild stk t = case stk of
  STKScalar{} -> astTrS t
  STKR SNat stk1 | Dict <- lemTensorKindOfSTK stk1 -> astTr t
  STKS sh stk1 | Dict <- lemTensorKindOfSTK stk1 -> withKnownShS sh $ astTrS t
  STKX sh stk1 | Dict <- lemTensorKindOfSTK stk1 -> withKnownShX sh $ astTrX t
  STKProduct @z1 @z2 stk1 stk2
    | Dict <- lemTensorKindOfBuild (SNat @k1) stk
    , Dict <- lemTensorKindOfBuild (SNat @k1) stk1
    , Dict <- lemTensorKindOfBuild (SNat @k2) stk1
    , Dict <- lemTensorKindOfBuild
                        (SNat @k1) (stensorKind @(BuildTensorKind k2 z1))
    , Dict <- lemTensorKindOfBuild
                        (SNat @k2) (stensorKind @(BuildTensorKind k1 z1))
    , Dict <- lemTensorKindOfBuild (SNat @k1) stk2
    , Dict <- lemTensorKindOfBuild (SNat @k2) stk2
    , Dict <- lemTensorKindOfBuild
                        (SNat @k1) (stensorKind @(BuildTensorKind k2 z2))
    , Dict <- lemTensorKindOfBuild
                        (SNat @k2) (stensorKind @(BuildTensorKind k1 z2)) ->
      astLetFun t $ \ !tShared ->
        let (u1, u2) = (astProject1 tShared, astProject2 tShared)
        in astPair (astTrBuild @k1 @k2 stk1 u1) (astTrBuild @k1 @k2 stk2 u2)

astIndexBuild :: forall y k s. AstSpan s
              => SNat k -> STensorKind y
              -> AstTensor AstMethodLet s (BuildTensorKind k y)
              -> AstInt AstMethodLet
              -> AstTensor AstMethodLet s y
astIndexBuild snat@SNat stk u i = case stk of
  STKScalar{} -> astFromS stensorKind $ astIndexStepS u (i :.$ ZIS)
  STKR SNat x | Dict <- lemTensorKindOfSTK x -> case ftkAst u of
    FTKR shmshn _ | SNat <- shrRank shmshn ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: k ': Drop 1 sh :~: sh) $
        withKnownShS (dropShS @1 sh) $
        astFromS (stensorKind @y)
        $ astIndexStepS (astSFromR @sh u) (i :.$ ZIS)
  STKS sh x | Dict <- lemTensorKindOfSTK x ->
    withKnownShS sh $ astIndexStepS u (i :.$ ZIS)
  STKX @sh' sh' x | Dict <- lemTensorKindOfSTK x -> case ftkAst u of
   FTKX shBuild' _->
    withKnownShX sh' $
    withCastXS shBuild' $ \(shBuild :: ShS shBuild) -> case shBuild of
      ZSS -> error "astIndexBuild: impossible empty shape"
      (:$$) _ rest ->
        withKnownShS rest $
        astFromS (stensorKind @y)
        $ astIndexStepS (astSFromX @shBuild @(Just k ': sh') u)
                        (i :.$ ZIS)
  STKProduct stk1 stk2
    | Dict <- lemTensorKindOfSTK stk1
    , Dict <- lemTensorKindOfSTK stk2
    , Dict <- lemTensorKindOfBuild snat stk1
    , Dict <- lemTensorKindOfBuild snat stk2 ->
      astLetFun u $ \ !u3 ->
        astPair (astIndexBuild snat stk1 (astProject1 u3) i)
                (astIndexBuild snat stk2 (astProject2 u3) i)

substProjRep
  :: forall k s s2 y2 y.
     (AstSpan s, AstSpan s2, TensorKind y2, TensorKind y)
  => SNat k -> IntVarName
  -> FullTensorKind y2 -> AstVarName s2 y2 -> AstTensor AstMethodLet s y
  -> ( AstVarName s2 (BuildTensorKind k y2)
     , FullTensorKind (BuildTensorKind k y2)
     , AstTensor AstMethodLet s y )
substProjRep snat@SNat var ftk2 var1 v
  | Dict <- lemTensorKindOfBuild snat (stensorKind @y2) =
    let var3 :: AstVarName s2 (BuildTensorKind k y2)
        var3 = mkAstVarName (varNameToAstVarId var1)  -- changed shape; TODO: shall we rename?
        ftk3 = buildFTK snat ftk2
        astVar3 = Ast.AstVar ftk3 var3
        v2 = substituteAst
               (astIndexBuild snat (ftkToStk ftk2) astVar3 (Ast.AstIntVar var))
               var1 v
          -- The subsitutions of projections don't break sharing,
          -- because they don't duplicate variables and the added var
          -- is eventually being eliminated instead of substituted for.
    in (var3, ftk3, v2)


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

mkTraceRule :: forall y z s. (TensorKind y, TensorKind z, AstSpan s)
            => String -> AstTensor AstMethodLet s y -> AstTensor AstMethodLet s z -> Int
            -> AstTensor AstMethodLet s y
            -> AstTensor AstMethodLet s y
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
    modifyIORef' traceNestingLevel pred
  let !_A = assert (ftkAst from == ftkAst to
                    `blame` "mkTraceRule: term shape changed"
                    `swith`( ftkAst from, ftkAst to
                           , from, to )) ()
  return $! to

hPutStrLnFlush :: Handle -> String -> IO ()
hPutStrLnFlush target s = do
  hFlush stdout >> hFlush stderr
  hPutStrLn target s
  hFlush stdout >> hFlush stderr
