{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | BOT (bulk-operation transformation) of the AST, which is a kind
-- of vectorization. It eliminates the build operation and, consequently,
-- any occurrence of indexing under build, which would cause delta expression
-- explosion and afterwards one-hot explosion when evaluating deltas.
module HordeAd.Core.AstVectorize
  ( build1Vectorize, traceRuleEnabledRef
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Control.Monad (when)
import Data.IORef
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (type (+), type (<=?))
import System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested (type (++))
import Data.Array.Nested.Convert (withShsFromShR, withShsFromShX)
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped qualified as Shaped
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Tail, unsafeCoerceRefl)

import HordeAd.Core.Ast (AstTensor)
import HordeAd.Core.Ast hiding (AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.Conversion
import HordeAd.Core.ConvertTensor
import HordeAd.Core.PPEngine
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
  :: forall y k s. KnownSpan s
  => SNat k -> SingletonTK y -> (IntVarName, AstTensor AstMethodLet s y)
  -> IO (AstTensor AstMethodLet s (BuildTensorKind k y))
{-# INLINE build1Vectorize #-}
build1Vectorize snat@SNat stk (!var, !v0) = do
  enabled <- readIORef traceRuleEnabledRef
  let width = 1000 * traceWidth
      startTerm = Ast.AstBuild1 snat stk (var, v0)
  when enabled $ do
    writeIORef traceNestingLevel 0
    hPutStrLnFlush stderr $
      "\n"
      ++ "START of vectorization for term "
      ++ ellipsisString width (printAstSimple startTerm)
      ++ "\n"
  let !endTerm = build1VOccurrenceUnknown snat (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (printAstSimple endTerm)
      ++ "\n"
  let !_A = assert (ftkAst startTerm == ftkAst endTerm
                    `blame` "build1Vectorize: term shape changed"
                    `swith` ( ftkAst startTerm
                            , ftkAst endTerm )) ()
  return endTerm


-- * Vectorization

-- | The application @build1VOccurrenceUnknown k (var, v)@ vectorizes
-- term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurrenceUnknown
  :: forall y k s. KnownSpan s
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
build1VOccurrenceUnknown snat@SNat (!var, !v0)
  | stk0 <- ftkToSTK (ftkAst v0) =
    let traceRule =
          mkTraceRule "build1VOcc" (Ast.AstBuild1 snat stk0 (var, v0))
                      (buildFTK snat (ftkAst v0)) v0 1
    in if varNameInAst var v0
       then build1V snat (var, v0)
       else traceRule $
         astReplicate snat stk0 v0

-- This refreshes the indexing variable in a build body.
-- This is used to avoid biding the same variable twice in the code,
-- (unless in very safe situations, e.g., different branches
-- of an arithmetic expression) which may end up as nested bindings eventually
-- and break our invariants that we need for simplified handling of bindings
-- when rewriting terms.
build1VOccurrenceUnknownRefresh
  :: forall y k s. KnownSpan s
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
{-# NOINLINE build1VOccurrenceUnknownRefresh #-}
build1VOccurrenceUnknownRefresh snat@SNat (var, v0) =
  funToAstIntMaybe (varNameToBounds var) $ \ (!varFresh, astVarFresh) ->
    let !v2 = substituteAst astVarFresh var v0
                -- cheap subst, because only a renaming
    in build1VOccurrenceUnknown snat (varFresh, v2)

-- | The application @build1V k (var, v)@ vectorizes term
-- @AstBuild1 k (var, v)@, where it's known that- @var@ occurs in @v@,
-- see above for what it means precisely.
build1V
  :: forall y k s. KnownSpan s
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
build1V snat@SNat (!var, !v0) | ftk0 <- ftkAst v0 =
  let bv = Ast.AstBuild1 snat (ftkToSTK ftk0) (var, v0)
      traceRule = mkTraceRule "build1V" bv (buildFTK snat (ftkAst v0)) v0 1
  in case v0 of
    Ast.AstPair t1 t2 -> traceRule $
      astPair (build1VOccurrenceUnknown snat (var, t1))
              (build1VOccurrenceUnknown snat (var, t2))
    Ast.AstProject1 t -> traceRule $
      astProject1 (build1V snat (var, t))
    Ast.AstProject2 t -> traceRule $
      astProject2 (build1V snat (var, t))
    Ast.AstFromVector snat1 stk l -> traceRule $
      astTrBuild snat1 snat stk
      $ astFromVector snat1 (buildSTK snat stk) (V.map (\v ->
          build1VOccurrenceUnknown snat (var, v)) l)
    Ast.AstSum k1 stk v
      | Dict0 <- lemTKAllNumBuild snat stk -> traceRule $
        astSum k1 (buildSTK snat stk)
        $ astTrBuild snat k1 stk $ build1V snat (var, v)
    Ast.AstReplicate snat2 stk v -> traceRule $
      astTrBuild snat2 snat stk
      $ astReplicate snat2 (buildSTK snat stk) $ build1V snat (var, v)
    Ast.AstMapAccumLDer k5@(SNat @k5) bftk eftk f df rf acc0 es
     | Refl <- lemBuildOfAD snat (ftkToSTK (ftkAst acc0))
     , Refl <- lemBuildOfAD snat (ftkToSTK bftk)
     , Refl <- lemBuildOfAD snat (ftkToSTK eftk) -> traceRule $
      astLetFun
        (astMapAccumLDer
           k5
           (buildFTK snat bftk)
           (buildFTK snat eftk)
           (build1VHFun snat (var, f))
           (build1VHFun snat (var, df))
           (build1VHFun snat (var, rf))
           (build1VOccurrenceUnknown snat (var, acc0))
           (astTrBuild (SNat @k) (SNat @k5) (ftkToSTK eftk)
            $ build1VOccurrenceUnknown snat (var, es)))
        (\x1bs1 -> astPair (astProject1 x1bs1)
                           (astTrBuild (SNat @k5) (SNat @k)
                                       (ftkToSTK bftk) (astProject2 x1bs1)))
    Ast.AstApply t ll -> traceRule $
      astApply (build1VHFun snat (var, t))
               (build1VOccurrenceUnknown snat (var, ll))
    Ast.AstVar var2 -> traceRule $
      if varNameToAstVarId var2 == varNameToAstVarId var
      then case var2 of
        AstVarName _ FtkAndBoundsBounds{} -> fromPlain @s $ Ast.AstIotaS snat
        _ -> error "build1V: build variable is not an index variable"
      else error "build1V: AstVar can't contain other free variables"
    Ast.AstCond b u v -> traceRule $
      let stk0 = ftkToSTK ftk0
          uv = astFromVector (SNat @2) stk0 (V.fromListN 2 [u, v])
          -- We handle products specially to avoid duplicating a variable,
          -- for which we can then substitute indexing, no big deal,
          -- but each of the indexing can subsequently get turned
          -- into a gather, which then makes a performance difference.
          t = case ftk0 of
            FTKProduct{} ->
              let uvN = nestTargetK (SNat @2) ftk0 uv
              in unNestTarget stk0 $ astIndexS ZSS uvN (astCond b 0 1 :.$ ZIS)
            _ ->
              astIndexBuild (SNat @2) ftk0 uv (astCond b 0 1)
      in build1VOccurrenceUnknown snat (var, t)
    Ast.AstBuild1 snat2 _ (var2, v2) -> traceRule $
      assert (var2 /= var) $
      build1VOccurrenceUnknown
        snat (var, build1VOccurrenceUnknown snat2 (var2, v2))
          -- happens only when testing and mixing different pipelines

    Ast.AstLet var1 u v -> traceRule $
      let (var3, v2) = substProjRep snat var var1 v
      in astLet var3 (withKnownSpan (varNameToSpan var1) $
                      build1VOccurrenceUnknown snat (var, u))
                     (build1VOccurrenceUnknownRefresh snat (var, v2))
           -- ensures no duplicated bindings, see below

    Ast.AstPrimalPart v -> traceRule $
      astPrimalPart $ build1V snat (var, v)
    Ast.AstDualPart v -> traceRule $
      astDualPart $ build1V snat (var, v)
    Ast.AstPlainPart v -> traceRule $
      astPlainPart $ build1V snat (var, v)
    Ast.AstFromPrimal v -> traceRule $
      fromPrimal $ build1V snat (var, v)
    Ast.AstFromDual v -> traceRule $
      fromDual $ build1V snat (var, v)
    Ast.AstFromPlain v -> traceRule $
      fromPlain $ build1V snat (var, v)

    Ast.AstPlusK u v -> traceRule $
      build1VOccurrenceUnknown snat (var, u)
      + build1VOccurrenceUnknown snat (var, v)
    Ast.AstTimesK u v -> traceRule $
      build1VOccurrenceUnknown snat (var, u)
      * build1VOccurrenceUnknown snat (var, v)
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstN1K opCode u -> traceRule $
      Ast.AstN1S opCode (build1V snat (var, u))
    Ast.AstR1K opCode u -> traceRule $
      Ast.AstR1S opCode (build1V snat (var, u))
    Ast.AstR2K opCode u v -> traceRule $
      Ast.AstR2S opCode (build1VOccurrenceUnknown snat (var, u))
                        (build1VOccurrenceUnknown snat (var, v))
    Ast.AstI2K opCode u v -> traceRule $
      Ast.AstI2S opCode (build1VOccurrenceUnknown snat (var, u))
                        (build1VOccurrenceUnknown snat (var, v))
    Ast.AstConcreteK{} ->
      error "build1V: AstConcreteK can't have free index variables"
    Ast.AstFloorK v -> traceRule $
      astFloorS $ build1V snat (var, v)
    Ast.AstFromIntegralK v -> traceRule $
      astFromIntegralS $ build1V snat (var, v)
    Ast.AstCastK v -> traceRule $
      astCastS $ build1V snat (var, v)
    Ast.AstArgMinK v -> traceRule $
      Ast.AstArgMinS $ build1V snat (var, v)
    Ast.AstArgMaxK v -> traceRule $
      Ast.AstArgMaxS $ build1V snat (var, v)

    Ast.AstPlusS u v -> traceRule $
      build1VOccurrenceUnknown snat (var, u)
      + build1VOccurrenceUnknown snat (var, v)
    Ast.AstTimesS u v -> traceRule $
      build1VOccurrenceUnknown snat (var, u)
      * build1VOccurrenceUnknown snat (var, v)
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstN1S opCode u -> traceRule $
      Ast.AstN1S opCode (build1V snat (var, u))
    Ast.AstR1S opCode u -> traceRule $
      Ast.AstR1S opCode (build1V snat (var, u))
    Ast.AstR2S opCode u v -> traceRule $
      Ast.AstR2S opCode (build1VOccurrenceUnknown snat (var, u))
                        (build1VOccurrenceUnknown snat (var, v))
    Ast.AstI2S opCode u v -> traceRule $
      Ast.AstI2S opCode (build1VOccurrenceUnknown snat (var, u))
                        (build1VOccurrenceUnknown snat (var, v))
    Ast.AstConcreteS{} ->
      error "build1V: AstConcreteS can't have free index variables"
    Ast.AstFloorS v -> traceRule $
      astFloorS $ build1V snat (var, v)
    Ast.AstFromIntegralS v -> traceRule $
      astFromIntegralS $ build1V snat (var, v)
    Ast.AstCastS v -> traceRule $
      astCastS $ build1V snat (var, v)
    Ast.AstArgMinS v -> traceRule $
      Ast.AstArgMinS $ build1V snat (var, v)
    Ast.AstArgMaxS v -> traceRule $
      Ast.AstArgMaxS $ build1V snat (var, v)

    Ast.AstIndexS shn v ix -> traceRule $
      build1VIndexS snat shn (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstScatterS shm shn shp v (vars, ix) -> traceRule $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS (var, ix)
      in astScatterS (SNat @k :$$ shm) shn (SNat @k :$$ shp)
                     (build1VOccurrenceUnknown snat (var, v))
                     (varFresh ::$ vars, astVarFresh :.$ ix2)
    Ast.AstGatherS shm shn shp v (vars, ix) -> traceRule $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS (var, ix)
      in astGatherS (SNat @k :$$ shm) shn (SNat @k :$$ shp)
                    (build1VOccurrenceUnknown snat (var, v))
                    (varFresh ::$ vars, astVarFresh :.$ ix2)
    Ast.AstIotaS{} ->
      error "build1V: AstIotaS can't have free variables"
    Ast.AstAppendS v w -> traceRule $
      astTrS $ astAppendS (astTrS $ build1VOccurrenceUnknown snat (var, v))
                          (astTrS $ build1VOccurrenceUnknown snat (var, w))
    Ast.AstSliceS i n k v -> traceRule $
      astTrS $ astSliceS i n k $ astTrS $ build1V snat (var, v)
    Ast.AstReverseS v -> traceRule $
      astTrS $ astReverseS $ astTrS $ build1V snat (var, v)
    Ast.AstTransposeS @perm @sh1 perm v -> traceRule $ case ftk0 of
      FTKS @sh _ _ ->
        let zsuccPerm :: Permutation.Perm (0 : Permutation.MapSucc perm)
            zsuccPerm = Permutation.permShift1 perm
        in gcastWith (unsafeCoerceRefl
                      :: Permutation.PermutePrefix
                           (0 : Permutation.MapSucc perm) (k : sh1)
                         :~: k : sh) $
           gcastWith (unsafeCoerceRefl
                      :: Rank (0 : Permutation.MapSucc perm)
                         :~: 1 + Rank perm) $
           fromMaybe (error "build1V: impossible non-permutation")
           $ Permutation.permCheckPermutation zsuccPerm
           $ astTransposeS zsuccPerm $ build1V snat (var, v)
    Ast.AstReshapeS sh v -> traceRule $
      astReshapeS (snat :$$ sh) $ build1V snat (var, v)

    Ast.AstConvert c v -> traceRule $
      astConvert (buildTKConversion snat (ftkAst v) c)
      $ build1V snat (var, v)

    Ast.AstIndex0{} -> error "build1V: term not accessible from user API"
    Ast.AstSum0{} -> error "build1V: term not accessible from user API"
    Ast.AstDot0{} -> error "build1V: term not accessible from user API"
    Ast.AstDot1InS{} -> error "build1V: term not accessible from user API"
    Ast.AstMatmul2S{} -> error "build1V: term not accessible from user API"

    Ast.AstBoolNotK b -> traceRule $
      Ast.AstBoolNotS $ build1V snat (var, b)
    Ast.AstBoolNotS b -> traceRule $
      Ast.AstBoolNotS $ build1V snat (var, b)
    Ast.AstBoolAndK b c -> traceRule $
      Ast.AstBoolAndS (build1VOccurrenceUnknown snat (var, b))
                      (build1VOccurrenceUnknown snat (var, c))
    Ast.AstBoolAndS b c -> traceRule $
      Ast.AstBoolAndS (build1VOccurrenceUnknown snat (var, b))
                      (build1VOccurrenceUnknown snat (var, c))
    Ast.AstLeqK u v -> traceRule $
      Ast.AstLeqS (snat :$$ ZSS) ZSS
                  (build1VOccurrenceUnknown snat (var, u))
                  (build1VOccurrenceUnknown snat (var, v))
    Ast.AstLeq u v | FTKS sh _ <- ftkAst u -> traceRule $
      Ast.AstLeqS (snat :$$ ZSS) sh
                  (build1VOccurrenceUnknown snat (var, u))
                  (build1VOccurrenceUnknown snat (var, v))
    Ast.AstLeqS shb sh u v -> traceRule $
      Ast.AstLeqS (snat :$$ shb) sh
                  (build1VOccurrenceUnknown snat (var, u))
                  (build1VOccurrenceUnknown snat (var, v))

-- This refreshes an index variable in a list of index expressions.
intBindingRefreshS
  :: (IntVarName, AstIxS AstMethodLet sh)
  -> (IntVarName, AstInt AstMethodLet, AstIxS AstMethodLet sh)
{-# NOINLINE intBindingRefreshS #-}
intBindingRefreshS (var, ix) =
  funToAstIntMaybe (varNameToBounds var) $ \ (!varFresh, astVarFresh) ->
    let !ix2 = substituteAstIxS astVarFresh var ix
                 -- cheap subst, because only a renaming
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
-- in @astIndex@, that eliminates indexing from the top of a term
-- position (except for two permissible normal forms) and vectorization,
-- @build1VOccurrenceUnknown@, that recursively goes down under constructors
-- until it encounter indexing again. We have to do this in lockstep
-- so that we simplify terms only as much as needed to vectorize.
--
-- If simplification can't proceed, which means that we reached one of the few
-- normal forms wrt simplification, we invoke the pure desperation rule (D)
-- which produces large tensors, which are hard to simplify even when
-- eventually proven unnecessary. The rule changes the index to a gather
-- and pushes the build down the gather, getting the vectorization unstuck.
build1VIndexS
  :: forall k shm shn x s. KnownSpan s
  => SNat k -> ShS shn
  -> ( IntVarName  -- bounds (0, k - 1)
     , AstTensor AstMethodLet s (TKS2 (shm ++ shn) x)
     , AstIxS AstMethodLet shm )
  -> AstTensor AstMethodLet s (TKS2 (k ': shn) x)
build1VIndexS k _ (!var, !v0, ZIS) =
  build1VOccurrenceUnknown k (var, v0)
build1VIndexS k@SNat shn (var, v0, ix) | FTKS shmshn x' <- ftkAst v0 =
  let x = ftkToSTK x'
      vTrace = Ast.AstBuild1 k (STKS shn x) (var, Ast.AstIndexS shn v0 ix)
      traceRule = mkTraceRule "build1VIndexS" vTrace
                              (buildFTK k (FTKS shn x')) v0 1
  in if varNameInAst var v0
     then case astIndexKnobsS (defaultKnobs {knobPhase = PhaseVectorization})
                              shn v0 ix of  -- push deeper
       Ast.AstIndexS _ v1 ZIS -> traceRule $
         build1VOccurrenceUnknown k (var, v1)
       v@(Ast.AstIndexS @shm1 @shn1 shn1 v1 ix1) -> traceRule $
         let (varFresh, astVarFresh, ix2) = intBindingRefreshS (var, ix1)
             ruleD :: AstTensor AstMethodLet s (TKS2 (k ': shn) x)
             ruleD | FTKS shmshn1 _ <- ftkAst v1 =
               astGatherS
                 (SNat @k :$$ ZSS)
                 shn1
                 (SNat @k :$$ Shaped.shsTakeIx @shn1 @shm1 Proxy shmshn1 ix2)
                 (build1VOccurrenceUnknown k (var, v1))
                 (varFresh ::$ ZS, astVarFresh :.$ ix2)
             len = ixsLength ix1
             pickRuleD :: AstTensor AstMethodLet s2 y2 -> Bool
             pickRuleD = \case  -- try to avoid ruleD if not a normal form
               Ast.AstFromVector{} -> len == 1
               Ast.AstScatterS{} -> True
               Ast.AstGatherS{} -> True
               Ast.AstMapAccumLDer{} -> True
               -- These can only be simplified to the AstFromVector NF above.
               Ast.AstReplicate{} -> True
               Ast.AstAppendS{} -> True
               -- These, in general, simplify to gathers, so as bad as ruleD.
               Ast.AstTransposeS{} -> True
               Ast.AstReshapeS{} -> True
               -- Rarely these don't simplify enough; left as an escape hatch:
               -- (TODO: simplify better)
               Ast.AstConvert{} -> True
               -- Hard to tell just from the prefix:
               Ast.AstProject1 v2 -> pickRuleD v2
               Ast.AstProject2 v2 -> pickRuleD v2
               _ -> False  -- not a normal form
         in if varNameInAst var v1 && pickRuleD v1
            then ruleD
            else build1VOccurrenceUnknown k (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurrenceUnknown k (var, v)
           -- peel off yet another constructor
     else traceRule $
            astGatherS (SNat @k :$$ ZSS)
                       shn
                       (Shaped.shsTakeIx @shn @shm Proxy shmshn ix)
                       v0 (var ::$ ZS, ix)

build1VHFun
  :: forall k x z s. KnownSpan s
  => SNat k -> (IntVarName, AstHFun s x z)
  -> AstHFun s (BuildTensorKind k x) (BuildTensorKind k z)
build1VHFun snat@SNat (var, v0) = case v0 of
  Ast.AstLambda var1 t ->
    -- This handles the case of l having free variables beyond var1,
    -- which is not possible for lambdas used in folds, etc.
    -- But note that, due to substProjVars, l2 has var occurrences,
    -- so build1VOccurrenceUnknownRefresh is neccessary to handle
    -- them and to eliminate them so that the function is closed again.
    let (var2, t2) = substProjRep snat var var1 t
    in Ast.AstLambda var2 (build1VOccurrenceUnknownRefresh snat (var, t2))


-- * Auxiliary operations

astTr :: forall n s r. KnownSpan s
      => AstTensor AstMethodLet s (TKR2 (2 + n) r)
      -> AstTensor AstMethodLet s (TKR2 (2 + n) r)
astTr a = case Permutation.makePerm @'[1, 0] of
  (perm :: Permutation.Perm perm) -> case ftkAst a of
    FTKR sh'@(k :$: m :$: shr) _ | SNat <- shrRank sh' ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        gcastWith (unsafeCoerceRefl :: (Rank perm <=? Rank sh) :~: True) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (Permutation.PermutePrefix perm sh) :~: Rank sh) $
        astConvUpRFromS (m :$: k :$: shr)
        . astTransposeS perm . astConvDownSFromR sh $ a
    _ -> error "astTr: impossible shape"

astTrS :: forall n m sh s r. KnownSpan s
       => AstTensor AstMethodLet s (TKS2 (n ': m ': sh) r)
       -> AstTensor AstMethodLet s (TKS2 (m ': n ': sh) r)
astTrS a | FTKS (_ :$$ _ :$$ sh) _ <- ftkAst a
         , SNat <- shsRank sh =  -- why on Earth is this needed?
  astTransposeS (Permutation.makePerm @'[1, 0]) a

astTrX :: forall n m shx s r. KnownSpan s
       => AstTensor AstMethodLet s (TKX2 (Just n ': Just m ': shx) r)
       -> AstTensor AstMethodLet s (TKX2 (Just m ': Just n ': shx) r)
astTrX a = case Permutation.makePerm @'[1, 0] of
  (perm :: Permutation.Perm perm) -> case ftkAst a of
    FTKX sh'@(mn :$% mm :$% shx) _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        gcastWith (unsafeCoerceRefl :: (Rank perm <=? Rank sh) :~: True) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (Permutation.PermutePrefix perm sh) :~: Rank sh) $
        astConvUpXFromS (mm :$% mn :$% shx)
        . astTransposeS perm . astConvDownSFromX sh $ a

astTrBuild
  :: forall k1 k2 s y. KnownSpan s
  => SNat k1 -> SNat k2 -> SingletonTK y
  -> AstTensor AstMethodLet s (BuildTensorKind k1 (BuildTensorKind k2 y))
  -> AstTensor AstMethodLet s (BuildTensorKind k2 (BuildTensorKind k1 y))
astTrBuild SNat SNat stk t = case stk of
  STKScalar -> astTrS t
  STKR{} -> astTr t
  STKS{} -> astTrS t
  STKX{} -> astTrX t
  STKProduct stk1 stk2 ->
    astLetFun t $ \ !tShared ->
      let (u1, u2) = (astProject1 tShared, astProject2 tShared)
      in astPair (astTrBuild (SNat @k1) (SNat @k2) stk1 u1)
                 (astTrBuild (SNat @k1) (SNat @k2) stk2 u2)

astIndexBuild :: forall y k s. KnownSpan s
              => SNat k -> FullShapeTK y
              -> AstTensor AstMethodLet s (BuildTensorKind k y)
              -> AstInt AstMethodLet
              -> AstTensor AstMethodLet s y
astIndexBuild snat@SNat ftk u i = case ftk of
  FTKScalar -> kfromS $ astIndexS ZSS u (i :.$ ZIS)
  FTKR sh' _ -> case ftkAst u of
    FTKR shmshn _ ->
      withShsFromShR shmshn $ \(sh :: ShS sh) ->
        gcastWith (unsafeCoerceRefl :: k ': Tail sh :~: sh) $
        astConvUpRFromS sh' $ astIndexS (shsTail sh) (astConvDownSFromR sh u) (i :.$ ZIS)
  FTKS sh _ -> astIndexS sh u (i :.$ ZIS)
  FTKX sh' _ -> case ftkAst u of
   FTKX shBuild' _->
    withShsFromShX shBuild' $ \shBuild -> case shBuild of
      _ :$$ rest ->
        astConvUpXFromS sh' $ astIndexS rest (astConvDownSFromX shBuild u) (i :.$ ZIS)
  FTKProduct ftk1 ftk2 ->
    astLetFun u $ \ !u3 ->
      astPair (astIndexBuild snat ftk1 (astProject1 u3) i)
              (astIndexBuild snat ftk2 (astProject2 u3) i)
  {- The following prevents generating duplicated gathers by vectorization
     but it generates big conversions that are even more costly,
     due to transforming HFuns, e.g., the arguments of folds:
  FTKProduct{} ->
    -- This conversion trick, in particular, prevents duplication of a variable
    -- in AstCond, for which we can then substitute indexing, no big deal,
    -- but each of the indexing can subsequently get turned into a gather,
    -- which then makes a performance difference.
    unNestTarget (ftkToSTK ftk)
    $ astIndexS ZSS (nestTargetK snat ftk u) (i :.$ ZIS) -}

substProjRep
  :: forall k s s2 y2 y. KnownSpan s
  => SNat k -> IntVarName
  -> AstVarName '(s2, y2) -> AstTensor AstMethodLet s y
  -> (AstVarName '(s2, BuildTensorKind k y2), AstTensor AstMethodLet s y)
substProjRep snat@SNat var var1 v =
  let ftk1 = varNameToFTK var1
      ftk3 = buildFTK snat ftk1
      var3 :: AstVarName '(s2, BuildTensorKind k y2)
      var3 = reshapeVarName ftk3 var1
      astVar3 = astVar var3
      indexing = withKnownSpan (varNameToSpan var1) $
                 astIndexBuild snat ftk1 astVar3 (astVar var)
      v2 = substituteAst indexing var1 v
        -- The subsitutions of projections and indexing don't break sharing
        -- too much, because they don't duplicate variables and the added var
        -- is eventually being eliminated instead of substituted for.
  in (var3, v2)


-- * Rule tracing machinery

traceRuleEnabledRef :: IORef Bool
{-# NOINLINE traceRuleEnabledRef #-}
traceRuleEnabledRef = unsafePerformIO $ newIORef False

traceNestingLevel :: IORef Int
{-# NOINLINE traceNestingLevel #-}
traceNestingLevel = unsafePerformIO $ newIORef 0

traceWidth :: Int
traceWidth = 90

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

-- We can't force @to@, because we want the debug info displayed before
-- @to@ is evaluated (or diverges).
-- TODO: switch away from IORefs to ensure correct blocking and then
-- really display the first part of the message before @to@ diverges.
mkTraceRule :: forall y z s. KnownSpan s
            => String
            -> AstTensor AstMethodLet s y
            -> FullShapeTK y
            -> AstTensor AstMethodLet s z
            -> Int
            -> AstTensor AstMethodLet s y
            -> AstTensor AstMethodLet s y
{-# NOINLINE mkTraceRule #-}
mkTraceRule prefix from !fromFTK caseAnalysed nwords ~to = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = traceWidth
      constructorName =
        unwords $ take nwords $ words $ take 21
        $ case caseAnalysed of
          Ast.AstVar{} -> "variable"
          Ast.AstIndexS{} -> "sindex"
          _ -> printAstSimple caseAnalysed
      ruleName = prefix ++ "." ++ constructorName
      ruleNamePadded = take 21 $ ruleName ++ repeat ' '
  when enabled $ do
    nestingLevel <- readIORef traceNestingLevel
    modifyIORef' traceNestingLevel succ
    -- Force in the correct order:
    let !paddedNesting = take 3 $ show nestingLevel ++ repeat ' '
    let !stringFrom = printAstSimple from
    let !stringTo = printAstSimple to
    hPutStrLnFlush stderr $ paddedNesting ++ "rule " ++ ruleNamePadded
                            ++ " sends " ++ padString width stringFrom
                            ++ " to " ++ padString width stringTo
    modifyIORef' traceNestingLevel pred
  let !_A = assert (fromFTK == ftkAst to
                    `blame` "mkTraceRule: term shape changed"
                    `swith` ( fromFTK, ftkAst to
                            , from, to )) ()
  return $! to

hPutStrLnFlush :: Handle -> String -> IO ()
hPutStrLnFlush target s = do
  hFlush stdout >> hFlush stderr
  hPutStrLn target s
  hFlush stdout >> hFlush stderr
