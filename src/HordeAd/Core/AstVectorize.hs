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
import Data.Default
import Data.Functor.Const
import Data.IntMap.Strict qualified as IM
import Data.IORef
import Data.List (mapAccumR)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat, OrderingI (..), cmpNat, type (+), type (-))
import System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (ssxAppend, ssxFromShape, ssxReplicate)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , IxR (..)
  , IxS (..)
  , IxX (..)
  , KnownShS (..)
  , KnownShX (..)
  , ListR (..)
  , ListS (..)
  , Rank
  , ShR (..)
  , ShS (..)
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape
  (shCvtSX, shrRank, shsAppend, shsLength, shsPermutePrefix, shsRank)

import HordeAd.Core.Ast (AstTensor)
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- This abbreviation is used a lot below.
astTr :: forall n s r. (KnownNat n, TensorKind r, AstSpan s)
      => AstTensor AstMethodLet s (TKR2 (2 + n) r) -> AstTensor AstMethodLet s (TKR2 (2 + n) r)
astTr = astTranspose [1, 0]

-- | The application @build1Vectorize k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, that is, rewrites it to a term
-- with the same value, but not containing the outermost @AstBuild1@
-- constructor and not increasing (and potentially decreasing)
-- the total number of @AstBuild1@ occuring in the term.
-- If no @AstBuild1@ terms occur in @v@, the resulting term won't
-- have any, either.
build1Vectorize
  :: forall k y s. (AstSpan s, TensorKind y)
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

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: forall k y s. (AstSpan s, TensorKind y)
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
         astReplicate snat v0

-- This is used to avoid biding the same variable twice in the code,
-- (unless in very safe situations, e.g., different branches
-- of an arithmetic expression) which may end up as nested bindings eventually
-- and break our invariants that we need for simplified handling of bindings
-- when rewriting terms.
build1VOccurenceUnknownRefresh
  :: (AstSpan s, TensorKind y)
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y) -> AstTensor AstMethodLet s (BuildTensorKind k y)
{-# NOINLINE build1VOccurenceUnknownRefresh #-}
build1VOccurenceUnknownRefresh snat@SNat (var, v0) =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !v2 = substituteAst  -- cheap subst, because only a renaming
                astVarFresh var v0
    in build1VOccurenceUnknown snat (varFresh, v2)

intBindingRefresh
  :: IntVarName -> AstIxR AstMethodLet n
  -> (IntVarName, AstInt AstMethodLet, AstIxR AstMethodLet n)
{-# NOINLINE intBindingRefresh #-}
intBindingRefresh var ix =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !ix2 = substituteAstIxR  -- cheap subst, because only a renaming
                 astVarFresh
                 var ix
    in (varFresh, astVarFresh, ix2)

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
--
-- We can't simplify the argument term here, because it may eliminate
-- the index variable. We simplify only in 'build1VOccurenceUnknown'.
build1V
  :: forall k s y. (AstSpan s, TensorKind y)
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
build1V snat@SNat (var, v0) =
  let k = sNatValue snat
      bv = Ast.AstBuild1 snat (var, v0)
      traceRule | Dict <- lemTensorKindOfBuild snat (stensorKind @y) =
        mkTraceRule "build1V" bv v0 1
  in case v0 of
    Ast.AstFromScalar v2@(Ast.AstVar _ var2)  -- TODO: make compositional
      | varNameToAstVarId var2 == varNameToAstVarId var -> traceRule $
        case isTensorInt v2 of
          Just Refl -> fromPrimal @s $ Ast.AstIotaS @k
            -- results in smaller terms than AstSlice(AstIota), because
            -- not turned into a concrete array so early
          _ -> error "build1V: build variable is not an index variable"
    Ast.AstFromScalar{} -> case astNonIndexStep v0 of
      Ast.AstFromScalar{} ->  -- let's hope this doesn't oscillate
        error $ "build1V: AstFromScalar: building over scalars is undefined: "
                ++ show v0
      v1 -> build1VOccurenceUnknown snat (var, v1)  -- last ditch effort
    Ast.AstToScalar{} ->
      error $ "build1V: AstToScalar: building over scalars is undefined: "
              ++ show v0
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
    Ast.AstVar _ var2 -> traceRule $
      if varNameToAstVarId var2 == varNameToAstVarId var
      then case isTensorInt v0 of
        Just Refl -> Ast.AstToScalar $ Ast.AstConcrete (FTKS ZSS FTKScalar)
                     $ RepN $ Nested.sscalar def  -- TODO: ???
        _ -> error "build1V: build variable is not an index variable"
      else error "build1V: AstVar can't contain other free variables"
    Ast.AstPrimalPart v
      | Dict <- lemTensorKindOfBuild snat (stensorKind @y) -> traceRule $
        astPrimalPart $ build1V snat (var, v)
    Ast.AstDualPart v
      | Dict <- lemTensorKindOfBuild snat (stensorKind @y) -> traceRule $
        astDualPart $ build1V snat (var, v)
    Ast.AstFromPrimal v | Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
      traceRule $
        Ast.AstFromPrimal $ build1V snat (var, v)
    Ast.AstD u u' | Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
      traceRule $
        Ast.AstD (build1VOccurenceUnknown snat (var, u))
                 (build1VOccurenceUnknown snat (var, u'))
    Ast.AstCond b v w -> traceRule $ case stensorKind @y of
      STKScalar{} ->
        error $ "build1V: AstCond: building over scalars is undefined: "
                ++ show v0
      STKR SNat x | Dict <- lemTensorKindOfSTK x ->
        let t = astIndexStep (astFromVector $ V.fromList [v, w])
                             (astCond b 0 1 :.: ZIR)
        in build1VOccurenceUnknown snat (var, t)
      STKS sh x | Dict <- lemTensorKindOfSTK x -> withKnownShS sh $
        let t = astIndexStepS @'[2] (astFromVectorS $ V.fromList [v, w])
                                    (astCond b 0 1 :.$ ZIS)
        in build1VOccurenceUnknown snat (var, t)
      STKX{} -> error "TODO"
      STKProduct{} -> error "TODO"  -- revisit when we have general Index; also look at tcond
      STKUntyped -> error "TODO"
    Ast.AstReplicate @y2 snat2@(SNat @k2) v
     | Dict <- lemTensorKindOfBuild snat (stensorKind @y2) -> traceRule $
      astTrGeneral @k2 (stensorKind @y2) (astReplicate snat2
                                          $ build1V snat (var, v))
    Ast.AstBuild1 snat2 (var2, v2) ->
      build1VOccurenceUnknown snat (var, build1VOccurenceUnknown snat2 (var2, v2))
        -- happens only when testing and mixing different pipelines
    Ast.AstLet @y2 var1 u v
      | Dict <- lemTensorKindOfBuild snat (stensorKind @y2)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @y) -> traceRule $
        let ftk2 = ftkAst u
            (var3, _ftk3, v2) =
              substProjRep snat var ftk2 var1 v
        in astLet var3 (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknownRefresh snat (var, v2))
             -- ensures no duplicated bindings, see below

    Ast.AstMinIndexR v -> traceRule $
     Ast.AstMinIndexR $ build1V snat (var, v)
    Ast.AstMaxIndexR v -> traceRule $
     Ast.AstMaxIndexR $ build1V snat (var, v)
    Ast.AstFloorR v -> traceRule $
     Ast.AstFloorR $ build1V snat (var, v)
    Ast.AstIotaR ->
      error "build1V: AstIotaR can't have free index variables"

    Ast.AstN1 opCode u -> traceRule $
      Ast.AstN1 opCode (build1V snat (var, u))
    Ast.AstN2 opCode u v -> traceRule $
      Ast.AstN2 opCode (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknown snat (var, v))
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstR1 opCode u -> traceRule $
      Ast.AstR1 opCode (build1V snat (var, u))
    Ast.AstR2 opCode u v -> traceRule $
      Ast.AstR2 opCode (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknown snat (var, v))
    Ast.AstI2 opCode u v -> traceRule $
      Ast.AstI2 opCode (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknown snat (var, v))
    Ast.AstSumOfList args -> traceRule $
      astSumOfList $ map (\v -> build1VOccurenceUnknown snat (var, v)) args
    Ast.AstFloor v -> traceRule $
     Ast.AstFloor $ build1V snat (var, v)
    Ast.AstCast v -> traceRule $
      astCast $ build1V snat (var, v)
    Ast.AstFromIntegral v -> traceRule $
      astFromIntegral $ build1V snat (var, v)

    Ast.AstN1R opCode u -> traceRule $
      Ast.AstN1R opCode (build1V snat (var, u))
    Ast.AstN2R opCode u v -> traceRule $
      Ast.AstN2R opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstR1R opCode u -> traceRule $
      Ast.AstR1R opCode (build1V snat (var, u))
    Ast.AstR2R opCode u v -> traceRule $
      Ast.AstR2R opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
    Ast.AstI2R opCode u v -> traceRule $
      Ast.AstI2R opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
    Ast.AstSumOfListR args -> traceRule $
      astSumOfListR $ map (\v -> build1VOccurenceUnknown snat (var, v)) args

    Ast.AstIndex v ix -> traceRule $ case stensorKind @y of
      STKR _ _ ->
        build1VIndex snat (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstSum @y2 (SNat @k1) v
      | Dict <- lemTensorKindOfBuild (SNat @k1) (stensorKind @y2)
      , Dict <- lemTensorKindOfBuild (SNat @k) (stensorKind @y) -> traceRule $
         astSum (SNat @k1) $ astTrGeneral @k @k1 (stensorKind @y2)
                           $ build1V snat (var, v)
    Ast.AstScatter sh v (vars, ix) -> traceRule $
      -- We use a refreshed var binding in the new scatter expression so as
      -- not to duplicate the var binding from build1VOccurenceUnknown call.
      let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix
      in astScatter (k :$: sh)
                    (build1VOccurenceUnknown snat (var, v))
                    (varFresh ::: vars, astVarFresh :.: ix2)

    Ast.AstFromVector l -> traceRule $
      astTr $ astFromVector (V.map (\v -> build1VOccurenceUnknown snat (var, v)) l)
    Ast.AstAppend v w -> traceRule $
      astTr $ astAppend (astTr $ build1VOccurenceUnknown snat (var, v))
                        (astTr $ build1VOccurenceUnknown snat (var, w))
    Ast.AstSlice i s v -> traceRule $
      astTr $ astSlice i s $ astTr $ build1V snat (var, v)
    Ast.AstReverse v -> traceRule $
      astTr $ astReverse $ astTr $ build1V snat (var, v)
    Ast.AstTranspose perm v -> traceRule $
      astTranspose (normalizePermutation $ 0 : map succ perm)
                   (build1V snat (var, v))
    Ast.AstReshape sh v -> traceRule $
      astReshape (k :$: sh) $ build1V snat (var, v)
    Ast.AstGather sh v (vars, ix) -> traceRule $
      let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix
      in astGatherStep (k :$: sh)
                       (build1VOccurenceUnknown snat (var, v))
                       (varFresh ::: vars, astVarFresh :.: ix2)
    Ast.AstCastR v -> traceRule $
      astCastR $ build1V snat (var, v)
    Ast.AstFromIntegralR v -> traceRule $
      astFromIntegralR $ build1V snat (var, v)
    Ast.AstConcrete{} ->
      error "build1V: AstConcrete can't have free index variables"

    Ast.AstProjectR l p -> traceRule $
      astProjectR (build1V snat (var, l)) p
    Ast.AstLetHVectorIn @_ @_ @z vars1 l v
     | Dict <- lemTensorKindOfBuild snat (stensorKind @z) -> traceRule $
      -- Here substitution traverses @v@ term tree @length vars@ times.
      --
      -- We lose the type information surrounding var1 twice: first,
      -- because we create a variable with one more dimension,
      -- again, because the original variables might have been marked
      -- with a shape and here we require a rank.
      let (vOut, varsOut) = substProjVars @k var vars1 v
      in astLetHVectorIn
           varsOut (build1VOccurenceUnknown snat (var, l))
                   (build1VOccurenceUnknownRefresh snat (var, vOut))
    Ast.AstZipR v -> traceRule $
      Ast.AstZipR $ build1V snat (var, v)
    Ast.AstUnzipR v -> traceRule $
      Ast.AstUnzipR $ build1V snat (var, v)

    Ast.AstMinIndexS v -> traceRule $
      Ast.AstMinIndexS $ build1V snat (var, v)
    Ast.AstMaxIndexS v -> traceRule $
      Ast.AstMaxIndexS $ build1V snat (var, v)
    Ast.AstFloorS v -> traceRule $
      Ast.AstFloorS $ build1V snat (var, v)
    Ast.AstIotaS ->
      error "build1V: AstIotaS can't have free index variables"

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
    Ast.AstSumOfListS args -> traceRule $
      astSumOfListS $ map (\v -> build1VOccurenceUnknown snat (var, v)) args

    Ast.AstIndexS @sh1 @sh2 v ix -> traceRule $ case stensorKind @y of
     STKS @sh _ _ ->
      withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
      gcastWith (unsafeCoerceRefl
                 :: Take (Rank sh1) (sh1 ++ sh) :~: sh1) $
      gcastWith (unsafeCoerceRefl
                 :: Drop (Rank sh1) (sh1 ++ sh) :~: sh) $
      withListSh (Proxy @sh1) $ \(_ :: IShR rankSh1) ->
      gcastWith (unsafeCoerceRefl :: rankSh1 :~: Rank sh1) $
      build1VIndexS @k @(Rank sh1) (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstSumS v -> traceRule $
      astSumS $ astTrS $ build1V snat (var, v)
    Ast.AstScatterS @shm @shn @shp v (vars, ix) -> traceRule $
      withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astScatterS @(k ': shm) @shn @(k ': shp)
                     (build1VOccurenceUnknown snat (var, v))
                     (Const varFresh ::$ vars, astVarFresh :.$ ix2)
    Ast.AstFromVectorS l -> traceRule $
      astTrS
      $ astFromVectorS (V.map (\v -> build1VOccurenceUnknown snat (var, v)) l)
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
    Ast.AstGatherS @shm @shn @shp v (vars, ix) -> traceRule $
      withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astGatherStepS @(k ': shm) @shn @(k ': shp)
                        (build1VOccurenceUnknown snat (var, v))
                        (Const varFresh ::$ vars, astVarFresh :.$ ix2)
    Ast.AstCastS v -> traceRule $
      astCastS $ build1V snat (var, v)
    Ast.AstFromIntegralS v -> traceRule $
      astFromIntegralS $ build1V snat (var, v)
    Ast.AstProjectS l p -> traceRule $ astProjectS (build1V snat (var, l)) p
    Ast.AstZipS v -> traceRule $
      Ast.AstZipS $ build1V snat (var, v)
    Ast.AstUnzipS v -> traceRule $
      Ast.AstUnzipS $ build1V snat (var, v)

    Ast.AstZipX v -> traceRule $
      Ast.AstZipX $ build1V snat (var, v)
    Ast.AstUnzipX v -> traceRule $
      Ast.AstUnzipX $ build1V snat (var, v)

    Ast.AstRFromS @sh1 v -> traceRule $
      astRFromS @(k ': sh1) $ build1V snat (var, v)
    Ast.AstRFromX @sh1 v -> traceRule $
      astRFromX @(Just k ': sh1) $ build1V snat (var, v)
    Ast.AstSFromR v -> traceRule $ astSFromR $ build1V snat (var, v)
    Ast.AstSFromX v -> traceRule $ astSFromX $ build1V snat (var, v)
    Ast.AstXFromR v -> traceRule $ astXFromR $ build1V snat (var, v)
    Ast.AstXFromS v -> traceRule $ astXFromS $ build1V snat (var, v)

    Ast.AstXNestR @sh1 @m v -> traceRule $
      withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
        astXNestR $ build1V snat (var, v)
    Ast.AstXNestS @sh1 @sh2 v -> traceRule $
      withKnownShX (knownShX @sh1
                    `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
      astXNestS $ build1V snat (var, v)
    Ast.AstXNest  @sh1 @sh2 v -> traceRule $
      withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
       astXNest $ build1V snat (var, v)
    Ast.AstXUnNestR v -> traceRule $ astXUnNestR $ build1V snat (var, v)
    Ast.AstXUnNestS v -> traceRule $ astXUnNestS $ build1V snat (var, v)
    Ast.AstXUnNest v -> traceRule $ astXUnNest $ build1V snat (var, v)

    Ast.AstMkHVector l -> traceRule $
      Ast.AstMkHVector
      $ V.map (\u -> build1VOccurenceUnknownDynamic snat (var, u)) l
    Ast.AstApply @x @z t ll
      | Dict <- lemTensorKindOfBuild snat (stensorKind @x)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z) -> traceRule $
        astHApply
          (build1VHFun snat (var, t))
          (build1VOccurenceUnknown snat (var, ll))
    Ast.AstMapAccumRDer @accShs @bShs @eShs @k5
                        k5@SNat accShs bShs eShs f df rf acc0 es
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
        (Ast.AstMapAccumRDer
           k5
           (buildFTK snat accShs)
           (buildFTK snat bShs)
           (buildFTK snat eShs)
           (build1VHFun snat (var, f))
           (build1VHFun snat (var, df))
           (build1VHFun snat (var, rf))
           (build1VOccurenceUnknown snat (var, acc0))
           (astTrGeneral @k @k5 (stensorKind @eShs)
            $ build1VOccurenceUnknown snat (var, es)))
        (\x1bs1 -> astPair (astProject1 x1bs1)
                           (astTrGeneral @k5 @k
                                         (stensorKind @bShs) (astProject2 x1bs1)))
    Ast.AstMapAccumLDer @accShs @bShs @eShs @k5
                        k5@SNat accShs bShs eShs f df rf acc0 es
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
        (Ast.AstMapAccumLDer
           k5
           (buildFTK snat accShs)
           (buildFTK snat bShs)
           (buildFTK snat eShs)
           (build1VHFun snat (var, f))
           (build1VHFun snat (var, df))
           (build1VHFun snat (var, rf))
           (build1VOccurenceUnknown snat (var, acc0))
           (astTrGeneral @k @k5 (stensorKind @eShs)
            $ build1VOccurenceUnknown snat (var, es)))
        (\x1bs1 -> astPair (astProject1 x1bs1)
                           (astTrGeneral @k5 @k
                                         (stensorKind @bShs) (astProject2 x1bs1)))
    _ -> error $ "TODO: " ++ show v0

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
build1VIndex
  :: forall m n s r k.
     (KnownNat m, KnownNat n, TensorKind r, AstSpan s)
  => SNat k
  -> ( IntVarName
     , AstTensor AstMethodLet s (TKR2 (m + n) r)
     , AstIxR AstMethodLet m )
  -> AstTensor AstMethodLet s (TKR2 (1 + n) r)
build1VIndex snat@SNat (var, v0, ZIR) = build1VOccurenceUnknown snat (var, v0)
build1VIndex snat@SNat (var, v0, ix@(_ :.: _)) =
  let k = sNatValue snat
      traceRule = mkTraceRule "build1VIndex"
                              (Ast.AstBuild1 snat (var, Ast.AstIndex v0 ix))
                              v0 1
  in if varNameInAst var v0
     then case astIndexStep v0 ix of  -- push deeper
       Ast.AstIndex v1 ZIR -> traceRule $
         build1VOccurenceUnknown snat (var, v1)
       v@(Ast.AstIndex @p v1 ix1) -> traceRule $
         let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix1
             ruleD = astGatherStep
                       (k :$: dropShape (shapeAst v1))
                       (build1VOccurenceUnknown snat (var, v1))
                       (varFresh ::: ZR, astVarFresh :.: ix2)
         in if varNameInAst var v1
            then case v1 of  -- try to avoid ruleD if not a normal form
              Ast.AstFromVector{} | valueOf @p == (1 :: Int) -> ruleD
              Ast.AstScatter{} -> ruleD
              _ -> build1VOccurenceUnknown snat (var, v)  -- not a normal form
            else build1VOccurenceUnknown snat (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurenceUnknown snat (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStep (k :$: dropShape (shapeAst v0)) v0 (var ::: ZR, ix)


-- * Vectorization of AstShaped

astTrS :: forall n m sh s r.
          (KnownNat n, KnownNat m, KnownShS sh, TensorKind r, AstSpan s)
       => AstTensor AstMethodLet s (TKS2 (n ': m ': sh) r) -> AstTensor AstMethodLet s (TKS2 (m ': n ': sh) r)
astTrS | SNat <- shsRank (knownShS @sh) =
  astTransposeS (Permutation.makePerm @'[1, 0])
astTrX :: forall n m sh s r.
--          (KnownNat n, KnownNat m, KnownShX sh, GoodScalar r, AstSpan s)
        AstTensor AstMethodLet s (TKX2 (Just n ': Just m ': sh) r) -> AstTensor AstMethodLet s (TKX2 (Just m ': Just n ': sh) r)
astTrX = error "TODO"

intBindingRefreshS
  :: IntVarName -> AstIxS AstMethodLet sh -> (IntVarName, AstInt AstMethodLet, AstIxS AstMethodLet sh)
{-# NOINLINE intBindingRefreshS #-}
intBindingRefreshS var ix =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !ix2 = substituteAstIxS  -- cheap subst, because only a renaming
                 astVarFresh
                 var ix
    in (varFresh, astVarFresh, ix2)

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
              Ast.AstFromVectorS{} | len == 1 -> ruleD
              Ast.AstScatterS{} -> ruleD
              _ -> build1VOccurenceUnknown (SNat @k) (var, v)  -- not a normal form
            else build1VOccurenceUnknown (SNat @k) (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurenceUnknown (SNat @k) (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStepS v0 (Const var ::$ ZS, ix)


-- * Vectorization of others

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

build1VOccurenceUnknownDynamic
  :: forall k s. AstSpan s
  => SNat k -> (IntVarName, AstDynamic AstMethodLet s) -> AstDynamic AstMethodLet s
build1VOccurenceUnknownDynamic SNat (var, d) = case d of
  DynamicRanked u ->
    DynamicRanked $ build1VOccurenceUnknown (SNat @k) (var, u)
  DynamicShaped u ->
    DynamicShaped $ build1VOccurenceUnknown (SNat @k) (var, u)
  DynamicRankedDummy @r @sh _ _ -> DynamicRankedDummy @r @(k ': sh) Proxy Proxy
  DynamicShapedDummy @r @sh _ _ -> DynamicShapedDummy @r @(k ': sh) Proxy Proxy
{- TODO: is this faster? but fromInteger has to be avoided
  DynamicRankedDummy @r @sh _ _ ->
    withListSh (Proxy @sh) $ \_ ->
      DynamicRanked @r (Ast.AstRFromS @(k ': sh) @s @r 0)
  DynamicShapedDummy @r @sh _ _ -> DynamicShaped @r @(k ': sh) 0
-}


-- * Auxiliary machinery

substProjRep
  :: forall k s s2 y2 y.
     ( AstSpan s, AstSpan s2, TensorKind y2, TensorKind y )
  => SNat k -> IntVarName
  -> FullTensorKind y2 -> AstVarName s2 y2 -> AstTensor AstMethodLet s y
  -> ( AstVarName s2 (BuildTensorKind k y2)
     , FullTensorKind (BuildTensorKind k y2)
     , AstTensor AstMethodLet s y )
substProjRep snat@SNat var ftk2 var1 v
  | Dict <- lemTensorKindOfBuild snat (stensorKind @y2) =
    let var3 :: AstVarName s2 (BuildTensorKind k y2)
        var3 = mkAstVarName (varNameToAstVarId var1)
        ftk3 = buildFTK snat ftk2
        astVar3 = Ast.AstVar ftk3 var3
        projection :: AstTensor AstMethodLet s2 (BuildTensorKind k y4)
                   -> FullTensorKind y4
                   -> AstTensor AstMethodLet s2 y4
        projection prVar = \case
          FTKScalar -> prVar
          FTKR sh FTKScalar | SNat <- shrRank sh ->
            Ast.AstIndex prVar (Ast.AstIntVar var :.: ZIR)
          FTKS sh FTKScalar -> withKnownShS sh
                     $ Ast.AstIndexS prVar (Ast.AstIntVar var :.$ ZIS)
          FTKX sh FTKScalar -> withKnownShX (ssxFromShape sh)
                     $ Ast.AstIndexX prVar (Ast.AstIntVar var :.% ZIX)
          FTKProduct ftk41 ftk42
            | Dict <- lemTensorKindOfSTK (ftkToStk ftk41)
            , Dict <- lemTensorKindOfSTK (ftkToStk ftk42)
            , Dict <- lemTensorKindOfBuild snat (ftkToStk ftk41)
            , Dict <- lemTensorKindOfBuild snat (ftkToStk ftk42) ->
              let prVar1 = astProject1 prVar
                  prVar2 = astProject2 prVar
              in astPair (projection prVar1 ftk41)
                         (projection prVar2 ftk42)
          ftk@(FTKUntyped shs0) -> case buildFTK snat ftk of
            FTKUntyped shs -> fun1DToAst shs $ \ !vars !asts ->
              let projDyn :: DynamicTensor (AstTensor AstMethodLet s2)
                          -> DynamicTensor VoidTensor
                          -> DynamicTensor (AstTensor AstMethodLet s2)
                  projDyn (DynamicRanked @_ @n2 t)
                          (DynamicRankedDummy @_ @sh3 _ _)
                    | Just Refl <- matchingRank @(k ': sh3) @n2 =
                      withListSh (Proxy @sh3) $ \sh1 ->
                        DynamicRanked $ projection t (FTKR sh1 FTKScalar)
                  projDyn (DynamicShaped @_ @sh2 t)
                          (DynamicShapedDummy @_ @sh3 _ _)
                    | Just Refl <- sameShape @sh2 @(k ': sh3) =
                      DynamicShaped $ projection t (FTKS @sh3 knownShS FTKScalar)
                  projDyn _ _ = error "projDyn: impossible DynamicTensor cases"
              in astLetHVectorIn
                   vars
                   prVar
                   (Ast.AstMkHVector $ V.zipWith projDyn asts shs0)
          _ -> error $ "TODO: " ++ show prVar
        v2 = substituteAst
               (projection astVar3 ftk2)
               var1 v
    in (var3, ftk3, v2)

substProjRanked :: forall n1 r1 s1 s y.
                   ( KnownNat n1, GoodScalar r1, AstSpan s, AstSpan s1
                   , TensorKind y )
                => Int -> IntVarName -> IShR n1
                -> AstVarName s1 (TKR n1 r1)
                -> AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
substProjRanked k var sh1 var1 =
  let var2 = mkAstVarName @s1 @(TKR (1 + n1) r1) (varNameToAstVarId var1)  -- changed shape; TODO: shall we rename?
      projection =
        Ast.AstIndex (Ast.AstVar (FTKR (k :$: sh1) FTKScalar) var2)
                     (Ast.AstIntVar var :.: ZIR)
  in substituteAst
       projection var1
         -- The subsitutions of projections don't break sharing,
         -- because they don't duplicate variables and the added var
         -- is eventually being eliminated instead of substituted for.

substProjShaped :: forall k sh1 r1 s1 s y.
                   ( KnownNat k, KnownShS sh1, GoodScalar r1
                   , AstSpan s, AstSpan s1, TensorKind y )
                => IntVarName -> AstVarName s1 (TKS sh1 r1)
                -> AstTensor AstMethodLet s y -> AstTensor AstMethodLet s y
substProjShaped var var1 =
  let var2 = mkAstVarName @s1 @(TKS (k : sh1) r1) (varNameToAstVarId var1)
      projection =
        Ast.AstIndexS (Ast.AstVar @(TKS (k ': sh1) r1) (FTKS knownShS FTKScalar) var2)
                      (Ast.AstIntVar var :.$ ZIS)
  in substituteAst
       projection var1

substProjDynamic :: forall k s y. (KnownNat k, AstSpan s, TensorKind y)
                 => IntVarName -> AstTensor AstMethodLet s y
                 -> AstDynamicVarName
                 -> (AstTensor AstMethodLet s y, AstDynamicVarName)
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

substProjVars :: forall k s y. (KnownNat k, AstSpan s, TensorKind y)
              => IntVarName -> [AstDynamicVarName]
              -> AstTensor AstMethodLet s y
              -> (AstTensor AstMethodLet s y, [AstDynamicVarName])
substProjVars var vars v3 = mapAccumR (substProjDynamic @k var) v3 vars

astTrDynamic :: AstSpan s
             => DynamicTensor (AstTensor AstMethodLet s)
             -> DynamicTensor (AstTensor AstMethodLet s)
astTrDynamic t@(DynamicRanked @_ @n1 u) =
  case cmpNat (Proxy @2) (Proxy @n1) of
    EQI -> DynamicRanked $ astTr @(n1 - 2) u
    LTI -> DynamicRanked $ astTr @(n1 - 2) u
    _ -> t
astTrDynamic t@(DynamicShaped @_ @sh u) | SNat @n <- shsRank (knownShS @sh) =
  case cmpNat (Proxy @2) (Proxy @n) of
    LTI -> withKnownShS (shsPermutePrefix (Permutation.makePerm @'[1, 0])
                                          (knownShS @sh)) $
           DynamicShaped $ astTransposeS (Permutation.makePerm @'[1, 0]) u
    EQI -> withKnownShS (shsPermutePrefix (Permutation.makePerm @'[1, 0])
                                          (knownShS @sh)) $
           DynamicShaped $ astTransposeS (Permutation.makePerm @'[1, 0]) u
    GTI -> t
astTrDynamic (DynamicRankedDummy p1 (Proxy @sh1)) =
  withKnownShS (shsPermutePrefix (Permutation.makePerm @'[1, 0])
                                 (knownShS @sh1)) $
  DynamicRankedDummy p1 (Proxy @(Permutation.PermutePrefix '[1, 0] sh1))
astTrDynamic (DynamicShapedDummy p1 (Proxy @sh1)) =
  withKnownShS (shsPermutePrefix (Permutation.makePerm @'[1, 0])
                                 (knownShS @sh1)) $
  DynamicShapedDummy p1 (Proxy @(Permutation.PermutePrefix '[1, 0] sh1))

astTrAstHVector :: forall s. AstSpan s
                => AstTensor AstMethodLet s TKUntyped
                -> AstTensor AstMethodLet s TKUntyped
astTrAstHVector t =
  fun1DToAst (shapeAstHVector t) $ \ !vars !asts ->
    astLetHVectorIn
      vars
      t
      (Ast.AstMkHVector @_ @s $ V.map astTrDynamic asts)

astTrGeneral
  :: forall k1 k2 s y. (AstSpan s, KnownNat k1, KnownNat k2)
  => STensorKindType y
  -> AstTensor AstMethodLet s (BuildTensorKind k1 (BuildTensorKind k2 y))
  -> AstTensor AstMethodLet s (BuildTensorKind k2 (BuildTensorKind k1 y))
astTrGeneral stk t = case stk of
  STKScalar{} -> t
  STKR SNat stk1 | Dict <- lemTensorKindOfSTK stk1 ->
    astTr t
  STKS sh stk1 | Dict <- lemTensorKindOfSTK stk1 ->
    withKnownShS sh $ astTrS t
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
        in astPair (astTrGeneral @k1 @k2 stk1 u1) (astTrGeneral @k1 @k2 stk2 u2)
  STKUntyped -> astTrAstHVector t


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
