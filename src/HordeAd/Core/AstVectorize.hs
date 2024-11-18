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
import Data.List (mapAccumR)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat, OrderingI (..), cmpNat, type (+), type (-))
import System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (pattern (:.%), pattern ZIX, ssxFromShape)
import Data.Array.Nested
  ( IShR
  , IxS (..)
  , KnownShS (..)
  , ListS (..)
  , Rank
  , ShR (..)
  , pattern (:$:)
  , pattern (:.$)
  , pattern (:.:)
  , pattern (::$)
  , pattern (:::)
  , pattern ZIR
  , pattern ZIS
  , pattern ZR
  , pattern ZS
  , type (++)
  )
import Data.Array.Nested.Internal.Shape (shrRank)

import HordeAd.Core.Ast (AstTensor)
import HordeAd.Core.Ast hiding (AstBool (..), AstTensor (..))
import HordeAd.Core.Ast qualified as Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Util.SizedList

-- This abbreviation is used a lot below.
astTr :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
      => AstTensor AstMethodLet s (TKR (2 + n) r) -> AstTensor AstMethodLet s (TKR (2 + n) r)
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
build1VOccurenceUnknown snat@SNat (var, v0)
  | Dict <- lemTensorKindOfBuild snat (stensorKind @y) =
    let traceRule = mkTraceRule "build1VOcc" (Ast.AstBuild1 snat (var, v0)) v0 1
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
  :: IntVarName -> AstIndex AstMethodLet n -> (IntVarName, AstInt AstMethodLet, AstIndex AstMethodLet n)
{-# NOINLINE intBindingRefresh #-}
intBindingRefresh var ix =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !ix2 = substituteAstIndex  -- cheap subst, because only a renaming
                 astVarFresh
                 var ix
    in (varFresh, astVarFresh, ix2)

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1V
  :: forall k s y. (AstSpan s, TensorKind y)
  => SNat k -> (IntVarName, AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
build1V snat@SNat (var, v00) =
  let k = sNatValue snat
      v0 = astNonIndexStep v00
        -- Almost surely the term will be transformed, so it can just
        -- as well we one-step simplified first (many steps if redexes
        -- get uncovered and so the simplification requires only constant
        -- look-ahead, but has a guaranteed net benefit).
      bv = Ast.AstBuild1 snat (var, v0)
      traceRule | Dict <- lemTensorKindOfBuild snat (stensorKind @y) =
        mkTraceRule "build1V" bv v0 1
  in case v0 of
    Ast.AstScalar t ->
      build1V snat (var, t)
    Ast.AstUnScalar t ->
      build1V snat (var, t)
    Ast.AstPair @x @z t1 t2
      | Dict <- lemTensorKindOfBuild snat (stensorKind @x)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z) ->
        astPair (build1VOccurenceUnknown snat (var, t1))
                 (build1VOccurenceUnknown snat (var, t2))
    Ast.AstProject1 @_ @z t
      | Dict <- lemTensorKindOfBuild snat (stensorKind @z)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
        astProject1 (build1V snat (var, t))
    Ast.AstProject2 @x t
      | Dict <- lemTensorKindOfBuild snat (stensorKind @x)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
        astProject2 (build1V snat (var, t))
    Ast.AstVar _ var2 | varNameToAstVarId var2 == varNameToAstVarId var ->
      case isTensorInt v0 of
        Just Refl -> fromPrimal @s $ Ast.AstIotaS @k
        _ -> error "build1V: build variable is not an index variable"
    Ast.AstVar{} ->
      error "build1V: AstVar can't contain other free index variables"
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
    Ast.AstCond b (Ast.AstFromPrimal v)
                  (Ast.AstFromPrimal w) -> case stensorKind @y of
      STKScalar _ ->
        let t = Ast.AstFromPrimal
                $ astIndexStep (astFromVector
                                $ V.fromList [Ast.AstScalar v, Ast.AstScalar w])
                               (singletonIndex (astCond b 0 1))
        in build1VOccurenceUnknown snat (var, t)
      STKR SNat STKScalar{} ->
        let t = Ast.AstFromPrimal
                $ astIndexStep (astFromVector $ V.fromList [v, w])
                               (singletonIndex (astCond b 0 1))
        in build1VOccurenceUnknown snat (var, t)
      STKS sh STKScalar{} -> withKnownShS sh $
        let t = Ast.AstFromPrimal
                $ astIndexStepS @'[2] (astFromVectorS $ V.fromList [v, w])
                                      (astCond b 0 1 :.$ ZIS)
        in build1VOccurenceUnknown snat (var, t)
      STKX{} -> error "TODO"
      STKProduct{} -> error "TODO"
      STKUntyped -> error "TODO"
      _ -> error "TODO"
    Ast.AstCond b v w -> case stensorKind @y of
      STKScalar _ ->
        let t = astIndexStep (astFromVector
                              $ V.fromList [Ast.AstScalar v, Ast.AstScalar w])
                             (singletonIndex (astCond b 0 1))
        in build1VOccurenceUnknown snat (var, t)
      STKR SNat STKScalar{} ->
        let t = astIndexStep (astFromVector $ V.fromList [v, w])
                             (singletonIndex (astCond b 0 1))
        in build1VOccurenceUnknown snat (var, t)
      STKS sh  STKScalar{}-> withKnownShS sh $
        let t = astIndexStepS @'[2] (astFromVectorS $ V.fromList [v, w])
                                    (astCond b 0 1 :.$ ZIS)
        in build1VOccurenceUnknown snat (var, t)
      STKX{} -> error "TODO"
      STKProduct{} -> error "TODO"
      STKUntyped -> error "TODO"
      _ -> error "TODO"
    Ast.AstReplicate @y2 snat2@(SNat @k2) v -> traceRule $
      let repl2Stk :: forall z.
                      STensorKindType z
                   -> AstTensor AstMethodLet s (BuildTensorKind k z)
                   -> AstTensor AstMethodLet s (BuildTensorKind k
                                                  (BuildTensorKind k2 z))
          repl2Stk stk u = case stk of
            STKScalar _ -> astTr $ astReplicate snat2 u
            STKR SNat STKScalar{} -> astTr $ astReplicate snat2 u
            STKS sh STKScalar{} -> withKnownShS sh $ astTrS $ astReplicate snat2 u
            STKX sh STKScalar{} -> withKnownShX sh $ astTrX $ astReplicate snat2 u
            STKProduct @z1 @z2 stk1 stk2
              | Dict <- lemTensorKindOfBuild snat stk1
              , Dict <- lemTensorKindOfBuild snat2 stk1
              , Dict <- lemTensorKindOfBuild
                          snat (stensorKind @(BuildTensorKind k2 z1))
              , Dict <- lemTensorKindOfBuild snat stk2
              , Dict <- lemTensorKindOfBuild snat2 stk2
              , Dict <- lemTensorKindOfBuild
                          snat (stensorKind @(BuildTensorKind k2 z2)) ->
                astLetFun u $ \ !uShared ->
                  let (u1, u2) = (astProject1 uShared, astProject2 uShared)
                  in astPair (repl2Stk stk1 u1) (repl2Stk stk2 u2)
            STKUntyped ->
              astTrAstHVector
              $ fun1DToAst (shapeAstHVector u) $ \ !vars !asts ->
                  astLetHVectorIn
                    vars
                    u
                    (Ast.AstMkHVector
                     $ replicate1HVectorF
                         (\k3 -> withSNat k3 $ \snat3 -> astReplicate snat3)
                         (astReplicate SNat)
                         snat2 asts)
            _ -> error "TODO"
     in repl2Stk (stensorKind @y2) (build1V snat (var, v))
    Ast.AstBuild1{} -> error "build1V: impossible case of AstBuild1"
    Ast.AstLet @y2 var1 u v
      | Dict <- lemTensorKindOfBuild snat (stensorKind @y2)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @y) ->
        let ftk2 = ftkAst u
            (var3, _ftk3, v2) =
              substProjRep snat var ftk2 var1 v
        in astLet var3 (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknownRefresh snat (var, v2))
             -- ensures no duplicated bindings, see below

    Ast.AstMinIndex v -> Ast.AstMinIndex $ build1V snat (var, v)
    Ast.AstMaxIndex v -> Ast.AstMaxIndex $ build1V snat (var, v)
    Ast.AstFloor v -> Ast.AstFloor $ build1V snat (var, v)
    Ast.AstIota ->
      error "build1V: AstIota can't have free index variables"

    Ast.AstN1 opCode u -> traceRule $
      Ast.AstN1 opCode (build1VOccurenceUnknown snat (var, u))
    Ast.AstN2 opCode u v -> traceRule $
      Ast.AstN2 opCode (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknown snat (var, v))
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstR1 opCode u -> traceRule $
      Ast.AstR1 opCode (build1VOccurenceUnknown snat (var, u))
    Ast.AstR2 opCode u v -> traceRule $
      Ast.AstR2 opCode (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknown snat (var, v))
    Ast.AstI2 opCode u v -> traceRule $
      Ast.AstI2 opCode (build1VOccurenceUnknown snat (var, u))
                       (build1VOccurenceUnknown snat (var, v))
    Ast.AstSumOfList args -> traceRule $
      astSumOfList $ map (\v -> build1VOccurenceUnknown snat (var, v)) args

    Ast.AstIndex v ix -> traceRule $
      build1VIndex snat (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstSum v -> traceRule $
      astSum $ astTr $ build1V snat (var, v)
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
    Ast.AstCast v -> astCast $ build1V snat (var, v)
    Ast.AstFromIntegral v -> astFromIntegral $ build1V snat (var, v)
    Ast.AstConcrete{} ->
      error "build1V: AstConcrete can't have free index variables"

    Ast.AstProjectR l p ->
      astProjectR (build1VOccurenceUnknown snat (var, l)) p
    Ast.AstLetHVectorIn @_ @_ @z vars1 l v
     | Dict <- lemTensorKindOfBuild snat (stensorKind @z) ->
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
    Ast.AstRFromS @sh1 v ->
      astRFromS @(k ': sh1) $ build1V snat (var, v)

    Ast.AstMinIndexS v -> Ast.AstMinIndexS $ build1V snat (var, v)
    Ast.AstMaxIndexS v -> Ast.AstMaxIndexS $ build1V snat (var, v)
    Ast.AstFloorS v -> Ast.AstFloorS $ build1V snat (var, v)
    Ast.AstIotaS ->
      error "build1V: AstIotaS can't have free index variables"

    Ast.AstN1S opCode u -> traceRule $
      Ast.AstN1S opCode (build1VOccurenceUnknown snat (var, u))
    Ast.AstN2S opCode u v -> traceRule $
      Ast.AstN2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another unlike. e.g., inside a let,
        -- which may get inlined
    Ast.AstR1S opCode u -> traceRule $
      Ast.AstR1S opCode (build1VOccurenceUnknown snat (var, u))
    Ast.AstR2S opCode u v -> traceRule $
      Ast.AstR2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
    Ast.AstI2S opCode u v -> traceRule $
      Ast.AstI2S opCode (build1VOccurenceUnknown snat (var, u))
                        (build1VOccurenceUnknown snat (var, v))
    Ast.AstSumOfListS args -> traceRule $
      astSumOfListS $ map (\v -> build1VOccurenceUnknown snat (var, v)) args

    Ast.AstIndexS @sh1 v ix -> traceRule $ case stensorKind @y of
     STKS @sh _ _ ->
      gcastWith (unsafeCoerce Refl
                 :: Take (Rank sh1) (sh1 ++ sh) :~: sh1) $
      gcastWith (unsafeCoerce Refl
                 :: Drop (Rank sh1) (sh1 ++ sh) :~: sh) $
      withListSh (Proxy @sh1) $ \(_ :: IShR rankSh1) ->
      gcastWith (unsafeCoerce Refl :: rankSh1 :~: Rank sh1) $
      build1VIndexS @k @(Rank sh1) (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstSumS v -> traceRule $
      astSumS $ astTrS $ build1V snat (var, v)
    Ast.AstScatterS @sh2 @p @sh3 v (vars, ix) -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: Take (1 + p) (k : sh3) :~: (k : Take p sh3)) $
      gcastWith (unsafeCoerce Refl
                 :: Drop (1 + p) (k : sh3) :~: Drop p sh3) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astScatterS @(k ': sh2) @(1 + p)
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
        gcastWith (unsafeCoerce Refl
                   :: Permutation.PermutePrefix (0 : Permutation.MapSucc perm) (k : sh1) :~: k : sh) $
        gcastWith (unsafeCoerce Refl
                   :: Rank (0 : Permutation.MapSucc perm) :~: 1 + Rank perm) $
        trustMeThisIsAPermutation @(0 : Permutation.MapSucc perm)
        $ astTransposeS zsuccPerm $ build1V snat (var, v)
    Ast.AstReshapeS @sh2 v -> traceRule $
      astReshapeS $ build1V snat (var, v)
    Ast.AstGatherS @sh2 @p @sh3 v (vars, ix) -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: Take (1 + p) (k : sh3) :~: (k : Take p sh3)) $
      gcastWith (unsafeCoerce Refl
                 :: Drop (1 + p) (k : sh3) :~: Drop p sh3) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astGatherStepS @(k ': sh2) @(1 + p)
                        (build1VOccurenceUnknown snat (var, v))
                        (Const varFresh ::$ vars, astVarFresh :.$ ix2)
    Ast.AstCastS v -> astCastS $ build1V snat (var, v)
    Ast.AstFromIntegralS v -> astFromIntegralS $ build1V snat (var, v)
    Ast.AstConcreteS{} ->
      error "build1V: AstConcreteS can't have free index variables"

    Ast.AstProjectS l p ->
      astProjectS (build1VOccurenceUnknown snat (var, l)) p
    Ast.AstSFromR v -> astSFromR $ build1V snat (var, v)

    Ast.AstMkHVector l -> traceRule $
      Ast.AstMkHVector
      $ V.map (\u -> build1VOccurenceUnknownDynamic snat (var, u)) l
    Ast.AstApply @x @z t ll
      | Dict <- lemTensorKindOfBuild snat (stensorKind @x)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z) -> traceRule $
        astHApply
          (build1VHFun snat (var, t))
          (build1VOccurenceUnknown snat (var, ll))
    Ast.AstBuildHVector1{} -> traceRule $
      error "build1V: impossible case of AstBuildHVector1"
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
     , Just Refl <- lemBuildOfAD snat (stensorKind @accShs)
     , Just Refl <- lemBuildOfAD snat (stensorKind @bShs)
     , Just Refl <- lemBuildOfAD snat (stensorKind @eShs) -> traceRule $
      astLetFun
        (Ast.AstMapAccumRDer
           k5
           (buildFullTensorKind snat accShs)
           (buildFullTensorKind snat bShs)
           (buildFullTensorKind snat eShs)
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
     , Just Refl <- lemBuildOfAD snat (stensorKind @accShs)
     , Just Refl <- lemBuildOfAD snat (stensorKind @bShs)
     , Just Refl <- lemBuildOfAD snat (stensorKind @eShs) -> traceRule $
      astLetFun
        (Ast.AstMapAccumLDer
           k5
           (buildFullTensorKind snat accShs)
           (buildFullTensorKind snat bShs)
           (buildFullTensorKind snat eShs)
           (build1VHFun snat (var, f))
           (build1VHFun snat (var, df))
           (build1VHFun snat (var, rf))
           (build1VOccurenceUnknown snat (var, acc0))
           (astTrGeneral @k @k5 (stensorKind @eShs)
            $ build1VOccurenceUnknown snat (var, es)))
        (\x1bs1 -> astPair (astProject1 x1bs1)
                            (astTrGeneral @k5 @k
                                          (stensorKind @bShs) (astProject2 x1bs1)))
    _ -> error "TODO"

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
     (KnownNat m, KnownNat n, GoodScalar r, AstSpan s)
  => SNat k -> (IntVarName, AstTensor AstMethodLet s (TKR (m + n) r), AstIndex AstMethodLet m)
  -> AstTensor AstMethodLet s (TKR (1 + n) r)
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

-- TODO: we avoid constraint KnownNat (Rank sh) that would infect
-- a lot of AstShaped constructor and from there a lot of the codebase.
-- This should be solved in a cleaner way.
--
-- This abbreviation is used a lot below.
astTrS :: forall n m sh s r.
          (KnownNat n, KnownNat m, KnownShS sh, GoodScalar r, AstSpan s)
       => AstTensor AstMethodLet s (TKS (n ': m ': sh) r) -> AstTensor AstMethodLet s (TKS (m ': n ': sh) r)
astTrS = withListSh (Proxy @sh) $ \_ -> astTransposeS (Permutation.makePerm @'[1, 0])
astTrX :: forall n m sh s r.
--          (KnownNat n, KnownNat m, KnownShX sh, GoodScalar r, AstSpan s)
        AstTensor AstMethodLet s (TKX (Just n ': Just m ': sh) r) -> AstTensor AstMethodLet s (TKX (Just m ': Just n ': sh) r)
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
     ( GoodScalar r, KnownNat k, KnownNat p, KnownShS sh, KnownShS (Take p sh)
     , KnownShS (Drop p (Take p sh ++ Drop p sh)), AstSpan s )
  => (IntVarName, AstTensor AstMethodLet s (TKS sh r), AstIxS AstMethodLet (Take p sh))
  -> AstTensor AstMethodLet s (TKS (k ': Drop p sh) r)
build1VIndexS (var, v0, ZIS) =
  gcastWith (unsafeCoerce Refl :: p :~: 0)
    -- otherwise sh would need to be empty, but then Take gets stuck
    -- so the application of this function wouldn't type-check
  $ build1VOccurenceUnknown (SNat @k) (var, v0)
build1VIndexS (var, v0, ix@(_ :.$ _)) =
  gcastWith (unsafeCoerce Refl :: sh :~: Take p sh ++ Drop p sh) $
  let vTrace = Ast.AstBuild1 (SNat @k) (var, Ast.AstIndexS v0 ix)
      traceRule = mkTraceRule "build1VIndexS" vTrace v0 1
  in if varNameInAst var v0
     then case astIndexStepS v0 ix of  -- push deeper
       Ast.AstIndexS v1 ZIS -> traceRule $
         build1VOccurenceUnknown (SNat @k) (var, v1)
       v@(Ast.AstIndexS @sh1 v1 ix1) -> traceRule $
         gcastWith (unsafeCoerce Refl
                    :: k ': sh1 :~: Take (1 + Rank sh1)
                                            (k ': sh1 ++ Drop p sh)) $
         gcastWith (unsafeCoerce Refl
                    :: Drop p sh
                       :~: Drop (1 + Rank sh1)
                                   (k ': sh1 ++ Drop p sh)) $
         withListSh (Proxy @(k ': sh1)) $ \(_ :: IShR rankSh1Plus1) ->
         gcastWith (unsafeCoerce Refl :: rankSh1Plus1 :~: 1 + Rank sh1) $
         let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix1
             ruleD = astGatherStepS @'[k] @(1 + Rank sh1)
                                    (build1VOccurenceUnknown (SNat @k) (var, v1))
                                    (Const varFresh ::$ ZS, astVarFresh :.$ ix2)
             len = length $ shapeT @sh1
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
        ftk3 = buildFullTensorKind snat ftk2
        astVar3 = Ast.AstVar ftk3 var3
        projection :: AstTensor AstMethodLet s2 (BuildTensorKind k y4)
                   -> FullTensorKind y4
                   -> AstTensor AstMethodLet s2 y4
        projection prVar = \case
          FTKScalar ->
            Ast.AstUnScalar $ Ast.AstIndex prVar (Ast.AstIntVar var :.: ZIR)
          FTKR sh | SNat <- shrRank sh ->
            Ast.AstIndex prVar (Ast.AstIntVar var :.: ZIR)
          FTKS sh -> withKnownShS sh
                     $ Ast.AstIndexS prVar (Ast.AstIntVar var :.$ ZIS)
          FTKX sh -> withKnownShX (ssxFromShape sh)
                     $ Ast.AstIndexX prVar (Ast.AstIntVar var :.% ZIX)
          FTKProduct @z1 @z2 ftk41 ftk42
            | Dict <- lemTensorKindOfF ftk41
            , Dict <- lemTensorKindOfF ftk42
            , Dict <- lemTensorKindOfBuild snat (stensorKind @z1)
            , Dict <- lemTensorKindOfBuild snat (stensorKind @z2) ->
              let prVar1 = astProject1 prVar
                  prVar2 = astProject2 prVar
              in astPair (projection prVar1 ftk41)
                         (projection prVar2 ftk42)
          ftk@(FTKUntyped shs0) -> case buildFullTensorKind snat ftk of
            FTKUntyped shs -> fun1DToAst shs $ \ !vars !asts ->
              let projDyn :: DynamicTensor (AstTensor AstMethodLet s2)
                          -> DynamicTensor VoidTensor
                          -> DynamicTensor (AstTensor AstMethodLet s2)
                  projDyn (DynamicRanked @_ @n2 t)
                          (DynamicRankedDummy @_ @sh3 _ _)
                    | Just Refl <- matchingRank @(k ': sh3) @n2 =
                      withListSh (Proxy @sh3) $ \sh1 ->
                        DynamicRanked $ projection t (FTKR sh1)
                  projDyn (DynamicShaped @_ @sh2 t)
                          (DynamicShapedDummy @_ @sh3 _ _)
                    | Just Refl <- sameShape @sh2 @(k ': sh3) =
                      DynamicShaped $ projection t (FTKS @sh3 knownShS)
                  projDyn _ _ = error "projDyn: impossible DynamicTensor cases"
              in astLetHVectorIn
                   vars
                   prVar
                   (Ast.AstMkHVector $ V.zipWith projDyn asts shs0)
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
        Ast.AstIndex (Ast.AstVar (FTKR $ k :$: sh1) var2)
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
        Ast.AstIndexS (Ast.AstVar @(TKS (k ': sh1) r1) (FTKS knownShS) var2)
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
             => DynamicTensor (AstTensor AstMethodLet s) -> DynamicTensor (AstTensor AstMethodLet s)
astTrDynamic t@(DynamicRanked @_ @n1 u) =
  case cmpNat (Proxy @2) (Proxy @n1) of
    EQI -> DynamicRanked $ astTr @(n1 - 2) u
    LTI -> DynamicRanked $ astTr @(n1 - 2) u
    _ -> t
astTrDynamic t@(DynamicShaped @_ @sh u) =
  let sh1 = shapeT @sh
      permute10 (m0 : m1 : ms) = m1 : m0 : ms
      permute10 ms = ms
      sh1Permuted = permute10 sh1
  in withShapeP sh1Permuted $ \(Proxy @shPermuted) ->
       withListSh (Proxy @sh) $ \_ ->
         case cmpNat (Proxy @2) (Proxy @(Rank sh)) of
           EQI -> case astTransposeS (Permutation.makePerm @'[1, 0]) u of
             (w :: AstTensor AstMethodLet s4 (TKS sh4 r4)) ->
               gcastWith (unsafeCoerce Refl :: sh4 :~: shPermuted) $
               DynamicShaped w
           LTI -> case astTransposeS (Permutation.makePerm @'[1, 0]) u of
             (w :: AstTensor AstMethodLet s4 (TKS sh4 r4)) ->
               gcastWith (unsafeCoerce Refl :: sh4 :~: shPermuted) $
               DynamicShaped w
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
                => AstTensor AstMethodLet s TKUntyped -> AstTensor AstMethodLet s TKUntyped
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
  STKScalar _ -> astTr t
  STKR SNat STKScalar{} -> astTr t
  STKS sh STKScalar{} -> withKnownShS sh $ astTrS t
  STKX sh STKScalar{} -> withKnownShX sh $ astTrX t
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
  _ -> error "TODO"


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

mkTraceRule :: forall y z s. (TensorKind y, AstSpan s)
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
