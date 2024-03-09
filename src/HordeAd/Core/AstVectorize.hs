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

import           Control.Exception.Assert.Sugar
import           Control.Monad (when)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import           Data.Int (Int64)
import           Data.IORef
import           Data.List (mapAccumR)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.IntMap as IM
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , SomeNat (..)
  , cmpNat
  , someNatVal
  , type (+)
  , type (-)
  )
import           System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import           System.IO.Unsafe (unsafePerformIO)
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast hiding
  (AstBool (..), AstHVector (..), AstRanked (..), AstShaped (..))
import           HordeAd.Core.Ast (AstHVector, AstRanked, AstShaped)
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstPrettyPrint
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.HVector
import           HordeAd.Core.HVectorOps
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (MapSucc, trustMeThisIsAPermutation)
import           HordeAd.Util.ShapedList (ShapedList (..))
import           HordeAd.Util.SizedIndex
import           HordeAd.Util.SizedList

-- * Vectorization of AstRanked

-- This abbreviation is used a lot below.
astTr :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
      => AstRanked s r (2 + n) -> AstRanked s r (2 + n)
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
  => Int -> (IntVarName, AstRanked s r n) -> AstRanked s r (1 + n)
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

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => Int -> (IntVarName, AstRanked s r n) -> AstRanked s r (1 + n)
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
  => Int -> (IntVarName, AstRanked s r n) -> AstRanked s r (1 + n)
{-# NOINLINE build1VOccurenceUnknownRefresh #-}
build1VOccurenceUnknownRefresh k (var, v0) =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !v2 = substituteAst  -- cheap subst, because only a renaming
                (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh)
                var v0
    in build1VOccurenceUnknown k (varFresh, v2)

intBindingRefresh
  :: IntVarName -> AstIndex n -> (IntVarName, AstInt, AstIndex n)
{-# NOINLINE intBindingRefresh #-}
intBindingRefresh var ix =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !ix2 = substituteAstIndex  -- cheap subst, because only a renaming
                 (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh)
                 var ix
    in (varFresh, astVarFresh, ix2)

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1V
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => Int -> (IntVarName, AstRanked s r n) -> AstRanked s r (1 + n)
build1V k (var, v00) =
  let v0 = simplifyStepNonIndex v00
        -- Almost surely the term will be transformed, so it can just
        -- as well we one-step simplified first (many steps if redexes
        -- get uncovered and so the simplification requires only constant
        -- look-ahead, but has a guaranteed net benefit).
      bv = Ast.AstBuild1 k (var, v0)
      traceRule = mkTraceRule "build1V" bv v0 1
  in case v0 of
    Ast.AstVar _ var2 | fromEnum var2 == fromEnum var ->
      case isRankedInt v0 of
        Just Refl -> fromPrimal @s @Int64 $ astSlice 0 k Ast.AstIota
        _ -> error "build1V: build variable is not an index variable"
    Ast.AstVar{} ->
      error "build1V: AstVar can't contain other free index variables"
    Ast.AstLet @_ @_ @r1 @_ @s1 var1@(AstVarName oldVarId) u v ->
      let var2 = AstVarName oldVarId  -- changed shape; TODO: shall we rename?
          sh = shapeAst u
          projection = Ast.AstIndex (Ast.AstVar (k :$: sh) var2)
                                    (Ast.AstIntVar var :.: ZIR)
          -- The subsitutions of projections don't break sharing,
          -- because they don't duplicate variables and the added var
          -- is eventually being eliminated instead of substituted for.
          v2 = substituteAst
                 (SubstitutionPayloadRanked @s1 @r1 projection) var1 v
      in astLet var2 (build1VOccurenceUnknown k (var, u))
                     (build1VOccurenceUnknownRefresh k (var, v2))
                        -- ensure no duplicated bindings, see below
    Ast.AstLetADShare{} -> error "build1V: AstLetADShare"
    Ast.AstCond b (Ast.AstConstant v) (Ast.AstConstant w) ->
      let t = Ast.AstConstant
              $ astIndexStep (astFromList [v, w])
                             (singletonIndex (astCond b 0 1))
      in build1V k (var, t)
    Ast.AstCond b v w ->
      let t = astIndexStep (astFromList [v, w])
                           (singletonIndex (astCond b 0 1))
      in build1V k (var, t)

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

    Ast.AstConstant v -> traceRule $
      Ast.AstConstant $ build1V k (var, v)
    Ast.AstPrimalPart v -> traceRule $
      astPrimalPart $ build1V k (var, v)
    Ast.AstDualPart v -> traceRule $
      astDualPart $ build1V k (var, v)
    Ast.AstD u u' -> traceRule $
      Ast.AstD (build1VOccurenceUnknown k (var, u))
               (build1VOccurenceUnknown k (var, u'))

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
  => Int -> (IntVarName, AstRanked s r (m + n), AstIndex m)
  -> AstRanked s r (1 + n)
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
              Ast.AstFromList{} | valueOf @p == (1 :: Int) -> ruleD
              Ast.AstFromVector{} | valueOf @p == (1 :: Int) -> ruleD
              Ast.AstScatter{} -> ruleD
              Ast.AstAppend{} -> ruleD
              _ -> build1VOccurenceUnknown k (var, v)  -- not a normal form
            else build1VOccurenceUnknown k (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurenceUnknown k (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStep (k :$: dropShape (shapeAst v0)) v0 (var ::: ZR, ix)


-- * Vectorization of AstShaped

-- TODO: we avoid constraint KnownNat (Sh.Rank sh) that would infect
-- a lot of AstShaped constructor and from there a lot of the codebase.
-- This should be solved in a cleaner way.
--
-- This abbreviation is used a lot below.
astTrS :: forall n m sh s r.
          (KnownNat n, KnownNat m, Sh.Shape sh, GoodScalar r, AstSpan s)
       => AstShaped s r (n ': m ': sh) -> AstShaped s r (m ': n ': sh)
astTrS = withListSh (Proxy @sh) $ \_ -> astTransposeS @'[1, 0]

-- | This works analogously to @build1Vectorize@m.
build1VectorizeS
  :: forall k sh s r. (GoodScalar r, KnownNat k, Sh.Shape sh, AstSpan s)
  => (IntVarName, AstShaped s r sh) -> AstShaped s r (k ': sh)
{-# NOINLINE build1VectorizeS #-}
build1VectorizeS (var, v0) = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = 1000 * traceWidth
      startTerm = Ast.AstBuild1S @k (var, v0)
      renames = IM.fromList [(1, ""), (2, "")]
  when enabled $ do
    writeIORef traceNestingLevel 0
    hPutStrLnFlush stderr $
      "\n"
      ++ "START of vectorization for term "
      ++ ellipsisString width (printAstSimpleS renames startTerm)
      ++ "\n"
  let !endTerm = build1VOccurenceUnknownS (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (printAstSimpleS renames endTerm)
      ++ "\n"
  return endTerm

build1VOccurenceUnknownS
  :: forall k sh s r. (GoodScalar r, KnownNat k, Sh.Shape sh, AstSpan s)
  => (IntVarName, AstShaped s r sh) -> AstShaped s r (k ': sh)
build1VOccurenceUnknownS (var, v0) =
  let traceRule = mkTraceRuleS "build1VOccS" (Ast.AstBuild1S (var, v0)) v0 1
  in if varNameInAstS var v0
     then build1VS (var, v0)
     else traceRule $
       astReplicateS v0

build1VOccurenceUnknownRefreshS
  :: forall k sh s r. (GoodScalar r, KnownNat k, Sh.Shape sh, AstSpan s)
  => (IntVarName, AstShaped s r sh) -> AstShaped s r (k ': sh)
{-# NOINLINE build1VOccurenceUnknownRefreshS #-}
build1VOccurenceUnknownRefreshS (var, v0) =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !v2 = substituteAstS  -- cheap subst, because only a renaming
                (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh)
                var v0
    in build1VOccurenceUnknownS (varFresh, v2)

intBindingRefreshS
  :: IntVarName -> AstIndexS sh -> (IntVarName, AstInt, AstIndexS sh)
{-# NOINLINE intBindingRefreshS #-}
intBindingRefreshS var ix =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !ix2 = substituteAstIndexS  -- cheap subst, because only a renaming
                 (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh)
                 var ix
    in (varFresh, astVarFresh, ix2)

build1VS
  :: forall k sh s r. (GoodScalar r, KnownNat k, Sh.Shape sh, AstSpan s)
  => (IntVarName, AstShaped s r sh) -> AstShaped s r (k ': sh)
build1VS (var, v00) =
  let v0 = simplifyStepNonIndexS v00
        -- Almost surely the term will be transformed, so it can just
        -- as well we one-step simplified first (many steps if redexes
        -- get uncovered and so the simplification requires only constant
        -- look-ahead, but has a guaranteed net benefit).
      bv = Ast.AstBuild1S (var, v0)
      traceRule = mkTraceRuleS "build1VS" bv v0 1
  in case v0 of
    Ast.AstVarS{} ->
      error "build1VS: AstVarS can't contain free index variables"
    Ast.AstLetS @sh1 @_ @r1 @_ @s1 var1@(AstVarName oldVarId) u v ->
      let var2 = AstVarName oldVarId  -- changed shape; TODO: shall we rename?
          projection = Ast.AstIndexS (Ast.AstVarS @(k ': sh1) var2)
                                     (Ast.AstIntVar var ::$ ZS)
          v2 = substituteAstS
                 (SubstitutionPayloadShaped @s1 @r1 projection) var1 v
      in astLetS var2 (build1VOccurenceUnknownS @k (var, u))
                      (build1VOccurenceUnknownRefreshS (var, v2))
    Ast.AstLetADShareS{} -> error "build1VS: AstLetADShareS"
    Ast.AstCondS b (Ast.AstConstantS v) (Ast.AstConstantS w) ->
      let t = Ast.AstConstantS
              $ astIndexStepS @'[2] (astFromListS [v, w])
                                    (astCond b 0 1 ::$ ZS)
      in build1VS (var, t)
    Ast.AstCondS b v w ->
      let t = astIndexStepS @'[2] (astFromListS [v, w])
                                  (astCond b 0 1 ::$ ZS)
      in build1VS (var, t)

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
                 :: Sh.Take (Sh.Rank sh1) (sh1 Sh.++ sh) :~: sh1) $
      gcastWith (unsafeCoerce Refl
                 :: Sh.Drop (Sh.Rank sh1) (sh1 Sh.++ sh) :~: sh) $
      build1VIndexS @k @(Sh.Rank sh1) (var, v, ix)  -- @var@ is in @v@ or @ix@
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
                     (varFresh ::$ vars, astVarFresh ::$ ix2)

    Ast.AstFromListS l -> traceRule $
      astTrS $ astFromListS (map (\v -> build1VOccurenceUnknownS (var, v)) l)
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
    Ast.AstTransposeS @perm @sh1 v -> traceRule $
      let zsuccPerm = 0 : map succ (Sh.shapeT @perm)
      in Sh.withShapeP zsuccPerm $ \(Proxy @zsuccP) ->
        gcastWith (unsafeCoerce Refl :: 0 ': MapSucc perm :~: zsuccP) $
          -- this one is needed for GHC >= 9.8 due to #23763
        gcastWith (unsafeCoerce Refl
                   :: Sh.Permute zsuccP (k : sh1) :~: k : sh) $
        gcastWith (unsafeCoerce Refl
                   :: Sh.Rank zsuccP :~: 1 + Sh.Rank perm) $
        trustMeThisIsAPermutation @zsuccP
        $ astTransposeS @zsuccP $ build1VS @k (var, v)
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
                        (varFresh ::$ vars, astVarFresh ::$ ix2)
    Ast.AstCastS v -> astCastS $ build1VS (var, v)
    Ast.AstFromIntegralS v -> astFromIntegralS $ build1VS (var, v)
    Ast.AstConstS{} ->
      error "build1VS: AstConstS can't have free index variables"

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

    Ast.AstConstantS v -> traceRule $
      Ast.AstConstantS $ build1VS (var, v)
    Ast.AstPrimalPartS v -> traceRule $
      astPrimalPartS $ build1VS (var, v)
    Ast.AstDualPartS v -> traceRule $
      astDualPartS $ build1VS (var, v)
    Ast.AstDS u u' -> traceRule $
      Ast.AstDS (build1VOccurenceUnknownS (var, u))
                (build1VOccurenceUnknownS (var, u'))

build1VIndexS
  :: forall k p sh s r.
     ( GoodScalar r, KnownNat k, Sh.Shape sh
     , Sh.Shape (Sh.Drop p (Sh.Take p sh Sh.++ Sh.Drop p sh)), AstSpan s )
  => (IntVarName, AstShaped s r sh, AstIndexS (Sh.Take p sh))
  -> AstShaped s r (k ': Sh.Drop p sh)
build1VIndexS (var, v0, ZS) =
  gcastWith (unsafeCoerce Refl :: p :~: 0)
    -- otherwise sh would need to be empty, but then Take gets stuck
    -- so the application of this function wouldn't type-check
  $ build1VOccurenceUnknownS (var, v0)
build1VIndexS (var, v0, ix@(_ ::$ _)) =
  gcastWith (unsafeCoerce Refl :: sh :~: Sh.Take p sh Sh.++ Sh.Drop p sh) $
  let vTrace = Ast.AstBuild1S (var, Ast.AstIndexS v0 ix)
      traceRule = mkTraceRuleS "build1VIndexS" vTrace v0 1
  in if varNameInAstS var v0
     then case astIndexStepS v0 ix of  -- push deeper
       Ast.AstIndexS v1 ZS -> traceRule $
         build1VOccurenceUnknownS (var, v1)
       v@(Ast.AstIndexS @sh1 v1 ix1) -> traceRule $
         gcastWith (unsafeCoerce Refl
                    :: k ': sh1 :~: Sh.Take (1 + Sh.Rank sh1)
                                            (k ': sh1 Sh.++ Sh.Drop p sh)) $
         gcastWith (unsafeCoerce Refl
                    :: Sh.Drop p sh
                       :~: Sh.Drop (1 + Sh.Rank sh1)
                                   (k ': sh1 Sh.++ Sh.Drop p sh)) $
         let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix1
             ruleD = astGatherStepS @'[k] @(1 + Sh.Rank sh1)
                       (build1VS @k (var, v1))
                       (varFresh ::$ ZS, astVarFresh ::$ ix2)
             len = length $ Sh.shapeT @sh1
         in if varNameInAstS var v1
            then case v1 of  -- try to avoid ruleD if not a normal form
              Ast.AstFromListS{} | len == 1 -> ruleD
              Ast.AstFromVectorS{} | len == 1 -> ruleD
              Ast.AstScatterS{} -> ruleD
              Ast.AstAppendS{} -> ruleD
              _ -> build1VOccurenceUnknownS (var, v)  -- not a normal form
            else build1VOccurenceUnknownS (var, v)  -- shortcut
       v -> traceRule $
         build1VOccurenceUnknownS (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStepS v0 (var ::$ ZS, ix)


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
                   $ replicate1HVectorF astReplicate astReplicateS k asts)

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
  Ast.AstLetInHVector @_ @r1 @s1 var1@(AstVarName oldVarId) u v ->
    let var2 = AstVarName oldVarId  -- changed shape; TODO: shall we rename?
        sh = shapeAst u
        projection = Ast.AstIndex (Ast.AstVar (sNatValue k :$: sh) var2)
                                  (Ast.AstIntVar var :.: ZIR)
        v2 = substituteAstHVector
               (SubstitutionPayloadRanked @s1 @r1 projection) var1 v
    in astLetInHVector var2 (build1VOccurenceUnknown (sNatValue k) (var, u))
                            (build1VOccurenceUnknownHVectorRefresh
                               k (var, v2))
  Ast.AstLetInHVectorS @sh2 @r1 @s1
    var1@(AstVarName oldVarId) u v ->
      let var2 = AstVarName oldVarId  -- changed shape; TODO: shall we rename?
          projection = Ast.AstIndexS (Ast.AstVarS @(k ': sh2) var2)
                                     (Ast.AstIntVar var ::$ ZS)
          v2 = substituteAstHVector
                 (SubstitutionPayloadShaped @s1 @r1 projection) var1 v
      in astLetInHVectorS var2 (build1VOccurenceUnknownS @k (var, u))
                               (build1VOccurenceUnknownHVectorRefresh
                                  k (var, v2))
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
  DynamicRanked u ->
    DynamicRanked $ build1VOccurenceUnknown (sNatValue k) (var, u)
  DynamicShaped u ->
    DynamicShaped $ build1VOccurenceUnknownS @k (var, u)
  DynamicRankedDummy @r @sh _ _ ->
    withListSh (Proxy @sh) $ \_ ->
      DynamicRanked @r (Ast.AstRFromS @(k ': sh) @s @r 0)
  DynamicShapedDummy @r @sh _ _ -> DynamicShaped @r @(k ': sh) 0

build1VOccurenceUnknownHVectorRefresh
  :: forall k s. AstSpan s
  => SNat k -> (IntVarName, AstHVector s) -> AstHVector s
{-# NOINLINE build1VOccurenceUnknownHVectorRefresh #-}
build1VOccurenceUnknownHVectorRefresh k (var, v0) =
  funToAstIntVar $ \ (!varFresh, !astVarFresh) ->
    let !v2 = substituteAstHVector  -- cheap subst, because only a renaming
                (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh)
                var v0
    in build1VOccurenceUnknownHVector k (varFresh, v2)


-- * Auxiliary machinery

substProjRanked :: forall n1 r1 n r s1 s.
                   ( KnownNat n1, GoodScalar r1, KnownNat n, GoodScalar r
                   , AstSpan s, AstSpan s1 )
                => Int -> IntVarName -> ShapeInt n1
                -> AstVarName (AstRanked s1) r1 n1
                -> AstRanked s r n -> AstRanked s r n
substProjRanked k var sh1 var1@(AstVarName varId) =
  let var2 = AstVarName varId
      projection =
        Ast.AstIndex (Ast.AstVar (k :$: sh1) var2)
                     (Ast.AstIntVar var :.: ZIR)
  in substituteAst
       (SubstitutionPayloadRanked @s1 @r1 projection) var1

substProjShaped :: forall n1 r1 sh r s1 s.
                   ( KnownNat n1, GoodScalar r1, Sh.Shape sh, GoodScalar r
                   , AstSpan s, AstSpan s1 )
                => Int -> IntVarName -> ShapeInt n1
                -> AstVarName (AstRanked s1) r1 n1
                -> AstShaped s r sh -> AstShaped s r sh
substProjShaped k var sh1 var1@(AstVarName varId) =
  let var2 = AstVarName varId
      projection =
        Ast.AstIndex (Ast.AstVar (k :$: sh1) var2)
                     (Ast.AstIntVar var :.: ZIR)
  in substituteAstS
       (SubstitutionPayloadRanked @s1 @r1 projection) var1

substProjRankedS :: forall k sh1 r1 n r s1 s.
                    ( KnownNat k, Sh.Shape sh1, GoodScalar r1
                    , KnownNat n, GoodScalar r, AstSpan s, AstSpan s1 )
                 => IntVarName -> AstVarName (AstShaped s1) r1 sh1
                 -> AstRanked s r n -> AstRanked s r n
substProjRankedS var var1@(AstVarName varId) =
  let var2 = AstVarName varId
      projection =
        Ast.AstIndexS (Ast.AstVarS @(k ': sh1) var2)
                      (Ast.AstIntVar var ::$ ZS)
  in substituteAst
       (SubstitutionPayloadShaped @s1 @r1 projection) var1

substProjShapedS :: forall k sh1 r1 sh r s1 s.
                    ( KnownNat k, Sh.Shape sh1, GoodScalar r1
                    , Sh.Shape sh, GoodScalar r, AstSpan s, AstSpan s1 )
                 => IntVarName -> AstVarName (AstShaped s1) r1 sh1
                 -> AstShaped s r sh -> AstShaped s r sh
substProjShapedS var var1@(AstVarName varId) =
  let var2 = AstVarName varId
      projection =
        Ast.AstIndexS (Ast.AstVarS @(k ': sh1) var2)
                      (Ast.AstIntVar var ::$ ZS)
  in substituteAstS
       (SubstitutionPayloadShaped @s1 @r1 projection) var1

substProjHVector :: forall n1 r1 s1 s.
                    (KnownNat n1, GoodScalar r1, AstSpan s, AstSpan s1)
                 => Int -> IntVarName -> ShapeInt n1
                 -> AstVarName (AstRanked s1) r1 n1
                 -> AstHVector s -> AstHVector s
substProjHVector k var sh1 var1@(AstVarName varId) =
  let var2 = AstVarName varId
      projection =
        Ast.AstIndex (Ast.AstVar (k :$: sh1) var2)
                     (Ast.AstIntVar var :.: ZIR)
  in substituteAstHVector
       (SubstitutionPayloadRanked @s1 @r1 projection) var1

substProjHVectorS :: forall k sh1 r1 s1 s.
                     ( KnownNat k, Sh.Shape sh1, GoodScalar r1
                     , AstSpan s, AstSpan s1 )
                  => IntVarName -> AstVarName (AstShaped s1) r1 sh1
                  -> AstHVector s -> AstHVector s
substProjHVectorS var var1@(AstVarName varId) =
  let var2 = AstVarName varId
      projection =
        Ast.AstIndexS (Ast.AstVarS @(k ': sh1) var2)
                      (Ast.AstIntVar var ::$ ZS)
  in substituteAstHVector
       (SubstitutionPayloadShaped @s1 @r1 projection) var1

substProjDynamic :: forall k n r s.
                    (KnownNat k, KnownNat n, GoodScalar r, AstSpan s)
                 => IntVarName -> AstRanked s r n
                 -> AstDynamicVarName
                 -> (AstRanked s r n, AstDynamicVarName)
substProjDynamic var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat) =
    ( withListSh (Proxy @sh3) $ \sh1 ->
        substProjRanked @_ @r3  @_ @_ @s
                        (valueOf @k) var sh1 (AstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamic var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat]) =
    ( substProjRankedS @k @sh3 @r3 @_ @_ @s var (AstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamic _ _ _ = error "substProjDynamic: unexpected type"

substProjDynamicS :: forall k sh r s.
                     (KnownNat k, Sh.Shape sh, GoodScalar r, AstSpan s)
                  => IntVarName -> AstShaped s r sh
                  -> AstDynamicVarName
                  -> (AstShaped s r sh, AstDynamicVarName)
substProjDynamicS var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat) =
    ( withListSh (Proxy @sh3) $ \sh1 ->
        substProjShaped @_ @r3 @_ @_ @s
                        (valueOf @k) var sh1 (AstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamicS var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat]) =
    ( substProjShapedS @k @sh3 @r3 @_ @_ @s var (AstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamicS _ _ _ = error "substProjDynamicS: unexpected type"

substProjVars :: forall k n r s.
                 (KnownNat k, KnownNat n, GoodScalar r, AstSpan s)
              => IntVarName -> [AstDynamicVarName]
              -> AstRanked s r n
              -> (AstRanked s r n, [AstDynamicVarName])
substProjVars var vars v3 = mapAccumR (substProjDynamic @k var) v3 vars

substProjVarsS :: forall k sh r s.
                  (KnownNat k, Sh.Shape sh, GoodScalar r, AstSpan s)
               => IntVarName -> [AstDynamicVarName]
               -> AstShaped s r sh
               -> (AstShaped s r sh, [AstDynamicVarName])
substProjVarsS var vars v3 = mapAccumR (substProjDynamicS @k var) v3 vars

substProjDynamicHVector :: forall k s. (KnownNat k, AstSpan s)
                        => IntVarName -> AstHVector s -> AstDynamicVarName
                        -> (AstHVector s, AstDynamicVarName)
substProjDynamicHVector var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat) =
    ( withListSh (Proxy @sh3) $ \sh1 ->
        substProjHVector @_ @r3 @s (valueOf @k) var sh1 (AstVarName varId) v3
    , AstDynamicVarName @ty @r3 @(k ': sh3) varId )
substProjDynamicHVector var v3 (AstDynamicVarName @ty @r3 @sh3 varId)
  | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat]) =
    ( substProjHVectorS @k @sh3 @r3 @s var (AstVarName varId) v3
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
astTrDynamic t@(DynamicRanked @_ @n1 u) =
  case cmpNat (Proxy @2) (Proxy @n1) of
    EQI -> DynamicRanked $ astTr @(n1 - 2) u
    LTI -> DynamicRanked $ astTr @(n1 - 2) u
    _ -> t
astTrDynamic t@(DynamicShaped @_ @sh u) =
  let sh1 = Sh.shapeT @sh
      permute10 (m0 : m1 : ms) = m1 : m0 : ms
      permute10 ms = ms
      sh1Permuted = permute10 sh1
  in Sh.withShapeP sh1Permuted $ \(Proxy @shPermuted) ->
       withListSh (Proxy @sh) $ \_ ->
         case cmpNat (Proxy @2) (Proxy @(Sh.Rank sh)) of
           EQI -> case astTransposeS @'[1, 0] u of
             (w :: AstShaped s4 r4 sh4) ->
               gcastWith (unsafeCoerce Refl :: sh4 :~: shPermuted) $
               DynamicShaped w
           LTI -> case astTransposeS @'[1, 0] u of
             (w :: AstShaped s4 r4 sh4) ->
               gcastWith (unsafeCoerce Refl :: sh4 :~: shPermuted) $
               DynamicShaped w
           _ -> t
astTrDynamic (DynamicRankedDummy p1 (Proxy @sh1)) =
  let permute10 (m0 : m1 : ms) = m1 : m0 : ms
      permute10 ms = ms
      sh1Permuted = permute10 $ Sh.shapeT @sh1
  in Sh.withShapeP sh1Permuted $ \proxy ->
       DynamicRankedDummy p1 proxy
astTrDynamic (DynamicShapedDummy p1 (Proxy @sh1)) =
  let permute10 (m0 : m1 : ms) = m1 : m0 : ms
      permute10 ms = ms
      sh1Permuted = permute10 $ Sh.shapeT @sh1
  in Sh.withShapeP sh1Permuted $ \proxy ->
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

mkTraceRule :: (KnownNat n, KnownNat m, GoodScalar r, AstSpan s)
            => String -> AstRanked s r n -> AstRanked s r m -> Int
            -> AstRanked s r n
            -> AstRanked s r n
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
  let !_A = assert (shapeAst from == shapeAst to
                    `blame` "mkTraceRule: term shape changed"
                    `swith`(shapeAst from, shapeAst to, from, to)) ()
  return $! to

mkTraceRuleS :: forall sh sh2 s r.
                (GoodScalar r, Sh.Shape sh, Sh.Shape sh2, AstSpan s)
             => String -> AstShaped s r sh -> AstShaped s r sh2 -> Int
             -> AstShaped s r sh -> AstShaped s r sh
{-# NOINLINE mkTraceRuleS #-}
mkTraceRuleS prefix from caseAnalysed nwords to = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = traceWidth
      renames = IM.fromList [(1, ""), (2, "")]
      constructorName =
        unwords $ take nwords $ words $ take 20
        $ printAstSimpleS renames caseAnalysed
      ruleName = prefix ++ "." ++ constructorName
      ruleNamePadded = take 20 $ ruleName ++ repeat ' '
  when enabled $ do
    nestingLevel <- readIORef traceNestingLevel
    modifyIORef' traceNestingLevel succ
    let paddedNesting = take 3 $ show nestingLevel ++ repeat ' '
    -- Force in the correct order:
    let !stringFrom = printAstSimpleS renames from
    let !stringTo = printAstSimpleS renames to
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
                                 ("build " ++ show (sNatValue k :: Int) ++ " ("
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
