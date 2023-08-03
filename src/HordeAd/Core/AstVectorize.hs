{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Vectorization of the AST, eliminating the build operation.
module HordeAd.Core.AstVectorize
  ( build1Vectorize, build1VectorizeS, traceRuleEnabledRef
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (when)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as OS
import           Data.Int (Int64)
import           Data.IORef
import           Data.Proxy (Proxy)
import qualified Data.Strict.IntMap as IM
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal, type (+))
import           System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast hiding
  (AstBool (..), AstDomains (..), AstRanked (..), AstShaped (..))
import           HordeAd.Core.Ast (AstDomains, AstRanked, AstShaped)
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstPrettyPrint
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (MapSucc, trustMeThisIsAPermutation)
import           HordeAd.Util.ShapedList (ShapedList (..))
import           HordeAd.Util.SizedIndex
import           HordeAd.Util.SizedList

-- * Vectorization of AstRanked

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

-- This abbreviation is used a lot below.
astTr :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
      => AstRanked s r (2 + n) -> AstRanked s r (2 + n)
astTr = astTranspose [1, 0]

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
build1VOccurenceUnknownRefresh k (var, v0) = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIOI id
  let v2 = substituteAst  -- cheap subst, because only a renaming
             (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh) var v0
  return $! build1VOccurenceUnknown k (varFresh, v2)

intBindingRefresh
  :: IntVarName -> AstIndex n -> (IntVarName, AstInt, AstIndex n)
{-# NOINLINE intBindingRefresh #-}
intBindingRefresh var ix = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIOI id
  let ix2 = substituteAstIndex  -- cheap subst, because only a renaming
              (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh)
              var ix
  return (varFresh, astVarFresh, ix2)

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
        Just Refl -> fromPrimal $ astSlice 0 k Ast.AstIota
        _ -> error "build1V: build variable is not an index variable"
    Ast.AstVar{} ->
      error "build1V: AstVar can't contain other free index variables"
    Ast.AstLet @_ @_ @r1 @s1 (AstVarName oldVar2) u v ->
      let var2 = AstVarName oldVar2  -- changed shape; TODO: shall we rename?
          sh = shapeAst u
          projection = Ast.AstIndex (Ast.AstVar (k :$ sh) var2)
                                    (Ast.AstIntVar var :. ZI)
          -- The subsitutions of projections don't break sharing,
          -- because they don't duplicate variables and the added var
          -- is eventually being eliminated instead of substituted for.
          v2 = substituteAst (SubstitutionPayloadRanked @s1 @r1 projection)
                             var2 v
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
    Ast.AstGather sh v (vars, ix) -> traceRule $
      let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix
      in astGatherStep (k :$ sh)
                       (build1VOccurenceUnknown k (var, v))
                       (varFresh ::: vars, astVarFresh :. ix2)
    Ast.AstCast v -> Ast.AstCast $ build1V k (var, v)
    Ast.AstFromIntegral v -> Ast.AstFromIntegral $ build1V k (var, v)
    Ast.AstConst{} ->
      error "build1V: AstConst can't have free index variables"

    Ast.AstSToR @sh1 v -> case someNatVal $ toInteger k of
      Just (SomeNat @k _proxy) ->
        Ast.AstSToR @(k ': sh1) $ build1VS (var, v)
      Nothing ->
        error "build1V: impossible someNatVal error"

    Ast.AstConstant v -> traceRule $
      Ast.AstConstant $ build1V k (var, v)
    Ast.AstPrimalPart v -> traceRule $
      Ast.AstPrimalPart $ build1V k (var, v)
    Ast.AstDualPart v -> traceRule $
      Ast.AstDualPart $ build1V k (var, v)
    Ast.AstD u u' ->
      Ast.AstD (build1VOccurenceUnknown k (var, u))
               (build1VOccurenceUnknown k (var, u'))
    Ast.AstLetDomains @s1 vars l v ->
      -- Here substitution traverses @v@ term tree @length vars@ times.
      let subst (var1, DynamicExists (AstRToD u1)) =
            let sh = shapeAst u1
                projection =
                  Ast.AstIndex (Ast.AstVar (k :$ sh) $ AstVarName var1)
                               (Ast.AstIntVar var :. ZI)
            in substituteAst (SubstitutionPayloadRanked @s1 @r projection)
                             (AstVarName var1)
          subst (var1, DynamicExists (AstSToD @sh1 _)) =
            let ls = OS.shapeT @sh1
            in case someNatVal $ toInteger (length ls) of
              Just (SomeNat @n2 _proxy) ->
                let sh = listShapeToShape @n2 ls
                    projection =
                      Ast.AstIndex (Ast.AstVar (k :$ sh) $ AstVarName var1)
                                   (Ast.AstIntVar var :. ZI)
                in substituteAst (SubstitutionPayloadRanked @s1 @r projection)
                                 (AstVarName var1)
              Nothing -> error "build1V: impossible someNatVal error"
          v2 = V.foldr subst v (V.zip vars (unwrapAstDomains l))
      in Ast.AstLetDomains vars (build1VOccurenceUnknownDomains k (var, l))
                                (build1VOccurenceUnknownRefresh k (var, v2))

build1VOccurenceUnknownDynamic
  :: AstSpan s
  => Int -> (IntVarName, DynamicExists (AstDynamic s))
  -> DynamicExists (AstDynamic s)
build1VOccurenceUnknownDynamic k (var, d) = case d of
  DynamicExists (AstRToD u) ->
    DynamicExists $ AstRToD $ build1VOccurenceUnknown k (var, u)
  DynamicExists (AstSToD u) -> case someNatVal $ toInteger k of
    Just (SomeNat @k _proxy) ->
      DynamicExists $ AstSToD $ build1VOccurenceUnknownS @k (var, u)
    Nothing ->
      error "build1VOccurenceUnknownDynamic: impossible someNatVal error"

build1VOccurenceUnknownDomains
  :: forall s. AstSpan s
  => Int -> (IntVarName, AstDomains s) -> AstDomains s
build1VOccurenceUnknownDomains k (var, v0) = case v0 of
  Ast.AstDomains l ->
    Ast.AstDomains $ V.map (\u -> build1VOccurenceUnknownDynamic k (var, u)) l
  Ast.AstDomainsLet @_ @r (AstVarName oldVar2) u v ->
    let var2 = AstVarName oldVar2  -- changed shape; TODO: shall we rename, too?
        sh = shapeAst u
        projection = Ast.AstIndex (Ast.AstVar (k :$ sh) var2)
                                  (Ast.AstIntVar var :. ZI)
        v2 = substituteAstDomains (SubstitutionPayloadRanked @s @r projection)
                                  var2 v
    in astDomainsLet var2 (build1VOccurenceUnknownRefresh k (var, u))
                          (build1VOccurenceUnknownDomains k (var, v2))
  Ast.AstDomainsLetS @sh2 @r
                     (AstVarName oldVar2) u v -> case someNatVal
                                                      $ toInteger k of
    Just (SomeNat @k _proxy) ->
      let var2 = AstVarName oldVar2  -- changed shape; TODO: shall we rename?
          projection = Ast.AstIndexS (Ast.AstVarS @(k ': sh2) var2)
                                     (Ast.AstIntVar var :$: ZSH)
          v2 = substituteAstDomains (SubstitutionPayloadShaped @s @r projection)
                                    var2 v
      in astDomainsLetS var2 (build1VOccurenceUnknownRefreshS @k (var, u))
                             (build1VOccurenceUnknownDomains k (var, v2))
    Nothing ->
      error "build1VOccurenceUnknownDomains: impossible someNatVal error"

-- | The application @build1VIndex k (var, v, ix)@ vectorizes
-- the term @AstBuild1 k (var, AstIndex v ix)@, where it's unknown whether
-- @var@ occurs in any of @v@, @ix@.
--
-- We try to push indexing down as far as needed to eliminate any occurences
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
build1VIndex k (var, v0, ZI) = build1VOccurenceUnknown k (var, v0)
build1VIndex k (var, v0, ix@(_ :. _)) =
  let traceRule = mkTraceRule "build1VIndex"
                              (Ast.AstBuild1 k (var, Ast.AstIndex v0 ix))
                              v0 1
  in if varNameInAst var v0
     then case astIndexStep v0 ix of  -- push deeper
       Ast.AstIndex v1 ZI -> traceRule $
         build1VOccurenceUnknown k (var, v1)
       v@(Ast.AstIndex @p v1 ix1) -> traceRule $
         let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix1
             ruleD = astGatherStep
                       (k :$ dropShape (shapeAst v1))
                       (build1V k (var, v1))
                       (varFresh ::: Z, astVarFresh :. ix2)
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
            astGatherStep (k :$ dropShape (shapeAst v0)) v0 (var ::: Z, ix)


-- * Vectorization of AstShaped

-- | This works analogously to @build1Vectorize@m.
build1VectorizeS
  :: forall k sh s r. (GoodScalar r, KnownNat k, OS.Shape sh, AstSpan s)
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

-- TODO: we avoid constraint KnownNat (OS.Rank sh) that would infect
-- a lot of AstShaped constructor and from there a lot of the codebase.
-- This should be solved in a cleaner way.
--
-- This abbreviation is used a lot below.
astTrS :: forall n m sh s r. (KnownNat n, KnownNat m, OS.Shape sh)
       => AstShaped s r (n ': m ': sh) -> AstShaped s r (m ': n ': sh)
astTrS =
  let p = length $ OS.shapeT @sh
  in case someNatVal $ toInteger p of
    Just (SomeNat @p _proxy) ->
      gcastWith (unsafeCoerce Refl :: OS.Rank sh :~: p) $
      astTransposeS @'[1, 0]
    Nothing -> error "astTrS: impossible someNatVal error"

build1VOccurenceUnknownS
  :: forall k sh s r. (GoodScalar r, KnownNat k, OS.Shape sh, AstSpan s)
  => (IntVarName, AstShaped s r sh) -> AstShaped s r (k ': sh)
build1VOccurenceUnknownS (var, v0) =
  let traceRule = mkTraceRuleS "build1VOccS" (Ast.AstBuild1S (var, v0)) v0 1
  in if varNameInAstS var v0
     then build1VS (var, v0)
     else traceRule $
       astReplicateS v0

build1VOccurenceUnknownRefreshS
  :: forall k sh s r. (GoodScalar r, KnownNat k, OS.Shape sh, AstSpan s)
  => (IntVarName, AstShaped s r sh) -> AstShaped s r (k ': sh)
{-# NOINLINE build1VOccurenceUnknownRefreshS #-}
build1VOccurenceUnknownRefreshS (var, v0) = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIOI id
  let v2 = substituteAstS  -- cheap subst, because only a renaming
             (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh) var v0
  return $! build1VOccurenceUnknownS (varFresh, v2)

intBindingRefreshS
  :: IntVarName -> AstIndexS sh -> (IntVarName, AstInt, AstIndexS sh)
{-# NOINLINE intBindingRefreshS #-}
intBindingRefreshS var ix = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIOI id
  let ix2 = substituteAstIndexS  -- cheap subst, because only a renaming
              (SubstitutionPayloadRanked @PrimalSpan @Int64 astVarFresh)
              var ix
  return (varFresh, astVarFresh, ix2)

build1VS
  :: forall k sh s r. (GoodScalar r, KnownNat k, OS.Shape sh, AstSpan s)
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
    Ast.AstLetS @sh1 @_ @r1 @s1 (AstVarName oldVar2) u v ->
      let var2 = AstVarName oldVar2  -- changed shape; TODO: shall we rename?
          projection = Ast.AstIndexS (Ast.AstVarS @(k ': sh1) var2)
                                     (Ast.AstIntVar var :$: ZSH)
          v2 = substituteAstS (SubstitutionPayloadShaped @s1 @r1 projection)
                              var2 v
      in astLetS var2 (build1VOccurenceUnknownS @k (var, u))
                      (build1VOccurenceUnknownRefreshS (var, v2))
    Ast.AstLetADShareS{} -> error "build1VS: AstLetADShareS"
    Ast.AstCondS b (Ast.AstConstantS v) (Ast.AstConstantS w) ->
      let t = Ast.AstConstantS
              $ astIndexStepS @'[2] (astFromListS [v, w])
                                    (astCond b 0 1 :$: ZSH)
      in build1VS (var, t)
    Ast.AstCondS b v w ->
      let t = astIndexStepS @'[2] (astFromListS [v, w])
                                  (astCond b 0 1 :$: ZSH)
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
                 :: OS.Take (OS.Rank sh1) (sh1 OS.++ sh) :~: sh1) $
      gcastWith (unsafeCoerce Refl
                 :: OS.Drop (OS.Rank sh1) (sh1 OS.++ sh) :~: sh) $
      build1VIndexS @k @(OS.Rank sh1) (var, v, ix)  -- @var@ is in @v@ or @ix@
    Ast.AstSumS v -> traceRule $
      astSumS $ astTrS $ build1VS (var, v)
    Ast.AstScatterS @sh2 @p @sh3 v (vars, ix) -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: OS.Take (1 + p) (k : sh3) :~: (k : OS.Take p sh3)) $
      gcastWith (unsafeCoerce Refl
                 :: OS.Drop (1 + p) (k : sh3) :~: OS.Drop p sh3) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astScatterS @(k ': sh2) @(1 + p)
                     (build1VOccurenceUnknownS (var, v))
                     (varFresh :$: vars, astVarFresh :$: ix2)

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
      let zsuccPerm = 0 : map succ (OS.shapeT @perm)
      in OS.withShapeP zsuccPerm $ \(_proxy :: Proxy zsuccPerm) ->
        gcastWith (unsafeCoerce Refl :: 0 ': MapSucc perm :~: zsuccPerm) $
        gcastWith (unsafeCoerce Refl
                   :: OS.Permute zsuccPerm (k : sh1) :~: k : sh) $
        gcastWith (unsafeCoerce Refl
                   :: OS.Rank zsuccPerm :~: 1 + OS.Rank perm) $
        trustMeThisIsAPermutation @zsuccPerm
        $ astTransposeS @zsuccPerm $ build1VS @k (var, v)
    Ast.AstReshapeS @sh2 v -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: OS.Size (k ': sh) :~: OS.Size (k ': sh2)) $
      astReshapeS $ build1VS (var, v)
    Ast.AstBuild1S{} -> error "build1VS: impossible case of AstBuild1S"
    Ast.AstGatherS @sh2 @p @sh3 v (vars, ix) -> traceRule $
      gcastWith (unsafeCoerce Refl
                 :: OS.Take (1 + p) (k : sh3) :~: (k : OS.Take p sh3)) $
      gcastWith (unsafeCoerce Refl
                 :: OS.Drop (1 + p) (k : sh3) :~: OS.Drop p sh3) $
      let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix
      in astGatherStepS @(k ': sh2) @(1 + p)
                        (build1VOccurenceUnknownS @k (var, v))
                        (varFresh :$: vars, astVarFresh :$: ix2)
    Ast.AstCastS v -> Ast.AstCastS $ build1VS (var, v)
    Ast.AstFromIntegralS v -> Ast.AstFromIntegralS $ build1VS (var, v)
    Ast.AstConstS{} ->
      error "build1VS: AstConstS can't have free index variables"

    Ast.AstRToS v -> Ast.AstRToS $ build1V (valueOf @k) (var, v)

    Ast.AstConstantS v -> traceRule $
      Ast.AstConstantS $ build1VS (var, v)
    Ast.AstPrimalPartS v -> traceRule $
      Ast.AstPrimalPartS $ build1VS (var, v)
    Ast.AstDualPartS v -> traceRule $
      Ast.AstDualPartS $ build1VS (var, v)
    Ast.AstDS u u' ->
      Ast.AstDS (build1VOccurenceUnknownS (var, u))
                (build1VOccurenceUnknownS (var, u'))
    Ast.AstLetDomainsS @s1 vars l v ->
      -- Here substitution traverses @v@ term tree @length vars@ times.
      let subst (var1, DynamicExists (AstRToD u1)) =
            OS.withShapeP (shapeToList $ shapeAst u1) $ \(_ :: Proxy sh1) ->
            let projection =
                  Ast.AstIndexS (Ast.AstVarS @(k ': sh1) $ AstVarName var1)
                                (Ast.AstIntVar var :$: ZSH)
            in substituteAstS (SubstitutionPayloadShaped @s1 @r projection)
                              (AstVarName var1)
          subst (var1, DynamicExists (AstSToD @sh1 _)) =
            let projection =
                  Ast.AstIndexS (Ast.AstVarS @(k ': sh1) $ AstVarName var1)
                                (Ast.AstIntVar var :$: ZSH)
            in substituteAstS (SubstitutionPayloadShaped @s1 @r projection)
                              (AstVarName var1)
          v2 = V.foldr subst v (V.zip vars (unwrapAstDomains l))
      in Ast.AstLetDomainsS
           vars
           (build1VOccurenceUnknownDomains (valueOf @k) (var, l))
           (build1VOccurenceUnknownRefreshS (var, v2))

build1VIndexS
  :: forall k p sh s r.
     ( GoodScalar r, KnownNat k, OS.Shape sh
     , OS.Shape (OS.Drop p (OS.Take p sh OS.++ OS.Drop p sh)), AstSpan s )
  => (IntVarName, AstShaped s r sh, AstIndexS (OS.Take p sh))
  -> AstShaped s r (k ': OS.Drop p sh)
build1VIndexS (var, v0, ZSH) =
  gcastWith (unsafeCoerce Refl :: p :~: 0)
    -- otherwise sh would need to be empty, but then Take gets stuck
    -- so the application of this function wouldn't type-check
  $ build1VOccurenceUnknownS (var, v0)
build1VIndexS (var, v0, ix@(_ :$: _)) =
  gcastWith (unsafeCoerce Refl :: sh :~: OS.Take p sh OS.++ OS.Drop p sh) $
  let vTrace = Ast.AstBuild1S (var, Ast.AstIndexS v0 ix)
      traceRule = mkTraceRuleS "build1VIndexS" vTrace v0 1
  in if varNameInAstS var v0
     then case astIndexStepS v0 ix of  -- push deeper
       Ast.AstIndexS v1 ZSH -> traceRule $
         build1VOccurenceUnknownS (var, v1)
       v@(Ast.AstIndexS @sh1 v1 ix1) -> traceRule $
         gcastWith (unsafeCoerce Refl
                    :: k ': sh1 :~: OS.Take (1 + OS.Rank sh1)
                                            (k ': sh1 OS.++ OS.Drop p sh)) $
         gcastWith (unsafeCoerce Refl
                    :: OS.Drop p sh
                       :~: OS.Drop (1 + OS.Rank sh1)
                                   (k ': sh1 OS.++ OS.Drop p sh)) $
         let (varFresh, astVarFresh, ix2) = intBindingRefreshS var ix1
             ruleD = astGatherStepS @'[k] @(1 + OS.Rank sh1)
                       (build1VS @k (var, v1))
                       (varFresh :$: ZSH, astVarFresh :$: ix2)
             len = length $ OS.shapeT @sh1
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
            astGatherStepS v0 (var :$: ZSH, ix)


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
    let !_A = assert (shapeAst from == shapeAst to
                     `blame` "mkTraceRule: term shape changed"
                     `swith`(shapeAst from, shapeAst to, from, to)) ()
    modifyIORef' traceNestingLevel pred
  return $! to

mkTraceRuleS :: forall sh sh2 s r.
                (GoodScalar r, OS.Shape sh, OS.Shape sh2, AstSpan s)
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

hPutStrLnFlush :: Handle -> String -> IO ()
hPutStrLnFlush target s = do
  hFlush stdout >> hFlush stderr
  hPutStrLn target s
  hFlush stdout >> hFlush stderr
