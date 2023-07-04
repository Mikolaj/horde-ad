{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Vectorization of @Ast@, eliminating the @build1@ operation.
module HordeAd.Core.AstVectorize
  ( build1Vectorize, build1VectorizeS, traceRuleEnabledRef
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (when)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as OS
import           Data.IORef
import           Data.Proxy (Proxy)
import qualified Data.Strict.IntMap as IM
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal, type (+))
import           System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast (AstDomains, AstInt, AstRanked, AstShaped)
import           HordeAd.Core.Ast hiding
  (AstBool (..), AstDomains (..), AstInt (..), AstRanked (..), AstShaped (..))
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstPrettyPrint
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.ShapedList (ShapedList (..))
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.SizedList
import           HordeAd.Internal.OrthotopeOrphanInstances
  (trustMeThisIsAPermutation)

-- * Vectorization of AstRanked

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
  ::  (KnownNat n, GoodScalar r)
  => Int -> (AstVarId, AstRanked r n) -> AstRanked r (1 + n)
build1VOccurenceUnknown k (var, v0) =
  let traceRule = mkTraceRule "build1VOcc" (Ast.AstBuild1 k (var, v0)) v0 1
  in if intVarInAst var v0
     then build1V k (var, v0)
     else traceRule $
       astReplicate k v0

build1VOccurenceUnknownRefresh
  :: forall n r. (KnownNat n, GoodScalar r)
  => Int -> (AstVarId, AstRanked r n) -> AstRanked r (1 + n)
{-# NOINLINE build1VOccurenceUnknownRefresh #-}
build1VOccurenceUnknownRefresh k (var, v0) = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIIO id
  let v2 = substitute1Ast (SubstitutionPayloadInt @r astVarFresh) var v0
  return $! build1VOccurenceUnknown k (varFresh, v2)

intBindingRefresh
  :: GoodScalar r
  => AstVarId -> AstIndex r n -> (AstVarId, AstInt r, AstIndex r n)
{-# NOINLINE intBindingRefresh #-}
intBindingRefresh var ix = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIIO id
  let ix2 =
        fmap (substituteAstInt (SubstitutionPayloadInt astVarFresh) var) ix
  return $! (varFresh, astVarFresh, ix2)

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1V
  :: forall n r. (KnownNat n, GoodScalar r)
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
          projection = Ast.AstIndex (Ast.AstVar (k :$ sh) var2)
                                     (Ast.AstIntVar var :. ZI)
          v2 = substitute1Ast (SubstitutionPayloadRanked @r projection) var2 v
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

    Ast.AstIndex v ix -> traceRule $
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
    Ast.AstGather sh v (vars, ix) -> traceRule $
      let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix
      in astGatherStep (k :$ sh)
                       (build1VOccurenceUnknown k (var, v))
                       (varFresh ::: vars, astVarFresh :. ix2)

    Ast.AstSToR @sh1 v -> case someNatVal $ toInteger k of
      Just (SomeNat @k _proxy) ->
        Ast.AstSToR @(k ': sh1) $ build1VS (var, v)
      Nothing ->
        error "build1V: impossible someNatVal error"

    Ast.AstConst{} ->
      error "build1V: AstConst can't have free int variables"
    Ast.AstConstant (AstPrimalPart v) -> traceRule $
      astConstant $ AstPrimalPart $ build1V k (var, v)
    Ast.AstD (AstPrimalPart u) (AstDualPart u') ->
      Ast.AstD (AstPrimalPart $ build1VOccurenceUnknown k (var, u))
               (AstDualPart $ build1VOccurenceUnknown k (var, u'))
    Ast.AstLetDomains vars l v ->
      -- Here substitution traverses @v@ term tree @length vars@ times.
      let subst (var1, AstRToD u1) =
            let sh = shapeAst u1
                projection = Ast.AstIndex (Ast.AstVar (k :$ sh) var1)
                                          (Ast.AstIntVar var :. ZI)
            in substitute1Ast (SubstitutionPayloadRanked @r projection) var1
          subst (var1, AstSToD @sh1 _) =
            let ls = OS.shapeT @sh1
            in case someNatVal $ toInteger (length ls) of
              Just (SomeNat @n2 _proxy) ->
                let sh = listShapeToShape @n2 ls
                    projection = Ast.AstIndex (Ast.AstVar (k :$ sh) var1)
                                              (Ast.AstIntVar var :. ZI)
                in substitute1Ast (SubstitutionPayloadRanked @r projection) var1
              Nothing -> error "build1V: impossible someNatVal error"
          v2 = V.foldr subst v (V.zip vars (unwrapAstDomains l))
            -- we use the substitution that does not simplify
      in Ast.AstLetDomains vars (build1VOccurenceUnknownDomains k (var, l))
                                (build1VOccurenceUnknownRefresh k (var, v2))

build1VOccurenceUnknownDynamic
  :: GoodScalar r
  => Int -> (AstVarId, AstDynamic r) -> AstDynamic r
build1VOccurenceUnknownDynamic k (var, d) = case d of
  AstRToD u -> AstRToD $ build1VOccurenceUnknown k (var, u)
  AstSToD u -> case someNatVal $ toInteger k of
    Just (SomeNat @k _proxy) ->
      AstSToD $ build1VOccurenceUnknownS @k (var, u)
    Nothing ->
      error "build1VOccurenceUnknownDynamic: impossible someNatVal error"

build1VOccurenceUnknownDomains
  :: forall r. GoodScalar r
  => Int -> (AstVarId, AstDomains r) -> AstDomains r
build1VOccurenceUnknownDomains k (var, v0) = case v0 of
  Ast.AstDomains l ->
    Ast.AstDomains $ V.map (\u -> build1VOccurenceUnknownDynamic k (var, u)) l
  Ast.AstDomainsLet var2 u v ->
    let sh = shapeAst u
        projection = Ast.AstIndex (Ast.AstVar (k :$ sh) var2)
                                  (Ast.AstIntVar var :. ZI)
        v2 = substitute1AstDomains (SubstitutionPayloadRanked @r projection) var2 v
          -- we use the substitution that does not simplify
    in astDomainsLet var2 (build1VOccurenceUnknownRefresh k (var, u))
                          (build1VOccurenceUnknownDomains k (var, v2))
  Ast.AstDomainsLetS @sh2 var2 u v -> case someNatVal $ toInteger k of
    Just (SomeNat @k _proxy) ->
      let projection = Ast.AstIndexS (Ast.AstVarS @(k ': sh2) var2)
                                     (Ast.AstIntVar var :$: ZSH)
          v2 = substitute1AstDomains (SubstitutionPayloadShaped @r projection)
                                     var2 v
            -- we use the substitution that does not simplify
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
  :: forall m n r. (KnownNat m, KnownNat n, GoodScalar r)
  => Int -> (AstVarId, AstRanked r (m + n), AstIndex r m)
  -> AstRanked r (1 + n)
build1VIndex k (var, v0, ZI) = build1VOccurenceUnknown k (var, v0)
build1VIndex k (var, v0, ix@(_ :. _)) =
  let traceRule = mkTraceRule "build1VIndex"
                              (Ast.AstBuild1 k (var, Ast.AstIndex v0 ix))
                              v0 1
  in if intVarInAst var v0
     then case astIndexStep v0 ix of  -- push deeper
       Ast.AstIndex v1 ZI -> traceRule $
         build1VOccurenceUnknown k (var, v1)
       v@(Ast.AstIndex @p v1 ix1) -> traceRule $
         let (varFresh, astVarFresh, ix2) = intBindingRefresh var ix1
             ruleD = astGatherStep
                       (k :$ dropShape (shapeAst v1))
                       (build1V k (var, v1))
                       (varFresh ::: Z, astVarFresh :. ix2)
         in if intVarInAst var v1
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

-- | The application @build1Vectorize k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, that is, rewrites it to a term
-- with the same value, but not containing the outermost @AstBuild1@
-- constructor and not increasing (and potentially decreasing)
-- the total number of @AstBuild1@ occuring in the term.
build1VectorizeS
  :: forall k sh r. (GoodScalar r, KnownNat k, OS.Shape sh)
  => (AstVarId, AstShaped r sh) -> AstShaped r (k ': sh)
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
astTrS :: forall n m sh r. (KnownNat n, KnownNat m, OS.Shape sh)
       => AstShaped r (n ': m ': sh) -> AstShaped r (m ': n ': sh)
astTrS =
  let p = length $ OS.shapeT @sh
  in case someNatVal $ toInteger p of
    Just (SomeNat @p _proxy) ->
      gcastWith (unsafeCoerce Refl :: OS.Rank sh :~: p) $
      astTransposeS @'[1, 0]
    Nothing -> error "astTrS: impossible someNatVal error"

build1VOccurenceUnknownS
  :: forall k sh r. (GoodScalar r, KnownNat k, OS.Shape sh)
  => (AstVarId, AstShaped r sh) -> AstShaped r (k ': sh)
build1VOccurenceUnknownS (var, v0) =
  let traceRule = mkTraceRuleS "build1VOccS" (Ast.AstBuild1S (var, v0)) v0 1
  in if intVarInAstS var v0
     then build1VS (var, v0)
     else traceRule $
       astReplicateS v0

build1VOccurenceUnknownRefreshS
  :: forall k sh r. (GoodScalar r, KnownNat k, OS.Shape sh)
  => (AstVarId, AstShaped r sh) -> AstShaped r (k ': sh)
{-# NOINLINE build1VOccurenceUnknownRefreshS #-}
build1VOccurenceUnknownRefreshS (var, v0) = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIIO id
  let v2 = substitute1AstS (SubstitutionPayloadInt @r astVarFresh) var v0
  return $! build1VOccurenceUnknownS (varFresh, v2)

intBindingRefreshS
  :: GoodScalar r
  => AstVarId -> AstIndexS r sh -> (AstVarId, AstInt r, AstIndexS r sh)
{-# NOINLINE intBindingRefreshS #-}
intBindingRefreshS var ix = unsafePerformIO $ do
  (varFresh, astVarFresh) <- funToAstIIO id
  let ix2 =
        fmap (substituteAstInt (SubstitutionPayloadInt astVarFresh) var) ix
  return $! (varFresh, astVarFresh, ix2)

-- | The application @build1VS k (var, v)@ vectorizes
-- the term @AstBuild1S k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1VS
  :: forall k sh r. (GoodScalar r, KnownNat k, OS.Shape sh)
  => (AstVarId, AstShaped r sh) -> AstShaped r (k ': sh)
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
      error "build1VS: AstVarS can't have free int variables"
    Ast.AstLetS @_ @sh2 var2 u v ->
      let projection = Ast.AstIndexS (Ast.AstVarS @(k ': sh2) var2)
                                     (Ast.AstIntVar var :$: ZSH)
          v2 = substitute1AstS (SubstitutionPayloadShaped @r projection) var2 v
            -- we use the substitution that does not simplify, which is sad,
            -- because very low hanging fruits may be left hanging, but we
            -- don't want to simplify the whole term; a better alternative
            -- would be a substitution that only simplifies the touched
            -- terms with one step lookahead, as normally when vectorizing
      in astLetS var2 (build1VOccurenceUnknownS @k (var, u))
                      (build1VOccurenceUnknownRefreshS (var, v2))
                         -- ensure no duplicated bindings; this is stronger
                         -- than what we need for simple substitution, etc.
    Ast.AstLetADShareS{} -> error "build1VS: AstLetADShareS"

    Ast.AstOpS opCode args -> traceRule $
      Ast.AstOpS opCode $ map (\v -> build1VOccurenceUnknownS (var, v)) args
        -- we permit duplicated bindings, because they can't easily
        -- be substituted into one another, unlike inside a let,
        -- which may get inlined
    Ast.AstSumOfListS args -> traceRule $
      Ast.AstSumOfListS $ map (\v -> build1VOccurenceUnknownS (var, v)) args
    Ast.AstIotaS ->
      error "build1VS: AstIotaS can't have free int variables"

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
    Ast.AstTransposeS @perm @sh1 v -> undefined
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

    Ast.AstRToS v -> Ast.AstRToS $ build1V (valueOf @k) (var, v)

    Ast.AstConstS{} ->
      error "build1VS: AstConstS can't have free int variables"
    Ast.AstConstantS (AstPrimalPartS v) -> traceRule $
      astConstantS $ AstPrimalPartS $ build1VS (var, v)
    Ast.AstDS (AstPrimalPartS u) (AstDualPartS u') ->
      Ast.AstDS (AstPrimalPartS $ build1VOccurenceUnknownS (var, u))
                (AstDualPartS $ build1VOccurenceUnknownS (var, u'))
    Ast.AstLetDomainsS vars l v ->
      -- Here substitution traverses @v@ term tree @length vars@ times.
      let subst (var1, AstRToD u1) =
            OS.withShapeP (shapeToList $ shapeAst u1) $ \(_ :: Proxy sh1) ->
            let projection = Ast.AstIndexS (Ast.AstVarS @(k ': sh1) var1)
                                           (Ast.AstIntVar var :$: ZSH)
            in substitute1AstS (SubstitutionPayloadShaped @r projection) var1
          subst (var1, AstSToD @sh1 _) =
            let projection = Ast.AstIndexS (Ast.AstVarS @(k ': sh1) var1)
                                           (Ast.AstIntVar var :$: ZSH)
            in substitute1AstS (SubstitutionPayloadShaped @r projection) var1
          v2 = V.foldr subst v (V.zip vars (unwrapAstDomains l))
            -- we use the substitution that does not simplify
      in Ast.AstLetDomainsS
           vars
           (build1VOccurenceUnknownDomains (valueOf @k) (var, l))
           (build1VOccurenceUnknownRefreshS (var, v2))

-- | The application @build1VIndexS k (var, v, ix)@ vectorizes
-- the term @AstBuild1S k (var, AstIndexS v ix)@, where it's unknown whether
-- @var@ occurs in any of @v@, @ix@.
--
-- We try to push indexing down as far as needed to eliminate any occurences
-- of @var@ from @v@ (but not necessarily from @ix@), which is enough
-- to replace @AstBuild1S@ with @AstGatherS@ and so complete
-- the vectorization.
--
-- This pushing down is performed by alternating steps of simplification,
-- in @astIndexStepS@, that eliminated indexing from the top of a term
-- position (except two permissible normal forms) and vectorization,
-- @build1VOccurenceUnknownS@, that recursively goes down under constructors
-- until it encounter indexing again. We have to do this in lockstep
-- so that we simplify terms only as much as needed to vectorize.
--
-- If simplification can't proceed, which means that we reached one of the few
-- normal forms wrt simplification, we invoke the pure desperation rule (D)
-- which produces large tensors, which are hard to simplify even when
-- eventually proven unnecessary. The rule changes the index to a gather
-- and pushes the build down the gather, getting the vectorization unstuck.
build1VIndexS
  :: forall k p sh r.
     ( GoodScalar r, KnownNat k, OS.Shape sh
     , OS.Shape (OS.Drop p (OS.Take p sh OS.++ OS.Drop p sh)) )
  => (AstVarId, AstShaped r sh, AstIndexS r (OS.Take p sh))
  -> AstShaped r (k ': OS.Drop p sh)
build1VIndexS (var, v0, ZSH) =
  gcastWith (unsafeCoerce Refl :: p :~: 0)
    -- otherwise sh would need to be empty, but then Take gets stuck
    -- so the application of this function wouldn't type-check
  $ build1VOccurenceUnknownS (var, v0)
build1VIndexS (var, v0, ix@(_ :$: _)) =
  gcastWith (unsafeCoerce Refl :: sh :~: OS.Take p sh OS.++ OS.Drop p sh) $
  let vTrace = Ast.AstBuild1S (var, Ast.AstIndexS v0 ix)
      traceRule = mkTraceRuleS "build1VIndexS" vTrace v0 1
  in if intVarInAstS var v0
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
         in if intVarInAstS var v1
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

mkTraceRuleS :: forall sh sh2 r. (GoodScalar r, OS.Shape sh, OS.Shape sh2)
             => String -> AstShaped r sh -> AstShaped r sh2 -> Int
             -> AstShaped r sh -> AstShaped r sh
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
