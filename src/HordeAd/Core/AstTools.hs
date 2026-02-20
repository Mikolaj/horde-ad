{-# LANGUAGE LambdaCase, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | An assortment of operations working on AST of the code to be differentiated
-- or the code resulting from differentiation.
module HordeAd.Core.AstTools
  ( -- * Full tensor kind derivation
    ftkAst, stkAstX
    -- * Variable occurrence detection
  , varInAst, varInIxS, varNameInAst, varNameInIxS
    -- * Tools related to sharing
  , astIsSmall, ixIsSmall, astLetDown, astVar, astShare
    -- * Odds and ends
  , bounds, intBounds
  , liftRFromS1, liftRFromS2, liftXFromS1, liftXFromS2
  , cAstConvert
  , cAstConvDownKFromS, cAstConvDownSFromR, cAstConvDownSFromX
  , cAstConvUpSFromK, cAstConvUpRFromS, cAstConvUpXFromS
  , pattern AstConvUpSFromK, pattern AstConvUp, AstConvUpMaybe(..)
  , convDown, convUp, convDownMaybe, convUpMaybe
  , setTotalSharing
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Bifunctor (second)
import Data.IORef
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable, typeRep)

import Data.Array.Nested (MapJust)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (withShsFromShR, withShsFromShX)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (fromSNat', snatPlus, unsafeCoerceRefl)

import HordeAd.Core.Ast
import HordeAd.Core.Conversion
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Full tensor kind derivation

-- | This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with unknowns. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape (which rarely happens in our AST that is based
-- on shaped tensors and always indicates an ill-typed term).
ftkAst :: forall s y ms. AstTensor ms s y -> FullShapeTK y
ftkAst t = case t of
  AstPair t1 t2 -> FTKProduct (ftkAst t1) (ftkAst t2)
  AstProject1 v -> case ftkAst v of
    FTKProduct ftk1 _ -> ftk1
  AstProject2 v -> case ftkAst v of
    FTKProduct _ ftk2 -> ftk2
  AstFromVector snat _ l -> case V.uncons l of
    Nothing -> error "ftkAst: empty vector"
    Just (v, _) -> buildFTK snat (ftkAst v)
  AstSum snat stk v -> razeFTK snat stk (ftkAst v)
  AstReplicate snat _ v -> buildFTK snat (ftkAst v)
  AstMapAccumLDer k bftk _eftk _f _df _rf acc0 _es ->
    FTKProduct (ftkAst acc0) (buildFTK k bftk)
  AstApply (AstLambda !_ !u) _ -> ftkAst u
  AstVar var -> varNameToFTK var
  AstCond _b v _w -> ftkAst v
  AstBuild1 snat _ (_var, v) -> buildFTK snat (ftkAst v)

  AstLet _ _ v -> ftkAst v
  AstShare var _ -> varNameToFTK var
  AstToShare v -> ftkAst v

  AstPrimalPart a -> ftkAst a
  AstDualPart a -> ftkAst a
  AstPlainPart a -> ftkAst a
  AstFromPrimal a -> ftkAst a
  AstFromDual a -> ftkAst a
  AstFromPlain a -> ftkAst a

  AstPlusK{} -> FTKScalar
  AstTimesK{} -> FTKScalar
  AstN1K{} -> FTKScalar
  AstR1K{} -> FTKScalar
  AstR2K{} -> FTKScalar
  AstI2K{} -> FTKScalar
  AstConcreteK _ -> FTKScalar
  AstFloorK{} -> FTKScalar
  AstFromIntegralK{} -> FTKScalar
  AstCastK{} -> FTKScalar
  AstArgMinK{} -> FTKScalar
  AstArgMaxK{} -> FTKScalar
  AstIndexK{} -> FTKScalar

  AstPlusS v _ -> ftkAst v
  AstTimesS v _ -> ftkAst v
  AstN1S _ v -> ftkAst v
  AstR1S _ v -> ftkAst v
  AstR2S _ v _ -> ftkAst v
  AstI2S _ v _ -> ftkAst v
  AstConcreteS a -> FTKS (Nested.sshape a) FTKScalar
  AstFloorS v -> case ftkAst v of
    FTKS sh FTKScalar -> FTKS sh FTKScalar
  AstFromIntegralS v -> case ftkAst v of
    FTKS sh FTKScalar -> FTKS sh FTKScalar
  AstCastS v -> case ftkAst v of
    FTKS sh FTKScalar -> FTKS sh FTKScalar
  AstArgMinS v -> case ftkAst v of
    FTKS sh FTKScalar -> FTKS (shsInit sh) FTKScalar
  AstArgMaxS v -> case ftkAst v of
    FTKS sh FTKScalar -> FTKS (shsInit sh) FTKScalar
  AstIndexS shn v _ix -> case ftkAst v of
    FTKS _ x -> FTKS shn x

  AstScatterS _ shn shp v _ -> case ftkAst v of
    FTKS _ x -> FTKS (shp `shsAppend` shn) x
  AstGatherS shm shn _shp v _ -> case ftkAst v of
    FTKS _ x -> FTKS (shm `shsAppend` shn) x
  AstIotaS n@SNat -> FTKS (n :$$ ZSS) FTKScalar
  AstAppendS a b -> case (ftkAst a, ftkAst b) of
    (FTKS (m :$$ sh) x, FTKS (n :$$ _) _) -> FTKS (snatPlus m n :$$ sh) x
  AstSliceS _ n@SNat _ a -> case ftkAst a of
    FTKS (_ :$$ sh) x -> FTKS (n :$$ sh) x
  AstReverseS v -> ftkAst v
  AstTransposeS perm v -> case ftkAst v of
    FTKS sh x -> FTKS (shsPermutePrefix perm sh) x
  AstReshapeS sh2 v -> case ftkAst v of
    FTKS _ x -> FTKS sh2 x

  AstConvert c u -> convertFTK c $ ftkAst u

  AstSum0{} -> FTKScalar
  AstDot0{} -> FTKScalar
  AstDot1InS sh _ _u _v -> FTKS sh FTKScalar
  AstMatmul2S m@SNat _ p@SNat _u _v -> FTKS (m :$$ p :$$ ZSS) FTKScalar

  AstBoolNotK{} -> FTKScalar
  AstBoolNotS a -> ftkAst a
  AstBoolAndK{} -> FTKScalar
  AstBoolAndS a _ -> ftkAst a
  AstLeqK{} -> FTKScalar
  AstLeq{} -> FTKScalar
  AstLeqS shb _ _ _ -> FTKS shb FTKScalar

stkAstX :: forall s x ms sh. AstTensor ms s (TKS2 sh x) -> SingletonTK x
{-# INLINE stkAstX #-}
stkAstX t = case ftkAst t of
  FTKS _ x -> ftkToSTK x


-- * Variable occurrence detection

-- | We assume no variable is shared between a binding and its nested binding
-- and nobody asks about occurrences of variables that are bound.
-- This keeps the occurrence checking code simple, because we never need
-- to compare variables to any variable in the bindings.
varInAst :: AstVarId -> AstTensor ms s y -> Bool
varInAst var = \case
  AstPair t1 t2 -> varInAst var t1 || varInAst var t2
  AstProject1 t -> varInAst var t
  AstProject2 t -> varInAst var t
  AstFromVector _ _ vl -> any (varInAst var) vl
  AstSum _ _ v -> varInAst var v
  AstReplicate _ _ v -> varInAst var v
  AstMapAccumLDer _k _bftk _eftk _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstApply t ll -> varInAstHFun var t || varInAst var ll
  AstVar var2 -> var == varNameToAstVarId var2
  AstCond b v w -> varInAst var b || varInAst var v || varInAst var w
  AstBuild1 _ _ (var2, v) ->
    assert (varNameToAstVarId var2 /= var) $
    varInAst var v

  AstLet _ u v -> varInAst var u || varInAst var v
  AstShare _ v -> varInAst var v
  AstToShare v -> varInAst var v

  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstPlainPart a -> varInAst var a
  AstFromPrimal v -> varInAst var v
  AstFromDual v -> varInAst var v
  AstFromPlain v -> varInAst var v

  AstPlusK t u -> varInAst var t || varInAst var u
  AstTimesK t u -> varInAst var t || varInAst var u
  AstN1K _ t -> varInAst var t
  AstR1K _ t -> varInAst var t
  AstR2K _ t u -> varInAst var t || varInAst var u
  AstI2K _ t u -> varInAst var t || varInAst var u
  AstConcreteK{} -> False
  AstFloorK a -> varInAst var a
  AstFromIntegralK t -> varInAst var t
  AstCastK t -> varInAst var t
  AstArgMinK t -> varInAst var t
  AstArgMaxK t -> varInAst var t
  AstIndexK v ix -> varInAst var v || varInIxS var ix

  AstPlusS t u -> varInAst var t || varInAst var u
  AstTimesS t u -> varInAst var t || varInAst var u
  AstN1S _ t -> varInAst var t
  AstR1S _ t -> varInAst var t
  AstR2S _ t u -> varInAst var t || varInAst var u
  AstI2S _ t u -> varInAst var t || varInAst var u
  AstConcreteS{} -> False
  AstFloorS a -> varInAst var a
  AstFromIntegralS a -> varInAst var a
  AstCastS t -> varInAst var t
  AstArgMinS a -> varInAst var a
  AstArgMaxS a -> varInAst var a
  AstIndexS _ v ix -> varInAst var v || varInIxS var ix

  AstScatterS _ _ _ v (_vars, ix) -> varInIxS var ix || varInAst var v
  AstGatherS _ _ _ v (_vars, ix) -> varInIxS var ix || varInAst var v
  AstIotaS{} -> False
  AstAppendS v u -> varInAst var v || varInAst var u
  AstSliceS _ _ _ v -> varInAst var v
  AstReverseS v -> varInAst var v
  AstTransposeS _perm v -> varInAst var v
  AstReshapeS _ v -> varInAst var v

  AstConvert _ v -> varInAst var v

  AstSum0 v -> varInAst var v
  AstDot0 u v -> varInAst var u || varInAst var v
  AstDot1InS _ _ u v -> varInAst var u || varInAst var v
  AstMatmul2S _ _ _ u v -> varInAst var u || varInAst var v

  AstBoolNotK b -> varInAst var b
  AstBoolNotS b -> varInAst var b
  AstBoolAndK arg1 arg2 -> varInAst var arg1 || varInAst var arg2
  AstBoolAndS arg1 arg2 -> varInAst var arg1 || varInAst var arg2
  AstLeqK arg1 arg2 -> varInAst var arg1 || varInAst var arg2
  AstLeq arg1 arg2 -> varInAst var arg1 || varInAst var arg2
  AstLeqS _ _ arg1 arg2 -> varInAst var arg1 || varInAst var arg2

varInIxS :: AstVarId -> AstIxS ms sh -> Bool
varInIxS var = any (varInAst var)

varInAstHFun :: AstVarId -> AstHFun s x y -> Bool
varInAstHFun _var AstLambda{} =
  False  -- we take advantage of the term being closed

varNameInAst :: AstVarName '(s, y) -> AstTensor ms s2 y2 -> Bool
varNameInAst var = varInAst (varNameToAstVarId var)

varNameInIxS :: AstVarName '(s, y) -> AstIxS ms sh -> Bool
varNameInIxS var = varInIxS (varNameToAstVarId var)


-- * Tools related to sharing

-- Turns off all but the most trivial cases of astIsSmall.
-- For tests only. Affects all simplification and inlining taking place
-- in parallel in the program at the time it's changed.
unsafeTotalSharingRef :: IORef Bool
{-# NOINLINE unsafeTotalSharingRef #-}
unsafeTotalSharingRef = unsafePerformIO $ newIORef False

setTotalSharing :: Bool -> IO ()
setTotalSharing b = atomicWriteIORef unsafeTotalSharingRef b

-- | A term requires sharing if it's too large as a term and so duplicating
-- it could affect the performance of simplification
-- or if it's too expensive when interpreted and so duplicating it
-- would increase the work done at runtime.
astIsSmall :: Bool -> AstTensor ms s y -> Bool
astIsSmall _ AstVar{} = True
astIsSmall _ AstShare{} = True
astIsSmall _ AstConcreteK{} = True
astIsSmall _ (AstConcreteS a) | fromSNat' (Nested.srank a) == 0 = True
astIsSmall lax t = unsafePerformIO $ do
  unsafeTotalSharing <- readIORef unsafeTotalSharingRef
  return $! if | unsafeTotalSharing -> False
               | lax -> astIsSmallN 50 t > 0
               | otherwise -> astIsSmallN 20 t > 0

-- The cases with n <= 20 are usually good redex candidates,
-- so we expose them, but only if they are not burried too deeply.
-- Some of these constructors change tensor metadata into
-- a non-canonical form, which sometimes incurs the cost of converting
-- the vector to canonical form. The cost can be shared only
-- when the constructor is not the root of the shared term,
-- so when inlining (the False argument) we share them
-- unless they are at the root of the term tree.
astIsSmallN :: Int -> AstTensor ms s y -> Int
astIsSmallN n _ | n <= 0 = 0
astIsSmallN n t0 = case t0 of
  AstPair t1 t2 -> astIsSmallN (astIsSmallN (n - 1) t1) t2
  AstProject1 t -> astIsSmallN (n - 1) t
  AstProject2 t -> astIsSmallN (n - 1) t
  AstFromVector (SNat' @1) _ v -> astIsSmallN (n - 1) $ v V.! 0
  AstSum (SNat' @1) _ v -> astIsSmallN (n - 1) v
  AstReplicate _ _ v ->
    astIsSmallN (n - 1) v  -- a really good redex and often in series
      -- executed as a metadata change, which is however not free
  AstVar{} -> n
  AstCond b u v -> astIsSmallN (astIsSmallN (astIsSmallN (n - 1) b) u) v
  AstConcreteK _ -> n
  AstConcreteS _ -> n  -- small term with zero interpretation cost;
                       -- the physical arrays is shared on GHC heap
  AstShare{} -> n
  AstPrimalPart v -> astIsSmallN (n - 1) v
  AstDualPart v -> astIsSmallN (n - 1) v
  AstPlainPart v -> astIsSmallN (n - 1) v
  AstFromPrimal v -> astIsSmallN (n - 1) v
  AstFromDual v -> astIsSmallN (n - 1) v
  AstFromPlain v -> astIsSmallN (n - 1) v

  -- This often appears from user writing (-1), often reduces away
  -- and it has only one argument.
  AstN1K NegateOp v -> astIsSmallN (n - 1) v
  AstN1S NegateOp v -> astIsSmallN (n - 1) v

  AstIotaS{} -> n
  AstSliceS _ _ _ v ->
    if n <= 20 then 0 else astIsSmallN (n - 1) v  -- executed as metadata change
  AstReverseS v ->
    astIsSmallN (n - 1) v  -- executed as a cheap metadata change
  AstTransposeS _perm v ->
    if n <= 20 then 0 else astIsSmallN (n - 1) v  -- executed as metadata change

  AstConvert _ v -> astIsSmallN (n - 1) v

  AstBoolNotK v -> astIsSmallN (n - 1) v
  AstBoolAndK u v -> astIsSmallN (astIsSmallN (n - 1) u) v
  AstLeqK u v -> astIsSmallN (astIsSmallN (n - 1) u) v
  AstLeq u v -> astIsSmallN (astIsSmallN (n - 1) u) v

  _ -> 0

ixIsSmall :: AstIxS ms sh -> Bool
ixIsSmall = all (astIsSmall True)

-- | Try to limit the scope of the let cheaply.
--
-- Note that this doesn't inline lets into indexes, so it can be safely
-- performed on user code without the risk of removing the workaround lets for
-- big non-constant values in indexes that prevent the loss of sharing occurring
-- when differentiating indexing. gathers and scatters.
astLetDown :: forall y z s s2. KnownSpan s2
           => AstVarName '(s, y) -> AstTensor AstMethodLet s y
           -> AstTensor AstMethodLet s2 z
           -> AstTensor AstMethodLet s2 z
astLetDown var u v@(AstVar var2) =
  if varNameToAstVarId var2 == varNameToAstVarId var
  then case testEquality var var2 of
    Just Refl -> u
    _ -> error "astLetDown: wrong variable types at AstVar"
  else v
astLetDown var u v = case v of
  -- Normaly the type bounds pair nesting, so the check is cheap.
  AstPair t1 t2 ->
    if | not (varNameInAst var t1) -> AstPair t1 (astLetDown var u t2)
       | not (varNameInAst var t2) -> AstPair (astLetDown var u t1) t2
       | otherwise -> AstLet var u v
  AstProject1 v2 -> AstProject1 (astLetDown var u v2)
  AstProject2 v2 -> AstProject2 (astLetDown var u v2)
  AstFromVector{} -> AstLet var u v
  AstSum snat stk v2 -> AstSum snat stk (astLetDown var u v2)
  AstReplicate snat stk v2 -> AstReplicate snat stk (astLetDown var u v2)
  -- Plausibly, accumulators are small and mapAccums are rare,
  -- so the check is cheap.
  AstMapAccumLDer k bftk eftk f df rf acc0 es ->
    if varNameInAst var acc0
    then AstLet var u v
    else AstMapAccumLDer k bftk eftk f df rf acc0 (astLetDown var u es)
  AstApply f t -> AstApply f (astLetDown var u t)
  -- handled above: AstVar
  AstCond{} -> AstLet var u v
  AstBuild1 k stk (var2, v2) ->
    let !v3 = astLetDown var u v2
    in AstBuild1 k stk (var2, v3)

  AstLet{} -> AstLet var u v

  AstPrimalPart v2 -> AstPrimalPart (astLetDown var u v2)
  AstDualPart v2 -> AstDualPart (astLetDown var u v2)
  AstPlainPart v2 -> AstPlainPart (astLetDown var u v2)
  AstFromPrimal v2 -> fromPrimal (astLetDown var u v2)
  AstFromDual v2 -> fromDual (astLetDown var u v2)
  AstFromPlain v2 -> fromPlain (astLetDown var u v2)

  AstPlusK{} -> AstLet var u v
  AstTimesK{} -> AstLet var u v
  AstN1K op u2 -> AstN1K op (astLetDown var u u2)
  AstR1K op u2 -> AstR1K op (astLetDown var u u2)
  AstR2K{} -> AstLet var u v
  AstI2K{} -> AstLet var u v
  AstConcreteK{} -> v
  AstFloorK a -> AstFloorK (astLetDown var u a)
  AstFromIntegralK v2 -> AstFromIntegralK (astLetDown var u v2)
  AstCastK v2 -> AstCastK (astLetDown var u v2)
  AstArgMinK v2 -> AstArgMinK (astLetDown var u v2)
  AstArgMaxK v2 -> AstArgMaxK (astLetDown var u v2)
  AstIndexK v2 ix ->
    if varNameInIxS var ix
    then AstLet var u v
    else AstIndexK (astLetDown var u v2) ix

  AstPlusS{} -> AstLet var u v
  AstTimesS{} -> AstLet var u v
  AstN1S op u2 -> AstN1S op (astLetDown var u u2)
  AstR1S op u2 -> AstR1S op (astLetDown var u u2)
  AstR2S{} -> AstLet var u v
  AstI2S{} -> AstLet var u v
  AstConcreteS{} -> v
  AstFloorS a -> AstFloorS (astLetDown var u a)
  AstFromIntegralS v2 -> AstFromIntegralS (astLetDown var u v2)
  AstCastS v2 -> AstCastS (astLetDown var u v2)
  AstArgMinS a -> AstArgMinS (astLetDown var u a)
  AstArgMaxS a -> AstArgMaxS (astLetDown var u a)
  -- In these three, index terms are usually small, so the check is cheap.
  -- Also, this undoes precisely the pushing of the lets up that rules
  -- for these three perform when simplifying. Note that we never push
  -- lets down indexes, which is important for user workarounds
  -- and is a legal inlining only when the iteration is trivial and so
  -- the number of dynamic occurrences of the inlined variable is trivial.
  AstIndexS shn v2 ix ->
    if varNameInIxS var ix
    then AstLet var u v
    else AstIndexS shn (astLetDown var u v2) ix

  AstScatterS shm shn shp v2 (vars, ix) ->
    if varNameInIxS var ix
    then AstLet var u v
    else AstScatterS shm shn shp (astLetDown var u v2) (vars, ix)
  AstGatherS shm shn shp v2 (vars, ix) ->
    if varNameInIxS var ix
    then AstLet var u v
    else AstGatherS shm shn shp (astLetDown var u v2) (vars, ix)
  AstIotaS{} -> v
  AstAppendS{} -> AstLet var u v
  AstSliceS i n k v2 -> AstSliceS i n k (astLetDown var u v2)
  AstReverseS v2 -> AstReverseS (astLetDown var u v2)
  AstTransposeS perm v2 -> AstTransposeS perm (astLetDown var u v2)
  AstReshapeS sh v2 -> AstReshapeS sh (astLetDown var u v2)

  AstConvert c v2 -> AstConvert c (astLetDown var u v2)

  AstSum0 v2 -> AstSum0 (astLetDown var u v2)
  AstDot0{} -> AstLet var u v
  AstDot1InS{} -> AstLet var u v
  AstMatmul2S{} -> AstLet var u v

  AstBoolNotK arg -> AstBoolNotK (astLetDown var u arg)
  AstBoolNotS arg -> AstBoolNotS (astLetDown var u arg)
  AstBoolAndK{} -> AstLet var u v
  AstBoolAndS{} -> AstLet var u v
  AstLeqK{} -> AstLet var u v
  AstLeq{} -> AstLet var u v
  AstLeqS{} -> AstLet var u v

astVar :: AstVarName '(s, y) -> AstTensor ms s y
astVar (AstVarName _ (FtkAndBoundsBounds lb ub)) | lb == ub =
  AstConcreteK lb
astVar var = AstVar var

astShare :: AstVarName '(s, y) -> AstTensor AstMethodShare s y
         -> AstTensor AstMethodShare s y
astShare (AstVarName _ (FtkAndBoundsBounds lb ub)) _ | lb == ub =
  AstConcreteK lb
astShare var t = AstShare var t


-- * Odds and ends

bounds :: forall r s ms. (Typeable r, KnownSpan s)
       => AstTensor ms s (TKScalar r) -> Maybe (r, r)
bounds t | SPlainSpan <- knownSpan @s
         , Just Refl <- testEquality (typeRep @r) (typeRep @Int) = intBounds t
bounds _ = Nothing

-- An approximation: lower and upper bound.
-- TODO: extend, e.g., to general quot and rem.
intBounds :: AstTensor ms PlainSpan (TKScalar Int) -> Maybe (Int, Int)
intBounds (AstConcreteK u) = Just (u, u)
intBounds (AstApply (AstLambda _ u) _) = intBounds u
intBounds (AstVar var) = varNameToBounds var
intBounds (AstCond _b u v) = do
  (u1, u2) <- intBounds u
  (v1, v2) <- intBounds v
  pure (min u1 v1, max u2 v2)
intBounds (AstLet _ _ u) = intBounds u  -- TODO: substitute?
intBounds (AstShare var _) = varNameToBounds var
intBounds (AstToShare u) = intBounds u
intBounds (AstPlusK u v) = do
  (u1, u2) <- intBounds u
  (v1, v2) <- intBounds v
  pure (u1 + v1, u2 + v2)
intBounds (AstN1K NegateOp u) = do
  (u1, u2) <- intBounds u
  pure (- u2, - u1)
intBounds (AstTimesK u v) = case (intBounds u, intBounds v) of
  (Nothing, Nothing) -> Nothing
  (mu, mv) ->  -- multiplication by zero makes even one operand enough;
               -- TODO: but this is, in theory, unsound, because the below
               -- are not real infinities
    let (u1, u2) = fromMaybe (-1000000000, 1000000000) mu
        (v1, v2) = fromMaybe (-1000000000, 1000000000) mv
        l = [u1 * v1, u1 * v2, u2 * v1, u2 * v2]
        (lb, ub) = (minimum l, maximum l)
    in if lb == -1000000000 && ub == 1000000000
       then Nothing
       else Just (lb, ub)
intBounds (AstI2K QuotOp u (AstConcreteK v)) | v > 0 = do  -- a common case
  (u1, u2) <- intBounds u
  pure (u1 `quotH` v, u2 `quotH` v)
intBounds (AstI2K RemOp u (AstConcreteK v)) | v > 0 = do
  (u1, u2) <- intBounds u
  pure $ if | u1 >= 0 -> (0, min u2 (v - 1))  -- very crude
            | u2 <= 0 -> (max u1 (- v + 1), 0)
            | otherwise -> (- v + 1, v - 1)
intBounds _ = Nothing

liftRFromS1 :: forall n x ms s. KnownSpan s
            => (forall sh.
                   AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
{-# INLINE liftRFromS1 #-}
liftRFromS1 f a = case ftkAst a of
  FTKR sh' x ->
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      cAstConvUpRFromS sh x
      $ f (cAstConvDownSFromR sh x a)

liftRFromS2 :: forall n x ms s. KnownSpan s
            => (forall sh.
                   AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x) -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
{-# INLINE liftRFromS2 #-}
liftRFromS2 f a b  = case ftkAst a of
  FTKR sh' x ->
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      cAstConvUpRFromS sh x
      $ f (cAstConvDownSFromR sh x a) (cAstConvDownSFromR sh x b)

liftXFromS1 :: forall sh' x ms s. KnownSpan s
            => (forall sh.
                   AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
{-# INLINE liftXFromS1 #-}
liftXFromS1 f a = case ftkAst a of
  FTKX sh' x ->
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      cAstConvUpXFromS sh' x
      $ f (cAstConvDownSFromX sh x a)

liftXFromS2 :: forall sh' x ms s. KnownSpan s
            => (forall sh.
                   AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x) -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
{-# INLINE liftXFromS2 #-}
liftXFromS2 f a b = case ftkAst a of
  FTKX sh' x ->
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      cAstConvUpXFromS sh' x
      $ f (cAstConvDownSFromX sh x a) (cAstConvDownSFromX sh x b)

cAstConvert :: KnownSpan s
            => TKConversion x z -> AstTensor ms s x -> AstTensor ms s z
cAstConvert c t
  | Just Refl <- matchingFTK (ftkAst t) (convertFTK c (ftkAst t)) = t
cAstConvert c1 (AstFromPrimal v) = fromPrimal $ cAstConvert c1 v
cAstConvert c1 (AstFromDual v) = fromDual $ cAstConvert c1 v
cAstConvert c1 (AstFromPlain v) = fromPlain $ cAstConvert c1 v
cAstConvert c1 (AstConvert c2 t2) = cAstConvert (c1 `convCmp` c2) t2
cAstConvert c t = AstConvert c t

cAstConvDownKFromS :: forall r ms s. KnownSpan s
                   => AstTensor ms s (TKS '[] r)
                   -> AstTensor ms s (TKScalar r)
cAstConvDownKFromS = cAstConvert (ConvCmp ConvX0 ConvSX)

cAstConvDownSFromR :: forall sh x ms s. KnownSpan s
                   => ShS sh -> FullShapeTK x
                   -> AstTensor ms s (TKR2 (Rank sh) x)
                   -> AstTensor ms s (TKS2 sh x)
cAstConvDownSFromR sh x t | Refl <- lemRankReplicate (Proxy @(Rank sh)) =
  cAstConvert (ConvCmp (ConvXS' (FTKS sh x)) ConvRX) t

cAstConvDownSFromX :: forall sh sh' x ms s. (KnownSpan s, Rank sh ~ Rank sh')
                   => ShS sh -> FullShapeTK x
                   -> AstTensor ms s (TKX2 sh' x)
                   -> AstTensor ms s (TKS2 sh x)
cAstConvDownSFromX sh x t = cAstConvert (ConvXS' (FTKS sh x)) t

cAstConvUpSFromK :: forall r ms s. (KnownSpan s, GoodScalar r)
                 => AstTensor ms s (TKScalar r)
                 -> AstTensor ms s (TKS '[] r)
cAstConvUpSFromK = cAstConvert (ConvCmp ConvXS (Conv0X STKScalar))

cAstConvUpRFromS :: forall sh x ms s. KnownSpan s
                 => ShS sh -> FullShapeTK x
                 -> AstTensor ms s (TKS2 sh x)
                 -> AstTensor ms s (TKR2 (Rank sh) x)
cAstConvUpRFromS sh x | Refl <- lemRankMapJust sh =
  cAstConvert (ConvCmp (ConvXR (ftkToSTK x)) ConvSX)

cAstConvUpXFromS :: forall sh sh' x ms s. (KnownSpan s, Rank sh ~ Rank sh')
                 => IShX sh' -> FullShapeTK x
                 -> AstTensor ms s (TKS2 sh x)
                 -> AstTensor ms s (TKX2 sh' x)
cAstConvUpXFromS sh' x =
  gcastWith (unsafeCoerceRefl :: Rank (MapJust sh) :~: Rank sh) $
  cAstConvert (ConvCmp (ConvXX' (FTKX sh' x)) ConvSX)

pattern AstConvUpSFromK :: () => sh ~ '[]
                        => AstTensor ms s (TKScalar r)
                        -> AstTensor ms s (TKS sh r)
pattern AstConvUpSFromK t <- (matchAstConvUpSFromK -> Just (Refl, t))

matchAstConvUpSFromK :: AstTensor ms s (TKS sh r)
                     -> Maybe ( sh :~: '[]
                              , AstTensor ms s (TKScalar r) )
matchAstConvUpSFromK = \case
  AstConvert c t
    | FTKScalar @ry <- ftkAst t
    , FTKS ZSS (FTKScalar @r) <- convertFTK c (ftkAst t)
    , Just Refl <- testEquality (typeRep @ry) (typeRep @r) ->
      Just (Refl, t)
  AstConvert c t
    | FTKR ZSR (FTKScalar @ry) <- ftkAst t
    , FTKS ZSS (FTKScalar @r) <- convertFTK c (ftkAst t)
    , Just Refl <- testEquality (typeRep @ry) (typeRep @r) ->
      Just (Refl, AstConvert (ConvCmp ConvX0 ConvRX) t)
  AstConvert c t
    | FTKX ZSX (FTKScalar @ry) <- ftkAst t
    , FTKS ZSS (FTKScalar @r) <- convertFTK c (ftkAst t)
    , Just Refl <- testEquality (typeRep @ry) (typeRep @r) ->
      Just (Refl, AstConvert ConvX0 t)
  AstConcreteS a | ZSS <- Nested.sshape a ->
    Just (Refl, AstConcreteK $ Nested.sunScalar a)
  AstFromPrimal t -> second AstFromPrimal <$> matchAstConvUpSFromK t
  AstFromDual t -> second AstFromDual <$> matchAstConvUpSFromK t
  AstFromPlain t -> second AstFromPlain <$> matchAstConvUpSFromK t
  _ -> Nothing

-- TODO: simplify this monstrosity, if possible
pattern AstConvUp :: forall {z1} {ms1} {s1}.
                     forall y z ms s. (z ~ z1, ms ~ ms1, s ~ s1)
                  => TKConversion y z -> FullShapeTK z -> AstTensor ms s y
                  -> AstTensor ms1 s1 z1
pattern AstConvUp c zftk a <- (matchAstConvUp -> AstConvUpJust c zftk a)

type role AstConvUpMaybe nominal nominal nominal
data AstConvUpMaybe z ms s =
    forall y.
    AstConvUpJust (TKConversion y z) (FullShapeTK z) (AstTensor ms s y)
  | AstConvUpNothing

matchAstConvUp :: AstTensor ms s z -> AstConvUpMaybe z ms s
matchAstConvUp = \case
  AstConvert c t
    | FTKR ZSR (FTKScalar @ry) <- ftkAst t
    , let zftk = convertFTK c (ftkAst t)
    , FTKS ZSS (FTKScalar @r) <- zftk
    , Just Refl <- testEquality (typeRep @ry) (typeRep @r) ->
      AstConvUpJust (ConvCmp ConvXS (Conv0X STKScalar))
                    zftk
                    (AstConvert (ConvCmp ConvX0 ConvRX) t)
  AstConvert c t
    | FTKX ZSX (FTKScalar @ry) <- ftkAst t
    , let zftk = convertFTK c (ftkAst t)
    , FTKS ZSS (FTKScalar @r) <- zftk
    , Just Refl <- testEquality (typeRep @ry) (typeRep @r) ->
      AstConvUpJust (ConvCmp ConvXS (Conv0X STKScalar))
                    zftk
                    (AstConvert ConvX0 t)
  AstConvert c t
    | FTKS ZSS (FTKScalar @r) <- ftkAst t
    , let zftk = convertFTK c (ftkAst t)
    , FTKR ZSR (FTKScalar @ry) <- zftk
    , Just Refl <- testEquality (typeRep @ry) (typeRep @r) ->
      AstConvUpJust (ConvCmp (ConvXR STKScalar) (Conv0X STKScalar))
                    zftk
                    (AstConvert (ConvCmp ConvX0 ConvSX) t)
  AstConvert c t
    | FTKS ZSS (FTKScalar @r) <- ftkAst t
    , let zftk = convertFTK c (ftkAst t)
    , FTKX ZSX (FTKScalar @ry) <- zftk
    , Just Refl <- testEquality (typeRep @ry) (typeRep @r) ->
      AstConvUpJust (Conv0X STKScalar)
                    zftk
                    (AstConvert (ConvCmp ConvX0 ConvSX) t)
  AstConvert c t ->
    let yftk = ftkAst t
        zftk = convertFTK c yftk
    in case convUpMaybe (ftkAst t) zftk of
      Just c2 -> AstConvUpJust c2 zftk t
      Nothing -> AstConvUpNothing
  AstConcreteS a | ZSS <- Nested.sshape a ->
    AstConvUpJust (ConvCmp ConvXS (Conv0X STKScalar))
                  (FTKS ZSS FTKScalar)
                  (AstConcreteK $ Nested.sunScalar a)
  AstFromPrimal t -> case matchAstConvUp t of
    AstConvUpJust c zftk u -> AstConvUpJust c zftk (AstFromPrimal u)
    AstConvUpNothing -> AstConvUpNothing
  AstFromDual t -> case matchAstConvUp t of
    AstConvUpJust c zftk u -> AstConvUpJust c zftk (AstFromDual u)
    AstConvUpNothing -> AstConvUpNothing
  AstFromPlain t -> case matchAstConvUp t of
    AstConvUpJust c zftk u -> AstConvUpJust c zftk (AstFromPlain u)
    AstConvUpNothing -> AstConvUpNothing
  _ -> AstConvUpNothing

convDown :: FullShapeTK y -> SingletonTK z -> TKConversion y z
convDown yftk zstk = case convDownMaybe yftk zstk of
  Just c -> c
  Nothing -> error $ "convDown: unexpected types "  -- TODO: try nevertheless?
                     ++ "(" ++ show yftk ++ ", " ++ show zstk ++ ")"

convUp :: FullShapeTK y -> FullShapeTK z -> TKConversion y z
convUp yftk zftk = case convUpMaybe yftk zftk of
  Just c -> c
  Nothing -> error $ "convUp: unexpected types "  -- TODO: try nevertheless?
                     ++ "(" ++ show yftk ++ ", " ++ show zftk ++ ")"

convDownMaybe :: FullShapeTK y0 -> SingletonTK z0 -> Maybe (TKConversion y0 z0)
convDownMaybe = \cases
  yftk0 zstk0 | Just Refl <- sameSTK (ftkToSTK yftk0) zstk0 -> Just ConvId
  (FTKS ZSS (FTKScalar @ry)) (STKScalar @rz)
    | Just Refl <- testEquality (typeRep @ry) (typeRep @rz) ->
      Just $ convCmp ConvX0 ConvSX
  (FTKR ZSR (FTKScalar @ry)) (STKScalar @rz)
    | Just Refl <- testEquality (typeRep @ry) (typeRep @rz) ->
      Just $ convCmp ConvX0 ConvRX
  (FTKX ZSX (FTKScalar @ry)) (STKScalar @rz)
    | Just Refl <- testEquality (typeRep @ry) (typeRep @rz) ->
      Just ConvX0
  (FTKR rsh rx) (STKS @sh sh@(_ :$$ _) x)
    | Just Refl <- sameSTK x (ftkToSTK rx)
    , Just Refl <- testEquality (shsRank sh) (shrRank rsh)
    , Refl <- lemRankReplicate (Proxy @(Rank sh)) ->
      Just $ convCmp (ConvXS' (FTKS sh rx)) ConvRX
  (FTKX xsh xx) (STKS sh@(_ :$$ _) x)
    | Just Refl <- sameSTK x (ftkToSTK xx)
    , Just Refl <- testEquality (shsRank sh) (shxRank xsh)
    , Refl <- lemRankMapJust sh ->
      Just $ ConvXS' (FTKS sh xx)
  (FTKProduct yftk1 yftk2) (STKProduct zstk1 zstk2) -> do
    c1 <- convDownMaybe yftk1 zstk1
    c2 <- convDownMaybe yftk2 zstk2
    Just $ ConvT2 c1 c2
  (FTKProduct (FTKS sh' yftk1) (FTKS sh'' yftk2)) (STKS sh (STKProduct ystk1
                                                                       ystk2))
    | Just Refl <- testEquality sh sh'
    , Just Refl <- testEquality sh sh''
    , Just Refl <- sameSTK ystk1 (ftkToSTK yftk1)
    , Just Refl <- sameSTK ystk2 (ftkToSTK yftk2) ->
      Just
      $ convCmp
          ConvXS
          (convCmp
             (ConvZip ystk1 ystk2)
             (ConvT2 ConvSX ConvSX))
  _ _ -> Nothing

convUpMaybe :: FullShapeTK y0 -> FullShapeTK z0 -> Maybe (TKConversion y0 z0)
convUpMaybe = \cases
  yftk0 zftk0 | Just Refl <- matchingFTK yftk0 zftk0 -> Just ConvId
  (FTKScalar @rz) (FTKS ZSS (FTKScalar @ry))
    | Just Refl <- testEquality (typeRep @ry) (typeRep @rz) ->
      Just $ convCmp ConvXS (Conv0X STKScalar)
  (FTKScalar @rz) (FTKR ZSR (FTKScalar @ry))
    | Just Refl <- testEquality (typeRep @ry) (typeRep @rz) ->
      Just $ convCmp (ConvXR STKScalar) (Conv0X STKScalar)
  (FTKScalar @rz) (FTKX ZSX (FTKScalar @ry))
    | Just Refl <- testEquality (typeRep @ry) (typeRep @rz) ->
      Just $ Conv0X STKScalar
  (FTKS sh@(_ :$$ _) x) (FTKR rsh rx)
    | Just Refl <- matchingFTK x rx
    , Just Refl <- testEquality (shsRank sh) (shrRank rsh)
    , Refl <- lemRankMapJust sh ->
      Just $ convCmp (ConvXR (ftkToSTK x)) ConvSX
  (FTKS sh@(_ :$$ _) x) zftk0@(FTKX xsh xx)
    | Just Refl <- matchingFTK x xx
    , Just Refl <- testEquality (shsRank sh) (shxRank xsh)
    , Refl <- lemRankMapJust sh ->
      Just $ convCmp (ConvXX' zftk0) ConvSX
  (FTKProduct yftk1 yftk2) (FTKProduct zftk1 zftk2) -> do
    c1 <- convUpMaybe yftk1 zftk1
    c2 <- convUpMaybe yftk2 zftk2
    Just $ ConvT2 c1 c2
  (FTKS sh (FTKProduct yftk1 yftk2)) (FTKProduct (FTKS sh' yftk1')
                                                 (FTKS sh'' yftk2'))
    | Just Refl <- testEquality sh sh'
    , Just Refl <- testEquality sh sh''
    , Just Refl <- matchingFTK yftk1 yftk1'
    , Just Refl <- matchingFTK yftk2 yftk2' ->
      Just
      $ convCmp
          (ConvT2 ConvXS ConvXS)
          (convCmp
             (ConvUnzip (ftkToSTK yftk1) (ftkToSTK yftk2))
             ConvSX)
  _ _ -> Nothing
