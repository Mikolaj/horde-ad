{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | An assortment of operations working on AST of the code to be differentiated
-- or the code resulting from differentiation.
module HordeAd.Core.AstTools
  ( -- * Full tensor kind derivation
    ftkAst, isTensorInt
    -- * Variable occurrence detection
  , varInAst, varInAstBool, varInIxS, varNameInAst, varNameInIxS
    -- * Determining if a term is too small to require sharing
  , astIsSmall, ixIsSmall
    -- * Odds and ends
  , bounds
  , liftRFromS1, liftRFromS2, liftXFromS1, liftXFromS2
  , cAstSFromK, cAstSFromR, cAstSFromX
  , setTotalSharing
  ) where

import Prelude hiding (foldl')

import Control.Exception.Assert.Sugar
import Data.Int (Int64)
import Data.IORef
import Data.Proxy (Proxy)
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (snatPlus)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.Ast
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
  AstMapAccumRDer k bftk _eftk _f _df _rf acc0 _es ->
    FTKProduct (ftkAst acc0) (buildFTK k bftk)
  AstMapAccumLDer k bftk _eftk _f _df _rf acc0 _es ->
    FTKProduct (ftkAst acc0) (buildFTK k bftk)
  AstApply (AstLambda !_ !l) _ -> ftkAst l
  AstVar var -> varNameToFTK var
  AstCond _b v _w -> ftkAst v
  AstBuild1 snat _ (_var, v) -> buildFTK snat (ftkAst v)

  AstLet _ _ v -> ftkAst v
  AstShare var _ -> varNameToFTK var
  AstToShare v -> ftkAst v

  AstPrimalPart a -> ftkAst a
  AstDualPart a -> ftkAst a
  AstFromPrimal a -> ftkAst a
  AstFromDual a -> ftkAst a

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

  AstIndexS shn v _ix -> case ftkAst v of
    FTKS _ x -> FTKS shn x
  AstScatterS shn v (_ , ix) -> case ftkAst v of
    FTKS _ x -> FTKS (ixsToShS ix `shsAppend` shn) x
  AstGatherS shn v (vars, _) -> case ftkAst v of
    FTKS _ x -> FTKS (listsToShS vars `shsAppend` shn) x
  AstMinIndexS v -> case ftkAst v of
    FTKS sh FTKScalar -> FTKS (shsInit sh) FTKScalar
  AstMaxIndexS v -> case ftkAst v of
    FTKS sh FTKScalar -> FTKS (shsInit sh) FTKScalar
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
  AstZipS v -> case ftkAst v of
    FTKProduct (FTKS sh y) (FTKS _ z) -> FTKS sh (FTKProduct y z)
  AstUnzipS v -> case ftkAst v of
    FTKS sh (FTKProduct y z) -> FTKProduct (FTKS sh y) (FTKS sh z)
  AstNestS sh1 sh2 v -> case ftkAst v of
    FTKS _ x -> FTKS sh1 (FTKS sh2 x)
  AstUnNestS v -> case ftkAst v of
    FTKS sh1 (FTKS sh2 x) -> FTKS (sh1 `shsAppend` sh2) x

  AstFromS stkz v ->
    let fromS :: FullShapeTK y2 -> SingletonTK z2 -> FullShapeTK z2
        fromS ftk stk = case (ftk, stk) of
          _ | Just Refl <- sameSTK (ftkToSTK ftk) stk -> ftk
          (FTKS ZSS (FTKScalar @r1), STKScalar @r2) ->
            case testEquality (typeRep @r1) (typeRep @r2) of
              Just Refl -> FTKScalar
              Nothing -> error "ftkAst: wrong tensor kinds for AstFromS"
          (FTKS sh x, STKR nx zx) ->
            case ( sameSTK (ftkToSTK x) zx
                 , testEquality (shsRank sh) nx ) of
              (Just Refl, Just Refl) -> FTKR (shCastSR sh) x
              _ -> error $ "ftkAst: wrong tensor kinds for AstFromS: "
                           ++ show (ftkToSTK x) ++ " vs " ++ show zx ++ " and "
                           ++ show sh ++ " vs " ++ show nx
          (FTKS sh x, STKX shx zx) ->
            case ( sameSTK (ftkToSTK x) zx
                 , testEquality (shsRank sh) (ssxRank shx) ) of
              (Just Refl, Just Refl) -> FTKX (shCastSX shx sh) x
              _ -> error "ftkAst: wrong tensor kinds for AstFromS"
          (FTKProduct ftk1 ftk2, STKProduct stk1 stk2) ->
            FTKProduct (fromS ftk1 stk1) (fromS ftk2 stk2)
          _ -> error $ "ftkAst: wrong tensor kinds for AstFromS: "
                       ++ show (ftk, stk)
    in fromS (ftkAst v) stkz
  AstSFromK{} -> FTKS ZSS FTKScalar
  AstSFromR sh v -> case ftkAst v of
    FTKR _ x -> FTKS sh x
  AstSFromX sh v -> case ftkAst v of
    FTKX _ x -> FTKS sh x

  AstSum0S v ->  case ftkAst v of
    FTKS _ x -> FTKS ZSS x
  AstDot0S _u _v -> FTKS ZSS FTKScalar
  AstDot1InS sh _ _u _v -> FTKS sh FTKScalar
  AstMatmul2S m@SNat _ p@SNat _u _v -> FTKS (m :$$ p :$$ ZSS) FTKScalar

isTensorInt :: forall s y ms. AstSpan s
            => Proxy s -> FullShapeTK y
            -> Maybe (AstTensor ms s y :~: AstInt ms)
isTensorInt _ ftk = case ftk of
  FTKScalar @r -> case ( testEquality (typeRep @r) (typeRep @Int64)
                       , sameAstSpan @s @PrimalSpan ) of
                    (Just Refl, Just Refl) -> Just Refl
                    _ -> Nothing
  _ -> Nothing


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
  AstMapAccumRDer _k _bftk _eftk _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstMapAccumLDer _k _bftk _eftk _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstApply t ll -> varInAstHFun var t || varInAst var ll
  AstVar var2 -> var == varNameToAstVarId var2
  AstCond b v w -> varInAstBool var b || varInAst var v || varInAst var w
  AstBuild1 _ _ (var2, v) ->
    assert (varNameToAstVarId var2 /= var) $
    varInAst var v

  AstLet _ u v -> varInAst var u || varInAst var v
  AstShare _ v -> varInAst var v
  AstToShare v -> varInAst var v

  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstFromPrimal v -> varInAst var v
  AstFromDual v -> varInAst var v

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

  AstIndexS _ v ix -> varInAst var v || varInIxS var ix
  AstScatterS _ v (_vars, ix) -> varInIxS var ix || varInAst var v
  AstGatherS _ v (_vars, ix) -> varInIxS var ix || varInAst var v
  AstMinIndexS a -> varInAst var a
  AstMaxIndexS a -> varInAst var a
  AstIotaS{} -> False
  AstAppendS v u -> varInAst var v || varInAst var u
  AstSliceS _ _ _ v -> varInAst var v
  AstReverseS v -> varInAst var v
  AstTransposeS _perm v -> varInAst var v
  AstReshapeS _ v -> varInAst var v
  AstZipS v -> varInAst var v
  AstUnzipS v -> varInAst var v
  AstNestS _ _ v -> varInAst var v
  AstUnNestS v -> varInAst var v

  AstFromS _ v -> varInAst var v
  AstSFromK t -> varInAst var t
  AstSFromR _ v -> varInAst var v
  AstSFromX _ v -> varInAst var v

  AstSum0S v -> varInAst var v
  AstDot0S u v -> varInAst var u || varInAst var v
  AstDot1InS _ _ u v -> varInAst var u || varInAst var v
  AstMatmul2S _ _ _ u v -> varInAst var u || varInAst var v

varInIxS :: AstVarId -> AstIxS ms sh -> Bool
varInIxS var = any (varInAst var)

varInAstHFun :: AstVarId -> AstHFun s s2 x y -> Bool
varInAstHFun _var AstLambda{} =
  False  -- we take advantage of the term being closed

varInAstBool :: AstVarId -> AstBool ms -> Bool
varInAstBool var = \case
  AstBoolConst{} -> False
  AstBoolNot b -> varInAstBool var b
  AstBoolAnd arg1 arg2 -> varInAstBool var arg1 || varInAstBool var arg2
  AstLeqK arg1 arg2 -> varInAst var arg1 || varInAst var arg2
  AstLeqS arg1 arg2 -> varInAst var arg1 || varInAst var arg2

varNameInAst :: AstVarName f y -> AstTensor ms s2 y2 -> Bool
varNameInAst var = varInAst (varNameToAstVarId var)

varNameInIxS :: AstVarName f y -> AstIxS ms sh -> Bool
varNameInIxS var = varInIxS (varNameToAstVarId var)


-- * Determining if a term requires sharing

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
astIsSmall _ AstConcreteK{} = True
astIsSmall _ (AstConcreteS a) | sNatValue (Nested.srank a) == 0 = True
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
  -- Projections are so cheap that the environment machinery is expensive
  -- in comparison, so no limit to the length of projections chains.
  AstProject1 t -> astIsSmallN n t
  AstProject2 t -> astIsSmallN n t
  AstFromVector (SNat' @1) _ v -> astIsSmallN (n - 1) $ v V.! 0
  AstSum (SNat' @1) _ v -> astIsSmallN (n - 1) v
  AstReplicate _ _ v ->
    astIsSmallN (n - 1) v  -- a really good redex and often in series
      -- executed as a metadata change, which is however not free
  AstVar{} -> n
  AstCond b u v -> astIsSmallN (astIsSmallN (astBoolIsSmallN (n - 1) b) u) v
  AstConcreteK _ -> n
  AstConcreteS _ -> n  -- small term with zero interpretation cost;
                       -- the physical arrays is shared on GHC heap

  AstPrimalPart v -> astIsSmallN (n - 1) v
  AstDualPart v -> astIsSmallN (n - 1) v
  AstFromPrimal v -> astIsSmallN (n - 1) v
  AstFromDual v -> astIsSmallN (n - 1) v

  AstPlusK u v -> if n <= 20 then 0 else astIsSmallN (astIsSmallN (n - 1) u) v
  AstTimesK u v -> if n <= 20 then 0 else astIsSmallN (astIsSmallN (n - 1) u) v
  AstN1K _ u -> if n <= 20 then 0 else astIsSmallN (n - 1) u
  AstR1K _ u -> if n <= 20 then 0 else astIsSmallN (n - 1) u
  AstR2K _ u v -> if n <= 20 then 0 else astIsSmallN (astIsSmallN (n - 1) u) v
  AstI2K _ u v -> if n <= 20 then 0 else astIsSmallN (astIsSmallN (n - 1) u) v
  AstFloorK u -> if n <= 20 then 0 else astIsSmallN (n - 1) u
  AstFromIntegralK v -> if n <= 20 then 0 else astIsSmallN (n - 1) v
  AstCastK v -> if n <= 20 then 0 else astIsSmallN (n - 1) v

  AstIotaS{} -> n
  AstSliceS _ _ _ v ->
    if n <= 20 then 0 else astIsSmallN (n - 1) v  -- executed as metadata change
  AstReverseS v ->
    astIsSmallN (n - 1) v  -- executed as a cheap metadata change
  AstTransposeS _perm v ->
    if n <= 20 then 0 else astIsSmallN (n - 1) v  -- executed as metadata change
  AstZipS v ->
    astIsSmallN (n - 1) v  -- executed as a cheap metadata change
  AstUnzipS v ->
    astIsSmallN (n - 1) v  -- executed as a cheap metadata change
  AstNestS _ _ v ->
    if n <= 20 then 0 else astIsSmallN (n - 1) v  -- executed as metadata change
  AstUnNestS v ->
    astIsSmallN (n - 1) v  -- executed as a cheap metadata change

  AstFromS _ v -> astIsSmallN (n - 1) v
  AstSFromK v -> astIsSmallN (n - 1) v
  AstSFromR _ v -> astIsSmallN (n - 1) v
  AstSFromX _ v -> astIsSmallN (n - 1) v

  _ -> 0

astBoolIsSmallN :: Int -> AstBool ms -> Int
astBoolIsSmallN n _ | n <= 0 = 0
astBoolIsSmallN n t0 = case t0 of
  AstBoolConst{} -> n
  AstBoolNot v -> astBoolIsSmallN (n - 1) v
  AstBoolAnd u v -> astBoolIsSmallN (astBoolIsSmallN (n - 1) u) v
  AstLeqK u v -> astIsSmallN (astIsSmallN (n - 1) u) v
  AstLeqS u v -> astIsSmallN (astIsSmallN (n - 1) u) v

ixIsSmall :: AstIxS ms sh -> Bool
ixIsSmall = all (astIsSmall True)

-- * Odds and ends

-- An approximation: lower and upper bound.
-- TODO: extend, e.g., to general quot and rem.
bounds :: GoodScalar r => AstTensor ms s (TKScalar r) -> (r, r)
bounds (AstConcreteK u) = (u, u)
bounds (AstVar var) = case varNameToBounds var of
  Nothing -> (-1000000000, 1000000000)
  Just (u1, u2) -> (fromIntegral u1, fromIntegral u2)
bounds (AstFromPrimal u) = bounds u
bounds (AstPrimalPart u) = bounds u
bounds (AstCond _b u v) = let (u1, u2) = bounds u
                              (v1, v2) = bounds v
                          in (min u1 v1, max u2 v2)
bounds (AstLet _ _ u) = bounds u  -- TODO: substitute?
bounds (AstPlusK u v) = let (u1, u2) = bounds u
                            (v1, v2) = bounds v
                        in (u1 + v1, u2 + v2)
bounds (AstN1K NegateOp u) = let (u1, u2) = bounds u in (- u2, - u1)
bounds (AstTimesK u v) =
  let (u1, u2) = bounds u
      (v1, v2) = bounds v
      l = [u1 * v1, u1 * v2, u2 * v1, u2 * v2]
  in (minimum l, maximum l)
bounds (AstI2K QuotOp u (AstConcreteK v)) | v > 0 =  -- a common case
  let (u1, u2) = bounds u
  in (u1 `quotH` v, u2 `quotH` v)
bounds (AstI2K RemOp u (AstConcreteK v)) | v > 0 =
  let (u1, u2) = bounds u
  in if | u1 >= 0 -> (0, min u2 (v - 1))  -- very crude
        | u2 <= 0 -> (max u1 (- v + 1), 0)
        | otherwise -> (- v + 1, v - 1)
bounds _ = (-1000000000, 1000000000)

liftRFromS1 :: forall n x ms s.
               (forall sh.
                   AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
-- The cheapest possible optimization to prevent trivial term buildup.
liftRFromS1 f (AstFromS stkz@(STKR snat x) u) = case ftkAst u of
  FTKS _ xu ->
    case sameSTK x (ftkToSTK xu) of
      Just Refl -> case f u of
        AstSFromR sh a | Just Refl <- testEquality (shsRank sh) snat -> a
        a -> AstFromS stkz a
      _ -> error $ "liftRFromS1: tensor kinds don't agree: "
                   ++ show x ++ " " ++ show xu
  _ -> error "liftRFromS1: unexpected tensor kind"
-- The pessimistic case, no optimization at all.
liftRFromS1 f a = case ftkAst a of
  ftk@(FTKR sh' _) ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      AstFromS @(TKS2 sh x) (ftkToSTK ftk)
      $ f (cAstSFromR @sh sh a)

-- We refrain from checking for AstFromPrimal (AstFromS), because that would
-- add three more cases for little gain (arithmetic expressions are unlikely
-- to have AstFromPrimal and especially a build-up of interspersed
-- conversions and AstFromPrimal).
liftRFromS2 :: forall n x ms s.
               (forall sh.
                   AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKR2 n x) -> AstTensor ms s (TKR2 n x)
            -> AstTensor ms s (TKR2 n x)
liftRFromS2 f (AstFromS stkz@(STKR snat x) u) (AstFromS _ v) =
  case (ftkAst u, ftkAst v) of
    (ftku@(FTKS shu xu), ftkv@(FTKS shv xv)) ->
      case ( sameSTK (ftkToSTK xu) x
           , sameSTK (ftkToSTK xv) x
           , testEquality shu shv ) of
      (Just Refl, Just Refl, Just Refl) -> case f u v of
        AstSFromR sh a | Just Refl <- testEquality (shsRank sh) snat -> a
        a -> AstFromS stkz a
      _ -> error $ "liftRFromS2: tensor kinds don't agree: "
                   ++ show ftku ++ " " ++ show ftkv ++ " "
                   ++ show stkz
    _ -> error "liftRFromS2: unexpected tensor kinds"
liftRFromS2 f a b  = case ftkAst a of
  ftk@(FTKR sh' _) ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      AstFromS @(TKS2 sh x) (ftkToSTK ftk)
      $ f (cAstSFromR @sh sh a) (cAstSFromR @sh sh b)
        -- both are not AstFromS, but one may be

liftXFromS1 :: forall sh' x ms s.
               (forall sh.
                   AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
liftXFromS1 f (AstFromS stkz@(STKX _ x) u) = case ftkAst u of
  FTKS _ xu ->
    case sameSTK x (ftkToSTK xu) of
      Just Refl -> case f u of
        AstSFromX _ a | Just Refl <- sameSTK stkz (ftkToSTK (ftkAst a)) -> a
        a -> AstFromS stkz a
      _ -> error $ "liftXFromS1: tensor kinds don't agree: "
                   ++ show x ++ " " ++ show xu
  _ -> error "liftXFromS1: unexpected tensor kind"
liftXFromS1 f a = case ftkAst a of
  ftk@(FTKX sh' _) ->
    withCastXS sh' $ \(sh :: ShS sh) ->
      AstFromS @(TKS2 sh x) (ftkToSTK ftk)
      $ f (cAstSFromX @sh @sh' sh a)

liftXFromS2 :: forall sh' x ms s.
               (forall sh.
                   AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 sh x))
            -> AstTensor ms s (TKX2 sh' x) -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKX2 sh' x)
liftXFromS2 f (AstFromS stkz@(STKX _ x) u) (AstFromS _ v) =
  case (ftkAst u, ftkAst v) of
    (ftku@(FTKS shu xu), ftkv@(FTKS shv xv)) ->
      case ( sameSTK (ftkToSTK xu) x
           , sameSTK (ftkToSTK xv) x
           , testEquality shu shv ) of
        (Just Refl, Just Refl, Just Refl) -> case f u v of
          AstSFromX _ a | Just Refl <- sameSTK stkz (ftkToSTK (ftkAst a)) -> a
          a -> AstFromS stkz a
        _ -> error $ "liftXFromS2: tensor kinds don't agree: "
                     ++ show ftku ++ " " ++ show ftkv ++ " "
                     ++ show (STKS shu x)
    _ -> error "liftXFromS2: unexpected tensor kinds"
liftXFromS2 f a b = case ftkAst a of
  ftk@(FTKX sh' _) ->
    withCastXS sh' $ \(sh :: ShS sh) ->
      AstFromS @(TKS2 sh x) (ftkToSTK ftk)
      $ f (cAstSFromX @sh @sh' sh a) (cAstSFromX @sh @sh' sh b)

cAstSFromK :: forall r ms s. GoodScalar r
           => AstTensor ms s (TKScalar r) -> AstTensor ms s (TKS '[] r)
cAstSFromK (AstFromS _ v) =
  case matchingFTK (ftkAst v) (FTKS ZSS (FTKScalar @r)) of
    Just Refl -> v
    _ -> error "cAstSFromK: different shapes in AstSFromK(AstFromS)"
cAstSFromK (AstFromPrimal (AstFromS _ v)) =
  case matchingFTK (ftkAst v) (FTKS ZSS (FTKScalar @r)) of
    Just Refl -> AstFromPrimal v
    _ -> error "cAstSFromK: different shapes in AstSFromK(AstFromS)"
cAstSFromK v = AstSFromK v

cAstSFromR :: forall sh x ms s.
              ShS sh -> AstTensor ms s (TKR2 (Rank sh) x)
           -> AstTensor ms s (TKS2 sh x)
cAstSFromR sh w@(AstFromS _ v) | FTKR _ x <- ftkAst w =
  case matchingFTK (FTKS sh x) (ftkAst v) of
    Just Refl -> v
    _ -> error "cAstSFromR: different shapes in AstSFromR(AstFromS)"
cAstSFromR sh (AstFromPrimal w@(AstFromS _ v)) | FTKR _ x <- ftkAst w =
  case matchingFTK (FTKS sh x) (ftkAst v) of
    Just Refl -> AstFromPrimal v
    _ -> error "cAstSFromR: different shapes in AstSFromR(AstFromS)"
cAstSFromR sh v = AstSFromR sh v

cAstSFromX :: forall sh sh' x ms s. Rank sh ~ Rank sh'
           => ShS sh -> AstTensor ms s (TKX2 sh' x)
           -> AstTensor ms s (TKS2 sh x)
cAstSFromX sh w@(AstFromS _ v) | FTKX _ x <- ftkAst w =
  case matchingFTK (FTKS sh x) (ftkAst v) of
    Just Refl -> v
    _ -> error "cAstSFromX: different shapes in AstSFromX(AstFromS)"
cAstSFromX sh (AstFromPrimal w@(AstFromS _ v)) | FTKX _ x <- ftkAst w =
  case matchingFTK (FTKS sh x) (ftkAst v) of
    Just Refl -> AstFromPrimal v
    _ -> error "cAstSFromX: different shapes in AstSFromX(AstFromS)"
cAstSFromX sh v = AstSFromX sh v
