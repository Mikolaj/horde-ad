{-# LANGUAGE CPP #-}
-- | Interpretation of AST terms in an arbitrary tensor operations
-- class instance. With the exception of the the interpretation
-- of the sharing mechanisms and any other performance tweaks,
-- the interpretation is the unique homorphism determined by the instance.
-- The sharing mechanisms are translated so as to preserve sharing in case
-- the instance is a term algebra as well.
module HordeAd.Core.AstInterpret
  ( interpretAstFull, interpretAstPrimal, interpretAstDual, interpretAst
    -- * Exported only to specialize elsewhere
  , interpretAstBool
  ) where

import Prelude

import Data.Coerce (coerce)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Type.Reflection (typeRep)

import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstTools
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

interpretAstFull
  :: forall target y. ADReady target
  => AstEnv target -> AstTensor AstMethodLet FullSpan y
  -> target y
{-# INLINE interpretAstFull #-}
interpretAstFull = interpretAst

-- Strict environment and strict ADVal and Delta make this hard to optimize.
-- Either the environment has to be traversed to remove the dual parts or
-- the dual part needs to be potentially needlessly computed.
-- However, with correct sharing and large tensors, the overall cost
-- is negligible, so we optimize only minimally.
-- It helps that usually the dual part is either trivially computed
-- to be zero or is used elsewhere. It's rarely really lost and forgotten.
interpretAstPrimal
  :: forall target y. ADReady target
  => AstEnv target -> AstTensor AstMethodLet PrimalSpan y
  -> PrimalOf target y
interpretAstPrimal !env v1 = case v1 of
  -- This prevents computing the complex dual parts for mapAccum in ADVal.
  AstMapAccumRDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFunPrimal env f0
        df = interpretAstHFunPrimal env df0
        rf = interpretAstHFunPrimal env rf0
        acc02 = interpretAstPrimal env acc0
        es2 = interpretAstPrimal env es
    in tmapAccumRDer (Proxy @(PrimalOf target))
                     k (ftkAst acc0) bftk eftk f df rf acc02 es2
  AstMapAccumLDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFunPrimal env f0
        df = interpretAstHFunPrimal env df0
        rf = interpretAstHFunPrimal env rf0
        acc02 = interpretAstPrimal env acc0
        es2 = interpretAstPrimal env es
    in tmapAccumLDer (Proxy @(PrimalOf target))
                     k (ftkAst acc0) bftk eftk f df rf acc02 es2
  -- This prevents multiple ifH expansions in ADVal.
  AstCond b a1 a2 ->
    let c = interpretAstBool env b
    in tcond (ftkToSTK $ ftkAst a1) c
             (interpretAstPrimal env a1) (interpretAstPrimal env a2)
  _ -> tprimalPart (interpretAst env v1)

interpretAstDual
  :: forall target y. ADReady target
  => AstEnv target -> AstTensor AstMethodLet DualSpan y
  -> DualOf target y
{-# INLINE interpretAstDual #-}
interpretAstDual !env v1 =
  tdualPart (ftkToSTK $ ftkAst v1) (interpretAst env v1)

-- A more precise type signature would result in @PrimalOf target@
-- whenever @s@ is @PrimalSpan@, but this would complicate things,
-- e.g., we'd need an extra type family
--
-- type family SpanTarget s target :: Target where
--   SpanTarget PrimalSpan target = PrimalOf target
--   SpanTarget DualSpan target = DualOf target
--   SpanTarget FullSpan target = target
--
-- to be used in AstEnv and the codomain of interpretAst and a lot of other
-- code would need to be changed. So instead we promote results to @target@
-- similarly as in AstEnv and simiarly as we omit @PrimalOf@ in the signatures
-- of most "Ops" methods.
--
-- | Interpret a term in an environment.
--
-- Note that for 'PrimalSpan' term, the results of this function
-- land in @target y@ and not in @PrimalOf target y@.
-- To make it sound nevertheless, we maintain an invariant that a value
-- of interpretation of a term with 'PrimalSpan' has zero dual part
-- and of a term with 'DualSpan' has zero primal part.
-- The invariants holds by the properties of instances of @Ops@
-- (see especially the ADVal instance, which zeroes dual part of many ops)
-- and structural induction on Ast, inspecting spans of constructors.
-- This promotion from @PrimalOf target y@ to @target y@ coincides
-- with how most operations that in Ast have 'PrimalSpan',
-- don't have 'PrimalOf' (but have full target instead)
-- in their method signatures in @Ops@, for user convenience.
-- See, e.g., 'AstConcreteS' vs 'tsconcrete' and 'AstFloorS' vs 'tsfloor'.
interpretAst
  :: forall target s y. (ADReady target, AstSpan s)
  => AstEnv target -> AstTensor AstMethodLet s y
  -> target y
interpretAst !env = \case
  AstPair t1 t2 -> tpair (interpretAst env t1) (interpretAst env t2)
  AstProject1 t -> tproject1 (interpretAst env t)
  AstProject2 t -> tproject2 (interpretAst env t)
  AstFromVector snat stk l ->
    let l2 = V.map (interpretAst env) l
    in tfromVector snat stk l2
  AstSum snat stk v -> tsum snat stk $ interpretAst env v
  AstReplicate snat stk v ->
    treplicate snat stk (interpretAst env v)
  AstMapAccumRDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in tmapAccumRDer (Proxy @target) k (ftkAst acc0) bftk eftk f df rf acc02 es2
  AstMapAccumLDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in tmapAccumLDer (Proxy @target) k (ftkAst acc0) bftk eftk f df rf acc02 es2
  AstApply t ll ->
    let t2 = interpretAstHFun env t
        ll2 = interpretAst env ll
    in tApply t2 ll2
  AstVar var ->
    let var2 :: AstVarName FullSpan y
        var2 = coerce var  -- only FullSpan variables permitted in env
    in case DMap.lookup var2 env of
      Just t ->
#ifdef WITH_EXPENSIVE_ASSERTIONS
        -- We can't assert anything about bounds, because values can be
        -- symbolic and so not directly comparable to bounds.
        assert (tftk (ftkToSTK $ varNameToFTK var) t == varNameToFTK var
                `blame` ( tftk (ftkToSTK $ varNameToFTK var) t
                        , varNameToFTK var, var, t ))
#endif
        t
      _ -> error $ "interpretAst: unknown AstVar " ++ show var
                   -- ++ " in environment " ++ showsPrecAstEnv 0 env ""
  AstCond b a1 a2 ->
    let c = interpretAstBool env b
    in tcond (ftkToSTK (ftkAst a1)) c
             (interpretAst env a1) (interpretAst env a2)
  AstBuild1 snat stk (var, v) ->
    let f i = interpretAst (extendEnvI var i env) v
    in tbuild1 snat stk f

  -- We assume there are no nested lets with the same variable.
  --
  -- Note that without the second sameAstSpan check, AstLet with both PrimalSpan
  -- would get translated to a composition of ttletPrimal and tfromPrimal,
  -- which doesn't make a difference in a translation from PrimalSpan
  -- terms to PrimalSpan terms, but does in a translation from PrimalSpan
  -- terms to FullSpan terms, causing a loss of a dual part.
  --
  -- However, right now this whole code fragment is disabled, because
  -- it increases the allocation in testsuites by ~3% and slows down the VTO1
  -- benchmark 5 times. To be re-evaluated when rewriting is changed
  -- and also more examples are available.
  AstLet {-@_ @_ @s1-} var u v -> {- case ( sameAstSpan @s1 @PrimalSpan
                                          , sameAstSpan @s @FullSpan ) of
    (Just Refl, Just Refl) ->
      let t = interpretAstPrimal env u
          stk = ftkToSTK (ftkAst u)
          env2 wPrimal = extendEnv var (tfromPrimal stk wPrimal) env
      in ttletPrimal t (\wPrimal -> interpretAst (env2 wPrimal) v)
        -- @ttletPrimal@ can be more frugal in some targets, though we pay
        -- for it with @ftkAst@
    _ -> -}
      let t = interpretAst env u
          env2 w = extendEnv var w env
      in ttlet t (\w -> interpretAst (env2 w) v)

  AstPrimalPart a ->
    tfromPrimal (ftkToSTK (ftkAst a)) (tprimalPart $ interpretAstFull env a)
  AstDualPart a ->
    tfromDual (tdualPart (ftkToSTK (ftkAst a)) $ interpretAstFull env a)
  AstFromPrimal a ->
    -- By the invariant, interpretation of @a@ has zero dual part,
    -- so we don't have to do the following to remove the dual part,
    -- but we still do, because there's almost no rewriting of delta
    -- expressions, so even though they are semantically zero, they'd build
    -- up considerably if not wiped out regularly. By constrast, operations
    -- on AstConstant are rewritten eagerly to AstConstant, so for AstFromDual
    -- we really don't need to do anything.
    tfromPrimal (ftkToSTK (ftkAst a)) (interpretAstPrimal env a)
  AstFromDual a -> interpretAst env a
    -- By the invariant, interpretation of @a@ has zero primal part,
    -- so we don't have to do the following to remove the primal part:
    --   tfromDual (interpretAstDual env a)

  AstPlusK u v -> interpretAst env u + interpretAst env v
  AstTimesK u v -> interpretAst env u * interpretAst env v
  AstN1K opCode u ->
    let u2 = interpretAst env u
    in interpretAstN1 opCode u2
  AstR1K opCode u ->
    let u2 = interpretAst env u
    in interpretAstR1 opCode u2
  AstR2K opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstR2 opCode u2 v2
  AstI2K opCode u v ->
    let u2 = interpretAst env u
        v2 = interpretAst env v
    in interpretAstI2 opCode u2 v2
  AstConcreteK k ->
    tkconcrete @target k
      -- this is equal to the following
      -- (and similarly for tsconcretet and tsiota below):
      -- tfromPrimal @target STKScalar $ tkconcrete @(PrimalOf target) k
  AstFloorK v ->
    -- By the invariant v has zero dual part, so the following suffices:
    tkfloor $ interpretAst env v
  AstFromIntegralK v ->
    -- By the invariant v has zero dual part, so the following suffices:
    tkfromIntegral $ interpretAst env v
  AstCastK v -> tkcast $ interpretAst env v

  AstPlusS u v -> interpretAst env u + interpretAst env v
  AstTimesS u v -> interpretAst env u * interpretAst env v
  AstN1S opCode u -> interpretAstN1 opCode (interpretAst env u)
  AstR1S opCode u -> interpretAstR1 opCode (interpretAst env u)
  AstR2S opCode u v ->
    interpretAstR2 opCode (interpretAst env u) (interpretAst env v)
  AstI2S opCode u v ->
    interpretAstI2 opCode (interpretAst env u) (interpretAst env v)
  AstConcreteS a -> tsconcrete a
  AstFloorS v ->
    -- By the invariant v has zero dual part, so the following suffices:
    tsfloor $ interpretAst env v
  AstFromIntegralS v ->
    -- By the invariant v has zero dual part, so the following suffices:
    tsfromIntegral $ interpretAst env v
  AstCastS @r1 @r2 v ->
    -- Specializing for the cases covered by rules in GHC.Internal.Float.
    case testEquality (typeRep @r1) (typeRep @Double) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @Float) of
        Just Refl -> tscast @_ @Double @Float $ interpretAst env v
        _ -> tscast @_ @Double $ interpretAst env v
      _ -> case testEquality (typeRep @r1) (typeRep @Float) of
        Just Refl -> case testEquality (typeRep @r2) (typeRep @Double) of
          Just Refl -> tscast @_ @Float @Double $ interpretAst env v
          _ -> tscast @_ @Float $ interpretAst env v
        _ -> tscast $ interpretAst env v

  AstIndexS @sh1 sh2 v ix -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS (ixsToShS ix) $
      withKnownShS sh2 $
      withKnownSTK x $
      let v2 = interpretAst env v
          ix3 = interpretAstPrimal env <$> ix
      in tsindex @target @sh1 v2 ix3
  {- TODO: this breaks specialization:
  AstScatterS shn v (ZS, ix) -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      withKnownSTK x $
      tsoneHot (interpretAst env v) (interpretAstPrimal env <$> ix) -}
  AstScatterS @shm @shn @shp
              shn v (vars, ix) -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS (listsToShS vars) $
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      withKnownSTK x $
      let t1 = interpretAst env v
          f2 :: IxSOf target shm -> IxSOf target shp
          f2 !ix2 = interpretAstPrimal (extendEnvVarsS vars ix2 env) <$> ix
      in tsscatter @_ @shm @shn @shp t1 f2
  AstGatherS shn v (ZS, ix) -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      withKnownSTK x $
      tsindex (interpretAst env v) (interpretAstPrimal env <$> ix)
  AstGatherS @shm @shn @shp
             shn v (vars, ix) -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS (listsToShS vars) $
      withKnownShS shn $
      withKnownShS (ixsToShS ix) $
      withKnownSTK x $
      let t1 = interpretAst env v
          f2 :: IxSOf target shm -> IxSOf target shp
          f2 !ix2 = interpretAstPrimal (extendEnvVarsS vars ix2 env) <$> ix
      in tsgather @_ @shm @shn @shp t1 f2
  AstMinIndexS v ->
    -- By the invariant v has zero dual part, so the following suffices:
    tsminIndex $ interpretAst env v
  AstMaxIndexS v ->
    -- By the invariant v has zero dual part, so the following suffices:
    tsmaxIndex $ interpretAst env v
  AstIotaS SNat -> tsiota
  AstAppendS a b -> case ftkToSTK (ftkAst a) of
    STKS _ x ->
      withKnownSTK x $
      let t1 = interpretAst env a
          t2 = interpretAst env b
      in tsappend t1 t2
  AstSliceS i n k v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tsslice i n k $ interpretAst env v
  AstReverseS v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tsreverse (interpretAst env v)
  AstTransposeS perm v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tstranspose perm $ interpretAst env v
  AstReshapeS sh2 v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownSTK x $
      tsreshape sh2 (interpretAst env v)
  AstZipS v -> szip $ interpretAst env v
  AstUnzipS v -> sunzip $ interpretAst env v
  AstNestS sh1 sh2 v -> case ftkToSTK (ftkAst v) of
    STKS _ x ->
      withKnownShS sh2 $
      withKnownSTK x $
      snest sh1 $ interpretAst env v
  AstUnNestS v -> case ftkToSTK (ftkAst v) of
    STKS sh1 (STKS sh2 x) ->
      withKnownShS sh1 $
      withKnownShS sh2 $
      withKnownSTK x $
      sunNest $ interpretAst env v

  AstFromS stkz v ->
    withKnownSTK (ftkToSTK (ftkAst v)) $
    tfromS stkz (interpretAst env v)
  AstSFromK t -> sfromK $ interpretAst env t
  AstSFromR sh v -> case ftkToSTK (ftkAst v) of
    STKR _ x ->
      withKnownShS sh $
      withKnownSTK x $
      sfromR $ interpretAst env v
  AstSFromX sh v -> case ftkToSTK (ftkAst v) of
    STKX _ x ->
      withKnownShS sh $
      withKnownSTK x $
      sfromX $ interpretAst env v

  AstSum0S v -> case ftkToSTK (ftkAst v) of
    STKS sh x ->
      withKnownShS sh $
      withKnownSTK x $
      tssum0 (interpretAst env v)
  AstDot0S u v -> case ftkAst u of
    FTKS sh _ ->
      withKnownShS sh $
      tsdot0 (interpretAst env u) (interpretAst env v)
  AstDot1InS @sh @n sh SNat u v ->
    withKnownShS sh $
    tsdot1In @_ @sh (SNat @n) (interpretAst env u) (interpretAst env v)
  AstMatmul2S SNat SNat SNat u v ->
    tsmatmul2 (interpretAst env u) (interpretAst env v)

interpretAstHFun
  :: forall target x y s s2. (AstSpan s2, BaseTensor target)
  => AstEnv target -> AstHFun s s2 x y
  -> HFunOf target x y
{-# INLINE interpretAstHFun #-}
interpretAstHFun _env (AstLambda var l) =
  tlambda @target (varNameToFTK var)
  $ HFun $ \ws -> interpretAst (extendEnv var ws emptyEnv) l
      -- Interpretation in empty environment makes sense here, because
      -- there are no free variables except for the one declared.

interpretAstHFunPrimal
  :: forall target x y. ADReady target
  => AstEnv target -> AstHFun PrimalSpan PrimalSpan x y
  -> HFunOf (PrimalOf target) x y
{-# INLINE interpretAstHFunPrimal #-}
interpretAstHFunPrimal _env (AstLambda var l) =
  tlambda @(PrimalOf target) (varNameToFTK var)
  $ HFun $ \ws -> interpretAst (extendEnv var ws emptyEnv) l
      -- This is probably optimized as much as possible, because
      -- thanks to the invariant, we get zero dual part from this
      -- PrimalSpan term and so interpretAstPrimal and tfromPrimal
      -- is not needed (and would not be possible, because we lack
      -- FullShapeTK y). From the other end, due to (PrimalOf target),
      -- there won't be any dual part coming from an argument.

interpretAstBool :: ADReady target
                 => AstEnv target -> AstBool AstMethodLet
                 -> BoolOf target
interpretAstBool !env = \case
  AstBoolConst a -> if a then true else false
  AstBoolNot arg -> notB $ interpretAstBool env arg
  AstBoolAnd arg1 arg2 ->
    let b1 = interpretAstBool env arg1
        b2 = interpretAstBool env arg2
    in b1 &&* b2
  AstLeqK arg1 arg2 ->
    let r1 = interpretAstPrimal env arg1
        r2 = interpretAstPrimal env arg2
    in r1 <=. r2
  AstLeqS arg1 arg2 ->
    let r1 = interpretAstPrimal env arg1
        r2 = interpretAstPrimal env arg2
    in r1 <=. r2


-- * Interpretation of arithmetic, boolean and relation operations

interpretAstN1 :: Num a
               => OpCodeNum1 -> a -> a
{-# INLINE interpretAstN1 #-}
interpretAstN1 NegateOp u = negate u
interpretAstN1 AbsOp u = abs u
interpretAstN1 SignumOp u = signum u

interpretAstR1 :: Floating a
               => OpCode1 -> a -> a
{-# INLINE interpretAstR1 #-}
interpretAstR1 RecipOp u = recip u
interpretAstR1 ExpOp u = exp u
interpretAstR1 LogOp u = log u
interpretAstR1 SqrtOp u = sqrt u
interpretAstR1 SinOp u = sin u
interpretAstR1 CosOp u = cos u
interpretAstR1 TanOp u = tan u
interpretAstR1 AsinOp u = asin u
interpretAstR1 AcosOp u = acos u
interpretAstR1 AtanOp u = atan u
interpretAstR1 SinhOp u = sinh u
interpretAstR1 CoshOp u = cosh u
interpretAstR1 TanhOp u = tanh u
interpretAstR1 AsinhOp u = asinh u
interpretAstR1 AcoshOp u = acosh u
interpretAstR1 AtanhOp u = atanh u

interpretAstR2 :: RealFloatH a
               => OpCode2 -> a -> a -> a
{-# INLINE interpretAstR2 #-}
interpretAstR2 DivideOp u v = u / v
interpretAstR2 PowerOp u v = u ** v
interpretAstR2 LogBaseOp u v = logBase u v
interpretAstR2 Atan2Op u v = atan2H u v

interpretAstI2 :: IntegralH a
               => OpCodeIntegral2 -> a -> a -> a
{-# INLINE interpretAstI2 #-}
interpretAstI2 QuotOp u v = quotH u v
interpretAstI2 RemOp u v = remH u v
