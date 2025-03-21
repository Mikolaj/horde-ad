{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
-- | Interpretation of AST terms in an aribtrary @RankedTensor@ & Co instance.
-- With the exception of the the interpretation of the sharing mechanisms,
-- the interpretation is the unique homorphism determined by the instance.
-- The sharing mechanisms are translated so as to preserve sharing in case
-- the instance is a term algebra as well.
module HordeAd.Core.AstInterpret
  ( interpretAstFull, interpretAstPrimal, interpretAstDual
    -- * Exported only to specialize elsewhere
  , interpretAst, interpretAstBool
  ) where

import Prelude

import Data.Coerce (coerce)
import Data.Dependent.EnumMap.Strict.Unsafe qualified as DMap.Unsafe
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Type.Reflection (typeRep)

import Data.Array.Nested.Internal.Shape

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
  AstMapAccumRDer k bftk eftk f0 df0 rf0 acc0 es ->
    -- This avoids computing the complex dual parts for mapAccum in ADVal.
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
  AstCond b a1 a2 ->
    -- This avoids multiple ifH expansions in ADVal.
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
-- We maintain an invariant that a value of interpretation
-- of a term with PrimalSpan has zero dual part
-- and of a term with DualSpan has zero primal part.
-- The invariants holds by the properties of instances of Ops
-- (see especially the ADVal instance, which zeroes dual part of many ops)
-- and structural induction on Ast, inspecting spans of constructors.
-- This promotion to @target@ coincides with how most operations that in Ast
-- have PrimalSpan, don't have PrimalOf (but have full target instead)
-- in their method signatures in Ops, for user comfort. E.g., AstConcreteS
-- vs tsconcrete and AstFloorS vs tsfloor.
--
-- The invariant only holds for valuations of PrimalSpan variables
-- that have zero primal part, etc., which holds for variables coming
-- from AstLet, but not for variables inside AstHFun. We specifically
-- in interpretAstHFun don't zero primal parts of arguments assigned
-- to PrimalSpan variables in order to promote PrimalSpan -> PrimalSpan
-- functions from AST to full dual number functions in target
-- so that derivatives can be cheaply used as dual number functions.
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
  -- The following can't be, in general, so partially evaluated, because v
  -- may contain variables that the evironment sends to terms,
  -- not to concrete numbers (and so Primal a is not equal to a).
  -- However, this matters only for POPL AD, not JAX AD and also it matters
  -- only with no vectorization of, at least, constant (primal-only) terms.
  -- AstBuild1 k (var, AstFromPrimal v) ->
  --   tconcrete
  --   $ OR.ravel . ORB.fromVector [k] . V.generate k
  --   $ interpretLambdaI interpretAstPrimal env (var, v)
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
          -- The function or function-like object resulting from this
          -- interpretation is not affected by the span of the term inside t,
          -- but only by the AST constructors used (it matters for
          -- the constructors that can be made well typed with more
          -- than one span). Therefore, the function can be made compatible
          -- with the ll argument, with which it agrees in every other way
          -- (specifically, the tensor kind), from type-checking.
          -- Moreover, even if the variable in t was PrimalSpan, the dual part
          -- won't be removed from the value assigned to it, unless
          -- a constructor that can only accept PrimalSpan argument
          -- is applied to the variable.
          -- This is the weirdness of the AstApply constructor semantics
          -- and it's essential for the implicit promotion of derivaties
          -- to general dual number functions.
        ll2 = interpretAst env ll
          -- See above. The interpretation makes t2 and ll2 agree in types
          -- so that t2 can finally be applied to ll2. If the spans
          -- agreed earlier, AstApply would likely be simplified before
          -- getting interpreted.
    in tApply t2 ll2
  AstVar var ->
    let var2 :: AstVarName FullSpan y
        var2 = coerce var  -- only FullSpan variables permitted in env
    -- The old assertion test below checks the same thing this lookup doesn't
    -- and more.
    in case DMap.Unsafe.lookupUnsafe var2 env of
      Just t ->
#ifdef WITH_EXPENSIVE_ASSERTIONS
        assert (tftk (ftkToSTK $ varNameToFTK var) t == varNameToFTK var
                `blame` ( tftk (ftkToSTK $ varNameToFTK var) t
                        , varNameToFTK var, var, t ))
#endif
        t
      _ -> error $ "interpretAst: unknown AstVar " ++ show var
                   -- ++ " in environment " ++ showsPrecAstEnv 0 env ""
  AstCond b a1 a2 ->
    let c = interpretAstBool env b
    in tcond (ftkToSTK (ftkAst a1))
             c (interpretAst env a1) (interpretAst env a2)
  AstBuild1 snat stk (var, v) ->
    let f i = interpretAst (extendEnvI var i env) v
    in tbuild1 snat stk f

  -- We assume there are no nested lets with the same variable.
  AstLet var u v ->
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
      -- if index is out of bounds, the operations returns with an undefined
      -- value of the correct rank and shape; this is needed, because
      -- vectorization can produce out of bound indexing from code where
      -- the indexing is guarded by conditionals
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
    -- the operation accepts out of bounds indexes,
    -- for the same reason ordinary indexing does, see above
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

  AstFromS stkz v -> tfromS (ftkToSTK (ftkAst v)) stkz (interpretAst env v)
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
    tsdot1In @_ @sh @n (interpretAst env u) (interpretAst env v)
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
      -- there are no free variables outside of those listed.
      -- The spans don't affect the interpretation, though the invariant
      -- still holds for term l and so the dual number into which it is
      -- interpreted has zero dual part if the span was PrimalSpan.

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
  AstBoolNot arg -> notB $ interpretAstBool env arg
  AstB2 opCodeBool arg1 arg2 ->
    let b1 = interpretAstBool env arg1
        b2 = interpretAstBool env arg2
    in interpretAstB2 opCodeBool b1 b2
  AstBoolConst a -> if a then true else false
  AstRelK opCodeRel arg1 arg2 ->
    let r1 = interpretAstPrimal env arg1
        r2 = interpretAstPrimal env arg2
    in interpretAstRelOp opCodeRel r1 r2
  AstRelS opCodeRel arg1 arg2 ->
    let r1 = interpretAstPrimal env arg1
        r2 = interpretAstPrimal env arg2
    in interpretAstRelOp opCodeRel r1 r2


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

interpretAstB2 :: Boolean b
               => OpCodeBool -> b -> b -> b
{-# INLINE interpretAstB2 #-}
interpretAstB2 AndOp u v = u &&* v
interpretAstB2 OrOp u v = u ||* v

interpretAstRelOp :: (EqH f y, OrdH f y)
                  => OpCodeRel -> f y -> f y -> BoolOf f
{-# INLINE interpretAstRelOp #-}
interpretAstRelOp EqOp u v = u ==. v
interpretAstRelOp NeqOp u v = u /=. v
interpretAstRelOp LeqOp u v = u <=. v
interpretAstRelOp GeqOp u v = u >=. v
interpretAstRelOp LsOp u v = u <. v
interpretAstRelOp GtOp u v = u >. v
