{-# LANGUAGE AllowAmbiguousTypes, CPP #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Interpretation of AST terms in an arbitrary tensor operations
-- class instance. With the exception of the the interpretation
-- of the sharing mechanisms and any other performance tweaks,
-- the interpretation is the unique homorphism determined by the instance.
-- The sharing mechanisms are translated so as to preserve sharing in case
-- the instance is a term algebra as well.
module HordeAd.Core.AstInterpret
  ( interpretAstFull, interpretAstPrimal, interpretAstDual, interpretAstPlain
  ) where

import Prelude

import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V

import Data.Array.Nested.Lemmas
import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstTools
import HordeAd.Core.Conversion
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

#ifdef WITH_EXPENSIVE_ASSERTIONS
import Control.Exception.Assert.Sugar
#endif

interpretAstFull
  :: forall target y. ADReady target
  => AstEnv target -> AstTensor AstMethodLet FullSpan y
  -> target y
{-# INLINE interpretAstFull #-}
interpretAstFull = interpretAst

interpretAstPrimal
  :: forall target y. ADReady target
  => AstEnv target -> AstTensor AstMethodLet PrimalSpan y
  -> PrimalOf target y
{-# INLINE interpretAstPrimal #-}
interpretAstPrimal = interpretAst

interpretAstDual
  :: forall target y. ADReady target
  => AstEnv target -> AstTensor AstMethodLet DualSpan y
  -> DualOf target y
{-# INLINE interpretAstDual #-}
interpretAstDual env a = tdualPart (ftkToSTK (ftkAst a)) $ interpretAst env a

interpretAstPlain
  :: forall target y. ADReady target
  => AstEnv target -> AstTensor AstMethodLet PlainSpan y
  -> PlainOf target y
{-# INLINE interpretAstPlain #-}
interpretAstPlain = interpretAst

-- | Interpret a term in an environment.
interpretAst
  :: forall target s y. (ADReady target, KnownSpan s)
  => AstEnv target -> AstTensor AstMethodLet s y
  -> SpanTargetFam target s y
{-# INLINEABLE interpretAst #-}
interpretAst !env | Refl <- lemPlainOfSpan (Proxy @target) (knownSpan @s)
                  , Dict0 <- dictSpanFam (Proxy @target) (knownSpan @s) = \case
  AstPair t1 t2 -> tpair (interpretAst env t1) (interpretAst env t2)
  AstProject1 t -> tproject1 (interpretAst env t)
  AstProject2 t -> tproject2 (interpretAst env t)
  AstFromVector snat stk l ->
    let l2 = V.map (interpretAst env) l
    in tfromVector snat stk l2
  AstSum snat stk v -> tsum snat stk $ interpretAst env v
  AstReplicate snat stk v ->
    treplicate snat stk (interpretAst env v)
  AstMapAccumLDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFun env f0
        df = interpretAstHFun env df0
        rf = interpretAstHFun env rf0
        acc02 = interpretAst env acc0
        es2 = interpretAst env es
    in tmapAccumLDer (Proxy @(SpanTargetFam target s))
                     k (ftkAst acc0) bftk eftk f df rf acc02 es2
  AstApply f t ->
    let f2 = interpretAstHFun env f
        t2 = interpretAst env t
    in tapply f2 t2
  AstVar var ->
    case DMap.lookup var env of
      Just (SpanTarget t) ->
#ifdef WITH_EXPENSIVE_ASSERTIONS
        withKnownSTK (ftkToSTK $ varNameToFTK var) $
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
    let c = interpretAst env b
    in tcond (ftkToSTK (ftkAst a1)) c
             (interpretAst env a1) (interpretAst env a2)
  -- TODO: recognize nested builds and, for Concrete, call tbuild instead;
  -- also recognize map and zipWith in nested builds and call these
  AstBuild1 snat stk (var, v) ->
    let f i = interpretAst (extendEnvI var i env) v
    in tbuild1 snat stk f

  -- We assume there are no nested lets with the same variable.
  AstLet @_ @_ @_ @s2 var u v ->
    let (toFull, fromFull) =
          toFromFullSpan (ftkToSTK (ftkAst v)) (knownSpan @s2)
        t = withKnownSpan (varNameToSpan var) $ interpretAst env u
        env2 w = extendEnv var w env
    in case varNameToSpan var of
         SFullSpan ->
           fromFull $ ttlet t (\w -> toFull $ interpretAst (env2 w) v)
         SPrimalStepSpan SFullSpan ->
           fromFull $ ttletPrimal t (\w -> toFull $ interpretAst (env2 w) v)
         SPrimalStepSpan _ ->
           error "interpretAst: can't store a nested primal value"
             -- actually, we could, by substituting into v0, etc.
         SDualSpan ->
           fromFull $ ttlet t (\w -> toFull $ interpretAst (env2 w) v)
             -- due to the dual hack
         SPlainSpan | SPlainSpan <- knownSpan @s2 ->  -- a speedup
           ttlet t (\w -> interpretAst (env2 w) v)
         SPlainSpan ->
           fromFull $ ttletPlain t (\w -> toFull $ interpretAst (env2 w) v)
  AstPrimalPart @_ @s2 a -> case knownSpan @s2 of
    SFullSpan -> tprimalPart $ interpretAst env a
    SPrimalStepSpan SFullSpan -> tprimalPart $ interpretAst env a
    SPrimalStepSpan _ ->
      error "interpretAst: can't convert a nested primal value"  -- (... easily)
    SDualSpan -> tdefTarget (ftkAst a)  -- primal zero
    SPlainSpan -> tprimalPart $ interpretAst env a
  AstDualPart a ->
    -- We zero the primal part, but keep it a dual number, not its second
    -- component, that is a Delta expression (in non-symbolic instances).
    tfromDual $ tdualPart (ftkToSTK (ftkAst a)) $ interpretAst env a
  AstPlainPart @_ @s2 a -> case knownSpan @s2 of
    SFullSpan -> tplainPart $ interpretAst env a
    SPrimalStepSpan SFullSpan -> tplainPart $ interpretAst env a
    SPrimalStepSpan _ ->
      error "interpretAst: can't convert a nested primal value"  -- (... easily)
    SDualSpan -> tdefTarget (ftkAst a)  -- plain zero
    SPlainSpan -> interpretAst env a
  AstFromPrimal a -> tfromPrimal (ftkToSTK (ftkAst a)) $ interpretAst env a
  AstFromDual a ->
    -- Not @tfromDual $ interpretAst env a@, because dual parts are represented
    -- as dual numbers with zero primal parts, so nothing needs to be done here,
    -- because the part is already zeroed by inductive assumption, so this
    -- also works as a representation of a dual number with zero primal part,
    -- which is the semantics of `AstFromDual`.
    interpretAst env a
  AstFromPlain a -> tfromPlain (ftkToSTK (ftkAst a)) $ interpretAst env a

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
  AstConcreteK k -> tkconcrete k
  AstFloorK v -> tkfloor $ interpretAst env v
  AstFromIntegralK v -> tkfromIntegral $ interpretAst env v
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
  AstFloorS v -> tsfloor $ interpretAst env v
  AstFromIntegralS v -> tsfromIntegral $ interpretAst env v
  AstCastS v -> tscast $ interpretAst env v

  AstIndexS @shm shn v ix ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let v2 = interpretAst env v
        ix3 = interpretAst env <$> ix
    in tsindex @_ @shm v2 ix3
  -- TODO: once specialization inspect-testing is back online,
  -- recover and also handle similarly tsupdate, both implemented
  -- as a gather and as a scatter
  -- TODO: this breaks specialization:
  AstScatterS shn v (ZS, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    tsoneHot (interpretAst env v) (interpretAst env <$> ix)
  AstScatterS @shm @shn @shp
              shn v (var ::$ ZS, ix) | SNat :$$ _ <- knownShS @shm ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAst env v
        f2 :: IntOf target -> IxSOf target shp
        f2 !i2 = interpretAst (extendEnvI var i2 env) <$> ix
    in tsscatter1 @_ @_ @shn @shp t1 f2
  AstScatterS @shm @shn @shp
              shn v (vars, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAst env v
        f2 :: IxSOf target shm -> IxSOf target shp
        f2 !ix2 = interpretAst (extendEnvVarsS vars ix2 env) <$> ix
    in tsscatter @_ @shm @shn @shp t1 f2
  AstGatherS shn v (ZS, ix) -> interpretAst env (AstIndexS shn v ix)
  AstGatherS @shm @shn @shp
             shn v (var ::$ ZS, ix) | SNat :$$ _ <- knownShS @shm ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAst env v
        f2 :: IntOf target -> IxSOf target shp
        f2 !i2 = interpretAst (extendEnvI var i2 env) <$> ix
    in tsgather1 @_ @_ @shn @shp t1 f2
  AstGatherS @shm @shn @shp
             shn v (vars, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAst env v
        f2 :: IxSOf target shm -> IxSOf target shp
        f2 !ix2 = interpretAst (extendEnvVarsS vars ix2 env) <$> ix
    in tsgather @_ @shm @shn @shp t1 f2
  AstMinIndexS v -> tsminIndex $ interpretAst env v
  AstMaxIndexS v -> tsmaxIndex $ interpretAst env v
  AstIotaS SNat -> tsiota
  AstAppendS a b ->
    withKnownSTK (stkAstX a) $
    let t1 = interpretAst env a
        t2 = interpretAst env b
    in tsappend t1 t2
  AstSliceS i n k v ->
    withKnownSTK (stkAstX v) $
    tsslice i n k $ interpretAst env v
  AstReverseS v ->
    withKnownSTK (stkAstX v) $
    tsreverse (interpretAst env v)
  AstTransposeS perm v ->
    withKnownSTK (stkAstX v) $
    tstranspose perm $ interpretAst env v
  AstReshapeS sh2 v ->
    withKnownSTK (stkAstX v) $
    tsreshape sh2 (interpretAst env v)

  AstConvert c a ->
    tconvert c (ftkToSTK (ftkAst a)) (interpretAst env a)

  AstIndex0S v ix ->
    let v2 = interpretAst env v
        ix3 = interpretAst env <$> ix
    in tsindex0 v2 ix3
  AstSum0S v -> case ftkAst v of
    FTKS sh _ ->
      withKnownShS sh $
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

  AstBoolNot arg ->
    tfromPlain STKScalar $ notB $ interpretAst env arg
  AstBoolNotA arg | FTKS sh _ <- ftkAst arg ->
    withKnownShS sh $
    tfromPlain (ftkToSTK $ ftkAst arg)
    $ tsmap0N notB $ interpretAst env arg
  AstBoolAnd arg1 arg2 ->
    let b1 = interpretAst env arg1
        b2 = interpretAst env arg2
    in tfromPlain STKScalar $ b1 &&* b2
  AstBoolAndA arg1 arg2 | FTKS sh _ <- ftkAst arg1 ->
    withKnownShS sh $
    let b1 = interpretAst env arg1
        b2 = interpretAst env arg2
    in tfromPlain (ftkToSTK $ ftkAst arg1)
       $ tszipWith0N (&&*) b1 b2
  AstLeqK arg1 arg2 ->
    let r1 = interpretAst env arg1
        r2 = interpretAst env arg2
    in tfromPlain STKScalar $ r1 <=. r2
  AstLeqS arg1 arg2 ->
    let r1 = interpretAst env arg1
        r2 = interpretAst env arg2
    in tfromPlain STKScalar $ r1 <=. r2
  AstLeqA @shb @sh shb sh arg1 arg2 | Refl <- lemAppNil @shb ->
    withKnownShS shb $
    withKnownShS sh $
    let r1 = interpretAst env arg1
        r2 = interpretAst env arg2
    in tfromPlain (STKS shb STKScalar)
       $ sunNest
       $ szipWithNested
           (\a1 a2 ->
             let c = convCmp ConvXS
                             (convCmp (Conv0X (STKS ZSS STKScalar))
                                      (convCmp ConvXS (Conv0X STKScalar)))
             in tconvert c STKScalar $ sunNest a1 <=. sunNest a2)
           (snest @_ @_ @sh shb r1) (snest shb r2)

interpretAstHFun
  :: forall target x y s. (KnownSpan s, BaseTensor (SpanTargetFam target s))
  => AstEnv target -> AstHFun s x y
  -> HFunOf (SpanTargetFam target s) x y
{-# INLINE interpretAstHFun #-}
interpretAstHFun _env (AstLambda var t) =
  tlambda @(SpanTargetFam target s) (varNameToFTK var)
  $ HFun $ \ (ws :: f x) ->
              toFullSpan @f (ftkToSTK (ftkAst t)) (knownSpan @s)
              $ interpretAst @f
                  (extendEnv var (fromFullSpan (knownSpan @s) ws) emptyEnv) t
      -- Interpretation in empty environment makes sense here, because
      -- there are no free variables except for the one declared.

-- This version accepts nested arrays, because they are needed here.
szipWithNested :: ( KnownShS sh, KnownSTK x, KnownSTK x1, KnownSTK x2
                  , BaseTensor target )
               => (target (TKS2 '[] x1) -> target (TKS2 '[] x2)
                   -> target (TKS2 '[] x))
               -> target (TKS2 sh x1) -> target (TKS2 sh x2)
               -> target (TKS2 sh x)
{-# INLINE szipWithNested #-}
szipWithNested @sh f u v | Refl <- lemAppNil @sh =
  tsbuild @_ @sh (\ix -> f (tsindex u ix) (tsindex v ix))


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
