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
  ( interpretAstFull, interpretAstPrimal, interpretAstDual, interpretAst
  ) where

import Prelude

import Data.Coerce (coerce)
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
  AstPair t1 t2 -> tpair (interpretAstPrimal env t1) (interpretAstPrimal env t2)
  AstProject1 t -> tproject1 (interpretAstPrimal env t)
  AstProject2 t -> tproject2 (interpretAstPrimal env t)
  AstFromVector snat stk l ->
    let l2 = V.map (interpretAstPrimal env) l
    in tfromVector snat stk l2
  AstSum snat stk v -> tsum snat stk $ interpretAstPrimal env v
  AstReplicate snat stk v ->
    treplicate snat stk (interpretAstPrimal env v)
  -- This prevents computing the complex dual parts for mapAccum in ADVal.
  AstMapAccumLDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFunPrimal env f0
        df = interpretAstHFunPrimal env df0
        rf = interpretAstHFunPrimal env rf0
        acc02 = interpretAstPrimal env acc0
        es2 = interpretAstPrimal env es
    in tmapAccumLDer (Proxy @(PrimalOf target))
                     k (ftkAst acc0) bftk eftk f df rf acc02 es2
  AstApply{} -> tprimalPart (interpretAst env v1)  -- TODO
  AstVar var ->
    let var2 :: AstVarName FullSpan y
        var2 = coerce var  -- only FullSpan variables permitted in env
    in case DMap.lookup var2 env of
      Just t ->
#ifdef WITH_EXPENSIVE_ASSERTIONS
        withKnownSTK (ftkToSTK $ varNameToFTK var) $
        -- We can't assert anything about bounds, because values can be
        -- symbolic and so not directly comparable to bounds.
        assert (tftk (ftkToSTK $ varNameToFTK var) t == varNameToFTK var
                `blame` ( tftk (ftkToSTK $ varNameToFTK var) t
                        , varNameToFTK var, var, t ))
#endif
        (tprimalPart t)
      _ -> error $ "interpretAst: unknown AstVar " ++ show var
                   -- ++ " in environment " ++ showsPrecAstEnv 0 env ""
  -- This prevents multiple ifH expansions in ADVal.
  AstCond b a1 a2 ->
    let c = interpretAstPlain env b
    in tcond (ftkToSTK $ ftkAst a1) c
             (interpretAstPrimal env a1) (interpretAstPrimal env a2)
  AstBuild1 snat stk (var, v) ->
    let f i = interpretAstPrimal (extendEnvI var i env) v
    in tbuild1 snat stk f

  AstLet var u v ->
    let t = interpretAst env u
        env2 w = extendEnv var w env
    in tprimalPart $ ttlet t (\w -> tfromPrimal (ftkToSTK $ ftkAst v)
                                    $ interpretAstPrimal (env2 w) v)
         -- TODO

  AstPrimalPart a -> tprimalPart $ interpretAst env a
  AstFromPrimal{} -> tprimalPart (interpretAst env v1)  -- TODO
  AstFromPlain a ->
    tfromPlain (ftkToSTK (ftkAst a)) (interpretAstPlain env a)

  AstPlusK u v -> interpretAstPrimal env u + interpretAstPrimal env v
  AstTimesK u v -> interpretAstPrimal env u * interpretAstPrimal env v
  AstN1K opCode u ->
    let u2 = interpretAstPrimal env u
    in interpretAstN1 opCode u2
  AstR1K opCode u ->
    let u2 = interpretAstPrimal env u
    in interpretAstR1 opCode u2
  AstR2K opCode u v ->
    let u2 = interpretAstPrimal env u
        v2 = interpretAstPrimal env v
    in interpretAstR2 opCode u2 v2
  AstI2K opCode u v ->
    let u2 = interpretAstPrimal env u
        v2 = interpretAstPrimal env v
    in interpretAstI2 opCode u2 v2
  AstCastK v -> tkcast $ interpretAstPrimal env v

  AstPlusS u v -> interpretAstPrimal env u + interpretAstPrimal env v
  AstTimesS u v -> interpretAstPrimal env u * interpretAstPrimal env v
  AstN1S opCode u -> interpretAstN1 opCode (interpretAstPrimal env u)
  AstR1S opCode u -> interpretAstR1 opCode (interpretAstPrimal env u)
  AstR2S opCode u v ->
    interpretAstR2 opCode (interpretAstPrimal env u) (interpretAstPrimal env v)
  AstI2S opCode u v ->
    interpretAstI2 opCode (interpretAstPrimal env u) (interpretAstPrimal env v)
  AstCastS v -> tscast $ interpretAstPrimal env v

  AstIndexS @shm shn v ix ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let v2 = interpretAstPrimal env v
        ix3 = interpretAstPlain env <$> ix
    in tsindex @_ @shm v2 ix3
  AstScatterS shn v (ZS, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    tsoneHot (interpretAstPrimal env v) (interpretAstPlain env <$> ix)
  AstScatterS @shm @shn @shp
              shn v (var ::$ ZS, ix) | SNat :$$ _ <- knownShS @shm ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAstPrimal env v
        f2 :: IntOf target -> IxSOf target shp
        f2 !i2 = interpretAstPlain (extendEnvI var i2 env) <$> ix
    in tsscatter1 @_ @_ @shn @shp t1 f2
  AstScatterS @shm @shn @shp
              shn v (vars, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAstPrimal env v
        f2 :: IxSOf target shm -> IxSOf target shp
        f2 !ix2 = interpretAstPlain (extendEnvVarsS vars ix2 env) <$> ix
    in tsscatter @_ @shm @shn @shp t1 f2
  AstGatherS shn v (ZS, ix) -> interpretAstPrimal env (AstIndexS shn v ix)
  AstGatherS @shm @shn @shp
             shn v (var ::$ ZS, ix) | SNat :$$ _ <- knownShS @shm ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAstPrimal env v
        f2 :: IntOf target -> IxSOf target shp
        f2 !i2 = interpretAstPlain (extendEnvI var i2 env) <$> ix
    in tsgather1 @_ @_ @shn @shp t1 f2
  AstGatherS @shm @shn @shp
             shn v (vars, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAstPrimal env v
        f2 :: IxSOf target shm -> IxSOf target shp
        f2 !ix2 = interpretAstPlain (extendEnvVarsS vars ix2 env) <$> ix
    in tsgather @_ @shm @shn @shp t1 f2
  AstAppendS a b ->
    withKnownSTK (stkAstX a) $
    let t1 = interpretAstPrimal env a
        t2 = interpretAstPrimal env b
    in tsappend t1 t2
  AstSliceS i n k v ->
    withKnownSTK (stkAstX v) $
    tsslice i n k $ interpretAstPrimal env v
  AstReverseS v ->
    withKnownSTK (stkAstX v) $
    tsreverse (interpretAstPrimal env v)
  AstTransposeS perm v ->
    withKnownSTK (stkAstX v) $
    tstranspose perm $ interpretAstPrimal env v
  AstReshapeS sh2 v ->
    withKnownSTK (stkAstX v) $
    tsreshape sh2 (interpretAstPrimal env v)

  AstConvert c a ->
    tconvert c (ftkToSTK (ftkAst a)) (interpretAstPrimal env a)

  AstIndex0S v ix ->
    let v2 = interpretAstPrimal env v
        ix3 = interpretAstPlain env <$> ix
    in tsindex0 v2 ix3
  AstSum0S v -> case ftkAst v of
    FTKS sh _ ->
      withKnownShS sh $
      tssum0 (interpretAstPrimal env v)
  AstDot0S u v -> case ftkAst u of
    FTKS sh _ ->
      withKnownShS sh $
      tsdot0 (interpretAstPrimal env u) (interpretAstPrimal env v)
  AstDot1InS @sh @n sh SNat u v ->
    withKnownShS sh $
    tsdot1In @_ @sh (SNat @n) (interpretAstPrimal env u) (interpretAstPrimal env v)
  AstMatmul2S SNat SNat SNat u v ->
    tsmatmul2 (interpretAstPrimal env u) (interpretAstPrimal env v)

interpretAstPlain
  :: forall target y. ADReady target
  => AstEnv target -> AstTensor AstMethodLet PlainSpan y
  -> PlainOf target y
interpretAstPlain !env v1 = case v1 of
  AstPair t1 t2 -> tpair (interpretAstPlain env t1) (interpretAstPlain env t2)
  AstProject1 t -> tproject1 (interpretAstPlain env t)
  AstProject2 t -> tproject2 (interpretAstPlain env t)
  AstFromVector snat stk l ->
    let l2 = V.map (interpretAstPlain env) l
    in tfromVector snat stk l2
  AstSum snat stk v -> tsum snat stk $ interpretAstPlain env v
  AstReplicate snat stk v ->
    treplicate snat stk (interpretAstPlain env v)
  -- This prevents computing the complex dual parts for mapAccum in ADVal.
  AstMapAccumLDer k bftk eftk f0 df0 rf0 acc0 es ->
    let f = interpretAstHFunPlain env f0
        df = interpretAstHFunPlain env df0
        rf = interpretAstHFunPlain env rf0
        acc02 = interpretAstPlain env acc0
        es2 = interpretAstPlain env es
    in tmapAccumLDer (Proxy @(PlainOf target))
                     k (ftkAst acc0) bftk eftk f df rf acc02 es2
  AstApply{} -> tplainPart (interpretAst env v1)  -- TODO
  AstVar var ->
    let var2 :: AstVarName FullSpan y
        var2 = coerce var  -- only FullSpan variables permitted in env
    in case DMap.lookup var2 env of
      Just t ->
#ifdef WITH_EXPENSIVE_ASSERTIONS
        withKnownSTK (ftkToSTK $ varNameToFTK var) $
        -- We can't assert anything about bounds, because values can be
        -- symbolic and so not directly comparable to bounds.
        assert (tftk (ftkToSTK $ varNameToFTK var) t == varNameToFTK var
                `blame` ( tftk (ftkToSTK $ varNameToFTK var) t
                        , varNameToFTK var, var, t ))
#endif
        (tplainPart t)
      _ -> error $ "interpretAst: unknown AstVar " ++ show var
                   -- ++ " in environment " ++ showsPrecAstEnv 0 env ""
  -- This prevents multiple ifH expansions in ADVal.
  AstCond b a1 a2 ->
    let c = interpretAstPlain env b
    in tcond (ftkToSTK $ ftkAst a1) c
             (interpretAstPlain env a1) (interpretAstPlain env a2)
  AstBuild1 snat stk (var, v) ->
    let f i = interpretAstPlain (extendEnvI var i env) v
    in tbuild1 snat stk f

  AstLet var u v ->
    let t = interpretAst env u
        env2 w = extendEnv var w env
    in tplainPart $ ttlet t (\w -> tfromPlain (ftkToSTK $ ftkAst v)
                                   $ interpretAstPlain (env2 w) v)
         -- TODO

  AstPlainPart a -> tplainPart $ interpretAst env a
  AstFromPrimal{} -> tplainPart (interpretAst env v1)  -- TODO
  AstFromPlain a -> interpretAstPlain env a

  AstPlusK u v -> interpretAstPlain env u + interpretAstPlain env v
  AstTimesK u v -> interpretAstPlain env u * interpretAstPlain env v
  AstN1K opCode u ->
    let u2 = interpretAstPlain env u
    in interpretAstN1 opCode u2
  AstR1K opCode u ->
    let u2 = interpretAstPlain env u
    in interpretAstR1 opCode u2
  AstR2K opCode u v ->
    let u2 = interpretAstPlain env u
        v2 = interpretAstPlain env v
    in interpretAstR2 opCode u2 v2
  AstI2K opCode u v ->
    let u2 = interpretAstPlain env u
        v2 = interpretAstPlain env v
    in interpretAstI2 opCode u2 v2
  AstConcreteK k -> tkconcrete k
  AstFloorK v ->
    tkfloor $ interpretAstPlain env v
  AstFromIntegralK v ->
    tkfromIntegral $ interpretAstPlain env v
  AstCastK v -> tkcast $ interpretAstPlain env v

  AstPlusS u v -> interpretAstPlain env u + interpretAstPlain env v
  AstTimesS u v -> interpretAstPlain env u * interpretAstPlain env v
  AstN1S opCode u -> interpretAstN1 opCode (interpretAstPlain env u)
  AstR1S opCode u -> interpretAstR1 opCode (interpretAstPlain env u)
  AstR2S opCode u v ->
    interpretAstR2 opCode (interpretAstPlain env u) (interpretAstPlain env v)
  AstI2S opCode u v ->
    interpretAstI2 opCode (interpretAstPlain env u) (interpretAstPlain env v)
  AstConcreteS a -> tsconcrete a
  AstFloorS v -> tsfloor $ interpretAstPlain env v
  AstFromIntegralS v -> tsfromIntegral $ interpretAstPlain env v
  AstCastS v -> tscast $ interpretAstPlain env v

  AstIndexS @shm shn v ix ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let v2 = interpretAstPlain env v
        ix3 = interpretAstPlain env <$> ix
    in tsindex @_ @shm v2 ix3
  AstScatterS shn v (ZS, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    tsoneHot (interpretAstPlain env v) (interpretAstPlain env <$> ix)
  AstScatterS @shm @shn @shp
              shn v (var ::$ ZS, ix) | SNat :$$ _ <- knownShS @shm ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAstPlain env v
        f2 :: IntOf target -> IxSOf target shp
        f2 !i2 = interpretAstPlain (extendEnvI var i2 env) <$> ix
    in tsscatter1 @_ @_ @shn @shp t1 f2
  AstScatterS @shm @shn @shp
              shn v (vars, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAstPlain env v
        f2 :: IxSOf target shm -> IxSOf target shp
        f2 !ix2 = interpretAstPlain (extendEnvVarsS vars ix2 env) <$> ix
    in tsscatter @_ @shm @shn @shp t1 f2
  AstGatherS shn v (ZS, ix) -> interpretAstPlain env (AstIndexS shn v ix)
  AstGatherS @shm @shn @shp
             shn v (var ::$ ZS, ix) | SNat :$$ _ <- knownShS @shm ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAstPlain env v
        f2 :: IntOf target -> IxSOf target shp
        f2 !i2 = interpretAstPlain (extendEnvI var i2 env) <$> ix
    in tsgather1 @_ @_ @shn @shp t1 f2
  AstGatherS @shm @shn @shp
             shn v (vars, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAstPlain env v
        f2 :: IxSOf target shm -> IxSOf target shp
        f2 !ix2 = interpretAstPlain (extendEnvVarsS vars ix2 env) <$> ix
    in tsgather @_ @shm @shn @shp t1 f2
  AstMinIndexS v ->
    tsminIndex $ interpretAstPlain env v
  AstMaxIndexS v ->
    tsmaxIndex $ interpretAstPlain env v
  AstIotaS SNat -> tsiota
  AstAppendS a b ->
    withKnownSTK (stkAstX a) $
    let t1 = interpretAstPlain env a
        t2 = interpretAstPlain env b
    in tsappend t1 t2
  AstSliceS i n k v ->
    withKnownSTK (stkAstX v) $
    tsslice i n k $ interpretAstPlain env v
  AstReverseS v ->
    withKnownSTK (stkAstX v) $
    tsreverse (interpretAstPlain env v)
  AstTransposeS perm v ->
    withKnownSTK (stkAstX v) $
    tstranspose perm $ interpretAstPlain env v
  AstReshapeS sh2 v ->
    withKnownSTK (stkAstX v) $
    tsreshape sh2 (interpretAstPlain env v)

  AstConvert c a ->
    tconvert c (ftkToSTK (ftkAst a)) (interpretAstPlain env a)

  AstIndex0S v ix ->
    let v2 = interpretAstPlain env v
        ix3 = interpretAstPlain env <$> ix
    in tsindex0 v2 ix3
  AstSum0S v -> case ftkAst v of
    FTKS sh _ ->
      withKnownShS sh $
      withKnownSTK (stkAstX v) $
      tssum0 (interpretAstPlain env v)
  AstDot0S u v -> case ftkAst u of
    FTKS sh _ ->
      withKnownShS sh $
      tsdot0 (interpretAstPlain env u) (interpretAstPlain env v)
  AstDot1InS @sh @n sh SNat u v ->
    withKnownShS sh $
    tsdot1In @_ @sh (SNat @n) (interpretAstPlain env u) (interpretAstPlain env v)
  AstMatmul2S SNat SNat SNat u v ->
    tsmatmul2 (interpretAstPlain env u) (interpretAstPlain env v)

  AstBoolNot arg ->
    notB $ interpretAstPlain env arg
  AstBoolNotA arg | FTKS sh _ <- ftkAst arg ->
    withKnownShS sh $
    tsmap0N notB $ interpretAstPlain env arg
  AstBoolAnd arg1 arg2 ->
    let b1 = interpretAstPlain env arg1
        b2 = interpretAstPlain env arg2
    in b1 &&* b2
  AstBoolAndA arg1 arg2 | FTKS sh _ <- ftkAst arg1 ->
    withKnownShS sh $
    let b1 = interpretAstPlain env arg1
        b2 = interpretAstPlain env arg2
    in tszipWith0N (&&*) b1 b2
  AstLeqK arg1 arg2 ->
    let r1 = interpretAstPlain env arg1
        r2 = interpretAstPlain env arg2
    in r1 <=. r2
  AstLeqS arg1 arg2 ->
    let r1 = interpretAstPlain env arg1
        r2 = interpretAstPlain env arg2
    in r1 <=. r2
  AstLeqA @shb @sh shb sh arg1 arg2 | Refl <- lemAppNil @shb ->
    withKnownShS shb $
    withKnownShS sh $
    let r1 = interpretAstPlain env arg1
        r2 = interpretAstPlain env arg2
    in sunNest
       $ szipWithNested
           (\a1 a2 ->
             let c = convCmp ConvXS
                             (convCmp (Conv0X (STKS ZSS STKScalar))
                                      (convCmp ConvXS (Conv0X STKScalar)))
             in tconvert c STKScalar $ sunNest a1 <=. sunNest a2)
           (snest @_ @_ @sh shb r1) (snest shb r2)

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
--   SpanTarget (PrimalStepSpan s2) target = PrimalOf (SpanTarget s2 target)
--   SpanTarget DualSpan target = DualOf target
--   SpanTarget FullSpan target = target
--   SpanTarget PlainSpan target = PlainOf target
--
-- to be used in AstEnv and the codomain of interpretAst and a lot of other
-- code would need to be changed. Alternatively, we could use a GADT indexed
-- by the spans and maybe put values of this GADT in environment,
-- but this would still be complex and likely affecting performance.
-- Instead we promote results to @target@ similarly as in AstEnv
-- and simiarly as we omit @PrimalOf@ in the signatures of most "Ops" methods.
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
    in tapply t2 ll2
  AstVar var ->
    let var2 :: AstVarName FullSpan y
        var2 = coerce var  -- only FullSpan variables permitted in env
    in case DMap.lookup var2 env of
      Just t ->
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
    let c = interpretAstPlain env b
    in tcond (ftkToSTK (ftkAst a1)) c
             (interpretAst env a1) (interpretAst env a2)
  -- TODO: recognize nested builds and, for Concrete, call tbuild instead
  -- also recognize map and zipWith in nested builds and call these
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
    tfromPrimal (ftkToSTK (ftkAst a)) (tprimalPart $ interpretAst env a)
  AstDualPart a ->
    tfromDual (tdualPart (ftkToSTK (ftkAst a)) $ interpretAstFull env a)
  AstPlainPart a ->
    tfromPlain (ftkToSTK (ftkAst a)) (tplainPart $ interpretAst env a)
  AstFromPrimal a | Just Refl <- sameAstSpan @s @FullSpan ->
    -- By the invariant, interpretation of @a@ has zero dual part,
    -- so we don't have to do the following to remove the dual part,
    -- but we still do, because there's almost no rewriting of delta
    -- expressions, so even though they are semantically zero, they'd build
    -- up considerably if not wiped out regularly. By constrast, operations
    -- on AstConstant are rewritten eagerly to AstConstant, so for AstFromDual
    -- we really don't need to do anything.
    tfromPrimal (ftkToSTK (ftkAst a)) (interpretAstPrimal env a)
  AstFromPrimal a -> interpretAst env a
  AstFromDual a -> interpretAst env a
    -- By the invariant, interpretation of @a@ has zero primal part,
    -- so we don't have to do the following to remove the primal part:
    --   tfromDual (interpretAstDual env a)
  AstFromPlain a ->
    tfromPlain (ftkToSTK (ftkAst a)) (interpretAstPlain env a)

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
  AstConcreteK k -> tkconcrete @target k
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
  AstCastS v -> tscast $ interpretAst env v

  AstIndexS @shm shn v ix ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let v2 = interpretAst env v
        ix3 = interpretAstPlain env <$> ix
    in tsindex @_ @shm v2 ix3
  -- TODO: once specialization inspect-testing is back online,
  -- recover and also handle similarly tsupdate, both implemented
  -- as a gather and as a scatter
  -- TODO: this breaks specialization:
  AstScatterS shn v (ZS, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    tsoneHot (interpretAst env v) (interpretAstPlain env <$> ix)
  AstScatterS @shm @shn @shp
              shn v (var ::$ ZS, ix) | SNat :$$ _ <- knownShS @shm ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAst env v
        f2 :: IntOf target -> IxSOf target shp
        f2 !i2 = interpretAstPlain (extendEnvI var i2 env) <$> ix
    in tsscatter1 @_ @_ @shn @shp t1 f2
  AstScatterS @shm @shn @shp
              shn v (vars, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAst env v
        f2 :: IxSOf target shm -> IxSOf target shp
        f2 !ix2 = interpretAstPlain (extendEnvVarsS vars ix2 env) <$> ix
    in tsscatter @_ @shm @shn @shp t1 f2
  AstGatherS shn v (ZS, ix) -> interpretAst env (AstIndexS shn v ix)
  AstGatherS @shm @shn @shp
             shn v (var ::$ ZS, ix) | SNat :$$ _ <- knownShS @shm ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAst env v
        f2 :: IntOf target -> IxSOf target shp
        f2 !i2 = interpretAstPlain (extendEnvI var i2 env) <$> ix
    in tsgather1 @_ @_ @shn @shp t1 f2
  AstGatherS @shm @shn @shp
             shn v (vars, ix) ->
    withKnownShS shn $
    withKnownSTK (stkAstX v) $
    let t1 = interpretAst env v
        f2 :: IxSOf target shm -> IxSOf target shp
        f2 !ix2 = interpretAstPlain (extendEnvVarsS vars ix2 env) <$> ix
    in tsgather @_ @shm @shn @shp t1 f2
  AstMinIndexS v ->
    -- By the invariant v has zero dual part, so the following suffices:
    tsminIndex $ interpretAst env v
  AstMaxIndexS v ->
    -- By the invariant v has zero dual part, so the following suffices:
    tsmaxIndex $ interpretAst env v
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
        ix3 = interpretAstPlain env <$> ix
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
    tfromPlain STKScalar $ notB $ interpretAstPlain env arg
  AstBoolNotA arg | FTKS sh _ <- ftkAst arg ->
    withKnownShS sh $
    tfromPlain (ftkToSTK $ ftkAst arg)
    $ tsmap0N notB $ interpretAstPlain env arg
  AstBoolAnd arg1 arg2 ->
    let b1 = interpretAstPlain env arg1
        b2 = interpretAstPlain env arg2
    in tfromPlain STKScalar $ b1 &&* b2
  AstBoolAndA arg1 arg2 | FTKS sh _ <- ftkAst arg1 ->
    withKnownShS sh $
    let b1 = interpretAstPlain env arg1
        b2 = interpretAstPlain env arg2
    in tfromPlain (ftkToSTK $ ftkAst arg1)
       $ tszipWith0N (&&*) b1 b2
  AstLeqK arg1 arg2 ->
    let r1 = interpretAstPlain env arg1
        r2 = interpretAstPlain env arg2
    in tfromPlain STKScalar $ r1 <=. r2
  AstLeqS arg1 arg2 ->
    let r1 = interpretAstPlain env arg1
        r2 = interpretAstPlain env arg2
    in tfromPlain STKScalar $ r1 <=. r2
  AstLeqA @shb @sh shb sh arg1 arg2 | Refl <- lemAppNil @shb ->
    withKnownShS shb $
    withKnownShS sh $
    let r1 = interpretAstPlain env arg1
        r2 = interpretAstPlain env arg2
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
  :: forall target x y s s2. (AstSpan s2, BaseTensor target)
  => AstEnv target -> AstHFun s s2 x y
  -> HFunOf target x y
{-# INLINE interpretAstHFun #-}
interpretAstHFun _env (AstLambda var t) =
  tlambda @target (varNameToFTK var)
  $ HFun $ \ws -> interpretAst (extendEnv var ws emptyEnv) t
      -- Interpretation in empty environment makes sense here, because
      -- there are no free variables except for the one declared.

interpretAstHFunPrimal
  :: forall target x y. ADReady target
  => AstEnv target -> AstHFun PrimalSpan PrimalSpan x y
  -> HFunOf (PrimalOf target) x y
{-# INLINE interpretAstHFunPrimal #-}
interpretAstHFunPrimal _env (AstLambda var t) =
  tlambda @(PrimalOf target) (varNameToFTK var)
  $ HFun $ \ws -> interpretAst (extendEnv var ws emptyEnv) t
      -- This is probably optimized as much as possible, because
      -- thanks to the invariant, we get zero dual part from this
      -- PrimalSpan term and so interpretAstPrimal and tfromPrimal
      -- is not needed (and would not be possible, because we lack
      -- FullShapeTK y). From the other end, due to (PrimalOf target),
      -- there won't be any dual part coming from an argument.

interpretAstHFunPlain
  :: forall target x y. ADReady target
  => AstEnv target -> AstHFun PlainSpan PlainSpan x y
  -> HFunOf (PlainOf target) x y
{-# INLINE interpretAstHFunPlain #-}
interpretAstHFunPlain _env (AstLambda var t) =
  tlambda @(PlainOf target) (varNameToFTK var)
  $ HFun $ \ws -> interpretAst (extendEnv var ws emptyEnv) t

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
