{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for AST terms. Most of these instances
-- vectorize any terms starting with the build constructor.
-- The AST term instances can be used as building blocks for 'ADVal'
-- instances defined in "TensorADVal" but may also be used standalone.
module HordeAd.Core.TensorAst
  ( forwardPassByInterpretation
  , revArtifactFromForwardPass
  , revProduceArtifact
  , fwdArtifactFromForwardPass, fwdProduceArtifact
  , unRawY
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Array.Shape qualified as Sh
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector qualified as Data.NonStrict.Vector
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, type (+))
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Shape qualified as X

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInline
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.AstVectorize
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorADVal (unADValInterpretation, unDeltaRY)
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorConcrete ()
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), FlipS (..), IntegralF (..), RealFloatF (..))
import HordeAd.Util.SizedList

-- * Symbolic reverse and forward derivative computation

forwardPassByInterpretation
  :: forall z. TensorKind z
  => (HVector (AstRanked FullSpan)
      -> InterpretationTarget (AstRanked FullSpan) z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> HVector (AstRaw PrimalSpan)
  -> AstVarName FullSpan TKUntyped
  -> HVector (AstRanked FullSpan)
  -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit hVectorPrimal var hVector =
  let deltaInputs = generateDeltaInputs hVectorPrimal
      varInputs = makeADInputs hVectorPrimal deltaInputs
      ast = g hVector
      env = extendEnv var (HVectorPseudoTensor $ dmkHVector varInputs) envInit
  in interpretAst env $ unRankedY (stensorKind @z) ast

revArtifactFromForwardPass
  :: forall x z. (x ~ TKUntyped, TensorKind z)
  => Bool
  -> (HVector (AstRaw PrimalSpan)
      -> AstVarName FullSpan x
      -> HVector (AstRanked FullSpan)
      -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z)
  -> TensorKindFull x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass hasDt forwardPass
                                 ftk@(FTKUntyped parameters0) =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varPrimal, hVectorPrimal, var, hVector) = funToAstRev ftk in
  let -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(!primalBody, !deltaIT) =
        unADValInterpretation (stensorKind @z)
        $ forwardPass hVectorPrimal var hVector
      !delta = unDeltaRY (stensorKind @z) deltaIT in
  let (!varDt, !astDt) =
        funToAst (shapeAstFull $ unRawY (stensorKind @z) primalBody) id in
  let mdt = if hasDt then Just $ rawY (stensorKind @z) astDt else Nothing
      !gradient = gradientFromDelta parameters0 primalBody mdt delta
      !unGradient = gunshare (stensorKind @x)
                    $ HVectorPseudoTensor $ dmkHVector gradient
      !unPrimal = gunshare (stensorKind @z) primalBody
{- too expensive currently, so inlined as above:
      unGradient =
        mapInterpretationTarget unshareRaw unshareRawS (stensorKind @x)
        $ HVectorPseudoTensor $ dmkHVector gradient
-}
  in ( AstArtifactRev varDt varPrimal unGradient unPrimal
     , delta )

revProduceArtifact
  :: forall x z. (x ~ TKUntyped, TensorKind z)
  => Bool
  -> (HVector (AstRanked FullSpan)
      -> InterpretationTarget (AstRanked FullSpan) z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> TensorKindFull x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifact #-}
revProduceArtifact hasDt g envInit =
  revArtifactFromForwardPass
    hasDt (forwardPassByInterpretation g envInit)

gunshare
  :: forall y.
     STensorKindType y
  -> InterpretationTarget (AstRaw PrimalSpan) y
  -> InterpretationTarget (AstRaw PrimalSpan) y
gunshare stk b = case stk of
  STKR{} -> AstRaw $ unshareAstRanked $ unAstRaw b
  STKS{} -> AstRawS $ unshareAstShaped $ unAstRawS b
  STKProduct stk1 stk2 ->
    let !t1 = gunshare stk1 $ tproject1 b
        !t2 = gunshare stk2 $ tproject2 b
    in ttuple t1 t2
  STKUntyped -> HVectorPseudoTensor $ AstRawWrap $ unshareAstHVector
                $ unAstRawWrap $ unHVectorPseudoTensor b

gunshareRanked
  :: forall y.
     STensorKindType y
  -> InterpretationTarget (AstRanked PrimalSpan) y
  -> InterpretationTarget (AstRanked PrimalSpan) y
gunshareRanked stk b = case stk of
  STKR{} -> AstRanked $ unshareAstRanked $ unAstRanked b
  STKS{} -> AstShaped $ unshareAstShaped $ unAstShaped b
  STKProduct stk1 stk2 ->
    let !t1 = gunshareRanked stk1 $ tproject1 b
        !t2 = gunshareRanked stk2 $ tproject2 b
    in ttuple t1 t2
  STKUntyped -> HVectorPseudoTensor $ unshareAstHVector
                $ unHVectorPseudoTensor b

fwdArtifactFromForwardPass
  :: forall x z. (x ~ TKUntyped, TensorKind z)
  => (HVector (AstRaw PrimalSpan)
      -> AstVarName FullSpan x
      -> HVector (AstRanked FullSpan)
      -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z)
  -> TensorKindFull x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass ftk@(FTKUntyped parameters0) =
  let !(!varPrimalD, hVectorD, varPrimal, hVectorPrimal, var, hVector) =
        funToAstFwd ftk in
  let !(!primalBody, !deltaIT) =
        unADValInterpretation (stensorKind @z)
        $ forwardPass hVectorPrimal var hVector
      !delta = unDeltaRY (stensorKind @z) deltaIT in
  let !derivative = derivativeFromDelta (V.length parameters0) delta hVectorD
      !unDerivative = gunshare (stensorKind @z) derivative
      !unPrimal = gunshare (stensorKind @z) primalBody
  in ( AstArtifactFwd varPrimalD varPrimal unDerivative unPrimal
     , delta )

fwdProduceArtifact
  :: forall x z. (x ~ TKUntyped, TensorKind z)
  => (HVector (AstRanked FullSpan)
      -> InterpretationTarget (AstRanked FullSpan) z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> TensorKindFull x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdProduceArtifact #-}
fwdProduceArtifact g envInit =
  fwdArtifactFromForwardPass (forwardPassByInterpretation g envInit)


-- * Unlawful boolean instances of ranked AST; they are lawful modulo evaluation

type instance BoolOf (AstRanked s) = AstBool

instance AstSpan s => EqF (AstRanked s) where
  AstRanked v ==. AstRanked u = AstRel EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstRanked v /=. AstRanked u = AstRel NeqOp (astSpanPrimal v) (astSpanPrimal u)

instance AstSpan s => OrdF (AstRanked s) where
  AstRanked (AstConst u) <. AstRanked (AstConst v) = AstBoolConst $ u < v
    -- common in indexing
  v <. u = AstRel LsOp (astSpanPrimal (unAstRanked v)) (astSpanPrimal (unAstRanked u))
  AstRanked (AstConst u) <=. AstRanked (AstConst v) = AstBoolConst $ u <= v
    -- common in indexing
  v <=. u = AstRel LeqOp (astSpanPrimal (unAstRanked v)) (astSpanPrimal (unAstRanked u))
  AstRanked (AstConst u) >. AstRanked (AstConst v) = AstBoolConst $ u > v
    -- common in indexing
  v >. u = AstRel GtOp (astSpanPrimal (unAstRanked v)) (astSpanPrimal (unAstRanked u))
  AstRanked (AstConst u) >=. AstRanked (AstConst v) = AstBoolConst $ u >= v
    -- common in indexing
  v >=. u = AstRel GeqOp (astSpanPrimal (unAstRanked v)) (astSpanPrimal (unAstRanked u))

instance IfF (AstRanked s) where
  ifF cond a b = AstRanked $ astCond cond (unAstRanked a) (unAstRanked b)


-- * Unlawful boolean instances of shaped AST; they are lawful modulo evaluation

type instance BoolOf (AstShaped s) = AstBool

instance AstSpan s => EqF (AstShaped s) where
  AstShaped v ==. AstShaped u = AstRelS EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstShaped v /=. AstShaped u = AstRelS NeqOp (astSpanPrimal v) (astSpanPrimal u)

instance AstSpan s => OrdF (AstShaped s) where
  AstShaped (AstConstS u) <. AstShaped (AstConstS v) = AstBoolConst $ u < v
    -- common in indexing
  v <. u = AstRelS LsOp (astSpanPrimal (unAstShaped v)) (astSpanPrimal (unAstShaped u))
  AstShaped (AstConstS u) <=. AstShaped (AstConstS v) = AstBoolConst $ u <= v
    -- common in indexing
  v <=. u = AstRelS LeqOp (astSpanPrimal (unAstShaped v)) (astSpanPrimal (unAstShaped u))
  AstShaped (AstConstS u) >. AstShaped (AstConstS v) = AstBoolConst $ u > v
    -- common in indexing
  v >. u = AstRelS GtOp (astSpanPrimal (unAstShaped v)) (astSpanPrimal (unAstShaped u))
  AstShaped (AstConstS u) >=. AstShaped (AstConstS v) =  AstBoolConst $ u >= v
    -- common in indexing
  v >=. u = AstRelS GeqOp (astSpanPrimal (unAstShaped v)) (astSpanPrimal (unAstShaped u))

instance IfF (AstShaped s) where
  ifF cond a b = AstShaped $ astCond cond (unAstShaped a) (unAstShaped b)


-- * Ranked tensor AST instances

instance (GoodScalar r, KnownNat n, RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstRanked s r n) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstRanked s) (AstRanked s Double n) #-}
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit = fromHVectorR

instance (GoodScalar r, KnownNat n)
         => DualNumberValue (AstRanked PrimalSpan r n) where
  type DValue (AstRanked PrimalSpan r n) = ORArray r n
  fromDValue t = AstRanked $ fromPrimal $ AstConst $ runFlipR t

instance (GoodScalar r, KnownNat n)
         => TermValue (AstRanked FullSpan r n) where
  type Value (AstRanked FullSpan r n) = ORArray r n
  fromValue t = AstRanked $ fromPrimal $ AstConst $ runFlipR t

instance ProductTensor (AstRanked s) where
  tmkHVector = AstMkHVector

instance AstSpan s => RankedTensor (AstRanked s) where
  rletTKIn :: forall y n r. (TensorKind y, KnownNat n, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstRanked s) y
           -> (InterpretationTarget (AstRanked s) y -> AstRanked s r n)
           -> AstRanked s r n
  rletTKIn stk a f =
    AstRanked
    $ astLetFun @y @_ @s (unRankedY stk a) (unAstRanked . f . rankedY stk)

  rshape = shapeAst . unAstRanked
  rminIndex = AstRanked . fromPrimal . AstMinIndex
              . astSpanPrimal . unAstRanked
  rmaxIndex = AstRanked . fromPrimal . AstMaxIndex
              . astSpanPrimal . unAstRanked
  rfloor = AstRanked . fromPrimal . AstFloor
           . astSpanPrimal . unAstRanked

  riota = AstRanked . fromPrimal $ AstIota
  rindex v ix =
    AstRanked $ astIndexStep (unAstRanked v) (unAstRanked <$> ix)
  rsum = AstRanked . astSum . unAstRanked
  rscatter sh t f = AstRanked $ astScatter sh (unAstRanked t)
                    $ funToAstIndex
                        (fmap unAstRanked . f . fmap AstRanked)
                          -- this introduces new variable names

  rfromVector = AstRanked . astFromVector . V.map unAstRanked
  rreplicate k = withSNat k $ \snat ->
    AstRanked . astReplicate snat . unAstRanked
  rappend u v =
    AstRanked $ astAppend (unAstRanked u) (unAstRanked v)
  rslice i n = AstRanked . astSlice i n . unAstRanked
  rreverse = AstRanked . astReverse . unAstRanked
  rtranspose perm = AstRanked . astTranspose perm . unAstRanked
  rreshape sh = AstRanked . astReshape sh . unAstRanked
  rbuild1 k f =
    AstRanked $ astBuild1Vectorize k (unAstRanked . f . AstRanked)
  rgather sh t f = AstRanked $ astGatherStep sh (unAstRanked t)
                   $ funToAstIndex
                       (fmap unAstRanked . f . fmap AstRanked)
                         -- this introduces new variable names
  rcast = AstRanked . astCast . unAstRanked
  rfromIntegral =
    AstRanked . fromPrimal . astFromIntegral . astSpanPrimal . unAstRanked
  rconst = AstRanked . fromPrimal . AstConst
  rletHVectorIn a f =
    AstRanked
    $ astLetHVectorInFun a (unAstRanked . f)
  rletHFunIn a f = AstRanked $ astLetHFunInFun a (unAstRanked . f)
  rfromS = AstRanked . astRFromS . unAstShaped

  rshare a@(AstRanked(AstShare{})) = a
  rshare a | astIsSmall True (unAstRanked a) = a
  rshare a = AstRanked $ fun1ToAst $ \ !var -> AstShare var (unAstRanked a)

  rconstant = AstRanked . fromPrimal . unAstRanked
  rprimalPart = AstRanked . astSpanPrimal . unAstRanked
  rdualPart = AstRanked . astSpanDual . unAstRanked
  rD u u' = AstRanked $ astSpanD (unAstRanked u) (unAstRanked u')
  rScale s t = AstRanked $ astDualPart $ AstConstant (unAstRanked s) * AstD (unAstRanked $ rzero (rshape s)) (unAstRanked t)

astLetHVectorInFun
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => AstTensor s TKUntyped -> (HVector (AstRanked s) -> AstTensor s (TKR r n))
  -> AstTensor s (TKR r n)
{-# INLINE astLetHVectorInFun #-}
astLetHVectorInFun a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorIn vars a (f asts)

astLetHFunInFun
  :: (GoodScalar r, KnownNat n, TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor s (TKR r n))
  -> AstTensor s (TKR r n)
{-# INLINE astLetHFunInFun #-}
astLetHFunInFun a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunIn var a (f ast)

astSpanPrimal :: forall s y. (AstSpan s, TensorKind y)
              => AstTensor s y -> AstTensor PrimalSpan y
astSpanPrimal t | Just Refl <- sameAstSpan @s @PrimalSpan = t
astSpanPrimal _ | Just Refl <- sameAstSpan @s @DualSpan =
  error "astSpanPrimal: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimal t | Just Refl <- sameAstSpan @s @FullSpan = astPrimalPart t
astSpanPrimal _ = error "a spuriuos case for pattern match coverage"

astSpanDual :: forall s y. (AstSpan s, TensorKind y)
            => AstTensor s y -> AstTensor DualSpan y
astSpanDual t | Just Refl <- sameAstSpan @s @PrimalSpan =
  AstDualPart $ AstConstant t  -- this is nil; likely to happen
astSpanDual t | Just Refl <- sameAstSpan @s @DualSpan = t
astSpanDual t | Just Refl <- sameAstSpan @s @FullSpan = astDualPart t
astSpanDual _ = error "a spuriuos case for pattern match coverage"

astSpanD :: forall s y. (AstSpan s, TensorKind y)
         => AstTensor PrimalSpan y -> AstTensor DualSpan y
         -> AstTensor s y
astSpanD u _ | Just Refl <- sameAstSpan @s @PrimalSpan = u
astSpanD _ u' | Just Refl <- sameAstSpan @s @DualSpan = u'
astSpanD u u' | Just Refl <- sameAstSpan @s @FullSpan = AstD u u'
astSpanD _ _ = error "a spuriuos case for pattern match coverage"

astLetFun :: forall y z s.
             (TensorKind y, TensorKind z, AstSpan s)
          => AstTensor s y -> (AstTensor s y -> AstTensor s z)
          -> AstTensor s z
astLetFun a f | astIsSmall True a = f a
astLetFun a f =
  let sh = shapeAstFull a
      (var, ast) = funToAst sh f
  in astLet var a ast  -- safe, because subsitution ruled out above

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize :: (KnownNat n, GoodScalar r, AstSpan s)
                   => Int -> (AstInt -> AstTensor s (TKR r n))
                   -> AstTensor s (TKR r (1 + n))
astBuild1Vectorize k f = withSNat k $ \snat ->
  build1Vectorize snat $ funToAstI f


-- * Shaped tensor AST instances

instance (GoodScalar r, KnownShS sh, ShapedTensor (AstShaped s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstShaped s r sh) where
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit = fromHVectorS

instance (GoodScalar r, KnownShS sh)
         => DualNumberValue (AstShaped PrimalSpan r sh) where
  type DValue (AstShaped PrimalSpan r sh) = OSArray r sh
  fromDValue t = AstShaped $ fromPrimal $ AstConstS $ runFlipS t

instance (GoodScalar r, KnownShS sh)
         => TermValue (AstShaped FullSpan r sh) where
  type Value (AstShaped FullSpan r sh) = OSArray r sh
  fromValue t = AstShaped $ fromPrimal $ AstConstS $ runFlipS t

instance AstSpan s => ShapedTensor (AstShaped s) where
  sletTKIn :: forall y sh r. (TensorKind y, GoodScalar r, KnownShS sh)
           => STensorKindType y -> InterpretationTarget (AstRanked s) y
           -> (InterpretationTarget (AstRanked s) y -> AstShaped s r sh)
           -> AstShaped s r sh
  sletTKIn stk a f =
    AstShaped
    $ astLetFun @y @_ @s (unRankedY stk a) (unAstShaped . f . rankedY stk)

  sminIndex = AstShaped . fromPrimal . AstMinIndexS . astSpanPrimal . unAstShaped
  smaxIndex = AstShaped . fromPrimal . AstMaxIndexS . astSpanPrimal . unAstShaped
  sfloor = AstShaped . fromPrimal . AstFloorS . astSpanPrimal . unAstShaped

  siota = AstShaped . fromPrimal $ AstIotaS
  sindex v ix =
    AstShaped $ astIndexStepS (unAstShaped v) (unAstRanked <$> ix)
  ssum = AstShaped . astSumS . unAstShaped
  sscatter t f = AstShaped $ astScatterS (unAstShaped t)
                 $ funToAstIndexS
                     (fmap unAstRanked . f . fmap AstRanked)
                       -- this introduces new variable names

  sfromVector = AstShaped . astFromVectorS . V.map unAstShaped
  sreplicate = AstShaped . astReplicate SNat . unAstShaped
  sappend u v = AstShaped $ astAppendS (unAstShaped u) (unAstShaped v)
  sslice (_ :: Proxy i) Proxy = AstShaped . astSliceS @i . unAstShaped
  sreverse = AstShaped . astReverseS . unAstShaped
  stranspose perm = AstShaped . astTransposeS perm . unAstShaped
  sreshape = AstShaped . astReshapeS . unAstShaped
  sbuild1 f =
    AstShaped $ astBuild1VectorizeS (unAstShaped . f . AstRanked)
  sgather t f = AstShaped $ astGatherStepS (unAstShaped t)
                $ funToAstIndexS
                    (fmap unAstRanked . f . fmap AstRanked)
                      -- this introduces new variable names
  scast = AstShaped . astCastS . unAstShaped
  sfromIntegral = AstShaped . fromPrimal . astFromIntegralS . astSpanPrimal . unAstShaped
  sconst = AstShaped . fromPrimal . AstConstS
  sletHVectorIn a f =
    AstShaped
    $ astLetHVectorInFunS a (unAstShaped . f)
  sletHFunIn a f = AstShaped $ astLetHFunInFunS a (unAstShaped . f)
  sfromR = AstShaped . astSFromR . unAstRanked

  sshare a@(AstShaped(AstShare{})) = a
  sshare a | astIsSmall True (unAstShaped a) = a
  sshare a = AstShaped $ fun1ToAst $ \ !var -> AstShare var (unAstShaped a)

  sconstant = AstShaped . fromPrimal . unAstShaped
  sprimalPart = AstShaped . astSpanPrimal . unAstShaped
  sdualPart = AstShaped . astSpanDual . unAstShaped
  sD u u' = AstShaped $ astSpanD (unAstShaped u) (unAstShaped u')
  sScale s t = AstShaped $ astDualPart $ AstConstant (unAstShaped s) * AstD 0 (unAstShaped t)

astLetHVectorInFunS
  :: forall sh s r. (KnownShS sh, GoodScalar r, AstSpan s)
  => AstTensor s TKUntyped -> (HVector (AstRanked s) -> AstTensor s (TKS r sh))
  -> AstTensor s (TKS r sh)
{-# INLINE astLetHVectorInFunS #-}
astLetHVectorInFunS a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorInS vars a (f asts)

astLetHFunInFunS
  :: (GoodScalar r, KnownShS sh, TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor s (TKS r sh))
  -> AstTensor s (TKS r sh)
{-# INLINE astLetHFunInFunS #-}
astLetHFunInFunS a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunInS var a (f ast)

astBuild1VectorizeS :: forall n sh r s.
                       (KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
                    => (AstInt -> AstTensor s (TKS r sh))
                    -> AstTensor s (TKS r (n ': sh))
astBuild1VectorizeS f =
  build1Vectorize (SNat @n) $ funToAstI f


-- * HVectorTensor instance

instance TermValue (DynamicTensor (AstRanked FullSpan)) where
  type Value (DynamicTensor (AstRanked FullSpan)) =
    DynamicTensor ORArray
  fromValue = \case
    DynamicRanked t -> DynamicRanked $ AstRanked $ fromPrimal $ AstConst $ runFlipR t
    DynamicShaped @_ @sh t ->
      gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: X.Rank sh) $
      DynamicShaped @_ @sh $ AstShaped $ fromPrimal $ AstConstS $ runFlipS t
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2

instance AdaptableHVector (AstRanked s) (AstTensor s TKUntyped) where
  toHVector = undefined  -- impossible without losing sharing
  toHVectorOf = id  -- but this is possible
  fromHVector aInit params =
    let (portion, rest) = V.splitAt (V.length $ shapeAstHVector aInit) params
    in Just (AstMkHVector portion, rest)

-- HVector causes overlap and violation of injectivity,
-- hence Data.NonStrict.Vector. Injectivity is crucial to limit the number
-- of type applications the library user has to supply.
instance TermValue (AstTensor FullSpan TKUntyped) where
  type Value (AstTensor FullSpan TKUntyped) =
    Data.NonStrict.Vector.Vector (DynamicTensor ORArray)
  fromValue t = AstMkHVector $ V.convert $ V.map fromValue t

instance AdaptableHVector (AstRanked FullSpan)
                          (HVectorPseudoTensor (AstRanked FullSpan) r y) where
  toHVector = undefined  -- impossible without losing sharing
  toHVectorOf = unHVectorPseudoTensor  -- but this is possible
  fromHVector (HVectorPseudoTensor aInit) params =
    let (portion, rest) = V.splitAt (V.length $ shapeAstHVector aInit) params
    in Just (HVectorPseudoTensor $ AstMkHVector portion, rest)

instance TermValue (HVectorPseudoTensor (AstRanked FullSpan) r y) where
  type Value (HVectorPseudoTensor (AstRanked FullSpan) r y) =
    HVectorPseudoTensor ORArray r y
  fromValue (HVectorPseudoTensor t) =
    HVectorPseudoTensor $ AstMkHVector $ V.map fromValue t

instance forall s. AstSpan s => HVectorTensor (AstRanked s) (AstShaped s) where
  dshape = shapeAstHVector
  tshapeFull stk t = case stk of
    STKR{} -> shapeAstFull $ unAstRanked t
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (tproject1 t))
                                       (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unHVectorPseudoTensor t
  dmkHVector = AstMkHVector
  dlambda :: forall x y. (TensorKind x, TensorKind y)
          => TensorKindFull x -> HFun x y -> HFunOf (AstRanked s) x y
  dlambda shss f =
    let (var, ast) = funToAst shss $ \ !ll ->
          unRankedY (stensorKind @y) $ unHFun f $ rankedY (stensorKind @x) ll
    in AstLambda (var, shss, ast)
  dHApply :: forall x y. (TensorKind x, TensorKind y)
          => HFunOf (AstRanked s) x y
          -> InterpretationTarget (AstRanked s) x
          -> InterpretationTarget (AstRanked s) y
  dHApply t ll = rankedY (stensorKind @y) $ astHApply t
                 $ unRankedY (stensorKind @x) $ ll
  dunHVector (AstMkHVector l) = l
  dunHVector hVectorOf =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstRanked $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstShaped $ AstProjectS hVectorOf i
    in V.imap f $ shapeAstHVector hVectorOf
  dletHVectorInHVector = astLetHVectorInHVectorFun
  dletHFunInHVector = astLetHFunInHVectorFun
  dlet :: forall y. TensorKind y
       => InterpretationTarget (AstRanked s) y
       -> (InterpretationTarget (AstRanked s) y -> HVectorOf (AstRanked s))
       -> HVectorOf (AstRanked s)
  dlet u f = case stensorKind @y of
    STKR{} -> astLetFun (unAstRanked u) (f . AstRanked)
    STKS{} -> astLetFun (unAstShaped u) (f . AstShaped)
    STKProduct{} ->
      -- TODO: seems wrong: a gets computed twice unless the projection
      -- gets simplified early enough, which maybe it does?
      dlet (tproject1 u) $ \a1 ->
        dlet (tproject2 u) $ \a2 -> f (ttuple a1 a2)
    STKUntyped{} -> astLetFun (unHVectorPseudoTensor u) (f . HVectorPseudoTensor)
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  -- In this instance, these three ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstRanked to AstRaw.
  tunshare :: forall y. TensorKind y
           => InterpretationTarget (AstRanked s) y
           -> InterpretationTarget (AstRanked s) y
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> gunshareRanked (stensorKind @y)
      _ -> error "tunshare: used not at PrimalSpan"
  -- These and many similar bangs are necessary to ensure variable IDs
  -- are generated in the expected order, resulting in nesting of lets
  -- occuring in the correct order and so no scoping errors.
  dshare a@AstShare{} = a
  dshare a | astIsSmall True a = a
  dshare a = fun1ToAst $ \ !var -> AstShare var a
  dbuild1 k f = astBuildHVector1Vectorize k (f . AstRanked)
  rrev :: forall r n. (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (AstRanked s)
       -> AstTensor s TKUntyped
  rrev f parameters0 =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new @parmeters@, which is much better than computing anew.
    let g :: HVector (AstRanked FullSpan)
          -> InterpretationTarget (AstRanked FullSpan) (TKR r n)
        g !hv = f hv
        !(!(AstArtifactRev _varDt var gradient _primal), _delta) =
          revProduceArtifact False g emptyEnv (FTKUntyped parameters0)
    in \ !parameters -> assert (voidHVectorMatches parameters0 parameters) $
      let env = extendEnv
                  var (HVectorPseudoTensor $ AstMkHVector parameters) emptyEnv
      in simplifyInline $ unHVectorPseudoTensor
         $ interpretAst env $ unAstRawWrap $ unHVectorPseudoTensor gradient
        -- this interpretation both substitutes parameters for the variables and
        -- reinterprets @PrimalSpan@ terms in @s@ terms;
        -- we could shortcut when @s@ is @PrimalSpan@ and @parameters@
        -- are the same variables, but it's a very special case;
        -- a faster implementation would be via AstHApply, but this tests
        -- a slightly different code path, so let's keep it
  drevDt :: forall x z. (x ~ TKUntyped, TensorKind z)
              => TensorKindFull x
              -> HFun x z
              -> AstHFun (TKProduct z x) x
  drevDt ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let g :: HVector (AstRanked FullSpan)
          -> InterpretationTarget (AstRanked FullSpan) z
        g !hv = unHFun f (HVectorPseudoTensor $ AstMkHVector hv)
        -- No bangs here, because this goes under lambda and may be unneeded
        -- or even incorrect (and so, e.g., trigger
        -- `error "tunshare: used not at PrimalSpan"`, because no derivative
        -- should be taken of spans other than PrimalSpan)
        (AstArtifactRev varDt var gradient primal, _delta) =
          revProduceArtifact True g emptyEnv ftkx
        ftkz = shapeAstFull $ unRawY (stensorKind @z) primal
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          AstLet varDt (astProject1 astP)
            $ AstLet var (astProject2 astP)
              $ simplifyInline $ unRawY (stensorKind @x) gradient
    in AstLambda (varP, ftk2, ast)
  dfwd :: forall x z. (x ~ TKUntyped, TensorKind z)
            => TensorKindFull x
            -> HFun x z
            -> AstHFun (TKProduct x x) z
  dfwd ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let g :: HVector (AstRanked FullSpan)
          -> InterpretationTarget (AstRanked FullSpan) z
        g !hv = unHFun f (HVectorPseudoTensor $ AstMkHVector hv)
        (AstArtifactFwd varDs var derivative _primal, _delta) =
          fwdProduceArtifact g emptyEnv ftkx
        ftk2 = FTKProduct ftkx ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          AstLet varDs (astProject1 astP)
            $ AstLet var (astProject2 astP)
              $ simplifyInline $ unRawY (stensorKind @z) derivative
    in AstLambda (varP, ftk2, ast)
  dmapAccumRDer _ !k !accShs !bShs !eShs =
    AstMapAccumRDer k accShs bShs eShs
  dmapAccumLDer _ !k !accShs !bShs !eShs =
    AstMapAccumLDer k accShs bShs eShs

astLetHVectorInHVectorFun
  :: AstSpan s
  => AstTensor s TKUntyped -> (HVector (AstRanked s) -> AstTensor s TKUntyped)
  -> AstTensor s TKUntyped
{-# INLINE astLetHVectorInHVectorFun #-}
astLetHVectorInHVectorFun a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorInHVector vars a (f asts)

astLetHFunInHVectorFun
  :: (TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor s TKUntyped)
  -> AstTensor s TKUntyped
{-# INLINE astLetHFunInHVectorFun #-}
astLetHFunInHVectorFun a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunInHVector var a (f ast)

astBuildHVector1Vectorize
  :: AstSpan s
  => SNat k -> (AstInt -> AstTensor s TKUntyped) -> AstTensor s TKUntyped
astBuildHVector1Vectorize k f = build1Vectorize k $ funToAstI f

-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: VoidHVector
  -> HVectorPseudoTensor (AstRanked PrimalSpan) Float '()
  -> Maybe (HVectorPseudoTensor (AstRanked PrimalSpan) Float '())
  -> Delta (AstRanked PrimalSpan) TKUntyped
  -> HVector (AstRanked PrimalSpan) #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (AstRanked PrimalSpan) -> EvalState (AstRanked PrimalSpan) #-}


-- * The AstRaw, AstNoVectorize and AstNoSimplify instances

type instance BoolOf (AstRanked s) = AstBool

{-deriving instance IfF (AstRanked s)
deriving instance AstSpan s => EqF (AstRanked s)
deriving instance AstSpan s => OrdF (AstRanked s)-}
deriving instance Eq (AstRanked s r n)
deriving instance Ord (AstRanked s r n)
deriving instance Num (AstTensor s (TKR r n)) => Num (AstRanked s r n)
deriving instance (Real (AstTensor s (TKR r n)))
                   => Real (AstRanked s r n)
deriving instance (IntegralF (AstTensor s (TKR r n)))
                  => IntegralF (AstRanked s r n)
deriving instance Fractional (AstTensor s (TKR r n))
                  => Fractional (AstRanked s r n)
deriving instance Floating (AstTensor s (TKR r n))
                  => Floating (AstRanked s r n)
deriving instance (RealFrac (AstTensor s (TKR r n)))
                  => RealFrac (AstRanked s r n)
deriving instance (RealFloatF (AstTensor s (TKR r n)))
                  => RealFloatF (AstRanked s r n)

type instance BoolOf (AstShaped s) = AstBool

{-deriving instance IfF (AstShaped s)
deriving instance AstSpan s => EqF (AstShaped s)
deriving instance AstSpan s => OrdF (AstShaped s)-}
deriving instance Eq (AstShaped s r sh)
deriving instance Ord (AstShaped s r sh)
deriving instance Num (AstTensor s (TKS r sh)) => Num (AstShaped s r sh)
deriving instance (Real (AstTensor s (TKS r sh)))
                   => Real (AstShaped s r sh)
deriving instance (IntegralF (AstTensor s (TKS r sh)))
                  => IntegralF (AstShaped s r sh)
deriving instance Fractional (AstTensor s (TKS r sh))
                  => Fractional (AstShaped s r sh)
deriving instance Floating (AstTensor s (TKS r sh))
                  => Floating (AstShaped s r sh)
deriving instance (RealFrac (AstTensor s (TKS r sh)))
                  => RealFrac (AstShaped s r sh)
deriving instance (RealFloatF (AstTensor s (TKS r sh)))
                  => RealFloatF (AstShaped s r sh)

type instance BoolOf (AstRaw s) = AstBool

{-deriving instance IfF (AstRaw s)
deriving instance AstSpan s => EqF (AstRaw s)
deriving instance AstSpan s => OrdF (AstRaw s)-}

instance IfF (AstRaw s) where
  ifF cond a b = AstRaw $ AstCond cond (unAstRaw a) (unAstRaw b)
instance AstSpan s => EqF (AstRaw s) where
  AstRaw v ==. AstRaw u = AstRel EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstRaw v /=. AstRaw u = AstRel NeqOp (astSpanPrimal v) (astSpanPrimal u)
instance AstSpan s => OrdF (AstRaw s) where
  v <. u = AstRel LsOp (astSpanPrimal (unAstRaw v)) (astSpanPrimal (unAstRaw u))
  v <=. u = AstRel LeqOp (astSpanPrimal (unAstRaw v)) (astSpanPrimal (unAstRaw u))
  v >. u = AstRel GtOp (astSpanPrimal (unAstRaw v)) (astSpanPrimal (unAstRaw u))
  v >=. u = AstRel GeqOp (astSpanPrimal (unAstRaw v)) (astSpanPrimal (unAstRaw u))
deriving instance Eq (AstRaw s r n)
deriving instance Ord (AstRaw s r n)
deriving instance Num (AstTensor s (TKR r n)) => Num (AstRaw s r n)
deriving instance (Real (AstTensor s (TKR r n)))
                   => Real (AstRaw s r n)
deriving instance (IntegralF (AstTensor s (TKR r n)))
                  => IntegralF (AstRaw s r n)
deriving instance Fractional (AstTensor s (TKR r n))
                  => Fractional (AstRaw s r n)
deriving instance Floating (AstTensor s (TKR r n))
                  => Floating (AstRaw s r n)
deriving instance (RealFrac (AstTensor s (TKR r n)))
                  => RealFrac (AstRaw s r n)
deriving instance (RealFloatF (AstTensor s (TKR r n)))
                  => RealFloatF (AstRaw s r n)

type instance BoolOf (AstRawS s) = AstBool

instance IfF (AstRawS s) where
  ifF cond a b = AstRawS $ AstCond cond (unAstRawS a) (unAstRawS b)
instance AstSpan s => EqF (AstRawS s) where
  AstRawS v ==. AstRawS u = AstRelS EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstRawS v /=. AstRawS u = AstRelS NeqOp (astSpanPrimal v) (astSpanPrimal u)
instance AstSpan s => OrdF (AstRawS s) where
  v <. u = AstRelS LsOp (astSpanPrimal (unAstRawS v)) (astSpanPrimal (unAstRawS u))
  v <=. u = AstRelS LeqOp (astSpanPrimal (unAstRawS v)) (astSpanPrimal (unAstRawS u))
  v >. u = AstRelS GtOp (astSpanPrimal (unAstRawS v)) (astSpanPrimal (unAstRawS u))
  v >=. u = AstRelS GeqOp (astSpanPrimal (unAstRawS v)) (astSpanPrimal (unAstRawS u))
deriving instance Eq (AstRawS s r sh)
deriving instance Ord (AstRawS s r sh)
deriving instance Num (AstTensor s (TKS r sh)) => Num (AstRawS s r sh)
deriving instance (IntegralF (AstTensor s (TKS r sh)))
                  => IntegralF (AstRawS s r sh)
deriving instance Fractional (AstTensor s (TKS r sh))
                  => Fractional (AstRawS s r sh)
deriving instance Floating (AstTensor s (TKS r sh))
                  => Floating (AstRawS s r sh)
deriving instance (RealFloatF (AstTensor s (TKS r sh)))
                  => RealFloatF (AstRawS s r sh)

type instance BoolOf (AstNoVectorize s) = AstBool

instance IfF (AstNoVectorize s) where
  ifF b v1 v2 =
    AstNoVectorize $ unAstRanked
    $ ifF b (AstRanked $ unAstNoVectorize v1) (AstRanked $ unAstNoVectorize v2)
instance AstSpan s => EqF (AstNoVectorize s) where
  v1 ==. v2 = AstRanked (unAstNoVectorize v1) ==. AstRanked (unAstNoVectorize v2)
instance AstSpan s => OrdF (AstNoVectorize s) where
  v1 <. v2 = AstRanked (unAstNoVectorize v1) <. AstRanked (unAstNoVectorize v2)
deriving instance Eq (AstNoVectorize s r n)
deriving instance Ord (AstNoVectorize s r n)
deriving instance Num (AstTensor s (TKR r n)) => Num (AstNoVectorize s r n)
deriving instance (Real (AstTensor s (TKR r n)))
                   => Real (AstNoVectorize s r n)
deriving instance (IntegralF (AstTensor s (TKR r n)))
                  => IntegralF (AstNoVectorize s r n)
deriving instance Fractional (AstTensor s (TKR r n))
                  => Fractional (AstNoVectorize s r n)
deriving instance Floating (AstTensor s (TKR r n))
                  => Floating (AstNoVectorize s r n)
deriving instance (RealFrac (AstTensor s (TKR r n)))
                  => RealFrac (AstNoVectorize s r n)
deriving instance (RealFloatF (AstTensor s (TKR r n)))
                  => RealFloatF (AstNoVectorize s r n)

type instance BoolOf (AstNoVectorizeS s) = AstBool

instance IfF (AstNoVectorizeS s) where
  ifF b v1 v2 =
    AstNoVectorizeS $ unAstShaped
    $ ifF b (AstShaped $ unAstNoVectorizeS v1) (AstShaped $ unAstNoVectorizeS v2)
instance AstSpan s => EqF (AstNoVectorizeS s) where
  v1 ==. v2 = AstShaped (unAstNoVectorizeS v1) ==. AstShaped (unAstNoVectorizeS v2)
instance AstSpan s => OrdF (AstNoVectorizeS s) where
  v1 <. v2 = AstShaped (unAstNoVectorizeS v1) <. AstShaped (unAstNoVectorizeS v2)
deriving instance Eq ((AstNoVectorizeS s) r sh)
deriving instance Ord ((AstNoVectorizeS s) r sh)
deriving instance Num (AstTensor s (TKS r sh)) => Num (AstNoVectorizeS s r sh)
deriving instance (IntegralF (AstTensor s (TKS r sh)))
                  => IntegralF (AstNoVectorizeS s r sh)
deriving instance Fractional (AstTensor s (TKS r sh))
                  => Fractional (AstNoVectorizeS s r sh)
deriving instance Floating (AstTensor s (TKS r sh))
                  => Floating (AstNoVectorizeS s r sh)
deriving instance (RealFloatF (AstTensor s (TKS r sh)))
                  => RealFloatF (AstNoVectorizeS s r sh)

type instance BoolOf (AstNoSimplify s) = AstBool

instance IfF (AstNoSimplify s) where
  ifF b v1 v2 =
    AstNoSimplify $ unAstRanked
    $ ifF b (AstRanked $ unAstNoSimplify v1) (AstRanked $ unAstNoSimplify v2)
instance AstSpan s => EqF (AstNoSimplify s) where
  v1 ==. v2 = AstRanked (unAstNoSimplify v1) ==. AstRanked (unAstNoSimplify v2)
instance AstSpan s => OrdF (AstNoSimplify s) where
  v1 <. v2 = AstRanked (unAstNoSimplify v1) <. AstRanked (unAstNoSimplify v2)
deriving instance Eq (AstNoSimplify s r n)
deriving instance Ord (AstNoSimplify s r n)
deriving instance Num (AstTensor s (TKR r n)) => Num (AstNoSimplify s r n)
deriving instance (Real (AstTensor s (TKR r n)))
                  => Real (AstNoSimplify s r n)
deriving instance (IntegralF (AstTensor s (TKR r n)))
                  => IntegralF (AstNoSimplify s r n)
deriving instance Fractional (AstTensor s (TKR r n))
                  => Fractional (AstNoSimplify s r n)
deriving instance Floating (AstTensor s (TKR r n))
                  => Floating (AstNoSimplify s r n)
deriving instance (RealFrac (AstTensor s (TKR r n)))
                  => RealFrac (AstNoSimplify s r n)
deriving instance (RealFloatF (AstTensor s (TKR r n)))
                  => RealFloatF (AstNoSimplify s r n)

type instance BoolOf (AstNoSimplifyS s) = AstBool

instance IfF (AstNoSimplifyS s) where
  ifF b v1 v2 =
    AstNoSimplifyS $ unAstShaped
    $ ifF b (AstShaped $ unAstNoSimplifyS v1) (AstShaped $ unAstNoSimplifyS v2)
instance AstSpan s => EqF (AstNoSimplifyS s) where
  v1 ==. v2 = AstShaped (unAstNoSimplifyS v1) ==. AstShaped (unAstNoSimplifyS v2)
instance AstSpan s => OrdF (AstNoSimplifyS s) where
  v1 <. v2 = AstShaped (unAstNoSimplifyS v1) <. AstShaped (unAstNoSimplifyS v2)
deriving instance Eq (AstNoSimplifyS s r sh)
deriving instance Ord (AstNoSimplifyS s r sh)
deriving instance Num (AstTensor s (TKS r sh)) => Num (AstNoSimplifyS s r sh)
deriving instance (IntegralF (AstTensor s (TKS r sh)))
                  => IntegralF (AstNoSimplifyS s r sh)
deriving instance Fractional (AstTensor s (TKS r sh))
                  => Fractional (AstNoSimplifyS s r sh)
deriving instance Floating (AstTensor s (TKS r sh))
                  => Floating (AstNoSimplifyS s r sh)
deriving instance (RealFloatF (AstTensor s (TKS r sh)))
                  => RealFloatF (AstNoSimplifyS s r sh)

instance ProductTensor (AstRaw s) where
  tmkHVector = AstRawWrap . AstMkHVector . unRawHVector

instance AstSpan s => RankedTensor (AstRaw s) where
  rletTKIn :: forall y n r.
              (TensorKind y, KnownNat n, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstRaw s) y
           -> (InterpretationTarget (AstRaw s) y -> AstRaw s r n)
           -> AstRaw s r n
  rletTKIn stk a f =
    AstRaw
    $ astLetFunRaw @y @_ @s (unRawY stk a) (unAstRaw . f . rawY stk)
  rshape = shapeAst . unAstRaw
  rminIndex = AstRaw . fromPrimal . AstMinIndex . astSpanPrimal . unAstRaw
  rmaxIndex = AstRaw . fromPrimal . AstMaxIndex . astSpanPrimal . unAstRaw
  rfloor = AstRaw . fromPrimal . AstFloor . astSpanPrimal . unAstRaw
  riota = AstRaw . fromPrimal $ AstIota
  rindex v ix = AstRaw $ AstIndex (unAstRaw v) (unAstRaw <$> ix)
  rsum = AstRaw . AstSum . unAstRaw
  rscatter sh t f = AstRaw $ AstScatter sh (unAstRaw t)
                    $ funToAstIndex (fmap unAstRaw . f . fmap AstRaw)
                        -- this introduces new variable names
  rfromVector = AstRaw . AstFromVector . V.map unAstRaw
  rreplicate k = withSNat k $ \snat ->
    AstRaw . AstReplicate snat . unAstRaw
  rappend u v = AstRaw $ AstAppend (unAstRaw u) (unAstRaw v)
  rslice i n = AstRaw . AstSlice i n . unAstRaw
  rreverse = AstRaw . AstReverse . unAstRaw
  rtranspose perm = AstRaw . AstTranspose perm . unAstRaw
  rreshape sh = AstRaw . AstReshape sh . unAstRaw
  rbuild1 k f = withSNat k $ \snat ->
    AstRaw $ AstBuild1 snat
    $ funToAstI  -- this introduces new variable names
    $ unAstRaw . f . AstRaw
  rgather sh t f = AstRaw $ AstGather sh (unAstRaw t)
                   $ funToAstIndex (fmap unAstRaw . f . fmap AstRaw)
                       -- this introduces new variable names
  rcast = AstRaw . AstCast . unAstRaw
  rfromIntegral =
    AstRaw . fromPrimal . AstFromIntegral . astSpanPrimal . unAstRaw
  rconst = AstRaw . fromPrimal . AstConst
  rletHVectorIn a f =
    AstRaw $ astLetHVectorInFunRaw (unAstRawWrap a) (unAstRaw . f . rawHVector)
  rletHFunIn a f = AstRaw $ astLetHFunInFunRaw a (unAstRaw . f)
  rfromS = AstRaw . AstRFromS . unAstRawS

  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  rshare a@(AstRaw (AstShare{})) = a
  rshare a | astIsSmall True (unAstRaw a) = a
  rshare a = AstRaw $ fun1ToAst $ \ !var -> AstShare var (unAstRaw a)

  rconstant = AstRaw . fromPrimal . unAstRaw
  rprimalPart = AstRaw . astSpanPrimal . unAstRaw
  rdualPart = AstRaw . astSpanDual . unAstRaw
  rD u u' = AstRaw $ astSpanD (unAstRaw u) (unAstRaw u')
  rScale s t = AstRaw $ astDualPart
               $ AstConstant (unAstRaw s) * AstD (unAstRanked $ rzero (rshape s)) (unAstRaw t)

astLetFunRaw :: forall y z s.
                (TensorKind y, TensorKind z, AstSpan s)
             => AstTensor s y -> (AstTensor s y -> AstTensor s z)
             -> AstTensor s z
astLetFunRaw a f | astIsSmall True a = f a  -- too important an optimization
astLetFunRaw a f =
  let sh = shapeAstFull a
      (var, ast) = funToAst sh f
  in AstLet var a ast  -- safe, because subsitution ruled out above

astLetHVectorInFunRaw
  :: forall n s r. (AstSpan s, GoodScalar r, KnownNat n)
  => AstTensor s TKUntyped -> (HVector (AstRanked s) -> AstTensor s (TKR r n))
  -> AstTensor s (TKR r n)
astLetHVectorInFunRaw a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorIn vars a (f asts)

astLetHVectorInFunRawS
  :: forall sh s r. (AstSpan s, KnownShS sh, GoodScalar r)
  => AstTensor s TKUntyped -> (HVector (AstRanked s) -> AstTensor s (TKS r sh))
  -> AstTensor s (TKS r sh)
astLetHVectorInFunRawS a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorInS vars a (f asts)

astLetHFunInFunRaw
  :: (GoodScalar r, KnownNat n, TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor s (TKR r n))
  -> AstTensor s (TKR r n)
astLetHFunInFunRaw a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunIn var a (f ast)

astLetHFunInFunRawS
  :: (GoodScalar r, KnownShS sh, TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor s (TKS r sh))
  -> AstTensor s (TKS r sh)
astLetHFunInFunRawS a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunInS var a (f ast)

astLetHVectorInHVectorFunRaw
  :: AstSpan s
  => AstTensor s TKUntyped -> (HVector (AstRanked s) -> AstTensor s TKUntyped)
  -> AstTensor s TKUntyped
astLetHVectorInHVectorFunRaw a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorInHVector vars a (f asts)

astLetHFunInHVectorFunRaw
  :: (TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor s TKUntyped)
  -> AstTensor s TKUntyped
astLetHFunInHVectorFunRaw a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunInHVector var a (f ast)

instance AstSpan s => ShapedTensor (AstRawS s) where
  sletTKIn :: forall y sh r. (TensorKind y, GoodScalar r, KnownShS sh)
           => STensorKindType y -> InterpretationTarget (AstRaw s) y
           -> (InterpretationTarget (AstRaw s) y -> AstRawS s r sh)
           -> AstRawS s r sh
  sletTKIn stk a f =
    AstRawS
    $ astLetFunRaw @y @_ @s (unRawY stk a) (unAstRawS . f . rawY stk)
  sminIndex = AstRawS . fromPrimal . AstMinIndexS . astSpanPrimal . unAstRawS
  smaxIndex = AstRawS . fromPrimal . AstMaxIndexS . astSpanPrimal . unAstRawS
  sfloor = AstRawS . fromPrimal . AstFloorS . astSpanPrimal . unAstRawS
  siota = AstRawS . fromPrimal $ AstIotaS
  sindex v ix = AstRawS $ AstIndexS (unAstRawS v) (unAstRaw <$> ix)
  ssum = AstRawS . AstSumS . unAstRawS
  sscatter t f = AstRawS $ AstScatterS (unAstRawS t)
                 $ funToAstIndexS (fmap unAstRaw . f . fmap AstRaw)
                     -- this introduces new variable names
  sfromVector = AstRawS . AstFromVectorS . V.map unAstRawS
  sreplicate = AstRawS . AstReplicate SNat . unAstRawS
  sappend u v = AstRawS $ AstAppendS (unAstRawS u) (unAstRawS v)
  sslice (_ :: Proxy i) Proxy = AstRawS . AstSliceS @i . unAstRawS
  sreverse = AstRawS . AstReverseS . unAstRawS
  stranspose perm = AstRawS . AstTransposeS perm . unAstRawS
  sreshape = AstRawS . AstReshapeS . unAstRawS
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (AstRawS s) -> AstRawS s r sh)
          -> AstRawS s r (n ': sh)
  sbuild1 f = AstRawS $ AstBuild1 (SNat @n)
              $ funToAstI  -- this introduces new variable names
              $ unAstRawS . f . AstRaw
  sgather t f = AstRawS $ AstGatherS (unAstRawS t)
                $ funToAstIndexS (fmap unAstRaw . f . fmap AstRaw)
                    -- this introduces new variable names
  scast = AstRawS . AstCastS . unAstRawS
  sfromIntegral = AstRawS . fromPrimal . AstFromIntegralS
                  . astSpanPrimal . unAstRawS
  sconst = AstRawS . fromPrimal . AstConstS
  sletHVectorIn a f =
    AstRawS
    $ astLetHVectorInFunRawS (unAstRawWrap a) (unAstRawS . f . rawHVector)
  sletHFunIn a f = AstRawS $ astLetHFunInFunRawS a (unAstRawS . f)
  sfromR = AstRawS . AstSFromR . unAstRaw

  sshare a@(AstRawS (AstShare{})) = a
  sshare a | astIsSmall True (unAstRawS a) = a
  sshare a = AstRawS $ fun1ToAst $ \ !var -> AstShare var (unAstRawS a)

  sconstant = AstRawS . fromPrimal . unAstRawS
  sprimalPart = AstRawS . astSpanPrimal . unAstRawS
  sdualPart = AstRawS . astSpanDual . unAstRawS
  sD u u' = AstRawS $ astSpanD (unAstRawS u) (unAstRawS u')
  sScale s t = AstRawS $ astDualPart
               $ AstConstant (unAstRawS s) * AstD 0 (unAstRawS t)

instance AstSpan s => HVectorTensor (AstRaw s) (AstRawS s) where
  dshape = shapeAstHVector . unAstRawWrap
  tshapeFull stk t = case stk of
    STKR{} -> shapeAstFull $ unAstRaw t
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (tproject1 t))
                                       (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unAstRawWrap $ unHVectorPseudoTensor t
  dmkHVector = AstRawWrap . AstMkHVector . unRawHVector
  dlambda :: forall x y. (TensorKind x, TensorKind y)
          => TensorKindFull x -> HFun x y -> HFunOf (AstRaw s) x y
  dlambda shss f =
    let (var, ast) = funToAst shss $ \ !ll ->
          unRankedY (stensorKind @y) $ unHFun f $ rankedY (stensorKind @x) ll
    in AstLambda (var, shss, ast)
  dHApply :: forall x y. (TensorKind x, TensorKind y)
          => HFunOf (AstRaw s) x y
          -> InterpretationTarget (AstRaw s) x
          -> InterpretationTarget (AstRaw s) y
  dHApply t ll =
    let app = AstHApply t $ unRawY (stensorKind @x) ll
    in rawY (stensorKind @y) app
  dunHVector (AstRawWrap (AstMkHVector l)) = rawHVector l
  dunHVector (AstRawWrap hVectorOf) =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstRanked $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstShaped $ AstProjectS hVectorOf i
    in rawHVector $ V.imap f $ shapeAstHVector hVectorOf
  dletHVectorInHVector a f =
    AstRawWrap
    $ astLetHVectorInHVectorFunRaw (unAstRawWrap a)
                                   (unAstRawWrap . f . rawHVector)
  dletHFunInHVector t f =
    AstRawWrap
    $ astLetHFunInHVectorFunRaw t (unAstRawWrap . f)
  dlet :: forall y. TensorKind y
       => InterpretationTarget (AstRaw s) y
       -> (InterpretationTarget (AstRaw s) y -> HVectorOf (AstRaw s))
       -> HVectorOf (AstRaw s)
  dlet u f = case stensorKind @y of
    STKR{} -> AstRawWrap $ astLetFunRaw (unAstRaw u) (unAstRawWrap . f . AstRaw)
    STKS{} -> AstRawWrap $ astLetFunRaw (unAstRawS u) (unAstRawWrap . f . AstRawS)
    STKProduct{} -> error "TODO"
    STKUntyped{} -> error "TODO"
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  -- In this instance, these three ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstRanked to AstRaw.
  tunshare :: forall y. TensorKind y
           => InterpretationTarget (AstRaw s) y
           -> InterpretationTarget (AstRaw s) y
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> gunshare (stensorKind @y)
      _ -> error "tunshare: used not at PrimalSpan"
  dshare a@(AstRawWrap AstShare{}) = a
  dshare a | astIsSmall True (unAstRawWrap a) = a
  dshare a = AstRawWrap $ fun1ToAst $ \ !var -> AstShare var (unAstRawWrap a)
  dbuild1 k f = AstRawWrap
                $ AstBuildHVector1 k $ funToAstI (unAstRawWrap . f . AstRaw)
  -- These three methods are called at this type in delta evaluation via
  -- dmapAccumR and dmapAccumL, they have to work. We could refrain from
  -- simplifying the resulting terms, but it's not clear that's more consistent.
  rrev f parameters0 hVector =  -- we don't have an AST constructor to hold it
    AstRawWrap
    $ rrev f parameters0 (unRawHVector hVector)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ k accShs bShs eShs f df rf acc0 es =
    AstRawWrap
    $ AstMapAccumRDer k accShs bShs eShs f df rf (unAstRawWrap acc0)
                                                 (unAstRawWrap es)
  dmapAccumLDer _ k accShs bShs eShs f df rf acc0 es =
    AstRawWrap
    $ AstMapAccumLDer k accShs bShs eShs f df rf (unAstRawWrap acc0)
                                                 (unAstRawWrap es)

instance ProductTensor (AstNoVectorize s) where
  tmkHVector = AstNoVectorizeWrap . AstMkHVector . unNoVectorizeHVector

noVectorizeY :: forall y s.
           STensorKindType y -> AstTensor s y
        -> InterpretationTarget (AstNoVectorize s) y
noVectorizeY stk t = case stk of
  STKR{} -> AstNoVectorize t
  STKS{} -> AstNoVectorizeS t
  STKProduct stk1 stk2 ->
    ttuple (noVectorizeY stk1 $ astProject1 t) (noVectorizeY stk2 $ astProject2 t)
  STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap t

unNoVectorizeY :: forall y s.
             STensorKindType y -> InterpretationTarget (AstNoVectorize s) y
          -> AstTensor s y
unNoVectorizeY stk t = case stk of
  STKR{} -> unAstNoVectorize t
  STKS{} -> unAstNoVectorizeS t
  STKProduct stk1 stk2 -> AstTuple (unNoVectorizeY stk1 $ tproject1 t)
                                   (unNoVectorizeY stk2 $ tproject2 t)
  STKUntyped -> unAstNoVectorizeWrap $ unHVectorPseudoTensor t

instance AstSpan s => RankedTensor (AstNoVectorize s) where
  rletTKIn :: forall y n r.
              (TensorKind y, KnownNat n, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstNoVectorize s) y
           -> (InterpretationTarget (AstNoVectorize s) y -> AstNoVectorize s r n)
           -> AstNoVectorize s r n
  rletTKIn stk a f =
    AstNoVectorize
    $ astLetFun @y @_ @s
                (unNoVectorizeY stk a) (unAstNoVectorize . f . noVectorizeY stk)
  rshape = rshape . unAstNoVectorize2
  rminIndex = astNoVectorize2 . rminIndex . unAstNoVectorize2
  rmaxIndex = astNoVectorize2 . rmaxIndex . unAstNoVectorize2
  rfloor = astNoVectorize2 . rfloor . unAstNoVectorize2
  riota = astNoVectorize2 riota
  rindex v ix =
    astNoVectorize2 $ rindex (unAstNoVectorize2 v) (unAstNoVectorize2 <$> ix)
  rsum = astNoVectorize2 . rsum . unAstNoVectorize2
  rscatter sh t f =
    astNoVectorize2 $ rscatter sh (unAstNoVectorize2 t)
                   $ fmap unAstNoVectorize2 . f . fmap astNoVectorize2
  rfromVector = astNoVectorize2 . rfromVector . V.map unAstNoVectorize2
  rreplicate k = astNoVectorize2 . rreplicate k . unAstNoVectorize2
  rappend u v =
    astNoVectorize2 $ rappend (unAstNoVectorize2 u) (unAstNoVectorize2 v)
  rslice i n = astNoVectorize2 . rslice i n . unAstNoVectorize2
  rreverse = astNoVectorize2 . rreverse . unAstNoVectorize2
  rtranspose perm = astNoVectorize2 . rtranspose perm . unAstNoVectorize2
  rreshape sh = astNoVectorize2 . rreshape sh . unAstNoVectorize2
  rbuild1 k f = withSNat k $ \snat ->
    AstNoVectorize $ AstBuild1 snat
    $ funToAstI  -- this introduces new variable names
    $ unAstNoVectorize . f . AstNoVectorize
  rgather sh t f =
    astNoVectorize2 $ rgather sh (unAstNoVectorize2 t)
                   $ fmap unAstNoVectorize2 . f . fmap astNoVectorize2
  rcast = astNoVectorize2 . rcast . unAstNoVectorize2
  rfromIntegral = astNoVectorize2 . rfromIntegral . unAstNoVectorize2
  rconst = astNoVectorize2 . rconst
  rletHVectorIn a f =
    AstNoVectorize $ unAstRanked
    $ rletHVectorIn (unAstNoVectorizeWrap a)
                    (unAstNoVectorize2 . f . noVectorizeHVector)
  rletHFunIn a f = astNoVectorize2 $ rletHFunIn a (unAstNoVectorize2 . f)
  rfromS = astNoVectorize2 . rfromS . unAstNoVectorizeS2
  rconstant = astNoVectorize2 . rconstant . unAstNoVectorize2
  rprimalPart = astNoVectorize2 . rprimalPart . unAstNoVectorize2
  rdualPart = astNoVectorize2 . rdualPart . unAstNoVectorize2
  rD u u' = astNoVectorize2 $ rD (unAstNoVectorize2 u) (unAstNoVectorize2 u')
  rScale s t = astNoVectorize2 $ rScale @(AstRanked s)
                                       (unAstNoVectorize2 s) (unAstNoVectorize2 t)

unAstNoVectorize2 :: AstNoVectorize s r n -> AstRanked s r n
unAstNoVectorize2 = AstRanked . unAstNoVectorize

astNoVectorize2 :: AstRanked s r n -> AstNoVectorize s r n
astNoVectorize2 = AstNoVectorize . unAstRanked

instance AstSpan s => ShapedTensor (AstNoVectorizeS s) where
  sletTKIn :: forall y sh r.
              (TensorKind y, KnownShS sh, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstNoVectorize s) y
           -> (InterpretationTarget (AstNoVectorize s) y -> AstNoVectorizeS s r sh)
           -> AstNoVectorizeS s r sh
  sletTKIn stk a f =
    AstNoVectorizeS
    $ astLetFun @y @_ @s
                (unNoVectorizeY stk a) (unAstNoVectorizeS . f . noVectorizeY stk)
  sminIndex = astNoVectorizeS2 . sminIndex . unAstNoVectorizeS2
  smaxIndex = astNoVectorizeS2 . smaxIndex . unAstNoVectorizeS2
  sfloor = astNoVectorizeS2 . sfloor . unAstNoVectorizeS2
  siota = astNoVectorizeS2 siota
  sindex v ix =
    astNoVectorizeS2 $ sindex (unAstNoVectorizeS2 v) ((AstRanked . unAstNoVectorize) <$> ix)
  ssum = astNoVectorizeS2 . ssum . unAstNoVectorizeS2
  sscatter t f = astNoVectorizeS2 $ sscatter (unAstNoVectorizeS2 t)
                 $ fmap (AstRanked . unAstNoVectorize) . f . fmap astNoVectorize2
  sfromVector = astNoVectorizeS2 . sfromVector . V.map unAstNoVectorizeS2
  sreplicate = astNoVectorizeS2 . sreplicate . unAstNoVectorizeS2
  sappend u v =
    astNoVectorizeS2 $ sappend (unAstNoVectorizeS2 u) (unAstNoVectorizeS2 v)
  sslice proxy1 proxy2 =
    astNoVectorizeS2 . sslice proxy1 proxy2 . unAstNoVectorizeS2
  sreverse = astNoVectorizeS2 . sreverse . unAstNoVectorizeS2
  stranspose perm =
    astNoVectorizeS2 . stranspose perm . unAstNoVectorizeS2
  sreshape = astNoVectorizeS2 . sreshape . unAstNoVectorizeS2
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (AstNoVectorizeS s) -> AstNoVectorizeS s r sh)
          -> AstNoVectorizeS s r (n ': sh)
  sbuild1 f = AstNoVectorizeS $ AstBuild1 (SNat @n)
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorizeS . f . AstNoVectorize
  sgather t f = astNoVectorizeS2 $ sgather (unAstNoVectorizeS2 t)
                $ fmap (AstRanked . unAstNoVectorize) . f . fmap astNoVectorize2
  scast = astNoVectorizeS2 . scast . unAstNoVectorizeS2
  sfromIntegral = astNoVectorizeS2 . sfromIntegral . unAstNoVectorizeS2
  sconst = astNoVectorizeS2 . sconst
  sletHVectorIn a f =
    astNoVectorizeS2
    $ sletHVectorIn (unAstNoVectorizeWrap a)
                    (unAstNoVectorizeS2 . f . noVectorizeHVector)
  sletHFunIn a f = astNoVectorizeS2 $ sletHFunIn a (unAstNoVectorizeS2 . f)
  sfromR = astNoVectorizeS2 . sfromR . AstRanked . unAstNoVectorize
  sconstant = astNoVectorizeS2 . sconstant . unAstNoVectorizeS2
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  sprimalPart = astNoVectorizeS2 . sprimalPart . unAstNoVectorizeS2
  sdualPart = astNoVectorizeS2 . sdualPart . unAstNoVectorizeS2
  sD u u' =
    astNoVectorizeS2 $ sD  (unAstNoVectorizeS2 u) (unAstNoVectorizeS2 u')
  sScale s t =
    astNoVectorizeS2 $ sScale @(AstShaped s)
                             (unAstNoVectorizeS2 s) (unAstNoVectorizeS2 t)

unAstNoVectorizeS2 :: AstNoVectorizeS s r sh -> AstShaped s r sh
unAstNoVectorizeS2 = AstShaped . unAstNoVectorizeS

astNoVectorizeS2 :: AstShaped s r sh -> AstNoVectorizeS s r sh
astNoVectorizeS2 = AstNoVectorizeS . unAstShaped

instance AstSpan s => HVectorTensor (AstNoVectorize s) (AstNoVectorizeS s) where
  dshape = dshape . unAstNoVectorizeWrap
  tshapeFull stk t = case stk of
    STKR{} -> shapeAstFull $ unAstNoVectorize t
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (tproject1 t))
                                       (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
  dmkHVector =
    AstNoVectorizeWrap . AstMkHVector . unNoVectorizeHVector
  dlambda = dlambda @(AstRanked s)
  dHApply :: forall x y. (TensorKind x, TensorKind y)
          => HFunOf (AstNoVectorize s) x y
          -> InterpretationTarget (AstNoVectorize s) x
          -> InterpretationTarget (AstNoVectorize s) y
  dHApply t ll = noVectorizeY (stensorKind @y) $ astHApply t
                 $ unNoVectorizeY (stensorKind @x) $ ll
  dunHVector =
    noVectorizeHVector . dunHVector . unAstNoVectorizeWrap
  dletHVectorInHVector a f =
    AstNoVectorizeWrap
    $ dletHVectorInHVector (unAstNoVectorizeWrap a)
                           (unAstNoVectorizeWrap . f . noVectorizeHVector)
  dletHFunInHVector t f =
    AstNoVectorizeWrap
    $ dletHFunInHVector t (unAstNoVectorizeWrap . f)
  dlet :: forall y. TensorKind y
       => InterpretationTarget (AstNoVectorize s) y
       -> (InterpretationTarget (AstNoVectorize s) y
           -> HVectorOf (AstNoVectorize s))
       -> HVectorOf (AstNoVectorize s)
  dlet u f = case stensorKind @y of
    STKR{} -> AstNoVectorizeWrap
              $ dlet (unAstNoVectorize2 u)
                     (unAstNoVectorizeWrap . f . astNoVectorize2)
    STKS{} -> AstNoVectorizeWrap
              $ dlet (unAstNoVectorizeS2 u)
                     (unAstNoVectorizeWrap . f . astNoVectorizeS2)
    STKProduct{} -> error "TODO"
    STKUntyped{} -> error "TODO"
  dbuild1 k f =
    AstNoVectorizeWrap
    $ AstBuildHVector1 k $ funToAstI (unAstNoVectorizeWrap . f . AstNoVectorize)
  rrev f parameters0 hVector =
    AstNoVectorizeWrap
    $ rrev f parameters0 (unNoVectorizeHVector hVector)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ k accShs bShs eShs f df rf acc0 es =
    AstNoVectorizeWrap
    $ dmapAccumRDer (Proxy @(AstRanked s))
                    k accShs bShs eShs f df rf (unAstNoVectorizeWrap acc0)
                                               (unAstNoVectorizeWrap es)
  dmapAccumLDer _ k accShs bShs eShs f df rf acc0 es =
    AstNoVectorizeWrap
    $ dmapAccumLDer (Proxy @(AstRanked s))
                    k accShs bShs eShs f df rf (unAstNoVectorizeWrap acc0)
                                               (unAstNoVectorizeWrap es)

unNoVectorizeHVector :: HVector (AstNoVectorize s) -> HVector (AstRanked s)
unNoVectorizeHVector =
  let f (DynamicRanked (AstNoVectorize t)) = DynamicRanked (AstRanked t)
      f (DynamicShaped (AstNoVectorizeS t)) = DynamicShaped (AstShaped t)
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noVectorizeHVector :: HVector (AstRanked s) -> HVector (AstNoVectorize s)
noVectorizeHVector =
  let f (DynamicRanked (AstRanked t)) = DynamicRanked $ AstNoVectorize t
      f (DynamicShaped (AstShaped t)) = DynamicShaped $ AstNoVectorizeS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

instance ProductTensor (AstNoSimplify s) where
  tmkHVector = AstNoSimplifyWrap . AstMkHVector . unNoSimplifyHVector

noSimplifyY :: forall y s.
           STensorKindType y -> AstTensor s y
        -> InterpretationTarget (AstNoSimplify s) y
noSimplifyY stk t = case stk of
  STKR{} -> AstNoSimplify t
  STKS{} -> AstNoSimplifyS t
  STKProduct stk1 stk2 ->
    ttuple (noSimplifyY stk1 $ AstProject1 t) (noSimplifyY stk2 $ AstProject2 t)
  STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap t

unNoSimplifyY :: forall y s.
             STensorKindType y -> InterpretationTarget (AstNoSimplify s) y
          -> AstTensor s y
unNoSimplifyY stk t = case stk of
  STKR{} -> unAstNoSimplify t
  STKS{} -> unAstNoSimplifyS t
  STKProduct stk1 stk2 -> AstTuple (unNoSimplifyY stk1 $ tproject1 t)
                                   (unNoSimplifyY stk2 $ tproject2 t)
  STKUntyped -> unAstNoSimplifyWrap $ unHVectorPseudoTensor t

instance AstSpan s => RankedTensor (AstNoSimplify s) where
  rletTKIn :: forall y n r. (TensorKind y, KnownNat n, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstNoSimplify s) y
           -> (InterpretationTarget (AstNoSimplify s) y -> AstNoSimplify s r n)
           -> AstNoSimplify s r n
  rletTKIn stk a f =
    AstNoSimplify
    $ astLetFunRaw @y @_ @s
                   (unNoSimplifyY stk a) (unAstNoSimplify . f . noSimplifyY stk)
  rshape = shapeAst . unAstNoSimplify
  rminIndex = AstNoSimplify . fromPrimal . AstMinIndex
              . astSpanPrimal . unAstNoSimplify
  rmaxIndex = AstNoSimplify . fromPrimal . AstMaxIndex
              . astSpanPrimal . unAstNoSimplify
  rfloor = AstNoSimplify . fromPrimal . AstFloor
           . astSpanPrimal . unAstNoSimplify
  riota = AstNoSimplify . fromPrimal $ AstIota
  rindex v ix =
    AstNoSimplify $ AstIndex (unAstNoSimplify v) (unAstNoSimplify <$> ix)
  rsum = AstNoSimplify . AstSum . unAstNoSimplify
  rscatter sh t f = AstNoSimplify $ AstScatter sh (unAstNoSimplify t)
                    $ funToAstIndex
                        (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                          -- this introduces new variable names
  rfromVector = AstNoSimplify . AstFromVector . V.map unAstNoSimplify
  rreplicate k = withSNat k $ \snat ->
    AstNoSimplify . AstReplicate snat . unAstNoSimplify
  rappend u v =
    AstNoSimplify $ AstAppend (unAstNoSimplify u) (unAstNoSimplify v)
  rslice i n = AstNoSimplify . AstSlice i n . unAstNoSimplify
  rreverse = AstNoSimplify . AstReverse . unAstNoSimplify
  rtranspose perm = AstNoSimplify . AstTranspose perm . unAstNoSimplify
  rreshape sh = AstNoSimplify . AstReshape sh . unAstNoSimplify
  rbuild1 k f =
    AstNoSimplify $ astBuild1Vectorize k (unAstNoSimplify . f . AstNoSimplify)
  rgather sh t f = AstNoSimplify $ AstGather sh (unAstNoSimplify t)
                   $ funToAstIndex
                       (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                         -- this introduces new variable names
  rcast = AstNoSimplify . AstCast . unAstNoSimplify
  rfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegral
                  . astSpanPrimal . unAstNoSimplify
  rconst = AstNoSimplify . fromPrimal . AstConst
  rletHVectorIn a f =
    AstNoSimplify
    $ astLetHVectorInFunRaw (unAstNoSimplifyWrap a)
                            (unAstNoSimplify . f . noSimplifyHVector)
  rletHFunIn a f = AstNoSimplify $ astLetHFunInFunRaw a (unAstNoSimplify . f)
  rfromS = AstNoSimplify . AstRFromS . unAstNoSimplifyS
  rconstant = AstNoSimplify . fromPrimal . unAstNoSimplify
  rprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  rdualPart = AstNoSimplify . astSpanDual . unAstNoSimplify
  rD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) (unAstNoSimplify u')
  rScale s t = AstNoSimplify $ astDualPart
               $ AstConstant (unAstNoSimplify s)
                 * AstD (unAstRanked $ rzero (rshape s)) (unAstNoSimplify t)

instance AstSpan s => ShapedTensor (AstNoSimplifyS s) where
  sletTKIn :: forall y sh r. (TensorKind y, GoodScalar r, KnownShS sh)
           => STensorKindType y -> InterpretationTarget (AstNoSimplify s) y
           -> (InterpretationTarget (AstNoSimplify s) y -> AstNoSimplifyS s r sh)
           -> AstNoSimplifyS s r sh
  sletTKIn stk a f =
    AstNoSimplifyS
    $ astLetFunRaw @y @_ @s
                   (unNoSimplifyY stk a) (unAstNoSimplifyS . f . noSimplifyY stk)
  sminIndex = AstNoSimplifyS . fromPrimal . AstMinIndexS
              . astSpanPrimal . unAstNoSimplifyS
  smaxIndex = AstNoSimplifyS . fromPrimal . AstMaxIndexS
              . astSpanPrimal . unAstNoSimplifyS
  sfloor = AstNoSimplifyS . fromPrimal . AstFloorS
           . astSpanPrimal . unAstNoSimplifyS
  siota = AstNoSimplifyS . fromPrimal $ AstIotaS
  sindex v ix =
    AstNoSimplifyS $ AstIndexS (unAstNoSimplifyS v) (unAstNoSimplify <$> ix)
  ssum = AstNoSimplifyS . AstSumS . unAstNoSimplifyS
  sscatter t f = AstNoSimplifyS $ AstScatterS (unAstNoSimplifyS t)
                 $ funToAstIndexS
                     (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                       -- this introduces new variable names
  sfromVector = AstNoSimplifyS . AstFromVectorS . V.map unAstNoSimplifyS
  sreplicate = AstNoSimplifyS . AstReplicate SNat . unAstNoSimplifyS
  sappend u v =
    AstNoSimplifyS $ AstAppendS (unAstNoSimplifyS u) (unAstNoSimplifyS v)
  sslice (_ :: Proxy i) Proxy = AstNoSimplifyS . AstSliceS @i . unAstNoSimplifyS
  sreverse = AstNoSimplifyS . AstReverseS . unAstNoSimplifyS
  stranspose perm =
    AstNoSimplifyS . AstTransposeS perm . unAstNoSimplifyS
  sreshape = AstNoSimplifyS . AstReshapeS . unAstNoSimplifyS
  sbuild1 f =
    AstNoSimplifyS
    $ astBuild1VectorizeS (unAstNoSimplifyS . f . AstNoSimplify)
  sgather t f = AstNoSimplifyS $ AstGatherS (unAstNoSimplifyS t)
                $ funToAstIndexS
                    (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                      -- this introduces new variable names
  scast = AstNoSimplifyS . AstCastS . unAstNoSimplifyS
  sfromIntegral = AstNoSimplifyS . fromPrimal . AstFromIntegralS
                  . astSpanPrimal . unAstNoSimplifyS
  sconst = AstNoSimplifyS . fromPrimal . AstConstS
  sletHVectorIn a f =
    AstNoSimplifyS
    $ astLetHVectorInFunRawS (unAstNoSimplifyWrap a)
                             (unAstNoSimplifyS . f . noSimplifyHVector)
  sletHFunIn a f = AstNoSimplifyS $ astLetHFunInFunRawS a (unAstNoSimplifyS . f)
  sfromR = AstNoSimplifyS . AstSFromR . unAstNoSimplify
  sconstant = AstNoSimplifyS . fromPrimal . unAstNoSimplifyS
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  sprimalPart = AstNoSimplifyS . astSpanPrimal . unAstNoSimplifyS
  sdualPart = AstNoSimplifyS . astSpanDual . unAstNoSimplifyS
  sD u u' =
    AstNoSimplifyS $ astSpanD (unAstNoSimplifyS u) (unAstNoSimplifyS u')
  sScale :: forall r sh. (GoodScalar r, KnownShS sh)
         => AstNoSimplifyS PrimalSpan r sh -> AstNoSimplifyS DualSpan r sh
         -> AstNoSimplifyS DualSpan r sh
  sScale s t =
    AstNoSimplifyS $ astDualPart
                   $ AstConstant (unAstNoSimplifyS s)
                     * AstD 0 (unAstNoSimplifyS t)

instance AstSpan s => HVectorTensor (AstNoSimplify s) (AstNoSimplifyS s) where
  dshape = shapeAstHVector . unAstNoSimplifyWrap
  tshapeFull stk t = case stk of
    STKR{} -> shapeAstFull $ unAstNoSimplify t
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (tproject1 t))
                                       (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t
  dmkHVector =
    AstNoSimplifyWrap . AstMkHVector . unNoSimplifyHVector
  dlambda :: forall x y. (TensorKind x, TensorKind y)
          => TensorKindFull x -> HFun x y -> HFunOf (AstNoSimplify s) x y
  dlambda shss f =
    let (var, ast) = funToAst shss $ \ !ll ->
          unRankedY (stensorKind @y) $ unHFun f $ rankedY (stensorKind @x) ll
    in AstLambda (var, shss, ast)
  dHApply :: forall x y. (TensorKind x, TensorKind y)
          => HFunOf (AstNoSimplify s) x y
          -> InterpretationTarget (AstNoSimplify s) x
          -> InterpretationTarget (AstNoSimplify s) y
  dHApply t ll =
    let app = AstHApply t $ unNoSimplifyY (stensorKind @x) ll
    in noSimplifyY (stensorKind @y) app
  dunHVector (AstNoSimplifyWrap (AstMkHVector l)) = noSimplifyHVector l
  dunHVector (AstNoSimplifyWrap hVectorOf) =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstRanked $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstShaped $ AstProjectS hVectorOf i
    in noSimplifyHVector
       $ V.imap f $ shapeAstHVector hVectorOf
  dletHVectorInHVector a f =
    AstNoSimplifyWrap
    $ astLetHVectorInHVectorFunRaw (unAstNoSimplifyWrap a)
                                   (unAstNoSimplifyWrap . f . noSimplifyHVector)
  dletHFunInHVector t f =
    AstNoSimplifyWrap
    $ astLetHFunInHVectorFunRaw t (unAstNoSimplifyWrap . f)
  dlet :: forall y. TensorKind y
       => InterpretationTarget (AstNoSimplify s) y
       -> (InterpretationTarget (AstNoSimplify s) y -> HVectorOf (AstNoSimplify s))
       -> HVectorOf (AstNoSimplify s)
  dlet u f = case stensorKind @y of
    STKR{} -> AstNoSimplifyWrap
              $ astLetFunRaw (unAstNoSimplify u)
                             (unAstNoSimplifyWrap . f . AstNoSimplify)
    STKS{} -> AstNoSimplifyWrap
              $ astLetFunRaw (unAstNoSimplifyS u)
                             (unAstNoSimplifyWrap . f . AstNoSimplifyS)
    STKProduct{} -> error "TODO"
    STKUntyped{} -> error "TODO"
  dbuild1 k f = AstNoSimplifyWrap
                $ astBuildHVector1Vectorize
                    k (unAstNoSimplifyWrap . f . AstNoSimplify)
  rrev f parameters0 hVector =  -- we don't have an AST constructor to hold it
    AstNoSimplifyWrap
    $ rrev f parameters0 (unNoSimplifyHVector hVector)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ k accShs bShs eShs f df rf acc0 es =
    AstNoSimplifyWrap
    $ AstMapAccumRDer k accShs bShs eShs f df rf (unAstNoSimplifyWrap acc0)
                                                 (unAstNoSimplifyWrap es)
  dmapAccumLDer _ k accShs bShs eShs f df rf acc0 es =
    AstNoSimplifyWrap
    $ AstMapAccumLDer k accShs bShs eShs f df rf (unAstNoSimplifyWrap acc0)
                                                 (unAstNoSimplifyWrap es)

unNoSimplifyHVector :: HVector (AstNoSimplify s) -> HVector (AstRanked s)
unNoSimplifyHVector =
  let f (DynamicRanked (AstNoSimplify t)) = DynamicRanked $ AstRanked t
      f (DynamicShaped (AstNoSimplifyS t)) = DynamicShaped (AstShaped t)
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noSimplifyHVector :: HVector (AstRanked s) -> HVector (AstNoSimplify s)
noSimplifyHVector =
  let f (DynamicRanked (AstRanked t)) = DynamicRanked $ AstNoSimplify t
      f (DynamicShaped (AstShaped t)) = DynamicShaped $ AstNoSimplifyS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f
