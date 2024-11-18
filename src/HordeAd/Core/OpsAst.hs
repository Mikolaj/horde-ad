{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for AST terms. Most of these instances
-- vectorize any terms starting with the build constructor.
-- The AST term instances can be used as building blocks for 'ADVal'
-- instances defined in "TensorADVal" but may also be used standalone.
module HordeAd.Core.OpsAst
  ( forwardPassByInterpretation
  , revArtifactFromForwardPass
  , revProduceArtifact
  , fwdArtifactFromForwardPass, fwdProduceArtifact
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty
  ) where

import Prelude

import Data.IntMap.Strict (IntMap)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat)

import Data.Array.Nested (IShR, KnownShS (..))

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInline
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.AstVectorize
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersAst
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.OpsADVal (unADValRep)
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.SizedList

-- * Symbolic reverse and forward derivative computation

forwardPassByInterpretation
  :: forall x z. TensorKind x
  => (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw PrimalSpan) z
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit hVectorPrimal var hVector =
  let deltaInputs = generateDeltaInputs $ ftkAst hVectorPrimal
      varInputs = makeADInputs (AstRaw hVectorPrimal) deltaInputs
      ast = g hVector
      env = extendEnv var varInputs envInit
  in interpretAst env ast

revArtifactFromForwardPass
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullTensorKind x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass hasDt forwardPass ftk
 | Dict <- lemTensorKindOfAD (stensorKind @x)
 , Dict <- lemTensorKindOfAD (stensorKind @z) =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varPrimal, hVectorPrimal, var, hVector) = funToAstRev ftk in
  let -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(!primalBody, !delta) =
        unADValRep (stensorKind @z)
        $ forwardPass hVectorPrimal var hVector in
  let (!varDt, !astDt) =
        funToAst (aDTensorKind $ ftkAst $ unAstRaw primalBody) id in
  let mdt = if hasDt
            then Just astDt
            else Nothing
      !gradient = gradientFromDelta ftk primalBody (AstRaw <$> mdt) delta
      !unGradient = unshareAstTensor $ unAstRaw gradient
      !unPrimal = unshareAstTensor $ unAstRaw primalBody
  in ( AstArtifactRev varDt varPrimal unGradient unPrimal
     , delta )

revProduceArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullTensorKind x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifact #-}
revProduceArtifact hasDt g envInit =
  revArtifactFromForwardPass hasDt (forwardPassByInterpretation g envInit)

fwdArtifactFromForwardPass
  :: forall x z. (TensorKind x, TensorKind z)
  => (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullTensorKind x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass ftk
 | Dict <- lemTensorKindOfAD (stensorKind @x)
 , Dict <- lemTensorKindOfAD (stensorKind @z) =
  let !(!varPrimalD, hVectorD, varPrimal, hVectorPrimal, var, hVector) =
        funToAstFwd ftk in
  let !(!primalBody, !delta) =
        unADValRep (stensorKind @z)
        $ forwardPass hVectorPrimal var hVector in
  let !derivative = derivativeFromDelta @x delta (AstRaw hVectorD)
      !unDerivative = unshareAstTensor $ unAstRaw derivative
      !unPrimal = unshareAstTensor $ unAstRaw primalBody
  in ( AstArtifactFwd varPrimalD varPrimal unDerivative unPrimal
     , delta )

fwdProduceArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullTensorKind x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdProduceArtifact #-}
fwdProduceArtifact f envInit =
  fwdArtifactFromForwardPass (forwardPassByInterpretation f envInit)


-- * AstTensor instances

-- These boolean instances are unlawful; they are lawful modulo evaluation.

type instance BoolOf (AstTensor AstMethodLet s) = AstBool AstMethodLet

instance IfF (AstTensor AstMethodLet s) where
  ifF cond a b = astCond cond a b

instance AstSpan s => EqF (AstTensor AstMethodLet s) where
  AstConcrete u ==. AstConcrete v = AstBoolConst $ u == v
    -- common in indexing
  v ==. u = AstRel EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstConcrete u /=. AstConcrete v = AstBoolConst $ u /= v
    -- common in indexing
  v /=. u = AstRel NeqOp (astSpanPrimal v) (astSpanPrimal u)

instance AstSpan s => OrdF (AstTensor AstMethodLet s) where
  AstConcrete u <. AstConcrete v = AstBoolConst $ u < v
    -- common in indexing
  v <. u = AstRel LsOp (astSpanPrimal v) (astSpanPrimal u)
  AstConcrete u <=. AstConcrete v = AstBoolConst $ u <= v
    -- common in indexing
  v <=. u = AstRel LeqOp (astSpanPrimal v) (astSpanPrimal u)
  AstConcrete u >. AstConcrete v = AstBoolConst $ u > v
    -- common in indexing
  v >. u = AstRel GtOp (astSpanPrimal v) (astSpanPrimal u)
  AstConcrete u >=. AstConcrete v = AstBoolConst $ u >= v
    -- common in indexing
  v >=. u = AstRel GeqOp (astSpanPrimal v) (astSpanPrimal u)


instance (GoodScalar r, KnownNat n, BaseTensor (AstTensor AstMethodLet s))
         => AdaptableHVector (AstTensor AstMethodLet s) (AstTensor AstMethodLet s (TKR n r)) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstTensor AstMethodLet s) (AstTensor AstMethodLet s (TKR n Double)) #-}
  type X (AstTensor AstMethodLet s (TKR n r)) = TKR n r
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKR n r)) =
    case sameTensorKind @(TKR n r) @(ADTensorKind (TKR n r)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (rzero (rshape aInit), Nothing)

instance (GoodScalar r, KnownShS sh, BaseTensor (AstTensor AstMethodLet s))
         => AdaptableHVector (AstTensor AstMethodLet s) (AstTensor AstMethodLet s (TKS sh r)) where
  type X (AstTensor AstMethodLet s (TKS sh r)) = TKS sh r
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD _aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKS sh r)) =
    case sameTensorKind @(TKS sh r) @(ADTensorKind (TKS sh r)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (srepl 0, Nothing)

instance (GoodScalar r, KnownNat n, BaseTensor (AstTensor AstMethodLet s), AstSpan s)
         => AdaptableHVector (AstTensor AstMethodLet s) (AsHVector (AstTensor AstMethodLet s (TKR n r))) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstTensor AstMethodLet s) (AsHVector (AstTensor AstMethodLet s (TKR n Double))) #-}
  type X (AsHVector (AstTensor AstMethodLet s (TKR n r))) = TKUntyped
  toHVectorOf = dmkHVector . V.singleton . DynamicRanked . unAsHVector
  fromHVector _aInit params =  -- TODO: tlet params $ \ !params1 ->
    case V.uncons $ dunHVector params of
      Just (dynamic, rest) ->
        Just (AsHVector $ fromDynamicR rzero dynamic, Just $ dmkHVector rest)
      Nothing -> Nothing

instance (GoodScalar r, KnownShS sh, BaseTensor (AstTensor AstMethodLet s), AstSpan s)
         => AdaptableHVector (AstTensor AstMethodLet s) (AsHVector (AstTensor AstMethodLet s (TKS sh r))) where
  type X (AsHVector (AstTensor AstMethodLet s (TKS sh r))) = TKUntyped
  toHVectorOf = dmkHVector . V.singleton . DynamicShaped . unAsHVector
  fromHVector _aInit params =  -- TODO: tlet params $ \ !params1 ->
    case V.uncons $ dunHVector params of
      Just (dynamic, rest) ->
        Just (AsHVector $ fromDynamicS (srepl 0) dynamic, Just $ dmkHVector rest)
      Nothing -> Nothing

instance (GoodScalar r, KnownNat n, AstSpan s)
         => DualNumberValue (AstTensor AstMethodLet s (TKR n r)) where
  type DValue (AstTensor AstMethodLet s (TKR n r)) = RepN (TKR n r)
  fromDValue t = fromPrimal $ AstConcrete $ unRepN t

instance (GoodScalar r, KnownShS sh, AstSpan s)
         => DualNumberValue (AstTensor AstMethodLet s (TKS sh r)) where
  type DValue (AstTensor AstMethodLet s (TKS sh r)) = RepN (TKS sh r)
  fromDValue t = fromPrimal $ AstConcreteS $ unRepN t

instance (GoodScalar r, KnownNat n)
         => TermValue (AstTensor AstMethodLet FullSpan (TKR n r)) where
  type Value (AstTensor AstMethodLet FullSpan (TKR n r)) = RepN (TKR n r)
  fromValue t = fromPrimal $ AstConcrete $ unRepN t

instance (GoodScalar r, KnownShS sh)
         => TermValue (AstTensor AstMethodLet FullSpan (TKS sh r)) where
  type Value (AstTensor AstMethodLet FullSpan (TKS sh r)) = RepN (TKS sh r)
  fromValue t = fromPrimal $ AstConcreteS $ unRepN t

{- This is needed by only one test, testSin0revhFold5S, now disabled
and this possibly breaks the cfwdOnHVector duplicability invariant in cfwd.
Analyze and, if possible, remove together with toHVectorOf.
instance AdaptableHVector (AstTensor AstMethodLet s) (AstTensor AstMethodLet s TKUntyped) where
  toHVectorOf = undefined  -- impossible without losing sharing
  toHVectorOf = id  -- but this is possible
  fromHVector aInit params =
    let (portion, rest) = V.splitAt (V.length $ shapeAstHVector aInit) params
    in Just (AstMkHVector $ unRankedHVector portion, rest)

instance (BaseTensor (AstTensor AstMethodLet s), AstSpan s)
         => AdaptableHVector (AstTensor AstMethodLet s) (DynamicTensor (AstTensor AstMethodLet s)) where
  toHVectorOf = rankedHVector . V.singleton
  fromHVector _aInit hv = case V.uncons $ unRankedHVector hv of
    Nothing -> Nothing
    Just (generic, rest) ->
      Just (generic, rankedHVector rest)

instance TermValue (HVectorPseudoTensor (AstRanked FullSpan) r y) where
  type Value (HVectorPseudoTensor (AstRanked FullSpan) r y) =
    HVectorPseudoTensor RepN r y
  fromValue (HVectorPseudoTensor t) =
    AstMkHVector $ V.map fromValue t
-}

astSpanPrimal :: forall s y. (AstSpan s, TensorKind y)
              => AstTensor AstMethodLet s y
              -> AstTensor AstMethodLet PrimalSpan y
astSpanPrimal t | Just Refl <- sameAstSpan @s @PrimalSpan = t
astSpanPrimal _ | Just Refl <- sameAstSpan @s @DualSpan =
  error "astSpanPrimal: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimal t | Just Refl <- sameAstSpan @s @FullSpan = astPrimalPart t
astSpanPrimal _ = error "a spuriuos case for pattern match coverage"

astSpanDual :: forall s y. (AstSpan s, TensorKind y)
            => AstTensor AstMethodLet s y -> AstTensor AstMethodLet DualSpan y
astSpanDual t | Just Refl <- sameAstSpan @s @PrimalSpan =
  AstDualPart $ AstFromPrimal t  -- this is nil; likely to happen
astSpanDual t | Just Refl <- sameAstSpan @s @DualSpan = t
astSpanDual t | Just Refl <- sameAstSpan @s @FullSpan = astDualPart t
astSpanDual _ = error "a spuriuos case for pattern match coverage"

astSpanD :: forall s y ms. (AstSpan s, TensorKind y)
         => AstTensor ms PrimalSpan y -> AstTensor ms DualSpan y
         -> AstTensor ms s y
astSpanD u _ | Just Refl <- sameAstSpan @s @PrimalSpan = u
astSpanD _ u' | Just Refl <- sameAstSpan @s @DualSpan = u'
astSpanD u u' | Just Refl <- sameAstSpan @s @FullSpan = AstD u u'
astSpanD _ _ = error "a spuriuos case for pattern match coverage"

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize
  :: (AstSpan s, TensorKind z)
  => SNat k -> (AstInt AstMethodLet -> AstTensor AstMethodLet s z)
  -> AstTensor AstMethodLet s (BuildTensorKind k z)
astBuild1Vectorize k f = build1Vectorize k $ funToAstI f

{-
-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: FullTensorKind TKUntyped
  -> HVectorPseudoTensor (AstRaw PrimalSpan) Float '()
  -> Maybe (HVectorPseudoTensor (AstRaw PrimalSpan) Float '())
  -> Delta (AstRaw PrimalSpan) TKUntyped
  -> AstRaw PrimalSpan TKUntyped #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (AstRaw PrimalSpan) -> EvalState (AstRaw PrimalSpan) #-}
-}

instance AstSpan s => LetTensor (AstTensor AstMethodLet s) where
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => AstTensor AstMethodLet s x
       -> (AstTensor AstMethodLet s x -> AstTensor AstMethodLet s z)
       -> AstTensor AstMethodLet s z
  tlet u f = astLetFun u f

  toShare :: AstTensor AstMethodLet s y
          -> AstRaw s y
  toShare t = AstRaw $ AstToShare t
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tunshare :: forall y. TensorKind y
           => AstRaw s y
           -> AstTensor AstMethodLet s y
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unshareAstTensor . unAstRaw
      _ -> error "tunshare: used not at PrimalSpan"

instance AstSpan s => BaseTensor (AstTensor AstMethodLet s) where
  rmkRepScalar = AstUnScalar
  runRepScalar = AstScalar

  rshape = shapeAst
  rminIndex = fromPrimal . AstMinIndex
              . astSpanPrimal
  rmaxIndex = fromPrimal . AstMaxIndex
              . astSpanPrimal
  rfloor = fromPrimal . AstFloor
           . astSpanPrimal

  riota = fromPrimal $ AstIota
  rindex v ix = astIndexStep v ix
  rsum = astSum
  rscatter sh t f = astScatter sh t
                    $ funToAstIndex f
                          -- this introduces new variable names

  rfromVector = astFromVector
  rreplicate k = withSNat k $ \snat ->
    astReplicate snat
  rappend u v =
    astAppend u v
  rslice i n = astSlice i n
  rreverse = astReverse
  rtranspose perm = astTranspose perm
  rreshape sh = astReshape sh
  rbuild1 k f = withSNat k $ \snat ->
    astBuild1Vectorize snat f
  rgather sh t f = astGatherStep sh t
                   $ funToAstIndex f
                         -- this introduces new variable names
  rcast = astCast
  rfromIntegral =
    fromPrimal . astFromIntegral . astSpanPrimal
  rconcrete = fromPrimal . AstConcrete
  rfromS = astRFromS

  rfromPrimal = fromPrimal
  rprimalPart = astSpanPrimal
  rdualPart = astSpanDual
  rD u u' = astSpanD u u'
  rScale s t = astDualPart $ AstFromPrimal s * AstD (rzero (rshape s)) t

  xshape t = case ftkAst t of
    FTKX sh -> sh
  xindex v ix = AstIndexX v ix
  xfromVector = AstFromVectorX
  xreplicate = AstReplicate SNat
  xconcrete = fromPrimal . AstConcreteX
  xfromPrimal = fromPrimal
  xprimalPart = astSpanPrimal
  xdualPart = astSpanDual
  xD u u' = astSpanD u u'

  sminIndex = fromPrimal . AstMinIndexS . astSpanPrimal
  smaxIndex = fromPrimal . AstMaxIndexS . astSpanPrimal
  sfloor = fromPrimal . AstFloorS . astSpanPrimal

  siota = fromPrimal $ AstIotaS
  sindex v ix =
    astIndexStepS v ix
  ssum = astSumS
  sscatter t f = astScatterS t
                 $ funToAstIxS f
                       -- this introduces new variable names

  sfromVector = astFromVectorS
  sreplicate = astReplicate SNat
  sappend u v = astAppendS u v
  sslice (_ :: Proxy i) Proxy = astSliceS @i
  sreverse = astReverseS
  stranspose perm = astTransposeS perm
  sreshape = astReshapeS
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (AstTensor AstMethodLet s) -> AstTensor AstMethodLet s (TKS sh r))
          -> AstTensor AstMethodLet s (TKS (n ': sh) r)
  sbuild1 f =
    astBuild1Vectorize (SNat @n) f
  sgather t f = astGatherStepS t
                $ funToAstIxS f
                      -- this introduces new variable names
  scast = astCastS
  sfromIntegral = fromPrimal . astFromIntegralS . astSpanPrimal
  sconcrete = fromPrimal . AstConcreteS
  sfromR = astSFromR

  sfromPrimal = fromPrimal
  sprimalPart = astSpanPrimal
  sdualPart = astSpanDual
  sD u u' = astSpanD u u'
  sScale s t = astDualPart $ AstFromPrimal s * AstD 0 t

  tpair t1 t2 = astPair t1 t2
  tproject1 = astProject1
  tproject2 = astProject2
  dshape = shapeAstHVector
  tftk stk t | Dict <- lemTensorKindOfS stk = ftkAst t
  tcond stk b u v | Dict <- lemTensorKindOfS stk = AstCond b u v
  tfromPrimal stk t | Dict <- lemTensorKindOfS stk = fromPrimal t
  tprimalPart stk t | Dict <- lemTensorKindOfS stk = astSpanPrimal t
  tdualPart stk t | Dict <- lemTensorKindOfS stk = astSpanDual t
  tD stk t d | Dict <- lemTensorKindOfS stk = astSpanD t d
  dmkHVector = AstMkHVector
  tlambda :: forall x z. TensorKind x
          => FullTensorKind x -> HFun x z -> HFunOf (AstTensor AstMethodLet s) x z
  tlambda shss f =
    let (var, ast) = funToAst shss $ \ !ll ->
          unHFun f ll
    in AstLambda (var, shss, ast)
  tApply :: forall x z. (TensorKind x, TensorKind z)
          => HFunOf (AstTensor AstMethodLet s) x z
          -> AstTensor AstMethodLet s x
          -> AstTensor AstMethodLet s z
  tApply t ll = astHApply t ll
  dunHVector (AstMkHVector l) = l
  dunHVector hVectorOf =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic AstMethodLet s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstProjectS hVectorOf i
    in V.imap f $ shapeAstHVector hVectorOf
  dbuild1 k f = astBuild1Vectorize k f
  -- TODO: (still) relevant?
  -- In this instance, these three ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstTensor to AstRaw.
  drev :: forall x z. (TensorKind x, TensorKind z)
       => FullTensorKind x
       -> HFun x z
       -> AstHFun x (ADTensorKind x)
  drev ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x) =
    -- we don't have an AST constructor to hold it, so we compute
    --
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let -- No bangs here, because this goes under lambda and may be unneeded
        -- or even incorrect (and so, e.g., trigger
        -- `error "tunshare: used not at PrimalSpan"`, because no derivative
        -- should be taken of spans other than PrimalSpan)
        (AstArtifactRev _varDt var gradient _primal, _delta) =
          revProduceArtifact False (unHFun f) emptyEnv ftkx
        (varP, ast) = funToAst ftkx $ \ !astP ->
          astLet var astP
          $ simplifyInline gradient
    in AstLambda (varP, ftkx, ast)
  drevDt :: forall x z. (TensorKind x, TensorKind z)
         => FullTensorKind x
         -> HFun x z
         -> AstHFun (TKProduct (ADTensorKind z) x) (ADTensorKind x)
  drevDt ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x)
                , Dict <- lemTensorKindOfAD (stensorKind @z) =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactRev varDt var gradient primal, _delta) =
          revProduceArtifact True (unHFun f) emptyEnv ftkx
        ftkz = aDTensorKind $ ftkAst primal
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet varDt (astProject1 astP)
          $ astLet var (astProject2 astP)
          $ simplifyInline gradient
    in AstLambda (varP, ftk2, ast)
  dfwd :: forall x z. (TensorKind x, TensorKind z)
       => FullTensorKind x
       -> HFun x z
       -> AstHFun (TKProduct (ADTensorKind x)  x) (ADTensorKind z)
  dfwd ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x)
              , Dict <- lemTensorKindOfAD (stensorKind @z) =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactFwd varDs var derivative _primal, _delta) =
          fwdProduceArtifact (unHFun f) emptyEnv ftkx
        ftk2 = FTKProduct (aDTensorKind ftkx) ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet varDs (astProject1 astP)
          $ astLet var (astProject2 astP)
          $ simplifyInline derivative
    in AstLambda (varP, ftk2, ast)
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstMapAccumRDer k accShs bShs eShs f df rf acc0 es
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstMapAccumLDer k accShs bShs eShs f df rf acc0 es


-- * The AstRaw instances

astSpanPrimalRaw :: forall s y. (AstSpan s, TensorKind y)
                 => AstTensor AstMethodShare s y -> AstTensor AstMethodShare PrimalSpan y
astSpanPrimalRaw t | Just Refl <- sameAstSpan @s @PrimalSpan = t
astSpanPrimalRaw _ | Just Refl <- sameAstSpan @s @DualSpan =
  error "astSpanPrimalRaw: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimalRaw t | Just Refl <- sameAstSpan @s @FullSpan = AstPrimalPart t
astSpanPrimalRaw _ = error "a spuriuos case for pattern match coverage"

astSpanDualRaw :: forall s y. (AstSpan s, TensorKind y)
               => AstTensor AstMethodShare s y -> AstTensor AstMethodShare DualSpan y
astSpanDualRaw t | Just Refl <- sameAstSpan @s @PrimalSpan =
  AstDualPart $ AstFromPrimal t  -- this is nil; likely to happen
astSpanDualRaw t | Just Refl <- sameAstSpan @s @DualSpan = t
astSpanDualRaw t | Just Refl <- sameAstSpan @s @FullSpan = AstDualPart t
astSpanDualRaw _ = error "a spuriuos case for pattern match coverage"

type instance BoolOf (AstRaw s) = AstBool AstMethodShare

instance IfF (AstRaw s) where
  ifF cond a b = AstRaw $ AstCond cond (unAstRaw a) (unAstRaw b)

instance AstSpan s => EqF (AstRaw s) where
  AstRaw v ==. AstRaw u = AstRel EqOp (astSpanPrimalRaw v) (astSpanPrimalRaw u)
  AstRaw v /=. AstRaw u = AstRel NeqOp (astSpanPrimalRaw v) (astSpanPrimalRaw u)
instance AstSpan s => OrdF (AstRaw s) where
  v <. u = AstRel LsOp (astSpanPrimalRaw (unAstRaw v)) (astSpanPrimalRaw (unAstRaw u))
  v <=. u = AstRel LeqOp (astSpanPrimalRaw (unAstRaw v)) (astSpanPrimalRaw (unAstRaw u))
  v >. u = AstRel GtOp (astSpanPrimalRaw (unAstRaw v)) (astSpanPrimalRaw (unAstRaw u))
  v >=. u = AstRel GeqOp (astSpanPrimalRaw (unAstRaw v)) (astSpanPrimalRaw (unAstRaw u))

deriving instance Eq (AstRaw s y)
deriving instance Ord (AstRaw s y)
deriving instance Num (AstTensor AstMethodShare s y) => Num (AstRaw s y)
deriving instance (IntegralF (AstTensor AstMethodShare s y))
                  => IntegralF (AstRaw s y)
deriving instance Fractional (AstTensor AstMethodShare s y)
                  => Fractional (AstRaw s y)
deriving instance Floating (AstTensor AstMethodShare s y)
                  => Floating (AstRaw s y)
deriving instance (RealFloatF (AstTensor AstMethodShare s y))
                  => RealFloatF (AstRaw s y)

instance AstSpan s => ShareTensor (AstRaw s) where
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tshare :: forall y. TensorKind y
         => AstRaw s y -> AstRaw s y
  tshare t = case unAstRaw t of
    u | astIsSmall True u -> t
    AstShare{} -> t
    AstVar{} -> t
    AstFromPrimal(AstVar{}) -> t
    AstPrimalPart(AstVar{}) -> t
    AstDualPart(AstVar{}) -> t
    u -> AstRaw $ fun1ToAst $ \ !var -> AstShare var u
  tunpair (AstRaw (AstPair t1 t2)) = (AstRaw t1, AstRaw t2)
  tunpair t = let tShared = tshare t
              in (tproject1 tShared, tproject2 tShared)
  tunvector (AstRaw (AstMkHVector l)) = rawHVector l
  tunvector t = dunHVector $ tshare t
  taddShare stk t1 t2 =  -- TODO: remove
    fromRepD $ addRepD (toRepDShare stk t1)
                       (toRepDShare stk t2)

instance AstSpan s => BaseTensor (AstRaw s) where
  rmkRepScalar = AstRaw . AstUnScalar . unAstRaw
  runRepScalar = AstRaw . AstScalar . unAstRaw

  rshape = shapeAst . unAstRaw
  rminIndex = AstRaw . fromPrimal . AstMinIndex . astSpanPrimalRaw . unAstRaw
  rmaxIndex = AstRaw . fromPrimal . AstMaxIndex . astSpanPrimalRaw . unAstRaw
  rfloor = AstRaw . fromPrimal . AstFloor . astSpanPrimalRaw . unAstRaw
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
    AstRaw . fromPrimal . AstFromIntegral . astSpanPrimalRaw . unAstRaw
  rconcrete = AstRaw . fromPrimal . AstConcrete
  rfromS = AstRaw . AstRFromS . unAstRaw

  rfromPrimal = AstRaw . fromPrimal . unAstRaw
  rprimalPart = AstRaw . astSpanPrimalRaw . unAstRaw
  rdualPart = astSpanDualRaw . unAstRaw
  rD u u' = AstRaw $ astSpanD (unAstRaw u) u'
  rScale s t =
    AstDualPart $ AstFromPrimal (unAstRaw s)
                  * AstD (unAstRaw $ rzero (rshape s)) t

  xshape t = case ftkAst $ unAstRaw t of
    FTKX sh -> sh
  xindex v ix =
    AstRaw $ AstIndexX (unAstRaw v) (unAstRaw <$> ix)
  xfromVector = AstRaw . AstFromVectorX . V.map unAstRaw
  xreplicate = AstRaw . AstReplicate SNat . unAstRaw
  xconcrete = AstRaw . fromPrimal . AstConcreteX
  xfromPrimal = AstRaw . fromPrimal . unAstRaw
  xprimalPart = AstRaw . astSpanPrimalRaw . unAstRaw
  xdualPart = astSpanDualRaw . unAstRaw
  xD u u' = AstRaw $ astSpanD (unAstRaw u) u'

  sminIndex = AstRaw . fromPrimal . AstMinIndexS . astSpanPrimalRaw . unAstRaw
  smaxIndex = AstRaw . fromPrimal . AstMaxIndexS . astSpanPrimalRaw . unAstRaw
  sfloor = AstRaw . fromPrimal . AstFloorS . astSpanPrimalRaw . unAstRaw
  siota = AstRaw . fromPrimal $ AstIotaS
  sindex v ix = AstRaw $ AstIndexS (unAstRaw v) (unAstRaw <$> ix)
  ssum = AstRaw . AstSumS . unAstRaw
  sscatter t f = AstRaw $ AstScatterS (unAstRaw t)
                 $ funToAstIxS (fmap unAstRaw . f . fmap AstRaw)
                     -- this introduces new variable names
  sfromVector = AstRaw . AstFromVectorS . V.map unAstRaw
  sreplicate = AstRaw . AstReplicate SNat . unAstRaw
  sappend u v = AstRaw $ AstAppendS (unAstRaw u) (unAstRaw v)
  sslice (_ :: Proxy i) Proxy = AstRaw . AstSliceS @i . unAstRaw
  sreverse = AstRaw . AstReverseS . unAstRaw
  stranspose perm = AstRaw . AstTransposeS perm . unAstRaw
  sreshape = AstRaw . AstReshapeS . unAstRaw
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (AstRaw s) -> AstRaw s (TKS sh r))
          -> AstRaw s (TKS (n ': sh) r)
  sbuild1 f = AstRaw $ AstBuild1 (SNat @n)
              $ funToAstI  -- this introduces new variable names
              $ unAstRaw . f . AstRaw
  sgather t f = AstRaw $ AstGatherS (unAstRaw t)
                $ funToAstIxS (fmap unAstRaw . f . fmap AstRaw)
                    -- this introduces new variable names
  scast = AstRaw . AstCastS . unAstRaw
  sfromIntegral = AstRaw . fromPrimal . AstFromIntegralS
                  . astSpanPrimalRaw . unAstRaw
  sconcrete = AstRaw . fromPrimal . AstConcreteS
  sfromR = AstRaw . AstSFromR . unAstRaw

  sfromPrimal = AstRaw . fromPrimal . unAstRaw
  sprimalPart = AstRaw . astSpanPrimalRaw . unAstRaw
  sdualPart = astSpanDualRaw . unAstRaw
  sD u u' = AstRaw $ astSpanD (unAstRaw u) u'
  sScale s t = AstDualPart $ AstFromPrimal (unAstRaw s) * AstD 0 t

  tpair t1 t2 = AstRaw $ AstPair (unAstRaw t1) (unAstRaw t2)
  tproject1 t = AstRaw $ AstProject1 $ unAstRaw t
  tproject2 t = AstRaw $ AstProject2 $ unAstRaw t
  dshape = shapeAstHVector . unAstRaw
  tftk stk t | Dict <- lemTensorKindOfS stk = ftkAst $ unAstRaw t
  tcond stk b u v | Dict <- lemTensorKindOfS stk =
    AstRaw $ AstCond b (unAstRaw u) (unAstRaw v)
  tfromPrimal stk t | Dict <- lemTensorKindOfS stk =
    AstRaw $ fromPrimal $ unAstRaw t
  tprimalPart stk t | Dict <- lemTensorKindOfS stk =
    AstRaw $ astSpanPrimalRaw $ unAstRaw t
  tdualPart stk t | Dict <- lemTensorKindOfS stk = astSpanDualRaw $ unAstRaw t
  tD stk t d | Dict <- lemTensorKindOfS stk = AstRaw $ astSpanD (unAstRaw t) d
  dmkHVector = AstRaw . AstMkHVector . unRawHVector
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tApply t ll = AstRaw $ AstApply t (unAstRaw ll)
  dunHVector (AstRaw (AstMkHVector l)) = rawHVector l
  dunHVector (AstRaw hVectorOf) =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic AstMethodShare s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstProjectS hVectorOf i
    in rawHVector $ V.imap f $ shapeAstHVector hVectorOf
  dbuild1 k f = AstRaw $ AstBuildHVector1 k $ funToAstI (unAstRaw . f . AstRaw)
  -- TODO: (still) relevant?
  -- In this instance, these two ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstTensor to AstRaw.
  --
  -- TODO: dupe?
  -- These three methods are called at this type in delta evaluation via
  -- dmapAccumR and dmapAccumL, they have to work. We could refrain from
  -- simplifying the resulting terms, but it's not clear that's more consistent.
  drev = drev @(AstTensor AstMethodLet PrimalSpan)
  drevDt = drevDt @(AstTensor AstMethodLet PrimalSpan)
  dfwd = dfwd @(AstTensor AstMethodLet PrimalSpan)
  dmapAccumRDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstRaw s)
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> HFunOf (AstRaw s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstRaw s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                    (TKProduct accShs eShs))
                         (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstRaw s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                    (TKProduct accShs eShs))
                         (ADTensorKind (TKProduct accShs eShs))
    -> AstRaw s accShs
    -> AstRaw s (BuildTensorKind k eShs)
    -> AstRaw s (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstRaw $ AstMapAccumRDer k accShs bShs eShs f df rf (unAstRaw acc0) (unAstRaw es)
  dmapAccumLDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstRaw s)
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> HFunOf (AstRaw s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstRaw s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                    (TKProduct accShs eShs))
                         (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstRaw s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                    (TKProduct accShs eShs))
                         (ADTensorKind (TKProduct accShs eShs))
    -> AstRaw s accShs
    -> AstRaw s (BuildTensorKind k eShs)
    -> AstRaw s (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstRaw $ AstMapAccumLDer k accShs bShs eShs f df rf (unAstRaw acc0) (unAstRaw es)


-- * The AstNoVectorize

type instance BoolOf (AstNoVectorize s) = AstBool AstMethodLet

deriving instance IfF (AstNoVectorize s)
deriving instance AstSpan s => EqF (AstNoVectorize s)
deriving instance AstSpan s => OrdF (AstNoVectorize s)
deriving instance Eq (AstNoVectorize s y)
deriving instance Ord (AstNoVectorize s y)
deriving instance Num (AstTensor AstMethodLet s y) => Num (AstNoVectorize s y)
deriving instance (IntegralF (AstTensor AstMethodLet s y))
                  => IntegralF (AstNoVectorize s y)
deriving instance Fractional (AstTensor AstMethodLet s y)
                  => Fractional (AstNoVectorize s y)
deriving instance Floating (AstTensor AstMethodLet s y)
                  => Floating (AstNoVectorize s y)
deriving instance (RealFloatF (AstTensor AstMethodLet s y))
                  => RealFloatF (AstNoVectorize s y)

unNoVectorizeHVector :: HVector (AstNoVectorize s) -> HVector (AstTensor AstMethodLet s)
unNoVectorizeHVector =
  let f (DynamicRanked (AstNoVectorize t)) = DynamicRanked t
      f (DynamicShaped (AstNoVectorize t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noVectorizeHVector :: HVector (AstTensor AstMethodLet s) -> HVector (AstNoVectorize s)
noVectorizeHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstNoVectorize t
      f (DynamicShaped t) = DynamicShaped $ AstNoVectorize t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

instance AstSpan s => LetTensor (AstNoVectorize s) where
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => AstNoVectorize s x
       -> (AstNoVectorize s x -> AstNoVectorize s z)
       -> AstNoVectorize s z
  tlet u f = AstNoVectorize
             $ astLetFun (unAstNoVectorize u)
                         (unAstNoVectorize . f . AstNoVectorize)

  toShare :: forall y. TensorKind y
          => AstNoVectorize s y
          -> AstRaw s y
  toShare t = toShare $ unAstNoVectorize t

instance AstSpan s => BaseTensor (AstNoVectorize s) where
  rmkRepScalar = AstNoVectorize . rmkRepScalar . unAstNoVectorize
  runRepScalar = AstNoVectorize . runRepScalar . unAstNoVectorize

  rshape = rshape . unAstNoVectorize
  rminIndex = AstNoVectorize . rminIndex . unAstNoVectorize
  rmaxIndex = AstNoVectorize . rmaxIndex . unAstNoVectorize
  rfloor = AstNoVectorize . rfloor . unAstNoVectorize
  riota = AstNoVectorize riota
  rindex v ix =
    AstNoVectorize $ rindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  rsum = AstNoVectorize . rsum . unAstNoVectorize
  rscatter sh t f =
    AstNoVectorize $ rscatter sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  rfromVector = AstNoVectorize . rfromVector . V.map unAstNoVectorize
  rreplicate k = AstNoVectorize . rreplicate k . unAstNoVectorize
  rappend u v =
    AstNoVectorize $ rappend (unAstNoVectorize u) (unAstNoVectorize v)
  rslice i n = AstNoVectorize . rslice i n . unAstNoVectorize
  rreverse = AstNoVectorize . rreverse . unAstNoVectorize
  rtranspose perm = AstNoVectorize . rtranspose perm . unAstNoVectorize
  rreshape sh = AstNoVectorize . rreshape sh . unAstNoVectorize
  rbuild1 k f = withSNat k $ \snat ->
    AstNoVectorize $ AstBuild1 snat
    $ funToAstI  -- this introduces new variable names
    $ unAstNoVectorize . f . AstNoVectorize
  rgather sh t f =
    AstNoVectorize $ rgather sh (unAstNoVectorize t)
                    $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  rcast = AstNoVectorize . rcast . unAstNoVectorize
  rfromIntegral = AstNoVectorize . rfromIntegral . unAstNoVectorize
  rconcrete = AstNoVectorize . rconcrete
  rfromS = AstNoVectorize . rfromS . unAstNoVectorize
  rfromPrimal = AstNoVectorize . rfromPrimal . unAstNoVectorize
  rprimalPart = AstNoVectorize . rprimalPart . unAstNoVectorize
  rdualPart = rdualPart . unAstNoVectorize
  rD u u' = AstNoVectorize $ rD (unAstNoVectorize u) u'
  rScale s t = rScale @(AstTensor AstMethodLet PrimalSpan) (unAstNoVectorize s) t

  xshape t = case ftkAst $ unAstNoVectorize t of
    FTKX sh -> sh
  xindex v ix =
    AstNoVectorize $ xindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  xfromVector = AstNoVectorize . xfromVector . V.map unAstNoVectorize
  xreplicate = AstNoVectorize . xreplicate . unAstNoVectorize
  xconcrete = AstNoVectorize . xconcrete
  xfromPrimal = AstNoVectorize . xfromPrimal . unAstNoVectorize
  xprimalPart = AstNoVectorize . xprimalPart . unAstNoVectorize
  xdualPart = xdualPart . unAstNoVectorize
  xD u u' =
    AstNoVectorize $ xD (unAstNoVectorize u) u'

  sminIndex = AstNoVectorize . sminIndex . unAstNoVectorize
  smaxIndex = AstNoVectorize . smaxIndex . unAstNoVectorize
  sfloor = AstNoVectorize . sfloor . unAstNoVectorize
  siota = AstNoVectorize siota
  sindex v ix =
    AstNoVectorize $ sindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  ssum = AstNoVectorize . ssum . unAstNoVectorize
  sscatter t f = AstNoVectorize $ sscatter (unAstNoVectorize t)
                 $ fmap (unAstNoVectorize) . f . fmap AstNoVectorize
  sfromVector = AstNoVectorize . sfromVector . V.map unAstNoVectorize
  sreplicate = AstNoVectorize . sreplicate . unAstNoVectorize
  sappend u v =
    AstNoVectorize $ sappend (unAstNoVectorize u) (unAstNoVectorize v)
  sslice proxy1 proxy2 =
    AstNoVectorize . sslice proxy1 proxy2 . unAstNoVectorize
  sreverse = AstNoVectorize . sreverse . unAstNoVectorize
  stranspose perm =
    AstNoVectorize . stranspose perm . unAstNoVectorize
  sreshape = AstNoVectorize . sreshape . unAstNoVectorize
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (AstNoVectorize s) -> AstNoVectorize s (TKS sh r))
          -> AstNoVectorize s (TKS (n ': sh) r)
  sbuild1 f = AstNoVectorize $ AstBuild1 (SNat @n)
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorize . f . AstNoVectorize
  sgather t f = AstNoVectorize $ sgather (unAstNoVectorize t)
                $ fmap (unAstNoVectorize) . f . fmap AstNoVectorize
  scast = AstNoVectorize . scast . unAstNoVectorize
  sfromIntegral = AstNoVectorize . sfromIntegral . unAstNoVectorize
  sconcrete = AstNoVectorize . sconcrete
  sfromR = AstNoVectorize . sfromR . unAstNoVectorize
  sfromPrimal = AstNoVectorize . sfromPrimal . unAstNoVectorize
  sprimalPart = AstNoVectorize . sprimalPart . unAstNoVectorize
  sdualPart = sdualPart . unAstNoVectorize
  sD u u' = AstNoVectorize $ sD @(AstTensor AstMethodLet s) (unAstNoVectorize u) u'
  sScale s t = sScale @(AstTensor AstMethodLet PrimalSpan) (unAstNoVectorize s) t

  tpair t1 t2 = AstNoVectorize $ astPair (unAstNoVectorize t1) (unAstNoVectorize t2)
  tproject1 t = AstNoVectorize $ astProject1 $ unAstNoVectorize t
  tproject2 t = AstNoVectorize $ astProject2 $ unAstNoVectorize t
  dshape = shapeAstHVector . unAstNoVectorize
  tftk stk t | Dict <- lemTensorKindOfS stk =
    ftkAst $ unAstNoVectorize t
  tcond stk b u v = AstNoVectorize $ tcond stk b (unAstNoVectorize u) (unAstNoVectorize v)
  tfromPrimal stk t = AstNoVectorize $ tfromPrimal stk $ unAstNoVectorize t
  tprimalPart stk t = AstNoVectorize $ tprimalPart stk $ unAstNoVectorize t
  tdualPart stk t = tdualPart stk $ unAstNoVectorize t
  tD stk t d = AstNoVectorize $ tD stk (unAstNoVectorize t) d
  dmkHVector = AstNoVectorize . dmkHVector . unNoVectorizeHVector
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tApply t ll = AstNoVectorize $ astHApply t (unAstNoVectorize ll)
  dunHVector =
    noVectorizeHVector . dunHVector . unAstNoVectorize
  dbuild1 k f =
    AstNoVectorize . AstBuildHVector1 k $ funToAstI (unAstNoVectorize . f . AstNoVectorize)
  drev = drev @(AstTensor AstMethodLet PrimalSpan)
  drevDt = drevDt @(AstTensor AstMethodLet PrimalSpan)
  dfwd = dfwd @(AstTensor AstMethodLet PrimalSpan)
  dmapAccumRDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstNoVectorize s)
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> HFunOf (AstNoVectorize s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstNoVectorize s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                            (TKProduct accShs eShs))
                                 (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstNoVectorize s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                            (TKProduct accShs eShs))
                                 (ADTensorKind (TKProduct accShs eShs))
    -> AstNoVectorize s accShs
    -> AstNoVectorize s (BuildTensorKind k eShs)
    -> AstNoVectorize s (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstNoVectorize $ AstMapAccumRDer k accShs bShs eShs f df rf (unAstNoVectorize acc0) (unAstNoVectorize es)
  dmapAccumLDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstNoVectorize s)
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> HFunOf (AstNoVectorize s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstNoVectorize s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                            (TKProduct accShs eShs))
                                 (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstNoVectorize s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                            (TKProduct accShs eShs))
                                 (ADTensorKind (TKProduct accShs eShs))
    -> AstNoVectorize s accShs
    -> AstNoVectorize s (BuildTensorKind k eShs)
    -> AstNoVectorize s (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstNoVectorize $ AstMapAccumLDer k accShs bShs eShs f df rf (unAstNoVectorize acc0) (unAstNoVectorize es)


-- * The AstNoSimplify instances

type instance BoolOf (AstNoSimplify s) = AstBool AstMethodLet

deriving instance IfF (AstNoSimplify s)
deriving instance AstSpan s => EqF (AstNoSimplify s)
deriving instance AstSpan s => OrdF (AstNoSimplify s)
deriving instance Eq (AstNoSimplify s y)
deriving instance Ord (AstNoSimplify s y)
deriving instance Num (AstTensor AstMethodLet s y) => Num (AstNoSimplify s y)
deriving instance (IntegralF (AstTensor AstMethodLet s y))
                  => IntegralF (AstNoSimplify s y)
deriving instance Fractional (AstTensor AstMethodLet s y)
                  => Fractional (AstNoSimplify s y)
deriving instance Floating (AstTensor AstMethodLet s y)
                  => Floating (AstNoSimplify s y)
deriving instance (RealFloatF (AstTensor AstMethodLet s y))
                  => RealFloatF (AstNoSimplify s y)

astLetFunNoSimplify
  :: forall x z s. (TensorKind x, TensorKind z, AstSpan s)
  => AstTensor AstMethodLet s x
  -> (AstTensor AstMethodLet s x -> AstTensor AstMethodLet s z)
  -> AstTensor AstMethodLet s z
astLetFunNoSimplify a f | astIsSmall True a = f a
                            -- too important an optimization to skip
astLetFunNoSimplify a f =
  let sh = ftkAst a
      (var, ast) = funToAst sh f
  in AstLet var a ast  -- safe, because subsitution ruled out above

unNoSimplifyHVector :: HVector (AstNoSimplify s) -> HVector (AstTensor AstMethodLet s)
unNoSimplifyHVector =
  let f (DynamicRanked (AstNoSimplify t)) = DynamicRanked t
      f (DynamicShaped (AstNoSimplify t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noSimplifyHVector :: HVector (AstTensor AstMethodLet s) -> HVector (AstNoSimplify s)
noSimplifyHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstNoSimplify t
      f (DynamicShaped t) = DynamicShaped $ AstNoSimplify t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

instance AstSpan s => LetTensor (AstNoSimplify s) where
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => AstNoSimplify s x
       -> (AstNoSimplify s x -> AstNoSimplify s z)
       -> AstNoSimplify s  z
  tlet u f = AstNoSimplify
             $ astLetFunNoSimplify (unAstNoSimplify u)
                                   (unAstNoSimplify . f . AstNoSimplify)

  toShare :: AstNoSimplify s y
          -> AstRaw s y
  toShare t = AstRaw $ AstToShare $ unAstNoSimplify t

instance AstSpan s => BaseTensor (AstNoSimplify s) where
  rmkRepScalar = AstNoSimplify . AstUnScalar . unAstNoSimplify
  runRepScalar = AstNoSimplify . AstScalar . unAstNoSimplify

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
  rbuild1 k f = withSNat k $ \snat ->
    AstNoSimplify $ astBuild1Vectorize snat (unAstNoSimplify . f . AstNoSimplify)
  rgather sh t f = AstNoSimplify $ AstGather sh (unAstNoSimplify t)
                   $ funToAstIndex
                       (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                         -- this introduces new variable names
  rcast = AstNoSimplify . AstCast . unAstNoSimplify
  rfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegral
                  . astSpanPrimal . unAstNoSimplify
  rconcrete = AstNoSimplify . fromPrimal . AstConcrete
  rfromS = AstNoSimplify . AstRFromS . unAstNoSimplify
  rfromPrimal = AstNoSimplify . fromPrimal . unAstNoSimplify
  rprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  rdualPart = astSpanDual . unAstNoSimplify
  rD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) u'
  rScale s t =
    astDualPart $ AstFromPrimal (unAstNoSimplify s)
                  * AstD (rzero (rshape s)) t

  xshape t = case ftkAst $ unAstNoSimplify t of
    FTKX sh -> sh
  xindex v ix =
    AstNoSimplify $ AstIndexX (unAstNoSimplify v) (unAstNoSimplify <$> ix)
  xfromVector = AstNoSimplify . AstFromVectorX . V.map unAstNoSimplify
  xreplicate = AstNoSimplify . AstReplicate SNat . unAstNoSimplify
  xconcrete = AstNoSimplify . fromPrimal . AstConcreteX
  xfromPrimal = AstNoSimplify . fromPrimal . unAstNoSimplify
  xprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  xdualPart = astSpanDual . unAstNoSimplify
  xD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) u'

  sminIndex = AstNoSimplify . fromPrimal . AstMinIndexS
              . astSpanPrimal . unAstNoSimplify
  smaxIndex = AstNoSimplify . fromPrimal . AstMaxIndexS
              . astSpanPrimal . unAstNoSimplify
  sfloor = AstNoSimplify . fromPrimal . AstFloorS
           . astSpanPrimal . unAstNoSimplify
  siota = AstNoSimplify . fromPrimal $ AstIotaS
  sindex v ix =
    AstNoSimplify $ AstIndexS (unAstNoSimplify v) (unAstNoSimplify <$> ix)
  ssum = AstNoSimplify . AstSumS . unAstNoSimplify
  sscatter t f = AstNoSimplify $ AstScatterS (unAstNoSimplify t)
                 $ funToAstIxS
                     (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                       -- this introduces new variable names
  sfromVector = AstNoSimplify . AstFromVectorS . V.map unAstNoSimplify
  sreplicate = AstNoSimplify . AstReplicate SNat . unAstNoSimplify
  sappend u v =
    AstNoSimplify $ AstAppendS (unAstNoSimplify u) (unAstNoSimplify v)
  sslice (_ :: Proxy i) Proxy = AstNoSimplify . AstSliceS @i . unAstNoSimplify
  sreverse = AstNoSimplify . AstReverseS . unAstNoSimplify
  stranspose perm =
    AstNoSimplify . AstTransposeS perm . unAstNoSimplify
  sreshape = AstNoSimplify . AstReshapeS . unAstNoSimplify
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (AstNoSimplify s) -> AstNoSimplify s (TKS sh r))
          -> AstNoSimplify s (TKS (n ': sh) r)
  sbuild1 f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @n) (unAstNoSimplify . f . AstNoSimplify)
  sgather t f = AstNoSimplify $ AstGatherS (unAstNoSimplify t)
                $ funToAstIxS
                    (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                      -- this introduces new variable names
  scast = AstNoSimplify . AstCastS . unAstNoSimplify
  sfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegralS
                  . astSpanPrimal . unAstNoSimplify
  sconcrete = AstNoSimplify . fromPrimal . AstConcreteS
  sfromR = AstNoSimplify . AstSFromR . unAstNoSimplify
  sfromPrimal = AstNoSimplify . fromPrimal . unAstNoSimplify
    -- exceptionally we do simplify AstFromPrimal to avoid long boring chains
  sprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  sdualPart = astSpanDual . unAstNoSimplify
  sD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) u'
  sScale s t =
    astDualPart $ AstFromPrimal (unAstNoSimplify s) * AstD 0 t

  tpair t1 t2 = AstNoSimplify $ AstPair (unAstNoSimplify t1) (unAstNoSimplify t2)
  tproject1 t = AstNoSimplify $ AstProject1 $ unAstNoSimplify t
  tproject2 t = AstNoSimplify $ AstProject2 $ unAstNoSimplify t
  dshape = shapeAstHVector . unAstNoSimplify
  tftk stk t | Dict <- lemTensorKindOfS stk =
    ftkAst $ unAstNoSimplify t
  tcond stk b u v | Dict <- lemTensorKindOfS stk =
    AstNoSimplify $ AstCond b (unAstNoSimplify u) (unAstNoSimplify v)
  tfromPrimal stk t | Dict <- lemTensorKindOfS stk =
    AstNoSimplify $ fromPrimal $ unAstNoSimplify t
  tprimalPart stk t | Dict <- lemTensorKindOfS stk =
    AstNoSimplify $ astSpanPrimal $ unAstNoSimplify t
  tdualPart stk t | Dict <- lemTensorKindOfS stk = astSpanDual $ unAstNoSimplify t
  tD stk t d | Dict <- lemTensorKindOfS stk =
    AstNoSimplify $ astSpanD (unAstNoSimplify t) d
  dmkHVector = AstNoSimplify . AstMkHVector . unNoSimplifyHVector
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tApply t ll = AstNoSimplify $ AstApply t (unAstNoSimplify ll)
  dunHVector (AstNoSimplify (AstMkHVector l)) = noSimplifyHVector l
  dunHVector (AstNoSimplify hVectorOf) =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic AstMethodLet s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstProjectS hVectorOf i
    in noSimplifyHVector $ V.imap f $ shapeAstHVector hVectorOf
  dbuild1 k f = AstNoSimplify $ astBuild1Vectorize
                    k (unAstNoSimplify . f . AstNoSimplify)
  drev = drev @(AstTensor AstMethodLet PrimalSpan)
  drevDt = drevDt @(AstTensor AstMethodLet PrimalSpan)
  dfwd = dfwd @(AstTensor AstMethodLet PrimalSpan)
  dmapAccumRDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstNoSimplify s)
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> HFunOf (AstNoSimplify s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstNoSimplify s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                           (TKProduct accShs eShs))
                                (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstNoSimplify s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs eShs))
    -> AstNoSimplify s accShs
    -> AstNoSimplify s (BuildTensorKind k eShs)
    -> AstNoSimplify s (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstNoSimplify $ AstMapAccumRDer k accShs bShs eShs f df rf (unAstNoSimplify acc0) (unAstNoSimplify es)
  dmapAccumLDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstNoSimplify s)
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> HFunOf (AstNoSimplify s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstNoSimplify s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                           (TKProduct accShs eShs))
                                (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstNoSimplify s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                           (TKProduct accShs eShs))
                                (ADTensorKind (TKProduct accShs eShs))
    -> AstNoSimplify s accShs
    -> AstNoSimplify s (BuildTensorKind k eShs)
    -> AstNoSimplify s (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstNoSimplify $ AstMapAccumLDer k accShs bShs eShs f df rf (unAstNoSimplify acc0) (unAstNoSimplify es)


-- TODO: move to a better home:

prettifyArtifactRev
  :: forall x z. (TensorKind x, TensorKind z)
  => AstArtifactRev x z
  -> ( AstVarName PrimalSpan (ADTensorKind z)
     , [AstDynamicVarName]
     , AstTensor AstMethodLet PrimalSpan (ADTensorKind x)
     , AstTensor AstMethodLet PrimalSpan z )
prettifyArtifactRev AstArtifactRev{..} = case stensorKind @x of
 STKUntyped ->
  fun1DToAst (shapeAstHVector artDerivativeRev) $ \ !vars1 !asts1 ->
    let idom = AstMkHVector asts1
        !derivative = substituteAst
                        idom artVarDomainRev artDerivativeRev in
    let !primal = substituteAst
                    idom artVarDomainRev artPrimalRev
    in (artVarDtRev, vars1, derivative, primal)
 stk ->
   let dynvar = case stk of
         STKR SNat (STKScalar @r _) ->
           AstDynamicVarName @Nat @r @'[]  -- TODO: ftk
                             (varNameToAstVarId artVarDomainRev)
         STKS @sh sh (STKScalar @r _)-> withKnownShS sh $
           AstDynamicVarName @Nat @r @sh
                             (varNameToAstVarId artVarDomainRev)
         _ -> AstDynamicVarName @Nat @Double @'[]  -- TODO: product?
                                (varNameToAstVarId artVarDomainRev)
   in (artVarDtRev, [dynvar], artDerivativeRev, artPrimalRev)

printArtifactSimple
  :: forall x z. (TensorKind x, TensorKind z)
  => IntMap String
  -> AstArtifactRev x z
  -> String
printArtifactSimple renames art | Dict <- lemTensorKindOfAD (stensorKind @z) =
  let !(!varDt, !vars1, !derivative, _) = prettifyArtifactRev art in
  let !varsPP = printAstVarName renames varDt
                : map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimple renames derivative

printArtifactPretty
  :: forall x z. (TensorKind x, TensorKind z)
  => IntMap String
  -> AstArtifactRev x z
  -> String
printArtifactPretty renames art | Dict <- lemTensorKindOfAD (stensorKind @z) =
  let !(!varDt, !vars1, !derivative, _) = prettifyArtifactRev art in
  let varsPP = printAstVarName renames varDt
               : map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPretty renames derivative

printArtifactPrimalSimple
  :: forall x z. (TensorKind x, TensorKind z)
  => IntMap String
  -> AstArtifactRev x z
  -> String
printArtifactPrimalSimple renames art =
  let !(_, !vars1, _, !primal) = prettifyArtifactRev art in
  let !varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimple renames primal

printArtifactPrimalPretty
  :: forall x z. (TensorKind x, TensorKind z)
  => IntMap String
  -> AstArtifactRev x z
  -> String
printArtifactPrimalPretty renames art =
  let !(_, !vars1, _, !primal) = prettifyArtifactRev art in
  let !varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPretty renames primal
