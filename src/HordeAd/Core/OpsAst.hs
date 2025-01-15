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
import GHC.TypeLits (KnownNat, Nat, type (+))
import Data.Type.Equality (gcastWith)
import Unsafe.Coerce (unsafeCoerce)
import Data.Type.Ord (Compare)
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++), Product, Rank, IShR, KnownShS (..), KnownShX (..), ShX (..), ShS (..))
import Data.Array.Mixed.Types (Init, unsafeCoerceRefl)
import Data.Array.Mixed.Shape (shxRank, shxInit, IShX, ssxFromShape, withKnownShX)
import Data.Array.Nested.Internal.Shape (shsRank, shsPermutePrefix, shrRank, shsInit, withKnownShS)
import Data.Array.Mixed.Permutation qualified as Permutation

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
import HordeAd.Core.HVectorOps
import HordeAd.Core.OpsADVal (unADValRep)
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

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
        funToAst (aDFTK $ ftkAst $ unAstRaw primalBody) id in
  let mdt = if hasDt then Just astDt else Nothing
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

instance AstSpan s => EqF (AstTensor AstMethodLet s) where
  AstConcrete _ u ==. AstConcrete _ v = AstBoolConst $ u ==. v
    -- common in indexing
  v ==. u = AstRel EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstConcrete _ u /=. AstConcrete _ v = AstBoolConst $ u /=. v
    -- common in indexing
  v /=. u = AstRel NeqOp (astSpanPrimal v) (astSpanPrimal u)

instance AstSpan s => OrdF (AstTensor AstMethodLet s) where
  AstConcrete _ u <. AstConcrete _ v = AstBoolConst $ u <. v
    -- common in indexing
  v <. u = AstRel LsOp (astSpanPrimal v) (astSpanPrimal u)
  AstConcrete _ u <=. AstConcrete _ v = AstBoolConst $ u <=. v
    -- common in indexing
  v <=. u = AstRel LeqOp (astSpanPrimal v) (astSpanPrimal u)
  AstConcrete _ u >. AstConcrete _ v = AstBoolConst $ u >. v
    -- common in indexing
  v >. u = AstRel GtOp (astSpanPrimal v) (astSpanPrimal u)
  AstConcrete _ u >=. AstConcrete _ v = AstBoolConst $ u >=. v
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
  toHVectorOf (AsHVector v) = case tftk (STKR (SNat @n)
                                              (STKScalar $ typeRep @r)) v of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        dmkHVector . V.singleton . DynamicShaped . sfromR @_ @_ @sh $ v
  fromHVector _aInit params =  -- TODO: tlet params $ \ !params1 ->
    case V.uncons $ dunHVector params of
      Just (dynamic, rest) ->
        Just (AsHVector $ fromDynamicR rzero rfromS dynamic, Just $ dmkHVector rest)
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
  fromDValue t = fromPrimal $ astConcrete (FTKR (rshape t) FTKScalar) t

instance (GoodScalar r, KnownShS sh, AstSpan s)
         => DualNumberValue (AstTensor AstMethodLet s (TKS sh r)) where
  type DValue (AstTensor AstMethodLet s (TKS sh r)) = RepN (TKS sh r)
  fromDValue t = fromPrimal $ astConcrete (FTKS knownShS FTKScalar) t

instance (GoodScalar r, KnownNat n)
         => TermValue (AstTensor AstMethodLet FullSpan (TKR n r)) where
  type Value (AstTensor AstMethodLet FullSpan (TKR n r)) = RepN (TKR n r)
  fromValue t = fromPrimal $ astConcrete (FTKR (rshape t) FTKScalar) t

instance (GoodScalar r, KnownShS sh)
         => TermValue (AstTensor AstMethodLet FullSpan (TKS sh r)) where
  type Value (AstTensor AstMethodLet FullSpan (TKS sh r)) = RepN (TKS sh r)
  fromValue t = fromPrimal $ astConcrete (FTKS knownShS FTKScalar) t

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
  tlet u f = astLetFun u f
  toShare t = AstRaw $ AstToShare t
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unshareAstTensor . unAstRaw
      _ -> error "tunshare: used not at PrimalSpan"
  tfromS = astFromS

instance AstSpan s => BaseTensor (AstTensor AstMethodLet s) where
  rshape = shapeAst
  rminIndex @_ @r2 a = case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) . fromPrimal . AstMinIndexS
          . astSpanPrimal . astSFromR @sh $ a
        ZSS -> error "xminIndex: impossible shape"
  rmaxIndex @_ @r2 a = case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) . fromPrimal . AstMaxIndexS
          . astSpanPrimal . astSFromR @sh $ a
        ZSS -> error "xmaxIndex: impossible shape"
  rfloor @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) . fromPrimal . AstFloorS
        . astSpanPrimal . astSFromR @sh $ a

  riota @r n =
    withSNat n $ \(SNat @n) -> astFromS $ fromPrimal $ AstIotaS @n @r
  rindex @_ @m @n a ix = case ftkAst a of
    FTKR @_ @x shmshn _ | SNat <- shrRank shmshn ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        withKnownShS (dropShS @m sh) $
        astFromS @(TKS2 (Drop m sh) x)
        $ astIndexStepS @(Take m sh) @(Drop m sh)
                        (astSFromR @sh a) (ixrToIxs ix)
  rsum v = withSNat (rlength v) $ \snat -> astSum snat stensorKind v
  rscatter @_ @m @_ @p shpshn0 t f = case ftkAst t of
    FTKR @_ @x shmshn0 _ | SNat <- shrRank shmshn0
                         , SNat <- shrRank shpshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        astFromS @(TKS2 shpshn x)
        $ astScatterS @(Take m shmshn)
                      @(Drop m shmshn)
                      @(Take p shpshn) (astSFromR @shmshn t)
        $ funToAstIxS (ixrToIxs . f . ixsToIxr)
            -- this introduces new variable names
  rfromVector l = withSNat (V.length l) $ \snat -> astFromVector snat l
  rreplicate k = withSNat k $ \snat -> astReplicate snat stensorKind
  rappend u v = case ftkAst u of
    FTKR shu' _ | SNat <- shrRank shu' -> case ftkAst v of
      FTKR shv' _ ->
        withCastRS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastRS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                astFromS $ astAppendS @mu @mv @restu
                                       (astSFromR @shu u)
                                       (astSFromR @shv v)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  rslice i n a = case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          withSNat i $ \(SNat @i) -> withSNat n $ \(SNat @n) ->
          withSNat (valueOf @m - i - n) $ \(SNat @k) ->
            gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
            astFromS @(TKS2 (n ': rest) x) . astSliceS @i @n @k . astSFromR @sh $ a
        ZSS -> error "xslice: impossible shape"
  rreverse a = case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          astFromS @(TKS2 sh x) . astReverseS . astSFromR @sh $ a
        ZSS -> error "xreverse: impossible shape"
  rtranspose permr a = case ftkAst a of
    FTKR @_ @x sh' _  ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        Permutation.permFromList permr $ \(perm :: Permutation.Perm perm) ->
          gcastWith (unsafeCoerceRefl :: Compare (Rank perm) (Rank sh) :~: LT) $
          trustMeThisIsAPermutation @perm $
          case shsPermutePrefix perm sh of
            (sh2 :: ShS sh2) ->
              withKnownShS sh $
              withKnownShS sh2 $
              gcastWith (unsafeCoerceRefl :: Rank sh2 :~: Rank sh) $
              astFromS @(TKS2 sh2 x) . astTransposeS perm . astSFromR @sh $ a
  rreshape sh2' a = case ftkAst a of
    FTKR @_ @x sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
      withCastRS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        astFromS @(TKS2 sh2 x) . astReshapeS . astSFromR @sh $ a
  rbuild1 k f = withSNat k $ \snat -> astBuild1Vectorize snat f
  rgather @_ @m @_ @p shmshn0 t f = case ftkAst t of
    FTKR shpshn0 _ | SNat <- shrRank shpshn0
                   , SNat <- shrRank shmshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        astFromS $ astGatherStepS @(Take m shmshn)
                                   @(Drop m shmshn)
                                   @(Take p shpshn) (astSFromR t)
        $ funToAstIxS (ixrToIxs . f . ixsToIxr)
            -- this introduces new variable names
  rcast @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) . astCastS . astSFromR @sh $ a
  rfromIntegral @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) . fromPrimal . astFromIntegralS
        . astSpanPrimal . astSFromR @sh $ a
  rzip @y @z a = case ftkAst a of
    FTKProduct (FTKR sh' _) (FTKR _ _) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFun a $ \a3 ->
          let (a31, a32) = tunpairDup a3
          in astFromS @(TKS2 sh (TKProduct y z))
             $ AstZipS $ astPair (astSFromR @sh a31)
                                 (astSFromR @sh a32)
  runzip @y @z a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFun (AstUnzipS $ astSFromR @sh a) $ \b3 ->
          let (b31, b32) = tunpairDup b3
          in astPair (astFromS @(TKS2 sh y) b31)
                     (astFromS @(TKS2 sh z) b32)
  rtoScalar = AstToScalar . astSFromR
  rfromScalar = astFromS . astFromScalar

  rfromPrimal = fromPrimal
  rprimalPart = astSpanPrimal
  rdualPart = astSpanDual
  rD u u' = astSpanD u u'
  rScale @r s t = case ftkAst s of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astDualPart
        $ AstFromPrimal s * AstD (astFromS @(TKS sh r) (astReplicate0NS 0)) t

  sminIndex = fromPrimal . AstMinIndexS . astSpanPrimal
  smaxIndex = fromPrimal . AstMaxIndexS . astSpanPrimal
  sfloor = fromPrimal . AstFloorS . astSpanPrimal

  siota = fromPrimal $ AstIotaS
  sindex v ix =
    astIndexStepS v ix
  ssum = astSum SNat stensorKind
  sscatter @_ @shm @shn @shp t f =
    astScatterS @shm @shn @shp t
    $ funToAstIxS f
        -- this introduces new variable names
  sfromVector @_ @k l = astFromVector (SNat @k) l
  sreplicate = astReplicate SNat stensorKind
  sappend u v = astAppendS u v
  sslice @_ @i Proxy Proxy = astSliceS @i
  sreverse = astReverseS
  stranspose perm = astTransposeS perm
  sreshape = astReshapeS
  sbuild1 @_ @n f = astBuild1Vectorize (SNat @n) f
  sgather @_ @shm @shn @shp t f =
    astGatherStepS @shm @shn @shp t
    $ funToAstIxS f
        -- this introduces new variable names
  scast = astCastS
  sfromIntegral = fromPrimal . astFromIntegralS . astSpanPrimal
  szip = AstZipS
  sunzip = AstUnzipS
  stoScalar = AstToScalar
  sfromScalar = astFromScalar

  sfromPrimal = fromPrimal
  sprimalPart = astSpanPrimal
  sdualPart = astSpanDual
  sD u u' = astSpanD u u'
  sScale s t = astDualPart $ AstFromPrimal s * AstD (astReplicate0NS 0) t

  xminIndex @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) . fromPrimal . AstMinIndexS @rest @n
          . astSpanPrimal . astSFromX @sh @sh' $ a
        ZSS -> error "xminIndex: impossible shape"
  xmaxIndex @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) . fromPrimal . AstMaxIndexS @rest @n
          . astSpanPrimal . astSFromX @sh @sh' $ a
        ZSS -> error "xmaxIndex: impossible shape"
  xfloor @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) {-@sh'-} . fromPrimal . AstFloorS
        . astSpanPrimal . astSFromX @sh @sh' $ a

  xiota @n @r = astFromS $ fromPrimal $ AstIotaS @n @r
  xshape t = case ftkAst t of
    FTKX sh _ -> sh
  xindex @_ @sh1 @sh2 a ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        withKnownShS (dropShS @(Rank sh1) sh) $
        astFromS @(TKS2 (Drop (Rank sh1) sh) x) {-@sh2-}
        $ astIndexStepS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                        (astSFromX @sh @sh1sh2 a)
                        (ixxToIxs ix)
  xsum = astSum SNat stensorKind
  xscatter @_ @shm @_ @shp shpshn0 t f = case ftkAst t of
    FTKX shmshn0 _ | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        astFromS $ astScatterS @(Take (Rank shm) shmshn)
                                @(Drop (Rank shm) shmshn)
                                @(Take (Rank shp) shpshn) (astSFromX t)
        $ funToAstIxS (ixxToIxs . f . ixsToIxx)
            -- this introduces new variable names
  xfromVector @_ @k l = astFromVector (SNat @k) l
  xreplicate = astReplicate SNat stensorKind
  xappend u v = case ftkAst u of
    FTKX @shu' shu' _ -> case ftkAst v of
      FTKX @shv' shv' _ ->
        withCastXS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastXS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                astFromS $ astAppendS @mu @mv @restu
                                       (astSFromX @shu @shu' u)
                                       (astSFromX @shv @shv' v)
              ZSS -> error "xappend: impossible shape"
          ZSS -> error "xappend: impossible shape"
  xslice @_ @i @n @k Proxy Proxy a = case ftkAst a of
    FTKX @sh' @x sh'@(_ :$% _) _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
          astFromS @(TKS2 (n ': rest) x) {-@(Just n ': rest')-}
          . astSliceS @i @n @k . astSFromX @sh @sh' $ a
        ZSS -> error "xslice: impossible shape"
  xreverse a = case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          astFromS @(TKS2 sh x) {-@sh'-} . astReverseS . astSFromX @sh @sh' $ a
        ZSS -> error "xreverse: impossible shape"
  xtranspose @perm perm a = case ftkAst a of
    FTKX @sh' @x sh' _ -> case shxPermutePrefix perm sh' of
      (sh2' :: IShX sh2') ->
        withKnownShX (ssxFromShape sh2') $
        withCastXS sh' $ \(sh :: ShS sh) ->
        withCastXS sh2' $ \(sh2 :: ShS sh2) ->
          withKnownShS sh $
          withKnownShS sh2 $
          gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm sh :~: sh2) $
          astFromS @(TKS2 sh2 x) . astTransposeS perm . astSFromX @sh @sh' $ a
  xreshape sh2' a = case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
      withCastXS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        astFromS @(TKS2 sh2 x) . astReshapeS . astSFromX @sh @sh' $ a
  xbuild1 @_ @n f = astBuild1Vectorize (SNat @n) f
  xmcast @x @_ @sh2 _ a =
    (unsafeCoerce a :: AstTensor AstMethodLet s (TKX2 sh2 x))
    -- TODO: we probably need a term for xmcast to avoid losing type
    -- information while we are checking types in this module
    -- (which we don't yet do and we should, because we lose type information
    -- when the AST term is fully constructed, so it's too late to check then).
  xgather @_ @shm @_ @shp shmshn0 t f = case ftkAst t of
    FTKX shpshn0 _ | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        astFromS $ astGatherStepS @(Take (Rank shm) shmshn)
                                   @(Drop (Rank shm) shmshn)
                                   @(Take (Rank shp) shpshn) (astSFromX t)
        $ funToAstIxS (ixxToIxs . f . ixsToIxx)
            -- this introduces new variable names
  xcast @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) . astCastS . astSFromX @sh @sh' $ a
  xfromIntegral @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) . fromPrimal . astFromIntegralS
        . astSpanPrimal . astSFromX @sh @sh' $ a
  xzip @y @z @sh' a = case ftkAst a of
    FTKProduct (FTKX sh' _) (FTKX _ _) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFun a $ \a3 ->
          let (a31, a32) = tunpairDup a3
          in astFromS @(TKS2 sh (TKProduct y z)) {-@sh'-}
             $ AstZipS $ astPair (astSFromX @sh @sh' a31)
                                 (astSFromX @sh @sh' a32)
  xunzip @y @z @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFun (AstUnzipS $ astSFromX @sh @sh' a) $ \b3 ->
          let (b31, b32) = tunpairDup b3
          in astPair (astFromS @(TKS2 sh y) {-@sh'-} b31)
                     (astFromS @(TKS2 sh z) {-@sh'-} b32)
  xtoScalar = AstToScalar . astSFromX
  xfromScalar = astFromS . astFromScalar
  xfromPrimal = fromPrimal
  xprimalPart = astSpanPrimal
  xdualPart = astSpanDual
  xD u u' = astSpanD u u'
  xScale @r s t = case ftkAst s of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astDualPart
        $ AstFromPrimal s * AstD (astFromS @(TKS sh r) (astReplicate0NS 0)) t

  kfloor = fromPrimal . AstFloor . astSpanPrimal
  kcast = astCast
  kfromIntegral = fromPrimal . astFromIntegral . astSpanPrimal

  rfromX @_ @sh' a = case ftkAst a of
    FTKX @_ @x sh' _ | SNat <- shxRank sh' ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS2 sh x) $ astSFromX @sh @sh' a
  sfromR = astSFromR
  sfromX = astSFromX
  xfromR a = case ftkAst a of
    FTKR @_ @x shr _ ->
      withCastRS shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS2 sh x) $ astSFromR @sh a

  xnestR sh =
    withKnownShX sh $
    astXNestR
  xnestS sh =
    withKnownShX sh $
    astXNestS
  xnest sh =
    withKnownShX sh $
    astXNest
  xunNestR = astXUnNestR
  xunNestS = astXUnNestS
  xunNest = astXUnNest

  tpair t1 t2 = astPair t1 t2
  tproject1 = astProject1
  tproject2 = astProject2
  dshape = shapeAstHVector
  tftk _stk = ftkAst
  tcond !stk !b !u !v | Dict <- lemTensorKindOfSTK stk = astCond b u v
  tfromPrimal stk t | Dict <- lemTensorKindOfSTK stk = fromPrimal t
  tprimalPart stk t | Dict <- lemTensorKindOfSTK stk = astSpanPrimal t
  tdualPart stk t | Dict <- lemTensorKindOfSTK stk = astSpanDual t
  tD stk t d | Dict <- lemTensorKindOfSTK stk = astSpanD t d
  tconcrete ftk a | Dict <- lemTensorKindOfSTK (ftkToStk ftk) =
    fromPrimal $ astConcrete ftk a
  dmkHVector = AstMkHVector
  tlambda shss f =
    let (var, ast) = funToAst shss $ \ !ll ->
          unHFun f ll
    in AstLambda (var, shss, ast)
  tApply t ll = astHApply t ll
  dunHVector (AstMkHVector l) = l
  dunHVector hVectorOf =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic AstMethodLet s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ astProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ astProjectS hVectorOf i
    in V.imap f $ shapeAstHVector hVectorOf
  tunpairDup t = (tproject1 t, tproject2 t)
  dbuild1 k f = astBuild1Vectorize k f
  -- TODO: (still) relevant?
  -- In this instance, these three ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstTensor to AstRaw.
  drev @x ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x) =
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
  drevDt @x @z ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x)
                      , Dict <- lemTensorKindOfAD (stensorKind @z) =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactRev varDt var gradient primal, _delta) =
          revProduceArtifact True (unHFun f) emptyEnv ftkx
        ftkz = aDFTK $ ftkAst primal
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet varDt (astProject1 astP)
          $ astLet var (astProject2 astP)
          $ simplifyInline gradient
    in AstLambda (varP, ftk2, ast)
  dfwd @x @z ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactFwd varDs var derivative _primal, _delta) =
          fwdProduceArtifact (unHFun f) emptyEnv ftkx
        ftk2 = FTKProduct (aDFTK ftkx) ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet varDs (astProject1 astP)
          $ astLet var (astProject2 astP)
          $ simplifyInline derivative
    in AstLambda (varP, ftk2, ast)
  dmapAccumRDer _ !k _ !bShs !eShs f df rf acc0 es =
    astMapAccumRDer k bShs eShs f df rf acc0 es
  dmapAccumLDer _ !k _ !bShs !eShs f df rf acc0 es =
    astMapAccumLDer k bShs eShs f df rf acc0 es


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
  tunvector t = dunHVectorRaw $ tshare t
   where
    dunHVectorRaw (AstRaw hVectorOf) =
      let f :: Int -> DynamicTensor VoidTensor -> DynamicTensor (AstRaw s)
          f i = \case
            DynamicRankedDummy @r @sh _ _ ->
              withListSh (Proxy @sh) $ \(_ :: IShR n) ->
                DynamicRanked @r @n $ AstRaw $ AstProjectR hVectorOf i
            DynamicShapedDummy @r @sh _ _ ->
              DynamicShaped @r @sh $ AstRaw $ AstProjectS hVectorOf i
      in V.imap f $ shapeAstHVector hVectorOf

astReplicate0NSNoSimp :: forall shn m s r. (KnownShS shn, GoodScalar r, AstSpan s)
                      => r -> AstTensor m s (TKS shn r)
astReplicate0NSNoSimp =
  let go :: ShS sh' -> AstTensor m s (TKS '[] r) -> AstTensor m s (TKS sh' r)
      go ZSS v = v
      go ((:$$) SNat sh') v =
        withKnownShS sh' $
        AstReplicate SNat stensorKind $ go sh' v
  in go (knownShS @shn) . fromPrimal . AstConcrete (FTKS ZSS FTKScalar) . sscalar

rawHVector :: HVector (AstTensor AstMethodShare s) -> HVector (AstRaw s)
rawHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstRaw t
      f (DynamicShaped t) = DynamicShaped $ AstRaw t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

instance AstSpan s => BaseTensor (AstRaw s) where
  rshape = shapeAst . unAstRaw
  rminIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) . fromPrimal . AstMinIndexS
          . astSpanPrimalRaw . AstSFromR @sh $ a
        ZSS -> error "xminIndex: impossible shape"
  rmaxIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) . fromPrimal . AstMaxIndexS
          . astSpanPrimalRaw . AstSFromR @sh $ a
        ZSS -> error "xmaxIndex: impossible shape"
  rfloor @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . fromPrimal . AstFloorS
        . astSpanPrimalRaw . AstSFromR @sh $ a

  riota @r n =
    AstRaw
    $ withSNat n $ \(SNat @n) -> AstFromS $ fromPrimal $ AstIotaS @n @r
  rindex @_ @m @n (AstRaw a) ix = AstRaw $ case ftkAst a of
    FTKR @_ @x shmshn _ | SNat <- shrRank shmshn ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        withKnownShS (dropShS @m sh) $
        AstFromS @(TKS2 (Drop m sh) x)
        $ AstIndexS @(Take m sh) @(Drop m sh)
                    (AstSFromR @sh a) (ixrToIxs (unAstRaw <$> ix))
  rsum v = withSNat (rlength v) $ \snat ->
             AstRaw . AstSum snat stensorKind . unAstRaw $ v
  rscatter @_ @m @_ @p shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR @_ @x shmshn0 _ | SNat <- shrRank shmshn0
                         , SNat <- shrRank shpshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        AstFromS @(TKS2 shpshn x)
        $ AstScatterS @(Take m shmshn)
                      @(Drop m shmshn)
                      @(Take p shpshn) (AstSFromR @shmshn t)
        $ funToAstIxS (fmap unAstRaw . ixrToIxs . f . ixsToIxr . fmap AstRaw)
            -- this introduces new variable names
  rfromVector l = withSNat (V.length l) $ \snat ->
    AstRaw . AstFromVector snat . V.map unAstRaw $ l
  rreplicate k = withSNat k $ \snat ->
    AstRaw . AstReplicate snat stensorKind . unAstRaw
  rappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKR shu' _ | SNat <- shrRank shu' -> case ftkAst v of
      FTKR shv' _ ->
        withCastRS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastRS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                AstFromS $ AstAppendS @mu @mv @restu
                                       (AstSFromR @shu u)
                                       (AstSFromR @shv v)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  rslice i n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          withSNat i $ \(SNat @i) -> withSNat n $ \(SNat @n) ->
          withSNat (valueOf @m - i - n) $ \(SNat @k) ->
            gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
            AstFromS @(TKS2 (n ': rest) x) . AstSliceS @i @n @k . AstSFromR @sh $ a
        ZSS -> error "xslice: impossible shape"
  rreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          AstFromS @(TKS2 sh x) . AstReverseS . AstSFromR @sh $ a
        ZSS -> error "xreverse: impossible shape"
  rtranspose permr (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR @_ @x sh' _  ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        Permutation.permFromList permr $ \(perm :: Permutation.Perm perm) ->
          gcastWith (unsafeCoerceRefl :: Compare (Rank perm) (Rank sh) :~: LT) $
          trustMeThisIsAPermutation @perm $
          case shsPermutePrefix perm sh of
            (sh2 :: ShS sh2) ->
              withKnownShS sh $
              withKnownShS sh2 $
              gcastWith (unsafeCoerceRefl :: Rank sh2 :~: Rank sh) $
              AstFromS @(TKS2 sh2 x) . AstTransposeS perm . AstSFromR @sh $ a
  rreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR @_ @x sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
      withCastRS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        AstFromS @(TKS2 sh2 x) . AstReshapeS . AstSFromR @sh $ a
  rbuild1 k f = withSNat k $ \snat ->
    AstRaw $ AstBuild1 snat
    $ funToAstI  -- this introduces new variable names
    $ unAstRaw . f . AstRaw
  rgather @_ @m @_ @p shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR shpshn0 _ | SNat <- shrRank shpshn0
                   , SNat <- shrRank shmshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        AstFromS $ AstGatherS @(Take m shmshn)
                              @(Drop m shmshn)
                              @(Take p shpshn) (AstSFromR t)
        $ funToAstIxS (fmap unAstRaw . ixrToIxs . f . ixsToIxr . fmap AstRaw)
            -- this introduces new variable names
  rcast @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . AstCastS . AstSFromR @sh $ a
  rfromIntegral @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . fromPrimal . AstFromIntegralS
        . astSpanPrimalRaw . AstSFromR @sh $ a
  rzip @y @z (AstRaw a) = AstRaw $ case ftkAst a of
    FTKProduct (FTKR sh' _) (FTKR _ _) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        let (a31, a32) = tunpair $ AstRaw a
        in AstFromS @(TKS2 sh (TKProduct y z))
           $ AstZipS $ AstPair (AstSFromR @sh $ unAstRaw a31)
                               (AstSFromR @sh $ unAstRaw a32)
  runzip @y @z (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        let b3 = AstUnzipS $ AstSFromR @sh a
            (b31, b32) = tunpair $ AstRaw b3
        in AstPair (AstFromS @(TKS2 sh y) $ unAstRaw b31)
                   (AstFromS @(TKS2 sh z) $ unAstRaw b32)
  rtoScalar = AstRaw . AstToScalar . AstSFromR . unAstRaw
  rfromScalar = AstRaw . AstFromS . AstFromScalar . unAstRaw

  rfromPrimal = AstRaw . fromPrimal . unAstRaw
  rprimalPart = AstRaw . astSpanPrimalRaw . unAstRaw
  rdualPart = astSpanDualRaw . unAstRaw
  rD u u' = AstRaw $ astSpanD (unAstRaw u) u'
  rScale @r (AstRaw s) t = case ftkAst s of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstDualPart
        $ AstFromPrimal s * AstD (AstFromS @(TKS sh r) (astReplicate0NSNoSimp 0)) t

  xminIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) . fromPrimal . AstMinIndexS @rest @n
          . astSpanPrimalRaw . AstSFromX @sh @sh' $ a
        ZSS -> error "xminIndex: impossible shape"
  xmaxIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) . fromPrimal . AstMaxIndexS @rest @n
          . astSpanPrimalRaw . AstSFromX @sh @sh' $ a
        ZSS -> error "xmaxIndex: impossible shape"
  xfloor @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2). fromPrimal . AstFloorS
        . astSpanPrimalRaw . AstSFromX @sh @sh' $ a

  xiota @n @r = AstRaw $ AstFromS $ fromPrimal $ AstIotaS @n @r
  xshape t = case ftkAst $ unAstRaw t of
    FTKX sh _ -> sh
  xindex @_ @sh1 @sh2 (AstRaw a) ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        withKnownShS (dropShS @(Rank sh1) sh) $
        AstRaw $ AstFromS @(TKS2 (Drop (Rank sh1) sh) x) {-@sh2-}
        $ AstIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (AstSFromX @sh @sh1sh2 a)
                    (ixxToIxs (unAstRaw <$> ix))
  xsum = AstRaw . AstSum SNat stensorKind . unAstRaw
  xscatter @_ @shm @_ @shp shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shmshn0 _ | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        AstFromS $ AstScatterS @(Take (Rank shm) shmshn)
                                @(Drop (Rank shm) shmshn)
                                @(Take (Rank shp) shpshn) (AstSFromX t)
        $ funToAstIxS (fmap unAstRaw . ixxToIxs . f . ixsToIxx . fmap AstRaw)
            -- this introduces new variable names
  xfromVector @_ @k l =
    AstRaw . AstFromVector (SNat @k) . V.map unAstRaw $ l
  xreplicate = AstRaw . AstReplicate SNat stensorKind . unAstRaw
  xappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKX @shu' shu' _ -> case ftkAst v of
      FTKX @shv' shv' _ ->
        withCastXS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastXS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                AstFromS $ AstAppendS @mu @mv @restu
                                       (AstSFromX @shu @shu' u)
                                       (AstSFromX @shv @shv' v)
              ZSS -> error "xappend: impossible shape"
          ZSS -> error "xappend: impossible shape"
  xslice @_ @i @n @k Proxy Proxy (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' @x sh'@(_ :$% _) _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
          AstFromS @(TKS2 (n ': rest) x) {-@(Just n ': rest')-}
          . AstSliceS @i @n @k . AstSFromX @sh @sh' $ a
        ZSS -> error "xslice: impossible shape"
  xreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          AstFromS @(TKS2 sh x) {-@sh'-} . AstReverseS . AstSFromX @sh @sh' $ a
        ZSS -> error "xreverse: impossible shape"
  xtranspose @perm perm (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' @x sh' _ -> case shxPermutePrefix perm sh' of
      (sh2' :: IShX sh2') ->
        withKnownShX (ssxFromShape sh2') $
        withCastXS sh' $ \(sh :: ShS sh) ->
        withCastXS sh2' $ \(sh2 :: ShS sh2) ->
          withKnownShS sh $
          withKnownShS sh2 $
          gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm sh :~: sh2) $
          AstFromS @(TKS2 sh2 x) . AstTransposeS perm . AstSFromX @sh @sh' $ a
  xreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
      withCastXS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        AstFromS @(TKS2 sh2 x) . AstReshapeS . AstSFromX @sh @sh' $ a
  xbuild1 @_ @n f = AstRaw $ AstBuild1 (SNat @n)
                    $ funToAstI  -- this introduces new variable names
                    $ unAstRaw . f . AstRaw
  xmcast @x @_ @sh2 _ (AstRaw a) = AstRaw $
    (unsafeCoerce a :: AstTensor AstMethodShare s (TKX2 sh2 x))
    -- TODO: we probably need a term for xmcast to avoid losing type
    -- information while we are checking types in this module
    -- (which we don't yet do and we should, because we lose type information
    -- when the AST term is fully constructed, so it's too late to check then).
  xgather @_ @shm @_ @shp shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shpshn0 _ | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        AstFromS $ AstGatherS @(Take (Rank shm) shmshn)
                               @(Drop (Rank shm) shmshn)
                               @(Take (Rank shp) shpshn) (AstSFromX t)
        $ funToAstIxS (fmap unAstRaw . ixxToIxs . f . ixsToIxx . fmap AstRaw)
            -- this introduces new variable names
  xcast @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . AstCastS . AstSFromX @sh @sh' $ a
  xfromIntegral @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . fromPrimal . AstFromIntegralS
        . astSpanPrimalRaw . AstSFromX @sh @sh' $ a
  xzip @y @z @sh' (AstRaw a) = case ftkAst a of
    FTKProduct (FTKX sh' _) (FTKX _ _) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstRaw
        $ let (a31, a32) = tunpair $ AstRaw a
          in AstFromS @(TKS2 sh (TKProduct y z)) {-@sh'-}
             $ AstZipS $ AstPair (AstSFromX @sh @sh' $ unAstRaw a31)
                                 (AstSFromX @sh @sh' $ unAstRaw a32)
  xunzip @y @z @sh' (AstRaw a) = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstRaw
        $ let b3 = AstRaw $ AstUnzipS $ AstSFromX @sh @sh' a
              (b31, b32) = tunpair b3
          in AstPair (AstFromS @(TKS2 sh y) {-@sh'-} $ unAstRaw b31)
                     (AstFromS @(TKS2 sh z) {-@sh'-} $ unAstRaw b32)
  xtoScalar = AstRaw . AstToScalar . AstSFromX . unAstRaw
  xfromScalar = AstRaw . AstFromS . AstFromScalar . unAstRaw
  xfromPrimal = AstRaw . fromPrimal . unAstRaw
  xprimalPart = AstRaw . astSpanPrimalRaw . unAstRaw
  xdualPart = astSpanDualRaw . unAstRaw
  xD u u' = AstRaw $ astSpanD (unAstRaw u) u'
  xScale @r (AstRaw s) t = case ftkAst s of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstDualPart $
        AstFromPrimal s * AstD (AstFromS @(TKS sh r) (astReplicate0NSNoSimp 0)) t

  sminIndex = AstRaw . fromPrimal . AstMinIndexS . astSpanPrimalRaw . unAstRaw
  smaxIndex = AstRaw . fromPrimal . AstMaxIndexS . astSpanPrimalRaw . unAstRaw
  sfloor = AstRaw . fromPrimal . AstFloorS . astSpanPrimalRaw . unAstRaw
  siota = AstRaw . fromPrimal $ AstIotaS
  sindex v ix = AstRaw $ AstIndexS (unAstRaw v) (unAstRaw <$> ix)
  ssum = AstRaw . AstSum SNat stensorKind . unAstRaw
  sscatter @_ @shm @shn @shp t f =
    AstRaw $ AstScatterS @shm @shn @shp (unAstRaw t)
           $ funToAstIxS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  sfromVector @_ @k l =
    AstRaw . AstFromVector (SNat @k) . V.map unAstRaw $ l
  sreplicate = AstRaw . AstReplicate SNat stensorKind . unAstRaw
  sappend u v = AstRaw $ AstAppendS (unAstRaw u) (unAstRaw v)
  sslice @_ @i Proxy Proxy = AstRaw . AstSliceS @i . unAstRaw
  sreverse = AstRaw . AstReverseS . unAstRaw
  stranspose perm = AstRaw . AstTransposeS perm . unAstRaw
  sreshape = AstRaw . AstReshapeS . unAstRaw
  sbuild1 @_ @n f = AstRaw $ AstBuild1 (SNat @n)
                    $ funToAstI  -- this introduces new variable names
                    $ unAstRaw . f . AstRaw
  sgather @_ @shm @shn @shp t f =
    AstRaw $ AstGatherS @shm @shn @shp (unAstRaw t)
           $ funToAstIxS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  scast = AstRaw . AstCastS . unAstRaw
  sfromIntegral =
    AstRaw . fromPrimal . AstFromIntegralS . astSpanPrimalRaw . unAstRaw
  szip = AstRaw . AstZipS . unAstRaw
  sunzip = AstRaw . AstUnzipS . unAstRaw
  stoScalar = AstRaw . AstToScalar . unAstRaw
  sfromScalar = AstRaw . AstFromScalar . unAstRaw

  sfromPrimal = AstRaw . fromPrimal . unAstRaw
  sprimalPart = AstRaw . astSpanPrimalRaw . unAstRaw
  sdualPart = astSpanDualRaw . unAstRaw
  sD u u' = AstRaw $ astSpanD (unAstRaw u) u'
  sScale s t =
    AstDualPart $ AstFromPrimal (unAstRaw s) * AstD (astReplicate0NSNoSimp 0) t

  kfloor = AstRaw . fromPrimal . AstFloor . astSpanPrimalRaw . unAstRaw
  kcast = AstRaw . AstCast . unAstRaw
  kfromIntegral = AstRaw . fromPrimal . AstFromIntegral
                  . astSpanPrimalRaw . unAstRaw

  rfromS @_ @sh | SNat <- shsRank (knownShS @sh) =
    AstRaw . AstFromS . unAstRaw
  rfromX @_ @sh' (AstRaw a) = case ftkAst a of
    FTKX @_ @x sh' _ | SNat <- shxRank sh' ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstRaw $ AstFromS @(TKS2 sh x) $ AstSFromX @sh @sh' a
  sfromR = AstRaw . AstSFromR . unAstRaw
  sfromX = AstRaw . AstSFromX . unAstRaw
  xfromR (AstRaw a) = case ftkAst a of
    FTKR @_ @x shr _ ->
      withCastRS shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstRaw $ AstFromS @(TKS2 sh x) $ AstSFromR @sh a
  xfromS = AstRaw . AstFromS . unAstRaw

  xnestR sh =
    withKnownShX sh $
    AstRaw . AstXNestR . unAstRaw
  xnestS sh =
    withKnownShX sh $
    AstRaw . AstXNestS . unAstRaw
  xnest sh =
    withKnownShX sh $
    AstRaw . AstXNest . unAstRaw
  xunNestR = AstRaw . AstXUnNestR . unAstRaw
  xunNestS = AstRaw . AstXUnNestS . unAstRaw
  xunNest = AstRaw . AstXUnNest . unAstRaw

  tpair t1 t2 = AstRaw $ AstPair (unAstRaw t1) (unAstRaw t2)
  tproject1 t = AstRaw $ AstProject1 $ unAstRaw t
  tproject2 t = AstRaw $ AstProject2 $ unAstRaw t
  dshape = shapeAstHVector . unAstRaw
  tftk _stk = ftkAst . unAstRaw
  tcond !stk !b !u !v | Dict <- lemTensorKindOfSTK stk =
    AstRaw $ AstCond b (unAstRaw u) (unAstRaw v)
  tfromPrimal stk t | Dict <- lemTensorKindOfSTK stk =
    AstRaw $ fromPrimal $ unAstRaw t
  tprimalPart stk t | Dict <- lemTensorKindOfSTK stk =
    AstRaw $ astSpanPrimalRaw $ unAstRaw t
  tdualPart stk t | Dict <- lemTensorKindOfSTK stk = astSpanDualRaw $ unAstRaw t
  tD stk t d | Dict <- lemTensorKindOfSTK stk = AstRaw $ astSpanD (unAstRaw t) d
  tconcrete ftk a | Dict <- lemTensorKindOfSTK (ftkToStk ftk) =
    AstRaw $ fromPrimal $ AstConcrete ftk a
  dmkHVector = AstRaw . AstMkHVector . unRawHVector
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tApply t ll = AstRaw $ AstApply t (unAstRaw ll)
  dbuild1 k f = AstRaw $ AstBuild1 k $ funToAstI (unAstRaw . f . AstRaw)
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
  dmapAccumRDer @_ @bShs @eShs _ !k _ !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstRaw $ AstMapAccumRDer k bShs eShs f df rf (unAstRaw acc0) (unAstRaw es)
  dmapAccumLDer @_ @bShs @eShs _ !k _ !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstRaw $ AstMapAccumLDer k bShs eShs f df rf (unAstRaw acc0) (unAstRaw es)


-- * The AstNoVectorize

type instance BoolOf (AstNoVectorize s) = AstBool AstMethodLet

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
  tlet u f = AstNoVectorize
             $ astLetFun (unAstNoVectorize u)
                         (unAstNoVectorize . f . AstNoVectorize)
  toShare t = toShare $ unAstNoVectorize t
  tfromS = AstNoVectorize . tfromS . unAstNoVectorize

instance AstSpan s => BaseTensor (AstNoVectorize s) where
  rshape = rshape . unAstNoVectorize
  rminIndex = AstNoVectorize . rminIndex . unAstNoVectorize
  rmaxIndex = AstNoVectorize . rmaxIndex . unAstNoVectorize
  rfloor = AstNoVectorize . rfloor . unAstNoVectorize
  riota = AstNoVectorize . riota
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
  rzip = AstNoVectorize . AstZipR . unAstNoVectorize
  runzip = AstNoVectorize . AstUnzipR . unAstNoVectorize
  rtoScalar = AstNoVectorize . rtoScalar . unAstNoVectorize
  rfromScalar = AstNoVectorize . rfromScalar . unAstNoVectorize

  rfromPrimal = AstNoVectorize . rfromPrimal . unAstNoVectorize
  rprimalPart = AstNoVectorize . rprimalPart . unAstNoVectorize
  rdualPart = rdualPart . unAstNoVectorize
  rD u u' = AstNoVectorize $ rD (unAstNoVectorize u) u'
  rScale s t =
    rScale @(AstTensor AstMethodLet PrimalSpan) (unAstNoVectorize s) t

  xminIndex = AstNoVectorize . xminIndex . unAstNoVectorize
  xmaxIndex = AstNoVectorize . xmaxIndex . unAstNoVectorize
  xfloor = AstNoVectorize . xfloor . unAstNoVectorize

  xiota @n = AstNoVectorize $ xiota @_ @n
  xshape t = case ftkAst $ unAstNoVectorize t of
    FTKX sh _ -> sh
  xindex v ix =
    AstNoVectorize $ xindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  xsum = AstNoVectorize . xsum . unAstNoVectorize
  xscatter @_ @shm @shn @shp sh t f =
    AstNoVectorize $ xscatter @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  xfromVector = AstNoVectorize . xfromVector . V.map unAstNoVectorize
  xreplicate = AstNoVectorize . xreplicate . unAstNoVectorize

  xappend u v =
    AstNoVectorize $ xappend (unAstNoVectorize u) (unAstNoVectorize v)
  xslice proxy1 proxy2 =
    AstNoVectorize . xslice proxy1 proxy2 . unAstNoVectorize
  xreverse = AstNoVectorize . xreverse . unAstNoVectorize
  xtranspose perm =
    AstNoVectorize . xtranspose perm . unAstNoVectorize
  xreshape sh = AstNoVectorize . xreshape sh . unAstNoVectorize
  xbuild1 @_ @n f = AstNoVectorize $ AstBuild1 (SNat @n)
                    $ funToAstI  -- this introduces new variable names
                    $ unAstNoVectorize . f . AstNoVectorize
  xmcast sh2 =
    AstNoVectorize . xmcast sh2 . unAstNoVectorize
  xgather @_ @shm @shn @shp sh t f =
    AstNoVectorize $ xgather @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  xcast = AstNoVectorize . xcast . unAstNoVectorize
  xfromIntegral = AstNoVectorize . xfromIntegral . unAstNoVectorize
  xzip = AstNoVectorize . xzip . unAstNoVectorize
  xunzip = AstNoVectorize . xunzip . unAstNoVectorize
  xtoScalar = AstNoVectorize . xtoScalar . unAstNoVectorize
  xfromScalar = AstNoVectorize . xfromScalar . unAstNoVectorize
  xfromPrimal = AstNoVectorize . xfromPrimal . unAstNoVectorize
  xprimalPart = AstNoVectorize . xprimalPart . unAstNoVectorize
  xdualPart = xdualPart . unAstNoVectorize
  xD u u' = AstNoVectorize $ xD (unAstNoVectorize u) u'
  xScale s t =
    xScale @(AstTensor AstMethodLet PrimalSpan) (unAstNoVectorize s) t

  sminIndex = AstNoVectorize . sminIndex . unAstNoVectorize
  smaxIndex = AstNoVectorize . smaxIndex . unAstNoVectorize
  sfloor = AstNoVectorize . sfloor . unAstNoVectorize
  siota = AstNoVectorize siota
  sindex v ix =
    AstNoVectorize $ sindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  ssum = AstNoVectorize . ssum . unAstNoVectorize
  sscatter @_ @shm @shn @shp t f =
    AstNoVectorize $ sscatter @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
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
  sbuild1 @_ @n f = AstNoVectorize $ AstBuild1 (SNat @n)
                    $ funToAstI  -- this introduces new variable names
                    $ unAstNoVectorize . f . AstNoVectorize
  sgather @_ @shm @shn @shp t f =
    AstNoVectorize $ sgather @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  scast = AstNoVectorize . scast . unAstNoVectorize
  sfromIntegral = AstNoVectorize . sfromIntegral . unAstNoVectorize
  szip = AstNoVectorize . AstZipS . unAstNoVectorize
  sunzip = AstNoVectorize . AstUnzipS . unAstNoVectorize
  stoScalar = AstNoVectorize . stoScalar . unAstNoVectorize
  sfromScalar = AstNoVectorize . sfromScalar . unAstNoVectorize

  sfromPrimal = AstNoVectorize . sfromPrimal . unAstNoVectorize
  sprimalPart = AstNoVectorize . sprimalPart . unAstNoVectorize
  sdualPart = sdualPart . unAstNoVectorize
  sD u u' = AstNoVectorize $ sD @(AstTensor AstMethodLet s) (unAstNoVectorize u) u'
  sScale s t =
    sScale @(AstTensor AstMethodLet PrimalSpan) (unAstNoVectorize s) t

  kfloor = AstNoVectorize . kfloor . unAstNoVectorize
  kcast = AstNoVectorize . kcast . unAstNoVectorize
  kfromIntegral = AstNoVectorize . kfromIntegral . unAstNoVectorize

  rfromX = AstNoVectorize . rfromX . unAstNoVectorize
  sfromR = AstNoVectorize . sfromR . unAstNoVectorize
  sfromX = AstNoVectorize . sfromX . unAstNoVectorize
  xfromR = AstNoVectorize . xfromR  . unAstNoVectorize

  xnestR sh =
    withKnownShX sh $
    AstNoVectorize . xnestR sh . unAstNoVectorize
  xnestS sh =
    withKnownShX sh $
    AstNoVectorize . xnestS sh . unAstNoVectorize
  xnest sh =
    withKnownShX sh $
    AstNoVectorize . xnest sh . unAstNoVectorize
  xunNestR = AstNoVectorize . xunNestR . unAstNoVectorize
  xunNestS = AstNoVectorize . xunNestS . unAstNoVectorize
  xunNest = AstNoVectorize . xunNest . unAstNoVectorize

  tpair t1 t2 = AstNoVectorize $ tpair (unAstNoVectorize t1) (unAstNoVectorize t2)
  tproject1 t = AstNoVectorize $ tproject1 $ unAstNoVectorize t
  tproject2 t = AstNoVectorize $ tproject2 $ unAstNoVectorize t
  dshape = shapeAstHVector . unAstNoVectorize
  tftk _stk = ftkAst . unAstNoVectorize
  tcond !stk !b !u !v =
    AstNoVectorize $ tcond stk b (unAstNoVectorize u) (unAstNoVectorize v)
  tfromPrimal stk t = AstNoVectorize $ tfromPrimal stk $ unAstNoVectorize t
  tprimalPart stk t = AstNoVectorize $ tprimalPart stk $ unAstNoVectorize t
  tdualPart stk t = tdualPart stk $ unAstNoVectorize t
  tD stk t d = AstNoVectorize $ tD stk (unAstNoVectorize t) d
  tconcrete ftk a = AstNoVectorize $ tconcrete ftk a
  dmkHVector = AstNoVectorize . dmkHVector . unNoVectorizeHVector
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tApply t ll = AstNoVectorize $ tApply t (unAstNoVectorize ll)
  dunHVector = noVectorizeHVector . dunHVector . unAstNoVectorize
  tunpairDup t = (tproject1 t, tproject2 t)
  dbuild1 k f =
    AstNoVectorize . AstBuild1 k $ funToAstI (unAstNoVectorize . f . AstNoVectorize)
  drev = drev @(AstTensor AstMethodLet PrimalSpan)
  drevDt = drevDt @(AstTensor AstMethodLet PrimalSpan)
  dfwd = dfwd @(AstTensor AstMethodLet PrimalSpan)
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstNoVectorize $ dmapAccumRDer Proxy k accShs bShs eShs f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstNoVectorize $ dmapAccumLDer Proxy k accShs bShs eShs f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)


-- * The AstNoSimplify instances

type instance BoolOf (AstNoSimplify s) = AstBool AstMethodLet

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
astLetFunNoSimplify a f = case ftkAst a of
  FTKR @_ @x2 sh' x | SNat <- shrRank sh'
                    , Dict <- lemTensorKindOfSTK (ftkToStk x) ->
    withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      let (var, ast) = funToAst (FTKS sh x) (f . AstFromS @(TKS2 sh x2))
      in AstLet var (AstSFromR @sh a) ast
           -- safe, because subsitution ruled out above
  -- TODO: also mixed and maybe recursively product
  ftk -> let (var, ast) = funToAst ftk f
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
  tlet u f = AstNoSimplify
             $ astLetFunNoSimplify (unAstNoSimplify u)
                                   (unAstNoSimplify . f . AstNoSimplify)
  toShare t = AstRaw $ AstToShare $ unAstNoSimplify t
  tfromS = AstNoSimplify . AstFromS . unAstNoSimplify

instance AstSpan s => BaseTensor (AstNoSimplify s) where
  rshape = shapeAst . unAstNoSimplify
  rminIndex @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) . fromPrimal . AstMinIndexS
          . astSpanPrimal . AstSFromR @sh $ a
        ZSS -> error "xminIndex: impossible shape"
  rmaxIndex @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) . fromPrimal . AstMaxIndexS
          . astSpanPrimal . AstSFromR @sh $ a
        ZSS -> error "xmaxIndex: impossible shape"
  rfloor @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . fromPrimal . AstFloorS
        . astSpanPrimal . AstSFromR @sh $ a

  riota @r n =
    AstNoSimplify
    $ withSNat n $ \(SNat @n) -> AstFromS $ fromPrimal $ AstIotaS @n @r
  rindex @_ @m @n (AstNoSimplify a) ix = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x shmshn _ | SNat <- shrRank shmshn ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        withKnownShS (dropShS @m sh) $
        AstFromS @(TKS2 (Drop m sh) x)
        $ AstIndexS @(Take m sh) @(Drop m sh)
                    (AstSFromR @sh a) (ixrToIxs (unAstNoSimplify <$> ix))
  rsum v = withSNat (rlength v) $ \snat ->
             AstNoSimplify . AstSum snat stensorKind . unAstNoSimplify $ v
  rscatter @_ @m @_ @p shpshn0 (AstNoSimplify t) f = AstNoSimplify $ case ftkAst t of
    FTKR @_ @x shmshn0 _ | SNat <- shrRank shmshn0
                         , SNat <- shrRank shpshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        AstFromS @(TKS2 shpshn x)
        $ AstScatterS @(Take m shmshn)
                      @(Drop m shmshn)
                      @(Take p shpshn) (AstSFromR @shmshn t)
        $ funToAstIxS (fmap unAstNoSimplify . ixrToIxs . f . ixsToIxr . fmap AstNoSimplify)
            -- this introduces new variable names
  rfromVector l = withSNat (V.length l) $ \snat ->
    AstNoSimplify . AstFromVector snat . V.map unAstNoSimplify $ l
  rreplicate k = withSNat k $ \snat ->
    AstNoSimplify . AstReplicate snat stensorKind . unAstNoSimplify
  rappend (AstNoSimplify u) (AstNoSimplify v) = AstNoSimplify $ case ftkAst u of
    FTKR shu' _ | SNat <- shrRank shu' -> case ftkAst v of
      FTKR shv' _ ->
        withCastRS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastRS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                AstFromS $ AstAppendS @mu @mv @restu
                                       (AstSFromR @shu u)
                                       (AstSFromR @shv v)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  rslice i n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          withSNat i $ \(SNat @i) -> withSNat n $ \(SNat @n) ->
          withSNat (valueOf @m - i - n) $ \(SNat @k) ->
            gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
            AstFromS @(TKS2 (n ': rest) x) . AstSliceS @i @n @k . AstSFromR @sh $ a
        ZSS -> error "xslice: impossible shape"
  rreverse (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          AstFromS @(TKS2 sh x) . AstReverseS . AstSFromR @sh $ a
        ZSS -> error "xreverse: impossible shape"
  rtranspose permr (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x sh' _  ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        Permutation.permFromList permr $ \(perm :: Permutation.Perm perm) ->
          gcastWith (unsafeCoerceRefl :: Compare (Rank perm) (Rank sh) :~: LT) $
          trustMeThisIsAPermutation @perm $
          case shsPermutePrefix perm sh of
            (sh2 :: ShS sh2) ->
              withKnownShS sh $
              withKnownShS sh2 $
              gcastWith (unsafeCoerceRefl :: Rank sh2 :~: Rank sh) $
              AstFromS @(TKS2 sh2 x) . AstTransposeS perm . AstSFromR @sh $ a
  rreshape sh2' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
      withCastRS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        AstFromS @(TKS2 sh2 x) . AstReshapeS . AstSFromR @sh $ a
  rbuild1 k f = withSNat k $ \snat ->
    AstNoSimplify
    $ astBuild1Vectorize snat (unAstNoSimplify . f . AstNoSimplify)
  rgather @_ @m @_ @p shmshn0 (AstNoSimplify t) f = AstNoSimplify $ case ftkAst t of
    FTKR shpshn0 _ | SNat <- shrRank shpshn0
                   , SNat <- shrRank shmshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        AstFromS $ AstGatherS @(Take m shmshn)
                              @(Drop m shmshn)
                              @(Take p shpshn) (AstSFromR t)
        $ funToAstIxS (fmap unAstNoSimplify . ixrToIxs . f . ixsToIxr . fmap AstNoSimplify)
            -- this introduces new variable names
  rcast @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . AstCastS . AstSFromR @sh $ a
  rfromIntegral @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . fromPrimal . AstFromIntegralS
        . astSpanPrimal . AstSFromR @sh $ a
  rzip @y @z (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKProduct (FTKR sh' _) (FTKR _ _) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFunNoSimplify a $ \a3 ->
          let (a31, a32) = tunpairDup a3
          in AstFromS @(TKS2 sh (TKProduct y z))
             $ AstZipS $ AstPair (AstSFromR @sh a31)
                                 (AstSFromR @sh a32)
  runzip @y @z (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFunNoSimplify (AstUnzipS $ AstSFromR @sh a) $ \b3 ->
          let (b31, b32) = tunpairDup b3
          in AstPair (AstFromS @(TKS2 sh y) b31)
                     (AstFromS @(TKS2 sh z) b32)
  rtoScalar = AstNoSimplify . AstToScalar . AstSFromR . unAstNoSimplify
  rfromScalar = AstNoSimplify . AstFromS . AstFromScalar . unAstNoSimplify

  rfromPrimal = AstNoSimplify . fromPrimal . unAstNoSimplify
  rprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  rdualPart = astSpanDual . unAstNoSimplify
  rD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) u'
  rScale @r (AstNoSimplify s) t = case ftkAst s of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstDualPart
        $ AstFromPrimal s * AstD (AstFromS @(TKS sh r) (astReplicate0NSNoSimp 0)) t

  xminIndex @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) . fromPrimal . AstMinIndexS @rest @n
          . astSpanPrimal . AstSFromX @sh @sh' $ a
        ZSS -> error "xminIndex: impossible shape"
  xmaxIndex @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) . fromPrimal . AstMaxIndexS @rest @n
          . astSpanPrimal . AstSFromX @sh @sh' $ a
        ZSS -> error "xmaxIndex: impossible shape"
  xfloor @_ @r2 @sh' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . fromPrimal . AstFloorS
        . astSpanPrimal . AstSFromX @sh @sh' $ a

  xiota @n @r = AstNoSimplify $ AstFromS $ fromPrimal $ AstIotaS @n @r
  xshape t = case ftkAst $ unAstNoSimplify t of
    FTKX sh _ -> sh
  xindex @_ @sh1 @sh2 (AstNoSimplify a) ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        withKnownShS (dropShS @(Rank sh1) sh) $
        AstNoSimplify $ AstFromS @(TKS2 (Drop (Rank sh1) sh) x) {-@sh2-}
        $ AstIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (AstSFromX @sh @sh1sh2 a)
                    (ixxToIxs (unAstNoSimplify <$> ix))
  xsum = AstNoSimplify . AstSum SNat stensorKind . unAstNoSimplify
  xscatter @_ @shm @_ @shp shpshn0 (AstNoSimplify t) f = AstNoSimplify
                                                         $ case ftkAst t of
    FTKX shmshn0 _ | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        AstFromS $ AstScatterS @(Take (Rank shm) shmshn)
                                @(Drop (Rank shm) shmshn)
                                @(Take (Rank shp) shpshn) (AstSFromX t)
        $ funToAstIxS (fmap unAstNoSimplify . ixxToIxs . f . ixsToIxx
                       . fmap AstNoSimplify)
            -- this introduces new variable names
  xfromVector @_ @k l =
    AstNoSimplify . AstFromVector (SNat @k) . V.map unAstNoSimplify $ l
  xreplicate = AstNoSimplify . AstReplicate SNat stensorKind . unAstNoSimplify
  xappend (AstNoSimplify u) (AstNoSimplify v) = AstNoSimplify $ case ftkAst u of
    FTKX @shu' shu' _ -> case ftkAst v of
      FTKX @shv' shv' _ ->
        withCastXS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastXS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                AstFromS $ AstAppendS @mu @mv @restu
                                       (AstSFromX @shu @shu' u)
                                       (AstSFromX @shv @shv' v)
              ZSS -> error "xappend: impossible shape"
          ZSS -> error "xappend: impossible shape"
  xslice @_ @i @n @k Proxy Proxy
         (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' @x sh'@(_ :$% _) _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
          AstFromS @(TKS2 (n ': rest) x)
          . AstSliceS @i @n @k . AstSFromX @sh @sh' $ a
        ZSS -> error "xslice: impossible shape"
  xreverse (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          AstFromS @(TKS2 sh x) {-@sh'-} . AstReverseS . AstSFromX @sh @sh' $ a
        ZSS -> error "xreverse: impossible shape"
  xtranspose @perm perm (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' @x sh' _ -> case shxPermutePrefix perm sh' of
      (sh2' :: IShX sh2') ->
        withKnownShX (ssxFromShape sh2') $
        withCastXS sh' $ \(sh :: ShS sh) ->
        withCastXS sh2' $ \(sh2 :: ShS sh2) ->
          withKnownShS sh $
          withKnownShS sh2 $
          gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm sh :~: sh2) $
          AstFromS @(TKS2 sh2 x) . AstTransposeS perm . AstSFromX @sh @sh' $ a
  xreshape sh2' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
      withCastXS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        AstFromS @(TKS2 sh2 x) . AstReshapeS . AstSFromX @sh @sh' $ a
  xbuild1 @_ @n f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @n) (unAstNoSimplify . f . AstNoSimplify)
  xmcast @x @_ @sh2 _ (AstNoSimplify a) = AstNoSimplify $
    (unsafeCoerce a :: AstTensor AstMethodLet s (TKX2 sh2 x))
    -- TODO: we probably need a term for xmcast to avoid losing type
    -- information while we are checking types in this module
    -- (which we don't yet do and we should, because we lose type information
    -- when the AST term is fully constructed, so it's too late to check then).
  xgather @_ @shm @_ @shp shmshn0 (AstNoSimplify t) f = AstNoSimplify
                                                        $ case ftkAst t of
    FTKX shpshn0 _ | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        AstFromS $ AstGatherS @(Take (Rank shm) shmshn)
                               @(Drop (Rank shm) shmshn)
                               @(Take (Rank shp) shpshn) (AstSFromX t)
        $ funToAstIxS (fmap unAstNoSimplify . ixxToIxs . f . ixsToIxx
                       . fmap AstNoSimplify)
            -- this introduces new variable names
  xcast @_ @r2 @sh' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . AstCastS . AstSFromX @sh @sh' $ a
  xfromIntegral @_ @r2 @sh' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) . fromPrimal . AstFromIntegralS
        . astSpanPrimal . AstSFromX @sh @sh' $ a
  xzip @y @z @sh' (AstNoSimplify a) = case ftkAst a of
    FTKProduct (FTKX sh' _) (FTKX _ _) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstNoSimplify
        $ astLetFunNoSimplify a $ \a3 ->
          let (a31, a32) = tunpairDup a3
          in AstFromS @(TKS2 sh (TKProduct y z)) {-@sh'-}
             $ AstZipS $ AstPair (AstSFromX @sh @sh' a31)
                                 (AstSFromX @sh @sh' a32)
  xunzip @y @z @sh' (AstNoSimplify a) = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstNoSimplify
        $ astLetFunNoSimplify (AstUnzipS $ AstSFromX @sh @sh' a) $ \b3 ->
          let (b31, b32) = tunpairDup b3
          in AstPair (AstFromS @(TKS2 sh y) {-@(TKX2 sh' y)-} b31)
                     (AstFromS @(TKS2 sh z) {-@(TKX2 sh' z)-} b32)
  xtoScalar = AstNoSimplify . AstToScalar . AstSFromX . unAstNoSimplify
  xfromScalar = AstNoSimplify . AstFromS . AstFromScalar . unAstNoSimplify
  xfromPrimal = AstNoSimplify . fromPrimal . unAstNoSimplify
  xprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  xdualPart = astSpanDual . unAstNoSimplify
  xD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) u'
  xScale @r (AstNoSimplify s) t = case ftkAst s of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstDualPart
        $ AstFromPrimal s * AstD (AstFromS @(TKS sh r) (astReplicate0NSNoSimp 0)) t

  sminIndex = AstNoSimplify . fromPrimal . AstMinIndexS
              . astSpanPrimal . unAstNoSimplify
  smaxIndex = AstNoSimplify . fromPrimal . AstMaxIndexS
              . astSpanPrimal . unAstNoSimplify
  sfloor = AstNoSimplify . fromPrimal . AstFloorS
           . astSpanPrimal . unAstNoSimplify
  siota = AstNoSimplify . fromPrimal $ AstIotaS
  sindex v ix =
    AstNoSimplify $ AstIndexS (unAstNoSimplify v) (unAstNoSimplify <$> ix)
  ssum = AstNoSimplify . AstSum SNat stensorKind . unAstNoSimplify
  sscatter @_ @shm @shn @shp t f =
    AstNoSimplify $ AstScatterS @shm @shn @shp (unAstNoSimplify t)
                  $ funToAstIxS
                      (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                        -- this introduces new variable names
  sfromVector @_ @k l =
    AstNoSimplify . AstFromVector (SNat @k) . V.map unAstNoSimplify $ l
  sreplicate = AstNoSimplify . AstReplicate SNat stensorKind . unAstNoSimplify
  sappend u v =
    AstNoSimplify $ AstAppendS (unAstNoSimplify u) (unAstNoSimplify v)
  sslice @_ @i Proxy Proxy = AstNoSimplify . AstSliceS @i . unAstNoSimplify
  sreverse = AstNoSimplify . AstReverseS . unAstNoSimplify
  stranspose perm =
    AstNoSimplify . AstTransposeS perm . unAstNoSimplify
  sreshape = AstNoSimplify . AstReshapeS . unAstNoSimplify
  sbuild1 @_ @n f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @n) (unAstNoSimplify . f . AstNoSimplify)
  sgather @_ @shm @shn @shp t f =
    AstNoSimplify $ AstGatherS @shm @shn @shp (unAstNoSimplify t)
                  $ funToAstIxS
                      (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                        -- this introduces new variable names
  scast = AstNoSimplify . AstCastS . unAstNoSimplify
  sfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegralS
                  . astSpanPrimal . unAstNoSimplify
  szip = AstNoSimplify . AstZipS . unAstNoSimplify
  sunzip = AstNoSimplify . AstUnzipS . unAstNoSimplify
  stoScalar = AstNoSimplify . AstToScalar . unAstNoSimplify
  sfromScalar = AstNoSimplify . AstFromScalar . unAstNoSimplify

  sfromPrimal = AstNoSimplify . fromPrimal . unAstNoSimplify
    -- exceptionally we do simplify AstFromPrimal to avoid long boring chains
  sprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  sdualPart = astSpanDual . unAstNoSimplify
  sD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) u'
  sScale s t =
    astDualPart
    $ AstFromPrimal (unAstNoSimplify s) * AstD (astReplicate0NSNoSimp 0) t

  kfloor = AstNoSimplify . fromPrimal . AstFloor
           . astSpanPrimal . unAstNoSimplify
  kcast = AstNoSimplify . AstCast . unAstNoSimplify
  kfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegral
                  . astSpanPrimal . unAstNoSimplify

  rfromX @_ @sh' (AstNoSimplify a) = case ftkAst a of
    FTKX @_ @x sh' _ | SNat <- shxRank sh' ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstNoSimplify $ AstFromS @(TKS2 sh x) $ AstSFromX @sh @sh' a
  sfromR = AstNoSimplify . AstSFromR . unAstNoSimplify
  sfromX  = AstNoSimplify . AstSFromX . unAstNoSimplify
  xfromR (AstNoSimplify a) = case ftkAst a of
    FTKR @_ @x shr _ ->
      withCastRS shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstNoSimplify $ AstFromS @(TKS2 sh x) $ AstSFromR @sh a

  xnestR sh =
    withKnownShX sh $
    AstNoSimplify . AstXNestR . unAstNoSimplify
  xnestS sh =
    withKnownShX sh $
    AstNoSimplify . AstXNestS . unAstNoSimplify
  xnest sh =
    withKnownShX sh $
    AstNoSimplify . AstXNest . unAstNoSimplify
  xunNestR = AstNoSimplify . AstXUnNestR . unAstNoSimplify
  xunNestS = AstNoSimplify . AstXUnNestS . unAstNoSimplify
  xunNest = AstNoSimplify . AstXUnNest . unAstNoSimplify

  tpair t1 t2 = AstNoSimplify $ AstPair (unAstNoSimplify t1) (unAstNoSimplify t2)
  tproject1 t = AstNoSimplify $ AstProject1 $ unAstNoSimplify t
  tproject2 t = AstNoSimplify $ AstProject2 $ unAstNoSimplify t
  dshape = shapeAstHVector . unAstNoSimplify
  tftk _stk = ftkAst . unAstNoSimplify
  tcond !stk !b !u !v | Dict <- lemTensorKindOfSTK stk =
    AstNoSimplify $ AstCond b (unAstNoSimplify u) (unAstNoSimplify v)
  tfromPrimal stk t | Dict <- lemTensorKindOfSTK stk =
    AstNoSimplify $ fromPrimal $ unAstNoSimplify t
  tprimalPart stk t | Dict <- lemTensorKindOfSTK stk =
    AstNoSimplify $ astSpanPrimal $ unAstNoSimplify t
  tdualPart stk t | Dict <- lemTensorKindOfSTK stk = astSpanDual $ unAstNoSimplify t
  tD stk t d | Dict <- lemTensorKindOfSTK stk =
    AstNoSimplify $ astSpanD (unAstNoSimplify t) d
  tconcrete ftk a | Dict <- lemTensorKindOfSTK (ftkToStk ftk) =
    AstNoSimplify $ fromPrimal $ AstConcrete ftk a
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
  tunpairDup (AstNoSimplify (AstPair t1 t2)) =  -- a tiny bit of simplification
    (AstNoSimplify t1, AstNoSimplify t2)
  tunpairDup t = (tproject1 t, tproject2 t)
  dbuild1 k f = AstNoSimplify $ astBuild1Vectorize
                    k (unAstNoSimplify . f . AstNoSimplify)
  drev = drev @(AstTensor AstMethodLet PrimalSpan)
  drevDt = drevDt @(AstTensor AstMethodLet PrimalSpan)
  dfwd = dfwd @(AstTensor AstMethodLet PrimalSpan)
  dmapAccumRDer @_ @bShs @eShs _ !k _ !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstNoSimplify $ AstMapAccumRDer k bShs eShs f df rf (unAstNoSimplify acc0) (unAstNoSimplify es)
  dmapAccumLDer @_ @bShs @eShs _ !k _ !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstNoSimplify $ AstMapAccumLDer k bShs eShs f df rf (unAstNoSimplify acc0) (unAstNoSimplify es)


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
printArtifactSimple renames art | Dict <- lemTensorKindOfAD (stensorKind @x)
                                , Dict <- lemTensorKindOfAD (stensorKind @z) =
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
printArtifactPretty renames art | Dict <- lemTensorKindOfAD (stensorKind @x)
                                , Dict <- lemTensorKindOfAD (stensorKind @z) =
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
