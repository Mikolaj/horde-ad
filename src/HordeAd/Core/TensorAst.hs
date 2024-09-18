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
  , rankedY, unRankedY
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Array.Shape qualified as Sh
import Data.IntMap.Strict (IntMap)
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
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.AstVectorize
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorADVal (unADValInterpretation)
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorConcrete ()
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), FlipS (..), IntegralF (..), RealFloatF (..))
import HordeAd.Util.SizedList

-- * Symbolic reverse and forward derivative computation

-- | The third argument (@hVectorPrimal0@) must be shallowly duplicable
-- (that is, either duplicable (e.g., a variable or concrete) or starting with
-- a tuple constructor).
forwardPassByInterpretation
  :: forall x z. (TensorKind x, TensorKind z)
  => (InterpretationTarget (AstRanked FullSpan) x
      -> InterpretationTarget (AstRanked FullSpan) z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> InterpretationTarget (AstRaw PrimalSpan) x
  -> AstVarName FullSpan x
  -> InterpretationTarget (AstRanked FullSpan) x
  -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit hVectorPrimal var hVector =
  let deltaInputs = generateDeltaInputs $ tshapeFull (stensorKind @x) hVectorPrimal
      varInputs = makeADInputs hVectorPrimal deltaInputs
      ast = g hVector
      env = extendEnv var varInputs envInit
  in interpretAst env $ unRankedY (stensorKind @z) ast

revArtifactFromForwardPass
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (InterpretationTarget (AstRaw PrimalSpan) x
      -> AstVarName FullSpan x
      -> InterpretationTarget (AstRanked FullSpan) x
      -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z)
  -> TensorKindFull x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass hasDt forwardPass ftk =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varPrimal, hVectorPrimal, var, hVector) = funToAstRev ftk in
  let -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(!primalBody, !deltaIT) =
        unADValInterpretation (stensorKind @z)
        $ forwardPass (rawY (stensorKind @x) hVectorPrimal) var
                      (rankedY (stensorKind @x) hVector)
      !delta = unDeltaRY (stensorKind @z) deltaIT in
  let (!varDt, !astDt) =
        funToAst (shapeAstFull $ unRawY (stensorKind @z) primalBody) id in
  let mdt = if hasDt then Just $ rawY (stensorKind @z) astDt else Nothing
      !gradient = gradientFromDelta ftk primalBody mdt delta
      !unGradient = gunshare (stensorKind @x) gradient
      !unPrimal = gunshare (stensorKind @z) primalBody
  in ( AstArtifactRev varDt varPrimal unGradient unPrimal
     , delta )

revProduceArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (InterpretationTarget (AstRanked FullSpan) x
      -> InterpretationTarget (AstRanked FullSpan) z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> TensorKindFull x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifact #-}
revProduceArtifact hasDt g envInit =
  revArtifactFromForwardPass hasDt (forwardPassByInterpretation g envInit)

gunshare
  :: forall y.
     STensorKindType y
  -> InterpretationTarget (AstRaw PrimalSpan) y
  -> InterpretationTarget (AstRanked PrimalSpan) y
gunshare stk b | Dict <- lemTensorKindOfS stk =
  rankedY stk $ unshareAstTensor $ unRawY stk b

fwdArtifactFromForwardPass
  :: forall x z. (TensorKind x, TensorKind z)
  => (InterpretationTarget (AstRaw PrimalSpan) x
      -> AstVarName FullSpan x
      -> InterpretationTarget (AstRanked FullSpan) x
      -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z)
  -> TensorKindFull x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass ftk =
  let !(!varPrimalD, hVectorD, varPrimal, hVectorPrimal, var, hVector) =
        funToAstFwd ftk in
  let !(!primalBody, !deltaIT) =
        unADValInterpretation (stensorKind @z)
        $ forwardPass (rawY (stensorKind @x) hVectorPrimal) var
                      (rankedY (stensorKind @x) hVector)
      !delta = unDeltaRY (stensorKind @z) deltaIT in
  let -- The second argument is duplicable (a variable), as required.
      !derivative = derivativeFromDelta delta (rawY (stensorKind @x) hVectorD)
      !unDerivative = gunshare (stensorKind @z) derivative
      !unPrimal = gunshare (stensorKind @z) primalBody
  in ( AstArtifactFwd varPrimalD varPrimal unDerivative unPrimal
     , delta )

fwdProduceArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => (InterpretationTarget (AstRanked FullSpan) x
      -> InterpretationTarget (AstRanked FullSpan) z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> TensorKindFull x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdProduceArtifact #-}
fwdProduceArtifact f envInit =
  fwdArtifactFromForwardPass (forwardPassByInterpretation f envInit)


-- * AstRanked instances

-- These boolean instances are unlawful; they are lawful modulo evaluation.

type instance BoolOf (AstRanked s) = AstBool AstMethodLet

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

{-deriving instance IfF (AstRanked s)
deriving instance AstSpan s => EqF (AstRanked s)
deriving instance AstSpan s => OrdF (AstRanked s)-}
deriving instance Eq (AstRanked s r n)
deriving instance Ord (AstRanked s r n)
deriving instance Num (AstTensor AstMethodLet s (TKR r n)) => Num (AstRanked s r n)
deriving instance (Real (AstTensor AstMethodLet s (TKR r n)))
                   => Real (AstRanked s r n)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKR r n)))
                  => IntegralF (AstRanked s r n)
deriving instance Fractional (AstTensor AstMethodLet s (TKR r n))
                  => Fractional (AstRanked s r n)
deriving instance Floating (AstTensor AstMethodLet s (TKR r n))
                  => Floating (AstRanked s r n)
deriving instance (RealFrac (AstTensor AstMethodLet s (TKR r n)))
                  => RealFrac (AstRanked s r n)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKR r n)))
                  => RealFloatF (AstRanked s r n)

type instance BoolOf (AstShaped s) = AstBool AstMethodLet

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

{-deriving instance IfF (AstShaped s)
deriving instance AstSpan s => EqF (AstShaped s)
deriving instance AstSpan s => OrdF (AstShaped s)-}
deriving instance Eq (AstShaped s r sh)
deriving instance Ord (AstShaped s r sh)
deriving instance Num (AstTensor AstMethodLet s (TKS r sh)) => Num (AstShaped s r sh)
deriving instance (Real (AstTensor AstMethodLet s (TKS r sh)))
                   => Real (AstShaped s r sh)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKS r sh)))
                  => IntegralF (AstShaped s r sh)
deriving instance Fractional (AstTensor AstMethodLet s (TKS r sh))
                  => Fractional (AstShaped s r sh)
deriving instance Floating (AstTensor AstMethodLet s (TKS r sh))
                  => Floating (AstShaped s r sh)
deriving instance (RealFrac (AstTensor AstMethodLet s (TKS r sh)))
                  => RealFrac (AstShaped s r sh)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKS r sh)))
                  => RealFloatF (AstShaped s r sh)

instance (GoodScalar r, KnownNat n, RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstRanked s r n) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstRanked s) (AstRanked s Double n) #-}
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit = fromHVectorR

instance (GoodScalar r, KnownNat n, RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstGeneric AstMethodLet s r n) where
  toHVector = rankedHVector . V.singleton . DynamicRanked
  fromHVector _aInit hv = case fromHVectorR hv of
    Nothing -> Nothing
    Just (ranked, rest) -> Just (AstGeneric $ unAstRanked ranked, rest)

instance (RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (DynamicTensor (AstGeneric AstMethodLet s)) where
  toHVector = rankedHVector . V.singleton
  fromHVector _aInit hv = case V.uncons $ unRankedHVector hv of
    Nothing -> Nothing
    Just (generic, rest) ->
      Just (generic, rankedHVector rest)

instance (GoodScalar r, KnownNat n, AstSpan s)
         => DualNumberValue (AstRanked s r n) where
  type DValue (AstRanked s r n) = ORArray r n
  fromDValue t = AstRanked $ fromPrimal $ AstConst $ runFlipR t

instance (GoodScalar r, KnownNat n)
         => TermValue (AstRanked FullSpan r n) where
  type Value (AstRanked FullSpan r n) = ORArray r n
  fromValue t = AstRanked $ fromPrimal $ AstConst $ runFlipR t

instance (GoodScalar r, KnownShS sh, ShapedTensor (AstShaped s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstShaped s r sh) where
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit = fromHVectorS

instance (GoodScalar r, KnownShS sh, AstSpan s)
         => DualNumberValue (AstShaped s r sh) where
  type DValue (AstShaped s r sh) = OSArray r sh
  fromDValue t = AstShaped $ fromPrimal $ AstConstS $ runFlipS t

instance (GoodScalar r, KnownShS sh)
         => TermValue (AstShaped FullSpan r sh) where
  type Value (AstShaped FullSpan r sh) = OSArray r sh
  fromValue t = AstShaped $ fromPrimal $ AstConstS $ runFlipS t

{- This is needed by only one test, testSin0revhFold5S, now disabled
and this possibly breaks the cfwdOnHVector duplicability invariant in cfwd.
Analyze and, if possible, remove together with toHVectorOf.
instance AdaptableHVector (AstRanked s) (AstTensor AstMethodLet s TKUntyped) where
  toHVector = undefined  -- impossible without losing sharing
  toHVectorOf = id  -- but this is possible
  fromHVector aInit params =
    let (portion, rest) = V.splitAt (V.length $ shapeAstHVector aInit) params
    in Just (AstMkHVector $ unRankedHVector portion, rest)
-}

-- HVector causes overlap and violation of injectivity,
-- hence Data.NonStrict.Vector. Injectivity is crucial to limit the number
-- of type applications the library user has to supply.
instance TermValue (AstTensor AstMethodLet FullSpan TKUntyped) where
  type Value (AstTensor AstMethodLet FullSpan TKUntyped) =
    Data.NonStrict.Vector.Vector (DynamicTensor ORArray)
  fromValue t = AstMkHVector $ V.convert $ V.map fromValue t

instance TermValue (HVectorPseudoTensor (AstRanked FullSpan) r y) where
  type Value (HVectorPseudoTensor (AstRanked FullSpan) r y) =
    HVectorPseudoTensor ORArray r y
  fromValue (HVectorPseudoTensor t) =
    HVectorPseudoTensor $ AstMkHVector $ V.map fromValue t

instance TermValue (DynamicTensor (AstGeneric AstMethodLet FullSpan)) where
  type Value (DynamicTensor (AstGeneric AstMethodLet FullSpan)) =
    DynamicTensor ORArray
  fromValue = \case
    DynamicRanked t -> DynamicRanked $ AstGeneric $ fromPrimal $ AstConst $ runFlipR t
    DynamicShaped @_ @sh t ->
      gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: X.Rank sh) $
      DynamicShaped @_ @sh $ AstGenericS $ fromPrimal $ AstConstS $ runFlipS t
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2

instance ProductTensor (AstRanked s) where
  ttuple t1 t2 = astTuple (unRankedY stensorKind t1)
                          (unRankedY stensorKind t2)
  tproject1 = rankedY stensorKind . astProject1
  tproject2 = rankedY stensorKind . astProject2
  tmkHVector = AstMkHVector . unRankedHVector

rankedY :: STensorKindType y -> AstTensor AstMethodLet s y
        -> InterpretationTarget (AstRanked s) y
rankedY stk t = case stk of
  STKR{} -> AstRanked t
  STKS{} -> AstShaped t
  STKProduct{} -> t
  STKUntyped -> HVectorPseudoTensor t

unRankedY :: STensorKindType y -> InterpretationTarget (AstRanked s) y
          -> AstTensor AstMethodLet s y
unRankedY stk t = case stk of
  STKR{} -> unAstRanked t
  STKS{} -> unAstShaped t
  STKProduct{} -> t
  STKUntyped -> unHVectorPseudoTensor t

astLetHVectorInFun
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => AstTensor AstMethodLet s TKUntyped -> (HVector (AstGeneric AstMethodLet s) -> AstTensor AstMethodLet s (TKR r n))
  -> AstTensor AstMethodLet s (TKR r n)
{-# INLINE astLetHVectorInFun #-}
astLetHVectorInFun a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorIn vars a (f asts)

astLetHFunInFun
  :: (GoodScalar r, KnownNat n, TensorKind x, TensorKind z)
  => AstHFun x z -> (AstHFun x z -> AstTensor AstMethodLet s (TKR r n))
  -> AstTensor AstMethodLet s (TKR r n)
{-# INLINE astLetHFunInFun #-}
astLetHFunInFun a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunIn var a (f ast)

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
  AstDualPart $ AstConstant t  -- this is nil; likely to happen
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
astBuild1Vectorize :: (KnownNat n, GoodScalar r, AstSpan s)
                   => Int -> (AstInt AstMethodLet -> AstTensor AstMethodLet s (TKR r n))
                   -> AstTensor AstMethodLet s (TKR r (1 + n))
astBuild1Vectorize k f = withSNat k $ \snat ->
  build1Vectorize snat $ funToAstI f

astLetHVectorInFunS
  :: forall sh s r. (KnownShS sh, GoodScalar r, AstSpan s)
  => AstTensor AstMethodLet s TKUntyped -> (HVector (AstGeneric AstMethodLet s) -> AstTensor AstMethodLet s (TKS r sh))
  -> AstTensor AstMethodLet s (TKS r sh)
{-# INLINE astLetHVectorInFunS #-}
astLetHVectorInFunS a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorIn vars a (f asts)

astLetHFunInFunS
  :: (GoodScalar r, KnownShS sh, TensorKind x, TensorKind z)
  => AstHFun x z -> (AstHFun x z -> AstTensor AstMethodLet s (TKS r sh))
  -> AstTensor AstMethodLet s (TKS r sh)
{-# INLINE astLetHFunInFunS #-}
astLetHFunInFunS a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunIn var a (f ast)

astBuild1VectorizeS :: forall n sh r s.
                       (KnownNat n, KnownShS sh, GoodScalar r, AstSpan s)
                    => (AstInt AstMethodLet -> AstTensor AstMethodLet s (TKS r sh))
                    -> AstTensor AstMethodLet s (TKS r (n ': sh))
astBuild1VectorizeS f =
  build1Vectorize (SNat @n) $ funToAstI f

astLetHVectorInHVectorFun
  :: AstSpan s
  => AstTensor AstMethodLet s TKUntyped -> (HVector (AstGeneric AstMethodLet s) -> AstTensor AstMethodLet s TKUntyped)
  -> AstTensor AstMethodLet s TKUntyped
{-# INLINE astLetHVectorInHVectorFun #-}
astLetHVectorInHVectorFun a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorIn vars a (f asts)

astLetHFunInHVectorFun
  :: (TensorKind x, TensorKind z)
  => AstHFun x z -> (AstHFun x z -> AstTensor AstMethodLet s TKUntyped)
  -> AstTensor AstMethodLet s TKUntyped
{-# INLINE astLetHFunInHVectorFun #-}
astLetHFunInHVectorFun a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunIn var a (f ast)

astBuildHVector1Vectorize
  :: AstSpan s
  => SNat k -> (AstInt AstMethodLet -> AstTensor AstMethodLet s TKUntyped) -> AstTensor AstMethodLet s TKUntyped
astBuildHVector1Vectorize k f = build1Vectorize k $ funToAstI f

-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: TensorKindFull TKUntyped
  -> HVectorPseudoTensor (AstRaw PrimalSpan) Float '()
  -> Maybe (HVectorPseudoTensor (AstRaw PrimalSpan) Float '())
  -> Delta (AstRaw PrimalSpan) TKUntyped
  -> InterpretationTarget (AstRaw PrimalSpan) TKUntyped #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (AstRaw PrimalSpan) -> EvalState (AstRaw PrimalSpan) #-}

instance AstSpan s => LetTensor (AstRanked s) (AstShaped s) where
  rletTKIn :: forall y n r. (TensorKind y, KnownNat n, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstRanked s) y
           -> (InterpretationTarget (AstRanked s) y -> AstRanked s r n)
           -> AstRanked s r n
  rletTKIn stk a f =
    AstRanked
    $ astLetFun @y @_ @s (unRankedY stk a) (unAstRanked . f . rankedY stk)
  rletHVectorIn a f =
    AstRanked
    $ astLetHVectorInFun a (unAstRanked . f . rankedHVector)
  rletHFunIn a f = AstRanked $ astLetHFunInFun a (unAstRanked . f)

  sletTKIn :: forall y sh r. (TensorKind y, GoodScalar r, KnownShS sh)
           => STensorKindType y -> InterpretationTarget (AstRanked s) y
           -> (InterpretationTarget (AstRanked s) y -> AstShaped s r sh)
           -> AstShaped s r sh
  sletTKIn stk a f =
    AstShaped
    $ astLetFun @y @_ @s (unRankedY stk a) (unAstShaped . f . rankedY stk)
  sletHVectorIn a f =
    AstShaped
    $ astLetHVectorInFunS a (unAstShaped . f . rankedHVector)
  sletHFunIn a f = AstShaped $ astLetHFunInFunS a (unAstShaped . f)

  dletHVectorInHVector u f = astLetHVectorInHVectorFun u (f . rankedHVector)
  dletHFunInHVector = astLetHFunInHVectorFun
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => InterpretationTarget (AstRanked s) x
       -> (ConcreteTarget (AstRanked s) x
           -> InterpretationTarget (AstRanked s) z)
       -> InterpretationTarget (AstRanked s) z
  tlet u f = case stensorKind @x of
    STKR{} ->
      rankedY (stensorKind @z)
      $ astLetFun (unAstRanked u)
                  (unRankedY (stensorKind @z) . f . AstRanked)
    STKS{} ->
      rankedY (stensorKind @z)
      $ astLetFun (unAstShaped u)
                  (unRankedY (stensorKind @z) . f . AstShaped)
    STKProduct{} ->
      blet u $ \ !uShared -> f (tproject1 uShared, tproject2 uShared)
    STKUntyped{} -> case stensorKind @z of
      STKR{} ->
        AstRanked
        $ astLetHVectorInFun (unHVectorPseudoTensor u)
                             (unAstRanked . f . rankedHVector)
      STKS{} ->
        AstShaped
        $ astLetHVectorInFunS (unHVectorPseudoTensor u)
                              (unAstShaped . f . rankedHVector)
      STKProduct{} ->
        blet u $ \ !uShared -> f $ dunHVector $ unHVectorPseudoTensor uShared
      STKUntyped{} ->
        HVectorPseudoTensor
        $ astLetHVectorInHVectorFun (unHVectorPseudoTensor u)
                                    (unHVectorPseudoTensor . f . rankedHVector)
  blet :: forall x z. (TensorKind x, TensorKind z)
       => InterpretationTarget (AstRanked s) x
       -> (InterpretationTarget (AstRanked s) x
           -> InterpretationTarget (AstRanked s) z)
       -> InterpretationTarget (AstRanked s) z
  blet u f = case stensorKind @x of
    STKR{} ->
      rankedY (stensorKind @z)
      $ astLetFun (unAstRanked u)
                  (unRankedY (stensorKind @z) . f . AstRanked)
    STKS{} ->
      rankedY (stensorKind @z)
      $ astLetFun (unAstShaped u)
                  (unRankedY (stensorKind @z) . f . AstShaped)
    STKProduct{} ->
      rankedY (stensorKind @z)
      $ astLetFun u
                  (unRankedY (stensorKind @z) . f)
    STKUntyped{} ->
      rankedY (stensorKind @z)
      $ astLetFun (unHVectorPseudoTensor u)
                  (unRankedY (stensorKind @z) . f . HVectorPseudoTensor)

  -- TODO: remove unsafeCoerce here and below
  toShare :: forall y. TensorKind y
          => InterpretationTarget (AstRanked s) y
          -> InterpretationTarget (AstRaw s) y
  toShare t = case stensorKind @y of
    STKR{} -> AstRaw $ unsafeCoerce $ unAstRanked t
    STKS{} -> AstRawS $ unsafeCoerce $ unAstShaped t
    STKProduct{} -> AstRawWrap $ unsafeCoerce t
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap $ unsafeCoerce
                  $ unHVectorPseudoTensor t
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tunshare :: forall y. TensorKind y
           => InterpretationTarget (AstRaw s) y
           -> InterpretationTarget (AstRanked s) y
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> gunshare (stensorKind @y)
      _ -> error "tunshare: used not at PrimalSpan"
  tconstant stk t = case stk of
    STKR{} -> rconstant t
    STKS{} -> sconstant t
    STKProduct{} -> fromPrimal t
    STKUntyped -> HVectorPseudoTensor $ fromPrimal $ unHVectorPseudoTensor t

  rrev :: forall r n. (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (AstRanked s)
       -> AstTensor AstMethodLet s TKUntyped
  rrev f parameters0 =  -- we don't have an AST constructor to hold it
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new @parmeters@, which is much better than computing anew.
    let g :: InterpretationTarget (AstRanked FullSpan) TKUntyped
          -> InterpretationTarget (AstRanked FullSpan) (TKR r n)
        g !hv = tlet hv $ \ !hvShared -> f hvShared
        !(!(AstArtifactRev _varDt var gradient _primal), _delta) =
          revProduceArtifact False g emptyEnv (FTKUntyped parameters0)
    in \ !parameters -> assert (voidHVectorMatches parameters0 parameters) $
      let env = extendEnv
                  var (HVectorPseudoTensor $ AstMkHVector (unRankedHVector parameters)) emptyEnv
      in simplifyInline $ unHVectorPseudoTensor
         $ interpretAst env $ unHVectorPseudoTensor gradient
        -- this interpretation both substitutes parameters for the variables and
        -- reinterprets @PrimalSpan@ terms in @s@ terms;
        -- we could shortcut when @s@ is @PrimalSpan@ and @parameters@
        -- are the same variables, but it's a very special case;
        -- a faster implementation would be via AstHApply, but this tests
        -- a slightly different code path, so let's keep it

instance AstSpan s => RankedTensor (AstRanked s) where
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
  rfromS = AstRanked . astRFromS . unAstShaped

  rconstant = AstRanked . fromPrimal . unAstRanked
  rprimalPart = AstRanked . astSpanPrimal . unAstRanked
  rdualPart = AstRanked . astSpanDual . unAstRanked
  rD u u' = AstRanked $ astSpanD (unAstRanked u) (unAstRanked u')
  rScale s t = AstRanked $ astDualPart $ AstConstant (unAstRanked s) * AstD (unAstRanked $ rzero (rshape s)) (unAstRanked t)

instance AstSpan s => ShapedTensor (AstShaped s) where
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
  sfromR = AstShaped . astSFromR . unAstRanked

  sconstant = AstShaped . fromPrimal . unAstShaped
  sprimalPart = AstShaped . astSpanPrimal . unAstShaped
  sdualPart = AstShaped . astSpanDual . unAstShaped
  sD u u' = AstShaped $ astSpanD (unAstShaped u) (unAstShaped u')
  sScale s t = AstShaped $ astDualPart $ AstConstant (unAstShaped s) * AstD 0 (unAstShaped t)

instance forall s. AstSpan s => HVectorTensor (AstRanked s) (AstShaped s) where
  dshape = shapeAstHVector
  tshapeFull stk t = case stk of
    STKR{} -> shapeAstFull $ unAstRanked t
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (tproject1 t))
                                       (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unHVectorPseudoTensor t
  tcond stk b u v = case stk of
    STKR{} -> ifF b u v
    STKS{} -> ifF b u v
    STKProduct{} -> AstCond b u v
    STKUntyped -> HVectorPseudoTensor
                  $ AstCond b (unHVectorPseudoTensor u)
                              (unHVectorPseudoTensor v)
  tprimalPart stk t = case stk of
    STKR{} -> rprimalPart t
    STKS{} -> sprimalPart t
    STKProduct{} -> astSpanPrimal t
    STKUntyped -> HVectorPseudoTensor $ astSpanPrimal $ unHVectorPseudoTensor t
  dmkHVector = AstMkHVector . unRankedHVector
  dlambda :: forall x z. (TensorKind x, TensorKind z)
          => TensorKindFull x -> HFun x z -> HFunOf (AstRanked s) x z
  dlambda shss f =
    let (var, ast) = funToAst shss $ \ !ll ->
          unRankedY (stensorKind @z) $ unHFun f $ rankedY (stensorKind @x) ll
    in AstLambda (var, shss, ast)
  dHApply :: forall x z. (TensorKind x, TensorKind z)
          => HFunOf (AstRanked s) x z
          -> InterpretationTarget (AstRanked s) x
          -> InterpretationTarget (AstRanked s) z
  dHApply t ll = rankedY (stensorKind @z) $ astHApply t
                 $ unRankedY (stensorKind @x) ll
  dunHVector (AstMkHVector l) = rankedHVector l
  dunHVector hVectorOf =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic AstMethodLet s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstGeneric $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstGenericS $ AstProjectS hVectorOf i
    in rankedHVector $ V.imap f $ shapeAstHVector hVectorOf
  dbuild1 k f = astBuildHVector1Vectorize k (f . AstRanked)
  -- TODO: (still) relevant?
  -- In this instance, these two ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstRanked to AstRaw.
  drevDt :: forall x z. (TensorKind x, TensorKind z)
         => TensorKindFull x
         -> HFun x z
         -> AstHFun (TKProduct z x) x
  drevDt ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let -- No bangs here, because this goes under lambda and may be unneeded
        -- or even incorrect (and so, e.g., trigger
        -- `error "tunshare: used not at PrimalSpan"`, because no derivative
        -- should be taken of spans other than PrimalSpan)
        (AstArtifactRev varDt var gradient primal, _delta) =
          revProduceArtifact True (unHFun f) emptyEnv ftkx
        ftkz = shapeAstFull $ unRankedY (stensorKind @z) primal
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          AstLet varDt (astProject1 astP)
            $ AstLet var (astProject2 astP)
              $ simplifyInline $ unRankedY (stensorKind @x) gradient
    in AstLambda (varP, ftk2, ast)
  dfwd :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
       -> HFun x z
       -> AstHFun (TKProduct x x) z
  dfwd ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactFwd varDs var derivative _primal, _delta) =
          fwdProduceArtifact (unHFun f) emptyEnv ftkx
        ftk2 = FTKProduct ftkx ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          AstLet varDs (astProject1 astP)
            $ AstLet var (astProject2 astP)
              $ simplifyInline $ unRankedY (stensorKind @z) derivative
    in AstLambda (varP, ftk2, ast)
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    rankedY (stensorKind @TKUntyped)
    $ AstMapAccumRDer k accShs bShs eShs f df rf
                      (unRankedY (stensorKind @TKUntyped) acc0)
                      (unRankedY (stensorKind @TKUntyped) es)
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    rankedY (stensorKind @TKUntyped)
    $ AstMapAccumLDer k accShs bShs eShs f df rf
                      (unRankedY (stensorKind @TKUntyped) acc0)
                      (unRankedY (stensorKind @TKUntyped) es)


-- * The AstRaw instances

type instance BoolOf (AstRaw s) = AstBool AstMethodShare

{-deriving instance IfF (AstRaw s)
deriving instance AstSpan s => EqF (AstRaw s)
deriving instance AstSpan s => OrdF (AstRaw s)-}

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
  AstDualPart $ AstConstant t  -- this is nil; likely to happen
astSpanDualRaw t | Just Refl <- sameAstSpan @s @DualSpan = t
astSpanDualRaw t | Just Refl <- sameAstSpan @s @FullSpan = AstDualPart t
astSpanDualRaw _ = error "a spuriuos case for pattern match coverage"

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
deriving instance Eq (AstRaw s r n)
deriving instance Ord (AstRaw s r n)
deriving instance Num (AstTensor AstMethodShare s (TKR r n)) => Num (AstRaw s r n)
deriving instance (Real (AstTensor AstMethodShare s (TKR r n)))
                   => Real (AstRaw s r n)
deriving instance (IntegralF (AstTensor AstMethodShare s (TKR r n)))
                  => IntegralF (AstRaw s r n)
deriving instance Fractional (AstTensor AstMethodShare s (TKR r n))
                  => Fractional (AstRaw s r n)
deriving instance Floating (AstTensor AstMethodShare s (TKR r n))
                  => Floating (AstRaw s r n)
deriving instance (RealFrac (AstTensor AstMethodShare s (TKR r n)))
                  => RealFrac (AstRaw s r n)
deriving instance (RealFloatF (AstTensor AstMethodShare s (TKR r n)))
                  => RealFloatF (AstRaw s r n)

type instance BoolOf (AstRawS s) = AstBool AstMethodShare

instance IfF (AstRawS s) where
  ifF cond a b = AstRawS $ AstCond cond (unAstRawS a) (unAstRawS b)
instance AstSpan s => EqF (AstRawS s) where
  AstRawS v ==. AstRawS u = AstRelS EqOp (astSpanPrimalRaw v) (astSpanPrimalRaw u)
  AstRawS v /=. AstRawS u = AstRelS NeqOp (astSpanPrimalRaw v) (astSpanPrimalRaw u)
instance AstSpan s => OrdF (AstRawS s) where
  v <. u = AstRelS LsOp (astSpanPrimalRaw (unAstRawS v)) (astSpanPrimalRaw (unAstRawS u))
  v <=. u = AstRelS LeqOp (astSpanPrimalRaw (unAstRawS v)) (astSpanPrimalRaw (unAstRawS u))
  v >. u = AstRelS GtOp (astSpanPrimalRaw (unAstRawS v)) (astSpanPrimalRaw (unAstRawS u))
  v >=. u = AstRelS GeqOp (astSpanPrimalRaw (unAstRawS v)) (astSpanPrimalRaw (unAstRawS u))
deriving instance Eq (AstRawS s r sh)
deriving instance Ord (AstRawS s r sh)
deriving instance Num (AstTensor AstMethodShare s (TKS r sh)) => Num (AstRawS s r sh)
deriving instance (IntegralF (AstTensor AstMethodShare s (TKS r sh)))
                  => IntegralF (AstRawS s r sh)
deriving instance Fractional (AstTensor AstMethodShare s (TKS r sh))
                  => Fractional (AstRawS s r sh)
deriving instance Floating (AstTensor AstMethodShare s (TKS r sh))
                  => Floating (AstRawS s r sh)
deriving instance (RealFloatF (AstTensor AstMethodShare s (TKS r sh)))
                  => RealFloatF (AstRawS s r sh)

type instance InterpretationTarget (AstRaw s) (TKProduct x z) =
  AstRawWrap (AstTensor AstMethodShare s (TKProduct x z))

instance Show (InterpretationTargetProductN (AstRaw s) x y) where
  showsPrec d (InterpretationTargetProductN t) = showsPrec d t

instance ProductTensor (AstRaw s) where
  ttuple t1 t2 = AstRawWrap $ AstTuple (unRawY stensorKind t1)
                                       (unRawY stensorKind t2)
  tproject1 t = rawY stensorKind $ AstProject1 $ unAstRawWrap t
  tproject2 t = rawY stensorKind $ AstProject2 $ unAstRawWrap t
  tmkHVector = AstRawWrap . AstMkHVector . unRawHVector

rawY :: STensorKindType y -> AstTensor AstMethodShare s y
     -> InterpretationTarget (AstRaw s) y
rawY stk t = case stk of
  STKR{} -> AstRaw t
  STKS{} -> AstRawS t
  STKProduct{} -> AstRawWrap t
  STKUntyped -> HVectorPseudoTensor $ AstRawWrap t

unRawY :: STensorKindType y -> InterpretationTarget (AstRaw s) y
       -> AstTensor AstMethodShare s y
unRawY stk t = case stk of
  STKR{} -> unAstRaw t
  STKS{} -> unAstRawS t
  STKProduct{} -> unAstRawWrap t
  STKUntyped -> unAstRawWrap $ unHVectorPseudoTensor t

instance ShareTensor (AstRaw s) where
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tshare :: forall y. TensorKind y
         => InterpretationTarget (AstRaw s) y -> InterpretationTarget (AstRaw s) y
  tshare t = case stensorKind @y of
    STKR{} | astIsSmall True (unAstRaw t) -> t
    STKR{} -> case t of
      AstRaw (AstShare{}) -> t
      _ -> AstRaw $ fun1ToAst $ \ !var -> AstShare var (unAstRaw t)
    STKS{} | astIsSmall True (unAstRawS t) -> t
    STKS{} -> case t of
      AstRawS (AstShare{}) -> t
      _ -> AstRawS $ fun1ToAst $ \ !var -> AstShare var (unAstRawS t)
    STKProduct{} | astIsSmall True (unAstRawWrap t) -> t
    STKProduct{} -> case t of
      AstRawWrap (AstShare{}) -> t
      _ -> let tShared = AstRawWrap $ fun1ToAst $ \ !var ->
                 AstShare var (unAstRawWrap t)
           in ttuple (tproject1 tShared) (tproject2 tShared)
    STKUntyped{} | astIsSmall True (unAstRawWrap $ unHVectorPseudoTensor t) -> t
    STKUntyped{} -> case unHVectorPseudoTensor t of
      AstRawWrap (AstShare{}) -> t
      _ -> HVectorPseudoTensor $ AstRawWrap $ fun1ToAst $ \ !var ->
             AstShare var $ unAstRawWrap $ unHVectorPseudoTensor t

instance AstSpan s => RankedTensor (AstRaw s) where
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
  rconst = AstRaw . fromPrimal . AstConst
  rfromS = AstRaw . AstRFromS . unAstRawS

  rconstant = AstRaw . fromPrimal . unAstRaw
  rprimalPart = AstRaw . astSpanPrimalRaw . unAstRaw
  rdualPart = AstRaw . astSpanDualRaw . unAstRaw
  rD u u' = AstRaw $ astSpanD (unAstRaw u) (unAstRaw u')
  rScale s t = AstRaw $ AstDualPart
               $ AstConstant (unAstRaw s)
                 * AstD (unAstRaw $ rzero (rshape s)) (unAstRaw t)

instance AstSpan s => ShapedTensor (AstRawS s) where
  sminIndex = AstRawS . fromPrimal . AstMinIndexS . astSpanPrimalRaw . unAstRawS
  smaxIndex = AstRawS . fromPrimal . AstMaxIndexS . astSpanPrimalRaw . unAstRawS
  sfloor = AstRawS . fromPrimal . AstFloorS . astSpanPrimalRaw . unAstRawS
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
                  . astSpanPrimalRaw . unAstRawS
  sconst = AstRawS . fromPrimal . AstConstS
  sfromR = AstRawS . AstSFromR . unAstRaw

  sconstant = AstRawS . fromPrimal . unAstRawS
  sprimalPart = AstRawS . astSpanPrimalRaw . unAstRawS
  sdualPart = AstRawS . astSpanDualRaw . unAstRawS
  sD u u' = AstRawS $ astSpanD (unAstRawS u) (unAstRawS u')
  sScale s t = AstRawS $ AstDualPart
               $ AstConstant (unAstRawS s) * AstD 0 (unAstRawS t)

instance AstSpan s => HVectorTensor (AstRaw s) (AstRawS s) where
  dshape = shapeAstHVector . unAstRawWrap
  tshapeFull stk t = case stk of
    STKR{} -> shapeAstFull $ unAstRaw t
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (tproject1 t))
                                       (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unAstRawWrap $ unHVectorPseudoTensor t
  tcond stk b u v = case stk of
    STKR{} -> ifF b u v
    STKS{} -> ifF b u v
    STKProduct{} -> AstRawWrap
                    $ AstCond b (unAstRawWrap u) (unAstRawWrap v)
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap
                  $ AstCond b (unAstRawWrap $ unHVectorPseudoTensor u)
                              (unAstRawWrap $ unHVectorPseudoTensor v)
  tprimalPart stk t = case stk of
    STKR{} -> rprimalPart t
    STKS{} -> sprimalPart t
    STKProduct{} -> AstRawWrap $ astSpanPrimalRaw $ unAstRawWrap t
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap
                  $ astSpanPrimalRaw $ unAstRawWrap $ unHVectorPseudoTensor t
  dmkHVector = AstRawWrap . AstMkHVector . unRawHVector
  dlambda = dlambda @(AstRanked s)
  dHApply :: forall x z. (TensorKind x, TensorKind z)
          => HFunOf (AstRaw s) x z
          -> InterpretationTarget (AstRaw s) x
          -> InterpretationTarget (AstRaw s) z
  dHApply t ll =
    let app = AstHApply t $ unRawY (stensorKind @x) ll
    in rawY (stensorKind @z) app
  dunHVector (AstRawWrap (AstMkHVector l)) = rawHVector l
  dunHVector (AstRawWrap hVectorOf) =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic AstMethodShare s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstGeneric $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstGenericS $ AstProjectS hVectorOf i
    in rawHVector $ V.imap f $ shapeAstHVector hVectorOf
  dbuild1 k f = AstRawWrap
                $ AstBuildHVector1 k $ funToAstI (unAstRawWrap . f . AstRaw)
  -- TODO: (still) relevant?
  -- In this instance, these two ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstRanked to AstRaw.
  --
  -- TODO: dupe?
  -- These three methods are called at this type in delta evaluation via
  -- dmapAccumR and dmapAccumL, they have to work. We could refrain from
  -- simplifying the resulting terms, but it's not clear that's more consistent.
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    rawY (stensorKind @TKUntyped)
    $ AstMapAccumRDer k accShs bShs eShs f df rf
                      (unRawY (stensorKind @TKUntyped) acc0)
                      (unRawY (stensorKind @TKUntyped) es)
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    rawY (stensorKind @TKUntyped)
    $ AstMapAccumLDer k accShs bShs eShs f df rf
                      (unRawY (stensorKind @TKUntyped) acc0)
                      (unRawY (stensorKind @TKUntyped) es)


-- * The AstNoVectorize

type instance BoolOf (AstNoVectorize s) = AstBool AstMethodLet

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
deriving instance Num (AstTensor AstMethodLet s (TKR r n)) => Num (AstNoVectorize s r n)
deriving instance (Real (AstTensor AstMethodLet s (TKR r n)))
                   => Real (AstNoVectorize s r n)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKR r n)))
                  => IntegralF (AstNoVectorize s r n)
deriving instance Fractional (AstTensor AstMethodLet s (TKR r n))
                  => Fractional (AstNoVectorize s r n)
deriving instance Floating (AstTensor AstMethodLet s (TKR r n))
                  => Floating (AstNoVectorize s r n)
deriving instance (RealFrac (AstTensor AstMethodLet s (TKR r n)))
                  => RealFrac (AstNoVectorize s r n)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKR r n)))
                  => RealFloatF (AstNoVectorize s r n)

type instance BoolOf (AstNoVectorizeS s) = AstBool AstMethodLet

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
deriving instance Num (AstTensor AstMethodLet s (TKS r sh)) => Num (AstNoVectorizeS s r sh)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKS r sh)))
                  => IntegralF (AstNoVectorizeS s r sh)
deriving instance Fractional (AstTensor AstMethodLet s (TKS r sh))
                  => Fractional (AstNoVectorizeS s r sh)
deriving instance Floating (AstTensor AstMethodLet s (TKS r sh))
                  => Floating (AstNoVectorizeS s r sh)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKS r sh)))
                  => RealFloatF (AstNoVectorizeS s r sh)

type instance InterpretationTarget (AstNoVectorize s) (TKProduct x z) =
  AstNoVectorizeWrap (AstTensor AstMethodLet s (TKProduct x z))

instance Show (InterpretationTargetProductN (AstNoVectorize s) x y) where
  showsPrec d (InterpretationTargetProductN t) = showsPrec d t

instance ProductTensor (AstNoVectorize s) where
  ttuple t1 t2 = AstNoVectorizeWrap $ astTuple (unNoVectorizeY stensorKind t1)
                                               (unNoVectorizeY stensorKind t2)
  tproject1 t = noVectorizeY stensorKind $ astProject1 $ unAstNoVectorizeWrap t
  tproject2 t = noVectorizeY stensorKind $ astProject2 $ unAstNoVectorizeWrap t
  tmkHVector = AstNoVectorizeWrap . AstMkHVector . unNoVectorizeHVector

noVectorizeY :: STensorKindType y -> AstTensor AstMethodLet s y
             -> InterpretationTarget (AstNoVectorize s) y
noVectorizeY stk t = case stk of
  STKR{} -> AstNoVectorize t
  STKS{} -> AstNoVectorizeS t
  STKProduct{} -> AstNoVectorizeWrap t
  STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap t

unNoVectorizeY :: STensorKindType y -> InterpretationTarget (AstNoVectorize s) y
               -> AstTensor AstMethodLet s y
unNoVectorizeY stk t = case stk of
  STKR{} -> unAstNoVectorize t
  STKS{} -> unAstNoVectorizeS t
  STKProduct{} -> unAstNoVectorizeWrap t
  STKUntyped -> unAstNoVectorizeWrap $ unHVectorPseudoTensor t

astLetFunNoSimplify :: forall y z s.
                       (TensorKind y, TensorKind z, AstSpan s)
                    => AstTensor AstMethodLet s y -> (AstTensor AstMethodLet s y -> AstTensor AstMethodLet s z)
                    -> AstTensor AstMethodLet s z
astLetFunNoSimplify a f | astIsSmall True a = f a  -- too important an optimization
astLetFunNoSimplify a f =
  let sh = shapeAstFull a
      (var, ast) = funToAst sh f
  in AstLet var a ast  -- safe, because subsitution ruled out above

astLetHVectorInFunNoSimplify
  :: forall n s r. (AstSpan s, GoodScalar r, KnownNat n)
  => AstTensor AstMethodLet s TKUntyped -> (HVector (AstGeneric AstMethodLet s) -> AstTensor AstMethodLet s (TKR r n))
  -> AstTensor AstMethodLet s (TKR r n)
astLetHVectorInFunNoSimplify a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorIn vars a (f asts)

astLetHVectorInFunNoSimplifyS
  :: forall sh s r. (AstSpan s, KnownShS sh, GoodScalar r)
  => AstTensor AstMethodLet s TKUntyped -> (HVector (AstGeneric AstMethodLet s) -> AstTensor AstMethodLet s (TKS r sh))
  -> AstTensor AstMethodLet s (TKS r sh)
astLetHVectorInFunNoSimplifyS a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorIn vars a (f asts)

astLetHFunInFunNoSimplify
  :: (GoodScalar r, KnownNat n, TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor AstMethodLet s (TKR r n))
  -> AstTensor AstMethodLet s (TKR r n)
astLetHFunInFunNoSimplify a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunIn var a (f ast)

astLetHFunInFunNoSimplifyS
  :: (GoodScalar r, KnownShS sh, TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor AstMethodLet s (TKS r sh))
  -> AstTensor AstMethodLet s (TKS r sh)
astLetHFunInFunNoSimplifyS a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunIn var a (f ast)

astLetHVectorInHVectorFunNoSimplify
  :: AstSpan s
  => AstTensor AstMethodLet s TKUntyped -> (HVector (AstGeneric AstMethodLet s) -> AstTensor AstMethodLet s TKUntyped)
  -> AstTensor AstMethodLet s TKUntyped
astLetHVectorInHVectorFunNoSimplify a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorIn vars a (f asts)

astLetHFunInHVectorFunNoSimplify
  :: (TensorKind x, TensorKind y)
  => AstHFun x y -> (AstHFun x y -> AstTensor AstMethodLet s TKUntyped)
  -> AstTensor AstMethodLet s TKUntyped
astLetHFunInHVectorFunNoSimplify a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunIn var a (f ast)

unAstNoVectorize2 :: AstNoVectorize s r n -> AstRanked s r n
unAstNoVectorize2 = AstRanked . unAstNoVectorize

astNoVectorize2 :: AstRanked s r n -> AstNoVectorize s r n
astNoVectorize2 = AstNoVectorize . unAstRanked

unAstNoVectorizeS2 :: AstNoVectorizeS s r sh -> AstShaped s r sh
unAstNoVectorizeS2 = AstShaped . unAstNoVectorizeS

astNoVectorizeS2 :: AstShaped s r sh -> AstNoVectorizeS s r sh
astNoVectorizeS2 = AstNoVectorizeS . unAstShaped

unNoVectorizeHVector :: HVector (AstNoVectorize s) -> HVector (AstGeneric AstMethodLet s)
unNoVectorizeHVector =
  let f (DynamicRanked (AstNoVectorize t)) = DynamicRanked (AstGeneric t)
      f (DynamicShaped (AstNoVectorizeS t)) = DynamicShaped (AstGenericS t)
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

unNoVectorizeHVectorR :: HVector (AstNoVectorize s) -> HVector (AstRanked s)
unNoVectorizeHVectorR =
  let f (DynamicRanked (AstNoVectorize t)) = DynamicRanked (AstRanked t)
      f (DynamicShaped (AstNoVectorizeS t)) = DynamicShaped (AstShaped t)
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noVectorizeHVectorR :: HVector (AstRanked s) -> HVector (AstNoVectorize s)
noVectorizeHVectorR =
  let f (DynamicRanked (AstRanked t)) = DynamicRanked $ AstNoVectorize t
      f (DynamicShaped (AstShaped t)) = DynamicShaped $ AstNoVectorizeS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

instance AstSpan s => LetTensor (AstNoVectorize s) (AstNoVectorizeS s) where
  rletTKIn :: forall y n r.
              (TensorKind y, KnownNat n, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstNoVectorize s) y
           -> (InterpretationTarget (AstNoVectorize s) y -> AstNoVectorize s r n)
           -> AstNoVectorize s r n
  rletTKIn stk a f =
    AstNoVectorize
    $ astLetFun @y @_ @s
                (unNoVectorizeY stk a) (unAstNoVectorize . f . noVectorizeY stk)
  rletHVectorIn a f =
    AstNoVectorize $ unAstRanked
    $ rletHVectorIn (unAstNoVectorizeWrap a)
                    (unAstNoVectorize2 . f . noVectorizeHVectorR)
  rletHFunIn a f = astNoVectorize2 $ rletHFunIn a (unAstNoVectorize2 . f)

  sletTKIn :: forall y sh r.
              (TensorKind y, KnownShS sh, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstNoVectorize s) y
           -> (InterpretationTarget (AstNoVectorize s) y -> AstNoVectorizeS s r sh)
           -> AstNoVectorizeS s r sh
  sletTKIn stk a f =
    AstNoVectorizeS
    $ astLetFun @y @_ @s
                (unNoVectorizeY stk a) (unAstNoVectorizeS . f . noVectorizeY stk)
  sletHVectorIn a f =
    astNoVectorizeS2
    $ sletHVectorIn (unAstNoVectorizeWrap a)
                    (unAstNoVectorizeS2 . f . noVectorizeHVectorR)
  sletHFunIn a f = astNoVectorizeS2 $ sletHFunIn a (unAstNoVectorizeS2 . f)

  dletHVectorInHVector a f =
    AstNoVectorizeWrap
    $ dletHVectorInHVector (unAstNoVectorizeWrap a)
                           (unAstNoVectorizeWrap . f . noVectorizeHVectorR)
  dletHFunInHVector t f =
    AstNoVectorizeWrap
    $ dletHFunInHVector t (unAstNoVectorizeWrap . f)
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => InterpretationTarget (AstNoVectorize s) x
       -> (ConcreteTarget (AstNoVectorize s) x
           -> InterpretationTarget (AstNoVectorize s) z)
       -> InterpretationTarget (AstNoVectorize s) z
  tlet u f = case stensorKind @x of
    STKR{} -> noVectorizeY (stensorKind @z)
              $ astLetFun
                  (unAstNoVectorize u)
                  (unNoVectorizeY (stensorKind @z) . f . AstNoVectorize)
    STKS{} -> noVectorizeY (stensorKind @z)
              $ astLetFun
                  (unAstNoVectorizeS u)
                  (unNoVectorizeY (stensorKind @z) . f . AstNoVectorizeS)
    STKProduct{} -> error "TODO"
    STKUntyped{} -> error "TODO"
  blet :: forall x z. (TensorKind x, TensorKind z)
       => InterpretationTarget (AstNoVectorize s) x
       -> (InterpretationTarget (AstNoVectorize s) x
           -> InterpretationTarget (AstNoVectorize s) z)
       -> InterpretationTarget (AstNoVectorize s) z
  blet u f = case stensorKind @x of
    STKR{} -> noVectorizeY (stensorKind @z)
              $ astLetFun
                  (unAstNoVectorize u)
                  (unNoVectorizeY (stensorKind @z) . f . AstNoVectorize)
    STKS{} -> noVectorizeY (stensorKind @z)
              $ astLetFun
                  (unAstNoVectorizeS u)
                  (unNoVectorizeY (stensorKind @z) . f . AstNoVectorizeS)
    STKProduct{} -> error "TODO"
    STKUntyped{} -> error "TODO"

  toShare :: forall y. TensorKind y
          => InterpretationTarget (AstNoVectorize s) y
          -> InterpretationTarget (AstRaw s) y
  toShare t = case (stensorKind @y) of
    STKR{} -> AstRaw $ unsafeCoerce $ unAstNoVectorize t
    STKS{} -> AstRawS $ unsafeCoerce $ unAstNoVectorizeS t
    STKProduct{} -> AstRawWrap $ unsafeCoerce $ unAstNoVectorizeWrap t
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap $ unsafeCoerce
                  $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
  tconstant stk t = case stk of
    STKR{} -> rconstant t
    STKS{} -> sconstant t
    STKProduct{} -> AstNoVectorizeWrap $ fromPrimal $ unAstNoVectorizeWrap t
    STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap $ fromPrimal
                  $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t

  rrev f parameters0 hVector =
    AstNoVectorizeWrap
    $ rrev f parameters0 (unNoVectorizeHVectorR hVector)

instance AstSpan s => RankedTensor (AstNoVectorize s) where
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
  rfromS = astNoVectorize2 . rfromS . unAstNoVectorizeS2
  rconstant = astNoVectorize2 . rconstant . unAstNoVectorize2
  rprimalPart = astNoVectorize2 . rprimalPart . unAstNoVectorize2
  rdualPart = astNoVectorize2 . rdualPart . unAstNoVectorize2
  rD u u' = astNoVectorize2 $ rD (unAstNoVectorize2 u) (unAstNoVectorize2 u')
  rScale s t = astNoVectorize2 $ rScale @(AstRanked s)
                                       (unAstNoVectorize2 s) (unAstNoVectorize2 t)

instance AstSpan s => ShapedTensor (AstNoVectorizeS s) where
  sminIndex = astNoVectorizeS2 . sminIndex . unAstNoVectorizeS2
  smaxIndex = astNoVectorizeS2 . smaxIndex . unAstNoVectorizeS2
  sfloor = astNoVectorizeS2 . sfloor . unAstNoVectorizeS2
  siota = astNoVectorizeS2 siota
  sindex v ix =
    astNoVectorizeS2 $ sindex (unAstNoVectorizeS2 v) (AstRanked . unAstNoVectorize <$> ix)
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

instance AstSpan s => HVectorTensor (AstNoVectorize s) (AstNoVectorizeS s) where
  dshape = dshape . unAstNoVectorizeWrap
  tshapeFull stk t = case stk of
    STKR{} -> shapeAstFull $ unAstNoVectorize t
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (tproject1 t))
                                       (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
  tcond stk b u v = case stk of
    STKR{} -> ifF b u v
    STKS{} -> ifF b u v
    STKProduct{} -> AstNoVectorizeWrap
                    $ AstCond b (unAstNoVectorizeWrap u) (unAstNoVectorizeWrap v)
    STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap
                  $ AstCond b (unAstNoVectorizeWrap $ unHVectorPseudoTensor u)
                              (unAstNoVectorizeWrap $ unHVectorPseudoTensor v)
  tprimalPart stk t = case stk of
    STKR{} -> rprimalPart t
    STKS{} -> sprimalPart t
    STKProduct{} -> AstNoVectorizeWrap $ astSpanPrimal $ unAstNoVectorizeWrap t
    STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap
                  $ astSpanPrimal $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
  dmkHVector =
    AstNoVectorizeWrap . AstMkHVector . unNoVectorizeHVector
  dlambda = dlambda @(AstRanked s)
  dHApply :: forall x y. (TensorKind x, TensorKind y)
          => HFunOf (AstNoVectorize s) x y
          -> InterpretationTarget (AstNoVectorize s) x
          -> InterpretationTarget (AstNoVectorize s) y
  dHApply t ll = noVectorizeY (stensorKind @y) $ astHApply t
                 $ unNoVectorizeY (stensorKind @x) ll
  dunHVector =
    noVectorizeHVectorR . dunHVector . unAstNoVectorizeWrap
  dbuild1 k f =
    AstNoVectorizeWrap
    $ AstBuildHVector1 k $ funToAstI (unAstNoVectorizeWrap . f . AstNoVectorize)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    noVectorizeY (stensorKind @TKUntyped)
    $ AstMapAccumRDer k accShs bShs eShs f df rf
                      (unNoVectorizeY (stensorKind @TKUntyped) acc0)
                      (unNoVectorizeY (stensorKind @TKUntyped) es)
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    noVectorizeY (stensorKind @TKUntyped)
    $ AstMapAccumLDer k accShs bShs eShs f df rf
                      (unNoVectorizeY (stensorKind @TKUntyped) acc0)
                      (unNoVectorizeY (stensorKind @TKUntyped) es)


-- * The AstNoSimplify instances

type instance BoolOf (AstNoSimplify s) = AstBool AstMethodLet

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
deriving instance Num (AstTensor AstMethodLet s (TKR r n)) => Num (AstNoSimplify s r n)
deriving instance (Real (AstTensor AstMethodLet s (TKR r n)))
                  => Real (AstNoSimplify s r n)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKR r n)))
                  => IntegralF (AstNoSimplify s r n)
deriving instance Fractional (AstTensor AstMethodLet s (TKR r n))
                  => Fractional (AstNoSimplify s r n)
deriving instance Floating (AstTensor AstMethodLet s (TKR r n))
                  => Floating (AstNoSimplify s r n)
deriving instance (RealFrac (AstTensor AstMethodLet s (TKR r n)))
                  => RealFrac (AstNoSimplify s r n)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKR r n)))
                  => RealFloatF (AstNoSimplify s r n)

type instance BoolOf (AstNoSimplifyS s) = AstBool AstMethodLet

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
deriving instance Num (AstTensor AstMethodLet s (TKS r sh)) => Num (AstNoSimplifyS s r sh)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKS r sh)))
                  => IntegralF (AstNoSimplifyS s r sh)
deriving instance Fractional (AstTensor AstMethodLet s (TKS r sh))
                  => Fractional (AstNoSimplifyS s r sh)
deriving instance Floating (AstTensor AstMethodLet s (TKS r sh))
                  => Floating (AstNoSimplifyS s r sh)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKS r sh)))
                  => RealFloatF (AstNoSimplifyS s r sh)

type instance InterpretationTarget (AstNoSimplify s) (TKProduct x z) =
  AstNoSimplifyWrap (AstTensor AstMethodLet s (TKProduct x z))

instance Show (InterpretationTargetProductN (AstNoSimplify s) x y) where
  showsPrec d (InterpretationTargetProductN t) = showsPrec d t

instance ProductTensor (AstNoSimplify s) where
  ttuple t1 t2 = AstNoSimplifyWrap $ astTuple (unNoSimplifyY stensorKind t1)
                                              (unNoSimplifyY stensorKind t2)
  tproject1 t = noSimplifyY stensorKind $ astProject1 $ unAstNoSimplifyWrap t
  tproject2 t = noSimplifyY stensorKind $ astProject2 $ unAstNoSimplifyWrap t
  tmkHVector = AstNoSimplifyWrap . AstMkHVector . unNoSimplifyHVector

noSimplifyY :: STensorKindType y -> AstTensor AstMethodLet s y
            -> InterpretationTarget (AstNoSimplify s) y
noSimplifyY stk t = case stk of
  STKR{} -> AstNoSimplify t
  STKS{} -> AstNoSimplifyS t
  STKProduct{} -> AstNoSimplifyWrap t
  STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap t

unNoSimplifyY :: STensorKindType y -> InterpretationTarget (AstNoSimplify s) y
              -> AstTensor AstMethodLet s y
unNoSimplifyY stk t = case stk of
  STKR{} -> unAstNoSimplify t
  STKS{} -> unAstNoSimplifyS t
  STKProduct{} -> unAstNoSimplifyWrap t
  STKUntyped -> unAstNoSimplifyWrap $ unHVectorPseudoTensor t

unNoSimplifyHVector :: HVector (AstNoSimplify s) -> HVector (AstGeneric AstMethodLet s)
unNoSimplifyHVector =
  let f (DynamicRanked (AstNoSimplify t)) = DynamicRanked $ AstGeneric t
      f (DynamicShaped (AstNoSimplifyS t)) = DynamicShaped (AstGenericS t)
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

unNoSimplifyHVectorR :: HVector (AstNoSimplify s) -> HVector (AstRanked s)
unNoSimplifyHVectorR =
  let f (DynamicRanked (AstNoSimplify t)) = DynamicRanked $ AstRanked t
      f (DynamicShaped (AstNoSimplifyS t)) = DynamicShaped (AstShaped t)
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noSimplifyHVector :: HVector (AstGeneric AstMethodLet s) -> HVector (AstNoSimplify s)
noSimplifyHVector =
  let f (DynamicRanked (AstGeneric t)) = DynamicRanked $ AstNoSimplify t
      f (DynamicShaped (AstGenericS t)) = DynamicShaped $ AstNoSimplifyS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

instance AstSpan s => LetTensor (AstNoSimplify s) (AstNoSimplifyS s) where
  rletTKIn :: forall y n r. (TensorKind y, KnownNat n, GoodScalar r)
           => STensorKindType y -> InterpretationTarget (AstNoSimplify s) y
           -> (InterpretationTarget (AstNoSimplify s) y -> AstNoSimplify s r n)
           -> AstNoSimplify s r n
  rletTKIn stk a f =
    AstNoSimplify
    $ astLetFunNoSimplify @y @_ @s
        (unNoSimplifyY stk a) (unAstNoSimplify . f . noSimplifyY stk)
  rletHVectorIn a f =
    AstNoSimplify
    $ astLetHVectorInFunNoSimplify (unAstNoSimplifyWrap a)
                                   (unAstNoSimplify . f . noSimplifyHVector)
  rletHFunIn a f = AstNoSimplify $ astLetHFunInFunNoSimplify a (unAstNoSimplify . f)

  sletTKIn :: forall y sh r. (TensorKind y, GoodScalar r, KnownShS sh)
           => STensorKindType y -> InterpretationTarget (AstNoSimplify s) y
           -> (InterpretationTarget (AstNoSimplify s) y -> AstNoSimplifyS s r sh)
           -> AstNoSimplifyS s r sh
  sletTKIn stk a f =
    AstNoSimplifyS
    $ astLetFunNoSimplify @y @_ @s
        (unNoSimplifyY stk a) (unAstNoSimplifyS . f . noSimplifyY stk)
  sletHVectorIn a f =
    AstNoSimplifyS
    $ astLetHVectorInFunNoSimplifyS (unAstNoSimplifyWrap a)
                                    (unAstNoSimplifyS . f . noSimplifyHVector)
  sletHFunIn a f = AstNoSimplifyS $ astLetHFunInFunNoSimplifyS a (unAstNoSimplifyS . f)

  dletHVectorInHVector a f =
    AstNoSimplifyWrap
    $ astLetHVectorInHVectorFunNoSimplify (unAstNoSimplifyWrap a)
                                          (unAstNoSimplifyWrap . f . noSimplifyHVector)
  dletHFunInHVector t f =
    AstNoSimplifyWrap
    $ astLetHFunInHVectorFunNoSimplify t (unAstNoSimplifyWrap . f)
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => InterpretationTarget (AstNoSimplify s) x
       -> (ConcreteTarget (AstNoSimplify s) x
           -> InterpretationTarget (AstNoSimplify s) z)
       -> InterpretationTarget (AstNoSimplify s)  z
  tlet u f = case stensorKind @x of
    STKR{} -> noSimplifyY (stensorKind @z)
              $ astLetFunNoSimplify
                  (unAstNoSimplify u)
                  (unNoSimplifyY (stensorKind @z) . f . AstNoSimplify)
    STKS{} -> noSimplifyY (stensorKind @z)
              $ astLetFunNoSimplify
                  (unAstNoSimplifyS u)
                  (unNoSimplifyY (stensorKind @z) . f . AstNoSimplifyS)
    STKProduct{} -> error "TODO"
    STKUntyped{} -> error "TODO"
  blet :: forall x z. (TensorKind x, TensorKind z)
       => InterpretationTarget (AstNoSimplify s) x
       -> (InterpretationTarget (AstNoSimplify s) x
           -> InterpretationTarget (AstNoSimplify s) z)
       -> InterpretationTarget (AstNoSimplify s)  z
  blet u f = case stensorKind @x of
    STKR{} -> noSimplifyY (stensorKind @z)
              $ astLetFunNoSimplify
                  (unAstNoSimplify u)
                  (unNoSimplifyY (stensorKind @z) . f . AstNoSimplify)
    STKS{} -> noSimplifyY (stensorKind @z)
              $ astLetFunNoSimplify
                  (unAstNoSimplifyS u)
                  (unNoSimplifyY (stensorKind @z) . f . AstNoSimplifyS)
    STKProduct{} -> error "TODO"
    STKUntyped{} -> error "TODO"

  toShare :: forall y. TensorKind y
          => InterpretationTarget (AstNoSimplify s) y
          -> InterpretationTarget (AstRaw s) y
  toShare t = case (stensorKind @y) of
    STKR{} -> AstRaw $ unsafeCoerce $ unAstNoSimplify t
    STKS{} -> AstRawS $ unsafeCoerce $ unAstNoSimplifyS t
    STKProduct{} -> AstRawWrap $ unsafeCoerce $ unAstNoSimplifyWrap t
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap $ unsafeCoerce
                  $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t
  tconstant stk t = case stk of
    STKR{} -> rconstant t
    STKS{} -> sconstant t
    STKProduct{} -> AstNoSimplifyWrap $ fromPrimal $ unAstNoSimplifyWrap t
    STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap $ fromPrimal
                  $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t

  rrev f parameters0 hVector =  -- we don't have an AST constructor to hold it
    AstNoSimplifyWrap
    $ rrev f parameters0 (unNoSimplifyHVectorR hVector)

instance AstSpan s => RankedTensor (AstNoSimplify s) where
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
  rfromS = AstNoSimplify . AstRFromS . unAstNoSimplifyS
  rconstant = AstNoSimplify . fromPrimal . unAstNoSimplify
  rprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  rdualPart = AstNoSimplify . astSpanDual . unAstNoSimplify
  rD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) (unAstNoSimplify u')
  rScale s t = AstNoSimplify $ astDualPart
               $ AstConstant (unAstNoSimplify s)
                 * AstD (unAstRanked $ rzero (rshape s)) (unAstNoSimplify t)

instance AstSpan s => ShapedTensor (AstNoSimplifyS s) where
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
  tcond stk b u v = case stk of
    STKR{} -> ifF b u v
    STKS{} -> ifF b u v
    STKProduct{} -> AstNoSimplifyWrap
                    $ AstCond b (unAstNoSimplifyWrap u) (unAstNoSimplifyWrap v)
    STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap
                  $ AstCond b (unAstNoSimplifyWrap $ unHVectorPseudoTensor u)
                              (unAstNoSimplifyWrap $ unHVectorPseudoTensor v)
  tprimalPart stk t = case stk of
    STKR{} -> rprimalPart t
    STKS{} -> sprimalPart t
    STKProduct{} -> AstNoSimplifyWrap $ astSpanPrimal $ unAstNoSimplifyWrap t
    STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap
                  $ astSpanPrimal $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t
  dmkHVector =
    AstNoSimplifyWrap . AstMkHVector . unNoSimplifyHVector
  dlambda = dlambda @(AstRanked s)
  dHApply :: forall x y. (TensorKind x, TensorKind y)
          => HFunOf (AstNoSimplify s) x y
          -> InterpretationTarget (AstNoSimplify s) x
          -> InterpretationTarget (AstNoSimplify s) y
  dHApply t ll =
    let app = AstHApply t $ unNoSimplifyY (stensorKind @x) ll
    in noSimplifyY (stensorKind @y) app
  dunHVector (AstNoSimplifyWrap (AstMkHVector l)) = noSimplifyHVector l
  dunHVector (AstNoSimplifyWrap hVectorOf) =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic AstMethodLet s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: IShR n) ->
              DynamicRanked @r @n $ AstGeneric $ AstProjectR hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstGenericS $ AstProjectS hVectorOf i
    in noSimplifyHVector
       $ V.imap f $ shapeAstHVector hVectorOf
  dbuild1 k f = AstNoSimplifyWrap
                $ astBuildHVector1Vectorize
                    k (unAstNoSimplifyWrap . f . AstNoSimplify)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    noSimplifyY (stensorKind @TKUntyped)
    $ AstMapAccumRDer k accShs bShs eShs f df rf
                      (unNoSimplifyY (stensorKind @TKUntyped) acc0)
                      (unNoSimplifyY (stensorKind @TKUntyped) es)
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    noSimplifyY (stensorKind @TKUntyped)
    $ AstMapAccumLDer k accShs bShs eShs f df rf
                      (unNoSimplifyY (stensorKind @TKUntyped) acc0)
                      (unNoSimplifyY (stensorKind @TKUntyped) es)


-- TODO: move to a better home:

-- TODO: these can't easily be in AstSimplify, because of unRankedY

prettifyArtifactRev
  :: TensorKind z
  => AstArtifactRev TKUntyped z
  -> ( AstVarName PrimalSpan z
     , [AstDynamicVarName]
     , InterpretationTarget (AstRanked PrimalSpan) TKUntyped
     , InterpretationTarget (AstRanked PrimalSpan) z )
prettifyArtifactRev AstArtifactRev{..} =
  fun1DToAst (shapeAstHVector
              $ unHVectorPseudoTensor artDerivativeRev) $ \ !vars1 !asts1 ->
    let idom = SubstitutionPayload $ AstMkHVector asts1
        !derivative = substituteAstInInterpretationTarget
                        idom artVarDomainRev artDerivativeRev in
    let !primal = substituteAstInInterpretationTarget
                    idom artVarDomainRev artPrimalRev
    in (artVarDtRev, vars1, derivative, primal)

printArtifactSimple
  :: TensorKind z
  => IntMap String
  -> AstArtifactRev TKUntyped z
  -> String
printArtifactSimple renames art =
  let !(!varDt, !vars1, !derivative, _) = prettifyArtifactRev art in
  let !varsPP = printAstVarName renames varDt
                : map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorSimple
                         renames (unHVectorPseudoTensor derivative)

printArtifactPretty
  :: TensorKind z
  => IntMap String
  -> AstArtifactRev TKUntyped z
  -> String
printArtifactPretty renames art =
  let !(!varDt, !vars1, !derivative, _) = prettifyArtifactRev art in
  let varsPP = printAstVarName renames varDt
               : map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorPretty
                         renames (unHVectorPseudoTensor derivative)

printArtifactPrimalSimple
  :: forall z. TensorKind z
  => IntMap String
  -> AstArtifactRev TKUntyped z
  -> String
printArtifactPrimalSimple renames art =
  let !(_, !vars1, _, !primal) = prettifyArtifactRev art in
  let !varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimpleY renames (unRankedY (stensorKind @z) primal)

printArtifactPrimalPretty
  :: forall z. TensorKind z
  => IntMap String
  -> AstArtifactRev TKUntyped z
  -> String
printArtifactPrimalPretty renames art =
  let !(_, !vars1, _, !primal) = prettifyArtifactRev art in
  let !varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPrettyY renames (unRankedY (stensorKind @z) primal)
