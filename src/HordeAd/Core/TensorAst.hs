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
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty
  , rawY
  ) where

import Prelude

import Data.Array.Shape qualified as Sh
import Data.IntMap.Strict (IntMap)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector qualified as Data.NonStrict.Vector
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested (Rank)

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
import HordeAd.Core.TensorADVal (unADValRep)
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorConcrete ()
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), FlipS (..), IntegralF (..), RealFloatF (..))
import HordeAd.Util.SizedList

-- * Symbolic reverse and forward derivative computation

forwardPassByInterpretation
  :: forall x z. (TensorKind x, TensorKind z)
  => (Rep (AstRanked FullSpan) x
      -> Rep (AstRanked FullSpan) z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> Rep (ADVal (AstRaw PrimalSpan)) z
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit hVectorPrimal var hVector =
  let deltaInputs = generateDeltaInputs $ shapeAstFull hVectorPrimal
      varInputs = makeADInputs (rawY (stensorKind @x) hVectorPrimal)
                               deltaInputs
      ast = g $ rankedY (stensorKind @x) hVector
      env = extendEnv var varInputs envInit
  in interpretAst env $ unRankedY (stensorKind @z) ast

revArtifactFromForwardPass
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> Rep (ADVal (AstRaw PrimalSpan)) z)
  -> TensorKindFull x
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
        funToAst (aDTensorKind $ shapeAstFull
                  $ unRawY (stensorKind @z) primalBody) id in
  let mdt = if hasDt
            then Just $ rawY (stensorKind @(ADTensorKind z)) astDt
            else Nothing
      !gradient = gradientFromDelta ftk primalBody mdt delta
      !unGradient = unshareAstTensor $ unRawY (stensorKind @(ADTensorKind x))
                    $ gradient
      !unPrimal = unshareAstTensor $ unRawY (stensorKind @z) primalBody
  in ( AstArtifactRev varDt varPrimal unGradient unPrimal
     , delta )

revProduceArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (Rep (AstRanked FullSpan) x
      -> Rep (AstRanked FullSpan) z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> TensorKindFull x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifact #-}
revProduceArtifact hasDt g envInit =
  revArtifactFromForwardPass hasDt (forwardPassByInterpretation g envInit)

fwdArtifactFromForwardPass
  :: forall x z. (TensorKind x, TensorKind z)
  => (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> Rep (ADVal (AstRaw PrimalSpan)) z)
  -> TensorKindFull x
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
  let !derivative = derivativeFromDelta @x delta
                    $ rawY (stensorKind @(ADTensorKind x)) hVectorD
      !unDerivative = unshareAstTensor
                      $ unRawY (stensorKind @(ADTensorKind z)) derivative
      !unPrimal = unshareAstTensor $ unRawY (stensorKind @z) primalBody
  in ( AstArtifactFwd varPrimalD varPrimal unDerivative unPrimal
     , delta )

fwdProduceArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => (Rep (AstRanked FullSpan) x
      -> Rep (AstRanked FullSpan) z)
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
  AstRanked (AstConst u) ==. AstRanked (AstConst v) = AstBoolConst $ u == v
    -- common in indexing
  AstRanked v ==. AstRanked u = AstRel EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstRanked (AstConst u) /=. AstRanked (AstConst v) = AstBoolConst $ u /= v
    -- common in indexing
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
deriving instance (IntegralF (AstTensor AstMethodLet s (TKR r n)))
                  => IntegralF (AstRanked s r n)
deriving instance Fractional (AstTensor AstMethodLet s (TKR r n))
                  => Fractional (AstRanked s r n)
deriving instance Floating (AstTensor AstMethodLet s (TKR r n))
                  => Floating (AstRanked s r n)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKR r n)))
                  => RealFloatF (AstRanked s r n)

type instance BoolOf (AstShaped s) = AstBool AstMethodLet

instance AstSpan s => EqF (AstShaped s) where
  AstShaped (AstConstS u) ==. AstShaped (AstConstS v) = AstBoolConst $ u == v
    -- common in indexing
  AstShaped v ==. AstShaped u = AstRelS EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstShaped (AstConstS u) /=. AstShaped (AstConstS v) = AstBoolConst $ u /= v
    -- common in indexing
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
deriving instance (IntegralF (AstTensor AstMethodLet s (TKS r sh)))
                  => IntegralF (AstShaped s r sh)
deriving instance Fractional (AstTensor AstMethodLet s (TKS r sh))
                  => Fractional (AstShaped s r sh)
deriving instance Floating (AstTensor AstMethodLet s (TKS r sh))
                  => Floating (AstShaped s r sh)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKS r sh)))
                  => RealFloatF (AstShaped s r sh)

instance (GoodScalar r, KnownNat n, RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstRanked s r n) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstRanked s) (AstRanked s Double n) #-}
  type X (AstRanked s r n) = TKR r n
  toHVector = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKR r n)) =
    case sameTensorKind @(TKR r n) @(ADTensorKind (TKR r n)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (rzero (rshape aInit), Nothing)

instance (GoodScalar r, KnownNat n, RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AsHVector (AstRanked s r n)) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstRanked s) (AsHVector (AstRanked s Double n)) #-}
  type X (AsHVector (AstRanked s r n)) = TKUntyped
  toHVector = V.singleton . DynamicRanked . unAsHVector
  fromHVector _aInit = fromHVectorR

instance (GoodScalar r, KnownNat n, RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstGeneric AstMethodLet s r n) where
  type X (AstGeneric AstMethodLet s r n) = TKR r n
  toHVector = AstRanked . unAstGeneric
  fromHVector _aInit t = Just (AstGeneric $ unAstRanked t, Nothing)
  fromHVectorAD aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKR r n)) =
    case sameTensorKind @(TKR r n) @(ADTensorKind (TKR r n)) of
      Just Refl -> Just (AstGeneric $ unAstRanked t, Nothing)
      _ -> Just (AstGeneric $ unAstRanked
                 $ rzero (rshape $ AstRanked $ unAstGeneric aInit), Nothing)

{-
instance (RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (DynamicTensor (AstGeneric AstMethodLet s)) where
  toHVector = rankedHVector . V.singleton
  fromHVector _aInit hv = case V.uncons $ unRankedHVector hv of
    Nothing -> Nothing
    Just (generic, rest) ->
      Just (generic, rankedHVector rest)
-}
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
  type X (AstShaped s r sh) = TKS r sh
  toHVector = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD _aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKS r sh)) =
    case sameTensorKind @(TKS r sh) @(ADTensorKind (TKS r sh)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (srepl 0, Nothing)

instance (GoodScalar r, KnownShS sh, ShapedTensor (AstShaped s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AsHVector (AstShaped s r sh)) where
  type X (AsHVector (AstShaped s r sh)) = TKUntyped
  toHVector = V.singleton . DynamicShaped . unAsHVector
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
      gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: Rank sh) $
      DynamicShaped @_ @sh $ AstGenericS $ fromPrimal $ AstConstS $ runFlipS t
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2

type instance BoolOf (AstMixed s) = AstBool AstMethodLet

instance AstSpan s => EqF (AstMixed s) where
  AstMixed (AstConstX u) ==. AstMixed (AstConstX v) = AstBoolConst $ u == v
    -- common in indexing
  AstMixed v ==. AstMixed u = AstRelX EqOp (astSpanPrimal v) (astSpanPrimal u)
  AstMixed (AstConstX u) /=. AstMixed (AstConstX v) = AstBoolConst $ u /= v
    -- common in indexing
  AstMixed v /=. AstMixed u = AstRelX NeqOp (astSpanPrimal v) (astSpanPrimal u)

instance AstSpan s => OrdF (AstMixed s) where
  AstMixed (AstConstX u) <. AstMixed (AstConstX v) = AstBoolConst $ u < v
    -- common in indexing
  v <. u = AstRelX LsOp (astSpanPrimal (unAstMixed v)) (astSpanPrimal (unAstMixed u))
  AstMixed (AstConstX u) <=. AstMixed (AstConstX v) = AstBoolConst $ u <= v
    -- common in indexing
  v <=. u = AstRelX LeqOp (astSpanPrimal (unAstMixed v)) (astSpanPrimal (unAstMixed u))
  AstMixed (AstConstX u) >. AstMixed (AstConstX v) = AstBoolConst $ u > v
    -- common in indexing
  v >. u = AstRelX GtOp (astSpanPrimal (unAstMixed v)) (astSpanPrimal (unAstMixed u))
  AstMixed (AstConstX u) >=. AstMixed (AstConstX v) =  AstBoolConst $ u >= v
    -- common in indexing
  v >=. u = AstRelX GeqOp (astSpanPrimal (unAstMixed v)) (astSpanPrimal (unAstMixed u))

instance IfF (AstMixed s) where
  ifF cond a b = AstMixed $ astCond cond (unAstMixed a) (unAstMixed b)

{-deriving instance IfF (AstMixed s)
deriving instance AstSpan s => EqF (AstMixed s)
deriving instance AstSpan s => OrdF (AstMixed s)-}
deriving instance Eq (AstMixed s r sh)
deriving instance Ord (AstMixed s r sh)
deriving instance Num (AstTensor AstMethodLet s (TKX r sh)) => Num (AstMixed s r sh)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKX r sh)))
                  => IntegralF (AstMixed s r sh)
deriving instance Fractional (AstTensor AstMethodLet s (TKX r sh))
                  => Fractional (AstMixed s r sh)
deriving instance Floating (AstTensor AstMethodLet s (TKX r sh))
                  => Floating (AstMixed s r sh)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKX r sh)))
                  => RealFloatF (AstMixed s r sh)

instance AstSpan s => ProductTensor (AstRanked s) where
  tpair t1 t2 = astPair (unRankedY stensorKind t1)
                          (unRankedY stensorKind t2)
  tproject1 = rankedY stensorKind . astProject1
  tproject2 = rankedY stensorKind . astProject2

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

astLetHFunInFun
  :: (TensorKind x, TensorKind y, TensorKind z)
  => AstHFun x z -> (AstHFun x z -> AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s y
{-# INLINE astLetHFunInFun #-}
astLetHFunInFun a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunIn var a (f ast)

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

-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: TensorKindFull TKUntyped
  -> HVectorPseudoTensor (AstRaw PrimalSpan) Float '()
  -> Maybe (HVectorPseudoTensor (AstRaw PrimalSpan) Float '())
  -> Delta (AstRaw PrimalSpan) TKUntyped
  -> Rep (AstRaw PrimalSpan) TKUntyped #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (AstRaw PrimalSpan) -> EvalState (AstRaw PrimalSpan) #-}

instance AstSpan s => LetTensor (AstRanked s) (AstShaped s) where
  rletHFunIn a f = AstRanked $ astLetHFunInFun a (unAstRanked . f)
  sletHFunIn a f = AstShaped $ astLetHFunInFun a (unAstShaped . f)
  dletHFunInHVector = astLetHFunInFun
  dlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstRanked s) x
       -> (RepDeep (AstRanked s) x -> Rep (AstRanked s) z)
       -> Rep (AstRanked s) z
  dlet u f = case stensorKind @x of
    STKScalar{} -> blet u f
    STKR STKScalar{} _ -> blet u f
    STKS STKScalar{} _ -> blet u f
    STKX STKScalar{} _ -> blet u f
    stk@STKProduct{} ->
      blet u $ \ !uShared -> f (repDeepDuplicable stk uShared)
    STKUntyped{} -> tlet u f
    _ -> error "TODO"
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstRanked s) x
       -> (RepShallow (AstRanked s) x -> Rep (AstRanked s) z)
       -> Rep (AstRanked s) z
  tlet u f = case stensorKind @x of
    STKScalar{} -> blet u f
    STKR STKScalar{} _ -> blet u f
    STKS STKScalar{} _ -> blet u f
    STKX STKScalar{} _ -> blet u f
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      blet u $ \ !uShared -> f (tproject1 uShared, tproject2 uShared)
    STKUntyped{} ->
      blet u $ \ !uShared -> f $ dunHVector $ unHVectorPseudoTensor uShared
    _ -> error "TODO"
  blet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstRanked s) x
       -> (Rep (AstRanked s) x -> Rep (AstRanked s) z)
       -> Rep (AstRanked s) z
  blet u f = case stensorKind @x of
    STKScalar{} -> blet (unRepScalar u) (f . RepScalar)
    STKR STKScalar{} _ ->
      rankedY (stensorKind @z)
      $ astLetFun (unAstRanked u)
                  (unRankedY (stensorKind @z) . f . AstRanked)
    STKS STKScalar{} _ ->
      rankedY (stensorKind @z)
      $ astLetFun (unAstShaped u)
                  (unRankedY (stensorKind @z) . f . AstShaped)
    STKX STKScalar{} _ ->
      rankedY (stensorKind @z)
      $ astLetFun (unAstMixed u)
                  (unRankedY (stensorKind @z) . f . AstMixed)
    STKProduct{} ->
      rankedY (stensorKind @z)
      $ astLetFun u
                  (unRankedY (stensorKind @z) . f)
    STKUntyped{} ->
      rankedY (stensorKind @z)
      $ astLetFun (unHVectorPseudoTensor u)
                  (unRankedY (stensorKind @z) . f . HVectorPseudoTensor)
    _ -> error "TODO"

  toShare :: forall y. TensorKind y
          => Rep (AstRanked s) y
          -> Rep (AstRaw s) y
  toShare t = case stensorKind @y of
    STKScalar _ ->
      RepScalar $ AstRaw $ AstToShare $ unAstRanked $ unRepScalar t
    STKR STKScalar{} SNat -> AstRaw $ AstToShare $ unAstRanked t
    STKS STKScalar{} sh -> withKnownShS sh $ AstRawS $ AstToShare $ unAstShaped t
    STKX STKScalar{} sh -> withKnownShX sh $ AstRawX $ AstToShare $ unAstMixed t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstRawWrap $ AstToShare t
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap $ AstToShare
                  $ unHVectorPseudoTensor t
    _ -> error "TODO"
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tunshare :: forall y. TensorKind y
           => Rep (AstRaw s) y
           -> Rep (AstRanked s) y
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> rankedY stensorKind . unshareAstTensor . unRawY stensorKind
      _ -> error "tunshare: used not at PrimalSpan"
  tconstant stk t = case stk of
    STKScalar _ -> RepScalar $ rconstant $ unRepScalar t
    STKR STKScalar{} SNat -> rconstant t
    STKS STKScalar{} sh -> withKnownShS sh $ sconstant t
    STKX STKScalar{} sh -> withKnownShX sh $ xconstant t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 -> fromPrimal t
    STKUntyped -> HVectorPseudoTensor $ fromPrimal $ unHVectorPseudoTensor t
    _ -> error "TODO"
  taddLet stk t1 t2 | Dict <- lemTensorKindOfS stk =
    -- when we have Num(AstTensor), this is better:
    --   rankedY stensorKind
    --   $ unRankedY stensorKind t1 + unRankedY stensorKind t2
    blet t1 $ \ !u1 ->
    blet t2 $ \ !u2 ->
      fromRepD $ addRepD (toRepDDuplicable stk u1)
                         (toRepDDuplicable stk u2)

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
  rbuild1 k f = withSNat k $ \snat ->
    AstRanked $ astBuild1Vectorize snat (unAstRanked . f . AstRanked)
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
  rdualPart = astSpanDual . unAstRanked
  rD u u' = AstRanked $ astSpanD (unAstRanked u) u'
  rScale s t = astDualPart $ AstConstant (unAstRanked s) * AstD (unAstRanked $ rzero (rshape s)) t

  xshape t = case shapeAstFull $ unAstMixed t of
    FTKX sh -> sh
  xindex v ix =
    AstMixed $ AstIndexX (unAstMixed v) (unAstRanked <$> ix)
  xfromVector = AstMixed . AstFromVectorX . V.map unAstMixed
  xreplicate = AstMixed . AstReplicate SNat . unAstMixed
  xconst = AstMixed . fromPrimal . AstConstX
  xconstant = AstMixed . fromPrimal . unAstMixed
  xprimalPart = AstMixed . astSpanPrimal . unAstMixed
  xdualPart = astSpanDual . unAstMixed
  xD u u' = AstMixed $ astSpanD (unAstMixed u) u'

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
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (AstShaped s) -> AstShaped s r sh)
          -> AstShaped s r (n ': sh)
  sbuild1 f =
    AstShaped $ astBuild1Vectorize (SNat @n) (unAstShaped . f . AstRanked)
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
  sdualPart = astSpanDual . unAstShaped
  sD u u' = AstShaped $ astSpanD (unAstShaped u) u'
  sScale s t = astDualPart $ AstConstant (unAstShaped s) * AstD 0 t

instance forall s. AstSpan s => HVectorTensor (AstRanked s) (AstShaped s) where
  dshape = shapeAstHVector
  tshapeFull stk t = case stk of
    STKScalar _ -> FTKScalar
    STKR STKScalar{} SNat -> shapeAstFull $ unAstRanked t
    STKS STKScalar{} sh -> FTKS sh
    STKX STKScalar{} sh -> withKnownShX sh shapeAstFull $ unAstMixed t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      FTKProduct (tshapeFull stk1 (tproject1 t))
                 (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tcond stk b u v = case stk of
    STKScalar _ -> RepScalar $ ifF b (unRepScalar u) (unRepScalar v)
    STKR STKScalar{} SNat -> ifF b u v
    STKS STKScalar{} sh -> withKnownShS sh $ ifF b u v
    STKX STKScalar{} sh -> withKnownShX sh $ ifF b u v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 -> AstCond b u v
    STKUntyped -> HVectorPseudoTensor
                  $ AstCond b (unHVectorPseudoTensor u)
                              (unHVectorPseudoTensor v)
    _ -> error "TODO"
  tprimalPart stk t = case stk of
    STKScalar _ -> RepScalar $ rprimalPart $ unRepScalar t
    STKR STKScalar{} SNat -> rprimalPart t
    STKS STKScalar{} sh -> withKnownShS sh $ sprimalPart t
    STKX STKScalar{} sh -> withKnownShX sh $ xprimalPart t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 -> astSpanPrimal t
    STKUntyped -> HVectorPseudoTensor $ astSpanPrimal $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tdualPart stk t = case stk of
    STKScalar _ -> AstUnScalar $ rdualPart $ unRepScalar t
    STKR STKScalar{} SNat -> rdualPart t
    STKS STKScalar{} sh -> withKnownShS sh $ sdualPart t
    STKX STKScalar{} sh -> withKnownShX sh $ xdualPart t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 -> astSpanDual t
    STKUntyped -> astSpanDual $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tD stk t d = case stk of
    STKScalar _ -> RepScalar $ rD (unRepScalar t) (AstScalar d)
    STKR STKScalar{} SNat -> rD t d
    STKS STKScalar{} sh -> withKnownShS sh $ sD t d
    STKX STKScalar{} sh -> withKnownShX sh $ xD t d
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      let (t1, t2) = (tproject1 t, tproject2 t)  -- TODO: sharing
          (d1, d2) = (AstProject1 d, AstProject2 d)  -- TODO: sharing
      in tpair (tD stk1 t1 d1) (tD stk2 t2 d2)
    STKUntyped -> error "TODO"
    _ -> error "TODO"
  dmkHVector = AstMkHVector . unRankedHVector
  dlambda :: forall x z. (TensorKind x, TensorKind z)
          => TensorKindFull x -> HFun x z -> HFunOf (AstRanked s) x z
  dlambda shss f =
    let (var, ast) = funToAst shss $ \ !ll ->
          unRankedY (stensorKind @z) $ unHFun f $ rankedY (stensorKind @x) ll
    in AstLambda (var, shss, ast)
  dHApply :: forall x z. (TensorKind x, TensorKind z)
          => HFunOf (AstRanked s) x z
          -> Rep (AstRanked s) x
          -> Rep (AstRanked s) z
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
  dbuild1 k f = astBuild1Vectorize k (f . AstRanked)
  -- TODO: (still) relevant?
  -- In this instance, these three ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstRanked to AstRaw.
  drev :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
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
         => TensorKindFull x
         -> HFun x z
         -> AstHFun (TKProduct (ADTensorKind z) x) (ADTensorKind x)
  drevDt ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x)
                , Dict <- lemTensorKindOfAD (stensorKind @z) =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactRev varDt var gradient primal, _delta) =
          revProduceArtifact True (unHFun f) emptyEnv ftkx
        ftkz = aDTensorKind $ shapeAstFull primal
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet varDt (astProject1 astP)
          $ astLet var (astProject2 astP)
          $ simplifyInline gradient
    in AstLambda (varP, ftk2, ast)
  dfwd :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
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
  dmapAccumRDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstRanked s)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (AstRanked s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstRanked s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                       (TKProduct accShs eShs))
                            (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstRanked s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                       (TKProduct accShs eShs))
                            (ADTensorKind (TKProduct accShs eShs))
    -> Rep (AstRanked s) accShs
    -> Rep (AstRanked s) (BuildTensorKind k eShs)
    -> Rep (AstRanked s) (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      rankedY stensorKind
      $ AstMapAccumRDer k accShs bShs eShs f df rf
                        (unRankedY stensorKind acc0)
                        (unRankedY stensorKind es)
  dmapAccumLDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstRanked s)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (AstRanked s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstRanked s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                       (TKProduct accShs eShs))
                            (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstRanked s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                       (TKProduct accShs eShs))
                            (ADTensorKind (TKProduct accShs eShs))
    -> Rep (AstRanked s) accShs
    -> Rep (AstRanked s) (BuildTensorKind k eShs)
    -> Rep (AstRanked s) (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      rankedY stensorKind
      $ AstMapAccumLDer k accShs bShs eShs f df rf
                        (unRankedY stensorKind acc0)
                        (unRankedY stensorKind es)


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
deriving instance (IntegralF (AstTensor AstMethodShare s (TKR r n)))
                  => IntegralF (AstRaw s r n)
deriving instance Fractional (AstTensor AstMethodShare s (TKR r n))
                  => Fractional (AstRaw s r n)
deriving instance Floating (AstTensor AstMethodShare s (TKR r n))
                  => Floating (AstRaw s r n)
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

type instance BoolOf (AstRawX s) = AstBool AstMethodShare

instance IfF (AstRawX s) where
  ifF cond a b = AstRawX $ AstCond cond (unAstRawX a) (unAstRawX b)
instance AstSpan s => EqF (AstRawX s) where
  AstRawX v ==. AstRawX u = AstRelX EqOp (astSpanPrimalRaw v) (astSpanPrimalRaw u)
  AstRawX v /=. AstRawX u = AstRelX NeqOp (astSpanPrimalRaw v) (astSpanPrimalRaw u)
instance AstSpan s => OrdF (AstRawX s) where
  v <. u = AstRelX LsOp (astSpanPrimalRaw (unAstRawX v)) (astSpanPrimalRaw (unAstRawX u))
  v <=. u = AstRelX LeqOp (astSpanPrimalRaw (unAstRawX v)) (astSpanPrimalRaw (unAstRawX u))
  v >. u = AstRelX GtOp (astSpanPrimalRaw (unAstRawX v)) (astSpanPrimalRaw (unAstRawX u))
  v >=. u = AstRelX GeqOp (astSpanPrimalRaw (unAstRawX v)) (astSpanPrimalRaw (unAstRawX u))
deriving instance Eq (AstRawX s r sh)
deriving instance Ord (AstRawX s r sh)
deriving instance Num (AstTensor AstMethodShare s (TKX r sh)) => Num (AstRawX s r sh)
deriving instance (IntegralF (AstTensor AstMethodShare s (TKX r sh)))
                  => IntegralF (AstRawX s r sh)
deriving instance Fractional (AstTensor AstMethodShare s (TKX r sh))
                  => Fractional (AstRawX s r sh)
deriving instance Floating (AstTensor AstMethodShare s (TKX r sh))
                  => Floating (AstRawX s r sh)
deriving instance (RealFloatF (AstTensor AstMethodShare s (TKX r sh)))
                  => RealFloatF (AstRawX s r sh)

type instance Rep (AstRaw s) (TKProduct x z) =
  AstRawWrap (AstTensor AstMethodShare s (TKProduct x z))

instance Show (RepProductN (AstRaw s) x y) where
  showsPrec d (RepProductN t) = showsPrec d t

instance ProductTensor (AstRaw s) where
  tpair t1 t2 = AstRawWrap $ AstPair (unRawY stensorKind t1)
                                       (unRawY stensorKind t2)
  tproject1 t = rawY stensorKind $ AstProject1 $ unAstRawWrap t
  tproject2 t = rawY stensorKind $ AstProject2 $ unAstRawWrap t

rawY :: STensorKindType y -> AstTensor AstMethodShare s y
     -> Rep (AstRaw s) y
rawY stk t = case stk of
  STKScalar{} -> RepScalar $ AstRaw $ AstScalar t
  STKR STKScalar{} _ -> AstRaw t
  STKS STKScalar{} _ -> AstRawS t
  STKX STKScalar{} _ -> AstRawX t
  STKProduct{} -> AstRawWrap t
  STKUntyped -> HVectorPseudoTensor $ AstRawWrap t
  _ -> error "TODO"

unRawY :: STensorKindType y -> Rep (AstRaw s) y
       -> AstTensor AstMethodShare s y
unRawY stk t = case stk of
  STKScalar{} -> AstUnScalar $ unAstRaw $ unRepScalar t
  STKR STKScalar{} _ -> unAstRaw t
  STKS STKScalar{} _ -> unAstRawS t
  STKX STKScalar{} _ -> unAstRawX t
  STKProduct{} -> unAstRawWrap t
  STKUntyped -> unAstRawWrap $ unHVectorPseudoTensor t
  _ -> error "TODO"

instance AstSpan s => ShareTensor (AstRaw s) where
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tshare :: forall y. TensorKind y
         => Rep (AstRaw s) y -> Rep (AstRaw s) y
  tshare t = case stensorKind @y of
    STKScalar{} -> RepScalar $ tshare $ unRepScalar t
    STKR STKScalar{} _  | astIsSmall True (unAstRaw t) -> t
    STKR STKScalar{} _ -> case t of
      AstRaw (AstShare{}) -> t
      AstRaw (AstVar{}) -> t
      AstRaw (AstConstant(AstVar{})) -> t
      AstRaw (AstPrimalPart(AstVar{})) -> t
      AstRaw (AstDualPart(AstVar{})) -> t
      _ -> AstRaw $ fun1ToAst $ \ !var -> AstShare var (unAstRaw t)
    STKS STKScalar{} _  | astIsSmall True (unAstRawS t) -> t
    STKS STKScalar{} _ -> case t of
      AstRawS (AstShare{}) -> t
      AstRawS (AstVar{}) -> t
      AstRawS (AstConstant(AstVar{})) -> t
      AstRawS (AstPrimalPart(AstVar{})) -> t
      AstRawS (AstDualPart(AstVar{})) -> t
      _ -> AstRawS $ fun1ToAst $ \ !var -> AstShare var (unAstRawS t)
    STKX STKScalar{} _  | astIsSmall True (unAstRawX t) -> t
    STKX STKScalar{} _ -> case t of
      AstRawX (AstShare{}) -> t
      AstRawX (AstVar{}) -> t
      AstRawX (AstConstant(AstVar{})) -> t
      AstRawX (AstPrimalPart(AstVar{})) -> t
      AstRawX (AstDualPart(AstVar{})) -> t
      _ -> AstRawX $ fun1ToAst $ \ !var -> AstShare var (unAstRawX t)
    STKProduct{} | astIsSmall True (unAstRawWrap t) -> t
    STKProduct{} -> case t of
      AstRawWrap (AstShare{}) -> t
      AstRawWrap (AstVar{}) -> t
      AstRawWrap (AstConstant(AstVar{})) -> t
      AstRawWrap (AstPrimalPart(AstVar{})) -> t
      AstRawWrap (AstDualPart(AstVar{})) -> t
      _ -> AstRawWrap $ fun1ToAst $ \ !var -> AstShare var (unAstRawWrap t)
    STKUntyped{}
      | astIsSmall True (unAstRawWrap $ unHVectorPseudoTensor t) -> t
    STKUntyped{} -> case unHVectorPseudoTensor t of
      AstRawWrap (AstShare{}) -> t
      AstRawWrap (AstVar{}) -> t
      AstRawWrap (AstConstant(AstVar{})) -> t
      AstRawWrap (AstPrimalPart(AstVar{})) -> t
      AstRawWrap (AstDualPart(AstVar{})) -> t
      _ -> HVectorPseudoTensor $ AstRawWrap $ fun1ToAst $ \ !var ->
             AstShare var $ unAstRawWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tunpair (AstRawWrap (AstPair t1 t2)) =
     (rawY stensorKind t1, rawY stensorKind t2)
  tunpair t = let tShared = tshare t
              in (tproject1 tShared, tproject2 tShared)
  tunvector (HVectorPseudoTensor (AstRawWrap (AstMkHVector l))) = rawHVector l
  tunvector t = dunHVector $ unHVectorPseudoTensor $ tshare t
  taddShare stk t1 t2 =
    -- when we have Num(AstTensor), this is better:
    --   rawY stensorKind $ unRawY stensorKind t1 + unRawY stensorKind t2
    fromRepD $ addRepD (toRepDShare stk t1)
                       (toRepDShare stk t2)

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
  rdualPart = astSpanDualRaw . unAstRaw
  rD u u' = AstRaw $ astSpanD (unAstRaw u) u'
  rScale s t =
    AstDualPart $ AstConstant (unAstRaw s)
                  * AstD (unAstRaw $ rzero (rshape s)) t

  xshape t = case shapeAstFull $ unAstRawX t of
    FTKX sh -> sh
  xindex v ix =
    AstRawX $ AstIndexX (unAstRawX v) (unAstRaw <$> ix)
  xfromVector = AstRawX . AstFromVectorX . V.map unAstRawX
  xreplicate = AstRawX . AstReplicate SNat . unAstRawX
  xconst = AstRawX . fromPrimal . AstConstX
  xconstant = AstRawX . fromPrimal . unAstRawX
  xprimalPart = AstRawX . astSpanPrimalRaw . unAstRawX
  xdualPart = astSpanDualRaw . unAstRawX
  xD u u' = AstRawX $ astSpanD (unAstRawX u) u'

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
  sdualPart = astSpanDualRaw . unAstRawS
  sD u u' = AstRawS $ astSpanD (unAstRawS u) u'
  sScale s t = AstDualPart $ AstConstant (unAstRawS s) * AstD 0 t

instance AstSpan s => HVectorTensor (AstRaw s) (AstRawS s) where
  dshape = shapeAstHVector . unAstRawWrap
  tshapeFull stk t = case stk of
    STKScalar _ -> FTKScalar
    STKR STKScalar{} SNat -> shapeAstFull $ unAstRaw t
    STKS STKScalar{} sh -> FTKS sh
    STKX STKScalar{} sh -> withKnownShX sh shapeAstFull $ unAstRawX t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      FTKProduct (tshapeFull stk1 (tproject1 t))
                 (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unAstRawWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tcond stk b u v = case stk of
    STKScalar _ -> RepScalar $ ifF b (unRepScalar u) (unRepScalar v)
    STKR STKScalar{} SNat -> ifF b u v
    STKS STKScalar{} sh -> withKnownShS sh $ ifF b u v
    STKX STKScalar{} sh -> withKnownShX sh $ ifF b u v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstRawWrap $ AstCond b (unAstRawWrap u) (unAstRawWrap v)
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap
                  $ AstCond b (unAstRawWrap $ unHVectorPseudoTensor u)
                              (unAstRawWrap $ unHVectorPseudoTensor v)
    _ -> error "TODO"
  tprimalPart stk t = case stk of
    STKScalar _ -> RepScalar $ rprimalPart $ unRepScalar t
    STKR STKScalar{} SNat -> rprimalPart t
    STKS STKScalar{} sh -> withKnownShS sh $ sprimalPart t
    STKX STKScalar{} sh -> withKnownShX sh $ xprimalPart t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstRawWrap $ astSpanPrimalRaw $ unAstRawWrap t
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap
                  $ astSpanPrimalRaw $ unAstRawWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tdualPart stk t = case stk of
    STKScalar _ -> AstUnScalar $ rdualPart $ unRepScalar t
    STKR STKScalar{} SNat -> rdualPart t
    STKS STKScalar{} sh -> withKnownShS sh $ sdualPart t
    STKX STKScalar{} sh -> withKnownShX sh $ xdualPart t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      astSpanDualRaw $ unAstRawWrap t
    STKUntyped -> astSpanDualRaw $ unAstRawWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tD stk t d = case stk of
    STKScalar _ -> RepScalar $ rD (unRepScalar t) (AstScalar d)
    STKR STKScalar{} SNat -> rD t d
    STKS STKScalar{} sh -> withKnownShS sh $ sD t d
    STKX STKScalar{} sh -> withKnownShX sh $ xD t d
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      let (t1, t2) = tunpair t
          (d1, d2) = (AstProject1 d, AstProject2 d)  -- TODO: sharing
      in tpair (tD stk1 t1 d1) (tD stk2 t2 d2)
    STKUntyped -> error "TODO"
    _ -> error "TODO"
  dmkHVector = AstRawWrap . AstMkHVector . unRawHVector
  dlambda = dlambda @(AstRanked s)
  dHApply :: forall x z. (TensorKind x, TensorKind z)
          => HFunOf (AstRaw s) x z
          -> Rep (AstRaw s) x
          -> Rep (AstRaw s) z
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
  drev = drev @(AstRanked s)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstRaw s)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (AstRaw s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstRaw s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                    (TKProduct accShs eShs))
                         (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstRaw s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                    (TKProduct accShs eShs))
                         (ADTensorKind (TKProduct accShs eShs))
    -> Rep (AstRaw s) accShs
    -> Rep (AstRaw s) (BuildTensorKind k eShs)
    -> Rep (AstRaw s) (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      rawY stensorKind
      $ AstMapAccumRDer k accShs bShs eShs f df rf
                        (unRawY stensorKind acc0)
                        (unRawY stensorKind es)
  dmapAccumLDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstRaw s)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (AstRaw s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstRaw s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                    (TKProduct accShs eShs))
                         (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstRaw s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                    (TKProduct accShs eShs))
                         (ADTensorKind (TKProduct accShs eShs))
    -> Rep (AstRaw s) accShs
    -> Rep (AstRaw s) (BuildTensorKind k eShs)
    -> Rep (AstRaw s) (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      rawY stensorKind
      $ AstMapAccumLDer k accShs bShs eShs f df rf
                        (unRawY stensorKind acc0)
                        (unRawY stensorKind es)


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
deriving instance (IntegralF (AstTensor AstMethodLet s (TKR r n)))
                  => IntegralF (AstNoVectorize s r n)
deriving instance Fractional (AstTensor AstMethodLet s (TKR r n))
                  => Fractional (AstNoVectorize s r n)
deriving instance Floating (AstTensor AstMethodLet s (TKR r n))
                  => Floating (AstNoVectorize s r n)
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

type instance BoolOf (AstNoVectorizeX s) = AstBool AstMethodLet

instance IfF (AstNoVectorizeX s) where
  ifF b v1 v2 =
    AstNoVectorizeX $ unAstMixed
    $ ifF b (AstMixed $ unAstNoVectorizeX v1) (AstMixed $ unAstNoVectorizeX v2)
instance AstSpan s => EqF (AstNoVectorizeX s) where
  v1 ==. v2 = AstMixed (unAstNoVectorizeX v1) ==. AstMixed (unAstNoVectorizeX v2)
instance AstSpan s => OrdF (AstNoVectorizeX s) where
  v1 <. v2 = AstMixed (unAstNoVectorizeX v1) <. AstMixed (unAstNoVectorizeX v2)
deriving instance Eq ((AstNoVectorizeX s) r sh)
deriving instance Ord ((AstNoVectorizeX s) r sh)
deriving instance Num (AstTensor AstMethodLet s (TKX r sh)) => Num (AstNoVectorizeX s r sh)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKX r sh)))
                  => IntegralF (AstNoVectorizeX s r sh)
deriving instance Fractional (AstTensor AstMethodLet s (TKX r sh))
                  => Fractional (AstNoVectorizeX s r sh)
deriving instance Floating (AstTensor AstMethodLet s (TKX r sh))
                  => Floating (AstNoVectorizeX s r sh)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKX r sh)))
                  => RealFloatF (AstNoVectorizeX s r sh)

type instance Rep (AstNoVectorize s) (TKProduct x z) =
  AstNoVectorizeWrap (AstTensor AstMethodLet s (TKProduct x z))

instance Show (RepProductN (AstNoVectorize s) x y) where
  showsPrec d (RepProductN t) = showsPrec d t

instance AstSpan s => ProductTensor (AstNoVectorize s) where
  tpair t1 t2 = AstNoVectorizeWrap $ astPair (unNoVectorizeY stensorKind t1)
                                             (unNoVectorizeY stensorKind t2)
  tproject1 t = noVectorizeY stensorKind $ astProject1 $ unAstNoVectorizeWrap t
  tproject2 t = noVectorizeY stensorKind $ astProject2 $ unAstNoVectorizeWrap t

noVectorizeY :: STensorKindType y -> AstTensor AstMethodLet s y
             -> Rep (AstNoVectorize s) y
noVectorizeY stk t = case stk of
  STKScalar{} -> RepScalar $ AstNoVectorize $ AstScalar t
  STKR STKScalar{} _ -> AstNoVectorize t
  STKS STKScalar{} _ -> AstNoVectorizeS t
  STKX STKScalar{} _ -> AstNoVectorizeX t
  STKProduct{} -> AstNoVectorizeWrap t
  STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap t
  _ -> error "TODO"

unNoVectorizeY :: STensorKindType y -> Rep (AstNoVectorize s) y
               -> AstTensor AstMethodLet s y
unNoVectorizeY stk t = case stk of
  STKScalar{} -> AstUnScalar $ unAstNoVectorize $ unRepScalar t
  STKR STKScalar{} _ -> unAstNoVectorize t
  STKS STKScalar{} _ -> unAstNoVectorizeS t
  STKX STKScalar{} _ -> unAstNoVectorizeX t
  STKProduct{} -> unAstNoVectorizeWrap t
  STKUntyped -> unAstNoVectorizeWrap $ unHVectorPseudoTensor t
  _ -> error "TODO"

unAstNoVectorize2 :: AstNoVectorize s r n -> AstRanked s r n
unAstNoVectorize2 = AstRanked . unAstNoVectorize

astNoVectorize2 :: AstRanked s r n -> AstNoVectorize s r n
astNoVectorize2 = AstNoVectorize . unAstRanked

unAstNoVectorizeS2 :: AstNoVectorizeS s r sh -> AstShaped s r sh
unAstNoVectorizeS2 = AstShaped . unAstNoVectorizeS

astNoVectorizeS2 :: AstShaped s r sh -> AstNoVectorizeS s r sh
astNoVectorizeS2 = AstNoVectorizeS . unAstShaped

unAstNoVectorizeX2 :: AstNoVectorizeX s r sh -> AstMixed s r sh
unAstNoVectorizeX2 = AstMixed . unAstNoVectorizeX

astNoVectorizeX2 :: AstMixed s r sh -> AstNoVectorizeX s r sh
astNoVectorizeX2 = AstNoVectorizeX . unAstMixed

unNoVectorizeHVector :: HVector (AstNoVectorize s) -> HVector (AstGeneric AstMethodLet s)
unNoVectorizeHVector =
  let f (DynamicRanked (AstNoVectorize t)) = DynamicRanked (AstGeneric t)
      f (DynamicShaped (AstNoVectorizeS t)) = DynamicShaped (AstGenericS t)
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
  rletHFunIn a f = astNoVectorize2 $ rletHFunIn a (unAstNoVectorize2 . f)
  sletHFunIn a f = astNoVectorizeS2 $ sletHFunIn a (unAstNoVectorizeS2 . f)
  dletHFunInHVector t f =
    AstNoVectorizeWrap
    $ dletHFunInHVector t (unAstNoVectorizeWrap . f)
  dlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstNoVectorize s) x
       -> (RepDeep (AstNoVectorize s) x -> Rep (AstNoVectorize s) z)
       -> Rep (AstNoVectorize s) z
  dlet u f = case stensorKind @x of
    STKScalar{} -> blet u f
    STKR STKScalar{} _ -> blet u f
    STKS STKScalar{} _ -> blet u f
    STKX STKScalar{} _ -> blet u f
    stk@STKProduct{} ->
      blet u $ \ !uShared -> f (repDeepDuplicable stk uShared)
    STKUntyped{} -> tlet u f
    _ -> error "TODO"
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstNoVectorize s) x
       -> (RepShallow (AstNoVectorize s) x -> Rep (AstNoVectorize s) z)
       -> Rep (AstNoVectorize s) z
  tlet u f = case stensorKind @x of
    STKScalar{} -> blet u f
    STKR STKScalar{} _ -> blet u f
    STKS STKScalar{} _ -> blet u f
    STKX STKScalar{} _ -> blet u f
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      blet u $ \ !uShared -> f (tproject1 uShared, tproject2 uShared)
    STKUntyped{} ->
      blet u $ \ !uShared -> f $ dunHVector $ unHVectorPseudoTensor uShared
    _ -> error "TODO"
  blet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstNoVectorize s) x
       -> (Rep (AstNoVectorize s) x -> Rep (AstNoVectorize s) z)
       -> Rep (AstNoVectorize s) z
  blet u f = case stensorKind @x of
    STKScalar{} -> blet (unRepScalar u) (f . RepScalar)
    STKR STKScalar{} _ -> noVectorizeY (stensorKind @z)
              $ astLetFun
                  (unAstNoVectorize u)
                  (unNoVectorizeY (stensorKind @z) . f . AstNoVectorize)
    STKS STKScalar{} _ -> noVectorizeY (stensorKind @z)
              $ astLetFun
                  (unAstNoVectorizeS u)
                  (unNoVectorizeY (stensorKind @z) . f . AstNoVectorizeS)
    STKX STKScalar{} _ -> noVectorizeY (stensorKind @z)
              $ astLetFun
                  (unAstNoVectorizeX u)
                  (unNoVectorizeY (stensorKind @z) . f . AstNoVectorizeX)
    STKProduct{} ->
      noVectorizeY (stensorKind @z)
      $ astLetFun
          (unAstNoVectorizeWrap u)
          (unNoVectorizeY (stensorKind @z) . f . AstNoVectorizeWrap)
    STKUntyped{} ->
      noVectorizeY (stensorKind @z)
      $ astLetFun
          (unAstNoVectorizeWrap $ unHVectorPseudoTensor u)
          (unNoVectorizeY (stensorKind @z)
           . f . HVectorPseudoTensor . AstNoVectorizeWrap)
    _ -> error "TODO"

  toShare :: forall y. TensorKind y
          => Rep (AstNoVectorize s) y
          -> Rep (AstRaw s) y
  toShare t = case stensorKind @y of
    STKScalar _ ->
      RepScalar $ AstRaw $ AstToShare $ unAstNoVectorize $ unRepScalar t
    STKR STKScalar{} SNat -> AstRaw $ AstToShare $ unAstNoVectorize t
    STKS STKScalar{} sh -> withKnownShS sh $ AstRawS $ AstToShare $ unAstNoVectorizeS t
    STKX STKScalar{} sh -> withKnownShX sh $ AstRawX $ AstToShare $ unAstNoVectorizeX t
    STKProduct{} -> AstRawWrap $ AstToShare $ unAstNoVectorizeWrap t
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap $ AstToShare
                  $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tconstant stk t = case stk of
    STKScalar _ -> RepScalar $ rconstant $ unRepScalar t
    STKR STKScalar{} SNat -> rconstant t
    STKS STKScalar{} sh -> withKnownShS sh $ sconstant t
    STKX STKScalar{} sh -> withKnownShX sh $ xconstant t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstNoVectorizeWrap $ fromPrimal $ unAstNoVectorizeWrap t
    STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap $ fromPrimal
                  $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  taddLet stk t1 t2 | Dict <- lemTensorKindOfS stk =
    blet t1 $ \ !u1 ->
    blet t2 $ \ !u2 ->
      fromRepD $ addRepD (toRepDDuplicable stk u1)
                         (toRepDDuplicable stk u2)

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
  rdualPart = rdualPart . unAstNoVectorize2
  rD u u' = astNoVectorize2 $ rD (unAstNoVectorize2 u) u'
  rScale s t = rScale @(AstRanked s) (unAstNoVectorize2 s) t

  xshape t = case shapeAstFull $ unAstNoVectorizeX t of
    FTKX sh -> sh
  xindex v ix =
    astNoVectorizeX2 $ xindex (unAstNoVectorizeX2 v) (unAstNoVectorize2 <$> ix)
  xfromVector = astNoVectorizeX2 . xfromVector . V.map unAstNoVectorizeX2
  xreplicate = astNoVectorizeX2 . xreplicate . unAstNoVectorizeX2
  xconst = astNoVectorizeX2 . xconst
  xconstant = astNoVectorizeX2 . xconstant . unAstNoVectorizeX2
  xprimalPart = astNoVectorizeX2 . xprimalPart . unAstNoVectorizeX2
  xdualPart = xdualPart . unAstNoVectorizeX2
  xD u u' =
    astNoVectorizeX2 $ xD (unAstNoVectorizeX2 u) u'

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
  sdualPart = sdualPart . unAstNoVectorizeS2
  sD u u' = astNoVectorizeS2 $ sD @(AstShaped s) (unAstNoVectorizeS2 u) u'
  sScale s t = sScale @(AstShaped s) (unAstNoVectorizeS2 s) t

instance AstSpan s => HVectorTensor (AstNoVectorize s) (AstNoVectorizeS s) where
  dshape = dshape . unAstNoVectorizeWrap
  tshapeFull stk t = case stk of
    STKScalar _ -> FTKScalar
    STKR STKScalar{} SNat -> shapeAstFull $ unAstNoVectorize t
    STKS STKScalar{} sh -> FTKS sh
    STKX STKScalar{} sh -> withKnownShX sh shapeAstFull $ unAstNoVectorizeX t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      FTKProduct (tshapeFull stk1 (tproject1 t))
                 (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tcond stk b u v = case stk of
    STKScalar _ -> RepScalar $ ifF b (unRepScalar u) (unRepScalar v)
    STKR STKScalar{} SNat -> ifF b u v
    STKS STKScalar{} sh -> withKnownShS sh $ ifF b u v
    STKX STKScalar{} sh -> withKnownShX sh $ ifF b u v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstNoVectorizeWrap
      $ AstCond b (unAstNoVectorizeWrap u) (unAstNoVectorizeWrap v)
    STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap
                  $ AstCond b (unAstNoVectorizeWrap $ unHVectorPseudoTensor u)
                              (unAstNoVectorizeWrap $ unHVectorPseudoTensor v)
    _ -> error "TODO"
  tprimalPart stk t = case stk of
    STKScalar _ -> RepScalar $ rprimalPart $ unRepScalar t
    STKR STKScalar{} SNat -> rprimalPart t
    STKS STKScalar{} sh -> withKnownShS sh $ sprimalPart t
    STKX STKScalar{} sh -> withKnownShX sh $ xprimalPart t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstNoVectorizeWrap $ astSpanPrimal $ unAstNoVectorizeWrap t
    STKUntyped -> HVectorPseudoTensor $ AstNoVectorizeWrap
                  $ astSpanPrimal $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tdualPart stk t = case stk of
    STKScalar _ -> AstUnScalar $ rdualPart $ unRepScalar t
    STKR STKScalar{} SNat -> rdualPart t
    STKS STKScalar{} sh -> withKnownShS sh $ sdualPart t
    STKX STKScalar{} sh -> withKnownShX sh $ xdualPart t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      astSpanDual $ unAstNoVectorizeWrap t
    STKUntyped -> astSpanDual $ unAstNoVectorizeWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tD stk t d = case stk of
    STKScalar _ -> RepScalar $ rD (unRepScalar t) (AstScalar d)
    STKR STKScalar{} SNat -> rD t d
    STKS STKScalar{} sh -> withKnownShS sh $ sD t d
    STKX STKScalar{} sh -> withKnownShX sh $ xD t d
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      let (t1, t2) = (tproject1 t, tproject2 t)  -- TODO: sharing
          (d1, d2) = (AstProject1 d, AstProject2 d)  -- TODO: sharing
      in tpair (tD stk1 t1 d1) (tD stk2 t2 d2)
    STKUntyped -> error "TODO"
    _ -> error "TODO"
  dmkHVector =
    AstNoVectorizeWrap . AstMkHVector . unNoVectorizeHVector
  dlambda = dlambda @(AstRanked s)
  dHApply :: forall x y. (TensorKind x, TensorKind y)
          => HFunOf (AstNoVectorize s) x y
          -> Rep (AstNoVectorize s) x
          -> Rep (AstNoVectorize s) y
  dHApply t ll = noVectorizeY (stensorKind @y) $ astHApply t
                 $ unNoVectorizeY (stensorKind @x) ll
  dunHVector =
    noVectorizeHVectorR . dunHVector . unAstNoVectorizeWrap
  dbuild1 k f =
    AstNoVectorizeWrap
    $ AstBuildHVector1 k $ funToAstI (unAstNoVectorizeWrap . f . AstNoVectorize)
  drev = drev @(AstRanked s)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstNoVectorize s)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (AstNoVectorize s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstNoVectorize s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                            (TKProduct accShs eShs))
                                 (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstNoVectorize s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                            (TKProduct accShs eShs))
                                 (ADTensorKind (TKProduct accShs eShs))
    -> Rep (AstNoVectorize s) accShs
    -> Rep (AstNoVectorize s) (BuildTensorKind k eShs)
    -> Rep (AstNoVectorize s) (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      noVectorizeY stensorKind
      $ AstMapAccumRDer k accShs bShs eShs f df rf
                        (unNoVectorizeY stensorKind acc0)
                        (unNoVectorizeY stensorKind es)
  dmapAccumLDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstNoVectorize s)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (AstNoVectorize s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstNoVectorize s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                            (TKProduct accShs eShs))
                                 (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstNoVectorize s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                            (TKProduct accShs eShs))
                                 (ADTensorKind (TKProduct accShs eShs))
    -> Rep (AstNoVectorize s) accShs
    -> Rep (AstNoVectorize s) (BuildTensorKind k eShs)
    -> Rep (AstNoVectorize s) (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      noVectorizeY stensorKind
      $ AstMapAccumLDer k accShs bShs eShs f df rf
                        (unNoVectorizeY stensorKind acc0)
                        (unNoVectorizeY stensorKind es)


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
deriving instance (IntegralF (AstTensor AstMethodLet s (TKR r n)))
                  => IntegralF (AstNoSimplify s r n)
deriving instance Fractional (AstTensor AstMethodLet s (TKR r n))
                  => Fractional (AstNoSimplify s r n)
deriving instance Floating (AstTensor AstMethodLet s (TKR r n))
                  => Floating (AstNoSimplify s r n)
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

type instance BoolOf (AstNoSimplifyX s) = AstBool AstMethodLet

instance IfF (AstNoSimplifyX s) where
  ifF b v1 v2 =
    AstNoSimplifyX $ unAstMixed
    $ ifF b (AstMixed $ unAstNoSimplifyX v1) (AstMixed $ unAstNoSimplifyX v2)
instance AstSpan s => EqF (AstNoSimplifyX s) where
  v1 ==. v2 = AstMixed (unAstNoSimplifyX v1) ==. AstMixed (unAstNoSimplifyX v2)
instance AstSpan s => OrdF (AstNoSimplifyX s) where
  v1 <. v2 = AstMixed (unAstNoSimplifyX v1) <. AstMixed (unAstNoSimplifyX v2)
deriving instance Eq (AstNoSimplifyX s r sh)
deriving instance Ord (AstNoSimplifyX s r sh)
deriving instance Num (AstTensor AstMethodLet s (TKX r sh)) => Num (AstNoSimplifyX s r sh)
deriving instance (IntegralF (AstTensor AstMethodLet s (TKX r sh)))
                  => IntegralF (AstNoSimplifyX s r sh)
deriving instance Fractional (AstTensor AstMethodLet s (TKX r sh))
                  => Fractional (AstNoSimplifyX s r sh)
deriving instance Floating (AstTensor AstMethodLet s (TKX r sh))
                  => Floating (AstNoSimplifyX s r sh)
deriving instance (RealFloatF (AstTensor AstMethodLet s (TKX r sh)))
                  => RealFloatF (AstNoSimplifyX s r sh)

type instance Rep (AstNoSimplify s) (TKProduct x z) =
  AstNoSimplifyWrap (AstTensor AstMethodLet s (TKProduct x z))

instance Show (RepProductN (AstNoSimplify s) x y) where
  showsPrec d (RepProductN t) = showsPrec d t

instance AstSpan s => ProductTensor (AstNoSimplify s) where
  tpair t1 t2 = AstNoSimplifyWrap $ astPair (unNoSimplifyY stensorKind t1)
                                            (unNoSimplifyY stensorKind t2)
  tproject1 t = noSimplifyY stensorKind $ astProject1 $ unAstNoSimplifyWrap t
  tproject2 t = noSimplifyY stensorKind $ astProject2 $ unAstNoSimplifyWrap t

astLetFunNoSimplify
  :: forall x z s. (TensorKind x, TensorKind z, AstSpan s)
  => AstTensor AstMethodLet s x
  -> (AstTensor AstMethodLet s x -> AstTensor AstMethodLet s z)
  -> AstTensor AstMethodLet s z
astLetFunNoSimplify a f | astIsSmall True a = f a
                            -- too important an optimization to skip
astLetFunNoSimplify a f =
  let sh = shapeAstFull a
      (var, ast) = funToAst sh f
  in AstLet var a ast  -- safe, because subsitution ruled out above

astLetHFunInFunNoSimplify
  :: (TensorKind x, TensorKind y, TensorKind z)
  => AstHFun x y -> (AstHFun x y -> AstTensor AstMethodLet s z)
  -> AstTensor AstMethodLet s z
astLetHFunInFunNoSimplify a f =
  let shss = domainShapeAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunIn var a (f ast)

noSimplifyY :: STensorKindType y -> AstTensor AstMethodLet s y
            -> Rep (AstNoSimplify s) y
noSimplifyY stk t = case stk of
  STKScalar{} -> RepScalar $ AstNoSimplify $ AstScalar t
  STKR STKScalar{} _ -> AstNoSimplify t
  STKS STKScalar{} _ -> AstNoSimplifyS t
  STKX STKScalar{} _ -> AstNoSimplifyX t
  STKProduct{} -> AstNoSimplifyWrap t
  STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap t
  _ -> error "TODO"

unNoSimplifyY :: STensorKindType y -> Rep (AstNoSimplify s) y
              -> AstTensor AstMethodLet s y
unNoSimplifyY stk t = case stk of
  STKScalar{} -> AstUnScalar $ unAstNoSimplify $ unRepScalar t
  STKR STKScalar{} _ -> unAstNoSimplify t
  STKS STKScalar{} _ -> unAstNoSimplifyS t
  STKX STKScalar{} _ -> unAstNoSimplifyX t
  STKProduct{} -> unAstNoSimplifyWrap t
  STKUntyped -> unAstNoSimplifyWrap $ unHVectorPseudoTensor t
  _ -> error "TODO"

unNoSimplifyHVector :: HVector (AstNoSimplify s) -> HVector (AstGeneric AstMethodLet s)
unNoSimplifyHVector =
  let f (DynamicRanked (AstNoSimplify t)) = DynamicRanked $ AstGeneric t
      f (DynamicShaped (AstNoSimplifyS t)) = DynamicShaped (AstGenericS t)
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
  rletHFunIn a f = AstNoSimplify $ astLetHFunInFunNoSimplify a (unAstNoSimplify . f)
  sletHFunIn a f = AstNoSimplifyS $ astLetHFunInFunNoSimplify a (unAstNoSimplifyS . f)
  dletHFunInHVector t f =
    AstNoSimplifyWrap
    $ astLetHFunInFunNoSimplify t (unAstNoSimplifyWrap . f)
  dlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstNoSimplify s) x
       -> (RepDeep (AstNoSimplify s) x -> Rep (AstNoSimplify s) z)
       -> Rep (AstNoSimplify s) z
  dlet u f = case stensorKind @x of
    STKScalar{} -> blet u f
    STKR STKScalar{} _ -> blet u f
    STKS STKScalar{} _ -> blet u f
    STKX STKScalar{} _ -> blet u f
    stk@STKProduct{} ->
      blet u $ \ !uShared -> f (repDeepDuplicable stk uShared)
    STKUntyped{} -> tlet u f
    _ -> error "TODO"
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstNoSimplify s) x
       -> (RepShallow (AstNoSimplify s) x -> Rep (AstNoSimplify s) z)
       -> Rep (AstNoSimplify s)  z
  tlet u f = case stensorKind @x of
    STKScalar{} -> blet u f
    STKR STKScalar{} _ -> blet u f
    STKS STKScalar{} _ -> blet u f
    STKX STKScalar{} _ -> blet u f
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      blet u $ \ !uShared -> f (tproject1 uShared, tproject2 uShared)
    STKUntyped{} ->
      blet u $ \ !uShared -> f $ dunHVector $ unHVectorPseudoTensor uShared
    _ -> error "TODO"
  blet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (AstNoSimplify s) x
       -> (Rep (AstNoSimplify s) x -> Rep (AstNoSimplify s) z)
       -> Rep (AstNoSimplify s)  z
  blet u f = case stensorKind @x of
    STKScalar{} -> blet (unRepScalar u) (f . RepScalar)
    STKR STKScalar{} _ -> noSimplifyY (stensorKind @z)
              $ astLetFunNoSimplify
                  (unAstNoSimplify u)
                  (unNoSimplifyY (stensorKind @z) . f . AstNoSimplify)
    STKS STKScalar{} _ -> noSimplifyY (stensorKind @z)
              $ astLetFunNoSimplify
                  (unAstNoSimplifyS u)
                  (unNoSimplifyY (stensorKind @z) . f . AstNoSimplifyS)
    STKX STKScalar{} _ -> noSimplifyY (stensorKind @z)
              $ astLetFunNoSimplify
                  (unAstNoSimplifyX u)
                  (unNoSimplifyY (stensorKind @z) . f . AstNoSimplifyX)
    STKProduct{} ->
      noSimplifyY (stensorKind @z)
      $ astLetFunNoSimplify
          (unAstNoSimplifyWrap u)
          (unNoSimplifyY (stensorKind @z) . f . AstNoSimplifyWrap)
    STKUntyped{} ->
      noSimplifyY (stensorKind @z)
      $ astLetFunNoSimplify
          (unAstNoSimplifyWrap $ unHVectorPseudoTensor u)
          (unNoSimplifyY (stensorKind @z)
           . f . HVectorPseudoTensor . AstNoSimplifyWrap)
    _ -> error "TODO"

  toShare :: forall y. TensorKind y
          => Rep (AstNoSimplify s) y
          -> Rep (AstRaw s) y
  toShare t = case stensorKind @y of
    STKScalar _ ->
      RepScalar $ AstRaw $ AstToShare $ unAstNoSimplify $ unRepScalar t
    STKR STKScalar{} SNat -> AstRaw $ AstToShare $ unAstNoSimplify t
    STKS STKScalar{} sh -> withKnownShS sh $ AstRawS $ AstToShare $ unAstNoSimplifyS t
    STKX STKScalar{} sh -> withKnownShX sh $ AstRawX $ AstToShare $ unAstNoSimplifyX t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstRawWrap $ AstToShare $ unAstNoSimplifyWrap t
    STKUntyped -> HVectorPseudoTensor $ AstRawWrap $ AstToShare
                  $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tconstant stk t = case stk of
    STKScalar _ -> RepScalar $ rconstant $ unRepScalar t
    STKR STKScalar{} SNat -> rconstant t
    STKS STKScalar{} sh -> withKnownShS sh $ sconstant t
    STKX STKScalar{} sh -> withKnownShX sh $ xconstant t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstNoSimplifyWrap $ fromPrimal $ unAstNoSimplifyWrap t
    STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap $ fromPrimal
                  $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  taddLet stk t1 t2 | Dict <- lemTensorKindOfS stk =
    blet t1 $ \ !u1 ->
    blet t2 $ \ !u2 ->
      fromRepD $ addRepD (toRepDDuplicable stk u1)
                         (toRepDDuplicable stk u2)

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
  rbuild1 k f = withSNat k $ \snat ->
    AstNoSimplify $ astBuild1Vectorize snat (unAstNoSimplify . f . AstNoSimplify)
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
  rdualPart = astSpanDual . unAstNoSimplify
  rD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) u'
  rScale s t =
    astDualPart $ AstConstant (unAstNoSimplify s)
                  * AstD (unAstRanked $ rzero (rshape s)) t

  xshape t = case shapeAstFull $ unAstNoSimplifyX t of
    FTKX sh -> sh
  xindex v ix =
    AstNoSimplifyX $ AstIndexX (unAstNoSimplifyX v) (unAstNoSimplify <$> ix)
  xfromVector = AstNoSimplifyX . AstFromVectorX . V.map unAstNoSimplifyX
  xreplicate = AstNoSimplifyX . AstReplicate SNat . unAstNoSimplifyX
  xconst = AstNoSimplifyX . fromPrimal . AstConstX
  xconstant = AstNoSimplifyX . fromPrimal . unAstNoSimplifyX
  xprimalPart = AstNoSimplifyX . astSpanPrimal . unAstNoSimplifyX
  xdualPart = astSpanDual . unAstNoSimplifyX
  xD u u' = AstNoSimplifyX $ astSpanD (unAstNoSimplifyX u) u'

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
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (AstNoSimplifyS s) -> AstNoSimplifyS s r sh)
          -> AstNoSimplifyS s r (n ': sh)
  sbuild1 f =
    AstNoSimplifyS
    $ astBuild1Vectorize (SNat @n) (unAstNoSimplifyS . f . AstNoSimplify)
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
  sdualPart = astSpanDual . unAstNoSimplifyS
  sD u u' = AstNoSimplifyS $ astSpanD (unAstNoSimplifyS u) u'
  sScale s t =
    astDualPart $ AstConstant (unAstNoSimplifyS s) * AstD 0 t

instance AstSpan s => HVectorTensor (AstNoSimplify s) (AstNoSimplifyS s) where
  dshape = shapeAstHVector . unAstNoSimplifyWrap
  tshapeFull stk t = case stk of
    STKScalar _ -> FTKScalar
    STKR STKScalar{} SNat -> shapeAstFull $ unAstNoSimplify t
    STKS STKScalar{} sh -> FTKS sh
    STKX STKScalar{} sh -> withKnownShX sh shapeAstFull $ unAstNoSimplifyX t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      FTKProduct (tshapeFull stk1 (tproject1 t))
                 (tshapeFull stk2 (tproject2 t))
    STKUntyped -> shapeAstFull $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tcond stk b u v = case stk of
    STKScalar _ -> RepScalar $ ifF b (unRepScalar u) (unRepScalar v)
    STKR STKScalar{} SNat -> ifF b u v
    STKS STKScalar{} sh -> withKnownShS sh $ ifF b u v
    STKX STKScalar{} sh -> withKnownShX sh $ ifF b u v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstNoSimplifyWrap
      $ AstCond b (unAstNoSimplifyWrap u) (unAstNoSimplifyWrap v)
    STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap
                  $ AstCond b (unAstNoSimplifyWrap $ unHVectorPseudoTensor u)
                              (unAstNoSimplifyWrap $ unHVectorPseudoTensor v)
    _ -> error "TODO"
  tprimalPart stk t = case stk of
    STKScalar _ -> RepScalar $ rprimalPart $ unRepScalar t
    STKR STKScalar{} SNat -> rprimalPart t
    STKS STKScalar{} sh -> withKnownShS sh $ sprimalPart t
    STKX STKScalar{} sh -> withKnownShX sh $ xprimalPart t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      AstNoSimplifyWrap $ astSpanPrimal $ unAstNoSimplifyWrap t
    STKUntyped -> HVectorPseudoTensor $ AstNoSimplifyWrap
                  $ astSpanPrimal $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tdualPart stk t = case stk of
    STKScalar _ -> AstUnScalar $ rdualPart $ unRepScalar t
    STKR STKScalar{} SNat -> rdualPart t
    STKS STKScalar{} sh -> withKnownShS sh $ sdualPart t
    STKX STKScalar{} sh -> withKnownShX sh $ xdualPart t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      astSpanDual $ unAstNoSimplifyWrap t
    STKUntyped -> astSpanDual $ unAstNoSimplifyWrap $ unHVectorPseudoTensor t
    _ -> error "TODO"
  tD stk t d = case stk of
    STKScalar _ -> RepScalar $ rD (unRepScalar t) (AstScalar d)
    STKR STKScalar{} SNat -> rD t d
    STKS STKScalar{} sh -> withKnownShS sh $ sD t d
    STKX STKScalar{} sh -> withKnownShX sh $ xD t d
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      let (t1, t2) = (tproject1 t, tproject2 t)  -- TODO: sharing
          (d1, d2) = (AstProject1 d, AstProject2 d)  -- TODO: sharing
      in tpair (tD stk1 t1 d1) (tD stk2 t2 d2)
    STKUntyped -> error "TODO"
    _ -> error "TODO"
  dmkHVector =
    AstNoSimplifyWrap . AstMkHVector . unNoSimplifyHVector
  dlambda = dlambda @(AstRanked s)
  dHApply :: forall x y. (TensorKind x, TensorKind y)
          => HFunOf (AstNoSimplify s) x y
          -> Rep (AstNoSimplify s) x
          -> Rep (AstNoSimplify s) y
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
                $ astBuild1Vectorize
                    k (unAstNoSimplifyWrap . f . AstNoSimplify)
  drev = drev @(AstRanked s)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstNoSimplify s)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (AstNoSimplify s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstNoSimplify s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                           (TKProduct accShs eShs))
                                (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstNoSimplify s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs eShs))
    -> Rep (AstNoSimplify s) accShs
    -> Rep (AstNoSimplify s) (BuildTensorKind k eShs)
    -> Rep (AstNoSimplify s) (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      noSimplifyY stensorKind
      $ AstMapAccumRDer k accShs bShs eShs f df rf
                        (unNoSimplifyY stensorKind acc0)
                        (unNoSimplifyY stensorKind es)
  dmapAccumLDer
    :: forall accShs bShs eShs k.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (AstNoSimplify s)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (AstNoSimplify s) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (AstNoSimplify s) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                           (TKProduct accShs eShs))
                                (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (AstNoSimplify s) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                           (TKProduct accShs eShs))
                                (ADTensorKind (TKProduct accShs eShs))
    -> Rep (AstNoSimplify s) accShs
    -> Rep (AstNoSimplify s) (BuildTensorKind k eShs)
    -> Rep (AstNoSimplify s) (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      noSimplifyY stensorKind
      $ AstMapAccumLDer k accShs bShs eShs f df rf
                        (unNoSimplifyY stensorKind acc0)
                        (unNoSimplifyY stensorKind es)


-- TODO: move to a better home:

-- TODO: these can't easily be in AstSimplify, because of unRankedY

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
    let idom = SubstitutionPayload $ AstMkHVector asts1
        !derivative = substituteAst
                        idom artVarDomainRev artDerivativeRev in
    let !primal = substituteAst
                    idom artVarDomainRev artPrimalRev
    in (artVarDtRev, vars1, derivative, primal)
 stk ->
   let dynvar = case stk of
         STKR (STKScalar @r _) SNat ->
           AstDynamicVarName @Nat @r @'[]  -- TODO: ftk
                             (varNameToAstVarId artVarDomainRev)
         STKS @_ @sh (STKScalar @r _) sh -> withKnownShS sh $
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
          ++ " -> " ++ printAstSimpleY renames derivative

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
          ++ " -> " ++ printAstPrettyY renames derivative

printArtifactPrimalSimple
  :: forall x z. (TensorKind x, TensorKind z)
  => IntMap String
  -> AstArtifactRev x z
  -> String
printArtifactPrimalSimple renames art =
  let !(_, !vars1, _, !primal) = prettifyArtifactRev art in
  let !varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimpleY renames primal

printArtifactPrimalPretty
  :: forall x z. (TensorKind x, TensorKind z)
  => IntMap String
  -> AstArtifactRev x z
  -> String
printArtifactPrimalPretty renames art =
  let !(_, !vars1, _, !primal) = prettifyArtifactRev art in
  let !varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPrettyY renames primal
