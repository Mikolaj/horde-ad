{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and (forward) derivative
-- calculation for an objective function on values of complicated
-- types (e.g., with tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Optimizers are add-ons.
module HordeAd.Core.Engine
  ( -- * Reverse derivative adaptors
    rev, revDt, revArtifactAdapt
  , revProduceArtifactWithoutInterpretation, revEvalArtifact
    -- * Forward derivative adaptors
  , fwd, fwdEvalArtifact
    -- * Old gradient adaptors
  , crev, crevDt
    -- * Old derivative adaptors
  , cfwd
  ) where

import Prelude

import Data.Int (Int64)
import Data.Maybe (fromMaybe, isJust)
import GHC.TypeLits (KnownNat)
import Type.Reflection (Typeable)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstTools
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorAst
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray, OSArray)

-- * Reverse derivative adaptors

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names to @rev@, but newcomers may have trouble understanding them.

-- | This simplified version of the reverse derivative operation
-- sets the incoming cotangent @dt@ to be 1 and assumes the codomain
-- of the function to be differentiated is a single ranked or shaped tensor
-- (or another datatype known to the libray but determined by only three
-- parameters @r@, @y@ and @g@, which is already not true for a pair
-- of different tensors).
--
-- We don't enforce (e.g., by quantifcation) that the objective function
-- is closed, because we evaluate the result of the differentiation
-- down to concrete arrays and so there's no risk of confusion of cotangents
-- from different levels of differentiation if it's done multiple times.
rev
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), TensorKind (X astvals), TensorKind z
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => (astvals -> Rep (AstRanked FullSpan) z)
  -> Value astvals
  -> Value astvals
{-# INLINE rev #-}
rev f vals = revDtMaybe f vals Nothing

-- | This version of the reverse derivative operation
-- explicitly takes the sensitivity parameter (the incoming cotangent).
-- It also permits an aribtrary (nested tuple+) type of not only the domain
-- but also the codomain of the function to be differentiated. The downside
-- is that if the function doesn't have a type signature,
-- the type often has to be spelled in full, instead of giving
-- only the rank or shape and/or the base scalar type of a single
-- tensor codomain.
revDt
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), TensorKind (X astvals), TensorKind z
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => (astvals -> Rep (AstRanked FullSpan) z)
  -> Value astvals
  -> Rep ORArray (ADTensorKind z)
  -> Value astvals
{-# INLINE revDt #-}
revDt f vals dt = revDtMaybe f vals (Just dt)

revDtMaybe
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), TensorKind (X astvals), TensorKind z
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => (astvals -> Rep (AstRanked FullSpan) z)
  -> Value astvals
  -> Maybe (Rep ORArray (ADTensorKind z))
  -> Value astvals  -- morally (ADTensorKind astvals)
{-# INLINE revDtMaybe #-}
revDtMaybe f vals0 mdt | Dict <- lemTensorKindOfAD (stensorKind @(X astvals)) =
  let g :: Rep (AstRanked FullSpan) (X astvals)
        -> Rep (AstRanked FullSpan) z
      g !hv = tlet hv $ \ !hvShared ->
        f $ parseHVector (fromValue vals0) (repDeepDuplicable stensorKind hvShared)
      valsH = toHVectorOf vals0
      voidH = tshapeFull stensorKind valsH
      artifact = fst $ revProduceArtifact (isJust mdt) g emptyEnv voidH
  in parseHVectorAD vals0 $ repDeepDuplicable stensorKind
     $ fst $ revEvalArtifact artifact valsH mdt
{- TODO
{-# SPECIALIZE revDtMaybe
  :: ( KnownNat n
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => (astvals -> AstRanked FullSpan Double n)
  -> Value astvals
  -> Maybe (ORArray Double n)
  -> Value astvals #-}
-}

revArtifactAdapt
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), TensorKind (X astvals), TensorKind z
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => Bool
  -> (astvals -> Rep (AstRanked FullSpan) z)
  -> Value astvals
  -> (AstArtifactRev (X astvals) z, Delta (AstRaw PrimalSpan) z )
revArtifactAdapt hasDt f vals0 =
  let g :: Rep (AstRanked FullSpan) (X astvals)
        -> Rep (AstRanked FullSpan) z
      g !hv = tlet hv $ \ !hvShared ->
        f $ parseHVector (fromValue vals0) (repDeepDuplicable stensorKind hvShared)
      valsH = toHVectorOf @ORArray vals0
      voidH = tshapeFull stensorKind valsH
  in revProduceArtifact hasDt g emptyEnv voidH
{- TODO
{-# SPECIALIZE revArtifactAdapt
  :: ( KnownNat n
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => Bool -> (astvals -> AstRanked FullSpan Double n) -> Value astvals
  -> (AstArtifactRev TKUntyped (TKR Double n), Delta (AstRaw PrimalSpan) (TKR Double n)) #-}
-}

revProduceArtifactWithoutInterpretation
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (Rep (ADVal (AstRaw PrimalSpan)) x
      -> Rep (ADVal (AstRaw PrimalSpan)) z)
  -> TensorKindFull x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifactWithoutInterpretation #-}
revProduceArtifactWithoutInterpretation hasDt f =
  revArtifactFromForwardPass @x @z hasDt (forwardPassByApplication f)

forwardPassByApplication
  :: forall x z. TensorKind x
  => (Rep (ADVal (AstRaw PrimalSpan)) x
      -> Rep (ADVal (AstRaw PrimalSpan)) z)
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> Rep (ADVal (AstRaw PrimalSpan)) z
{-# INLINE forwardPassByApplication #-}
forwardPassByApplication g hVectorPrimal _var _hVector =
  let deltaInputs = generateDeltaInputs $ shapeAstFull hVectorPrimal
      varInputs = makeADInputs (rawY (stensorKind @x) hVectorPrimal)
                               deltaInputs
  in g varInputs

revEvalArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => AstArtifactRev x z
  -> Rep ORArray x
  -> Maybe (Rep ORArray (ADTensorKind z))
  -> (Rep ORArray (ADTensorKind x), Rep ORArray z)
{-# INLINE revEvalArtifact #-}
revEvalArtifact AstArtifactRev{..} parameters mdt
 | Dict <- lemTensorKindOfAD (stensorKind @z) =
  let oneAtF = repConstant 1 $ aDTensorKind $ shapeAstFull artPrimalRev
      dt = fromMaybe oneAtF mdt
      env = extendEnv artVarDomainRev parameters emptyEnv
      envDt = extendEnv artVarDtRev dt env
      gradient = interpretAst envDt artDerivativeRev
      primal = interpretAst env artPrimalRev
  in (gradient, primal)


-- * Forward derivative adaptors

-- | The forward derivative operation takes the sensitivity parameter
-- (the incoming tangent). It also permits an aribtrary (nested tuple+)
-- type of not only the domain but also the codomain of the function
-- to be differentiated.
--
-- Warning: this fails often with ranked tensor due to inability
-- to determine the tensor shapes, see test testBarReluMax3Fwd.
-- Shaped tensors work fine. Similarly, the complex codomain resolution
-- may fail at runtime if it contains lists or vectors of tensors, etc.
fwd
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), TensorKind (X astvals)
     , TensorKind z
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => (astvals -> Rep (AstRanked FullSpan) z)
  -> Value astvals
  -> Value astvals  -- morally (ADTensorKind astvals)
  -> Rep ORArray (ADTensorKind z)
fwd f vals ds =
  let g :: Rep (AstRanked FullSpan) (X astvals) -> Rep (AstRanked FullSpan) z
      g !hv = tlet hv $ \ !hvShared ->
        f $ parseHVector (fromValue vals) (repDeepDuplicable stensorKind hvShared)
      valsH = toHVectorOf vals
      voidH = tshapeFull stensorKind valsH
      artifact = fst $ fwdProduceArtifact g emptyEnv voidH
      dsH = toHVectorOf ds
  in fst $ fwdEvalArtifact @_ @z artifact valsH
         $ toADTensorKindShared stensorKind dsH

fwdEvalArtifact
  :: forall x z. TensorKind x
  => AstArtifactFwd x z
  -> Rep ORArray x
  -> Rep ORArray (ADTensorKind x)
  -> (Rep ORArray (ADTensorKind z), Rep ORArray z)
{-# INLINE fwdEvalArtifact #-}
fwdEvalArtifact AstArtifactFwd{..} parameters ds
 | Dict <- lemTensorKindOfAD (stensorKind @x) =
  if aDTensorKind (tshapeFull (stensorKind @x) parameters)
     == tshapeFull (stensorKind @(ADTensorKind x)) ds then
    let env = extendEnv artVarDomainFwd parameters emptyEnv
        envD = extendEnv artVarDsFwd ds env
        derivative = interpretAst envD artDerivativeFwd
        primal = interpretAst env artPrimalFwd
    in (derivative, primal)
 else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shapes"


-- * Old gradient adaptors, with constant and fixed inputs and dt

-- The equality `RankedOf f ~ ORArray` is needed for type-checking
-- later on, even though GHC 9.6.4 reports it as redundant.
--
-- We are inlining these functions because they take function arguments
-- and are not too large. However, becausethey are called in many places,
-- we break the inline chain at crevOnHVector, to avoid exe blowup.
-- | The old versions that use the fixed input and @dt@ to compute gradient
-- only at these values, both transposing and evaluating at the same time.
--
-- These work for @f@ both ranked and shaped.
crev
  :: forall advals z.
     ( X advals ~ X (DValue advals), TensorKind (X advals), TensorKind z
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector ORArray (DValue advals)
     , DualNumberValue advals)
  => (advals -> Rep (ADVal ORArray) z)
  -> DValue advals
  -> DValue advals
{-# INLINE crev #-}
crev f vals = crevDtMaybe f vals Nothing

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall advals z.
     ( X advals ~ X (DValue advals), TensorKind (X advals), TensorKind z
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector ORArray (DValue advals)
     , DualNumberValue advals)
  => (advals -> Rep (ADVal ORArray) z)
  -> DValue advals
  -> Rep ORArray (ADTensorKind z)
  -> DValue advals
{-# INLINE crevDt #-}
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall advals z.
     ( X advals ~ X (DValue advals), TensorKind (X advals), TensorKind z
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector ORArray (DValue advals)
     , DualNumberValue advals)
  => (advals -> Rep (ADVal ORArray) z)
  -> DValue advals
  -> Maybe (Rep ORArray (ADTensorKind z))
  -> DValue advals  -- morally (ADTensorKind advals)
{-# INLINE crevDtMaybe #-}
crevDtMaybe f vals mdt | Dict <- lemTensorKindOfAD (stensorKind @(X advals)) =
  let g :: Rep (ADVal ORArray) (X advals) -> Rep (ADVal ORArray) z
      g = f . parseHVector (fromDValue vals) . repDeepDuplicable stensorKind
        -- repDeepDuplicable requires its argument to be deeply duplicable and
        -- crevOnHVector satisfies that via makeADInputs
      valsH = toHVectorOf vals
  in parseHVectorAD vals $ repDeepDuplicable stensorKind
     $ fst $ crevOnHVector mdt g valsH
       -- repDeepDuplicable requires its argument to be deeply duplicable and
       -- crevOnHVector satisfies that via gradientFromDelta

{-# SPECIALIZE crevOnHVector
  :: Maybe (Rep ORArray TKUntyped)
  -> (Rep (ADVal ORArray) TKUntyped
      -> Rep (ADVal ORArray) TKUntyped)
  -> Rep ORArray TKUntyped
  -> (Rep ORArray TKUntyped, Rep ORArray TKUntyped) #-}


-- * Old derivative adaptors, with constant and fixed inputs

-- | This takes the sensitivity parameter, by convention.
cfwd
  :: forall advals z.
     ( X advals ~ X (DValue advals), TensorKind (X advals), TensorKind z
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector ORArray (DValue advals)
     , DualNumberValue advals )
  => (advals -> Rep (ADVal ORArray) z)
  -> DValue advals
  -> DValue advals  -- morally (ADTensorKind advals)
  -> Rep ORArray (ADTensorKind z)
cfwd f vals ds =
  let g :: Rep (ADVal ORArray) (X advals) -> Rep (ADVal ORArray) z
      g = f . parseHVector (fromDValue vals) . repDeepDuplicable stensorKind
        -- repDeepDuplicable requires its argument to be deeply duplicable and
        -- cfwdOnHVector satisfies that via makeADInputs
        -- TODO: or use tlet as above?
      valsH = toHVectorOf vals
      dsH = toHVectorOf ds
  in fst $ cfwdOnHVector valsH g $ toADTensorKindShared stensorKind dsH





-- These and all other SPECIALIZE pragmas are needed due to the already
-- mostly fixed issues #21286 and others, even just to compare
-- the output with the and without.
-- We need pragmas on shaped operations even for ranked benchmarks,
-- because threading the dictionaries through mutual recursive functions
-- would cause trouble.

{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet PrimalSpan (TKR r n)
  -> ORArray r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR r n)
  -> AstRaw PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv ORArray
  -> AstTensor AstMethodLet PrimalSpan (TKR r n)
  -> ORArray r n #-}

{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (KnownShS sh, Typeable r)
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet PrimalSpan (TKS r sh)
  -> OSArray r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (KnownShS sh, Typeable r)
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKS r sh)
  -> AstRawS PrimalSpan r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (KnownShS sh, Typeable r)
  => AstEnv ORArray
  -> AstTensor AstMethodLet PrimalSpan (TKS r sh)
  -> OSArray r sh #-}

{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet PrimalSpan (TKR r n)
  -> ORArray r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet PrimalSpan (TKR Double n)
  -> ORArray Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet PrimalSpan (TKR Float n)
  -> ORArray Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet PrimalSpan (TKR Int64 n)
  -> ORArray Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR r n)
  -> AstRaw PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR Double n)
  -> AstRaw PrimalSpan Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR Float n)
  -> AstRaw PrimalSpan Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR Int64 n)
  -> AstRaw PrimalSpan Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv ORArray
  -> AstTensor AstMethodLet PrimalSpan (TKR r n)
  -> ORArray r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor AstMethodLet PrimalSpan (TKR Double n)
  -> ORArray Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor AstMethodLet PrimalSpan (TKR Float n)
  -> ORArray Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor AstMethodLet PrimalSpan (TKR Int64 n)
  -> ORArray Int64 n #-}

{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet DualSpan (TKR r n)
  -> Delta ORArray (TKR r n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet DualSpan (TKR Double n)
  -> Delta ORArray (TKR Double n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet DualSpan (TKR Float n)
  -> Delta ORArray (TKR Float n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet DualSpan (TKR Int64 n)
  -> Delta ORArray (TKR Int64 n) #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan (TKR r n)
  -> Delta (AstRaw PrimalSpan) (TKR r n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan (TKR Double n)
  -> Delta (AstRaw PrimalSpan) (TKR Double n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan (TKR Float n)
  -> Delta (AstRaw PrimalSpan) (TKR Float n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan (TKR Int64 n)
  -> Delta (AstRaw PrimalSpan) (TKR Int64 n) #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv ORArray
  -> AstTensor AstMethodLet DualSpan (TKR r n)
  -> DummyDualTarget (TKR r n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor AstMethodLet DualSpan (TKR Double n)
  -> DummyDualTarget (TKR Double n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor AstMethodLet DualSpan (TKR Float n)
  -> DummyDualTarget (TKR Float n) #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor AstMethodLet DualSpan (TKR Int64 n)
  -> DummyDualTarget (TKR Int64 n) #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKR r n)
  -> ADVal ORArray r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR r n)
  -> ADVal (AstRaw PrimalSpan) r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKR r n)
  -> ORArray r n #-}

{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKS r sh)
  -> ADVal OSArray r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS r sh)
  -> ADVal (AstRawS PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKS r sh)
  -> OSArray r sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKR r n)
  -> ADVal ORArray r n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKR Double n)
  -> ADVal ORArray Double n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKR Float n)
  -> ADVal ORArray Float n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKR Int64 n)
  -> ADVal ORArray Int64 n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR r n)
  -> ADVal (AstRaw PrimalSpan) r n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR Double n)
  -> ADVal (AstRaw PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR Float n)
  -> ADVal (AstRaw PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR Int64 n)
  -> ADVal (AstRaw PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKR r n)
  -> ORArray r n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKR Double n)
  -> ORArray Double n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKR Float n)
  -> ORArray Float n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKR Int64 n)
  -> ORArray Int64 n #-}

{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKS r sh)
  -> ADVal OSArray r sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKS Double sh)
  -> ADVal OSArray Double sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKS Float sh)
  -> ADVal OSArray Float sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s (TKS Int64 sh)
  -> ADVal OSArray Int64 sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS r sh)
  -> ADVal (AstRawS PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS Double sh)
  -> ADVal (AstRawS PrimalSpan) Double sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS Float sh)
  -> ADVal (AstRawS PrimalSpan) Float sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS Int64 sh)
  -> ADVal (AstRawS PrimalSpan) Int64 sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKS r sh)
  -> OSArray r sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKS Double sh)
  -> OSArray Double sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKS Float sh)
  -> OSArray Float sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s (TKS Int64 sh)
  -> OSArray Int64 sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor AstMethodLet s TKUntyped
  -> HVectorPseudoTensor (ADVal ORArray) Float '() #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s TKUntyped
  -> HVectorPseudoTensor (ADVal (AstRaw PrimalSpan)) Float '() #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s TKUntyped
  -> HVectorPseudoTensor ORArray Float '() #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor AstMethodLet s TKUntyped
  -> HVectorPseudoTensor ORArray Float '() #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal ORArray)
  -> AstBool AstMethodLet
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstBool AstMethodLet
  -> AstBool AstMethodShare #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv ORArray
  -> AstBool AstMethodLet
  -> Bool #-}
