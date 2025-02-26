{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and (forward) derivative
-- calculation for an objective function on values of complicated
-- types (e.g., with tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.Ops", this forms the basic
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
  , cfwd, cfwdBoth
  ) where

import Prelude

import Data.Int (Int64)
import Data.Maybe (isJust)
import Type.Reflection (Typeable)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersAst
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.Ops
import HordeAd.Core.OpsADVal
import HordeAd.Core.OpsAst
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

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
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget RepN (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
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
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget RepN (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> RepN (ADTensorKind z)
  -> Value astvals
{-# INLINE revDt #-}
revDt f vals dt = revDtMaybe f vals (Just dt)

revDtMaybe
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget RepN (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> Maybe (RepN (ADTensorKind z))
  -> Value astvals  -- morally Value (ADTensorKind astvals)
{-# INLINE revDtMaybe #-}
revDtMaybe f vals0 mdt =
  let g :: AstTensor AstMethodLet FullSpan (X astvals)
        -> AstTensor AstMethodLet FullSpan z
      g !hv = tlet hv $ \ !hvShared ->
        f $ fromTarget hvShared
      valsTarget = toTarget vals0
      xftk = tftk (knownSTK @(X astvals)) valsTarget
      artifact = fst $ revProduceArtifact (isJust mdt) g emptyEnv xftk
  in fromTarget $ fromADTensorKindShared (ftkToSTK xftk)
     $ fst $ revEvalArtifact artifact valsTarget mdt
{- TODO
{-# SPECIALIZE revDtMaybe
  :: ( KnownNat n
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget RepN (Value astvals)
     , TermValue astvals )
  => (astvals -> AstTensor AstMethodLet FullSpan n Double)
  -> Value astvals
  -> Maybe (RepN (TKR n Double))
  -> Value astvals #-}
-}

revArtifactAdapt
  :: forall astvals z. AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
  => Bool
  -> (astvals -> AstTensor AstMethodLet FullSpan z)
  -> FullTensorKind (X astvals)
  -> (AstArtifactRev (X astvals) z, Delta (AstRaw PrimalSpan) z )
revArtifactAdapt hasDt f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X astvals)
        -> AstTensor AstMethodLet FullSpan z
      g !hv = tlet hv $ \ !hvShared ->
        f $ fromTarget hvShared
  in revProduceArtifact hasDt g emptyEnv xftk
{- TODO
{-# SPECIALIZE revArtifactAdapt
  :: ( KnownNat n
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget RepN (Value astvals)
     , TermValue astvals )
  => Bool -> (astvals -> AstTensor AstMethodLet FullSpan n Double) -> FullTensorKind (X astvals)
  -> (AstArtifactRev TKUntyped (TKR n Double), Delta (AstRaw PrimalSpan) (TKR n Double)) #-}
-}

revProduceArtifactWithoutInterpretation
  :: forall x z.
     Bool
  -> (ADVal (AstRaw PrimalSpan) x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullTensorKind x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifactWithoutInterpretation #-}
revProduceArtifactWithoutInterpretation hasDt f xftk =
  revArtifactFromForwardPass @x @z hasDt (forwardPassByApplication f xftk) xftk

forwardPassByApplication
  :: forall x z.
     (ADVal (AstRaw PrimalSpan) x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullTensorKind x
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw PrimalSpan) z
{-# INLINE forwardPassByApplication #-}
forwardPassByApplication g xftk hVectorPrimal _var _hVector =
  let deltaInputs = generateDeltaInputs xftk
      varInputs = dDnotShared (AstRaw hVectorPrimal) deltaInputs
  in g varInputs

revEvalArtifact
  :: forall x z.
     AstArtifactRev x z
  -> RepN x
  -> Maybe (RepN (ADTensorKind z))
  -> (RepN (ADTensorKind x), RepN z)
{-# INLINE revEvalArtifact #-}
revEvalArtifact AstArtifactRev{..} parameters mdt =
  let env = extendEnv artVarDomainRev parameters emptyEnv
      envDt = case mdt of
        Nothing ->
          let oneAtF = constantTarget 1 $ adFTK $ ftkAst artPrimalRev
          in extendEnv artVarDtRev oneAtF env
        Just dt ->
          extendEnv artVarDtRev dt env
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
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget RepN (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> Value astvals  -- morally (ADTensorKind astvals)
  -> RepN (ADTensorKind z)
fwd f vals ds =
  let g :: AstTensor AstMethodLet FullSpan (X astvals)
        -> AstTensor AstMethodLet FullSpan z
      g !hv = tlet hv $ \ !hvShared ->
        f $ fromTarget hvShared
      valsTarget = toTarget vals
      xftk = tftk (knownSTK @(X astvals)) valsTarget
      artifact = fst $ fwdProduceArtifact g emptyEnv xftk
      dsTarget = toTarget ds
  in fst $ fwdEvalArtifact @_ @z artifact valsTarget
         $ toADTensorKindShared xftk dsTarget

fwdEvalArtifact
  :: forall x z. KnownSTK x
  => AstArtifactFwd x z
  -> RepN x
  -> RepN (ADTensorKind x)
  -> (RepN (ADTensorKind z), RepN z)
{-# INLINE fwdEvalArtifact #-}
fwdEvalArtifact AstArtifactFwd{..} parameters ds =
  let xstk = knownSTK @x
      astk = adSTK xstk
  in if adFTK (tftk xstk parameters) == tftk astk ds then
       let env = extendEnv artVarDomainFwd parameters emptyEnv
           envD = extendEnv artVarDsFwd ds env
           derivative = interpretAst envD artDerivativeFwd
           primal = interpretAst env artPrimalFwd
       in (derivative, primal)
     else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shape"


-- * Old gradient adaptors, with constant and fixed inputs and dt

-- We are inlining these functions because they take function arguments
-- and are not too large. However, becausethey are called in many places,
-- we break the inline chain at crevOnHVector, to avoid exe blowup.
-- | The old versions that use the fixed input and @dt@ to compute gradient
-- only at these values, both transposing and evaluating at the same time.
--
-- These work for @f@ both ranked and shaped.
crev
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals), KnownSTK z
     , AdaptableTarget (ADVal RepN) advals
     , AdaptableTarget RepN (DValue advals) )
  => (advals -> ADVal RepN z)
  -> DValue advals
  -> DValue advals
{-# INLINE crev #-}
crev f vals = crevDtEither f vals (Left (knownSTK @z))

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal RepN) advals
     , AdaptableTarget RepN (DValue advals) )
  => (advals -> ADVal RepN z)
  -> DValue advals
  -> RepN (ADTensorKind z)
  -> DValue advals
{-# INLINE crevDt #-}
crevDt f vals dt = crevDtEither f vals (Right dt)

crevDtEither
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal RepN) advals
     , AdaptableTarget RepN (DValue advals) )
  => (advals -> ADVal RepN z)
  -> DValue advals
  -> Either (STensorKind z) (RepN (ADTensorKind z))
  -> DValue advals  -- morally DValue (ADTensorKind advals)
{-# INLINE crevDtEither #-}
crevDtEither f vals edt =
  let g :: ADVal RepN (X advals) -> ADVal RepN z
      g = f . fromTarget
      xftk = tftk (knownSTK @(X advals)) valsTarget
      valsTarget = toTarget vals
  in fromTarget $ fromADTensorKindShared (ftkToSTK xftk)
     $ fst $ crevOnHVector edt g xftk valsTarget

{-
{-# SPECIALIZE crevOnHVector
  :: Either (RepN TKUntyped)
  -> (ADVal RepN TKUntyped
      -> ADVal RepN TKUntyped)
  -> RepN TKUntyped
  -> (RepN TKUntyped, RepN TKUntyped) #-}
-}

-- * Old derivative adaptors, with constant and fixed inputs

-- | This takes the sensitivity parameter, by convention.
cfwd
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal RepN) advals
     , AdaptableTarget RepN (DValue advals) )
  => (advals -> ADVal RepN z)
  -> DValue advals
  -> DValue advals  -- morally (ADTensorKind advals)
  -> RepN (ADTensorKind z)
cfwd f vals ds = fst $ cfwdBoth f vals ds

cfwdBoth
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal RepN) advals
     , AdaptableTarget RepN (DValue advals) )
  => (advals -> ADVal RepN z)
  -> DValue advals
  -> DValue advals  -- morally (ADTensorKind advals)
  -> (RepN (ADTensorKind z), RepN z)
cfwdBoth f vals ds =
  let xftk = tftk (knownSTK @(X advals)) valsTarget
      valsTarget = toTarget vals
      g :: ADVal RepN (X advals) -> ADVal RepN z
      g = f . fromTarget
      dsTarget = toTarget ds
  in cfwdOnHVector xftk valsTarget g
     $ toADTensorKindShared xftk dsTarget




-- These and all other SPECIALIZE pragmas are needed due to the already
-- mostly fixed issues #21286 and others, even just to compare
-- the output with the and without.
-- We need pragmas on shaped operations even for ranked benchmarks,
-- because threading the dictionaries through mutual recursive functions
-- would cause trouble.

{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: Typeable r
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet PrimalSpan (TKR n r)
  -> RepN (TKR n r) #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: Typeable r
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR n r)
  -> AstRaw PrimalSpan (TKR n r) #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: Typeable r
  => AstEnv RepN
  -> AstTensor AstMethodLet PrimalSpan (TKR n r)
  -> RepN (TKR n r) #-}

{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: Typeable r
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet PrimalSpan (TKS sh r)
  -> RepN (TKS sh r) #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: Typeable r
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKS sh r)
  -> AstRaw PrimalSpan (TKS sh r) #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: Typeable r
  => AstEnv RepN
  -> AstTensor AstMethodLet PrimalSpan (TKS sh r)
  -> RepN (TKS sh r) #-}

{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet PrimalSpan (TKR n r)
  -> RepN (TKR n r) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet PrimalSpan (TKR n Double)
  -> RepN (TKR n Double) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet PrimalSpan (TKR n Float)
  -> RepN (TKR n Float) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet PrimalSpan (TKR n Int64)
  -> RepN (TKR n Int64) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR n r)
  -> AstRaw PrimalSpan (TKR n r) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR n Double)
  -> AstRaw PrimalSpan (TKR n Double) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR n Float)
  -> AstRaw PrimalSpan (TKR n Float) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan (TKR n Int64)
  -> AstRaw PrimalSpan (TKR n Int64) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv RepN
  -> AstTensor AstMethodLet PrimalSpan (TKR n r)
  -> RepN (TKR n r) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv RepN
  -> AstTensor AstMethodLet PrimalSpan (TKR n Double)
  -> RepN (TKR n Double) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv RepN
  -> AstTensor AstMethodLet PrimalSpan (TKR n Float)
  -> RepN (TKR n Float) #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv RepN
  -> AstTensor AstMethodLet PrimalSpan (TKR n Int64)
  -> RepN (TKR n Int64) #-}

{-# SPECIALIZE interpretAstDual
  :: AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet DualSpan (TKR n r)
  -> Delta RepN (TKR n r) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet DualSpan (TKR n Double)
  -> Delta RepN (TKR n Double) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet DualSpan (TKR n Float)
  -> Delta RepN (TKR n Float) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet DualSpan (TKR n Int64)
  -> Delta RepN (TKR n Int64) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan (TKR n r)
  -> Delta (AstRaw PrimalSpan) (TKR n r) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan (TKR n Double)
  -> Delta (AstRaw PrimalSpan) (TKR n Double) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan (TKR n Float)
  -> Delta (AstRaw PrimalSpan) (TKR n Float) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan (TKR n Int64)
  -> Delta (AstRaw PrimalSpan) (TKR n Int64) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv RepN
  -> AstTensor AstMethodLet DualSpan (TKR n r)
  -> DummyDualTarget (TKR n r) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv RepN
  -> AstTensor AstMethodLet DualSpan (TKR n Double)
  -> DummyDualTarget (TKR n Double) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv RepN
  -> AstTensor AstMethodLet DualSpan (TKR n Float)
  -> DummyDualTarget (TKR n Float) #-}
{-# SPECIALIZE interpretAstDual
  :: AstEnv RepN
  -> AstTensor AstMethodLet DualSpan (TKR n Int64)
  -> DummyDualTarget (TKR n Int64) #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKR n r)
  -> ADVal RepN (TKR n r) #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR n r)
  -> ADVal (AstRaw PrimalSpan) (TKR n r) #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKR n r)
  -> RepN (TKR n r) #-}

{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKS sh r)
  -> ADVal RepN (TKS sh r) #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS sh r)
  -> ADVal (AstRaw PrimalSpan) (TKS sh r) #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKS sh r)
  -> RepN (TKS sh r) #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKR n r)
  -> ADVal RepN (TKR n r) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKR n Double)
  -> ADVal RepN (TKR n Double) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKR n Float)
  -> ADVal RepN (TKR n Float) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKR n Int64)
  -> ADVal RepN (TKR n Int64) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR n r)
  -> ADVal (AstRaw PrimalSpan) (TKR n r) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR n Double)
  -> ADVal (AstRaw PrimalSpan) (TKR n Double) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR n Float)
  -> ADVal (AstRaw PrimalSpan) (TKR n Float) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKR n Int64)
  -> ADVal (AstRaw PrimalSpan) (TKR n Int64) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKR n r)
  -> RepN (TKR n r) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKR n Double)
  -> RepN (TKR n Double) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKR n Float)
  -> RepN (TKR n Float) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKR n Int64)
  -> RepN (TKR n Int64) #-}

{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKS sh r)
  -> ADVal RepN (TKS sh r) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKS sh Double)
  -> ADVal RepN (TKS sh Double) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKS sh Float)
  -> ADVal RepN (TKS sh Float) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s (TKS sh Int64)
  -> ADVal RepN (TKS sh Int64) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS sh r)
  -> ADVal (AstRaw PrimalSpan) (TKS sh r) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS sh Double)
  -> ADVal (AstRaw PrimalSpan) (TKS sh Double) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS sh Float)
  -> ADVal (AstRaw PrimalSpan) (TKS sh Float) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s (TKS sh Int64)
  -> ADVal (AstRaw PrimalSpan) (TKS sh Int64) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKS sh r)
  -> RepN (TKS sh r) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKS sh Double)
  -> RepN (TKS sh Double) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKS sh Float)
  -> RepN (TKS sh Float) #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s (TKS sh Int64)
  -> RepN (TKS sh Int64) #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal RepN)
  -> AstTensor AstMethodLet s TKUntyped
  -> ADVal RepN TKUntyped #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet s TKUntyped
  -> ADVal (AstRaw PrimalSpan) TKUntyped #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv RepN
  -> AstTensor AstMethodLet s TKUntyped
  -> RepN TKUntyped #-}
-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal RepN)
  -> AstBool AstMethodLet
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstBool AstMethodLet
  -> AstBool AstMethodShare #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv RepN
  -> AstBool AstMethodLet
  -> Bool #-}
