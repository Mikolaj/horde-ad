{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and (forward) derivative
-- calculation for an objective function on values of complicated
-- types (e.g., with tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.Ops", this forms the basic
-- high-level API of the horde-ad library. Optimizers are add-ons.
module HordeAd.ADEngine
  ( -- * Reverse derivative adaptors
    IncomingCotangentHandling(..)
  , rev, revDt, revArtifactAdapt, revArtifactDelta
  , revProduceArtifactWithoutInterpretation, revEvalArtifact
    -- * Forward derivative adaptors
  , fwd, fwdEvalArtifact
    -- * Non-AST gradient adaptors
  , crev, crevDt
    -- * Non-AST derivative adaptors
  , cfwd, cfwdBoth
  ) where

import Prelude

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstInterpret
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersAst
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.DeltaEval
import HordeAd.Core.Ops
import HordeAd.Core.OpsADVal
import HordeAd.Core.OpsAst
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- An orphan needed to tweak dependencies to specialize better.
instance KnownSTK y
         => TermValue (AstTensor AstMethodLet FullSpan y) where
  type Value (AstTensor AstMethodLet FullSpan y) = Concrete y
  fromValue t = tconcrete (tftkG (knownSTK @y) $ unConcrete t) t


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
     , AdaptableTarget Concrete (Value astvals) )
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
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> Concrete (ADTensorKind z)
  -> Value astvals
{-# INLINE revDt #-}
revDt f vals dt = revDtMaybe f vals (Just dt)

revDtMaybe
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> Maybe (Concrete (ADTensorKind z))
  -> Value astvals  -- morally Value (ADTensorKind astvals)
{-# INLINE revDtMaybe #-}
revDtMaybe f vals0 mdt =
  let valsTarget = toTarget vals0
      xftk = tftkG (knownSTK @(X astvals)) $ unConcrete valsTarget
      cotangentHandling =
        maybe (IgnoreIncomingCotangent) (const UseIncomingCotangent) mdt
      artifact = revArtifactAdapt cotangentHandling f xftk
  in fromTarget $ fromADTensorKindShared (ftkToSTK xftk)
     $ fst $ revEvalArtifact artifact valsTarget mdt

revArtifactAdapt
  :: forall astvals z. AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
  => IncomingCotangentHandling
  -> (astvals -> AstTensor AstMethodLet FullSpan z)
  -> FullShapeTK (X astvals)
  -> AstArtifactRev (X astvals) z
{-# INLINE revArtifactAdapt #-}
revArtifactAdapt cotangentHandling f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X astvals)
        -> AstTensor AstMethodLet FullSpan z
      g !arg = ttlet arg $ f . fromTarget  -- fromTarget requires duplicable
  in revProduceArtifact cotangentHandling g emptyEnv xftk

-- For tests only.
revArtifactDelta
  :: forall astvals z. AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
  => IncomingCotangentHandling
  -> (astvals -> AstTensor AstMethodLet FullSpan z)
  -> FullShapeTK (X astvals)
  -> (AstArtifactRev (X astvals) z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revArtifactDelta #-}
revArtifactDelta cotangentHandling f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X astvals)
        -> AstTensor AstMethodLet FullSpan z
      g !arg = ttlet arg $ f . fromTarget
  in revArtifactFromForwardPass cotangentHandling
                                (forwardPassByInterpretation g emptyEnv) xftk

revProduceArtifactWithoutInterpretation
  :: forall x z.
     IncomingCotangentHandling
  -> (ADVal (AstRaw PrimalSpan) x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullShapeTK x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifactWithoutInterpretation #-}
revProduceArtifactWithoutInterpretation cotangentHandling f xftk =
  revArtifactFromForwardPass cotangentHandling
                             (forwardPassByApplication f) xftk

forwardPassByApplication
  :: forall x z.
     (ADVal (AstRaw PrimalSpan) x
      -> ADVal (AstRaw PrimalSpan) z)
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw PrimalSpan) z
{-# INLINE forwardPassByApplication #-}
forwardPassByApplication g hVectorPrimal var _hVector =
  let deltaInputs = generateDeltaInputs $ varNameToFTK var
      varInputs = dDnotShared (AstRaw hVectorPrimal) deltaInputs
  in g varInputs

revEvalArtifact
  :: forall x z.
     AstArtifactRev x z
  -> Concrete x
  -> Maybe (Concrete (ADTensorKind z))
  -> (Concrete (ADTensorKind x), Concrete z)
{-# INLINE revEvalArtifact #-}
revEvalArtifact AstArtifactRev{..} parameters mdt =
  let azstk = varNameToFTK artVarDtRev
      env = extendEnv artVarDomainRev parameters emptyEnv
      envDt = case mdt of
        Nothing ->
          let oneAtF = treplTarget 1 azstk
          in extendEnv artVarDtRev oneAtF env
        Just dt ->
          if tftkG (ftkToSTK azstk) (unConcrete dt) == azstk
          then extendEnv artVarDtRev dt env
          else error "revEvalArtifact: reverse derivative incoming cotangent should have the same shape as the codomain of the objective function"
      gradient = interpretAstPrimal envDt artDerivativeRev
      primal = interpretAstPrimal env artPrimalRev
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
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> Value astvals  -- morally (ADTensorKind astvals)
  -> Concrete (ADTensorKind z)
{-# INLINE fwd #-}
fwd f vals ds =
  let g :: AstTensor AstMethodLet FullSpan (X astvals)
        -> AstTensor AstMethodLet FullSpan z
      g !arg = ttlet arg $ f . fromTarget
      valsTarget = toTarget vals
      xftk = tftkG (knownSTK @(X astvals)) $ unConcrete valsTarget
      artifact = fst $ fwdProduceArtifact g emptyEnv xftk
      dsTarget = toTarget ds
  in fst $ fwdEvalArtifact @_ @z artifact valsTarget
         $ toADTensorKindShared xftk dsTarget

fwdEvalArtifact
  :: forall x z. KnownSTK x
  => AstArtifactFwd x z
  -> Concrete x
  -> Concrete (ADTensorKind x)
  -> (Concrete (ADTensorKind z), Concrete z)
{-# INLINE fwdEvalArtifact #-}
fwdEvalArtifact AstArtifactFwd{..} parameters ds =
  let xstk = knownSTK @x
      axstk = adSTK xstk
  in if adFTK (tftkG xstk (unConcrete parameters)) == tftkG axstk (unConcrete ds)
     then let env = extendEnv artVarDomainFwd parameters emptyEnv
              envD = extendEnv artVarDsFwd ds env
              derivative = interpretAstPrimal envD artDerivativeFwd
              primal = interpretAstPrimal env artPrimalFwd
          in (derivative, primal)
     else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shape"


-- * Non-AST gradient adaptors, with constant and fixed inputs and dt

-- We are inlining these functions because they take function arguments
-- and are not too large. However, becausethey are called in many places,
-- we break the inline chain at crevOnHVector, to avoid exe blowup.
-- | The old versions that use the fixed input and @dt@ to compute gradient
-- only at these values, both transposing and evaluating at the same time.
--
-- These work for @f@ both ranked and shaped.
crev
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete z)
  -> DValue advals
  -> DValue advals
{-# INLINE crev #-}
crev f vals = crevDtMaybe f vals Nothing

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete z)
  -> DValue advals
  -> Concrete (ADTensorKind z)
  -> DValue advals
{-# INLINE crevDt #-}
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete z)
  -> DValue advals
  -> Maybe (Concrete (ADTensorKind z))
  -> DValue advals  -- morally DValue (ADTensorKind advals)
{-# INLINE crevDtMaybe #-}
crevDtMaybe f vals mdt =
  let g :: ADVal Concrete (X advals) -> ADVal Concrete z
      g = f . fromTarget
      xftk = tftkG (knownSTK @(X advals)) $ unConcrete valsTarget
      valsTarget = toTarget vals
  in fromTarget $ fromADTensorKindShared (ftkToSTK xftk)
     $ fst $ crevOnHVector mdt g xftk valsTarget


-- * Non-AST derivative adaptors, with constant and fixed inputs

-- | This takes the sensitivity parameter, by convention.
cfwd
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete z)
  -> DValue advals
  -> DValue advals  -- morally (ADTensorKind advals)
  -> Concrete (ADTensorKind z)
{-# INLINE cfwd #-}
cfwd f vals ds = fst $ cfwdBoth f vals ds

cfwdBoth
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete z)
  -> DValue advals
  -> DValue advals  -- morally (ADTensorKind advals)
  -> (Concrete (ADTensorKind z), Concrete z)
{-# INLINE cfwdBoth #-}
cfwdBoth f vals ds =
  let xftk = tftkG (knownSTK @(X advals)) $ unConcrete valsTarget
      valsTarget = toTarget vals
      g :: ADVal Concrete (X advals) -> ADVal Concrete z
      g = f . fromTarget
      dsTarget = toTarget ds
  in cfwdOnHVector xftk valsTarget g
     $ toADTensorKindShared xftk dsTarget





-- This specialization is not possible where the functions are defined,
-- due to dependency cycles, but it's possible here:
{-# SPECIALIZE gradientFromDelta :: FullShapeTK x -> FullShapeTK z -> Concrete (ADTensorKind z) -> Delta Concrete z -> Concrete (ADTensorKind x) #-}
{-# SPECIALIZE evalRev :: FullShapeTK y -> EvalState Concrete -> Concrete (ADTensorKind y) -> Delta Concrete y -> EvalState Concrete #-}
{-# SPECIALIZE evalRevFTK :: EvalState Concrete -> Concrete (ADTensorKind y) -> Delta Concrete y -> EvalState Concrete #-}
-- RULE left-hand side too complicated to desugar:
-- {-# SPECIALIZE evalRevSame :: y ~ ADTensorKind y => EvalState Concrete -> Concrete (ADTensorKind y) -> Delta Concrete y -> EvalState Concrete #-}
{-# SPECIALIZE evalRevFromnMap :: EvalState Concrete -> EvalState Concrete #-}

{-# SPECIALIZE evalRevSame :: EvalState Concrete -> Concrete (TKScalar Double) -> Delta Concrete (TKScalar Double) -> EvalState Concrete #-}
{-# SPECIALIZE evalRevSame :: EvalState Concrete -> Concrete (TKScalar Float) -> Delta Concrete (TKScalar Float) -> EvalState Concrete #-}
{-# SPECIALIZE evalRevSame :: EvalState Concrete -> Concrete (TKR n Double) -> Delta Concrete (TKR n Double) -> EvalState Concrete #-}
{-# SPECIALIZE evalRevSame :: EvalState Concrete -> Concrete (TKR n Float) -> Delta Concrete (TKR n Float) -> EvalState Concrete #-}
{-# SPECIALIZE evalRevSame :: EvalState Concrete -> Concrete (TKS sh Double) -> Delta Concrete (TKS sh Double) -> EvalState Concrete #-}
{-# SPECIALIZE evalRevSame :: EvalState Concrete -> Concrete (TKS sh Float) -> Delta Concrete (TKS sh Float) -> EvalState Concrete #-}
{-# SPECIALIZE evalRevSame :: EvalState Concrete -> Concrete (TKX sh Double) -> Delta Concrete (TKX sh Double) -> EvalState Concrete #-}
{-# SPECIALIZE evalRevSame :: EvalState Concrete -> Concrete (TKX sh Float) -> Delta Concrete (TKX sh Float) -> EvalState Concrete #-}


-- These and all other SPECIALIZE pragmas are needed due to the already
-- mostly fixed issues #21286 and others, even just to compare
-- the output with them and without.
-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: AstEnv (ADVal Concrete)
  -> AstTensor AstMethodLet PrimalSpan y
  -> ADVal Concrete y #-}
{-# SPECIALIZE interpretAst
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan y
  -> ADVal (AstRaw PrimalSpan) y #-}
{-# SPECIALIZE interpretAst
  :: AstEnv Concrete
  -> AstTensor AstMethodLet PrimalSpan y
  -> Concrete y #-}
{-# SPECIALIZE interpretAst
  :: AstEnv (ADVal Concrete)
  -> AstTensor AstMethodLet DualSpan y
  -> ADVal Concrete y #-}
{-# SPECIALIZE interpretAst
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet DualSpan y
  -> ADVal (AstRaw PrimalSpan) y #-}
{-# SPECIALIZE interpretAst
  :: AstEnv Concrete
  -> AstTensor AstMethodLet DualSpan y
  -> Concrete y #-}
{-# SPECIALIZE interpretAst
  :: AstEnv (ADVal Concrete)
  -> AstTensor AstMethodLet FullSpan y
  -> ADVal Concrete y #-}
{-# SPECIALIZE interpretAst
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet FullSpan y
  -> ADVal (AstRaw PrimalSpan) y #-}
{-# SPECIALIZE interpretAst
  :: AstEnv Concrete
  -> AstTensor AstMethodLet FullSpan y
  -> Concrete y #-}

{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal Concrete)
  -> AstTensor AstMethodLet PrimalSpan y
  -> Concrete y #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodLet PrimalSpan y
  -> AstRaw PrimalSpan y #-}
{-# SPECIALIZE interpretAstPrimal
  :: AstEnv Concrete
  -> AstTensor AstMethodLet PrimalSpan y
  -> Concrete y #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal Concrete)
  -> AstBool AstMethodLet
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstBool AstMethodLet
  -> AstBool AstMethodShare #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv Concrete
  -> AstBool AstMethodLet
  -> Bool #-}
