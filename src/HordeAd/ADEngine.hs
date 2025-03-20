{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and forward derivative
-- calculation for an objective function on values of complicated types,
-- e.g., nested tuples of tensors.
module HordeAd.ADEngine
  ( -- * Symbolic reverse derivative adaptors
    grad, vjp
  , gradArtifact, vjpArtifact
  , gradInterpretArtifact, vjpInterpretArtifact
    -- * Symbolic forward derivative adaptors
  , jvp, jvpArtifact, jvpInterpretArtifact
    -- * Non-symbolic reverse derivative adaptors
  , cgrad, cvjp
    -- * Non-symbolic forward derivative adaptors
  , cjvp
    -- * Internal machinery for symbolic adaptors
  , IncomingCotangentHandling(..)
  , revArtifactAdapt, revArtifactDelta
  , revProduceArtifactWithoutInterpretation, revInterpretArtifact
  , fwdArtifactAdapt, fwdArtifactDelta, fwdInterpretArtifact
    -- * Internal machinery for non-symbolic adaptors
  , cfwdBoth
  ) where

import Prelude

import HordeAd.AstEngine
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
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Symbolic reverse derivative adaptors

-- | This simplified version of the reverse derivative operation
-- sets the incoming cotangent @dt@ to be 1 and assumes the codomain
-- of the function to be differentiated is a scalar.
--
-- We don't enforce (e.g., by quantifcation) that the objective function
-- is closed, because we evaluate the result of the differentiation
-- down to concrete arrays and so there's no risk of confusion of cotangents
-- from different levels of differentiation if it's done multiple times.
-- For simplicity of the type signature, the resulting value is converted from
-- the type of concrete contangents to the type of concrete input parameters.
grad
  :: forall astvals r.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan (TKScalar r))
  -> Value astvals
  -> Value astvals  -- morally Value (ADTensorKind astvals)
{-# INLINE grad #-}
grad f vals = revMaybe f vals Nothing

-- | This version of the reverse derivative operation
-- explicitly takes the sensitivity parameter (the incoming cotangent).
-- It also permits an aribtrary (nested tuple+) type of the domain
-- and aribtrary (nested pair) tensor kind of the codomain
-- of the function to be differentiated. The downside of the generality
-- is that if the function doesn't have a type signature,
-- the type often has to be spelled in full to aid type reconstruction.
-- For simplicity of the type signature, the resulting value is converted from
-- the type of concrete contangents to the type of concrete input parameters.
vjp
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> Concrete (ADTensorKind z)
  -> Value astvals  -- morally Value (ADTensorKind astvals)
{-# INLINE vjp #-}
vjp f vals dt = revMaybe f vals (Just dt)

gradArtifact
  :: forall astvals r.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan (TKScalar r))
  -> Value astvals
  -> AstArtifactRev (X astvals) (TKScalar r)
{-# INLINE gradArtifact #-}
gradArtifact f vals0 =
  let xftk = tftkG (knownSTK @(X astvals)) $ unConcrete $ toTarget vals0
  in revArtifactAdapt IgnoreIncomingCotangent f xftk

vjpArtifact
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> AstArtifactRev (X astvals) z
{-# INLINE vjpArtifact #-}
vjpArtifact f vals0 =
  let xftk = tftkG (knownSTK @(X astvals)) $ unConcrete $ toTarget vals0
  in revArtifactAdapt UseIncomingCotangent f xftk

gradInterpretArtifact
  :: forall x r avals.
     (X avals ~ ADTensorKind x, AdaptableTarget Concrete avals)
  => AstArtifactRev x (TKScalar r)
  -> Concrete x
  -> avals
{-# INLINE gradInterpretArtifact #-}
gradInterpretArtifact AstArtifactRev{..} parameters =
  let xftk = varNameToFTK artVarDomainRev
      azftk = varNameToFTK artVarDtRev
                -- STKScalar @(ADTensorScalar r) or STKScalar @Z0
      oneAtF = treplTarget 1 azftk
      env = extendEnv artVarDtRev oneAtF
            $ extendEnv artVarDomainRev parameters emptyEnv
  in if tftkG (ftkToSTK xftk) (unConcrete parameters) == xftk
     then fromTarget $ interpretAstPrimal env artDerivativeRev
     else error "gradInterpretArtifact: reverse derivative parameters must have the same shape as the domain of the objective function"

vjpInterpretArtifact
  :: forall x z avals.
     (X avals ~ ADTensorKind x, AdaptableTarget Concrete avals)
  => AstArtifactRev x z
  -> Concrete x
  -> Concrete (ADTensorKind z)
  -> avals
{-# INLINE vjpInterpretArtifact #-}
vjpInterpretArtifact AstArtifactRev{..} parameters dt =
  let xftk = varNameToFTK artVarDomainRev
      azftk = varNameToFTK artVarDtRev
      env = extendEnv artVarDtRev dt
            $ extendEnv artVarDomainRev parameters emptyEnv
  in if tftkG (ftkToSTK xftk) (unConcrete parameters) == xftk
     then if tftkG (ftkToSTK azftk) (unConcrete dt) == azftk
          then fromTarget $ interpretAstPrimal env artDerivativeRev
          else error "vjpInterpretArtifact: reverse derivative incoming cotangent must have the same shape as the codomain of the objective function"
     else error "vjpInterpretArtifact: reverse derivative parameters must have the same shape as the domain of the objective function"


-- * Symbolic reverse derivative adaptors' internal machinery

revMaybe
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> Maybe (Concrete (ADTensorKind z))
  -> Value astvals  -- morally Value (ADTensorKind astvals)
{-# INLINE revMaybe #-}
revMaybe f vals0 mdt =
  let valsTarget = toTarget vals0
      xftk = tftkG (knownSTK @(X astvals)) $ unConcrete valsTarget
      cotangentHandling =
        maybe (IgnoreIncomingCotangent) (const UseIncomingCotangent) mdt
      artifactRaw = revArtifactAdapt cotangentHandling f xftk
      artifact = simplifyArtifactGradient artifactRaw
  in fromTarget $ fromADTensorKindShared (ftkToSTK xftk)
     $ fst $ revInterpretArtifact artifact valsTarget mdt

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

revInterpretArtifact
  :: forall x z.
     AstArtifactRev x z
  -> Concrete x
  -> Maybe (Concrete (ADTensorKind z))
  -> (Concrete (ADTensorKind x), Concrete z)
{-# INLINE revInterpretArtifact #-}
revInterpretArtifact AstArtifactRev{..} parameters mdt =
  let azftk = varNameToFTK artVarDtRev
      env = extendEnv artVarDomainRev parameters emptyEnv
      envDt = case mdt of
        Nothing ->
          let oneAtF = treplTarget 1 azftk
          in extendEnv artVarDtRev oneAtF env
        Just dt ->
          if tftkG (ftkToSTK azftk) (unConcrete dt) == azftk
          then extendEnv artVarDtRev dt env
          else error "revInterpretArtifact: reverse derivative incoming cotangent must have the same shape as the codomain of the objective function"
      gradient = interpretAstPrimal envDt artDerivativeRev
      primal = interpretAstPrimal env artPrimalRev
  in (gradient, primal)


-- * Symbolic reverse derivative adaptors' testing-only internal machinery

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
  -> (ADVal (AstRaw PrimalSpan) x -> ADVal (AstRaw PrimalSpan) z)
  -> FullShapeTK x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifactWithoutInterpretation #-}
revProduceArtifactWithoutInterpretation cotangentHandling f xftk =
  revArtifactFromForwardPass cotangentHandling
                             (forwardPassByApplication f) xftk

forwardPassByApplication
  :: forall x z.
     (ADVal (AstRaw PrimalSpan) x -> ADVal (AstRaw PrimalSpan) z)
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw PrimalSpan) z
{-# INLINE forwardPassByApplication #-}
forwardPassByApplication g astVarPrimal var _astVar =
  let deltaInputs = generateDeltaInputs $ varNameToFTK var
      varInputs = dDnotShared (AstRaw astVarPrimal) deltaInputs
  in g varInputs


-- * Symbolic forward derivative adaptors

-- | The forward derivative operation takes the perturbation parameter
-- (the incoming tangent). It also permits an aribtrary (nested tuple+)
-- type of the domain and aribtrary (nested pair) tensor kind of the codomain
-- of the function to be differentiated. The generality sometimes makes it
-- necessary to suppy type hints when applying this operation.
jvp
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> Value astvals  -- morally (ADTensorKind astvals)
  -> Concrete (ADTensorKind z)
{-# INLINE jvp #-}
jvp f vals0 ds =
  let valsTarget = toTarget vals0
      xftk = tftkG (knownSTK @(X astvals)) $ unConcrete valsTarget
      artifactRaw = fwdArtifactAdapt f xftk
      artifact = simplifyArtifactDerivative artifactRaw
  in fst $ fwdInterpretArtifact artifact valsTarget
         $ toADTensorKindShared xftk (toTarget ds)
       -- the shapes of vals0 vs ds are checked in fwdInterpretArtifact

jvpArtifact
  :: forall astvals z.
     ( X astvals ~ X (Value astvals), KnownSTK (X astvals)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
     , AdaptableTarget Concrete (Value astvals) )
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> Value astvals
  -> AstArtifactFwd (X astvals) z
{-# INLINE jvpArtifact #-}
jvpArtifact f vals0 =
  let xftk = tftkG (knownSTK @(X astvals)) $ unConcrete $ toTarget vals0
  in fwdArtifactAdapt f xftk

jvpInterpretArtifact
  :: forall x z.
     AstArtifactFwd x z
  -> Concrete x
  -> Concrete (ADTensorKind x)
  -> Concrete (ADTensorKind z)
{-# INLINE jvpInterpretArtifact #-}
jvpInterpretArtifact art parameters = fst . fwdInterpretArtifact art parameters
  -- the shapes of parameters vs ds are checked in fwdInterpretArtifact


-- * Symbolic forward derivative adaptors' internal machinery

fwdArtifactAdapt
  :: forall astvals z. AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> FullShapeTK (X astvals)
  -> AstArtifactFwd (X astvals) z
{-# INLINE fwdArtifactAdapt #-}
fwdArtifactAdapt f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X astvals)
        -> AstTensor AstMethodLet FullSpan z
      g !arg = ttlet arg $ f . fromTarget  -- fromTarget requires duplicable
  in fwdProduceArtifact g emptyEnv xftk

fwdInterpretArtifact
  :: forall x z.
     AstArtifactFwd x z
  -> Concrete x
  -> Concrete (ADTensorKind x)
  -> (Concrete (ADTensorKind z), Concrete z)
{-# INLINE fwdInterpretArtifact #-}
fwdInterpretArtifact AstArtifactFwd{..} parameters ds =
  let xftk = varNameToFTK artVarDomainFwd
      xstk = ftkToSTK xftk
      env = extendEnv artVarDomainFwd parameters emptyEnv
      envD = extendEnv artVarDsFwd ds env
  in if tftkG xstk (unConcrete parameters) == xftk
     then if tftkG (adSTK xstk) (unConcrete ds) == adFTK xftk
          then let derivative = interpretAstPrimal envD artDerivativeFwd
                   primal = interpretAstPrimal env artPrimalFwd
               in (derivative, primal)
          else error "fwdInterpretArtifact: forward derivative perturbation must have the same shape as the domain of the objective function"
     else error "fwdInterpretArtifact: forward derivative input must have the same shape as the domain of the objective function"


-- * Symbolic forward derivative adaptors' testing-only internal machinery

fwdArtifactDelta
  :: forall astvals z. AdaptableTarget (AstTensor AstMethodLet FullSpan) astvals
  => (astvals -> AstTensor AstMethodLet FullSpan z)
  -> FullShapeTK (X astvals)
  -> (AstArtifactFwd (X astvals) z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdArtifactDelta #-}
fwdArtifactDelta f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X astvals)
        -> AstTensor AstMethodLet FullSpan z
      g !arg = ttlet arg $ f . fromTarget
  in fwdArtifactFromForwardPass (forwardPassByInterpretation g emptyEnv) xftk


-- * Non-symbolic reverse derivative adaptors

-- We are inlining these functions because they take function arguments
-- and are not too large. However, because they are called in many places,
-- we break the inline chain not far from the top, to avoid exe blowup.
-- | This simplified version of the concrete (non-symbolic)
-- reverse derivative operation sets the incoming cotangent @dt@ to be 1
-- and assumes the codomain of the function to be differentiated is a scalar.
cgrad
  :: forall advals r.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete (TKScalar r))
  -> DValue advals
  -> DValue advals  -- morally DValue (ADTensorKind advals)
{-# INLINE cgrad #-}
cgrad f vals = crevMaybe f vals Nothing

-- | This more general version of the concrete (non-symbolic)
-- reverse derivative operation additionally takes the sensitivity parameter
-- (the incoming cotangent).
cvjp
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete z)
  -> DValue advals
  -> Concrete (ADTensorKind z)
  -> DValue advals  -- morally DValue (ADTensorKind advals)
{-# INLINE cvjp #-}
cvjp f vals dt = crevMaybe f vals (Just dt)


-- * Non-symbolic reverse derivative adaptors' internal machinery

crevMaybe
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete z)
  -> DValue advals
  -> Maybe (Concrete (ADTensorKind z))
  -> DValue advals  -- morally DValue (ADTensorKind advals)
{-# INLINE crevMaybe #-}
crevMaybe f vals0 mdt =
  let valsTarget = toTarget vals0
      g :: ADVal Concrete (X advals) -> ADVal Concrete z
      g = f . fromTarget
      xftk = tftkG (knownSTK @(X advals)) $ unConcrete valsTarget
  in fromTarget $ fromADTensorKindShared (ftkToSTK xftk)
     $ fst $ crevOnParams mdt g xftk valsTarget


-- * Non-symbolic forward derivative adaptors

-- | This takes the perturbation parameter, by convention.
cjvp
  :: forall advals z.
     ( X advals ~ X (DValue advals), KnownSTK (X advals)
     , AdaptableTarget (ADVal Concrete) advals
     , AdaptableTarget Concrete (DValue advals) )
  => (advals -> ADVal Concrete z)
  -> DValue advals
  -> DValue advals  -- morally (ADTensorKind advals)
  -> Concrete (ADTensorKind z)
{-# INLINE cjvp #-}
cjvp f vals ds = fst $ cfwdBoth f vals ds


-- * Non-symbolic forward derivative adaptors' internal machinery

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
cfwdBoth f vals0 ds =
  let valsTarget = toTarget vals0
      xftk = tftkG (knownSTK @(X advals)) $ unConcrete valsTarget
      g :: ADVal Concrete (X advals) -> ADVal Concrete z
      g = f . fromTarget
      dsTarget = toTarget ds
  in if tftkG (ftkToSTK xftk) (unConcrete dsTarget) == xftk
     then cfwdOnParams xftk valsTarget g
          $ toADTensorKindShared xftk dsTarget
     else error "cfwdBoth: forward derivative input must have the same shape as the perturbation argument"





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
