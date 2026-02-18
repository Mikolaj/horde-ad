{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and forward derivative
-- calculation for an objective function on values of complicated types,
-- e.g., nested tuples of tensors.
--
-- The objective function can be defined as a sufficiently polymorphic
-- Haskell function that uses numeric classes as well as the multi-dimensional
-- tensor operation listed in "HordeAd.OpsTensor". To obtain symbolic
-- derivatives (derivative code that can be executed many times without
-- performing AD again), the user needs an objective function polymorphic
-- enough so that it can be instantiated to the 'HordeAd.Core.Ast.AstTensor'
-- type (nested in tuples, etc., for some extra flexibility).
-- For non-symbolic derivatives, the ability to instantiate to the
-- `HordeAd.Core.CarriersADVal.ADVal` type of dual numbers is enough.
-- See the classes these types are instances of to gauge the breadth
-- of the offered respective APIs.
module HordeAd.ADEngine
  ( -- * Symbolic reverse derivative adaptors
    grad, grad2, vjp, vjp2
  , gradArtifact, vjpArtifact
  , gradInterpretArtifact, vjpInterpretArtifact
    -- * Symbolic forward derivative adaptors
  , jvp, jvp2, jvpArtifact, jvpInterpretArtifact
    -- * Non-symbolic reverse derivative adaptors
  , cgrad, cgrad2, cvjp, cvjp2
    -- * Non-symbolic forward derivative adaptors
  , cjvp, cjvp2
    -- * Internal machinery for symbolic adaptors
  , IncomingCotangentHandling(..)
  , revArtifactAdapt, revArtifactAdaptDt, revArtifactDelta
  , revProduceArtifactWithoutInterpretation, revInterpretArtifact
  , fwdArtifactAdapt, fwdArtifactDelta, fwdInterpretArtifact
  ) where

import Prelude

import Data.Proxy (Proxy (Proxy))

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEngine
import HordeAd.Core.AstEnv
import HordeAd.Core.AstInterpret
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersAst
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.Ops
import HordeAd.Core.OpsADVal
import HordeAd.Core.OpsAst
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Symbolic reverse derivative adaptors

-- | This simplified version of the symbolic reverse derivative operation
-- sets the incoming cotangent @dt@ to be 1 and assumes the codomain
-- of the function to be differentiated is a scalar.
--
-- We don't enforce (e.g., by quantifcation) that the objective function
-- is closed, because we evaluate the result of the differentiation
-- down to concrete arrays and so there's no risk of "perturbation confusion"
-- between different levels of differentiation if it's done multiple times.
-- For simplicity of the type signature, the resulting value is converted from
-- the type of concrete contangents to the type of concrete input parameters.
grad
  :: forall src r tgt.
     ( GoodScalar r, X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan (TKScalar r) )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> Value src  -- morally Value (ADTensorKind src)
{-# INLINE grad #-}
grad f vals = snd $ grad2 f vals

-- | The @grad2@ operation works just as 'grad', but additionally produces
-- the primal result of the objective function at minimal extra cost.
grad2
  :: forall src r tgt.
     ( GoodScalar r, X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan (TKScalar r) )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> ( Concrete (TKScalar r)
     , Value src )  -- morally Value (ADTensorKind src)
{-# INLINE grad2 #-}
grad2 f vals | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
  revMaybe f vals Nothing

-- | This version of the symbolic reverse derivative operation
-- explicitly takes the sensitivity parameter (the incoming cotangent).
-- It also permits an arbitrary (nested tuple+) type of the domain
-- and arbitrary (nested pair) tensor kind of the codomain
-- of the function to be differentiated. The downside of the generality
-- is that if the function doesn't have an explicit type signature,
-- the type to which this operation is instantiated often has to be spelled
-- in full via explicit type applications to aid type reconstruction.
-- For simplicity of the type signature, the resulting value is converted from
-- the type of concrete contangents to the type of concrete input parameters.
vjp
  :: forall src ztgt tgt.
     ( X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> Concrete (ADTensorKind ztgt)
  -> Value src  -- morally Value (ADTensorKind src)
{-# INLINE vjp #-}
vjp f vals0 dt = snd $ vjp2 f vals0 dt

-- | The @vjp2@ operation works just as 'vjp', but additionally produces
-- the primal result of the objective function at minimal extra cost.
vjp2
  :: forall src ztgt tgt.
     ( X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> Concrete (ADTensorKind ztgt)
  -> ( Concrete ztgt
     , Value src )  -- morally Value (ADTensorKind src)
{-# INLINE vjp2 #-}
vjp2 = revMaybeDt

-- | Compute the reverse derivative not for a specific input, but as symbolic
-- function from inputs to the gradient value.
-- The function is represented as an "artifact", which is the gradient
-- AST term together with the variable corresponding to the input.
gradArtifact
  :: forall src r tgt.
     ( GoodScalar r, X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan (TKScalar r) )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> AstArtifactRev (X src) (TKScalar r)
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE gradArtifact #-}
gradArtifact f vals0
  | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
    let xftk = tftkG (knownSTK @(X src)) $ unConcrete $ toTarget vals0
    in revArtifactAdapt IgnoreIncomingCotangent f xftk

-- | Compute the reverse derivative not for a specific input, but as symbolic
-- function from inputs and incoming cotangents to the gradient value.
-- The function is represented as an "artifact", which is the gradient
-- AST term together with variables corresponding to the input and cotangent.
vjpArtifact
  :: forall src ztgt tgt.
     ( X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> AstArtifactRev (X src) ztgt
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE vjpArtifact #-}
vjpArtifact f vals0 =
  let xftk = tftkG (knownSTK @(X src)) $ unConcrete $ toTarget vals0
  in revArtifactAdaptDt f xftk

-- | Interpret the "artifact" as a function from a concrete tensor
-- to a concrete tensor (possibly adapted, e.g., from horde-ad nested pairs
-- to Haskell n-tuples).
gradInterpretArtifact
  :: forall x r avals.
     (GoodScalar r, X avals ~ ADTensorKind x, AdaptableTarget Concrete avals)
  => AstArtifactRev x (TKScalar r)
       -- ^ the artifact containing the symbolic code of the derivative
  -> Concrete x
  -> avals
{-# INLINE gradInterpretArtifact #-}
gradInterpretArtifact AstArtifactRev{..} parameters
  | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
    let xftk = varNameToFTK artVarDomainRev
        azftk = varNameToFTK artVarDtRev
                  -- STKScalar @(ADTensorScalar r) or STKScalar @Z1
        oneAtF = treplTarget 1 azftk
        env = extendEnv artVarDtRev oneAtF
              $ extendEnv artVarDomainRev parameters emptyEnv
    in if tftkG (ftkToSTK xftk) (unConcrete parameters) == xftk
       then fromTarget $ interpretAstFull env artDerivativeRev
       else error $ "gradInterpretArtifact: reverse derivative parameters must have the same shape as the domain of the objective function: "
                    ++ show ( tftkG (ftkToSTK xftk) (unConcrete parameters)
                            , xftk )

-- | Interpret the "artifact" as a function from concrete tensors
-- to a concrete tensor (possibly adapted, e.g., from horde-ad nested pairs
-- to Haskell n-tuples).
vjpInterpretArtifact
  :: forall x z avals.
     (X avals ~ ADTensorKind x, AdaptableTarget Concrete avals)
  => AstArtifactRev x z
       -- ^ the artifact containing the symbolic code of the derivative
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
          then fromTarget $ interpretAstFull env artDerivativeRev
          else error $ "vjpInterpretArtifact: reverse derivative incoming cotangent must have the same shape as the codomain of the objective function: "
                       ++ show (tftkG (ftkToSTK azftk) (unConcrete dt), azftk)
     else error $ "vjpInterpretArtifact: reverse derivative parameters must have the same shape as the domain of the objective function: "
                  ++ show (tftkG (ftkToSTK xftk) (unConcrete parameters), xftk)


-- * Symbolic reverse derivative adaptors' internal machinery

revMaybe
  :: forall src ztgt tgt.
     ( TKAllNum (ADTensorKind ztgt)
     , X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> Maybe (Concrete (ADTensorKind ztgt))
  -> ( Concrete ztgt
     , Value src )  -- morally Value (ADTensorKind src)
{-# INLINE revMaybe #-}
revMaybe f vals0 mdt =
  let valsTarget = toTarget vals0
      xftk = tftkG (knownSTK @(X src)) $ unConcrete valsTarget
      cotangentHandling =
        maybe IgnoreIncomingCotangent (const UseIncomingCotangent) mdt
      artifactRaw = revArtifactAdapt cotangentHandling f xftk
      artifact = simplifyArtifactRev artifactRaw
      (primal, res) = revInterpretArtifact artifact valsTarget mdt
  in (primal, fromTarget $ fromADTensorKindShared xftk res)

revArtifactAdapt
  :: forall src ztgt tgt.
     ( TKAllNum (ADTensorKind ztgt)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => IncomingCotangentHandling
  -> (src -> tgt)  -- ^ the objective function
  -> FullShapeTK (X src)
  -> AstArtifactRev (X src) ztgt
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE revArtifactAdapt #-}
revArtifactAdapt cotangentHandling f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X src) -> tgt
      g !arg = simplifyUserCode $ ttlet arg $ f . fromTarget
                                  -- fromTarget requires duplicable
  in revProduceArtifact cotangentHandling g emptyEnv xftk

revInterpretArtifact
  :: forall x z. TKAllNum (ADTensorKind z)
  => AstArtifactRev x z
       -- ^ the artifact containing the symbolic code of the derivative
  -> Concrete x
  -> Maybe (Concrete (ADTensorKind z))
  -> (Concrete z, Concrete (ADTensorKind x))
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
          else error $ "revInterpretArtifact: reverse derivative incoming cotangent must have the same shape as the codomain of the objective function: "
                       ++ show (tftkG (ftkToSTK azftk) (unConcrete dt), azftk)
      gradient = interpretAstFull envDt artDerivativeRev
      primal = interpretAstFull env artPrimalRev
  in (primal, gradient)

-- These three functions are as above, but the dt must be provided and so,
-- due to technical reasons, the type is less constrained.
revMaybeDt
  :: forall src ztgt tgt.
     ( X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> Concrete (ADTensorKind ztgt)
  -> ( Concrete ztgt
     , Value src )  -- morally Value (ADTensorKind src)
{-# INLINE revMaybeDt #-}
revMaybeDt f vals0 dt =
  let valsTarget = toTarget vals0
      xftk = tftkG (knownSTK @(X src)) $ unConcrete valsTarget
      artifactRaw = revArtifactAdaptDt f xftk
      artifact = simplifyArtifactRev artifactRaw
      (primal, res) = revInterpretArtifactDt artifact valsTarget dt
  in (primal, fromTarget $ fromADTensorKindShared xftk res)

revArtifactAdaptDt
  :: forall src ztgt tgt.
     ( AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> FullShapeTK (X src)
  -> AstArtifactRev (X src) ztgt
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE revArtifactAdaptDt #-}
revArtifactAdaptDt f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X src) -> tgt
      g !arg = simplifyUserCode $ ttlet arg $ f . fromTarget
                                  -- fromTarget requires duplicable
  in revProduceArtifactDt g emptyEnv xftk

revInterpretArtifactDt
  :: forall x z.
     AstArtifactRev x z
       -- ^ the artifact containing the symbolic code of the derivative
  -> Concrete x
  -> Concrete (ADTensorKind z)
  -> (Concrete z, Concrete (ADTensorKind x))
{-# INLINE revInterpretArtifactDt #-}
revInterpretArtifactDt AstArtifactRev{..} parameters dt =
  let azftk = varNameToFTK artVarDtRev
      env = extendEnv artVarDomainRev parameters emptyEnv
      envDt =
        if tftkG (ftkToSTK azftk) (unConcrete dt) == azftk
        then extendEnv artVarDtRev dt env
        else error $ "revInterpretArtifactDt: reverse derivative incoming cotangent must have the same shape as the codomain of the objective function: "
                     ++ show (tftkG (ftkToSTK azftk) (unConcrete dt), azftk)
      gradient = interpretAstFull envDt artDerivativeRev
      primal = interpretAstFull env artPrimalRev
  in (primal, gradient)


-- * Symbolic reverse derivative adaptors' testing-only internal machinery

revArtifactDelta
  :: forall src ztgt tgt.
     ( TKAllNum (ADTensorKind ztgt)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => IncomingCotangentHandling
  -> (src -> tgt)  -- ^ the objective function
  -> FullShapeTK (X src)
  -> (AstArtifactRev (X src) ztgt, Delta (AstRaw FullSpan) ztgt)
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE revArtifactDelta #-}
revArtifactDelta cotangentHandling f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X src) -> tgt
      g !arg = ttlet arg $ f . fromTarget
  in revArtifactFromForwardPass cotangentHandling
                                (forwardPassByInterpretation g emptyEnv) xftk

revProduceArtifactWithoutInterpretation
  :: forall x z. TKAllNum (ADTensorKind z)
  => IncomingCotangentHandling
  -> (ADVal (AstRaw FullSpan) x -> ADVal (AstRaw FullSpan) z)
  -> FullShapeTK x
  -> (AstArtifactRev x z, Delta (AstRaw FullSpan) z)
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE revProduceArtifactWithoutInterpretation #-}
revProduceArtifactWithoutInterpretation cotangentHandling f xftk =
  -- No simplification performed to let individual tests decide.
  revArtifactFromForwardPass cotangentHandling
                             (forwardPassByApplication f)
                             xftk

forwardPassByApplication
  :: forall x z.
     (ADVal (AstRaw FullSpan) x -> ADVal (AstRaw FullSpan) z)
  -> AstTensor AstMethodShare FullSpan x
  -> AstVarName '(FullSpan, x)
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw FullSpan) z
{-# INLINE forwardPassByApplication #-}
forwardPassByApplication g astVarPrimal var _astVar =
  let deltaInputs = generateDeltaInputs $ varNameToFTK var
      varInputs = dDnotShared (AstRaw astVarPrimal) deltaInputs
  in g varInputs


-- * Symbolic forward derivative adaptors

-- | The forward derivative operation takes the perturbation parameter
-- by convention. It permits an arbitrary (nested tuple+)
-- type of the domain and arbitrary (nested pair) tensor kind of the codomain
-- of the function to be differentiated. The generality sometimes makes it
-- necessary to suppy type hints when applying this operation.
jvp
  :: forall src ztgt tgt.
     ( X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> Value src  -- morally (ADTensorKind src)
  -> Concrete (ADTensorKind ztgt)
{-# INLINE jvp #-}
jvp f vals0 ds = snd $ jvp2 f vals0 ds

-- | The @jvp2@ operation works just as 'jvp', but additionally produces
-- the primal result of the objective function at the direction parameter
-- (without taking the perturbation into account) at minimal extra cost.
jvp2
  :: forall src ztgt tgt.
     ( X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> Value src  -- morally (ADTensorKind src)
  -> (Concrete ztgt, Concrete (ADTensorKind ztgt))
{-# INLINE jvp2 #-}
jvp2 f vals0 ds =
  let valsTarget = toTarget vals0
      xftk = tftkG (knownSTK @(X src)) $ unConcrete valsTarget
      artifactRaw = fwdArtifactAdapt f xftk
      artifact = simplifyArtifactFwd artifactRaw
  in fwdInterpretArtifact artifact valsTarget
     $ toADTensorKindShared xftk (toTarget ds)
       -- the shapes of vals0 vs ds are checked in fwdInterpretArtifact

-- | Compute the forward derivative not for a specific input, but as symbolic
-- function from inputs and perturbation to the derivative value.
-- The function is represented as an "artifact", which is the derivative
-- AST term together with variables corresponding to the input and perturbation.
jvpArtifact
  :: forall src ztgt tgt.
     ( X src ~ X (Value src), KnownSTK (X src)
     , AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , AdaptableTarget Concrete (Value src)
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> Value src
  -> AstArtifactFwd (X src) ztgt
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE jvpArtifact #-}
jvpArtifact f vals0 =
  let xftk = tftkG (knownSTK @(X src)) $ unConcrete $ toTarget vals0
  in fwdArtifactAdapt f xftk

-- | Interpret the "artifact" as a function from concrete tensors
-- to a concrete tensor.
jvpInterpretArtifact
  :: forall x z.
     AstArtifactFwd x z
       -- ^ the artifact containing the symbolic code of the derivative
  -> Concrete x
  -> Concrete (ADTensorKind x)
  -> Concrete (ADTensorKind z)
{-# INLINE jvpInterpretArtifact #-}
jvpInterpretArtifact art parameters = snd . fwdInterpretArtifact art parameters
  -- the shapes of parameters vs ds are checked in fwdInterpretArtifact


-- * Symbolic forward derivative adaptors' internal machinery

fwdArtifactAdapt
  :: forall src ztgt tgt.
     ( AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> FullShapeTK (X src)
  -> AstArtifactFwd (X src) ztgt
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE fwdArtifactAdapt #-}
fwdArtifactAdapt f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X src) -> tgt
      g !arg = simplifyUserCode $ ttlet arg $ f . fromTarget
                                  -- fromTarget requires duplicable
  in fwdProduceArtifact g emptyEnv xftk

fwdInterpretArtifact
  :: forall x z.
     AstArtifactFwd x z
       -- ^ the artifact containing the symbolic code of the derivative
  -> Concrete x
  -> Concrete (ADTensorKind x)
  -> (Concrete z, Concrete (ADTensorKind z))
{-# INLINE fwdInterpretArtifact #-}
fwdInterpretArtifact AstArtifactFwd{..} parameters ds =
  let xftk = varNameToFTK artVarDomainFwd
      xstk = ftkToSTK xftk
      env = extendEnv artVarDomainFwd parameters emptyEnv
      envD = extendEnv artVarDsFwd ds env
  in if tftkG xstk (unConcrete parameters) == xftk
     then if tftkG (adSTK xstk) (unConcrete ds) == adFTK xftk
          then let derivative = interpretAstFull envD artDerivativeFwd
                   primal = interpretAstFull env artPrimalFwd
               in (primal, derivative)
          else error $ "fwdInterpretArtifact: forward derivative perturbation must have the same shape as the domain of the objective function: "
                       ++ show (tftkG (adSTK xstk) (unConcrete ds), adFTK xftk)
     else error $ "fwdInterpretArtifact: forward derivative input must have the same shape as the domain of the objective function: "
                  ++ show (tftkG xstk (unConcrete parameters), xftk)


-- * Symbolic forward derivative adaptors' testing-only internal machinery

fwdArtifactDelta
  :: forall src ztgt tgt.
     ( AdaptableTarget (AstTensor AstMethodLet FullSpan) src
     , tgt ~ AstTensor AstMethodLet FullSpan ztgt )
  => (src -> tgt)  -- ^ the objective function
  -> FullShapeTK (X src)
  -> (AstArtifactFwd (X src) ztgt, Delta (AstRaw FullSpan) ztgt)
       -- ^ the artifact containing the symbolic code of the derivative
{-# INLINE fwdArtifactDelta #-}
fwdArtifactDelta f xftk =
  let g :: AstTensor AstMethodLet FullSpan (X src) -> tgt
      g !arg = ttlet arg $ f . fromTarget
  in fwdArtifactFromForwardPass (forwardPassByInterpretation g emptyEnv) xftk


-- * Non-symbolic reverse derivative adaptors

-- These adaptor are generalized to any suitable target, because
-- it's useful when defining complex nested derivatives.
-- However, it incurs many extra type applications, which is why
-- we refrain from such a generalization for the symbolic adaptors above,
-- which are less likely to be used in nested derivatives
-- and more likely to be used a lot in simple use cases..

-- We are inlining these functions because they take function arguments
-- and are not too large. However, because they are called in many places,
-- we break the inline chain not far from the top, to avoid exe blowup.
--
-- | This simplified version of the concrete (non-symbolic)
-- reverse derivative operation sets the incoming cotangent @dt@ to be 1
-- and assumes the codomain of the function to be differentiated is a scalar.
cgrad
  :: forall src r tgt target.
     ( GoodScalar r, X src ~ X (DValue src), KnownSTK (X src)
     , AdaptableTarget (ADVal target) src
     , AdaptableTarget target (DValue src)
     , tgt ~ ADVal target (TKScalar r)
     , ADReadyNoLet target, ShareTensor target )
  => (src -> tgt)  -- ^ the objective function
  -> DValue src
  -> DValue src  -- morally DValue (ADTensorKind src)
{-# INLINE cgrad #-}
cgrad f vals = snd $ cgrad2 f vals

cgrad2
  :: forall src r tgt target.
     ( GoodScalar r, X src ~ X (DValue src), KnownSTK (X src)
     , AdaptableTarget (ADVal target) src
     , AdaptableTarget target (DValue src)
     , tgt ~ ADVal target (TKScalar r)
     , ADReadyNoLet target, ShareTensor target )
  => (src -> tgt)  -- ^ the objective function
  -> DValue src
  -> ( target (TKScalar r)
     , DValue src )  -- morally DValue (ADTensorKind src)
{-# INLINE cgrad2 #-}
cgrad2 f vals | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
  crevMaybe f vals Nothing

-- | This more general version of the concrete (non-symbolic)
-- reverse derivative operation additionally takes the sensitivity parameter
-- (the incoming cotangent).
cvjp
  :: forall src ztgt tgt target.
     ( X src ~ X (DValue src), KnownSTK (X src)
     , AdaptableTarget (ADVal target) src
     , AdaptableTarget target (DValue src)
     , tgt ~ ADVal target ztgt
     , ADReadyNoLet target, ShareTensor target )
  => (src -> tgt)  -- ^ the objective function
  -> DValue src
  -> target (ADTensorKind ztgt)
  -> DValue src  -- morally DValue (ADTensorKind src)
{-# INLINE cvjp #-}
cvjp f vals0 dt = snd $ cvjp2 f vals0 dt

cvjp2
  :: forall src ztgt tgt target.
     ( X src ~ X (DValue src), KnownSTK (X src)
     , AdaptableTarget (ADVal target) src
     , AdaptableTarget target (DValue src)
     , tgt ~ ADVal target ztgt
     , ADReadyNoLet target, ShareTensor target )
  => (src -> tgt)  -- ^ the objective function
  -> DValue src
  -> target (ADTensorKind ztgt)
  -> ( target ztgt
     , DValue src )  -- morally DValue (ADTensorKind src)
{-# INLINE cvjp2 #-}
cvjp2 = crevMaybeDt


-- * Non-symbolic reverse derivative adaptors' internal machinery

crevMaybe
  :: forall src ztgt tgt target.
     ( TKAllNum (ADTensorKind ztgt)
     , X src ~ X (DValue src), KnownSTK (X src)
     , AdaptableTarget (ADVal target) src
     , AdaptableTarget target (DValue src)
     , tgt ~ ADVal target ztgt
     , ADReadyNoLet target, ShareTensor target )
  => (src -> tgt)  -- ^ the objective function
  -> DValue src
  -> Maybe (target (ADTensorKind ztgt))
  -> ( target ztgt
     , DValue src )  -- morally SValue (ADTensorKind src)
{-# INLINE crevMaybe #-}
crevMaybe f vals0 mdt =
  let valsTarget = toTarget vals0
      g :: ADVal target (X src) -> tgt
      g = f . fromTarget
      xftk = tftk (knownSTK @(X src)) valsTarget
      (primal, res) = crevOnParams mdt g xftk valsTarget
  in (primal, fromTarget $ fromADTensorKindShared xftk res)

-- This function is as above, but the dt must be provided and so,
-- due to technical reasons, the type is less constrained.
crevMaybeDt
  :: forall src ztgt tgt target.
     ( X src ~ X (DValue src), KnownSTK (X src)
     , AdaptableTarget (ADVal target) src
     , AdaptableTarget target (DValue src)
     , tgt ~ ADVal target ztgt
     , ADReadyNoLet target, ShareTensor target )
  => (src -> tgt)  -- ^ the objective function
  -> DValue src
  -> target (ADTensorKind ztgt)
  -> ( target ztgt
     , DValue src )  -- morally SValue (ADTensorKind src)
{-# INLINE crevMaybeDt #-}
crevMaybeDt f vals0 dt =
  let valsTarget = toTarget vals0
      g :: ADVal target (X src) -> tgt
      g = f . fromTarget
      xftk = tftk (knownSTK @(X src)) valsTarget
      (primal, res) = crevOnParamsDt dt g xftk valsTarget
  in (primal, fromTarget $ fromADTensorKindShared xftk res)


-- * Non-symbolic forward derivative adaptors

-- | Concrete (non-symbolic) forward derivative operation. It always takes
-- the perturbation parameter, by convention.
cjvp
  :: forall src ztgt tgt target.
     ( X src ~ X (DValue src), KnownSTK (X src)
     , AdaptableTarget (ADVal target) src
     , AdaptableTarget target (DValue src)
     , tgt ~ ADVal target ztgt
     , ADReadyNoLet target, ShareTensor target )
  => (src -> tgt)  -- ^ the objective function
  -> DValue src
  -> DValue src  -- morally (ADTensorKind src)
  -> target (ADTensorKind ztgt)
{-# INLINE cjvp #-}
cjvp f vals ds = snd $ cjvp2 f vals ds

-- | The @cjvp2@ operation works just as 'cjvp', but additionally produces
-- the primal result of the objective function at the direction parameter
-- (without taking the perturbation into account) at no extra cost.
cjvp2
  :: forall src ztgt tgt target.
     ( X src ~ X (DValue src), KnownSTK (X src)
     , AdaptableTarget (ADVal target) src
     , AdaptableTarget target (DValue src)
     , tgt ~ ADVal target ztgt
     , ADReadyNoLet target, ShareTensor target )
  => (src -> tgt)  -- ^ the objective function
  -> DValue src
  -> DValue src  -- morally (ADTensorKind src)
  -> (target ztgt, target (ADTensorKind ztgt))
{-# INLINE cjvp2 #-}
cjvp2 f vals0 ds =
  let valsTarget = toTarget vals0
      xftk = tftk (knownSTK @(X src)) valsTarget
      g :: ADVal target (X src) -> tgt
      g = f . fromTarget
      dsTarget = toTarget ds
  in if tftk (ftkToSTK xftk) dsTarget == xftk
     then cfwdOnParams xftk valsTarget g
          $ toADTensorKindShared xftk dsTarget
     else error $ "cjvp2: forward derivative input must have the same shape as the perturbation argument: "
                  ++ show (tftk (ftkToSTK xftk) dsTarget, xftk)
