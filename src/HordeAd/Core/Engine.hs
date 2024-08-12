{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and (forward) derivative
-- calculation for an objective function on values of complicated
-- types (e.g., with tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Optimizers are add-ons.
module HordeAd.Core.Engine
  ( -- * Reverse derivative adaptors
    rev, revDt, revArtifactAdapt
  , revProduceArtifactWithoutInterpretation
  , revProduceArtifactWithoutInterpretationTKNew
  , revEvalArtifact, revEvalArtifactTKNew
    -- * Forward derivative adaptors
  , fwd, fwdArtifactAdapt, fwdEvalArtifact
    -- * Old gradient adaptors
  , crev, crevDt
    -- * Old derivative adaptors
  , cfwd
  ) where

import Prelude

import Data.Int (Int64)
import Data.Maybe (fromMaybe, isJust)
import Data.Vector.Generic qualified as V
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
  :: forall r y g tgtAstVals astvals.
     ( tgtAstVals ~ g r y
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector ORArray (Value astvals)
     , AdaptableHVector ORArray (Value tgtAstVals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals -> Value astvals
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
  :: forall tgtAstVals astvals.
     ( AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector ORArray (Value astvals)
     , AdaptableHVector ORArray (Value tgtAstVals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals -> Value tgtAstVals
  -> Value astvals
{-# INLINE revDt #-}
revDt f vals dt = revDtMaybe f vals (Just dt)

revDtMaybe
  :: forall tgtAstVals astvals.
     ( AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector ORArray (Value astvals)
     , AdaptableHVector ORArray (Value tgtAstVals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals -> Maybe (Value tgtAstVals)
  -> Value astvals
{-# INLINE revDtMaybe #-}
revDtMaybe f vals mdt =
  let g hVector = HVectorPseudoTensor
                  $ toHVectorOf $ f $ parseHVector (fromValue vals) hVector
      valsH = toHVectorOf vals
      voidH = voidFromHVector valsH
      artifact = fst $ revProduceArtifact (isJust mdt) g emptyEnv voidH
      mdth = toHVectorOf <$> mdt
  in parseHVector vals
     $ fst $ revEvalArtifact artifact valsH mdth
{-# SPECIALIZE revDtMaybe
  :: ( KnownNat n
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => (astvals -> AstRanked FullSpan Double n)
  -> Value astvals
  -> Maybe (ORArray Double n)
  -> Value astvals #-}

revArtifactAdapt
  :: forall r y g tgtAstVals astvals.
     ( tgtAstVals ~ g r y
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => Bool -> (astvals -> tgtAstVals) -> Value astvals
  -> (AstArtifact TKUntyped TKUntyped, Delta (AstRaw PrimalSpan) TKUntyped )
revArtifactAdapt hasDt f vals =
  let g hVector = HVectorPseudoTensor
                  $ toHVectorOf $ f $ parseHVector (fromValue vals) hVector
      valsH = toHVectorOf @ORArray vals
      voidH = voidFromHVector valsH
  in revProduceArtifact hasDt g emptyEnv voidH
{-# SPECIALIZE revArtifactAdapt
  :: ( KnownNat n
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => Bool -> (astvals -> AstRanked FullSpan Double n) -> Value astvals
  -> (AstArtifact TKUntyped TKUntyped, Delta (AstRaw PrimalSpan) TKUntyped) #-}

revProduceArtifactWithoutInterpretation
  :: (AdaptableHVector (ADVal (AstRaw PrimalSpan))
                       (ADVal primal_g r y))
  => Bool
  -> (HVector (ADVal (AstRaw PrimalSpan)) -> ADVal primal_g r y)
  -> VoidHVector
  -> (AstArtifact TKUntyped TKUntyped, Delta (AstRaw PrimalSpan) TKUntyped)
{-# INLINE revProduceArtifactWithoutInterpretation #-}
revProduceArtifactWithoutInterpretation hasDt f =
  let g :: HVector (AstRaw PrimalSpan)
        -> [AstDynamicVarName]
        -> HVector (AstRanked FullSpan)
        -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) TKUntyped
      g hVectorPrimal vars hVector =
        HVectorPseudoTensor $ toHVector
        $ forwardPassByApplication f hVectorPrimal vars hVector
  in revArtifactFromForwardPass hasDt g

revProduceArtifactWithoutInterpretationTKNew
  :: forall x z. (x ~ TKUntyped, TensorKind z)
  => Bool
  -> (HVector (ADVal (AstRaw PrimalSpan))
      -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z)
  -> VoidHVector
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifactWithoutInterpretationTKNew #-}
revProduceArtifactWithoutInterpretationTKNew hasDt f =
  let g :: HVector (AstRaw PrimalSpan)
        -> AstVarName FullSpan x
        -> HVector (AstRanked FullSpan)
        -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z
      g hVectorPrimal = forwardPassByApplicationTKNew f hVectorPrimal
  in revArtifactFromForwardPassTKNew @x @z hasDt g

forwardPassByApplication
  :: (HVector (ADVal (AstRaw PrimalSpan)) -> ADVal primal_g r y)
  -> HVector (AstRaw PrimalSpan)
  -> [AstDynamicVarName]
  -> HVector (AstRanked FullSpan)
  -> ADVal primal_g r y
{-# INLINE forwardPassByApplication #-}
forwardPassByApplication g hVectorPrimal _vars _hVector =
  let deltaInputs = generateDeltaInputs hVectorPrimal
      varInputs = makeADInputs hVectorPrimal deltaInputs
  in g varInputs

forwardPassByApplicationTKNew
  :: (HVector (ADVal (AstRaw PrimalSpan))
      -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z)
  -> HVector (AstRaw PrimalSpan)
  -> AstVarName FullSpan TKUntyped
  -> HVector (AstRanked FullSpan)
  -> InterpretationTarget (ADVal (AstRaw PrimalSpan)) z
{-# INLINE forwardPassByApplicationTKNew #-}
forwardPassByApplicationTKNew g hVectorPrimal _var _hVector =
  let deltaInputs = generateDeltaInputs hVectorPrimal
      varInputs = makeADInputs hVectorPrimal deltaInputs
  in g varInputs

revEvalArtifact
  :: AstArtifact TKUntyped TKUntyped
  -> HVector ORArray
  -> Maybe (HVector ORArray)
  -> (HVector ORArray, HVector ORArray)
{-# INLINE revEvalArtifact #-}
revEvalArtifact (AstArtifact varsDt vars
                             (HVectorPseudoTensor (AstRawWrap gradient))
                             (HVectorPseudoTensor (AstRawWrap primal)))
                parameters mdt =
  let domsB = voidFromVars varsDt
      dt1 = mapHVectorShaped (const $ srepl 1) $ V.map dynamicFromVoid domsB
      dts = fromMaybe dt1 mdt
  in if voidHVectorMatches (shapeAstHVector primal) dts
     then
       let env = extendEnvHVector vars parameters emptyEnv
           envDt = extendEnvHVector varsDt dts env
           gradientHVector = unHVectorPseudoTensor $ interpretAst envDt gradient
           primalTensor = unHVectorPseudoTensor $ interpretAst env primal
       in (gradientHVector, primalTensor)
     else error "revEvalArtifact: primal result and the incoming contangent should have same shapes"

revEvalArtifactTKNew
  :: forall x z. (x ~ TKUntyped, TensorKind z)
  => AstArtifactRev x z
  -> HVector ORArray
  -> Maybe (InterpretationTarget ORArray z)
  -> (HVector ORArray, InterpretationTarget ORArray z)
{-# INLINE revEvalArtifactTKNew #-}
revEvalArtifactTKNew (AstArtifactRev varDt var
                             (HVectorPseudoTensor (AstRawWrap gradient))
                             primal)
                parameters mdt =
  let oneAtF = interpretationConstant 1 $ tshapeFull (stensorKind @z) primal
      dt = fromMaybe oneAtF mdt
      pars = HVectorPseudoTensor $ dmkHVector parameters
      env = extendEnv var pars emptyEnv
      envDt = extendEnv varDt dt env
      gradientHVector = unHVectorPseudoTensor $ interpretAst envDt gradient
      primalTensor = interpretAst env $ unRawY (stensorKind @z) primal
  in (gradientHVector, primalTensor)


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
  :: forall tgtAstVals astvals.
     ( AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector ORArray (Value astvals)
     , AdaptableHVector ORArray (Value tgtAstVals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals -> Value astvals
  -> Value tgtAstVals
fwd f vals ds =
  let g hVector = HVectorPseudoTensor
                  $ toHVectorOf $ f $ parseHVector (fromValue vals) hVector
      valsH = toHVectorOf vals
      voidH = voidFromHVector valsH
      artifact = fst $ fwdProduceArtifact g emptyEnv voidH
      dsH = toHVectorOf ds
      err = error "fwd: codomain of unknown length"
  in parseHVector err $ fst $ fwdEvalArtifact artifact valsH dsH

fwdArtifactAdapt
  :: forall r y g tgtAstVals astvals.
     ( tgtAstVals ~ g r y
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector ORArray (Value astvals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals
  -> (AstArtifact TKUntyped TKUntyped, Delta (AstRaw PrimalSpan) TKUntyped)
fwdArtifactAdapt f vals =
  let g hVector = HVectorPseudoTensor
                  $ toHVectorOf $ f $ parseHVector (fromValue vals) hVector
      valsH = toHVectorOf @ORArray vals
      voidH = voidFromHVector valsH
  in fwdProduceArtifact g emptyEnv voidH

fwdEvalArtifact
  :: AstArtifact TKUntyped TKUntyped
  -> HVector ORArray
  -> HVector ORArray
  -> (HVector ORArray, HVector ORArray)
{-# INLINE fwdEvalArtifact #-}
fwdEvalArtifact (AstArtifact varDs vars derivative primal) parameters ds =
  if hVectorsMatch parameters ds then
    let env = extendEnvHVector vars parameters emptyEnv
        envDs = extendEnvHVector varDs ds env
        derivativeTensor = unHVectorPseudoTensor $ interpretAst envDs $ unAstRawWrap $ unHVectorPseudoTensor derivative
        primalTensor = unHVectorPseudoTensor $ interpretAst env $ unAstRawWrap $ unHVectorPseudoTensor primal
    in (derivativeTensor, primalTensor)
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
  :: forall r y f vals advals.
     ( RankedOf f ~ ORArray
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector (ADVal ORArray) (ADVal f r y)
     , AdaptableHVector ORArray vals
     , AdaptableHVector ORArray (f r y)
     , DualNumberValue advals, vals ~ DValue advals )
  => (advals -> ADVal f r y) -> vals -> vals
{-# INLINE crev #-}
crev f vals = crevDtMaybe f vals Nothing

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f vals advals.
     ( RankedOf f ~ ORArray
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector (ADVal ORArray) (ADVal f r y)
     , AdaptableHVector ORArray vals
     , AdaptableHVector ORArray (f r y)
     , DualNumberValue advals, vals ~ DValue advals )
  => (advals -> ADVal f r y) -> vals -> f r y -> vals
{-# INLINE crevDt #-}
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall r y f vals advals.
     ( RankedOf f ~ ORArray
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector (ADVal ORArray) (ADVal f r y)
     , AdaptableHVector ORArray vals
     , AdaptableHVector ORArray (f r y)
     , DualNumberValue advals, vals ~ DValue advals )
  => (advals -> ADVal f r y) -> vals -> Maybe (f r y) -> vals
{-# INLINE crevDtMaybe #-}
crevDtMaybe f vals mdt =
  let g hVector = hVectorADValToADVal
                  $ toHVectorOf $ f $ parseHVector (fromDValue vals) hVector
      valsH = toHVectorOf vals
      mdth = toHVector @ORArray <$> mdt
  in parseHVector vals
     $ fst $ crevOnHVector mdth g valsH

{-# SPECIALIZE crevOnHVector
  :: Maybe (HVector ORArray)
  -> (HVector (ADVal ORArray)
  -> ADVal (HVectorPseudoTensor ORArray) Float '())
  -> HVector ORArray
  -> (HVector ORArray, HVector ORArray) #-}


-- * Old derivative adaptors, with constant and fixed inputs

-- | This takes the sensitivity parameter, by convention.
cfwd
  :: forall r y f vals advals.
     ( RankedOf f ~ ORArray
     , AdaptableHVector (ADVal ORArray) advals
     , AdaptableHVector (ADVal ORArray) (ADVal f r y)
     , AdaptableHVector ORArray vals
     , AdaptableHVector ORArray (f r y)
     , DualNumberValue advals, vals ~ DValue advals )
  => (advals -> ADVal f r y) -> vals -> vals -> f r y
cfwd f vals ds =
  let g hVector = hVectorADValToADVal
                  $ toHVectorOf @(ADVal ORArray)
                  $ f $ parseHVector (fromDValue vals) hVector
      valsH = toHVectorOf vals
      dsH = toHVectorOf ds
      err = error "fwd: codomain of unknown length"
  in parseHVector err $ fst $ cfwdOnHVector valsH g dsH





-- These and all other SPECIALIZE pragmas are needed due to the already
-- mostly fixed issues #21286 and others, even just to compare
-- the output with the and without.
-- We need pragmas on shaped operations even for ranked benchmarks,
-- because threading the dictionaries through mutual recursive functions
-- would cause trouble.

{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal ORArray)
  -> AstTensor PrimalSpan (TKR r n)
  -> ORArray r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor PrimalSpan (TKR r n)
  -> AstRanked PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv ORArray
  -> AstTensor PrimalSpan (TKR r n)
  -> ORArray r n #-}

{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (KnownShS sh, Typeable r)
  => AstEnv (ADVal ORArray)
  -> AstTensor PrimalSpan (TKS r sh)
  -> OSArray r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (KnownShS sh, Typeable r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor PrimalSpan (TKS r sh)
  -> AstShaped PrimalSpan r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (KnownShS sh, Typeable r)
  => AstEnv ORArray
  -> AstTensor PrimalSpan (TKS r sh)
  -> OSArray r sh #-}

{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal ORArray)
  -> AstTensor PrimalSpan (TKR r n)
  -> ORArray r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor PrimalSpan (TKR Double n)
  -> ORArray Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor PrimalSpan (TKR Float n)
  -> ORArray Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor PrimalSpan (TKR Int64 n)
  -> ORArray Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor PrimalSpan (TKR r n)
  -> AstRanked PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor PrimalSpan (TKR Double n)
  -> AstRanked PrimalSpan Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor PrimalSpan (TKR Float n)
  -> AstRanked PrimalSpan Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor PrimalSpan (TKR Int64 n)
  -> AstRanked PrimalSpan Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv ORArray
  -> AstTensor PrimalSpan (TKR r n)
  -> ORArray r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor PrimalSpan (TKR Double n)
  -> ORArray Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor PrimalSpan (TKR Float n)
  -> ORArray Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor PrimalSpan (TKR Int64 n)
  -> ORArray Int64 n #-}

{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal ORArray)
  -> AstTensor DualSpan (TKR r n)
  -> DeltaR ORArray r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor DualSpan (TKR Double n)
  -> DeltaR ORArray Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor DualSpan (TKR Float n)
  -> DeltaR ORArray Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal ORArray)
  -> AstTensor DualSpan (TKR Int64 n)
  -> DeltaR ORArray Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor DualSpan (TKR r n)
  -> DeltaR (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor DualSpan (TKR Double n)
  -> DeltaR (AstRanked PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor DualSpan (TKR Float n)
  -> DeltaR (AstRanked PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor DualSpan (TKR Int64 n)
  -> DeltaR (AstRanked PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv ORArray
  -> AstTensor DualSpan (TKR r n)
  -> DummyDual r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor DualSpan (TKR Double n)
  -> DummyDual Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor DualSpan (TKR Float n)
  -> DummyDual Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv ORArray
  -> AstTensor DualSpan (TKR Int64 n)
  -> DummyDual Int64 n #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKR r n)
  -> ADVal ORArray r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKR r n)
  -> ADVal (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv ORArray
  -> AstTensor s (TKR r n)
  -> ORArray r n #-}

{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKS r sh)
  -> ADVal OSArray r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKS r sh)
  -> ADVal (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Typeable r, AstSpan s)
  => AstEnv ORArray
  -> AstTensor s (TKS r sh)
  -> OSArray r sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKR r n)
  -> ADVal ORArray r n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKR Double n)
  -> ADVal ORArray Double n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKR Float n)
  -> ADVal ORArray Float n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKR Int64 n)
  -> ADVal ORArray Int64 n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKR r n)
  -> ADVal (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKR Double n)
  -> ADVal (AstRanked PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKR Float n)
  -> ADVal (AstRanked PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKR Int64 n)
  -> ADVal (AstRanked PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s (TKR r n)
  -> ORArray r n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s (TKR Double n)
  -> ORArray Double n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s (TKR Float n)
  -> ORArray Float n #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s (TKR Int64 n)
  -> ORArray Int64 n #-}

{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKS r sh)
  -> ADVal OSArray r sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKS Double sh)
  -> ADVal OSArray Double sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKS Float sh)
  -> ADVal OSArray Float sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s (TKS Int64 sh)
  -> ADVal OSArray Int64 sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKS r sh)
  -> ADVal (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKS Double sh)
  -> ADVal (AstShaped PrimalSpan) Double sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKS Float sh)
  -> ADVal (AstShaped PrimalSpan) Float sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s (TKS Int64 sh)
  -> ADVal (AstShaped PrimalSpan) Int64 sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s (TKS r sh)
  -> OSArray r sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s (TKS Double sh)
  -> OSArray Double sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s (TKS Float sh)
  -> OSArray Float sh #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s (TKS Int64 sh)
  -> OSArray Int64 sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal ORArray)
  -> AstTensor s TKUntyped
  -> HVectorPseudoTensor (ADVal ORArray) Float '() #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstTensor s TKUntyped
  -> HVectorPseudoTensor (ADVal (AstRanked PrimalSpan)) Float '() #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s TKUntyped
  -> HVectorPseudoTensor ORArray Float '() #-}
{-# SPECIALIZE interpretAst
  :: AstSpan s
  => AstEnv ORArray
  -> AstTensor s TKUntyped
  -> HVectorPseudoTensor ORArray Float '() #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal ORArray)
  -> AstBool
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstBool
  -> AstBool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv ORArray
  -> AstBool
  -> Bool #-}
