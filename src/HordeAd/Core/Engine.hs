{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and (forward) derivative
-- calculation for an objective function on values of complicated
-- types (e.g., with tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Optimizers are add-ons.
module HordeAd.Core.Engine
  ( -- * Reverse derivative adaptors
    rev, revDt, revArtifactAdapt, revProduceArtifactWithoutInterpretation
  , revEvalArtifact
    -- * Forward derivative adaptors
  , fwd, fwdArtifactAdapt, fwdEvalArtifact
    -- * Old gradient adaptors
  , crev, crevDt
    -- * Old derivative adaptors
  , cfwd
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Int (Int64)
import           Data.Maybe (fromMaybe, isJust)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Type.Reflection (Typeable)

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
import HordeAd.Core.Types

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
     , AdaptableHVector (Flip OR.Array) (Value astvals)
     , AdaptableHVector (Flip OR.Array) (Value tgtAstVals)
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
     , AdaptableHVector (Flip OR.Array) (Value astvals)
     , AdaptableHVector (Flip OR.Array) (Value tgtAstVals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals -> Value tgtAstVals
  -> Value astvals
{-# INLINE revDt #-}
revDt f vals dt = revDtMaybe f vals (Just dt)

revDtMaybe
  :: forall tgtAstVals astvals.
     ( AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector (Flip OR.Array) (Value astvals)
     , AdaptableHVector (Flip OR.Array) (Value tgtAstVals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals -> Maybe (Value tgtAstVals)
  -> Value astvals
{-# INLINE revDtMaybe #-}
revDtMaybe f vals mdt =
  let g hVector = HVectorPseudoTensor
                  $ toHVectorOf $ f $ parseHVector (fromValue vals) hVector
      valsH = toHVectorOf vals
      voidH = voidFromHVector valsH
      artifact = fst $ revProduceArtifact (isJust mdt) g EM.empty voidH
      mdth = toHVectorOf <$> mdt
  in parseHVector vals
     $ fst $ revEvalArtifact artifact valsH mdth
{-# SPECIALIZE revDtMaybe
  :: ( KnownNat n
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (Flip OR.Array) (Value astvals)
     , TermValue astvals )
  => (astvals -> AstRanked FullSpan Double n)
  -> Value astvals
  -> Maybe (Flip OR.Array Double n)
  -> Value astvals #-}

revArtifactAdapt
  :: forall r y g tgtAstVals astvals.
     ( tgtAstVals ~ g r y
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector (Flip OR.Array) (Value astvals)
     , TermValue astvals )
  => Bool -> (astvals -> tgtAstVals) -> Value astvals
  -> (AstArtifact, DeltaH (AstRaw PrimalSpan))
revArtifactAdapt hasDt f vals =
  let g hVector = HVectorPseudoTensor
                  $ toHVectorOf $ f $ parseHVector (fromValue vals) hVector
      valsH = toHVectorOf @(Flip OR.Array) vals
      voidH = voidFromHVector valsH
  in revProduceArtifact hasDt g EM.empty voidH
{-# SPECIALIZE revArtifactAdapt
  :: ( KnownNat n
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (Flip OR.Array) (Value astvals)
     , TermValue astvals )
  => Bool -> (astvals -> AstRanked FullSpan Double n) -> Value astvals
  -> (AstArtifact, DeltaH (AstRaw PrimalSpan)) #-}

revProduceArtifactWithoutInterpretation
  :: (AdaptableHVector (ADVal (AstRaw PrimalSpan))
                       (ADVal primal_g r y))
  => Bool
  -> (HVector (ADVal (AstRaw PrimalSpan)) -> ADVal primal_g r y)
  -> VoidHVector
  -> (AstArtifact, DeltaH (AstRaw PrimalSpan))
{-# INLINE revProduceArtifactWithoutInterpretation #-}
revProduceArtifactWithoutInterpretation hasDt f =
  let g hVectorPrimal vars hVector =
        hVectorADValToADVal
        $ toHVector
        $ forwardPassByApplication f hVectorPrimal vars hVector
  in revArtifactFromForwardPass hasDt g

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

revEvalArtifact
  :: AstArtifact
  -> HVector (Flip OR.Array)
  -> Maybe (HVector (Flip OR.Array))
  -> (HVector (Flip OR.Array), HVector (Flip OR.Array))
{-# INLINE revEvalArtifact #-}
revEvalArtifact (AstArtifact varsDt vars
                             (AstRawWrap gradient) (AstRawWrap primal))
                parameters mdt =
  let domsB = voidFromVars varsDt
      dt1 = mapHVectorShaped (const 1) $ V.map dynamicFromVoid domsB
      dts = fromMaybe dt1 mdt
  in if voidHVectorMatches (shapeAstHVector primal) dts
     then
       let env = extendEnvHVector vars parameters EM.empty
           envDt = extendEnvHVector varsDt dts env
           gradientHVector = interpretAstHVector envDt gradient
           primalTensor = interpretAstHVector env primal
       in (gradientHVector, primalTensor)
     else error "revEvalArtifact: primal result and the incoming contangent should have same shapes"


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
     , AdaptableHVector (Flip OR.Array) (Value astvals)
     , AdaptableHVector (Flip OR.Array) (Value tgtAstVals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals -> Value astvals
  -> Value tgtAstVals
fwd f vals ds =
  let g hVector = HVectorPseudoTensor
                  $ toHVectorOf $ f $ parseHVector (fromValue vals) hVector
      valsH = toHVectorOf vals
      voidH = voidFromHVector valsH
      artifact = fst $ fwdProduceArtifact g EM.empty voidH
      dsH = toHVectorOf ds
      err = error "fwd: codomain of unknown length"
  in parseHVector err $ fst $ fwdEvalArtifact artifact valsH dsH

fwdArtifactAdapt
  :: forall r y g tgtAstVals astvals.
     ( tgtAstVals ~ g r y
     , AdaptableHVector (AstRanked FullSpan) astvals
     , AdaptableHVector (AstRanked FullSpan) tgtAstVals
     , AdaptableHVector (Flip OR.Array) (Value astvals)
     , TermValue astvals )
  => (astvals -> tgtAstVals) -> Value astvals
  -> (AstArtifact, DeltaH (AstRaw PrimalSpan))
fwdArtifactAdapt f vals =
  let g hVector = HVectorPseudoTensor
                  $ toHVectorOf $ f $ parseHVector (fromValue vals) hVector
      valsH = toHVectorOf @(Flip OR.Array) vals
      voidH = voidFromHVector valsH
  in fwdProduceArtifact g EM.empty voidH

fwdEvalArtifact
  :: AstArtifact
  -> HVector (Flip OR.Array)
  -> HVector (Flip OR.Array)
  -> (HVector (Flip OR.Array), HVector (Flip OR.Array))
{-# INLINE fwdEvalArtifact #-}
fwdEvalArtifact (AstArtifact varDs vars derivative primal) parameters ds =
  if hVectorsMatch parameters ds then
    let env = extendEnvHVector vars parameters EM.empty
        envDs = extendEnvHVector varDs ds env
        derivativeTensor = interpretAstHVector envDs $ unAstRawWrap derivative
        primalTensor = interpretAstHVector env $ unAstRawWrap primal
    in (derivativeTensor, primalTensor)
 else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shapes"


-- * Old gradient adaptors, with constant and fixed inputs and dt

-- The equality `RankedOf f ~ Flip OR.Array` is needed for type-checking
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
     ( RankedOf f ~ Flip OR.Array
     , AdaptableHVector (ADVal (Flip OR.Array)) advals
     , AdaptableHVector (ADVal (Flip OR.Array)) (ADVal f r y)
     , AdaptableHVector (Flip OR.Array) vals
     , AdaptableHVector (Flip OR.Array) (f r y)
     , DualNumberValue advals, vals ~ DValue advals )
  => (advals -> ADVal f r y) -> vals -> vals
{-# INLINE crev #-}
crev f vals = crevDtMaybe f vals Nothing

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f vals advals.
     ( RankedOf f ~ Flip OR.Array
     , AdaptableHVector (ADVal (Flip OR.Array)) advals
     , AdaptableHVector (ADVal (Flip OR.Array)) (ADVal f r y)
     , AdaptableHVector (Flip OR.Array) vals
     , AdaptableHVector (Flip OR.Array) (f r y)
     , DualNumberValue advals, vals ~ DValue advals )
  => (advals -> ADVal f r y) -> vals -> f r y -> vals
{-# INLINE crevDt #-}
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall r y f vals advals.
     ( RankedOf f ~ Flip OR.Array
     , AdaptableHVector (ADVal (Flip OR.Array)) advals
     , AdaptableHVector (ADVal (Flip OR.Array)) (ADVal f r y)
     , AdaptableHVector (Flip OR.Array) vals
     , AdaptableHVector (Flip OR.Array) (f r y)
     , DualNumberValue advals, vals ~ DValue advals )
  => (advals -> ADVal f r y) -> vals -> Maybe (f r y) -> vals
{-# INLINE crevDtMaybe #-}
crevDtMaybe f vals mdt =
  let g hVector = hVectorADValToADVal
                  $ toHVectorOf $ f $ parseHVector (fromDValue vals) hVector
      valsH = toHVectorOf vals
      mdth = toHVector @(Flip OR.Array) <$> mdt
  in parseHVector vals
     $ fst $ crevOnHVector mdth g valsH

{-# SPECIALIZE crevOnHVector
  :: Maybe (HVector (Flip OR.Array))
  -> (HVector (ADVal (Flip OR.Array))
  -> ADVal (HVectorPseudoTensor (Flip OR.Array)) Float '())
  -> HVector (Flip OR.Array)
  -> (HVector (Flip OR.Array), HVector (Flip OR.Array)) #-}


-- * Old derivative adaptors, with constant and fixed inputs

-- | This takes the sensitivity parameter, by convention.
cfwd
  :: forall r y f vals advals.
     ( RankedOf f ~ Flip OR.Array
     , AdaptableHVector (ADVal (Flip OR.Array)) advals
     , AdaptableHVector (ADVal (Flip OR.Array)) (ADVal f r y)
     , AdaptableHVector (Flip OR.Array) vals
     , AdaptableHVector (Flip OR.Array) (f r y)
     , DualNumberValue advals, vals ~ DValue advals )
  => (advals -> ADVal f r y) -> vals -> vals -> f r y
cfwd f vals ds =
  let g hVector = hVectorADValToADVal
                  $ toHVectorOf @(ADVal (Flip OR.Array))
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
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked PrimalSpan r n
  -> AstRanked PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (Flip OR.Array)
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}

{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped PrimalSpan r sh
  -> AstShaped PrimalSpan r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r)
  => AstEnv (Flip OR.Array)
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}

{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked PrimalSpan r n
  -> AstRanked PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked PrimalSpan Double n
  -> AstRanked PrimalSpan Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked PrimalSpan Float n
  -> AstRanked PrimalSpan Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked PrimalSpan Int64 n
  -> AstRanked PrimalSpan Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (Flip OR.Array)
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAstPrimalS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped PrimalSpan Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped PrimalSpan Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped PrimalSpan Int64 sh
  -> Flip OS.Array Int64 sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped PrimalSpan r sh
  -> AstShaped PrimalSpan r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped PrimalSpan Double sh
  -> AstShaped PrimalSpan Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped PrimalSpan Float sh
  -> AstShaped PrimalSpan Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped PrimalSpan Int64 sh
  -> AstShaped PrimalSpan Int64 sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (Flip OR.Array)
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array)
  -> AstShaped PrimalSpan Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array)
  -> AstShaped PrimalSpan Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array)
  -> AstShaped PrimalSpan Int64 sh
  -> Flip OS.Array Int64 sh #-}

{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked DualSpan r n
  -> DeltaR (Flip OR.Array) r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked DualSpan Double n
  -> DeltaR (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked DualSpan Float n
  -> DeltaR (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked DualSpan Int64 n
  -> DeltaR (Flip OR.Array) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked DualSpan r n
  -> DeltaR (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked DualSpan Double n
  -> DeltaR (AstRanked PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked DualSpan Float n
  -> DeltaR (AstRanked PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked DualSpan Int64 n
  -> DeltaR (AstRanked PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (Flip OR.Array)
  -> AstRanked DualSpan r n
  -> DummyDual r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked DualSpan Double n
  -> DummyDual Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked DualSpan Float n
  -> DummyDual Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array)
  -> AstRanked DualSpan Int64 n
  -> DummyDual Int64 n #-}

{-# SPECIALIZE interpretAstDualS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped DualSpan r sh
  -> DeltaS (Flip OS.Array) r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped DualSpan Double sh
  -> DeltaS (Flip OS.Array) Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped DualSpan Float sh
  -> DeltaS (Flip OS.Array) Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped DualSpan Int64 sh
  -> DeltaS (Flip OS.Array) Int64 sh #-}
{-# SPECIALIZE interpretAstDualS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped DualSpan r sh
  -> DeltaS (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped DualSpan Double sh
  -> DeltaS (AstShaped PrimalSpan) Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped DualSpan Float sh
  -> DeltaS (AstShaped PrimalSpan) Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped DualSpan Int64 sh
  -> DeltaS (AstShaped PrimalSpan) Int64 sh #-}
{-# SPECIALIZE interpretAstDualS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (Flip OR.Array)
  -> AstShaped DualSpan r sh
  -> DummyDual r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array)
  -> AstShaped DualSpan Double sh
  -> DummyDual Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array)
  -> AstShaped DualSpan Float sh
  -> DummyDual Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array)
  -> AstShaped DualSpan Int64 sh
  -> DummyDual Int64 sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked s r n
  -> ADVal (Flip OR.Array) r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked s r n
  -> ADVal (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstRanked s r n
  -> Flip OR.Array r n #-}

{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped s r sh
  -> ADVal (Flip OS.Array) r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped s r sh
  -> ADVal (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstShaped s r sh
  -> Flip OS.Array r sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked s r n
  -> ADVal (Flip OR.Array) r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked s Double n
  -> ADVal (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked s Float n
  -> ADVal (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstRanked s Int64 n
  -> ADVal (Flip OR.Array) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked s r n
  -> ADVal (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked s Double n
  -> ADVal (AstRanked PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked s Float n
  -> ADVal (AstRanked PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstRanked s Int64 n
  -> ADVal (AstRanked PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstRanked s r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstRanked s Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstRanked s Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstRanked s Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped s r sh
  -> ADVal (Flip OS.Array) r sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped s Double sh
  -> ADVal (Flip OS.Array) Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped s Float sh
  -> ADVal (Flip OS.Array) Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array))
  -> AstShaped s Int64 sh
  -> ADVal (Flip OS.Array) Int64 sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped s r sh
  -> ADVal (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped s Double sh
  -> ADVal (AstShaped PrimalSpan) Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped s Float sh
  -> ADVal (AstShaped PrimalSpan) Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstShaped s Int64 sh
  -> ADVal (AstShaped PrimalSpan) Int64 sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstShaped s r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstShaped s Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstShaped s Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array)
  -> AstShaped s Int64 sh
  -> Flip OS.Array Int64 sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstHVector
  :: AstSpan s
  => AstEnv (ADVal (Flip OR.Array))
  -> AstHVector s
  -> HVector (ADVal (Flip OR.Array)) #-}
{-# SPECIALIZE interpretAstHVector
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstHVector s
  -> HVector (ADVal (AstRanked PrimalSpan)) #-}
{-# SPECIALIZE interpretAstHVector
  :: AstSpan s
  => AstEnv (Flip OR.Array)
  -> AstHVector s
  -> HVector (Flip OR.Array) #-}
{-# SPECIALIZE interpretAstHVector
  :: AstSpan s
  => AstEnv (Flip OR.Array)
  -> AstHVector s
  -> HVector (Flip OR.Array) #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array))
  -> AstBool
  -> Bool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRanked PrimalSpan))
  -> AstBool
  -> AstBool #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array)
  -> AstBool
  -> Bool #-}
