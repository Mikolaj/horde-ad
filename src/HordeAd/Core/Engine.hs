{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and (forward) derivative
-- calculation for an objective function on values of complicated
-- types (e.g., with tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Optimizers are add-ons.
module HordeAd.Core.Engine
  ( -- * Reverse derivative adaptors
    rev, revDt, revArtifactAdapt
    -- * Forward derivative adaptors
  , fwd, fwdArtifactAdapt
    -- * Reverse and forward derivative stages class
  , DerivativeStages (..)
  , forwardPassByInterpretation, forwardPassByInterpretationS
  , forwardPassByApplication
    -- * Lower level functions related to reverse derivative stages
  , revArtifactFromForwardPass, revArtifactFromForwardPassS
    -- * Lower level functions related to forward derivative stages
  , fwdArtifactFromForwardPass, fwdArtifactFromForwardPassS
    -- * Old gradient adaptors, with constant and fixed inputs and dt
  , crev, crevDt, crevOnDomains, crevOnADInputs
    -- * Old derivative adaptors, with constant and fixed inputs
  , cfwd, cfwdOnDomains, cfwdOnADInputs
    -- * Additional common mechanisms
  , generateDeltaInputsOD, generateDeltaInputsAst, makeADInputs, shapedToRanked
    -- * Re-exported for tests
  , interpretAst
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Const
import           Data.Int (Int64)
import           Data.Maybe (fromMaybe, isJust)
import           Data.Proxy (Proxy)
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import           Type.Reflection (Typeable, typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInline
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstTools
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.TensorADVal ()
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.SizedIndex

-- * Reverse derivative adaptors

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names to @rev@, but newcomers may have trouble understanding them.

{- TODO: this is temporarily replaced by a workaround needed for the SPECIALIZE
   to work, #23798.
-- | These work for any @g@ of DerivativeStages class.
rev
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> g r y) -> vals -> vals
rev f vals = revDtMaybe f vals Nothing
{- TODO: RULE left-hand side too complicated to desugar
{-# SPECIALIZE rev
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> AstRanked FullSpan Double y) -> vals
  -> vals #-}
-}

-- | This version additionally takes the sensitivity parameter.
revDt
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> g r y) -> vals -> ConcreteOf g r y -> vals
revDt f vals dt = revDtMaybe f vals (Just dt)
{- TODO: RULE left-hand side too complicated to desugar
{-# SPECIALIZE revDt
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> AstRanked FullSpan Double y) -> vals -> Flip OR.Array Double y
  -> vals #-}
-}

revDtMaybe
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> g r y) -> vals -> Maybe (ConcreteOf g) r y) -> vals
{-# INLINE revDtMaybe #-}
revDtMaybe f vals mdt =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
      artifact = fst $ revProduceArtifact (isJust mdt) g EM.empty domainsOD
  in parseDomains vals
     $ fst $ revEvalArtifact artifact domainsOD mdt
-}

-- | These work for any @g@ of DerivativeStages class.
rev
  :: forall r y g astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => (astvals -> g r y) -> Value astvals -> Value astvals
rev f vals = revDtMaybe f vals Nothing
{-# SPECIALIZE rev
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => (astvals -> AstRanked FullSpan Double y) -> Value astvals
  -> Value astvals #-}

-- | This version additionally takes the sensitivity parameter.
revDt
  :: forall r y g astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => (astvals -> g r y) -> Value astvals -> ConcreteOf g r y
  -> Value astvals
revDt f vals dt = revDtMaybe f vals (Just dt)
{-# SPECIALIZE revDt
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => (astvals -> AstRanked FullSpan Double y) -> Value astvals
  -> Flip OR.Array Double y
  -> Value astvals #-}

revDtMaybe
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g r y) -> vals -> Maybe (ConcreteOf g r y) -> vals
{-# INLINE revDtMaybe #-}
revDtMaybe f vals mdt =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
      artifact = fst $ revProduceArtifact (isJust mdt) g EM.empty domainsOD
  in gcastWith (unsafeCoerce Refl :: Value vals :~: vals) $  -- !!!
     parseDomains vals
     $ fst $ revEvalArtifact artifact domainsOD mdt

revArtifactAdapt
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => Bool -> (astvals -> g r y) -> vals
  -> (AstArtifactRev (PrimalOf g) r y, Dual (PrimalOf g) r y)
revArtifactAdapt hasDt f vals =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
  in revProduceArtifact hasDt g EM.empty domainsOD
{-# SPECIALIZE revArtifactAdapt
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => Bool -> (astvals -> AstRanked FullSpan Double y) -> Value astvals
  -> ( AstArtifactRev (AstRanked PrimalSpan) Double y
     , Dual (AstRanked PrimalSpan) Double y ) #-}


-- * Forward derivative adaptors

-- | This takes the sensitivity parameter, by convention.
-- It uses the same delta expressions as for gradients.
--
-- Warning: this fails often with ranked tensor due to inability
-- to determine tensor shapes, see test testBarReluMax3Fwd.
-- Shaped tensors work fine.
fwd
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g r y) -> vals -> vals -> ConcreteOf g r y
fwd f x ds =
  let g domains = f $ parseDomains x domains
      domainsOD = toDomains x
      artifact = fst $ fwdProduceArtifact g EM.empty domainsOD
  in fst $ fwdEvalArtifact artifact domainsOD (toDomains ds)

fwdArtifactAdapt
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g r y) -> vals
  -> (AstArtifactFwd (PrimalOf g) r y, Dual (PrimalOf g) r y)
fwdArtifactAdapt f vals =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
  in fwdProduceArtifact g EM.empty domainsOD


-- * Reverse and forward derivative stages instances

-- TODO: it's not clear if the instance should be of Clown OD.Array or of
-- DomainsOD, for which we already have unletAstDomains6, etc.;
-- let's wait until we have rev as a function of Tensor class in case
-- that affects rev and/or Delta
--instance DerivativeStages @() (Clown OD.Array) where
--  revEvalArtifact = undefined
--  revProduceArtifact = undefined

instance DerivativeStages (AstRanked FullSpan) where
  {-# INLINE revProduceArtifact #-}
  revProduceArtifact hasDt g envInit =
    revArtifactFromForwardPass hasDt (forwardPassByInterpretation g envInit)

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varDt, vars), gradient, primal, sh) parameters mdt =
    let env = foldr extendEnvDR EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe (rreplicate0N (listShapeToShape sh) 1) mdt
        envDt = extendEnvR varDt dt env
        gradientDomain = interpretAstDomains envDt gradient
        primalTensor = interpretAstPrimal env primal
    in (gradientDomain, primalTensor)

  {-# INLINE fwdProduceArtifact #-}
  fwdProduceArtifact g envInit =
    fwdArtifactFromForwardPass (forwardPassByInterpretation g envInit)

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    if sameShapesDomainsOD parameters ds then
      let env = foldr extendEnvDR EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvDR env $ zip varDs $ V.toList ds
          derivativeTensor = interpretAstPrimal envDs derivative
          primalTensor = interpretAstPrimal @(Flip OR.Array) env primal
      in (derivativeTensor, primalTensor)
   else error "forward derivative input and sensitivity arguments should have same shapes"

instance DerivativeStages (AstShaped FullSpan) where
  {-# INLINE revProduceArtifact #-}
  revProduceArtifact hasDt g envInit =
    revArtifactFromForwardPassS hasDt (forwardPassByInterpretationS g envInit)

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varDt, vars), gradient, primal, _) parameters mdt =
    let env = foldr extendEnvDS EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe 1 mdt
        envDt = extendEnvS varDt dt env
        gradientDomain = interpretAstDomains envDt gradient
        primalTensor = interpretAstPrimalS env primal
    in (gradientDomain, primalTensor)

  {-# INLINE fwdProduceArtifact #-}
  fwdProduceArtifact g envInit =
    fwdArtifactFromForwardPassS (forwardPassByInterpretationS g envInit)

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    let env = foldr extendEnvDS EM.empty $ zip vars $ V.toList parameters
        envDs = foldr extendEnvDS env $ zip varDs $ V.toList ds
        derivativeTensor = interpretAstPrimalS envDs derivative
        primalTensor = interpretAstPrimalS @(Flip OR.Array) env primal
    in (derivativeTensor, primalTensor)

forwardPassByInterpretation
  :: (GoodScalar r, KnownNat n)
  => (Domains (AstDynamic FullSpan) -> AstRanked FullSpan r n)
  -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> Domains (AstDynamic PrimalSpan)
  -> [AstDynamicVarName (AstRanked FullSpan)]
  -> Domains (AstDynamic FullSpan)
  -> ADVal (AstRanked PrimalSpan) r n
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit domainsPrimal vars domains =
  let deltaInputs = generateDeltaInputsAst domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      ast = g domains
      env = foldr extendEnvDR envInit $ zip vars $ V.toList varInputs
  in interpretAst env ast

forwardPassByInterpretationS
  :: (GoodScalar r, OS.Shape sh)
  => (Domains (AstDynamic FullSpan) -> AstShaped FullSpan r sh)
  -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> Domains (AstDynamic PrimalSpan)
  -> [AstDynamicVarName (AstShaped FullSpan)]
  -> Domains (AstDynamic FullSpan)
  -> ADVal (AstShaped PrimalSpan) r sh
{-# INLINE forwardPassByInterpretationS #-}
forwardPassByInterpretationS g envInit domainsPrimal vars domains =
  let deltaInputs = generateDeltaInputsAst domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      ast = g domains
      env = foldr extendEnvDS envInit $ zip vars $ V.toList varInputs
  in interpretAstS env ast

forwardPassByApplication
  :: (Domains (ADValClown (AstDynamic PrimalSpan)) -> ADVal (PrimalOf g) r y)
  -> Domains (AstDynamic PrimalSpan)
  -> [AstDynamicVarName g]
  -> Domains (AstDynamic FullSpan)
  -> ADVal (PrimalOf g) r y
{-# INLINE forwardPassByApplication #-}
forwardPassByApplication g domainsPrimal _ _ =
  let deltaInputs = generateDeltaInputsAst domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
  in g varInputs


-- * Lower level functions related to reverse derivative stages

revArtifactFromForwardPass
  :: forall r n. (GoodScalar r, KnownNat n)
  => Bool
  -> (Domains (AstDynamic PrimalSpan)
      -> [AstDynamicVarName (AstRanked FullSpan)]
      -> Domains (AstDynamic FullSpan)
      -> ADVal (AstRanked PrimalSpan) r n)
  -> DomainsOD
  -> ( AstArtifactRev (AstRanked PrimalSpan) r n
     , Dual (AstRanked PrimalSpan) r n )
{-# INLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass hasDt forwardPass parameters0 =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varDtId, varsPrimal, domainsPrimal, vars, domains) =
        funToAstRev parameters0 in
  let -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
  let varDt = AstVarName varDtId
      sh = shapeAst primalBody
      astDt = AstVar sh varDt
      mdt = if hasDt then Just astDt else Nothing
      !(!astBindings, !gradient) =
        reverseDervative (V.length parameters0) primalBody mdt delta
  in ( ( (varDt, varsPrimal)
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6 [] l primalBody
       , shapeToList sh )
     , delta )
       -- storing sh computed from primalBody often saves the unletAst6
       -- execution; we could store the whole primalBody, as we do in calls
       -- to reverseDervative, but we can potentially free it earlier this way
       -- (as soon as sh is forced or determined to be unneeded)

revArtifactFromForwardPassS
  :: forall r sh. (GoodScalar r, OS.Shape sh)
  => Bool
  -> (Domains (AstDynamic PrimalSpan)
      -> [AstDynamicVarName (AstShaped FullSpan)]
      -> Domains (AstDynamic FullSpan)
      -> ADVal (AstShaped PrimalSpan) r sh)
  -> DomainsOD
  -> ( AstArtifactRev (AstShaped PrimalSpan) r sh
     , Dual (AstShaped PrimalSpan) r sh )
{-# INLINE revArtifactFromForwardPassS #-}
revArtifactFromForwardPassS hasDt forwardPass parameters0 =
  let !(!varDtId, varsPrimal, domainsPrimal, vars, domains) =
        funToAstRevS parameters0 in
  let !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
  let varDt = AstVarName varDtId
      astDt = AstVarS varDt
      mdt = if hasDt then Just astDt else Nothing
      !(!astBindings, !gradient) =
        reverseDervative (V.length parameters0) primalBody mdt delta
  in ( ( (varDt, varsPrimal)
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6S [] l primalBody
       , OS.shapeT @sh )
     , delta )


-- * Lower level functions related to forward derivative stages

fwdArtifactFromForwardPass
  :: forall r n. (GoodScalar r, KnownNat n)
  => (Domains (AstDynamic PrimalSpan)
      -> [AstDynamicVarName (AstRanked FullSpan)]
      -> Domains (AstDynamic FullSpan)
      -> ADVal (AstRanked PrimalSpan) r n)
  -> DomainsOD
  -> ( AstArtifactFwd (AstRanked PrimalSpan) r n
     , Dual (AstRanked PrimalSpan) r n )
{-# INLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass parameters0 =
  let !(!varsPrimalDs, domainsDs, varsPrimal, domainsPrimal, vars, domains) =
        funToAstFwd parameters0 in
  let !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
  let !(!astBindings, !derivative) =
        forwardDerivative (V.length parameters0) delta domainsDs
  in ( ( (varsPrimalDs, varsPrimal)
       , unletAst6 astBindings l derivative
       , unletAst6 []l primalBody )
     , delta )

fwdArtifactFromForwardPassS
  :: forall r sh. (GoodScalar r, OS.Shape sh)
  => (Domains (AstDynamic PrimalSpan)
      -> [AstDynamicVarName (AstShaped FullSpan)]
      -> Domains (AstDynamic FullSpan)
      -> ADVal (AstShaped PrimalSpan) r sh)
  -> DomainsOD
  -> ( AstArtifactFwd (AstShaped PrimalSpan) r sh
     , Dual (AstShaped PrimalSpan) r sh )
{-# INLINE fwdArtifactFromForwardPassS #-}
fwdArtifactFromForwardPassS forwardPass parameters0 =
  let !(!varsPrimalDs, domainsDs, varsPrimal, domainsPrimal, vars, domains) =
        funToAstFwdS parameters0 in
  let !(D l primalBody delta) = forwardPass domainsPrimal vars domains  in
  let !(!astBindings, !derivative) =
        forwardDerivative (V.length parameters0) delta domainsDs
  in ( ( (varsPrimalDs, varsPrimal)
       , unletAst6S astBindings l derivative
       , unletAst6S [] l primalBody )
     , delta )


-- * Old gradient adaptors, with constant and fixed inputs and dt

{- TODO: this is temporarily replaced by a workaround needed for the SPECIALIZE
   to work, #23798.
-- | The old versions that use the fixed input and @dt@ to compute gradient
-- only at these values, both transposing and evaluating at the same time.
--
-- These work for @f@ both ranked and shaped.
crev
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals, Value vals ~ vals )
  => (advals -> ADVal f r y) -> vals -> vals
crev f vals = crevDtMaybe f vals Nothing

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals, Value vals ~ vals )
  => (advals -> ADVal f r y) -> vals -> f r y -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals, Value vals ~ vals )
  => (advals -> ADVal f r y) -> vals -> Maybe (f r y) -> vals
{-# INLINE crevDtMaybe #-}
crevDtMaybe f vals mdt =
  let g inputs = f $ parseDomains vals inputs
  in parseDomains vals $ fst $ crevOnDomains mdt g (toDomains vals)
-}

-- | The old versions that use the fixed input and @dt@ to compute gradient
-- only at these values, both transposing and evaluating at the same time.
--
-- These work for @f@ both ranked and shaped.
crev
  :: forall r y f advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array (Value advals) )
  => (advals -> ADVal f r y) -> Value advals -> Value advals
crev f vals = crevDtMaybe f vals Nothing
{-# SPECIALIZE crev
  :: ( HasSingletonDict y
     , AdaptableDomains (DynamicOf (ADVal (Flip OR.Array))) advals
     , AdaptableDomains OD.Array (Value advals) )
  => (advals -> ADVal (Flip OR.Array) Double y)
  -> Value advals
  -> Value advals #-}

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array (Value advals) )
  => (advals -> ADVal f r y) -> Value advals -> f r y -> Value advals
crevDt f vals dt = crevDtMaybe f vals (Just dt)
{-# SPECIALIZE crevDt
  :: ( HasSingletonDict y
     , AdaptableDomains (DynamicOf (ADVal (Flip OR.Array))) advals
     , AdaptableDomains OD.Array (Value advals) )
  => (advals -> ADVal (Flip OR.Array) Double y)
  -> Value advals
  -> Flip OR.Array Double y
  -> Value advals #-}

crevDtMaybe
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> Maybe (f r y) -> vals
{-# INLINE crevDtMaybe #-}
crevDtMaybe f vals mdt =
  gcastWith (unsafeCoerce Refl :: Value vals :~: vals) $  -- !!!
  let g inputs = f $ parseDomains vals inputs
  in parseDomains vals $ fst $ crevOnDomains mdt g (toDomains vals)

crevOnDomains
  :: forall r y f.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array )
  => Maybe (f r y)
  -> (Domains (DynamicOf (ADVal f)) -> ADVal f r y)
  -> DomainsOD
  -> (DomainsOD, f r y)
crevOnDomains mdt f parameters =
  let deltaInputs = generateDeltaInputsOD parameters
      inputs = makeADInputs parameters deltaInputs
  in crevOnADInputs mdt f inputs
{-# SPECIALIZE crevOnDomains
  :: HasSingletonDict y
  => Maybe (Flip OR.Array Double y)
  -> (Domains (DynamicOf (ADVal (Flip OR.Array)))
      -> ADVal (Flip OR.Array) Double y)
  -> DomainsOD
  -> (DomainsOD, Flip OR.Array Double y) #-}

crevOnADInputs
  :: ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array )
  => Maybe (f r y)
  -> (Domains (DynamicOf (ADVal f)) -> ADVal f r y)
  -> Domains (DynamicOf (ADVal f))
  -> (DomainsOD, f r y)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D _ v deltaTopLevel) = f inputs in
  let (!astBindings, !gradient) =
        reverseDervative (V.length inputs) v mdt deltaTopLevel
  in assert (null astBindings)
       (gradient, v)
{-# SPECIALIZE crevOnADInputs
  :: HasSingletonDict y
  => Maybe (Flip OR.Array Double y)
  -> (Domains (DynamicOf (ADVal (Flip OR.Array)))
      -> ADVal (Flip OR.Array) Double y)
  -> Domains (DynamicOf (ADVal (Flip OR.Array)))
  -> (DomainsOD, Flip OR.Array Double y) #-}


-- * Old derivative adaptors, with constant and fixed inputs

-- | This takes the sensitivity parameter, by convention.
cfwd
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> vals
  -> f r y
cfwd f x ds =
  let g inputs = f $ parseDomains ds inputs
  in fst $ cfwdOnDomains (toDomains x) g (toDomains ds)

cfwdOnDomains
  :: ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array )
  => DomainsOD
  -> (Domains (DynamicOf (ADVal f)) -> ADVal f r y)
  -> DomainsOD
  -> (f r y, f r y)
cfwdOnDomains parameters f ds =
  let deltaInputs = generateDeltaInputsOD parameters
      inputs = makeADInputs parameters deltaInputs
  in cfwdOnADInputs inputs f ds

cfwdOnADInputs
  :: ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array )
  => Domains (DynamicOf (ADVal f))
  -> (Domains (DynamicOf (ADVal f)) -> ADVal f r y)
  -> DomainsOD
  -> (f r y, f r y)
{-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs inputs f ds =
  let !(D _ v deltaTopLevel) = f inputs in
  let (astBindings, derivative) =
        forwardDerivative (V.length inputs) deltaTopLevel ds
  in assert (null astBindings)
       (derivative, v)


-- * Additional common mechanisms

-- Actually, this is fully general, not only working for DomainsOD.
generateDeltaInputsOD
  :: forall ranked shaped dynamic.
     ( dynamic ~ DynamicOf ranked, ConvertTensor ranked shaped
     , Dual (Clown dynamic) ~ DeltaD ranked shaped )
  => Domains dynamic
  -> Domains (DualClown dynamic)
{-# INLINE generateDeltaInputsOD #-}
generateDeltaInputsOD params =
  let arrayToInput :: Int
                   -> DynamicExists dynamic
                   -> DynamicExists (DualClown dynamic)
      arrayToInput i (DynamicExists @r t) =
        let shl = dshape @ranked t
        in case someNatVal $ toInteger $ length shl of
          Just (SomeNat (_ :: Proxy n)) ->
            let sh = listShapeToShape shl
            in DynamicExists $ Flip $ RToD $ InputR @ranked @shaped @r @n
                                                    sh (toInputId i)
          Nothing -> error "generateDeltaInputs: impossible someNatVal error"
  in V.imap arrayToInput params
{- TODO: this can't be specified without a proxy, so we inline instead
{-# SPECIALIZE generateDeltaInputs
  :: DomainsOD -> Data.Vector.Vector (Dual OD.Array Double) #-}
-}

-- This is preferred for AstDynamic, because it results in shorter terms.
generateDeltaInputsAst
  :: forall ranked shaped dynamic.
     ( dynamic ~ AstDynamic PrimalSpan
     , Dual (Clown dynamic) ~ DeltaD ranked shaped )
  => Domains dynamic
  -> Domains (DualClown dynamic)
{-# INLINE generateDeltaInputsAst #-}
generateDeltaInputsAst params =
  let arrayToInput :: Int
                   -> DynamicExists dynamic
                   -> DynamicExists (DualClown dynamic)
      arrayToInput i (DynamicExists @r d) = case d of
        AstRToD @n w ->
          DynamicExists $ Flip $ RToD $ InputR @ranked @shaped @r @n
                                               (shapeAst w) (toInputId i)
        AstSToD @sh _w ->
          DynamicExists $ Flip $ SToD $ InputS @ranked @shaped @r @sh
                                               (toInputId i)
  in V.imap arrayToInput params
{- TODO: this can't be specified without a proxy, so we inline instead
{-# SPECIALIZE generateDeltaInputs
  :: DomainsOD -> Data.Vector.Vector (Dual OD.Array Double) #-}
-}

makeADInputs
  :: Domains dynamic
  -> Domains (DualClown dynamic)
  -> Domains (ADValClown dynamic)
{-# INLINE makeADInputs #-}
makeADInputs =
  V.zipWith (\(DynamicExists @r p)
              (DynamicExists @r2 d) ->
    case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> DynamicExists
                   $ Flip $ dDnotShared emptyADShare (Clown p) $ runFlip d
      _ -> error "makeADInputs: type mismatch")

shapedToRanked
  :: forall vals svals dynamic.
     ( dynamic ~ OD.Array, NoShape svals ~ vals, Value vals ~ vals
     , AdaptableDomains dynamic vals
     , AdaptableDomains dynamic svals, ForgetShape svals )
  => svals -> vals
shapedToRanked svals =
  parseDomains @dynamic (forgetShape svals) $ toDomains @dynamic svals




-- These and all other SPECIALIZE pragmas are needed due to the already
-- mostly fixed issues #21286 and others, because we want to have
-- reasonable performance on GHC 9.2 and 9.4 as well.
-- We need pragmas on shaped operations even for ranked benchmarks,
-- because threading the dictionaries through mutual recursive functions
-- would cause trouble.

{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan r n
  -> AstRanked PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}

{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (OS.Shape sh, Typeable r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (OS.Shape sh, Typeable r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan r sh
  -> AstShaped PrimalSpan r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (OS.Shape sh, Typeable r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}

{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan r n
  -> AstRanked PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Double n
  -> AstRanked PrimalSpan Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Float n
  -> AstRanked PrimalSpan Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Int64 n
  -> AstRanked PrimalSpan Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAstPrimalS
  :: (OS.Shape sh, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan Int64 sh
  -> Flip OS.Array Int64 sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: (OS.Shape sh, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan r sh
  -> AstShaped PrimalSpan r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan Double sh
  -> AstShaped PrimalSpan Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan Float sh
  -> AstShaped PrimalSpan Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan Int64 sh
  -> AstShaped PrimalSpan Int64 sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: (OS.Shape sh, GoodScalar r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: OS.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan Int64 sh
  -> Flip OS.Array Int64 sh #-}

{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan r n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Double n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Float n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Int64 n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan r n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Double n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Float n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Int64 n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan r n
  -> DummyDual r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Double n
  -> DummyDual Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Float n
  -> DummyDual Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Int64 n
  -> DummyDual Int64 n #-}

{-# SPECIALIZE interpretAstDualS
  :: (OS.Shape sh, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped DualSpan r sh
  -> Product (Clown (Const ADShare)) (DeltaS (Flip OR.Array) (Flip OS.Array)) r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped DualSpan Double sh
  -> Product (Clown (Const ADShare)) (DeltaS (Flip OR.Array) (Flip OS.Array)) Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped DualSpan Float sh
  -> Product (Clown (Const ADShare)) (DeltaS (Flip OR.Array) (Flip OS.Array)) Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped DualSpan Int64 sh
  -> Product (Clown (Const ADShare)) (DeltaS (Flip OR.Array) (Flip OS.Array)) Int64 sh #-}
{-# SPECIALIZE interpretAstDualS
  :: (OS.Shape sh, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped DualSpan r sh
  -> Product (Clown (Const ADShare)) (DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)) r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped DualSpan Double sh
  -> Product (Clown (Const ADShare)) (DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped DualSpan Float sh
  -> Product (Clown (Const ADShare)) (DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped DualSpan Int64 sh
  -> Product (Clown (Const ADShare)) (DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Int64 sh #-}
{-# SPECIALIZE interpretAstDualS
  :: (OS.Shape sh, GoodScalar r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped DualSpan r sh
  -> DummyDual r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped DualSpan Double sh
  -> DummyDual Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped DualSpan Float sh
  -> DummyDual Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: OS.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped DualSpan Int64 sh
  -> DummyDual Int64 sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s r n
  -> ADVal (Flip OR.Array) r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s r n
  -> ADVal (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s r n
  -> Flip OR.Array r n #-}

{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (OS.Shape sh, Typeable r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s r sh
  -> ADVal (Flip OS.Array) r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (OS.Shape sh, Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s r sh
  -> ADVal (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (OS.Shape sh, Typeable r, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s r sh
  -> Flip OS.Array r sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s r n
  -> ADVal (Flip OR.Array) r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s Double n
  -> ADVal (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s Float n
  -> ADVal (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s Int64 n
  -> ADVal (Flip OR.Array) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s r n
  -> ADVal (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s Double n
  -> ADVal (AstRanked PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s Float n
  -> ADVal (AstRanked PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s Int64 n
  -> ADVal (AstRanked PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s r sh
  -> ADVal (Flip OS.Array) r sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s Double sh
  -> ADVal (Flip OS.Array) Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s Float sh
  -> ADVal (Flip OS.Array) Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s Int64 sh
  -> ADVal (Flip OS.Array) Int64 sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s r sh
  -> ADVal (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s Double sh
  -> ADVal (AstShaped PrimalSpan) Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s Float sh
  -> ADVal (AstShaped PrimalSpan) Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s Int64 sh
  -> ADVal (AstShaped PrimalSpan) Int64 sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (OS.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s Int64 sh
  -> Flip OS.Array Int64 sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstDomains
  :: AstSpan s
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstDomains s
  -> Domains (ADValClown OD.Array) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstDomains s
  -> Domains (ADValClown (AstDynamic PrimalSpan)) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstSpan s
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstDomains s
  -> DomainsOD #-}
{-# SPECIALIZE interpretAstDomains
  :: AstSpan s
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstDomains s
  -> DomainsOD #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstBool
  -> (ADShare, Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstBool
  -> (ADShare, AstBool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstBool
  -> (ADShare, Bool) #-}
