-- | The implementation of reverse derivative and (forward) derivative
-- calculation for an objective function on values of complicated
-- types (e.g., with tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Optimizers are add-ons.
module HordeAd.Core.Engine
  ( -- * Reverse derivative adaptors
    rev, revDt, revDtFun
    -- * Forward derivative adaptors
  , fwd, fwdDtFun
    -- * Reverse and forward derivative stages class
  , DerivativeStages (..)
    -- * Lower level functions related to reverse derivative stages
  , revAstOnDomainsFun, revAstOnDomainsFunS
    -- * Lower level functions related to forward derivative stages
  , fwdAstOnDomainsFun, fwdAstOnDomainsFunS
    -- * Old gradient adaptors, with constant and fixed inputs and dt
  , crev, crevDt, crevOnDomains, crevOnADInputs
    -- * Old derivative adaptors, with constant and fixed inputs
  , cfwd, cfwdOnDomains, cfwdOnADInputs
    -- * Additional common mechanisms
  , generateDeltaInputs, makeADInputs, shapedToRanked
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Kind (Constraint)
import           Data.Maybe (fromMaybe, isJust)
import           Data.Proxy (Proxy)
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import           Type.Reflection (typeRep)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInline
import HordeAd.Core.AstInterpret
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

-- * Reverse derivative adaptors

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names to @rev@, but newcomers may have trouble understanding them.

-- | These work for any @g@ of DerivativeStages class.
rev
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> g FullSpan r y) -> vals -> vals
rev f vals = revDtMaybe f vals Nothing
{- TODO: check with GHC 9.6.3: RULE left-hand side too complicated to desugar
{-# SPECIALIZE rev
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> AstRanked FullSpan Double y) -> vals
  -> vals #-}
-}

-- | This version additionally takes the sensitivity parameter.
revDt
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> g FullSpan r y) -> vals -> ConcreteOf g r y -> vals
revDt f vals dt = revDtMaybe f vals (Just dt)
{- TODO: check with GHC 9.6.3: RULE left-hand side too complicated to desugar
{-# SPECIALIZE revDt
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> AstRanked FullSpan Double y) -> vals -> Flip OR.Array Double y
  -> vals #-}
-}

revDtMaybe
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> g FullSpan r y) -> vals -> Maybe (ConcreteOf g r y) -> vals
{-# INLINE revDtMaybe #-}
revDtMaybe f vals mdt =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
      artifact = fst $ revDtInit (isJust mdt) g EM.empty domainsOD
  in parseDomains (toValue vals)
     $ fst $ revAstOnDomainsEval artifact domainsOD mdt

revDtFun
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => Bool -> (astvals -> g FullSpan r y) -> vals
  -> (AstArtifactRev g r y, Dual (g PrimalSpan) r y)
{-# INLINE revDtFun #-}
revDtFun hasDt f vals =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
  in revDtInit hasDt g EM.empty domainsOD


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
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g FullSpan r y) -> vals -> vals -> ConcreteOf g r y
fwd f x ds =
  let g domains = f $ parseDomains x domains
      domainsOD = toDomains x
      artifact = fst $ fwdDtInit g EM.empty domainsOD
  in fst $ fwdAstOnDomainsEval artifact domainsOD (toDomains ds)

fwdDtFun
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g FullSpan r y) -> vals
  -> (AstArtifactFwd g r y, Dual (g PrimalSpan) r y)
{-# INLINE fwdDtFun #-}
fwdDtFun f vals =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
  in fwdDtInit g EM.empty domainsOD


-- * Reverse and forward derivative stages class

type DerivativeStages :: forall k. (AstSpanType -> TensorKind k) -> Constraint
class DerivativeStages g where
  revDtInit
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => Bool
    -> (Domains (AstDynamic FullSpan) -> g FullSpan r y)
    -> AstEnv (ADVal (RankedOf (g PrimalSpan)))
              (ADVal (ShapedOf (g PrimalSpan)))
    -> DomainsOD
    -> (AstArtifactRev g r y, Dual (g PrimalSpan) r y)

  revAstOnDomainsEval
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => AstArtifactRev g r y -> DomainsOD -> Maybe (ConcreteOf g r y)
    -> (DomainsOD, ConcreteOf g r y)

  fwdDtInit
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => (Domains (AstDynamic FullSpan) -> g FullSpan r y)
    -> AstEnv (ADVal (RankedOf (g PrimalSpan)))
              (ADVal (ShapedOf (g PrimalSpan)))
    -> DomainsOD
    -> (AstArtifactFwd g r y, Dual (g PrimalSpan) r y)

  fwdAstOnDomainsEval
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => AstArtifactFwd g r y -> DomainsOD -> DomainsOD
    -> (ConcreteOf g r y, ConcreteOf g r y)


-- TODO: it's not clear if the instance should be of Clown OD.Array or of
-- DomainsOD, for which we already have unletAstDomains6, etc.;
-- let's wait until we have rev as a function of Tensor class in case
-- that affects rev and/or Delta
--instance DerivativeStages @() (Clown OD.Array) where
--  revAstOnDomainsEval = undefined
--  revDtInit = undefined

instance DerivativeStages AstRanked where
  {-# INLINE revDtInit #-}
  revDtInit hasDt g envInit =
    revAstOnDomainsFun hasDt (forwardPassByInterpretation g envInit)

  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars), gradient, primal) parameters mdt =
    let env = foldr extendEnvDR EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe (treplicate0N (tshape primal) 1) mdt
        envDt = extendEnvR varDt dt env
        gradientDomain = interpretAstDomainsDummy envDt gradient
        primalTensor = interpretAstPrimal env primal
    in (gradientDomain, primalTensor)

  {-# INLINE fwdDtInit #-}
  fwdDtInit g envInit =
    fwdAstOnDomainsFun (forwardPassByInterpretation g envInit)

  {-# INLINE fwdAstOnDomainsEval #-}
  fwdAstOnDomainsEval ((varDs, vars), derivative, primal) parameters ds =
    if sameShapesDomainsOD parameters ds then
      let env = foldr extendEnvDR EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvDR env $ zip varDs $ V.toList ds
          derivativeTensor = interpretAstPrimal envDs derivative
          primalTensor = interpretAstPrimal @(Flip OR.Array) env primal
      in (derivativeTensor, primalTensor)
   else error "forward derivative input and sensitivity arguments should have same shapes"

instance DerivativeStages AstShaped where
  {-# INLINE revDtInit #-}
  revDtInit hasDt g envInit =
    revAstOnDomainsFunS hasDt (forwardPassByInterpretationS g envInit)

  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars), gradient, primal) parameters mdt =
    let env = foldr extendEnvDS EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe 1 mdt
        envDt = extendEnvS varDt dt env
        gradientDomain = interpretAstDomainsDummy envDt gradient
        primalTensor = interpretAstPrimalS env primal
    in (gradientDomain, primalTensor)

  {-# INLINE fwdDtInit #-}
  fwdDtInit g envInit =
    fwdAstOnDomainsFunS (forwardPassByInterpretationS g envInit)

  {-# INLINE fwdAstOnDomainsEval #-}
  fwdAstOnDomainsEval ((varDs, vars), derivative, primal) parameters ds =
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
  -> [AstDynamicVarName FullSpan AstRanked]
  -> Domains (AstDynamic FullSpan)
  -> ADVal (AstRanked PrimalSpan) r n
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit domainsPrimal vars domains =
  let deltaInputs = generateDeltaInputs domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      ast = g domains
      env = foldr extendEnvDR envInit $ zip vars $ V.toList varInputs
  in interpretAst env ast

forwardPassByInterpretationS
  :: (GoodScalar r, OS.Shape sh)
  => (Domains (AstDynamic FullSpan) -> AstShaped FullSpan r sh)
  -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> Domains (AstDynamic PrimalSpan)
  -> [AstDynamicVarName FullSpan AstShaped]
  -> Domains (AstDynamic FullSpan)
  -> ADVal (AstShaped PrimalSpan) r sh
{-# INLINE forwardPassByInterpretationS #-}
forwardPassByInterpretationS g envInit domainsPrimal vars domains =
  let deltaInputs = generateDeltaInputs domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      ast = g domains
      env = foldr extendEnvDS envInit $ zip vars $ V.toList varInputs
  in interpretAstS env ast


-- * Lower level functions related to reverse derivative stages

revAstOnDomainsFun
  :: forall r n. (GoodScalar r, KnownNat n)
  => Bool
  -> (Domains (AstDynamic PrimalSpan)
      -> [AstDynamicVarName FullSpan AstRanked]
      -> Domains (AstDynamic FullSpan)
      -> ADVal (AstRanked PrimalSpan) r n)
  -> DomainsOD
  -> (AstArtifactRev AstRanked r n, Dual (AstRanked PrimalSpan) r n)
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun hasDt forwardPass parameters0 =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varDtId, varsPrimal, domainsPrimal, vars, domains) =
        funToAstRev parameters0 in
  let -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
  let varDt = AstVarName varDtId
      astDt = AstVar (tshape primalBody) varDt
      mdt = if hasDt then Just astDt else Nothing
      !(!astBindings, !gradient) =
        reverseDervative (V.length parameters0) primalBody mdt delta
  in ( ( (varDt, varsPrimal)
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6 l primalBody )
     , delta )

revAstOnDomainsFunS
  :: forall r sh. (GoodScalar r, OS.Shape sh)
  => Bool
  -> (Domains (AstDynamic PrimalSpan)
      -> [AstDynamicVarName FullSpan AstShaped]
      -> Domains (AstDynamic FullSpan)
      -> ADVal (AstShaped PrimalSpan) r sh)
  -> DomainsOD
  -> (AstArtifactRev AstShaped r sh, Dual (AstShaped PrimalSpan) r sh)
{-# INLINE revAstOnDomainsFunS #-}
revAstOnDomainsFunS hasDt forwardPass parameters0 =
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
       , unletAst6S l primalBody )
     , delta )


-- * Lower level functions related to forward derivative stages

fwdAstOnDomainsFun
  :: forall r n. (GoodScalar r, KnownNat n)
  => (Domains (AstDynamic PrimalSpan)
      -> [AstDynamicVarName FullSpan AstRanked]
      -> Domains (AstDynamic FullSpan)
      -> ADVal (AstRanked PrimalSpan) r n)
  -> DomainsOD
  -> (AstArtifactFwd AstRanked r n, Dual (AstRanked PrimalSpan) r n)
{-# INLINE fwdAstOnDomainsFun #-}
fwdAstOnDomainsFun forwardPass parameters0 =
  let !(!varsPrimalDs, domainsDs, varsPrimal, domainsPrimal, vars, domains) =
        funToAstFwd parameters0 in
  let !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
  let !derivative =
        forwardDerivative (V.length parameters0) delta domainsDs
  in ( ( (varsPrimalDs, varsPrimal)
       , unletAst6 l derivative
       , unletAst6 l primalBody )
     , delta )

fwdAstOnDomainsFunS
  :: forall r sh. (GoodScalar r, OS.Shape sh)
  => (Domains (AstDynamic PrimalSpan)
      -> [AstDynamicVarName FullSpan AstShaped]
      -> Domains (AstDynamic FullSpan)
      -> ADVal (AstShaped PrimalSpan) r sh)
  -> DomainsOD
  -> (AstArtifactFwd AstShaped r sh, Dual (AstShaped PrimalSpan) r sh)
{-# INLINE fwdAstOnDomainsFunS #-}
fwdAstOnDomainsFunS forwardPass parameters0 =
  let !(!varsPrimalDs, domainsDs, varsPrimal, domainsPrimal, vars, domains) =
        funToAstFwdS parameters0 in
  let !(D l primalBody delta) = forwardPass domainsPrimal vars domains  in
  let !derivative =
        forwardDerivative (V.length parameters0) delta domainsDs
  in ( ( (varsPrimalDs, varsPrimal)
       , unletAst6S l derivative
       , unletAst6S l primalBody )
     , delta )


-- * Old gradient adaptors, with constant and fixed inputs and dt

-- | The old versions that use the fixed input and @dt@ to compute gradient
-- only at these values, both transposing and evaluating at the same time.
--
-- These work for @f@ both ranked and shaped.
crev
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> vals
crev f vals = crevDtMaybe f vals Nothing

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> f r y -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> Maybe (f r y) -> vals
crevDtMaybe f vals dt =
  let g inputs = f $ parseDomains vals inputs
  in parseDomains (toValue vals) $ fst $ crevOnDomains dt g (toDomains vals)

crevOnDomains
  :: ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array )
  => Maybe (f r y)
  -> (Domains (DynamicOf (ADVal f)) -> ADVal f r y)
  -> DomainsOD
  -> (DomainsOD, f r y)
crevOnDomains dt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in crevOnADInputs dt f inputs

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
  let (astBindings, gradient) =
        reverseDervative (V.length inputs) v mdt deltaTopLevel
  in assert (null astBindings)
       (gradient, v)


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
  let deltaInputs = generateDeltaInputs parameters
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
  let derivative = forwardDerivative (V.length inputs) deltaTopLevel ds
  in (derivative, v)


-- * Additional common mechanisms

type DualClown dynamic = Flip (Dual (Clown dynamic)) '()

generateDeltaInputs
  :: forall ranked shaped dynamic.
     ( dynamic ~ DynamicOf ranked, ConvertTensor ranked shaped
     , Dual (Clown dynamic) ~ DeltaD ranked shaped )
  => Domains dynamic
  -> Domains (DualClown dynamic)
{-# INLINE generateDeltaInputs #-}
generateDeltaInputs params =
  let arrayToInput :: Int
                   -> DynamicExists dynamic
                   -> DynamicExists (DualClown dynamic)
      arrayToInput i (DynamicExists @r t) =
        case someNatVal $ toInteger $ length $ dshape @ranked t of
          Just (SomeNat (_ :: Proxy n)) ->
            DynamicExists $ Flip $ RToD $ InputR @ranked @shaped @r @n
                                 $ toInputId i
          Nothing -> error "generateDeltaInputs: impossible someNatVal error"
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
     ( dynamic ~ OD.Array, Value svals ~ vals, Value vals ~ vals
     , AdaptableDomains dynamic vals
     , AdaptableDomains dynamic svals, RandomDomains svals )
  => svals -> vals
shapedToRanked svals =
  parseDomains @dynamic (toValue svals) $ toDomains @dynamic svals
