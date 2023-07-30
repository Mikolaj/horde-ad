-- | The implementation of reverse derivative and derivative calculation
-- for an objective function on values of complicated types (e.g., with
-- tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Optimizers are add-ons.
module HordeAd.Core.Engine
  ( -- * Reverse derivative adaptors
    rev, revDt
  , Adaptable (..)
    -- * Lower level function related to reverse derivative adaptors
  , revDtFun, revAstOnDomainsFun
    -- * Forward derivative adaptors
  , fwd
    -- * Lower level function related to forward derivative adaptors
  , fwdDtFun, fwdAstOnDomainsFun
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

-- These work for g of Adaptable class.
rev
  :: forall r y g vals astvals.
     ( Adaptable g, GoodScalar r, HasSingletonDict y
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

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r y g vals astvals.
     ( Adaptable g, GoodScalar r, HasSingletonDict y
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
     ( Adaptable g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> g FullSpan r y) -> vals -> Maybe (ConcreteOf g r y) -> vals
{-# INLINE revDtMaybe #-}
revDtMaybe f vals mdt =
  let asts4 = fst $ revDtFun (isJust mdt) f vals
  in parseDomains (toValue vals)
     $ fst $ revAstOnDomainsEval asts4 (toDomains vals) mdt

type Adaptable :: forall k. (AstSpanType -> TensorKind k) -> Constraint
class Adaptable g where
  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, HasSingletonDict y
       , AdaptableDomains (AstDynamic FullSpan) astvals, vals ~ Value astvals )
    => Bool -> (astvals -> g FullSpan r y) -> vals
    -> AstEnv (ADVal (RankedOf (g PrimalSpan)))
              (ADVal (ShapedOf (g PrimalSpan)))
    -> DomainsOD
    -> (AstArtifactRev g r y, Dual (g PrimalSpan) r y)

  revAstOnDomainsEval
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => AstArtifactRev g r y -> DomainsOD -> Maybe (ConcreteOf g r y)
    -> (DomainsOD, ConcreteOf g r y)

  fwdDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, HasSingletonDict y
       , AdaptableDomains (AstDynamic FullSpan) astvals, vals ~ Value astvals )
    => (astvals -> g FullSpan r y) -> vals
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
--instance Adaptable @() (Clown OD.Array) where
--  revAstOnDomainsEval = undefined
--  revDtInit = undefined

instance Adaptable AstRanked where
  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, KnownNat y
       , AdaptableDomains (AstDynamic FullSpan) astvals, vals ~ Value astvals )
    => Bool -> (astvals -> AstRanked FullSpan r y) -> vals
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> DomainsOD
    -> (AstArtifactRev AstRanked r y, Dual (AstRanked PrimalSpan) r y)
  {-# INLINE revDtInit #-}
  revDtInit hasDt f vals envInit parameters0 =
    let revDtInterpret :: Domains (ADValClown (AstDynamic PrimalSpan))
                       -> Domains (AstDynamic FullSpan)
                       -> [AstDynamicVarName FullSpan AstRanked]
                       -> ADVal (AstRanked PrimalSpan) r y
        revDtInterpret varInputs domains vars =
          let ast = f $ parseDomains vals domains
              env = foldr extendEnvDR envInit $ zip vars $ V.toList varInputs
          in interpretAst env ast
    in revAstOnDomainsFun hasDt parameters0 revDtInterpret

  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars), gradient, primal) parameters mdt =
    let env = foldr extendEnvDR EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe (treplicate0N (tshape primal) 1) mdt
        envDt = extendEnvR varDt dt env
        gradientDomain = interpretAstDomainsDummy envDt gradient
        primalTensor = interpretAstPrimal env primal
    in (gradientDomain, primalTensor)

  fwdDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, HasSingletonDict y
       , AdaptableDomains (AstDynamic FullSpan) astvals, vals ~ Value astvals )
    => (astvals -> AstRanked FullSpan r y) -> vals
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> DomainsOD
    -> (AstArtifactFwd AstRanked r y, Dual (AstRanked PrimalSpan) r y)
  {-# INLINE fwdDtInit #-}
  fwdDtInit f vals envInit parameters0 =
    let revDtInterpret :: Domains (ADValClown (AstDynamic PrimalSpan))
                       -> Domains (AstDynamic FullSpan)
                       -> [AstDynamicVarName FullSpan AstRanked]
                       -> ADVal (AstRanked PrimalSpan) r y
        revDtInterpret varInputs domains vars =
          let ast = f $ parseDomains vals domains
              env = foldr extendEnvDR envInit $ zip vars $ V.toList varInputs
          in interpretAst env ast
    in fwdAstOnDomainsFun parameters0 revDtInterpret

  {-# INLINE fwdAstOnDomainsEval #-}
  fwdAstOnDomainsEval ((varDs, vars), derivative, primal) parameters ds =
    if sameShapesDomainsOD parameters ds then
      let env = foldr extendEnvDR EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvDR env $ zip varDs $ V.toList ds
          derivativeTensor = interpretAstPrimal envDs derivative
          primalTensor = interpretAstPrimal @(Flip OR.Array) env primal
      in (derivativeTensor, primalTensor)
   else error "forward derivative input and sensitivity arguments should have same shapes"

instance Adaptable AstShaped where
  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, OS.Shape y
       , AdaptableDomains (AstDynamic FullSpan) astvals, vals ~ Value astvals )
    => Bool -> (astvals -> AstShaped FullSpan r y) -> vals
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> DomainsOD
    -> (AstArtifactRev AstShaped r y, Dual (AstShaped PrimalSpan) r y)
  {-# INLINE revDtInit #-}
  revDtInit hasDt f vals envInit parameters0 =
    let revDtInterpret :: Domains (ADValClown (AstDynamic PrimalSpan))
                       -> Domains (AstDynamic FullSpan)
                       -> [AstDynamicVarName FullSpan AstShaped]
                       -> ADVal (AstShaped PrimalSpan) r y
        revDtInterpret varInputs domains vars =
          let ast = f $ parseDomains vals domains
              env = foldr extendEnvDS envInit $ zip vars $ V.toList varInputs
          in interpretAstS env ast
    in revAstOnDomainsFunS hasDt parameters0 revDtInterpret

  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars), gradient, primal) parameters mdt =
    let env = foldr extendEnvDS EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe 1 mdt
        envDt = extendEnvS varDt dt env
        gradientDomain = interpretAstDomainsDummy envDt gradient
        primalTensor = interpretAstPrimalS env primal
    in (gradientDomain, primalTensor)

  fwdDtInit = undefined  -- TODO

  fwdAstOnDomainsEval = undefined  -- TODO


-- * Lower level function related to reverse derivative adaptors

revDtFun
  :: forall r y g vals astvals.
     ( Adaptable g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => Bool -> (astvals -> g FullSpan r y) -> vals
  -> (AstArtifactRev g r y, Dual (g PrimalSpan) r y)
{-# INLINE revDtFun #-}
revDtFun hasDt f vals = revDtInit hasDt f vals EM.empty (toDomains vals)

revAstOnDomainsFun
  :: forall r n. (GoodScalar r, KnownNat n)
  => Bool -> DomainsOD
  -> (Domains (ADValClown (AstDynamic PrimalSpan))
      -> Domains (AstDynamic FullSpan)
      -> [AstDynamicVarName FullSpan AstRanked]
      -> ADVal (AstRanked PrimalSpan) r n)
  -> (AstArtifactRev AstRanked r n, Dual (AstRanked PrimalSpan) r n)
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun hasDt parameters0 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varDtId, varsPrimal, astsPrimal, vars, asts) =
        funToAstRev parameters0 in
  let domains = V.fromList asts
      domainsPrimal = V.fromList astsPrimal
      deltaInputs = generateDeltaInputs domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = f varInputs domains vars in
  let varDt = AstVarName varDtId
      astDt = AstVar (tshape primalBody) varDt
      mdt = if hasDt then Just astDt else Nothing
      !(!astBindings, !gradient) =
        reverseDervative (V.length parameters0) primalBody mdt deltaTopLevel
  in ( ( (varDt, varsPrimal)
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6 l primalBody )
     , deltaTopLevel )

revAstOnDomainsFunS
  :: forall r sh. (GoodScalar r, OS.Shape sh)
  => Bool -> DomainsOD
  -> (Domains (ADValClown (AstDynamic PrimalSpan))
      -> Domains (AstDynamic FullSpan)
      -> [AstDynamicVarName FullSpan AstShaped]
      -> ADVal (AstShaped PrimalSpan) r sh)
  -> (AstArtifactRev AstShaped r sh, Dual (AstShaped PrimalSpan) r sh)
{-# INLINE revAstOnDomainsFunS #-}
revAstOnDomainsFunS hasDt parameters0 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varDtId, varsPrimal, astsPrimal, vars, asts) =
        funToAstRevS parameters0 in
  let domains = V.fromList asts
      domainsPrimal = V.fromList astsPrimal
      deltaInputs = generateDeltaInputs domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = f varInputs domains vars in
  let varDt = AstVarName varDtId
      astDt = AstVarS varDt
      mdt = if hasDt then Just astDt else Nothing
      !(!astBindings, !gradient) =
        reverseDervative (V.length parameters0) primalBody mdt deltaTopLevel
  in ( ( (varDt, varsPrimal)
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6S l primalBody )
     , deltaTopLevel )


-- * Forward derivative adaptors

-- This takes the sensitivity parameter, by convention.
-- It uses the same delta expressions as for gradients.
fwd
  :: forall r y g vals astvals.
     ( Adaptable g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g FullSpan r y) -> vals -> vals
  -> ConcreteOf g r y
fwd f x ds =
  let asts4 = fst $ fwdDtFun f x
  in fst $ fwdAstOnDomainsEval asts4 (toDomains x) (toDomains ds)


-- * Lower level function related to forward derivative adaptors

fwdDtFun
  :: forall r y g vals astvals.
     ( Adaptable g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g FullSpan r y) -> vals
  -> (AstArtifactFwd g r y, Dual (g PrimalSpan) r y)
{-# INLINE fwdDtFun #-}
fwdDtFun f vals = fwdDtInit f vals EM.empty (toDomains vals)

fwdAstOnDomainsFun
  :: forall r n. (GoodScalar r, KnownNat n)
  => DomainsOD
  -> (Domains (ADValClown (AstDynamic PrimalSpan))
      -> Domains (AstDynamic FullSpan)
      -> [AstDynamicVarName FullSpan AstRanked]
      -> ADVal (AstRanked PrimalSpan) r n)
  -> (AstArtifactFwd AstRanked r n, Dual (AstRanked PrimalSpan) r n)
{-# INLINE fwdAstOnDomainsFun #-}
fwdAstOnDomainsFun parameters0 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varsPrimalDs, astsPrimalDs, varsPrimal, astsPrimal, vars, asts) =
        funToAstFwd parameters0 in
  let domains = V.fromList asts
      domainsPrimal = V.fromList astsPrimal
      deltaInputs = generateDeltaInputs domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = f varInputs domains vars in
  let astDs = V.fromList astsPrimalDs
      !derivative = forwardDerivative (V.length parameters0) deltaTopLevel astDs
  in ( ( (varsPrimalDs, varsPrimal)
       , unletAst6 l derivative
       , unletAst6 l primalBody )
     , deltaTopLevel )


-- * Old gradient adaptors, with constant and fixed inputs and dt

-- These work for f both ranked and shaped.
crev
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
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

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
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

-- The old versions that use the fixed input and dt to compute gradient
-- only at these values, both transposing and evaluating at the same time.
-- These work for f both ranked and shaped.
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
     $ (gradient, v)


-- * Old derivative adaptors, with constant and fixed inputs

-- This takes the sensitivity parameter, by convention.
-- It uses the same delta expressions as for gradients.
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
