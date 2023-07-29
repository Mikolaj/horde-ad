-- | The implementation of calculating gradient and derivative
-- of an objective function expressed wtih the `Tensor` class.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Adaptors, optimizers, etc.,
-- are add-ons.
module HordeAd.Core.Engine
  ( rev, revDt
  , Adaptable (..)
  , revDtFun, revAstOnDomainsFun
  , crev, crevDt, crevOnDomains, crevOnADInputs
  , cfwd, cfwdOnDomains, cfwdOnADInputs
  , generateDeltaInputs, makeADInputs, shapedToRanked
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.DynamicS as OD
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

-- * Gradient adaptors

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
  revAstOnDomainsEval
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => ADAstArtifact6 (g PrimalSpan) r y -> Domains OD.Array
    -> Maybe (ConcreteOf g r y)
    -> (Domains OD.Array, ConcreteOf g r y)

  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, HasSingletonDict y
       , AdaptableDomains (AstDynamic FullSpan) astvals, vals ~ Value astvals )
    => Bool -> (astvals -> g FullSpan r y) -> vals
    -> AstEnv (ADVal (RankedOf (g PrimalSpan)))
              (ADVal (ShapedOf (g PrimalSpan)))
    -> DomainsOD
    -> (ADAstArtifact6 (g PrimalSpan) r y, Dual (g PrimalSpan) r y)

-- TODO: it's not clear if the instance should be of Clown OD.Array or of
-- Domains OD.Array, for which we already have unletAstDomains6, etc.;
-- let's wait until we have rev as a function of Tensor class in case
-- that affects rev and/or Delta
--instance Adaptable @() (Clown OD.Array) where
--  revAstOnDomainsEval = undefined
--  revDtInit = undefined

instance Adaptable AstRanked where
  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars1), gradient, primal) parameters mdt =
    let env1 = foldr extendEnvDR EM.empty $ zip vars1 $ V.toList parameters
        dt = fromMaybe (treplicate0N (tshape primal) 1) mdt
        envDt = extendEnvR varDt dt env1
        gradientDomain = interpretAstDomainsDummy envDt gradient
        primalTensor = interpretAstPrimal env1 primal
    in (gradientDomain, primalTensor)

  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, KnownNat y
       , AdaptableDomains (AstDynamic FullSpan) astvals, vals ~ Value astvals )
    => Bool -> (astvals -> AstRanked FullSpan r y) -> vals
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> DomainsOD
    -> ( ADAstArtifact6 (AstRanked PrimalSpan) r y
       , Dual (AstRanked PrimalSpan) r y )
  {-# INLINE revDtInit #-}
  revDtInit hasDt f vals envInit parameters0 =
    let revDtInterpret :: Domains (ADValClown (AstDynamic PrimalSpan))
                       -> Domains (AstDynamic FullSpan)
                       -> [AstDynamicVarName PrimalSpan (AstRanked PrimalSpan)]
                       -> ADVal (AstRanked PrimalSpan) r y
        revDtInterpret varInputs domains vars1 =
          let ast = f $ parseDomains vals domains
              env1 = foldr extendEnvDR envInit $ zip vars1 $ V.toList varInputs
          in interpretAst env1 ast
    in revAstOnDomainsFun hasDt parameters0 revDtInterpret

instance Adaptable AstShaped where
  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars1), gradient, primal) parameters mdt =
    let env1 = foldr extendEnvDS EM.empty $ zip vars1 $ V.toList parameters
        dt = fromMaybe 1 mdt
        envDt = extendEnvS varDt dt env1
        gradientDomain = interpretAstDomainsDummy envDt gradient
        primalTensor = interpretAstPrimalS env1 primal
    in (gradientDomain, primalTensor)

  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, OS.Shape y
       , AdaptableDomains (AstDynamic FullSpan) astvals, vals ~ Value astvals )
    => Bool -> (astvals -> AstShaped FullSpan r y) -> vals
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> DomainsOD
    -> ( ADAstArtifact6 (AstShaped PrimalSpan) r y
       , Dual (AstShaped PrimalSpan) r y )
  {-# INLINE revDtInit #-}
  revDtInit hasDt f vals envInit parameters0 =
    let revDtInterpret :: Domains (ADValClown (AstDynamic PrimalSpan))
                       -> Domains (AstDynamic FullSpan)
                       -> [AstDynamicVarName PrimalSpan (AstShaped PrimalSpan)]
                       -> ADVal (AstShaped PrimalSpan) r y
        revDtInterpret varInputs domains vars1 =
          let ast = f $ parseDomains vals domains
              env1 = foldr extendEnvDS envInit $ zip vars1 $ V.toList varInputs
          in interpretAstS env1 ast
    in revAstOnDomainsFunS hasDt parameters0 revDtInterpret

revDtFun
  :: forall r y g vals astvals.
     ( Adaptable g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => Bool -> (astvals -> g FullSpan r y) -> vals
  -> (ADAstArtifact6 (g PrimalSpan) r y, Dual (g PrimalSpan) r y)
{-# INLINE revDtFun #-}
revDtFun hasDt f vals = revDtInit hasDt f vals EM.empty (toDomains vals)

revAstOnDomainsFun
  :: forall r n. (KnownNat n, GoodScalar r)
  => Bool -> DomainsOD
  -> (Domains (ADValClown (AstDynamic PrimalSpan))
      -> Domains (AstDynamic FullSpan)
      -> [AstDynamicVarName PrimalSpan (AstRanked PrimalSpan)]
      -> ADVal (AstRanked PrimalSpan) r n)
  -> ( ADAstArtifact6 (AstRanked PrimalSpan) r n
     , Dual (AstRanked PrimalSpan) r n )
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun hasDt parameters0 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !(!vars@(varDtId, vars1), asts1, astsPrimal1) =
        funToAstAll parameters0 in
  let domains = V.fromList asts1
      domainsPrimal = V.fromList astsPrimal1
      deltaInputs = generateDeltaInputs domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = f varInputs domains vars1 in
  let astDt = AstVar (tshape primalBody) varDtId
      mdt = if hasDt then Just astDt else Nothing
      !(!astBindings, !gradient) =
        reverseDervative (V.length parameters0) primalBody mdt deltaTopLevel
  in ( ( vars
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6 l primalBody )
     , deltaTopLevel )

revAstOnDomainsFunS
  :: forall r sh. (OS.Shape sh, GoodScalar r)
  => Bool -> DomainsOD
  -> (Domains (ADValClown (AstDynamic PrimalSpan))
      -> Domains (AstDynamic FullSpan)
      -> [AstDynamicVarName PrimalSpan (AstShaped PrimalSpan)]
      -> ADVal (AstShaped PrimalSpan) r sh)
  -> ( ADAstArtifact6 (AstShaped PrimalSpan) r sh
     , Dual (AstShaped PrimalSpan) r sh )
{-# INLINE revAstOnDomainsFunS #-}
revAstOnDomainsFunS hasDt parameters0 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !(!vars@(varDtId, vars1), asts1, astsPrimal1) =
        funToAstAllS parameters0 in
  let domains = V.fromList asts1
      domainsPrimal = V.fromList astsPrimal1
      deltaInputs = generateDeltaInputs domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = f varInputs domains vars1 in
  let astDt = AstVarS varDtId
      mdt = if hasDt then Just astDt else Nothing
      !(!astBindings, !gradient) =
        reverseDervative (V.length parameters0) primalBody mdt deltaTopLevel
  in ( ( vars
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6S l primalBody )
     , deltaTopLevel )


-- * Old gradient adaptors, with constant and fixed inputs and dt.

-- These work for f both ranked and shaped.
crev
  :: forall r y f vals advals.
     ( DualPart f, HasSingletonDict y, GoodScalar r
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f vals advals.
     ( DualPart f, HasSingletonDict y, GoodScalar r
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> f r y -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall r y f vals advals.
     ( DualPart f, HasSingletonDict y, GoodScalar r
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
  :: ( DualPart f, HasSingletonDict y, GoodScalar r
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
  :: ( DualPart f, HasSingletonDict y, GoodScalar r
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


-- * The old derivative adaptors

-- This takes the sensitivity parameter, by convention.
-- It uses the same delta expressions as for gradients.
cfwd
  :: forall r y f vals advals.
     ( DualPart f, HasSingletonDict y, GoodScalar r
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> vals
  -> f r y
cfwd f x ds =
  let g inputs = f $ parseDomains ds inputs
  in fst $ cfwdOnDomains (toDomains x) g (toDomains ds)

-- The direction vector ds is taken as an extra argument.
cfwdOnDomains
  :: ( DualPart f, HasSingletonDict y, GoodScalar r
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
  :: ( DualPart f, HasSingletonDict y, GoodScalar r
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


-- * Additional mechanisms

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
