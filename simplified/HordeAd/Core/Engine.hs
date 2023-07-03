{-# LANGUAGE AllowAmbiguousTypes #-}
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
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Kind (Constraint, Type)
import           Data.Maybe (fromMaybe, isJust)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, SomeNat (..), someNatVal)
import           Type.Reflection (typeRep)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass

-- * Gradient adaptors

rev
  :: forall r y f vals astvals.
     ( Adaptable f, GoodScalar r, HasSingletonDict f y
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> AstOf f r y) -> vals -> vals
rev f vals = revDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r y f vals astvals.
     ( Adaptable f, GoodScalar r, HasSingletonDict f y
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> AstOf f r y) -> vals -> f r y -> vals
revDt f vals dt = revDtMaybe f vals (Just dt)

revDtMaybe
  :: forall r y f vals astvals.
     ( Adaptable f, GoodScalar r, HasSingletonDict f y
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , RandomDomains vals, vals ~ Value astvals )
  => (astvals -> AstOf f r y) -> vals -> Maybe (f r y) -> vals
revDtMaybe f vals mdt =
  let asts4 = fst $ revDtFun (isJust mdt) f vals
  in parseDomains (toValue vals)
     $ fst $ revAstOnDomainsEval asts4 (toDomains vals) mdt

type Adaptable :: forall k. (Type -> k -> Type) -> Constraint
class Adaptable f where
  revAstOnDomainsEval
    :: forall r y. (GoodScalar r, HasSingletonDict f y)
    => ADAstArtifact6 f r y -> Domains OD.Array -> Maybe (f r y)
    -> (Domains OD.Array, f r y)

  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, HasSingletonDict f y
       , AdaptableDomains AstDynamic astvals
       , vals ~ Value astvals )
    => Bool -> (astvals -> AstOf f r y) -> vals
    -> AstEnv (ADVal (AstOf (RankedOf f)))
    -> DomainsOD
    -> (ADAstArtifact6 f r y, Dual (AstOf f) r y)

-- TODO: it's not clear if the instance should be of Clown OD.Array or of
-- Domains OD.Array, for which we already have unletAstDomains6, etc.;
-- let's wait until we have rev as a function of Tensor class in case
-- that affects rev and/or Delta
instance Adaptable @() (Clown OD.Array) where
  revAstOnDomainsEval = undefined
  revDtInit = undefined

instance Adaptable @Nat (Flip OR.Array) where
  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars1), gradient, primal) parameters mdt =
    let env1 = foldr extendEnvDR EM.empty $ zip vars1 $ V.toList parameters
        dt = fromMaybe (treplicate0N (tshape primal) 1) mdt
        envDt = extendEnvR varDt dt env1
        gradientDomain = interpretAstDomainsDummy envDt gradient
        primalTensor = interpretAst env1 primal
    in (gradientDomain, primalTensor)

  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, KnownNat y
       , AdaptableDomains AstDynamic astvals, vals ~ Value astvals )
    => Bool -> (astvals -> AstRanked r y) -> vals
    -> AstEnv (ADVal AstRanked)
    -> DomainsOD
    -> (ADAstArtifact6 (Flip OR.Array) r y, Dual AstRanked r y)
  {-# INLINE revDtInit #-}
  revDtInit hasDt f vals envInit parameters0 =
    let revDtInterpret :: Domains (ADValClown AstDynamic)
                       -> Domains AstDynamic
                       -> [AstDynamicVarName]
                       -> ADVal AstRanked r y
        revDtInterpret varInputs domains vars1 =
          let ast = f $ parseDomains vals domains
              env1 = foldr extendEnvDR envInit $ zip vars1 $ V.toList varInputs
          in interpretAst env1 ast
    in revAstOnDomainsFun hasDt parameters0 revDtInterpret

instance Adaptable @[Nat] (Flip OS.Array) where
  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars1), gradient, primal) parameters mdt =
    let env1 = foldr extendEnvDR EM.empty $ zip vars1 $ V.toList parameters
        dt = fromMaybe 1 mdt
        envDt = extendEnvS varDt dt env1
        gradientDomain = interpretAstDomainsDummy envDt gradient
        primalTensor = interpretAstS env1 primal
    in (gradientDomain, primalTensor)

  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, OS.Shape y, KnownNat (OS.Size y)
       , AdaptableDomains AstDynamic astvals, vals ~ Value astvals )
    => Bool -> (astvals -> AstShaped r y) -> vals -> AstEnv (ADVal AstRanked)
    -> DomainsOD
    -> (ADAstArtifact6 (Flip OS.Array) r y, Dual AstShaped r y)
  {-# INLINE revDtInit #-}
  revDtInit hasDt f vals envInit parameters0 =
    let revDtInterpret :: Domains (ADValClown AstDynamic)
                       -> Domains AstDynamic
                       -> [AstDynamicVarName]
                       -> ADVal AstShaped r y
        revDtInterpret varInputs domains vars1 =
          let ast = f $ parseDomains vals domains
              env1 = foldr extendEnvDR envInit $ zip vars1 $ V.toList varInputs
          in interpretAstS env1 ast
    in revAstOnDomainsFunS hasDt parameters0 revDtInterpret

revDtFun
  :: forall r y f vals astvals.
     ( Adaptable f, GoodScalar r, HasSingletonDict f y
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => Bool -> (astvals -> AstOf f r y) -> vals
  -> (ADAstArtifact6 f r y, Dual (AstOf f) r y)
{-# INLINE revDtFun #-}
revDtFun hasDt f vals = revDtInit hasDt f vals EM.empty (toDomains vals)

revAstOnDomainsFun
  :: forall r n. (KnownNat n, GoodScalar r)
  => Bool -> DomainsOD
  -> (Domains (ADValClown AstDynamic)
      -> Domains AstDynamic
      -> [AstDynamicVarName]
      -> ADVal AstRanked r n)
  -> (ADAstArtifact6 (Flip OR.Array) r n, Dual AstRanked r n)
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun hasDt parameters0 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !(!vars@(AstVarName varDtId, vars1), asts1) =
        funToAstAll parameters0 in
  let domains = V.fromList asts1
      deltaInputs = generateDeltaInputs domains
      varInputs = makeADInputs domains deltaInputs
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
  :: forall r sh. (OS.Shape sh, KnownNat (OS.Size sh), GoodScalar r)
  => Bool -> DomainsOD
  -> (Domains (ADValClown AstDynamic)
      -> Domains AstDynamic
      -> [AstDynamicVarName]
      -> ADVal AstShaped r sh)
  -> (ADAstArtifact6 (Flip OS.Array) r sh, Dual AstShaped r sh)
{-# INLINE revAstOnDomainsFunS #-}
revAstOnDomainsFunS hasDt parameters0 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !(!vars@(AstVarName varDtId, vars1), asts1) =
        funToAstAll parameters0 in
  let domains = V.fromList asts1
      deltaInputs = generateDeltaInputs domains
      varInputs = makeADInputs domains deltaInputs
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
     ( DualPart f, HasSingletonDict f y, GoodScalar r
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f vals advals.
     ( DualPart f, HasSingletonDict f y, GoodScalar r
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> f r y -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall r y f vals advals.
     ( DualPart f, HasSingletonDict f y, GoodScalar r
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
  :: ( DualPart f, HasSingletonDict f y, GoodScalar r
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
  :: ( DualPart f, HasSingletonDict f y, GoodScalar r
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
     ( DualPart f, HasSingletonDict f y, GoodScalar r
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
  :: ( DualPart f, HasSingletonDict f y, GoodScalar r
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
  :: ( DualPart f, HasSingletonDict f y, GoodScalar r
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

generateDeltaInputs
  :: forall ranked shaped dynamic.
     ( dynamic ~ DynamicOf ranked, ConvertTensor ranked shaped
     , Dual (Clown dynamic) ~ DeltaD ranked shaped )
  => Domains dynamic
  -> Data.Vector.Vector (DeltaInputsExists dynamic)
generateDeltaInputs params =
  let arrayToInput :: Int -> DynamicExists dynamic -> DeltaInputsExists dynamic
      arrayToInput i (DynamicExists @_ @r t) =
        case someNatVal $ toInteger $ length $ dshape @ranked t of
          Just (SomeNat (_ :: Proxy n)) ->
            DeltaInputsExists $ RToD $ InputR @ranked @shaped @r @n
                                     $ toInputId i
          Nothing -> error "generateDeltaInputs: impossible someNatVal error"
  in V.imap arrayToInput params
{- TODO: this can't be specified without a proxy
{-# SPECIALIZE generateDeltaInputs
  :: DomainsOD -> Data.Vector.Vector (Dual OD.Array Double) #-}
-}

data DeltaInputsExists (dynamic :: Type -> Type) =
  forall r. GoodScalar r => DeltaInputsExists (Dual (Clown dynamic) r '())

makeADInputs
  :: Domains dynamic -> Data.Vector.Vector (DeltaInputsExists dynamic)
  -> Domains (ADValClown dynamic)
{-# INLINE makeADInputs #-}
makeADInputs =
  V.zipWith (\(DynamicExists @_ @r p)
              (DeltaInputsExists @_ @r2 d) ->
    case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> DynamicExists $ Flip $ dDnotShared emptyADShare (Clown p) d
      _ -> error "makeADInputs: type mismatch")

shapedToRanked
  :: forall vals svals dynamic.
     ( dynamic ~ OD.Array, Value svals ~ vals, Value vals ~ vals
     , AdaptableDomains dynamic vals
     , AdaptableDomains dynamic svals, RandomDomains svals )
  => svals -> vals
shapedToRanked svals =
  parseDomains @dynamic (toValue svals) $ toDomains @dynamic svals
