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
  , crev, crevDt, revOnADInputs, revOnDomains
  , fwd, slowFwdOnADInputs, slowFwdOnDomains
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
import           Data.Maybe (isJust)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, SomeNat (..), someNatVal)

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
  :: forall r n vals astvals.
     ( GoodScalar r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals
     , Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> AstRanked r n) -> vals -> vals
rev f vals = revDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r n vals astvals.
     ( GoodScalar r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals
     , Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> AstRanked r n) -> vals -> Flip OR.Array r n -> vals
revDt f vals dt = revDtMaybe f vals (Just dt)

revDtMaybe
  :: forall r n vals astvals.
     ( GoodScalar r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals
     , Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> AstRanked r n) -> vals -> Maybe (Flip OR.Array r n) -> vals
revDtMaybe f vals mdt =
  let asts4 = fst $ revDtFun (isJust mdt) f vals
  in parseDomains vals $ fst $ revAstOnDomainsEval asts4 (toDomains vals) mdt

type Adaptable :: forall k. (Type -> k -> Type) -> Constraint
class Adaptable f where
  revAstOnDomainsEval
    :: forall r y. (GoodScalar r, HasSingletonDict f y)
    => ADAstArtifact6 f r y -> Domains OD.Array r -> Maybe (f r y)
    -> (Domains OD.Array r, f r y)

  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, HasSingletonDict f y
       , AdaptableDomains AstDynamic astvals
       , vals ~ Value astvals, Underlying astvals ~ r )
    => Bool -> (astvals -> AstOf f r y) -> vals -> AstEnv (ADVal (AstOf f)) r
    -> DomainsOD r
    -> (ADAstArtifact6 f r y, Dual (AstOf f) r y)

instance Adaptable @() (Clown OD.Array) where

instance Adaptable @Nat (Flip OR.Array) where
  {-# INLINE revAstOnDomainsEval #-}
  revAstOnDomainsEval ((varDt, vars1), gradient, primal) parameters dt =
    let env1 = foldr extendEnvD EM.empty $ zip vars1 $ V.toList parameters
        dtValue = case dt of
          Just a -> a
          Nothing -> treplicate0N (tshape primal) 1
        envDt = extendEnvR varDt dtValue env1
        (memo1, gradientDomain) =
          interpretAstDomainsDummy envDt emptyMemo gradient
        primalTensor = snd $ interpretAst env1 memo1 primal
    in (gradientDomain, primalTensor)

  revDtInit
    :: forall r y vals astvals.
       ( GoodScalar r, KnownNat y
       , AdaptableDomains AstDynamic astvals
       , vals ~ Value astvals, Underlying astvals ~ r )
    => Bool -> (astvals -> AstRanked r y) -> vals -> AstEnv (ADVal AstRanked) r
    -> DomainsOD r
    -> (ADAstArtifact6 (Flip OR.Array) r y, Dual AstRanked r y)
  {-# INLINE revDtInit #-}
  revDtInit hasDt f vals envInit parameters0 =
    let revDtInterpret :: Domains (ADValClown AstDynamic) r
                       -> Domains AstDynamic r
                       -> [AstDynamicVarName r]
                       -> ADVal AstRanked r y
        revDtInterpret varInputs domains vars1 =
          let ast = f $ parseDomains vals domains
              env1 = foldr extendEnvD envInit $ zip vars1 $ V.toList varInputs
          in snd $ interpretAst env1 emptyMemo ast
    in revAstOnDomainsFun hasDt parameters0 revDtInterpret

instance Adaptable @[Nat] (Flip OS.Array) where

revDtFun
  :: forall r n vals astvals.
     ( GoodScalar r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Underlying vals ~ r, Underlying astvals ~ r )
  => Bool -> (astvals -> AstRanked r n) -> vals
  -> (ADAstArtifact6 (Flip OR.Array) r n, Dual AstRanked r n)
{-# INLINE revDtFun #-}
revDtFun hasDt f vals = revDtInit hasDt f vals EM.empty (toDomains vals)

revAstOnDomainsFun
  :: forall r n. (KnownNat n, GoodScalar r)
  => Bool -> DomainsOD r
  -> (Domains (ADValClown AstDynamic) r
      -> Domains AstDynamic r
      -> [AstDynamicVarName r]
      -> ADVal AstRanked r n)
  -> (ADAstArtifact6 (Flip OR.Array) r n, Dual AstRanked r n)
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun hasDt parameters0 f =
  let shapes1 = map (dshape @(Flip OR.Array)) $ V.toList parameters0
      -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !(!vars@(!_, vars1), (astDt, asts1)) = funToAstAll shapes1 in
  let domains = V.fromList asts1
      deltaInputs = generateDeltaInputs @AstRanked domains
      varInputs = makeADInputs domains deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = f varInputs domains vars1 in
  let mdt = if hasDt then Just $ astDt (tshape primalBody) else Nothing
      !(!astBindings, !gradient) =
        reverseDervative (length shapes1) primalBody mdt deltaTopLevel
  in ( ( vars
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6 l primalBody )
     , deltaTopLevel )


-- * Old gradient adaptors, with constant and fixed inputs and dt.

-- These work for f both ranked and shaped.
crev
  :: forall y r vals advals f.
     ( DualPart f, HasSingletonDict f y, GoodScalar r
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals, r ~ Underlying vals, Underlying advals ~ r )
  => (advals -> ADVal f r y) -> vals
  -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt
  :: forall y r vals advals f.
     ( DualPart f, HasSingletonDict f y, GoodScalar r
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals, r ~ Underlying vals, Underlying advals ~ r )
  => (advals -> ADVal f r y) -> vals -> f r y
  -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall y r vals advals f.
     ( DualPart f, HasSingletonDict f y, GoodScalar r
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals, RandomDomains vals
     , vals ~ Value advals, r ~ Underlying vals, Underlying advals ~ r )
  => (advals -> ADVal f r y) -> vals -> Maybe (f r y)
  -> vals
crevDtMaybe f vals dt =
  let g inputs = f $ parseDomains vals inputs
  in parseDomains (toValue vals) $ fst $ revOnDomains dt g (toDomains vals)

-- The old versions that use the fixed input and dt to compute gradient
-- only at these values, both transposing and evaluating at the same time.
-- These work for f both ranked and shaped.
revOnADInputs
  :: ( DualPart f, HasSingletonDict f y, GoodScalar r
     , DynamicOf f ~ OD.Array )
  => Maybe (f r y)
  -> (Domains (DynamicOf (ADVal f)) r -> ADVal f r y)
  -> Domains (DynamicOf (ADVal f)) r
  -> (DomainsOD r, f r y)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs mdt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D _ v deltaTopLevel) = f inputs in
  let (astBindings, gradient) =
        reverseDervative (V.length inputs) v mdt deltaTopLevel
  in assert (null astBindings)
     $ (gradient, v)

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: ( DualPart f, HasSingletonDict f y, GoodScalar r
     , DynamicOf f ~ OD.Array )
  => Maybe (f r y)
  -> (Domains (DynamicOf (ADVal f)) r -> ADVal f r y)
  -> DomainsOD r
  -> (DomainsOD r, f r y)
revOnDomains dt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in revOnADInputs dt f inputs


-- * The old derivative adaptors

-- It uses the same delta expressions as for gradients. See @fwdOnDomains@
-- for a fast variant (TODO: not ported from the old code yet).

-- This takes the sensitivity parameter, by convention.
fwd
  :: forall a r n vals advals dynamic.
     ( dynamic ~ ADValClown OD.Array, a ~ Flip OR.Array r n
     , GoodScalar r, KnownNat n
     , AdaptableDomains dynamic advals, AdaptableDomains OD.Array vals
     , r ~ Underlying vals, vals ~ Value advals, Underlying advals ~ r )
  => (advals -> ADVal (Flip OR.Array) r n) -> vals -> vals
  -> a
fwd f x ds =
  let g inputs = f $ parseDomains ds inputs
  in fst $ slowFwdOnDomains (toDomains x) g (toDomains ds)

slowFwdOnADInputs
  :: ( dynamic ~ ADValClown OD.Array, a ~ Flip OR.Array r n
     , GoodScalar r, KnownNat n )
  => Domains dynamic r
  -> (Domains dynamic r -> ADVal (Flip OR.Array) r n)
  -> DomainsOD r
  -> (a, a)
{-# INLINE slowFwdOnADInputs #-}
slowFwdOnADInputs inputs f ds =
  let dim = V.length inputs
      !(D _ v deltaTopLevel) = f inputs in
  let derivative = derivativeFromDeltaR @(Flip OR.Array) dim deltaTopLevel ds
  in (derivative, v)

-- The direction vector ds is taken as an extra argument.
slowFwdOnDomains
  :: forall a r n dynamic.
     ( dynamic ~ ADValClown OD.Array, a ~ Flip OR.Array r n
     , GoodScalar r, KnownNat n )
  => DomainsOD r
  -> (Domains dynamic r -> ADVal (Flip OR.Array) r n)
  -> DomainsOD r
  -> (a, a)
slowFwdOnDomains parameters f ds =
  let deltaInputs = generateDeltaInputs @(Flip OR.Array) parameters
      inputs = makeADInputs parameters deltaInputs
  in slowFwdOnADInputs inputs f ds


-- * Additional mechanisms

generateDeltaInputs
  :: forall ranked shaped r dynamic.
     ( dynamic ~ DynamicOf ranked, ConvertTensor ranked shaped, GoodScalar r
     , Dual (Clown dynamic) ~ DeltaD ranked shaped )
  => Domains dynamic r
  -> Data.Vector.Vector (Dual (Clown dynamic) r '())
generateDeltaInputs params =
  let arrayToInput :: Int -> dynamic r -> Dual (Clown dynamic) r '()
      arrayToInput i t = case someNatVal $ toInteger $ length
                              $ dshape @ranked t of
        Just (SomeNat (_ :: Proxy n)) ->
          RToD @ranked $ InputR @ranked @r @n $ toInputId i
        Nothing -> error "generateDeltaInputs: impossible someNatVal error"
  in V.imap arrayToInput params
{- TODO: this can't be specified without a proxy
{-# SPECIALIZE generateDeltaInputs
  :: DomainsOD Double
  -> Data.Vector.Vector (Dual OD.Array Double) #-}
-}

makeADInputs
  :: Domains dynamic r
  -> Data.Vector.Vector (Dual (Clown dynamic) r '())
  -> Domains (ADValClown dynamic) r
{-# INLINE makeADInputs #-}
makeADInputs = V.zipWith (\p d -> Flip $ dDnotShared emptyADShare (Clown p) d)

shapedToRanked
  :: forall vals svals dynamic r.
     ( dynamic ~ OD.Array, Value svals ~ vals, Value vals ~ vals
     , AdaptableDomains dynamic vals
     , AdaptableDomains dynamic svals, RandomDomains svals
     , r ~ Underlying vals, r ~ Underlying svals )
  => svals -> vals
shapedToRanked svals =
  parseDomains @dynamic (toValue svals) $ toDomains @dynamic svals
