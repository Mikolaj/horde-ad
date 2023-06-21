{-# LANGUAGE AllowAmbiguousTypes #-}
-- | The implementation of calculating gradient and derivative
-- of an objective function expressed wtih the `Tensor` class.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Adaptors, optimizers, etc.,
-- are add-ons.
module HordeAd.Core.Engine
  ( revL, revDtMaybeL, revDtFun, revDtInit, revDtInterpret, rev, revDt
  , crev, crevDt
  , revAstOnDomains, revOnDomains
  , revAstOnDomainsF, revAstOnDomainsFun, revAstOnDomainsEval, revOnADInputs
  , revOnADInputsS
  , fwd, slowFwdOnADInputs, slowFwdOnDomains
  , generateDeltaInputs, makeADInputs, shapedToRanked
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Delta
  ( DeltaD (RToD)
  , DeltaDt (..)
  , DeltaR (InputR)
  , Dual
  , derivativeFromDeltaR
  , gradientFromDelta
  , toInputId
  )
import HordeAd.Core.DualNumber
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass

-- * Gradient adaptors

-- These only work with non-scalar codomain. A fully general version
-- is possible, but the user has to write many more type applications.
revL
  :: forall r n vals astvals ranked.
     ( ranked ~ ADVal AstRanked
     , InterpretAstR ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals
     , Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> AstRanked r n) -> [vals] -> [vals]
revL f valsAll = revDtMaybeL f valsAll Nothing

revDtMaybeL
  :: forall r n vals astvals ranked.
     ( ranked ~ ADVal AstRanked
     , InterpretAstR ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals
     , Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> AstRanked r n) -> [vals] -> Maybe (Flip OR.Array r n) -> [vals]
revDtMaybeL _ [] _ = []
revDtMaybeL f valsAll@(vals : _) dt =
  let asts4 = fst $ revDtFun f vals
      h val = parseDomains val $ fst
              $ revAstOnDomainsEval asts4 (toDomains val) dt
  in map h valsAll

revDtFun
  :: forall r n vals astvals ranked.
     ( ranked ~ ADVal AstRanked
     , InterpretAstR ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> AstRanked r n) -> vals
  -> (ADAstArtifact6 n r, Dual AstRanked r n)
{-# INLINE revDtFun #-}
revDtFun f vals =
  let parameters0 = toDomains vals
  in revDtInit f vals EM.empty parameters0

revDtInit
  :: forall r n vals astvals ranked.
     ( ranked ~ ADVal AstRanked
     , InterpretAstR ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals
     , vals ~ Value astvals, Underlying astvals ~ r)
  => (astvals -> AstRanked r n) -> vals -> AstEnv ranked r
  -> DomainsOD r
  -> (ADAstArtifact6 n r, Dual AstRanked r n)
{-# INLINE revDtInit #-}
revDtInit f vals envInit parameters0 =
  revAstOnDomainsFun parameters0 (revDtInterpret envInit vals f)

revDtInterpret
  :: forall n r vals astvals ranked.
     ( ranked ~ ADVal AstRanked
     , InterpretAstR ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals
     , vals ~ Value astvals, Underlying astvals ~ r )
  => AstEnv ranked r
  -> vals -> (astvals -> AstRanked r n)
  -> Domains (DynamicOf ranked) r -> Domains AstDynamic r
  -> (ADAstVarNames n r, ADAstVars n r)
  -> ranked r n
{-# INLINE revDtInterpret #-}
revDtInterpret envInit valsInit f = \varInputs domains
                                     ((_, vars1), (_, _)) ->
  let ast = f $ parseDomains valsInit domains
      env1 = foldr extendEnvD envInit
             $ zip vars1 $ V.toList varInputs
  in snd $ interpretAst env1 emptyMemo ast

rev
  :: forall r n vals astvals ranked.
     ( ranked ~ ADVal AstRanked
     , InterpretAstR ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals
     , Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> AstRanked r n) -> vals -> vals
rev f vals = head $ revL f [vals]

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r n vals astvals ranked.
     ( ranked ~ ADVal AstRanked
     , InterpretAstR ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals
     , Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> AstRanked r n) -> vals -> Flip OR.Array r n -> vals
revDt f vals dt = head $ revDtMaybeL f [vals] (Just dt)

revAstOnDomains
  :: forall r n ranked.
     ( ranked ~ Flip OR.Array
     , InterpretAstR ranked r, KnownNat n )
  => (Domains (ADValClown AstDynamic) r -> ADVal AstRanked r n)
  -> Domains OD.Array r -> Maybe (ranked r n)
  -> (Domains OD.Array r, ranked r n)
-- The functions in which @revAstOnDomains@ inlines are not inlined
-- themselves in client code, so the bloat is limited.
{-# INLINE revAstOnDomains #-}
revAstOnDomains f parameters =
  revAstOnDomainsEval (fst $ revAstOnDomainsF f parameters) parameters

revAstOnDomainsF
  :: forall r n.
     (KnownNat n, GoodScalar r)
  => (Domains (ADValClown AstDynamic) r -> ADVal AstRanked r n)
  -> DomainsOD r
  -> (ADAstArtifact6 n r, Dual AstRanked r n)
{-# INLINE revAstOnDomainsF #-}
revAstOnDomainsF f parameters  =
  revAstOnDomainsFun parameters (\varInputs _ _ -> f varInputs)

revAstOnDomainsFun
  :: forall r n. (KnownNat n, GoodScalar r)
  => DomainsOD r
  -> (Domains (ADValClown AstDynamic) r
      -> Domains AstDynamic r
      -> (ADAstVarNames n r, ADAstVars n r)
      -> ADVal AstRanked r n)
  -> (ADAstArtifact6 n r, Dual AstRanked r n)
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun parameters0 f =
  let shapes1 = map (dshape @(Flip OR.Array)) $ V.toList parameters0
      -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !v6@(!vars@(!_, _), (astDt, asts1)) = funToAstAll shapes1 in
  let domains = V.fromList asts1
      deltaInputs = generateDeltaInputs @AstRanked domains
      varInputs = makeADInputs domains deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = f varInputs domains v6
      deltaDt = packDeltaDtA (Right $ astDt (tshape primalBody))
                             deltaTopLevel in
  let !(!astBindings, !gradient) = gradientFromDelta (length shapes1) deltaDt
  in ( ( vars
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6 l primalBody )
     , deltaTopLevel )

packDeltaDtA :: (KnownNat n, GoodScalar r)
             => Either (AstRanked r n) (AstRanked r n)
             -> Dual AstRanked r n
             -> DeltaDt AstRanked AstShaped r
packDeltaDtA (Left tsh) = DeltaDtR (treplicate0N (tshape tsh) 1)
packDeltaDtA (Right t) = DeltaDtR t

revAstOnDomainsEval
  :: forall r n ranked.
     ( ranked ~ Flip OR.Array
     , InterpretAstR ranked r, KnownNat n )
  => ADAstArtifact6 n r -> Domains OD.Array r -> Maybe (ranked r n)
  -> (Domains OD.Array r, ranked r n)
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


-- * Old gradient adaptors, with constant and fixed inputs and dt.

crev
  :: forall n r vals advals ranked.
     ( ranked ~ ADVal (Flip OR.Array)
     , AdaptableDomains (DynamicOf ranked) advals
     , AdaptableDomains OD.Array vals
     , KnownNat n, GoodScalar r
     , r ~ Underlying vals, vals ~ Value vals
     , vals ~ Value advals, Underlying advals ~ r )
  => (advals -> ranked r n) -> vals
  -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt
  :: forall n r vals advals ranked.
     ( ranked ~ ADVal (Flip OR.Array)
     , AdaptableDomains (DynamicOf ranked) advals
     , AdaptableDomains OD.Array vals
     , KnownNat n, GoodScalar r
     , r ~ Underlying vals, vals ~ Value vals
     , vals ~ Value advals, Underlying advals ~ r )
  => (advals -> ranked r n) -> vals -> OR.Array n r
  -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall n r vals advals ranked.
     ( ranked ~ ADVal (Flip OR.Array)
     , AdaptableDomains (DynamicOf ranked) advals
     , AdaptableDomains OD.Array vals
     , KnownNat n, GoodScalar r
     , r ~ Underlying vals, vals ~ Value vals
     , vals ~ Value advals, Underlying advals ~ r )
  => (advals -> ranked r n) -> vals -> Maybe (OR.Array n r)
  -> vals
crevDtMaybe f vals dt =
  let g inputs = f $ parseDomains vals inputs
  in parseDomains vals $ fst $ revOnDomains (Flip <$> dt) g (toDomains vals)

-- The old versions that use the fixed input and dt to compute gradient
-- only at these values, both transposing and evaluating at the same time.
revOnADInputs
  :: (dynamic ~ ADValClown OD.Array, KnownNat n, GoodScalar r)
  => Maybe (Flip OR.Array r n)
  -> (Domains dynamic r -> ADVal (Flip OR.Array) r n)
  -> Domains dynamic r
  -> (DomainsOD r, Flip OR.Array r n)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs dt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D _ v deltaTopLevel) = f inputs
      deltaDt = packDeltaDtR (maybe (Left v) Right dt) deltaTopLevel in
  let (_, gradient) = gradientFromDelta (V.length inputs) deltaDt
  in (gradient, v)

packDeltaDtR :: (KnownNat n, GoodScalar r)
             => Either (Flip OR.Array r n) (Flip OR.Array r n)
             -> Dual (Flip OR.Array) r n
             -> DeltaDt (Flip OR.Array) (Flip OS.Array) r
packDeltaDtR (Left tsh) = DeltaDtR (treplicate0N (tshape tsh) 1)
packDeltaDtR (Right t) = DeltaDtR t

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: (dynamic ~ ADValClown OD.Array, KnownNat n, GoodScalar r)
  => Maybe (Flip OR.Array r n)
  -> (Domains dynamic r -> ADVal (Flip OR.Array) r n)
  -> DomainsOD r
  -> (DomainsOD r, Flip OR.Array r n)
revOnDomains dt f parameters =
  let deltaInputs = generateDeltaInputs @(Flip OR.Array) parameters
      inputs = makeADInputs parameters deltaInputs
  in revOnADInputs dt f inputs


-- * Old gradient adaptors for shaped tensors

revOnADInputsS
  :: ( dynamic ~ ADValClown OD.Array
     , OS.Shape sh, KnownNat (OS.Size sh), GoodScalar r )
  => Maybe (Flip OS.Array r sh)
  -> (Domains dynamic r -> ADVal (Flip OS.Array) r sh)
  -> Domains dynamic r
  -> (DomainsOD r, Flip OS.Array r sh)
-- The functions in which @revOnADInputsS@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputsS #-}
revOnADInputsS dt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D _ v deltaTopLevel) = f inputs
      deltaDt = packDeltaDtS dt deltaTopLevel in
  let (_, gradient) = gradientFromDelta (V.length inputs) deltaDt
  in (gradient, v)

packDeltaDtS :: forall sh r. (OS.Shape sh, KnownNat (OS.Size sh), GoodScalar r)
             => Maybe (Flip OS.Array r sh)
             -> Dual (Flip OS.Array) r sh
             -> DeltaDt (Flip OR.Array) (Flip OS.Array) r
packDeltaDtS Nothing = DeltaDtS (sreplicate0N @(Flip OS.Array) @r @sh 1)
packDeltaDtS (Just t) = DeltaDtS t


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
