{-# LANGUAGE AllowAmbiguousTypes #-}
-- | The implementation of calculating gradient and derivative
-- of an objective function expressed wtih the `Tensor` class.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Adaptors, optimizers, etc.,
-- are add-ons.
module HordeAd.Core.Engine
  ( -- * The adaptors
    revL, revDtMaybeL, revDtFun, revDtInit, revDtInterpret, rev, revDt
  , crev, crevDt, fwd
  , -- * The most often used part of the high-level API
    revAstOnDomains, revOnDomains
  , -- * Operations exposed not for the library users but add-on makers
    revAstOnDomainsF, revAstOnDomainsFun, revAstOnDomainsEval, revOnADInputs
  , generateDeltaInputs, makeADInputs
  , -- * Internal operations, exposed, e.g., for tests
    slowFwdOnADInputs, slowFwdOnDomains
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Tannen
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Compose
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Delta
  (ForwardDerivative (..), derivativeFromDelta, gradientFromDelta, toInputId)
import HordeAd.Core.Domains
import HordeAd.Core.DualClass
  ( Dual
  , HasConversions (..)
  , HasRanks (..)
  , IsPrimalA (..)
  , IsPrimalR (..)
  , dFromR
  , dInputR
  )
import HordeAd.Core.DualNumber
import HordeAd.Core.TensorClass

-- * Adaptor objective functions with more complex domains

-- These only work with non-scalar codomain. A fully general version
-- is possible, but the user has to write many more type applications.
revL
  :: forall r n vals astvals ranked.
     ( ranked ~ Tannen ADVal AstRanked
     , InterpretAstA ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals, Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> Ast n r) -> [vals] -> [vals]
revL f valsAll = revDtMaybeL f valsAll Nothing

revDtMaybeL
  :: forall r n vals astvals ranked.
     ( ranked ~ Tannen ADVal AstRanked
     , InterpretAstA ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals, Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> Ast n r) -> [vals] -> Maybe (Flip OR.Array r n) -> [vals]
revDtMaybeL _ [] _ = []
revDtMaybeL f valsAll@(vals : _) dt =
  let asts4 = fst $ revDtFun f vals
      h val = parseDomains val $ fst
              $ revAstOnDomainsEval asts4 (toDomains val) dt
  in map h valsAll

revDtFun
  :: forall r n vals astvals ranked.
     ( ranked ~ Tannen ADVal AstRanked
     , InterpretAstA ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals, Underlying vals ~ r, Underlying astvals ~ r  )
  => (astvals -> Ast n r) -> vals
  -> (ADAstArtifact6 n r, Dual (AstRanked r n))
{-# INLINE revDtFun #-}
revDtFun f vals =
  let parameters0 = toDomains vals
  in revDtInit f vals EM.empty parameters0

revDtInit
  :: forall r n vals astvals dynamic ranked.
     ( dynamic ~ Compose ADVal AstDynamic
     , ranked ~ Tannen ADVal AstRanked
     , InterpretAstA ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals
     , vals ~ Value vals, vals ~ Value astvals, Underlying vals ~ r, Underlying astvals ~ r)
  => (astvals -> Ast n r) -> vals -> AstEnv dynamic ranked r
  -> DomainsOD r
  -> (ADAstArtifact6 n r, Dual (AstRanked r n))
{-# INLINE revDtInit #-}
revDtInit f vals envInit parameters0 =
  let shapes1 = map dshape $ V.toList parameters0
  in revAstOnDomainsFun shapes1 (revDtInterpret envInit vals f)

revDtInterpret
  :: forall n r vals astvals dynamic ranked.
     ( dynamic ~ Compose ADVal AstDynamic
     , ranked ~ Tannen ADVal AstRanked
     , InterpretAstA ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals
     , vals ~ Value astvals, Underlying astvals ~ r )
  => AstEnv dynamic ranked r
  -> vals -> (astvals -> Ast n r)
  -> Domains dynamic r -> Domains AstDynamic r
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
     ( ranked ~ Tannen ADVal AstRanked
     , InterpretAstA ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals, Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> Ast n r) -> vals -> vals
rev f vals = head $ revL f [vals]

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r n vals astvals ranked.
     ( ranked ~ Tannen ADVal AstRanked
     , InterpretAstA ranked r, KnownNat n
     , AdaptableDomains AstDynamic astvals, AdaptableDomains OD.Array vals
     , vals ~ Value vals, vals ~ Value astvals, Underlying vals ~ r, Underlying astvals ~ r )
  => (astvals -> Ast n r) -> vals -> Flip OR.Array r n -> vals
revDt f vals dt = head $ revDtMaybeL f [vals] (Just dt)

-- Old version of the three functions, with constant, fixed inputs and dt.
crev
  :: forall n r vals advals dynamic ranked.
     ( dynamic ~ Compose ADVal OD.Array
     , ranked ~ Tannen ADVal (Flip OR.Array)
     , AdaptableDomains dynamic advals, AdaptableDomains OD.Array vals
     , IsPrimalR r, KnownNat n, GoodScalar r
     , r ~ Underlying vals, vals ~ Value vals, vals ~ Value advals, Underlying advals ~ r )
  => (advals -> ranked r n) -> vals
  -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt
  :: forall n r vals advals dynamic ranked.
     ( dynamic ~ Compose ADVal OD.Array
     , ranked ~ Tannen ADVal (Flip OR.Array)
     , AdaptableDomains dynamic advals, AdaptableDomains OD.Array vals
     , IsPrimalR r, KnownNat n, GoodScalar r
     , r ~ Underlying vals, vals ~ Value vals, vals ~ Value advals, Underlying advals ~ r )
  => (advals -> ranked r n) -> vals -> OR.Array n r
  -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall n r vals advals dynamic ranked.
     ( dynamic ~ Compose ADVal OD.Array
     , ranked ~ Tannen ADVal (Flip OR.Array)
     , AdaptableDomains dynamic advals, AdaptableDomains OD.Array vals
     , IsPrimalR r, KnownNat n, GoodScalar r
     , r ~ Underlying vals, vals ~ Value vals, vals ~ Value advals, Underlying advals ~ r )
  => (advals -> ranked r n) -> vals -> Maybe (OR.Array n r)
  -> vals
crevDtMaybe f vals dt =
  let g inputs = runTannen $ f $ parseDomains vals inputs
  in parseDomains vals $ fst $ revOnDomains (Flip <$> dt) g (toDomains vals)


-- * Evaluation that computes gradients.

-- A new version that produced the gradient function, which can be
-- applied multiple times to input and dt. The second component
-- of the result is the objective function value, inefficiently
-- computed, only for testing.
revAstOnDomains
  :: forall r n dynamic ranked.
     ( dynamic ~ OD.Array
     , ranked ~ Flip OR.Array
     , InterpretAstA ranked r, KnownNat n )
  => (Domains (Compose ADVal AstDynamic) r -> Tannen ADVal AstRanked r n)
  -> Domains dynamic r -> Maybe (ranked r n)
  -> (Domains dynamic r, ranked r n)
-- The functions in which @revAstOnDomains@ inlines are not inlined
-- themselves in client code, so the bloat is limited.
{-# INLINE revAstOnDomains #-}
revAstOnDomains f parameters =
  revAstOnDomainsEval (revAstOnDomainsF f parameters) parameters

revAstOnDomainsF
  :: forall r n.
     (KnownNat n, ShowAstSimplify r)
  => (Domains (Compose ADVal AstDynamic) r -> Tannen ADVal AstRanked r n)
  -> DomainsOD r
  -> ADAstArtifact6 n r
{-# INLINE revAstOnDomainsF #-}
revAstOnDomainsF f parameters  =
  let shapes1 = map dshape $ V.toList parameters
  in fst $ revAstOnDomainsFun shapes1 (\varInputs _ _ -> f varInputs)

revAstOnDomainsFun
  :: forall r n. (KnownNat n, ShowAstSimplify r)
  => [[Int]]
  -> (Domains (Compose ADVal AstDynamic) r
      -> Domains AstDynamic r
      -> (ADAstVarNames n r, ADAstVars n r)
      -> Tannen ADVal AstRanked r n)
  -> (ADAstArtifact6 n r, Dual (AstRanked r n))
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun shapes1 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !v6@(!vars@(!_, _), (astDt, asts1)) = funToAstAll shapes1 in
  let domains = V.fromList asts1
      deltaInputs = generateDeltaInputs domains
      varInputs = makeADInputs domains deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = runTannen $ f varInputs domains v6
      deltaDt = packDeltaDtA (Right $ astDt (tshape primalBody))
                             deltaTopLevel in
  let !(!astBindings, !gradient) = gradientFromDelta (length shapes1) deltaDt
  in ( ( vars
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6 l primalBody )
     , deltaTopLevel )

revAstOnDomainsEval
  :: forall r n dynamic ranked.
     ( dynamic ~ OD.Array
     , ranked ~ Flip OR.Array
     , InterpretAstA ranked r, KnownNat n )
  => ADAstArtifact6 n r -> Domains dynamic r -> Maybe (ranked r n)
  -> (Domains dynamic r, ranked r n)
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

-- The old versions that use the fixed input and dt to compute gradient
-- only at these values, both transposing and evaluating at the same time.
revOnADInputs
  :: (dynamic ~ Compose ADVal OD.Array, KnownNat n, GoodScalar r, IsPrimalR r)
  => Maybe (Flip OR.Array r n)
  -> (Domains dynamic r -> ADVal (Flip OR.Array r n))
  -> Domains dynamic r
  -> (DomainsOD r, Flip OR.Array r n)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs dt f inputs =
  let dim1 = V.length inputs
      -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D _ v deltaTopLevel) = f inputs
      deltaDt = packDeltaDtR (maybe (Left v) Right dt) deltaTopLevel in
  let (_, gradient) = gradientFromDelta dim1 deltaDt
  in (gradient, v)

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: (dynamic ~ Compose ADVal OD.Array, KnownNat n, GoodScalar r, IsPrimalR r)
  => Maybe (Flip OR.Array r n)
  -> (Domains dynamic r -> ADVal (Flip OR.Array r n))
  -> DomainsOD r
  -> (DomainsOD r, Flip OR.Array r n)
revOnDomains dt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in revOnADInputs dt f inputs


-- * The slow evaluation producing objective function derivatives

-- It uses the same delta expressions as for gradients. See @fwdOnDomains@
-- for a fast variant (TODO: not ported from the old code yet).

-- This takes the sensitivity parameter, by convention.
fwd
  :: forall a r vals advals dynamic.
     ( dynamic ~ Compose ADVal OD.Array
     , ForwardDerivative OD.Array a r, GoodScalar r
     , AdaptableDomains dynamic advals, AdaptableDomains OD.Array vals
     , r ~ Underlying vals, vals ~ Value advals, Underlying advals ~ r )
  => (advals -> ADVal a) -> vals -> vals
  -> a
fwd f x ds =
  let g inputs = f $ parseDomains ds inputs
  in fst $ slowFwdOnDomains (toDomains x) g (toDomains ds)

slowFwdOnADInputs
  :: ( dynamic ~ Compose ADVal OD.Array
     , ForwardDerivative OD.Array a r )
  => Domains dynamic r
  -> (Domains dynamic r -> ADVal a)
  -> DomainsOD r
  -> (a, a)
{-# INLINE slowFwdOnADInputs #-}
slowFwdOnADInputs inputs f ds =
  let dim1 = V.length inputs
      !(D _ v deltaTopLevel) = f inputs in  -- TODO: _
  let derivative = derivativeFromDelta dim1 deltaTopLevel ds
  in (derivative, v)

-- The direction vector ds is taken as an extra argument.
slowFwdOnDomains
  :: forall a r dynamic.
     ( dynamic ~ Compose ADVal OD.Array
     , ForwardDerivative OD.Array a r, GoodScalar r )
  => DomainsOD r
  -> (Domains dynamic r -> ADVal a)
  -> DomainsOD r
  -> (a, a)
slowFwdOnDomains parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in slowFwdOnADInputs inputs f ds


-- * Additional mechanisms

generateDeltaInputs
  :: forall dynamic ranked shaped r.
     ( ConvertTensor dynamic ranked shaped, GoodScalar r
     , HasRanks ranked, HasConversions dynamic ranked )
  => Domains dynamic r
  -> Data.Vector.Vector (Dual (dynamic r))
generateDeltaInputs params =
  let arrayToInput :: Int -> dynamic r -> Dual (dynamic r)
      arrayToInput i t = case someNatVal $ toInteger $ length
                              $ dshape t of
        Just (SomeNat (_ :: Proxy n)) ->
          dFromR $ dInputR @ranked @r @n $ toInputId i
        Nothing -> error "generateDeltaInputs: impossible someNatVal error"
  in V.imap arrayToInput params
{- TODO: this can't be specified without a proxy
{-# SPECIALIZE generateDeltaInputs
  :: DomainsOD Double
  -> Data.Vector.Vector (Dual (OD.Array Double)) #-}
-}

makeADInputs
  :: Domains dynamic r
  -> Data.Vector.Vector (Dual (dynamic r))
  -> Domains (Compose ADVal dynamic) r
{-# INLINE makeADInputs #-}
makeADInputs = V.zipWith (\p d -> Compose $ dDnotShared emptyADShare p d)
