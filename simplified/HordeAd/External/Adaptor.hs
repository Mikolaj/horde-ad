{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | This is an adaptor from user-defined objective functions
-- with complicated domains to the restricted from of functions
-- that the AD machinery can efficiently differentiate.
module HordeAd.External.Adaptor
  ( revL, revDtMaybeL, revDtFun, rev, revDt
  , srevL, srevDtMaybeL, srev, srevDt
  , crev, crevDt, fwd
  ) where

import Prelude

import           Control.Arrow ((&&&))
import           Control.Exception (assert)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Compose
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Delta (DeltaR, ForwardDerivative)
import HordeAd.Core.Domains
import HordeAd.Core.DualClass (dFromVectorR, dScalarR)
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass

-- These only work with non-scalar codomain. A fully general version
-- is possible, but the user has to write many more type applications.
revL
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> [vals] -> [vals]
revL f valsAll = revDtMaybeL f valsAll Nothing

revDtMaybeL
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> [vals] -> Maybe (TensorOf n r) -> [vals]
revDtMaybeL _ [] _ = []
revDtMaybeL f valsAll@(vals : _) dt =
  let asts4 = fst $ revDtFun f vals
      h val = parseDomains val $ fst
              $ revAstOnDomainsEval asts4 (toDomains val) dt
  in map h valsAll

revDtFun
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals
  -> (ADAstArtifact6 n r, DeltaR n (Ast0 r))
{-# INLINE revDtFun #-}
revDtFun f vals =
  let parameters0 = toDomains vals
      dim0 = tlength @r @0 $ tfromD $ doms0 parameters0
      shapes1 = map dshape $ V.toList $ domsR parameters0
  in revAstOnDomainsFun dim0 shapes1 (revDtInterpret vals f)

revDtInterpret
  :: forall r n vals astvals.
     ( InterpretAst r, KnownNat n, ScalarOf r ~ r, Floating (Vector r)
     , RealFloat r, AdaptableDomains astvals
     , vals ~ Value astvals, Scalar astvals ~ Ast0 r )
  => vals -> (astvals -> Ast n r)
  -> Domains (ADVal (Ast0 r)) -> Domains (Ast0 r)
  -> (ADAstVarNames n r, ADAstVars n r)
  -> Compose ADVal (AstRanked r) n
{-# INLINE revDtInterpret #-}
revDtInterpret vals f varInputs domains ((var0, _, vars1), (ast0, _, _)) =
  let ast = f $ parseDomains vals domains
      d0 = dD emptyADShare
              ast0
              (dFromVectorR $ V.map dScalarR $ inputDual0 varInputs)
      env0 = extendEnvR var0 (Compose d0) EM.empty
      env1 = foldr extendEnvD env0
             $ zip vars1 $ V.toList
             $ V.zipWith (dDnotShared emptyADShare)
                         (inputPrimal1 varInputs)
                         (inputDual1 varInputs)
  in snd $ interpretAst env1 emptyMemo ast

rev
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals -> vals
rev f vals = head $ revL f [vals]

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals -> TensorOf n r -> vals
revDt f vals dt = head $ revDtMaybeL f [vals] (Just dt)

-- Versions that work with scalar codomain.
srevL
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> [vals] -> [vals]
srevL f = revL (tscalar . f)

srevDtMaybeL
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> [vals] -> Maybe r -> [vals]
srevDtMaybeL _ [] _ = []
srevDtMaybeL f valsAll dt = revDtMaybeL (tscalar . f) valsAll (tscalar <$> dt)

srev
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> vals -> vals
srev f = rev (tscalar . f)

-- This version additionally takes the sensitivity parameter.
srevDt
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> vals -> r -> vals
srevDt f vals dt = revDt (tscalar . f) vals (tscalar dt)

-- Old version of the three functions, with constant, fixed inputs and dt.
crev :: forall n r vals advals.
       ( r ~ Scalar vals, vals ~ Value advals
       , ADTensor r, DynamicTensor r, DomainsTensor r
       , IsPrimal (Flip OR.Array r n)
       , AdaptableDomains vals, AdaptableDomains advals
       , Scalar advals ~ ADVal r
       , Domains r ~ Data.Vector.Vector (DTensorOf r)
       , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
       , vals ~ Value vals, DomainsOf r ~ Domains r )
    => (advals -> Compose ADVal (Flip OR.Array r) n) -> vals
    -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt :: forall n r vals advals.
         ( r ~ Scalar vals, vals ~ Value advals
         , ADTensor r, DynamicTensor r, DomainsTensor r
         , IsPrimal (Flip OR.Array r n)
         , AdaptableDomains vals, AdaptableDomains advals
         , Scalar advals ~ ADVal r
         , Domains r ~ Data.Vector.Vector (DTensorOf r)
         , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
         , vals ~ Value vals, DomainsOf r ~ Domains r )
      => (advals -> Compose ADVal (Flip OR.Array r) n) -> vals -> OR.Array n r
      -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall n vals r advals.
     ( r ~ Scalar vals, vals ~ Value advals
     , ADTensor r, DynamicTensor r, DomainsTensor r
     , IsPrimal (Flip OR.Array r n)
     , AdaptableDomains vals, AdaptableDomains advals
     , Scalar advals ~ ADVal r
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
     , vals ~ Value vals, DomainsOf r ~ Domains r )
  => (advals -> Compose ADVal (Flip OR.Array r) n)
  -> vals -> Maybe (OR.Array n r)
  -> vals
crevDtMaybe f vals dt =
  let g inputs = getCompose $ f $ parseDomains vals inputs
  in parseDomains vals $ fst $ revOnDomains (Flip <$> dt) g (toDomains vals)

-- This takes the sensitivity parameter, by convention.
fwd :: forall a vals r advals.
       ( ForwardDerivative a, r ~ Scalar vals, vals ~ Value advals
       , ADTensor r, DynamicTensor r, DomainsTensor r, IsPrimalWithScalar a r
       , AdaptableDomains (Value advals), Scalar advals ~ ADVal r
       , AdaptableDomains advals, Domains r ~ Data.Vector.Vector (DTensorOf r)
       , DTensorOf (ADVal r) ~ ADVal (DTensorOf r) )
    => (advals -> ADVal a) -> vals -> vals
    -> a
fwd f x ds =
  let g inputs = f $ parseDomains ds inputs
  in fst $ slowFwdOnDomains (toDomains x) g (toDomains ds)
