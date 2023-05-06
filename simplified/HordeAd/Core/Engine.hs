-- | The implementation of calculating gradient and derivative
-- of an objective function expressed wtih the `Tensor` class.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Adaptors, optimizers, etc.,
-- are add-ons.
module HordeAd.Core.Engine
  ( -- * The adaptors
    revL, revDtMaybeL, revDtFun, revDtInterpret, rev, revDt
  , srevL, srevDtMaybeL, srev, srevDt
  , crev, crevDt, fwd
  , -- * The most often used part of the high-level API
    revAstOnDomains, revOnDomains
  , -- * Operations exposed not for the library users but add-on makers
    revAstOnDomainsF, revAstOnDomainsFun, revAstOnDomainsEval, revOnADInputs
  , generateDeltaInputs, initializerFixed, initializerFixed01
  , -- * Internal operations, exposed, e.g., for tests
    slowFwdOnADInputs, slowFwdOnDomains
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Compose
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Delta
  ( DeltaR
  , ForwardDerivative (..)
  , derivativeFromDelta
  , gradientFromDelta
  , toInputId
  )
import HordeAd.Core.Domains
import HordeAd.Core.DualClass
  (Dual, dFromR, dFromVectorR, dInput0, dInputR, dScalarR)
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass

-- * Adaptor objective functions with more complex domains

-- These only work with non-scalar codomain. A fully general version
-- is possible, but the user has to write many more type applications.
revL
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r, KnownNat n
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> [vals] -> [vals]
revL f valsAll = revDtMaybeL f valsAll Nothing

revDtMaybeL
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r, KnownNat n
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
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
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r, KnownNat n
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals
  -> (ADAstArtifact6 n r, DeltaR n (Ast0 r))
{-# INLINE revDtFun #-}
revDtFun f vals =
  let parameters0 = toDomains vals
      dim0 = tlength @r @0 $ tfromD $ doms0 parameters0
      shapes1 = map dshape $ toListDoms $ domsR parameters0
  in revAstOnDomainsFun dim0 shapes1 (revDtInterpret EM.empty vals f)

revDtInterpret
  :: forall n r vals astvals.
     ( InterpretAst r, Scalar r ~ r, Value r ~ r, KnownNat n
     , AdaptableDomains astvals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => AstEnv (ADVal (Ast0 r)) -> vals -> (astvals -> Ast n r)
  -> Domains (ADVal (Ast0 r)) -> Domains (Ast0 r)
  -> (ADAstVarNames n r, ADAstVars n r)
  -> Compose ADVal (AstRanked r) n
{-# INLINE revDtInterpret #-}
revDtInterpret envInit valsInit f = \varInputs domains
                                     ((var0, _, vars1), (ast0, _, _)) ->
  let ast = f $ parseDomains valsInit domains
      d0 = dD emptyADShare
              ast0
              (dFromVectorR $ V.map dScalarR $ inputDual0 varInputs)
      env0 = extendEnvR var0 (Compose d0) envInit
      env1 = foldr extendEnvD env0
             $ zip vars1 $ V.toList
             $ V.zipWith (dDnotShared emptyADShare)
                         (inputPrimal1 varInputs)
                         (inputDual1 varInputs)
  in snd $ interpretAst env1 emptyMemo ast

rev
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r, KnownNat n
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals -> vals
rev f vals = head $ revL f [vals]

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r, KnownNat n
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals -> TensorOf n r -> vals
revDt f vals dt = head $ revDtMaybeL f [vals] (Just dt)

-- Versions that work with scalar codomain.
srevL
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> [vals] -> [vals]
srevL f = revL (tscalar . f)

srevDtMaybeL
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> [vals] -> Maybe r -> [vals]
srevDtMaybeL _ [] _ = []
srevDtMaybeL f valsAll dt = revDtMaybeL (tscalar . f) valsAll (tscalar <$> dt)

srev
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> vals -> vals
srev f = rev (tscalar . f)

-- This version additionally takes the sensitivity parameter.
srevDt
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, Scalar r ~ r, Value r ~ r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> vals -> r -> vals
srevDt f vals dt = revDt (tscalar . f) vals (tscalar dt)

-- Old version of the three functions, with constant, fixed inputs and dt.
crev
  :: forall n r vals advals.
     ( ADTensor r, IsPrimal (Flip OR.Array r n)
     , AdaptableDomains advals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value advals
     , Scalar advals ~ ADVal r )
  => (advals -> Compose ADVal (Flip OR.Array r) n) -> vals
  -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt
  :: forall n r vals advals.
     ( ADTensor r, IsPrimal (Flip OR.Array r n)
     , AdaptableDomains advals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value advals
     , Scalar advals ~ ADVal r )
  => (advals -> Compose ADVal (Flip OR.Array r) n) -> vals -> OR.Array n r
  -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall n vals r advals.
     ( ADTensor r, IsPrimal (Flip OR.Array r n)
     , AdaptableDomains advals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value advals
     , Scalar advals ~ ADVal r )
  => (advals -> Compose ADVal (Flip OR.Array r) n)
  -> vals -> Maybe (OR.Array n r)
  -> vals
crevDtMaybe f vals dt =
  let g inputs = getCompose $ f $ parseDomains vals inputs
  in parseDomains vals $ fst $ revOnDomains (Flip <$> dt) g (toDomains vals)

-- This takes the sensitivity parameter, by convention.
fwd :: forall a vals r advals.
       ( ADTensor r, Scalar a ~ r, ForwardDerivative a
       , AdaptableDomains advals, AdaptableDomains (Value advals)
       , r ~ Scalar vals, vals ~ Value advals
       , Scalar advals ~ ADVal r )
    => (advals -> ADVal a) -> vals -> vals
    -> a
fwd f x ds =
  let g inputs = f $ parseDomains ds inputs
  in fst $ slowFwdOnDomains (toDomains x) g (toDomains ds)


-- * Evaluation that computes gradients.

-- A new version that produced the gradient function, which can be
-- applied multiple times to input and dt. The second component
-- of the result is the objective function value, inefficiently
-- computed, only for testing.
revAstOnDomains
  :: forall r n.
     (ADTensor r, InterpretAst r, KnownNat n, Scalar r ~ r, Value r ~ r)
  => (Domains (ADVal (Ast0 r)) -> Compose ADVal (AstRanked r) n)
  -> Domains r -> Maybe (TensorOf n r)
  -> (Domains r, TensorOf n r)
-- The functions in which @revAstOnDomains@ inlines are not inlined
-- themselves in client code, so the bloat is limited.
{-# INLINE revAstOnDomains #-}
revAstOnDomains f parameters =
  revAstOnDomainsEval (revAstOnDomainsF f parameters) parameters

revAstOnDomainsF
  :: forall r n.
     (ADTensor r, KnownNat n, ShowAstSimplify r)
  => (Domains (ADVal (Ast0 r)) -> Compose ADVal (AstRanked r) n)
  -> Domains r
  -> ADAstArtifact6 n r
{-# INLINE revAstOnDomainsF #-}
revAstOnDomainsF f parameters  =
  let dim0 = tlength $ domains0 parameters
      shapes1 = map dshape $ toListDoms $ domsR parameters
  in fst $ revAstOnDomainsFun dim0 shapes1 (\varInputs _ _ -> f varInputs)

revAstOnDomainsFun
  :: forall r n. (KnownNat n, ShowAstSimplify r)
  => Int -> [[Int]]
  -> (Domains (ADVal (Ast0 r)) -> Domains (Ast0 r)
      -> (ADAstVarNames n r, ADAstVars n r)
      -> Compose ADVal (AstRanked r) n)
  -> (ADAstArtifact6 n r, DeltaR n (Ast0 r))
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun dim0 shapes1 f =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !v6@(!vars@(!_, _, _), (ast0, astDt, asts1)) =
        funToAstAll (singletonShape dim0) shapes1 in
  let domains = mkDomains ast0 (fromListDoms asts1)
      deltaInputs = generateDeltaInputs domains
      varInputs = makeADInputs domains deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l primalBody deltaTopLevel) = getCompose $ f varInputs domains v6
      deltaDt = packDeltaDt (Right $ astDt (tshape primalBody)) deltaTopLevel in
  let !(!astBindings, !gradient) =
        gradientFromDelta dim0 (length shapes1) deltaDt
  in ( ( vars
       , unletAstDomains6 astBindings l (dmkDomains gradient)
       , unletAst6 l primalBody )
     , deltaTopLevel )

revAstOnDomainsEval
  :: forall r n.
     (ADTensor r, InterpretAst r, KnownNat n, Scalar r ~ r, Value r ~ r)
  => ADAstArtifact6 n r -> Domains r -> Maybe (TensorOf n r)
  -> (Domains r, TensorOf n r)
{-# INLINE revAstOnDomainsEval #-}
revAstOnDomainsEval ((var0, varDt, vars1), gradient, primal) parameters dt =
  let env1 = foldr extendEnvD EM.empty
             $ zip (AstDynamicVarName var0 : vars1) $ toListDoms parameters
      dtValue = case dt of
        Just a -> a
        Nothing -> tkonst0N (tshape primal) 1
      envDt = extendEnvR varDt dtValue env1
      (memo1, gradientDomain) =
        interpretAstDomainsDummy envDt emptyMemo gradient
      primalTensor = snd $ interpretAst env1 memo1 primal
  in (fromVectorDoms gradientDomain, primalTensor)

-- The old versions that use the fixed input and dt to compute gradient
-- only at these values, both transposing and evaluating at the same time.
revOnADInputs
  :: (ADTensor r, IsPrimal a, Scalar a ~ r)
  => Maybe a
  -> (Domains (ADVal r) -> ADVal a)
  -> Domains (ADVal r)
  -> (Domains r, a)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs dt f inputs@ADInputs{..} =
  let dim0 = tlength inputPrimal0
      dim1 = V.length inputPrimal1
      -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D _ v deltaTopLevel) = f inputs
      deltaDt = packDeltaDt (maybe (Left v) Right dt) deltaTopLevel in
  let (_, gradient) = gradientFromDelta dim0 dim1 deltaDt
  in (gradient, v)

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: (ADTensor r, IsPrimal a, Scalar a ~ r)
  => Maybe a
  -> (Domains (ADVal r) -> ADVal a)
  -> Domains r
  -> (Domains r, a)
revOnDomains dt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in revOnADInputs dt f inputs


-- * The slow evaluation producing objective function derivatives

-- It uses the same delta expressions as for gradients. See @fwdOnDomains@
-- for a fast variant (TODO: not ported from the old code yet).

slowFwdOnADInputs
  :: (ADTensor r, ForwardDerivative a, Scalar a ~ r)
  => Domains (ADVal r)
  -> (Domains (ADVal r) -> ADVal a)
  -> Domains r
  -> (a, a)
{-# INLINE slowFwdOnADInputs #-}
slowFwdOnADInputs inputs@ADInputs{..} f ds =
  let dim0 = tlength inputPrimal0
      dim1 = V.length inputPrimal1
      !(D _ v deltaTopLevel) = f inputs in  -- TODO: _
  let derivative = derivativeFromDelta dim0 dim1 deltaTopLevel ds
  in (derivative, v)

-- The direction vector ds is taken as an extra argument.
slowFwdOnDomains
  :: (ADTensor r, ForwardDerivative a, Scalar a ~ r)
  => Domains r
  -> (Domains (ADVal r) -> ADVal a)
  -> Domains r
  -> (a, a)
slowFwdOnDomains parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in slowFwdOnADInputs inputs f ds


-- * Additional mechanisms

generateDeltaInputs
  :: forall r. ADTensor r
  => Domains r
  -> ( Data.Vector.Vector (Dual r)
     , Data.Vector.Vector (Dual (DTensorOf r)) )
generateDeltaInputs params =
  let arrayToInput :: Int -> DTensorOf r -> Dual (DTensorOf r)
      arrayToInput i t = case someNatVal $ toInteger $ length $ dshape t of
        Just (SomeNat (_ :: Proxy n)) ->
          dFromR $ dInputR @r @n $ toInputId i
        Nothing -> error "generateDeltaInputs: impossible someNatVal error"
      !v0 = V.generate (tlength $ domains0 params) (dInput0 . toInputId)
      !v1 = V.imap arrayToInput (domainsR params)
  in (v0, v1)
{-# SPECIALIZE generateDeltaInputs
  :: Domains Double
  -> ( Data.Vector.Vector (Dual Double)
     , Data.Vector.Vector (Dual (OD.Array Double)) ) #-}

-- | Initialize parameters using a uniform distribution with a fixed range
-- taken from an argument.
--
-- Must be Double, because @randomVector@ only works on that.
--
-- This only works fine for nets with levels that have similar size and use
-- the same activation function. Otherwise, the range should vary per level.
-- A rule of thumb range for weights is @sqrt(6 / (F_in + F_out)@,
-- where @F_in + F_out@ is the sum of inputs and outputs of the largest level.
-- See https://github.com/pytorch/pytorch/issues/15314 and their newer code.
initializerFixed :: Int -> Double -> (Int, [Int], c, d)
                 -> ((Int, Int), Int, Double, Domains Double)
initializerFixed seed range (nParams0, lParams1, _, _) =
  let vParams1 = V.fromList lParams1
      createRandomVector n seedV =
        LA.scale (2 * range)
        $ LA.randomVector seedV LA.Uniform n - LA.scalar 0.5
      dom0 = OR.fromVector [nParams0] $ createRandomVector nParams0 seed
      domR =
        V.imap (\i sz ->
                  OD.fromVector [sz]
                  $ createRandomVector sz (seed + sz + i)) vParams1
      totalParams = nParams0
                    + V.sum vParams1
  in ( (nParams0, V.length vParams1)
     , totalParams
     , range
     , mkDomains (Flip dom0) domR )

initializerFixed01 :: Int -> Double -> (Int, [Int])
                   -> ((Int, Int), Int, Double, Domains Double)
initializerFixed01 seed range (nParams0, lParams1) =
  initializerFixed seed range (nParams0, lParams1, undefined, undefined)
