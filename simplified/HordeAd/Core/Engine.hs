-- | The implementation of calculating gradient and derivative
-- of an objective function expressed wtih the `Tensor` class.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Adaptors, optimizers, etc.,
-- are add-ons.
module HordeAd.Core.Engine
  ( ADInputs(..)
  , makeADInputs, nullADInputs
  , -- * The most often used part of the high-level API
    revAstOnDomains, revOnDomains
  , -- * Operations exposed not for the library users but add-on makers
    revAstOnDomainsFun, revAstOnDomainsEval, revOnADInputs
  , generateDeltaInputs, initializerFixed, initializerFixed01
  , -- * Internal operations, exposed, e.g., for tests
    slowFwdOnADInputs, slowFwdOnDomains
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.EnumMap.Strict as EM
import           Data.MonoTraversable (Element)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.Ast
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Delta
  ( DeltaR
  , ForwardDerivative (..)
  , derivativeFromDelta
  , gradientFromDelta
  , toInputId
  )
import HordeAd.Core.DualClass (Dual, dFromR, dInput0, dInputR)
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal (ADTensor)
import HordeAd.Core.TensorClass

data ADInputs r = ADInputs
  { inputPrimal0 :: Domain0 r
  , inputDual0   :: Data.Vector.Vector (Dual r)
  , inputPrimal1 :: DomainR r
  , inputDual1   :: Data.Vector.Vector (Dual (DTensorOf r))
  }

makeADInputs
  :: Tensor r
  => Domains r
  -> ( Data.Vector.Vector (Dual r)
     , Data.Vector.Vector (Dual (DTensorOf r)) )
  -> ADInputs r
{-# INLINE makeADInputs #-}
makeADInputs params (vs0, vs1)
  = ADInputs (domains0 params) vs0 (domainsR params) vs1

inputsToDomains :: DynamicTensor r => ADInputs r -> Domains r
inputsToDomains ADInputs{..} =
  mkDomains inputPrimal0 inputPrimal1

nullADInputs :: (Tensor r, DynamicTensor r) => ADInputs r -> Bool
nullADInputs adinputs = nullDomains (inputsToDomains adinputs)


-- * Evaluation that computes gradients.

-- A new version that produced the gradient function, which can be
-- applied multiple times to input and dt. The second component
-- of the result is the objective function value, inefficiently
-- computed, only for testing.
revAstOnDomains
  :: forall r n.
     ( ADTensor r, InterpretAst r, DomainsTensor r
     , KnownNat n, ScalarOf r ~ r, ShowAstSimplify r )
  => (ADInputs (Ast0 r) -> ADVal (Ast n r))
  -> Domains r -> Maybe (TensorOf n r)
  -> (Domains r, TensorOf n r)
-- The functions in which @revAstOnDomains@ inlines are not inlined
-- themselves in client code, so the bloat is limited.
{-# INLINE revAstOnDomains #-}
revAstOnDomains f parameters =
  revAstOnDomainsEval
    (fst $ revAstOnDomainsFun (\varInputs _ _ -> f varInputs) parameters)
    parameters

revAstOnDomainsFun
  :: forall r n. (KnownNat n, Tensor r, DomainsTensor r, ShowAstSimplify r)
  => (ADInputs (Ast0 r) -> Domains (Ast0 r)
      -> (ADAstVarNames n r, ADAstVars n r)
      -> ADVal (Ast n r))
  -> Domains r
  -> (ADAstArtifact6 n r, DeltaR n (Ast0 r))
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun f parameters0 =
  let dim0 = tlength $ domains0 parameters0
      shapes1 = map dshape $ V.toList $ domainsR parameters0
      -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects.
      !v6@(!vars@(!_, _, _), (ast0, astDt, asts1)) =
        funToAstAll (singletonShape dim0) shapes1 in
  let domains = mkDomains ast0 (V.fromList asts1)
      deltaInputs = generateDeltaInputs domains
      varInputs = makeADInputs domains deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D astBindings0 primalBody deltaTopLevel) = f varInputs domains v6
      deltaDt = packDeltaDt (Right $ astDt (tshape primalBody)) deltaTopLevel in
  let gradient = gradientFromDelta astBindings0 dim0 (length shapes1) deltaDt
  in ((vars, gradient, tletWrap astBindings0 primalBody), deltaTopLevel)

revAstOnDomainsEval
  :: forall r n.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , ShowAstSimplify r )
  => ADAstArtifact6 n r -> Domains r -> Maybe (TensorOf n r)
  -> (Domains r, TensorOf n r)
{-# INLINE revAstOnDomainsEval #-}
revAstOnDomainsEval ((var0, varDt, vars1), gradient, primal)
                    parameters dt =
  let env1 = foldr (\(AstDynamicVarName var, v) ->
                      extendEnvR var (tfromD v)) EM.empty
             $ zip (AstDynamicVarName var0 : vars1) $ V.toList parameters
      dtValue = case dt of
        Just a -> a
        Nothing -> tkonst0N (tshape primal) 1
      envDt = extendEnvR varDt dtValue env1
      (memo1, gradientDomain) =
        interpretAstDomainsDummy envDt emptyMemo gradient
      primalTensor = snd $ interpretAst env1 memo1 primal
  in (gradientDomain, primalTensor)

-- The old versions that use the fixed input and dt to compute gradient
-- only at these values, both transposing and evaluating at the same time.
revOnADInputs
  :: ( Tensor r, DynamicTensor r, DomainsTensor r, IsPrimalWithScalar a r
     , DomainsOf r ~ Domains r )
  => Maybe a
  -> (ADInputs r -> ADVal a)
  -> ADInputs r
  -> (Domains r, a)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs dt f inputs@ADInputs{..} =
  let dim0 = tlength inputPrimal0
      dim1 = V.length inputPrimal1
      -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D astBindings0 v deltaTopLevel) = f inputs
      deltaDt = packDeltaDt (maybe (Left v) Right dt) deltaTopLevel in
  let gradient = gradientFromDelta astBindings0 dim0 dim1 deltaDt
  in (gradient, letWrapPrimal astBindings0 v)

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: ( ADTensor r, DynamicTensor r, DomainsTensor r, IsPrimalWithScalar a r
     , DomainsOf r ~ Domains r )
  => Maybe a
  -> (ADInputs r -> ADVal a)
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
  :: (Tensor r, DynamicTensor r, Element a ~ r, ForwardDerivative a)
  => ADInputs r
  -> (ADInputs r -> ADVal a)
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
  :: ( ADTensor r, DynamicTensor r, DomainsTensor r, Element a ~ r
     , ForwardDerivative a )
  => Domains r
  -> (ADInputs r -> ADVal a)
  -> Domains r
  -> (a, a)
slowFwdOnDomains parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in slowFwdOnADInputs inputs f ds


-- * Additional mechanisms

generateDeltaInputs
  :: forall r. (ADTensor r, DomainsTensor r)
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
     , mkDomains dom0 domR )

initializerFixed01 :: Int -> Double -> (Int, [Int])
                   -> ((Int, Int), Int, Double, Domains Double)
initializerFixed01 seed range (nParams0, lParams1) =
  initializerFixed seed range (nParams0, lParams1, undefined, undefined)
