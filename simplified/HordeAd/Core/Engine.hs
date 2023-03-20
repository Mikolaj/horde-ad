-- | The implementation of calculating gradient, derivative and value
-- of an objective function defined on dual numbers, as defined
-- in "HordeAd.Core.DualNumber". Together with that module, this forms
-- the basic high-level API of the horde-ad library. Optimizers, etc.,
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
  , prettyPrintDf
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.RankedS as OR
import           Data.Proxy (Proxy)
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Text.Show.Pretty (ppShow)

import HordeAd.Core.ADValTensor
import HordeAd.Core.Ast
import HordeAd.Core.Delta
  (Delta0, derivativeFromDelta, gradientFromDelta, toInputId)
import HordeAd.Core.DualClass (Dual, dFrom1X, dInput0, dInput1)
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

data ADInputs r = ADInputs
  { inputPrimal0 :: Domain0 r
  , inputDual0   :: Data.Vector.Vector (Dual r)
  , inputPrimal1 :: Domain1 r
  , inputDual1   :: Data.Vector.Vector (Dual (DynamicTensor r))
  }

makeADInputs
  :: Domains r
  -> ( Data.Vector.Vector (Dual r)
     , Data.Vector.Vector (Dual (DynamicTensor r)) )
  -> ADInputs r
{-# INLINE makeADInputs #-}
makeADInputs Domains{..} (vs0, vs1)
  = ADInputs domains0 vs0 domains1 vs1

inputsToDomains :: ADInputs r -> Domains r
inputsToDomains ADInputs{..} =
  Domains inputPrimal0 inputPrimal1

nullADInputs :: Tensor r => ADInputs r -> Bool
nullADInputs adinputs = nullDomains (inputsToDomains adinputs)

-- * Evaluation that computes gradients.

-- A new version that produced the gradient function, which can be
-- applied multiple times to input and dt. The second component
-- of the result is the objective function value, inefficiently
-- computed, only for testing.
revAstOnDomains
  :: forall r n.
     ( ADTensor r, InterpretAst r, KnownNat n, ScalarOf r ~ r
     , Num (Vector r), Show r, Numeric r )
  => (ADInputs (Ast0 r) -> ADVal (Ast n r))
  -> Domains r -> Maybe (TensorOf n r)
  -> (Domains r, TensorOf n r)
-- The functions in which @revAstOnDomains@ inlines are not inlined
-- themselves in client code, so the bloat is limited.
{-# INLINE revAstOnDomains #-}
revAstOnDomains f parameters dt =
  let dim0 = tlength $ domains0 parameters
      shapes1 = map tshapeD $ V.toList $ domains1 parameters
  in revAstOnDomainsEval dim0 (length shapes1)
                         (revAstOnDomainsFun dim0 shapes1 f)
                         parameters dt

revAstOnDomainsFun
  :: forall r n.
     (KnownNat n, Num (Vector r), Show r, Numeric r)
  => Int -> [[Int]]
  -> (ADInputs (Ast0 r) -> ADVal (Ast n r))
  -> ( AstVarName (TensorOf 1 r)
     , [AstDynamicVarName r]
     , AstVarName (TensorOf n r)
     , Domains (Ast0 r)
     , Ast n r )
{-# INLINE revAstOnDomainsFun #-}
revAstOnDomainsFun dim0 shapes1 f =
  let (var0, ast0) = funToAstR (singletonShape dim0) id
      (vars1, asts1) = unzip $ map funToAstD shapes1
      domains = Domains ast0 (V.fromList asts1)
      deltaInputs = generateDeltaInputs domains
      varInputs = makeADInputs domains deltaInputs
      -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D vAst deltaTopLevel) = f varInputs
      (varDt, astDt) = funToAstR (tshape vAst) id
      deltaDt = packDeltaDt (Right astDt) deltaTopLevel
  in let gradientAst = gradientFromDelta dim0 (length shapes1) deltaDt
     in (var0, vars1, varDt, gradientAst, vAst)

revAstOnDomainsEval
  :: forall r n.
     ( ADTensor r, InterpretAst r, KnownNat n, ScalarOf r ~ r
     , Num (Vector r), Show r, Numeric r )
  => Int -> Int
  -> ( AstVarName (TensorOf 1 r)
     , [AstDynamicVarName r]
     , AstVarName (TensorOf n r)
     , Domains (Ast0 r)
     , Ast n r )
  -> Domains r -> Maybe (TensorOf n r)
  -> (Domains r, TensorOf n r)
{-# INLINE revAstOnDomainsEval #-}
revAstOnDomainsEval dim0 dim1
                    (var0, vars1, varDt, gradientAst, vAst)
                    parameters dt =
  let !_A0 = assert (dim0 == tlength (domains0 parameters)) ()
      !_A1 = assert (dim1 == V.length (domains1 parameters)) ()
      env0 = extendEnvR var0 (domains0 parameters) IM.empty
      env1 = foldr (\(AstDynamicVarName var, v) ->
                      extendEnvR var (tfromD v)) env0
             $ zip vars1 $ V.toList $ domains1 parameters
      dtValue = case dt of
        Just a -> a
        Nothing -> tkonst0N (tshape vAst) 1
      envDt = extendEnvR varDt dtValue env1
      gradientDomain =
        Domains (interpretAst envDt $ domains0 gradientAst)
                (V.map (\t -> case t of
                         AstDynamicDummy -> tdummyD
                         _ -> interpretAstDynamic envDt t)
                 $ domains1 gradientAst)
  in (gradientDomain, interpretAst env1 vAst)

-- The old versions that use the fixed input and dt to compute gradient
-- only at these values, both transposing and evaluating at the same time.
revOnADInputs
  :: (ADTensor r, IsPrimalWithScalar a r)
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
      !(D v deltaTopLevel) = f inputs
      deltaDt = packDeltaDt (maybe (Left v) Right dt) deltaTopLevel
  in let gradient = gradientFromDelta dim0 dim1 deltaDt
     in (gradient, v)

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: (ADTensor r, IsPrimalWithScalar a r)
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
-- for a fast variant.

slowFwdOnADInputs
  :: (ADTensor r, Dual r ~ Delta0 r)
  => ADInputs r
  -> (ADInputs r -> ADVal r)
  -> Domains r
  -> (r, r)
{-# INLINE slowFwdOnADInputs #-}
slowFwdOnADInputs inputs@ADInputs{..} f ds =
  let dim0 = tlength inputPrimal0
      dim1 = V.length inputPrimal1
      !(D v deltaTopLevel) = f inputs
  in let derivative = derivativeFromDelta dim0 dim1 deltaTopLevel ds
     in (derivative, v)

-- The direction vector ds is taken as an extra argument.
slowFwdOnDomains
  :: (ADTensor r, Dual r ~ Delta0 r)
  => Domains r
  -> (ADInputs r -> ADVal r)
  -> Domains r
  -> (r, r)
slowFwdOnDomains parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in slowFwdOnADInputs inputs f ds


-- * Additional mechanisms

prettyPrintDf
  :: (ADTensor r, Show (Dual r))
  => (ADInputs r -> ADVal r)
  -> Domains r
  -> String
prettyPrintDf f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
      !(D _ deltaTopLevel) = f inputs
  in ppShow deltaTopLevel

generateDeltaInputs
  :: forall r. ADTensor r
  => Domains r
  -> ( Data.Vector.Vector (Dual r)
     , Data.Vector.Vector (Dual (DynamicTensor r)) )
generateDeltaInputs Domains{..} =
  let arrayToInput :: Int -> DynamicTensor r -> Dual (DynamicTensor r)
      arrayToInput i t = case someNatVal $ toInteger $ length $ tshapeD t of
        Just (SomeNat (_ :: Proxy n)) ->
          dFrom1X $ dInput1 @r @n $ toInputId i
        Nothing -> error "generateDeltaInputs: impossible someNatVal error"
      !v0 = V.generate (tlength domains0) (dInput0 . toInputId)
      !v1 = V.imap arrayToInput domains1
  in (v0, v1)
{-# SPECIALIZE generateDeltaInputs
  :: Domains Double
  -> ( Data.Vector.Vector (Dual Double)
     , Data.Vector.Vector (Dual (OT.Array Double)) ) #-}

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
      domains0 = OR.fromVector [nParams0] $ createRandomVector nParams0 seed
      domains1 =
        V.imap (\i sz ->
                  OT.fromVector [sz]
                  $ createRandomVector sz (seed + sz + i)) vParams1
      totalParams = nParams0
                    + V.sum vParams1
  in ( (nParams0, V.length vParams1)
     , totalParams
     , range
     , Domains{..} )

initializerFixed01 :: Int -> Double -> (Int, [Int])
                   -> ((Int, Int), Int, Double, Domains Double)
initializerFixed01 seed range (nParams0, lParams1) =
  initializerFixed seed range (nParams0, lParams1, undefined, undefined)
