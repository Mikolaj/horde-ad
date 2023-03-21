-- | The implementation of calculating gradient, derivative and value
-- of an objective function defined on dual numbers, as defined
-- in "HordeAd.Core.DualNumber". Together with that module, this forms
-- the basic high-level API of the horde-ad library. Optimizers, etc.,
-- are add-ons.
module HordeAd.Core.Engine2
  ( -- * The most often used part of the high-level API
    revOnDomainsFun, revOnDomains, fwdOnDomains, valueOnDomains
  , -- * The less often used part of the high-level API
    valueGeneral
  , -- * Operations exposed not for the library users but add-on makers
    revOnADInputsFun, revOnADInputs, fwdOnADInputs
  , generateDeltaInputs, initializerFixed, initializerFixed01
  , -- * Internal operations, exposed, e.g., for tests
    slowFwdOnADInputs, slowFwdOnDomains
  , prettyPrintDf
  , domainsFromD01, domainsFrom01, domainsFrom0V
  , listsToParameters, listsToParameters4, domainsD0
  , ADInputs(..)
  , makeADInputs, nullADInputs, at0, at1
  , ifoldlDual', foldlDual'
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Text.Show.Pretty (ppShow)

import HordeAd.Core.Delta (derivativeFromDelta, gradientFromDelta, toInputId)
import HordeAd.Core.DualClass2
  (HasInputs (..), dFromD, dFromR, dInput0, dInputR, dummyDual, packDeltaDt)
import HordeAd.Core.DualNumber2
import HordeAd.Core.TensorClass

-- These are optimized as "pair of vectors" representing vectors of @ADVal@
-- in an efficient way (especially, or only, with gradient descent,
-- where the vectors are reused in some ways).

data ADInputs d r = ADInputs
  { inputPrimal0 :: Domain0 r
  , inputDual0   :: Data.Vector.Vector (Dual d r)
  , inputPrimal1 :: DomainR r
  , inputDual1   :: Data.Vector.Vector (Dual d (DynamicTensor r))
  }

makeADInputs
  :: Domains r
  -> ( Data.Vector.Vector (Dual d r)
     , Data.Vector.Vector (Dual d (DynamicTensor r)) )
  -> ADInputs d r
{-# INLINE makeADInputs #-}
makeADInputs Domains{..} (vs0, vs1)
  = ADInputs domains0 vs0 domainsR vs1

inputsToDomains :: ADInputs d r -> Domains r
inputsToDomains ADInputs{..} =
  Domains inputPrimal0 inputPrimal1

nullADInputs :: Tensor r => ADInputs d r -> Bool
nullADInputs adinputs = nullDomains (inputsToDomains adinputs)

{- This is to slow:
at0 :: ADModeAndNum d r => ADInputs d r -> Int -> ADVal d r
{-# INLINE at0 #-}
at0 ADInputs{..} i = dD (tunScalar $ inputPrimal0 ! (singletonIndex i))
                        (inputDual0 V.! i)
-}
at0 :: ADModeAndNum d r => ADInputs d r -> Int -> ADVal d r
{-# INLINE at0 #-}
at0 ADInputs{..} i = D (OR.toVector inputPrimal0 V.! i) (inputDual0 V.! i)

at1 :: forall n r d. (KnownNat n, ADModeAndNum d r, TensorOf n r ~ OR.Array n r)
    =>  ADInputs d r -> Int -> ADVal d (OR.Array n r)
{-# INLINE at1 #-}
at1 ADInputs{..} i = dD (tfromD $ inputPrimal1 V.! i)
                        (dFromD $ inputDual1 V.! i)

ifoldlDual' :: forall a d r. ADModeAndNum d r
             => (a -> Int -> ADVal d r -> a)
             -> a
             -> ADInputs d r
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = dD valX (inputDual0 V.! i)
        in f acc i b
  V.ifoldl' g a $ OR.toVector inputPrimal0

foldlDual' :: forall a d r. ADModeAndNum d r
            => (a -> ADVal d r -> a)
            -> a
            -> ADInputs d r
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = dD valX (inputDual0 V.! i)
        in f acc b
  V.ifoldl' g a $ OR.toVector inputPrimal0


-- * Evaluation that ignores the dual part of the dual numbers.
-- It's intended for efficiently calculating the value of the function only.

-- The general case, needed for old hacky tests using only scalars.
valueGeneral
  :: Tensor r
  => (ADInputs 'ADModeValue r -> a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueGeneral #-}
valueGeneral f domains@Domains{..} =
  let replicateDummy len = V.replicate len dummyDual
      inputs = makeADInputs domains
                            ( replicateDummy (tlength domains0)  -- dummy
                            , replicateDummy (V.length domainsR) )
  in f inputs

valueOnDomains
  :: Tensor r
  => (ADInputs 'ADModeValue r -> ADVal 'ADModeValue a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueOnDomains #-}
valueOnDomains f parameters =
  let D v _ = valueGeneral f parameters
  in v


-- * Evaluation that computes gradients.

revOnADInputsFun
  :: (HasDelta r, IsPrimalAndHasInputs 'ADModeGradient a r)
  => (a -> a)
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> ADInputs 'ADModeGradient r
  -> (Domains r, a)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputsFun #-}
revOnADInputsFun dt f inputs@ADInputs{..} =
  let dim0 = tlength inputPrimal0
      dim1 = V.length inputPrimal1
      -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started
      !(D v deltaTopLevel) = f inputs
      deltaDt = packDeltaDt (dt v) v deltaTopLevel
  in let gradient = gradientFromDelta dim0 dim1 deltaDt
     in (gradient, v)

revOnADInputs
  :: (HasDelta r, IsPrimalAndHasInputs 'ADModeGradient a r)
  => a
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> ADInputs 'ADModeGradient r
  -> (Domains r, a)
{-# INLINE revOnADInputs #-}
revOnADInputs = revOnADInputsFun . const

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newbies may have trouble understanding it.
-- Also, as of now, @revOnDomains@ is restricted to objective functions with scalar
-- codomains, while VJP is fully general.
revOnDomainsFun
  :: (HasDelta r, IsPrimalAndHasInputs 'ADModeGradient a r)
  => (a -> a)
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> Domains r
  -> (Domains r, a)
revOnDomainsFun dt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in revOnADInputsFun dt f inputs

revOnDomains
  :: (HasDelta r, IsPrimalAndHasInputs 'ADModeGradient a r)
  => a
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient a)
  -> Domains r
  -> (Domains r, a)
revOnDomains = revOnDomainsFun . const


-- * The slow evaluation for derivatives that uses the same
-- delta expressions as for gradients. See @fwdOnDomains@
-- for a fast variant.

slowFwdOnADInputs
  :: HasDelta r
  => ADInputs 'ADModeGradient r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
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
  :: HasDelta r
  => Domains r
  -> (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> (r, r)
slowFwdOnDomains parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in slowFwdOnADInputs inputs f ds


-- * Evaluation for efficiently computing forward derivatives.

fwdOnADInputs
  :: ADInputs 'ADModeDerivative r
  -> (ADInputs 'ADModeDerivative r -> ADVal 'ADModeDerivative a)
  -> (Dual 'ADModeDerivative a, a)
{-# INLINE fwdOnADInputs #-}
fwdOnADInputs inputs f =
  let D v d = f inputs
  in (d, v)

-- JVP (jacobian-vector product) or Rop (right operation) are alternative
-- names, but newbies may have trouble understanding it.
-- The direction vector ds is taken as an extra argument.
--
-- The type equality constraint is needed, because the `Dual` type family
-- can't declare it, because it needs to remain injective.
fwdOnDomains
  :: ( Numeric r, Dual 'ADModeDerivative r ~ r
     , Dual 'ADModeDerivative (DynamicTensor r) ~ DynamicTensor r
     , TensorOf 1 r ~ OR.Array 1 r )
  => Domains r
  -> (ADInputs 'ADModeDerivative r -> ADVal 'ADModeDerivative a)
  -> Domains r  -- ds
  -> (Dual 'ADModeDerivative a, a)
fwdOnDomains parameters f Domains{..} =
  let inputs =
        makeADInputs
          parameters
          (V.convert (OR.toVector domains0), domainsR)  -- ds
  in fwdOnADInputs inputs f


-- * Additional mechanisms

prettyPrintDf
  :: HasDelta r
  => (ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> Domains r
  -> String
prettyPrintDf f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
      !(D _ deltaTopLevel) = f inputs
  in ppShow deltaTopLevel

generateDeltaInputs
  :: forall r. HasDelta r
  => Domains r
  -> ( Data.Vector.Vector (Dual 'ADModeGradient r)
     , Data.Vector.Vector (Dual 'ADModeGradient (OD.Array r)) )
generateDeltaInputs Domains{..} =
  let arrayToInput :: Int -> OD.Array r -> Dual 'ADModeGradient (OD.Array r)
      arrayToInput i t = case someNatVal $ toInteger $ length $ OD.shapeL t of
        Just (SomeNat (_ :: Proxy n)) ->
          dFromR $ dInputR @'ADModeGradient @r @n $ toInputId i
        Nothing -> error "generateDeltaInputs: impossible someNatVal error"
      !v0 = V.generate (tlength domains0) (dInput0 . toInputId)
      !v1 = V.imap arrayToInput domainsR
  in (v0, v1)
{-# SPECIALIZE generateDeltaInputs
  :: Domains Double
  -> ( Data.Vector.Vector (Dual 'ADModeGradient Double)
     , Data.Vector.Vector (Dual 'ADModeGradient (OD.Array Double)) ) #-}

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
      domainsR =
        V.imap (\i sz ->
                  OD.fromVector [sz]
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

-- * Simplified version compatibility shims

domainsFromD01 :: Domain0 r -> DomainR r -> Domains r
domainsFromD01 = Domains

domainsFrom01 :: (Numeric r, TensorOf 1 r ~ OR.Array 1 r)
              => Vector r -> DomainR r -> Domains r
domainsFrom01 v0 = Domains (OR.fromVector [V.length v0] v0)

domainsFrom0V :: ( Numeric r, DynamicTensor r ~ OD.Array r
                 , TensorOf 1 r ~ OR.Array 1 r )
              => Vector r -> Data.Vector.Vector (Vector r) -> Domains r
domainsFrom0V v0 vs =
  domainsFrom01 v0 (V.map (\v -> OD.fromVector [V.length v] v) vs)

listsToParameters :: ( Numeric r, DynamicTensor r ~ OD.Array r
                     , TensorOf 1 r ~ OR.Array 1 r )
                  => ([r], [r]) -> Domains r
listsToParameters (a0, a1) =
  domainsFrom0V (V.fromList a0) (V.singleton (V.fromList a1))

listsToParameters4 :: ([Double], [Double], [Double], [Double]) -> Domains Double
listsToParameters4 (a0, a1, _a2, _aX) = listsToParameters (a0, a1)

domainsD0 :: (Numeric r, TensorOf 1 r ~ OR.Array 1 r) => Domains r -> Vector r
domainsD0 = OR.toVector . domains0
