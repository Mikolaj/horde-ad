{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | This is a shim module provided exclusively to use old tests.
module HordeAd.Core.DualNumber2
  ( ADVal, dD, pattern D, Dual
  , ADModeAndNum, HasDelta
  , fromX1, from1X
  , Vec, vecToV, vToVec
  , SNat(..), staticNatValue, staticNatFromProxy
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
  , addParameters, dotParameters
  , sumElements10, index10, minimum0, maximum0
  , (<.>!), (<.>!!)
  , fromList1, fromVector1, konst1, append1, slice1, reverse1
  , build1Elementwise, build1Closure
  , map1Elementwise
  , -- * Re-exports
    ADMode(..)
  , IsPrimal, IsPrimalWithScalar, IsPrimalAndHasFeatures, IsPrimalAndHasInputs
  , Domain0, DomainR, Domains
  , domains0, domainsR, mkDomains, emptyDomain0, nullDomains
  , Domain1, domains1
  , ADInputs
  , at0, at1, ifoldlDual', foldlDual'
  , domainsFromD01, domainsFrom01, domainsFrom0V
  , listsToParameters, listsToParameters4, domainsD0
  , valueGeneral, valueOnDomains, revOnADInputs, revOnDomains
  , constant, scale, logistic, altSumElements10
  , softMax, lossCrossEntropy, lossCrossEntropyV
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA

import           HordeAd.Core.Delta (Delta0, ForwardDerivative)
import           HordeAd.Core.DualClass hiding (IsPrimal)
import qualified HordeAd.Core.DualClass as DualClass
import           HordeAd.Core.DualNumber (dD, dDnotShared)
import qualified HordeAd.Core.DualNumber as DualNumber
import qualified HordeAd.Core.Engine as Engine
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorADVal (ADTensor)
import           HordeAd.Core.TensorClass
import           HordeAd.Internal.TensorOps

pattern D :: a -> Dual a -> DualNumber.ADVal a
pattern D u u' <- DualNumber.D u u'
{-# COMPLETE D #-}

type Domain1 r = DomainR r

domains1 :: Domains r -> Domain1 r
domains1 = domainsR

type ADInputs d r = Engine.ADInputs r

data ADMode =
    ADModeGradient
  | ADModeDerivative
  | ADModeValue
  deriving Show

type ADVal (d :: ADMode) a = DualNumber.ADVal a

type IsPrimal (d :: ADMode) a =
  DualClass.IsPrimal a

type IsPrimalWithScalar (d :: ADMode) a r =
  DualNumber.IsPrimalWithScalar a r

type IsPrimalAndHasFeatures (d :: ADMode) a r =
  DualNumber.IsPrimalWithScalar a r

type IsPrimalAndHasInputs (d :: ADMode) a r =
  DualNumber.IsPrimalWithScalar a r

type ADModeAndNum (d :: ADMode) r =
  ( DualNumber.ADNum r
  , ForwardDerivative r
  , Primal (DualNumber.ADVal r) ~ r
  , ScalarOf (DualNumber.ADVal r) ~ r
  , Tensor (DualNumber.ADVal r)
  , DynamicTensor (DualNumber.ADVal r)
  , TensorOf 1 (DualNumber.ADVal r) ~ DualNumber.ADVal (Vec r)
  , Fractional (TensorOf 0 (DualNumber.ADVal r))
  )

type HasDelta r = ( ADModeAndNum 'ADModeGradient r
                  , Dual r ~ Delta0 r )

-- shims:

-- The general case, needed for old hacky tests using only scalars.
valueGeneral
  :: forall r a. (ADTensor r, DomainsTensor r)
  => (Engine.ADInputs r -> a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueGeneral #-}
valueGeneral f parameters =
  let deltaInputs = Engine.generateDeltaInputs parameters
      inputs = Engine.makeADInputs parameters deltaInputs
  in f inputs

valueOnDomains
  :: ( ADTensor r, DynamicTensor r, DomainsTensor r
     , DualNumber.IsPrimalWithScalar a r, DomainsOf r ~ Domains r )
  => (Engine.ADInputs r -> DualNumber.ADVal a)
  -> Domains r
  -> a
{-# INLINE valueOnDomains #-}
valueOnDomains f parameters =
  let deltaInputs = Engine.generateDeltaInputs parameters
      inputs = Engine.makeADInputs parameters deltaInputs
  in snd $ Engine.revOnADInputs Nothing f inputs

revOnADInputs
  :: ( ADTensor r, DynamicTensor r, DomainsTensor r
     , DualNumber.IsPrimalWithScalar a r, DomainsOf r ~ Domains r )
  => a
  -> (Engine.ADInputs r -> DualNumber.ADVal a)
  -> Engine.ADInputs r
  -> (Domains r, a)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs = Engine.revOnADInputs  . Just

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: ( ADTensor r, DynamicTensor r, DomainsTensor r
     , DualNumber.IsPrimalWithScalar a r, DomainsOf r ~ Domains r )
  => a
  -> (Engine.ADInputs r -> DualNumber.ADVal a)
  -> Domains r
  -> (Domains r, a)
revOnDomains = Engine.revOnDomains . Just

-- * Simplified version compatibility shims

at0 :: ADModeAndNum d r => Engine.ADInputs r -> Int -> ADVal d r
{-# INLINE at0 #-}
at0 Engine.ADInputs{..} i = dD (OR.toVector inputPrimal0 V.! i) (inputDual0 V.! i)

at1 :: forall n r d. (KnownNat n, ADModeAndNum d r, TensorOf n r ~ OR.Array n r)
    => Engine.ADInputs r -> Int -> ADVal d (OR.Array n r)
{-# INLINE at1 #-}
at1 Engine.ADInputs{..} i = dD (tfromD $ inputPrimal1 V.! i)
                               (dFromD $ inputDual1 V.! i)

ifoldlDual' :: forall a d r. ADModeAndNum d r
             => (a -> Int -> ADVal d r -> a)
             -> a
             -> Engine.ADInputs r
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a Engine.ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = dD valX (inputDual0 V.! i)
        in f acc i b
  V.ifoldl' g a $ OR.toVector inputPrimal0

foldlDual' :: forall a d r. ADModeAndNum d r
            => (a -> ADVal d r -> a)
            -> a
            -> Engine.ADInputs r
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a Engine.ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = dD valX (inputDual0 V.! i)
        in f acc b
  V.ifoldl' g a $ OR.toVector inputPrimal0

domainsFromD01 :: DynamicTensor r => Domain0 r -> DomainR r -> Domains r
domainsFromD01 = mkDomains

domainsFrom01 :: (Numeric r, TensorOf 1 r ~ OR.Array 1 r, DynamicTensor r)
              => Vector r -> DomainR r -> Domains r
domainsFrom01 v0 = mkDomains (OR.fromVector [V.length v0] v0)

domainsFrom0V :: ( Numeric r, DTensorOf r ~ OD.Array r
                 , TensorOf 1 r ~ OR.Array 1 r, DynamicTensor r )
              => Vector r -> Data.Vector.Vector (Vector r) -> Domains r
domainsFrom0V v0 vs =
  domainsFrom01 v0 (V.map (\v -> OD.fromVector [V.length v] v) vs)

listsToParameters :: ( Numeric r, DTensorOf r ~ OD.Array r
                     , TensorOf 1 r ~ OR.Array 1 r, DynamicTensor r )
                  => ([r], [r]) -> Domains r
listsToParameters (a0, a1) =
  domainsFrom0V (V.fromList a0) (V.singleton (V.fromList a1))

listsToParameters4 :: ([Double], [Double], [Double], [Double]) -> Domains Double
listsToParameters4 (a0, a1, _a2, _aX) = listsToParameters (a0, a1)

domainsD0 :: Tensor r
          => (Numeric r, TensorOf 1 r ~ OR.Array 1 r) => Domains r -> Vector r
domainsD0 = OR.toVector . domains0

-- * Auxiliary definitions

fromX1 :: forall n d r. (ADModeAndNum d r, KnownNat n)
       => ADVal d (OD.Array r) -> ADVal d (TensorOf n r)
fromX1 (DualNumber.D u u') = dDnotShared (tfromD u) (dFromD u')

from1X :: (ADModeAndNum d r, KnownNat n)
       => ADVal d (TensorOf n r) -> ADVal d (OD.Array r)
from1X (DualNumber.D u u') = dDnotShared (dfromR u) (dFromR u')

-- Shims to reuse the tests for ordinary vectors.
type Vec r = OR.Array 1 r

vecToV :: Numeric r => Vec r -> Vector r
vecToV = OR.toVector

vToVec :: Numeric r => Vector r  -> Vec r
vToVec v = OR.fromVector [V.length v] v

-- All this is not needed in the simplified version, except for compilation
-- with the common test code.
-- | Sizes of tensor dimensions, of batches, etc., packed for passing
-- between functions as witnesses of type variable values.
data SNat (n :: Nat) where
  MkSNat :: KnownNat n => SNat n

staticNatValue :: forall n i. (KnownNat n, Num i) => SNat n -> i
{-# INLINE staticNatValue #-}
staticNatValue = fromInteger . natVal

staticNatFromProxy :: KnownNat n => Proxy n -> SNat n
staticNatFromProxy Proxy = MkSNat

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: IsPrimal d a => ADVal d a -> ADVal d a
ensureToplevelSharing (DualNumber.D u u') = dD u u'

scaleNotShared :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scaleNotShared a (DualNumber.D u u') = dDnotShared (a * u) (dScale a u')

addNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
addNotShared (DualNumber.D u u') (DualNumber.D v v') = dDnotShared (u + v) (dAdd u' v')

multNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
multNotShared (DualNumber.D u u') (DualNumber.D v v') =
  dDnotShared (u * v) (dAdd (dScale v u') (dScale u v'))

addParameters :: ( Numeric r, Num (Vector r), DTensorOf r ~ OD.Array r
                 , Tensor r, DynamicTensor r)
              => Domains r -> Domains r -> Domains r
addParameters paramsA paramsB =
  mkDomains (domains0 paramsA + domains0 paramsB)
            (V.zipWith (+) (domainsR paramsA) (domainsR paramsB))

-- Dot product and sum respective ranks and then sum it all.
dotParameters
  :: Tensor r
  => (Numeric r, DTensorOf r ~ OD.Array r, TensorOf 1 r ~ OR.Array 1 r)
  => Domains r -> Domains r -> r
dotParameters paramsA paramsB =
  domains0 paramsA `tdot0R` domains0 paramsB
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1)
          (domainsR paramsA) (domainsR paramsB))


-- * Legacy operations needed to re-use vector differentiation tests

-- Operations resulting in a scalar

sumElements10 :: Tensor r => TensorOf 1 r -> r
sumElements10 = tunScalar . tsum

index10 :: Tensor r => TensorOf 1 r -> Int -> r
index10 d ix = tunScalar $ d ! (singletonIndex $ fromIntegral ix)

minimum0 :: (KnownNat n, Tensor r) => TensorOf n r -> r
minimum0 = tunScalar . tminimum

maximum0 :: (KnownNat n, Tensor r) => TensorOf n r -> r
maximum0 = tunScalar . tmaximum

-- | Dot product.
infixr 8 <.>!
(<.>!) :: Tensor r => TensorOf 1 r -> TensorOf 1 r -> r
(<.>!) u v = tunScalar $ tdot0 u v

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: Tensor r => TensorOf 1 r -> TensorOf 1 (Primal r) -> r
(<.>!!) u s = (<.>!) u (tconstant s)


-- Operations resulting in a vector (really, a OR.Array)

-- @1@ means rank one, so the dual component represents a vector.
fromList1 :: Tensor r => [r] -> TensorOf 1 r
fromList1 = tfromList . map tscalar

fromVector1 :: Tensor r => Data.Vector.Vector r -> TensorOf 1 r
fromVector1 = tfromVector . V.map tscalar

konst1 :: Tensor r => r -> Int -> TensorOf 1 r
konst1 d n = tkonst n (tscalar d)

append1 :: Tensor r => TensorOf 1 r -> TensorOf 1 r -> TensorOf 1 r
append1 = tappend

slice1 :: Tensor r => Int -> Int -> TensorOf 1 r -> TensorOf 1 r
slice1 = tslice

reverse1 :: Tensor r => TensorOf 1 r -> TensorOf 1 r
reverse1 = treverse


-- Build and map variants

-- Fake rank 1. This is still an array of delta expressions, thinly wrapped,
-- instead of a single delta expression representing an array.
-- We gain a little by storing the primal part in an unboxed vector.
build1Elementwise
  :: Tensor r
  => Int -> (Int -> r) -> TensorOf 1 r
build1Elementwise n f = tfromList $ map (tscalar . f) [0 .. n - 1]
  -- equivalent to @fromVector1 $ build1POPL n f@

build1Closure
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1Closure n f =
  let g i = let DualNumber.D u _ = f i in u
      h i = let DualNumber.D _ u' = f $ fromIntegral i in u'
  in dD (OR.fromList [n] $ map g [0 .. n - 1])
        (dBuildR n (dScalarR . h))

map1Elementwise
  :: Tensor r
  => (r -> r) -> TensorOf 1 r -> TensorOf 1 r
map1Elementwise f = tmap1 (tscalar . f . tunScalar)
    -- equivalent to
    -- @fromVector1 . map1POPL f . rank1toVector
    --   where rank1toVector d@(D v _v') = V.generate (llength d) (lindex0 d)@


-- These can't be easily generalized to non-ADVal without causing
-- typing problems where this special variant is used, so it has to stay
-- for the sake of old tests.
scale :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scale a (DualNumber.D u u') = dD (a * u) (dScale a u')

constant :: IsPrimal d a => a -> ADVal d a
constant a = dD a dZero

logistic :: (Floating a, IsPrimal d a) => ADVal d a -> ADVal d a
logistic (DualNumber.D u u') =
  let y = recip (1 + exp (- u))
  in dD y (dScale (y * (1 - y)) u')

foldl'0 :: ADModeAndNum d r
        => (ADVal d r -> ADVal d r -> ADVal d r)
        -> ADVal d r -> ADVal d (Vec r)
        -> ADVal d r
foldl'0 f uu' (DualNumber.D v v') =
  let g !acc ix p =
        f (dD p (dIndex0 v' (singletonIndex $ fromIntegral ix)
                            (flattenShape (tshapeR v)))) acc
  in V.ifoldl' g uu' (OR.toVector v)

altSumElements10 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
altSumElements10 = foldl'0 (+) 0

sumElementsVectorOfDual
  :: ADModeAndNum d r => Data.Vector.Vector (ADVal d r) -> ADVal d r
sumElementsVectorOfDual = V.foldl' (+) 0

softMax :: ADModeAndNum d r
        => Data.Vector.Vector (ADVal d r)
        -> Data.Vector.Vector (ADVal d r)
softMax us =
  let expUs = V.map exp us  -- used twice below, so named, to enable sharing
      sumExpUs = sumElementsVectorOfDual expUs
  in V.map (\r -> r * recip sumExpUs) expUs

scaleADVal :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scaleADVal a (DualNumber.D u u') = dD (a * u) (dScale a u')

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy :: forall d r. ADModeAndNum d r
                 => Vector r
                 -> Data.Vector.Vector (ADVal d r)
                 -> ADVal d r
lossCrossEntropy targ res =
  let f :: ADVal d r -> Int -> ADVal d r -> ADVal d r
      f !acc i d = acc + scaleADVal (targ V.! i) (log d)
  in negate $ V.ifoldl' f 0 res

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyV :: ADModeAndNum d r
                  => Vec r
                  -> ADVal d (Vec r)
                  -> ADVal d r
lossCrossEntropyV targ res = negate $ log res <.>!! targ
