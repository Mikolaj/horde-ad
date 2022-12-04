{-# LANGUAGE CPP, DataKinds, FlexibleInstances, GADTs, QuantifiedConstraints,
             RankNTypes, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.DualNumber
  ( module HordeAd.Core.DualNumber
  , ADVal, dD, dDnotShared
  , ADMode(..), ADModeAndNum
  , IsPrimal (..), IsPrimalAndHasFeatures, HasDelta
  , Domain0, Domain1, Domains(..), nullDomains  -- an important re-export
  , Ast(..), AstInt(..), CodeOut(..), RelOut(..)
  ) where

import Prelude

import           Data.List.Index (imap)
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import qualified Numeric.LinearAlgebra.Devel

import HordeAd.Core.DualClass
import HordeAd.Internal.Delta (Domain0, Domain1, Domains (..), nullDomains)

-- * Auxiliary definitions

-- This is not needed in the simplified version, except for compilation
-- with the common test code.
-- | Sizes of tensor dimensions, of batches, etc., packed for passing
-- between functions as witnesses of type variable values.
data StaticNat (n :: Nat) where
  MkSN :: KnownNat n => StaticNat n

staticNatValue :: forall n i. (KnownNat n, Num i) => StaticNat n -> i
{-# INLINE staticNatValue #-}
staticNatValue = fromInteger . natVal

staticNatFromProxy :: KnownNat n => Proxy n -> StaticNat n
staticNatFromProxy Proxy = MkSN

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: IsPrimal d a => ADVal d a -> ADVal d a
ensureToplevelSharing (D u u') = dD u u'

scaleNotShared :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scaleNotShared a (D u u') = dDnotShared (a * u) (dScale a u')

addNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
addNotShared (D u u') (D v v') = dDnotShared (u + v) (dAdd u' v')

multNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
multNotShared (D u u') (D v v') =
  dDnotShared (u * v) (dAdd (dScale v u') (dScale u v'))

addParameters :: Num (Vector r)
              => Domains r -> Domains r -> Domains r
addParameters (Domains a0 a1) (Domains b0 b1) =
  Domains (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: Numeric r => Domains r -> Domains r -> r
dotParameters (Domains a0 a1) (Domains b0 b1) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if V.null v1 || V.null u1
      then 0
      else v1 LA.<.> u1) a1 b1)


-- * General operations, for any tensor rank

-- These instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (ADVal d a) where

instance Ord (ADVal d a) where

instance (Num a, IsPrimal d a) => Num (ADVal d a) where
  D u u' + D v v' = dD (u + v) (dAdd u' v')
  D u u' - D v v' = dD (u - v) (dAdd u' (dScale (-1) v'))
  D u u' * D v v' = dD (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = dD (negate v) (dScale (-1) v')
  abs (D v v') = dD (abs v) (dScale (signum v) v')
  signum (D v _) = dD (signum v) dZero
  fromInteger = constant . fromInteger

instance (Real a, IsPrimal d a) => Real (ADVal d a) where
  toRational = undefined  -- TODO?

instance (Fractional a, IsPrimal d a) => Fractional (ADVal d a) where
  D u u' / D v v' =
    let recipSq = recip (v * v)  -- ensure sharing; also elsewhere
    in dD (u / v) (dAdd (dScale (v * recipSq) u') (dScale (- u * recipSq) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in dD (recip v) (dScale minusRecipSq v')
  fromRational = constant . fromRational

instance (Floating a, IsPrimal d a) => Floating (ADVal d a) where
  pi = constant pi
  exp (D u u') = let expU = exp u
                 in dD expU (dScale expU u')
  log (D u u') = dD (log u) (dScale (recip u) u')
  sqrt (D u u') = let sqrtU = sqrt u
                  in dD sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D u u' ** D v v' = dD (u ** v) (dAdd (dScale (v * (u ** (v - 1))) u')
                                       (dScale ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D u u') = dD (sin u) (dScale (cos u) u')
  cos (D u u') = dD (cos u) (dScale (- (sin u)) u')
  tan (D u u') = let cosU = cos u
                 in dD (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D u u') = dD (asin u) (dScale (recip (sqrt (1 - u*u))) u')
  acos (D u u') = dD (acos u) (dScale (- recip (sqrt (1 - u*u))) u')
  atan (D u u') = dD (atan u) (dScale (recip (1 + u*u)) u')
  sinh (D u u') = dD (sinh u) (dScale (cosh u) u')
  cosh (D u u') = dD (cosh u) (dScale (sinh u) u')
  tanh (D u u') = let y = tanh u
                  in dD y (dScale (1 - y * y) u')
  asinh (D u u') = dD (asinh u) (dScale (recip (sqrt (1 + u*u))) u')
  acosh (D u u') = dD (acosh u) (dScale (recip (sqrt (u*u - 1))) u')
  atanh (D u u') = dD (atanh u) (dScale (recip (1 - u*u)) u')

instance (RealFrac a, IsPrimal d a) => RealFrac (ADVal d a) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance (RealFloat a, IsPrimal d a) => RealFloat (ADVal d a) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in dD (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

constant :: IsPrimal d a => a -> ADVal d a
constant a = dD a dZero

scale :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scale a (D u u') = dD (a * u) (dScale a u')

logistic :: (Floating a, IsPrimal d a) => ADVal d a -> ADVal d a
logistic (D u u') =
  let y = recip (1 + exp (- u))
  in dD y (dScale (y * (1 - y)) u')

-- Optimized and more clearly written @u ** 2@.
square :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a
square (D u u') = dD (u * u) (dScale (2 * u) u')

squaredDifference :: (Num a, IsPrimal d a)
                  => a -> ADVal d a -> ADVal d a
squaredDifference targ res = square $ res - constant targ

relu :: (ADModeAndNum d r, IsPrimalAndHasFeatures d a r)
     => ADVal d a -> ADVal d a
relu v@(D u _) =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0) u
  in scale oneIfGtZero v

reluLeaky :: (ADModeAndNum d r, IsPrimalAndHasFeatures d a r)
          => ADVal d a -> ADVal d a
reluLeaky v@(D u _) =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0.01) u
  in scale oneIfGtZero v

varAst :: String -> ADVal d (Ast d a)
varAst s = dDnotShared (AstVar s) undefined

liftToAst :: ADVal d a -> ADVal d (Ast d a)
liftToAst d = dDnotShared (AstConst d) undefined


-- * Operations resulting in a scalar

sumElements0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
sumElements0 (D u u') = dD (LA.sumElements u) (dSumElements0 u' (V.length u))

index10 :: ADModeAndNum d r => ADVal d (Vector r) -> Int -> ADVal d r
index10 (D u u') ix = dD (u V.! ix) (dIndex10 u' ix (V.length u))

indexAst10 :: ADVal d (Ast d (Vector r)) -> AstInt -> ADVal d (Ast d r)
indexAst10 (D u _) ix = dDnotShared (AstIndex u ix)
                                    undefined  -- dummy anyway
  -- TODO: despite dDnotShared, consider sharing Ast expressions,
  -- but within the primal part, not dual or both

minimum0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
minimum0 (D u u') =
  dD (LA.minElement u) (dIndex10 u' (LA.minIndex u) (V.length u))

maximum0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
maximum0 (D u u') =
  dD (LA.maxElement u) (dIndex10 u' (LA.maxIndex u) (V.length u))

foldl'0 :: ADModeAndNum d r
        => (ADVal d r -> ADVal d r -> ADVal d r)
        -> ADVal d r -> ADVal d (Vector r)
        -> ADVal d r
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (dD p (dIndex10 v' ix k)) acc
  in V.ifoldl' g uu' v

altSumElements0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
altSumElements0 = foldl'0 (+) 0

-- | Dot product.
infixr 8 <.>!
(<.>!) :: ADModeAndNum d r
       => ADVal d (Vector r) -> ADVal d (Vector r) -> ADVal d r
(<.>!) (D u u') (D v v') = dD (u LA.<.> v) (dAdd (dDot0 v u') (dDot0 u v'))

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: ADModeAndNum d r
        => ADVal d (Vector r) -> Vector r -> ADVal d r
(<.>!!) (D u u') v = dD (u LA.<.> v) (dDot0 v u')

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

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy :: forall d r. ADModeAndNum d r
                 => Vector r
                 -> Data.Vector.Vector (ADVal d r)
                 -> ADVal d r
lossCrossEntropy targ res =
  let f :: ADVal d r -> Int -> ADVal d r -> ADVal d r
      f !acc i d = acc + scale (targ V.! i) (log d)
  in negate $ V.ifoldl' f 0 res

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyV :: ADModeAndNum d r
                  => Vector r
                  -> ADVal d (Vector r)
                  -> ADVal d r
lossCrossEntropyV targ res = negate $ log res <.>!! targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyV
  :: ADModeAndNum d r
  => Vector r -> ADVal d (Vector r) -> ADVal d r
lossSoftMaxCrossEntropyV target (D u u') =
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let expU = exp (u - LA.scalar (LA.maxElement u))
      sumExpU = LA.sumElements expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = LA.scaleRecip sumExpU expU
      softMaxU = LA.scale recipSum expU
  in dD (negate $ log softMaxU LA.<.> target)  -- TODO: avoid: log . exp
        (dDot0 (softMaxU - target) u')


-- * Operations resulting in a vector

-- @1@ means rank one, so the dual component represents a vector.
fromList1 :: ADModeAndNum d r
          => [ADVal d r] -> ADVal d (Vector r)
fromList1 l = dD (V.fromList $ map (\(D u _) -> u) l)  -- I hope this fuses
                 (dFromList1 $ map (\(D _ u') -> u') l)

fromVector1 :: ADModeAndNum d r
            => Data.Vector.Vector (ADVal d r) -> ADVal d (Vector r)
fromVector1 v = dD (V.convert $ V.map (\(D u _) -> u) v)  -- I hope this fuses
                   (dFromVector1 $ V.map (\(D _ u') -> u') v)

konst1 :: ADModeAndNum d r => ADVal d r -> Int -> ADVal d (Vector r)
konst1 (D u u') n = dD (LA.konst u n) (dKonst1 u' n)

append1 :: ADModeAndNum d r
        => ADVal d (Vector r) -> ADVal d (Vector r)
        -> ADVal d (Vector r)
append1 (D u u') (D v v') = dD (u V.++ v) (dAppend1 u' (V.length u) v')

slice1 :: ADModeAndNum d r
       => Int -> Int -> ADVal d (Vector r) -> ADVal d (Vector r)
slice1 i n (D u u') = dD (V.slice i n u) (dSlice1 i n u' (V.length u))

reverse1 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d (Vector r)
reverse1 (D u u') = dD (V.reverse u) (dReverse1 u')

-- Build variants

build1POPL :: Int -> (Int -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
build1POPL n f = V.fromList $ map f [0 .. n - 1]

-- Fake rank 1. This is still an array of delta expressions, thinly wrapped,
-- instead of a single delta expression representing an array.
-- We gain a little by storing the primal part in an unboxed vector.
build1Elementwise, build1Closure, build1
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vector r)
build1Elementwise n f = fromList1 $ map f [0 .. n - 1]
  -- equivalent to @fromVector1 $ build1POPL n f@

build1Closure n f =
  let g i = let D u _ = f i in u
      h i = let D _ u' = f i in u'
  in dD (V.fromList $ map g [0 .. n - 1]) (dBuild1 n h)

build1 = build1Closure

buildAst1
  :: ADModeAndNum d r
  => Int -> (String, ADVal d (Ast d r)) -> ADVal d (Vector r)
buildAst1 n (var, D u _) = case u of
-- TODO:
-- AstOp PlusOut [e1, e2] -> ... if works like bulk, replace by bulk
-- TODO:
-- AstCond b x1 x2 -> ...
--   handle conditionals that depend on var, so that we produce conditional
--   delta expressions of size proportional to the exponent of conditional
--   nesting, instead of proportional to the number of elements of the tensor
  AstIndex v (AstIntVar var2) | var2 == var -> slice1 0 n $ interpret v
  AstConst d -> konst1 d n
  _ ->  -- fallback to POPL (memory blowup, but avoids functions on tape)
    build1Elementwise n (interpretLambdaInt var u)

interpret :: Ast d a -> ADVal d a
interpret = undefined  -- TODO, easy but tedious; some code exists

interpretLambda :: String -> Ast d r -> ADVal d r -> ADVal d r
interpretLambda = undefined  -- TODO

interpretLambdaInt :: String -> Ast d r -> Int -> ADVal d r
interpretLambdaInt = undefined  -- TODO

map1POPL :: (ADVal d r -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
         -> Data.Vector.Vector (ADVal d r)
map1POPL f vd = V.map f vd

-- The list probably fuses away, which may make it a bit faster than
-- if written using @build1Elementwise@.
map1Elementwise, map1Closure
  :: ADModeAndNum d r
  => (ADVal d r -> ADVal d r) -> ADVal d (Vector r) -> ADVal d (Vector r)
map1Elementwise f _d@(D v v') =
  let k = V.length v
      g ix p = f $ dD p (dIndex10 v' ix k)
      ds = imap g $ V.toList v
  in fromList1 ds
    -- equivalent to @build1Elementwise (V.length v) $ \i -> f (index10 _d i)@
    -- equivalent to
    -- @fromVector1 . map1POPL f . rank1toVector
    --   where rank1toVector d@(D v _v') = V.generate (V.length v) (index10 d)@

map1Closure f d@(D v _) = build1Closure (V.length v) $ \i -> f (index10 d i)

mapAst1
  :: ADModeAndNum d r
  => (String, ADVal d (Ast d r)) -> ADVal d (Vector r) -> ADVal d (Vector r)
mapAst1 (var, D u _) e@(D v _v') = case u of
-- TODO:
-- AstOp PlusOut [e1, e2] -> ... if works like bulk, replace by bulk
-- AstCond b x1 x2 -> ...
  AstVar var2 | var2 == var -> e  -- identity mapping
  AstVar _var2 -> undefined  -- TODO: a problem, nested map or build
  AstConst d -> konst1 d (V.length v)
  _ ->  -- fallback to POPL (memory blowup, but avoids functions on tape)
    map1Elementwise (interpretLambda var u) e

-- No padding; remaining areas ignored.
maxPool1 :: ADModeAndNum d r
         => Int -> Int -> ADVal d (Vector r) -> ADVal d (Vector r)
maxPool1 ksize stride v@(D u _) =
  let slices = [slice1 i ksize v | i <- [0, stride .. V.length u - ksize]]
  in fromList1 $ map maximum0 slices

softMaxV :: ADModeAndNum d r
         => ADVal d (Vector r) -> ADVal d (Vector r)
softMaxV d@(D u _) =
  let expU = exp d  -- shared in 2 places, though cse may do this for us
      sumExpU = sumElements0 expU
  in konst1 (recip sumExpU) (V.length u) * expU


-- TODO: move to separate orphan module(s) at some point
-- This requires UndecidableInstances

instance (Num (Vector r), Numeric r, Ord r)
         => Real (Vector r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Num (Vector r), Numeric r, Fractional r, Ord r)
         => RealFrac (Vector r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

-- TODO: is there atan2 in hmatrix or can it be computed faster than this?
instance ( Floating (Vector r), Numeric r, RealFloat r )
         => RealFloat (Vector r) where
  atan2 = Numeric.LinearAlgebra.Devel.zipVectorWith atan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain

type instance Element Double = Double

type instance Element Float = Float

instance MonoFunctor Double where
  omap f = f

instance MonoFunctor Float where
  omap f = f
