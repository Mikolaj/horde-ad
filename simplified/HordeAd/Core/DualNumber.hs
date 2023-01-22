{-# LANGUAGE CPP, DataKinds, FlexibleInstances, FunctionalDependencies, GADTs,
             MultiParamTypeClasses, QuantifiedConstraints, RankNTypes,
             TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.DualNumber
  ( module HordeAd.Core.DualNumber
  , ADVal, dD, dDnotShared
  , ADMode(..), ADModeAndNum
  , IntOf, VectorOf
  , IsPrimal (..), IsPrimalAndHasFeatures, IsPrimalAndHasInputs, HasDelta
  , Element, HasPrimal(..)
  , VectorLike(..), ADReady
  , Domain0, Domain1, Domains(..), nullDomains  -- an important re-export
  , -- temporarily re-exported, until these are wrapped in sugar
    Ast0(..), AstPrimalPart0(..), Ast1(..), AstPrimalPart1(..)
  , AstVarName(..), AstVar(..)
  , AstInt(..), AstBool(..)
  , CodeOut(..), CodeIntOut(..), CodeBoolOut(..), RelOut(..)
  ) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.MonoTraversable (MonoFunctor (omap))
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.DualClass
import HordeAd.Internal.Delta
  (Domain0, Domain1, Domains (..), atIndexInTensorR, isTensorDummy, nullDomains)

-- * Auxiliary definitions

type Vec r = OR.Array 1 r

vecToV :: Numeric r => Vec r -> Vector r
vecToV = OR.toVector

vToVec :: Numeric r => Vector r  -> Vec r
vToVec v = OR.fromVector [V.length v] v

-- This is not needed in the simplified version, except for compilation
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
ensureToplevelSharing (D u u') = dD u u'

scaleNotShared :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scaleNotShared a (D u u') = dDnotShared (a * u) (dScale a u')

addNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
addNotShared (D u u') (D v v') = dDnotShared (u + v) (dAdd u' v')

multNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
multNotShared (D u u') (D v v') =
  dDnotShared (u * v) (dAdd (dScale v u') (dScale u v'))

addParameters :: (Numeric r, Num (Vector r))
              => Domains r -> Domains r -> Domains r
addParameters (Domains a0 a1) (Domains b0 b1) =
  Domains (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: Numeric r => Domains r -> Domains r -> r
dotParameters (Domains a0 a1) (Domains b0 b1) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OT.toVector v1 LA.<.> OT.toVector u1) a1 b1)


-- * General operations, for any tensor rank

-- These instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (ADVal d a) where

instance Ord (ADVal d a) where

instance (Num a, IsPrimal d a) => Num (ADVal d a) where
  D u u' + D v v' = dD (u + v) (dAdd u' v')
  D u u' - D v v' = dD (u - v) (dAdd u' (dScale (fromInteger (-1)) v'))
    -- without @fromInteger@, this is interpreted as @negate 1@,
    -- causing a crash for ranked tensors (can't guess the rank of @1@
    -- and then no other argument to derive the rank of @negate@);
    -- dynamic tensors dont check at all; shaped have all needed info in types
  D u u' * D v v' = dD (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = dD (negate v) (dScale (fromInteger (-1)) v')
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

instance (Num a, IsPrimal d a) => HasPrimal (ADVal d a) where
  type PrimalOf (ADVal d a) = a
  type DualOf (ADVal d a) = Dual d a
  constant a = dD a dZero
  scale a (D u u') = dD (a * u) (dScale a u')
  primalPart (D u _) = u
  dualPart (D _ u') = u'
  ddD = dD
  fromIntOf = constant . fromInteger . fromIntegral

instance HasPrimal Float where
  type PrimalOf Float = Float
  type DualOf Float = ()
  constant = id
  scale = (*)
  primalPart = id
  dualPart _ = ()
  ddD u _ = u
  fromIntOf = fromInteger . fromIntegral

instance HasPrimal Double where
  type PrimalOf Double = Double
  type DualOf Double = ()
  constant = id
  scale = (*)
  primalPart = id
  dualPart _ = ()
  ddD u _ = u
  fromIntOf = fromInteger . fromIntegral

-- The constraint requires UndecidableInstances.
instance (KnownNat n, Numeric r, Num (Vector r))
         => HasPrimal (OR.Array n r) where
  type PrimalOf (OR.Array n r) = OR.Array n r
  type DualOf (OR.Array n r) = ()
  constant = id
  scale = (*)
  primalPart = id
  dualPart _ = ()
  ddD u _ = u
  fromIntOf = fromInteger . fromIntegral

instance HasPrimal (Ast0 r) where
  type PrimalOf (Ast0 r) = AstPrimalPart0 r
  type DualOf (Ast0 r) = ()  -- TODO: data AstDualPart: dScale, dAdd, dkonst1
  constant = AstConstant0
  scale = AstScale0
  primalPart = AstPrimalPart0
  dualPart = error "TODO"
  ddD = error "TODO"
  fromIntOf = AstInt0

instance HasPrimal (Ast1 n r) where
  type PrimalOf (Ast1 n r) = AstPrimalPart1 n r
  type DualOf (Ast1 n r) = ()  -- TODO: data AstDualPart: dScale, dAdd, dkonst1
  constant = AstConstant1
  scale = AstScale1
  primalPart = AstPrimalPart1
  dualPart = error "TODO"
  ddD = error "TODO"
  fromIntOf = AstInt1

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

relu, reluLeaky
  :: ( HasPrimal a, MonoFunctor (PrimalOf a), Num (PrimalOf a)
     , Ord (Element (PrimalOf a)), Fractional (Element (PrimalOf a)) )
  => a -> a
relu v =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0) (primalPart v)
  in scale oneIfGtZero v

reluLeaky v =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0.01) (primalPart v)
  in scale oneIfGtZero v

-- TODO: bring back rank-poly relu by adding a class with Ast0 and Ast1
-- or even better generalize the function after omap above so that
-- it has a sensible Ast instance and then kill reluAst0 and reluAst1;
-- we'd need Conditional class that works with our AstBool type
-- and some sugar to be able to use >, &&, etc.
reluAst0
  :: (MonoFunctor (PrimalOf (Ast0 r)), Fractional r)
  => Ast0 r -> Ast0 r
reluAst0 v =
  let oneIfGtZero = omap (\(AstPrimalPart0 x) ->
                            AstPrimalPart0 $ AstCond0 (AstRel GtOut [x, 0]) 1 0)
                         (primalPart v)
  in scale oneIfGtZero v

reluAst1
  :: ( KnownNat n, Num (Vector r), MonoFunctor (PrimalOf (Ast1 n r))
     , Fractional r, Numeric r )
  => Ast1 n r -> Ast1 n r
reluAst1 v =
  let oneIfGtZero = omap (\(AstPrimalPart0 x) ->
                            AstPrimalPart0 $ AstCond0 (AstRel GtOut [x, 0]) 1 0)
                         (primalPart v)
  in scale oneIfGtZero v

-- * Operations resulting in a scalar

sumElements10 :: ADModeAndNum d r
              => ADVal d (Vec r) -> ADVal d r
sumElements10 = lsum10

index10 :: ADModeAndNum d r => ADVal d (Vec r) -> Int -> ADVal d r
index10 = lindex10

minimum0 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
minimum0 = lminimum0

maximum0 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
maximum0 = lmaximum0

foldl'0 :: ADModeAndNum d r
        => (ADVal d r -> ADVal d r -> ADVal d r)
        -> ADVal d r -> ADVal d (Vec r)
        -> ADVal d r
foldl'0 f uu' (D v v') =
  let k = llength v
      g !acc ix p = f (dD p (dIndex10 v' [ix] [k])) acc
  in V.ifoldl' g uu' (OR.toVector v)

altSumElements10 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
altSumElements10 = foldl'0 (+) 0

-- | Dot product.
infixr 8 <.>!
(<.>!) :: ADModeAndNum d r
       => ADVal d (Vec r) -> ADVal d (Vec r) -> ADVal d r
(<.>!) = ldot0

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: ADModeAndNum d r
        => ADVal d (Vec r) -> Vec r -> ADVal d r
(<.>!!) (D u u') v = dD (ldot0 u v) (dDot10 v u')

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
                  => Vec r
                  -> ADVal d (Vec r)
                  -> ADVal d r
lossCrossEntropyV targ res = negate $ log res <.>!! targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyV
  :: ADModeAndNum d r
  => Vec r -> ADVal d (Vec r) -> ADVal d r
lossSoftMaxCrossEntropyV target (D u u') =
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let expU = exp (u - lkonst1 (llength u) (lmaximum0 u))
      sumExpU = lsum10 expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = LA.scaleRecip sumExpU expU
      softMaxU = lkonst1 (llength expU) recipSum * expU
  in dD (negate $ log softMaxU `ldot0` target)  -- TODO: avoid: log . exp
        (dDot10 (softMaxU - target) u')


-- * Operations resulting in a vector

-- @1@ means rank one, so the dual component represents a vector.
fromList1 :: ADModeAndNum d r
          => [ADVal d r] -> ADVal d (Vec r)
fromList1 = lfromList1

fromVector1 :: ADModeAndNum d r
            => Data.Vector.Vector (ADVal d r) -> ADVal d (Vec r)
fromVector1 = lfromVector1

konst1 :: ADModeAndNum d r => ADVal d r -> Int -> ADVal d (Vec r)
konst1 d n = lkonst1 n d

append1 :: ADModeAndNum d r
        => ADVal d (Vec r) -> ADVal d (Vec r) -> ADVal d (Vec r)
append1 = lappend1

slice1 :: ADModeAndNum d r
       => Int -> Int -> ADVal d (Vec r) -> ADVal d (Vec r)
slice1 = lslice1

reverse1 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d (Vec r)
reverse1 = lreverse1

-- TODO: define Enum instance of (AstInt r) to enable AST for this.
-- No padding; remaining areas ignored.
maxPool1 :: ADModeAndNum d r
         => Int -> Int -> ADVal d (Vec r) -> ADVal d (Vec r)
maxPool1 ksize stride v =
  let slices = [slice1 i ksize v | i <- [0, stride .. llength v - ksize]]
  in fromList1 $ map maximum0 slices

softMaxV :: ADModeAndNum d r
         => ADVal d (Vec r) -> ADVal d (Vec r)
softMaxV d =
  let expU = exp d  -- shared in 2 places, though cse may do this for us
      sumExpU = sumElements10 expU
  in lkonst1 (llength d) (recip sumExpU) * expU

from10 :: ADModeAndNum d r => ADVal d (OR.Array 0 r) -> ADVal d r
from10 (D u u') = dD (OR.unScalar u) (dFrom10 u')

from01 :: ADModeAndNum d r => ADVal d r -> ADVal d (OR.Array 0 r)
from01 (D u u') = dD (OR.scalar u) (dFrom01 u')


-- * Build and map variants

build1POPL :: Int -> (Int -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
build1POPL n f = V.fromList $ map f [0 .. n - 1]

-- Fake rank 1. This is still an array of delta expressions, thinly wrapped,
-- instead of a single delta expression representing an array.
-- We gain a little by storing the primal part in an unboxed vector.
build1Elementwise
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1Elementwise n f = fromList1 $ map f [0 .. n - 1]
  -- equivalent to @fromVector1 $ build1POPL n f@

build1Closure
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1Closure n f =
  let g i = let D u _ = f i in u
      h i = let D _ u' = f i in u'
  in dD (lfromList1 $ map g [0 .. n - 1]) (dBuild01 [n] (\l -> h (head l)))

build1
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1 = build1Closure

map1POPL :: (ADVal d r -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
         -> Data.Vector.Vector (ADVal d r)
map1POPL f vd = V.map f vd

map1Elementwise
  :: ADModeAndNum d r
  => (ADVal d r -> ADVal d r) -> ADVal d (Vec r) -> ADVal d (Vec r)
map1Elementwise f d =
  build1Elementwise (llength d) $ \i -> f (index10 d i)
    -- equivalent to
    -- @fromVector1 . map1POPL f . rank1toVector
    --   where rank1toVector d@(D v _v') = V.generate (llength d) (index10 d)@

map1Closure
  :: ADModeAndNum d r
  => (ADVal d r -> ADVal d r) -> ADVal d (Vec r) -> ADVal d (Vec r)
map1Closure f d = build1Closure (llength d) $ \i -> f (index10 d i)


-- * Instances of VectorLike

instance (Numeric r, IntOf r ~ Int, VectorOf r ~ Vec r)
         => VectorLike (Vec r) r where
  llength = OR.size
  lminIndex = LA.minIndex . OR.toVector
  lmaxIndex = LA.maxIndex . OR.toVector

  lindex10 v ix = (V.! ix) $ OR.toVector v
  lsum10 = OR.sumA
  ldot0 u v = OR.toVector u LA.<.> OR.toVector v
  lminimum0 = LA.minElement . OR.toVector
  lmaximum0 = LA.maxElement . OR.toVector

  lfromList1 l = OR.fromList [length l] l
  lfromVector1 v = OR.fromVector [V.length v] $ V.convert v
  lkonst1 n r = OR.constant [n] r
  lappend1 = OR.append
  lslice1 i k = OR.slice [(i, k)]
  lreverse1 = OR.rev [0]
  lbuild1 n f = OR.generate [n] (\l -> f (head l))
  lmap1 = OR.mapA
  lzipWith = OR.zipWithA

instance VectorLike (Ast1 1 r) (Ast0 r) where
  llength = AstLength
  lminIndex = AstMinIndex
  lmaxIndex = AstMaxIndex

  lindex10 v ix = AstIndex10 v [ix]
  lsum10 = AstSum10
  ldot0 = AstDot10
  lminimum0 v = AstIndex10 v [AstMinIndex v]
  lmaximum0 v = AstIndex10 v [AstMaxIndex v]

  lfromList1 = AstFromList01
  lfromVector1 = AstFromVector01
  lkonst1 = AstKonst01
  lappend1 = AstAppend1
  lslice1 = AstSlice1
  lreverse1 = AstReverse1
  lbuild1 = astBuild1  -- TODO: this vectorizers depth-first, but is this
  lmap1 = astMap1      -- needed? should we vectorize the whole program instead?
  lzipWith = undefined  -- TODO: express all with build instead?

-- Not that this instance doesn't do vectorization. To enable it,
-- use the Ast instance, vectorize and finally interpret in ADVal.
-- The interpretation step uses this instance, including lbuild1
-- and lmap1, as a fallback for failed vectorization.
instance ADModeAndNum d r
         => VectorLike (ADVal d (Vec r)) (ADVal d r) where
  llength (D u _) = llength u
  lminIndex (D u _) = lminIndex u
  lmaxIndex (D u _) = lmaxIndex u

  lindex10 (D u u') ix = dD (lindex10 u ix) (dIndex10 u' [ix] [llength u])
  lsum10 (D u u') = dD (lsum10 u) (dSum10 [llength u] u')
  ldot0 (D u u') (D v v') = dD (ldot0 u v) (dAdd (dDot10 v u') (dDot10 u v'))
  lminimum0 (D u u') =
    dD (lminimum0 u) (dIndex10 u' [lminIndex u] [llength u])
  lmaximum0 (D u u') =
    dD (lmaximum0 u) (dIndex10 u' [lmaxIndex u] [llength u])

  lfromList1 l = dD (lfromList1 $ map (\(D u _) -> u) l)  -- I hope this fuses
                    (dFromList01 [length l] $ map (\(D _ u') -> u') l)
  lfromVector1 v = dD (lfromVector1 $ V.map (\(D u _) -> u) v)
                        -- I hope it fuses
                      (dFromVector01 [V.length v] $ V.map (\(D _ u') -> u') v)
  lkonst1 n (D u u') = dD (lkonst1 n u) (dKonst01 [n] u')
  lappend1 (D u u') (D v v') = dD (lappend1 u v) (dAppend1 u' (llength u) v')
  lslice1 i n (D u u') = dD (lslice1 i n u) (dSlice1 i n u' (llength u))
  lreverse1 (D u u') = dD (lreverse1 u) (dReverse1 u')
  lbuild1 = build1Closure  -- to test against build1Elementwise from Ast
  lmap1 = map1Closure  -- to test against map1Elementwise from Ast
  lzipWith = undefined

-- * AST-based build and map variants

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

astBuild1 :: AstInt r -> (AstInt r -> Ast0 r) -> Ast1 1 r
{-# NOINLINE astBuild1 #-}
astBuild1 n f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! build1Vectorize n ( freshAstVar
                              , AstFrom01 (f (AstIntVar freshAstVar)) )

astMap1 :: (Ast0 r -> Ast0 r) -> Ast1 1 r -> Ast1 1 r
{-# NOINLINE astMap1 #-}
astMap1 f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! map1Vectorize (freshAstVar, f (AstVar0 freshAstVar)) e

build1Vectorize
  :: AstInt r -> (AstVarName Int, Ast1 n r)
  -> Ast1 (1 + n) r
build1Vectorize n (var, u) =
  if not (intVarInAst1 var u)
  then AstKonst1 n u
  else case u of
    AstOp1 codeOut args ->
      AstOp1 codeOut $ map (\w -> build1Vectorize n (var, w)) args
    AstCond1 b v w ->
      if intVarInAstBool var b then
        -- This handles conditionals that depend on var,
        -- so that we produce conditional delta expressions
        -- of size proportional to the exponent of conditional
        -- nesting, instead of proportional to the number of elements
        -- of the tensor.
        AstSelect1 n (var, b)
                   (build1Vectorize n (var, v))
                   (build1Vectorize n (var, w))
      else
        AstCond1 b (build1Vectorize n (var, v))
                   (build1Vectorize n (var, w))
    AstSelect1 _n2 (_var2, _b) _v _w -> AstBuildPair1 n (var, u)  -- TODO
    AstInt1{} -> AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, u)
    AstConst1{} ->
      error "build1Vectorize: AstConst1 can't have free int variables"
    AstConstant1 _r -> AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, u)
      -- this is very fast when interpreted in a smart way, but constant
      -- character needs to be exposed for nested cases;
      -- TODO: similarly propagate AstConstant upwards elsewhere
    AstScale1 (AstPrimalPart1 r) d ->
      AstScale1 (AstPrimalPart1 $ AstBuildPair1 n (var, r))  -- no need to vect
                (build1Vectorize n (var, d))

    AstVar1{} -> error "build1Vectorize: AstVar1 can't have free int variables"

    AstIndex1 v i -> build1VectorizeIndex1 n var v i
      -- @var@ is in @v@ or @i@; TODO: simplify i first
    AstSum1 v -> AstSum1 $ AstTranspose1 $ build1Vectorize n (var, v)
      -- that's because @build n (f . g) == map f (build n g)@
      -- and @map sum1 == sum1 . transpose1@
      -- TODO: though probably only for regular arrays
    AstFromList1 l ->
      AstTranspose1
      $ AstFromList1 (map (\v -> build1Vectorize n (var, v)) l)
    AstFromVector1 l ->
      AstTranspose1
      $ AstFromVector1 (V.map (\v -> build1Vectorize n (var, v)) l)
    AstKonst1{} -> AstBuildPair1 n (var, u)  -- TODO
    AstAppend1{} -> AstBuildPair1 n (var, u)  -- TODO
    AstSlice1{} -> AstBuildPair1 n (var, u)  -- TODO
    AstReverse1{} -> AstBuildPair1 n (var, u)  -- TODO
    AstBuildPair1{} -> AstBuildPair1 n (var, u)
      -- normal form? or a previous failure of vectorization that should have
      -- led to a shortcut instead of being encoutered now?
    AstTranspose1{} -> AstBuildPair1 n (var, u)  -- TODO
    AstReshape1{} -> AstBuildPair1 n (var, u)  -- TODO

    AstFromList01 l ->
      build1Vectorize n (var, AstFromList1 (map AstFrom01 l))
    AstFromVector01 l ->
      build1Vectorize n (var, AstFromVector1 (V.map AstFrom01 l))
    AstKonst01 k v -> build1Vectorize n (var, AstKonst1 k (AstFrom01 v))
    AstBuildPair01{} -> AstBuildPair1 n (var, u)  -- see AstBuildPair1 above
    AstMapPair01{} -> AstBuildPair1 n (var, u)  -- TODO
    AstZipWithPair01{} -> AstBuildPair1 n (var, u)  -- TODO
    AstFrom01 v -> build1VectorizeFrom01 n (var, v)

    AstOMap1{} -> AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, u)
    -- All other patterns are redundant due to GADT typing.

-- @var@ is in @v@ or @i@.
build1VectorizeIndex1
  :: AstInt r -> AstVarName Int -> Ast1 (1 + n) r -> AstInt r
  -> Ast1 (1 + n) r
build1VectorizeIndex1 n var v1 i =
  case v1 of
    AstOp1 codeOut args ->
      AstOp1 codeOut $ map (\w -> build1VectorizeIndex1 n var w i) args
    AstCond1 b v w ->
      if intVarInAstBool var b then
        AstSelect1 n (var, b)
                   (build1Vectorize n (var, AstIndex1 v i))
                   (build1Vectorize n (var, AstIndex1 w i))
      else
        AstCond1 b (build1Vectorize n (var, AstIndex1 v i))
                   (build1Vectorize n (var, AstIndex1 w i))
    AstConst1 _r -> build1VectorizeIndex1InI n var v1 i
    AstFromList1 l | AstIntConst k <- i -> build1Vectorize n (var, l !! k)
    -- TODO: AstAppend1 v1 v2 -> ... AstCond (i < AstLength v1) (...v1) (...v2)
    AstKonst1 _ r -> build1Vectorize n (var, r)
    AstSlice1 i2 _ u ->
      build1Vectorize n (var, AstIndex1 u (AstIntOp PlusIntOut [i2, i]))
        -- TODO: or should we rewrite in the opposite direction?
    -- TODO: AstReverse1 easy
    -- AstBuildPair1 _ (var2, u2) ->
    --   build1Vectorize n (var, substitute var2 i u2))
           -- TODO: use environments instead
    _ ->
      if intVarInAst1 var v1
      then -- can't do much, probably, since v different in each cell?
        AstBuildPair1 n (var, AstIndex1 v1 i)
      else
        build1VectorizeIndex1InI n var v1 i

-- The case where @var@ does not occur in @v@, which implies it's in @i@.
build1VectorizeIndex1InI
  :: AstInt r -> AstVarName Int -> Ast1 (1 + n) r -> AstInt r
  -> Ast1 (1 + n) r
build1VectorizeIndex1InI n var v i = case i of
  AstIntOp PlusIntOut [AstIntVar var2, i2] | var2 == var ->
    AstSlice1 i2 n v
  AstIntVar var2 -> assert (var2 == var) $
    AstSlice1 0 n v  -- simplified further elsewhere, if just identity
  {- TODO: these are impossible (they duplicate the first branch
     of build1Vectorize), unless we start descending recursively:
  AstIntConst _i2 ->
    AstKonst1 n (AstIndex1 v i)  -- v and i the same in each cell, so legit
  AstIntVar _var2 ->
    AstKonst1 n (AstIndex1 v i)  -- v and i the same in each cell, so legit
  -}
  _ -> AstBuildPair1 n (var, AstIndex1 v i)
    -- TODO:
    -- add a new 'gather' operation somehow and, if a more complex index
    -- expression, construct 'gather'

build1VectorizeFrom01
  :: AstInt r -> (AstVarName Int, Ast0 r) -> Ast1 1 r
build1VectorizeFrom01 n (var, u) =
  case u of
    AstOp0 codeOut args ->
      AstOp1 codeOut
      $ map (\w -> build1Vectorize n (var, AstFrom01 w)) args
        -- we can't call recursively build1VectorizeFrom01, because
        -- some of the arguments may don't have the int variable
    AstCond0 b v w ->
      if intVarInAstBool var b then
        AstSelect1 n (var, b)
                   (build1Vectorize n (var, AstFrom01 v))
                   (build1Vectorize n (var, AstFrom01 w))
      else
        AstCond1 b (build1Vectorize n (var, AstFrom01 v))
                   (build1Vectorize n (var, AstFrom01 w))
    AstInt0{} ->
      AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, AstFrom01 u)
    AstConst0{} ->
      error "build1VectorizeFrom01: AstConst0 can't have free int variables"
    AstConstant0 _r ->
      AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, AstFrom01 u)
      -- this is very fast when interpreted in a smart way, but constant
      -- character needs to be exposed for nested cases;
      -- TODO: similarly propagate AstConstant upwards elsewhere
    AstScale0 (AstPrimalPart0 r) d ->
      AstScale1 (AstPrimalPart1 $ AstBuildPair1 n (var, AstFrom01 r))
                (build1Vectorize n (var, AstFrom01 d))
    AstVar0{} ->
      error "build1VectorizeFrom01: AstVar0 can't have free int variables"
    AstIndex10 v [i] -> build1Vectorize n (var, AstIndex1 v i)
    AstIndex10{} ->
      error "build1VectorizeFrom01: wrong number of indexes for rank 1"
    AstSum10 v -> build1Vectorize n (var, AstSum1 v)
    AstDot10 v w -> build1Vectorize n (var, AstSum1 (AstOp1 TimesOut [v, w]))
      -- AstDot1 is dubious, because dot product results in a scalar,
      -- not in one rank less and also (some) fast implementations
      -- depend on it resulting in a scalar.
    AstFrom10 v -> build1Vectorize n (var, v)

    AstOMap0{} ->
      AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, AstFrom01 u)

-- TODO: speed up by keeping free vars in each node.
intVarInAst0 :: AstVarName Int -> Ast0 r -> Bool
intVarInAst0 var = \case
  AstOp0 _ l -> or $ map (intVarInAst0 var) l
  AstCond0 b x y ->
    intVarInAstBool var b || intVarInAst0 var x || intVarInAst0 var y
  AstInt0 n -> intVarInAstInt var n
  AstConst0{} -> False
  AstConstant0 (AstPrimalPart0 v) -> intVarInAst0 var v
  AstScale0 (AstPrimalPart0 v) u -> intVarInAst0 var v || intVarInAst0 var u

  AstVar0{} -> False  -- not an int variable

  AstIndex10 v ixs -> intVarInAst1 var v || or (map (intVarInAstInt var) ixs)
  AstSum10 v -> intVarInAst1 var v
  AstDot10 v u -> intVarInAst1 var v || intVarInAst1 var u
  AstFrom10 v -> intVarInAst1 var v
  AstOMap0 (_, v) u -> intVarInAst0 var v || intVarInAst0 var u
    -- the variable in binder position, so ignored (and should be distinct)

intVarInAst1 :: AstVarName Int -> Ast1 n r -> Bool
intVarInAst1 var = \case
  AstOp1 _ l -> or $ map (intVarInAst1 var) l
  AstCond1 b x y ->
    intVarInAstBool var b || intVarInAst1 var x || intVarInAst1 var y
  AstSelect1 n (_, b) x y ->
    intVarInAstInt var n || intVarInAstBool var b
    || intVarInAst1 var x || intVarInAst1 var y
  AstInt1 n -> intVarInAstInt var n
  AstConst1{} -> False
  AstConstant1 (AstPrimalPart1 v) -> intVarInAst1 var v
  AstScale1 (AstPrimalPart1 v) u -> intVarInAst1 var v || intVarInAst1 var u

  AstVar1{} -> False  -- not an int variable

  AstIndex1 v ix -> intVarInAst1 var v || intVarInAstInt var ix
  AstSum1 v -> intVarInAst1 var v
  AstFromList1 l -> or $ map (intVarInAst1 var) l  -- down from rank 1 to 0
  AstFromVector1 vl -> or $ map (intVarInAst1 var) $ V.toList vl
  AstKonst1 n v -> intVarInAstInt var n || intVarInAst1 var v
  AstAppend1 v u -> intVarInAst1 var v || intVarInAst1 var u
  AstSlice1 i k v -> intVarInAstInt var i || intVarInAstInt var k
                     || intVarInAst1 var v
  AstReverse1 v -> intVarInAst1 var v
  AstBuildPair1 n (_, v) -> intVarInAstInt var n || intVarInAst1 var v
  AstTranspose1 v -> intVarInAst1 var v
  AstReshape1 _ v -> intVarInAst1 var v

  AstFromList01 l -> or $ map (intVarInAst0 var) l
  AstFromVector01 l -> V.or $ V.map (intVarInAst0 var) l
  AstKonst01 n v -> intVarInAstInt var n || intVarInAst0 var v
  AstBuildPair01 n (_, v) -> intVarInAstInt var n || intVarInAst0 var v
  AstMapPair01 (_, v) u -> intVarInAst0 var v || intVarInAst1 var u
  AstZipWithPair01 (_, _, v) u w ->
    intVarInAst0 var v || intVarInAst1 var u || intVarInAst1 var w
  AstFrom01 u -> intVarInAst0 var u

  AstOMap1 (_, v) u -> intVarInAst0 var v || intVarInAst1 var u

intVarInAstInt :: AstVarName Int -> AstInt r -> Bool
intVarInAstInt var = \case
  AstIntOp _ l -> or $ map (intVarInAstInt var) l
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstIntConst{} -> False
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstLength v -> intVarInAst1 var v
  AstMinIndex v -> intVarInAst1 var v
  AstMaxIndex v -> intVarInAst1 var v

intVarInAstBool :: AstVarName Int -> AstBool r -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> or $ map (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> or $ map (intVarInAst0 var) l
  AstRelInt _ l  -> or $ map (intVarInAstInt var) l

-- TODO: Shall this be represented and processed as just build?
-- But doing this naively copies @w@ a lot, so we'd need to wait
-- until AST handles sharing properly. Or make @w@ a variable.
map1Vectorize
  :: (AstVarName r, Ast0 r) -> Ast1 1 r
  -> Ast1 1 r
map1Vectorize (var, u) w = case u of
  AstOp0 codeOut args ->
    AstOp1 codeOut $ map (\x -> map1Vectorize (var, x) w) args
  AstInt0 _i -> AstMapPair01 (var, u) w  -- TODO
  AstCond0 _b _x1 _x2 -> AstMapPair01 (var, u) w  -- TODO
  AstConst0 r -> AstKonst01 (AstLength w) (AstConst0 r)
  AstConstant0 _r -> AstMapPair01 (var, u) w  -- TODO
  AstScale0 (AstPrimalPart0 r) d ->
    AstScale1 (AstPrimalPart1 $ AstMapPair01 (var, r) w)
              (map1Vectorize (var, d) w)
  AstVar0 var2 | var2 == var -> w  -- identity mapping
  AstVar0 var2 -> AstKonst01 (AstLength w) (AstVar0 var2)
  AstIndex10 _v _i -> AstMapPair01 (var, u) w  -- TODO
    -- both _v and _i can depend on var, e.g., because of conditionals
  AstSum10 _v -> AstMapPair01 (var, u) w  -- TODO
  AstDot10 _u _v -> AstMapPair01 (var, u) w  -- TODO
  _ -> AstMapPair01 (var, u) w  -- TODO
  -- TODO: -- All other patterns are redundant due to GADT typing.

leqAst :: Ast0 r -> Ast0 r -> AstBool r
leqAst d e = AstRel LeqOut [d, e]

gtAst :: Ast0 r -> Ast0 r -> AstBool r
gtAst d e = AstRel GtOut [d, e]

gtIntAst :: AstInt r -> AstInt r -> AstBool r
gtIntAst i j = AstRelInt GtOut [i, j]

interpretLambdaD0
  :: ADModeAndNum d r
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> (AstVarName r, Ast0 r)
  -> ADVal d r -> ADVal d r
interpretLambdaD0 env (AstVarName var, ast) =
  \d -> interpretAst0 (IM.insert var (AstVarR0 d) env) ast

interpretLambdaI0
  :: ADModeAndNum d r
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> (AstVarName Int, Ast0 r)
  -> Int -> ADVal d r
interpretLambdaI0 env (AstVarName var, ast) =
  \i -> interpretAst0 (IM.insert var (AstVarI i) env) ast

interpretLambdaI1
  :: (ADModeAndNum d r, KnownNat n)
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> (AstVarName Int, Ast1 n r)
  -> Int -> ADVal d (OR.Array n r)
interpretLambdaI1 env (AstVarName var, ast) =
  \i -> interpretAst1 (IM.insert var (AstVarI i) env) ast

interpretAst0Primal
  :: ADModeAndNum d r
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> Ast0 r -> r
interpretAst0Primal env r = let D u _ = interpretAst0 env r in u

interpretAst0
  :: ADModeAndNum d r
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> Ast0 r -> ADVal d r
interpretAst0 env = \case
  AstOp0 codeOut args ->
    interpretAstOp (interpretAst0 env) codeOut args
  AstCond0 b a1 a2 -> if interpretAstBool env b
                      then interpretAst0 env a1
                      else interpretAst0 env a2
  AstInt0 i -> fromInteger $ fromIntegral $ interpretAstInt env i
  AstConst0 a -> constant a
  AstConstant0 (AstPrimalPart0 a) -> constant $ interpretAst0Primal env a
  AstScale0 (AstPrimalPart0 r) d ->
    scale (interpretAst0Primal env r) (interpretAst0 env d)

  AstVar0 (AstVarName var) -> case IM.lookup var env of
    Just (AstVarR0 d) -> d
    Just AstVarR1{} ->
      error $ "interpretAst: type mismatch for var " ++ show var
    Just AstVarI{} -> error $ "interpretAst: type mismatch for var " ++ show var
    Nothing -> error $ "interpretAst: unknown variable var " ++ show var

  AstIndex10 v is ->
    let index10' (D u u') ixs = dD (u `atIndexInTensorR` ixs)
                                   (dIndex10 u' ixs (OR.shapeL u))
    in index10' (interpretAst1 env v) (map (interpretAstInt env) is)
  AstSum10 v ->
    let sum10 (D u u') = dD (OR.sumA u) (dSum10 (OR.shapeL u) u')
    in sum10 (interpretAst1 env v)
  AstDot10 x y ->
    let dot0 (D u u') (D v v') = dD (OR.toVector u LA.<.> OR.toVector v)
                                    (dAdd (dDot10 v u') (dDot10 u v'))
    in dot0 (interpretAst1 env x) (interpretAst1 env y)
  AstFrom10 u -> from10 $ interpretAst1 env u

  AstOMap0 (var, r) e ->  -- this only works on the primal part hence @constant@
    constant
    $ omap (\x -> let D u _ = interpretLambdaD0 env (var, r) (constant x)
                  in u)
           (interpretAst0Primal env e)

interpretAst1Primal
  :: (ADModeAndNum d r, KnownNat n)
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> Ast1 n r -> OR.Array n r
interpretAst1Primal env v = let D u _ = interpretAst1 env v in u

interpretAst1
  :: (ADModeAndNum d r, KnownNat n)
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> Ast1 n r -> ADVal d (OR.Array n r)
interpretAst1 env = \case
  AstOp1 codeOut args ->
    interpretAstOp (interpretAst1 env) codeOut args
  AstCond1 b a1 a2 -> if interpretAstBool env b
                      then interpretAst1 env a1
                      else interpretAst1 env a2
  AstSelect1 n (AstVarName var, b) a1 a2 ->
    let k = interpretAstInt env n
        f [i] = if interpretAstBool (IM.insert var (AstVarI i) env) b
                then 1
                else 0
        f _ = error "AstSelect: unexpected argument"
        bitmap = constant $ OR.generate [k] f
        v1 = interpretAst1 env a1
        v2 = interpretAst1 env a2
    in bitmap * v1 + v2 - bitmap * v2
  AstInt1 i -> fromInteger $ fromIntegral $ interpretAstInt env i
  AstConst1 a -> constant a
  AstConstant1 (AstPrimalPart1 a) -> constant $ interpretAst1Primal env a
  AstScale1 (AstPrimalPart1 r) d ->
    scale (interpretAst1Primal env r) (interpretAst1 env d)

  AstVar1 (AstVarName var) -> case IM.lookup var env of
    Just AstVarR0{} ->
      error $ "interpretAst: type mismatch for var " ++ show var
    Just (AstVarR1 d) -> d
    Just AstVarI{} -> error $ "interpretAst: type mismatch for var " ++ show var
    Nothing -> error $ "interpretAst: unknown variable var " ++ show var

  AstIndex1 v i ->
    let index1' (D u u') ix = dD (u `OR.index` ix)
                                 (dIndex1 u' ix (head $ OR.shapeL u))
    in index1' (interpretAst1 env v) (interpretAstInt env i)
  AstSum1 v ->
    let sum1 (D u u') = dD (ORB.sumA $ OR.unravel u)
                           (dSum1 (head $ OR.shapeL u) u')
    in sum1 (interpretAst1 env v)
  AstFromList1 l -> fromList1' (map (interpretAst1 env) l)
  AstFromVector1 l ->
    let fromVector1' lu =
          dD (OR.ravel . ORB.fromVector [V.length lu] . V.convert
              $ V.map (\(D u _) -> u) lu)
             (dFromVector1 $ V.map (\(D _ u') -> u') lu)
    in fromVector1' (V.map (interpretAst1 env) l)
  AstKonst1 n v ->
    let konst1' n' (D u u') = dD (OR.ravel (ORB.constant [n'] u))
                                 (dKonst1 n' u')
    in konst1' (interpretAstInt env n) (interpretAst1 env v)
  AstAppend1 x y ->
    let append1' (D u u') (D v v') =
          dD (OR.append u v) (dAppend1 u' (head $ OR.shapeL u) v')
    in append1' (interpretAst1 env x) (interpretAst1 env y)
  AstSlice1 i k v ->
    let slice1' i' k' (D u u') = dD (OR.slice [(i', k')] u)
                                    (dSlice1 i' k' u' (head $ OR.shapeL u))
    in slice1' (interpretAstInt env i) (interpretAstInt env k)
               (interpretAst1 env v)
  AstReverse1 v ->
    let reverse1' (D u u') = dD (OR.rev [0] u) (dReverse1 u')
    in reverse1' (interpretAst1 env v)
  AstBuildPair1 i (var, v) ->
    let build1' n f = fromList1' $ map f [0 .. n - 1]
    in build1' (interpretAstInt env i) (interpretLambdaI1 env (var, v))
      -- fallback to POPL (memory blowup, but avoids functions on tape);
      -- an alternative is to use dBuild1 and store function on tape
  AstTranspose1 v ->
    let transpose1 (D u u') = dD (OR.transpose [1, 0] u) (dTranspose1 u')
    in transpose1 (interpretAst1 env v)
  AstReshape1{} -> undefined  -- TODO

  AstFromList01 l -> lfromList1 $ map (interpretAst0 env) l
  AstFromVector01 v -> lfromVector1 $ V.map (interpretAst0 env) v
  AstKonst01 n r -> lkonst1 (interpretAstInt env n) (interpretAst0 env r)
  AstBuildPair01 i (var, AstConstant0 r) ->
    constant
    $ lbuild1  -- from OR.Array instance
        (interpretAstInt env i)
        (\j -> let D v _ = interpretLambdaI0 env (var, AstConstant0 r) j
               in v)
  AstBuildPair01 i (var, r) ->
    build1Elementwise (interpretAstInt env i) (interpretLambdaI0 env (var, r))
      -- fallback to POPL (memory blowup, but avoids functions on tape)
  AstMapPair01 (var, r) e ->
    map1Elementwise (interpretLambdaD0 env (var, r)) (interpretAst1 env e)
      -- fallback to POPL (memory blowup, but avoids functions on tape)
  AstZipWithPair01 (_var1, _var2, _r) _e1 _e2 -> undefined
    -- a 2-var interpretLambda would be needed; or express all with build
  AstFrom01 u -> from01 $ interpretAst0 env u

  AstOMap1 (var, r) e ->  -- this only works on the primal part hence @constant@
    constant
    $ omap (\x -> let D u _ = interpretLambdaD0 env (var, r) (constant x)
                  in u)
           (interpretAst1Primal env e)

fromList1' :: (ADModeAndNum d r, KnownNat n)
           => [ADVal d (OR.Array n r)]
           -> ADVal d (OR.Array (1 + n) r)
fromList1' lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (OR.ravel . ORB.fromList [length lu]
      $ map (\(D u _) -> u) lu)
     (dFromList1 $ map (\(D _ u') -> u') lu)

interpretAstInt :: ADModeAndNum d r
                => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
                -> AstInt r -> Int
interpretAstInt env = \case
  AstIntOp codeIntOut args ->
    interpretAstIntOp (interpretAstInt env) codeIntOut args
  AstIntCond b a1 a2 -> if interpretAstBool env b
                        then interpretAstInt env a1
                        else interpretAstInt env a2
  AstIntConst a -> a
  AstIntVar (AstVarName var) -> case IM.lookup var env of
    Just AstVarR0{} ->
      error $ "interpretAstP: type mismatch for var " ++ show var
    Just AstVarR1{} ->
      error $ "interpretAstP: type mismatch for var " ++ show var
    Just (AstVarI i) -> i
    Nothing -> error $ "interpretAstP: unknown variable var " ++ show var
  AstLength v -> llength $ interpretAst1 env v
  AstMinIndex v -> lminIndex $ interpretAst1 env v
  AstMaxIndex v -> lmaxIndex $ interpretAst1 env v

interpretAstBool :: ADModeAndNum d r
                 => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
                 -> AstBool r -> Bool
interpretAstBool env = \case
  AstBoolOp codeBoolOut args ->
    interpretAstBoolOp (interpretAstBool env) codeBoolOut args
  AstBoolConst a -> a
  AstRel relOut args ->
    let f x = interpretAst0Primal env x
    in interpretAstRel f relOut args
  AstRelInt relOut args ->
    let f = interpretAstInt env
    in interpretAstRel f relOut args

interpretAstOp :: RealFloat b
               => (c -> b) -> CodeOut -> [c] -> b
{-# INLINE interpretAstOp #-}
interpretAstOp f PlusOut [u, v] = f u + f v
interpretAstOp f MinusOut [u, v] = f u - f v
interpretAstOp f TimesOut [u, v] = f u * f v
interpretAstOp f NegateOut [u] = negate $ f u
interpretAstOp f AbsOut [u] = abs $ f u
interpretAstOp f SignumOut [u] = signum $ f u
interpretAstOp f DivideOut [u, v] = f u / f v
interpretAstOp f RecipOut [u] = recip $ f u
interpretAstOp f ExpOut [u] = exp $ f u
interpretAstOp f LogOut [u] = log $ f u
interpretAstOp f SqrtOut [u] = sqrt $ f u
interpretAstOp f PowerOut [u, v] = f u ** f v
interpretAstOp f LogBaseOut [u, v] = logBase (f u) (f v)
interpretAstOp f SinOut [u] = sin $ f u
interpretAstOp f CosOut [u] = cos $ f u
interpretAstOp f TanOut [u] = tan $ f u
interpretAstOp f AsinOut [u] = asin $ f u
interpretAstOp f AcosOut [u] = acos $ f u
interpretAstOp f AtanOut [u] = atan $ f u
interpretAstOp f SinhOut [u] = sinh $ f u
interpretAstOp f CoshOut [u] = cosh $ f u
interpretAstOp f TanhOut [u] = tanh $ f u
interpretAstOp f AsinhOut [u] = asinh $ f u
interpretAstOp f AcoshOut [u] = acosh $ f u
interpretAstOp f AtanhOut [u] = atanh $ f u
interpretAstOp f Atan2Out [u, v] = atan2 (f u) (f v)
interpretAstOp f MaxOut [u, v] = max (f u) (f v)
interpretAstOp f MinOut [u, v] = min (f u) (f v)
interpretAstOp _ codeOut args =
  error $ "interpretAstOp: wrong number of arguments"
          ++ show (codeOut, length args)

interpretAstIntOp :: (AstInt r -> Int) -> CodeIntOut -> [AstInt r] -> Int
{-# INLINE interpretAstIntOp #-}
interpretAstIntOp f PlusIntOut [u, v] = f u + f v
interpretAstIntOp f MinusIntOut [u, v] = f u - f v
interpretAstIntOp f TimesIntOut [u, v] = f u * f v
interpretAstIntOp f NegateIntOut [u] = negate $ f u
interpretAstIntOp f AbsIntOut [u] = abs $ f u
interpretAstIntOp f SignumIntOut [u] = signum $ f u
interpretAstIntOp f MaxIntOut [u, v] = max (f u) (f v)
interpretAstIntOp f MinIntOut [u, v] = min (f u) (f v)
interpretAstIntOp _ codeIntOut args =
  error $ "interpretAstIntOp: wrong number of arguments"
          ++ show (codeIntOut, length args)

interpretAstBoolOp :: (AstBool r -> Bool) -> CodeBoolOut -> [AstBool r]
                   -> Bool
{-# INLINE interpretAstBoolOp #-}
interpretAstBoolOp f NotOut [u] = not $ f u
interpretAstBoolOp f AndOut [u, v] = f u && f v
interpretAstBoolOp f OrOut [u, v] = f u || f v
interpretAstBoolOp f IffOut [u, v] = f u == f v
interpretAstBoolOp _ codeBoolOut args =
  error $ "interpretAstBoolOp: wrong number of arguments"
          ++ show (codeBoolOut, length args)

interpretAstRel :: Ord b => (a -> b) -> RelOut -> [a] -> Bool
{-# INLINE interpretAstRel #-}
interpretAstRel f EqOut [u, v] = f u == f v
interpretAstRel f NeqOut [u, v] = f u /= f v
interpretAstRel f LeqOut [u, v] = f u <= f v
interpretAstRel f GeqOut [u, v] = f u >= f v
interpretAstRel f LsOut [u, v] = f u < f v
interpretAstRel f GtOut [u, v] = f u > f v
interpretAstRel _ codeRelOut args =
  error $ "interpretAstRel: wrong number of arguments"
          ++ show (codeRelOut, length args)
