{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, GADTs, MultiParamTypeClasses,
             QuantifiedConstraints, RankNTypes, TypeFamilies,
             UndecidableInstances #-}
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
  , Domain0, Domain1, Domains(..), nullDomains  -- an important re-export
  , -- temporarily re-exported, until these are wrapped in sugar
    Ast(..), AstPrimalPart1(..)
  , AstVarName(..), AstVar(..)
  , AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  ) where

import Prelude

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
import HordeAd.Internal.OrthotopeOrphanInstances (liftVR, liftVR2)

-- * Auxiliary definitions

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


-- * Numeric instances for ADVal

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

-- * VectorLike class definition and instances for tensors, ADVal and Ast

-- This setup hacks around the need to define separate instances for
-- Double, Float, etc., instead of a single instance for @Numeric r@, as below.
class VectorOf r ~ v => VectorLike1 v r where
  llength :: VectorOf r -> IntOf r
  lminIndex :: VectorOf r -> IntOf r
  lmaxIndex :: VectorOf r -> IntOf r

  lindex0 :: VectorOf r -> IntOf r -> r
  lsum0 :: VectorOf r -> r
  ldot0 :: VectorOf r -> VectorOf r -> r
  lminimum0 :: VectorOf r -> r
  lmaximum0 :: VectorOf r -> r

  lfromList1 :: [r] -> VectorOf r
  lfromVector1 :: Data.Vector.Vector r -> VectorOf r
  lkonst1 :: IntOf r -> r -> VectorOf r
  lappend1 :: VectorOf r -> VectorOf r -> VectorOf r
  lslice1 :: IntOf r -> IntOf r -> VectorOf r -> VectorOf r
  lreverse1 :: VectorOf r -> VectorOf r
  lbuild1 :: IntOf r -> (IntOf r -> r) -> VectorOf r
  lmap1 :: (r -> r) -> VectorOf r -> VectorOf r
  lzipWith :: (r -> r -> r) -> VectorOf r -> VectorOf r -> VectorOf r

type VectorLike r = VectorLike1 (VectorOf r) r

type ADReady r =
  ( RealFloat r, RealFloat (VectorOf r)
  , HasPrimal r, HasPrimal (VectorOf r)
  , VectorLike r, Integral (IntOf r) )

-- This instance is a faster way to get an objective function value.
-- However, it doesn't do vectorization, so won't work on GPU, ArrayFire, etc.
-- For vectorization, go through Ast and valueOnDomains.
instance (Numeric r, IntOf r ~ Int, VectorOf r ~ OR.Array 1 r)
         => VectorLike1 (OR.Array 1 r) r where
  llength = OR.size
  lminIndex = LA.minIndex . OR.toVector
  lmaxIndex = LA.maxIndex . OR.toVector

  lindex0 v ix = (V.! ix) $ OR.toVector v
  lsum0 = LA.sumElements . OR.toVector
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
  lmap1 = liftVR . V.map
  lzipWith = liftVR2 . V.zipWith

-- Not that this instance doesn't do vectorization. To enable it,
-- use the Ast instance, which vectorizes and finally interpret in ADVal.
-- In principle, this instance is only useful for comparative tests,
-- though for code without build/map/etc., it should be equivalent
-- to going via Ast.
instance ADModeAndNum d r
         => VectorLike1 (ADVal d (OR.Array 1 r)) (ADVal d r) where
  llength (D u _) = llength u
  lminIndex (D u _) = lminIndex u
  lmaxIndex (D u _) = lmaxIndex u

  lindex0 d ix = index0' d [ix]
  lsum0 = sum0'
  ldot0 = dot0'
  lminimum0 (D u u') =
    dD (lminimum0 u) (dIndex0 u' [lminIndex u] [llength u])
  lmaximum0 (D u u') =
    dD (lmaximum0 u) (dIndex0 u' [lmaxIndex u] [llength u])

  lfromList1 l = fromList01' [length l] l
  lfromVector1 l = fromVector01' [V.length l] l
  lkonst1 n = konst01' [n]
  lappend1 = append1'
  lslice1 = slice1'
  lreverse1 = reverse1'
  lbuild1 = build1Closure  -- to test against build1Elementwise from Ast
  lmap1 f v = build1Closure (llength v) (\i -> f (v `lindex0` i))
  lzipWith f v u =
    build1Closure (llength v) (\i -> f (v `lindex0` i) (u `lindex0` i))

instance VectorLike1 (Ast 1 r) (Ast 0 r) where
  llength = AstLength
  lminIndex = AstMinIndex
  lmaxIndex = AstMaxIndex

  lindex0 v ix = AstIndex1 v ix
  lsum0 = AstSum1
  ldot0 u v = AstDot0 u v
  lminimum0 v = AstIndex1 v (AstMinIndex v)
  lmaximum0 v = AstIndex1 v (AstMaxIndex v)

  lfromList1 l = AstFromList1 l
  lfromVector1 l = AstFromVector1 l
  lkonst1 n r = AstKonst1 n r
  lappend1 = AstAppend1
  lslice1 = AstSlice1
  lreverse1 = AstReverse1
  lbuild1 = astBuild1
  lmap1 f v = astBuild1 (llength v) (\i -> f (v `lindex0` i))
  lzipWith f v u =
    astBuild1 (llength v) (\i -> f (v `lindex0` i) (u `lindex0` i))

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

astBuild1 :: AstInt r -> (AstInt r -> Ast 0 r) -> Ast 1 r
{-# NOINLINE astBuild1 #-}
astBuild1 n f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! build1Vectorize1 n ( freshAstVar
                               , (f (AstIntVar freshAstVar)) )
    -- TODO: this vectorizers depth-first, which is needed. But do we
    -- also need a translation to non-vectorized terms for anything
    -- (other than for comparative tests)?


-- * HasPrimal instances for all relevant types

-- We could accept any @RealFloat@ instead of @PrimalOf a@, but then
-- we'd need to coerce, e.g., via realToFrac, which is risky and lossy.
-- Also, the stricter typing is likely to catch real errors most of the time,
-- not just sloppy omission of explitic coercions.
class HasPrimal a where
  type PrimalOf a
  type DualOf a
  constant :: PrimalOf a -> a
  scale :: Num (PrimalOf a) => PrimalOf a -> a -> a
  primalPart :: a -> PrimalOf a
  dualPart :: a -> DualOf a
  ddD :: PrimalOf a -> DualOf a -> a
  -- TODO: we'd probably also need dZero, dIndex0 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?
  --
  -- Unrelated, but no better home ATM:
  fromIntOf :: IntOf a -> a

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

instance HasPrimal (Ast n r) where
  type PrimalOf (Ast n r) = AstPrimalPart1 n r
  type DualOf (Ast n r) = ()  -- TODO: data AstDualPart: dScale, dAdd, dkonst1
  constant = AstConstant1
  scale = AstScale1
  primalPart = AstPrimalPart1
  dualPart = error "TODO"
  ddD = error "TODO"
  fromIntOf = AstInt1


-- * Legacy operations needed to re-use vector differentiation tests

-- General operations, for any tensor rank

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

-- TODO: bring back rank-poly relu by adding a class with Ast 0 and Ast 1
-- or even better generalize the function after omap above so that
-- it has a sensible Ast instance and then kill reluAst0 and reluAst1;
-- we'd need Conditional class that works with our AstBool type
-- and some sugar to be able to use >, &&, etc.
reluAst0
  :: ( Num (Vector r), MonoFunctor (PrimalOf (Ast 0 r))
     , Numeric r )
  => Ast 0 r -> Ast 0 r
reluAst0 v =
  let oneIfGtZero = omap (\(AstPrimalPart1 x) ->
                            AstPrimalPart1 $ AstCond1 (AstRel GtOp [x, 0]) 1 0)
                         (primalPart v)
  in scale oneIfGtZero v

reluAst1
  :: ( KnownNat n, Num (Vector r), MonoFunctor (PrimalOf (Ast n r))
     , Numeric r )
  => Ast n r -> Ast n r
reluAst1 v =
  let oneIfGtZero = omap (\(AstPrimalPart1 x) ->
                            AstPrimalPart1 $ AstCond1 (AstRel GtOp [x, 0]) 1 0)
                         (primalPart v)
  in scale oneIfGtZero v


-- Operations resulting in a scalar

sumElements10 :: ADModeAndNum d r
              => ADVal d (Vec r) -> ADVal d r
sumElements10 = lsum0

index10 :: ADModeAndNum d r => ADVal d (Vec r) -> Int -> ADVal d r
index10 = lindex0

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
      g !acc ix p = f (dD p (dIndex0 v' [ix] [k])) acc
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
(<.>!!) (D u u') v = dD (ldot0 u v) (dDot0 v u')

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
      sumExpU = lsum0 expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = LA.scaleRecip sumExpU expU
      softMaxU = lkonst1 (llength expU) recipSum * expU
  in dD (negate $ log softMaxU `ldot0` target)  -- TODO: avoid: log . exp
        (dDot0 (softMaxU - target) u')


-- Operations resulting in a vector (really, a rank 1 OR.Array)

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


-- Build and map variants

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
  build1Elementwise (llength d) $ \i -> f (lindex0 d i)
    -- equivalent to
    -- @fromVector1 . map1POPL f . rank1toVector
    --   where rank1toVector d@(D v _v') = V.generate (llength d) (lindex0 d)@


-- * Vectorization of the build operation

build1Vectorize1
  :: AstInt r -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1Vectorize1 n (var, u) =
  if intVarInAst var u
  then build1Vectorize1Var n (var, u)
  else AstKonst1 n u

-- | The variable is known to occur in the term.
build1Vectorize1Var
  :: AstInt r -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1Vectorize1Var n (var, u) =
  case u of
    AstOp1 opCode args ->
      AstOp1 opCode $ map (\w -> build1Vectorize1 n (var, w)) args
    AstCond1 b v w ->
      if intVarInAstBool var b then
        -- This handles conditionals that depend on var,
        -- so that we produce conditional delta expressions
        -- of size proportional to the exponent of conditional
        -- nesting, instead of proportional to the number of elements
        -- of the tensor.
        AstSelect1 n (var, b)
                   (build1Vectorize1 n (var, v))
                   (build1Vectorize1 n (var, w))
      else
        AstCond1 b (build1Vectorize1 n (var, v))
                   (build1Vectorize1 n (var, w))
    AstSelect1 n2 (var2, b) v w ->
      AstTranspose1 $ AstSelect1 n2 (var2, b)
        (AstTranspose1 $ build1Vectorize1 n (var, v))
        (AstTranspose1 $ build1Vectorize1 n (var, w))
    AstInt1{} -> AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, u)
    AstConst1{} ->
      error "build1Vectorize1Var: AstConst1 can't have free int variables"
    AstConstant1{} -> AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, u)
      -- this is very fast when interpreted in a smart way, but constant
      -- character needs to be exposed for nested cases;
      -- TODO: similarly propagate AstConstant upwards elsewhere
    AstScale1 (AstPrimalPart1 r) d ->
      AstScale1 (AstPrimalPart1 $ AstBuildPair1 n (var, r))  -- no need to vect
                (build1Vectorize1 n (var, d))

    AstVar0{} ->
      error "build1Vectorize1Var: AstVar0 can't have free int variables"
    AstVar1{} ->
      error "build1Vectorize1Var: AstVar1 can't have free int variables"

    AstIndex1 v i -> build1VectorizeIndex1Var n var v i
      -- @var@ is in @v@ or @i@; TODO: simplify i first or even fully
      -- evaluate (may involve huge data processing) if contains no vars
      -- and then some things simplify a lot
    AstSum1 v -> AstTranspose1 $ AstSum1 $ AstTranspose1
                 $ build1Vectorize1Var n (var, v)
      -- that's because @build n (f . g) == map f (build n g)@
      -- and @map f == transpose1 . f . transpose1@
      -- TODO: though only for some f; check and fail early
    AstFromList1 l ->
      AstTranspose1
      $ AstFromList1 (map (\v -> build1Vectorize1 n (var, v)) l)
    AstFromVector1 l ->
      AstTranspose1
      $ AstFromVector1 (V.map (\v -> build1Vectorize1 n (var, v)) l)
    AstKonst1 k _v | intVarInAstInt var k -> AstBuildPair1 n (var, u)  -- TODO
    AstKonst1 k v -> AstTranspose1 $ AstKonst1 k $ AstTranspose1
                     $ build1Vectorize1 n (var, v)
    AstAppend1 v w -> AstTranspose1 $ AstAppend1
                        (AstTranspose1 $ build1Vectorize1 n (var, v))
                        (AstTranspose1 $ build1Vectorize1 n (var, w))
    AstSlice1 i k _v | intVarInAstInt var i || intVarInAstInt var k ->
      AstBuildPair1 n (var, u)  -- TODO
    AstSlice1 i k v -> AstTranspose1 $ AstSlice1 i k $ AstTranspose1
                       $ build1Vectorize1 n (var, v)
    AstReverse1 v -> AstTranspose1 $ AstReverse1 $ AstTranspose1
                     $ build1Vectorize1Var n (var, v)
    AstBuildPair1{} -> AstBuildPair1 n (var, u)
      -- TODO: a previous failure of vectorization that should have
      -- led to an abort instead of showing up late
    AstTranspose1 v ->
      build1Vectorize1Var n (var, AstTransposeGeneral1 [1, 0] v)
    AstTransposeGeneral1 perm v -> AstTransposeGeneral1 (0 : map succ perm)
                                   $ build1Vectorize1Var n (var, v)
    AstFlatten v -> build1Vectorize1 n (var, AstReshape1 [AstLength u] v)
    AstReshape1 ns _v | or $ map (intVarInAstInt var) ns ->
      AstBuildPair1 n (var, u)  -- TODO
    AstReshape1 ns v -> AstReshape1 (n : ns) $ build1Vectorize1 n (var, v)

    -- Rewriting syntactic sugar in the simplest way (but much more efficient
    -- non-sugar implementations/vectorizations exist):
    AstIndex0 v [i] -> build1Vectorize1Var n (var, AstIndex1 v i)
      -- TODO: express with AstFlatten (costly, but simple), for which
      -- we probably need AstShape AstInt constructor
    AstIndex0{} ->
      error "build1Vectorize1Var: wrong number of indexes for rank 1"
    AstSum0 v -> build1Vectorize1Var n (var, AstSum1 $ AstFlatten v)
    AstDot0 v w ->
      build1Vectorize1Var n (var, AstSum1 (AstOp1 TimesOp [ AstFlatten v
                                                          , AstFlatten w ]))
      -- AstDot1 is dubious, because dot product results in a scalar,
      -- not in one rank less and also (some) fast implementations
      -- depend on it resulting in a scalar.
      -- AstOp1 does not require Numeric constraint, so better than @*@.
    AstFromList01 sh l ->
      build1Vectorize1Var n (var, AstReshape1 sh $ AstFromList1 l)
    AstFromVector01 sh l ->
      build1Vectorize1Var n (var, AstReshape1 sh $ AstFromVector1 l)
    AstKonst01 sh v ->
      let k = product sh
      in build1Vectorize1Var n (var, AstReshape1 sh $ AstKonst1 k v)
    AstBuildPair01{} -> AstBuildPair1 n (var, u)  -- see AstBuildPair1 above

    AstOMap0{} -> AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, u)
    AstOMap1{} -> AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, u)
    -- All other patterns are redundant due to GADT typing.

-- The application @build1VectorizeIndex n var v i@
-- vectorizes the term @AstBuildPair1 n (var, AstIndex1 v i)@.
build1VectorizeIndex1
  :: AstInt r -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Ast (1 + n) r
build1VectorizeIndex1 n var v i =
  if intVarInAst var v || intVarInAstInt var i
  then build1VectorizeIndex1Var n var v i
  else AstKonst1 n (AstIndex1 v i)

-- | The variable is known to occur in the term or in the index
-- (it doesn't matter much which, because other variables may occur, too).
-- We try to push the indexing down the term tree and partially
-- evalute/simplify the term, if possible in constant time. Eventually,
-- we are down to indexing of a too simple but non-constant expression,
-- and then the only hope is in analyzing the index expression in turn.
build1VectorizeIndex1Var
  :: AstInt r -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Ast (1 + n) r
build1VectorizeIndex1Var n var v1 i =
  case v1 of
    AstOp1 opCode args ->
      AstOp1 opCode $ map (\w -> build1VectorizeIndex1 n var w i) args
    AstCond1 b v w ->
      if intVarInAstBool var b then
        AstSelect1 n (var, b)
                   (build1VectorizeIndex1 n var v i)
                   (build1VectorizeIndex1 n var w i)
      else
        AstCond1 b (build1VectorizeIndex1 n var v i)
                   (build1VectorizeIndex1 n var w i)
    AstSelect1{} -> build1VectorizeIndex1Try n var v1 i
      -- can't push the indexing down, so try analyzing the index instead;
      -- we may want to add yet another constructor that says "pick the element
      -- on this path out of this select" and hope it reduces fine elsewhere
      -- or we may partially evaluate @i@ and try to reduce on the spot
    AstInt1{} ->
      AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, AstIndex1 v1 i)
    AstConst1{} ->  -- var must be in i
      AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, AstIndex1 v1 i)
    AstConstant1{} ->
      AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, AstIndex1 v1 i)
    AstScale1 (AstPrimalPart1 r) d ->
      AstScale1 (AstPrimalPart1 $ AstBuildPair1 n (var, AstIndex1 r i))
                (build1VectorizeIndex1 n var d i)

    AstVar0{} -> error "build1VectorizeIndex1Var: wrong rank"
    AstVar1{} ->  -- var must be in i, so it's hard to simplify
      build1VectorizeIndex1Try n var v1 i

    AstIndex1 _v _i -> undefined  -- TODO: a list of indexes needed?
    AstSum1 v ->
      build1Vectorize1Var n
        (var, AstSum1 (AstTranspose1 $ AstIndex1 (AstTranspose1 v) i))
          -- that's because @index (sum v) i == sum (map (index i) v)@
    -- Can't push indexing down, so try analyzing the index instead:
    AstFromList1{} -> build1VectorizeIndex1Try n var v1 i
    AstFromVector1{} -> build1VectorizeIndex1Try n var v1 i
    -- Partially evaluate in constant time:
    AstKonst1 _k v -> build1Vectorize1 n (var, v)
    AstAppend1 v w ->
      build1Vectorize1 n
        (var, AstCond1 (AstRelInt LsOp [i, AstLength v])
                       (AstIndex1 v i)
                       (AstIndex1 w (AstIntOp PlusIntOp [i, AstLength v])))
          -- this is basically partial evaluation, but in constant time,
          -- as opposed to similarly evaluating AstFromList1, etc.;
          -- this may get stuck as AstSelect1 eventually, but pushing indexing
          -- down into both v and w would then get stuck as well (twice!)
    AstSlice1 i2 _k v ->
      build1VectorizeIndex1 n var v (AstIntOp PlusIntOp [i, i2])
    AstReverse1 v ->
      build1VectorizeIndex1Var n var v
        (AstIntOp MinusIntOp [AstIntOp MinusIntOp [AstLength v, 1], i])
    AstBuildPair1{} -> AstBuildPair1 n (var, AstIndex1 v1 i)
      -- TODO: a previous failure of vectorization that should have
      -- led to an abort instead of showing up late
      -- TODO: or a wonderful chance to recover failed vectorization,
      -- by taking only an element of this build! so shall failed
      -- vectorization not abort, after all? and only check at whole program
      -- vectorization end that no build has been left unvectorized?
      -- the code would be
      -- build1Vectorize1 n (var, substitute var2 i u2))
      -- or we'd use environments instead of the substitution
    -- Can't push indexing down, so try analyzing the index instead:
    AstTranspose1{} -> build1VectorizeIndex1Try n var v1 i
      -- a more general indexing needed, one intespersed with transpose
      -- or operating on the underlying vector of elements instead?
    AstTransposeGeneral1{} -> build1VectorizeIndex1Try n var v1 i
      -- an even more general indexing needed?
    AstFlatten{} -> build1VectorizeIndex1Try n var v1 i
    AstReshape1{} -> build1VectorizeIndex1Try n var v1 i
      -- an even more general indexing needed?

    AstIndex0{} -> error "build1VectorizeIndex1Var: wrong rank"
    AstSum0{} -> error "build1VectorizeIndex1Var: wrong rank"
    AstDot0{} -> error "build1VectorizeIndex1Var: wrong rank"
    AstFromList01 sh l ->
      build1VectorizeIndex1Var n var (AstReshape1 sh $ AstFromList1 l) i
    AstFromVector01 sh l ->
      build1VectorizeIndex1Var n var (AstReshape1 sh $ AstFromVector1 l) i
    AstKonst01 sh v ->
      let k = product sh
      in build1VectorizeIndex1Var n var (AstReshape1 sh $ AstKonst1 k v) i
    AstBuildPair01{} ->
      AstBuildPair1 n (var, AstIndex1 v1 i)  -- see AstBuildPair1 above

    AstOMap0{} -> error "build1VectorizeIndex1Var: wrong rank"
    AstOMap1{} ->
      AstConstant1 $ AstPrimalPart1 $ AstBuildPair1 n (var, AstIndex1 v1 i)
    -- All other patterns are redundant due to GADT typing.

-- | The variable is known to occur in the term or in the index
-- (it doesn't matter much which, because other variables may occur, too).
-- We can' push indexing down any more, so we analyze the index expression
-- instead.
build1VectorizeIndex1Try
  :: AstInt r -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Ast (1 + n) r
build1VectorizeIndex1Try n var v i = case i of
  AstIntOp PlusIntOp [AstIntVar var2, i2]
    | var2 == var && not (intVarInAstInt var i2) && not (intVarInAst var v) ->
      AstSlice1 i2 n v
  AstIntVar var2 | var2 == var && not (intVarInAst var v) ->
    AstSlice1 0 n v
  _ -> AstBuildPair1 n (var, AstIndex1 v i)
    -- TODO: many more cases; not sure how systematic it can be

intVarInAst :: AstVarName Int -> Ast n r -> Bool
intVarInAst var = \case
  AstOp1 _ l -> or $ map (intVarInAst var) l
  AstCond1 b x y ->
    intVarInAstBool var b || intVarInAst var x || intVarInAst var y
  AstSelect1 n (_, b) x y ->
    intVarInAstInt var n || intVarInAstBool var b
    || intVarInAst var x || intVarInAst var y
  AstInt1 n -> intVarInAstInt var n
  AstConst1{} -> False
  AstConstant1 (AstPrimalPart1 v) -> intVarInAst var v
  AstScale1 (AstPrimalPart1 v) u -> intVarInAst var v || intVarInAst var u

  AstVar0{} -> False  -- not an int variable
  AstVar1{} -> False  -- not an int variable

  AstIndex1 v ix -> intVarInAst var v || intVarInAstInt var ix
  AstSum1 v -> intVarInAst var v
  AstFromList1 l -> or $ map (intVarInAst var) l  -- down from rank 1 to 0
  AstFromVector1 vl -> or $ map (intVarInAst var) $ V.toList vl
  AstKonst1 n v -> intVarInAstInt var n || intVarInAst var v
  AstAppend1 v u -> intVarInAst var v || intVarInAst var u
  AstSlice1 i k v -> intVarInAstInt var i || intVarInAstInt var k
                     || intVarInAst var v
  AstReverse1 v -> intVarInAst var v
  AstBuildPair1 n (_, v) -> intVarInAstInt var n || intVarInAst var v
  AstTranspose1 v -> intVarInAst var v
  AstTransposeGeneral1 _ v -> intVarInAst var v
  AstFlatten v -> intVarInAst var v
  AstReshape1 sh v -> or (map (intVarInAstInt var) sh) || intVarInAst var v

  AstIndex0 v ixs -> intVarInAst var v || or (map (intVarInAstInt var) ixs)
  AstSum0 v -> intVarInAst var v
  AstDot0 v u -> intVarInAst var v || intVarInAst var u
  AstFromList01 sh l -> or (map (intVarInAstInt var) sh)
                        || or (map (intVarInAst var) l)
  AstFromVector01 sh l -> or (map (intVarInAstInt var) sh)
                          || V.or (V.map (intVarInAst var) l)
  AstKonst01 sh v -> or (map (intVarInAstInt var) sh) || intVarInAst var v
  AstBuildPair01 n (_, v) -> intVarInAstInt var n || intVarInAst var v

  AstOMap0 (_, v) u -> intVarInAst var v || intVarInAst var u
    -- the variable in binder position, so ignored (and should be distinct)
  AstOMap1 (_, v) u -> intVarInAst var v || intVarInAst var u

intVarInAstInt :: AstVarName Int -> AstInt r -> Bool
intVarInAstInt var = \case
  AstIntOp _ l -> or $ map (intVarInAstInt var) l
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstIntConst{} -> False
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstLength v -> intVarInAst var v
  AstMinIndex v -> intVarInAst var v
  AstMaxIndex v -> intVarInAst var v

intVarInAstBool :: AstVarName Int -> AstBool r -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> or $ map (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> or $ map (intVarInAst var) l
  AstRelInt _ l  -> or $ map (intVarInAstInt var) l


-- * Odds and ends

leqAst :: Ast 0 r -> Ast 0 r -> AstBool r
leqAst d e = AstRel LeqOp [d, e]

gtAst :: Ast 0 r -> Ast 0 r -> AstBool r
gtAst d e = AstRel GtOp [d, e]

gtIntAst :: AstInt r -> AstInt r -> AstBool r
gtIntAst i j = AstRelInt GtOp [i, j]


-- * Interpretation of Ast in ADVal

-- First come definition of some ADVal combinators to be used below.
-- They are more general than their legacy versions for rank 1 above
-- and sometimes more general than the Ast operations.
index0' :: (ADModeAndNum d r, KnownNat n)
        => ADVal d (OR.Array n r) -> [Int] -> ADVal d r
index0' (D u u') ixs = dD (u `atIndexInTensorR` ixs)
                          (dIndex0 u' ixs (OR.shapeL u))

sum0' :: (ADModeAndNum d r, KnownNat n)
      => ADVal d (OR.Array n r) -> ADVal d r
sum0' (D u u') = dD (LA.sumElements $ OR.toVector u) (dSum0 (OR.shapeL u) u')

dot0' :: (ADModeAndNum d r, KnownNat n)
      => ADVal d (OR.Array n r) -> ADVal d (OR.Array n r) -> ADVal d r
dot0' (D u u') (D v v') = dD (OR.toVector u LA.<.> OR.toVector v)
                              (dAdd (dDot0 v u') (dDot0 u v'))

unScalar0 :: ADModeAndNum d r => ADVal d (OR.Array 0 r) -> ADVal d r
unScalar0 (D u u') = dD (OR.unScalar u) (dUnScalar0 u')

index1' :: (ADModeAndNum d r, KnownNat n)
        => ADVal d (OR.Array (1 + n) r) -> Int -> ADVal d (OR.Array n r)
index1' (D u u') ix = dD (u `OR.index` ix)
                         (dIndex1 u' ix (head $ OR.shapeL u))

sum1' :: (ADModeAndNum d r, KnownNat n)
      => ADVal d (OR.Array (1 + n) r) -> ADVal d (OR.Array n r)
sum1' (D u u') = dD (ORB.sumA $ OR.unravel u)
                    (dSum1 (head $ OR.shapeL u) u')

fromList1' :: (ADModeAndNum d r, KnownNat n)
           => [ADVal d (OR.Array n r)]
           -> ADVal d (OR.Array (1 + n) r)
fromList1' lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (OR.ravel . ORB.fromList [length lu]
      $ map (\(D u _) -> u) lu)
     (dFromList1 $ map (\(D _ u') -> u') lu)

fromVector1' :: (ADModeAndNum d r, KnownNat n)
             => Data.Vector.Vector (ADVal d (OR.Array n r))
             -> ADVal d (OR.Array (1 + n) r)
fromVector1' lu =
  dD (OR.ravel . ORB.fromVector [V.length lu] . V.convert
      $ V.map (\(D u _) -> u) lu)
     (dFromVector1 $ V.map (\(D _ u') -> u') lu)

konst1' :: (ADModeAndNum d r, KnownNat n)
        => Int -> ADVal d (OR.Array n r) -> ADVal d (OR.Array (1 + n) r)
konst1' n (D u u') = dD (OR.ravel (ORB.constant [n] u))
                         (dKonst1 n u')

append1' :: (ADModeAndNum d r, KnownNat n)
         => ADVal d (OR.Array n r) -> ADVal d (OR.Array n r)
         -> ADVal d (OR.Array n r)
append1' (D u u') (D v v') = dD (OR.append u v)
                                (dAppend1 u' (head $ OR.shapeL u) v')

slice1' :: (ADModeAndNum d r, KnownNat n)
        => Int -> Int -> ADVal d (OR.Array n r) -> ADVal d (OR.Array n r)
slice1' i k (D u u') = dD (OR.slice [(i, k)] u)
                          (dSlice1 i k u' (head $ OR.shapeL u))

reverse1' :: (ADModeAndNum d r, KnownNat n)
          => ADVal d (OR.Array n r) -> ADVal d (OR.Array n r)
reverse1' (D u u') = dD (OR.rev [0] u) (dReverse1 u')

-- The element-wise (POPL) version, but only one rank at a time.
build1' :: (ADModeAndNum d r, KnownNat n)
        => Int -> (Int -> ADVal d (OR.Array n r))
        -> ADVal d (OR.Array (1 + n) r)
build1' n f = fromList1' $ map f [0 .. n - 1]

transposeGeneral1' :: (ADModeAndNum d r, KnownNat n)
                   => [Int] -> ADVal d (OR.Array n r) -> ADVal d (OR.Array n r)
transposeGeneral1' perm (D u u') = dD (OR.transpose perm u)
                                      (dTransposeGeneral1 perm u')

reshape1' :: (ADModeAndNum d r, KnownNat n, KnownNat m)
          => OR.ShapeL -> ADVal d (OR.Array n r) -> ADVal d (OR.Array m r)
reshape1' sh (D u u') = dD (OR.reshape sh u) (dReshape1 (OR.shapeL u) sh u')

fromList01' :: (ADModeAndNum d r, KnownNat n)
            => OR.ShapeL -> [ADVal d r]
            -> ADVal d (OR.Array n r)
fromList01' sh l =
  dD (OR.fromList sh $ map (\(D u _) -> u) l)  -- I hope this fuses
     (dFromList01 sh $ map (\(D _ u') -> u') l)

fromVector01' :: (ADModeAndNum d r, KnownNat n)
              => OR.ShapeL -> Data.Vector.Vector (ADVal d r)
              -> ADVal d (OR.Array n r)
fromVector01' sh l =
  dD (OR.fromVector sh $ V.convert $ V.map (\(D u _) -> u) l)  -- hope it fuses
     (dFromVector01 sh $ V.map (\(D _ u') -> u') l)

konst01' :: (ADModeAndNum d r, KnownNat n)
         => OR.ShapeL -> ADVal d r -> ADVal d (OR.Array n r)
konst01' sh (D u u') = dD (OR.constant sh u) (dKonst01 sh u')

scalar1 :: ADModeAndNum d r => ADVal d r -> ADVal d (OR.Array 0 r)
scalar1 (D u u') = dD (OR.scalar u) (dScalar1 u')

interpretLambdaD1
  :: ADModeAndNum d r
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> (AstVarName r, Ast 0 r)
  -> ADVal d r -> ADVal d r
interpretLambdaD1 env (AstVarName var, ast) =
  \d -> unScalar0 $ interpretAst (IM.insert var (AstVarR0 d) env) ast

interpretLambdaI1
  :: (ADModeAndNum d r, KnownNat n)
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> (AstVarName Int, Ast n r)
  -> Int -> ADVal d (OR.Array n r)
interpretLambdaI1 env (AstVarName var, ast) =
  \i -> interpretAst (IM.insert var (AstVarI i) env) ast

interpretAstPrimal
  :: (ADModeAndNum d r, KnownNat n)
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> Ast n r -> OR.Array n r
interpretAstPrimal env v = let D u _ = interpretAst env v in u

interpretAst
  :: (ADModeAndNum d r, KnownNat n)
  => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
  -> Ast n r -> ADVal d (OR.Array n r)
interpretAst env = \case
  AstOp1 opCode args ->
    interpretAstOp (interpretAst env) opCode args
  AstCond1 b a1 a2 -> if interpretAstBool env b
                      then interpretAst env a1
                      else interpretAst env a2
  AstSelect1 n (AstVarName var, b) a1 a2 ->
    let k = interpretAstInt env n
        f [i] = if interpretAstBool (IM.insert var (AstVarI i) env) b
                then 1
                else 0
        f _ = error "interpretAst: unexpected argument to AstSelect1"
        bitmap = constant $ OR.generate [k] f
        v1 = interpretAst env a1
        v2 = interpretAst env a2
    in bitmap * v1 + v2 - bitmap * v2
  AstInt1 i -> fromInteger $ fromIntegral $ interpretAstInt env i
  AstConst1 a -> constant a
  AstConstant1 (AstPrimalPart1 a) -> constant $ interpretAstPrimal env a
  AstScale1 (AstPrimalPart1 r) d ->
    scale (interpretAstPrimal env r) (interpretAst env d)

  AstVar0 (AstVarName var) -> case IM.lookup var env of
    Just (AstVarR0 d) -> scalar1 d
    Just AstVarR1{} ->
      error $ "interpretAst: type mismatch for var " ++ show var
    Just AstVarI{} ->
      error $ "interpretAst: type mismatch for var " ++ show var
    Nothing -> error $ "interpretAst: unknown variable var " ++ show var
  AstVar1 (AstVarName var) -> case IM.lookup var env of
    Just AstVarR0{} ->
      error $ "interpretAst: type mismatch for var " ++ show var
    Just (AstVarR1 d) -> d
    Just AstVarI{} ->
      error $ "interpretAst: type mismatch for var " ++ show var
    Nothing -> error $ "interpretAst: unknown variable var " ++ show var

  AstIndex1 v i -> index1' (interpretAst env v) (interpretAstInt env i)
  AstSum1 v -> sum1' (interpretAst env v)
  AstFromList1 l -> fromList1' (map (interpretAst env) l)
  AstFromVector1 l -> fromVector1' (V.map (interpretAst env) l)
  AstKonst1 n v -> konst1' (interpretAstInt env n) (interpretAst env v)
  AstAppend1 x y -> append1' (interpretAst env x) (interpretAst env y)
  AstSlice1 i k v -> slice1' (interpretAstInt env i) (interpretAstInt env k)
               (interpretAst env v)
  AstReverse1 v -> reverse1' (interpretAst env v)
  AstBuildPair1 i (var, AstConstant1 r) ->
    let n = interpretAstInt env i
    in constant
       $ OR.ravel . ORB.fromVector [n] . V.generate n
       $ \j -> let D v _ = interpretLambdaI1 env (var, AstConstant1 r) j
               in v
  AstBuildPair1 i (var, v) ->
    build1' (interpretAstInt env i) (interpretLambdaI1 env (var, v))
      -- fallback to POPL (memory blowup, but avoids functions on tape);
      -- an alternative is to use dBuild1 and store function on tape
  AstTranspose1 v -> interpretAst env $ AstTransposeGeneral1 [1, 0] v
  AstTransposeGeneral1 perm v ->
    let d@(D u _) = interpretAst env v
    in if OR.rank u <= length perm - 1 then d else transposeGeneral1' perm d
  AstFlatten v -> let d@(D u _) = interpretAst env v
                  in reshape1' [OR.size u] d
  AstReshape1 ns v -> reshape1' (map (interpretAstInt env) ns)
                                (interpretAst env v)

  AstIndex0 v is ->
    scalar1 $ index0' (interpretAst env v) (map (interpretAstInt env) is)
  AstSum0 v -> scalar1 $ sum0' (interpretAst env v)
  AstDot0 x y -> scalar1 $ dot0' (interpretAst env x) (interpretAst env y)
  AstFromList01 sh l -> fromList01' (map (interpretAstInt env) sh)
                        $ map (unScalar0 . interpretAst env) l
  AstFromVector01 sh l -> fromVector01' (map (interpretAstInt env) sh)
                          $ V.map (unScalar0 . interpretAst env) l
  AstKonst01 sh r -> konst01' (map (interpretAstInt env) sh)
                              (unScalar0 $ interpretAst env r)
  AstBuildPair01 i (var, r) -> interpretAst env $ AstBuildPair1 i (var, r)

  AstOMap0 (var, r) e ->  -- this only works on the primal part hence @constant@
    constant
    $ omap (\x -> let D u _ = interpretLambdaD1 env (var, r) (constant x)
                  in u)
           (interpretAstPrimal env e)
  AstOMap1 (var, r) e ->  -- this only works on the primal part hence @constant@
    constant
    $ omap (\x -> let D u _ = interpretLambdaD1 env (var, r) (constant x)
                  in u)
           (interpretAstPrimal env e)

interpretAstInt :: ADModeAndNum d r
                => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
                -> AstInt r -> Int
interpretAstInt env = \case
  AstIntOp opCodeInt args ->
    interpretAstIntOp (interpretAstInt env) opCodeInt args
  AstIntCond b a1 a2 -> if interpretAstBool env b
                        then interpretAstInt env a1
                        else interpretAstInt env a2
  AstIntConst a -> a
  AstIntVar (AstVarName var) -> case IM.lookup var env of
    Just AstVarR0{} ->
      error $ "interpretAstInt: type mismatch for var " ++ show var
    Just AstVarR1{} ->
      error $ "interpretAstInt: type mismatch for var " ++ show var
    Just (AstVarI i) -> i
    Nothing -> error $ "interpretAstInt: unknown variable var " ++ show var
  AstLength v -> case OR.shapeL $ interpretAstPrimal env v of
    [] -> error "interpretAstInt: impossible shape for rank >= 1"
    len_outermost : _ -> len_outermost
  AstMinIndex v -> lminIndex $ interpretAst env v
  AstMaxIndex v -> lmaxIndex $ interpretAst env v

interpretAstBool :: ADModeAndNum d r
                 => IM.IntMap (AstVar (ADVal d r) (ADVal d (Vec r)))
                 -> AstBool r -> Bool
interpretAstBool env = \case
  AstBoolOp opCodeBool args ->
    interpretAstBoolOp (interpretAstBool env) opCodeBool args
  AstBoolConst a -> a
  AstRel opCodeRel args ->
    let f x = interpretAstPrimal env x
    in interpretAstRel f opCodeRel args
  AstRelInt opCodeRel args ->
    let f = interpretAstInt env
    in interpretAstRel f opCodeRel args

interpretAstOp :: RealFloat b
               => (c -> b) -> OpCode -> [c] -> b
{-# INLINE interpretAstOp #-}
interpretAstOp f PlusOp [u, v] = f u + f v
interpretAstOp f MinusOp [u, v] = f u - f v
interpretAstOp f TimesOp [u, v] = f u * f v
interpretAstOp f NegateOp [u] = negate $ f u
interpretAstOp f AbsOp [u] = abs $ f u
interpretAstOp f SignumOp [u] = signum $ f u
interpretAstOp f DivideOp [u, v] = f u / f v
interpretAstOp f RecipOp [u] = recip $ f u
interpretAstOp f ExpOp [u] = exp $ f u
interpretAstOp f LogOp [u] = log $ f u
interpretAstOp f SqrtOp [u] = sqrt $ f u
interpretAstOp f PowerOp [u, v] = f u ** f v
interpretAstOp f LogBaseOp [u, v] = logBase (f u) (f v)
interpretAstOp f SinOp [u] = sin $ f u
interpretAstOp f CosOp [u] = cos $ f u
interpretAstOp f TanOp [u] = tan $ f u
interpretAstOp f AsinOp [u] = asin $ f u
interpretAstOp f AcosOp [u] = acos $ f u
interpretAstOp f AtanOp [u] = atan $ f u
interpretAstOp f SinhOp [u] = sinh $ f u
interpretAstOp f CoshOp [u] = cosh $ f u
interpretAstOp f TanhOp [u] = tanh $ f u
interpretAstOp f AsinhOp [u] = asinh $ f u
interpretAstOp f AcoshOp [u] = acosh $ f u
interpretAstOp f AtanhOp [u] = atanh $ f u
interpretAstOp f Atan2Op [u, v] = atan2 (f u) (f v)
interpretAstOp f MaxOp [u, v] = max (f u) (f v)
interpretAstOp f MinOp [u, v] = min (f u) (f v)
interpretAstOp _ opCode args =
  error $ "interpretAstOp: wrong number of arguments"
          ++ show (opCode, length args)

interpretAstIntOp :: (AstInt r -> Int) -> OpCodeInt -> [AstInt r] -> Int
{-# INLINE interpretAstIntOp #-}
interpretAstIntOp f PlusIntOp [u, v] = f u + f v
interpretAstIntOp f MinusIntOp [u, v] = f u - f v
interpretAstIntOp f TimesIntOp [u, v] = f u * f v
interpretAstIntOp f NegateIntOp [u] = negate $ f u
interpretAstIntOp f AbsIntOp [u] = abs $ f u
interpretAstIntOp f SignumIntOp [u] = signum $ f u
interpretAstIntOp f MaxIntOp [u, v] = max (f u) (f v)
interpretAstIntOp f MinIntOp [u, v] = min (f u) (f v)
interpretAstIntOp _ opCodeInt args =
  error $ "interpretAstIntOp: wrong number of arguments"
          ++ show (opCodeInt, length args)

interpretAstBoolOp :: (AstBool r -> Bool) -> OpCodeBool -> [AstBool r]
                   -> Bool
{-# INLINE interpretAstBoolOp #-}
interpretAstBoolOp f NotOp [u] = not $ f u
interpretAstBoolOp f AndOp [u, v] = f u && f v
interpretAstBoolOp f OrOp [u, v] = f u || f v
interpretAstBoolOp f IffOp [u, v] = f u == f v
interpretAstBoolOp _ opCodeBool args =
  error $ "interpretAstBoolOp: wrong number of arguments"
          ++ show (opCodeBool, length args)

interpretAstRel :: Ord b => (a -> b) -> OpCodeRel -> [a] -> Bool
{-# INLINE interpretAstRel #-}
interpretAstRel f EqOp [u, v] = f u == f v
interpretAstRel f NeqOp [u, v] = f u /= f v
interpretAstRel f LeqOp [u, v] = f u <= f v
interpretAstRel f GeqOp [u, v] = f u >= f v
interpretAstRel f LsOp [u, v] = f u < f v
interpretAstRel f GtOp [u, v] = f u > f v
interpretAstRel _ opCodeRel args =
  error $ "interpretAstRel: wrong number of arguments"
          ++ show (opCodeRel, length args)
