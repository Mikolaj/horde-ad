{-# LANGUAGE CPP, DataKinds, FlexibleInstances, FunctionalDependencies, GADTs,
             MultiParamTypeClasses, QuantifiedConstraints, RankNTypes,
             TypeFamilies #-}
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
  , ADMode(..), ADModeAndNum, ADModeAndNumNew
  , liftToAst0, liftToAst1
  , NumOf, VectorOf
  , IsPrimal (..), IsPrimalAndHasFeatures, IsPrimalAndHasInputs, HasDelta
  , Under, Element
  , Domain0, Domain1, Domains(..), nullDomains  -- an important re-export
  , -- temporarily re-exported, until these are wrapped in sugar
    Ast(..), Ast0, Ast1, AstVarName(..), AstVar(..), AstInt(..), AstBool(..)
  , CodeOut(..), CodeIntOut(..), CodeBoolOut(..), RelOut(..)
  ) where

import Prelude

import           Data.MonoTraversable (MonoFunctor (omap))
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Map as M
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA

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

relu :: (ADModeAndNumNew d r, IsPrimalAndHasFeatures d a r)
     => ADVal d a -> ADVal d a
relu v@(D u _) =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0) u
  in scale oneIfGtZero v

reluLeaky :: (ADModeAndNumNew d r, IsPrimalAndHasFeatures d a r)
          => ADVal d a -> ADVal d a
reluLeaky v@(D u _) =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0.01) u
  in scale oneIfGtZero v

condAst :: IsPrimal d (Ast r d a)
        => AstBool r d -> ADVal d (Ast r d a) -> ADVal d (Ast r d a)
        -> ADVal d (Ast r d a)
condAst b (D d _) (D e _) = astToD (AstCond b d e)


-- * Operations resulting in a scalar

varAst0 :: (ADModeAndNumNew d r, Under r ~ r)
        => String -> ADVal d (Ast r d r)
varAst0 s = astToD (AstVar $ AstVarName s)

sumElements10 :: ADModeAndNumNew d r
              => ADVal d (VectorOf r) -> ADVal d r
sumElements10 (D u u') = dD (lsumElements10 u) (dSumElements10 u' (llength u))

index10 :: ADModeAndNumNew d r => ADVal d (VectorOf r) -> NumOf r -> ADVal d r
index10 (D u u') ix = dD (lindex10 u ix) (dIndex10 u' ix (llength u))

minimum0 :: ADModeAndNumNew d r => ADVal d (VectorOf r) -> ADVal d r
minimum0 (D u u') =
  dD (lminElement u) (dIndex10 u' (lminIndex u) (llength u))

maximum0 :: ADModeAndNumNew d r => ADVal d (VectorOf r) -> ADVal d r
maximum0 (D u u') =
  dD (lmaxElement u) (dIndex10 u' (lmaxIndex u) (llength u))

foldl'0 :: ADModeAndNum d r
        => (ADVal d r -> ADVal d r -> ADVal d r)
        -> ADVal d r -> ADVal d (Vector r)
        -> ADVal d r
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (dD p (dIndex10 v' ix k)) acc
  in V.ifoldl' g uu' v

altSumElements10 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
altSumElements10 = foldl'0 (+) 0

-- | Dot product.
infixr 8 <.>!
(<.>!) :: ADModeAndNumNew d r
       => ADVal d (VectorOf r) -> ADVal d (VectorOf r) -> ADVal d r
(<.>!) (D u u') (D v v') = dD (ldot0 u v) (dAdd (dDot0 v u') (dDot0 u v'))

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: ADModeAndNumNew d r
        => ADVal d (VectorOf r) -> VectorOf r -> ADVal d r
(<.>!!) (D u u') v = dD (ldot0 u v) (dDot0 v u')

sumElementsVectorOfDual
  :: ADModeAndNumNew d r => Data.Vector.Vector (ADVal d r) -> ADVal d r
sumElementsVectorOfDual = V.foldl' (+) 0

softMax :: ADModeAndNumNew d r
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
lossCrossEntropyV :: ADModeAndNumNew d r
                  => VectorOf r
                  -> ADVal d (VectorOf r)
                  -> ADVal d r
lossCrossEntropyV targ res = negate $ log res <.>!! targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyV
  :: ADModeAndNumNew d r
  => VectorOf r -> ADVal d (VectorOf r) -> ADVal d r
lossSoftMaxCrossEntropyV target (D u u') =
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let expU = exp (u - lkonst1 (lmaxElement u) (llength u))
      sumExpU = lsumElements10 expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = LA.scaleRecip sumExpU expU
      softMaxU = lkonst1 recipSum (llength expU) * expU
  in dD (negate $ log softMaxU `ldot0` target)  -- TODO: avoid: log . exp
        (dDot0 (softMaxU - target) u')


-- * Operations resulting in a vector

-- @1@ means rank one, so the dual component represents a vector.
fromList1 :: ADModeAndNumNew d r
          => [ADVal d r] -> ADVal d (VectorOf r)
fromList1 l = dD (lfromList1 $ map (\(D u _) -> u) l)  -- I hope this fuses
                 (dFromList1 $ map (\(D _ u') -> u') l)

fromVector1 :: ADModeAndNumNew d r
            => Data.Vector.Vector (ADVal d r) -> ADVal d (VectorOf r)
fromVector1 v = dD (lfromVector1 $ V.map (\(D u _) -> u) v)  -- I hope it fuses
                   (dFromVector1 $ V.map (\(D _ u') -> u') v)

konst1 :: ADModeAndNumNew d r => ADVal d r -> NumOf r -> ADVal d (VectorOf r)
konst1 (D u u') n = dD (lkonst1 u n) (dKonst1 u' n)

append1 :: ADModeAndNumNew d r
        => ADVal d (VectorOf r) -> ADVal d (VectorOf r) -> ADVal d (VectorOf r)
append1 (D u u') (D v v') = dD (lappend1 u v) (dAppend1 u' (llength u) v')

slice1 :: ADModeAndNumNew d r
       => NumOf r -> NumOf r -> ADVal d (VectorOf r) -> ADVal d (VectorOf r)
slice1 i n (D u u') = dD (lslice1 i n u) (dSlice1 i n u' (llength u))

reverse1 :: ADModeAndNumNew d r => ADVal d (VectorOf r) -> ADVal d (VectorOf r)
reverse1 (D u u') = dD (lreverse1 u) (dReverse1 u')

-- TODO: define Enum instance of (AstInt r d) to enable AST for this.
-- No padding; remaining areas ignored.
maxPool1 :: ADModeAndNum d r
         => Int -> Int -> ADVal d (Vector r) -> ADVal d (Vector r)
maxPool1 ksize stride v@(D u _) =
  let slices = [slice1 i ksize v | i <- [0, stride .. V.length u - ksize]]
  in fromList1 $ map maximum0 slices

softMaxV :: ADModeAndNumNew d r
         => ADVal d (VectorOf r) -> ADVal d (VectorOf r)
softMaxV d@(D u _) =
  let expU = exp d  -- shared in 2 places, though cse may do this for us
      sumExpU = sumElements10 expU
  in konst1 (recip sumExpU) (llength u) * expU


-- * Build and map variants

build1POPL :: Int -> (Int -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
build1POPL n f = V.fromList $ map f [0 .. n - 1]

-- Fake rank 1. This is still an array of delta expressions, thinly wrapped,
-- instead of a single delta expression representing an array.
-- We gain a little by storing the primal part in an unboxed vector.
build1Elementwise
  :: ADModeAndNumNew d r
  => Int -> (Int -> ADVal d r) -> ADVal d (VectorOf r)
build1Elementwise n f = fromList1 $ map f [0 .. n - 1]
  -- equivalent to @fromVector1 $ build1POPL n f@

build1Closure
  :: (ADModeAndNumNew d r, NumOf r ~ Int)
  => Int -> (Int -> ADVal d r) -> ADVal d (VectorOf r)
build1Closure n f =
  let g i = let D u _ = f i in u
      h i = let D _ u' = f i in u'
  in dD (lfromList1 $ map g [0 .. n - 1]) (dBuild1 n h)

build1
  :: (ADModeAndNumNew d r, NumOf r ~ Int)
  => Int -> (Int -> ADVal d r) -> ADVal d (VectorOf r)
build1 = build1Closure

map1POPL :: (ADVal d r -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
         -> Data.Vector.Vector (ADVal d r)
map1POPL f vd = V.map f vd

map1Elementwise
  :: (ADModeAndNumNew d r, NumOf r ~ Int)
  => (ADVal d r -> ADVal d r) -> ADVal d (VectorOf r) -> ADVal d (VectorOf r)
map1Elementwise f d@(D v _v') =
  build1Elementwise (llength v) $ \i -> f (index10 d i)
    -- equivalent to
    -- @fromVector1 . map1POPL f . rank1toVector
    --   where rank1toVector d@(D v _v') = V.generate (V.length v) (index10 d)@

map1Closure
  :: (ADModeAndNumNew d r, NumOf r ~ Int)
  => (ADVal d r -> ADVal d r) -> ADVal d (VectorOf r) -> ADVal d (VectorOf r)
map1Closure f d@(D v _) = build1Closure (llength v) $ \i -> f (index10 d i)


-- * AST-based build and map variants

-- Orphan instances to split a module.
instance (VectorOf r ~ Vector r, Under r ~ r, Numeric r)
         => AstVectorLike d r (Vector r) r where
  lbuildAst1 n (var, u) =
    interpretAst M.empty $ build1Vectorize (AstIntConst n) (var, u)
  lmapAst1 (var, u) e =
    interpretAst M.empty $ map1Vectorize (var, u) (AstD e)

instance IsPrimal d (Ast r d (Vector r))
         => AstVectorLike d r (Ast r d (Vector r)) (Ast r d r) where
  lbuildAst1 n (var, u) = astToD (build1Vectorize n (var, u))
  lmapAst1 (var, u) (D w _) = astToD (map1Vectorize (var, u) w)

buildAst1
  :: (AstVectorLike d u v r, ADModeAndNumNew d r)
  => NumOf r -> (String, ADVal d (Ast u d u)) -> ADVal d v
buildAst1 n (var, D u _) = lbuildAst1 n (AstVarName var, u)

mapAst1
  :: (AstVectorLike d u v r, ADModeAndNumNew d r)
  => (String, ADVal d (Ast u d u)) -> ADVal d v -> ADVal d v
mapAst1 (var, D u _) e = lmapAst1 (AstVarName var, u) e

-- TODO: question: now I vectorize nested builds/maps when they are created;
-- should I instead wait and vectorize the whole term? Probably
-- no harm done, since the whole term is eventually vectorized anyway,
-- with arbitrily deep traversals.
build1Vectorize
  :: ADModeAndNumNew d r
  => AstInt r d -> (AstVarName Int, Ast r d r)
  -> Ast r d (Vector r)
build1Vectorize n (var, u) = case u of
  AstOp codeOut args ->  -- AstOp0
    AstOp codeOut $ map (\w -> build1Vectorize n (var, w)) args  -- AstOp1
  AstCond _b _x _y ->
    -- TODO:
    -- Handle conditionals that depend on var, so that we produce conditional
    -- delta expressions of size proportional to the exponent of conditional
    -- nesting, instead of proportional to the number of elements of the tensor.
    --
    -- Perhaps partition indexes vs b resulting in bitmasks b1 and b2
    -- and recursively process vectorized b1 * x1 + b2 * x2?
    AstBuild1 n (var, u)
      -- fallback to POPL (memory blowup, but avoids functions on tape)
      -- TODO: instead, save AST on tape and interpret the function at backprop;
      -- that would permit serialization to GPU, though serialization
      -- of Tree0 while preserving sharing is costly, but perhaps GPUs
      -- can generate deltas themselves now that closures are not needed?
  AstConst r -> AstKonst1 (AstConst r) n
  AstD d -> AstKonst1 (AstD d) n
  AstVar var2 -> AstKonst1 (AstVar var2) n
  AstMinElement _v -> AstBuild1 n (var, u)  -- TODO
  AstMaxElement _v -> AstBuild1 n (var, u)  -- TODO
  AstSumElements10 _v -> AstBuild1 n (var, u)  -- TODO
  AstIndex10 v i -> index10Vectorize n var v i  -- TODO simplify i first
  AstDot0 _u _v -> AstBuild1 n (var, u)  -- TODO
    -- equal to @build1Vectorize n (var, AstSumElements10 (u * v))@,
    -- but how to vectorize AstSumElements10?
  -- All other patterns are redundant due to GADT typing.

index10Vectorize
  :: ADModeAndNumNew d r
  => AstInt r d -> AstVarName Int -> Ast r d (Vector r) -> AstInt r d
  -> Ast r d (Vector r)
index10Vectorize n var v i =
  case v of
    AstOp codeOut args ->  -- AstOp1
      AstOp codeOut $ map (\w -> index10Vectorize n var w i) args  -- AstOp1
    AstCond b x y ->
      build1Vectorize n (var, AstCond b (AstIndex10 x i) (AstIndex10 y i))
    AstConst _r -> index10VectorizeVarNotInV n var v i
    AstD _d -> index10VectorizeVarNotInV n var v i
    -- AstFromList1, AstFromVector1: see Note [AstFromList1 is hard]
    AstFromList1 l | AstIntConst k <- i -> build1Vectorize n (var, l !! k)
    -- TODO: AstAppend1 v1 v2 -> ... AstCond (i < AstLength v1) (...v1) (...v2)
    AstKonst1 r _ -> build1Vectorize n (var, r)
    AstSlice1 i2 _ u ->
      build1Vectorize n (var, AstIndex10 u (AstIntOp PlusIntOut [i2, i]))
        -- TODO: or should we rewrite in the opposite direction?
    -- TODO: AstReverse1 easy
    -- AstBuild1 _ (var2, u2) ->
    --   build1Vectorize n (var, substitute var2 i u2))
           -- TODO: use environments instead
    _ ->
      if intVarInAst var v
      then -- can't do much, probably, since v different in each cell?
        AstBuild1 n (var, AstIndex10 v i)
      else
        index10VectorizeVarNotInV n var v i

-- The case where @var@ does not occur in @v@.
index10VectorizeVarNotInV
  :: AstInt r d -> AstVarName Int -> Ast r d (Vector r) -> AstInt r d
  -> Ast r d (Vector r)
index10VectorizeVarNotInV n var v i = case i of
  AstIntOp PlusIntOut [AstIntVar var2, i2] | var2 == var ->
    AstSlice1 i2 n v
  AstIntConst _i2 ->
    AstKonst1 (AstIndex10 v i) n  -- v and i the same in each cell, so legit
  AstIntVar var2 | var2 == var ->
    AstSlice1 0 n v  -- simplified further elsewhere, if just identity
  AstIntVar _var2 ->
    AstKonst1 (AstIndex10 v i) n  -- v and i the same in each cell, so legit
  _ -> AstBuild1 n (var, AstIndex10 v i)
    -- TODO:
    -- add a new 'gather' operation somehow and, if a more complex index
    -- expression, construct 'gather'

intVarInAst :: AstVarName Int -> Ast r d a -> Bool
intVarInAst var v = case v of
  AstOp _ lv -> or $ map (intVarInAst var) lv  -- unused
  AstCond _b x y -> intVarInAst var x || intVarInAst var y  -- TODO: check in b
  AstConst{} -> False  -- unused
  AstD{} -> False  -- unused
  AstFromList1 l -> or $ map (intVarInAst var) l  -- down from rank 1 to 0
  AstFromVector1 vl -> or $ map (intVarInAst var) $ V.toList vl
  _ -> True  -- conservative, TODO

{- Note [AstFromList1 is hard]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is an example where simple but complete vectorization makes things worse.
Any simple rule that would let us fully vectorize

AstBuild1 N ("ix", AstIndex10
                     (AstFromList1 [ AstIndex10 v (AstIntVar "ix")
                                   , AstIndex10 v (1 + AstIntVar "ix") ])
                     (AstIntVar "ix" `mod` 2))

would be similar to the POPL implementation of build,
which means constructing a collection of all build elements,
substituting a known integer for "ix" in each and storing them all
(eventually as delta-expressions on tape) until evaluation.

While substituting a known integer for "ix" may simplify @v@
and permit vectorization of builds nested inside @v@, this nevertheless
turns a 2-element expression written by the user into a N-element
monstrosity. With high enough N, evaluating the result takes much more
memory than storing a non-vectorized closure on tape (the closure
would be a serialized Ast expression, so possibly fine on GPUs).

A non-simple rule that would handle this example would need a special
build constructor variant that does not build from individual elements,
but from vectors, distributing their elements in various patterns
(in case of @mod@, concatenating their many "ix"-affected copies).
-}

-- TODO: Shall this be represented and processed as just build?
-- But doing this naively copies @w@ a lot, so we'd need to wait
-- until AST handles sharing properly.
map1Vectorize
  :: ADModeAndNumNew d r
  => (AstVarName (ADVal d r), Ast r d r) -> Ast r d (Vector r)
  -> Ast r d (Vector r)
map1Vectorize (var, u) w = case u of
  AstOp codeOut args ->
    AstOp codeOut $ map (\x -> map1Vectorize (var, x) w) args
  AstCond _b _x1 _x2 -> AstMap1 (var, u) w  -- TODO
  AstConst r -> AstKonst1 (AstConst r) (AstLength w)
  AstD d -> AstKonst1 (AstD d) (AstLength w)
  AstVar var2 | var2 == var -> w  -- identity mapping
  AstVar var2 -> AstKonst1 (AstVar var2) (AstLength w)
  AstMinElement _v -> AstMap1 (var, u) w  -- TODO
  AstMaxElement _v -> AstMap1 (var, u) w  -- TODO
  AstSumElements10 _v -> AstMap1 (var, u) w  -- TODO
  AstIndex10 _v _i -> AstMap1 (var, u) w  -- TODO
    -- both _v and _i can depend on var, e.g., because of conditionals
  AstDot0 _u _v -> AstMap1 (var, u) w  -- TODO
  -- All other patterns are redundant due to GADT typing.

varInt :: String -> AstInt r d
varInt = AstIntVar . AstVarName

leqAst :: ADVal d (Ast r d r) -> ADVal d (Ast r d r) -> AstBool r d
leqAst (D d _) (D e _) = AstRel LeqOut [d, e]

gtAst :: ADVal d (Ast r d r) -> ADVal d (Ast r d r) -> AstBool r d
gtAst (D d _) (D e _) = AstRel GtOut [d, e]

gtIntAst :: AstInt r d -> AstInt r d -> AstBool r d
gtIntAst i j = AstRelInt GtOut [i, j]

interpretLambdaD0
  :: (ADModeAndNumNew d r, Under r ~ r, IsPrimalAndHasFeatures d a r)
  => M.Map String (AstVar r d) -> (AstVarName (ADVal d r), Ast r d a)
  -> ADVal d r -> ADVal d a
interpretLambdaD0 env (AstVarName var, ast) =
  \d -> interpretAst (M.insert var (AstVar0 d) env) ast

interpretLambdaI
  :: (ADModeAndNumNew d r, Under r ~ r, IsPrimalAndHasFeatures d a r)
  => M.Map String (AstVar r d) -> (AstVarName Int, Ast r d a)
  -> Int -> ADVal d a
interpretLambdaI env (AstVarName var, ast) =
  \i -> interpretAst (M.insert var (AstVarI i) env) ast

interpretAst
  :: (ADModeAndNumNew d r, Under r ~ r, IsPrimalAndHasFeatures d a r)
  => M.Map String (AstVar r d) -> Ast r d a -> ADVal d a
interpretAst env = \case
  AstOp codeOut args ->
    interpretAstOp (interpretAst env) codeOut args
  AstCond b a1 a2 -> if interpretAstBool env b
                     then interpretAst env a1
                     else interpretAst env a2
  AstConst a -> constant a
  AstD d -> d
  AstVar (AstVarName var) -> case M.lookup var env of
    Just (AstVar0 d) -> d
    Just AstVarI{} -> error $ "interpretAst: type mismatch for " ++ var
    Nothing -> error $ "interpretAst: unknown variable " ++ var
  AstMinElement v -> minimum0 $ interpretAst env v
  AstMaxElement v -> maximum0 $ interpretAst env v
  AstSumElements10 v -> sumElements10 $ interpretAst env v
  AstIndex10 v i -> index10 (interpretAst env v) (interpretAstInt env i)
  AstDot0 u v -> interpretAst env u <.>! interpretAst env v
  AstFromList1 l -> fromList1 $ map (interpretAst env) l
  AstFromVector1 v -> fromVector1 $ V.map (interpretAst env) v
  AstKonst1 r n -> konst1 (interpretAst env r) (interpretAstInt env n)
  AstAppend1 u v ->
    -- It's hard to simplify this already in build1Vectorize, because
    -- we may not know the real sizes there, only symbolic ones.
    let u'@(D pu _) = interpretAst env u
        v'@(D pv _) = interpretAst env v
    in if | V.null pu -> u'  -- perhaps common in code generated from AST
          | V.null pv -> v'
          | otherwise -> append1 u' v'
  AstSlice1 i n v ->
    let i' = interpretAstInt env i
        n' = interpretAstInt env n
        v'@(D pv _) = interpretAst env v
    in if i' == 0 && n' == V.length pv
       then v'  -- perhaps common in code generated from AST
       else slice1 i' n' v'
  AstReverse1 v -> reverse1 $ interpretAst env v
  AstBuild1 i (var, r) ->
    build1Elementwise (interpretAstInt env i) (interpretLambdaI env (var, r))
      -- fallback to POPL (memory blowup, but avoids functions on tape)
  AstMap1 (var, r) e ->
    map1Elementwise (interpretLambdaD0 env (var, r)) (interpretAst env e)
      -- fallback to POPL (memory blowup, but avoids functions on tape)
  AstOMap1{} -> error "TODO: AstOMap1"

interpretAstInt :: (ADModeAndNumNew d r, Under r ~ r)
                => M.Map String (AstVar r d) -> AstInt r d -> Int
interpretAstInt env = \case
  AstIntOp codeIntOut args ->
    interpretAstIntOp (interpretAstInt env) codeIntOut args
  AstIntCond b a1 a2 -> if interpretAstBool env b
                        then interpretAstInt env a1
                        else interpretAstInt env a2
  AstIntConst a -> a
  AstIntVar (AstVarName var) -> case M.lookup var env of
    Just AstVar0{} -> error $ "interpretAstP: type mismatch for " ++ var
    Just (AstVarI i) -> i
    Nothing -> error $ "interpretAstP: unknown variable " ++ var
  AstLength v -> V.length $ let D u _u' = interpretAst env v in u
  AstMinIndex v -> LA.minIndex $ let D u _u' = interpretAst env v in u
  AstMaxIndex v -> LA.maxIndex $ let D u _u' = interpretAst env v in u

interpretAstBool :: (ADModeAndNumNew d r, Under r ~ r)
                 => M.Map String (AstVar r d) -> AstBool r d -> Bool
interpretAstBool env = \case
  AstBoolOp codeBoolOut args ->
    interpretAstBoolOp (interpretAstBool env) codeBoolOut args
  AstBoolConst a -> a
  AstRel relOut args ->
    let f x = let D u _u' = interpretAst env x in u
    in interpretAstRel f relOut args
  AstRelInt relOut args ->
    let f = interpretAstInt env
    in interpretAstRel f relOut args

interpretAstOp :: RealFloat b
               => (Ast r d a -> b) -> CodeOut -> [Ast r d a] -> b
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

interpretAstIntOp :: (AstInt r d -> Int) -> CodeIntOut -> [AstInt r d] -> Int
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

interpretAstBoolOp :: (AstBool r d -> Bool) -> CodeBoolOut -> [AstBool r d]
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
