{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-missing-methods #-}
-- | Dual numbers and operations on them, which are extensions of normal
-- arithmetic and other operations to also cover derivatives.
module HordeAd.DualNumber where

import Prelude

import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra
  (Matrix, Numeric, Vector, konst, sumElements, (#>), (<.>))

import HordeAd.Delta (Delta (..))

-- * The main dual number types

data DualNumber r = D r (Delta r)

class (Monad m, Functor m, Applicative m) => DeltaMonad r m | m -> r where
  returnLet :: DualNumber r -> m (DualNumber r)
  returnLetV :: DualNumber (Vector r) -> m (DualNumber (Vector r))
  returnLetL :: DualNumber (Matrix r) -> m (DualNumber (Matrix r))


-- * General non-monadic operations

-- This instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (DualNumber r) where

instance Ord (DualNumber r) where

-- These instances are dangerous. Expressions should be wrapped in
-- the monadic @returnLet@ whenever there is a possibility they can be
-- used multiple times in a larger expression. Safer yet, monadic arithmetic
-- operations that already include @returnLet@ should be used instead,
-- such as @+\@, @*\@, etc.
instance Num r => Num (DualNumber r) where
  D u u' + D v v' = D (u + v) (Add u' v')
  D u u' - D v v' = D (u - v) (Add u' (Scale (-1) v'))
  D u u' * D v v' = D (u * v) (Add (Scale v u') (Scale u v'))
  negate (D v v') = D (- v) (Scale (-1) v')
  abs = undefined  -- TODO
  signum = undefined  -- TODO
  fromInteger = scalar . fromInteger

instance Real r => Real (DualNumber r) where
  toRational = undefined  -- TODO?

instance Fractional r => Fractional (DualNumber r) where
  D u u' / D v v' =
    let recipSq = recip (v * v)
    in D (u / v) (Add (Scale (v * recipSq) u') (Scale (- u * recipSq) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in D (recip v) (Scale minusRecipSq v')
  fromRational = scalar . fromRational

instance Floating r => Floating (DualNumber r) where
  pi = scalar pi
  exp (D u u') = let expU = exp u
                 in D expU (Scale expU u')
  log (D u u') = D (log u) (Scale (recip u) u')
  sqrt = undefined  -- TODO
  D u u' ** D v v' = D (u ** v) (Add (Scale (v * (u ** (v - 1))) u')
                                     (Scale ((u ** v) * log u) v'))
  logBase = undefined  -- TODO
  sin (D u u') = D (sin u) (Scale (cos u) u')
  cos (D u u') = D (cos u) (Scale (- (sin u)) u')
  tan = undefined  -- TODO
  asin = undefined  -- TODO
  acos = undefined  -- TODO
  atan = undefined  -- TODO
  sinh = undefined  -- TODO
  cosh = undefined  -- TODO
  tanh (D u u') = let y = tanh u
                  in D y (Scale (1 - y * y) u')
  asinh = undefined  -- TODO
  acosh = undefined  -- TODO
  atanh = undefined  -- TODO

instance RealFrac r => RealFrac (DualNumber r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance RealFloat r => RealFloat (DualNumber r) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in D (atan2 u v) (Add (Scale (- u * t) v') (Scale (v * t) u'))
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

scalar :: r -> DualNumber r
scalar r = D r Zero

scale :: Num r => r -> DualNumber r -> DualNumber r
scale r (D u u') = D (r * u) (Scale r u')

-- Optimized and more clearly written @u ** 2@.
square :: Num r => DualNumber r -> DualNumber r
square (D u u') = D (u * u) (Scale (2 * u) u')

logistic :: Floating r => DualNumber r -> DualNumber r
logistic (D u u') =
  let y = recip (1 + exp (- u))
  in D y (Scale (y * (1 - y)) u')

squaredDifference :: Num r => r -> DualNumber r -> DualNumber r
squaredDifference targ res = square $ res - scalar targ


-- * Non-monadic operations related to vectors

infixr 8 <.>!
(<.>!) :: Numeric r
       => DualNumber (Vector r)
       -> DualNumber (Vector r)
       -> DualNumber r
(<.>!) (D u u') (D v v') = D (u <.> v) (Add (Dot v u') (Dot u v'))

infixr 8 <.>!!
(<.>!!) :: Numeric r
        => DualNumber (Vector r)
        -> Vector r
        -> DualNumber r
(<.>!!) (D u u') v = D (u <.> v) (Dot v u')

konst' :: Numeric r => DualNumber r -> Int -> DualNumber (Vector r)
konst' (D u u') n = D (konst u n) (Konst u')

sumElements' :: Numeric r => DualNumber (Vector r) -> DualNumber r
sumElements' (D u u') = D (sumElements u) (SumElements u' (V.length u))

deltaSeq :: Numeric r
         => Data.Vector.Vector (DualNumber r) -> DualNumber (Vector r)
deltaSeq v = D (V.convert $ V.map (\(D u _) -> u) v)  -- I hope this fuses
               (Seq $ V.map (\(D _ u') -> u') v)

indexDeltaOfVector :: Numeric r
                   => DualNumber (Vector r) -> Int -> DualNumber r
indexDeltaOfVector (D u u') i = D (u V.! i) (Index u' i (V.length u))

-- | Dense matrix-vector product.
infixr 8 #>!
(#>!) :: Numeric r
      => DualNumber (Matrix r)
      -> DualNumber (Vector r)
      -> DualNumber (Vector r)
(#>!) (D u u') (D v v') =
  D (u #> v) (Add (DotRowL v u')
                  (DotL u (AsRow v')))

-- The unoptimized version:
-- D (u #> v) (Add (DotL (asRow v) u')
--                 (DotL u (AsRow v')))

-- | Dense matrix-vector product with a constant vector.
infixr 8 #>!!
(#>!!) :: Numeric r
       => DualNumber (Matrix r)
       -> Vector r
       -> DualNumber (Vector r)
(#>!!) (D u u') v = D (u #> v) (DotRowL v u')

-- The unoptimized version:
-- (#>!!) (D u u') v = D (u #> v) (DotL (asRow v) u')


-- * Monadic operations for scalars

-- Unfortunately, monadic versions of these operations are not
-- polymorphic over whether they operate on scalars, vectors or other types,
-- so further down they are duplicated.

tanhAct :: (DeltaMonad r m, Floating r) => DualNumber r -> m (DualNumber r)
tanhAct = returnLet . tanh

reluAct :: (DeltaMonad r m, Num r, Ord r) => DualNumber r -> m (DualNumber r)
reluAct (D u u') = returnLet $ D (max 0 u) (Scale (if u > 0 then 1 else 0) u')

logisticAct :: (DeltaMonad r m, Floating r) => DualNumber r -> m (DualNumber r)
logisticAct = returnLet . logistic

sumElementsVectorOfDelta :: Num r
                         => Data.Vector.Vector (DualNumber r)
                         -> DualNumber r
sumElementsVectorOfDelta = V.foldl' (+) (scalar 0)

softMaxAct :: (DeltaMonad r m, Floating r)
           => Data.Vector.Vector (DualNumber r)
           -> m (Data.Vector.Vector (DualNumber r))
softMaxAct us = do
  let expUs = V.map exp us
      sumExpUs = sumElementsVectorOfDelta expUs
  -- This has to be let-bound, because it's used many times below.
  recipSum <- returnLet $ recip sumExpUs
  V.mapM (\r -> returnLet $ r * recipSum) expUs

lossSquared :: (DeltaMonad r m, Num r) => r -> DualNumber r -> m (DualNumber r)
lossSquared targ res = returnLet $ squaredDifference targ res

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy :: forall m r. (DeltaMonad r m, Floating r, Numeric r)
                 => Vector r
                 -> Data.Vector.Vector (DualNumber r)
                 -> m (DualNumber r)
lossCrossEntropy targ res = do
  let f :: DualNumber r -> Int -> DualNumber r -> DualNumber r
      f !acc i d = acc + scale (targ V.! i) (log d)
  returnLet $ negate $ V.ifoldl' f (scalar 0) res


-- * Monadic operations for vectors

-- The monad sadly forces duplication of code.

tanhActV :: (DeltaMonad r m, Floating (Vector r))
         => DualNumber (Vector r) -> m (DualNumber (Vector r))
tanhActV = returnLetV . tanh

reluActV :: (DeltaMonad r m, Numeric r, Ord r, Num (Vector r))
         => DualNumber (Vector r) -> m (DualNumber (Vector r))
reluActV dn@(D u _) = do
  let oneIfGtZero = V.map (\x -> if x > 0 then 1 else 0) u
  returnLetV $ scale oneIfGtZero dn
    -- I have a bad feeling about this

reluLeakyActV :: ( DeltaMonad r m, Numeric r, Fractional r, Ord r
                 , Num (Vector r) )
              => DualNumber (Vector r) -> m (DualNumber (Vector r))
reluLeakyActV dn@(D u _) = do
  let oneIfGtZero = V.map (\x -> if x > 0 then 1 else 0.01) u
  returnLetV $ scale oneIfGtZero dn

logisticActV :: (DeltaMonad r m, Floating (Vector r))
             => DualNumber (Vector r)
             -> m (DualNumber (Vector r))
logisticActV = returnLetV . logistic

softMaxActV :: (DeltaMonad r m, Fractional r, Numeric r, Floating (Vector r))
            => DualNumber (Vector r)
            -> m (DualNumber (Vector r))
softMaxActV d@(D u _) = do
  let expU = exp d
      sumExpU = sumElements' expU
  -- This has to be let-bound, because it's used many times below.
  recipSum <- returnLet $ recip sumExpU
  returnLetV $ konst' recipSum (V.length u) * expU

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyV :: (DeltaMonad r m, Numeric r, Floating (Vector r))
                  => Vector r
                  -> DualNumber (Vector r)
                  -> m (DualNumber r)
lossCrossEntropyV targ res = returnLet $ negate $ log res <.>!! targ
