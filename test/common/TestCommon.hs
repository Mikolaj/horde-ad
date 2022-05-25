{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module TestCommon ((+\), (*\), (**\),
                   dReverse0, dReverse1, fX, fX1Y, fXXY, fXYplusZ, fXtoY, freluX,
                   vec_omit_scalarSum_aux, sumElementsV, altSumElementsV,
                   sinKonst, sinKonstOut, sinKonstDelay, sinKonstS, sinKonstOutS, sinKonstDelayS,
                   powKonst, powKonstOut, powKonstDelay,
                   listsToParameters,
                   qcTest, fquad, quad,
                   atanReadmeM, atanReadmeDReverse,
                   vatanReadmeM, vatanReadmeDReverse,
                  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import           Test.Tasty
import           Test.Tasty.QuickCheck

import HordeAd hiding (sumElementsVectorOfDual)
import HordeAd.Core.DualClass (IsPrimal, dAdd, dScale)

-- Unfortunately, monadic versions of the operations below are not
-- polymorphic over whether they operate on scalars, vectors or other types,
-- so we should probably abandon them.

(+\) :: DualMonad d r m
     => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(+\) u v = returnLet $ u + v

(*\) :: DualMonad d r m
     => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(*\) u v = returnLet $ u * v

(**\) :: DualMonad d r m
      => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
(**\) u v = returnLet $ u ** v

dReverse0
  :: HasDelta r
  => (DualNumberVariables 'DModeGradient r
      -> DualMonadGradient r (DualNumber 'DModeGradient r))
  -> [r]
  -> ([r], r)
dReverse0 f deltaInput =
  let ((results, _, _, _), value) =
        dReverse 1 f (V.fromList deltaInput, V.empty, V.empty, V.empty)
  in (V.toList results, value)

fX :: DualMonad 'DModeGradient Float m
   => DualNumberVariables 'DModeGradient Float
   -> m (DualNumber 'DModeGradient Float)
fX variables = do
  let x = var0 variables 0
  return x

fX1Y :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fX1Y variables = do
  let x = var0 variables 0
      y = var0 variables 1
  x1 <- x +\ 1
  x1 *\ y

fXXY :: DualMonad 'DModeGradient Float m
     => DualNumberVariables 'DModeGradient Float
     -> m (DualNumber 'DModeGradient Float)
fXXY variables = do
  let x = var0 variables 0
      y = var0 variables 1
  xy <- x *\ y
  x *\ xy

fXYplusZ :: DualMonad 'DModeGradient Float m
         => DualNumberVariables 'DModeGradient Float
         -> m (DualNumber 'DModeGradient Float)
fXYplusZ variables = do
  let x = var0 variables 0
      y = var0 variables 1
      z = var0 variables 2
  xy <- x *\ y
  xy +\ z

fXtoY :: DualMonad 'DModeGradient Float m
      => DualNumberVariables 'DModeGradient Float
      -> m (DualNumber 'DModeGradient Float)
fXtoY variables = do
  let x = var0 variables 0
      y = var0 variables 1
  x **\ y

freluX :: DualMonad 'DModeGradient Float m
       => DualNumberVariables 'DModeGradient Float
       -> m (DualNumber 'DModeGradient Float)
freluX variables = do
  let x = var0 variables 0
  reluAct x

quad :: DualMonad d r m
     => DualNumber d r -> DualNumber d r -> m (DualNumber d r)
quad x y = do
  x2 <- returnLet $ square x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ 5

fquad :: forall r d m. DualMonad d r m
      => DualNumberVariables d r -> m (DualNumber d r)
fquad variables = do
  let x = var0 variables 0
      y = var0 variables 1
  quad x y

vec_omit_scalarSum_aux
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
vec_omit_scalarSum_aux vec = returnLet $ foldlDual' (+) 0 vec

sumElementsV
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
sumElementsV variables = do
  let x = var1 variables 0
  returnLet $ sumElements0 x

altSumElementsV
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
altSumElementsV variables = do
  let x = var1 variables 0
  returnLet $ altSumElements0 x

-- hlint would complain about spurious @id@, so we need to define our own.
id2 :: a -> a
id2 x = x

sinKonst
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
sinKonst variables = do
  let x = var1 variables 0
  return $ sumElements0 $
    sin x + (id2 $ id2 $ id2 $ konst1 1 2)

sinKonstOut
  :: ( DualMonad d r m
     , Floating (Out (DualNumber d (Vector r))) )
  => DualNumberVariables d r -> m (DualNumber d r)
sinKonstOut variables = do
  let x = var1 variables 0
  return $ sumElements0 $
    unOut $ sin (Out x) + Out (id2 $ id2 $ id2 $ konst1 1 2)

sinDelayed :: (Floating a, IsPrimal d a) => DualNumber d a -> DualNumber d a
sinDelayed (D u u') = delayD (sin u) (dScale (cos u) u')

plusDelayed :: (Floating a, IsPrimal d a)
            => DualNumber d a -> DualNumber d a -> DualNumber d a
plusDelayed (D u u') (D v v') = delayD (u + v) (dAdd u' v')

sinKonstDelay
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
sinKonstDelay variables = do
  let x = var1 variables 0
  return $ sumElements0 $
    sinDelayed x `plusDelayed` (id2 $ id2 $ id2 $ konst1 1 2)

powKonst
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
powKonst variables = do
  let x = var1 variables 0
  return $ sumElements0 $
    x ** (sin x + (id2 $ id2 $ id2 $ konst1 (sumElements0 x) 2))

powKonstOut
  :: ( DualMonad d r m
     , Floating (Out (DualNumber d (Vector r))) )
  => DualNumberVariables d r -> m (DualNumber d r)
powKonstOut variables = do
  let x = var1 variables 0
  return $ sumElements0 $
    x ** unOut (sin (Out x)
                + Out (id2 $ id2 $ id2 $ konst1 (sumElements0 x) 2))

powKonstDelay
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
powKonstDelay variables = do
  let x = var1 variables 0
  return $ sumElements0 $
    x ** (sinDelayed x
          `plusDelayed` (id2 $ id2 $ id2 $ konst1 (sumElements0 x) 2))

sinKonstS
  :: forall d r m. DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
sinKonstS variables = do
  let x = varS variables 0
  return $ sumElements0 $ fromS1
    ((sin x + (id2 $ id2 $ id2 $ konstS 1))
       :: DualNumber d (OS.Array '[2] r))

sinKonstOutS
  :: forall r d m. ( DualMonad d r m
                   , Floating (Out (DualNumber d (OS.Array '[2] r))) )
  => DualNumberVariables d r -> m (DualNumber d r)
sinKonstOutS variables = do
  let x = varS variables 0
  return $ sumElements0 $ fromS1
    (unOut (sin (Out x) + Out (id2 $ id2 $ id2 $ konstS 1))
       :: DualNumber d (OS.Array '[2] r))

sinKonstDelayS
  :: forall d r m. DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
sinKonstDelayS variables = do
  let x = varS variables 0
  return $ sumElements0 $ fromS1
    ((sinDelayed x `plusDelayed` (id2 $ id2 $ id2 $ konstS 1))
       :: DualNumber d (OS.Array '[2] r))

dReverse1
  :: (r ~ Float, d ~ 'DModeGradient)
  => (DualNumberVariables d r -> DualMonadGradient r (DualNumber d r))
  -> [[r]]
  -> ([[r]], r)
dReverse1 f deltaInput =
  let ((_, results, _, _), value) =
        dReverse 1 f
          (V.empty, V.fromList (map V.fromList deltaInput), V.empty, V.empty)
  in (map V.toList $ V.toList results, value)

listsToParameters :: ([Double], [Double]) -> Domains Double
listsToParameters (a0, a1) =
  (V.fromList a0, V.singleton $ V.fromList a1, V.empty, V.empty)

listsToParameters4 :: ([Double], [Double], [Double], [Double]) -> Domains Double
listsToParameters4 (a0, a1, a2, aX) =
  ( V.fromList a0
  , V.singleton $ V.fromList a1
  , if null a2 then V.empty else V.singleton $ HM.matrix 1 a2
  , if null aX then V.empty else V.singleton $ OT.fromList [length aX] aX )

qcTest :: TestName
       -> (forall d r m. ( DualMonad d r m
                         , Floating (Out (DualNumber d (Vector r)))
                         , Floating (Out (DualNumber d (OS.Array '[2] r))) )
           => DualNumberVariables d r -> m (DualNumber d r))
       -> ((Double, Double, Double) -> ([Double], [Double], [Double], [Double]))
       -> TestTree
qcTest txt f fArg =
  quickCheckTest txt f (listsToParameters4 . fArg) ((-2, -2, -2), (2, 2, 2)) ((-1e-7, -1e-7, -1e-7), (1e-7, 1e-7, 1e-7)) (-10, 10)

-- A quick consistency check of all the kinds of derivatives and gradients
-- and all kinds of computing the value of the objective function.
quickCheckTest :: TestName
       -> (forall d r m. ( DualMonad d r m
                         , Floating (Out (DualNumber d (Vector r)))
                         , Floating (Out (DualNumber d (OS.Array '[2] r))) )
           => DualNumberVariables d r -> m (DualNumber d r))
       -> ((Double, Double, Double) -> Domains Double)
       -> ((Double, Double, Double), (Double, Double, Double))
       -> ((Double, Double, Double), (Double, Double, Double))
       -> (Double, Double)
       -> TestTree
quickCheckTest txt f fArgDom dsRange perturbationRange dtRange =
  testProperty txt
  $ forAll (choose dsRange) $ \xyz dsRaw ->
    forAll (choose perturbationRange) $ \perturbationRaw ->
    forAll (choose dtRange) $ \dt ->
      let args = fArgDom xyz
          ds = fArgDom dsRaw
          perturbation = fArgDom perturbationRaw
          ff@(derivative, ffValue) = dFastForward f args ds
          (derivativeAtPerturbation, valueAtPerturbation) =
            dFastForward f args perturbation
          close a b = abs (a - b) <= 1e-4
          (gradient, revValue) = dReverse dt f args
      in -- Two forward derivative implementations agree fully:
         dForward f args ds === ff
         -- Objective function value from gradients is the same.
         .&&. ffValue == revValue
         -- Gradients and derivatives agree.
         .&&. close (dt * derivative)
                    (dotParameters gradient ds)
         -- Objective function value is unaffected by perturbation.
         .&&. ffValue == valueAtPerturbation
         -- Derivative approximates the perturbation of value.
         .&&. close (primalValue
                                 f (addParameters
                                                  args perturbation))
                    (ffValue + derivativeAtPerturbation)

-- A function that goes from `R^3` to `R^2`, with a representation
-- of the input and the output tuple that is convenient for interfacing
-- with the library.
atanReadmeOriginal :: RealFloat a => a -> a -> a -> Data.Vector.Vector a
atanReadmeOriginal x y z =
  let w = x * sin y
  in V.fromList [atan2 z w, z * x]

-- Here we instantiate the function to dual numbers
-- and add a glue code that selects the function inputs from
-- a uniform representation of objective function parameters
-- represented as delta-variables (`DualNumberVariables`).
atanReadmeVariables
  :: IsScalar d r
  => DualNumberVariables d r -> Data.Vector.Vector (DualNumber d r)
atanReadmeVariables variables =
  let x : y : z : _ = vars variables
  in atanReadmeOriginal x y z

-- According to the paper, to handle functions with non-scalar results,
-- we dot-product them with dt which, for simplicity, we here set
-- to a record containing only ones. We could also apply the dot-product
-- automatically in the library code (though perhaps we should
-- emit a warning too, in case the user just forgot to apply
-- a loss function and that's the only reason the result is not a scalar?).
-- For now, let's perform the dot product in user code.

-- Here is the function for dot product with ones, which is just the sum
-- of elements of a vector.
sumElementsOfDualNumbers
  :: IsScalar d r
  => Data.Vector.Vector (DualNumber d r) -> DualNumber d r
sumElementsOfDualNumbers = V.foldl' (+) 0

-- Here we apply the function.
atanReadmeScalar
  :: IsScalar d r
  => DualNumberVariables d r -> DualNumber d r
atanReadmeScalar = sumElementsOfDualNumbers . atanReadmeVariables

-- Here we introduce a single delta-let binding (`returnLet`) to ensure
-- that if this code is used in a larger context and repeated,
-- no explosion of delta-expressions can happen.
-- If the code above had any repeated non-variable expressions
-- (e.g., if @w@ appeared twice) the user would need to make it monadic
-- and apply @returnLet@ already there.
atanReadmeM
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
atanReadmeM = returnLet . atanReadmeScalar

-- The underscores and empty vectors are placeholders for the vector,
-- matrix and arbitrary tensor components of the parameters tuple,
-- which we here don't use (above we construct a vector output,
-- but it's a vector of scalar parameters, not a single parameter
-- of rank 1).
atanReadmeDReverse :: HasDelta r
                   => Domain0 r -> (Domain0 r, r)
atanReadmeDReverse ds =
  let ((result, _, _, _), value) =
        dReverse 1 atanReadmeM (ds, V.empty, V.empty, V.empty)
  in (result, value)

-- And here's a version of the example that uses vector parameters
-- (quite wasteful in this case) and transforms intermediate results
-- via a primitive differentiable type of vectors instead of inside
-- vectors of primitive differentiable scalars.

vatanReadmeM
  :: DualMonad d r m
  => DualNumberVariables d r -> m (DualNumber d r)
vatanReadmeM variables = do
  let xyzVector = var1 variables 0
      [x, y, z] = map (index0 xyzVector) [0, 1, 2]
      v = seq1 $ atanReadmeOriginal x y z
  returnLet $ sumElements0 v

vatanReadmeDReverse :: HasDelta r
                    => Domain1 r -> (Domain1 r, r)
vatanReadmeDReverse dsV =
  let ((_, result, _, _), value) =
        dReverse 1 vatanReadmeM (V.empty, dsV, V.empty, V.empty)
  in (result, value)
