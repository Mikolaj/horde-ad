{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module TestSingleGradient (testTrees, fquad, quad) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Test.Tasty.QuickCheck

import HordeAd hiding (sumElementsVectorOfDual)
import HordeAd.Core.DualClass (IsPrimal, dAdd, dScale)

testTrees :: [TestTree]
testTrees = [ testDReverse0
            , testDReverse1
            , testPrintDf
            , testDForward
            , testDFastForward
            , quickCheckForwardAndBackward
            , readmeTests
            , readmeTestsV
            ]

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

testDReverse0 :: TestTree
testDReverse0 = testGroup "Simple dReverse application tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ dReverse0 f v @?= expected)
    [ ("fX", fX, [99], ([1.0],99.0))
    , ("fX1Y", fX1Y, [3, 2], ([2.0,4.0],8.0))
    , ("fXXY", fXXY, [3, 2], ([12.0,9.0],18.0))
    , ("fXYplusZ", fXYplusZ, [1, 2, 3], ([2.0,1.0,1.0],5.0))
    , ( "fXtoY", fXtoY, [0.00000000000001, 2]
      , ([2.0e-14,-3.2236188e-27],9.9999994e-29) )
    , ("fXtoY2", fXtoY, [1, 2], ([2.0,0.0],1.0))
    , ("freluX", freluX, [-1], ([0.0],0.0))
    , ("freluX2", freluX, [0], ([0.0],0.0))
    , ("freluX3", freluX, [0.0001], ([1.0],1.0e-4))
    , ("freluX4", freluX, [99], ([1.0],99.0))
    , ("fquad", fquad, [2, 3], ([4.0,6.0],18.0))
    , ("scalarSum", vec_omit_scalarSum_aux, [1, 1, 3], ([1.0,1.0,1.0],5.0))
    ]

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

testDReverse1 :: TestTree
testDReverse1 = testGroup "Simple dReverse application to vectors tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ dReverse1 f v @?= expected)
    [ ("sumElementsV", sumElementsV, [[1, 1, 3]], ([[1.0,1.0,1.0]],5.0))
    , ("altSumElementsV", altSumElementsV, [[1, 1, 3]], ([[1.0,1.0,1.0]],5.0))
    , ( "sinKonst", sinKonst, [[1, 3]]
      , ([[0.5403023,-0.9899925]],2.982591) )
    , ( "sinKonstOut", sinKonstOut, [[1, 3]]
      , ([[0.5403023,-0.9899925]],2.982591) )
    , ( "sinKonstDelay", sinKonstDelay, [[1, 3]]
      , ([[0.5403023,-0.9899925]],2.982591) )
    , ( "powKonst", powKonst, [[1, 3]]
      , ([[108.7523,131.60072]],95.58371) )
    , ( "powKonstOut", powKonstOut, [[1, 3]]
      , ([[108.7523,131.60072]],95.58371) )
    , ( "powKonstDelay", powKonstDelay, [[1, 3]]
      , ([[108.7523,131.60072]],95.58371) )
    ]

testPrintDf :: TestTree
testPrintDf = testGroup "Pretty printing test" $
  map (\(txt, f, v, expected) ->
        testCase txt $ prettyPrintDf False f
          (V.empty, V.fromList (map V.fromList v), V.empty, V.empty)
        @?= expected)
    [ ( "sumElementsV", sumElementsV, [[1 :: Float, 1, 3]]
      , unlines
        [ "let0 DeltaId_0 = SumElements0 (Var1 (DeltaId 0)) 3"
        , "in Var0 (DeltaId 0)" ] )
    , ( "altSumElementsV", altSumElementsV, [[1, 1, 3]]
      , unlines
        [ "let0 DeltaId_0 = Add0"
        , "  (Index0 (Var1 (DeltaId 0)) 2 3)"
        , "  (Add0"
        , "     (Index0 (Var1 (DeltaId 0)) 1 3)"
        , "     (Add0 (Index0 (Var1 (DeltaId 0)) 0 3) Zero0))"
        , "in Var0 (DeltaId 0)" ] )
    , ( "sinKonst", sinKonst, [[1, 3]]
      , unlines
        [ "in SumElements0"
        , "  (Add1"
        , "     (Scale1 [ 0.5403023 , -0.9899925 ] (Var1 (DeltaId 0)))"
        , "     (Konst1 Zero0 2))"
        , "  2" ] )
    , ( "sinKonstOut", sinKonstOut, [[1, 3]]
      , unlines
        [ "in SumElements0"
        , "  (Outline1"
        , "     PlusOut"
        , "     [ [ 0.84147096 , 0.14112 ] , [ 1.0 , 1.0 ] ]"
        , "     [ Outline1 SinOut [ [ 1.0 , 3.0 ] ] [ Var1 (DeltaId 0) ]"
        , "     , Konst1 Zero0 2"
        , "     ])"
        , "  2" ] )
    , ( "powKonst", powKonst, [[1, 3]]
      , unlines
        [ "in SumElements0"
        , "  (Add1"
        , "     (Scale1 [ 4.8414707 , 130.56084 ] (Var1 (DeltaId 0)))"
        , "     (Scale1"
        , "        [ 0.0 , 103.91083 ]"
        , "        (Add1"
        , "           (Scale1 [ 0.5403023 , -0.9899925 ] (Var1 (DeltaId 0)))"
        , "           (Konst1 (SumElements0 (Var1 (DeltaId 0)) 2) 2))))"
        , "  2" ] )
    , ( "powKonstOut", powKonstOut, [[1, 3]]
      , unlines
        [ "in SumElements0"
        , "  (Add1"
        , "     (Scale1 [ 4.8414707 , 130.56084 ] (Var1 (DeltaId 0)))"
        , "     (Scale1"
        , "        [ 0.0 , 103.91083 ]"
        , "        (Outline1"
        , "           PlusOut"
        , "           [ [ 0.84147096 , 0.14112 ] , [ 4.0 , 4.0 ] ]"
        , "           [ Outline1 SinOut [ [ 1.0 , 3.0 ] ] [ Var1 (DeltaId 0) ]"
        , "           , Konst1 (SumElements0 (Var1 (DeltaId 0)) 2) 2"
        , "           ])))"
        , "  2" ] )
    ]

testDForward :: TestTree
testDForward =
 testGroup "Simple dForward application tests" $
  map (\(txt, f, v, expected) ->
        let vp = listsToParameters v
        in testCase txt $ dForward f vp vp @?= expected)
    [ ("fquad", fquad, ([2 :: Double, 3], []), (26.0, 18.0))
    , ( "atanReadmeM", atanReadmeM, ([1.1, 2.2, 3.3], [])
      , (7.662345305800865, 4.9375516951604155) )
    , ( "vatanReadmeM", vatanReadmeM, ([], [1.1, 2.2, 3.3])
      , (7.662345305800865, 4.9375516951604155) )
    ]

listsToParameters :: ([Double], [Double]) -> Domains Double
listsToParameters (a0, a1) =
  (V.fromList a0, V.singleton $ V.fromList a1, V.empty, V.empty)

listsToParameters4 :: ([Double], [Double], [Double], [Double]) -> Domains Double
listsToParameters4 (a0, a1, a2, aX) =
  ( V.fromList a0
  , V.singleton $ V.fromList a1
  , if null a2 then V.empty else V.singleton $ HM.matrix 1 a2
  , if null aX then V.empty else V.singleton $ OT.fromList [length aX] aX )

testDFastForward :: TestTree
testDFastForward =
 testGroup "Simple dFastForward application tests" $
  map (\(txt, f, v, expected) ->
        let vp = listsToParameters v
        in testCase txt $ dFastForward f vp vp @?= expected)
    [ ("fquad", fquad, ([2 :: Double, 3], []), (26.0, 18.0))
    , ( "atanReadmeM", atanReadmeM, ([1.1, 2.2, 3.3], [])
      , (7.662345305800865, 4.9375516951604155) )
    , ( "vatanReadmeM", vatanReadmeM, ([], [1.1, 2.2, 3.3])
      , (7.662345305800865, 4.9375516951604155) )
    ]

qcTest :: TestName
       -> (forall d r m. ( DualMonad d r m
                         , Floating (Out (DualNumber d (Vector r)))
                         , Floating (Out (DualNumber d (OS.Array '[2] r))) )
           => DualNumberVariables d r -> m (DualNumber d r))
       -> ((Double, Double, Double) -> ([Double], [Double], [Double], [Double]))
       -> TestTree
qcTest txt f fArg =
  testProperty txt
  $ forAll (choose ((-2, -2, -2), (2, 2, 2))) $ \xyz dsRaw ->
    forAll (choose ( (-1e-7, -1e-7, -1e-7)
                   , (1e-7, 1e-7, 1e-7) )) $ \perturbationRaw ->
    forAll (choose (-10, 10)) $ \dt ->
      let args = listsToParameters4 $ fArg xyz
          ds = listsToParameters4 $ fArg dsRaw
          perturbation = listsToParameters4 $ fArg perturbationRaw
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

-- The formula for comparing derivative and gradient is due to @awf
-- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
quickCheckForwardAndBackward :: TestTree
quickCheckForwardAndBackward =
  testGroup "Simple QuickCheck of gradient vs derivative vs perturbation"
    [ qcTest "fquad" fquad (\(x, y, _z) -> ([x, y], [], [], []))
    , qcTest "atanReadmeM" atanReadmeM
             (\(x, y, z) -> ([x, y, z], [], [], []))
    , qcTest "vatanReadmeM" vatanReadmeM
             (\(x, y, z) -> ([], [x, y, z], [], []))
    , qcTest "sinKonst" sinKonst  -- powKonst NaNs immediately
             (\(x, _, z) -> ([], [x, z], [], []))
    , qcTest "sinKonstOut" sinKonstOut
             (\(x, _, z) -> ([], [x, z], [], []))
    , qcTest "sinKonstDelay" sinKonstDelay
             (\(x, _, z) -> ([], [x, z], [], []))
    , qcTest "sinKonstS" sinKonstS
             (\(x, _, z) -> ([], [], [], [x, z]))
    , qcTest "sinKonstOutS" sinKonstOutS
             (\(x, _, z) -> ([], [], [], [x, z]))
    , qcTest "sinKonstDelayS" sinKonstDelayS
             (\(x, _, z) -> ([], [], [], [x, z]))
   ]

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

readmeTests :: TestTree
readmeTests = testGroup "Simple tests for README"
  [ testCase " Float (1.1, 2.2, 3.3)"
    $ atanReadmeDReverse (V.fromList [1.1 :: Float, 2.2, 3.3])
      @?= (V.fromList [3.0715904, 0.18288425, 1.1761366], 4.937552)
  , testCase " Double (1.1, 2.2, 3.3)"
    $ atanReadmeDReverse (V.fromList [1.1 :: Double, 2.2, 3.3])
      @?= ( V.fromList [ 3.071590389300859
                       , 0.18288422990948425
                       , 1.1761365368997136 ]
          , 4.9375516951604155 )
  ]

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

readmeTestsV :: TestTree
readmeTestsV = testGroup "Simple tests of vector-based code for README"
  [ testCase "V Float (1.1, 2.2, 3.3)"
    $ vatanReadmeDReverse (V.singleton $ V.fromList [1.1 :: Float, 2.2, 3.3])
      @?= ( V.singleton $ V.fromList [3.0715904, 0.18288425, 1.1761366]
          , 4.937552 )
  , testCase "V Double (1.1, 2.2, 3.3)"
    $ vatanReadmeDReverse (V.singleton $ V.fromList [1.1 :: Double, 2.2, 3.3])
      @?= ( V.singleton $ V.fromList [ 3.071590389300859
                                     , 0.18288422990948425
                                     , 1.1761365368997136 ]
          , 4.9375516951604155 )
  ]
