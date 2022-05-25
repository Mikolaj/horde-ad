{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module TestSingleGradient (testTrees) where

import Prelude

import qualified Data.Vector.Generic as V
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd hiding (sumElementsVectorOfDual)

import TestCommon

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

-- The formula for comparing derivative and gradient is due to @awf
-- at https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
quickCheckForwardAndBackward :: TestTree
quickCheckForwardAndBackward =
  testGroup "Simple QuickCheck of gradient vs derivative vs perturbation"
    [ quickCheckTest0 "fquad" fquad (\(x, y, _z) -> ([x, y], [], [], []))
    , quickCheckTest0 "atanReadmeM" atanReadmeM
             (\(x, y, z) -> ([x, y, z], [], [], []))
    , quickCheckTest0 "vatanReadmeM" vatanReadmeM
             (\(x, y, z) -> ([], [x, y, z], [], []))
    , quickCheckTest0 "sinKonst" sinKonst  -- powKonst NaNs immediately
             (\(x, _, z) -> ([], [x, z], [], []))
    , quickCheckTest0 "sinKonstOut" sinKonstOut
             (\(x, _, z) -> ([], [x, z], [], []))
    , quickCheckTest0 "sinKonstDelay" sinKonstDelay
             (\(x, _, z) -> ([], [x, z], [], []))
    , quickCheckTest0 "sinKonstS" sinKonstS
             (\(x, _, z) -> ([], [], [], [x, z]))
    , quickCheckTest0 "sinKonstOutS" sinKonstOutS
             (\(x, _, z) -> ([], [], [], [x, z]))
    , quickCheckTest0 "sinKonstDelayS" sinKonstDelayS
             (\(x, _, z) -> ([], [], [], [x, z]))
   ]

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
