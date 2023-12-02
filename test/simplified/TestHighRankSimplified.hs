{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
--{-# OPTIONS_GHC -ddump-prep -dsuppress-all #-}
{-# OPTIONS_GHC -ddump-spec #-}
module TestHighRankSimplified (testTrees) where

import Prelude hiding ((<*))

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           GHC.TypeLits (KnownNat, type (+), type (-), type (<=))
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor

import TestAdaptorSimplified
  ( assertEqualUpToEpsilon'
  , assertEqualUpToEpsilonShort
  , assertEqualUpToEpsilonShorter
  , relu1
  , rev'
  , t128
  , t16
  , t48
  )

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "3fooMap" testFooMap
  ]

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

bar :: forall a. RealFloat a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooBuild1 :: forall r n.
             ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
          => TensorOf (1 + n) r -> TensorOf (1 + n) r
fooBuild1 v =
  let r = tsum v
      tk = tkonst0N (tailShape $ tshape v)
      v' = tk $ tminimum $ tflatten v
  in tbuild1 3 $ \ix ->
       r * foo ( tk 3
               , tk 5 * r
               , r * v')
       + bar (r, tindex v [min 1 (ix + 1)])

fooMap1 :: (ADReady r, KnownNat n, RealFloat (TensorOf n r))
        => ShapeInt (1 + n) -> TensorOf 0 r -> TensorOf (1 + n) r
fooMap1 sh r =
  let v = fooBuild1 $ tkonst0N sh (r * r)
  in tmap0N (\x -> x * r + 5) v

testFooMap :: Assertion
testFooMap =
  assertEqualUpToEpsilon' 1e-4
    2.7516298
    (rev' @(OR.Array 1 Float) (fooMap1 [130]) 0.1)
