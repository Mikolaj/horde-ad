{-# LANGUAGE OverloadedLists #-}
module TestAdaptorSimplified
  ( testTrees, rev', assertEqualUpToEpsilon'
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.IntMap as IM
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.DualClass (inputConstant)

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
  ]

rev' :: forall a r n m.
        ( KnownNat n, KnownNat m, HasDelta r, ADReady r, InterpretAst r
        , a ~ OR.Array m r, ScalarOf r ~ r
        , TensorOf n r ~ OR.Array n r
        , TensorOf n (ADVal 'ADModeGradient r)
          ~ ADVal 'ADModeGradient (OR.Array n r)
        , TensorOf m (ADVal 'ADModeGradient r)
          ~ ADVal 'ADModeGradient (OR.Array m r)
        , ADReady (ADVal 'ADModeGradient r) )
     => (forall x. ADReady x => TensorOf n x -> TensorOf m x)
     -> OR.Array n r
     -> ( TensorOf m r, a )
rev' f vals =
  let value0 = f vals
      dt = inputConstant @a 1
      g inputs = f $ parseADInputs vals inputs
      (_, value1) = revOnDomainsFun dt g (toDomains vals)
  in ( value0, value1 )

assertEqualUpToEpsilon'
    :: ( AssertEqualUpToEpsilon z b
       , HasCallStack )
    => z  -- ^ error margin (i.e., the epsilon)
    -> (b, b)
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon'
    errMargin
    ( value0, value1 ) = do
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
