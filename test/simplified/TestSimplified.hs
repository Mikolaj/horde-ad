{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, OverloadedLists,
             RankNTypes, TypeFamilies #-}
module TestSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import HordeAd.Internal.SizedList

testTrees :: [TestTree]
testTrees = [ testCase "nestedSumBuild" testNestedSumBuild
            ]


nestedSumBuild :: forall r. ADReady r
               => {-AstIndex 2 Double -> -}TensorOf 1 r -> TensorOf 1 r
nestedSumBuild {-sl-} v =
  {-
 let  !_A1 = takeIndex @2 (1 :. (2 :: AstInt r) :. ZI)
      !_A2 = takeIndex @0 (1 :. (2 :: AstInt r) :. ZI)
      !_A3 = dropIndex @2 (1 :. (2 :: AstInt r) :. ZI)
      !_A4 = dropIndex @0 (1 :. (2 :: AstInt r) :. ZI)
      !_A1v = takeSized @2 (AstVarName 1 ::: AstVarName 2 ::: Z)
      !_A2v = takeSized @0 (AstVarName 1 ::: AstVarName 2 ::: Z)
      !_A3v = dropSized @2 (AstVarName 1 ::: AstVarName 2 ::: Z)
      !_A4v = dropSized @0 (AstVarName 1 ::: AstVarName 2 ::: Z)
      !_B1 = takeIndex @2 sl
      !_B2 = takeIndex @0 sl
      !_B3 = dropIndex @2 sl
      !_B4 = dropIndex @0 sl
 in -- tfromList0N [13] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
-}
-- {-
  tbuild1 13 (\ix ->
    tsum (tbuild1 4 (\ix2 ->
      flip tindex [ix2]
        (tbuild1 5 (\ _ -> tsum v)
         * tfromList
             [ tfromIntOf0 ix
             ]))))
-- -}

testPoly11
  :: r ~ Double
  => (forall x. ADReady x => TensorOf 1 x -> TensorOf 1 x) -> Int -> [r] -> [r]
  -> Assertion
testPoly11 f outSize input expected = do
  let domainsInput =
        domainsFrom0V V.empty (V.singleton (V.fromList input))
      dt = vToVec $ LA.konst 1 outSize
        -- "1" wrong due to fragility of hmatrix and tensor numeric instances
      !(_, !astValue) =
        revOnDomains dt
          (\adinputs ->
             interpretAst (IM.singleton 0
                             (AstVarR $ from1X $ at1 @1 adinputs 0))
                          (f (AstVar [length input] (AstVarName 0))))
          domainsInput
  return ()

testNestedSumBuild :: Assertion
testNestedSumBuild = do
  let sl = 1 :. (2 :: AstInt Double) :. ZI
  testPoly11 (nestedSumBuild {-sl-}) 13 [] []
