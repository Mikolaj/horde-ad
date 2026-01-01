{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Tests.Permutation where

import Data.Type.Equality

import Data.Array.Nested.Permutation

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.Hedgehog

-- import Debug.Trace

import Gen


tests :: TestTree
tests = testGroup "Permutation"
  [testProperty "permCheckPermutation" $ property $ do
    n <- forAll $ Gen.int (Range.linear 0 10)
    list <- forAll $ genPermR n
    let r = permFromListCont list $ \perm ->
              permCheckPermutation perm ()
    case r of
      Just () -> return ()
      Nothing -> failure
  ,testProperty "permInverse" $ property $
    genRank $ \n ->
    genPerm n $ \perm ->
    genStaticShX n $ \ssh ->
    permInverse perm $ \_invperm proof ->
      case proof ssh of
        Refl -> return ()
  ]
