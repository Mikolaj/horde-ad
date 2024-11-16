{-# LANGUAGE OverloadedLists #-}
module TestMnistCNNR
  ( testTrees
  ) where

import Prelude

import Data.IntMap.Strict qualified as IM
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested

import HordeAd.Core.Ast
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.TensorAst ()
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.SizedList

testTrees :: [TestTree]
testTrees = [testCase "CNNOPP" testCNNOPP]

testCNNOPP :: Assertion
testCNNOPP = printAstPretty IM.empty maxPool2dUnpadded @?= ""

maxPool2dUnpadded
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
  => target (TKR r 4)
maxPool2dUnpadded =
  rbuild [1, 1, 1, 1] $ \case
    [_, _, iBh, iBw] ->
      let arrt = slicez conv2dUnpadded [1, 1, 2 * iBh, 2 * iBw]
      in rmaximum arrt
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"

conv2dUnpadded
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
  => target (TKR r 4)
conv2dUnpadded =
  rbuild [1, 1, 2, 2] $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez
                    (rconcrete
                     $ Nested.rreplicateScal (1 :$: 1 :$: 2 :$: 2 :$: ZSR) 1)
                    [iImg, 0, iBh, iBw]
      in rindex0 arrAt [0, 0, 0, 0]
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

slicez
  :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double, n ~ 4)
  => target (TKR r n) -> IndexOf target n -> target (TKR r n)
slicez d ixBase =
  rbuild [1, 1, 2, 2] $ \ixResult -> indexz0 d (zipWith_Index (+) ixBase ixResult)

indexz0
  :: forall target r n.
     (target ~ AstTensor AstMethodLet FullSpan, r ~ Double, n ~ 4)
  => target (TKR r n) -> IndexOf target n -> target (TKR r 0)
indexz0 d ix = ifF (1 >. (indexToList ix !! 0)) (d ! ix) (rscalar 0)

rmaximum :: (target ~ AstTensor AstMethodLet FullSpan, r ~ Double)
         => target (TKR r 4) -> target (TKR r 0)
rmaximum t0 = tlet t0 $ \t -> rindex0 t [0, 0, 0, 0]
