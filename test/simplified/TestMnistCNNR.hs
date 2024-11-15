{-# LANGUAGE OverloadedLists #-}
module TestMnistCNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import Data.IntMap.Strict qualified as IM
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import Numeric.LinearAlgebra (Numeric)
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Text.Printf

import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.TensorAst
import HordeAd.External.OptimizerTools
import HordeAd.Internal.BackendOX (RepN (..))
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))

import EqEpsilon

import MnistCnnRanked2 qualified
import MnistData

testTrees :: [TestTree]
testTrees = [testCase "CNNOPP" testCNNOPP]

testCNNOPP :: Assertion
testCNNOPP = do
  let blackGlyph :: AstTensor AstMethodLet FullSpan (TKR Double 4)
      blackGlyph = AstFromPrimal $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @1)
                   $ AstReplicate (SNat @2)
                   $ AstReplicate (SNat @2)
                       (AstConcrete (Nested.rscalar 7) :: AstTensor AstMethodLet PrimalSpan (TKR Double 0))
      afcnn2T :: AstTensor AstMethodLet FullSpan (TKR Double 4)
      afcnn2T = maxPool2dUnpadded2 $ conv2dUnpadded2 blackGlyph
  printAstPretty IM.empty afcnn2T
    @?= ""

maxPool2dUnpadded2
  :: (ADReady target, GoodScalar r)
  => target (TKR r 4) -> target (TKR r 4)
maxPool2dUnpadded2 arr =
  rbuild [1, 1, 1, 1] $ \case
    [_, _, iBh, iBw] ->
      let arrt = slicez2 [1, 1, 2, 2] arr [1, 1, 2 * iBh, 2 * iBw]
      in rmaximum2 arrt
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"

conv2dUnpadded2
  :: (ADReady target, GoodScalar r)
  => target (TKR r 4) -> target (TKR r 4)
conv2dUnpadded2 arrA =
  let shB = [1, 1, 2, 2]
  in rbuild shB $ \case
    [iImg, _, iBh, iBw] ->
      let arrAt = slicez2 shB arrA [iImg, 0, iBh, iBw]
      in rindex0 arrAt [0, 0, 0, 0]
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

slicez2
  :: (ADReady target, GoodScalar r, KnownNat n)
  => IShR n -> target (TKR r n) -> IndexOf target n -> target (TKR r n)
slicez2 shOut d ixBase =
  rbuild shOut $ \ixResult -> indexz02 d (zipWith_Index (+) ixBase ixResult)

indexz02
  :: forall target r n. (ADReady target, GoodScalar r, KnownNat n)
  => target (TKR r n) -> IndexOf target n -> target (TKR r 0)
indexz02 d ix = ifF (within0 @target (rshape @target d) ix) (d ! ix) (rscalar 0)

rmaximum2 :: ( BaseTensor target, BaseTensor (PrimalOf target)
            , LetTensor target, KnownNat n, GoodScalar r )
         => target (TKR r n) -> target (TKR r 0)
rmaximum2 t0 = tlet t0 $ \t -> rindex0 t [0, 0, 0, 0]
