module TestMnistFCNNR ( testTrees ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           GHC.TypeLits (Nat, SomeNat (..), someNatVal)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.AstInterpret
import           HordeAd.Core.DualNumber
import           HordeAd.Core.Engine
import           HordeAd.Core.TensorADVal (ADValClown)
import           HordeAd.Core.Types
import           HordeAd.External.CommonRankedOps
import qualified MnistFcnnRanked2

testTrees :: [IO ()]
testTrees = [ mnistTestCase2VTA
            , mnistTestCase2VTA
            , mnistTestCase2VTI
            , mnistTestCase2VTI
            , mnistTestCase2VTO
            ]

{- moving any of these to this file removes the crash:
afcnnMnistLoss2
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => MnistData r -> MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
  -> ranked r 0
afcnnMnistLoss2 (datum, target) =
  let datum1 = tconst $ OR.fromVector [sizeMnistGlyphInt] datum
      target1 = tconst $ OR.fromVector [sizeMnistLabelInt] target
  in MnistFcnnRanked2.afcnnMnistLoss2TensorData (datum1, target1)

afcnnMnistTest2
  :: forall ranked r.
     (ranked ~ Flip OR.Array, GoodScalar r, Differentiable r)
  => MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
  -> [MnistData r]
  -> DomainsOD
  -> r
afcnnMnistTest2 _ [] _ = 0
afcnnMnistTest2 valsInit dataList testParams =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = tconst $ OR.fromVector [sizeMnistGlyphInt] glyph
            nn :: MnistFcnnRanked2.ADFcnnMnist2Parameters ranked r
               -> ranked r 1
            nn = inline MnistFcnnRanked2.afcnnMnist2 logistic softMax1 glyph1
            v = OR.toVector $ runFlip $ nn $ parseDomains valsInit testParams
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)
-}


-- | Stochastic Gradient Descent.
sgd :: forall n r a. GoodScalar r
    => (a -> Domains (ADValClown OD.Array) -> ADVal (Flip OR.Array) r n)
    -> (DomainsOD, Flip OR.Array r n)
sgd f = undefined

mnistTestCase2VTA :: forall ranked. IO ()
mnistTestCase2VTA = do
  let f :: a -> Domains (ADValClown OD.Array)
        -> ADVal (Flip OR.Array) Double 0
      f _ adinputs =
        MnistFcnnRanked2.afcnnMnistLoss2
          undefined (parseDomains undefined adinputs)
      !dd = sgd f
  return ()

mnistTestCase2VTI
  :: forall ranked. ranked ~ Flip OR.Array
  => IO ()
mnistTestCase2VTI = do
  let f :: a -> b -> ADVal ranked Double 0
      f _ _ = interpretAst undefined (undefined :: AstRanked PrimalSpan Double 0)
      !dd = sgd f
  return ()

mnistTestCase2VTO :: IO ()
mnistTestCase2VTO =
 case someNatVal 3 of
   Just (SomeNat _) -> do
    let !result = MnistFcnnRanked2.afcnnMnist2 logistic undefined undefined (undefined :: MnistFcnnRanked2.ADFcnnMnist2Parameters (AstRanked FullSpan) Double)
        g domains = (undefined (parseDomains undefined domains :: MnistFcnnRanked2.ADFcnnMnist2Parameters (AstRanked FullSpan) Double) :: AstRanked FullSpan Double 0)
        ((vars, _, _, _), _) = revProduceArtifact undefined g undefined undefined
        !gradientDomain =
          revEvalArtifact @Nat @AstRanked
                          (vars, undefined, undefined, undefined)
                          undefined Nothing
        ftest :: DomainsOD -> Double
        !ftest = MnistFcnnRanked2.afcnnMnistTest2 undefined undefined
    return ()
