module TestConvQuickCheck ( tensorADOnceMnistTests2 ) where

import Prelude

import Data.Bifunctor (first, second)
import Data.Proxy (Proxy (Proxy))
import System.Random
import Test.Tasty
import Test.Tasty.QuickCheck hiding (label, shuffle)


import HordeAd
import HordeAd.Core.Adaptor

import MnistData
import MnistFcnnRanked2 (XParams2)
import MnistFcnnRanked2 qualified


tensorADOnceMnistTests2 :: TestTree
tensorADOnceMnistTests2 = testGroup "Ranked2 Once MNIST tests"
  [ testProperty "VTO2 grad vs fwd" $
    \seed0 ->
    forAllShrink (chooseInt (0, 600)) shrinkIntegral $ \width1Hidden ->
    forAllShrink (chooseInt (0, 200)) shrinkIntegral $ \width1Hidden2 ->
    forAllShrink (chooseInt (0, 5)) shrinkIntegral $ \simp ->
    forAll (choose (0.01, 1)) $ \range ->
    forAll (choose (0.01, 1)) $ \range2 ->
    forAll (choose (0.5, 1.5)) $ \dt ->
    withSNat (1 + width1Hidden) $ \(SNat @widthHidden) ->
    withSNat (1 + width1Hidden2) $ \(SNat @widthHidden2) ->
    let (glyph0, seed2) = randomValue @(Concrete (TKS '[SizeMnistGlyph] Double))
                                      0.5 (mkStdGen seed0)
        (label0, seed3) = randomValue @(Concrete (TKS '[SizeMnistLabel] Double))
                                      5 seed2
        (glyph, label) = ( rmap1 (rscalar 0.5 +) $ forgetShape glyph0
                         , rmap1 (rscalar 5 + ) $ forgetShape label0 )
        ds :: Concrete (XParams2 Double Double)
        (ds, seed4) = first forgetShape $
          randomValue
            @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                             Concrete widthHidden widthHidden2 Double Double)))
            range seed3
        (targetInit, artRaw) =
          MnistFcnnRanked2.mnistTrainBench2VTOGradient
            @Double (Proxy @Double) UseIncomingCotangent
            range2 seed4 (1 + width1Hidden) (1 + width1Hidden2)
        art = iterate simplifyArtifactRev artRaw !! simp
        parametersAndInput = tpair targetInit (tpair glyph label)
        (value1, _gradient1) = second tproject1 $
          revInterpretArtifact art parametersAndInput (Just $ kconcrete dt)
        f :: ADVal Concrete (XParams2 Double Double)
          -> ADVal Concrete (TKScalar Double)
        f adinputs =
          MnistFcnnRanked2.afcnnMnistLoss2
            (rfromPrimal glyph, rfromPrimal label) (fromTarget adinputs)
        (value2, _derivative2) = cjvp2 f targetInit ds
    in
      conjoin
        [ counterexample
            ("Objective function value from grad and jvp matches: "
             ++ show (value1, value2, value1 - value2))
            (abs (value1 - value2) < 1e-10)

        ]
  ]