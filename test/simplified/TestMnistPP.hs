{-# LANGUAGE OverloadedLists #-}
-- | Tests of MNIST nns that pretty-print resulting gradient and primal terms.
module TestMnistPP
  ( testTrees
  ) where

import Prelude

import GHC.Exts (IsList (..))
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Ranked.Shape

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.Ops (treplicate)

import MnistCnnRanked2 qualified
import MnistCnnShaped2 qualified
import MnistData
import MnistFcnnRanked1 qualified
import MnistFcnnRanked2 (XParams2)
import MnistFcnnRanked2 qualified
import MnistRnnRanked2 (ADRnnMnistParameters)
import MnistRnnRanked2 qualified

testTrees :: [TestTree]
testTrees = [ tensorMnistPPFCNNR
            , tensorMnistPPRNNR
            , tensorMnistCNNRPP
            ]

-- * FCNNR tests

type XParams widthHidden widthHidden2 r =
  X (MnistFcnnRanked1.ADFcnnMnist1Parameters
       Concrete widthHidden widthHidden2 r)

tensorMnistPPFCNNR :: TestTree
tensorMnistPPFCNNR = testGroup "PP and Ast tests for Short Ranked MNIST"
  [ testCase "VTO1 PP Lin" testVTOPP
  , testCase "VTO1 Ast Lin" testVTOAst
  , testCase "VTO1 PP NonLin" testVTOPPNonLin
  , testCase "VTO1 Ast NonLin" testVTOAstNonLin
  , testCase "VTO2 PP Lin" testVT2OPP
  , testCase "VTO2 Ast Lin" testVT2OAst
  , testCase "VTO2 PP NonLin" testVT2OPPNonLin
  , testCase "VTO2 PP NonLin2" testVT2OPPNonLin2
  , testCase "VTO2 Ast NonLin2" testVT2OAstNonLin2
  , testCase "VTO2 PP NonLin3" testVT2OPPNonLin3
  , testCase "VTO2 Ast NonLin3" testVT2OAstNonLin3
  ]

valsInitVTOPP :: (Num r, Enum r, Nested.PrimElt r)
              => MnistFcnnRanked1.ADFcnnMnist1Parameters Concrete 3 4 r
valsInitVTOPP =
  ( ( fromList (replicate 3 (Concrete
                             $ Nested.sfromListPrim
                                 (SNat @SizeMnistGlyph)
                                 [1 .. fromIntegral sizeMnistGlyphInt]))
    , Concrete $ Nested.sfromListPrim (SNat @3) [1, 2, 3] )
  , ( fromList (replicate 4 (Concrete $ Nested.sfromListPrim
                                          (SNat @3) [1, 2, 3]))
    , Concrete $ Nested.sfromListPrim (SNat @4) [1, 2, 3, 4] )
  , ( fromList (replicate sizeMnistLabelInt
                          (Concrete $ Nested.sfromListPrim
                                        (SNat @4) [1, 2, 3, 4]))
    , Concrete $ Nested.sfromListPrim (SNat @SizeMnistLabel)
                                      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] ) )

testVTOPP :: Assertion
testVTOPP = do
  resetVarCounter
  let blackGlyph = treplicate (SNat @SizeMnistGlyph) knownSTK
                   $ fromPrimal $ rconcrete $ Nested.rscalar 7
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                   (AstTensor AstMethodLet FullSpan) 3 4 Float
              -> AstTensor AstMethodLet FullSpan (TKR 1 Float)
      afcnn2T =
        MnistFcnnRanked1.afcnnMnist1 id id
                                     (SNat @3) (SNat @4) (sfromR blackGlyph)
      ftk = tftk @Concrete (knownSTK @(XParams 3 4 Float))
                           (toTarget @Concrete valsInitVTOPP)
      artifactRev = revArtifactAdapt UseIncomingCotangent afcnn2T ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v5, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v5]) + tproject2 (tproject2 v1))"
  printArtifactPrimalPretty artifactRev
    @?= "\\v1 -> let v4 = sfromVector (fromList [ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject1 (tproject1 (tproject1 v1)))), ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) in rfromS (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v5), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v5)]) + tproject2 (tproject2 v1))"
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject1 (tproject1 (tproject1 v1)))), ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate @4 (sfromR dret !$ [9]) ; v8 = sreplicate @4 (sfromR dret !$ [8]) ; v9 = sreplicate @4 (sfromR dret !$ [7]) ; v10 = sreplicate @4 (sfromR dret !$ [6]) ; v11 = sreplicate @4 (sfromR dret !$ [5]) ; v12 = sreplicate @4 (sfromR dret !$ [4]) ; v13 = sreplicate @4 (sfromR dret !$ [3]) ; v14 = sreplicate @4 (sfromR dret !$ [2]) ; v15 = sreplicate @4 (sfromR dret !$ [1]) ; v16 = sreplicate @4 (sfromR dret !$ [0]) ; v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7)))))))) ; v18 = sreplicate @3 (v17 !$ [3]) ; v19 = sreplicate @3 (v17 !$ [2]) ; v20 = sreplicate @3 (v17 !$ [1]) ; v21 = sreplicate @3 (v17 !$ [0]) ; v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)) in tpair (tpair (tpair (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v22 !$ [0])) (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v22 !$ [1])) (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v22 !$ [2])) Z1))) v22) (tpair (tpair (v4 * v21) (tpair (v4 * v20) (tpair (v4 * v19) (tpair (v4 * v18) Z1)))) v17)) (tpair (tpair (v5 * v16) (tpair (v5 * v15) (tpair (v5 * v14) (tpair (v5 * v13) (tpair (v5 * v12) (tpair (v5 * v11) (tpair (v5 * v10) (tpair (v5 * v9) (tpair (v5 * v8) (tpair (v5 * v7) Z1)))))))))) (sfromR dret))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) ; x7 = sfromR dret !$ [9] ; x8 = sfromR dret !$ [8] ; x9 = sfromR dret !$ [7] ; x10 = sfromR dret !$ [6] ; x11 = sfromR dret !$ [5] ; x12 = sfromR dret !$ [4] ; x13 = sfromR dret !$ [3] ; x14 = sfromR dret !$ [2] ; x15 = sfromR dret !$ [1] ; x16 = sfromR dret !$ [0] ; v17 = tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x7)))))))) ; x18 = v17 !$ [3] ; x19 = v17 !$ [2] ; x20 = v17 !$ [1] ; x21 = v17 !$ [0] ; v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x18)) in tpair (tpair (tpair (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v22 !$ [0])) (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v22 !$ [1])) (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v22 !$ [2])) Z1))) v22) (tpair (tpair (v4 * sreplicate @3 x21) (tpair (v4 * sreplicate @3 x20) (tpair (v4 * sreplicate @3 x19) (tpair (v4 * sreplicate @3 x18) Z1)))) v17)) (tpair (tpair (v5 * sreplicate @4 x16) (tpair (v5 * sreplicate @4 x15) (tpair (v5 * sreplicate @4 x14) (tpair (v5 * sreplicate @4 x13) (tpair (v5 * sreplicate @4 x12) (tpair (v5 * sreplicate @4 x11) (tpair (v5 * sreplicate @4 x10) (tpair (v5 * sreplicate @4 x9) (tpair (v5 * sreplicate @4 x8) (tpair (v5 * sreplicate @4 x7) Z1)))))))))) (sfromR dret))"

testVTOAst :: Assertion
testVTOAst = do
  let ftk = tftk @Concrete (knownSTK @(XParams 3 4 Float))
                 (toTarget @Concrete valsInitVTOPP)
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan (XParams 3 4 Float)
      var = AstVar varName
      vals = toTarget @Concrete valsInitVTOPP
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @SizeMnistGlyph) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => MnistFcnnRanked1.ADFcnnMnist1Parameters f 3 4 Float
             -> f (TKR 1 Float)
      afcnn2 = MnistFcnnRanked1.afcnnMnist1
                 id id (SNat @3) (SNat @4)
                 (sfromR $ rconcrete $ unConcrete blackGlyph)
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 valsInitVTOPP
  interpretAstFull @Concrete env
                   (simplifyInline @(TKR 1 Float) afcnn1)
    @?= afcnn2 valsInitVTOPP
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 1 Float) afcnn1)
    @?= afcnn2 valsInitVTOPP

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let blackGlyph = treplicate (SNat @SizeMnistGlyph) knownSTK
                   $ fromPrimal $ rconcrete $ Nested.rscalar 7
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                         (AstTensor AstMethodLet FullSpan) 3 4 Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logisticS softMax1S
                                     (SNat @3) (SNat @4) (sfromR blackGlyph)
      ftk = tftk @Concrete (knownSTK @(XParams 3 4 Double))
                           (toTarget @Concrete valsInitVTOPP)
      artifactRevnonLin =
        revArtifactAdapt UseIncomingCotangent afcnn2TnonLin ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\v1 -> rfromS (let v15 = scast (recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1)))))) ; v19 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v15, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v15]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v22 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v19, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v19]) + tproject2 (tproject2 v1)) in sreplicate @10 (recip (ssum0 v22)) * v22)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\v1 -> let v9 = sfromVector (fromList [ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject1 (tproject1 (tproject1 v1)))), ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = sconcrete (sreplicate [3] 1.0) + v10 ; v12 = recip v11 ; v15 = scast v12 ; v16 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v15), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v15)])) + tproject2 (tproject2 (tproject1 v1)) ; v17 = exp (negate v16) ; v18 = sconcrete (sreplicate [4] 1.0) + v17 ; v19 = recip v18 ; v22 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v19), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v19)]) + tproject2 (tproject2 v1)) ; x23 = ssum @10 v22 ; v24 = sreplicate @10 (recip x23) in rfromS (v24 * v22)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret v1 -> let v9 = sfromVector (fromList [ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject1 (tproject1 (tproject1 v1)))), ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), ssum @784 (sconcrete (sreplicate [784] 7.0) * tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = sconcrete (sreplicate [3] 1.0) + v10 ; v12 = recip v11 ; v13 = sconcrete (sreplicate [3] 1.0) + negate v12 ; v14 = v12 * v13 ; v15 = scast v12 ; v16 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v15), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v15)])) + tproject2 (tproject2 (tproject1 v1)) ; v17 = exp (negate v16) ; v18 = sconcrete (sreplicate [4] 1.0) + v17 ; v19 = recip v18 ; v20 = sconcrete (sreplicate [4] 1.0) + negate v19 ; v21 = v19 * v20 ; v22 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v19), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v19)]) + tproject2 (tproject2 v1)) ; x23 = ssum @10 v22 ; v24 = sreplicate @10 (recip x23) ; v26 = v22 * (sreplicate @10 (negate (recip (x23 * x23)) * ssum @10 (v22 * sfromR dret)) + v24 * sfromR dret) ; v27 = sreplicate @4 (v26 !$ [9]) ; v28 = sreplicate @4 (v26 !$ [8]) ; v29 = sreplicate @4 (v26 !$ [7]) ; v30 = sreplicate @4 (v26 !$ [6]) ; v31 = sreplicate @4 (v26 !$ [5]) ; v32 = sreplicate @4 (v26 !$ [4]) ; v33 = sreplicate @4 (v26 !$ [3]) ; v34 = sreplicate @4 (v26 !$ [2]) ; v35 = sreplicate @4 (v26 !$ [1]) ; v36 = sreplicate @4 (v26 !$ [0]) ; v37 = v21 * (tproject1 (tproject1 (tproject2 v1)) * v36 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v35 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v29 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v28 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v27))))))))) ; v38 = scast v37 ; v39 = sreplicate @3 (v38 !$ [3]) ; v40 = sreplicate @3 (v38 !$ [2]) ; v41 = sreplicate @3 (v38 !$ [1]) ; v42 = sreplicate @3 (v38 !$ [0]) ; v43 = v14 * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v42 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v41 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v40 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v39))) in tpair (tpair (tpair (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v43 !$ [0])) (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v43 !$ [1])) (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v43 !$ [2])) Z1))) v43) (tpair (tpair (v15 * v42) (tpair (v15 * v41) (tpair (v15 * v40) (tpair (v15 * v39) Z1)))) v37)) (tpair (tpair (v19 * v36) (tpair (v19 * v35) (tpair (v19 * v34) (tpair (v19 * v33) (tpair (v19 * v32) (tpair (v19 * v31) (tpair (v19 * v30) (tpair (v19 * v29) (tpair (v19 * v28) (tpair (v19 * v27) Z1)))))))))) v26)"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret v1 -> let v12 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1))))) ; v15 = scast v12 ; v19 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v15, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v15]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v22 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v19, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v19]) + tproject2 (tproject2 v1)) ; x23 = ssum0 v22 ; v26 = v22 * (sreplicate @10 (negate (recip (x23 * x23)) * sdot0 v22 (sfromR dret)) + sreplicate @10 (recip x23) * sfromR dret) ; x27 = v26 !$ [9] ; x28 = v26 !$ [8] ; x29 = v26 !$ [7] ; x30 = v26 !$ [6] ; x31 = v26 !$ [5] ; x32 = v26 !$ [4] ; x33 = v26 !$ [3] ; x34 = v26 !$ [2] ; x35 = v26 !$ [1] ; x36 = v26 !$ [0] ; v37 = (v19 * (sconcrete (sreplicate [4] 1.0) + negate v19)) * (tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x36 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x35 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x29 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x28 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x27))))))))) ; v38 = scast v37 ; x39 = v38 !$ [3] ; x40 = v38 !$ [2] ; x41 = v38 !$ [1] ; x42 = v38 !$ [0] ; v43 = (v12 * (sconcrete (sreplicate [3] 1.0) + negate v12)) * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x42 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x41 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x40 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x39))) in tpair (tpair (tpair (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v43 !$ [0])) (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v43 !$ [1])) (tpair (sconcrete (sreplicate [784] 7.0) * sreplicate @784 (v43 !$ [2])) Z1))) v43) (tpair (tpair (v15 * sreplicate @3 x42) (tpair (v15 * sreplicate @3 x41) (tpair (v15 * sreplicate @3 x40) (tpair (v15 * sreplicate @3 x39) Z1)))) v37)) (tpair (tpair (v19 * sreplicate @4 x36) (tpair (v19 * sreplicate @4 x35) (tpair (v19 * sreplicate @4 x34) (tpair (v19 * sreplicate @4 x33) (tpair (v19 * sreplicate @4 x32) (tpair (v19 * sreplicate @4 x31) (tpair (v19 * sreplicate @4 x30) (tpair (v19 * sreplicate @4 x29) (tpair (v19 * sreplicate @4 x28) (tpair (v19 * sreplicate @4 x27) Z1)))))))))) v26)"

testVTOAstNonLin :: Assertion
testVTOAstNonLin = do
  let ftk = tftk @Concrete (knownSTK @(XParams 3 4 Double))
                 (toTarget @Concrete valsInitVTOPP)
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan (XParams 3 4 Double)
      var = AstVar varName
      vals = toTarget @Concrete valsInitVTOPP
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @SizeMnistGlyph) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => MnistFcnnRanked1.ADFcnnMnist1Parameters f 3 4 Double
             -> f (TKR 1 Double)
      afcnn2 = MnistFcnnRanked1.afcnnMnist1
                 logisticS softMax1S (SNat @3) (SNat @4)
                 (sfromR $ rconcrete $ unConcrete blackGlyph)
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 valsInitVTOPP
  interpretAstFull @Concrete env
                   (simplifyInline @(TKR 1 Double) afcnn1)
    @?= afcnn2 valsInitVTOPP
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 1 Double) afcnn1)
    @?= afcnn2 valsInitVTOPP

valsInitVT2OPP :: MnistFcnnRanked2.ADFcnnMnist2Parameters Concrete Double Float
valsInitVT2OPP =
  ( ( Concrete $ Nested.rfromListPrimLinear [4, 3]
               (concat $ replicate 4 [1, 2, 3])
    , Concrete $ Nested.rfromListPrimLinear [4] [1, 2, 3, 4] )
  , ( Concrete $ Nested.rfromListPrimLinear [5, 4]
               (concat $ replicate 5 [1, 2, 3, 4])
    , Concrete $ Nested.rfromListPrimLinear [5] [1, 2, 3, 4, 5] )
  , ( Concrete $ Nested.rfromListPrimLinear [2, 5]
               (concat $ replicate 2 [1, 2, 3, 4, 5])
    , Concrete $ Nested.rfromListPrimLinear [2] [1, 2] ) )

testVT2OPP :: Assertion
testVT2OPP = do
  resetVarCounter
  let blackGlyph = treplicate (SNat @3) knownSTK
                   $ fromPrimal $ rconcrete $ Nested.rscalar 7
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                   (AstTensor AstMethodLet FullSpan) Double Float
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id blackGlyph
      ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                           (toTarget @Concrete valsInitVT2OPP)
      artifactRev = revArtifactAdapt UseIncomingCotangent afcnn2T ftk
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let m5 = str (sreplicate @5 (scast (ssum @3 (sconcrete (sreplicate [3,4] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = str (sreplicate @2 (scast (ssum @4 (m5 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in rfromS (ssum @5 (m6 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1)))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m5 = str (sreplicate @5 (scast (ssum @3 (sconcrete (sreplicate [3,4] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = str (sreplicate @2 (scast (ssum @4 (m5 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v8 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m9 = sreplicate @4 (scast v8) ; v10 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m9))) in tpair (tpair (tpair (rfromS (str (sconcrete (sreplicate [3,4] 7.0) * sreplicate @3 v10))) (rfromS v10)) (tpair (rfromS (str (m5 * m9))) (rfromS v8))) (tpair (rfromS (str (m6 * sreplicate @5 (sfromR dret)))) dret)"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m5 = str (sreplicate @5 (scast (ssum @3 (sconcrete (sreplicate [3,4] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = str (sreplicate @2 (scast (ssum @4 (m5 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v8 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m9 = sreplicate @4 (scast v8) ; v10 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m9))) in tpair (tpair (tpair (rfromS (str (sconcrete (sreplicate [3,4] 7.0) * sreplicate @3 v10))) (rfromS v10)) (tpair (rfromS (str (m5 * m9))) (rfromS v8))) (tpair (rfromS (str (m6 * sreplicate @5 (sfromR dret)))) dret)"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4,3] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4] FTKScalar)) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5,4] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5] FTKScalar)) ConvSX)))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2,5] FTKScalar)) ConvSX)) ConvId)) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKR (SNat @1) STKScalar))) (let v5 = scast (sdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1)))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; v8 = sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 (sfromR dret)) ; v9 = scast v8 ; v10 = scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v9)) in tpair (tpair (tpair (sconcrete (sreplicate [4,3] 7.0) * str (sreplicate @3 v10)) v10) (tpair (sreplicate @5 v5 * str (sreplicate @4 v9)) v8)) (tpair (sreplicate @2 (scast (sdot1In (sreplicate @5 v5) (sfromR (tproject1 (tproject2 (tproject1 m1))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @5 (sfromR dret))) dret))"

testVT2OAst :: Assertion
testVT2OAst = do
  let ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                 (toTarget @Concrete valsInitVT2OPP)
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan (XParams2 Double Float)
      var = AstVar varName
      vals = toTarget @Concrete valsInitVT2OPP
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @3) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => MnistFcnnRanked2.ADFcnnMnist2Parameters f Double Float
             -> f (TKR 1 Double)
      afcnn2 = MnistFcnnRanked2.afcnnMnist2
                 id id
                 (rconcrete $ unConcrete blackGlyph)
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 valsInitVT2OPP
  interpretAstFull @Concrete env
                   (simplifyInline @(TKR 1 Double) afcnn1)
    @?= afcnn2 valsInitVT2OPP
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 1 Double) afcnn1)
    @?= afcnn2 valsInitVT2OPP

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let blackGlyph = treplicate (SNat @3) knownSTK
                   $ fromPrimal $ rconcrete $ Nested.rscalar 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Float Float
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Float)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      constant =
        let ((a1, a2), (a3, a4), (a5, a6)) = valsInitVT2OPP
        in ( ( rcast $ fromPrimal $ rconcrete $ unConcrete a1
             , rcast $ fromPrimal $ rconcrete $ unConcrete a2 )
           , ( fromPrimal $ rcast $ rconcrete $ unConcrete a3
             , fromPrimal $ rcast $ rconcrete $ unConcrete a4 )
           , ( rcast $ fromPrimal $ rconcrete $ unConcrete a5
             , fromPrimal $ rcast $ rconcrete $ unConcrete a6 ) )
      ast3 = fun1ToAst (FTKR (0 :$: ZSR) (FTKScalar @Float))
                       (const $ afcnn2TnonLin constant)
  "\\dummy" ++ " -> " ++ printAstSimple ast3
    @?= "\\dummy -> rfromS (tlet (exp (ssum @5 (str (sreplicate @2 (tlet (ssum @4 (str (sreplicate @5 (tlet (tfromPrimal (STKS [4] STKScalar) (ssum @3 (sconcrete (sreplicate [3,4] 7.0) * str (scast (sconcrete (sfromListLinear [4,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0])))) + scast (sconcrete (sfromListLinear [4] [1.0,2.0,3.0,4.0])))) (\\v5 -> ttletPrimal (recip (sconcrete (sreplicate [4] 1.0) + exp (negate (sfromR (tprimalPart (rfromS v5)))))) (\\v6 -> tfromPrimal (STKS [4] STKScalar) v6 + sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [4] STKScalar) (v6 * (sconcrete (sreplicate [4] 1.0) + negate v6)) * sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v5))))))))))) * tfromPrimal (STKS [4,5] STKScalar) (sconcrete (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0]))) + tfromPrimal (STKS [5] STKScalar) (scast (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v7 -> ttletPrimal (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (sfromR (tprimalPart (rfromS v7)))))) (\\v8 -> tfromPrimal (STKS [5] STKScalar) v8 + sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [5] STKScalar) (v8 * (sconcrete (sreplicate [5] 1.0) + negate v8)) * sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v7))))))))))) * tfromPrimal (STKS [5,2] STKScalar) (str (scast (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))))) + tfromPrimal (STKS [2] STKScalar) (scast (sconcrete (sfromListLinear [2] [1.0,2.0]))))) (\\v9 -> sreplicate @2 (recip (ssum @2 v9)) * v9))"
  "\\dummy" ++ " -> " ++ printAstSimple (simplifyInlineContract ast3)
    @?= "\\dummy -> rfromS (tlet (exp (sdot1In (sreplicate @2 (tlet (sdot1In (sreplicate @5 (ttletPrimal (recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sfromListLinear [4] [-43.0,-44.0,-45.0,-46.0])))) (\\v6 -> tfromPrimal (STKS [4] STKScalar) v6 + tfromDual (tdualPart (STKS [4] STKScalar) (tfromPrimal (STKS [4] STKScalar) (v6 * (sconcrete (sreplicate [4] 1.0) + negate v6)) * tfromDual (tdualPart (STKS [4] STKScalar) (tfromPrimal (STKS [4] STKScalar) (sconcrete (sreplicate [4] 0.0))))))))) (tfromPrimal (STKS [5,4] STKScalar) (sconcrete (sfromListLinear [5,4] [1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0]))) + tfromPrimal (STKS [5] STKScalar) (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0]))) (\\v7 -> ttletPrimal (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (tprimalPart v7)))) (\\v8 -> tfromPrimal (STKS [5] STKScalar) v8 + tfromDual (tdualPart (STKS [5] STKScalar) (tfromPrimal (STKS [5] STKScalar) (v8 * (sconcrete (sreplicate [5] 1.0) + negate v8)) * tfromDual (tdualPart (STKS [5] STKScalar) v7))))))) (tfromPrimal (STKS [2,5] STKScalar) (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))) + tfromPrimal (STKS [2] STKScalar) (sconcrete (sfromListLinear [2] [1.0,2.0])))) (\\v9 -> sreplicate @2 (recip (ssum0 v9)) * v9))"

testVT2OPPNonLin2 :: Assertion
testVT2OPPNonLin2 = do
  resetVarCounter
  let blackGlyph = treplicate (SNat @3) knownSTK
                   $ fromPrimal $ rconcrete $ Nested.rscalar 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Double Float
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                           (toTarget @Concrete valsInitVT2OPP)
      artifactRevnonLin =
        revArtifactAdapt UseIncomingCotangent afcnn2TnonLin ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\m1 -> rfromS (let v23 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (scast (recip (sconcrete (sreplicate [4] 1.0) + exp (negate (sdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in sreplicate @2 (recip (ssum0 v23)) * v23)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (sconcrete (sreplicate [3,4] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; m16 = str (sreplicate @5 (scast v13)) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v23 = exp (ssum @5 (str (sreplicate @2 v20) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum @2 v23 ; v25 = sreplicate @2 (recip x24) in rfromS (v25 * v23)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (sconcrete (sreplicate [3,4] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; v14 = sconcrete (sreplicate [4] 1.0) + negate v13 ; v15 = v13 * v14 ; m16 = str (sreplicate @5 (scast v13)) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v21 = sconcrete (sreplicate [5] 1.0) + negate v20 ; v22 = v20 * v21 ; v23 = exp (ssum @5 (str (sreplicate @2 v20) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum @2 v23 ; v25 = sreplicate @2 (recip x24) ; v27 = v23 * (sreplicate @2 (negate (recip (x24 * x24)) * ssum @2 (v23 * sfromR dret)) + v25 * sfromR dret) ; v28 = v22 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v27)) ; m29 = sreplicate @4 (scast v28) ; v30 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m29))) in tpair (tpair (tpair (rfromS (str (sconcrete (sreplicate [3,4] 7.0) * sreplicate @3 v30))) (rfromS v30)) (tpair (rfromS (str (m16 * m29))) (rfromS v28))) (tpair (rfromS (str (str (sreplicate @2 v20) * sreplicate @5 v27))) (rfromS v27))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4,3] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4] FTKScalar)) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5,4] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5] FTKScalar)) ConvSX)))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2,5] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2] FTKScalar)) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (sdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v16 = scast v13 ; v20 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v23 = exp (sdot1In (sreplicate @2 v20) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum0 v23 ; v27 = v23 * (sreplicate @2 (negate (recip (x24 * x24)) * sdot0 v23 (sfromR dret)) + sreplicate @2 (recip x24) * sfromR dret) ; v28 = (v20 * (sconcrete (sreplicate [5] 1.0) + negate v20)) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v27) ; v29 = scast v28 ; v30 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v29)) in tpair (tpair (tpair (sconcrete (sreplicate [4,3] 7.0) * str (sreplicate @3 v30)) v30) (tpair (sreplicate @5 v16 * str (sreplicate @4 v29)) v28)) (tpair (sreplicate @2 v20 * str (sreplicate @5 v27)) v27))"

testVT2OAstNonLin2 :: Assertion
testVT2OAstNonLin2 = do
  let ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                 (toTarget @Concrete valsInitVT2OPP)
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan (XParams2 Double Float)
      var = AstVar varName
      vals = toTarget @Concrete valsInitVT2OPP
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @3) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => MnistFcnnRanked2.ADFcnnMnist2Parameters f Double Float
             -> f (TKR 1 Double)
      afcnn2 = MnistFcnnRanked2.afcnnMnist2
                 logistic softMax1
                 (rconcrete $ unConcrete blackGlyph)
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 valsInitVT2OPP
  interpretAstFull @Concrete env
                   (simplifyInline @(TKR 1 Double) afcnn1)
    @?= afcnn2 valsInitVT2OPP
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 1 Double) afcnn1)
    @?= afcnn2 valsInitVT2OPP

testVT2OPPNonLin3 :: Assertion
testVT2OPPNonLin3 = do
  resetVarCounter
  let blackGlyph = treplicate (SNat @3) knownSTK
                   $ fromPrimal $ rconcrete $ Nested.rscalar 7
      blackLabel = treplicate (SNat @2) knownSTK
                   $ fromPrimal $ rconcrete $ Nested.rscalar 8
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Double Float
                    -> AstTensor AstMethodLet FullSpan (TKScalar Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnistLoss2 (blackGlyph, blackLabel)
      ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                           (toTarget @Concrete valsInitVT2OPP)
      artifactRevnonLin =
        revArtifactAdapt UseIncomingCotangent afcnn2TnonLin ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\m1 -> let v23 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (scast (recip (sconcrete (sreplicate [4] 1.0) + exp (negate (sdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in negate (kfromS (sdot0 (sconcrete (sreplicate [2] 8.0)) (log (sreplicate @2 (recip (ssum0 v23)) * v23))))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (sconcrete (sreplicate [3,4] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; m16 = str (sreplicate @5 (scast v13)) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v23 = exp (ssum @5 (str (sreplicate @2 v20) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum @2 v23 ; v25 = sreplicate @2 (recip x24) ; v26 = v25 * v23 ; v27 = log v26 in negate (kfromS (ssum @2 (sconcrete (sreplicate [2] 8.0) * v27)))"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (sconcrete (sreplicate [3,4] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; v14 = sconcrete (sreplicate [4] 1.0) + negate v13 ; v15 = v13 * v14 ; m16 = str (sreplicate @5 (scast v13)) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v21 = sconcrete (sreplicate [5] 1.0) + negate v20 ; v22 = v20 * v21 ; v23 = exp (ssum @5 (str (sreplicate @2 v20) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum @2 v23 ; v25 = sreplicate @2 (recip x24) ; v26 = v25 * v23 ; v29 = sconcrete (sreplicate [2] 8.0) * (recip v26 * sreplicate @2 (sfromK ((-1.0) * dret))) ; v30 = v23 * (sreplicate @2 (negate (recip (x24 * x24)) * ssum @2 (v23 * v29)) + v25 * v29) ; v31 = v22 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v30)) ; m32 = sreplicate @4 (scast v31) ; v33 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m32))) in tpair (tpair (tpair (rfromS (str (sconcrete (sreplicate [3,4] 7.0) * sreplicate @3 v33))) (rfromS v33)) (tpair (rfromS (str (m16 * m32))) (rfromS v31))) (tpair (rfromS (str (str (sreplicate @2 v20) * sreplicate @5 v30))) (rfromS v30))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4,3] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4] FTKScalar)) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5,4] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5] FTKScalar)) ConvSX)))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2,5] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2] FTKScalar)) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (sdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v16 = scast v13 ; v20 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v23 = exp (sdot1In (sreplicate @2 v20) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum0 v23 ; x25 = recip x24 ; v29 = sconcrete (sreplicate [2] 8.0) * (recip (sreplicate @2 x25 * v23) * sreplicate @2 (sscalar (-1.0) * sfromK dret)) ; v30 = v23 * (sreplicate @2 (negate (recip (x24 * x24)) * sdot0 v23 v29) + sreplicate @2 x25 * v29) ; v31 = (v20 * (sconcrete (sreplicate [5] 1.0) + negate v20)) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v30) ; v32 = scast v31 ; v33 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v32)) in tpair (tpair (tpair (sconcrete (sreplicate [4,3] 7.0) * str (sreplicate @3 v33)) v33) (tpair (sreplicate @5 v16 * str (sreplicate @4 v32)) v31)) (tpair (sreplicate @2 v20 * str (sreplicate @5 v30)) v30))"

testVT2OAstNonLin3 :: Assertion
testVT2OAstNonLin3 = do
  let ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                 (toTarget @Concrete valsInitVT2OPP)
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan (XParams2 Double Float)
      var = AstVar varName
      vals = toTarget @Concrete valsInitVT2OPP
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @3) knownSTK $ rscalar 7
      blackLabel = treplicate (SNat @2) knownSTK $ rscalar 8
      afcnn2 :: ADReady f
             => MnistFcnnRanked2.ADFcnnMnist2Parameters f Double Float
             -> f (TKScalar Double)
      afcnn2 = MnistFcnnRanked2.afcnnMnistLoss2
                 ( rconcrete $ unConcrete blackGlyph
                 , rconcrete $ unConcrete blackLabel )
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 valsInitVT2OPP
  interpretAstFull @Concrete env
                   (simplifyInline @(TKScalar Double) afcnn1)
    @?= afcnn2 valsInitVT2OPP
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKScalar Double) afcnn1)
    @?= afcnn2 valsInitVT2OPP


-- * RNNR tests

tensorMnistPPRNNR :: TestTree
tensorMnistPPRNNR = testGroup "PP and Ast tests for RNNR MNIST"
  [ testCase "RNNO PP" testRNNOPP
  , testCase "RNNO Ast" testRNNOAst
  , testCase "RNNO PP 2" testRNNOPP2
  , testCase "RNNO Ast 2" testRNNOAst2
  ]

valsInitRNNOPP
  :: Int -> Int -> ADRnnMnistParameters Concrete Double
valsInitRNNOPP out_width sizeMnistHeightI =
  ( ( Concrete
      $ Nested.rfromListPrimLinear [out_width, sizeMnistHeightI]
          (map fromIntegral [0 .. out_width * sizeMnistHeightI - 1])
    , Concrete
      $ Nested.rfromListPrimLinear [out_width, out_width]
          (map fromIntegral [0 .. out_width * out_width - 1])
    , Concrete
      $ Nested.rfromListPrimLinear [out_width]
          (map fromIntegral [0 .. out_width - 1]) )
  , ( Concrete
      $ Nested.rfromListPrimLinear [out_width, out_width]
          (map fromIntegral [0 .. out_width * out_width - 1])
    , Concrete
      $ Nested.rfromListPrimLinear [out_width, out_width]
          (map fromIntegral [0 .. out_width * out_width - 1])
    , Concrete
      $ Nested.rfromListPrimLinear [out_width]
          (map fromIntegral [0 .. out_width - 1]) )
  , ( Concrete
      $ Nested.rfromListPrimLinear [sizeMnistLabelInt, out_width]
          (map fromIntegral [0 .. sizeMnistLabelInt * out_width - 1])
    , Concrete
      $ Nested.rfromListPrimLinear [sizeMnistLabelInt]
          (map fromIntegral [0 .. sizeMnistLabelInt - 1]) ) )

testRNNOPP :: Assertion
testRNNOPP = do
  resetVarCounter
  let batch_size = 1
      sizeMnistHeightI = 1
      blackGlyph :: AstTensor AstMethodLet PrimalSpan (TKR 3 Double)
      blackGlyph = AstReplicate (SNat @1) knownSTK
                   $ AstReplicate (SNat @1) knownSTK
                   $ AstReplicate (SNat @1) knownSTK
                       (rconcrete $ Nested.rscalar 7
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: ADRnnMnistParameters (AstTensor AstMethodLet FullSpan)
                                      Double
              -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      ftk = tftk @Concrete
                 (knownSTK @(X (ADRnnMnistParameters Concrete Double)))
                 (toTarget @Concrete $ valsInitRNNOPP 1 sizeMnistHeightI)
      artifactRev = revArtifactAdapt UseIncomingCotangent afcnn2T ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (str (sreplicate @1 (str (sfromR (tproject1 (tproject2 m1))) !$ [0] * sreplicate @10 (tanh (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] * tanh (sscalar 7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0]) + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0])))) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let x16 = sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0] ; x18 = tanh (sscalar 7.0 * x16 + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0]) ; x19 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] ; x21 = tanh (x19 * x18 + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]) ; v22 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] in rfromS (str (sreplicate @1 (v22 * sreplicate @10 x21)) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let x16 = sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0] ; x18 = tanh (sscalar 7.0 * x16 + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0]) ; x19 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] ; x21 = tanh (x19 * x18 + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]) ; v22 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] ; x24 = (sscalar 1.0 + negate x21 * x21) * ssum @10 (v22 * ssum @1 (str (sfromR dret))) ; x25 = (sscalar 1.0 + negate x18 * x18) * (x19 * x24) in tpair (tpair (tpair (tpair (rfromS (soneHot (sscalar 7.0 * x25) [0, 0])) (rfromS (soneHot (sscalar 0.0) [0, 0]))) (rfromS (soneHot x25 [0]))) (tpair (tpair (rfromS (soneHot (x18 * x24) [0, 0])) (rfromS (soneHot (sscalar 0.0) [0, 0]))) (rfromS (soneHot x24 [0])))) (tpair (rfromS (str (soneHot (sreplicate @10 x21 * ssum @1 (str (sfromR dret))) [0]))) (rfromS (ssum @1 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1,1] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1,1] FTKScalar)) ConvSX))) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1] FTKScalar)) ConvSX))) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1,1] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1,1] FTKScalar)) ConvSX))) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1] FTKScalar)) ConvSX)))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [10,1] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [10] FTKScalar)) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKS [1,1] STKScalar)) (STKS [1] STKScalar)) (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKS [1,1] STKScalar)) (STKS [1] STKScalar))) (STKProduct (STKS [10,1] STKScalar) (STKS [10] STKScalar))) (let x18 = tanh (sscalar 7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0]) ; x19 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] ; x21 = tanh (x19 * x18 + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]) ; x24 = (sscalar 1.0 + negate x21 * x21) * sdot0 (str (sfromR (tproject1 (tproject2 m1))) !$ [0]) (str (sfromR dret) !$ [0]) ; x25 = (sscalar 1.0 + negate x18 * x18) * (x19 * x24) in tpair (tpair (tpair (tpair (sreplicate @1 (sreplicate @1 (sscalar 7.0 * x25))) (sconcrete (sfromListLinear [1,1] [0.0]))) (sreplicate @1 x25)) (tpair (tpair (sreplicate @1 (sreplicate @1 (x18 * x24))) (sconcrete (sfromListLinear [1,1] [0.0]))) (sreplicate @1 x24))) (tpair (str (sreplicate @1 (sreplicate @10 x21 * str (sfromR dret) !$ [0]))) (str (sfromR dret) !$ [0])))"

testRNNOAst :: Assertion
testRNNOAst = do
  let batch_size = 1
      sizeMnistHeightI = 1
      ftk = tftk @Concrete
                 (knownSTK @(X (ADRnnMnistParameters Concrete Double)))
                 (toTarget @Concrete $ valsInitRNNOPP 1 sizeMnistHeightI)
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan
                       (X (ADRnnMnistParameters Concrete Double))
      var = AstVar varName
      vals = toTarget @Concrete $ valsInitRNNOPP 1 sizeMnistHeightI
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @1) knownSTK
                   $ treplicate (SNat @1) knownSTK
                   $ treplicate (SNat @1) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => ADRnnMnistParameters f Double
             -> f (TKR 2 Double)
      afcnn2 = MnistRnnRanked2.rnnMnistZeroR
                 batch_size (rconcrete $ unConcrete blackGlyph)
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 (valsInitRNNOPP 1 sizeMnistHeightI)
  interpretAstFull @Concrete env
                   (simplifyInline @(TKR 2 Double) afcnn1)
    @?= afcnn2 (valsInitRNNOPP 1 sizeMnistHeightI)
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 2 Double) afcnn1)
    @?= afcnn2 (valsInitRNNOPP 1 sizeMnistHeightI)

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let batch_size = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstTensor AstMethodLet PrimalSpan (TKR 3 Double)
      blackGlyph = AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                       (rconcrete $ Nested.rscalar 7
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: ADRnnMnistParameters (AstTensor AstMethodLet FullSpan)
                                      Double
              -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      ftk = tftk @Concrete
                 (knownSTK @(X (ADRnnMnistParameters Concrete Double)))
                 (toTarget @Concrete $ valsInitRNNOPP 2 sizeMnistHeightI)
      artifactRev = revArtifactAdapt UseIncomingCotangent afcnn2T ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (let m40 = sappend (tanh (str (sreplicate @2 (sdot1In (sconcrete (sreplicate [2,2] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) (tanh (str (sreplicate @2 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 (tanh (sdot1In (sconcrete (sreplicate [2,2] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((str (sreplicate @2 (sdot1In (sconcrete (sreplicate [2,2] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice (SNat @0) (SNat @2) m40)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m40)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let m37 = tanh ((str (sreplicate @2 (ssum @2 (sconcrete (sreplicate [2,2] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (ssum @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v38 = tanh ((ssum @2 (sconcrete (sreplicate [2,2] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + ssum @2 (sconcrete (sreplicate [2,2] 0.0))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m39 = tanh ((str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v38)))) + str (sreplicate @2 (ssum @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m40 = sappend m37 m39 ; m41 = tanh ((sreplicate @2 (ssum @2 (sconcrete (sreplicate [2,2] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) + ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * stranspose @[2,1,0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m40))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m42 = tanh ((ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 m41)) + ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m40))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) in rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * str (sreplicate @10 m42)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m37 = tanh ((str (sreplicate @2 (ssum @2 (sconcrete (sreplicate [2,2] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (ssum @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v38 = tanh ((ssum @2 (sconcrete (sreplicate [2,2] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + ssum @2 (sconcrete (sreplicate [2,2] 0.0))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m39 = tanh ((str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v38)))) + str (sreplicate @2 (ssum @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m40 = sappend m37 m39 ; m41 = tanh ((sreplicate @2 (ssum @2 (sconcrete (sreplicate [2,2] 7.0) * str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) + ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * stranspose @[2,1,0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m40))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m42 = tanh ((ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 m41)) + ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m40))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m44 = (sconcrete (sreplicate [2,2] 1.0) + negate m42 * m42) * ssum @10 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @2 (sfromR dret))) ; m45 = (sconcrete (sreplicate [2,2] 1.0) + negate m41 * m41) * ssum @2 (stranspose @[1,2,0] (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m44)) ; m46 = sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (str (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * sreplicate @2 m45)))) (sconcrete (sreplicate [2,2] 0.0))) + sappend (sconcrete (sreplicate [2,2] 0.0)) (sappend (str (ssum @2 (stranspose @[1,2,0] (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m44)))) (sconcrete (sfromListLinear [0,2] []))) ; m47 = (sconcrete (sreplicate [2,2] 1.0) + negate m39 * m39) * sslice (SNat @2) (SNat @2) m46 ; m48 = sreplicate @2 (ssum @2 (str m47)) ; v49 = (sconcrete (sreplicate [2] 1.0) + negate v38 * v38) * ssum @2 (str (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * m48)) ; m50 = (sconcrete (sreplicate [2,2] 1.0) + negate m37 * m37) * sslice (SNat @0) (SNat @2) m46 in tpair (tpair (tpair (tpair (rfromS (str (sconcrete (sreplicate [2,2] 7.0) * sreplicate @2 (ssum @2 (str m50))) + (str (sconcrete (sreplicate [2,2] 7.0) * sreplicate @2 v49) + str (sconcrete (sreplicate [2,2] 7.0) * sreplicate @2 (ssum @2 m45))))) (rfromS (str (sconcrete (sreplicate [2,2] 0.0)) + (str (sconcrete (sreplicate [2,2] 0.0)) + str (ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m40))) * sreplicate @2 m45))))))) (rfromS (ssum @2 (str m50) + (v49 + ssum @2 m45)))) (tpair (tpair (rfromS (str (str (sreplicate @2 v38) * m48) + str (ssum @2 (stranspose @[2,0,1] (stranspose @[2,0,1] (sreplicate @2 m41) * sreplicate @2 m44))))) (rfromS (str (sconcrete (sreplicate [2,2] 0.0)) + str (ssum @2 (stranspose @[2,0,1] (stranspose @[2,0,1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m40))) * sreplicate @2 m44)))))) (rfromS (ssum @2 (str m47) + ssum @2 (str m44))))) (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @10 m42) * sreplicate @2 (sfromR dret))))) (rfromS (ssum @2 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [10,2] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [10] FTKScalar)) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [2,2] STKScalar) (STKS [2,2] STKScalar)) (STKS [2] STKScalar)) (STKProduct (STKProduct (STKS [2,2] STKScalar) (STKS [2,2] STKScalar)) (STKS [2] STKScalar))) (STKProduct (STKS [10,2] STKScalar) (STKS [10] STKScalar))) (let m37 = tanh (str (sreplicate @2 (sdot1In (sconcrete (sreplicate [2,2] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v38 = tanh (sdot1In (sconcrete (sreplicate [2,2] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m39 = tanh (str (sreplicate @2 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 v38))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m40 = sappend m37 m39 ; m41 = tanh ((sreplicate @2 (sdot1In (sconcrete (sreplicate [2,2] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + smatmul2 (str (sslice (SNat @0) (SNat @2) m40)) (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m42 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (str m41) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m40)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m44 = (sconcrete (sreplicate [2,2] 1.0) + negate m42 * m42) * smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR dret) ; m45 = (sconcrete (sreplicate [2,2] 1.0) + negate m41 * m41) * smatmul2 (str m44) (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) ; m46 = sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) (str m45)) (sconcrete (sreplicate [2,2] 0.0)) + sappend (sconcrete (sreplicate [2,2] 0.0)) (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) m44) ; m47 = (sconcrete (sreplicate [2,2] 1.0) + negate m39 * m39) * sslice (SNat @2) (SNat @2) m46 ; v48 = ssum @2 (str m47) ; v49 = (sconcrete (sreplicate [2] 1.0) + negate v38 * v38) * sdot1In (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) (sreplicate @2 v48) ; m50 = (sconcrete (sreplicate [2,2] 1.0) + negate m37 * m37) * sslice (SNat @0) (SNat @2) m46 in tpair (tpair (tpair (tpair (sconcrete (sreplicate [2,2] 7.0) * str (sreplicate @2 (ssum @2 (str m50))) + (sconcrete (sreplicate [2,2] 7.0) * str (sreplicate @2 v49) + sconcrete (sreplicate [2,2] 7.0) * str (sreplicate @2 (ssum @2 m45)))) (smatmul2 (str m45) (str (sslice (SNat @0) (SNat @2) m40)))) (ssum @2 (str m50) + (v49 + ssum @2 m45))) (tpair (tpair (sreplicate @2 v38 * str (sreplicate @2 v48) + smatmul2 m44 m41) (smatmul2 m44 (str (sslice (SNat @2) (SNat @2) m40)))) (ssum @2 (str m47) + ssum @2 (str m44)))) (tpair (smatmul2 (sfromR dret) (str m42)) (ssum @2 (str (sfromR dret)))))"

testRNNOAst2 :: Assertion
testRNNOAst2 = do
  let batch_size = 2
      sizeMnistHeightI = 2
      ftk = tftk @Concrete
                 (knownSTK @(X (ADRnnMnistParameters Concrete Double)))
                 (toTarget @Concrete $ valsInitRNNOPP 2 sizeMnistHeightI)
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan
                       (X (ADRnnMnistParameters Concrete Double))
      var = AstVar varName
      vals = toTarget @Concrete $ valsInitRNNOPP 2 sizeMnistHeightI
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @2) knownSTK
                   $ treplicate (SNat @2) knownSTK
                   $ treplicate (SNat @2) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => ADRnnMnistParameters f Double
             -> f (TKR 2 Double)
      afcnn2 = MnistRnnRanked2.rnnMnistZeroR
                 batch_size (rconcrete $ unConcrete blackGlyph)
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 (valsInitRNNOPP 2 sizeMnistHeightI)
  interpretAstFull @Concrete env
                   (simplifyInline @(TKR 2 Double) afcnn1)
    @?= afcnn2 (valsInitRNNOPP 2 sizeMnistHeightI)
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 2 Double) afcnn1)
    @?= afcnn2 (valsInitRNNOPP 2 sizeMnistHeightI)


-- * CNNR tests

tensorMnistCNNRPP :: TestTree
tensorMnistCNNRPP = testGroup "Ast tests for CNNR MNIST"
  [ testCase "CNNO PP 1" testCNNOPP1
  , testCase "CNNO Ast 1" testCNNOAst1
  , testCase "CNNO PP 2" testCNNOPP2
  , testCase "CNNO Ast 2" testCNNOAst2
  , testCase "CNNO PP 2S" testCNNOPP2S
  ]

testCNNOPP1 :: Assertion
testCNNOPP1 = do
  resetVarCounter
  let batch_size = 5
      sizeMnistWidthI = 7
      sizeMnistHeightI = 9
      ftk = tftk @Concrete
                 (knownSTK @(X (MnistCnnRanked2.ADCnnMnistParameters
                                  Concrete Double)))
                 vals
      valsInit :: MnistCnnRanked2.ADCnnMnistParameters Concrete Double
      valsInit =
        forgetShape $ fst
        $ randomValue @(MnistCnnRanked2.ADCnnMnistParametersShaped
                         Concrete 7 9  -- see sizeMnistWidthI, etc.
                         1 1 1 1 Double)
                      0.4 (mkStdGen 44)
      vals = toTarget @Concrete valsInit
      blackGlyph = treplicate (SNat @5) knownSTK
                   $ treplicate (SNat @1) knownSTK
                   $ treplicate (SNat @7) knownSTK
                   $ treplicate (SNat @9) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => MnistCnnRanked2.ADCnnMnistParameters f Double
             -> f (TKR 2 Double)
      afcnn2 = MnistCnnRanked2.convMnistTwoR
                 sizeMnistHeightI sizeMnistWidthI batch_size
                 (rconcrete $ unConcrete blackGlyph)
      artifactRev = revArtifactAdapt UseIncomingCotangent afcnn2 ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (let t189 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[7,9,4] (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [7,9] 7.0)) (\\[i358, i359] -> [i358 + i359]))) (\\[i185, i186] -> [i185 + i186])))))) * sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; t204 = sreshape @[3,4,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i192, i193, i194, i195] -> [ifH (sscalar -0.0 <=. negate (t189 !$ [0, kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i192, i194]), kfromS (sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) !$ [i193, i195])])) 0 1]) * sgather (t189 !$ [0]) (\\[i198, i199, i200, i201] -> [kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i198, i200]), kfromS (sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) !$ [i199, i201])])) ; t213 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[3,4,4] (stranspose @[2,0,3,1] (sgather (stranspose @[2,3,4,0,1] (sgather (stranspose @[3,5,0,4,1,2] (sgather (stranspose @[3,2,1,6,5,4,0] (sreplicate @2 (stranspose @[5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[2,1,0] t204))))))) (\\[i346, i350] -> [kfromS (smaxIndex (t204 !$ [i346, i350])), i350, i346]))) (\\[i355, i356] -> [i355, i356, i355 + i356]))) (\\[i209, i210] -> [i209, i209 + i210, i210])) * sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])))))) + stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m223 = sreshape @[2,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i215, i216, i217] -> [ifH (sscalar -0.0 <=. negate (t213 !$ [0, i216, kfromS (sconcrete (sfromListLinear [2,2] [0,1,2,3]) !$ [i215, i217])])) 0 1]) * stranspose @[0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (t213 !$ [0]))) (\\[i219, i220] -> [kfromS (sconcrete (sfromListLinear [2,2] [0,1,2,3]) !$ [i219, i220])]))) ; m227 = sreplicate @1 (sreplicate @5 (sdot0 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0]) (sgather m223 (\\[i224] -> [i224, kfromS (smaxIndex (m223 !$ [i224]))])))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) * sreplicate @10 (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i228] -> [ifH (sscalar -0.0 <=. negate (m227 !$ [0, i228])) 0 1]) * m227 !$ [0]) + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w187 = stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [7,9] 7.0)) (\\[i183, i184] -> [i183 + i184]))) (\\[i185, i186] -> [i185 + i186])))))) ; w188 = sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))) ; t189 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[7,9,4] (w187 * w188)))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m190 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m191 = str (sreplicate @2 (sconcrete (sreplicate [4] 2) * siota (SNat @4))) + sreplicate @4 (siota (SNat @2)) ; u202 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i192, i193, i194, i195] -> [let x196 = m190 !$ [i192, i194] ; x197 = m191 !$ [i193, i195] in ifH (sscalar -0.0 <=. negate (t189 !$ [0, kfromS x196, kfromS x197])) 0 1]) ; u203 = sgather (t189 !$ [0]) (\\[i198, i199, i200, i201] -> [kfromS (m190 !$ [i198, i200]), kfromS (m191 !$ [i199, i201])]) ; t204 = sreshape @[3,4,4] (u202 * u203) ; u211 = stranspose @[2,0,3,1] (sgather (stranspose @[2,3,4,0,1] (sgather (stranspose @[3,5,0,4,1,2] (sgather (stranspose @[3,2,1,6,5,4,0] (sreplicate @2 (stranspose @[5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[2,1,0] t204))))))) (\\[i205, i206] -> [kfromS (smaxIndex (t204 !$ [i205, i206])), i206, i205]))) (\\[i207, i208] -> [i207, i208, i207 + i208]))) (\\[i209, i210] -> [i209, i209 + i210, i210])) ; u212 = sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])) ; t213 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[3,4,4] (u211 * u212)))) + stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m214 = str (sreplicate @2 (sconcrete (sreplicate [2] 2) * siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) ; t221 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i215, i216, i217] -> [let x218 = m214 !$ [i215, i217] in ifH (sscalar -0.0 <=. negate (t213 !$ [0, i216, kfromS x218])) 0 1]) ; t222 = stranspose @[0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (t213 !$ [0]))) (\\[i219, i220] -> [kfromS (m214 !$ [i219, i220])])) ; m223 = sreshape @[2,4] (t221 * t222) ; v225 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v226 = sgather m223 (\\[i224] -> [i224, kfromS (smaxIndex (m223 !$ [i224]))]) ; m227 = sreplicate @1 (sreplicate @5 (ssum @2 (v225 * v226))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v229 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i228] -> [ifH (sscalar -0.0 <=. negate (m227 !$ [0, i228])) 0 1]) ; v230 = m227 !$ [0] ; m231 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m232 = sreplicate @10 (v229 * v230) in rfromS (m231 * m232 + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w187 = stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [7,9] 7.0)) (\\[i183, i184] -> [i183 + i184]))) (\\[i185, i186] -> [i185 + i186])))))) ; w188 = sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))) ; t189 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[7,9,4] (w187 * w188)))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m190 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m191 = str (sreplicate @2 (sconcrete (sreplicate [4] 2) * siota (SNat @4))) + sreplicate @4 (siota (SNat @2)) ; u202 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i192, i193, i194, i195] -> [let x196 = m190 !$ [i192, i194] ; x197 = m191 !$ [i193, i195] in ifH (sscalar -0.0 <=. negate (t189 !$ [0, kfromS x196, kfromS x197])) 0 1]) ; u203 = sgather (t189 !$ [0]) (\\[i198, i199, i200, i201] -> [kfromS (m190 !$ [i198, i200]), kfromS (m191 !$ [i199, i201])]) ; t204 = sreshape @[3,4,4] (u202 * u203) ; u211 = stranspose @[2,0,3,1] (sgather (stranspose @[2,3,4,0,1] (sgather (stranspose @[3,5,0,4,1,2] (sgather (stranspose @[3,2,1,6,5,4,0] (sreplicate @2 (stranspose @[5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[2,1,0] t204))))))) (\\[i205, i206] -> [kfromS (smaxIndex (t204 !$ [i205, i206])), i206, i205]))) (\\[i207, i208] -> [i207, i208, i207 + i208]))) (\\[i209, i210] -> [i209, i209 + i210, i210])) ; u212 = sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])) ; t213 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[3,4,4] (u211 * u212)))) + stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m214 = str (sreplicate @2 (sconcrete (sreplicate [2] 2) * siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) ; t221 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i215, i216, i217] -> [let x218 = m214 !$ [i215, i217] in ifH (sscalar -0.0 <=. negate (t213 !$ [0, i216, kfromS x218])) 0 1]) ; t222 = stranspose @[0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (t213 !$ [0]))) (\\[i219, i220] -> [kfromS (m214 !$ [i219, i220])])) ; m223 = sreshape @[2,4] (t221 * t222) ; v225 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v226 = sgather m223 (\\[i224] -> [i224, kfromS (smaxIndex (m223 !$ [i224]))]) ; m227 = sreplicate @1 (sreplicate @5 (ssum @2 (v225 * v226))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v229 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i228] -> [ifH (sscalar -0.0 <=. negate (m227 !$ [0, i228])) 0 1]) ; v230 = m227 !$ [0] ; m231 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m232 = sreplicate @10 (v229 * v230) ; m234 = soneHot (v229 * ssum @10 (m231 * sfromR dret)) [0] ; v235 = sreplicate @2 (ssum @5 (ssum @1 m234)) ; t239 = soneHot (sappend (sconcrete (sfromListLinear [0,4] [])) (sappend (str (sscatter (stranspose @[0,2,1] (t221 * sreshape @[2,2,2] (sscatter (v225 * v235) (\\[i236] -> [i236, kfromS (smaxIndex (m223 !$ [i236]))])))) (\\[i237, i238] -> [kfromS (m214 !$ [i237, i238])]))) (sconcrete (sreplicate [1,4] 0.0)))) [0] ; u240 = sreshape @[3,4,2,2] (stranspose @[1,2,0] (sreplicate @4 (ssum @1 t239))) ; t251 = soneHot (sscatter (u202 * sreshape @[3,4,2,2] (stranspose @[2,1,0] (ssum @2 (ssum @3 (ssum @4 (stranspose @[3,4,5,2,1,0] (ssum @2 (stranspose @[6,2,1,0,5,4,3] (sscatter (stranspose @[2,4,5,0,3,1] (sscatter (stranspose @[3,4,0,1,2] (sscatter (stranspose @[1,3,0,2] (u212 * u240)) (\\[i241, i242] -> [i241, i241 + i242, i242]))) (\\[i243, i244] -> [i243, i244, i243 + i244]))) (\\[i245, i246] -> [kfromS (smaxIndex (t204 !$ [i245, i246])), i246, i245])))))))))) (\\[i247, i248, i249, i250] -> [kfromS (m190 !$ [i247, i249]), kfromS (m191 !$ [i248, i250])])) [0] in tpair (tpair (tpair (rfromS (soneHot (ssum @1 (ssum @1 (ssum @9 (ssum @7 (w187 * sreshape @[7,9,1,1,2,2] (stranspose @[1,2,0] (sreplicate @4 (ssum @1 t251)))))))) [0, 0])) (rfromS (ssum @9 (ssum @7 (stranspose @[1,2,0] t251))))) (tpair (rfromS (soneHot (ssum @4 (ssum @3 (u211 * u240))) [0, 0])) (rfromS (ssum @4 (ssum @3 (stranspose @[1,2,0] t239)))))) (tpair (tpair (rfromS (soneHot (v226 * v235) [0])) (rfromS (ssum @5 (str m234)))) (tpair (rfromS (str (soneHot (ssum @5 (str (m232 * sfromR dret))) [0]))) (rfromS (ssum @5 (str (sfromR dret))))))"
-- TODO: different test result with GHC 9.10:   printArtifactPretty (simplifyArtifact artifactRev)
--    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let u181 = sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [7,9] 7.0)) (\\[i296, i297] -> [i296 + i297]))) (\\[i179, i180] -> [i179 + i180]) ; t183 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[7,9,4] (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] u181)))) * sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; u192 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i184, i185, i186, i187] -> [ifH (sscalar -0.0 <=. negate (t183 !$ [0, 2 * i184 + i186, 2 * i185 + i187])) 0 1]) ; t194 = sreshape @[3,4,4] (u192 * sgather (t183 !$ [0]) (\\[i188, i189, i190, i191] -> [2 * i188 + i190, 2 * i189 + i191])) ; u201 = sgather (stranspose @[2,3,4,0,1] (sgather (stranspose @[3,5,0,4,1,2] (sgather (stranspose @[3,2,1,6,5,4,0] (sreplicate @2 (stranspose @[5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[2,1,0] t194))))))) (\\[i284, i288] -> [kfromS (smaxIndex (t194 !$ [i284, i288])), i288, i284]))) (\\[i293, i294] -> [i293, i294, i293 + i294]))) (\\[i199, i200] -> [i199, i199 + i200, i200]) ; m202 = sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0] ; t203 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[3,4,4] (stranspose @[2,0,3,1] u201 * sreplicate @3 (sreplicate @4 m202))))) + stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; t209 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i204, i205, i206] -> [ifH (sscalar -0.0 <=. negate (t203 !$ [0, i205, 2 * i204 + i206])) 0 1]) ; m211 = sreshape @[2,4] (t209 * stranspose @[0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (t203 !$ [0]))) (\\[i207, i208] -> [2 * i207 + i208]))) ; v213 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v214 = sgather m211 (\\[i212] -> [i212, kfromS (smaxIndex (m211 !$ [i212]))]) ; m215 = sreplicate @1 (sreplicate @5 (sdot0 v213 v214)) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v217 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i216] -> [ifH (sscalar -0.0 <=. negate (m215 !$ [0, i216])) 0 1]) ; v222 = v217 * sdot1In (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) (str (sfromR dret)) ; x223 = ssum0 v222 ; m227 = sappend (str (sscatter (stranspose @[0,2,1] t209 * stranspose @[0,2,1] (sreshape @[2,2,2] (sscatter (v213 * sreplicate @2 x223) (\\[i224] -> [i224, kfromS (smaxIndex (m211 !$ [i224]))])))) (\\[i225, i226] -> [2 * i225 + i226]))) (sconcrete (sreplicate [1,4] 0.0)) ; u228 = sreshape @[3,4,2,2] (stranspose @[1,2,0] (sreplicate @4 m227)) ; m239 = sscatter (u192 * sreshape @[3,4,2,2] (ssum @2 (ssum @3 (ssum @4 (ssum @2 (stranspose @[6,5,4,3,2,1,0] (sscatter (stranspose @[2,4,5,0,3,1] (sscatter (stranspose @[3,4,0,1,2] (sscatter (stranspose @[1,3,0,2] (sreplicate @3 (sreplicate @4 m202)) * stranspose @[1,3,0,2] u228) (\\[i229, i230] -> [i229, i229 + i230, i230]))) (\\[i231, i232] -> [i231, i232, i231 + i232]))) (\\[i233, i234] -> [kfromS (smaxIndex (t194 !$ [i233, i234])), i234, i233])))))))) (\\[i235, i236, i237, i238] -> [2 * i235 + i237, 2 * i236 + i238]) in tpair (tpair (tpair (sreplicate @1 (sreplicate @1 (ssum @9 (sdot1In (stranspose @[0,3,1,2] u181) (stranspose @[2,3,1,4,5,0] (sreshape @[7,9,1,1,2,2] (stranspose @[1,2,0] (sreplicate @4 m239))) !$ [0, 0]))))) (ssum @9 (ssum @7 (stranspose @[1,2,0] (sreplicate @1 m239))))) (tpair (sreplicate @1 (sreplicate @1 (ssum @4 (sdot1In (stranspose @[0,3,1,2] u201) (stranspose @[1,2,3,0] u228))))) (ssum @4 (ssum @3 (stranspose @[1,2,0] (sreplicate @1 m227)))))) (tpair (tpair (sreplicate @1 (v214 * sreplicate @2 x223)) (sreplicate @1 (ssum0 v222))) (tpair (str (sreplicate @1 (sdot1In (sreplicate @10 (v217 * m215 !$ [0])) (sfromR dret)))) (ssum @5 (str (sfromR dret))))))"

testCNNOAst1 :: Assertion
testCNNOAst1 = do
  let batch_size = 5
      sizeMnistWidthI = 7
      sizeMnistHeightI = 9
      ftk = tftk @Concrete
                 (knownSTK @(X (MnistCnnRanked2.ADCnnMnistParameters
                                  Concrete Double)))
                 vals
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan
                       (X (MnistCnnRanked2.ADCnnMnistParameters
                             Concrete Double))
      var = AstVar varName
      valsInit :: MnistCnnRanked2.ADCnnMnistParameters Concrete Double
      valsInit =
        forgetShape $ fst
        $ randomValue @(MnistCnnRanked2.ADCnnMnistParametersShaped
                         Concrete 7 9  -- see sizeMnistWidthI, etc.
                         1 1 1 1 Double)
                      0.4 (mkStdGen 44)
      vals = toTarget @Concrete valsInit
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @5) knownSTK
                   $ treplicate (SNat @1) knownSTK
                   $ treplicate (SNat @7) knownSTK
                   $ treplicate (SNat @9) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => MnistCnnRanked2.ADCnnMnistParameters f Double
             -> f (TKR 2 Double)
      afcnn2 = MnistCnnRanked2.convMnistTwoR
                 sizeMnistHeightI sizeMnistWidthI batch_size
                 (rconcrete $ unConcrete blackGlyph)
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 valsInit
  interpretAstFull @Concrete env
                   (simplifyInline @(TKR 2 Double) afcnn1)
    @?= afcnn2 valsInit
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 2 Double) afcnn1)
    @?= afcnn2 valsInit

testCNNOPP2 :: Assertion
testCNNOPP2 = do
  resetVarCounter
  let batch_size = 7
      sizeMnistWidthI = 14
      sizeMnistHeightI = 23
      ftk = tftk @Concrete
                 (knownSTK @(X (MnistCnnRanked2.ADCnnMnistParameters
                                  Concrete Double)))
                 vals
      valsInit :: MnistCnnRanked2.ADCnnMnistParameters Concrete Double
      valsInit =
        forgetShape $ fst
        $ randomValue @(MnistCnnRanked2.ADCnnMnistParametersShaped
                         Concrete 14 23  -- see sizeMnistWidthI, etc.
                         2 3 4 5 Double)
                      0.4 (mkStdGen 44)
      vals = toTarget @Concrete valsInit
      blackGlyph = treplicate (SNat @7) knownSTK
                   $ treplicate (SNat @1) knownSTK
                   $ treplicate (SNat @14) knownSTK
                   $ treplicate (SNat @23) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => MnistCnnRanked2.ADCnnMnistParameters f Double
             -> f (TKR 2 Double)
      afcnn2 = MnistCnnRanked2.convMnistTwoR
                 sizeMnistHeightI sizeMnistWidthI batch_size
                 (rconcrete $ unConcrete blackGlyph)
      artifactRev = revArtifactAdapt UseIncomingCotangent afcnn2 ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> rfromS (let t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i473, i474] -> [i473 + i474]))) (\\[i251, i252] -> [i251 + i252]))))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; u271 = sreshape @[4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [ifH (sscalar -0.0 <=. negate (t255 !$ [i258, kfromS (sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) !$ [i259, i261]), kfromS (sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) !$ [i260, i262])])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [kfromS (sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) !$ [i265, i267]), kfromS (sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) !$ [i266, i268])]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i458, i460, i461] -> [kfromS (smaxIndex (u271 !$ [i461, i458, i460])), i460, i458, i461]))) (\\[i466, i468] -> [i466, i468, i466 + i468]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; u296 = sreshape @[4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [ifH (sscalar -0.0 <=. negate (t280 !$ [i283, kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i284, i286]), kfromS (sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) !$ [i285, i287])])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i290, i292]), kfromS (sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) !$ [i291, i293])]))) ; m301 = str (sreplicate @7 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (u296 !$ [i297, i298, i299]))])))))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in smatmul2 (sfromR (tproject1 (tproject2 (tproject2 u1)))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar -0.0 <=. negate (m301 !$ [i302, i303])) 0 1]) * m301) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w253 = sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i249, i250] -> [i249 + i250]))) (\\[i251, i252] -> [i251 + i252]))))))) ; w254 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))) ; t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (w253 * w254))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; w269 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let x263 = m256 !$ [i259, i261] ; x264 = m257 !$ [i260, i262] in ifH (sscalar -0.0 <=. negate (t255 !$ [i258, kfromS x263, kfromS x264])) 0 1]) ; w270 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [kfromS (m256 !$ [i265, i267]), kfromS (m257 !$ [i266, i268])])) ; u271 = sreshape @[4,7,11,4] (w269 * w270) ; w279 = sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i272, i273, i274] -> [kfromS (smaxIndex (u271 !$ [i274, i272, i273])), i273, i272, i274]))) (\\[i275, i276] -> [i275, i276, i275 + i276]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (w279 * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m281 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m282 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; w294 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [let x288 = m281 !$ [i284, i286] ; x289 = m282 !$ [i285, i287] in ifH (sscalar -0.0 <=. negate (t280 !$ [i283, kfromS x288, kfromS x289])) 0 1]) ; w295 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [kfromS (m281 !$ [i290, i292]), kfromS (m282 !$ [i291, i293])])) ; u296 = sreshape @[4,3,5,4] (w294 * w295) ; m300 = str (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (u296 !$ [i297, i298, i299]))])))) ; m301 = str (sreplicate @7 (ssum @60 (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m300))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m304 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar -0.0 <=. negate (m301 !$ [i302, i303])) 0 1]) ; t305 = str (sreplicate @10 (m304 * m301)) in rfromS (ssum @5 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * t305) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w253 = sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i249, i250] -> [i249 + i250]))) (\\[i251, i252] -> [i251 + i252]))))))) ; w254 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))) ; t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (w253 * w254))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; w269 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let x263 = m256 !$ [i259, i261] ; x264 = m257 !$ [i260, i262] in ifH (sscalar -0.0 <=. negate (t255 !$ [i258, kfromS x263, kfromS x264])) 0 1]) ; w270 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [kfromS (m256 !$ [i265, i267]), kfromS (m257 !$ [i266, i268])])) ; u271 = sreshape @[4,7,11,4] (w269 * w270) ; w279 = sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i272, i273, i274] -> [kfromS (smaxIndex (u271 !$ [i274, i272, i273])), i273, i272, i274]))) (\\[i275, i276] -> [i275, i276, i275 + i276]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (w279 * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m281 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m282 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; w294 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [let x288 = m281 !$ [i284, i286] ; x289 = m282 !$ [i285, i287] in ifH (sscalar -0.0 <=. negate (t280 !$ [i283, kfromS x288, kfromS x289])) 0 1]) ; w295 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [kfromS (m281 !$ [i290, i292]), kfromS (m282 !$ [i291, i293])])) ; u296 = sreshape @[4,3,5,4] (w294 * w295) ; m300 = str (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (u296 !$ [i297, i298, i299]))])))) ; m301 = str (sreplicate @7 (ssum @60 (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m300))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m304 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar -0.0 <=. negate (m301 !$ [i302, i303])) 0 1]) ; t305 = str (sreplicate @10 (m304 * m301)) ; m307 = m304 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * sreplicate @5 (sfromR dret))) ; m308 = sreplicate @60 (ssum @7 (str m307)) ; t316 = stranspose @[2,0,1] (sscatter (stranspose @[1,2,3,4,0] (w294 * sreshape @[4,3,5,2,2] (sscatter (sreshape @[4,3,5] (ssum @5 (str (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m308)))) (\\[i309, i310, i311] -> [i309, i310, i311, kfromS (smaxIndex (u296 !$ [i309, i310, i311]))])))) (\\[i312, i313, i314, i315] -> [kfromS (m281 !$ [i312, i314]), kfromS (m282 !$ [i313, i315])])) ; w317 = sreshape @[4,7,11,4,3,4] (stranspose @[1,2,3,0] (sreplicate @48 t316)) ; t329 = stranspose @[2,0,1] (sscatter (stranspose @[1,2,3,4,0] (w269 * sreshape @[4,7,11,2,2] (stranspose @[3,2,1,0] (ssum @4 (ssum @7 (ssum @11 (stranspose @[4,5,6,3,2,1,0] (ssum @3 (stranspose @[7,3,2,1,0,6,5,4] (sscatter (stranspose @[2,5,4,6,0,3,1] (sscatter (stranspose @[3,5,0,4,1,2] (sscatter (stranspose @[1,4,0,2,3] (ssum @4 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))) * w317))) (\\[i318, i319] -> [i318, i318 + i319, i319]))) (\\[i320, i321] -> [i320, i321, i320 + i321]))) (\\[i322, i323, i324] -> [kfromS (smaxIndex (u271 !$ [i324, i322, i323])), i323, i322, i324]))))))))))) (\\[i325, i326, i327, i328] -> [kfromS (m256 !$ [i325, i327]), kfromS (m257 !$ [i326, i328])])) in tpair (tpair (tpair (rfromS (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (w253 * sreshape @[4,14,23,1,1,3,4] (stranspose @[1,2,3,0] (sreplicate @12 t329))))))))))) [0]))) (rfromS (ssum @23 (ssum @14 (stranspose @[1,2,0] t329))))) (tpair (rfromS (ssum @11 (str (ssum @7 (str (w279 * w317)))))) (rfromS (ssum @11 (ssum @7 (stranspose @[1,2,0] t316)))))) (tpair (tpair (rfromS (str (m300 * m308))) (rfromS (ssum @7 (str m307)))) (tpair (rfromS (ssum @7 (stranspose @[2,1,0] (t305 * sreplicate @5 (sfromR dret))))) (rfromS (ssum @7 (str (sfromR dret))))))"
-- TODO: different test result with GHC 9.10:   printArtifactPretty (simplifyArtifact artifactRev)
--    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let u247 = sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i397, i398] -> [i397 + i398]))) (\\[i245, i246] -> [i245 + i246]) ; t249 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] u247))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; w259 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i250, i251, i252, i253, i254] -> [ifH (sscalar -0.0 <=. negate (t249 !$ [i250, 2 * i251 + i253, 2 * i252 + i254])) 0 1]) ; u261 = sreshape @[4,7,11,4] (w259 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t249) (\\[i255, i256, i257, i258] -> [2 * i255 + i257, 2 * i256 + i258]))) ; w269 = sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u261))))))) (\\[i380, i382, i383] -> [kfromS (smaxIndex (u261 !$ [i383, i380, i382])), i382, i380, i383]))) (\\[i388, i390] -> [i388, i390, i388 + i390]))) (\\[i267, i268] -> [i267, i267 + i268, i268]) ; t270 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (sreplicate @4 (stranspose @[2,0,3,4,1] w269) * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; w280 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i271, i272, i273, i274, i275] -> [ifH (sscalar -0.0 <=. negate (t270 !$ [i271, 2 * i272 + i274, 2 * i273 + i275])) 0 1]) ; u282 = sreshape @[4,3,5,4] (w280 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t270) (\\[i276, i277, i278, i279] -> [2 * i276 + i278, 2 * i277 + i279]))) ; v286 = sreshape @[60] (sgather u282 (\\[i283, i284, i285] -> [i283, i284, i285, kfromS (smaxIndex (u282 !$ [i283, i284, i285]))])) ; m287 = str (sreplicate @7 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @5 v286))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m290 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i288, i289] -> [ifH (sscalar -0.0 <=. negate (m287 !$ [i288, i289])) 0 1]) ; m293 = m290 * smatmul2 (str (sfromR (tproject1 (tproject2 (tproject2 u1))))) (sfromR dret) ; v294 = ssum @7 (str m293) ; t302 = sscatter (stranspose @[1,2,3,4,0] w280 * stranspose @[1,2,3,4,0] (sreshape @[4,3,5,2,2] (sscatter (sreshape @[4,3,5] (sdot1In (str (sfromR (tproject1 (tproject1 (tproject2 u1))))) (sreplicate @60 v294))) (\\[i295, i296, i297] -> [i295, i296, i297, kfromS (smaxIndex (u282 !$ [i295, i296, i297]))])))) (\\[i298, i299, i300, i301] -> [2 * i298 + i300, 2 * i299 + i301]) ; w303 = sreshape @[4,7,11,4,3,4] (stranspose @[1,2,3,0] (sreplicate @48 (stranspose @[2,0,1] t302))) ; t315 = sscatter (stranspose @[1,2,3,4,0] w259 * stranspose @[1,2,3,4,0] (sreshape @[4,7,11,2,2] (ssum @4 (ssum @7 (ssum @11 (ssum @3 (stranspose @[7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,5,4,6,0,3,1] (sscatter (stranspose @[3,5,0,4,1,2] (sscatter (sdot1In (stranspose @[2,5,0,3,4,1] (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))) (stranspose @[2,5,1,3,4,0] w303)) (\\[i304, i305] -> [i304, i304 + i305, i305]))) (\\[i306, i307] -> [i306, i307, i306 + i307]))) (\\[i308, i309, i310] -> [kfromS (smaxIndex (u261 !$ [i310, i308, i309])), i309, i308, i310]))))))))) (\\[i311, i312, i313, i314] -> [2 * i311 + i313, 2 * i312 + i314]) in tpair (tpair (tpair (str (sreplicate @1 (ssum @23 (sdot1In (stranspose @[4,0,3,2,1] (sreplicate @4 (stranspose @[2,1,3,0] u247))) (stranspose @[3,4,2,0,5,6,1] (sreshape @[4,14,23,1,1,3,4] (stranspose @[1,2,3,0] (sreplicate @12 (stranspose @[2,0,1] t315)))) !$ [0, 0]))))) (ssum @23 (ssum @14 t315))) (tpair (ssum @11 (sdot1In (stranspose @[2,0,3,4,5,1] (sreplicate @4 (stranspose @[2,0,3,4,1] w269))) (stranspose @[2,0,3,4,5,1] w303))) (ssum @11 (ssum @7 t302)))) (tpair (tpair (sreplicate @5 v286 * str (sreplicate @60 v294)) (ssum @7 (str m293))) (tpair (smatmul2 (sfromR dret) (str m290 * str m287)) (ssum @7 (str (sfromR dret))))))"

testCNNOAst2 :: Assertion
testCNNOAst2 = do
  let batch_size = 7
      sizeMnistWidthI = 14
      sizeMnistHeightI = 23
      ftk = tftk @Concrete
                 (knownSTK @(X (MnistCnnRanked2.ADCnnMnistParameters
                                  Concrete Double)))
                 vals
      varName = mkAstVarName ftk Nothing . intToAstVarId $ 100000000
      var :: AstTensor AstMethodLet FullSpan
                       (X (MnistCnnRanked2.ADCnnMnistParameters
                             Concrete Double))
      var = AstVar varName
      valsInit :: MnistCnnRanked2.ADCnnMnistParameters Concrete Double
      valsInit =
        forgetShape $ fst
        $ randomValue @(MnistCnnRanked2.ADCnnMnistParametersShaped
                         Concrete 14 23  -- see sizeMnistWidthI, etc.
                         2 3 4 5 Double)
                      0.4 (mkStdGen 44)
      vals = toTarget @Concrete valsInit
      env = extendEnv varName vals emptyEnv
      blackGlyph = treplicate (SNat @7) knownSTK
                   $ treplicate (SNat @1) knownSTK
                   $ treplicate (SNat @14) knownSTK
                   $ treplicate (SNat @23) knownSTK $ rscalar 7
      afcnn2 :: ADReady f
             => MnistCnnRanked2.ADCnnMnistParameters f Double
             -> f (TKR 2 Double)
      afcnn2 = MnistCnnRanked2.convMnistTwoR
                 sizeMnistHeightI sizeMnistWidthI batch_size
                 (rconcrete $ unConcrete blackGlyph)
      afcnn1 = afcnn2 $ fromTarget var
  interpretAstFull @Concrete env afcnn1
    @?= afcnn2 valsInit
  interpretAstFull @Concrete env
                   (simplifyInline @(TKR 2 Double) afcnn1)
    @?= afcnn2 valsInit
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 2 Double) afcnn1)
    @?= afcnn2 valsInit

testCNNOPP2S :: Assertion
testCNNOPP2S = do
  resetVarCounter
  let batch_size = SNat @7
      sizeMnistWidthI = SNat @14
      sizeMnistHeightI = SNat @23
      ftk = tftk @Concrete
                 (knownSTK @(X (MnistCnnShaped2.ADCnnMnistParametersShaped
                                  Concrete 14 23 2 3 4 5 Double)))
                 vals
      valsInit :: MnistCnnShaped2.ADCnnMnistParametersShaped Concrete 14 23 2 3 4 5 Double
      valsInit =
        fst
        $ randomValue @(MnistCnnShaped2.ADCnnMnistParametersShaped
                         Concrete 14 23  -- see sizeMnistWidthI, etc.
                         2 3 4 5 Double)
                      0.4 (mkStdGen 44)
      vals = toTarget @Concrete valsInit
      blackGlyph = treplicate batch_size knownSTK
                   $ treplicate (SNat @1) knownSTK
                   $ treplicate sizeMnistWidthI knownSTK
                   $ treplicate sizeMnistHeightI knownSTK $ sscalar 7
      afcnn2 :: ADReady f
             => MnistCnnShaped2.ADCnnMnistParametersShaped f 14 23 2 3 4 5 Double
             -> f (TKS '[SizeMnistLabel, 7] Double)
      afcnn2 = MnistCnnShaped2.convMnistTwoS
                 (SNat @2) (SNat @3) sizeMnistWidthI sizeMnistHeightI
                 (SNat @4) (SNat @5) batch_size
                 (sconcrete $ unConcrete blackGlyph)
      artifactRev = revArtifactAdapt UseIncomingCotangent afcnn2 ftk
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\u1 -> let t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i473, i474] -> [i473 + i474]))) (\\[i251, i252] -> [i251 + i252]))))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; u271 = sreshape @[4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [ifH (sscalar -0.0 <=. negate (t255 !$ [i258, kfromS (sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) !$ [i259, i261]), kfromS (sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) !$ [i260, i262])])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [kfromS (sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) !$ [i265, i267]), kfromS (sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) !$ [i266, i268])]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i458, i460, i461] -> [kfromS (smaxIndex (u271 !$ [i461, i458, i460])), i460, i458, i461]))) (\\[i466, i468] -> [i466, i468, i466 + i468]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; u296 = sreshape @[4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [ifH (sscalar -0.0 <=. negate (t280 !$ [i283, kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i284, i286]), kfromS (sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) !$ [i285, i287])])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i290, i292]), kfromS (sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) !$ [i291, i293])]))) ; m301 = str (sreplicate @7 (sdot1In (tproject1 (tproject1 (tproject2 u1))) (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (u296 !$ [i297, i298, i299]))])))))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) in smatmul2 (tproject1 (tproject2 (tproject2 u1))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar -0.0 <=. negate (m301 !$ [i302, i303])) 0 1]) * m301) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w253 = sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i249, i250] -> [i249 + i250]))) (\\[i251, i252] -> [i251 + i252]))))))) ; w254 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))) ; t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (w253 * w254))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; w269 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let x263 = m256 !$ [i259, i261] ; x264 = m257 !$ [i260, i262] in ifH (sscalar -0.0 <=. negate (t255 !$ [i258, kfromS x263, kfromS x264])) 0 1]) ; w270 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [kfromS (m256 !$ [i265, i267]), kfromS (m257 !$ [i266, i268])])) ; u271 = sreshape @[4,7,11,4] (w269 * w270) ; w279 = sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i272, i273, i274] -> [kfromS (smaxIndex (u271 !$ [i274, i272, i273])), i273, i272, i274]))) (\\[i275, i276] -> [i275, i276, i275 + i276]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (w279 * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; m281 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m282 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; w294 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [let x288 = m281 !$ [i284, i286] ; x289 = m282 !$ [i285, i287] in ifH (sscalar -0.0 <=. negate (t280 !$ [i283, kfromS x288, kfromS x289])) 0 1]) ; w295 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [kfromS (m281 !$ [i290, i292]), kfromS (m282 !$ [i291, i293])])) ; u296 = sreshape @[4,3,5,4] (w294 * w295) ; m300 = str (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (u296 !$ [i297, i298, i299]))])))) ; m301 = str (sreplicate @7 (ssum @60 (str (tproject1 (tproject1 (tproject2 u1))) * m300))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m304 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar -0.0 <=. negate (m301 !$ [i302, i303])) 0 1]) ; t305 = str (sreplicate @10 (m304 * m301)) in ssum @5 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * t305) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w253 = sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i249, i250] -> [i249 + i250]))) (\\[i251, i252] -> [i251 + i252]))))))) ; w254 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))) ; t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (w253 * w254))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; w269 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let x263 = m256 !$ [i259, i261] ; x264 = m257 !$ [i260, i262] in ifH (sscalar -0.0 <=. negate (t255 !$ [i258, kfromS x263, kfromS x264])) 0 1]) ; w270 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [kfromS (m256 !$ [i265, i267]), kfromS (m257 !$ [i266, i268])])) ; u271 = sreshape @[4,7,11,4] (w269 * w270) ; w279 = sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i272, i273, i274] -> [kfromS (smaxIndex (u271 !$ [i274, i272, i273])), i273, i272, i274]))) (\\[i275, i276] -> [i275, i276, i275 + i276]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (w279 * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; m281 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m282 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; w294 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [let x288 = m281 !$ [i284, i286] ; x289 = m282 !$ [i285, i287] in ifH (sscalar -0.0 <=. negate (t280 !$ [i283, kfromS x288, kfromS x289])) 0 1]) ; w295 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [kfromS (m281 !$ [i290, i292]), kfromS (m282 !$ [i291, i293])])) ; u296 = sreshape @[4,3,5,4] (w294 * w295) ; m300 = str (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (u296 !$ [i297, i298, i299]))])))) ; m301 = str (sreplicate @7 (ssum @60 (str (tproject1 (tproject1 (tproject2 u1))) * m300))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m304 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar -0.0 <=. negate (m301 !$ [i302, i303])) 0 1]) ; t305 = str (sreplicate @10 (m304 * m301)) ; m307 = m304 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * sreplicate @5 dret)) ; m308 = sreplicate @60 (ssum @7 (str m307)) ; t316 = stranspose @[2,0,1] (sscatter (stranspose @[1,2,3,4,0] (w294 * sreshape @[4,3,5,2,2] (sscatter (sreshape @[4,3,5] (ssum @5 (str (str (tproject1 (tproject1 (tproject2 u1))) * m308)))) (\\[i309, i310, i311] -> [i309, i310, i311, kfromS (smaxIndex (u296 !$ [i309, i310, i311]))])))) (\\[i312, i313, i314, i315] -> [kfromS (m281 !$ [i312, i314]), kfromS (m282 !$ [i313, i315])])) ; w317 = sreshape @[4,7,11,4,3,4] (stranspose @[1,2,3,0] (sreplicate @48 t316)) ; t329 = stranspose @[2,0,1] (sscatter (stranspose @[1,2,3,4,0] (w269 * sreshape @[4,7,11,2,2] (stranspose @[3,2,1,0] (ssum @4 (ssum @7 (ssum @11 (stranspose @[4,5,6,3,2,1,0] (ssum @3 (stranspose @[7,3,2,1,0,6,5,4] (sscatter (stranspose @[2,5,4,6,0,3,1] (sscatter (stranspose @[3,5,0,4,1,2] (sscatter (stranspose @[1,4,0,2,3] (ssum @4 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))) * w317))) (\\[i318, i319] -> [i318, i318 + i319, i319]))) (\\[i320, i321] -> [i320, i321, i320 + i321]))) (\\[i322, i323, i324] -> [kfromS (smaxIndex (u271 !$ [i324, i322, i323])), i323, i322, i324]))))))))))) (\\[i325, i326, i327, i328] -> [kfromS (m256 !$ [i325, i327]), kfromS (m257 !$ [i326, i328])])) in tpair (tpair (tpair (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (w253 * sreshape @[4,14,23,1,1,3,4] (stranspose @[1,2,3,0] (sreplicate @12 t329))))))))))) [0])) (ssum @23 (ssum @14 (stranspose @[1,2,0] t329)))) (tpair (ssum @11 (str (ssum @7 (str (w279 * w317))))) (ssum @11 (ssum @7 (stranspose @[1,2,0] t316))))) (tpair (tpair (str (m300 * m308)) (ssum @7 (str m307))) (tpair (ssum @7 (stranspose @[2,1,0] (t305 * sreplicate @5 dret))) (ssum @7 (str dret))))"
-- TODO: different test result with GHC 9.10: printArtifactPretty (simplifyArtifact artifactRev)
--    @?= "\\dret u1 -> let u247 = sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i397, i398] -> [i397 + i398]))) (\\[i245, i246] -> [i245 + i246]) ; t249 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] u247))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; w259 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i250, i251, i252, i253, i254] -> [ifH (sscalar -0.0 <=. negate (t249 !$ [i250, 2 * i251 + i253, 2 * i252 + i254])) 0 1]) ; u261 = sreshape @[4,7,11,4] (w259 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t249) (\\[i255, i256, i257, i258] -> [2 * i255 + i257, 2 * i256 + i258]))) ; w269 = sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u261))))))) (\\[i380, i382, i383] -> [kfromS (smaxIndex (u261 !$ [i383, i380, i382])), i382, i380, i383]))) (\\[i388, i390] -> [i388, i390, i388 + i390]))) (\\[i267, i268] -> [i267, i267 + i268, i268]) ; t270 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (sreplicate @4 (stranspose @[2,0,3,4,1] w269) * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; w280 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i271, i272, i273, i274, i275] -> [ifH (sscalar -0.0 <=. negate (t270 !$ [i271, 2 * i272 + i274, 2 * i273 + i275])) 0 1]) ; u282 = sreshape @[4,3,5,4] (w280 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t270) (\\[i276, i277, i278, i279] -> [2 * i276 + i278, 2 * i277 + i279]))) ; v286 = sreshape @[60] (sgather u282 (\\[i283, i284, i285] -> [i283, i284, i285, kfromS (smaxIndex (u282 !$ [i283, i284, i285]))])) ; m287 = str (sreplicate @7 (sdot1In (tproject1 (tproject1 (tproject2 u1))) (sreplicate @5 v286))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m290 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i288, i289] -> [ifH (sscalar -0.0 <=. negate (m287 !$ [i288, i289])) 0 1]) ; m293 = m290 * smatmul2 (str (tproject1 (tproject2 (tproject2 u1)))) dret ; v294 = ssum @7 (str m293) ; t302 = sscatter (stranspose @[1,2,3,4,0] w280 * stranspose @[1,2,3,4,0] (sreshape @[4,3,5,2,2] (sscatter (sreshape @[4,3,5] (sdot1In (str (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @60 v294))) (\\[i295, i296, i297] -> [i295, i296, i297, kfromS (smaxIndex (u282 !$ [i295, i296, i297]))])))) (\\[i298, i299, i300, i301] -> [2 * i298 + i300, 2 * i299 + i301]) ; w303 = sreshape @[4,7,11,4,3,4] (stranspose @[1,2,3,0] (sreplicate @48 (stranspose @[2,0,1] t302))) ; t315 = sscatter (stranspose @[1,2,3,4,0] w259 * stranspose @[1,2,3,4,0] (sreshape @[4,7,11,2,2] (ssum @4 (ssum @7 (ssum @11 (ssum @3 (stranspose @[7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,5,4,6,0,3,1] (sscatter (stranspose @[3,5,0,4,1,2] (sscatter (sdot1In (stranspose @[2,5,0,3,4,1] (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))) (stranspose @[2,5,1,3,4,0] w303)) (\\[i304, i305] -> [i304, i304 + i305, i305]))) (\\[i306, i307] -> [i306, i307, i306 + i307]))) (\\[i308, i309, i310] -> [kfromS (smaxIndex (u261 !$ [i310, i308, i309])), i309, i308, i310]))))))))) (\\[i311, i312, i313, i314] -> [2 * i311 + i313, 2 * i312 + i314]) in tpair (tpair (tpair (str (sreplicate @1 (ssum @23 (sdot1In (stranspose @[4,0,3,2,1] (sreplicate @4 (stranspose @[2,1,3,0] u247))) (stranspose @[3,4,2,0,5,6,1] (sreshape @[4,14,23,1,1,3,4] (stranspose @[1,2,3,0] (sreplicate @12 (stranspose @[2,0,1] t315)))) !$ [0, 0]))))) (ssum @23 (ssum @14 t315))) (tpair (ssum @11 (sdot1In (stranspose @[2,0,3,4,5,1] (sreplicate @4 (stranspose @[2,0,3,4,1] w269))) (stranspose @[2,0,3,4,5,1] w303))) (ssum @11 (ssum @7 t302)))) (tpair (tpair (sreplicate @5 v286 * str (sreplicate @60 v294)) (ssum @7 (str m293))) (tpair (smatmul2 dret (str m290 * str m287)) (ssum @7 (str dret))))"
