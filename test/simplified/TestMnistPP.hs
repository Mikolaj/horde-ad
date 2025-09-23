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
    @?= "\\v1 -> rfromS (let v7 = sfromVector (fromList [sscalar 7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sscalar 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sscalar 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v8 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v7, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v7, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v7, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v7]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v8, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v8, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v8, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v8, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v8, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v8, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v8, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v8, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v8, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v8]) + tproject2 (tproject2 v1))"
  printArtifactPrimalPretty artifactRev
    @?= "\\v1 -> let x4 = ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) ; x5 = ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) ; x6 = ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) ; v7 = sfromVector (fromList [sscalar 7.0 * x4, sscalar 7.0 * x5, sscalar 7.0 * x6]) + tproject2 (tproject1 (tproject1 v1)) ; v8 = sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v7), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v7), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v7), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v7)]) + tproject2 (tproject2 (tproject1 v1)) in rfromS (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v8), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v8), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v8), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v8), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v8), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v8), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v8), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v8), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v8)]) + tproject2 (tproject2 v1))"
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> let x4 = ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) ; x5 = ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) ; x6 = ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) ; v7 = sfromVector (fromList [sscalar 7.0 * x4, sscalar 7.0 * x5, sscalar 7.0 * x6]) + tproject2 (tproject1 (tproject1 v1)) ; v8 = sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v7), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v7), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v7), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v7)]) + tproject2 (tproject2 (tproject1 v1)) ; v10 = sreplicate @4 (sfromR dret !$ [9]) ; v11 = sreplicate @4 (sfromR dret !$ [8]) ; v12 = sreplicate @4 (sfromR dret !$ [7]) ; v13 = sreplicate @4 (sfromR dret !$ [6]) ; v14 = sreplicate @4 (sfromR dret !$ [5]) ; v15 = sreplicate @4 (sfromR dret !$ [4]) ; v16 = sreplicate @4 (sfromR dret !$ [3]) ; v17 = sreplicate @4 (sfromR dret !$ [2]) ; v18 = sreplicate @4 (sfromR dret !$ [1]) ; v19 = sreplicate @4 (sfromR dret !$ [0]) ; v20 = tproject1 (tproject1 (tproject2 v1)) * v19 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v18 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v17 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v16 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v15 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v11 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v10)))))))) ; v21 = sreplicate @3 (v20 !$ [3]) ; v22 = sreplicate @3 (v20 !$ [2]) ; v23 = sreplicate @3 (v20 !$ [1]) ; v24 = sreplicate @3 (v20 !$ [0]) ; v25 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v24 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v23 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v22 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v21)) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v25 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v25 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v25 !$ [2])) Z1))) v25) (tpair (tpair (v7 * v24) (tpair (v7 * v23) (tpair (v7 * v22) (tpair (v7 * v21) Z1)))) v20)) (tpair (tpair (v8 * v19) (tpair (v8 * v18) (tpair (v8 * v17) (tpair (v8 * v16) (tpair (v8 * v15) (tpair (v8 * v14) (tpair (v8 * v13) (tpair (v8 * v12) (tpair (v8 * v11) (tpair (v8 * v10) Z1)))))))))) (sfromR dret))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> let v7 = sfromVector (fromList [sscalar 7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sscalar 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sscalar 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v8 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v7, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v7, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v7, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v7]) + tproject2 (tproject2 (tproject1 v1)) ; x10 = sfromR dret !$ [9] ; x11 = sfromR dret !$ [8] ; x12 = sfromR dret !$ [7] ; x13 = sfromR dret !$ [6] ; x14 = sfromR dret !$ [5] ; x15 = sfromR dret !$ [4] ; x16 = sfromR dret !$ [3] ; x17 = sfromR dret !$ [2] ; x18 = sfromR dret !$ [1] ; x19 = sfromR dret !$ [0] ; v20 = tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x19 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x18 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x17 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x16 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x15 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x11 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x10)))))))) ; x21 = v20 !$ [3] ; x22 = v20 !$ [2] ; x23 = v20 !$ [1] ; x24 = v20 !$ [0] ; v25 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x24 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x23 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x22 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x21)) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v25 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v25 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v25 !$ [2])) Z1))) v25) (tpair (tpair (v7 * sreplicate @3 x24) (tpair (v7 * sreplicate @3 x23) (tpair (v7 * sreplicate @3 x22) (tpair (v7 * sreplicate @3 x21) Z1)))) v20)) (tpair (tpair (v8 * sreplicate @4 x19) (tpair (v8 * sreplicate @4 x18) (tpair (v8 * sreplicate @4 x17) (tpair (v8 * sreplicate @4 x16) (tpair (v8 * sreplicate @4 x15) (tpair (v8 * sreplicate @4 x14) (tpair (v8 * sreplicate @4 x13) (tpair (v8 * sreplicate @4 x12) (tpair (v8 * sreplicate @4 x11) (tpair (v8 * sreplicate @4 x10) Z1)))))))))) (sfromR dret))"

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
    @?= "\\v1 -> rfromS (let v18 = scast (recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [sscalar 7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sscalar 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sscalar 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1)))))) ; v22 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v18, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v18, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v18, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v18]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v25 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v22, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v22]) + tproject2 (tproject2 v1)) in sreplicate @10 (recip (ssum0 v25)) * v25)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\v1 -> let x9 = ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) ; x10 = ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) ; x11 = ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) ; v12 = sfromVector (fromList [sscalar 7.0 * x9, sscalar 7.0 * x10, sscalar 7.0 * x11]) + tproject2 (tproject1 (tproject1 v1)) ; v13 = exp (negate v12) ; v14 = sconcrete (sreplicate [3] 1.0) + v13 ; v15 = recip v14 ; v18 = scast v15 ; v19 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v18), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v18), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v18), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)])) + tproject2 (tproject2 (tproject1 v1)) ; v20 = exp (negate v19) ; v21 = sconcrete (sreplicate [4] 1.0) + v20 ; v22 = recip v21 ; v25 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v22), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v22)]) + tproject2 (tproject2 v1)) ; x26 = ssum @10 v25 ; v27 = sreplicate @10 (recip x26) in rfromS (v27 * v25)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret v1 -> let x9 = ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) ; x10 = ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) ; x11 = ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) ; v12 = sfromVector (fromList [sscalar 7.0 * x9, sscalar 7.0 * x10, sscalar 7.0 * x11]) + tproject2 (tproject1 (tproject1 v1)) ; v13 = exp (negate v12) ; v14 = sconcrete (sreplicate [3] 1.0) + v13 ; v15 = recip v14 ; v16 = sconcrete (sreplicate [3] 1.0) + negate v15 ; v17 = v15 * v16 ; v18 = scast v15 ; v19 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v18), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v18), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v18), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)])) + tproject2 (tproject2 (tproject1 v1)) ; v20 = exp (negate v19) ; v21 = sconcrete (sreplicate [4] 1.0) + v20 ; v22 = recip v21 ; v23 = sconcrete (sreplicate [4] 1.0) + negate v22 ; v24 = v22 * v23 ; v25 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v22), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v22)]) + tproject2 (tproject2 v1)) ; x26 = ssum @10 v25 ; v27 = sreplicate @10 (recip x26) ; v29 = v25 * (sreplicate @10 (negate (recip (x26 * x26)) * ssum @10 (v25 * sfromR dret)) + v27 * sfromR dret) ; v30 = sreplicate @4 (v29 !$ [9]) ; v31 = sreplicate @4 (v29 !$ [8]) ; v32 = sreplicate @4 (v29 !$ [7]) ; v33 = sreplicate @4 (v29 !$ [6]) ; v34 = sreplicate @4 (v29 !$ [5]) ; v35 = sreplicate @4 (v29 !$ [4]) ; v36 = sreplicate @4 (v29 !$ [3]) ; v37 = sreplicate @4 (v29 !$ [2]) ; v38 = sreplicate @4 (v29 !$ [1]) ; v39 = sreplicate @4 (v29 !$ [0]) ; v40 = v24 * (tproject1 (tproject1 (tproject2 v1)) * v39 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v38 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v37 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v36 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v35 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v31 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v30))))))))) ; v41 = scast v40 ; v42 = sreplicate @3 (v41 !$ [3]) ; v43 = sreplicate @3 (v41 !$ [2]) ; v44 = sreplicate @3 (v41 !$ [1]) ; v45 = sreplicate @3 (v41 !$ [0]) ; v46 = v17 * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v45 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v44 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v43 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v42))) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v46 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v46 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v46 !$ [2])) Z1))) v46) (tpair (tpair (v18 * v45) (tpair (v18 * v44) (tpair (v18 * v43) (tpair (v18 * v42) Z1)))) v40)) (tpair (tpair (v22 * v39) (tpair (v22 * v38) (tpair (v22 * v37) (tpair (v22 * v36) (tpair (v22 * v35) (tpair (v22 * v34) (tpair (v22 * v33) (tpair (v22 * v32) (tpair (v22 * v31) (tpair (v22 * v30) Z1)))))))))) v29)"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret v1 -> let v15 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [sscalar 7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sscalar 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sscalar 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1))))) ; v18 = scast v15 ; v22 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v18, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v18, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v18, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v18]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v25 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v22, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v22]) + tproject2 (tproject2 v1)) ; x26 = ssum0 v25 ; v29 = v25 * (sreplicate @10 (negate (recip (x26 * x26)) * sdot0 v25 (sfromR dret)) + sreplicate @10 (recip x26) * sfromR dret) ; x30 = v29 !$ [9] ; x31 = v29 !$ [8] ; x32 = v29 !$ [7] ; x33 = v29 !$ [6] ; x34 = v29 !$ [5] ; x35 = v29 !$ [4] ; x36 = v29 !$ [3] ; x37 = v29 !$ [2] ; x38 = v29 !$ [1] ; x39 = v29 !$ [0] ; v40 = (v22 * (sconcrete (sreplicate [4] 1.0) + negate v22)) * (tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x39 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x38 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x37 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x36 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x35 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x31 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x30))))))))) ; v41 = scast v40 ; x42 = v41 !$ [3] ; x43 = v41 !$ [2] ; x44 = v41 !$ [1] ; x45 = v41 !$ [0] ; v46 = (v15 * (sconcrete (sreplicate [3] 1.0) + negate v15)) * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x45 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x44 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x43 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x42))) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v46 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v46 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v46 !$ [2])) Z1))) v46) (tpair (tpair (v18 * sreplicate @3 x45) (tpair (v18 * sreplicate @3 x44) (tpair (v18 * sreplicate @3 x43) (tpair (v18 * sreplicate @3 x42) Z1)))) v40)) (tpair (tpair (v22 * sreplicate @4 x39) (tpair (v22 * sreplicate @4 x38) (tpair (v22 * sreplicate @4 x37) (tpair (v22 * sreplicate @4 x36) (tpair (v22 * sreplicate @4 x35) (tpair (v22 * sreplicate @4 x34) (tpair (v22 * sreplicate @4 x33) (tpair (v22 * sreplicate @4 x32) (tpair (v22 * sreplicate @4 x31) (tpair (v22 * sreplicate @4 x30) Z1)))))))))) v29)"

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
    @?= "\\m1 -> let v5 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; m6 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 7.0) * v5 + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m7 = str (sreplicate @2 (scast (ssum @4 (m6 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in rfromS (ssum @5 (m7 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1)))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v5 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; m6 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 7.0) * v5 + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m7 = str (sreplicate @2 (scast (ssum @4 (m6 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v9 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m10 = sreplicate @4 (scast v9) ; v11 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m10))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v11)))) (rfromS v11)) (tpair (rfromS (str (m6 * m10))) (rfromS v9))) (tpair (rfromS (str (m7 * sreplicate @5 (sfromR dret)))) dret)"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v5 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; m6 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 7.0) * v5 + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m7 = str (sreplicate @2 (scast (ssum @4 (m6 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v9 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m10 = sreplicate @4 (scast v9) ; v11 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m10))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v11)))) (rfromS v11)) (tpair (rfromS (str (m6 * m10))) (rfromS v9))) (tpair (rfromS (str (m7 * sreplicate @5 (sfromR dret)))) dret)"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4,3] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4] FTKScalar)) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5,4] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5] FTKScalar)) ConvSX)))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2,5] FTKScalar)) ConvSX)) ConvId)) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKR (SNat @1) STKScalar))) (let v6 = scast (sconcrete (sreplicate [4] 7.0) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; v9 = sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 (sfromR dret)) ; v10 = scast v9 ; v11 = scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v10)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v11))) v11) (tpair (sreplicate @5 v6 * str (sreplicate @4 v10)) v9)) (tpair (sreplicate @2 (scast (sdot1In (sreplicate @5 v6) (sfromR (tproject1 (tproject2 (tproject1 m1))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @5 (sfromR dret))) dret))"

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
    @?= "\\dummy -> rfromS (tlet (exp (ssum @5 (str (sreplicate @2 (tlet (ssum @4 (tfromPlain (STKS [4,5] STKScalar) (sconcrete (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0])) * str (sreplicate @5 (tlet (tfromPlain (STKS [4] STKScalar) (sconcrete (sreplicate [4] 7.0) * ssum @3 (str (scast (sconcrete (sfromListLinear [4,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0])))) + scast (sconcrete (sfromListLinear [4] [1.0,2.0,3.0,4.0])))) (\\v5 -> ttletPrimal (recip (tfromPlain (STKS [4] STKScalar) (sconcrete (sreplicate [4] 1.0)) + exp (negate (sfromR (tprimalPart (rfromS v5)))))) (\\v6 -> tfromPrimal (STKS [4] STKScalar) v6 + sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [4] STKScalar) (v6 * (tfromPlain (STKS [4] STKScalar) (sconcrete (sreplicate [4] 1.0)) + negate v6)) * sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v5)))))))))))) + tfromPlain (STKS [5] STKScalar) (scast (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v7 -> ttletPrimal (recip (tfromPlain (STKS [5] STKScalar) (sconcrete (sreplicate [5] 1.0)) + exp (negate (sfromR (tprimalPart (rfromS v7)))))) (\\v8 -> tfromPrimal (STKS [5] STKScalar) v8 + sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [5] STKScalar) (v8 * (tfromPlain (STKS [5] STKScalar) (sconcrete (sreplicate [5] 1.0)) + negate v8)) * sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v7))))))))))) * tfromPlain (STKS [5,2] STKScalar) (str (scast (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))))) + tfromPlain (STKS [2] STKScalar) (scast (sconcrete (sfromListLinear [2] [1.0,2.0]))))) (\\v9 -> sreplicate @2 (recip (ssum @2 v9)) * v9))"
  "\\dummy" ++ " -> " ++ printAstSimple (simplifyInlineContract ast3)
    @?= "\\dummy -> rfromS (tlet (exp (tfromPlain (STKS [2] STKScalar) (sconcrete (sfromListLinear [2] [1.0,2.0])) + sdot1In (sreplicate @2 (tlet (tfromPlain (STKS [5] STKScalar) (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])) + sdot1In (tfromPlain (STKS [5,4] STKScalar) (sconcrete (sfromListLinear [5,4] [1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0]))) (sreplicate @5 (ttletPrimal (recip (tfromPlain (STKS [4] STKScalar) (sconcrete (sreplicate [4] 1.0)) + exp (tfromPlain (STKS [4] STKScalar) (sconcrete (sfromListLinear [4] [-43.0,-44.0,-45.0,-46.0]))))) (\\v6 -> tfromPrimal (STKS [4] STKScalar) v6 + tfromDual (tdualPart (STKS [4] STKScalar) (tfromPrimal (STKS [4] STKScalar) (v6 * (tfromPlain (STKS [4] STKScalar) (sconcrete (sreplicate [4] 1.0)) + negate v6)) * tfromDual (tdualPart (STKS [4] STKScalar) (tfromPlain (STKS [4] STKScalar) (sconcrete (sreplicate [4] 0.0)))))))))) (\\v7 -> ttletPrimal (recip (tfromPlain (STKS [5] STKScalar) (sconcrete (sreplicate [5] 1.0)) + tprimalPart (exp (negate v7)))) (\\v8 -> tfromPrimal (STKS [5] STKScalar) v8 + tfromDual (tdualPart (STKS [5] STKScalar) (tfromPrimal (STKS [5] STKScalar) (v8 * (tfromPlain (STKS [5] STKScalar) (sconcrete (sreplicate [5] 1.0)) + negate v8)) * tfromDual (tdualPart (STKS [5] STKScalar) v7))))))) (tfromPlain (STKS [2,5] STKScalar) (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))))) (\\v9 -> sreplicate @2 (recip (ssum0 v9)) * v9))"

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
    @?= "\\m1 -> rfromS (let v24 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (scast (recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in sreplicate @2 (recip (ssum0 v24)) * v24)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = sconcrete (sreplicate [4] 1.0) + v12 ; v14 = recip v13 ; m17 = str (sreplicate @5 (scast v14)) ; v18 = scast (ssum @4 (m17 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v19 = exp (negate v18) ; v20 = sconcrete (sreplicate [5] 1.0) + v19 ; v21 = recip v20 ; v24 = exp (ssum @5 (str (sreplicate @2 v21) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) in rfromS (v26 * v24)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = sconcrete (sreplicate [4] 1.0) + v12 ; v14 = recip v13 ; v15 = sconcrete (sreplicate [4] 1.0) + negate v14 ; v16 = v14 * v15 ; m17 = str (sreplicate @5 (scast v14)) ; v18 = scast (ssum @4 (m17 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v19 = exp (negate v18) ; v20 = sconcrete (sreplicate [5] 1.0) + v19 ; v21 = recip v20 ; v22 = sconcrete (sreplicate [5] 1.0) + negate v21 ; v23 = v21 * v22 ; v24 = exp (ssum @5 (str (sreplicate @2 v21) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v28 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * ssum @2 (v24 * sfromR dret)) + v26 * sfromR dret) ; v29 = v23 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v28)) ; m30 = sreplicate @4 (scast v29) ; v31 = v16 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m30))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v31)))) (rfromS v31)) (tpair (rfromS (str (m17 * m30))) (rfromS v29))) (tpair (rfromS (str (str (sreplicate @2 v21) * sreplicate @5 v28))) (rfromS v28))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4,3] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4] FTKScalar)) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5,4] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5] FTKScalar)) ConvSX)))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2,5] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2] FTKScalar)) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v14 = recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v17 = scast v14 ; v21 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v17) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v24 = exp (sdot1In (sreplicate @2 v21) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum0 v24 ; v28 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * sdot0 v24 (sfromR dret)) + sreplicate @2 (recip x25) * sfromR dret) ; v29 = (v21 * (sconcrete (sreplicate [5] 1.0) + negate v21)) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v28) ; v30 = scast v29 ; v31 = (v14 * (sconcrete (sreplicate [4] 1.0) + negate v14)) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v30)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v31))) v31) (tpair (sreplicate @5 v17 * str (sreplicate @4 v30)) v29)) (tpair (sreplicate @2 v21 * str (sreplicate @5 v28)) v28))"

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
    @?= "\\m1 -> let v24 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (scast (recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in (-8.0) * kfromS (ssum0 (log (sreplicate @2 (recip (ssum0 v24)) * v24)))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = sconcrete (sreplicate [4] 1.0) + v12 ; v14 = recip v13 ; m17 = str (sreplicate @5 (scast v14)) ; v18 = scast (ssum @4 (m17 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v19 = exp (negate v18) ; v20 = sconcrete (sreplicate [5] 1.0) + v19 ; v21 = recip v20 ; v24 = exp (ssum @5 (str (sreplicate @2 v21) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v27 = v26 * v24 ; x28 = ssum @2 (log v27) in (-8.0) * kfromS x28"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = sconcrete (sreplicate [4] 1.0) + v12 ; v14 = recip v13 ; v15 = sconcrete (sreplicate [4] 1.0) + negate v14 ; v16 = v14 * v15 ; m17 = str (sreplicate @5 (scast v14)) ; v18 = scast (ssum @4 (m17 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v19 = exp (negate v18) ; v20 = sconcrete (sreplicate [5] 1.0) + v19 ; v21 = recip v20 ; v22 = sconcrete (sreplicate [5] 1.0) + negate v21 ; v23 = v21 * v22 ; v24 = exp (ssum @5 (str (sreplicate @2 v21) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v27 = v26 * v24 ; v30 = recip v27 * sreplicate @2 (sfromK ((-8.0) * dret)) ; v31 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * ssum @2 (v24 * v30)) + v26 * v30) ; v32 = v23 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v31)) ; m33 = sreplicate @4 (scast v32) ; v34 = v16 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m33))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v34)))) (rfromS v34)) (tpair (rfromS (str (m17 * m33))) (rfromS v32))) (tpair (rfromS (str (str (sreplicate @2 v21) * sreplicate @5 v31))) (rfromS v31))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4,3] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [4] FTKScalar)) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5,4] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [5] FTKScalar)) ConvSX)))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2,5] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2] FTKScalar)) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v14 = recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v17 = scast v14 ; v21 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v17) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v24 = exp (sdot1In (sreplicate @2 v21) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum0 v24 ; x26 = recip x25 ; v30 = recip (sreplicate @2 x26 * v24) * sreplicate @2 (sscalar (-8.0) * sfromK dret) ; v31 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * sdot0 v24 v30) + sreplicate @2 x26 * v30) ; v32 = (v21 * (sconcrete (sreplicate [5] 1.0) + negate v21)) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v31) ; v33 = scast v32 ; v34 = (v14 * (sconcrete (sreplicate [4] 1.0) + negate v14)) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v33)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v34))) v34) (tpair (sreplicate @5 v17 * str (sreplicate @4 v33)) v32)) (tpair (sreplicate @2 v21 * str (sreplicate @5 v31)) v31))"

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
    @?= "\\m1 -> let x16 = sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0] ; x17 = tanh (sscalar 7.0 * x16 + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]) ; v20 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] in rfromS (str (sreplicate @1 (v20 * sreplicate @10 x19)) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let x16 = sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0] ; x17 = tanh (sscalar 7.0 * x16 + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]) ; v20 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] ; x22 = (sscalar 1.0 + negate x19 * x19) * ssum @10 (v20 * ssum @1 (str (sfromR dret))) ; x23 = (sscalar 1.0 + negate x17 * x17) * (x18 * x22) in tpair (tpair (tpair (tpair (rfromS (soneHot (sscalar 7.0 * x23) [0, 0])) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (rfromS (soneHot x23 [0]))) (tpair (tpair (rfromS (soneHot (x17 * x22) [0, 0])) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (rfromS (soneHot x22 [0])))) (tpair (rfromS (str (soneHot (sreplicate @10 x19 * ssum @1 (str (sfromR dret))) [0]))) (rfromS (ssum @1 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1,1] FTKScalar)) ConvSX)) ConvId) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1] FTKScalar)) ConvSX))) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1,1] FTKScalar)) ConvSX)) ConvId) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [1] FTKScalar)) ConvSX)))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [10,1] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [10] FTKScalar)) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKR (SNat @2) STKScalar)) (STKS [1] STKScalar)) (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKR (SNat @2) STKScalar)) (STKS [1] STKScalar))) (STKProduct (STKS [10,1] STKScalar) (STKS [10] STKScalar))) (let x17 = tanh (sscalar 7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]) ; x22 = (sscalar 1.0 + negate x19 * x19) * sdot0 (str (sfromR (tproject1 (tproject2 m1))) !$ [0]) (str (sfromR dret) !$ [0]) ; x23 = (sscalar 1.0 + negate x17 * x17) * (x18 * x22) in tpair (tpair (tpair (tpair (sreplicate @1 (sreplicate @1 (sscalar 7.0 * x23))) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (sreplicate @1 x23)) (tpair (tpair (sreplicate @1 (sreplicate @1 (x17 * x22))) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (sreplicate @1 x22))) (tpair (str (sreplicate @1 (sreplicate @10 x19 * str (sfromR dret) !$ [0]))) (str (sfromR dret) !$ [0])))"

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
    @?= "\\m1 -> rfromS (let m42 = sappend (tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) (tanh (str (sreplicate @2 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 (tanh (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice (SNat @0) (SNat @2) m42)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m42)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let v37 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m38 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v37)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v39 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; v40 = tanh (sconcrete (sreplicate [2] 7.0) * v39 + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m41 = tanh (str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v40)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m42 = sappend m38 m41 ; v43 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m44 = tanh ((sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v43) + ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * stranspose @[2,1,0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m42))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m45 = tanh ((ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 m44)) + ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m42))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) in rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * str (sreplicate @10 m45)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v37 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m38 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v37)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v39 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; v40 = tanh (sconcrete (sreplicate [2] 7.0) * v39 + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m41 = tanh (str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v40)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m42 = sappend m38 m41 ; v43 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m44 = tanh ((sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v43) + ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * stranspose @[2,1,0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m42))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m45 = tanh ((ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 m44)) + ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m42))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m47 = (sconcrete (sreplicate [2,2] 1.0) + negate m45 * m45) * ssum @10 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @2 (sfromR dret))) ; m48 = (sconcrete (sreplicate [2,2] 1.0) + negate m44 * m44) * ssum @2 (stranspose @[1,2,0] (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m47)) ; m49 = sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (str (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * sreplicate @2 m48)))) (sconcrete (sreplicate [2,2] 0.0))) + sappend (sconcrete (sreplicate [2,2] 0.0)) (sappend (str (ssum @2 (stranspose @[1,2,0] (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m47)))) (sconcrete (sfromListLinear [0,2] []))) ; m50 = (sconcrete (sreplicate [2,2] 1.0) + negate m41 * m41) * sslice (SNat @2) (SNat @2) m49 ; m51 = sreplicate @2 (ssum @2 (str m50)) ; v52 = (sconcrete (sreplicate [2] 1.0) + negate v40 * v40) * ssum @2 (str (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * m51)) ; m53 = (sconcrete (sreplicate [2,2] 1.0) + negate m38 * m38) * sslice (SNat @0) (SNat @2) m49 in tpair (tpair (tpair (tpair (rfromS (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str m53))) + (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v52)) + str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 m48))))) (rfromS (str (ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m42))) * sreplicate @2 m48)))))) (rfromS (ssum @2 (str m53) + (v52 + ssum @2 m48)))) (tpair (tpair (rfromS (str (str (sreplicate @2 v40) * m51) + str (ssum @2 (stranspose @[2,0,1] (stranspose @[2,0,1] (sreplicate @2 m44) * sreplicate @2 m47))))) (rfromS (str (ssum @2 (stranspose @[2,0,1] (stranspose @[2,0,1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m42))) * sreplicate @2 m47)))))) (rfromS (ssum @2 (str m50) + ssum @2 (str m47))))) (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @10 m45) * sreplicate @2 (sfromR dret))))) (rfromS (ssum @2 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2,2] FTKScalar)) ConvSX))) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [2,2] FTKScalar)) ConvSX))) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [10,2] FTKScalar)) ConvSX)) (ConvCmp (ConvXR STKScalar) (ConvCmp (ConvXX' (FTKX [10] FTKScalar)) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [2,2] STKScalar) (STKS [2,2] STKScalar)) (STKS [2] STKScalar)) (STKProduct (STKProduct (STKS [2,2] STKScalar) (STKS [2,2] STKScalar)) (STKS [2] STKScalar))) (STKProduct (STKS [10,2] STKScalar) (STKS [10] STKScalar))) (let m38 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v40 = tanh (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m41 = tanh (str (sreplicate @2 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 v40))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m42 = sappend m38 m41 ; m44 = tanh ((sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) + smatmul2 (str (sslice (SNat @0) (SNat @2) m42)) (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m45 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (str m44) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m42)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m47 = (sconcrete (sreplicate [2,2] 1.0) + negate m45 * m45) * smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR dret) ; m48 = (sconcrete (sreplicate [2,2] 1.0) + negate m44 * m44) * smatmul2 (str m47) (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) ; m49 = sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) (str m48)) (sconcrete (sreplicate [2,2] 0.0)) + sappend (sconcrete (sreplicate [2,2] 0.0)) (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) m47) ; m50 = (sconcrete (sreplicate [2,2] 1.0) + negate m41 * m41) * sslice (SNat @2) (SNat @2) m49 ; v51 = ssum @2 (str m50) ; v52 = (sconcrete (sreplicate [2] 1.0) + negate v40 * v40) * sdot1In (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) (sreplicate @2 v51) ; m53 = (sconcrete (sreplicate [2,2] 1.0) + negate m38 * m38) * sslice (SNat @0) (SNat @2) m49 in tpair (tpair (tpair (tpair (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str m53))) + (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v52)) + str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 m48)))) (smatmul2 (str m48) (str (sslice (SNat @0) (SNat @2) m42)))) (ssum @2 (str m53) + (v52 + ssum @2 m48))) (tpair (tpair (sreplicate @2 v40 * str (sreplicate @2 v51) + smatmul2 m47 m44) (smatmul2 m47 (str (sslice (SNat @2) (SNat @2) m42)))) (ssum @2 (str m50) + ssum @2 (str m47)))) (tpair (smatmul2 (sfromR dret) (str m45)) (ssum @2 (str (sfromR dret)))))"

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
    @?= "\\u1 -> rfromS (let t189 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[7,9,4] (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [7,9] 7.0)) (\\[i358, i359] -> [i358 + i359]))) (\\[i185, i186] -> [i185 + i186])))))) * sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; t204 = sreshape @[3,4,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i192, i193, i194, i195] -> [ifH (sscalar (-0.0) <=. negate (splainPart t189 !$ [0, kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i192, i194]), kfromS (sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) !$ [i193, i195])])) 0 1]) * sgather (t189 !$ [0]) (\\[i198, i199, i200, i201] -> [kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i198, i200]), kfromS (sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) !$ [i199, i201])])) ; t213 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[3,4,4] (stranspose @[2,0,3,1] (sgather (stranspose @[2,3,4,0,1] (sgather (stranspose @[3,5,0,4,1,2] (sgather (stranspose @[3,2,1,6,5,4,0] (sreplicate @2 (stranspose @[5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[2,1,0] t204))))))) (\\[i346, i350] -> [kfromS (smaxIndex (splainPart t204 !$ [i346, i350])), i350, i346]))) (\\[i355, i356] -> [i355, i356, i355 + i356]))) (\\[i209, i210] -> [i209, i209 + i210, i210])) * sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])))))) + stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m223 = sreshape @[2,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i215, i216, i217] -> [ifH (sscalar (-0.0) <=. negate (splainPart t213 !$ [0, i216, kfromS (sconcrete (sfromListLinear [2,2] [0,1,2,3]) !$ [i215, i217])])) 0 1]) * stranspose @[0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (t213 !$ [0]))) (\\[i219, i220] -> [kfromS (sconcrete (sfromListLinear [2,2] [0,1,2,3]) !$ [i219, i220])]))) ; m227 = sreplicate @1 (sreplicate @5 (sdot0 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0]) (sgather m223 (\\[i224] -> [i224, kfromS (smaxIndex (splainPart m223 !$ [i224]))])))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) * sreplicate @10 (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i228] -> [ifH (sscalar (-0.0) <=. negate (splainPart m227 !$ [0, i228])) 0 1]) * m227 !$ [0]) + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w187 = splainPart (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [7,9] 7.0)) (\\[i183, i184] -> [i183 + i184]))) (\\[i185, i186] -> [i185 + i186]))))))) ; w188 = sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))) ; t189 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[7,9,4] (w187 * w188)))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m190 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m191 = str (sreplicate @2 (sconcrete (sreplicate [4] 2) * siota (SNat @4))) + sreplicate @4 (siota (SNat @2)) ; u202 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i192, i193, i194, i195] -> [let i196 = tplainPart (kfromS (m190 !$ [i192, i194])) ; i197 = tplainPart (kfromS (m191 !$ [i193, i195])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t189 !$ [0, i196, i197]))) 0 1])) ; u203 = sgather (t189 !$ [0]) (\\[i198, i199, i200, i201] -> [tplainPart (kfromS (m190 !$ [i198, i200])), tplainPart (kfromS (m191 !$ [i199, i201]))]) ; t204 = sreshape @[3,4,4] (u202 * u203) ; u211 = stranspose @[2,0,3,1] (sgather (stranspose @[2,3,4,0,1] (sgather (stranspose @[3,5,0,4,1,2] (sgather (stranspose @[3,2,1,6,5,4,0] (sreplicate @2 (stranspose @[5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[2,1,0] t204))))))) (\\[i205, i206] -> [kfromS (smaxIndex (splainPart (splainPart t204 !$ [i205, i206]))), i206, i205]))) (\\[i207, i208] -> [i207, i208, i207 + i208]))) (\\[i209, i210] -> [i209, i209 + i210, i210])) ; u212 = sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])) ; t213 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[3,4,4] (u211 * u212)))) + stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m214 = str (sreplicate @2 (sconcrete (sreplicate [2] 2) * siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) ; t221 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i215, i216, i217] -> [let i218 = tplainPart (kfromS (m214 !$ [i215, i217])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t213 !$ [0, i216, i218]))) 0 1])) ; t222 = stranspose @[0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (t213 !$ [0]))) (\\[i219, i220] -> [tplainPart (kfromS (m214 !$ [i219, i220]))])) ; m223 = sreshape @[2,4] (t221 * t222) ; v225 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v226 = sgather m223 (\\[i224] -> [i224, kfromS (smaxIndex (splainPart (splainPart m223 !$ [i224])))]) ; m227 = sreplicate @1 (sreplicate @5 (ssum @2 (v225 * v226))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v229 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i228] -> [ifH (sscalar (-0.0) <=. splainPart (negate (splainPart m227 !$ [0, i228]))) 0 1])) ; v230 = m227 !$ [0] ; m231 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m232 = sreplicate @10 (v229 * v230) in rfromS (m231 * m232 + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w187 = splainPart (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [7,9] 7.0)) (\\[i183, i184] -> [i183 + i184]))) (\\[i185, i186] -> [i185 + i186]))))))) ; w188 = sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))) ; t189 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[7,9,4] (w187 * w188)))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m190 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m191 = str (sreplicate @2 (sconcrete (sreplicate [4] 2) * siota (SNat @4))) + sreplicate @4 (siota (SNat @2)) ; u202 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i192, i193, i194, i195] -> [let i196 = tplainPart (kfromS (m190 !$ [i192, i194])) ; i197 = tplainPart (kfromS (m191 !$ [i193, i195])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t189 !$ [0, i196, i197]))) 0 1])) ; u203 = sgather (t189 !$ [0]) (\\[i198, i199, i200, i201] -> [tplainPart (kfromS (m190 !$ [i198, i200])), tplainPart (kfromS (m191 !$ [i199, i201]))]) ; t204 = sreshape @[3,4,4] (u202 * u203) ; u211 = stranspose @[2,0,3,1] (sgather (stranspose @[2,3,4,0,1] (sgather (stranspose @[3,5,0,4,1,2] (sgather (stranspose @[3,2,1,6,5,4,0] (sreplicate @2 (stranspose @[5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[2,1,0] t204))))))) (\\[i205, i206] -> [kfromS (smaxIndex (splainPart (splainPart t204 !$ [i205, i206]))), i206, i205]))) (\\[i207, i208] -> [i207, i208, i207 + i208]))) (\\[i209, i210] -> [i209, i209 + i210, i210])) ; u212 = sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])) ; t213 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[3,4,4] (u211 * u212)))) + stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m214 = str (sreplicate @2 (sconcrete (sreplicate [2] 2) * siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) ; t221 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i215, i216, i217] -> [let i218 = tplainPart (kfromS (m214 !$ [i215, i217])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t213 !$ [0, i216, i218]))) 0 1])) ; t222 = stranspose @[0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (t213 !$ [0]))) (\\[i219, i220] -> [tplainPart (kfromS (m214 !$ [i219, i220]))])) ; m223 = sreshape @[2,4] (t221 * t222) ; v225 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v226 = sgather m223 (\\[i224] -> [i224, kfromS (smaxIndex (splainPart (splainPart m223 !$ [i224])))]) ; m227 = sreplicate @1 (sreplicate @5 (ssum @2 (v225 * v226))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v229 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i228] -> [ifH (sscalar (-0.0) <=. splainPart (negate (splainPart m227 !$ [0, i228]))) 0 1])) ; v230 = m227 !$ [0] ; m231 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m232 = sreplicate @10 (v229 * v230) ; m234 = soneHot (v229 * ssum @10 (m231 * sfromR dret)) [0] ; v235 = sreplicate @2 (ssum @5 (ssum @1 m234)) ; t239 = soneHot (sappend (sconcrete (sfromListLinear [0,4] [])) (sappend (str (sscatter (stranspose @[0,2,1] (t221 * sreshape @[2,2,2] (sscatter (v225 * v235) (\\[i236] -> [i236, kfromS (smaxIndex (splainPart (splainPart m223 !$ [i236])))])))) (\\[i237, i238] -> [tplainPart (kfromS (m214 !$ [i237, i238]))]))) (sconcrete (sreplicate [1,4] 0.0)))) [0] ; u240 = sreshape @[3,4,2,2] (stranspose @[1,2,0] (sreplicate @4 (ssum @1 t239))) ; t251 = soneHot (sscatter (u202 * sreshape @[3,4,2,2] (stranspose @[2,1,0] (ssum @2 (ssum @3 (ssum @4 (stranspose @[3,4,5,2,1,0] (ssum @2 (stranspose @[6,2,1,0,5,4,3] (sscatter (stranspose @[2,4,5,0,3,1] (sscatter (stranspose @[3,4,0,1,2] (sscatter (stranspose @[1,3,0,2] (u212 * u240)) (\\[i241, i242] -> [i241, i241 + i242, i242]))) (\\[i243, i244] -> [i243, i244, i243 + i244]))) (\\[i245, i246] -> [kfromS (smaxIndex (splainPart (splainPart t204 !$ [i245, i246]))), i246, i245])))))))))) (\\[i247, i248, i249, i250] -> [tplainPart (kfromS (m190 !$ [i247, i249])), tplainPart (kfromS (m191 !$ [i248, i250]))])) [0] in tpair (tpair (tpair (rfromS (soneHot (ssum @1 (ssum @1 (ssum @9 (ssum @7 (w187 * sreshape @[7,9,1,1,2,2] (stranspose @[1,2,0] (sreplicate @4 (ssum @1 t251)))))))) [0, 0])) (rfromS (ssum @9 (ssum @7 (stranspose @[1,2,0] t251))))) (tpair (rfromS (soneHot (ssum @4 (ssum @3 (u211 * u240))) [0, 0])) (rfromS (ssum @4 (ssum @3 (stranspose @[1,2,0] t239)))))) (tpair (tpair (rfromS (soneHot (v226 * v235) [0])) (rfromS (ssum @5 (str m234)))) (tpair (rfromS (str (soneHot (ssum @5 (str (m232 * sfromR dret))) [0]))) (rfromS (ssum @5 (str (sfromR dret))))))"
-- TODO: different test result with GHC 9.10:   printArtifactPretty (simplifyArtifact artifactRev)
--    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let u181 = sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [7,9] 7.0)) (\\[i296, i297] -> [i296 + i297]))) (\\[i179, i180] -> [i179 + i180]) ; t183 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[7,9,4] (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] u181)))) * sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; u192 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i184, i185, i186, i187] -> [ifH (sscalar (-0.0) <=. negate (t183 !$ [0, 2 * i184 + i186, 2 * i185 + i187])) 0 1]) ; t194 = sreshape @[3,4,4] (u192 * sgather (t183 !$ [0]) (\\[i188, i189, i190, i191] -> [2 * i188 + i190, 2 * i189 + i191])) ; u201 = sgather (stranspose @[2,3,4,0,1] (sgather (stranspose @[3,5,0,4,1,2] (sgather (stranspose @[3,2,1,6,5,4,0] (sreplicate @2 (stranspose @[5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[2,1,0] t194))))))) (\\[i284, i288] -> [kfromS (smaxIndex (t194 !$ [i284, i288])), i288, i284]))) (\\[i293, i294] -> [i293, i294, i293 + i294]))) (\\[i199, i200] -> [i199, i199 + i200, i200]) ; m202 = sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0] ; t203 = sreplicate @1 (ssum @4 (stranspose @[2,0,1] (sreshape @[3,4,4] (stranspose @[2,0,3,1] u201 * sreplicate @3 (sreplicate @4 m202))))) + stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; t209 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i204, i205, i206] -> [ifH (sscalar (-0.0) <=. negate (t203 !$ [0, i205, 2 * i204 + i206])) 0 1]) ; m211 = sreshape @[2,4] (t209 * stranspose @[0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (t203 !$ [0]))) (\\[i207, i208] -> [2 * i207 + i208]))) ; v213 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v214 = sgather m211 (\\[i212] -> [i212, kfromS (smaxIndex (m211 !$ [i212]))]) ; m215 = sreplicate @1 (sreplicate @5 (sdot0 v213 v214)) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v217 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i216] -> [ifH (sscalar (-0.0) <=. negate (m215 !$ [0, i216])) 0 1]) ; v222 = v217 * sdot1In (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) (str (sfromR dret)) ; x223 = ssum0 v222 ; m227 = sappend (str (sscatter (stranspose @[0,2,1] t209 * stranspose @[0,2,1] (sreshape @[2,2,2] (sscatter (v213 * sreplicate @2 x223) (\\[i224] -> [i224, kfromS (smaxIndex (m211 !$ [i224]))])))) (\\[i225, i226] -> [2 * i225 + i226]))) (sconcrete (sreplicate [1,4] 0.0)) ; u228 = sreshape @[3,4,2,2] (stranspose @[1,2,0] (sreplicate @4 m227)) ; m239 = sscatter (u192 * sreshape @[3,4,2,2] (ssum @2 (ssum @3 (ssum @4 (ssum @2 (stranspose @[6,5,4,3,2,1,0] (sscatter (stranspose @[2,4,5,0,3,1] (sscatter (stranspose @[3,4,0,1,2] (sscatter (stranspose @[1,3,0,2] (sreplicate @3 (sreplicate @4 m202)) * stranspose @[1,3,0,2] u228) (\\[i229, i230] -> [i229, i229 + i230, i230]))) (\\[i231, i232] -> [i231, i232, i231 + i232]))) (\\[i233, i234] -> [kfromS (smaxIndex (t194 !$ [i233, i234])), i234, i233])))))))) (\\[i235, i236, i237, i238] -> [2 * i235 + i237, 2 * i236 + i238]) in tpair (tpair (tpair (sreplicate @1 (sreplicate @1 (ssum @9 (sdot1In (stranspose @[0,3,1,2] u181) (stranspose @[2,3,1,4,5,0] (sreshape @[7,9,1,1,2,2] (stranspose @[1,2,0] (sreplicate @4 m239))) !$ [0, 0]))))) (ssum @9 (ssum @7 (stranspose @[1,2,0] (sreplicate @1 m239))))) (tpair (sreplicate @1 (sreplicate @1 (ssum @4 (sdot1In (stranspose @[0,3,1,2] u201) (stranspose @[1,2,3,0] u228))))) (ssum @4 (ssum @3 (stranspose @[1,2,0] (sreplicate @1 m227)))))) (tpair (tpair (sreplicate @1 (v214 * sreplicate @2 x223)) (sreplicate @1 (ssum0 v222))) (tpair (str (sreplicate @1 (sdot1In (sreplicate @10 (v217 * m215 !$ [0])) (sfromR dret)))) (ssum @5 (str (sfromR dret))))))"

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
    @?= "\\u1 -> rfromS (let t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i473, i474] -> [i473 + i474]))) (\\[i251, i252] -> [i251 + i252]))))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; u271 = sreshape @[4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [ifH (sscalar (-0.0) <=. negate (splainPart t255 !$ [i258, kfromS (sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) !$ [i259, i261]), kfromS (sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) !$ [i260, i262])])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [kfromS (sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) !$ [i265, i267]), kfromS (sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) !$ [i266, i268])]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i458, i460, i461] -> [kfromS (smaxIndex (splainPart u271 !$ [i461, i458, i460])), i460, i458, i461]))) (\\[i466, i468] -> [i466, i468, i466 + i468]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; u296 = sreshape @[4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [ifH (sscalar (-0.0) <=. negate (splainPart t280 !$ [i283, kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i284, i286]), kfromS (sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) !$ [i285, i287])])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i290, i292]), kfromS (sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) !$ [i291, i293])]))) ; m301 = str (sreplicate @7 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (splainPart u296 !$ [i297, i298, i299]))])))))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in smatmul2 (sfromR (tproject1 (tproject2 (tproject2 u1)))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar (-0.0) <=. negate (splainPart m301 !$ [i302, i303])) 0 1]) * m301) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w253 = splainPart (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i249, i250] -> [i249 + i250]))) (\\[i251, i252] -> [i251 + i252])))))))) ; w254 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))) ; t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (w253 * w254))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; w269 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let i263 = tplainPart (kfromS (m256 !$ [i259, i261])) ; i264 = tplainPart (kfromS (m257 !$ [i260, i262])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t255 !$ [i258, i263, i264]))) 0 1])) ; w270 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [tplainPart (kfromS (m256 !$ [i265, i267])), tplainPart (kfromS (m257 !$ [i266, i268]))])) ; u271 = sreshape @[4,7,11,4] (w269 * w270) ; w279 = sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i272, i273, i274] -> [kfromS (smaxIndex (splainPart (splainPart u271 !$ [i274, i272, i273]))), i273, i272, i274]))) (\\[i275, i276] -> [i275, i276, i275 + i276]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (w279 * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m281 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m282 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; w294 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [let i288 = tplainPart (kfromS (m281 !$ [i284, i286])) ; i289 = tplainPart (kfromS (m282 !$ [i285, i287])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t280 !$ [i283, i288, i289]))) 0 1])) ; w295 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [tplainPart (kfromS (m281 !$ [i290, i292])), tplainPart (kfromS (m282 !$ [i291, i293]))])) ; u296 = sreshape @[4,3,5,4] (w294 * w295) ; m300 = str (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (splainPart (splainPart u296 !$ [i297, i298, i299])))])))) ; m301 = str (sreplicate @7 (ssum @60 (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m300))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m304 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar (-0.0) <=. splainPart (negate (splainPart m301 !$ [i302, i303]))) 0 1])) ; t305 = str (sreplicate @10 (m304 * m301)) in rfromS (ssum @5 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * t305) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w253 = splainPart (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i249, i250] -> [i249 + i250]))) (\\[i251, i252] -> [i251 + i252])))))))) ; w254 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))) ; t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (w253 * w254))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; w269 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let i263 = tplainPart (kfromS (m256 !$ [i259, i261])) ; i264 = tplainPart (kfromS (m257 !$ [i260, i262])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t255 !$ [i258, i263, i264]))) 0 1])) ; w270 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [tplainPart (kfromS (m256 !$ [i265, i267])), tplainPart (kfromS (m257 !$ [i266, i268]))])) ; u271 = sreshape @[4,7,11,4] (w269 * w270) ; w279 = sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i272, i273, i274] -> [kfromS (smaxIndex (splainPart (splainPart u271 !$ [i274, i272, i273]))), i273, i272, i274]))) (\\[i275, i276] -> [i275, i276, i275 + i276]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (w279 * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m281 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m282 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; w294 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [let i288 = tplainPart (kfromS (m281 !$ [i284, i286])) ; i289 = tplainPart (kfromS (m282 !$ [i285, i287])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t280 !$ [i283, i288, i289]))) 0 1])) ; w295 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [tplainPart (kfromS (m281 !$ [i290, i292])), tplainPart (kfromS (m282 !$ [i291, i293]))])) ; u296 = sreshape @[4,3,5,4] (w294 * w295) ; m300 = str (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (splainPart (splainPart u296 !$ [i297, i298, i299])))])))) ; m301 = str (sreplicate @7 (ssum @60 (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m300))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m304 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar (-0.0) <=. splainPart (negate (splainPart m301 !$ [i302, i303]))) 0 1])) ; t305 = str (sreplicate @10 (m304 * m301)) ; m307 = m304 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * sreplicate @5 (sfromR dret))) ; m308 = sreplicate @60 (ssum @7 (str m307)) ; t316 = stranspose @[2,0,1] (sscatter (stranspose @[1,2,3,4,0] (w294 * sreshape @[4,3,5,2,2] (sscatter (sreshape @[4,3,5] (ssum @5 (str (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m308)))) (\\[i309, i310, i311] -> [i309, i310, i311, kfromS (smaxIndex (splainPart (splainPart u296 !$ [i309, i310, i311])))])))) (\\[i312, i313, i314, i315] -> [tplainPart (kfromS (m281 !$ [i312, i314])), tplainPart (kfromS (m282 !$ [i313, i315]))])) ; w317 = sreshape @[4,7,11,4,3,4] (stranspose @[1,2,3,0] (sreplicate @48 t316)) ; t329 = stranspose @[2,0,1] (sscatter (stranspose @[1,2,3,4,0] (w269 * sreshape @[4,7,11,2,2] (stranspose @[3,2,1,0] (ssum @4 (ssum @7 (ssum @11 (stranspose @[4,5,6,3,2,1,0] (ssum @3 (stranspose @[7,3,2,1,0,6,5,4] (sscatter (stranspose @[2,5,4,6,0,3,1] (sscatter (stranspose @[3,5,0,4,1,2] (sscatter (stranspose @[1,4,0,2,3] (ssum @4 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))) * w317))) (\\[i318, i319] -> [i318, i318 + i319, i319]))) (\\[i320, i321] -> [i320, i321, i320 + i321]))) (\\[i322, i323, i324] -> [kfromS (smaxIndex (splainPart (splainPart u271 !$ [i324, i322, i323]))), i323, i322, i324]))))))))))) (\\[i325, i326, i327, i328] -> [tplainPart (kfromS (m256 !$ [i325, i327])), tplainPart (kfromS (m257 !$ [i326, i328]))])) in tpair (tpair (tpair (rfromS (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (w253 * sreshape @[4,14,23,1,1,3,4] (stranspose @[1,2,3,0] (sreplicate @12 t329))))))))))) [0]))) (rfromS (ssum @23 (ssum @14 (stranspose @[1,2,0] t329))))) (tpair (rfromS (ssum @11 (str (ssum @7 (str (w279 * w317)))))) (rfromS (ssum @11 (ssum @7 (stranspose @[1,2,0] t316)))))) (tpair (tpair (rfromS (str (m300 * m308))) (rfromS (ssum @7 (str m307)))) (tpair (rfromS (ssum @7 (stranspose @[2,1,0] (t305 * sreplicate @5 (sfromR dret))))) (rfromS (ssum @7 (str (sfromR dret))))))"
-- TODO: different test result with GHC 9.10:   printArtifactPretty (simplifyArtifact artifactRev)
--    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let u247 = sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i397, i398] -> [i397 + i398]))) (\\[i245, i246] -> [i245 + i246]) ; t249 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] u247))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; w259 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i250, i251, i252, i253, i254] -> [ifH (sscalar (-0.0) <=. negate (t249 !$ [i250, 2 * i251 + i253, 2 * i252 + i254])) 0 1]) ; u261 = sreshape @[4,7,11,4] (w259 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t249) (\\[i255, i256, i257, i258] -> [2 * i255 + i257, 2 * i256 + i258]))) ; w269 = sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u261))))))) (\\[i380, i382, i383] -> [kfromS (smaxIndex (u261 !$ [i383, i380, i382])), i382, i380, i383]))) (\\[i388, i390] -> [i388, i390, i388 + i390]))) (\\[i267, i268] -> [i267, i267 + i268, i268]) ; t270 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (sreplicate @4 (stranspose @[2,0,3,4,1] w269) * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; w280 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i271, i272, i273, i274, i275] -> [ifH (sscalar (-0.0) <=. negate (t270 !$ [i271, 2 * i272 + i274, 2 * i273 + i275])) 0 1]) ; u282 = sreshape @[4,3,5,4] (w280 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t270) (\\[i276, i277, i278, i279] -> [2 * i276 + i278, 2 * i277 + i279]))) ; v286 = sreshape @[60] (sgather u282 (\\[i283, i284, i285] -> [i283, i284, i285, kfromS (smaxIndex (u282 !$ [i283, i284, i285]))])) ; m287 = str (sreplicate @7 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @5 v286))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m290 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i288, i289] -> [ifH (sscalar (-0.0) <=. negate (m287 !$ [i288, i289])) 0 1]) ; m293 = m290 * smatmul2 (str (sfromR (tproject1 (tproject2 (tproject2 u1))))) (sfromR dret) ; v294 = ssum @7 (str m293) ; t302 = sscatter (stranspose @[1,2,3,4,0] w280 * stranspose @[1,2,3,4,0] (sreshape @[4,3,5,2,2] (sscatter (sreshape @[4,3,5] (sdot1In (str (sfromR (tproject1 (tproject1 (tproject2 u1))))) (sreplicate @60 v294))) (\\[i295, i296, i297] -> [i295, i296, i297, kfromS (smaxIndex (u282 !$ [i295, i296, i297]))])))) (\\[i298, i299, i300, i301] -> [2 * i298 + i300, 2 * i299 + i301]) ; w303 = sreshape @[4,7,11,4,3,4] (stranspose @[1,2,3,0] (sreplicate @48 (stranspose @[2,0,1] t302))) ; t315 = sscatter (stranspose @[1,2,3,4,0] w259 * stranspose @[1,2,3,4,0] (sreshape @[4,7,11,2,2] (ssum @4 (ssum @7 (ssum @11 (ssum @3 (stranspose @[7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,5,4,6,0,3,1] (sscatter (stranspose @[3,5,0,4,1,2] (sscatter (sdot1In (stranspose @[2,5,0,3,4,1] (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))) (stranspose @[2,5,1,3,4,0] w303)) (\\[i304, i305] -> [i304, i304 + i305, i305]))) (\\[i306, i307] -> [i306, i307, i306 + i307]))) (\\[i308, i309, i310] -> [kfromS (smaxIndex (u261 !$ [i310, i308, i309])), i309, i308, i310]))))))))) (\\[i311, i312, i313, i314] -> [2 * i311 + i313, 2 * i312 + i314]) in tpair (tpair (tpair (str (sreplicate @1 (ssum @23 (sdot1In (stranspose @[4,0,3,2,1] (sreplicate @4 (stranspose @[2,1,3,0] u247))) (stranspose @[3,4,2,0,5,6,1] (sreshape @[4,14,23,1,1,3,4] (stranspose @[1,2,3,0] (sreplicate @12 (stranspose @[2,0,1] t315)))) !$ [0, 0]))))) (ssum @23 (ssum @14 t315))) (tpair (ssum @11 (sdot1In (stranspose @[2,0,3,4,5,1] (sreplicate @4 (stranspose @[2,0,3,4,1] w269))) (stranspose @[2,0,3,4,5,1] w303))) (ssum @11 (ssum @7 t302)))) (tpair (tpair (sreplicate @5 v286 * str (sreplicate @60 v294)) (ssum @7 (str m293))) (tpair (smatmul2 (sfromR dret) (str m290 * str m287)) (ssum @7 (str (sfromR dret))))))"

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
    @?= "\\u1 -> let t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i473, i474] -> [i473 + i474]))) (\\[i251, i252] -> [i251 + i252]))))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; u271 = sreshape @[4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [ifH (sscalar (-0.0) <=. negate (splainPart t255 !$ [i258, kfromS (sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) !$ [i259, i261]), kfromS (sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) !$ [i260, i262])])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [kfromS (sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) !$ [i265, i267]), kfromS (sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) !$ [i266, i268])]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i458, i460, i461] -> [kfromS (smaxIndex (splainPart u271 !$ [i461, i458, i460])), i460, i458, i461]))) (\\[i466, i468] -> [i466, i468, i466 + i468]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; u296 = sreshape @[4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [ifH (sscalar (-0.0) <=. negate (splainPart t280 !$ [i283, kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i284, i286]), kfromS (sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) !$ [i285, i287])])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [kfromS (sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) !$ [i290, i292]), kfromS (sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) !$ [i291, i293])]))) ; m301 = str (sreplicate @7 (sdot1In (tproject1 (tproject1 (tproject2 u1))) (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (splainPart u296 !$ [i297, i298, i299]))])))))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) in smatmul2 (tproject1 (tproject2 (tproject2 u1))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar (-0.0) <=. negate (splainPart m301 !$ [i302, i303])) 0 1]) * m301) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w253 = splainPart (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i249, i250] -> [i249 + i250]))) (\\[i251, i252] -> [i251 + i252])))))))) ; w254 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))) ; t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (w253 * w254))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; w269 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let i263 = tplainPart (kfromS (m256 !$ [i259, i261])) ; i264 = tplainPart (kfromS (m257 !$ [i260, i262])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t255 !$ [i258, i263, i264]))) 0 1])) ; w270 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [tplainPart (kfromS (m256 !$ [i265, i267])), tplainPart (kfromS (m257 !$ [i266, i268]))])) ; u271 = sreshape @[4,7,11,4] (w269 * w270) ; w279 = sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i272, i273, i274] -> [kfromS (smaxIndex (splainPart (splainPart u271 !$ [i274, i272, i273]))), i273, i272, i274]))) (\\[i275, i276] -> [i275, i276, i275 + i276]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (w279 * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; m281 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m282 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; w294 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [let i288 = tplainPart (kfromS (m281 !$ [i284, i286])) ; i289 = tplainPart (kfromS (m282 !$ [i285, i287])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t280 !$ [i283, i288, i289]))) 0 1])) ; w295 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [tplainPart (kfromS (m281 !$ [i290, i292])), tplainPart (kfromS (m282 !$ [i291, i293]))])) ; u296 = sreshape @[4,3,5,4] (w294 * w295) ; m300 = str (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (splainPart (splainPart u296 !$ [i297, i298, i299])))])))) ; m301 = str (sreplicate @7 (ssum @60 (str (tproject1 (tproject1 (tproject2 u1))) * m300))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m304 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar (-0.0) <=. splainPart (negate (splainPart m301 !$ [i302, i303]))) 0 1])) ; t305 = str (sreplicate @10 (m304 * m301)) in ssum @5 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * t305) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w253 = splainPart (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] (sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i249, i250] -> [i249 + i250]))) (\\[i251, i252] -> [i251 + i252])))))))) ; w254 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))) ; t255 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (w253 * w254))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; w269 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let i263 = tplainPart (kfromS (m256 !$ [i259, i261])) ; i264 = tplainPart (kfromS (m257 !$ [i260, i262])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t255 !$ [i258, i263, i264]))) 0 1])) ; w270 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t255) (\\[i265, i266, i267, i268] -> [tplainPart (kfromS (m256 !$ [i265, i267])), tplainPart (kfromS (m257 !$ [i266, i268]))])) ; u271 = sreshape @[4,7,11,4] (w269 * w270) ; w279 = sreplicate @4 (stranspose @[2,0,3,4,1] (sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u271))))))) (\\[i272, i273, i274] -> [kfromS (smaxIndex (splainPart (splainPart u271 !$ [i274, i272, i273]))), i273, i272, i274]))) (\\[i275, i276] -> [i275, i276, i275 + i276]))) (\\[i277, i278] -> [i277, i277 + i278, i278]))) ; t280 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (w279 * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; m281 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; m282 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; w294 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i283, i284, i285, i286, i287] -> [let i288 = tplainPart (kfromS (m281 !$ [i284, i286])) ; i289 = tplainPart (kfromS (m282 !$ [i285, i287])) in ifH (sscalar (-0.0) <=. splainPart (negate (splainPart t280 !$ [i283, i288, i289]))) 0 1])) ; w295 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t280) (\\[i290, i291, i292, i293] -> [tplainPart (kfromS (m281 !$ [i290, i292])), tplainPart (kfromS (m282 !$ [i291, i293]))])) ; u296 = sreshape @[4,3,5,4] (w294 * w295) ; m300 = str (sreplicate @5 (sreshape @[60] (sgather u296 (\\[i297, i298, i299] -> [i297, i298, i299, kfromS (smaxIndex (splainPart (splainPart u296 !$ [i297, i298, i299])))])))) ; m301 = str (sreplicate @7 (ssum @60 (str (tproject1 (tproject1 (tproject2 u1))) * m300))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m304 = splainPart (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303] -> [ifH (sscalar (-0.0) <=. splainPart (negate (splainPart m301 !$ [i302, i303]))) 0 1])) ; t305 = str (sreplicate @10 (m304 * m301)) ; m307 = m304 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * sreplicate @5 dret)) ; m308 = sreplicate @60 (ssum @7 (str m307)) ; t316 = stranspose @[2,0,1] (sscatter (stranspose @[1,2,3,4,0] (w294 * sreshape @[4,3,5,2,2] (sscatter (sreshape @[4,3,5] (ssum @5 (str (str (tproject1 (tproject1 (tproject2 u1))) * m308)))) (\\[i309, i310, i311] -> [i309, i310, i311, kfromS (smaxIndex (splainPart (splainPart u296 !$ [i309, i310, i311])))])))) (\\[i312, i313, i314, i315] -> [tplainPart (kfromS (m281 !$ [i312, i314])), tplainPart (kfromS (m282 !$ [i313, i315]))])) ; w317 = sreshape @[4,7,11,4,3,4] (stranspose @[1,2,3,0] (sreplicate @48 t316)) ; t329 = stranspose @[2,0,1] (sscatter (stranspose @[1,2,3,4,0] (w269 * sreshape @[4,7,11,2,2] (stranspose @[3,2,1,0] (ssum @4 (ssum @7 (ssum @11 (stranspose @[4,5,6,3,2,1,0] (ssum @3 (stranspose @[7,3,2,1,0,6,5,4] (sscatter (stranspose @[2,5,4,6,0,3,1] (sscatter (stranspose @[3,5,0,4,1,2] (sscatter (stranspose @[1,4,0,2,3] (ssum @4 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))) * w317))) (\\[i318, i319] -> [i318, i318 + i319, i319]))) (\\[i320, i321] -> [i320, i321, i320 + i321]))) (\\[i322, i323, i324] -> [kfromS (smaxIndex (splainPart (splainPart u271 !$ [i324, i322, i323]))), i323, i322, i324]))))))))))) (\\[i325, i326, i327, i328] -> [tplainPart (kfromS (m256 !$ [i325, i327])), tplainPart (kfromS (m257 !$ [i326, i328]))])) in tpair (tpair (tpair (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (w253 * sreshape @[4,14,23,1,1,3,4] (stranspose @[1,2,3,0] (sreplicate @12 t329))))))))))) [0])) (ssum @23 (ssum @14 (stranspose @[1,2,0] t329)))) (tpair (ssum @11 (str (ssum @7 (str (w279 * w317))))) (ssum @11 (ssum @7 (stranspose @[1,2,0] t316))))) (tpair (tpair (str (m300 * m308)) (ssum @7 (str m307))) (tpair (ssum @7 (stranspose @[2,1,0] (t305 * sreplicate @5 dret))) (ssum @7 (str dret))))"
-- TODO: different test result with GHC 9.10: printArtifactPretty (simplifyArtifact artifactRev)
--    @?= "\\dret u1 -> let u247 = sgather (stranspose @[2,0,1] (sgather (sconcrete (sreplicate [14,23] 7.0)) (\\[i397, i398] -> [i397 + i398]))) (\\[i245, i246] -> [i245 + i246]) ; t249 = ssum @12 (stranspose @[3,0,1,2] (sreshape @[4,14,23,12] (sreplicate @4 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[1,2,0] (sreplicate @1 (stranspose @[2,0,3,1] u247))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))))) + stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; w259 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i250, i251, i252, i253, i254] -> [ifH (sscalar (-0.0) <=. negate (t249 !$ [i250, 2 * i251 + i253, 2 * i252 + i254])) 0 1]) ; u261 = sreshape @[4,7,11,4] (w259 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t249) (\\[i255, i256, i257, i258] -> [2 * i255 + i257, 2 * i256 + i258]))) ; w269 = sgather (stranspose @[2,4,5,0,3,1] (sgather (stranspose @[4,6,0,5,2,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @3 (stranspose @[6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[3,2,1,0] u261))))))) (\\[i380, i382, i383] -> [kfromS (smaxIndex (u261 !$ [i383, i380, i382])), i382, i380, i383]))) (\\[i388, i390] -> [i388, i390, i388 + i390]))) (\\[i267, i268] -> [i267, i267 + i268, i268]) ; t270 = ssum @48 (stranspose @[3,0,1,2] (sreshape @[4,7,11,48] (sreplicate @4 (stranspose @[2,0,3,4,1] w269) * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; w280 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i271, i272, i273, i274, i275] -> [ifH (sscalar (-0.0) <=. negate (t270 !$ [i271, 2 * i272 + i274, 2 * i273 + i275])) 0 1]) ; u282 = sreshape @[4,3,5,4] (w280 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,0] t270) (\\[i276, i277, i278, i279] -> [2 * i276 + i278, 2 * i277 + i279]))) ; v286 = sreshape @[60] (sgather u282 (\\[i283, i284, i285] -> [i283, i284, i285, kfromS (smaxIndex (u282 !$ [i283, i284, i285]))])) ; m287 = str (sreplicate @7 (sdot1In (tproject1 (tproject1 (tproject2 u1))) (sreplicate @5 v286))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m290 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i288, i289] -> [ifH (sscalar (-0.0) <=. negate (m287 !$ [i288, i289])) 0 1]) ; m293 = m290 * smatmul2 (str (tproject1 (tproject2 (tproject2 u1)))) dret ; v294 = ssum @7 (str m293) ; t302 = sscatter (stranspose @[1,2,3,4,0] w280 * stranspose @[1,2,3,4,0] (sreshape @[4,3,5,2,2] (sscatter (sreshape @[4,3,5] (sdot1In (str (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @60 v294))) (\\[i295, i296, i297] -> [i295, i296, i297, kfromS (smaxIndex (u282 !$ [i295, i296, i297]))])))) (\\[i298, i299, i300, i301] -> [2 * i298 + i300, 2 * i299 + i301]) ; w303 = sreshape @[4,7,11,4,3,4] (stranspose @[1,2,3,0] (sreplicate @48 (stranspose @[2,0,1] t302))) ; t315 = sscatter (stranspose @[1,2,3,4,0] w259 * stranspose @[1,2,3,4,0] (sreshape @[4,7,11,2,2] (ssum @4 (ssum @7 (ssum @11 (ssum @3 (stranspose @[7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,5,4,6,0,3,1] (sscatter (stranspose @[3,5,0,4,1,2] (sscatter (sdot1In (stranspose @[2,5,0,3,4,1] (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))) (stranspose @[2,5,1,3,4,0] w303)) (\\[i304, i305] -> [i304, i304 + i305, i305]))) (\\[i306, i307] -> [i306, i307, i306 + i307]))) (\\[i308, i309, i310] -> [kfromS (smaxIndex (u261 !$ [i310, i308, i309])), i309, i308, i310]))))))))) (\\[i311, i312, i313, i314] -> [2 * i311 + i313, 2 * i312 + i314]) in tpair (tpair (tpair (str (sreplicate @1 (ssum @23 (sdot1In (stranspose @[4,0,3,2,1] (sreplicate @4 (stranspose @[2,1,3,0] u247))) (stranspose @[3,4,2,0,5,6,1] (sreshape @[4,14,23,1,1,3,4] (stranspose @[1,2,3,0] (sreplicate @12 (stranspose @[2,0,1] t315)))) !$ [0, 0]))))) (ssum @23 (ssum @14 t315))) (tpair (ssum @11 (sdot1In (stranspose @[2,0,3,4,5,1] (sreplicate @4 (stranspose @[2,0,3,4,1] w269))) (stranspose @[2,0,3,4,5,1] w303))) (ssum @11 (ssum @7 t302)))) (tpair (tpair (sreplicate @5 v286 * str (sreplicate @60 v294)) (ssum @7 (str m293))) (tpair (smatmul2 dret (str m290 * str m287)) (ssum @7 (str dret))))"
