{-# OPTIONS_GHC -fno-late-specialise #-}
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
                             $ Nested.sfromList1Prim
                                 (SNat @SizeMnistGlyph)
                                 [1 .. fromIntegral sizeMnistGlyphInt]))
    , Concrete $ Nested.sfromList1Prim (SNat @3) [1, 2, 3] )
  , ( fromList (replicate 4 (Concrete $ Nested.sfromList1Prim
                                          (SNat @3) [1, 2, 3]))
    , Concrete $ Nested.sfromList1Prim (SNat @4) [1, 2, 3, 4] )
  , ( fromList (replicate sizeMnistLabelInt
                          (Concrete $ Nested.sfromList1Prim
                                        (SNat @4) [1, 2, 3, 4]))
    , Concrete $ Nested.sfromList1Prim (SNat @SizeMnistLabel)
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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v5, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v5]) + tproject2 (tproject2 v1))"
  printArtifactPrimalPretty artifactRev
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [kfromS (ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate @784 (sfromK 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate @784 (sfromK 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate @784 (sfromK 7.0))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [kfromS (ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4))]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [kfromS (ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v5))]) + tproject2 (tproject2 v1))"
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [kfromS (ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate @784 (sfromK 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate @784 (sfromK 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate @784 (sfromK 7.0))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [kfromS (ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4))]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate @4 (sfromK (sfromR dret `sindex0` [9])) ; v8 = sreplicate @4 (sfromK (sfromR dret `sindex0` [8])) ; v9 = sreplicate @4 (sfromK (sfromR dret `sindex0` [7])) ; v10 = sreplicate @4 (sfromK (sfromR dret `sindex0` [6])) ; v11 = sreplicate @4 (sfromK (sfromR dret `sindex0` [5])) ; v12 = sreplicate @4 (sfromK (sfromR dret `sindex0` [4])) ; v13 = sreplicate @4 (sfromK (sfromR dret `sindex0` [3])) ; v14 = sreplicate @4 (sfromK (sfromR dret `sindex0` [2])) ; v15 = sreplicate @4 (sfromK (sfromR dret `sindex0` [1])) ; v16 = sreplicate @4 (sfromK (sfromR dret `sindex0` [0])) in tpair (let v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7)))))))) ; v18 = sreplicate @3 (sfromK (v17 `sindex0` [3])) ; v19 = sreplicate @3 (sfromK (v17 `sindex0` [2])) ; v20 = sreplicate @3 (sfromK (v17 `sindex0` [1])) ; v21 = sreplicate @3 (sfromK (v17 `sindex0` [0])) in tpair (let v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)) in tpair (tpair (sreplicate @784 (sfromK (7.0 * v22 `sindex0` [0]))) (tpair (sreplicate @784 (sfromK (7.0 * v22 `sindex0` [1]))) (tpair (sreplicate @784 (sfromK (7.0 * v22 `sindex0` [2]))) Z1))) v22) (tpair (tpair (v4 * v21) (tpair (v4 * v20) (tpair (v4 * v19) (tpair (v4 * v18) Z1)))) v17)) (tpair (tpair (v5 * v16) (tpair (v5 * v15) (tpair (v5 * v14) (tpair (v5 * v13) (tpair (v5 * v12) (tpair (v5 * v11) (tpair (v5 * v10) (tpair (v5 * v9) (tpair (v5 * v8) (tpair (v5 * v7) Z1)))))))))) (sfromR dret))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) ; x7 = sfromR dret `sindex0` [9] ; x8 = sfromR dret `sindex0` [8] ; x9 = sfromR dret `sindex0` [7] ; x10 = sfromR dret `sindex0` [6] ; x11 = sfromR dret `sindex0` [5] ; x12 = sfromR dret `sindex0` [4] ; x13 = sfromR dret `sindex0` [3] ; x14 = sfromR dret `sindex0` [2] ; x15 = sfromR dret `sindex0` [1] ; x16 = sfromR dret `sindex0` [0] in tpair (let v17 = tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x7)))))))) ; x18 = v17 `sindex0` [3] ; x19 = v17 `sindex0` [2] ; x20 = v17 `sindex0` [1] ; x21 = v17 `sindex0` [0] in tpair (let v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x18)) in tpair (tpair (sreplicate @784 (7.0 * v22 `sindex0` [0])) (tpair (sreplicate @784 (7.0 * v22 `sindex0` [1])) (tpair (sreplicate @784 (7.0 * v22 `sindex0` [2])) Z1))) v22) (tpair (tpair (v4 * sreplicate @3 x21) (tpair (v4 * sreplicate @3 x20) (tpair (v4 * sreplicate @3 x19) (tpair (v4 * sreplicate @3 x18) Z1)))) v17)) (tpair (tpair (v5 * sreplicate @4 x16) (tpair (v5 * sreplicate @4 x15) (tpair (v5 * sreplicate @4 x14) (tpair (v5 * sreplicate @4 x13) (tpair (v5 * sreplicate @4 x12) (tpair (v5 * sreplicate @4 x11) (tpair (v5 * sreplicate @4 x10) (tpair (v5 * sreplicate @4 x9) (tpair (v5 * sreplicate @4 x8) (tpair (v5 * sreplicate @4 x7) Z1)))))))))) (sfromR dret))"

testVTOAst :: Assertion
testVTOAst = do
  let ftk = tftk @Concrete (knownSTK @(XParams 3 4 Float))
                 (toTarget @Concrete valsInitVTOPP)
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKR 1 Float) afcnn1)
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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\v1 -> rfromS (let v13 = recip (scast (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1)))))) ; v16 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v13, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v13, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v13, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v13]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v18 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v16, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v16]) + tproject2 (tproject2 v1)) in sreplicate @10 (recip (ssum0 v18)) * v18)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\v1 -> rfromS (let v9 = sfromVector (fromList [kfromS (ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate @784 (sfromK 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate @784 (sfromK 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate @784 (sfromK 7.0))))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = recip (sconcrete (sreplicate [3] 1.0) + v10) ; v13 = scast v11 ; v14 = scast (sfromVector (fromList [kfromS (ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v13)), kfromS (ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v13)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v13)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v13))])) + tproject2 (tproject2 (tproject1 v1)) ; v15 = exp (negate v14) ; v16 = recip (sconcrete (sreplicate [4] 1.0) + v15) ; v18 = exp (sfromVector (fromList [kfromS (ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v16))]) + tproject2 (tproject2 v1)) ; x19 = kfromS (ssum @10 v18) ; v20 = sreplicate @10 (sfromK (recip x19)) in v20 * v18)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret v1 -> let v9 = sfromVector (fromList [kfromS (ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate @784 (sfromK 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate @784 (sfromK 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate @784 (sfromK 7.0))))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = recip (sconcrete (sreplicate [3] 1.0) + v10) ; v12 = v11 * (sconcrete (sreplicate [3] 1.0) + negate v11) ; v13 = scast v11 ; v14 = scast (sfromVector (fromList [kfromS (ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v13)), kfromS (ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v13)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v13)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v13))])) + tproject2 (tproject2 (tproject1 v1)) ; v15 = exp (negate v14) ; v16 = recip (sconcrete (sreplicate [4] 1.0) + v15) ; v17 = v16 * (sconcrete (sreplicate [4] 1.0) + negate v16) ; v18 = exp (sfromVector (fromList [kfromS (ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v16)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v16))]) + tproject2 (tproject2 v1)) ; x19 = kfromS (ssum @10 v18) ; v20 = sreplicate @10 (sfromK (recip x19)) ; v22 = v18 * (sreplicate @10 (sfromK (negate (recip (x19 * x19)) * kfromS (ssum @10 (v18 * sfromR dret)))) + v20 * sfromR dret) ; v23 = sreplicate @4 (sfromK (v22 `sindex0` [9])) ; v24 = sreplicate @4 (sfromK (v22 `sindex0` [8])) ; v25 = sreplicate @4 (sfromK (v22 `sindex0` [7])) ; v26 = sreplicate @4 (sfromK (v22 `sindex0` [6])) ; v27 = sreplicate @4 (sfromK (v22 `sindex0` [5])) ; v28 = sreplicate @4 (sfromK (v22 `sindex0` [4])) ; v29 = sreplicate @4 (sfromK (v22 `sindex0` [3])) ; v30 = sreplicate @4 (sfromK (v22 `sindex0` [2])) ; v31 = sreplicate @4 (sfromK (v22 `sindex0` [1])) ; v32 = sreplicate @4 (sfromK (v22 `sindex0` [0])) in tpair (let v33 = v17 * (tproject1 (tproject1 (tproject2 v1)) * v32 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v31 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v29 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v28 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v27 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v26 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v25 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v24 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v23))))))))) ; v34 = scast v33 ; v35 = sreplicate @3 (sfromK (v34 `sindex0` [3])) ; v36 = sreplicate @3 (sfromK (v34 `sindex0` [2])) ; v37 = sreplicate @3 (sfromK (v34 `sindex0` [1])) ; v38 = sreplicate @3 (sfromK (v34 `sindex0` [0])) in tpair (let v39 = v12 * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v38 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v37 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v36 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v35))) in tpair (tpair (sreplicate @784 (sfromK (7.0 * v39 `sindex0` [0]))) (tpair (sreplicate @784 (sfromK (7.0 * v39 `sindex0` [1]))) (tpair (sreplicate @784 (sfromK (7.0 * v39 `sindex0` [2]))) Z1))) v39) (tpair (tpair (v13 * v38) (tpair (v13 * v37) (tpair (v13 * v36) (tpair (v13 * v35) Z1)))) v33)) (tpair (tpair (v16 * v32) (tpair (v16 * v31) (tpair (v16 * v30) (tpair (v16 * v29) (tpair (v16 * v28) (tpair (v16 * v27) (tpair (v16 * v26) (tpair (v16 * v25) (tpair (v16 * v24) (tpair (v16 * v23) Z1)))))))))) v22)"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret v1 -> let v11 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1))))) ; v13 = scast v11 ; v16 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v13, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v13, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v13, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v13]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v18 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v16, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v16]) + tproject2 (tproject2 v1)) ; x19 = ssum0 v18 ; v22 = v18 * (sreplicate @10 (negate (recip (x19 * x19)) * sdot0 v18 (sfromR dret)) + sreplicate @10 (recip x19) * sfromR dret) ; x23 = v22 `sindex0` [9] ; x24 = v22 `sindex0` [8] ; x25 = v22 `sindex0` [7] ; x26 = v22 `sindex0` [6] ; x27 = v22 `sindex0` [5] ; x28 = v22 `sindex0` [4] ; x29 = v22 `sindex0` [3] ; x30 = v22 `sindex0` [2] ; x31 = v22 `sindex0` [1] ; x32 = v22 `sindex0` [0] in tpair (let v33 = (v16 * (sconcrete (sreplicate [4] 1.0) + negate v16)) * (tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x32 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x31 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x29 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x28 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x27 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x26 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x25 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x24 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x23))))))))) ; v34 = scast v33 ; x35 = v34 `sindex0` [3] ; x36 = v34 `sindex0` [2] ; x37 = v34 `sindex0` [1] ; x38 = v34 `sindex0` [0] in tpair (let v39 = (v11 * (sconcrete (sreplicate [3] 1.0) + negate v11)) * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x38 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x37 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x36 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x35))) in tpair (tpair (sreplicate @784 (7.0 * v39 `sindex0` [0])) (tpair (sreplicate @784 (7.0 * v39 `sindex0` [1])) (tpair (sreplicate @784 (7.0 * v39 `sindex0` [2])) Z1))) v39) (tpair (tpair (v13 * sreplicate @3 x38) (tpair (v13 * sreplicate @3 x37) (tpair (v13 * sreplicate @3 x36) (tpair (v13 * sreplicate @3 x35) Z1)))) v33)) (tpair (tpair (v16 * sreplicate @4 x32) (tpair (v16 * sreplicate @4 x31) (tpair (v16 * sreplicate @4 x30) (tpair (v16 * sreplicate @4 x29) (tpair (v16 * sreplicate @4 x28) (tpair (v16 * sreplicate @4 x27) (tpair (v16 * sreplicate @4 x26) (tpair (v16 * sreplicate @4 x25) (tpair (v16 * sreplicate @4 x24) (tpair (v16 * sreplicate @4 x23) Z1)))))))))) v22)"

testVTOAstNonLin :: Assertion
testVTOAstNonLin = do
  let ftk = tftk @Concrete (knownSTK @(XParams 3 4 Double))
                 (toTarget @Concrete valsInitVTOPP)
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKR 1 Double) afcnn1)
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
    @?= "\\m1 -> rfromS (let v5 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; m6 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 7.0) * v5 + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m7 = str (sreplicate @2 (scast (ssum @4 (m6 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in ssum @5 (m7 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1)))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v5 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; m6 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 7.0) * v5 + sfromR (tproject2 (tproject1 (tproject1 m1)))))) in tpair (let v9 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m10 = sreplicate @4 (scast v9) in tpair (let v11 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m10))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v11)))) (rfromS v11)) (tpair (rfromS (str (m6 * m10))) (rfromS v9))) (tpair (rfromS (str (let m7 = str (sreplicate @2 (scast (ssum @4 (m6 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in m7 * sreplicate @5 (sfromR dret)))) dret)"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v5 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; m6 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 7.0) * v5 + sfromR (tproject2 (tproject1 (tproject1 m1)))))) in tpair (let v9 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m10 = sreplicate @4 (scast v9) in tpair (let v11 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m10))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v11)))) (rfromS v11)) (tpair (rfromS (str (m6 * m10))) (rfromS v9))) (tpair (rfromS (str (let m7 = str (sreplicate @2 (scast (ssum @4 (m6 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in m7 * sreplicate @5 (sfromR dret)))) dret)"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) ConvId)) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKR (SNat @1) STKScalar))) (let v6 = scast (sconcrete (sreplicate [4] 7.0) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) in tpair (let v9 = sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 (sfromR dret)) ; v10 = scast v9 in tpair (let v11 = scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v10)) in tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v11))) v11) (tpair (sreplicate @5 v6 * str (sreplicate @4 v10)) v9)) (tpair (sreplicate @2 (scast (sdot1In (sreplicate @5 v6) (sfromR (tproject1 (tproject2 (tproject1 m1))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @5 (sfromR dret))) dret))"

testVT2OAst :: Assertion
testVT2OAst = do
  let ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                 (toTarget @Concrete valsInitVT2OPP)
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKR 1 Double) afcnn1)
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
      ast3 = snd $ funToAst @FullSpan
                            (FTKR (0 :$: ZSR) (FTKScalar @Float))
                            (const $ afcnn2TnonLin constant)
  "\\dummy" ++ " -> " ++ printAstSimple ast3
    @?= "\\dummy -> tfromPlain (STKR (SNat @1) STKScalar) (rfromS (tlet (exp (ssum @5 (str (sreplicate @2 (tlet (ssum @4 (sconcrete (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0]) * str (sreplicate @5 (tlet (sconcrete (sreplicate [4] 7.0) * ssum @3 (str (scast (sconcrete (sfromListLinear [4,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0])))) + scast (sconcrete (sfromListLinear [4] [1.0,2.0,3.0,4.0]))) (\\v7 -> recip (sconcrete (sreplicate [4] 1.0) + exp (negate v7)))))) + scast (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0]))) (\\v10 -> recip (sconcrete (sreplicate [5] 1.0) + exp (negate v10))))) * str (scast (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0])))) + scast (sconcrete (sfromListLinear [2] [1.0,2.0])))) (\\v12 -> sreplicate @2 (recip (ssum @2 v12)) * v12)))"
  "\\dummy" ++ " -> " ++ printAstSimple (simplifyInlineContract ast3)
    @?= "\\dummy -> tfromPlain (STKR (SNat @1) STKScalar) (rfromS (sconcrete (sfromListLinear [2] [0.26894158,0.73105836])))"

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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\m1 -> rfromS (let v20 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (recip (scast (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in sreplicate @2 (recip (ssum0 v20)) * v20)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> rfromS (let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = recip (sconcrete (sreplicate [4] 1.0) + v12) ; m15 = str (sreplicate @5 (scast v13)) ; v16 = scast (ssum @4 (m15 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v17 = exp (negate v16) ; v18 = recip (sconcrete (sreplicate [5] 1.0) + v17) ; v20 = exp (ssum @5 (str (sreplicate @2 v18) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x21 = kfromS (ssum @2 v20) ; v22 = sreplicate @2 (sfromK (recip x21)) in v22 * v20)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = recip (sconcrete (sreplicate [4] 1.0) + v12) ; v14 = v13 * (sconcrete (sreplicate [4] 1.0) + negate v13) ; m15 = str (sreplicate @5 (scast v13)) ; v16 = scast (ssum @4 (m15 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v17 = exp (negate v16) ; v18 = recip (sconcrete (sreplicate [5] 1.0) + v17) ; v19 = v18 * (sconcrete (sreplicate [5] 1.0) + negate v18) ; v20 = exp (ssum @5 (str (sreplicate @2 v18) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x21 = kfromS (ssum @2 v20) ; v22 = sreplicate @2 (sfromK (recip x21)) ; v24 = v20 * (sreplicate @2 (sfromK (negate (recip (x21 * x21)) * kfromS (ssum @2 (v20 * sfromR dret)))) + v22 * sfromR dret) in tpair (let v25 = v19 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v24)) ; m26 = sreplicate @4 (scast v25) in tpair (let v27 = v14 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m26))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v27)))) (rfromS v27)) (tpair (rfromS (str (m15 * m26))) (rfromS v25))) (tpair (rfromS (str (str (sreplicate @2 v18) * sreplicate @5 v24))) (rfromS v24))"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v15 = scast v13 ; v18 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v15) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v20 = exp (sdot1In (sreplicate @2 v18) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x21 = ssum0 v20 ; v24 = v20 * (sreplicate @2 (negate (recip (x21 * x21)) * sdot0 v20 (sfromR dret)) + sreplicate @2 (recip x21) * sfromR dret) in tpair (let v25 = (v18 * (sconcrete (sreplicate [5] 1.0) + negate v18)) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v24) ; v26 = scast v25 in tpair (let v27 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v26)) in tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v27))) v27) (tpair (sreplicate @5 v15 * str (sreplicate @4 v26)) v25)) (tpair (sreplicate @2 v18 * str (sreplicate @5 v24)) v24))"

testVT2OAstNonLin2 :: Assertion
testVT2OAstNonLin2 = do
  let ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                 (toTarget @Concrete valsInitVT2OPP)
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKR 1 Double) afcnn1)
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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\m1 -> let v20 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (recip (scast (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in (-8.0) * ssum0 (log (sreplicate @2 (recip (ssum0 v20)) * v20))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> negate (kfromS (ssum @2 (let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = recip (sconcrete (sreplicate [4] 1.0) + v12) ; m15 = str (sreplicate @5 (scast v13)) ; v16 = scast (ssum @4 (m15 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v17 = exp (negate v16) ; v18 = recip (sconcrete (sreplicate [5] 1.0) + v17) ; v20 = exp (ssum @5 (str (sreplicate @2 v18) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x21 = kfromS (ssum @2 v20) ; v22 = sreplicate @2 (sfromK (recip x21)) ; v23 = v22 * v20 ; v24 = log v23 in sconcrete (sreplicate [2] 8.0) * v24)))"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = recip (sconcrete (sreplicate [4] 1.0) + v12) ; v14 = v13 * (sconcrete (sreplicate [4] 1.0) + negate v13) ; m15 = str (sreplicate @5 (scast v13)) ; v16 = scast (ssum @4 (m15 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v17 = exp (negate v16) ; v18 = recip (sconcrete (sreplicate [5] 1.0) + v17) ; v19 = v18 * (sconcrete (sreplicate [5] 1.0) + negate v18) ; v20 = exp (ssum @5 (str (sreplicate @2 v18) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x21 = kfromS (ssum @2 v20) ; v22 = sreplicate @2 (sfromK (recip x21)) ; v23 = v22 * v20 ; v26 = recip v23 * sreplicate @2 (sfromK ((-8.0) * dret)) ; v27 = v20 * (sreplicate @2 (sfromK (negate (recip (x21 * x21)) * kfromS (ssum @2 (v20 * v26)))) + v22 * v26) in tpair (let v28 = v19 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v27)) ; m29 = sreplicate @4 (scast v28) in tpair (let v30 = v14 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m29))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v30)))) (rfromS v30)) (tpair (rfromS (str (m15 * m29))) (rfromS v28))) (tpair (rfromS (str (str (sreplicate @2 v18) * sreplicate @5 v27))) (rfromS v27))"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v15 = scast v13 ; v18 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v15) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v20 = exp (sdot1In (sreplicate @2 v18) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x21 = ssum0 v20 ; x22 = recip x21 ; v26 = recip (sreplicate @2 x22 * v20) * sreplicate @2 ((-8.0) * dret) ; v27 = v20 * (sreplicate @2 (negate (recip (x21 * x21)) * sdot0 v20 v26) + sreplicate @2 x22 * v26) in tpair (let v28 = (v18 * (sconcrete (sreplicate [5] 1.0) + negate v18)) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v27) ; v29 = scast v28 in tpair (let v30 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v29)) in tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v30))) v30) (tpair (sreplicate @5 v15 * str (sreplicate @4 v29)) v28)) (tpair (sreplicate @2 v18 * str (sreplicate @5 v27)) v27))"

testVT2OAstNonLin3 :: Assertion
testVT2OAstNonLin3 = do
  let ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                 (toTarget @Concrete valsInitVT2OPP)
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKScalar Double) afcnn1)
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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\m1 -> rfromS (str (sreplicate @1 (str (sfromR (tproject1 (tproject2 m1))) !$ [0] * sreplicate @10 (tanh (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] * tanh (7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0])))) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (let x16 = sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] ; x17 = tanh (7.0 * x16 + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0]) ; v20 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] in str (sreplicate @1 (v20 * sreplicate @10 (sfromK x19))) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let x16 = sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] ; x17 = tanh (7.0 * x16 + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0]) in tpair (let v20 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] ; x22 = (1.0 + negate x19 * x19) * kfromS (ssum @10 (v20 * ssum @1 (str (sfromR dret)))) in tpair (let x23 = (1.0 + negate x17 * x17) * (x18 * x22) in tpair (tpair (rfromS (soneHot (sfromK (7.0 * x23)) [0, 0])) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (rfromS (soneHot (sfromK x23) [0]))) (tpair (tpair (rfromS (soneHot (sfromK (x17 * x22)) [0, 0])) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (rfromS (soneHot (sfromK x22) [0])))) (tpair (rfromS (str (soneHot (sreplicate @10 (sfromK x19) * ssum @1 (str (sfromR dret))) [0]))) (rfromS (ssum @1 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKS [1,1] STKScalar)) (STKS [1] STKScalar)) (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKS [1,1] STKScalar)) (STKS [1] STKScalar))) (STKProduct (STKS [10,1] STKScalar) (STKS [10] STKScalar))) (let x17 = tanh (7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0]) in tpair (let x22 = (1.0 + negate x19 * x19) * sdot0 (str (sfromR (tproject1 (tproject2 m1))) !$ [0]) (str (sfromR dret) !$ [0]) in tpair (let x23 = (1.0 + negate x17 * x17) * (x18 * x22) in tpair (tpair (sreplicate @1 (sreplicate @1 (7.0 * x23))) (sconcrete (sfromListLinear [1,1] [0.0]))) (sreplicate @1 x23)) (tpair (tpair (sreplicate @1 (sreplicate @1 (x17 * x22))) (sconcrete (sfromListLinear [1,1] [0.0]))) (sreplicate @1 x22))) (tpair (str (sreplicate @1 (sreplicate @10 x19 * str (sfromR dret) !$ [0]))) (str (sfromR dret) !$ [0])))"

testRNNOAst :: Assertion
testRNNOAst = do
  let batch_size = 1
      sizeMnistHeightI = 1
      ftk = tftk @Concrete
                 (knownSTK @(X (ADRnnMnistParameters Concrete Double)))
                 (toTarget @Concrete $ valsInitRNNOPP 1 sizeMnistHeightI)
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKR 2 Double) afcnn1)
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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\m1 -> rfromS (let m42 = sappend (tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) (tanh (str (sreplicate @2 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 (tanh (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice (SNat @0) (SNat @2) m42)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m42)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (let v37 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m38 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v37)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v39 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; v40 = tanh (sconcrete (sreplicate [2] 7.0) * v39 + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m41 = tanh (str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v40)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m42 = sappend m38 m41 ; v43 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m44 = tanh ((sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v43) + ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * stranspose @[2, 1, 0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m42))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m45 = tanh ((ssum @2 (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2, 0, 1] (sreplicate @2 m44)) + ssum @2 (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2, 0, 1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m42))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) in ssum @2 (stranspose @[2, 1, 0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * str (sreplicate @10 m45)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v37 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m38 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v37)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v39 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; v40 = tanh (sconcrete (sreplicate [2] 7.0) * v39 + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m41 = tanh (str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v40)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m42 = sappend m38 m41 ; v43 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m44 = tanh ((sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v43) + ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * stranspose @[2, 1, 0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m42))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m45 = tanh ((ssum @2 (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2, 0, 1] (sreplicate @2 m44)) + ssum @2 (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2, 0, 1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m42))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) in tpair (let m47 = (sconcrete (sreplicate [2,2] 1.0) + negate m45 * m45) * ssum @10 (str (stranspose @[2, 1, 0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @2 (sfromR dret))) ; m48 = (sconcrete (sreplicate [2,2] 1.0) + negate m44 * m44) * ssum @2 (stranspose @[1, 2, 0] (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m47)) ; m49 = sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (str (ssum @2 (stranspose @[2, 1, 0] (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * sreplicate @2 m48)))) (sconcrete (sreplicate [2,2] 0.0))) + sappend (sconcrete (sreplicate [2,2] 0.0)) (sappend (str (ssum @2 (stranspose @[1, 2, 0] (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m47)))) (sconcrete (sfromListLinear [0,2] []))) ; m50 = (sconcrete (sreplicate [2,2] 1.0) + negate m41 * m41) * sslice (SNat @2) (SNat @2) m49 ; m51 = sreplicate @2 (ssum @2 (str m50)) in tpair (let v52 = (sconcrete (sreplicate [2] 1.0) + negate v40 * v40) * ssum @2 (str (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * m51)) ; m53 = (sconcrete (sreplicate [2,2] 1.0) + negate m38 * m38) * sslice (SNat @0) (SNat @2) m49 in tpair (tpair (rfromS (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str m53))) + (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v52)) + str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 m48))))) (rfromS (str (ssum @2 (str (stranspose @[2, 1, 0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m42))) * sreplicate @2 m48)))))) (rfromS (ssum @2 (str m53) + (v52 + ssum @2 m48)))) (tpair (tpair (rfromS (str (str (sreplicate @2 v40) * m51) + str (ssum @2 (stranspose @[2, 0, 1] (stranspose @[2, 0, 1] (sreplicate @2 m44) * sreplicate @2 m47))))) (rfromS (str (ssum @2 (stranspose @[2, 0, 1] (stranspose @[2, 0, 1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m42))) * sreplicate @2 m47)))))) (rfromS (ssum @2 (str m50) + ssum @2 (str m47))))) (tpair (rfromS (ssum @2 (stranspose @[2, 1, 0] (str (sreplicate @10 m45) * sreplicate @2 (sfromR dret))))) (rfromS (ssum @2 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [2,2] STKScalar) (STKS [2,2] STKScalar)) (STKS [2] STKScalar)) (STKProduct (STKProduct (STKS [2,2] STKScalar) (STKS [2,2] STKScalar)) (STKS [2] STKScalar))) (STKProduct (STKS [10,2] STKScalar) (STKS [10] STKScalar))) (let m38 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v40 = tanh (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m41 = tanh (str (sreplicate @2 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 v40))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m42 = sappend m38 m41 ; m44 = tanh ((sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) + smatmul2 (str (sslice (SNat @0) (SNat @2) m42)) (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m45 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (str m44) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m42)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) in tpair (let m47 = (sconcrete (sreplicate [2,2] 1.0) + negate m45 * m45) * smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR dret) ; m48 = (sconcrete (sreplicate [2,2] 1.0) + negate m44 * m44) * smatmul2 (str m47) (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) ; m49 = sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) (str m48)) (sconcrete (sreplicate [2,2] 0.0)) + sappend (sconcrete (sreplicate [2,2] 0.0)) (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) m47) ; m50 = (sconcrete (sreplicate [2,2] 1.0) + negate m41 * m41) * sslice (SNat @2) (SNat @2) m49 ; v51 = ssum @2 (str m50) in tpair (let v52 = (sconcrete (sreplicate [2] 1.0) + negate v40 * v40) * sdot1In (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) (sreplicate @2 v51) ; m53 = (sconcrete (sreplicate [2,2] 1.0) + negate m38 * m38) * sslice (SNat @0) (SNat @2) m49 in tpair (tpair (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str m53))) + (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v52)) + str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 m48)))) (smatmul2 (str m48) (str (sslice (SNat @0) (SNat @2) m42)))) (ssum @2 (str m53) + (v52 + ssum @2 m48))) (tpair (tpair (sreplicate @2 v40 * str (sreplicate @2 v51) + smatmul2 m47 m44) (smatmul2 m47 (str (sslice (SNat @2) (SNat @2) m42)))) (ssum @2 (str m50) + ssum @2 (str m47)))) (tpair (smatmul2 (sfromR dret) (str m45)) (ssum @2 (str (sfromR dret)))))"

testRNNOAst2 :: Assertion
testRNNOAst2 = do
  let batch_size = 2
      sizeMnistHeightI = 2
      ftk = tftk @Concrete
                 (knownSTK @(X (ADRnnMnistParameters Concrete Double)))
                 (toTarget @Concrete $ valsInitRNNOPP 2 sizeMnistHeightI)
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKR 2 Double) afcnn1)
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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (let t252 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[7, 9, 4] (sfromPlain (stranspose @[2, 0, 3, 1] (sgather @[9, 2] (stranspose @[2, 0, 1] (sgather @[7, 2] (sconcrete (sreplicate [7,9] 7.0)) (\\[i440, i441] -> [i440 + i441]))) (\\[i246, i247] -> [i246 + i247]))) * sreplicate @7 (sreplicate @9 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; u265 = sreshape @[5, 3, 4, 4] (sfromPlain (sreplicate @5 (sgather @[3, 4, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i255, i256, i257, i258] -> [ifH (0.0 <=. negate (splainPart t252 `sindex0` [0, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i255, i257], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i256, i258]])) 0 1]))) * stranspose @[4, 0, 1, 2, 3] (sgather @[3, 4, 2, 2] (stranspose @[2, 1, 0] (sreplicate @5 (stranspose @[0, 2, 1] t252 !$ [0]))) (\\[i259, i260, i261, i262] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i259, i261], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i260, i262]]))) ; u275 = str (sreplicate @1 (ssum @4 (stranspose @[3, 0, 1, 2] (sreshape @[5, 3, 4, 4] (stranspose @[4, 0, 1, 2, 3] (sgather @[3, 4, 2, 2] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[3, 4, 5] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @2 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @2 (sreplicate @4 (sreplicate @3 (stranspose @[3, 2, 1, 0] u265))))))) (\\[i430, i431, i432] -> [i432, i430, i431, kargMax (splainPart u265 !$ [i432, i430, i431])]))) (\\[i269, i270, i271, i272] -> [i269, i270, i271, i272, i269 + i271, i270 + i272])) * sreplicate @5 (sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])))))))) + sreplicate @5 (stranspose @[2, 0, 1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; t285 = sreshape @[5, 2, 4] (sfromPlain (sgather @[5, 2, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278, i279, i280] -> [ifH (0.0 <=. negate (splainPart u275 `sindex0` [i277, 0, i279, sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i278, i280]])) 0 1])) * stranspose @[2, 0, 3, 1] (sgather @[2, 2] (stranspose @[1, 2, 0] (sslice (SNat @0) (SNat @2) (stranspose @[1, 2, 3, 0] u275 !$ [0]))) (\\[i281, i282] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i281, i282]]))) ; m290 = sreplicate @1 (sdot1In (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0])) (sreshape @[5, 2] (str (sreplicate @1 (str (sreplicate @1 (sgather @[5, 2] t285 (\\[i286, i287] -> [i286, i287, kargMax (splainPart t285 !$ [i286, i287])])))))))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) * sreplicate @10 (sfromPlain (sgather1 @5 (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\i291 -> [ifH (0.0 <=. negate (splainPart m290 `sindex0` [0, i291])) 0 1])) * m290 !$ [0]) + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [1,1,2,2] STKScalar) (STKS [1] STKScalar)) (STKProduct (STKS [1,1,2,2] STKScalar) (STKS [1] STKScalar))) (STKProduct (STKProduct (STKS [1,2] STKScalar) (STKS [1] STKScalar)) (STKProduct (STKS [10,1] STKScalar) (STKS [10] STKScalar)))) (let u250 = sgather @[9, 2] (stranspose @[2, 0, 1] (sgather @[7, 2] (sconcrete (sreplicate [7,9] 7.0)) (\\[i506, i507] -> [i506 + i507]))) (\\[i246, i247] -> [i246 + i247]) ; t252 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[7, 9, 4] (sfromPlain (stranspose @[2, 0, 3, 1] u250) * sreplicate @7 (sreplicate @9 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; u263 = sgather @[3, 4, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i255, i256, i257, i258] -> [ifH (0.0 <=. negate (splainPart t252 `sindex0` [0, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i255, i257], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i256, i258]])) 0 1]) ; u265 = sreshape @[5, 3, 4, 4] (sfromPlain (sreplicate @5 u263) * stranspose @[4, 0, 1, 2, 3] (sgather @[3, 4, 2, 2] (stranspose @[2, 1, 0] (sreplicate @5 (stranspose @[0, 2, 1] t252 !$ [0]))) (\\[i259, i260, i261, i262] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i259, i261], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i260, i262]]))) ; w273 = sgather @[3, 4, 2, 2] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[3, 4, 5] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @2 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @2 (sreplicate @4 (sreplicate @3 (stranspose @[3, 2, 1, 0] u265))))))) (\\[i496, i497, i498] -> [i498, i496, i497, kargMax (splainPart u265 !$ [i498, i496, i497])]))) (\\[i269, i270, i271, i272] -> [i269, i270, i271, i272, i269 + i271, i270 + i272]) ; m274 = sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0] ; u275 = str (sreplicate @1 (ssum @4 (stranspose @[3, 0, 1, 2] (sreshape @[5, 3, 4, 4] (stranspose @[4, 0, 1, 2, 3] w273 * sreplicate @5 (sreplicate @3 (sreplicate @4 m274))))))) + sreplicate @5 (stranspose @[2, 0, 1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; u283 = sgather @[5, 2, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278, i279, i280] -> [ifH (0.0 <=. negate (splainPart u275 `sindex0` [i277, 0, i279, sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i278, i280]])) 0 1]) ; t285 = sreshape @[5, 2, 4] (sfromPlain u283 * stranspose @[2, 0, 3, 1] (sgather @[2, 2] (stranspose @[1, 2, 0] (sslice (SNat @0) (SNat @2) (stranspose @[1, 2, 3, 0] u275 !$ [0]))) (\\[i281, i282] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i281, i282]]))) ; v288 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; m289 = sreshape @[5, 2] (str (sreplicate @1 (str (sreplicate @1 (sgather @[5, 2] t285 (\\[i286, i287] -> [i286, i287, kargMax (splainPart t285 !$ [i286, i287])])))))) ; m290 = sreplicate @1 (sdot1In (sreplicate @5 v288) m289) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v292 = sgather1 @5 (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\i291 -> [ifH (0.0 <=. negate (splainPart m290 `sindex0` [0, i291])) 0 1]) ; v297 = sfromPlain v292 * sdot1In (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) (str (sfromR dret)) in tpair (let t302 = sappend (stranspose @[2, 0, 1] (sscatter @[2, 2] (sfromPlain (stranspose @[1, 3, 0, 2] u283) * stranspose @[1, 3, 0, 2] (sreshape @[5, 2, 2, 2] (sscatter @[5, 2] (stranspose @[1, 2, 0] (sreshape @[5, 1, 1, 2] (sreplicate @5 v288 * str (sreplicate @2 v297))) !$ [0, 0]) (\\[i298, i299] -> [i298, i299, kargMax (splainPart t285 !$ [i298, i299])])))) (\\[i300, i301] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i300, i301]]))) (sconcrete (sreplicate [1,4,5] 0.0)) ; w303 = sreshape @[5, 3, 4, 2, 2] (stranspose @[1, 2, 3, 0] (sreplicate @4 (stranspose @[2, 0, 1] t302))) in tpair (let m315 = ssum @5 (stranspose @[2, 0, 1] (sscatter @[3, 4, 2, 2] (sfromPlain (stranspose @[1, 2, 3, 4, 0] (sreplicate @5 u263)) * stranspose @[1, 2, 3, 4, 0] (sreshape @[5, 3, 4, 2, 2] (ssum @3 (ssum @4 (ssum @2 (ssum @2 (stranspose @[7, 6, 5, 4, 0, 1, 2, 3] (sscatter @[3, 4, 5] (stranspose @[4, 5, 6, 0, 1, 2, 3] (sscatter @[3, 4, 2, 2] (stranspose @[1, 2, 3, 4, 0] (sreplicate @5 (sreplicate @3 (sreplicate @4 m274))) * stranspose @[1, 2, 3, 4, 0] w303) (\\[i304, i305, i306, i307] -> [i304, i305, i306, i307, i304 + i306, i305 + i307]))) (\\[i308, i309, i310] -> [i310, i308, i309, kargMax (splainPart u265 !$ [i310, i308, i309])]))))))))) (\\[i311, i312, i313, i314] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i311, i313], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i312, i314]]))) in tpair (sreplicate @1 (sreplicate @1 (ssum @9 (sdot1In (sfromPlain (stranspose @[0, 3, 1, 2] u250)) (stranspose @[1, 2, 3, 0] (sreshape @[7, 9, 2, 2] (stranspose @[1, 2, 0] (sreplicate @4 m315)))))))) (ssum @9 (ssum @7 (stranspose @[1, 2, 0] (sreplicate @1 m315))))) (tpair (sreplicate @1 (sreplicate @1 (ssum @4 (ssum @3 (sdot1In w273 (stranspose @[1, 2, 3, 4, 0] w303)))))) (ssum @4 (ssum @3 (ssum @5 (stranspose @[3, 1, 2, 0] (sreplicate @1 t302))))))) (tpair (tpair (sreplicate @1 (sdot1In (str m289) (sreplicate @2 v297))) (sreplicate @1 (ssum0 v297))) (tpair (str (sreplicate @1 (sdot1In (sreplicate @10 (sfromPlain v292 * m290 !$ [0])) (sfromR dret)))) (ssum @5 (str (sfromR dret))))))"

testCNNOAst1 :: Assertion
testCNNOAst1 = do
  let batch_size = 5
      sizeMnistWidthI = 7
      sizeMnistHeightI = 9
      ftk = tftk @Concrete
                 (knownSTK @(X (MnistCnnRanked2.ADCnnMnistParameters
                                  Concrete Double)))
                 vals
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKR 2 Double) afcnn1)
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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> rfromS (let t324 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain (sreplicate @4 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i541, i542] -> [i541 + i542]))) (\\[i318, i319] -> [i318 + i319])))) * str (sreplicate @14 (str (sreplicate @23 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; w338 = sreshape @[7, 4, 7, 11, 4] (sfromPlain (sreplicate @7 (sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i327, i328, i329, i330, i331] -> [ifH (0.0 <=. negate (splainPart t324 `sindex0` [i327, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i328, i330], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i329, i331]])) 0 1]))) * stranspose @[5, 4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[2, 1, 3, 0] (sreplicate @7 (stranspose @[2, 1, 0] t324))) (\\[i332, i333, i334, i335] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i332, i334], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i333, i335]]))) ; u348 = ssum @48 (stranspose @[4, 0, 1, 2, 3] (sreshape @[7, 4, 7, 11, 48] (str (sreplicate @4 (stranspose @[4, 0, 1, 5, 2, 3] (sgather @[7, 11, 3, 4] (stranspose @[4, 5, 6, 7, 0, 1, 2, 3] (sgather @[7, 11, 7, 4] (stranspose @[5, 4, 3, 2, 1, 8, 7, 6, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 7, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w338))))))) (\\[i532, i533, i534, i535] -> [i534, i535, i532, i533, kargMax (splainPart w338 !$ [i534, i535, i532, i533])]))) (\\[i343, i344, i345, i346] -> [i343, i344, i345, i346, i343 + i345, i344 + i346])))) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w363 = sreshape @[7, 4, 3, 5, 4] (sfromPlain (sgather @[7, 4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i351, i352, i353, i354, i355, i356] -> [ifH (0.0 <=. negate (splainPart u348 `sindex0` [i351, i352, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i353, i355], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i354, i356]])) 0 1])) * stranspose @[4, 5, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[2, 3, 0, 1] u348) (\\[i357, i358, i359, i360] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i357, i359], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i358, i360]]))) ; m370 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str (sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w363))) (\\[i364, i365, i366, i367] -> [i364, i365, i366, i367, kargMax (splainPart w363 !$ [i364, i365, i366, i367])])))) (\\i368 -> [i368, i368]))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in smatmul2 (sfromR (tproject1 (tproject2 (tproject2 u1)))) (sfromPlain (sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i371, i372] -> [ifH (0.0 <=. negate (splainPart m370 `sindex0` [i371, i372])) 0 1])) * m370) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [4,1,3,4] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [4,4,3,4] STKScalar) (STKS [4] STKScalar))) (STKProduct (STKProduct (STKS [5,60] STKScalar) (STKS [5] STKScalar)) (STKProduct (STKS [10,5] STKScalar) (STKS [10] STKScalar)))) (let u322 = sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i615, i616] -> [i615 + i616]))) (\\[i318, i319] -> [i318 + i319]) ; t324 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain (sreplicate @4 (stranspose @[2, 0, 3, 1] u322)) * str (sreplicate @14 (str (sreplicate @23 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; w336 = sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i327, i328, i329, i330, i331] -> [ifH (0.0 <=. negate (splainPart t324 `sindex0` [i327, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i328, i330], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i329, i331]])) 0 1]) ; w338 = sreshape @[7, 4, 7, 11, 4] (sfromPlain (sreplicate @7 w336) * stranspose @[5, 4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[2, 1, 3, 0] (sreplicate @7 (stranspose @[2, 1, 0] t324))) (\\[i332, i333, i334, i335] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i332, i334], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i333, i335]]))) ; w347 = sgather @[7, 11, 3, 4] (stranspose @[4, 5, 6, 7, 0, 1, 2, 3] (sgather @[7, 11, 7, 4] (stranspose @[5, 4, 3, 2, 1, 8, 7, 6, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 7, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w338))))))) (\\[i604, i605, i606, i607] -> [i606, i607, i604, i605, kargMax (splainPart w338 !$ [i606, i607, i604, i605])]))) (\\[i343, i344, i345, i346] -> [i343, i344, i345, i346, i343 + i345, i344 + i346]) ; u348 = ssum @48 (stranspose @[4, 0, 1, 2, 3] (sreshape @[7, 4, 7, 11, 48] (str (sreplicate @4 (stranspose @[4, 0, 1, 5, 2, 3] w347)) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w361 = sgather @[7, 4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i351, i352, i353, i354, i355, i356] -> [ifH (0.0 <=. negate (splainPart u348 `sindex0` [i351, i352, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i353, i355], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i354, i356]])) 0 1]) ; w363 = sreshape @[7, 4, 3, 5, 4] (sfromPlain w361 * stranspose @[4, 5, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[2, 3, 0, 1] u348) (\\[i357, i358, i359, i360] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i357, i359], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i358, i360]]))) ; m369 = sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w363))) (\\[i364, i365, i366, i367] -> [i364, i365, i366, i367, kargMax (splainPart w363 !$ [i364, i365, i366, i367])])))) (\\i368 -> [i368, i368]) ; m370 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str m369) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m373 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i371, i372] -> [ifH (0.0 <=. negate (splainPart m370 `sindex0` [i371, i372])) 0 1]) ; m376 = sfromPlain m373 * smatmul2 (str (sfromR (tproject1 (tproject2 (tproject2 u1))))) (sfromR dret) in tpair (let u386 = sscatter @[3, 5, 2, 2] (sfromPlain (stranspose @[2, 3, 4, 5, 0, 1] w361) * stranspose @[2, 3, 4, 5, 0, 1] (sreshape @[7, 4, 3, 5, 2, 2] (ssum @7 (stranspose @[5, 0, 1, 2, 3, 4] (sscatter @[7, 4, 3, 5] (stranspose @[1, 2, 3, 4, 0] (sreshape @[7, 7, 4, 3, 5] (sscatter1 @7 (smatmul2 (str m376) (sfromR (tproject1 (tproject1 (tproject2 u1))))) (\\i377 -> [i377, i377])))) (\\[i378, i379, i380, i381] -> [i378, i379, i380, i381, kargMax (splainPart w363 !$ [i378, i379, i380, i381])])))))) (\\[i382, i383, i384, i385] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i382, i384], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i383, i385]]) ; w387 = sreshape @[7, 4, 7, 11, 4, 3, 4] (stranspose @[1, 2, 3, 4, 0] (sreplicate @48 (stranspose @[2, 3, 0, 1] u386))) in tpair (let t400 = ssum @7 (stranspose @[3, 2, 0, 1] (sscatter @[7, 11, 2, 2] (sfromPlain (stranspose @[2, 3, 4, 5, 1, 0] (sreplicate @7 w336)) * stranspose @[2, 3, 4, 5, 1, 0] (sreshape @[7, 4, 7, 11, 2, 2] (ssum @7 (ssum @11 (ssum @3 (ssum @4 (stranspose @[8, 7, 6, 5, 0, 1, 2, 3, 4] (sscatter @[7, 11, 7, 4] (stranspose @[4, 5, 6, 7, 0, 1, 2, 3] (sscatter @[7, 11, 3, 4] (sdot1In (stranspose @[2, 3, 5, 6, 0, 4, 1] (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) (stranspose @[2, 3, 5, 6, 0, 4, 1] w387)) (\\[i388, i389, i390, i391] -> [i388, i389, i390, i391, i388 + i390, i389 + i391]))) (\\[i392, i393, i394, i395] -> [i394, i395, i392, i393, kargMax (splainPart w338 !$ [i394, i395, i392, i393])]))))))))) (\\[i396, i397, i398, i399] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i396, i398], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i397, i399]]))) in tpair (str (sreplicate @1 (ssum @23 (sdot1In (sfromPlain (stranspose @[2, 0, 3, 4, 1] (sreplicate @4 (stranspose @[2, 0, 3, 1] u322)))) (stranspose @[2, 0, 3, 4, 1] (sreshape @[4, 14, 23, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @12 t400)))))))) (ssum @23 (ssum @14 (stranspose @[1, 2, 0] t400)))) (tpair (ssum @11 (ssum @7 (sdot1In (stranspose @[2, 3, 0, 4, 5, 6, 1] (sreplicate @4 (stranspose @[4, 0, 1, 5, 2, 3] w347))) (stranspose @[2, 3, 1, 4, 5, 6, 0] w387)))) (ssum @11 (ssum @7 (ssum @7 (stranspose @[2, 0, 1] u386)))))) (tpair (tpair (smatmul2 m376 m369) (ssum @7 (str m376))) (tpair (smatmul2 (sfromR dret) (sfromPlain (str m373) * str m370)) (ssum @7 (str (sfromR dret))))))"

testCNNOAst2 :: Assertion
testCNNOAst2 = do
  let batch_size = 7
      sizeMnistWidthI = 14
      sizeMnistHeightI = 23
      ftk = tftk @Concrete
                 (knownSTK @(X (MnistCnnRanked2.ADCnnMnistParameters
                                  Concrete Double)))
                 vals
      varName = mkAstVarName ftk . intToAstVarId $ 100000000
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
                   (simplifyUserCode @(TKR 2 Double) afcnn1)
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
  printArtifactPrimalPretty (simplifyArtifactRev artifactRev)
    @?= "\\u1 -> let t274 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain (sreplicate @4 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i504, i505] -> [i504 + i505]))) (\\[i268, i269] -> [i268 + i269])))) * str (sreplicate @14 (str (sreplicate @23 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; w287 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[11, 2] (sfromPlain (sreplicate @11 (sgather @[23, 7, 4, 7, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i276, i277, i278, i279, i280] -> [ifH (0.0 <=. negate (splainPart t274 `sindex0` [i278, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i279, i280], i276])) 0 1]))) * stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 2] (stranspose @[2, 0, 3, 1] (sreplicate @7 (sreplicate @11 (str t274)))) (\\[i281, i282] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i281, i282]]))) (\\[i285, i286] -> [i285, 2 * i285 + i286]))) ; u297 = ssum @48 (stranspose @[4, 0, 1, 2, 3] (sreshape @[7, 4, 7, 11, 48] (str (sreplicate @4 (stranspose @[2, 3, 0, 4, 5, 1] (sgather @[11, 4] (stranspose @[3, 5, 2, 0, 4, 1] (sgather @[7, 3] (stranspose @[4, 6, 0, 3, 5, 2, 1] (sgather @[7, 11, 4, 7] (stranspose @[1, 2, 3, 4, 5, 7, 6, 0] (sreplicate @3 (stranspose @[6, 5, 4, 3, 2, 0, 1] (sreplicate @11 (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w287)))))) (\\[i488, i489, i490, i492] -> [i492, i490, i488, i489, kargMax (splainPart w287 !$ [i492, i490, i488, i489])]))) (\\[i496, i498] -> [i496, i498, i496 + i498]))) (\\[i294, i295] -> [i294, i294 + i295])))) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w310 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[5, 2] (sfromPlain (sreplicate @5 (sgather @[11, 7, 4, 3, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303] -> [ifH (0.0 <=. negate (splainPart u297 `sindex0` [i300, i301, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i302, i303], i299])) 0 1]))) * stranspose @[4, 5, 2, 3, 0, 1] (sgather @[3, 2] (stranspose @[1, 3, 2, 0] (sreplicate @5 (stranspose @[2, 1, 0] u297))) (\\[i304, i305] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i304, i305]]))) (\\[i308, i309] -> [i308, 2 * i308 + i309]))) ; m317 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str (sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w310))) (\\[i311, i312, i313, i314] -> [i311, i312, i313, i314, kargMax (splainPart w310 !$ [i311, i312, i313, i314])])))) (\\i315 -> [i315, i315]))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) in smatmul2 (tproject1 (tproject2 (tproject2 u1))) (sfromPlain (sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i318, i319] -> [ifH (0.0 <=. negate (splainPart m317 `sindex0` [i318, i319])) 0 1])) * m317) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w272 = sreplicate @4 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i270, i271] -> [i270 + i271]))) (\\[i268, i269] -> [i268 + i269]))) ; w273 = str (sreplicate @14 (str (sreplicate @23 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))) ; t274 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain w272 * w273))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; m275 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; w283 = sreplicate @11 (sgather @[23, 7, 4, 7, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i276, i277, i278, i279, i280] -> [ifH (0.0 <=. negate (splainPart t274 `sindex0` [i278, m275 `sindex0` [i279, i280], i276])) 0 1])) ; w284 = stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 2] (stranspose @[2, 0, 3, 1] (sreplicate @7 (sreplicate @11 (str t274)))) (\\[i281, i282] -> [m275 `sindex0` [i281, i282]])) ; w287 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[11, 2] (sfromPlain w283 * w284) (\\[i285, i286] -> [i285, 2 * i285 + i286]))) ; w296 = str (sreplicate @4 (stranspose @[2, 3, 0, 4, 5, 1] (sgather @[11, 4] (stranspose @[3, 5, 2, 0, 4, 1] (sgather @[7, 3] (stranspose @[4, 6, 0, 3, 5, 2, 1] (sgather @[7, 11, 4, 7] (stranspose @[1, 2, 3, 4, 5, 7, 6, 0] (sreplicate @3 (stranspose @[6, 5, 4, 3, 2, 0, 1] (sreplicate @11 (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w287)))))) (\\[i288, i289, i290, i291] -> [i291, i290, i288, i289, kargMax (splainPart w287 !$ [i291, i290, i288, i289])]))) (\\[i292, i293] -> [i292, i293, i292 + i293]))) (\\[i294, i295] -> [i294, i294 + i295])))) ; u297 = ssum @48 (stranspose @[4, 0, 1, 2, 3] (sreshape @[7, 4, 7, 11, 48] (w296 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; m298 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; w306 = sreplicate @5 (sgather @[11, 7, 4, 3, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303] -> [ifH (0.0 <=. negate (splainPart u297 `sindex0` [i300, i301, m298 `sindex0` [i302, i303], i299])) 0 1])) ; w307 = stranspose @[4, 5, 2, 3, 0, 1] (sgather @[3, 2] (stranspose @[1, 3, 2, 0] (sreplicate @5 (stranspose @[2, 1, 0] u297))) (\\[i304, i305] -> [m298 `sindex0` [i304, i305]])) ; w310 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[5, 2] (sfromPlain w306 * w307) (\\[i308, i309] -> [i308, 2 * i308 + i309]))) ; t316 = str (sreplicate @5 (str (sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w310))) (\\[i311, i312, i313, i314] -> [i311, i312, i313, i314, kargMax (splainPart w310 !$ [i311, i312, i313, i314])])))) (\\i315 -> [i315, i315])))) ; m317 = ssum @60 (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t316) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m320 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i318, i319] -> [ifH (0.0 <=. negate (splainPart m317 `sindex0` [i318, i319])) 0 1]) ; t321 = str (sreplicate @10 (sfromPlain m320 * m317)) in ssum @5 (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * t321) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w272 = sreplicate @4 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i270, i271] -> [i270 + i271]))) (\\[i268, i269] -> [i268 + i269]))) ; w273 = str (sreplicate @14 (str (sreplicate @23 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))) ; t274 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain w272 * w273))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; m275 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; w283 = sreplicate @11 (sgather @[23, 7, 4, 7, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i276, i277, i278, i279, i280] -> [ifH (0.0 <=. negate (splainPart t274 `sindex0` [i278, m275 `sindex0` [i279, i280], i276])) 0 1])) ; w284 = stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 2] (stranspose @[2, 0, 3, 1] (sreplicate @7 (sreplicate @11 (str t274)))) (\\[i281, i282] -> [m275 `sindex0` [i281, i282]])) ; w287 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[11, 2] (sfromPlain w283 * w284) (\\[i285, i286] -> [i285, 2 * i285 + i286]))) ; w296 = str (sreplicate @4 (stranspose @[2, 3, 0, 4, 5, 1] (sgather @[11, 4] (stranspose @[3, 5, 2, 0, 4, 1] (sgather @[7, 3] (stranspose @[4, 6, 0, 3, 5, 2, 1] (sgather @[7, 11, 4, 7] (stranspose @[1, 2, 3, 4, 5, 7, 6, 0] (sreplicate @3 (stranspose @[6, 5, 4, 3, 2, 0, 1] (sreplicate @11 (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w287)))))) (\\[i288, i289, i290, i291] -> [i291, i290, i288, i289, kargMax (splainPart w287 !$ [i291, i290, i288, i289])]))) (\\[i292, i293] -> [i292, i293, i292 + i293]))) (\\[i294, i295] -> [i294, i294 + i295])))) ; u297 = ssum @48 (stranspose @[4, 0, 1, 2, 3] (sreshape @[7, 4, 7, 11, 48] (w296 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; m298 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; w306 = sreplicate @5 (sgather @[11, 7, 4, 3, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303] -> [ifH (0.0 <=. negate (splainPart u297 `sindex0` [i300, i301, m298 `sindex0` [i302, i303], i299])) 0 1])) ; w307 = stranspose @[4, 5, 2, 3, 0, 1] (sgather @[3, 2] (stranspose @[1, 3, 2, 0] (sreplicate @5 (stranspose @[2, 1, 0] u297))) (\\[i304, i305] -> [m298 `sindex0` [i304, i305]])) ; w310 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[5, 2] (sfromPlain w306 * w307) (\\[i308, i309] -> [i308, 2 * i308 + i309]))) ; t316 = str (sreplicate @5 (str (sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w310))) (\\[i311, i312, i313, i314] -> [i311, i312, i313, i314, kargMax (splainPart w310 !$ [i311, i312, i313, i314])])))) (\\i315 -> [i315, i315])))) ; m317 = ssum @60 (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t316) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m320 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i318, i319] -> [ifH (0.0 <=. negate (splainPart m317 `sindex0` [i318, i319])) 0 1]) ; t321 = str (sreplicate @10 (sfromPlain m320 * m317)) ; m323 = sfromPlain m320 * ssum @10 (str (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * sreplicate @5 dret)) in tpair (let u333 = stranspose @[2, 1, 0] (ssum @5 (stranspose @[3, 0, 2, 1] (sscatter @[3, 2] (stranspose @[4, 5, 2, 3, 0, 1] (sfromPlain w306 * sscatter @[5, 2] (stranspose @[3, 5, 0, 1, 2, 4] (sreshape @[7, 4, 3, 5, 2, 2] (stranspose @[4, 3, 2, 1, 0] (ssum @7 (stranspose @[5, 4, 3, 2, 1, 0] (sscatter @[7, 4, 3, 5] (stranspose @[1, 2, 3, 4, 0] (sreshape @[7, 7, 4, 3, 5] (sscatter1 @7 (str (ssum @5 (str (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * sreplicate @60 m323)))) (\\i324 -> [i324, i324])))) (\\[i325, i326, i327, i328] -> [i325, i326, i327, i328, kargMax (splainPart w310 !$ [i325, i326, i327, i328])]))))))) (\\[i329, i330] -> [i329, 2 * i329 + i330]))) (\\[i331, i332] -> [m298 `sindex0` [i331, i332]])))) ; w334 = sreshape @[7, 4, 7, 11, 4, 3, 4] (stranspose @[1, 2, 3, 4, 0] (sreplicate @48 u333)) in tpair (let t347 = str (ssum @11 (ssum @7 (stranspose @[1, 3, 0, 2] (sscatter @[7, 2] (stranspose @[4, 5, 2, 3, 0, 1] (sfromPlain w283 * sscatter @[11, 2] (stranspose @[3, 5, 0, 1, 2, 4] (sreshape @[7, 4, 7, 11, 2, 2] (stranspose @[4, 3, 2, 1, 0] (ssum @7 (ssum @11 (stranspose @[5, 6, 4, 3, 2, 1, 0] (ssum @3 (stranspose @[7, 0, 1, 2, 3, 4, 6, 5] (sscatter @[7, 11, 4, 7] (stranspose @[2, 6, 5, 3, 0, 4, 1] (sscatter @[7, 3] (stranspose @[3, 5, 2, 0, 4, 1] (sscatter @[11, 4] (stranspose @[2, 5, 0, 1, 3, 4] (ssum @4 (str (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))) * w334)))) (\\[i335, i336] -> [i335, i335 + i336]))) (\\[i337, i338] -> [i337, i338, i337 + i338]))) (\\[i339, i340, i341, i342] -> [i342, i341, i339, i340, kargMax (splainPart w287 !$ [i342, i341, i339, i340])])))))))))) (\\[i343, i344] -> [i343, 2 * i343 + i344]))) (\\[i345, i346] -> [m275 `sindex0` [i345, i346]]))))) in tpair (str (soneHot (ssum @23 (str (ssum @14 (str (sfromPlain w272 * sreshape @[4, 14, 23, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @12 t347))))))) [0])) (ssum @23 (ssum @14 (stranspose @[1, 2, 0] t347)))) (tpair (ssum @11 (str (ssum @7 (str (ssum @7 (w296 * w334)))))) (ssum @11 (ssum @7 (stranspose @[1, 2, 0] (ssum @7 u333)))))) (tpair (tpair (ssum @7 (stranspose @[2, 1, 0] (t316 * sreplicate @60 m323))) (ssum @7 (str m323))) (tpair (ssum @7 (stranspose @[2, 1, 0] (t321 * sreplicate @5 dret))) (ssum @7 (str dret))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> let u272 = sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i586, i587] -> [i586 + i587]))) (\\[i268, i269] -> [i268 + i269]) ; t274 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain (sreplicate @4 (stranspose @[2, 0, 3, 1] u272)) * str (sreplicate @14 (str (sreplicate @23 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; w283 = sgather @[23, 7, 4, 7, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i276, i277, i278, i279, i280] -> [ifH (0.0 <=. negate (splainPart t274 `sindex0` [i278, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i279, i280], i276])) 0 1]) ; w287 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[11, 2] (sfromPlain (sreplicate @11 w283) * stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 2] (stranspose @[2, 0, 3, 1] (sreplicate @7 (sreplicate @11 (str t274)))) (\\[i281, i282] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i281, i282]]))) (\\[i285, i286] -> [i285, 2 * i285 + i286]))) ; w296 = sgather @[11, 4] (stranspose @[3, 5, 2, 0, 4, 1] (sgather @[7, 3] (stranspose @[4, 6, 0, 3, 5, 2, 1] (sgather @[7, 11, 4, 7] (stranspose @[1, 2, 3, 4, 5, 7, 6, 0] (sreplicate @3 (stranspose @[6, 5, 4, 3, 2, 0, 1] (sreplicate @11 (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w287)))))) (\\[i568, i569, i570, i572] -> [i572, i570, i568, i569, kargMax (splainPart w287 !$ [i572, i570, i568, i569])]))) (\\[i576, i578] -> [i576, i578, i576 + i578]))) (\\[i294, i295] -> [i294, i294 + i295]) ; u297 = ssum @48 (stranspose @[4, 0, 1, 2, 3] (sreshape @[7, 4, 7, 11, 48] (str (sreplicate @4 (stranspose @[2, 3, 0, 4, 5, 1] w296)) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w306 = sgather @[11, 7, 4, 3, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i299, i300, i301, i302, i303] -> [ifH (0.0 <=. negate (splainPart u297 `sindex0` [i300, i301, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i302, i303], i299])) 0 1]) ; w310 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[5, 2] (sfromPlain (sreplicate @5 w306) * stranspose @[4, 5, 2, 3, 0, 1] (sgather @[3, 2] (stranspose @[1, 3, 2, 0] (sreplicate @5 (stranspose @[2, 1, 0] u297))) (\\[i304, i305] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i304, i305]]))) (\\[i308, i309] -> [i308, 2 * i308 + i309]))) ; m316 = sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w310))) (\\[i311, i312, i313, i314] -> [i311, i312, i313, i314, kargMax (splainPart w310 !$ [i311, i312, i313, i314])])))) (\\i315 -> [i315, i315]) ; m317 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str m316) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m320 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i318, i319] -> [ifH (0.0 <=. negate (splainPart m317 `sindex0` [i318, i319])) 0 1]) ; m323 = sfromPlain m320 * smatmul2 (str (tproject1 (tproject2 (tproject2 u1)))) dret in tpair (let u333 = ssum @5 (stranspose @[3, 1, 2, 0] (sscatter @[3, 2] (sfromPlain (stranspose @[4, 5, 2, 3, 0, 1] (sreplicate @5 w306)) * stranspose @[4, 5, 2, 3, 0, 1] (sscatter @[5, 2] (stranspose @[3, 5, 0, 1, 2, 4] (sreshape @[7, 4, 3, 5, 2, 2] (ssum @7 (stranspose @[5, 0, 1, 2, 3, 4] (sscatter @[7, 4, 3, 5] (stranspose @[1, 2, 3, 4, 0] (sreshape @[7, 7, 4, 3, 5] (sscatter1 @7 (smatmul2 (str m323) (tproject1 (tproject1 (tproject2 u1)))) (\\i324 -> [i324, i324])))) (\\[i325, i326, i327, i328] -> [i325, i326, i327, i328, kargMax (splainPart w310 !$ [i325, i326, i327, i328])])))))) (\\[i329, i330] -> [i329, 2 * i329 + i330]))) (\\[i331, i332] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i331, i332]]))) ; w334 = sreshape @[7, 4, 7, 11, 4, 3, 4] (stranspose @[1, 2, 3, 4, 0] (sreplicate @48 u333)) in tpair (let t347 = ssum @11 (ssum @7 (stranspose @[1, 3, 2, 0] (sscatter @[7, 2] (sfromPlain (stranspose @[4, 5, 2, 3, 0, 1] (sreplicate @11 w283)) * stranspose @[4, 5, 2, 3, 0, 1] (sscatter @[11, 2] (stranspose @[3, 5, 0, 1, 2, 4] (sreshape @[7, 4, 7, 11, 2, 2] (ssum @7 (ssum @11 (ssum @3 (stranspose @[7, 6, 5, 0, 1, 2, 3, 4] (sscatter @[7, 11, 4, 7] (stranspose @[2, 6, 5, 3, 0, 4, 1] (sscatter @[7, 3] (stranspose @[3, 5, 2, 0, 4, 1] (sscatter @[11, 4] (sdot1In (stranspose @[3, 6, 0, 2, 4, 5, 1] (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) (stranspose @[3, 6, 0, 2, 4, 5, 1] w334)) (\\[i335, i336] -> [i335, i335 + i336]))) (\\[i337, i338] -> [i337, i338, i337 + i338]))) (\\[i339, i340, i341, i342] -> [i342, i341, i339, i340, kargMax (splainPart w287 !$ [i342, i341, i339, i340])])))))))) (\\[i343, i344] -> [i343, 2 * i343 + i344]))) (\\[i345, i346] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i345, i346]])))) in tpair (str (sreplicate @1 (ssum @23 (sdot1In (sfromPlain (stranspose @[2, 0, 3, 4, 1] (sreplicate @4 (stranspose @[2, 0, 3, 1] u272)))) (stranspose @[2, 0, 3, 4, 1] (sreshape @[4, 14, 23, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @12 t347)))))))) (ssum @23 (ssum @14 (stranspose @[1, 2, 0] t347)))) (tpair (ssum @11 (ssum @7 (sdot1In (stranspose @[2, 3, 0, 4, 5, 6, 1] (sreplicate @4 (stranspose @[2, 3, 0, 4, 5, 1] w296))) (stranspose @[2, 3, 1, 4, 5, 6, 0] w334)))) (ssum @11 (ssum @7 (ssum @7 (stranspose @[0, 2, 3, 1] u333)))))) (tpair (tpair (smatmul2 m323 m316) (ssum @7 (str m323))) (tpair (smatmul2 dret (sfromPlain (str m320) * str m317)) (ssum @7 (str dret))))"
