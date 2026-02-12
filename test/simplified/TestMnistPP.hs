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
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [kfromS (ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate @784 (sscalar 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate @784 (sscalar 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate @784 (sscalar 7.0))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [kfromS (ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4))]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [kfromS (ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v5)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v5))]) + tproject2 (tproject2 v1))"
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [kfromS (ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate @784 (sscalar 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate @784 (sscalar 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate @784 (sscalar 7.0))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [kfromS (ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4))]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate @4 (sfromR dret !$ [9]) ; v8 = sreplicate @4 (sfromR dret !$ [8]) ; v9 = sreplicate @4 (sfromR dret !$ [7]) ; v10 = sreplicate @4 (sfromR dret !$ [6]) ; v11 = sreplicate @4 (sfromR dret !$ [5]) ; v12 = sreplicate @4 (sfromR dret !$ [4]) ; v13 = sreplicate @4 (sfromR dret !$ [3]) ; v14 = sreplicate @4 (sfromR dret !$ [2]) ; v15 = sreplicate @4 (sfromR dret !$ [1]) ; v16 = sreplicate @4 (sfromR dret !$ [0]) in tpair (let v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7)))))))) ; v18 = sreplicate @3 (v17 !$ [3]) ; v19 = sreplicate @3 (v17 !$ [2]) ; v20 = sreplicate @3 (v17 !$ [1]) ; v21 = sreplicate @3 (v17 !$ [0]) in tpair (let v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)) in tpair (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v22 !$ [0])) (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v22 !$ [1])) (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v22 !$ [2])) Z1))) v22) (tpair (tpair (v4 * v21) (tpair (v4 * v20) (tpair (v4 * v19) (tpair (v4 * v18) Z1)))) v17)) (tpair (tpair (v5 * v16) (tpair (v5 * v15) (tpair (v5 * v14) (tpair (v5 * v13) (tpair (v5 * v12) (tpair (v5 * v11) (tpair (v5 * v10) (tpair (v5 * v9) (tpair (v5 * v8) (tpair (v5 * v7) Z1)))))))))) (sfromR dret))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) ; x7 = sfromR dret !$ [9] ; x8 = sfromR dret !$ [8] ; x9 = sfromR dret !$ [7] ; x10 = sfromR dret !$ [6] ; x11 = sfromR dret !$ [5] ; x12 = sfromR dret !$ [4] ; x13 = sfromR dret !$ [3] ; x14 = sfromR dret !$ [2] ; x15 = sfromR dret !$ [1] ; x16 = sfromR dret !$ [0] in tpair (let v17 = tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x7)))))))) ; x18 = v17 !$ [3] ; x19 = v17 !$ [2] ; x20 = v17 !$ [1] ; x21 = v17 !$ [0] in tpair (let v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x18)) in tpair (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v22 !$ [0])) (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v22 !$ [1])) (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v22 !$ [2])) Z1))) v22) (tpair (tpair (v4 * sreplicate @3 x21) (tpair (v4 * sreplicate @3 x20) (tpair (v4 * sreplicate @3 x19) (tpair (v4 * sreplicate @3 x18) Z1)))) v17)) (tpair (tpair (v5 * sreplicate @4 x16) (tpair (v5 * sreplicate @4 x15) (tpair (v5 * sreplicate @4 x14) (tpair (v5 * sreplicate @4 x13) (tpair (v5 * sreplicate @4 x12) (tpair (v5 * sreplicate @4 x11) (tpair (v5 * sreplicate @4 x10) (tpair (v5 * sreplicate @4 x9) (tpair (v5 * sreplicate @4 x8) (tpair (v5 * sreplicate @4 x7) Z1)))))))))) (sfromR dret))"

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
    @?= "\\v1 -> rfromS (let v12 = recip (scast (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1)))))) ; v14 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v12, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v12, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v12, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v12]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v16 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v14, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v14]) + tproject2 (tproject2 v1)) in sreplicate @10 (recip (sfromK (ssum0 v16))) * v16)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\v1 -> rfromS (let v9 = sfromVector (fromList [kfromS (ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate @784 (sscalar 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate @784 (sscalar 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate @784 (sscalar 7.0))))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate v9)) ; v12 = scast v10 ; v13 = scast (sfromVector (fromList [kfromS (ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v12)), kfromS (ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v12)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v12)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v12))])) + tproject2 (tproject2 (tproject1 v1)) ; v14 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate v13)) ; v16 = exp (sfromVector (fromList [kfromS (ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v14))]) + tproject2 (tproject2 v1)) ; x17 = kfromS (ssum @10 v16) ; v18 = sreplicate @10 (recip (sfromK x17)) in v18 * v16)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret v1 -> let v9 = sfromVector (fromList [kfromS (ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate @784 (sscalar 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate @784 (sscalar 7.0)))), kfromS (ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate @784 (sscalar 7.0))))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate v9)) ; v11 = v10 * (sconcrete (sreplicate [3] 1.0) + negate v10) ; v12 = scast v10 ; v13 = scast (sfromVector (fromList [kfromS (ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v12)), kfromS (ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v12)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v12)), kfromS (ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v12))])) + tproject2 (tproject2 (tproject1 v1)) ; v14 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate v13)) ; v15 = v14 * (sconcrete (sreplicate [4] 1.0) + negate v14) ; v16 = exp (sfromVector (fromList [kfromS (ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v14)), kfromS (ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v14))]) + tproject2 (tproject2 v1)) ; x17 = kfromS (ssum @10 v16) ; v18 = sreplicate @10 (recip (sfromK x17)) ; v20 = v16 * (sreplicate @10 (negate (recip (sfromK (x17 * x17))) * ssum @10 (v16 * sfromR dret)) + v18 * sfromR dret) ; v21 = sreplicate @4 (v20 !$ [9]) ; v22 = sreplicate @4 (v20 !$ [8]) ; v23 = sreplicate @4 (v20 !$ [7]) ; v24 = sreplicate @4 (v20 !$ [6]) ; v25 = sreplicate @4 (v20 !$ [5]) ; v26 = sreplicate @4 (v20 !$ [4]) ; v27 = sreplicate @4 (v20 !$ [3]) ; v28 = sreplicate @4 (v20 !$ [2]) ; v29 = sreplicate @4 (v20 !$ [1]) ; v30 = sreplicate @4 (v20 !$ [0]) in tpair (let v31 = v15 * (tproject1 (tproject1 (tproject2 v1)) * v30 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v29 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v28 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v27 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v26 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v25 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v24 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v23 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v22 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v21))))))))) ; v32 = scast v31 ; v33 = sreplicate @3 (v32 !$ [3]) ; v34 = sreplicate @3 (v32 !$ [2]) ; v35 = sreplicate @3 (v32 !$ [1]) ; v36 = sreplicate @3 (v32 !$ [0]) in tpair (let v37 = v11 * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v36 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v35 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v34 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v33))) in tpair (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v37 !$ [0])) (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v37 !$ [1])) (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v37 !$ [2])) Z1))) v37) (tpair (tpair (v12 * v36) (tpair (v12 * v35) (tpair (v12 * v34) (tpair (v12 * v33) Z1)))) v31)) (tpair (tpair (v14 * v30) (tpair (v14 * v29) (tpair (v14 * v28) (tpair (v14 * v27) (tpair (v14 * v26) (tpair (v14 * v25) (tpair (v14 * v24) (tpair (v14 * v23) (tpair (v14 * v22) (tpair (v14 * v21) Z1)))))))))) v20)"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret v1 -> let v10 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [7.0 * ssum0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1))))) ; v12 = scast v10 ; v14 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v12, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v12, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v12, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v12]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v16 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v14, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v14, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v14]) + tproject2 (tproject2 v1)) ; x17 = ssum0 v16 ; v20 = v16 * (sreplicate @10 (negate (recip (sfromK (x17 * x17))) * sfromK (sdot0 v16 (sfromR dret))) + sreplicate @10 (recip (sfromK x17)) * sfromR dret) ; x21 = v20 !$ [9] ; x22 = v20 !$ [8] ; x23 = v20 !$ [7] ; x24 = v20 !$ [6] ; x25 = v20 !$ [5] ; x26 = v20 !$ [4] ; x27 = v20 !$ [3] ; x28 = v20 !$ [2] ; x29 = v20 !$ [1] ; x30 = v20 !$ [0] in tpair (let v31 = (v14 * (sconcrete (sreplicate [4] 1.0) + negate v14)) * (tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x30 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x29 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x28 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x27 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x26 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x25 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x24 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x23 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x22 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x21))))))))) ; v32 = scast v31 ; x33 = v32 !$ [3] ; x34 = v32 !$ [2] ; x35 = v32 !$ [1] ; x36 = v32 !$ [0] in tpair (let v37 = (v10 * (sconcrete (sreplicate [3] 1.0) + negate v10)) * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x36 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x35 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x34 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x33))) in tpair (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v37 !$ [0])) (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v37 !$ [1])) (tpair (sfromPlain (sreplicate @784 (sscalar 7.0)) * sreplicate @784 (v37 !$ [2])) Z1))) v37) (tpair (tpair (v12 * sreplicate @3 x36) (tpair (v12 * sreplicate @3 x35) (tpair (v12 * sreplicate @3 x34) (tpair (v12 * sreplicate @3 x33) Z1)))) v31)) (tpair (tpair (v14 * sreplicate @4 x30) (tpair (v14 * sreplicate @4 x29) (tpair (v14 * sreplicate @4 x28) (tpair (v14 * sreplicate @4 x27) (tpair (v14 * sreplicate @4 x26) (tpair (v14 * sreplicate @4 x25) (tpair (v14 * sreplicate @4 x24) (tpair (v14 * sreplicate @4 x23) (tpair (v14 * sreplicate @4 x22) (tpair (v14 * sreplicate @4 x21) Z1)))))))))) v20)"

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
    @?= "\\dummy -> rfromS (tlet (exp (ssum @5 (str (sreplicate @2 (tlet (ssum @4 (tfromPlain (STKS [4,5] STKScalar) (sconcrete (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0])) * tfromPrimal (STKS [4,5] STKScalar) (str (sreplicate @5 (tlet (sconcrete (sreplicate [4] 7.0) * ssum @3 (str (scast (sconcrete (sfromListLinear [4,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0])))) + scast (sconcrete (sfromListLinear [4] [1.0,2.0,3.0,4.0]))) (\\v7 -> recip (tfromPlain (STKS [4] STKScalar) (sconcrete (sreplicate [4] 1.0)) + exp (tfromPlain (STKS [4] STKScalar) (negate v7)))))))) + tfromPlain (STKS [5] STKScalar) (scast (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v8 -> tletPrimal (recip (tfromPlain (STKS [5] STKScalar) (sconcrete (sreplicate [5] 1.0)) + tprimalPart (exp (negate v8)))) (\\v9 -> tfromPrimal (STKS [5] STKScalar) v9 + tfromDual (sfromR (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [5] STKScalar) (v9 * (tfromPlain (STKS [5] STKScalar) (sconcrete (sreplicate [5] 1.0)) + negate v9)) * tfromDual (sfromR (tdualPart (STKR (SNat @1) STKScalar) (rfromS v8))))))))))) * tfromPlain (STKS [5,2] STKScalar) (str (scast (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))))) + tfromPlain (STKS [2] STKScalar) (scast (sconcrete (sfromListLinear [2] [1.0,2.0]))))) (\\v10 -> sreplicate @2 (recip (sfromK (ssum @2 v10))) * v10))"
  "\\dummy" ++ " -> " ++ printAstSimple (simplifyInlineContract ast3)
    @?= "\\dummy -> tfromPlain (STKR (SNat @1) STKScalar) (rfromS (sconcrete (sfromListLinear [2] [8885746.0,2.415394e7]) * sreplicate @2 (recip (sscalar 3.3039686e7))))"

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
    @?= "\\m1 -> rfromS (let v18 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (recip (scast (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in sreplicate @2 (recip (sfromK (ssum0 v18))) * v18)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> rfromS (let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate v11)) ; m14 = str (sreplicate @5 (scast v12)) ; v15 = scast (ssum @4 (m14 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v16 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate v15)) ; v18 = exp (ssum @5 (str (sreplicate @2 v16) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x19 = kfromS (ssum @2 v18) ; v20 = sreplicate @2 (recip (sfromK x19)) in v20 * v18)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate v11)) ; v13 = v12 * (sconcrete (sreplicate [4] 1.0) + negate v12) ; m14 = str (sreplicate @5 (scast v12)) ; v15 = scast (ssum @4 (m14 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v16 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate v15)) ; v17 = v16 * (sconcrete (sreplicate [5] 1.0) + negate v16) ; v18 = exp (ssum @5 (str (sreplicate @2 v16) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x19 = kfromS (ssum @2 v18) ; v20 = sreplicate @2 (recip (sfromK x19)) ; v22 = v18 * (sreplicate @2 (negate (recip (sfromK (x19 * x19))) * ssum @2 (v18 * sfromR dret)) + v20 * sfromR dret) in tpair (let v23 = v17 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v22)) ; m24 = sreplicate @4 (scast v23) in tpair (let v25 = v13 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m24))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v25)))) (rfromS v25)) (tpair (rfromS (str (m14 * m24))) (rfromS v23))) (tpair (rfromS (str (str (sreplicate @2 v16) * sreplicate @5 v22))) (rfromS v22))"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v12 = recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v14 = scast v12 ; v16 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v14) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v18 = exp (sdot1In (sreplicate @2 v16) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x19 = ssum0 v18 ; v22 = v18 * (sreplicate @2 (negate (recip (sfromK (x19 * x19))) * sfromK (sdot0 v18 (sfromR dret))) + sreplicate @2 (recip (sfromK x19)) * sfromR dret) in tpair (let v23 = (v16 * (sconcrete (sreplicate [5] 1.0) + negate v16)) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v22) ; v24 = scast v23 in tpair (let v25 = (v12 * (sconcrete (sreplicate [4] 1.0) + negate v12)) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v24)) in tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v25))) v25) (tpair (sreplicate @5 v14 * str (sreplicate @4 v24)) v23)) (tpair (sreplicate @2 v16 * str (sreplicate @5 v22)) v22))"

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
    @?= "\\m1 -> let v18 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (recip (scast (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in (-8.0) * ssum0 (log (sreplicate @2 (recip (sfromK (ssum0 v18))) * v18))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate v11)) ; m14 = str (sreplicate @5 (scast v12)) ; v15 = scast (ssum @4 (m14 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v16 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate v15)) ; v18 = exp (ssum @5 (str (sreplicate @2 v16) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x19 = kfromS (ssum @2 v18) ; v20 = sreplicate @2 (recip (sfromK x19)) ; v21 = v20 * v18 ; x22 = kfromS (ssum @2 (log v21)) in (-8.0) * x22"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate v11)) ; v13 = v12 * (sconcrete (sreplicate [4] 1.0) + negate v12) ; m14 = str (sreplicate @5 (scast v12)) ; v15 = scast (ssum @4 (m14 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v16 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate v15)) ; v17 = v16 * (sconcrete (sreplicate [5] 1.0) + negate v16) ; v18 = exp (ssum @5 (str (sreplicate @2 v16) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x19 = kfromS (ssum @2 v18) ; v20 = sreplicate @2 (recip (sfromK x19)) ; v21 = v20 * v18 ; v24 = recip v21 * sreplicate @2 (sfromK ((-8.0) * dret)) ; v25 = v18 * (sreplicate @2 (negate (recip (sfromK (x19 * x19))) * ssum @2 (v18 * v24)) + v20 * v24) in tpair (let v26 = v17 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v25)) ; m27 = sreplicate @4 (scast v26) in tpair (let v28 = v13 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m27))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v28)))) (rfromS v28)) (tpair (rfromS (str (m14 * m27))) (rfromS v26))) (tpair (rfromS (str (str (sreplicate @2 v16) * sreplicate @5 v25))) (rfromS v25))"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v12 = recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v14 = scast v12 ; v16 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v14) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v18 = exp (sdot1In (sreplicate @2 v16) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x19 = ssum0 v18 ; x20 = recip (sfromK x19) ; v24 = recip (sreplicate @2 x20 * v18) * sreplicate @2 ((-8.0) * dret) ; v25 = v18 * (sreplicate @2 (negate (recip (sfromK (x19 * x19))) * sfromK (sdot0 v18 v24)) + sreplicate @2 x20 * v24) in tpair (let v26 = (v16 * (sconcrete (sreplicate [5] 1.0) + negate v16)) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v25) ; v27 = scast v26 in tpair (let v28 = (v12 * (sconcrete (sreplicate [4] 1.0) + negate v12)) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v27)) in tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v28))) v28) (tpair (sreplicate @5 v14 * str (sreplicate @4 v27)) v26)) (tpair (sreplicate @2 v16 * str (sreplicate @5 v25)) v25))"

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
    @?= "\\m1 -> rfromS (let x16 = kfromS (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) ; x17 = kfromS (tanh (sfromK (7.0 * x16) + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0])) ; x18 = kfromS (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0]) ; x19 = kfromS (tanh (sfromK (x18 * x17) + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0])) ; v20 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] in str (sreplicate @1 (v20 * sreplicate @10 (sfromK x19))) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let x16 = kfromS (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) ; x17 = kfromS (tanh (sfromK (7.0 * x16) + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0])) ; x18 = kfromS (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0]) ; x19 = kfromS (tanh (sfromK (x18 * x17) + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0])) in tpair (let v20 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] ; x22 = kfromS (sfromK (1.0 + negate x19 * x19) * ssum @10 (v20 * ssum @1 (str (sfromR dret)))) in tpair (let x23 = (1.0 + negate x17 * x17) * (x18 * x22) in tpair (tpair (rfromS (soneHot (sfromK (7.0 * x23)) [0, 0])) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (rfromS (soneHot (sfromK x23) [0]))) (tpair (tpair (rfromS (soneHot (sfromK (x17 * x22)) [0, 0])) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (rfromS (soneHot (sfromK x22) [0])))) (tpair (rfromS (str (soneHot (sreplicate @10 (sfromK x19) * ssum @1 (str (sfromR dret))) [0]))) (rfromS (ssum @1 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) ConvId) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) ConvId) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKR (SNat @2) STKScalar)) (STKS [1] STKScalar)) (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKR (SNat @2) STKScalar)) (STKS [1] STKScalar))) (STKProduct (STKS [10,1] STKScalar) (STKS [10] STKScalar))) (let x17 = tanh (7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0]) in tpair (let x22 = (1.0 + negate x19 * x19) * sdot0 (str (sfromR (tproject1 (tproject2 m1))) !$ [0]) (str (sfromR dret) !$ [0]) in tpair (let x23 = (1.0 + negate x17 * x17) * (x18 * x22) in tpair (tpair (sreplicate @1 (sreplicate @1 (7.0 * x23))) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (sreplicate @1 x23)) (tpair (tpair (sreplicate @1 (sreplicate @1 (x17 * x22))) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (sreplicate @1 x22))) (tpair (str (sreplicate @1 (sreplicate @10 x19 * str (sfromR dret) !$ [0]))) (str (sfromR dret) !$ [0])))"

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
    @?= "\\u1 -> rfromS (let t160 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[7, 9, 4] (sfromPlain (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[9, 2] (stranspose @[2, 0, 1] (sgather @[7, 2] (sconcrete (sreplicate [7,9] 7.0)) (\\[i285, i286] -> [i285 + i286]))) (\\[i154, i155] -> [i154 + i155]))))))) * sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; t175 = sreshape @[3, 4, 4] (sfromPlain (sgather @[3, 4, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i163, i164, i165, i166] -> [ifH (0.0 <=. kplainPart (negate (t160 `sindex0` [0, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i163, i165], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i164, i166]]))) 0 1])) * sgather @[3, 4, 2, 2] (t160 !$ [0]) (\\[i169, i170, i171, i172] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i169, i171], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i170, i172]])) ; t184 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[3, 4, 4] (sgather @[3, 4, 2, 2] (sgather @[3, 4] (stranspose @[6, 5, 4, 0, 1, 2, 3] (sreplicate @3 (sreplicate @4 (sreplicate @2 (sreplicate @2 (stranspose @[2, 1, 0] t175)))))) (\\[i176, i177] -> [i176, i177, kargMax (splainPart t175 !$ [i176, i177])])) (\\[i178, i179, i180, i181] -> [i178 + i180, i179 + i181, i178, i179, i180, i181]) * sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])))))) + stranspose @[2, 0, 1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m194 = sreshape @[2, 4] (sfromPlain (sgather @[2, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i186, i187, i188] -> [ifH (0.0 <=. kplainPart (negate (t184 `sindex0` [0, i187, sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i186, i188]]))) 0 1])) * stranspose @[0, 2, 1] (sgather @[2, 2] (str (sslice (SNat @0) (SNat @2) (t184 !$ [0]))) (\\[i190, i191] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i190, i191]]))) ; m198 = sreplicate @1 (sreplicate @5 (sdot0 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0]) (sgather1 @2 m194 (\\i195 -> [i195, kargMax (splainPart m194 !$ [i195])])))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) * sreplicate @10 (sfromPlain (sgather1 @5 (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\i199 -> [ifH (0.0 <=. kplainPart (negate (m198 `sindex0` [0, i199]))) 0 1])) * m198 !$ [0]) + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (let w158 = stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[9, 2] (stranspose @[2, 0, 1] (sgather @[7, 2] (sconcrete (sreplicate [7,9] 7.0)) (\\[i156, i157] -> [i156 + i157]))) (\\[i154, i155] -> [i154 + i155])))))) ; w159 = sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))) ; t160 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[7, 9, 4] (sfromPlain w158 * w159)))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m161 = str (sreplicate @2 (sconcrete (sreplicate [4] 2) * siota (SNat @4))) + sreplicate @4 (siota (SNat @2)) ; m162 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; u173 = sgather @[3, 4, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i163, i164, i165, i166] -> [let i167 = kfromS (m161 !$ [i164, i166]) ; i168 = kfromS (m162 !$ [i163, i165]) in ifH (0.0 <=. kplainPart (negate (kfromS (t160 !$ [0, i168, i167])))) 0 1]) ; u174 = sgather @[3, 4, 2, 2] (t160 !$ [0]) (\\[i169, i170, i171, i172] -> [kfromS (m162 !$ [i169, i171]), kfromS (m161 !$ [i170, i172])]) ; t175 = sreshape @[3, 4, 4] (sfromPlain u173 * u174) ; u182 = sgather @[3, 4, 2, 2] (sgather @[3, 4] (stranspose @[6, 5, 4, 0, 1, 2, 3] (sreplicate @3 (sreplicate @4 (sreplicate @2 (sreplicate @2 (stranspose @[2, 1, 0] t175)))))) (\\[i176, i177] -> [i176, i177, kargMax (splainPart t175 !$ [i176, i177])])) (\\[i178, i179, i180, i181] -> [i178 + i180, i179 + i181, i178, i179, i180, i181]) ; u183 = sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])) ; t184 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[3, 4, 4] (u182 * u183)))) + stranspose @[2, 0, 1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m185 = str (sreplicate @2 (sconcrete (sreplicate [2] 2) * siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) ; t192 = sgather @[2, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i186, i187, i188] -> [let i189 = kfromS (m185 !$ [i186, i188]) in ifH (0.0 <=. kplainPart (negate (kfromS (t184 !$ [0, i187, i189])))) 0 1]) ; t193 = stranspose @[0, 2, 1] (sgather @[2, 2] (str (sslice (SNat @0) (SNat @2) (t184 !$ [0]))) (\\[i190, i191] -> [kfromS (m185 !$ [i190, i191])])) ; m194 = sreshape @[2, 4] (sfromPlain t192 * t193) ; v196 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v197 = sgather1 @2 m194 (\\i195 -> [i195, kargMax (splainPart m194 !$ [i195])]) ; m198 = sreplicate @1 (sreplicate @5 (ssum @2 (v196 * v197))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v200 = sgather1 @5 (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\i199 -> [ifH (0.0 <=. kplainPart (negate (kfromS (m198 !$ [0, i199])))) 0 1]) ; v201 = m198 !$ [0] ; m202 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m203 = sreplicate @10 (sfromPlain v200 * v201) in m202 * m203 + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w158 = stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[9, 2] (stranspose @[2, 0, 1] (sgather @[7, 2] (sconcrete (sreplicate [7,9] 7.0)) (\\[i156, i157] -> [i156 + i157]))) (\\[i154, i155] -> [i154 + i155])))))) ; w159 = sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))) ; t160 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[7, 9, 4] (sfromPlain w158 * w159)))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m161 = str (sreplicate @2 (sconcrete (sreplicate [4] 2) * siota (SNat @4))) + sreplicate @4 (siota (SNat @2)) ; m162 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; u173 = sgather @[3, 4, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i163, i164, i165, i166] -> [let i167 = kfromS (m161 !$ [i164, i166]) ; i168 = kfromS (m162 !$ [i163, i165]) in ifH (0.0 <=. kplainPart (negate (kfromS (t160 !$ [0, i168, i167])))) 0 1]) ; u174 = sgather @[3, 4, 2, 2] (t160 !$ [0]) (\\[i169, i170, i171, i172] -> [kfromS (m162 !$ [i169, i171]), kfromS (m161 !$ [i170, i172])]) ; t175 = sreshape @[3, 4, 4] (sfromPlain u173 * u174) ; u182 = sgather @[3, 4, 2, 2] (sgather @[3, 4] (stranspose @[6, 5, 4, 0, 1, 2, 3] (sreplicate @3 (sreplicate @4 (sreplicate @2 (sreplicate @2 (stranspose @[2, 1, 0] t175)))))) (\\[i176, i177] -> [i176, i177, kargMax (splainPart t175 !$ [i176, i177])])) (\\[i178, i179, i180, i181] -> [i178 + i180, i179 + i181, i178, i179, i180, i181]) ; u183 = sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])) ; t184 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[3, 4, 4] (u182 * u183)))) + stranspose @[2, 0, 1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m185 = str (sreplicate @2 (sconcrete (sreplicate [2] 2) * siota (SNat @2))) + sreplicate @2 (siota (SNat @2)) ; t192 = sgather @[2, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i186, i187, i188] -> [let i189 = kfromS (m185 !$ [i186, i188]) in ifH (0.0 <=. kplainPart (negate (kfromS (t184 !$ [0, i187, i189])))) 0 1]) ; t193 = stranspose @[0, 2, 1] (sgather @[2, 2] (str (sslice (SNat @0) (SNat @2) (t184 !$ [0]))) (\\[i190, i191] -> [kfromS (m185 !$ [i190, i191])])) ; m194 = sreshape @[2, 4] (sfromPlain t192 * t193) ; v196 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v197 = sgather1 @2 m194 (\\i195 -> [i195, kargMax (splainPart m194 !$ [i195])]) ; m198 = sreplicate @1 (sreplicate @5 (ssum @2 (v196 * v197))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v200 = sgather1 @5 (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\i199 -> [ifH (0.0 <=. kplainPart (negate (kfromS (m198 !$ [0, i199])))) 0 1]) ; v201 = m198 !$ [0] ; m202 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m203 = sreplicate @10 (sfromPlain v200 * v201) ; m205 = soneHot (sfromPlain v200 * ssum @10 (m202 * sfromR dret)) [0] ; v206 = sreplicate @2 (ssum @5 (ssum @1 m205)) in tpair (let t210 = soneHot (sappend (sconcrete (sfromListLinear [0,4] [])) (sappend (str (sscatter @[2, 2] (stranspose @[0, 2, 1] (sfromPlain t192 * sreshape @[2, 2, 2] (sscatter1 @2 (v196 * v206) (\\i207 -> [i207, kargMax (splainPart m194 !$ [i207])])))) (\\[i208, i209] -> [kfromS (m185 !$ [i208, i209])]))) (sconcrete (sreplicate [1,4] 0.0)))) [0] ; u211 = sreshape @[3, 4, 2, 2] (stranspose @[1, 2, 0] (sreplicate @4 (ssum @1 t210))) in tpair (let t222 = soneHot (sscatter @[3, 4, 2, 2] (sfromPlain u173 * sreshape @[3, 4, 2, 2] (stranspose @[2, 1, 0] (ssum @2 (ssum @2 (ssum @4 (ssum @3 (stranspose @[3, 4, 5, 6, 2, 1, 0] (sscatter @[3, 4] (sscatter @[3, 4, 2, 2] (u183 * u211) (\\[i212, i213, i214, i215] -> [i212 + i214, i213 + i215, i212, i213, i214, i215])) (\\[i216, i217] -> [i216, i217, kargMax (splainPart t175 !$ [i216, i217])]))))))))) (\\[i218, i219, i220, i221] -> [kfromS (m162 !$ [i218, i220]), kfromS (m161 !$ [i219, i221])])) [0] in tpair (rfromS (soneHot (ssum @1 (ssum @1 (ssum @9 (ssum @7 (sfromPlain w158 * sreshape @[7, 9, 1, 1, 2, 2] (stranspose @[1, 2, 0] (sreplicate @4 (ssum @1 t222)))))))) [0, 0])) (rfromS (ssum @9 (ssum @7 (stranspose @[1, 2, 0] t222))))) (tpair (rfromS (soneHot (ssum @4 (ssum @3 (u182 * u211))) [0, 0])) (rfromS (ssum @4 (ssum @3 (stranspose @[1, 2, 0] t210)))))) (tpair (tpair (rfromS (soneHot (v197 * v206) [0])) (rfromS (ssum @5 (str m205)))) (tpair (rfromS (str (soneHot (ssum @5 (str (m203 * sfromR dret))) [0]))) (rfromS (ssum @5 (str (sfromR dret))))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [1,1,2,2] STKScalar) (STKS [1] STKScalar)) (STKProduct (STKS [1,1,2,2] STKScalar) (STKS [1] STKScalar))) (STKProduct (STKProduct (STKS [1,2] STKScalar) (STKS [1] STKScalar)) (STKProduct (STKS [10,1] STKScalar) (STKS [10] STKScalar)))) (let u158 = sgather @[9, 2] (stranspose @[2, 0, 1] (sgather @[7, 2] (sconcrete (sreplicate [7,9] 7.0)) (\\[i321, i322] -> [i321 + i322]))) (\\[i154, i155] -> [i154 + i155]) ; t160 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[7, 9, 4] (sfromPlain (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] u158))))) * sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; u173 = sgather @[3, 4, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i163, i164, i165, i166] -> [ifH (0.0 <=. kplainPart (negate (t160 `sindex0` [0, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i163, i165], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i164, i166]]))) 0 1]) ; t175 = sreshape @[3, 4, 4] (sfromPlain u173 * sgather @[3, 4, 2, 2] (t160 !$ [0]) (\\[i169, i170, i171, i172] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i169, i171], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i170, i172]])) ; u182 = sgather @[3, 4, 2, 2] (sgather @[3, 4] (stranspose @[6, 5, 4, 0, 1, 2, 3] (sreplicate @3 (sreplicate @4 (sreplicate @2 (sreplicate @2 (stranspose @[2, 1, 0] t175)))))) (\\[i176, i177] -> [i176, i177, kargMax (splainPart t175 !$ [i176, i177])])) (\\[i178, i179, i180, i181] -> [i178 + i180, i179 + i181, i178, i179, i180, i181]) ; m183 = sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0] ; t184 = sreplicate @1 (ssum @4 (stranspose @[2, 0, 1] (sreshape @[3, 4, 4] (u182 * sreplicate @3 (sreplicate @4 m183))))) + stranspose @[2, 0, 1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; t192 = sgather @[2, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i186, i187, i188] -> [ifH (0.0 <=. kplainPart (negate (t184 `sindex0` [0, i187, sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i186, i188]]))) 0 1]) ; m194 = sreshape @[2, 4] (sfromPlain t192 * stranspose @[0, 2, 1] (sgather @[2, 2] (str (sslice (SNat @0) (SNat @2) (t184 !$ [0]))) (\\[i190, i191] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i190, i191]]))) ; v196 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; v197 = sgather1 @2 m194 (\\i195 -> [i195, kargMax (splainPart m194 !$ [i195])]) ; m198 = sreplicate @1 (sreplicate @5 (sdot0 v196 v197)) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v200 = sgather1 @5 (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\i199 -> [ifH (0.0 <=. kplainPart (negate (m198 `sindex0` [0, i199]))) 0 1]) ; v205 = sfromPlain v200 * sdot1In (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) (str (sfromR dret)) ; x206 = sfromK (ssum0 v205) in tpair (let m210 = sappend (str (sscatter @[2, 2] (sfromPlain (stranspose @[0, 2, 1] t192) * stranspose @[0, 2, 1] (sreshape @[2, 2, 2] (sscatter1 @2 (v196 * sreplicate @2 x206) (\\i207 -> [i207, kargMax (splainPart m194 !$ [i207])])))) (\\[i208, i209] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i208, i209]]))) (sconcrete (sreplicate [1,4] 0.0)) ; u211 = sreshape @[3, 4, 2, 2] (stranspose @[1, 2, 0] (sreplicate @4 m210)) in tpair (let m222 = sscatter @[3, 4, 2, 2] (sfromPlain u173 * sreshape @[3, 4, 2, 2] (ssum @2 (ssum @2 (ssum @4 (ssum @3 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sscatter @[3, 4] (sscatter @[3, 4, 2, 2] (sreplicate @3 (sreplicate @4 m183) * u211) (\\[i212, i213, i214, i215] -> [i212 + i214, i213 + i215, i212, i213, i214, i215])) (\\[i216, i217] -> [i216, i217, kargMax (splainPart t175 !$ [i216, i217])])))))))) (\\[i218, i219, i220, i221] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i218, i220], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i219, i221]]) in tpair (sreplicate @1 (sreplicate @1 (ssum @9 (sdot1In (sfromPlain (stranspose @[0, 3, 1, 2] u158)) (stranspose @[2, 3, 1, 4, 5, 0] (sreshape @[7, 9, 1, 1, 2, 2] (stranspose @[1, 2, 0] (sreplicate @4 m222))) !$ [0, 0]))))) (ssum @9 (ssum @7 (stranspose @[1, 2, 0] (sreplicate @1 m222))))) (tpair (sreplicate @1 (sreplicate @1 (ssum @4 (sdot1In (stranspose @[1, 2, 3, 0] u182) (stranspose @[1, 2, 3, 0] u211))))) (ssum @4 (ssum @3 (stranspose @[1, 2, 0] (sreplicate @1 m210)))))) (tpair (tpair (sreplicate @1 (v197 * sreplicate @2 x206)) (sreplicate @1 (ssum0 v205))) (tpair (str (sreplicate @1 (sdot1In (sreplicate @10 (sfromPlain v200 * m198 !$ [0])) (sfromR dret)))) (ssum @5 (str (sfromR dret))))))"

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
    @?= "\\u1 -> rfromS (let t230 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain (sreplicate @4 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i424, i425] -> [i424 + i425]))) (\\[i224, i225] -> [i224 + i225])))))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; u246 = sreshape @[4, 7, 11, 4] (sfromPlain (sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i233, i234, i235, i236, i237] -> [ifH (0.0 <=. kplainPart (negate (t230 `sindex0` [i233, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i234, i236], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i235, i237]]))) 0 1])) * stranspose @[4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[1, 2, 0] t230) (\\[i240, i241, i242, i243] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i240, i242], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i241, i243]]))) ; t255 = ssum @48 (stranspose @[3, 0, 1, 2] (sreshape @[4, 7, 11, 48] (sreplicate @4 (stranspose @[0, 1, 4, 2, 3] (sgather @[7, 11, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[7, 11, 4] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[3, 2, 1, 0] u246))))))) (\\[i417, i418, i419] -> [i419, i417, i418, kargMax (splainPart u246 !$ [i419, i417, i418])]))) (\\[i250, i251, i252, i253] -> [i250, i251, i252, i253, i250 + i252, i251 + i253]))) * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; u271 = sreshape @[4, 3, 5, 4] (sfromPlain (sgather @[4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [ifH (0.0 <=. kplainPart (negate (t255 `sindex0` [i258, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i259, i261], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i260, i262]]))) 0 1])) * stranspose @[4, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[1, 2, 0] t255) (\\[i265, i266, i267, i268] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i265, i267], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i266, i268]]))) ; m276 = str (sreplicate @7 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @5 (sreshape @[60] (sgather @[4, 3, 5] u271 (\\[i272, i273, i274] -> [i272, i273, i274, kargMax (splainPart u271 !$ [i272, i273, i274])])))))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in smatmul2 (sfromR (tproject1 (tproject2 (tproject2 u1)))) (sfromPlain (sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278] -> [ifH (0.0 <=. kplainPart (negate (m276 `sindex0` [i277, i278]))) 0 1])) * m276) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> rfromS (let w228 = sreplicate @4 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i226, i227] -> [i226 + i227]))) (\\[i224, i225] -> [i224 + i225]))))))) ; w229 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))) ; t230 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain w228 * w229))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m231 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; m232 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; w244 = sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i233, i234, i235, i236, i237] -> [let i238 = kfromS (m231 !$ [i235, i237]) ; i239 = kfromS (m232 !$ [i234, i236]) in ifH (0.0 <=. kplainPart (negate (kfromS (t230 !$ [i233, i239, i238])))) 0 1]) ; w245 = stranspose @[4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[1, 2, 0] t230) (\\[i240, i241, i242, i243] -> [kfromS (m232 !$ [i240, i242]), kfromS (m231 !$ [i241, i243])])) ; u246 = sreshape @[4, 7, 11, 4] (sfromPlain w244 * w245) ; w254 = sreplicate @4 (stranspose @[0, 1, 4, 2, 3] (sgather @[7, 11, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[7, 11, 4] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[3, 2, 1, 0] u246))))))) (\\[i247, i248, i249] -> [i249, i247, i248, kargMax (splainPart u246 !$ [i249, i247, i248])]))) (\\[i250, i251, i252, i253] -> [i250, i251, i252, i253, i250 + i252, i251 + i253]))) ; t255 = ssum @48 (stranspose @[3, 0, 1, 2] (sreshape @[4, 7, 11, 48] (w254 * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; w269 = sgather @[4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let i263 = kfromS (m256 !$ [i260, i262]) ; i264 = kfromS (m257 !$ [i259, i261]) in ifH (0.0 <=. kplainPart (negate (kfromS (t255 !$ [i258, i264, i263])))) 0 1]) ; w270 = stranspose @[4, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[1, 2, 0] t255) (\\[i265, i266, i267, i268] -> [kfromS (m257 !$ [i265, i267]), kfromS (m256 !$ [i266, i268])])) ; u271 = sreshape @[4, 3, 5, 4] (sfromPlain w269 * w270) ; m275 = str (sreplicate @5 (sreshape @[60] (sgather @[4, 3, 5] u271 (\\[i272, i273, i274] -> [i272, i273, i274, kargMax (splainPart u271 !$ [i272, i273, i274])])))) ; m276 = str (sreplicate @7 (ssum @60 (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m275))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m279 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278] -> [ifH (0.0 <=. kplainPart (negate (kfromS (m276 !$ [i277, i278])))) 0 1]) ; t280 = str (sreplicate @10 (sfromPlain m279 * m276)) in ssum @5 (stranspose @[2, 1, 0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * t280) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w228 = sreplicate @4 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i226, i227] -> [i226 + i227]))) (\\[i224, i225] -> [i224 + i225]))))))) ; w229 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))) ; t230 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain w228 * w229))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; m231 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; m232 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; w244 = sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i233, i234, i235, i236, i237] -> [let i238 = kfromS (m231 !$ [i235, i237]) ; i239 = kfromS (m232 !$ [i234, i236]) in ifH (0.0 <=. kplainPart (negate (kfromS (t230 !$ [i233, i239, i238])))) 0 1]) ; w245 = stranspose @[4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[1, 2, 0] t230) (\\[i240, i241, i242, i243] -> [kfromS (m232 !$ [i240, i242]), kfromS (m231 !$ [i241, i243])])) ; u246 = sreshape @[4, 7, 11, 4] (sfromPlain w244 * w245) ; w254 = sreplicate @4 (stranspose @[0, 1, 4, 2, 3] (sgather @[7, 11, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[7, 11, 4] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[3, 2, 1, 0] u246))))))) (\\[i247, i248, i249] -> [i249, i247, i248, kargMax (splainPart u246 !$ [i249, i247, i248])]))) (\\[i250, i251, i252, i253] -> [i250, i251, i252, i253, i250 + i252, i251 + i253]))) ; t255 = ssum @48 (stranspose @[3, 0, 1, 2] (sreshape @[4, 7, 11, 48] (w254 * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; w269 = sgather @[4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let i263 = kfromS (m256 !$ [i260, i262]) ; i264 = kfromS (m257 !$ [i259, i261]) in ifH (0.0 <=. kplainPart (negate (kfromS (t255 !$ [i258, i264, i263])))) 0 1]) ; w270 = stranspose @[4, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[1, 2, 0] t255) (\\[i265, i266, i267, i268] -> [kfromS (m257 !$ [i265, i267]), kfromS (m256 !$ [i266, i268])])) ; u271 = sreshape @[4, 3, 5, 4] (sfromPlain w269 * w270) ; m275 = str (sreplicate @5 (sreshape @[60] (sgather @[4, 3, 5] u271 (\\[i272, i273, i274] -> [i272, i273, i274, kargMax (splainPart u271 !$ [i272, i273, i274])])))) ; m276 = str (sreplicate @7 (ssum @60 (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m275))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m279 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278] -> [ifH (0.0 <=. kplainPart (negate (kfromS (m276 !$ [i277, i278])))) 0 1]) ; t280 = str (sreplicate @10 (sfromPlain m279 * m276)) ; m282 = sfromPlain m279 * ssum @10 (str (stranspose @[2, 1, 0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * sreplicate @5 (sfromR dret))) ; m283 = sreplicate @60 (ssum @7 (str m282)) in tpair (let t291 = stranspose @[2, 0, 1] (sscatter @[3, 5, 2, 2] (stranspose @[1, 2, 3, 4, 0] (sfromPlain w269 * sreshape @[4, 3, 5, 2, 2] (sscatter @[4, 3, 5] (sreshape @[4, 3, 5] (ssum @5 (str (str (sfromR (tproject1 (tproject1 (tproject2 u1)))) * m283)))) (\\[i284, i285, i286] -> [i284, i285, i286, kargMax (splainPart u271 !$ [i284, i285, i286])])))) (\\[i287, i288, i289, i290] -> [kfromS (m257 !$ [i287, i289]), kfromS (m256 !$ [i288, i290])])) ; w292 = sreshape @[4, 7, 11, 4, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @48 t291)) in tpair (let t304 = stranspose @[2, 0, 1] (sscatter @[7, 11, 2, 2] (stranspose @[1, 2, 3, 4, 0] (sfromPlain w244 * sreshape @[4, 7, 11, 2, 2] (stranspose @[3, 2, 1, 0] (ssum @7 (ssum @11 (ssum @3 (stranspose @[4, 5, 6, 0, 1, 2, 3] (ssum @4 (stranspose @[7, 3, 2, 1, 0, 6, 5, 4] (sscatter @[7, 11, 4] (stranspose @[4, 5, 6, 0, 1, 2, 3] (sscatter @[7, 11, 3, 4] (stranspose @[0, 1, 3, 4, 2] (ssum @4 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))) * w292))) (\\[i293, i294, i295, i296] -> [i293, i294, i295, i296, i293 + i295, i294 + i296]))) (\\[i297, i298, i299] -> [i299, i297, i298, kargMax (splainPart u246 !$ [i299, i297, i298])]))))))))))) (\\[i300, i301, i302, i303] -> [kfromS (m232 !$ [i300, i302]), kfromS (m231 !$ [i301, i303])])) in tpair (rfromS (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (sfromPlain w228 * sreshape @[4, 14, 23, 1, 1, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @12 t304))))))))))) [0]))) (rfromS (ssum @23 (ssum @14 (stranspose @[1, 2, 0] t304))))) (tpair (rfromS (ssum @11 (str (ssum @7 (str (w254 * w292)))))) (rfromS (ssum @11 (ssum @7 (stranspose @[1, 2, 0] t291)))))) (tpair (tpair (rfromS (str (m275 * m283))) (rfromS (ssum @7 (str m282)))) (tpair (rfromS (ssum @7 (stranspose @[2, 1, 0] (t280 * sreplicate @5 (sfromR dret))))) (rfromS (ssum @7 (str (sfromR dret))))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [4,1,3,4] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [4,4,3,4] STKScalar) (STKS [4] STKScalar))) (STKProduct (STKProduct (STKS [5,60] STKScalar) (STKS [5] STKScalar)) (STKProduct (STKS [10,5] STKScalar) (STKS [10] STKScalar)))) (let u228 = sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i497, i498] -> [i497 + i498]))) (\\[i224, i225] -> [i224 + i225]) ; t230 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain (sreplicate @4 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] u228)))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1)))))) ; w244 = sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i233, i234, i235, i236, i237] -> [ifH (0.0 <=. kplainPart (negate (t230 `sindex0` [i233, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i234, i236], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i235, i237]]))) 0 1]) ; u246 = sreshape @[4, 7, 11, 4] (sfromPlain w244 * stranspose @[4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[1, 2, 0] t230) (\\[i240, i241, i242, i243] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i240, i242], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i241, i243]]))) ; w254 = sgather @[7, 11, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[7, 11, 4] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[3, 2, 1, 0] u246))))))) (\\[i488, i489, i490] -> [i490, i488, i489, kargMax (splainPart u246 !$ [i490, i488, i489])]))) (\\[i250, i251, i252, i253] -> [i250, i251, i252, i253, i250 + i252, i251 + i253]) ; t255 = ssum @48 (stranspose @[3, 0, 1, 2] (sreshape @[4, 7, 11, 48] (sreplicate @4 (stranspose @[0, 1, 4, 2, 3] w254) * str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; w269 = sgather @[4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [ifH (0.0 <=. kplainPart (negate (t255 `sindex0` [i258, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i259, i261], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i260, i262]]))) 0 1]) ; u271 = sreshape @[4, 3, 5, 4] (sfromPlain w269 * stranspose @[4, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[1, 2, 0] t255) (\\[i265, i266, i267, i268] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i265, i267], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i266, i268]]))) ; v275 = sreshape @[60] (sgather @[4, 3, 5] u271 (\\[i272, i273, i274] -> [i272, i273, i274, kargMax (splainPart u271 !$ [i272, i273, i274])])) ; m276 = str (sreplicate @7 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @5 v275))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m279 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278] -> [ifH (0.0 <=. kplainPart (negate (m276 `sindex0` [i277, i278]))) 0 1]) ; m282 = sfromPlain m279 * smatmul2 (str (sfromR (tproject1 (tproject2 (tproject2 u1))))) (sfromR dret) ; v283 = ssum @7 (str m282) in tpair (let t291 = sscatter @[3, 5, 2, 2] (sfromPlain (stranspose @[1, 2, 3, 4, 0] w269) * stranspose @[1, 2, 3, 4, 0] (sreshape @[4, 3, 5, 2, 2] (sscatter @[4, 3, 5] (sreshape @[4, 3, 5] (sdot1In (str (sfromR (tproject1 (tproject1 (tproject2 u1))))) (sreplicate @60 v283))) (\\[i284, i285, i286] -> [i284, i285, i286, kargMax (splainPart u271 !$ [i284, i285, i286])])))) (\\[i287, i288, i289, i290] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i287, i289], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i288, i290]]) ; w292 = sreshape @[4, 7, 11, 4, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @48 (stranspose @[2, 0, 1] t291))) in tpair (let t304 = sscatter @[7, 11, 2, 2] (sfromPlain (stranspose @[1, 2, 3, 4, 0] w244) * stranspose @[1, 2, 3, 4, 0] (sreshape @[4, 7, 11, 2, 2] (ssum @7 (ssum @11 (ssum @3 (ssum @4 (stranspose @[7, 6, 5, 4, 0, 1, 2, 3] (sscatter @[7, 11, 4] (stranspose @[4, 5, 6, 0, 1, 2, 3] (sscatter @[7, 11, 3, 4] (sdot1In (sreplicate @7 (sreplicate @11 (stranspose @[2, 3, 1, 0] (sfromR (tproject1 (tproject2 (tproject1 u1))))))) (stranspose @[1, 2, 4, 5, 3, 0] w292)) (\\[i293, i294, i295, i296] -> [i293, i294, i295, i296, i293 + i295, i294 + i296]))) (\\[i297, i298, i299] -> [i299, i297, i298, kargMax (splainPart u246 !$ [i299, i297, i298])]))))))))) (\\[i300, i301, i302, i303] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i300, i302], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i301, i303]]) in tpair (str (sreplicate @1 (ssum @23 (sdot1In (sfromPlain (stranspose @[4, 0, 3, 2, 1] (sreplicate @4 (stranspose @[2, 1, 3, 0] u228)))) (stranspose @[3, 4, 2, 0, 5, 6, 1] (sreshape @[4, 14, 23, 1, 1, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @12 (stranspose @[2, 0, 1] t304)))) !$ [0, 0]))))) (ssum @23 (ssum @14 t304))) (tpair (ssum @11 (sdot1In (stranspose @[2, 0, 3, 4, 5, 1] (sreplicate @4 (stranspose @[0, 1, 4, 2, 3] w254))) (stranspose @[2, 0, 3, 4, 5, 1] w292))) (ssum @11 (ssum @7 t291)))) (tpair (tpair (sreplicate @5 v275 * str (sreplicate @60 v283)) (ssum @7 (str m282))) (tpair (smatmul2 (sfromR dret) (sfromPlain (str m279) * str m276)) (ssum @7 (str (sfromR dret))))))"

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
    @?= "\\u1 -> let t230 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain (sreplicate @4 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i424, i425] -> [i424 + i425]))) (\\[i224, i225] -> [i224 + i225])))))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; u246 = sreshape @[4, 7, 11, 4] (sfromPlain (sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i233, i234, i235, i236, i237] -> [ifH (0.0 <=. kplainPart (negate (t230 `sindex0` [i233, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i234, i236], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i235, i237]]))) 0 1])) * stranspose @[4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[1, 2, 0] t230) (\\[i240, i241, i242, i243] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i240, i242], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i241, i243]]))) ; t255 = ssum @48 (stranspose @[3, 0, 1, 2] (sreshape @[4, 7, 11, 48] (sreplicate @4 (stranspose @[0, 1, 4, 2, 3] (sgather @[7, 11, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[7, 11, 4] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[3, 2, 1, 0] u246))))))) (\\[i417, i418, i419] -> [i419, i417, i418, kargMax (splainPart u246 !$ [i419, i417, i418])]))) (\\[i250, i251, i252, i253] -> [i250, i251, i252, i253, i250 + i252, i251 + i253]))) * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; u271 = sreshape @[4, 3, 5, 4] (sfromPlain (sgather @[4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [ifH (0.0 <=. kplainPart (negate (t255 `sindex0` [i258, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i259, i261], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i260, i262]]))) 0 1])) * stranspose @[4, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[1, 2, 0] t255) (\\[i265, i266, i267, i268] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i265, i267], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i266, i268]]))) ; m276 = str (sreplicate @7 (sdot1In (tproject1 (tproject1 (tproject2 u1))) (sreplicate @5 (sreshape @[60] (sgather @[4, 3, 5] u271 (\\[i272, i273, i274] -> [i272, i273, i274, kargMax (splainPart u271 !$ [i272, i273, i274])])))))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) in smatmul2 (tproject1 (tproject2 (tproject2 u1))) (sfromPlain (sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278] -> [ifH (0.0 <=. kplainPart (negate (m276 `sindex0` [i277, i278]))) 0 1])) * m276) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w228 = sreplicate @4 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i226, i227] -> [i226 + i227]))) (\\[i224, i225] -> [i224 + i225]))))))) ; w229 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))) ; t230 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain w228 * w229))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; m231 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; m232 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; w244 = sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i233, i234, i235, i236, i237] -> [let i238 = kfromS (m231 !$ [i235, i237]) ; i239 = kfromS (m232 !$ [i234, i236]) in ifH (0.0 <=. kplainPart (negate (kfromS (t230 !$ [i233, i239, i238])))) 0 1]) ; w245 = stranspose @[4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[1, 2, 0] t230) (\\[i240, i241, i242, i243] -> [kfromS (m232 !$ [i240, i242]), kfromS (m231 !$ [i241, i243])])) ; u246 = sreshape @[4, 7, 11, 4] (sfromPlain w244 * w245) ; w254 = sreplicate @4 (stranspose @[0, 1, 4, 2, 3] (sgather @[7, 11, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[7, 11, 4] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[3, 2, 1, 0] u246))))))) (\\[i247, i248, i249] -> [i249, i247, i248, kargMax (splainPart u246 !$ [i249, i247, i248])]))) (\\[i250, i251, i252, i253] -> [i250, i251, i252, i253, i250 + i252, i251 + i253]))) ; t255 = ssum @48 (stranspose @[3, 0, 1, 2] (sreshape @[4, 7, 11, 48] (w254 * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; w269 = sgather @[4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let i263 = kfromS (m256 !$ [i260, i262]) ; i264 = kfromS (m257 !$ [i259, i261]) in ifH (0.0 <=. kplainPart (negate (kfromS (t255 !$ [i258, i264, i263])))) 0 1]) ; w270 = stranspose @[4, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[1, 2, 0] t255) (\\[i265, i266, i267, i268] -> [kfromS (m257 !$ [i265, i267]), kfromS (m256 !$ [i266, i268])])) ; u271 = sreshape @[4, 3, 5, 4] (sfromPlain w269 * w270) ; m275 = str (sreplicate @5 (sreshape @[60] (sgather @[4, 3, 5] u271 (\\[i272, i273, i274] -> [i272, i273, i274, kargMax (splainPart u271 !$ [i272, i273, i274])])))) ; m276 = str (sreplicate @7 (ssum @60 (str (tproject1 (tproject1 (tproject2 u1))) * m275))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m279 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278] -> [ifH (0.0 <=. kplainPart (negate (kfromS (m276 !$ [i277, i278])))) 0 1]) ; t280 = str (sreplicate @10 (sfromPlain m279 * m276)) in ssum @5 (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * t280) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w228 = sreplicate @4 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i226, i227] -> [i226 + i227]))) (\\[i224, i225] -> [i224 + i225]))))))) ; w229 = str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))) ; t230 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain w228 * w229))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; m231 = str (sreplicate @2 (sconcrete (sreplicate [11] 2) * siota (SNat @11))) + sreplicate @11 (siota (SNat @2)) ; m232 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; w244 = sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i233, i234, i235, i236, i237] -> [let i238 = kfromS (m231 !$ [i235, i237]) ; i239 = kfromS (m232 !$ [i234, i236]) in ifH (0.0 <=. kplainPart (negate (kfromS (t230 !$ [i233, i239, i238])))) 0 1]) ; w245 = stranspose @[4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[1, 2, 0] t230) (\\[i240, i241, i242, i243] -> [kfromS (m232 !$ [i240, i242]), kfromS (m231 !$ [i241, i243])])) ; u246 = sreshape @[4, 7, 11, 4] (sfromPlain w244 * w245) ; w254 = sreplicate @4 (stranspose @[0, 1, 4, 2, 3] (sgather @[7, 11, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[7, 11, 4] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[3, 2, 1, 0] u246))))))) (\\[i247, i248, i249] -> [i249, i247, i248, kargMax (splainPart u246 !$ [i249, i247, i248])]))) (\\[i250, i251, i252, i253] -> [i250, i251, i252, i253, i250 + i252, i251 + i253]))) ; t255 = ssum @48 (stranspose @[3, 0, 1, 2] (sreshape @[4, 7, 11, 48] (w254 * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; m256 = str (sreplicate @2 (sconcrete (sreplicate [5] 2) * siota (SNat @5))) + sreplicate @5 (siota (SNat @2)) ; m257 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; w269 = sgather @[4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [let i263 = kfromS (m256 !$ [i260, i262]) ; i264 = kfromS (m257 !$ [i259, i261]) in ifH (0.0 <=. kplainPart (negate (kfromS (t255 !$ [i258, i264, i263])))) 0 1]) ; w270 = stranspose @[4, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[1, 2, 0] t255) (\\[i265, i266, i267, i268] -> [kfromS (m257 !$ [i265, i267]), kfromS (m256 !$ [i266, i268])])) ; u271 = sreshape @[4, 3, 5, 4] (sfromPlain w269 * w270) ; m275 = str (sreplicate @5 (sreshape @[60] (sgather @[4, 3, 5] u271 (\\[i272, i273, i274] -> [i272, i273, i274, kargMax (splainPart u271 !$ [i272, i273, i274])])))) ; m276 = str (sreplicate @7 (ssum @60 (str (tproject1 (tproject1 (tproject2 u1))) * m275))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m279 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278] -> [ifH (0.0 <=. kplainPart (negate (kfromS (m276 !$ [i277, i278])))) 0 1]) ; t280 = str (sreplicate @10 (sfromPlain m279 * m276)) ; m282 = sfromPlain m279 * ssum @10 (str (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * sreplicate @5 dret)) ; m283 = sreplicate @60 (ssum @7 (str m282)) in tpair (let t291 = stranspose @[2, 0, 1] (sscatter @[3, 5, 2, 2] (stranspose @[1, 2, 3, 4, 0] (sfromPlain w269 * sreshape @[4, 3, 5, 2, 2] (sscatter @[4, 3, 5] (sreshape @[4, 3, 5] (ssum @5 (str (str (tproject1 (tproject1 (tproject2 u1))) * m283)))) (\\[i284, i285, i286] -> [i284, i285, i286, kargMax (splainPart u271 !$ [i284, i285, i286])])))) (\\[i287, i288, i289, i290] -> [kfromS (m257 !$ [i287, i289]), kfromS (m256 !$ [i288, i290])])) ; w292 = sreshape @[4, 7, 11, 4, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @48 t291)) in tpair (let t304 = stranspose @[2, 0, 1] (sscatter @[7, 11, 2, 2] (stranspose @[1, 2, 3, 4, 0] (sfromPlain w244 * sreshape @[4, 7, 11, 2, 2] (stranspose @[3, 2, 1, 0] (ssum @7 (ssum @11 (ssum @3 (stranspose @[4, 5, 6, 0, 1, 2, 3] (ssum @4 (stranspose @[7, 3, 2, 1, 0, 6, 5, 4] (sscatter @[7, 11, 4] (stranspose @[4, 5, 6, 0, 1, 2, 3] (sscatter @[7, 11, 3, 4] (stranspose @[0, 1, 3, 4, 2] (ssum @4 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))) * w292))) (\\[i293, i294, i295, i296] -> [i293, i294, i295, i296, i293 + i295, i294 + i296]))) (\\[i297, i298, i299] -> [i299, i297, i298, kargMax (splainPart u246 !$ [i299, i297, i298])]))))))))))) (\\[i300, i301, i302, i303] -> [kfromS (m232 !$ [i300, i302]), kfromS (m231 !$ [i301, i303])])) in tpair (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (sfromPlain w228 * sreshape @[4, 14, 23, 1, 1, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @12 t304))))))))))) [0])) (ssum @23 (ssum @14 (stranspose @[1, 2, 0] t304)))) (tpair (ssum @11 (str (ssum @7 (str (w254 * w292))))) (ssum @11 (ssum @7 (stranspose @[1, 2, 0] t291))))) (tpair (tpair (str (m275 * m283)) (ssum @7 (str m282))) (tpair (ssum @7 (stranspose @[2, 1, 0] (t280 * sreplicate @5 dret))) (ssum @7 (str dret))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> let u228 = sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sconcrete (sreplicate [14,23] 7.0)) (\\[i497, i498] -> [i497 + i498]))) (\\[i224, i225] -> [i224 + i225]) ; t230 = ssum @12 (stranspose @[3, 0, 1, 2] (sreshape @[4, 14, 23, 12] (sfromPlain (sreplicate @4 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[1, 2, 0] (sreplicate @1 (stranspose @[2, 0, 3, 1] u228)))))) * str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))))) + stranspose @[2, 0, 1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1))))) ; w244 = sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i233, i234, i235, i236, i237] -> [ifH (0.0 <=. kplainPart (negate (t230 `sindex0` [i233, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i234, i236], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i235, i237]]))) 0 1]) ; u246 = sreshape @[4, 7, 11, 4] (sfromPlain w244 * stranspose @[4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[1, 2, 0] t230) (\\[i240, i241, i242, i243] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i240, i242], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i241, i243]]))) ; w254 = sgather @[7, 11, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[7, 11, 4] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicate @3 (sreplicate @11 (sreplicate @7 (stranspose @[3, 2, 1, 0] u246))))))) (\\[i488, i489, i490] -> [i490, i488, i489, kargMax (splainPart u246 !$ [i490, i488, i489])]))) (\\[i250, i251, i252, i253] -> [i250, i251, i252, i253, i250 + i252, i251 + i253]) ; t255 = ssum @48 (stranspose @[3, 0, 1, 2] (sreshape @[4, 7, 11, 48] (sreplicate @4 (stranspose @[0, 1, 4, 2, 3] w254) * str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + stranspose @[2, 0, 1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1))))) ; w269 = sgather @[4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i258, i259, i260, i261, i262] -> [ifH (0.0 <=. kplainPart (negate (t255 `sindex0` [i258, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i259, i261], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i260, i262]]))) 0 1]) ; u271 = sreshape @[4, 3, 5, 4] (sfromPlain w269 * stranspose @[4, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[1, 2, 0] t255) (\\[i265, i266, i267, i268] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i265, i267], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i266, i268]]))) ; v275 = sreshape @[60] (sgather @[4, 3, 5] u271 (\\[i272, i273, i274] -> [i272, i273, i274, kargMax (splainPart u271 !$ [i272, i273, i274])])) ; m276 = str (sreplicate @7 (sdot1In (tproject1 (tproject1 (tproject2 u1))) (sreplicate @5 v275))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m279 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i277, i278] -> [ifH (0.0 <=. kplainPart (negate (m276 `sindex0` [i277, i278]))) 0 1]) ; m282 = sfromPlain m279 * smatmul2 (str (tproject1 (tproject2 (tproject2 u1)))) dret ; v283 = ssum @7 (str m282) in tpair (let t291 = sscatter @[3, 5, 2, 2] (sfromPlain (stranspose @[1, 2, 3, 4, 0] w269) * stranspose @[1, 2, 3, 4, 0] (sreshape @[4, 3, 5, 2, 2] (sscatter @[4, 3, 5] (sreshape @[4, 3, 5] (sdot1In (str (tproject1 (tproject1 (tproject2 u1)))) (sreplicate @60 v283))) (\\[i284, i285, i286] -> [i284, i285, i286, kargMax (splainPart u271 !$ [i284, i285, i286])])))) (\\[i287, i288, i289, i290] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i287, i289], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i288, i290]]) ; w292 = sreshape @[4, 7, 11, 4, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @48 (stranspose @[2, 0, 1] t291))) in tpair (let t304 = sscatter @[7, 11, 2, 2] (sfromPlain (stranspose @[1, 2, 3, 4, 0] w244) * stranspose @[1, 2, 3, 4, 0] (sreshape @[4, 7, 11, 2, 2] (ssum @7 (ssum @11 (ssum @3 (ssum @4 (stranspose @[7, 6, 5, 4, 0, 1, 2, 3] (sscatter @[7, 11, 4] (stranspose @[4, 5, 6, 0, 1, 2, 3] (sscatter @[7, 11, 3, 4] (sdot1In (sreplicate @7 (sreplicate @11 (stranspose @[2, 3, 1, 0] (tproject1 (tproject2 (tproject1 u1)))))) (stranspose @[1, 2, 4, 5, 3, 0] w292)) (\\[i293, i294, i295, i296] -> [i293, i294, i295, i296, i293 + i295, i294 + i296]))) (\\[i297, i298, i299] -> [i299, i297, i298, kargMax (splainPart u246 !$ [i299, i297, i298])]))))))))) (\\[i300, i301, i302, i303] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i300, i302], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i301, i303]]) in tpair (str (sreplicate @1 (ssum @23 (sdot1In (sfromPlain (stranspose @[4, 0, 3, 2, 1] (sreplicate @4 (stranspose @[2, 1, 3, 0] u228)))) (stranspose @[3, 4, 2, 0, 5, 6, 1] (sreshape @[4, 14, 23, 1, 1, 3, 4] (stranspose @[1, 2, 3, 0] (sreplicate @12 (stranspose @[2, 0, 1] t304)))) !$ [0, 0]))))) (ssum @23 (ssum @14 t304))) (tpair (ssum @11 (sdot1In (stranspose @[2, 0, 3, 4, 5, 1] (sreplicate @4 (stranspose @[0, 1, 4, 2, 3] w254))) (stranspose @[2, 0, 3, 4, 5, 1] w292))) (ssum @11 (ssum @7 t291)))) (tpair (tpair (sreplicate @5 v275 * str (sreplicate @60 v283)) (ssum @7 (str m282))) (tpair (smatmul2 dret (sfromPlain (str m279) * str m276)) (ssum @7 (str dret))))"
