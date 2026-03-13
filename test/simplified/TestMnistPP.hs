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

import EqEpsilon

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
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [7.0 * ssum0 @[784] (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 @[784] (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 @[784] (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v5, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v5]) + tproject2 (tproject2 v1))"
  printArtifactPrimalPretty artifactRev
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [ssum0 @[784] (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate0N @[784] 7.0)), ssum0 @[784] (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate0N @[784] 7.0)), ssum0 @[784] (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate0N @[784] 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum0 @[3] (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum0 @[3] (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum0 @[3] (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum0 @[3] (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [ssum0 @[4] (tproject1 (tproject1 (tproject2 v1)) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v5), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v5)]) + tproject2 (tproject2 v1))"
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [ssum0 @[784] (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate0N @[784] 7.0)), ssum0 @[784] (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate0N @[784] 7.0)), ssum0 @[784] (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate0N @[784] 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum0 @[3] (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum0 @[3] (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum0 @[3] (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum0 @[3] (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate0N @[4] (sfromR dret `sindex0` [9]) ; v8 = sreplicate0N @[4] (sfromR dret `sindex0` [8]) ; v9 = sreplicate0N @[4] (sfromR dret `sindex0` [7]) ; v10 = sreplicate0N @[4] (sfromR dret `sindex0` [6]) ; v11 = sreplicate0N @[4] (sfromR dret `sindex0` [5]) ; v12 = sreplicate0N @[4] (sfromR dret `sindex0` [4]) ; v13 = sreplicate0N @[4] (sfromR dret `sindex0` [3]) ; v14 = sreplicate0N @[4] (sfromR dret `sindex0` [2]) ; v15 = sreplicate0N @[4] (sfromR dret `sindex0` [1]) ; v16 = sreplicate0N @[4] (sfromR dret `sindex0` [0]) in tpair (let v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7)))))))) ; v18 = sreplicate0N @[3] (v17 `sindex0` [3]) ; v19 = sreplicate0N @[3] (v17 `sindex0` [2]) ; v20 = sreplicate0N @[3] (v17 `sindex0` [1]) ; v21 = sreplicate0N @[3] (v17 `sindex0` [0]) in tpair (let v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)) in tpair (tpair (sfromPlain (sreplicate0N @[784] 7.0) * sreplicate0N @[784] (v22 `sindex0` [0])) (tpair (sfromPlain (sreplicate0N @[784] 7.0) * sreplicate0N @[784] (v22 `sindex0` [1])) (tpair (sfromPlain (sreplicate0N @[784] 7.0) * sreplicate0N @[784] (v22 `sindex0` [2])) Z1))) v22) (tpair (tpair (v4 * v21) (tpair (v4 * v20) (tpair (v4 * v19) (tpair (v4 * v18) Z1)))) v17)) (tpair (tpair (v5 * v16) (tpair (v5 * v15) (tpair (v5 * v14) (tpair (v5 * v13) (tpair (v5 * v12) (tpair (v5 * v11) (tpair (v5 * v10) (tpair (v5 * v9) (tpair (v5 * v8) (tpair (v5 * v7) Z1)))))))))) (sfromR dret))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [7.0 * ssum0 @[784] (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 @[784] (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 @[784] (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) ; x7 = sfromR dret `sindex0` [9] ; x8 = sfromR dret `sindex0` [8] ; x9 = sfromR dret `sindex0` [7] ; x10 = sfromR dret `sindex0` [6] ; x11 = sfromR dret `sindex0` [5] ; x12 = sfromR dret `sindex0` [4] ; x13 = sfromR dret `sindex0` [3] ; x14 = sfromR dret `sindex0` [2] ; x15 = sfromR dret `sindex0` [1] ; x16 = sfromR dret `sindex0` [0] in tpair (let v17 = tproject1 (tproject1 (tproject2 v1)) * sreplicate0N @[4] x16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate0N @[4] x15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate0N @[4] x14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate0N @[4] x13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate0N @[4] x12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate0N @[4] x11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate0N @[4] x10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate0N @[4] x9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate0N @[4] x8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate0N @[4] x7)))))))) ; x18 = v17 `sindex0` [3] ; x19 = v17 `sindex0` [2] ; x20 = v17 `sindex0` [1] ; x21 = v17 `sindex0` [0] in tpair (let v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate0N @[3] x21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate0N @[3] x20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate0N @[3] x19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate0N @[3] x18)) in tpair (tpair (sreplicate0N @[784] (7.0 * v22 `sindex0` [0])) (tpair (sreplicate0N @[784] (7.0 * v22 `sindex0` [1])) (tpair (sreplicate0N @[784] (7.0 * v22 `sindex0` [2])) Z1))) v22) (tpair (tpair (v4 * sreplicate0N @[3] x21) (tpair (v4 * sreplicate0N @[3] x20) (tpair (v4 * sreplicate0N @[3] x19) (tpair (v4 * sreplicate0N @[3] x18) Z1)))) v17)) (tpair (tpair (v5 * sreplicate0N @[4] x16) (tpair (v5 * sreplicate0N @[4] x15) (tpair (v5 * sreplicate0N @[4] x14) (tpair (v5 * sreplicate0N @[4] x13) (tpair (v5 * sreplicate0N @[4] x12) (tpair (v5 * sreplicate0N @[4] x11) (tpair (v5 * sreplicate0N @[4] x10) (tpair (v5 * sreplicate0N @[4] x9) (tpair (v5 * sreplicate0N @[4] x8) (tpair (v5 * sreplicate0N @[4] x7) Z1)))))))))) (sfromR dret))"

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
    @?= "\\v1 -> rfromS (let v13 = recip (scast (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [7.0 * ssum0 @[784] (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 @[784] (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 @[784] (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1)))))) ; v16 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v13, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v13, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v13, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v13]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v19 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v16, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v16]) + tproject2 (tproject2 v1)) in sreplicate0N @[10] (recip (ssum0 @[10] v19)) * v19)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\v1 -> rfromS (let v9 = sfromVector (fromList [ssum0 @[784] (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate0N @[784] 7.0)), ssum0 @[784] (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate0N @[784] 7.0)), ssum0 @[784] (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate0N @[784] 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = recip (sconcrete (sreplicate [3] 1.0) + v10) ; v13 = scast (v11 + sconcrete (sreplicate [3] 0.0)) ; v14 = scast (sfromVector (fromList [ssum0 @[3] (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v13), ssum0 @[3] (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v13), ssum0 @[3] (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v13), ssum0 @[3] (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v13)])) + tproject2 (tproject2 (tproject1 v1)) ; v15 = exp (negate v14) ; v16 = recip (sconcrete (sreplicate [4] 1.0) + v15) ; v18 = v16 + sconcrete (sreplicate [4] 0.0) ; v19 = exp (sfromVector (fromList [ssum0 @[4] (tproject1 (tproject1 (tproject2 v1)) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v18)]) + tproject2 (tproject2 v1)) ; x20 = ssum0 @[10] v19 ; v21 = sreplicate0N @[10] (recip x20) in v21 * v19)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret v1 -> let v9 = sfromVector (fromList [ssum0 @[784] (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sfromPlain (sreplicate0N @[784] 7.0)), ssum0 @[784] (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sfromPlain (sreplicate0N @[784] 7.0)), ssum0 @[784] (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sfromPlain (sreplicate0N @[784] 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = recip (sconcrete (sreplicate [3] 1.0) + v10) ; v12 = v11 * (sconcrete (sreplicate [3] 1.0) + negate v11) ; v13 = scast (v11 + sconcrete (sreplicate [3] 0.0)) ; v14 = scast (sfromVector (fromList [ssum0 @[3] (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v13), ssum0 @[3] (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v13), ssum0 @[3] (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v13), ssum0 @[3] (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v13)])) + tproject2 (tproject2 (tproject1 v1)) ; v15 = exp (negate v14) ; v16 = recip (sconcrete (sreplicate [4] 1.0) + v15) ; v17 = v16 * (sconcrete (sreplicate [4] 1.0) + negate v16) ; v18 = v16 + sconcrete (sreplicate [4] 0.0) ; v19 = exp (sfromVector (fromList [ssum0 @[4] (tproject1 (tproject1 (tproject2 v1)) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v18), ssum0 @[4] (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v18)]) + tproject2 (tproject2 v1)) ; x20 = ssum0 @[10] v19 ; v21 = sreplicate0N @[10] (recip x20) ; v23 = v19 * (sreplicate0N @[10] (negate (recip (x20 * x20)) * ssum0 @[10] (v19 * sfromR dret)) + v21 * sfromR dret) ; v24 = sreplicate0N @[4] (v23 `sindex0` [9]) ; v25 = sreplicate0N @[4] (v23 `sindex0` [8]) ; v26 = sreplicate0N @[4] (v23 `sindex0` [7]) ; v27 = sreplicate0N @[4] (v23 `sindex0` [6]) ; v28 = sreplicate0N @[4] (v23 `sindex0` [5]) ; v29 = sreplicate0N @[4] (v23 `sindex0` [4]) ; v30 = sreplicate0N @[4] (v23 `sindex0` [3]) ; v31 = sreplicate0N @[4] (v23 `sindex0` [2]) ; v32 = sreplicate0N @[4] (v23 `sindex0` [1]) ; v33 = sreplicate0N @[4] (v23 `sindex0` [0]) in tpair (let v34 = v17 * (tproject1 (tproject1 (tproject2 v1)) * v33 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v32 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v29 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v28 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v27 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v26 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v25 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v24))))))))) ; v35 = scast v34 ; v36 = sreplicate0N @[3] (v35 `sindex0` [3]) ; v37 = sreplicate0N @[3] (v35 `sindex0` [2]) ; v38 = sreplicate0N @[3] (v35 `sindex0` [1]) ; v39 = sreplicate0N @[3] (v35 `sindex0` [0]) in tpair (let v40 = v12 * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v39 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v38 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v37 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v36))) in tpair (tpair (sfromPlain (sreplicate0N @[784] 7.0) * sreplicate0N @[784] (v40 `sindex0` [0])) (tpair (sfromPlain (sreplicate0N @[784] 7.0) * sreplicate0N @[784] (v40 `sindex0` [1])) (tpair (sfromPlain (sreplicate0N @[784] 7.0) * sreplicate0N @[784] (v40 `sindex0` [2])) Z1))) v40) (tpair (tpair (v13 * v39) (tpair (v13 * v38) (tpair (v13 * v37) (tpair (v13 * v36) Z1)))) v34)) (tpair (tpair (v18 * v33) (tpair (v18 * v32) (tpair (v18 * v31) (tpair (v18 * v30) (tpair (v18 * v29) (tpair (v18 * v28) (tpair (v18 * v27) (tpair (v18 * v26) (tpair (v18 * v25) (tpair (v18 * v24) Z1)))))))))) v23)"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret v1 -> let v11 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [7.0 * ssum0 @[784] (tproject1 (tproject1 (tproject1 (tproject1 v1)))), 7.0 * ssum0 @[784] (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), 7.0 * ssum0 @[784] (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1))))) ; v13 = scast v11 ; v16 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v13, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v13, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v13, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v13]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v19 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v16, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v16, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v16]) + tproject2 (tproject2 v1)) ; x20 = ssum0 @[10] v19 ; v23 = v19 * (sreplicate0N @[10] (negate (recip (x20 * x20)) * sdot0 v19 (sfromR dret)) + sreplicate0N @[10] (recip x20) * sfromR dret) ; x24 = v23 `sindex0` [9] ; x25 = v23 `sindex0` [8] ; x26 = v23 `sindex0` [7] ; x27 = v23 `sindex0` [6] ; x28 = v23 `sindex0` [5] ; x29 = v23 `sindex0` [4] ; x30 = v23 `sindex0` [3] ; x31 = v23 `sindex0` [2] ; x32 = v23 `sindex0` [1] ; x33 = v23 `sindex0` [0] in tpair (let v34 = v16 * ((sconcrete (sreplicate [4] 1.0) + negate v16) * (tproject1 (tproject1 (tproject2 v1)) * sreplicate0N @[4] x33 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate0N @[4] x32 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate0N @[4] x31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate0N @[4] x30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate0N @[4] x29 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate0N @[4] x28 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate0N @[4] x27 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate0N @[4] x26 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate0N @[4] x25 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate0N @[4] x24)))))))))) ; v35 = scast v34 ; x36 = v35 `sindex0` [3] ; x37 = v35 `sindex0` [2] ; x38 = v35 `sindex0` [1] ; x39 = v35 `sindex0` [0] in tpair (let v40 = v11 * ((sconcrete (sreplicate [3] 1.0) + negate v11) * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate0N @[3] x39 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate0N @[3] x38 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate0N @[3] x37 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate0N @[3] x36)))) in tpair (tpair (sreplicate0N @[784] (7.0 * v40 `sindex0` [0])) (tpair (sreplicate0N @[784] (7.0 * v40 `sindex0` [1])) (tpair (sreplicate0N @[784] (7.0 * v40 `sindex0` [2])) Z1))) v40) (tpair (tpair (v13 * sreplicate0N @[3] x39) (tpair (v13 * sreplicate0N @[3] x38) (tpair (v13 * sreplicate0N @[3] x37) (tpair (v13 * sreplicate0N @[3] x36) Z1)))) v34)) (tpair (tpair (v16 * sreplicate0N @[4] x33) (tpair (v16 * sreplicate0N @[4] x32) (tpair (v16 * sreplicate0N @[4] x31) (tpair (v16 * sreplicate0N @[4] x30) (tpair (v16 * sreplicate0N @[4] x29) (tpair (v16 * sreplicate0N @[4] x28) (tpair (v16 * sreplicate0N @[4] x27) (tpair (v16 * sreplicate0N @[4] x26) (tpair (v16 * sreplicate0N @[4] x25) (tpair (v16 * sreplicate0N @[4] x24) Z1)))))))))) v23)"

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
    @?= "\\dret m1 -> let v5 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; m6 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 7.0) * v5 + sfromR (tproject2 (tproject1 (tproject1 m1)))))) in tpair (let v9 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m10 = sreplicate @4 (scast v9) in tpair (let v11 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m10))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v11)))) (rfromS v11)) (tpair (rfromS (str (m6 * m10))) (rfromS v9))) (tpair (rfromS (str (let m7 = str (sreplicate @2 (scast (ssum @4 (m6 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in m7 * sreplicate @5 (sfromR dret)))) (rfromS (sfromR dret)))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v5 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; m6 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 7.0) * v5 + sfromR (tproject2 (tproject1 (tproject1 m1)))))) in tpair (let v9 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m10 = sreplicate @4 (scast v9) in tpair (let v11 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m10))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v11)))) (rfromS v11)) (tpair (rfromS (str (m6 * m10))) (rfromS v9))) (tpair (rfromS (str (let m7 = str (sreplicate @2 (scast (ssum @4 (m6 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in m7 * sreplicate @5 (sfromR dret)))) (rfromS (sfromR dret)))"
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
    @?= "\\dummy -> tfromPlain (STKR (SNat @1) STKScalar) (rfromS (tlet (exp (ssum @5 (str (sreplicate @2 (tlet (ssum @4 (sconcrete (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0]) * str (sreplicate @5 (tlet (sconcrete (sreplicate [4] 7.0) * ssum @3 (str (scast (sconcrete (sfromListLinear [4,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0])))) + scast (sconcrete (sfromListLinear [4] [1.0,2.0,3.0,4.0]))) (\\v7 -> recip (sconcrete (sreplicate [4] 1.0) + exp (negate v7)))))) + scast (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0]))) (\\v10 -> recip (sconcrete (sreplicate [5] 1.0) + exp (negate v10))))) * str (scast (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0])))) + scast (sconcrete (sfromListLinear [2] [1.0,2.0])))) (\\v12 -> sreplicate0N @[2] (recip (ssum0 @[2] v12)) * v12)))"
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
    @?= "\\m1 -> rfromS (let v21 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (recip (scast (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in sreplicate0N @[2] (recip (ssum0 @[2] v21)) * v21)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> rfromS (let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = recip (sconcrete (sreplicate [4] 1.0) + v12) ; m15 = str (sreplicate @5 (scast (v13 + sconcrete (sreplicate [4] 0.0)))) ; v16 = scast (ssum @4 (m15 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v17 = exp (negate v16) ; v18 = recip (sconcrete (sreplicate [5] 1.0) + v17) ; m20 = str (sreplicate @2 (v18 + sconcrete (sreplicate [5] 0.0))) ; v21 = exp (ssum @5 (m20 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x22 = ssum0 @[2] v21 ; v23 = sreplicate0N @[2] (recip x22) in v23 * v21)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v11 = sconcrete (sreplicate [4] 7.0) * v10 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v12 = exp (negate v11) ; v13 = recip (sconcrete (sreplicate [4] 1.0) + v12) ; v14 = v13 * (sconcrete (sreplicate [4] 1.0) + negate v13) ; m15 = str (sreplicate @5 (scast (v13 + sconcrete (sreplicate [4] 0.0)))) ; v16 = scast (ssum @4 (m15 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v17 = exp (negate v16) ; v18 = recip (sconcrete (sreplicate [5] 1.0) + v17) ; v19 = v18 * (sconcrete (sreplicate [5] 1.0) + negate v18) ; m20 = str (sreplicate @2 (v18 + sconcrete (sreplicate [5] 0.0))) ; v21 = exp (ssum @5 (m20 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x22 = ssum0 @[2] v21 ; v23 = sreplicate0N @[2] (recip x22) ; v25 = v21 * (sreplicate0N @[2] (negate (recip (x22 * x22)) * ssum0 @[2] (v21 * sfromR dret)) + v23 * sfromR dret) in tpair (let v26 = v19 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v25)) ; m27 = sreplicate @4 (scast v26) in tpair (let v28 = v14 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m27))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v28)))) (rfromS v28)) (tpair (rfromS (str (m15 * m27))) (rfromS v26))) (tpair (rfromS (str (m20 * sreplicate @5 v25))) (rfromS v25))"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v15 = scast v13 ; v18 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v15) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v21 = exp (sdot1In (sreplicate @2 v18) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x22 = ssum0 @[2] v21 ; v25 = v21 * (sreplicate0N @[2] (negate (recip (x22 * x22)) * sdot0 v21 (sfromR dret)) + sreplicate0N @[2] (recip x22) * sfromR dret) in tpair (let v26 = v18 * ((sconcrete (sreplicate [5] 1.0) + negate v18) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v25)) ; v27 = scast v26 in tpair (let v28 = v13 * ((sconcrete (sreplicate [4] 1.0) + negate v13) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v27))) in tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v28))) v28) (tpair (sreplicate @5 v15 * str (sreplicate @4 v27)) v26)) (tpair (sreplicate @2 v18 * str (sreplicate @5 v25)) v25))"

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
    @?= "\\m1 -> let v22 = exp (sdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 (recip (scast (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in (-8.0) * ssum0 @[2] (log (sreplicate0N @[2] (recip (ssum0 @[2] v22)) * v22))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v11 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v12 = sconcrete (sreplicate [4] 7.0) * v11 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v13 = exp (negate v12) ; v14 = recip (sconcrete (sreplicate [4] 1.0) + v13) ; m16 = str (sreplicate @5 (scast (v14 + sconcrete (sreplicate [4] 0.0)))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = recip (sconcrete (sreplicate [5] 1.0) + v18) ; m21 = str (sreplicate @2 (v19 + sconcrete (sreplicate [5] 0.0))) ; v22 = exp (ssum @5 (m21 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x23 = ssum0 @[2] v22 ; v24 = sreplicate0N @[2] (recip x23) ; v25 = v24 * v22 ; x26 = ssum0 @[2] (log v25) in (-8.0) * x26"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v11 = ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) ; v12 = sconcrete (sreplicate [4] 7.0) * v11 + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v13 = exp (negate v12) ; v14 = recip (sconcrete (sreplicate [4] 1.0) + v13) ; v15 = v14 * (sconcrete (sreplicate [4] 1.0) + negate v14) ; m16 = str (sreplicate @5 (scast (v14 + sconcrete (sreplicate [4] 0.0)))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = recip (sconcrete (sreplicate [5] 1.0) + v18) ; v20 = v19 * (sconcrete (sreplicate [5] 1.0) + negate v19) ; m21 = str (sreplicate @2 (v19 + sconcrete (sreplicate [5] 0.0))) ; v22 = exp (ssum @5 (m21 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x23 = ssum0 @[2] v22 ; v24 = sreplicate0N @[2] (recip x23) ; v25 = v24 * v22 ; v28 = recip v25 * sreplicate0N @[2] ((-8.0) * dret) ; v29 = v22 * (sreplicate0N @[2] (negate (recip (x23 * x23)) * ssum0 @[2] (v22 * v28)) + v24 * v28) in tpair (let v30 = v20 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v29)) ; m31 = sreplicate @4 (scast v30) in tpair (let v32 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m31))) in tpair (rfromS (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v32)))) (rfromS v32)) (tpair (rfromS (str (m16 * m31))) (rfromS v30))) (tpair (rfromS (str (m21 * sreplicate @5 v29))) (rfromS v29))"
  printArtifactPretty (simplifyArtifactRev artifactRevnonLin)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKS [4,3] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [5,4] STKScalar) (STKS [5] STKScalar))) (STKProduct (STKS [2,5] STKScalar) (STKS [2] STKScalar))) (let v14 = recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sreplicate [4] (-7.0)) * ssum @3 (str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v16 = scast v14 ; v19 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (sdot1In (sreplicate @5 v16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v22 = exp (sdot1In (sreplicate @2 v19) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x23 = ssum0 @[2] v22 ; x24 = recip x23 ; v28 = sreplicate0N @[2] ((-8.0) * dret) / (sreplicate0N @[2] x24 * v22) ; v29 = v22 * (sreplicate0N @[2] (negate (recip (x23 * x23)) * sdot0 v22 v28) + sreplicate0N @[2] x24 * v28) in tpair (let v30 = v19 * ((sconcrete (sreplicate [5] 1.0) + negate v19) * sdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v29)) ; v31 = scast v30 in tpair (let v32 = v14 * ((sconcrete (sreplicate [4] 1.0) + negate v14) * scast (sdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v31))) in tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v32))) v32) (tpair (sreplicate @5 v16 * str (sreplicate @4 v31)) v30)) (tpair (sreplicate @2 v19 * str (sreplicate @5 v29)) v29))"

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
      blackGlyph = rreplicateN (1 :$: 1 :$: 1 :$: ZSR)
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
    @?= "\\m1 -> rfromS (str (sreplicate @1 (str (sfromR (tproject1 (tproject2 m1))) !$ [0] * sreplicate0N @[10] (tanh (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] * tanh (7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0])))) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (let x16 = sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] ; x17 = tanh (7.0 * x16 + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0]) ; v20 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] in str (sreplicate @1 (v20 * sreplicate0N @[10] x19)) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let x16 = sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] ; x17 = tanh (7.0 * x16 + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0]) ; v20 = str (sfromR (tproject1 (tproject2 m1))) !$ [0] ; v22 = ssum @1 (str (sfromR dret)) in tpair (let x23 = (1.0 + negate (x19 * x19)) * ssum0 @[10] (v20 * v22) in tpair (let x24 = (1.0 + negate (x17 * x17)) * (x18 * x23) in tpair (tpair (rfromS (soneHot (sfromK (7.0 * x24)) [0, 0])) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (rfromS (soneHot (sfromK x24) [0]))) (tpair (tpair (rfromS (soneHot (sfromK (x17 * x23)) [0, 0])) (rfromS (sconcrete (sfromListLinear [1,1] [0.0])))) (rfromS (soneHot (sfromK x23) [0])))) (tpair (rfromS (str (soneHot (sreplicate0N @[10] x19 * v22) [0]))) (rfromS (ssum @1 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKS [1,1] STKScalar)) (STKS [1] STKScalar)) (STKProduct (STKProduct (STKS [1,1] STKScalar) (STKS [1,1] STKScalar)) (STKS [1] STKScalar))) (STKProduct (STKS [10,1] STKScalar) (STKS [10] STKScalar))) (let x17 = tanh (7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) `sindex0` [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) `sindex0` [0]) ; x18 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) `sindex0` [0, 0] ; x19 = tanh (x18 * x17 + sfromR (tproject2 (tproject2 (tproject1 m1))) `sindex0` [0]) ; v22 = str (sfromR dret) !$ [0] in tpair (let x23 = (1.0 + negate x19 * x19) * sdot0 (str (sfromR (tproject1 (tproject2 m1))) !$ [0]) v22 in tpair (let x24 = (1.0 + negate x17 * x17) * (x18 * x23) in tpair (tpair (sreplicate0N @[1, 1] (7.0 * x24)) (sconcrete (sfromListLinear [1,1] [0.0]))) (sreplicate0N @[1] x24)) (tpair (tpair (sreplicate0N @[1, 1] (x17 * x23)) (sconcrete (sfromListLinear [1,1] [0.0]))) (sreplicate0N @[1] x23))) (tpair (str (sreplicate @1 (sreplicate0N @[10] x19 * v22))) (str (sfromR dret) !$ [0])))"

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
      blackGlyph = rreplicateN (2 :$: 2 :$: 2 :$: ZSR)
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
    @?= "\\m1 -> rfromS (let m43 = sappend (tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) (tanh (str (sreplicate @2 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 (tanh (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh (smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + (smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice (SNat @0) (SNat @2) m43) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))))) + (smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m43) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (let v38 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m39 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v38)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v40 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; v41 = tanh (sconcrete (sreplicate [2] 7.0) * v40 + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m42 = tanh (str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v41)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m43 = sappend m39 m42 ; v44 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m45 = tanh (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v44) + (ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * stranspose @[2, 1, 0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m43)))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m46 = tanh (ssum @2 (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2, 0, 1] (sreplicate @2 m45)) + (ssum @2 (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2, 0, 1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m43)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in ssum @2 (stranspose @[2, 1, 0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * str (sreplicate @10 m46)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v38 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m39 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v38)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v40 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; v41 = tanh (sconcrete (sreplicate [2] 7.0) * v40 + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m42 = tanh (str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v41)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m43 = sappend m39 m42 ; v44 = ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) ; m45 = tanh (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v44) + (ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * stranspose @[2, 1, 0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m43)))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m46 = tanh (ssum @2 (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2, 0, 1] (sreplicate @2 m45)) + (ssum @2 (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2, 0, 1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m43)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in tpair (let m48 = (sconcrete (sreplicate [2,2] 1.0) + negate (m46 * m46)) * ssum @10 (str (stranspose @[2, 1, 0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @2 (sfromR dret))) ; m49 = (sconcrete (sreplicate [2,2] 1.0) + negate (m45 * m45)) * ssum @2 (stranspose @[1, 2, 0] (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m48)) ; m50 = sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (str (ssum @2 (stranspose @[2, 1, 0] (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * sreplicate @2 m49)))) (sconcrete (sreplicate [2,2] 0.0))) + sappend (sconcrete (sreplicate [2,2] 0.0)) (sappend (str (ssum @2 (stranspose @[1, 2, 0] (stranspose @[1, 2, 0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m48)))) (sconcrete (sfromListLinear [0,2] []))) ; m51 = (sconcrete (sreplicate [2,2] 1.0) + negate (m42 * m42)) * sslice (SNat @2) (SNat @2) m50 ; m52 = sreplicate @2 (ssum @2 (str m51)) in tpair (let v53 = (sconcrete (sreplicate [2] 1.0) + negate (v41 * v41)) * ssum @2 (str (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * m52)) ; m54 = (sconcrete (sreplicate [2,2] 1.0) + negate (m39 * m39)) * sslice (SNat @0) (SNat @2) m50 in tpair (tpair (rfromS (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str m54))) + (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v53)) + str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 m49))))) (rfromS (str (ssum @2 (str (stranspose @[2, 1, 0] (sreplicate @2 (str (sslice (SNat @0) (SNat @2) m43))) * sreplicate @2 m49)))))) (rfromS (ssum @2 (str m54) + (v53 + ssum @2 m49)))) (tpair (tpair (rfromS (str (str (sreplicate @2 v41) * m52) + str (ssum @2 (stranspose @[2, 0, 1] (stranspose @[2, 0, 1] (sreplicate @2 m45) * sreplicate @2 m48))))) (rfromS (str (ssum @2 (stranspose @[2, 0, 1] (stranspose @[2, 0, 1] (sreplicate @2 (str (sslice (SNat @2) (SNat @2) m43))) * sreplicate @2 m48)))))) (rfromS (ssum @2 (str m51) + ssum @2 (str m48))))) (tpair (rfromS (ssum @2 (stranspose @[2, 1, 0] (str (sreplicate @10 m46) * sreplicate @2 (sfromR dret))))) (rfromS (ssum @2 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret m1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (STKProduct (STKProduct (STKProduct (STKProduct (STKS [2,2] STKScalar) (STKS [2,2] STKScalar)) (STKS [2] STKScalar)) (STKProduct (STKProduct (STKS [2,2] STKScalar) (STKS [2,2] STKScalar)) (STKS [2] STKScalar))) (STKProduct (STKS [10,2] STKScalar) (STKS [10] STKScalar))) (let m39 = tanh (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v41 = tanh (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m42 = tanh (str (sreplicate @2 (sdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 v41))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m43 = sappend m39 m42 ; m45 = tanh (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) + (smatmul2 (str (sslice (SNat @0) (SNat @2) m43)) (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m46 = tanh (smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (str m45) + (smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m43) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in tpair (let m48 = (sconcrete (sreplicate [2,2] 1.0) + negate m46 * m46) * smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR dret) ; m49 = (sconcrete (sreplicate [2,2] 1.0) + negate m45 * m45) * smatmul2 (str m48) (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) ; m50 = sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) (str m49)) (sconcrete (sreplicate [2,2] 0.0)) + sappend (sconcrete (sreplicate [2,2] 0.0)) (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) m48) ; m51 = (sconcrete (sreplicate [2,2] 1.0) + negate m42 * m42) * sslice (SNat @2) (SNat @2) m50 ; v52 = ssum @2 (str m51) in tpair (let v53 = (sconcrete (sreplicate [2] 1.0) + negate v41 * v41) * sdot1In (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) (sreplicate @2 v52) ; m54 = (sconcrete (sreplicate [2,2] 1.0) + negate m39 * m39) * sslice (SNat @0) (SNat @2) m50 in tpair (tpair (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str m54))) + (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v53)) + str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 m49)))) (smatmul2 (str m49) (str (sslice (SNat @0) (SNat @2) m43)))) (ssum @2 (str m54) + (v53 + ssum @2 m49))) (tpair (tpair (sreplicate @2 v41 * str (sreplicate @2 v52) + smatmul2 m48 m45) (smatmul2 m48 (str (sslice (SNat @2) (SNat @2) m43)))) (ssum @2 (str m51) + ssum @2 (str m48)))) (tpair (smatmul2 (sfromR dret) (str m46)) (ssum @2 (str (sfromR dret)))))"

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
    @?= "\\u1 -> rfromS (let t259 = sreplicate @1 (ssum @2 (sdot1In (sfromPlain (stranspose @[1, 2, 0] (sgather @[9, 2] (stranspose @[2, 0, 1] (sgather @[7, 2] (sconcrete (sreplicate [7,9] 7.0)) (\\[i474, i475] -> [i474 + i475]))) (\\[i253, i254] -> [i253 + i254])))) (stranspose @[2, 0, 3, 1] (sreplicate @7 (stranspose @[1, 2, 0] (sreplicate @9 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0]))))))) + stranspose @[2, 0, 1] (sreplicateN @[7, 9] (sfromR (tproject2 (tproject1 (tproject1 u1))))) ; u272 = sreshape @[5, 3, 4, 4] (stranspose @[2, 3, 4, 0, 1] (sreplicateN @[1, 1] (sfromPlain (sreplicate @5 (sgather @[3, 4, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i262, i263, i264, i265] -> [ifH (0.0 <=. negate (splainPart t259 `sindex0` [0, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i262, i264], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i263, i265]])) 0 1]))) * stranspose @[4, 0, 1, 2, 3] (sgather @[3, 4, 2, 2] (stranspose @[2, 1, 0] (sreplicate @5 (stranspose @[0, 2, 1] t259 !$ [0]))) (\\[i266, i267, i268, i269] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i266, i268], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i267, i269]]))))) ; u282 = str (sreplicate @1 (ssum @2 (sdot1In (stranspose @[1, 4, 2, 3, 0] (sgather @[2, 2, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[3, 4, 5] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @2 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicateN @[2, 4, 3] (stranspose @[3, 2, 1, 0] u272))))) (\\[i464, i465, i466] -> [i466, i464, i465, kargMax (splainPart u272 !$ [i466, i464, i465])]))) (\\[i276, i277, i278, i279] -> [i278, i279, i276, i277, i278 + i276, i279 + i277]))) (stranspose @[2, 0, 3, 4, 1] (sreplicate @5 (stranspose @[1, 2, 0] (sreplicate @3 (stranspose @[1, 2, 0] (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])))))))))) + sreplicate @5 (stranspose @[2, 0, 1] (sreplicateN @[3, 4] (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; t292 = sreshape @[5, 2, 4] (stranspose @[2, 3, 0, 1] (sreplicateN @[1, 1] (sfromPlain (sgather @[5, 2, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i284, i285, i286, i287] -> [ifH (0.0 <=. negate (splainPart u282 `sindex0` [i284, 0, i286, sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i285, i287]])) 0 1])) * stranspose @[2, 0, 3, 1] (sgather @[2, 2] (stranspose @[1, 2, 0] (sslice (SNat @0) (SNat @2) (stranspose @[1, 2, 3, 0] u282 !$ [0]))) (\\[i288, i289] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i288, i289]]))))) ; m297 = sreplicate @1 (sdot1In (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0])) (sreshape @[5, 2] (stranspose @[2, 0, 1] (sreplicateN @[1, 1] (sgather @[5, 2] t292 (\\[i293, i294] -> [i293, i294, kargMax (splainPart t292 !$ [i293, i294])])))))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) * sreplicate @10 (sfromPlain (sgather1 @5 (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\i298 -> [ifH (0.0 <=. negate (splainPart m297 `sindex0` [0, i298])) 0 1])) * m297 !$ [0]) + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [1,1,2,2] STKScalar) (STKS [1] STKScalar)) (STKProduct (STKS [1,1,2,2] STKScalar) (STKS [1] STKScalar))) (STKProduct (STKProduct (STKS [1,2] STKScalar) (STKS [1] STKScalar)) (STKProduct (STKS [10,1] STKScalar) (STKS [10] STKScalar)))) (let u257 = sgather @[9, 2] (stranspose @[2, 0, 1] (sgather @[7, 2] (sconcrete (sreplicate [7,9] 7.0)) (\\[i566, i567] -> [i566 + i567]))) (\\[i253, i254] -> [i253 + i254]) ; t259 = sreplicate @1 (ssum @2 (sdot1In (sfromPlain (stranspose @[1, 2, 0] u257)) (stranspose @[2, 0, 3, 1] (sreplicate @7 (stranspose @[1, 2, 0] (sreplicate @9 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0]))))))) + stranspose @[2, 0, 1] (sreplicateN @[7, 9] (sfromR (tproject2 (tproject1 (tproject1 u1))))) ; u270 = sgather @[3, 4, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i262, i263, i264, i265] -> [ifH (0.0 <=. negate (splainPart t259 `sindex0` [0, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i262, i264], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i263, i265]])) 0 1]) ; u272 = sreshape @[5, 3, 4, 4] (stranspose @[2, 3, 4, 0, 1] (sreplicateN @[1, 1] (sfromPlain (sreplicate @5 u270) * stranspose @[4, 0, 1, 2, 3] (sgather @[3, 4, 2, 2] (stranspose @[2, 1, 0] (sreplicate @5 (stranspose @[0, 2, 1] t259 !$ [0]))) (\\[i266, i267, i268, i269] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i266, i268], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i267, i269]]))))) ; w280 = sgather @[2, 2, 3, 4] (stranspose @[3, 4, 5, 6, 0, 1, 2] (sgather @[3, 4, 5] (stranspose @[4, 3, 2, 1, 7, 6, 5, 0] (sreplicate @2 (stranspose @[3, 4, 5, 6, 0, 1, 2] (sreplicateN @[2, 4, 3] (stranspose @[3, 2, 1, 0] u272))))) (\\[i556, i557, i558] -> [i558, i556, i557, kargMax (splainPart u272 !$ [i558, i556, i557])]))) (\\[i276, i277, i278, i279] -> [i278, i279, i276, i277, i278 + i276, i279 + i277]) ; m281 = sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0] ; u282 = str (sreplicate @1 (ssum @2 (sdot1In (stranspose @[1, 4, 2, 3, 0] w280) (stranspose @[2, 0, 3, 4, 1] (sreplicate @5 (stranspose @[1, 2, 0] (sreplicate @3 (stranspose @[1, 2, 0] (sreplicate @4 m281))))))))) + sreplicate @5 (stranspose @[2, 0, 1] (sreplicateN @[3, 4] (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; u290 = sgather @[5, 2, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i284, i285, i286, i287] -> [ifH (0.0 <=. negate (splainPart u282 `sindex0` [i284, 0, i286, sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i285, i287]])) 0 1]) ; t292 = sreshape @[5, 2, 4] (stranspose @[2, 3, 0, 1] (sreplicateN @[1, 1] (sfromPlain u290 * stranspose @[2, 0, 3, 1] (sgather @[2, 2] (stranspose @[1, 2, 0] (sslice (SNat @0) (SNat @2) (stranspose @[1, 2, 3, 0] u282 !$ [0]))) (\\[i288, i289] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i288, i289]]))))) ; v295 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; m296 = sreshape @[5, 2] (stranspose @[2, 0, 1] (sreplicateN @[1, 1] (sgather @[5, 2] t292 (\\[i293, i294] -> [i293, i294, kargMax (splainPart t292 !$ [i293, i294])])))) ; m297 = sreplicate @1 (sdot1In (sreplicate @5 v295) m296) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v299 = sgather1 @5 (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\i298 -> [ifH (0.0 <=. negate (splainPart m297 `sindex0` [0, i298])) 0 1]) ; v304 = sfromPlain v299 * sdot1In (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) (str (sfromR dret)) in tpair (let t310 = sappend (stranspose @[2, 0, 1] (sscatter @[2, 2] (sfromPlain (stranspose @[1, 3, 0, 2] u290) * stranspose @[2, 3, 1, 5, 0, 4] (sreshape @[5, 2, 1, 1, 2, 2] (sscatter @[5, 2] (stranspose @[1, 2, 0] (sreshape @[5, 1, 1, 2] (sreplicate @5 v295 * str (sreplicate @2 v304))) !$ [0, 0]) (\\[i306, i307] -> [i306, i307, kargMax (splainPart t292 !$ [i306, i307])]))) !$ [0, 0]) (\\[i308, i309] -> [sconcrete (sfromListLinear [2,2] [0,1,2,3]) `sindex0` [i308, i309]]))) (sconcrete (sreplicate [1,4,5] 0.0)) in tpair (let m323 = ssum @5 (stranspose @[2, 0, 1] (sscatter @[3, 4, 2, 2] (sfromPlain (stranspose @[1, 2, 3, 4, 0] (sreplicate @5 u270)) * stranspose @[3, 4, 1, 2, 5, 6, 0] (sreshape @[5, 3, 4, 1, 1, 2, 2] (ssumN @[2, 2, 4, 3] (stranspose @[7, 6, 5, 4, 0, 1, 2, 3] (sscatter @[3, 4, 5] (stranspose @[4, 5, 6, 0, 1, 2, 3] (sscatter @[2, 2, 3, 4] (stranspose @[1, 2, 3, 4, 0] (sreplicate @5 (stranspose @[1, 2, 0] (sreplicate @3 (stranspose @[1, 2, 0] (sreplicate @4 m281))))) * sreplicateN @[2, 2] t310) (\\[i312, i313, i314, i315] -> [i314, i315, i312, i313, i314 + i312, i315 + i313]))) (\\[i316, i317, i318] -> [i318, i316, i317, kargMax (splainPart u272 !$ [i318, i316, i317])]))))) !$ [0, 0]) (\\[i319, i320, i321, i322] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i319, i321], sconcrete (sfromListLinear [4,2] [0,1,2,3,4,5,6,7]) `sindex0` [i320, i322]]))) in tpair (sreplicateN @[1, 1] (ssum @9 (sdot1In (sfromPlain (stranspose @[0, 3, 1, 2] u257)) (stranspose @[3, 0, 1, 2] (sreplicateN @[2, 2] m323))))) (ssumN @[7, 9] (stranspose @[1, 2, 0] (sreplicate @1 m323)))) (tpair (sreplicateN @[1, 1] (ssumN @[3, 4] (sdot1In (stranspose @[2, 3, 0, 1] w280) (stranspose @[3, 4, 0, 1, 2] (sreplicateN @[2, 2] (stranspose @[2, 0, 1] t310)))))) (ssumN @[5, 3, 4] (stranspose @[3, 1, 2, 0] (sreplicate @1 t310))))) (tpair (tpair (sreplicate @1 (sdot1In (str m296) (sreplicate @2 v304))) (ssum @5 (str (sreplicate @1 v304)))) (tpair (str (sreplicate @1 (sdot1In (sreplicate @10 (sfromPlain v299 * m297 !$ [0])) (sfromR dret)))) (ssum @5 (str (sfromR dret))))))"

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
    @?= "\\u1 -> rfromS (let t324 = ssum @4 (sdot1In (sfromPlain (stranspose @[2, 0, 3, 4, 1] (sreplicate @4 (stranspose @[3, 1, 2, 0] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sreplicate0N @[14, 23] 7.0) (\\[i572, i573] -> [i572 + i573]))) (\\[i318, i319] -> [i318 + i319])))))) (stranspose @[3, 1, 0, 4, 2] (sreplicate @14 (stranspose @[1, 2, 3, 0] (sreplicate @23 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))) + stranspose @[2, 0, 1] (sreplicateN @[14, 23] (sfromR (tproject2 (tproject1 (tproject1 u1))))) ; w338 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (sfromPlain (sreplicate @7 (sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i327, i328, i329, i330, i331] -> [ifH (0.0 <=. negate (splainPart t324 `sindex0` [i327, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i328, i330], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i329, i331]])) 0 1]))) * stranspose @[5, 4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[2, 1, 3, 0] (sreplicate @7 (stranspose @[2, 1, 0] t324))) (\\[i332, i333, i334, i335] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i332, i334], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i333, i335]]))))) ; u348 = ssumN @[3, 4] (sdot1In (stranspose @[3, 4, 1, 0, 5, 6, 2] (sreplicate @4 (stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 11, 3, 4] (stranspose @[4, 5, 6, 7, 0, 1, 2, 3] (sgather @[7, 11, 7, 4] (stranspose @[5, 4, 3, 2, 1, 8, 7, 6, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 7, 0, 1, 2] (sreplicateN @[3, 11, 7] (stranspose @[4, 3, 2, 1, 0] w338))))) (\\[i563, i564, i565, i566] -> [i565, i566, i563, i564, kargMax (splainPart w338 !$ [i565, i566, i563, i564])]))) (\\[i343, i344, i345, i346] -> [i343, i344, i345, i346, i343 + i345, i344 + i346]))))) (stranspose @[2, 3, 0, 4, 5, 6, 1] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicateN @[7, 11] (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; w363 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (sfromPlain (sgather @[7, 4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i351, i352, i353, i354, i355, i356] -> [ifH (0.0 <=. negate (splainPart u348 `sindex0` [i351, i352, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i353, i355], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i354, i356]])) 0 1])) * stranspose @[4, 5, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[2, 3, 0, 1] u348) (\\[i357, i358, i359, i360] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i357, i359], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i358, i360]]))))) ; m370 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str (sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w363))) (\\[i364, i365, i366, i367] -> [i364, i365, i366, i367, kargMax (splainPart w363 !$ [i364, i365, i366, i367])])))) (\\i368 -> [i368, i368]))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in smatmul2 (sfromR (tproject1 (tproject2 (tproject2 u1)))) (sfromPlain (sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i371, i372] -> [ifH (0.0 <=. negate (splainPart m370 `sindex0` [i371, i372])) 0 1])) * m370) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> tconvert (ConvT2 (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX))) (ConvT2 (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)) (ConvT2 (ConvCmp (ConvXR STKScalar) ConvSX) (ConvCmp (ConvXR STKScalar) ConvSX)))) (STKProduct (STKProduct (STKProduct (STKS [4,1,3,4] STKScalar) (STKS [4] STKScalar)) (STKProduct (STKS [4,4,3,4] STKScalar) (STKS [4] STKScalar))) (STKProduct (STKProduct (STKS [5,60] STKScalar) (STKS [5] STKScalar)) (STKProduct (STKS [10,5] STKScalar) (STKS [10] STKScalar)))) (let u322 = sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sreplicate0N @[14, 23] 7.0) (\\[i678, i679] -> [i678 + i679]))) (\\[i318, i319] -> [i318 + i319]) ; t324 = ssum @4 (sdot1In (sfromPlain (stranspose @[2, 0, 3, 4, 1] (sreplicate @4 (stranspose @[3, 1, 2, 0] u322)))) (stranspose @[3, 1, 0, 4, 2] (sreplicate @14 (stranspose @[1, 2, 3, 0] (sreplicate @23 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))) + stranspose @[2, 0, 1] (sreplicateN @[14, 23] (sfromR (tproject2 (tproject1 (tproject1 u1))))) ; w336 = sgather @[4, 7, 11, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i327, i328, i329, i330, i331] -> [ifH (0.0 <=. negate (splainPart t324 `sindex0` [i327, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i328, i330], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i329, i331]])) 0 1]) ; w338 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (sfromPlain (sreplicate @7 w336) * stranspose @[5, 4, 0, 1, 2, 3] (sgather @[7, 11, 2, 2] (stranspose @[2, 1, 3, 0] (sreplicate @7 (stranspose @[2, 1, 0] t324))) (\\[i332, i333, i334, i335] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i332, i334], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i333, i335]]))))) ; w347 = sgather @[7, 11, 3, 4] (stranspose @[4, 5, 6, 7, 0, 1, 2, 3] (sgather @[7, 11, 7, 4] (stranspose @[5, 4, 3, 2, 1, 8, 7, 6, 0] (sreplicate @4 (stranspose @[3, 4, 5, 6, 7, 0, 1, 2] (sreplicateN @[3, 11, 7] (stranspose @[4, 3, 2, 1, 0] w338))))) (\\[i667, i668, i669, i670] -> [i669, i670, i667, i668, kargMax (splainPart w338 !$ [i669, i670, i667, i668])]))) (\\[i343, i344, i345, i346] -> [i343, i344, i345, i346, i343 + i345, i344 + i346]) ; u348 = ssumN @[3, 4] (sdot1In (stranspose @[3, 4, 1, 0, 5, 6, 2] (sreplicate @4 (stranspose @[4, 5, 2, 3, 0, 1] w347))) (stranspose @[2, 3, 0, 4, 5, 6, 1] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicateN @[7, 11] (sfromR (tproject2 (tproject2 (tproject1 u1)))))) ; w361 = sgather @[7, 4, 3, 5, 2, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i351, i352, i353, i354, i355, i356] -> [ifH (0.0 <=. negate (splainPart u348 `sindex0` [i351, i352, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i353, i355], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i354, i356]])) 0 1]) ; w363 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (sfromPlain w361 * stranspose @[4, 5, 0, 1, 2, 3] (sgather @[3, 5, 2, 2] (stranspose @[2, 3, 0, 1] u348) (\\[i357, i358, i359, i360] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i357, i359], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i358, i360]]))))) ; m369 = sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w363))) (\\[i364, i365, i366, i367] -> [i364, i365, i366, i367, kargMax (splainPart w363 !$ [i364, i365, i366, i367])])))) (\\i368 -> [i368, i368]) ; m370 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str m369) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m373 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i371, i372] -> [ifH (0.0 <=. negate (splainPart m370 `sindex0` [i371, i372])) 0 1]) ; m376 = sfromPlain m373 * smatmul2 (str (sfromR (tproject1 (tproject2 (tproject2 u1))))) (sfromR dret) in tpair (let u386 = sscatter @[3, 5, 2, 2] (sfromPlain (stranspose @[2, 3, 4, 5, 0, 1] w361) * stranspose @[4, 5, 2, 3, 6, 7, 0, 1] (sreshape @[7, 4, 3, 5, 1, 1, 2, 2] (ssum @7 (stranspose @[5, 0, 1, 2, 3, 4] (sscatter @[7, 4, 3, 5] (stranspose @[1, 2, 3, 4, 0] (sreshape @[7, 7, 4, 3, 5] (sscatter1 @7 (smatmul2 (str m376) (sfromR (tproject1 (tproject1 (tproject2 u1))))) (\\i377 -> [i377, i377])))) (\\[i378, i379, i380, i381] -> [i378, i379, i380, i381, kargMax (splainPart w363 !$ [i378, i379, i380, i381])]))))) !$ [0, 0]) (\\[i382, i383, i384, i385] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i382, i384], sconcrete (sfromListLinear [5,2] [0,1,2,3,4,5,6,7,8,9]) `sindex0` [i383, i385]]) in tpair (let t399 = ssum @7 (stranspose @[3, 2, 0, 1] (sscatter @[7, 11, 2, 2] (sfromPlain (stranspose @[2, 3, 4, 5, 1, 0] (sreplicate @7 w336)) * stranspose @[4, 5, 2, 3, 6, 7, 1, 0] (sreshape @[7, 4, 7, 11, 1, 1, 2, 2] (ssumN @[4, 3, 11, 7] (stranspose @[8, 7, 6, 5, 0, 1, 2, 3, 4] (sscatter @[7, 11, 7, 4] (stranspose @[4, 5, 6, 7, 0, 1, 2, 3] (sscatter @[7, 11, 3, 4] (sdot1In (stranspose @[5, 6, 2, 3, 0, 1, 4] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) (stranspose @[5, 6, 1, 2, 3, 0, 4] (sreplicateN @[4, 3, 4] (stranspose @[2, 3, 0, 1] u386)))) (\\[i387, i388, i389, i390] -> [i387, i388, i389, i390, i387 + i389, i388 + i390]))) (\\[i391, i392, i393, i394] -> [i393, i394, i391, i392, kargMax (splainPart w338 !$ [i393, i394, i391, i392])]))))) !$ [0, 0]) (\\[i395, i396, i397, i398] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i395, i397], sconcrete (sfromListLinear [11,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]) `sindex0` [i396, i398]]))) in tpair (str (sreplicate @1 (ssum @23 (sdot1In (sfromPlain (stranspose @[4, 0, 1, 2, 3] (sreplicate @4 (stranspose @[3, 1, 2, 0] u322)))) (stranspose @[4, 2, 0, 1, 3] (sreplicateN @[3, 4] t399)))))) (ssumN @[14, 23] (stranspose @[1, 2, 0] t399))) (tpair (ssumN @[7, 11] (sdot1In (stranspose @[5, 6, 0, 2, 3, 4, 1] (sreplicate @4 (stranspose @[4, 5, 2, 3, 0, 1] w347))) (stranspose @[5, 6, 4, 0, 1, 2, 3] (sreplicateN @[4, 3, 4] (stranspose @[2, 3, 0, 1] u386))))) (ssumN @[7, 11, 7] u386))) (tpair (tpair (smatmul2 m376 m369) (ssum @7 (str m376))) (tpair (smatmul2 (sfromR dret) (sfromPlain (str m373) * str m370)) (ssum @7 (str (sfromR dret))))))"

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
  assertEqualUpToEpsilon 1e-5
    (interpretAstFull @Concrete env afcnn1)
    (afcnn2 valsInit)
  assertEqualUpToEpsilon 1e-5
    (interpretAstFull @Concrete env
                      (simplifyUserCode @(TKR 2 Double) afcnn1))
    (afcnn2 valsInit)
  assertEqualUpToEpsilon 1e-5
    (interpretAstFull @Concrete env
                      (simplifyInlineContract @(TKR 2 Double) afcnn1))
    (afcnn2 valsInit)

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
    @?= "\\u1 -> let t304 = ssum @4 (sdot1In (sfromPlain (stranspose @[2, 0, 3, 4, 1] (sreplicate @4 (stranspose @[3, 1, 2, 0] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sreplicate0N @[14, 23] 7.0) (\\[i565, i566] -> [i565 + i566]))) (\\[i298, i299] -> [i298 + i299])))))) (stranspose @[3, 1, 0, 4, 2] (sreplicate @14 (stranspose @[1, 2, 3, 0] (sreplicate @23 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))) + stranspose @[2, 0, 1] (sreplicateN @[14, 23] (tproject2 (tproject1 (tproject1 u1)))) ; w317 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[11, 2] (sfromPlain (sreplicate @11 (sgather @[23, 7, 4, 7, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i306, i307, i308, i309, i310] -> [ifH (0.0 <=. negate (splainPart t304 `sindex0` [i308, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i309, i310], i306])) 0 1]))) * stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 2] (stranspose @[2, 0, 3, 1] (sreplicateN @[7, 11] (str t304))) (\\[i311, i312] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i311, i312]]))) (\\[i315, i316] -> [i315, 2 * i315 + i316]))))) ; u327 = ssumN @[3, 4] (sdot1In (stranspose @[3, 4, 1, 0, 5, 6, 2] (sreplicate @4 (stranspose @[2, 4, 5, 1, 3, 0] (sgather @[11, 4] (stranspose @[3, 5, 2, 0, 4, 1] (sgather @[7, 3] (stranspose @[4, 6, 0, 3, 5, 2, 1] (sgather @[7, 11, 4, 7] (stranspose @[1, 2, 3, 4, 5, 7, 6, 0] (sreplicate @3 (stranspose @[6, 5, 4, 3, 2, 0, 1] (sreplicateN @[11, 7] (stranspose @[4, 3, 2, 1, 0] w317))))) (\\[i549, i550, i551, i553] -> [i553, i551, i549, i550, kargMax (splainPart w317 !$ [i553, i551, i549, i550])]))) (\\[i557, i559] -> [i557, i559, i557 + i559]))) (\\[i324, i325] -> [i324, i324 + i325]))))) (stranspose @[2, 3, 0, 4, 5, 6, 1] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicateN @[7, 11] (tproject2 (tproject2 (tproject1 u1))))) ; w340 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[5, 2] (sfromPlain (sreplicate @5 (sgather @[11, 7, 4, 3, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333] -> [ifH (0.0 <=. negate (splainPart u327 `sindex0` [i330, i331, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i332, i333], i329])) 0 1]))) * stranspose @[4, 5, 2, 3, 0, 1] (sgather @[3, 2] (stranspose @[1, 3, 2, 0] (sreplicate @5 (stranspose @[2, 1, 0] u327))) (\\[i334, i335] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i334, i335]]))) (\\[i338, i339] -> [i338, 2 * i338 + i339]))))) ; m347 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str (sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w340))) (\\[i341, i342, i343, i344] -> [i341, i342, i343, i344, kargMax (splainPart w340 !$ [i341, i342, i343, i344])])))) (\\i345 -> [i345, i345]))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) in smatmul2 (tproject1 (tproject2 (tproject2 u1))) (sfromPlain (sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i348, i349] -> [ifH (0.0 <=. negate (splainPart m347 `sindex0` [i348, i349])) 0 1])) * m347) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w302 = stranspose @[1, 2, 0] (sreplicate @4 (stranspose @[3, 1, 2, 0] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sreplicate0N @[14, 23] 7.0) (\\[i300, i301] -> [i300 + i301]))) (\\[i298, i299] -> [i298 + i299])))) ; w303 = stranspose @[2, 3, 1, 0] (sreplicate @14 (stranspose @[1, 2, 3, 0] (sreplicate @23 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))) ; t304 = ssumN @[3, 4] (sfromPlain w302 * w303) + stranspose @[2, 0, 1] (sreplicateN @[14, 23] (tproject2 (tproject1 (tproject1 u1)))) ; m305 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; w313 = sreplicate @11 (sgather @[23, 7, 4, 7, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i306, i307, i308, i309, i310] -> [ifH (0.0 <=. negate (splainPart t304 `sindex0` [i308, m305 `sindex0` [i309, i310], i306])) 0 1])) ; w314 = stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 2] (stranspose @[2, 0, 3, 1] (sreplicateN @[7, 11] (str t304))) (\\[i311, i312] -> [m305 `sindex0` [i311, i312]])) ; w317 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[11, 2] (sfromPlain w313 * w314) (\\[i315, i316] -> [i315, 2 * i315 + i316]))))) ; w326 = stranspose @[2, 3, 4, 1, 0] (sreplicate @4 (stranspose @[2, 4, 5, 1, 3, 0] (sgather @[11, 4] (stranspose @[3, 5, 2, 0, 4, 1] (sgather @[7, 3] (stranspose @[4, 6, 0, 3, 5, 2, 1] (sgather @[7, 11, 4, 7] (stranspose @[1, 2, 3, 4, 5, 7, 6, 0] (sreplicate @3 (stranspose @[6, 5, 4, 3, 2, 0, 1] (sreplicateN @[11, 7] (stranspose @[4, 3, 2, 1, 0] w317))))) (\\[i318, i319, i320, i321] -> [i321, i320, i318, i319, kargMax (splainPart w317 !$ [i321, i320, i318, i319])]))) (\\[i322, i323] -> [i322, i323, i322 + i323]))) (\\[i324, i325] -> [i324, i324 + i325])))) ; u327 = ssumN @[4, 3, 4] (w326 * stranspose @[1, 2, 3, 0] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicateN @[7, 11] (tproject2 (tproject2 (tproject1 u1))))) ; m328 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; w336 = sreplicate @5 (sgather @[11, 7, 4, 3, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333] -> [ifH (0.0 <=. negate (splainPart u327 `sindex0` [i330, i331, m328 `sindex0` [i332, i333], i329])) 0 1])) ; w337 = stranspose @[4, 5, 2, 3, 0, 1] (sgather @[3, 2] (stranspose @[1, 3, 2, 0] (sreplicate @5 (stranspose @[2, 1, 0] u327))) (\\[i334, i335] -> [m328 `sindex0` [i334, i335]])) ; w340 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[5, 2] (sfromPlain w336 * w337) (\\[i338, i339] -> [i338, 2 * i338 + i339]))))) ; t346 = str (sreplicate @5 (str (sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w340))) (\\[i341, i342, i343, i344] -> [i341, i342, i343, i344, kargMax (splainPart w340 !$ [i341, i342, i343, i344])])))) (\\i345 -> [i345, i345])))) ; m347 = ssum @60 (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t346) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m350 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i348, i349] -> [ifH (0.0 <=. negate (splainPart m347 `sindex0` [i348, i349])) 0 1]) ; t351 = str (sreplicate @10 (sfromPlain m350 * m347)) in ssum @5 (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * t351) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w302 = stranspose @[1, 2, 0] (sreplicate @4 (stranspose @[3, 1, 2, 0] (sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sreplicate0N @[14, 23] 7.0) (\\[i300, i301] -> [i300 + i301]))) (\\[i298, i299] -> [i298 + i299])))) ; w303 = stranspose @[2, 3, 1, 0] (sreplicate @14 (stranspose @[1, 2, 3, 0] (sreplicate @23 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))) ; t304 = ssumN @[3, 4] (sfromPlain w302 * w303) + stranspose @[2, 0, 1] (sreplicateN @[14, 23] (tproject2 (tproject1 (tproject1 u1)))) ; m305 = str (sreplicate @2 (sconcrete (sreplicate [7] 2) * siota (SNat @7))) + sreplicate @7 (siota (SNat @2)) ; w313 = sreplicate @11 (sgather @[23, 7, 4, 7, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i306, i307, i308, i309, i310] -> [ifH (0.0 <=. negate (splainPart t304 `sindex0` [i308, m305 `sindex0` [i309, i310], i306])) 0 1])) ; w314 = stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 2] (stranspose @[2, 0, 3, 1] (sreplicateN @[7, 11] (str t304))) (\\[i311, i312] -> [m305 `sindex0` [i311, i312]])) ; w317 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[11, 2] (sfromPlain w313 * w314) (\\[i315, i316] -> [i315, 2 * i315 + i316]))))) ; w326 = stranspose @[2, 3, 4, 1, 0] (sreplicate @4 (stranspose @[2, 4, 5, 1, 3, 0] (sgather @[11, 4] (stranspose @[3, 5, 2, 0, 4, 1] (sgather @[7, 3] (stranspose @[4, 6, 0, 3, 5, 2, 1] (sgather @[7, 11, 4, 7] (stranspose @[1, 2, 3, 4, 5, 7, 6, 0] (sreplicate @3 (stranspose @[6, 5, 4, 3, 2, 0, 1] (sreplicateN @[11, 7] (stranspose @[4, 3, 2, 1, 0] w317))))) (\\[i318, i319, i320, i321] -> [i321, i320, i318, i319, kargMax (splainPart w317 !$ [i321, i320, i318, i319])]))) (\\[i322, i323] -> [i322, i323, i322 + i323]))) (\\[i324, i325] -> [i324, i324 + i325])))) ; u327 = ssumN @[4, 3, 4] (w326 * stranspose @[1, 2, 3, 0] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicateN @[7, 11] (tproject2 (tproject2 (tproject1 u1))))) ; m328 = str (sreplicate @2 (sconcrete (sreplicate [3] 2) * siota (SNat @3))) + sreplicate @3 (siota (SNat @2)) ; w336 = sreplicate @5 (sgather @[11, 7, 4, 3, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333] -> [ifH (0.0 <=. negate (splainPart u327 `sindex0` [i330, i331, m328 `sindex0` [i332, i333], i329])) 0 1])) ; w337 = stranspose @[4, 5, 2, 3, 0, 1] (sgather @[3, 2] (stranspose @[1, 3, 2, 0] (sreplicate @5 (stranspose @[2, 1, 0] u327))) (\\[i334, i335] -> [m328 `sindex0` [i334, i335]])) ; w340 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[5, 2] (sfromPlain w336 * w337) (\\[i338, i339] -> [i338, 2 * i338 + i339]))))) ; t346 = str (sreplicate @5 (str (sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w340))) (\\[i341, i342, i343, i344] -> [i341, i342, i343, i344, kargMax (splainPart w340 !$ [i341, i342, i343, i344])])))) (\\i345 -> [i345, i345])))) ; m347 = ssum @60 (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t346) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m350 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i348, i349] -> [ifH (0.0 <=. negate (splainPart m347 `sindex0` [i348, i349])) 0 1]) ; t351 = str (sreplicate @10 (sfromPlain m350 * m347)) ; m353 = sfromPlain m350 * ssum @10 (str (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * sreplicate @5 dret)) in tpair (let u363 = stranspose @[2, 1, 0] (ssum @5 (stranspose @[3, 0, 2, 1] (sscatter @[3, 2] (stranspose @[4, 5, 2, 3, 0, 1] (sfromPlain w336 * sscatter @[5, 2] (stranspose @[3, 5, 0, 1, 2, 4] (ssumN @[1, 1] (stranspose @[4, 5, 0, 1, 2, 3] (sreshape @[7, 4, 3, 5, 1, 1, 2, 2] (stranspose @[4, 3, 2, 1, 0] (ssum @7 (stranspose @[5, 4, 3, 2, 1, 0] (sscatter @[7, 4, 3, 5] (stranspose @[1, 2, 3, 4, 0] (sreshape @[7, 7, 4, 3, 5] (sscatter1 @7 (str (ssum @5 (str (stranspose @[2, 1, 0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * sreplicate @60 m353)))) (\\i354 -> [i354, i354])))) (\\[i355, i356, i357, i358] -> [i355, i356, i357, i358, kargMax (splainPart w340 !$ [i355, i356, i357, i358])]))))))))) (\\[i359, i360] -> [i359, 2 * i359 + i360]))) (\\[i361, i362] -> [m328 `sindex0` [i361, i362]])))) in tpair (let t376 = str (ssumN @[7, 11] (stranspose @[1, 3, 0, 2] (sscatter @[7, 2] (stranspose @[4, 5, 2, 3, 0, 1] (sfromPlain w313 * sscatter @[11, 2] (stranspose @[3, 5, 0, 1, 2, 4] (ssumN @[1, 1] (stranspose @[4, 5, 0, 1, 2, 3] (sreshape @[7, 4, 7, 11, 1, 1, 2, 2] (stranspose @[4, 3, 2, 1, 0] (ssumN @[11, 7] (stranspose @[5, 6, 4, 3, 2, 1, 0] (ssum @3 (stranspose @[7, 0, 1, 2, 3, 4, 6, 5] (sscatter @[7, 11, 4, 7] (stranspose @[2, 6, 5, 3, 0, 4, 1] (sscatter @[7, 3] (stranspose @[3, 5, 2, 0, 4, 1] (sscatter @[11, 4] (stranspose @[5, 3, 0, 4, 1, 2] (ssum @4 (stranspose @[4, 3, 0, 1, 2] (stranspose @[1, 2, 3, 0] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))) * sreplicateN @[4, 3, 4] u363)))) (\\[i364, i365] -> [i364, i364 + i365]))) (\\[i366, i367] -> [i366, i367, i366 + i367]))) (\\[i368, i369, i370, i371] -> [i371, i370, i368, i369, kargMax (splainPart w317 !$ [i371, i370, i368, i369])]))))))))))) (\\[i372, i373] -> [i372, 2 * i372 + i373]))) (\\[i374, i375] -> [m305 `sindex0` [i374, i375]])))) in tpair (str (soneHot (ssum @23 (stranspose @[3, 0, 1, 2] (ssum @14 (stranspose @[3, 2, 0, 1] (sfromPlain w302 * sreplicateN @[3, 4] t376))))) [0])) (ssumN @[14, 23] (stranspose @[1, 2, 0] t376))) (tpair (ssum @11 (stranspose @[4, 0, 1, 2, 3] (ssum @7 (stranspose @[4, 3, 0, 1, 2] (ssum @7 (stranspose @[3, 0, 1, 2] (w326 * sreplicateN @[4, 3, 4] u363))))))) (ssumN @[7, 11] (stranspose @[1, 2, 0] (ssum @7 u363))))) (tpair (tpair (ssum @7 (stranspose @[2, 1, 0] (t346 * sreplicate @60 m353))) (ssum @7 (str m353))) (tpair (ssum @7 (stranspose @[2, 1, 0] (t351 * sreplicate @5 dret))) (ssum @7 (str dret))))"
  printArtifactPretty (simplifyArtifactRev artifactRev)
    @?= "\\dret u1 -> let u302 = sgather @[23, 4] (stranspose @[2, 0, 1] (sgather @[14, 3] (sreplicate0N @[14, 23] 7.0) (\\[i679, i680] -> [i679 + i680]))) (\\[i298, i299] -> [i298 + i299]) ; t304 = ssum @4 (sdot1In (sfromPlain (stranspose @[2, 0, 3, 4, 1] (sreplicate @4 (stranspose @[3, 1, 2, 0] u302)))) (stranspose @[3, 1, 0, 4, 2] (sreplicate @14 (stranspose @[1, 2, 3, 0] (sreplicate @23 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))) + stranspose @[2, 0, 1] (sreplicateN @[14, 23] (tproject2 (tproject1 (tproject1 u1)))) ; w313 = sgather @[23, 7, 4, 7, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i306, i307, i308, i309, i310] -> [ifH (0.0 <=. negate (splainPart t304 `sindex0` [i308, sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i309, i310], i306])) 0 1]) ; w317 = sreshape @[7, 4, 7, 11, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[11, 2] (sfromPlain (sreplicate @11 w313) * stranspose @[4, 5, 2, 3, 0, 1] (sgather @[7, 2] (stranspose @[2, 0, 3, 1] (sreplicateN @[7, 11] (str t304))) (\\[i311, i312] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i311, i312]]))) (\\[i315, i316] -> [i315, 2 * i315 + i316]))))) ; w326 = sgather @[11, 4] (stranspose @[3, 5, 2, 0, 4, 1] (sgather @[7, 3] (stranspose @[4, 6, 0, 3, 5, 2, 1] (sgather @[7, 11, 4, 7] (stranspose @[1, 2, 3, 4, 5, 7, 6, 0] (sreplicate @3 (stranspose @[6, 5, 4, 3, 2, 0, 1] (sreplicateN @[11, 7] (stranspose @[4, 3, 2, 1, 0] w317))))) (\\[i661, i662, i663, i665] -> [i665, i663, i661, i662, kargMax (splainPart w317 !$ [i665, i663, i661, i662])]))) (\\[i669, i671] -> [i669, i671, i669 + i671]))) (\\[i324, i325] -> [i324, i324 + i325]) ; u327 = ssumN @[3, 4] (sdot1In (stranspose @[3, 4, 1, 0, 5, 6, 2] (sreplicate @4 (stranspose @[2, 4, 5, 1, 3, 0] w326))) (stranspose @[2, 3, 0, 4, 5, 6, 1] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2, 0, 1] (sreplicateN @[7, 11] (tproject2 (tproject2 (tproject1 u1))))) ; w336 = sgather @[11, 7, 4, 3, 2] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333] -> [ifH (0.0 <=. negate (splainPart u327 `sindex0` [i330, i331, sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i332, i333], i329])) 0 1]) ; w340 = sreshape @[7, 4, 3, 5, 4] (stranspose @[2, 3, 4, 5, 0, 1] (sreplicateN @[1, 1] (stranspose @[2, 3, 4, 0, 5, 1] (sgather @[5, 2] (sfromPlain (sreplicate @5 w336) * stranspose @[4, 5, 2, 3, 0, 1] (sgather @[3, 2] (stranspose @[1, 3, 2, 0] (sreplicate @5 (stranspose @[2, 1, 0] u327))) (\\[i334, i335] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i334, i335]]))) (\\[i338, i339] -> [i338, 2 * i338 + i339]))))) ; m346 = sgather1 @7 (sreshape @[7, 7, 60] (stranspose @[4, 0, 1, 2, 3] (sgather @[7, 4, 3, 5] (stranspose @[5, 4, 3, 2, 1, 0] (sreplicate @7 (stranspose @[4, 3, 2, 1, 0] w340))) (\\[i341, i342, i343, i344] -> [i341, i342, i343, i344, kargMax (splainPart w340 !$ [i341, i342, i343, i344])])))) (\\i345 -> [i345, i345]) ; m347 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str m346) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m350 = sgather @[5, 7] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i348, i349] -> [ifH (0.0 <=. negate (splainPart m347 `sindex0` [i348, i349])) 0 1]) ; m353 = sfromPlain m350 * smatmul2 (str (tproject1 (tproject2 (tproject2 u1)))) dret in tpair (let u363 = ssum @5 (stranspose @[3, 1, 2, 0] (sscatter @[3, 2] (sfromPlain (stranspose @[4, 5, 2, 3, 0, 1] (sreplicate @5 w336)) * stranspose @[4, 5, 2, 3, 0, 1] (sscatter @[5, 2] (stranspose @[4, 5, 3, 7, 0, 1, 2, 6] (sreshape @[7, 4, 3, 5, 1, 1, 2, 2] (ssum @7 (stranspose @[5, 0, 1, 2, 3, 4] (sscatter @[7, 4, 3, 5] (stranspose @[1, 2, 3, 4, 0] (sreshape @[7, 7, 4, 3, 5] (sscatter1 @7 (smatmul2 (str m353) (tproject1 (tproject1 (tproject2 u1)))) (\\i354 -> [i354, i354])))) (\\[i355, i356, i357, i358] -> [i355, i356, i357, i358, kargMax (splainPart w340 !$ [i355, i356, i357, i358])]))))) !$ [0, 0]) (\\[i359, i360] -> [i359, 2 * i359 + i360]))) (\\[i361, i362] -> [sconcrete (sfromListLinear [3,2] [0,1,2,3,4,5]) `sindex0` [i361, i362]]))) in tpair (let t376 = ssumN @[7, 11] (stranspose @[1, 3, 2, 0] (sscatter @[7, 2] (sfromPlain (stranspose @[4, 5, 2, 3, 0, 1] (sreplicate @11 w313)) * stranspose @[4, 5, 2, 3, 0, 1] (sscatter @[11, 2] (stranspose @[4, 5, 3, 7, 0, 1, 2, 6] (sreshape @[7, 4, 7, 11, 1, 1, 2, 2] (ssumN @[3, 11, 7] (stranspose @[7, 6, 5, 0, 1, 2, 3, 4] (sscatter @[7, 11, 4, 7] (stranspose @[2, 6, 5, 3, 0, 4, 1] (sscatter @[7, 3] (stranspose @[3, 5, 2, 0, 4, 1] (sscatter @[11, 4] (sdot1In (stranspose @[6, 3, 0, 5, 1, 2, 4] (sreplicate @7 (stranspose @[2, 3, 4, 1, 0] (sreplicate @7 (stranspose @[1, 2, 3, 4, 0] (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) (stranspose @[6, 2, 3, 5, 0, 1, 4] (sreplicateN @[4, 3, 4] u363))) (\\[i364, i365] -> [i364, i364 + i365]))) (\\[i366, i367] -> [i366, i367, i366 + i367]))) (\\[i368, i369, i370, i371] -> [i371, i370, i368, i369, kargMax (splainPart w317 !$ [i371, i370, i368, i369])]))))) !$ [0, 0]) (\\[i372, i373] -> [i372, 2 * i372 + i373]))) (\\[i374, i375] -> [sconcrete (sfromListLinear [7,2] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]) `sindex0` [i374, i375]]))) in tpair (str (sreplicate @1 (ssum @23 (sdot1In (sfromPlain (stranspose @[4, 0, 1, 2, 3] (sreplicate @4 (stranspose @[3, 1, 2, 0] u302)))) (stranspose @[4, 2, 0, 1, 3] (sreplicateN @[3, 4] t376)))))) (ssumN @[14, 23] (stranspose @[1, 2, 0] t376))) (tpair (ssumN @[7, 11] (sdot1In (stranspose @[5, 6, 0, 2, 3, 4, 1] (sreplicate @4 (stranspose @[2, 4, 5, 1, 3, 0] w326))) (stranspose @[5, 6, 4, 0, 1, 2, 3] (sreplicateN @[4, 3, 4] u363)))) (ssumN @[7, 7, 11] (stranspose @[0, 2, 3, 1] u363)))) (tpair (tpair (smatmul2 m353 m346) (ssum @7 (str m353))) (tpair (smatmul2 dret (sfromPlain (str m350) * str m347)) (ssum @7 (str dret))))"
