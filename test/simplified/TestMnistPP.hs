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
import Data.Array.Nested.Internal.Shape

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.Ops (treplicate)

import MnistCnnRanked2 qualified
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
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate @4 (sfromR dret !$ [9]) ; v8 = sreplicate @4 (sfromR dret !$ [8]) ; v9 = sreplicate @4 (sfromR dret !$ [7]) ; v10 = sreplicate @4 (sfromR dret !$ [6]) ; v11 = sreplicate @4 (sfromR dret !$ [5]) ; v12 = sreplicate @4 (sfromR dret !$ [4]) ; v13 = sreplicate @4 (sfromR dret !$ [3]) ; v14 = sreplicate @4 (sfromR dret !$ [2]) ; v15 = sreplicate @4 (sfromR dret !$ [1]) ; v16 = sreplicate @4 (sfromR dret !$ [0]) ; v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7)))))))) ; v18 = sreplicate @3 (v17 !$ [3]) ; v19 = sreplicate @3 (v17 !$ [2]) ; v20 = sreplicate @3 (v17 !$ [1]) ; v21 = sreplicate @3 (v17 !$ [0]) ; v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v22 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v22 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v22 !$ [2])) Z0))) v22) (tpair (tpair (v4 * v21) (tpair (v4 * v20) (tpair (v4 * v19) (tpair (v4 * v18) Z0)))) v17)) (tpair (tpair (v5 * v16) (tpair (v5 * v15) (tpair (v5 * v14) (tpair (v5 * v13) (tpair (v5 * v12) (tpair (v5 * v11) (tpair (v5 * v10) (tpair (v5 * v9) (tpair (v5 * v8) (tpair (v5 * v7) Z0)))))))))) (sfromR dret))"
  printArtifactPrimalPretty artifactRev
    @?= "\\v1 -> let v4 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) in rfromS (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v5), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v5)]) + tproject2 (tproject2 v1))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) (sreplicate @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) (sreplicate @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) (sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate @4 (sfromR dret !$ [9]) ; v8 = sreplicate @4 (sfromR dret !$ [8]) ; v9 = sreplicate @4 (sfromR dret !$ [7]) ; v10 = sreplicate @4 (sfromR dret !$ [6]) ; v11 = sreplicate @4 (sfromR dret !$ [5]) ; v12 = sreplicate @4 (sfromR dret !$ [4]) ; v13 = sreplicate @4 (sfromR dret !$ [3]) ; v14 = sreplicate @4 (sfromR dret !$ [2]) ; v15 = sreplicate @4 (sfromR dret !$ [1]) ; v16 = sreplicate @4 (sfromR dret !$ [0]) ; v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7)))))))) ; v18 = sreplicate @3 (v17 !$ [3]) ; v19 = sreplicate @3 (v17 !$ [2]) ; v20 = sreplicate @3 (v17 !$ [1]) ; v21 = sreplicate @3 (v17 !$ [0]) ; v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v22 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v22 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v22 !$ [2])) Z0))) v22) (tpair (tpair (v4 * v21) (tpair (v4 * v20) (tpair (v4 * v19) (tpair (v4 * v18) Z0)))) v17)) (tpair (tpair (v5 * v16) (tpair (v5 * v15) (tpair (v5 * v14) (tpair (v5 * v13) (tpair (v5 * v12) (tpair (v5 * v11) (tpair (v5 * v10) (tpair (v5 * v9) (tpair (v5 * v8) (tpair (v5 * v7) Z0)))))))))) (sfromR dret))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) (sreplicate @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) (sreplicate @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) (sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v5, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v5]) + tproject2 (tproject2 v1))"

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
  printArtifactPretty artifactRevnonLin
    @?= "\\dret v1 -> let v9 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + v10 ; v12 = recip v11 ; v13 = sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + negate v12 ; v14 = v12 * v13 ; v15 = scast (sconcrete (sfromListLinear [3] [0.0,0.0,0.0]) + v12) ; v16 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v15), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v15)])) + tproject2 (tproject2 (tproject1 v1)) ; v17 = exp (negate v16) ; v18 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + v17 ; v19 = recip v18 ; v20 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + negate v19 ; v21 = v19 * v20 ; v22 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v19 ; v23 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v22), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v22)]) + tproject2 (tproject2 v1)) ; x24 = ssum @10 v23 ; v25 = sreplicate @10 (recip x24) ; v27 = v23 * (sreplicate @10 (negate (recip (x24 * x24)) * ssum @10 (v23 * sfromR dret)) + v25 * sfromR dret) ; v28 = sreplicate @4 (v27 !$ [9]) ; v29 = sreplicate @4 (v27 !$ [8]) ; v30 = sreplicate @4 (v27 !$ [7]) ; v31 = sreplicate @4 (v27 !$ [6]) ; v32 = sreplicate @4 (v27 !$ [5]) ; v33 = sreplicate @4 (v27 !$ [4]) ; v34 = sreplicate @4 (v27 !$ [3]) ; v35 = sreplicate @4 (v27 !$ [2]) ; v36 = sreplicate @4 (v27 !$ [1]) ; v37 = sreplicate @4 (v27 !$ [0]) ; v38 = v21 * (tproject1 (tproject1 (tproject2 v1)) * v37 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v36 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v35 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v29 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v28))))))))) ; v39 = scast v38 ; v40 = sreplicate @3 (v39 !$ [3]) ; v41 = sreplicate @3 (v39 !$ [2]) ; v42 = sreplicate @3 (v39 !$ [1]) ; v43 = sreplicate @3 (v39 !$ [0]) ; v44 = v14 * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v43 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v42 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v41 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v40))) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v44 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v44 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v44 !$ [2])) Z0))) v44) (tpair (tpair (v15 * v43) (tpair (v15 * v42) (tpair (v15 * v41) (tpair (v15 * v40) Z0)))) v38)) (tpair (tpair (v22 * v37) (tpair (v22 * v36) (tpair (v22 * v35) (tpair (v22 * v34) (tpair (v22 * v33) (tpair (v22 * v32) (tpair (v22 * v31) (tpair (v22 * v30) (tpair (v22 * v29) (tpair (v22 * v28) Z0)))))))))) v27)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\v1 -> let v9 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + v10 ; v12 = recip v11 ; v15 = scast (sconcrete (sfromListLinear [3] [0.0,0.0,0.0]) + v12) ; v16 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v15), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v15)])) + tproject2 (tproject2 (tproject1 v1)) ; v17 = exp (negate v16) ; v18 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + v17 ; v19 = recip v18 ; v22 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v19 ; v23 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v22), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v22)]) + tproject2 (tproject2 v1)) ; x24 = ssum @10 v23 ; v25 = sreplicate @10 (recip x24) in rfromS (v25 * v23)"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret v1 -> let v12 = recip (sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + exp (negate (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) (sreplicate @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) (sreplicate @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) (sreplicate @784 (sscalar 7.0))])) + negate (tproject2 (tproject1 (tproject1 v1))))) ; v15 = scast (sconcrete (sfromListLinear [3] [0.0,0.0,0.0]) + v12) ; v19 = recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v15, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v15]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v22 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v19 ; v23 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v22, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v22]) + tproject2 (tproject2 v1)) ; x24 = ssum0 v23 ; v27 = v23 * (sreplicate @10 (negate (recip (x24 * x24)) * sdot0 v23 (sfromR dret)) + sreplicate @10 (recip x24) * sfromR dret) ; v28 = sreplicate @4 (v27 !$ [9]) ; v29 = sreplicate @4 (v27 !$ [8]) ; v30 = sreplicate @4 (v27 !$ [7]) ; v31 = sreplicate @4 (v27 !$ [6]) ; v32 = sreplicate @4 (v27 !$ [5]) ; v33 = sreplicate @4 (v27 !$ [4]) ; v34 = sreplicate @4 (v27 !$ [3]) ; v35 = sreplicate @4 (v27 !$ [2]) ; v36 = sreplicate @4 (v27 !$ [1]) ; v37 = sreplicate @4 (v27 !$ [0]) ; v38 = (v19 * (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + negate v19)) * (tproject1 (tproject1 (tproject2 v1)) * v37 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v36 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v35 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v29 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v28))))))))) ; v39 = scast v38 ; v40 = sreplicate @3 (v39 !$ [3]) ; v41 = sreplicate @3 (v39 !$ [2]) ; v42 = sreplicate @3 (v39 !$ [1]) ; v43 = sreplicate @3 (v39 !$ [0]) ; v44 = (v12 * (sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + negate v12)) * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v43 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v42 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v41 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v40))) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v44 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v44 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0) * sreplicate @784 (v44 !$ [2])) Z0))) v44) (tpair (tpair (v15 * v43) (tpair (v15 * v42) (tpair (v15 * v41) (tpair (v15 * v40) Z0)))) v38)) (tpair (tpair (v22 * v37) (tpair (v22 * v36) (tpair (v22 * v35) (tpair (v22 * v34) (tpair (v22 * v33) (tpair (v22 * v32) (tpair (v22 * v31) (tpair (v22 * v30) (tpair (v22 * v29) (tpair (v22 * v28) Z0)))))))))) v27)"
  printArtifactPrimalPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\v1 -> rfromS (let v15 = scast (sconcrete (sfromListLinear [3] [0.0,0.0,0.0]) + recip (sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + exp (negate (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) (sreplicate @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) (sreplicate @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) (sreplicate @784 (sscalar 7.0))])) + negate (tproject2 (tproject1 (tproject1 v1)))))) ; v22 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v15, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v15]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v23 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v22, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v22]) + tproject2 (tproject2 v1)) in sreplicate @10 (recip (ssum0 v23)) * v23)"

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
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m5 = str (sreplicate @5 (scast (ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = str (sreplicate @2 (scast (ssum @4 (m5 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v8 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m9 = sreplicate @4 (scast v8) ; v10 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m9))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * sreplicate @3 v10))) (rfromS v10)) (tpair (rfromS (str (m5 * m9))) (rfromS v8))) (tpair (rfromS (str (m6 * sreplicate @5 (sfromR dret)))) (rfromS (sfromR dret)))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let m5 = str (sreplicate @5 (scast (ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = str (sreplicate @2 (scast (ssum @4 (m5 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in rfromS (ssum @5 (m6 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1)))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let m5 = str (sreplicate @5 (scast (ssdot1In (sreplicate @4 (sreplicate @3 (sscalar 7.0))) (sfromR (tproject1 (tproject1 (tproject1 m1)))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v8 = ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 (sfromR dret)) ; m9 = sreplicate @4 (scast v8) ; v10 = scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) m9) in tpair (tpair (tpair (sreplicate @4 (sreplicate @3 (sscalar 7.0)) * str (sreplicate @3 v10)) v10) (tpair (str m5 * str m9) v8)) (tpair (sreplicate @2 (scast (ssdot1In (str m5) (sfromR (tproject1 (tproject2 (tproject1 m1))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @5 (sfromR dret))) dret))"
  printArtifactSimple (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (tlet (str (sreplicate @5 (scast (ssdot1In (sreplicate @4 (sreplicate @3 (sscalar 7.0))) (sfromR (tproject1 (tproject1 (tproject1 m1)))) + sfromR (tproject2 (tproject1 (tproject1 m1))))))) (\\m5 -> tlet (ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 (sfromR dret))) (\\v8 -> tlet (sreplicate @4 (scast v8)) (\\m9 -> tlet (scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) m9)) (\\v10 -> tpair (tpair (tpair (sreplicate @4 (sreplicate @3 (sscalar 7.0)) * str (sreplicate @3 v10)) v10) (tpair (str m5 * str m9) v8)) (tpair (sreplicate @2 (scast (ssdot1In (str m5) (sfromR (tproject1 (tproject2 (tproject1 m1))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @5 (sfromR dret))) dret))))))"

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
    @?= "\\dummy -> rfromS (tlet (exp (ssum @5 (str (sreplicate @2 (tlet (ssum @4 (str (sreplicate @5 (tlet (tfromPrimal (STKS [4] STKScalar) (ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (scast (sconcrete (sfromListLinear [4,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0])))) + scast (sconcrete (sfromListLinear [4] [1.0,2.0,3.0,4.0])))) (\\v3 -> ttletPrimal (recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (sfromR (tprimalPart (rfromS v3)))))) (\\v4 -> tfromPrimal (STKS [4] STKScalar) v4 + sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [4] STKScalar) (v4 * (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + negate v4)) * sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v3))))))))))) * tfromPrimal (STKS [4,5] STKScalar) (sconcrete (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0]))) + tfromPrimal (STKS [5] STKScalar) (scast (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v6 -> ttletPrimal (recip (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + exp (negate (sfromR (tprimalPart (rfromS v6)))))) (\\v7 -> tfromPrimal (STKS [5] STKScalar) v7 + sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [5] STKScalar) (v7 * (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + negate v7)) * sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v6))))))))))) * tfromPrimal (STKS [5,2] STKScalar) (str (scast (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))))) + tfromPrimal (STKS [2] STKScalar) (scast (sconcrete (sfromListLinear [2] [1.0,2.0]))))) (\\v9 -> sreplicate @2 (recip (ssum @2 v9)) * v9))"
  "\\dummy" ++ " -> " ++ printAstSimple (simplifyInlineContract ast3)
    @?= "\\dummy -> rfromS (tlet (exp (ssdot1In (sreplicate @2 (tlet (ssdot1In (sreplicate @5 (tlet (tfromPrimal (STKS [4] STKScalar) (sconcrete (sfromListLinear [4] [1.0,2.0,3.0,4.0]) + ssdot1In (sreplicate @4 (sreplicate @3 (sscalar 7.0))) (sconcrete (sfromListLinear [4,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0])))) (\\v3 -> ttletPrimal (recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (tprimalPart v3)))) (\\v4 -> tfromPrimal (STKS [4] STKScalar) v4 + tfromDual (tdualPart (STKS [4] STKScalar) (tfromPrimal (STKS [4] STKScalar) (v4 * (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + negate v4)) * tfromDual (tdualPart (STKS [4] STKScalar) v3))))))) (tfromPrimal (STKS [5,4] STKScalar) (sconcrete (sfromListLinear [5,4] [1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0]))) + tfromPrimal (STKS [5] STKScalar) (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0]))) (\\v6 -> ttletPrimal (recip (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + exp (negate (tprimalPart v6)))) (\\v7 -> tfromPrimal (STKS [5] STKScalar) v7 + tfromDual (tdualPart (STKS [5] STKScalar) (tfromPrimal (STKS [5] STKScalar) (v7 * (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + negate v7)) * tfromDual (tdualPart (STKS [5] STKScalar) v6))))))) (tfromPrimal (STKS [2,5] STKScalar) (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))) + tfromPrimal (STKS [2] STKScalar) (sconcrete (sfromListLinear [2] [1.0,2.0])))) (\\v9 -> sreplicate @2 (recip (ssum0 v9)) * v9))"

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
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + v11 ; v13 = recip v12 ; v14 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + negate v13 ; v15 = v13 * v14 ; m16 = str (sreplicate @5 (scast (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v13))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + v18 ; v20 = recip v19 ; v21 = sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + negate v20 ; v22 = v20 * v21 ; m23 = str (sreplicate @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + v20)) ; v24 = exp (ssum @5 (m23 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v28 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * ssum @2 (v24 * sfromR dret)) + v26 * sfromR dret) ; m29 = sreplicate @5 v28 ; v30 = v22 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * m29)) ; m31 = sreplicate @4 (scast v30) ; v32 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m31))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * sreplicate @3 v32))) (rfromS v32)) (tpair (rfromS (str (m16 * m31))) (rfromS v30))) (tpair (rfromS (str (m23 * m29))) (rfromS v28))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + v11 ; v13 = recip v12 ; m16 = str (sreplicate @5 (scast (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v13))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + v18 ; v20 = recip v19 ; m23 = str (sreplicate @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + v20)) ; v24 = exp (ssum @5 (m23 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) in rfromS (v26 * v24)"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v13 = recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (ssdot1In (sreplicate @4 (sreplicate @3 (sscalar 7.0))) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m16 = str (sreplicate @5 (scast (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v13))) ; v20 = recip (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + exp (negate (scast (ssdot1In (str m16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m23 = str (sreplicate @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + v20)) ; v24 = exp (ssdot1In (str m23) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum0 v24 ; v28 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * sdot0 v24 (sfromR dret)) + sreplicate @2 (recip x25) * sfromR dret) ; v30 = (v20 * (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + negate v20)) * ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v28) ; m31 = sreplicate @4 (scast v30) ; v32 = (v13 * (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + negate v13)) * scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) m31) in tpair (tpair (tpair (sreplicate @4 (sreplicate @3 (sscalar 7.0)) * str (sreplicate @3 v32)) v32) (tpair (str m16 * str m31) v30)) (tpair (str m23 * str (sreplicate @5 v28)) v28))"
  printArtifactPrimalPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\m1 -> rfromS (let v24 = exp (ssdot1In (sreplicate @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + recip (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + exp (negate (scast (ssdot1In (sreplicate @5 (scast (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (ssdot1In (sreplicate @4 (sreplicate @3 (sscalar 7.0))) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in sreplicate @2 (recip (ssum0 v24)) * v24)"

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
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + v11 ; v13 = recip v12 ; v14 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + negate v13 ; v15 = v13 * v14 ; m16 = str (sreplicate @5 (scast (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v13))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + v18 ; v20 = recip v19 ; v21 = sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + negate v20 ; v22 = v20 * v21 ; m23 = str (sreplicate @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + v20)) ; v24 = exp (ssum @5 (m23 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v27 = v26 * v24 ; v30 = recip v27 * (sreplicate @2 (sscalar 8.0) * sreplicate @2 (sscalar (-1.0) * sfromK dret)) ; v31 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * ssum @2 (v24 * v30)) + v26 * v30) ; m32 = sreplicate @5 v31 ; v33 = v22 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * m32)) ; m34 = sreplicate @4 (scast v33) ; v35 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m34))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * sreplicate @3 v35))) (rfromS v35)) (tpair (rfromS (str (m16 * m34))) (rfromS v33))) (tpair (rfromS (str (m23 * m32))) (rfromS v31))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + v11 ; v13 = recip v12 ; m16 = str (sreplicate @5 (scast (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v13))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + v18 ; v20 = recip v19 ; m23 = str (sreplicate @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + v20)) ; v24 = exp (ssum @5 (m23 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v27 = v26 * v24 ; v28 = log v27 in kfromS (negate (ssum @2 (v28 * sreplicate @2 (sscalar 8.0))))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v13 = recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (ssdot1In (sreplicate @4 (sreplicate @3 (sscalar 7.0))) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m16 = str (sreplicate @5 (scast (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v13))) ; v20 = recip (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + exp (negate (scast (ssdot1In (str m16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m23 = str (sreplicate @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + v20)) ; v24 = exp (ssdot1In (str m23) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum0 v24 ; v26 = sreplicate @2 (recip x25) ; v30 = recip (v26 * v24) * (sreplicate @2 (sscalar 8.0) * sreplicate @2 (sscalar (-1.0) * sfromK dret)) ; v31 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * sdot0 v24 v30) + v26 * v30) ; v33 = (v20 * (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + negate v20)) * ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v31) ; m34 = sreplicate @4 (scast v33) ; v35 = (v13 * (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + negate v13)) * scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) m34) in tpair (tpair (tpair (sreplicate @4 (sreplicate @3 (sscalar 7.0)) * str (sreplicate @3 v35)) v35) (tpair (str m16 * str m34) v33)) (tpair (str m23 * str (sreplicate @5 v31)) v31))"
  printArtifactPrimalPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\m1 -> kfromS (let v24 = exp (ssdot1In (sreplicate @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + recip (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0]) + exp (negate (scast (ssdot1In (sreplicate @5 (scast (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (ssdot1In (sreplicate @4 (sreplicate @3 (sscalar 7.0))) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in negate (sdot0 (log (sreplicate @2 (recip (ssum0 v24)) * v24)) (sreplicate @2 (sscalar 8.0))))"

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
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m2 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) !$ [0] ; m3 = sreplicate @1 (sreplicate @1 (sreplicate @1 (sscalar 7.0))) !$ [0] ; m4 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) !$ [0] ; m5 = str (sreplicate @1 (sslice (SNat @0) (SNat @1) (sconcrete (sfromListLinear [2,1] [0.0,0.0])))) !$ [0] ; m6 = tanh ((m2 * m3 + m4 * m5) + str (sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m7 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) !$ [0] ; m8 = str (sreplicate @1 m6) !$ [0] ; m9 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) !$ [0] ; m10 = str (sreplicate @1 (sslice (SNat @1) (SNat @1) (sconcrete (sfromListLinear [2,1] [0.0,0.0])))) !$ [0] ; m11 = tanh ((m7 * m8 + m9 * m10) + str (sreplicate @1 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m12 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject1 (tproject2 m1)))) !$ [0] ; m13 = str (sreplicate @10 m11) !$ [0] ; m15 = (sconcrete (sfromListLinear [1,1] [1.0]) + negate m11 * m11) * ssum @10 (str (soneHot (m12 * sfromR dret) [0])) ; m16 = (sconcrete (sfromListLinear [1,1] [1.0]) + negate m6 * m6) * ssum @1 (str (soneHot (m7 * m15) [0])) in tpair (tpair (tpair (tpair (rfromS (ssum @1 (stranspose @[2,1,0] (soneHot (m3 * m16) [0])))) (rfromS (ssum @1 (stranspose @[2,1,0] (soneHot (m5 * m16) [0]))))) (rfromS (ssum @1 (str m16)))) (tpair (tpair (rfromS (ssum @1 (stranspose @[2,1,0] (soneHot (m8 * m15) [0])))) (rfromS (ssum @1 (stranspose @[2,1,0] (soneHot (m10 * m15) [0]))))) (rfromS (ssum @1 (str m15))))) (tpair (rfromS (ssum @1 (stranspose @[2,1,0] (soneHot (m13 * sfromR dret) [0])))) (rfromS (ssum @1 (str (sfromR dret)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let m2 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) !$ [0] ; m3 = sreplicate @1 (sreplicate @1 (sreplicate @1 (sscalar 7.0))) !$ [0] ; m4 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) !$ [0] ; m5 = str (sreplicate @1 (sslice (SNat @0) (SNat @1) (sconcrete (sfromListLinear [2,1] [0.0,0.0])))) !$ [0] ; m6 = tanh ((m2 * m3 + m4 * m5) + str (sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m7 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) !$ [0] ; m8 = str (sreplicate @1 m6) !$ [0] ; m9 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) !$ [0] ; m10 = str (sreplicate @1 (sslice (SNat @1) (SNat @1) (sconcrete (sfromListLinear [2,1] [0.0,0.0])))) !$ [0] ; m11 = tanh ((m7 * m8 + m9 * m10) + str (sreplicate @1 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m12 = stranspose @[2,1,0] (sreplicate @1 (sfromR (tproject1 (tproject2 m1)))) !$ [0] ; m13 = str (sreplicate @10 m11) !$ [0] in rfromS (m12 * m13 + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar)) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let m6 = tanh ((sgather (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (\\[i61, i62] -> [i61, 0]) * sreplicate @1 (sreplicate @1 (sscalar 7.0)) + sgather (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (\\[i58, i59] -> [i58, 0]) * sreplicate @1 (sconcrete (sfromListLinear [1] [0.0]))) + str (sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m7 = sgather (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (\\[i53, i54] -> [i53, 0]) ; m8 = sreplicate @1 (m6 !$ [0]) ; m11 = tanh ((m7 * m8 + sgather (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (\\[i48, i49] -> [i48, 0]) * sreplicate @1 (sconcrete (sfromListLinear [1] [0.0]))) + str (sreplicate @1 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m15 = (sconcrete (sfromListLinear [1,1] [1.0]) + negate m11 * m11) * ssum @10 (str (sreplicate @1 (sgather (sfromR (tproject1 (tproject2 m1))) (\\[i43, i44] -> [i43, 0]) * sfromR dret))) ; m16 = (sconcrete (sfromListLinear [1,1] [1.0]) + negate m6 * m6) * sreplicate @1 (m7 !$ [0] * m15 !$ [0]) in tpair (tpair (tpair (tpair (sgather (sreplicate @1 (sreplicate @1 (sscalar 7.0)) * m16) (\\[i36, i37] -> [i36, 0])) (sgather (sreplicate @1 (sconcrete (sfromListLinear [1] [0.0])) * m16) (\\[i33, i34] -> [i33, 0]))) (sgather m16 (\\[i31] -> [i31, 0]))) (tpair (tpair (sgather (m8 * m15) (\\[i28, i29] -> [i28, 0])) (sgather (sreplicate @1 (sconcrete (sfromListLinear [1] [0.0])) * m15) (\\[i25, i26] -> [i25, 0]))) (sgather m15 (\\[i23] -> [i23, 0])))) (tpair (sgather (sreplicate @10 (m11 !$ [0]) * sfromR dret) (\\[i20, i21] -> [i20, 0])) (sgather (sfromR dret) (\\[i18] -> [i18, 0]))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (sgather (sfromR (tproject1 (tproject2 m1))) (\\[i66, i67] -> [i66, 0]) * sreplicate @10 (tanh ((sreplicate @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0]) * tanh ((sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) * sreplicate @1 (sscalar 7.0) + sconcrete (sfromListLinear [1] [0.0]) * sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0])) + sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0])) + sconcrete (sfromListLinear [1] [0.0]) * sreplicate @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0])) + sreplicate @1 (sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]))) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"

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
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m3 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @0) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @0) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t5 = str (sreplicate @2 m4) ; m6 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t5) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @2) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m7 = sappend m3 m6 ; t8 = str (sreplicate @2 (sslice (SNat @0) (SNat @2) m7)) ; m9 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t8)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t10 = str (sreplicate @2 m9) ; t11 = str (sreplicate @2 (sslice (SNat @2) (SNat @2) m7)) ; m12 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t10) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t11)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; t13 = str (sreplicate @10 m12) ; m15 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m12 * m12) * ssum @10 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @2 (sfromR dret))) ; t16 = sreplicate @2 m15 ; t17 = sreplicate @2 m15 ; m18 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m9 * m9) * ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t17)) ; t19 = sreplicate @2 m18 ; m20 = sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t19))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + sappend (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t16))) (sconcrete (sfromListLinear [0,2] []))) ; m21 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m6 * m6) * sslice (SNat @2) (SNat @2) m20 ; t22 = sreplicate @2 m21 ; m23 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m4 * m4) * ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t22)) ; m24 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m3 * m3) * sslice (SNat @0) (SNat @2) m20 in tpair (tpair (tpair (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0))) * sreplicate @2 m24)) + (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0))) * sreplicate @2 m23)) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0))) * sreplicate @2 m18))))) (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (sslice (SNat @0) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) * sreplicate @2 m24)) + (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (sslice (SNat @0) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) * sreplicate @2 m23)) + ssum @2 (stranspose @[2,1,0] (t8 * t19)))))) (rfromS (ssum @2 (str m24) + (ssum @2 (str m23) + ssum @2 (str m18))))) (tpair (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (t5 * t22)) + ssum @2 (stranspose @[2,1,0] (t10 * t17)))) (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (sslice (SNat @2) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) * sreplicate @2 m21)) + ssum @2 (stranspose @[2,1,0] (t11 * t16))))) (rfromS (ssum @2 (str m21) + ssum @2 (str m15))))) (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (t13 * sreplicate @2 (sfromR dret))))) (rfromS (ssum @2 (str (sfromR dret)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let m3 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @0) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @0) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t5 = str (sreplicate @2 m4) ; m6 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t5) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @2) (SNat @2) (sconcrete (sfromListLinear [4,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m7 = sappend m3 m6 ; t8 = str (sreplicate @2 (sslice (SNat @0) (SNat @2) m7)) ; m9 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t8)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t10 = str (sreplicate @2 m9) ; t11 = str (sreplicate @2 (sslice (SNat @2) (SNat @2) m7)) ; m12 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t10) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t11)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; t13 = str (sreplicate @10 m12) in rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * t13) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar)) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let m3 = tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m4 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m7 = sappend m3 m6 ; m9 = tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice (SNat @0) (SNat @2) m7)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m12 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m9 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m7)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m15 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m12 * m12) * smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR dret) ; m18 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m9 * m9) * smatmul2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m15 ; m20 = sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) m18) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) + sappend (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) m15) ; m21 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m6 * m6) * sslice (SNat @2) (SNat @2) m20 ; m23 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m4 * m4) * smatmul2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m21 ; m24 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m3 * m3) * sslice (SNat @0) (SNat @2) m20 in tpair (tpair (tpair (tpair (ssdot1In (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) (str (sreplicate @2 m24)) + (ssdot1In (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) (str (sreplicate @2 m23)) + ssdot1In (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) (str (sreplicate @2 m18)))) (smatmul2 m24 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) + (smatmul2 m23 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) + smatmul2 m18 (str (sslice (SNat @0) (SNat @2) m7))))) (ssum @2 (str m24) + (ssum @2 (str m23) + ssum @2 (str m18)))) (tpair (tpair (smatmul2 m21 (str m4) + smatmul2 m15 (str m9)) (smatmul2 m21 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) + smatmul2 m15 (str (sslice (SNat @2) (SNat @2) m7)))) (ssum @2 (str m21) + ssum @2 (str m15)))) (tpair (smatmul2 (sfromR dret) (str m12)) (ssum @2 (str (sfromR dret)))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (let m7 = sappend (tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice (SNat @0) (SNat @2) m7)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m7)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"

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
                   (simplifyInline @(TKR 2 Double) afcnn1)
    @?= afcnn2 (valsInitRNNOPP 2 sizeMnistHeightI)
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 2 Double) afcnn1)
    @?= afcnn2 (valsInitRNNOPP 2 sizeMnistHeightI)


-- * CNNR tests

tensorMnistCNNRPP :: TestTree
tensorMnistCNNRPP = testGroup "Ast tests for CNNR MNIST"
  [ testCase "CNNO Ast" testCNNOAst
  , testCase "CNNO Ast 2" testCNNOAst2
  ]

testCNNOAst :: Assertion
testCNNOAst = do
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
                   (simplifyInline @(TKR 2 Double) afcnn1)
    @?= afcnn2 valsInit
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 2 Double) afcnn1)
    @?= afcnn2 valsInit

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
                   (simplifyInline @(TKR 2 Double) afcnn1)
    @?= afcnn2 valsInit
  interpretAstFull @Concrete env
                   (simplifyInlineContract @(TKR 2 Double) afcnn1)
    @?= afcnn2 valsInit
