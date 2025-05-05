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
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v5, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v5]) + tproject2 (tproject2 v1))"
  printArtifactPrimalPretty artifactRev
    @?= "\\v1 -> let v4 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) in rfromS (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v5), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v5), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v5)]) + tproject2 (tproject2 v1))"
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate @4 (sfromR dret !$ [9]) ; v8 = sreplicate @4 (sfromR dret !$ [8]) ; v9 = sreplicate @4 (sfromR dret !$ [7]) ; v10 = sreplicate @4 (sfromR dret !$ [6]) ; v11 = sreplicate @4 (sfromR dret !$ [5]) ; v12 = sreplicate @4 (sfromR dret !$ [4]) ; v13 = sreplicate @4 (sfromR dret !$ [3]) ; v14 = sreplicate @4 (sfromR dret !$ [2]) ; v15 = sreplicate @4 (sfromR dret !$ [1]) ; v16 = sreplicate @4 (sfromR dret !$ [0]) ; v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7)))))))) ; v18 = sreplicate @3 (v17 !$ [3]) ; v19 = sreplicate @3 (v17 !$ [2]) ; v20 = sreplicate @3 (v17 !$ [1]) ; v21 = sreplicate @3 (v17 !$ [0]) ; v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18)) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v22 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v22 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v22 !$ [2])) Z0))) v22) (tpair (tpair (v4 * v21) (tpair (v4 * v20) (tpair (v4 * v19) (tpair (v4 * v18) Z0)))) v17)) (tpair (tpair (v5 * v16) (tpair (v5 * v15) (tpair (v5 * v14) (tpair (v5 * v13) (tpair (v5 * v12) (tpair (v5 * v11) (tpair (v5 * v10) (tpair (v5 * v9) (tpair (v5 * v8) (tpair (v5 * v7) Z0)))))))))) (sfromR dret))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> let v4 = sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) ; x7 = sfromR dret !$ [9] ; x8 = sfromR dret !$ [8] ; x9 = sfromR dret !$ [7] ; x10 = sfromR dret !$ [6] ; x11 = sfromR dret !$ [5] ; x12 = sfromR dret !$ [4] ; x13 = sfromR dret !$ [3] ; x14 = sfromR dret !$ [2] ; x15 = sfromR dret !$ [1] ; x16 = sfromR dret !$ [0] ; v17 = tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x16 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x15 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x14 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x13 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x12 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x11 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x10 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x9 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x7)))))))) ; x18 = v17 !$ [3] ; x19 = v17 !$ [2] ; x20 = v17 !$ [1] ; x21 = v17 !$ [0] ; v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x21 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x20 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x18)) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v22 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v22 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v22 !$ [2])) Z0))) v22) (tpair (tpair (v4 * sreplicate @3 x21) (tpair (v4 * sreplicate @3 x20) (tpair (v4 * sreplicate @3 x19) (tpair (v4 * sreplicate @3 x18) Z0)))) v17)) (tpair (tpair (v5 * sreplicate @4 x16) (tpair (v5 * sreplicate @4 x15) (tpair (v5 * sreplicate @4 x14) (tpair (v5 * sreplicate @4 x13) (tpair (v5 * sreplicate @4 x12) (tpair (v5 * sreplicate @4 x11) (tpair (v5 * sreplicate @4 x10) (tpair (v5 * sreplicate @4 x9) (tpair (v5 * sreplicate @4 x8) (tpair (v5 * sreplicate @4 x7) Z0)))))))))) (sfromR dret))"

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
    @?= "\\v1 -> rfromS (let v15 = scast (sconcrete (sreplicate [3] 0.0) + recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1)))))) ; v22 = sconcrete (sreplicate [4] 0.0) + recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v15, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v15]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v23 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v22, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v22]) + tproject2 (tproject2 v1)) in sreplicate @10 (recip (ssum0 v23)) * v23)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\v1 -> let v9 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = sconcrete (sreplicate [3] 1.0) + v10 ; v12 = recip v11 ; v15 = scast (sconcrete (sreplicate [3] 0.0) + v12) ; v16 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v15), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v15)])) + tproject2 (tproject2 (tproject1 v1)) ; v17 = exp (negate v16) ; v18 = sconcrete (sreplicate [4] 1.0) + v17 ; v19 = recip v18 ; v22 = sconcrete (sreplicate [4] 0.0) + v19 ; v23 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v22), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v22)]) + tproject2 (tproject2 v1)) ; x24 = ssum @10 v23 ; v25 = sreplicate @10 (recip x24) in rfromS (v25 * v23)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret v1 -> let v9 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = sconcrete (sreplicate [3] 1.0) + v10 ; v12 = recip v11 ; v13 = sconcrete (sreplicate [3] 1.0) + negate v12 ; v14 = v12 * v13 ; v15 = scast (sconcrete (sreplicate [3] 0.0) + v12) ; v16 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v15), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v15)])) + tproject2 (tproject2 (tproject1 v1)) ; v17 = exp (negate v16) ; v18 = sconcrete (sreplicate [4] 1.0) + v17 ; v19 = recip v18 ; v20 = sconcrete (sreplicate [4] 1.0) + negate v19 ; v21 = v19 * v20 ; v22 = sconcrete (sreplicate [4] 0.0) + v19 ; v23 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v22), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v22), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v22)]) + tproject2 (tproject2 v1)) ; x24 = ssum @10 v23 ; v25 = sreplicate @10 (recip x24) ; v27 = v23 * (sreplicate @10 (negate (recip (x24 * x24)) * ssum @10 (v23 * sfromR dret)) + v25 * sfromR dret) ; v28 = sreplicate @4 (v27 !$ [9]) ; v29 = sreplicate @4 (v27 !$ [8]) ; v30 = sreplicate @4 (v27 !$ [7]) ; v31 = sreplicate @4 (v27 !$ [6]) ; v32 = sreplicate @4 (v27 !$ [5]) ; v33 = sreplicate @4 (v27 !$ [4]) ; v34 = sreplicate @4 (v27 !$ [3]) ; v35 = sreplicate @4 (v27 !$ [2]) ; v36 = sreplicate @4 (v27 !$ [1]) ; v37 = sreplicate @4 (v27 !$ [0]) ; v38 = v21 * (tproject1 (tproject1 (tproject2 v1)) * v37 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v36 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v35 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v29 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v28))))))))) ; v39 = scast v38 ; v40 = sreplicate @3 (v39 !$ [3]) ; v41 = sreplicate @3 (v39 !$ [2]) ; v42 = sreplicate @3 (v39 !$ [1]) ; v43 = sreplicate @3 (v39 !$ [0]) ; v44 = v14 * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v43 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v42 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v41 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v40))) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v44 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v44 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v44 !$ [2])) Z0))) v44) (tpair (tpair (v15 * v43) (tpair (v15 * v42) (tpair (v15 * v41) (tpair (v15 * v40) Z0)))) v38)) (tpair (tpair (v22 * v37) (tpair (v22 * v36) (tpair (v22 * v35) (tpair (v22 * v34) (tpair (v22 * v33) (tpair (v22 * v32) (tpair (v22 * v31) (tpair (v22 * v30) (tpair (v22 * v29) (tpair (v22 * v28) Z0)))))))))) v27)"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret v1 -> let v12 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1))))) ; v15 = scast (sconcrete (sreplicate [3] 0.0) + v12) ; v19 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v15, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v15]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v22 = sconcrete (sreplicate [4] 0.0) + v19 ; v23 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v22, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v22, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v22]) + tproject2 (tproject2 v1)) ; x24 = ssum0 v23 ; v27 = v23 * (sreplicate @10 (negate (recip (x24 * x24)) * sdot0 v23 (sfromR dret)) + sreplicate @10 (recip x24) * sfromR dret) ; x28 = v27 !$ [9] ; x29 = v27 !$ [8] ; x30 = v27 !$ [7] ; x31 = v27 !$ [6] ; x32 = v27 !$ [5] ; x33 = v27 !$ [4] ; x34 = v27 !$ [3] ; x35 = v27 !$ [2] ; x36 = v27 !$ [1] ; x37 = v27 !$ [0] ; v38 = (v19 * (sconcrete (sreplicate [4] 1.0) + negate v19)) * (tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x37 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x36 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x35 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x29 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x28))))))))) ; v39 = scast v38 ; x40 = v39 !$ [3] ; x41 = v39 !$ [2] ; x42 = v39 !$ [1] ; x43 = v39 !$ [0] ; v44 = (v12 * (sconcrete (sreplicate [3] 1.0) + negate v12)) * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x43 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x42 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x41 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x40))) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v44 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v44 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v44 !$ [2])) Z0))) v44) (tpair (tpair (v15 * sreplicate @3 x43) (tpair (v15 * sreplicate @3 x42) (tpair (v15 * sreplicate @3 x41) (tpair (v15 * sreplicate @3 x40) Z0)))) v38)) (tpair (tpair (v22 * sreplicate @4 x37) (tpair (v22 * sreplicate @4 x36) (tpair (v22 * sreplicate @4 x35) (tpair (v22 * sreplicate @4 x34) (tpair (v22 * sreplicate @4 x33) (tpair (v22 * sreplicate @4 x32) (tpair (v22 * sreplicate @4 x31) (tpair (v22 * sreplicate @4 x30) (tpair (v22 * sreplicate @4 x29) (tpair (v22 * sreplicate @4 x28) Z0)))))))))) v27)"

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
    @?= "\\m1 -> let m5 = str (sreplicate @5 (scast (ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = str (sreplicate @2 (scast (ssum @4 (m5 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in rfromS (ssum @5 (m6 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1)))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m5 = str (sreplicate @5 (scast (ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = str (sreplicate @2 (scast (ssum @4 (m5 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v8 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m9 = sreplicate @4 (scast v8) ; v10 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m9))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0) * v10)))) (rfromS v10)) (tpair (rfromS (str (m5 * m9))) (rfromS v8))) (tpair (rfromS (str (m6 * sreplicate @5 (sfromR dret)))) (rfromS (sfromR dret)))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m5 = str (sreplicate @5 (scast (ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = str (sreplicate @2 (scast (ssum @4 (m5 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v8 = ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 (sfromR dret))) ; m9 = sreplicate @4 (scast v8) ; v10 = scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m9))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0) * v10)))) (rfromS v10)) (tpair (rfromS (str (m5 * m9))) (rfromS v8))) (tpair (rfromS (str (m6 * sreplicate @5 (sfromR dret)))) (rfromS (sfromR dret)))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v5 = scast (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1)))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; v8 = ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 (sfromR dret)) ; v9 = scast v8 ; v10 = scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v9)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v10))) v10) (tpair (sreplicate @5 v5 * str (sreplicate @4 v9)) v8)) (tpair (sreplicate @2 (scast (ssdot1In (sreplicate @5 v5) (sfromR (tproject1 (tproject2 (tproject1 m1))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @5 (sfromR dret))) dret))"

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
    @?= "\\dummy -> rfromS (tlet (exp (ssum @5 (str (sreplicate @2 (tlet (ssum @4 (str (sreplicate @5 (tlet (tfromPrimal (STKS [4] STKScalar) (ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (scast (sconcrete (sfromListLinear [4,3] [1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0,1.0,2.0,3.0])))) + scast (sconcrete (sfromListLinear [4] [1.0,2.0,3.0,4.0])))) (\\v3 -> ttletPrimal (recip (sconcrete (sreplicate [4] 1.0) + exp (negate (sfromR (tprimalPart (rfromS v3)))))) (\\v4 -> tfromPrimal (STKS [4] STKScalar) v4 + sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [4] STKScalar) (v4 * (sconcrete (sreplicate [4] 1.0) + negate v4)) * sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v3))))))))))) * tfromPrimal (STKS [4,5] STKScalar) (sconcrete (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0]))) + tfromPrimal (STKS [5] STKScalar) (scast (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0])))) (\\v6 -> ttletPrimal (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (sfromR (tprimalPart (rfromS v6)))))) (\\v7 -> tfromPrimal (STKS [5] STKScalar) v7 + sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS (tfromPrimal (STKS [5] STKScalar) (v7 * (sconcrete (sreplicate [5] 1.0) + negate v7)) * sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v6))))))))))) * tfromPrimal (STKS [5,2] STKScalar) (str (scast (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))))) + tfromPrimal (STKS [2] STKScalar) (scast (sconcrete (sfromListLinear [2] [1.0,2.0]))))) (\\v9 -> sreplicate @2 (recip (ssum @2 v9)) * v9))"
  "\\dummy" ++ " -> " ++ printAstSimple (simplifyInlineContract ast3)
    @?= "\\dummy -> rfromS (tlet (exp (ssdot1In (sreplicate @2 (tlet (ssdot1In (sreplicate @5 (ttletPrimal (recip (sconcrete (sreplicate [4] 1.0) + exp (sconcrete (sfromListLinear [4] [-43.0,-44.0,-45.0,-46.0])))) (\\v4 -> tfromPrimal (STKS [4] STKScalar) v4 + tfromDual (tdualPart (STKS [4] STKScalar) (tfromPrimal (STKS [4] STKScalar) (v4 * (sconcrete (sreplicate [4] 1.0) + negate v4)) * tfromDual (tdualPart (STKS [4] STKScalar) (tfromPrimal (STKS [4] STKScalar) (sconcrete (sreplicate [4] 0.0))))))))) (tfromPrimal (STKS [5,4] STKScalar) (sconcrete (sfromListLinear [5,4] [1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0]))) + tfromPrimal (STKS [5] STKScalar) (sconcrete (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0]))) (\\v6 -> ttletPrimal (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (tprimalPart v6)))) (\\v7 -> tfromPrimal (STKS [5] STKScalar) v7 + tfromDual (tdualPart (STKS [5] STKScalar) (tfromPrimal (STKS [5] STKScalar) (v7 * (sconcrete (sreplicate [5] 1.0) + negate v7)) * tfromDual (tdualPart (STKS [5] STKScalar) v6))))))) (tfromPrimal (STKS [2,5] STKScalar) (sconcrete (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))) + tfromPrimal (STKS [2] STKScalar) (sconcrete (sfromListLinear [2] [1.0,2.0])))) (\\v9 -> sreplicate @2 (recip (ssum0 v9)) * v9))"

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
    @?= "\\m1 -> rfromS (let v24 = exp (ssdot1In (sreplicate @2 (sconcrete (sreplicate [5] 0.0) + recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (sreplicate @5 (scast (sconcrete (sreplicate [4] 0.0) + recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in sreplicate @2 (recip (ssum0 v24)) * v24)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; m16 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 0.0) + v13))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; m23 = str (sreplicate @2 (sconcrete (sreplicate [5] 0.0) + v20)) ; v24 = exp (ssum @5 (m23 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) in rfromS (v26 * v24)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; v14 = sconcrete (sreplicate [4] 1.0) + negate v13 ; v15 = v13 * v14 ; m16 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 0.0) + v13))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v21 = sconcrete (sreplicate [5] 1.0) + negate v20 ; v22 = v20 * v21 ; m23 = str (sreplicate @2 (sconcrete (sreplicate [5] 0.0) + v20)) ; v24 = exp (ssum @5 (m23 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v28 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * ssum @2 (v24 * sfromR dret)) + v26 * sfromR dret) ; v29 = v22 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v28)) ; m30 = sreplicate @4 (scast v29) ; v31 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m30))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0) * v31)))) (rfromS v31)) (tpair (rfromS (str (m16 * m30))) (rfromS v29))) (tpair (rfromS (str (m23 * sreplicate @5 v28))) (rfromS v28))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v16 = scast (sconcrete (sreplicate [4] 0.0) + v13) ; v20 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (sreplicate @5 v16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v23 = sconcrete (sreplicate [5] 0.0) + v20 ; v24 = exp (ssdot1In (sreplicate @2 v23) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum0 v24 ; v28 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * sdot0 v24 (sfromR dret)) + sreplicate @2 (recip x25) * sfromR dret) ; v29 = (v20 * (sconcrete (sreplicate [5] 1.0) + negate v20)) * ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v28) ; v30 = scast v29 ; v31 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v30)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v31))) v31) (tpair (sreplicate @5 v16 * str (sreplicate @4 v30)) v29)) (tpair (sreplicate @2 v23 * str (sreplicate @5 v28)) v28))"

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
    @?= "\\m1 -> let v24 = exp (ssdot1In (sreplicate @2 (sconcrete (sreplicate [5] 0.0) + recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (sreplicate @5 (scast (sconcrete (sreplicate [4] 0.0) + recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in negate (kfromS (sdot0 (sconcrete (sreplicate [2] 8.0)) (log (sreplicate @2 (recip (ssum0 v24)) * v24))))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; m16 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 0.0) + v13))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; m23 = str (sreplicate @2 (sconcrete (sreplicate [5] 0.0) + v20)) ; v24 = exp (ssum @5 (m23 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v27 = v26 * v24 ; v28 = log v27 in negate (kfromS (ssum @2 (v28 * sreplicate @2 (sscalar 8.0))))"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; v14 = sconcrete (sreplicate [4] 1.0) + negate v13 ; v15 = v13 * v14 ; m16 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 0.0) + v13))) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v21 = sconcrete (sreplicate [5] 1.0) + negate v20 ; v22 = v20 * v21 ; m23 = str (sreplicate @2 (sconcrete (sreplicate [5] 0.0) + v20)) ; v24 = exp (ssum @5 (m23 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum @2 v24 ; v26 = sreplicate @2 (recip x25) ; v27 = v26 * v24 ; v30 = recip v27 * sreplicate @2 (sscalar 8.0 * sfromK ((-1.0) * dret)) ; v31 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * ssum @2 (v24 * v30)) + v26 * v30) ; v32 = v22 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v31)) ; m33 = sreplicate @4 (scast v32) ; v34 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m33))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0) * v34)))) (rfromS v34)) (tpair (rfromS (str (m16 * m33))) (rfromS v32))) (tpair (rfromS (str (m23 * sreplicate @5 v31))) (rfromS v31))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v16 = scast (sconcrete (sreplicate [4] 0.0) + v13) ; v20 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (sreplicate @5 v16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v23 = sconcrete (sreplicate [5] 0.0) + v20 ; v24 = exp (ssdot1In (sreplicate @2 v23) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum0 v24 ; x26 = recip x25 ; v30 = recip (sreplicate @2 x26 * v24) * sreplicate @2 (sscalar (-8.0) * sfromK dret) ; v31 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * sdot0 v24 v30) + sreplicate @2 x26 * v30) ; v32 = (v20 * (sconcrete (sreplicate [5] 1.0) + negate v20)) * ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v31) ; v33 = scast v32 ; v34 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v33)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v34))) v34) (tpair (sreplicate @5 v16 * str (sreplicate @4 v33)) v32)) (tpair (sreplicate @2 v23 * str (sreplicate @5 v31)) v31))"

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
    @?= "\\m1 -> rfromS (str (sreplicate @1 (str (sfromR (tproject1 (tproject2 m1))) !$ [0])) * sreplicate @10 (tanh ((sreplicate @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0]) * tanh ((sreplicate @1 (sscalar 7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) + sconcrete (sfromListLinear [1] [0.0]) * sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0])) + sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0])) + sconcrete (sfromListLinear [1] [0.0]) * sreplicate @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0])) + sreplicate @1 (sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]))) + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let v23 = sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) ; v24 = sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) ; v25 = tanh ((v23 * sreplicate @1 (sscalar 7.0) + sconcrete (sfromListLinear [1] [0.0]) * v24) + sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0])) ; v26 = sreplicate @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0]) ; v27 = sreplicate @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0]) ; v28 = tanh ((v26 * v25 + sconcrete (sfromListLinear [1] [0.0]) * v27) + sreplicate @1 (sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0])) ; m29 = str (sreplicate @1 (str (sfromR (tproject1 (tproject2 m1))) !$ [0])) in rfromS (m29 * sreplicate @10 v28 + str (sreplicate @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let v23 = sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) ; v24 = sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) ; v25 = tanh ((v23 * sreplicate @1 (sscalar 7.0) + sconcrete (sfromListLinear [1] [0.0]) * v24) + sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0])) ; v26 = sreplicate @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0]) ; v27 = sreplicate @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0]) ; v28 = tanh ((v26 * v25 + sconcrete (sfromListLinear [1] [0.0]) * v27) + sreplicate @1 (sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0])) ; m29 = str (sreplicate @1 (str (sfromR (tproject1 (tproject2 m1))) !$ [0])) ; v31 = (sconcrete (sfromListLinear [1] [1.0]) + negate v28 * v28) * ssum @10 (m29 * sfromR dret) ; v32 = (sconcrete (sfromListLinear [1] [1.0]) + negate v25 * v25) * (v26 * v31) in tpair (tpair (tpair (tpair (rfromS (soneHot (ssum @1 (sreplicate @1 (sscalar 7.0) * v32)) [0, 0])) (rfromS (soneHot (ssum @1 (sconcrete (sfromListLinear [1] [0.0]) * v32)) [0, 0]))) (rfromS (soneHot (ssum @1 v32) [0]))) (tpair (tpair (rfromS (soneHot (ssum @1 (v25 * v31)) [0, 0])) (rfromS (soneHot (ssum @1 (sconcrete (sfromListLinear [1] [0.0]) * v31)) [0, 0]))) (rfromS (soneHot (ssum @1 v31) [0])))) (tpair (rfromS (str (soneHot (ssum @1 (str (sreplicate @10 v28 * sfromR dret))) [0]))) (rfromS (ssum @1 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar)) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v25 = tanh ((sreplicate @1 (sscalar 7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0]) + sconcrete (sfromListLinear [1] [0.0]) * sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0])) + sreplicate @1 (sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0])) ; x26 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] ; v28 = tanh ((sreplicate @1 x26 * v25 + sconcrete (sfromListLinear [1] [0.0]) * sreplicate @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0])) + sreplicate @1 (sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0])) ; v31 = (sconcrete (sfromListLinear [1] [1.0]) + negate v28 * v28) * ssdot1In (sreplicate @1 (str (sfromR (tproject1 (tproject2 m1))) !$ [0])) (str (sfromR dret)) ; v32 = (sconcrete (sfromListLinear [1] [1.0]) + negate v25 * v25) * (sreplicate @1 x26 * v31) in tpair (tpair (tpair (tpair (sreplicate @1 (sreplicate @1 (sscalar 7.0 * v32 !$ [0]))) (sreplicate @1 (sreplicate @1 (sscalar 0.0 * v32 !$ [0])))) (sreplicate @1 (v32 !$ [0]))) (tpair (tpair (sreplicate @1 (sreplicate @1 (v25 !$ [0] * v31 !$ [0]))) (sreplicate @1 (sreplicate @1 (sscalar 0.0 * v31 !$ [0])))) (sreplicate @1 (v31 !$ [0])))) (tpair (str (sreplicate @1 (sreplicate @10 (v28 !$ [0]) * str (sfromR dret) !$ [0]))) (str (sfromR dret) !$ [0])))"

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
    @?= "\\m1 -> rfromS (let m6 = sappend (tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 7.0)) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 7.0)) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 7.0)) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice (SNat @0) (SNat @2) m6)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m6)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let m3 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m5 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 m4)) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m6 = sappend m3 m5 ; m7 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @0) (SNat @2) m6)))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m8 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 m7)) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @2) (SNat @2) m6)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) in rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * str (sreplicate @10 m8)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m3 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m5 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 m4)) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m6 = sappend m3 m5 ; m7 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @0) (SNat @2) m6)))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m8 = tanh ((ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 m7)) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @2 (sslice (SNat @2) (SNat @2) m6)))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m10 = (sconcrete (sreplicate [2,2] 1.0) + negate m8 * m8) * ssum @10 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @2 (sfromR dret))) ; m11 = (sconcrete (sreplicate [2,2] 1.0) + negate m7 * m7) * ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * sreplicate @2 m10)) ; m12 = sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 m11))) (sconcrete (sreplicate [2,2] 0.0))) + sappend (sconcrete (sreplicate [2,2] 0.0)) (sappend (ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * sreplicate @2 m10))) (sconcrete (sfromListLinear [0,2] []))) ; m13 = (sconcrete (sreplicate [2,2] 1.0) + negate m5 * m5) * sslice (SNat @2) (SNat @2) m12 ; m14 = (sconcrete (sreplicate [2,2] 1.0) + negate m4 * m4) * ssum @2 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * sreplicate @2 m13)) ; m15 = (sconcrete (sreplicate [2,2] 1.0) + negate m3 * m3) * sslice (SNat @0) (SNat @2) m12 in tpair (tpair (tpair (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)) * m15))) + (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)) * m14))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 7.0)) * m11)))))) (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))) * sreplicate @2 m15)) + (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))) * sreplicate @2 m14)) + ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (sslice (SNat @0) (SNat @2) m6)) * sreplicate @2 m11)))))) (rfromS (ssum @2 (str m15) + (ssum @2 (str m14) + ssum @2 (str m11))))) (tpair (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 m4) * sreplicate @2 m13)) + ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 m7) * sreplicate @2 m10)))) (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (sconcrete (sreplicate [2,2] 0.0))) * sreplicate @2 m13)) + ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (sslice (SNat @2) (SNat @2) m6)) * sreplicate @2 m10))))) (rfromS (ssum @2 (str m13) + ssum @2 (str m10))))) (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @10 m8) * sreplicate @2 (sfromR dret))))) (rfromS (ssum @2 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar)) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let m3 = tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 7.0)) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 7.0)) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m5 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m4 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m6 = sappend m3 m5 ; m7 = tanh ((ssdot1In (str (sreplicate @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 7.0)) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice (SNat @0) (SNat @2) m6)) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m8 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m7 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice (SNat @2) (SNat @2) m6)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m10 = (sconcrete (sreplicate [2,2] 1.0) + negate m8 * m8) * smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR dret) ; m11 = (sconcrete (sreplicate [2,2] 1.0) + negate m7 * m7) * smatmul2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m10 ; m12 = sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) m11) (sconcrete (sreplicate [2,2] 0.0)) + sappend (sconcrete (sreplicate [2,2] 0.0)) (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) m10) ; m13 = (sconcrete (sreplicate [2,2] 1.0) + negate m5 * m5) * sslice (SNat @2) (SNat @2) m12 ; m14 = (sconcrete (sreplicate [2,2] 1.0) + negate m4 * m4) * smatmul2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m13 ; m15 = (sconcrete (sreplicate [2,2] 1.0) + negate m3 * m3) * sslice (SNat @0) (SNat @2) m12 in tpair (tpair (tpair (tpair (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sconcrete (sreplicate [2,2] 7.0) * m15))) + (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sconcrete (sreplicate [2,2] 7.0) * m14))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sconcrete (sreplicate [2,2] 7.0) * m11))))) (smatmul2 m15 (sconcrete (sreplicate [2,2] 0.0)) + (smatmul2 m14 (sconcrete (sreplicate [2,2] 0.0)) + smatmul2 m11 (str (sslice (SNat @0) (SNat @2) m6))))) (ssum @2 (str m15) + (ssum @2 (str m14) + ssum @2 (str m11)))) (tpair (tpair (smatmul2 m13 (str m4) + smatmul2 m10 (str m7)) (smatmul2 m13 (sconcrete (sreplicate [2,2] 0.0)) + smatmul2 m10 (str (sslice (SNat @2) (SNat @2) m6)))) (ssum @2 (str m13) + ssum @2 (str m10)))) (tpair (smatmul2 (sfromR dret) (str m8)) (ssum @2 (str (sfromR dret)))))"

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
    @?= "\\u1 -> rfromS (let u279 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,7,9,4] (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [7,5,9] 7.0)) (\\[i507, i508] -> [i507 + i508]))) (\\[i275, i276] -> [i275 + i276])))))) * sreplicate @5 (sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; u291 = sreshape @[5,3,4,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i280, i281, i282, i283, i284] -> [ifH (sscalar -0.0 <=. negate (u279 !$ [i280, 0, 2 * i281 + i283, 2 * i282 + i284])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,3,0] u279 !$ [0]) (\\[i285, i286, i287, i288] -> [2 * i285 + i287, 2 * i286 + i288]))) ; u301 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,3,4,4] (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,4,5,2,0,1] (sgather (stranspose @[4,6,0,2,5,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[3,2,1,0] u291))))))) (\\[i490, i492, i494] -> [kfromS (smaxIndex (u291 !$ [i494, i490, i492])), i492, i490, i494]))) (\\[i499, i500] -> [i499, i500, i499 + i500]))) (\\[i297, i298] -> [i297, i297 + i298, i298])) * sreplicate @5 (sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; t310 = sreshape @[5,2,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303, i304, i305] -> [ifH (sscalar -0.0 <=. negate (u301 !$ [i302, 0, i304, 2 * i303 + i305])) 0 1]) * stranspose @[2,0,3,1] (sgather (stranspose @[2,3,1,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,1,0] (sreplicate @2 (str u301 !$ [0]))))) (\\[i306, i307] -> [i306, 2 * i306 + i307]))) ; m315 = sreplicate @1 (ssdot1In (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0])) (sreshape @[5,2] (str (sreplicate @1 (str (sreplicate @1 (sgather t310 (\\[i311, i312] -> [i311, i312, kfromS (smaxIndex (t310 !$ [i311, i312]))])))))))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) * sreplicate @10 (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i316] -> [ifH (sscalar -0.0 <=. negate (m315 !$ [0, i316])) 0 1]) * m315 !$ [0]) + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w277 = stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [7,5,9] 7.0)) (\\[i273, i274] -> [i273 + i274]))) (\\[i275, i276] -> [i275 + i276])))))) ; w278 = sreplicate @5 (sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0]))))) ; u279 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,7,9,4] (w277 * w278))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w289 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i280, i281, i282, i283, i284] -> [ifH (sscalar -0.0 <=. negate (u279 !$ [i280, 0, 2 * i281 + i283, 2 * i282 + i284])) 0 1]) ; w290 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,3,0] u279 !$ [0]) (\\[i285, i286, i287, i288] -> [2 * i285 + i287, 2 * i286 + i288])) ; u291 = sreshape @[5,3,4,4] (w289 * w290) ; w299 = stranspose @[2,3,0,4,1] (sgather (stranspose @[3,4,5,2,0,1] (sgather (stranspose @[4,6,0,2,5,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[3,2,1,0] u291))))))) (\\[i292, i293, i294] -> [kfromS (smaxIndex (u291 !$ [i294, i292, i293])), i293, i292, i294]))) (\\[i295, i296] -> [i295, i296, i295 + i296]))) (\\[i297, i298] -> [i297, i297 + i298, i298])) ; w300 = sreplicate @5 (sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0]))) ; u301 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,3,4,4] (w299 * w300))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; u308 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303, i304, i305] -> [ifH (sscalar -0.0 <=. negate (u301 !$ [i302, 0, i304, 2 * i303 + i305])) 0 1]) ; u309 = stranspose @[2,0,3,1] (sgather (stranspose @[2,3,1,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,1,0] (sreplicate @2 (str u301 !$ [0]))))) (\\[i306, i307] -> [i306, 2 * i306 + i307])) ; t310 = sreshape @[5,2,4] (u308 * u309) ; m313 = str (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0])) ; m314 = str (sreshape @[5,2] (str (sreplicate @1 (str (sreplicate @1 (sgather t310 (\\[i311, i312] -> [i311, i312, kfromS (smaxIndex (t310 !$ [i311, i312]))]))))))) ; m315 = sreplicate @1 (ssum @2 (m313 * m314)) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v317 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i316] -> [ifH (sscalar -0.0 <=. negate (m315 !$ [0, i316])) 0 1]) ; v318 = m315 !$ [0] ; m319 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m320 = sreplicate @10 (v317 * v318) in rfromS (m319 * m320 + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w277 = stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [7,5,9] 7.0)) (\\[i273, i274] -> [i273 + i274]))) (\\[i275, i276] -> [i275 + i276])))))) ; w278 = sreplicate @5 (sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0]))))) ; u279 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,7,9,4] (w277 * w278))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w289 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i280, i281, i282, i283, i284] -> [ifH (sscalar -0.0 <=. negate (u279 !$ [i280, 0, 2 * i281 + i283, 2 * i282 + i284])) 0 1]) ; w290 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,3,0] u279 !$ [0]) (\\[i285, i286, i287, i288] -> [2 * i285 + i287, 2 * i286 + i288])) ; u291 = sreshape @[5,3,4,4] (w289 * w290) ; w299 = stranspose @[2,3,0,4,1] (sgather (stranspose @[3,4,5,2,0,1] (sgather (stranspose @[4,6,0,2,5,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[3,2,1,0] u291))))))) (\\[i292, i293, i294] -> [kfromS (smaxIndex (u291 !$ [i294, i292, i293])), i293, i292, i294]))) (\\[i295, i296] -> [i295, i296, i295 + i296]))) (\\[i297, i298] -> [i297, i297 + i298, i298])) ; w300 = sreplicate @5 (sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0]))) ; u301 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,3,4,4] (w299 * w300))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; u308 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303, i304, i305] -> [ifH (sscalar -0.0 <=. negate (u301 !$ [i302, 0, i304, 2 * i303 + i305])) 0 1]) ; u309 = stranspose @[2,0,3,1] (sgather (stranspose @[2,3,1,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,1,0] (sreplicate @2 (str u301 !$ [0]))))) (\\[i306, i307] -> [i306, 2 * i306 + i307])) ; t310 = sreshape @[5,2,4] (u308 * u309) ; m313 = str (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0])) ; m314 = str (sreshape @[5,2] (str (sreplicate @1 (str (sreplicate @1 (sgather t310 (\\[i311, i312] -> [i311, i312, kfromS (smaxIndex (t310 !$ [i311, i312]))]))))))) ; m315 = sreplicate @1 (ssum @2 (m313 * m314)) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v317 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i316] -> [ifH (sscalar -0.0 <=. negate (m315 !$ [0, i316])) 0 1]) ; v318 = m315 !$ [0] ; m319 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m320 = sreplicate @10 (v317 * v318) ; m322 = soneHot (v317 * ssum @10 (m319 * sfromR dret)) [0] ; u327 = str (soneHot (ssum @2 (stranspose @[2,1,0] (sappend (sconcrete (sfromListLinear [0,5,2,4] [])) (sappend (stranspose @[3,2,0,1] (sscatter (stranspose @[1,3,0,2] (u308 * sreshape @[5,2,2,2] (sscatter (ssum @1 (str (ssum @1 (str (sreshape @[5,1,1,2] (str (m313 * sreplicate @2 (ssum @1 m322)))))))) (\\[i323, i324] -> [i323, i324, kfromS (smaxIndex (t310 !$ [i323, i324]))])))) (\\[i325, i326] -> [i325, 2 * i325 + i326]))) (sconcrete (sreplicate [1,5,2,4] 0.0)))))) [0]) ; w328 = sreshape @[5,3,4,2,2] (stranspose @[1,2,3,0] (sreplicate @4 (ssum @1 (str u327)))) ; u340 = stranspose @[3,0,1,2] (soneHot (sscatter (stranspose @[1,2,3,4,0] (w289 * sreshape @[5,3,4,2,2] (stranspose @[3,2,1,0] (ssum @2 (ssum @3 (ssum @4 (stranspose @[4,5,6,3,2,1,0] (ssum @2 (stranspose @[7,3,2,1,0,6,5,4] (sscatter (stranspose @[2,5,3,6,0,4,1] (sscatter (stranspose @[4,5,3,0,1,2] (sscatter (stranspose @[2,4,0,1,3] (w300 * w328)) (\\[i329, i330] -> [i329, i329 + i330, i330]))) (\\[i331, i332] -> [i331, i332, i331 + i332]))) (\\[i333, i334, i335] -> [kfromS (smaxIndex (u291 !$ [i335, i333, i334])), i334, i333, i335]))))))))))) (\\[i336, i337, i338, i339] -> [2 * i336 + i338, 2 * i337 + i339])) [0]) in tpair (tpair (tpair (rfromS (soneHot (ssum @1 (ssum @1 (ssum @9 (ssum @7 (ssum @5 (w277 * sreshape @[5,7,9,1,1,2,2] (stranspose @[1,2,3,0] (sreplicate @4 (ssum @1 (str u340)))))))))) [0, 0])) (rfromS (ssum @9 (ssum @7 (stranspose @[1,2,0] (ssum @5 u340)))))) (tpair (rfromS (soneHot (ssum @4 (ssum @3 (ssum @5 (w299 * w328)))) [0, 0])) (rfromS (ssum @4 (ssum @3 (stranspose @[1,2,0] (ssum @5 u327))))))) (tpair (tpair (rfromS (soneHot (ssum @5 (str (m314 * sreplicate @2 (ssum @1 m322)))) [0])) (rfromS (ssum @5 (str m322)))) (tpair (rfromS (str (soneHot (ssum @5 (str (m320 * sfromR dret))) [0]))) (rfromS (ssum @5 (str (sfromR dret))))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let w277 = sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [7,5,9] 7.0)) (\\[i601, i602] -> [i601 + i602]))) (\\[i275, i276] -> [i275 + i276]) ; u279 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,7,9,4] (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] w277)))) * sreplicate @5 (sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w289 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i280, i281, i282, i283, i284] -> [ifH (sscalar -0.0 <=. negate (u279 !$ [i280, 0, 2 * i281 + i283, 2 * i282 + i284])) 0 1]) ; u291 = sreshape @[5,3,4,4] (w289 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,3,0] u279 !$ [0]) (\\[i285, i286, i287, i288] -> [2 * i285 + i287, 2 * i286 + i288]))) ; w299 = sgather (stranspose @[3,4,5,2,0,1] (sgather (stranspose @[4,6,0,2,5,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[3,2,1,0] u291))))))) (\\[i584, i586, i588] -> [kfromS (smaxIndex (u291 !$ [i588, i584, i586])), i586, i584, i588]))) (\\[i593, i594] -> [i593, i594, i593 + i594]))) (\\[i297, i298] -> [i297, i297 + i298, i298]) ; m300 = sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0] ; u301 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,3,4,4] (stranspose @[2,3,0,4,1] w299 * sreplicate @5 (sreplicate @3 (sreplicate @4 m300))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; u308 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i302, i303, i304, i305] -> [ifH (sscalar -0.0 <=. negate (u301 !$ [i302, 0, i304, 2 * i303 + i305])) 0 1]) ; t310 = sreshape @[5,2,4] (u308 * stranspose @[2,0,3,1] (sgather (stranspose @[2,3,1,0] (sslice (SNat @0) (SNat @2) (stranspose @[2,1,0] (sreplicate @2 (str u301 !$ [0]))))) (\\[i306, i307] -> [i306, 2 * i306 + i307]))) ; v313 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; m314 = sreshape @[5,2] (str (sreplicate @1 (str (sreplicate @1 (sgather t310 (\\[i311, i312] -> [i311, i312, kfromS (smaxIndex (t310 !$ [i311, i312]))])))))) ; m315 = sreplicate @1 (ssdot1In (sreplicate @5 v313) m314) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v317 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i316] -> [ifH (sscalar -0.0 <=. negate (m315 !$ [0, i316])) 0 1]) ; v322 = v317 * ssdot1In (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) (str (sfromR dret)) ; t327 = ssum @2 (stranspose @[2,1,0] (sappend (stranspose @[3,2,0,1] (sscatter (stranspose @[1,3,0,2] u308 * stranspose @[1,3,0,2] (sreshape @[5,2,2,2] (sscatter (stranspose @[1,2,0] (sreshape @[5,1,1,2] (sreplicate @5 v313 * str (sreplicate @2 v322))) !$ [0, 0]) (\\[i323, i324] -> [i323, i324, kfromS (smaxIndex (t310 !$ [i323, i324]))])))) (\\[i325, i326] -> [i325, 2 * i325 + i326]))) (sconcrete (sreplicate [1,5,2,4] 0.0)))) ; w328 = sreshape @[5,3,4,2,2] (stranspose @[1,2,3,0] (sreplicate @4 t327)) ; t340 = sscatter (stranspose @[1,2,3,4,0] w289 * stranspose @[1,2,3,4,0] (sreshape @[5,3,4,2,2] (ssum @2 (ssum @3 (ssum @4 (ssum @2 (stranspose @[7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,5,3,6,0,4,1] (sscatter (stranspose @[4,5,3,0,1,2] (sscatter (stranspose @[2,4,0,1,3] (sreplicate @5 (sreplicate @3 (sreplicate @4 m300))) * stranspose @[2,4,0,1,3] w328) (\\[i329, i330] -> [i329, i329 + i330, i330]))) (\\[i331, i332] -> [i331, i332, i331 + i332]))) (\\[i333, i334, i335] -> [kfromS (smaxIndex (u291 !$ [i335, i333, i334])), i334, i333, i335]))))))))) (\\[i336, i337, i338, i339] -> [2 * i336 + i338, 2 * i337 + i339]) in tpair (tpair (tpair (sreplicate @1 (sreplicate @1 (ssum @9 (ssum @7 (ssdot1In (stranspose @[3,0,4,1,2] w277) (stranspose @[1,0,3,4,2] (stranspose @[3,4,2,1,0] (sreshape @[5,7,9,1,1,2,2] (stranspose @[1,2,3,0] (sreplicate @4 (stranspose @[2,0,1] t340)))) !$ [0, 0]))))))) (ssum @9 (ssum @7 (ssum @5 (stranspose @[3,1,2,0] (sreplicate @1 t340)))))) (tpair (sreplicate @1 (sreplicate @1 (ssum @4 (ssum @3 (ssdot1In (stranspose @[3,0,4,1,2] w299) (stranspose @[1,2,3,4,0] w328)))))) (ssum @4 (ssum @3 (ssum @5 (stranspose @[1,2,3,0] (sreplicate @1 t327))))))) (tpair (tpair (sreplicate @1 (ssdot1In (str m314) (sreplicate @2 v322))) (ssum @5 (str (sreplicate @1 v322)))) (tpair (str (sreplicate @1 (ssdot1In (sreplicate @10 (v317 * m315 !$ [0])) (sfromR dret)))) (ssum @5 (str (sfromR dret))))))"

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
    @?= "\\u1 -> rfromS (let u325 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i603, i604] -> [i603 + i604]))) (\\[i321, i322] -> [i321 + i322])))))))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w338 = sreshape @[7,4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i326, i327, i328, i329, i330, i331] -> [ifH (sscalar -0.0 <=. negate (u325 !$ [i326, i327, 2 * i328 + i330, 2 * i329 + i331])) 0 1]) * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u325) (\\[i332, i333, i334, i335] -> [2 * i332 + i334, 2 * i333 + i335]))) ; u348 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w338))))))) (\\[i580, i584, i585, i587] -> [kfromS (smaxIndex (w338 !$ [i587, i585, i580, i584])), i584, i580, i585, i587]))) (\\[i592, i594] -> [i592, i594, i592 + i594]))) (\\[i345, i346] -> [i345, i345 + i346, i346])))) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w361 = sreshape @[7,4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354] -> [ifH (sscalar -0.0 <=. negate (u348 !$ [i349, i350, 2 * i351 + i353, 2 * i352 + i354])) 0 1]) * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u348) (\\[i355, i356, i357, i358] -> [2 * i355 + i357, 2 * i356 + i358]))) ; m368 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w361))) (\\[i362, i363, i364, i365] -> [i362, i363, i364, i365, kfromS (smaxIndex (w361 !$ [i362, i363, i364, i365]))])))) (\\[i366] -> [i366, i366]))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in smatmul2 (sfromR (tproject1 (tproject2 (tproject2 u1)))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i369, i370] -> [ifH (sscalar -0.0 <=. negate (m368 !$ [i369, i370])) 0 1]) * m368) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w323 = str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i319, i320] -> [i319 + i320]))) (\\[i321, i322] -> [i321 + i322])))))))) ; w324 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))) ; u325 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w323 * w324))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w336 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i326, i327, i328, i329, i330, i331] -> [ifH (sscalar -0.0 <=. negate (u325 !$ [i326, i327, 2 * i328 + i330, 2 * i329 + i331])) 0 1]) ; w337 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u325) (\\[i332, i333, i334, i335] -> [2 * i332 + i334, 2 * i333 + i335])) ; w338 = sreshape @[7,4,7,11,4] (w336 * w337) ; w347 = str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w338))))))) (\\[i339, i340, i341, i342] -> [kfromS (smaxIndex (w338 !$ [i342, i341, i339, i340])), i340, i339, i341, i342]))) (\\[i343, i344] -> [i343, i344, i343 + i344]))) (\\[i345, i346] -> [i345, i345 + i346, i346])))) ; u348 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w347 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w359 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354] -> [ifH (sscalar -0.0 <=. negate (u348 !$ [i349, i350, 2 * i351 + i353, 2 * i352 + i354])) 0 1]) ; w360 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u348) (\\[i355, i356, i357, i358] -> [2 * i355 + i357, 2 * i356 + i358])) ; w361 = sreshape @[7,4,3,5,4] (w359 * w360) ; t367 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w361))) (\\[i362, i363, i364, i365] -> [i362, i363, i364, i365, kfromS (smaxIndex (w361 !$ [i362, i363, i364, i365]))])))) (\\[i366] -> [i366, i366])))) ; m368 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * t367) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m371 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i369, i370] -> [ifH (sscalar -0.0 <=. negate (m368 !$ [i369, i370])) 0 1]) ; t372 = str (sreplicate @10 (m371 * m368)) in rfromS (ssum @5 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * t372) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w323 = str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i319, i320] -> [i319 + i320]))) (\\[i321, i322] -> [i321 + i322])))))))) ; w324 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))) ; u325 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w323 * w324))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w336 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i326, i327, i328, i329, i330, i331] -> [ifH (sscalar -0.0 <=. negate (u325 !$ [i326, i327, 2 * i328 + i330, 2 * i329 + i331])) 0 1]) ; w337 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u325) (\\[i332, i333, i334, i335] -> [2 * i332 + i334, 2 * i333 + i335])) ; w338 = sreshape @[7,4,7,11,4] (w336 * w337) ; w347 = str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w338))))))) (\\[i339, i340, i341, i342] -> [kfromS (smaxIndex (w338 !$ [i342, i341, i339, i340])), i340, i339, i341, i342]))) (\\[i343, i344] -> [i343, i344, i343 + i344]))) (\\[i345, i346] -> [i345, i345 + i346, i346])))) ; u348 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w347 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w359 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354] -> [ifH (sscalar -0.0 <=. negate (u348 !$ [i349, i350, 2 * i351 + i353, 2 * i352 + i354])) 0 1]) ; w360 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u348) (\\[i355, i356, i357, i358] -> [2 * i355 + i357, 2 * i356 + i358])) ; w361 = sreshape @[7,4,3,5,4] (w359 * w360) ; t367 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w361))) (\\[i362, i363, i364, i365] -> [i362, i363, i364, i365, kfromS (smaxIndex (w361 !$ [i362, i363, i364, i365]))])))) (\\[i366] -> [i366, i366])))) ; m368 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * t367) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m371 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i369, i370] -> [ifH (sscalar -0.0 <=. negate (m368 !$ [i369, i370])) 0 1]) ; t372 = str (sreplicate @10 (m371 * m368)) ; m374 = m371 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * sreplicate @5 (sfromR dret))) ; u384 = stranspose @[3,2,0,1] (sscatter (stranspose @[2,3,4,5,1,0] (w359 * sreshape @[7,4,3,5,2,2] (stranspose @[4,3,2,1,0] (ssum @7 (stranspose @[5,4,3,2,1,0] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (str (ssum @5 (str (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * sreplicate @60 m374)))) (\\[i375] -> [i375, i375])))) (\\[i376, i377, i378, i379] -> [i376, i377, i378, i379, kfromS (smaxIndex (w361 !$ [i376, i377, i378, i379]))]))))))) (\\[i380, i381, i382, i383] -> [2 * i380 + i382, 2 * i381 + i383])) ; w385 = sreshape @[7,4,7,11,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 u384)) ; u398 = stranspose @[3,2,0,1] (sscatter (stranspose @[2,3,4,5,1,0] (w336 * sreshape @[7,4,7,11,2,2] (stranspose @[4,3,2,1,0] (ssum @4 (ssum @7 (ssum @11 (stranspose @[5,6,7,4,3,2,1,0] (ssum @3 (stranspose @[8,4,3,2,1,0,7,6,5] (sscatter (stranspose @[2,6,5,3,7,0,4,1] (sscatter (stranspose @[4,6,3,0,5,1,2] (sscatter (stranspose @[2,5,0,1,3,4] (ssum @4 (str (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))) * w385)))) (\\[i386, i387] -> [i386, i386 + i387, i387]))) (\\[i388, i389] -> [i388, i389, i388 + i389]))) (\\[i390, i391, i392, i393] -> [kfromS (smaxIndex (w338 !$ [i393, i392, i390, i391])), i391, i390, i392, i393]))))))))))) (\\[i394, i395, i396, i397] -> [2 * i394 + i396, 2 * i395 + i397])) in tpair (tpair (tpair (rfromS (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (ssum @7 (w323 * sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 u398)))))))))))) [0]))) (rfromS (ssum @23 (ssum @14 (stranspose @[1,2,0] (ssum @7 u398)))))) (tpair (rfromS (ssum @11 (str (ssum @7 (str (ssum @7 (w347 * w385))))))) (rfromS (ssum @11 (ssum @7 (stranspose @[1,2,0] (ssum @7 u384))))))) (tpair (tpair (rfromS (ssum @7 (stranspose @[2,1,0] (t367 * sreplicate @60 m374)))) (rfromS (ssum @7 (str m374)))) (tpair (rfromS (ssum @7 (stranspose @[2,1,0] (t372 * sreplicate @5 (sfromR dret))))) (rfromS (ssum @7 (str (sfromR dret))))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let w323 = sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i721, i722] -> [i721 + i722]))) (\\[i321, i322] -> [i321 + i322]) ; u325 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] w323)))))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w336 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i326, i327, i328, i329, i330, i331] -> [ifH (sscalar -0.0 <=. negate (u325 !$ [i326, i327, 2 * i328 + i330, 2 * i329 + i331])) 0 1]) ; w338 = sreshape @[7,4,7,11,4] (w336 * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u325) (\\[i332, i333, i334, i335] -> [2 * i332 + i334, 2 * i333 + i335]))) ; w347 = sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w338))))))) (\\[i698, i702, i703, i705] -> [kfromS (smaxIndex (w338 !$ [i705, i703, i698, i702])), i702, i698, i703, i705]))) (\\[i710, i712] -> [i710, i712, i710 + i712]))) (\\[i345, i346] -> [i345, i345 + i346, i346]) ; u348 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,1] w347)) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w359 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354] -> [ifH (sscalar -0.0 <=. negate (u348 !$ [i349, i350, 2 * i351 + i353, 2 * i352 + i354])) 0 1]) ; w361 = sreshape @[7,4,3,5,4] (w359 * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u348) (\\[i355, i356, i357, i358] -> [2 * i355 + i357, 2 * i356 + i358]))) ; m367 = sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w361))) (\\[i362, i363, i364, i365] -> [i362, i363, i364, i365, kfromS (smaxIndex (w361 !$ [i362, i363, i364, i365]))])))) (\\[i366] -> [i366, i366]) ; m368 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str m367) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m371 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i369, i370] -> [ifH (sscalar -0.0 <=. negate (m368 !$ [i369, i370])) 0 1]) ; m374 = m371 * smatmul2 (str (sfromR (tproject1 (tproject2 (tproject2 u1))))) (sfromR dret) ; u384 = sscatter (stranspose @[2,3,4,5,1,0] w359 * stranspose @[2,3,4,5,1,0] (sreshape @[7,4,3,5,2,2] (ssum @7 (stranspose @[5,0,1,2,3,4] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (smatmul2 (str m374) (sfromR (tproject1 (tproject1 (tproject2 u1))))) (\\[i375] -> [i375, i375])))) (\\[i376, i377, i378, i379] -> [i376, i377, i378, i379, kfromS (smaxIndex (w361 !$ [i376, i377, i378, i379]))])))))) (\\[i380, i381, i382, i383] -> [2 * i380 + i382, 2 * i381 + i383]) ; w385 = sreshape @[7,4,7,11,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 (stranspose @[3,2,0,1] u384))) ; u398 = sscatter (stranspose @[2,3,4,5,1,0] w336 * stranspose @[2,3,4,5,1,0] (sreshape @[7,4,7,11,2,2] (ssum @4 (ssum @7 (ssum @11 (ssum @3 (stranspose @[8,7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,6,5,3,7,0,4,1] (sscatter (stranspose @[4,6,3,0,5,1,2] (sscatter (ssdot1In (stranspose @[3,6,0,2,4,5,1] (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) (stranspose @[3,6,0,2,4,5,1] w385)) (\\[i386, i387] -> [i386, i386 + i387, i387]))) (\\[i388, i389] -> [i388, i389, i388 + i389]))) (\\[i390, i391, i392, i393] -> [kfromS (smaxIndex (w338 !$ [i393, i392, i390, i391])), i391, i390, i392, i393]))))))))) (\\[i394, i395, i396, i397] -> [2 * i394 + i396, 2 * i395 + i397]) in tpair (tpair (tpair (str (sreplicate @1 (ssum @23 (ssum @14 (ssdot1In (stranspose @[1,5,0,4,3,2] (sreplicate @4 (stranspose @[3,2,1,4,0] w323))) (stranspose @[1,0,2,4,5,3] (stranspose @[4,5,3,2,1,0] (sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 (stranspose @[3,2,0,1] u398)))) !$ [0, 0]))))))) (ssum @23 (ssum @14 (ssum @7 (stranspose @[3,0,1,2] u398))))) (tpair (ssum @11 (ssum @7 (ssdot1In (stranspose @[2,3,0,4,5,6,1] (sreplicate @4 (stranspose @[2,3,0,4,5,1] w347))) (stranspose @[2,3,1,4,5,6,0] w385)))) (ssum @11 (ssum @7 (ssum @7 (stranspose @[3,0,1,2] u384)))))) (tpair (tpair (smatmul2 m374 m367) (ssum @7 (str m374))) (tpair (smatmul2 (sfromR dret) (str m371 * str m368)) (ssum @7 (str (sfromR dret))))))"

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
    @?= "\\u1 -> let u325 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i603, i604] -> [i603 + i604]))) (\\[i321, i322] -> [i321 + i322])))))))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w338 = sreshape @[7,4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i326, i327, i328, i329, i330, i331] -> [ifH (sscalar -0.0 <=. negate (u325 !$ [i326, i327, 2 * i328 + i330, 2 * i329 + i331])) 0 1]) * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u325) (\\[i332, i333, i334, i335] -> [2 * i332 + i334, 2 * i333 + i335]))) ; u348 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w338))))))) (\\[i580, i584, i585, i587] -> [kfromS (smaxIndex (w338 !$ [i587, i585, i580, i584])), i584, i580, i585, i587]))) (\\[i592, i594] -> [i592, i594, i592 + i594]))) (\\[i345, i346] -> [i345, i345 + i346, i346])))) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w361 = sreshape @[7,4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354] -> [ifH (sscalar -0.0 <=. negate (u348 !$ [i349, i350, 2 * i351 + i353, 2 * i352 + i354])) 0 1]) * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u348) (\\[i355, i356, i357, i358] -> [2 * i355 + i357, 2 * i356 + i358]))) ; m368 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w361))) (\\[i362, i363, i364, i365] -> [i362, i363, i364, i365, kfromS (smaxIndex (w361 !$ [i362, i363, i364, i365]))])))) (\\[i366] -> [i366, i366]))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) in smatmul2 (tproject1 (tproject2 (tproject2 u1))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i369, i370] -> [ifH (sscalar -0.0 <=. negate (m368 !$ [i369, i370])) 0 1]) * m368) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w323 = str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i319, i320] -> [i319 + i320]))) (\\[i321, i322] -> [i321 + i322])))))))) ; w324 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))) ; u325 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w323 * w324))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w336 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i326, i327, i328, i329, i330, i331] -> [ifH (sscalar -0.0 <=. negate (u325 !$ [i326, i327, 2 * i328 + i330, 2 * i329 + i331])) 0 1]) ; w337 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u325) (\\[i332, i333, i334, i335] -> [2 * i332 + i334, 2 * i333 + i335])) ; w338 = sreshape @[7,4,7,11,4] (w336 * w337) ; w347 = str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w338))))))) (\\[i339, i340, i341, i342] -> [kfromS (smaxIndex (w338 !$ [i342, i341, i339, i340])), i340, i339, i341, i342]))) (\\[i343, i344] -> [i343, i344, i343 + i344]))) (\\[i345, i346] -> [i345, i345 + i346, i346])))) ; u348 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w347 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w359 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354] -> [ifH (sscalar -0.0 <=. negate (u348 !$ [i349, i350, 2 * i351 + i353, 2 * i352 + i354])) 0 1]) ; w360 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u348) (\\[i355, i356, i357, i358] -> [2 * i355 + i357, 2 * i356 + i358])) ; w361 = sreshape @[7,4,3,5,4] (w359 * w360) ; t367 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w361))) (\\[i362, i363, i364, i365] -> [i362, i363, i364, i365, kfromS (smaxIndex (w361 !$ [i362, i363, i364, i365]))])))) (\\[i366] -> [i366, i366])))) ; m368 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t367) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m371 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i369, i370] -> [ifH (sscalar -0.0 <=. negate (m368 !$ [i369, i370])) 0 1]) ; t372 = str (sreplicate @10 (m371 * m368)) in ssum @5 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * t372) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w323 = str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i319, i320] -> [i319 + i320]))) (\\[i321, i322] -> [i321 + i322])))))))) ; w324 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))) ; u325 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w323 * w324))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w336 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i326, i327, i328, i329, i330, i331] -> [ifH (sscalar -0.0 <=. negate (u325 !$ [i326, i327, 2 * i328 + i330, 2 * i329 + i331])) 0 1]) ; w337 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u325) (\\[i332, i333, i334, i335] -> [2 * i332 + i334, 2 * i333 + i335])) ; w338 = sreshape @[7,4,7,11,4] (w336 * w337) ; w347 = str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w338))))))) (\\[i339, i340, i341, i342] -> [kfromS (smaxIndex (w338 !$ [i342, i341, i339, i340])), i340, i339, i341, i342]))) (\\[i343, i344] -> [i343, i344, i343 + i344]))) (\\[i345, i346] -> [i345, i345 + i346, i346])))) ; u348 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w347 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w359 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354] -> [ifH (sscalar -0.0 <=. negate (u348 !$ [i349, i350, 2 * i351 + i353, 2 * i352 + i354])) 0 1]) ; w360 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u348) (\\[i355, i356, i357, i358] -> [2 * i355 + i357, 2 * i356 + i358])) ; w361 = sreshape @[7,4,3,5,4] (w359 * w360) ; t367 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w361))) (\\[i362, i363, i364, i365] -> [i362, i363, i364, i365, kfromS (smaxIndex (w361 !$ [i362, i363, i364, i365]))])))) (\\[i366] -> [i366, i366])))) ; m368 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t367) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m371 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i369, i370] -> [ifH (sscalar -0.0 <=. negate (m368 !$ [i369, i370])) 0 1]) ; t372 = str (sreplicate @10 (m371 * m368)) ; m374 = m371 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * sreplicate @5 dret)) ; u384 = stranspose @[3,2,0,1] (sscatter (stranspose @[2,3,4,5,1,0] (w359 * sreshape @[7,4,3,5,2,2] (stranspose @[4,3,2,1,0] (ssum @7 (stranspose @[5,4,3,2,1,0] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (str (ssum @5 (str (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * sreplicate @60 m374)))) (\\[i375] -> [i375, i375])))) (\\[i376, i377, i378, i379] -> [i376, i377, i378, i379, kfromS (smaxIndex (w361 !$ [i376, i377, i378, i379]))]))))))) (\\[i380, i381, i382, i383] -> [2 * i380 + i382, 2 * i381 + i383])) ; w385 = sreshape @[7,4,7,11,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 u384)) ; u398 = stranspose @[3,2,0,1] (sscatter (stranspose @[2,3,4,5,1,0] (w336 * sreshape @[7,4,7,11,2,2] (stranspose @[4,3,2,1,0] (ssum @4 (ssum @7 (ssum @11 (stranspose @[5,6,7,4,3,2,1,0] (ssum @3 (stranspose @[8,4,3,2,1,0,7,6,5] (sscatter (stranspose @[2,6,5,3,7,0,4,1] (sscatter (stranspose @[4,6,3,0,5,1,2] (sscatter (stranspose @[2,5,0,1,3,4] (ssum @4 (str (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))) * w385)))) (\\[i386, i387] -> [i386, i386 + i387, i387]))) (\\[i388, i389] -> [i388, i389, i388 + i389]))) (\\[i390, i391, i392, i393] -> [kfromS (smaxIndex (w338 !$ [i393, i392, i390, i391])), i391, i390, i392, i393]))))))))))) (\\[i394, i395, i396, i397] -> [2 * i394 + i396, 2 * i395 + i397])) in tpair (tpair (tpair (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (ssum @7 (w323 * sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 u398)))))))))))) [0])) (ssum @23 (ssum @14 (stranspose @[1,2,0] (ssum @7 u398))))) (tpair (ssum @11 (str (ssum @7 (str (ssum @7 (w347 * w385)))))) (ssum @11 (ssum @7 (stranspose @[1,2,0] (ssum @7 u384)))))) (tpair (tpair (ssum @7 (stranspose @[2,1,0] (t367 * sreplicate @60 m374))) (ssum @7 (str m374))) (tpair (ssum @7 (stranspose @[2,1,0] (t372 * sreplicate @5 dret))) (ssum @7 (str dret))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> let w323 = sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i721, i722] -> [i721 + i722]))) (\\[i321, i322] -> [i321 + i322]) ; u325 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] w323)))))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w336 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i326, i327, i328, i329, i330, i331] -> [ifH (sscalar -0.0 <=. negate (u325 !$ [i326, i327, 2 * i328 + i330, 2 * i329 + i331])) 0 1]) ; w338 = sreshape @[7,4,7,11,4] (w336 * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u325) (\\[i332, i333, i334, i335] -> [2 * i332 + i334, 2 * i333 + i335]))) ; w347 = sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w338))))))) (\\[i698, i702, i703, i705] -> [kfromS (smaxIndex (w338 !$ [i705, i703, i698, i702])), i702, i698, i703, i705]))) (\\[i710, i712] -> [i710, i712, i710 + i712]))) (\\[i345, i346] -> [i345, i345 + i346, i346]) ; u348 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,1] w347)) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w359 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i349, i350, i351, i352, i353, i354] -> [ifH (sscalar -0.0 <=. negate (u348 !$ [i349, i350, 2 * i351 + i353, 2 * i352 + i354])) 0 1]) ; w361 = sreshape @[7,4,3,5,4] (w359 * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u348) (\\[i355, i356, i357, i358] -> [2 * i355 + i357, 2 * i356 + i358]))) ; m367 = sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w361))) (\\[i362, i363, i364, i365] -> [i362, i363, i364, i365, kfromS (smaxIndex (w361 !$ [i362, i363, i364, i365]))])))) (\\[i366] -> [i366, i366]) ; m368 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str m367) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m371 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i369, i370] -> [ifH (sscalar -0.0 <=. negate (m368 !$ [i369, i370])) 0 1]) ; m374 = m371 * smatmul2 (str (tproject1 (tproject2 (tproject2 u1)))) dret ; u384 = sscatter (stranspose @[2,3,4,5,1,0] w359 * stranspose @[2,3,4,5,1,0] (sreshape @[7,4,3,5,2,2] (ssum @7 (stranspose @[5,0,1,2,3,4] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (smatmul2 (str m374) (tproject1 (tproject1 (tproject2 u1)))) (\\[i375] -> [i375, i375])))) (\\[i376, i377, i378, i379] -> [i376, i377, i378, i379, kfromS (smaxIndex (w361 !$ [i376, i377, i378, i379]))])))))) (\\[i380, i381, i382, i383] -> [2 * i380 + i382, 2 * i381 + i383]) ; w385 = sreshape @[7,4,7,11,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 (stranspose @[3,2,0,1] u384))) ; u398 = sscatter (stranspose @[2,3,4,5,1,0] w336 * stranspose @[2,3,4,5,1,0] (sreshape @[7,4,7,11,2,2] (ssum @4 (ssum @7 (ssum @11 (ssum @3 (stranspose @[8,7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,6,5,3,7,0,4,1] (sscatter (stranspose @[4,6,3,0,5,1,2] (sscatter (ssdot1In (stranspose @[3,6,0,2,4,5,1] (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) (stranspose @[3,6,0,2,4,5,1] w385)) (\\[i386, i387] -> [i386, i386 + i387, i387]))) (\\[i388, i389] -> [i388, i389, i388 + i389]))) (\\[i390, i391, i392, i393] -> [kfromS (smaxIndex (w338 !$ [i393, i392, i390, i391])), i391, i390, i392, i393]))))))))) (\\[i394, i395, i396, i397] -> [2 * i394 + i396, 2 * i395 + i397]) in tpair (tpair (tpair (str (sreplicate @1 (ssum @23 (ssum @14 (ssdot1In (stranspose @[1,5,0,4,3,2] (sreplicate @4 (stranspose @[3,2,1,4,0] w323))) (stranspose @[1,0,2,4,5,3] (stranspose @[4,5,3,2,1,0] (sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 (stranspose @[3,2,0,1] u398)))) !$ [0, 0]))))))) (ssum @23 (ssum @14 (ssum @7 (stranspose @[3,0,1,2] u398))))) (tpair (ssum @11 (ssum @7 (ssdot1In (stranspose @[2,3,0,4,5,6,1] (sreplicate @4 (stranspose @[2,3,0,4,5,1] w347))) (stranspose @[2,3,1,4,5,6,0] w385)))) (ssum @11 (ssum @7 (ssum @7 (stranspose @[3,0,1,2] u384)))))) (tpair (tpair (smatmul2 m374 m367) (ssum @7 (str m374))) (tpair (smatmul2 dret (str m371 * str m368)) (ssum @7 (str dret))))"
