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
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let m5 = str (sreplicate @5 (scast (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1)))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v8 = ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 (sfromR dret)) ; v9 = scast v8 ; v10 = scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v9)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v10))) v10) (tpair (str m5 * str (sreplicate @4 v9)) v8)) (tpair (sreplicate @2 (scast (ssdot1In (str m5) (sfromR (tproject1 (tproject2 (tproject1 m1))))) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @5 (sfromR dret))) dret))"

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
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m16 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 0.0) + v13))) ; v20 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (str m16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m23 = str (sreplicate @2 (sconcrete (sreplicate [5] 0.0) + v20)) ; v24 = exp (ssdot1In (str m23) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum0 v24 ; v28 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * sdot0 v24 (sfromR dret)) + sreplicate @2 (recip x25) * sfromR dret) ; v29 = (v20 * (sconcrete (sreplicate [5] 1.0) + negate v20)) * ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v28) ; v30 = scast v29 ; v31 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v30)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v31))) v31) (tpair (str m16 * str (sreplicate @4 v30)) v29)) (tpair (str m23 * str (sreplicate @5 v28)) v28))"

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
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m16 = str (sreplicate @5 (scast (sconcrete (sreplicate [4] 0.0) + v13))) ; v20 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (str m16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m23 = str (sreplicate @2 (sconcrete (sreplicate [5] 0.0) + v20)) ; v24 = exp (ssdot1In (str m23) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x25 = ssum0 v24 ; x26 = recip x25 ; v30 = recip (sreplicate @2 x26 * v24) * sreplicate @2 (sscalar (-8.0) * sfromK dret) ; v31 = v24 * (sreplicate @2 (negate (recip (x25 * x25)) * sdot0 v24 v30) + sreplicate @2 x26 * v30) ; v32 = (v20 * (sconcrete (sreplicate [5] 1.0) + negate v20)) * ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v31) ; v33 = scast v32 ; v34 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v33)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v34))) v34) (tpair (str m16 * str (sreplicate @4 v33)) v32)) (tpair (str m23 * str (sreplicate @5 v31)) v31))"

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
    @?= "\\u1 -> rfromS (let u362 = ssum @4 (stranspose @[4,0,1,2,3] (sreshape @[5,1,7,9,4] (str (sreplicate @1 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [5,9,1,7] 7.0)) (\\[i643, i644] -> [i644 + i643]))) (\\[i647, i650] -> [i647 + i650]))) (\\[i356, i357] -> [i356 + i357])))) * sreplicate @5 (str (sreplicate @7 (str (sreplicate @9 (sgather (sfromR (tproject1 (tproject1 (tproject1 u1)))) (\\[i358, i359] -> [i358 + i359]))))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w381 = sreshape @[5,1,3,4,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i363, i364, i365, i366, i367, i368, i369, i370] -> [ifH (sscalar -0.0 <=. negate (u362 !$ [i363 + i367, i364 + i368, 2 * i365 + i369, 2 * i366 + i370])) 0 1]) * sgather u362 (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [i371 + i375, i372 + i376, 2 * i373 + i377, 2 * i374 + i378])) ; u401 = ssum @4 (stranspose @[4,0,1,2,3] (sreshape @[5,1,3,4,4] (str (sreplicate @1 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w381) (\\[i382, i383, i384, i385, i386, i387] -> [i383 + i382]))) (\\[i625, i627, i628, i629, i631] -> [kfromS (smaxIndex (w381 !$ [i631 + i629, i628, i625, i627])), i627, i625, i628, i629, i631]))) (\\[i636, i639] -> [i636, i639, i636 + i639]))) (\\[i395, i396] -> [i395, i395 + i396, i396])))) * sreplicate @5 (str (sreplicate @3 (str (sreplicate @4 (sgather (sfromR (tproject1 (tproject2 (tproject1 u1)))) (\\[i397, i398] -> [i397 + i398]))))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w420 = sreshape @[5,1,1,2,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i402, i403, i404, i405, i406, i407, i408, i409] -> [ifH (sscalar -0.0 <=. negate (u401 !$ [i402 + i406, i403 + i407, 2 * i404 + i408, 2 * i405 + i409])) 0 1]) * sgather u401 (\\[i410, i411, i412, i413, i414, i415, i416, i417] -> [i410 + i414, i411 + i415, 2 * i412 + i416, 2 * i413 + i417])) ; m427 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str (sgather (sreshape @[5,5,2] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @5 (stranspose @[4,3,2,1,0] w420))) (\\[i421, i422, i423, i424] -> [i421, i422, i423, i424, kfromS (smaxIndex (w420 !$ [i421, i422, i423, i424]))])))) (\\[i425] -> [i425, i425]))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) * sreplicate @10 (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i428] -> [ifH (sscalar -0.0 <=. negate (m427 !$ [0, i428])) 0 1]) * m427 !$ [0]) + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w360 = str (sreplicate @1 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [5,9,1,7] 7.0)) (\\[i352, i353] -> [i353 + i352]))) (\\[i354, i355] -> [i354 + i355]))) (\\[i356, i357] -> [i356 + i357])))) ; w361 = sreplicate @5 (str (sreplicate @7 (str (sreplicate @9 (sgather (sfromR (tproject1 (tproject1 (tproject1 u1)))) (\\[i358, i359] -> [i358 + i359])))))) ; u362 = ssum @4 (stranspose @[4,0,1,2,3] (sreshape @[5,1,7,9,4] (w360 * w361))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w379 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i363, i364, i365, i366, i367, i368, i369, i370] -> [ifH (sscalar -0.0 <=. negate (u362 !$ [i363 + i367, i364 + i368, 2 * i365 + i369, 2 * i366 + i370])) 0 1]) ; w380 = sgather u362 (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [i371 + i375, i372 + i376, 2 * i373 + i377, 2 * i374 + i378]) ; w381 = sreshape @[5,1,3,4,4] (w379 * w380) ; w399 = str (sreplicate @1 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w381) (\\[i382, i383, i384, i385, i386, i387] -> [i383 + i382]))) (\\[i388, i389, i390, i391, i392] -> [kfromS (smaxIndex (w381 !$ [i392 + i391, i390, i388, i389])), i389, i388, i390, i391, i392]))) (\\[i393, i394] -> [i393, i394, i393 + i394]))) (\\[i395, i396] -> [i395, i395 + i396, i396])))) ; w400 = sreplicate @5 (str (sreplicate @3 (str (sreplicate @4 (sgather (sfromR (tproject1 (tproject2 (tproject1 u1)))) (\\[i397, i398] -> [i397 + i398])))))) ; u401 = ssum @4 (stranspose @[4,0,1,2,3] (sreshape @[5,1,3,4,4] (w399 * w400))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w418 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i402, i403, i404, i405, i406, i407, i408, i409] -> [ifH (sscalar -0.0 <=. negate (u401 !$ [i402 + i406, i403 + i407, 2 * i404 + i408, 2 * i405 + i409])) 0 1]) ; w419 = sgather u401 (\\[i410, i411, i412, i413, i414, i415, i416, i417] -> [i410 + i414, i411 + i415, 2 * i412 + i416, 2 * i413 + i417]) ; w420 = sreshape @[5,1,1,2,4] (w418 * w419) ; t426 = str (sreplicate @1 (str (sgather (sreshape @[5,5,2] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @5 (stranspose @[4,3,2,1,0] w420))) (\\[i421, i422, i423, i424] -> [i421, i422, i423, i424, kfromS (smaxIndex (w420 !$ [i421, i422, i423, i424]))])))) (\\[i425] -> [i425, i425])))) ; m427 = ssum @2 (stranspose @[2,1,0] (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * t426) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v429 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i428] -> [ifH (sscalar -0.0 <=. negate (m427 !$ [0, i428])) 0 1]) ; v430 = m427 !$ [0] ; m431 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m432 = sreplicate @10 (v429 * v430) in rfromS (m431 * m432 + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w360 = str (sreplicate @1 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [5,9,1,7] 7.0)) (\\[i352, i353] -> [i353 + i352]))) (\\[i354, i355] -> [i354 + i355]))) (\\[i356, i357] -> [i356 + i357])))) ; w361 = sreplicate @5 (str (sreplicate @7 (str (sreplicate @9 (sgather (sfromR (tproject1 (tproject1 (tproject1 u1)))) (\\[i358, i359] -> [i358 + i359])))))) ; u362 = ssum @4 (stranspose @[4,0,1,2,3] (sreshape @[5,1,7,9,4] (w360 * w361))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w379 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i363, i364, i365, i366, i367, i368, i369, i370] -> [ifH (sscalar -0.0 <=. negate (u362 !$ [i363 + i367, i364 + i368, 2 * i365 + i369, 2 * i366 + i370])) 0 1]) ; w380 = sgather u362 (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [i371 + i375, i372 + i376, 2 * i373 + i377, 2 * i374 + i378]) ; w381 = sreshape @[5,1,3,4,4] (w379 * w380) ; w399 = str (sreplicate @1 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w381) (\\[i382, i383, i384, i385, i386, i387] -> [i383 + i382]))) (\\[i388, i389, i390, i391, i392] -> [kfromS (smaxIndex (w381 !$ [i392 + i391, i390, i388, i389])), i389, i388, i390, i391, i392]))) (\\[i393, i394] -> [i393, i394, i393 + i394]))) (\\[i395, i396] -> [i395, i395 + i396, i396])))) ; w400 = sreplicate @5 (str (sreplicate @3 (str (sreplicate @4 (sgather (sfromR (tproject1 (tproject2 (tproject1 u1)))) (\\[i397, i398] -> [i397 + i398])))))) ; u401 = ssum @4 (stranspose @[4,0,1,2,3] (sreshape @[5,1,3,4,4] (w399 * w400))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w418 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i402, i403, i404, i405, i406, i407, i408, i409] -> [ifH (sscalar -0.0 <=. negate (u401 !$ [i402 + i406, i403 + i407, 2 * i404 + i408, 2 * i405 + i409])) 0 1]) ; w419 = sgather u401 (\\[i410, i411, i412, i413, i414, i415, i416, i417] -> [i410 + i414, i411 + i415, 2 * i412 + i416, 2 * i413 + i417]) ; w420 = sreshape @[5,1,1,2,4] (w418 * w419) ; t426 = str (sreplicate @1 (str (sgather (sreshape @[5,5,2] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @5 (stranspose @[4,3,2,1,0] w420))) (\\[i421, i422, i423, i424] -> [i421, i422, i423, i424, kfromS (smaxIndex (w420 !$ [i421, i422, i423, i424]))])))) (\\[i425] -> [i425, i425])))) ; m427 = ssum @2 (stranspose @[2,1,0] (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * t426) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v429 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i428] -> [ifH (sscalar -0.0 <=. negate (m427 !$ [0, i428])) 0 1]) ; v430 = m427 !$ [0] ; m431 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m432 = sreplicate @10 (v429 * v430) ; m434 = soneHot (v429 * ssum @10 (m431 * sfromR dret)) [0] ; u448 = sscatter (w418 * sreshape @[5,1,1,2,1,1,2,2] (stranspose @[4,3,2,1,0] (ssum @5 (stranspose @[5,4,3,2,1,0] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[5,5,1,1,2] (sscatter (str (ssum @1 (str (stranspose @[2,1,0] (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * sreplicate @2 m434)))) (\\[i435] -> [i435, i435])))) (\\[i436, i437, i438, i439] -> [i436, i437, i438, i439, kfromS (smaxIndex (w420 !$ [i436, i437, i438, i439]))])))))) (\\[i440, i441, i442, i443, i444, i445, i446, i447] -> [i440 + i444, i441 + i445, 2 * i442 + i446, 2 * i443 + i447]) ; w449 = sreshape @[5,1,3,4,1,1,2,2] (stranspose @[1,2,3,4,0] (sreplicate @4 u448)) ; u475 = sscatter (w379 * sreshape @[5,1,3,4,1,1,2,2] (stranspose @[0,4,3,2,1] (sscatter (stranspose @[4,5,9,8,7,6,0,1,2,3] (sscatter (stranspose @[2,7,6,5,3,8,0,4,1] (sscatter (stranspose @[4,7,3,0,5,6,1,2] (sscatter (stranspose @[2,6,0,1,3,4,5] (ssum @1 (str (w400 * w449)))) (\\[i452, i453] -> [i452, i452 + i453, i453]))) (\\[i454, i455] -> [i454, i455, i454 + i455]))) (\\[i456, i457, i458, i459, i460] -> [kfromS (smaxIndex (w381 !$ [i460 + i459, i458, i456, i457])), i457, i456, i458, i459, i460]))) (\\[i461, i462, i463, i464, i465, i466] -> [i462 + i461])))) (\\[i467, i468, i469, i470, i471, i472, i473, i474] -> [i467 + i471, i468 + i472, 2 * i469 + i473, 2 * i470 + i474]) in tpair (tpair (tpair (rfromS (sscatter (ssum @9 (str (ssum @7 (str (ssum @5 (w360 * sreshape @[5,1,7,9,1,1,2,2] (stranspose @[1,2,3,4,0] (sreplicate @4 u475)))))))) (\\[i476, i477] -> [i476 + i477]))) (rfromS (ssum @9 (ssum @7 (stranspose @[1,2,0] (ssum @5 u475)))))) (tpair (rfromS (sscatter (ssum @4 (str (ssum @3 (str (ssum @5 (w399 * w449)))))) (\\[i450, i451] -> [i450 + i451]))) (rfromS (ssum @4 (ssum @3 (stranspose @[1,2,0] (ssum @5 u448))))))) (tpair (tpair (rfromS (ssum @5 (stranspose @[2,1,0] (t426 * sreplicate @2 m434)))) (rfromS (ssum @5 (str m434)))) (tpair (rfromS (str (soneHot (ssum @5 (str (m432 * sfromR dret))) [0]))) (rfromS (ssum @5 (str (sfromR dret))))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let w360 = str (sreplicate @1 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [5,9,1,7] 7.0)) (\\[i734, i735] -> [i735 + i734]))) (\\[i738, i741] -> [i738 + i741]))) (\\[i356, i357] -> [i356 + i357])))) ; u362 = ssum @4 (stranspose @[4,0,1,2,3] (sreshape @[5,1,7,9,4] (w360 * sreplicate @5 (str (sreplicate @7 (str (sreplicate @9 (sgather (sfromR (tproject1 (tproject1 (tproject1 u1)))) (\\[i358, i359] -> [i358 + i359]))))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w379 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i363, i364, i365, i366, i367, i368, i369, i370] -> [ifH (sscalar -0.0 <=. negate (u362 !$ [i363 + i367, i364 + i368, 2 * i365 + i369, 2 * i366 + i370])) 0 1]) ; w381 = sreshape @[5,1,3,4,4] (w379 * sgather u362 (\\[i371, i372, i373, i374, i375, i376, i377, i378] -> [i371 + i375, i372 + i376, 2 * i373 + i377, 2 * i374 + i378])) ; w399 = str (sreplicate @1 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w381) (\\[i382, i383, i384, i385, i386, i387] -> [i383 + i382]))) (\\[i716, i718, i719, i720, i722] -> [kfromS (smaxIndex (w381 !$ [i722 + i720, i719, i716, i718])), i718, i716, i719, i720, i722]))) (\\[i727, i730] -> [i727, i730, i727 + i730]))) (\\[i395, i396] -> [i395, i395 + i396, i396])))) ; w400 = str (sreplicate @3 (str (sreplicate @4 (sgather (sfromR (tproject1 (tproject2 (tproject1 u1)))) (\\[i397, i398] -> [i397 + i398]))))) ; u401 = ssum @4 (stranspose @[4,0,1,2,3] (sreshape @[5,1,3,4,4] (w399 * sreplicate @5 w400))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w418 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i402, i403, i404, i405, i406, i407, i408, i409] -> [ifH (sscalar -0.0 <=. negate (u401 !$ [i402 + i406, i403 + i407, 2 * i404 + i408, 2 * i405 + i409])) 0 1]) ; w420 = sreshape @[5,1,1,2,4] (w418 * sgather u401 (\\[i410, i411, i412, i413, i414, i415, i416, i417] -> [i410 + i414, i411 + i415, 2 * i412 + i416, 2 * i413 + i417])) ; t426 = str (sreplicate @1 (str (sgather (sreshape @[5,5,2] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @5 (stranspose @[4,3,2,1,0] w420))) (\\[i421, i422, i423, i424] -> [i421, i422, i423, i424, kfromS (smaxIndex (w420 !$ [i421, i422, i423, i424]))])))) (\\[i425] -> [i425, i425])))) ; m427 = ssdot1In (str (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1)))))) (stranspose @[1,2,0] t426) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v429 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i428] -> [ifH (sscalar -0.0 <=. negate (m427 !$ [0, i428])) 0 1]) ; v434 = v429 * ssdot1In (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) (str (sfromR dret)) ; u448 = sscatter (w418 * sreshape @[5,1,1,2,1,1,2,2] (ssum @5 (stranspose @[5,0,1,2,3,4] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[5,5,1,1,2] (sscatter (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0]) * str (sreplicate @2 v434)) (\\[i435] -> [i435, i435])))) (\\[i436, i437, i438, i439] -> [i436, i437, i438, i439, kfromS (smaxIndex (w420 !$ [i436, i437, i438, i439]))]))))) (\\[i440, i441, i442, i443, i444, i445, i446, i447] -> [i440 + i444, i441 + i445, 2 * i442 + i446, 2 * i443 + i447]) ; w449 = sreshape @[5,1,3,4,1,1,2,2] (stranspose @[1,2,3,4,0] (sreplicate @4 u448)) ; u475 = sscatter (w379 * sreshape @[5,1,3,4,1,1,2,2] (stranspose @[0,4,3,2,1] (sscatter (stranspose @[4,5,9,8,7,6,0,1,2,3] (sscatter (stranspose @[2,7,6,5,3,8,0,4,1] (sscatter (stranspose @[4,7,3,0,5,6,1,2] (sscatter (stranspose @[2,6,0,1,3,4,5] (sreplicate @5 (w400 !$ [0])) * stranspose @[2,6,0,1,3,4,5] (str w449 !$ [0])) (\\[i452, i453] -> [i452, i452 + i453, i453]))) (\\[i454, i455] -> [i454, i455, i454 + i455]))) (\\[i456, i457, i458, i459, i460] -> [kfromS (smaxIndex (w381 !$ [i460 + i459, i458, i456, i457])), i457, i456, i458, i459, i460]))) (\\[i461, i462, i463, i464, i465, i466] -> [i462 + i461])))) (\\[i467, i468, i469, i470, i471, i472, i473, i474] -> [i467 + i471, i468 + i472, 2 * i469 + i473, 2 * i470 + i474]) in tpair (tpair (tpair (sscatter (ssum @9 (ssum @7 (ssdot1In (stranspose @[2,3,1,4,5,6,7,0] w360) (stranspose @[2,3,1,4,5,6,7,0] (sreshape @[5,1,7,9,1,1,2,2] (stranspose @[1,2,3,4,0] (sreplicate @4 u475))))))) (\\[i476, i477] -> [i476 + i477])) (ssum @9 (ssum @7 (ssum @5 (stranspose @[0,2,3,1] u475))))) (tpair (sscatter (ssum @4 (ssum @3 (ssdot1In (stranspose @[2,3,1,4,5,6,7,0] w399) (stranspose @[2,3,1,4,5,6,7,0] w449)))) (\\[i450, i451] -> [i450 + i451])) (ssum @4 (ssum @3 (ssum @5 (stranspose @[0,2,3,1] u448)))))) (tpair (tpair (ssdot1In (str t426) (sreplicate @1 (sreplicate @2 v434))) (ssum @5 (str (sreplicate @1 v434)))) (tpair (str (sreplicate @1 (ssdot1In (sreplicate @10 (v429 * m427 !$ [0])) (sfromR dret)))) (ssum @5 (str (sfromR dret))))))"

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
    @?= "\\u1 -> rfromS (let u360 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [7,23,1,14] 7.0)) (\\[i623, i624] -> [i624 + i623]))) (\\[i627, i630] -> [i627 + i630]))) (\\[i354, i355] -> [i354 + i355])))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (sgather (sfromR (tproject1 (tproject1 (tproject1 u1)))) (\\[i356, i357] -> [i356 + i357]))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w379 = sreshape @[7,4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i361, i362, i363, i364, i365, i366, i367, i368] -> [ifH (sscalar -0.0 <=. negate (u360 !$ [i361 + i365, i362 + i366, 2 * i363 + i367, 2 * i364 + i368])) 0 1]) * sgather u360 (\\[i369, i370, i371, i372, i373, i374, i375, i376] -> [i369 + i373, i370 + i374, 2 * i371 + i375, 2 * i372 + i376])) ; u399 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w379) (\\[i380, i381, i382, i383, i384, i385] -> [i381 + i380]))) (\\[i605, i607, i608, i609, i611] -> [kfromS (smaxIndex (w379 !$ [i611 + i609, i608, i605, i607])), i607, i605, i608, i609, i611]))) (\\[i616, i619] -> [i616, i619, i616 + i619]))) (\\[i393, i394] -> [i393, i393 + i394, i394])))) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sgather (sfromR (tproject1 (tproject2 (tproject1 u1)))) (\\[i395, i396] -> [i395 + i396]))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w418 = sreshape @[7,4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifH (sscalar -0.0 <=. negate (u399 !$ [i400 + i404, i401 + i405, 2 * i402 + i406, 2 * i403 + i407])) 0 1]) * sgather u399 (\\[i408, i409, i410, i411, i412, i413, i414, i415] -> [i408 + i412, i409 + i413, 2 * i410 + i414, 2 * i411 + i415])) ; m425 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w418))) (\\[i419, i420, i421, i422] -> [i419, i420, i421, i422, kfromS (smaxIndex (w418 !$ [i419, i420, i421, i422]))])))) (\\[i423] -> [i423, i423]))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in smatmul2 (sfromR (tproject1 (tproject2 (tproject2 u1)))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i426, i427] -> [ifH (sscalar -0.0 <=. negate (m425 !$ [i426, i427])) 0 1]) * m425) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w358 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [7,23,1,14] 7.0)) (\\[i350, i351] -> [i351 + i350]))) (\\[i352, i353] -> [i352 + i353]))) (\\[i354, i355] -> [i354 + i355])))) ; w359 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (sgather (sfromR (tproject1 (tproject1 (tproject1 u1)))) (\\[i356, i357] -> [i356 + i357])))))) ; u360 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w358 * w359))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w377 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i361, i362, i363, i364, i365, i366, i367, i368] -> [ifH (sscalar -0.0 <=. negate (u360 !$ [i361 + i365, i362 + i366, 2 * i363 + i367, 2 * i364 + i368])) 0 1]) ; w378 = sgather u360 (\\[i369, i370, i371, i372, i373, i374, i375, i376] -> [i369 + i373, i370 + i374, 2 * i371 + i375, 2 * i372 + i376]) ; w379 = sreshape @[7,4,7,11,4] (w377 * w378) ; w397 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w379) (\\[i380, i381, i382, i383, i384, i385] -> [i381 + i380]))) (\\[i386, i387, i388, i389, i390] -> [kfromS (smaxIndex (w379 !$ [i390 + i389, i388, i386, i387])), i387, i386, i388, i389, i390]))) (\\[i391, i392] -> [i391, i392, i391 + i392]))) (\\[i393, i394] -> [i393, i393 + i394, i394])))) ; w398 = sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sgather (sfromR (tproject1 (tproject2 (tproject1 u1)))) (\\[i395, i396] -> [i395 + i396])))))) ; u399 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w397 * w398))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w416 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifH (sscalar -0.0 <=. negate (u399 !$ [i400 + i404, i401 + i405, 2 * i402 + i406, 2 * i403 + i407])) 0 1]) ; w417 = sgather u399 (\\[i408, i409, i410, i411, i412, i413, i414, i415] -> [i408 + i412, i409 + i413, 2 * i410 + i414, 2 * i411 + i415]) ; w418 = sreshape @[7,4,3,5,4] (w416 * w417) ; t424 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w418))) (\\[i419, i420, i421, i422] -> [i419, i420, i421, i422, kfromS (smaxIndex (w418 !$ [i419, i420, i421, i422]))])))) (\\[i423] -> [i423, i423])))) ; m425 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * t424) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m428 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i426, i427] -> [ifH (sscalar -0.0 <=. negate (m425 !$ [i426, i427])) 0 1]) ; t429 = str (sreplicate @10 (m428 * m425)) in rfromS (ssum @5 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * t429) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w358 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [7,23,1,14] 7.0)) (\\[i350, i351] -> [i351 + i350]))) (\\[i352, i353] -> [i352 + i353]))) (\\[i354, i355] -> [i354 + i355])))) ; w359 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (sgather (sfromR (tproject1 (tproject1 (tproject1 u1)))) (\\[i356, i357] -> [i356 + i357])))))) ; u360 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w358 * w359))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w377 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i361, i362, i363, i364, i365, i366, i367, i368] -> [ifH (sscalar -0.0 <=. negate (u360 !$ [i361 + i365, i362 + i366, 2 * i363 + i367, 2 * i364 + i368])) 0 1]) ; w378 = sgather u360 (\\[i369, i370, i371, i372, i373, i374, i375, i376] -> [i369 + i373, i370 + i374, 2 * i371 + i375, 2 * i372 + i376]) ; w379 = sreshape @[7,4,7,11,4] (w377 * w378) ; w397 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w379) (\\[i380, i381, i382, i383, i384, i385] -> [i381 + i380]))) (\\[i386, i387, i388, i389, i390] -> [kfromS (smaxIndex (w379 !$ [i390 + i389, i388, i386, i387])), i387, i386, i388, i389, i390]))) (\\[i391, i392] -> [i391, i392, i391 + i392]))) (\\[i393, i394] -> [i393, i393 + i394, i394])))) ; w398 = sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sgather (sfromR (tproject1 (tproject2 (tproject1 u1)))) (\\[i395, i396] -> [i395 + i396])))))) ; u399 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w397 * w398))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w416 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifH (sscalar -0.0 <=. negate (u399 !$ [i400 + i404, i401 + i405, 2 * i402 + i406, 2 * i403 + i407])) 0 1]) ; w417 = sgather u399 (\\[i408, i409, i410, i411, i412, i413, i414, i415] -> [i408 + i412, i409 + i413, 2 * i410 + i414, 2 * i411 + i415]) ; w418 = sreshape @[7,4,3,5,4] (w416 * w417) ; t424 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w418))) (\\[i419, i420, i421, i422] -> [i419, i420, i421, i422, kfromS (smaxIndex (w418 !$ [i419, i420, i421, i422]))])))) (\\[i423] -> [i423, i423])))) ; m425 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * t424) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m428 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i426, i427] -> [ifH (sscalar -0.0 <=. negate (m425 !$ [i426, i427])) 0 1]) ; t429 = str (sreplicate @10 (m428 * m425)) ; m431 = m428 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * sreplicate @5 (sfromR dret))) ; u445 = sscatter (w416 * sreshape @[7,4,3,5,1,1,2,2] (stranspose @[4,3,2,1,0] (ssum @7 (stranspose @[5,4,3,2,1,0] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (str (ssum @5 (str (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * sreplicate @60 m431)))) (\\[i432] -> [i432, i432])))) (\\[i433, i434, i435, i436] -> [i433, i434, i435, i436, kfromS (smaxIndex (w418 !$ [i433, i434, i435, i436]))])))))) (\\[i437, i438, i439, i440, i441, i442, i443, i444] -> [i437 + i441, i438 + i442, 2 * i439 + i443, 2 * i440 + i444]) ; w446 = sreshape @[7,4,7,11,1,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 u445)) ; u472 = sscatter (w377 * sreshape @[7,4,7,11,1,1,2,2] (stranspose @[0,4,3,2,1] (sscatter (stranspose @[4,5,9,8,7,6,0,1,2,3] (sscatter (stranspose @[2,7,6,5,3,8,0,4,1] (sscatter (stranspose @[4,7,3,0,5,6,1,2] (sscatter (stranspose @[2,6,0,1,3,4,5] (ssum @4 (str (w398 * w446)))) (\\[i449, i450] -> [i449, i449 + i450, i450]))) (\\[i451, i452] -> [i451, i452, i451 + i452]))) (\\[i453, i454, i455, i456, i457] -> [kfromS (smaxIndex (w379 !$ [i457 + i456, i455, i453, i454])), i454, i453, i455, i456, i457]))) (\\[i458, i459, i460, i461, i462, i463] -> [i459 + i458])))) (\\[i464, i465, i466, i467, i468, i469, i470, i471] -> [i464 + i468, i465 + i469, 2 * i466 + i470, 2 * i467 + i471]) in tpair (tpair (tpair (rfromS (sscatter (ssum @23 (str (ssum @14 (str (ssum @7 (w358 * sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 u472)))))))) (\\[i473, i474] -> [i473 + i474]))) (rfromS (ssum @23 (ssum @14 (stranspose @[1,2,0] (ssum @7 u472)))))) (tpair (rfromS (sscatter (ssum @11 (str (ssum @7 (str (ssum @7 (w397 * w446)))))) (\\[i447, i448] -> [i447 + i448]))) (rfromS (ssum @11 (ssum @7 (stranspose @[1,2,0] (ssum @7 u445))))))) (tpair (tpair (rfromS (ssum @7 (stranspose @[2,1,0] (t424 * sreplicate @60 m431)))) (rfromS (ssum @7 (str m431)))) (tpair (rfromS (ssum @7 (stranspose @[2,1,0] (t429 * sreplicate @5 (sfromR dret))))) (rfromS (ssum @7 (str (sfromR dret))))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let w358 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [7,23,1,14] 7.0)) (\\[i701, i702] -> [i702 + i701]))) (\\[i705, i708] -> [i705 + i708]))) (\\[i354, i355] -> [i354 + i355])))) ; u360 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w358 * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (sgather (sfromR (tproject1 (tproject1 (tproject1 u1)))) (\\[i356, i357] -> [i356 + i357]))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w377 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i361, i362, i363, i364, i365, i366, i367, i368] -> [ifH (sscalar -0.0 <=. negate (u360 !$ [i361 + i365, i362 + i366, 2 * i363 + i367, 2 * i364 + i368])) 0 1]) ; w379 = sreshape @[7,4,7,11,4] (w377 * sgather u360 (\\[i369, i370, i371, i372, i373, i374, i375, i376] -> [i369 + i373, i370 + i374, 2 * i371 + i375, 2 * i372 + i376])) ; w397 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w379) (\\[i380, i381, i382, i383, i384, i385] -> [i381 + i380]))) (\\[i683, i685, i686, i687, i689] -> [kfromS (smaxIndex (w379 !$ [i689 + i687, i686, i683, i685])), i685, i683, i686, i687, i689]))) (\\[i694, i697] -> [i694, i697, i694 + i697]))) (\\[i393, i394] -> [i393, i393 + i394, i394])))) ; w398 = str (sreplicate @7 (str (sreplicate @11 (sgather (sfromR (tproject1 (tproject2 (tproject1 u1)))) (\\[i395, i396] -> [i395 + i396]))))) ; u399 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w397 * sreplicate @7 w398))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w416 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifH (sscalar -0.0 <=. negate (u399 !$ [i400 + i404, i401 + i405, 2 * i402 + i406, 2 * i403 + i407])) 0 1]) ; w418 = sreshape @[7,4,3,5,4] (w416 * sgather u399 (\\[i408, i409, i410, i411, i412, i413, i414, i415] -> [i408 + i412, i409 + i413, 2 * i410 + i414, 2 * i411 + i415])) ; t424 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w418))) (\\[i419, i420, i421, i422] -> [i419, i420, i421, i422, kfromS (smaxIndex (w418 !$ [i419, i420, i421, i422]))])))) (\\[i423] -> [i423, i423])))) ; m425 = ssdot1In (str (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1)))))) (stranspose @[1,2,0] t424) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m428 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i426, i427] -> [ifH (sscalar -0.0 <=. negate (m425 !$ [i426, i427])) 0 1]) ; m431 = m428 * smatmul2 (str (sfromR (tproject1 (tproject2 (tproject2 u1))))) (sfromR dret) ; u445 = sscatter (w416 * sreshape @[7,4,3,5,1,1,2,2] (ssum @7 (stranspose @[5,0,1,2,3,4] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (smatmul2 (str m431) (sfromR (tproject1 (tproject1 (tproject2 u1))))) (\\[i432] -> [i432, i432])))) (\\[i433, i434, i435, i436] -> [i433, i434, i435, i436, kfromS (smaxIndex (w418 !$ [i433, i434, i435, i436]))]))))) (\\[i437, i438, i439, i440, i441, i442, i443, i444] -> [i437 + i441, i438 + i442, 2 * i439 + i443, 2 * i440 + i444]) ; w446 = sreshape @[7,4,7,11,1,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 u445)) ; u472 = sscatter (w377 * sreshape @[7,4,7,11,1,1,2,2] (stranspose @[0,4,3,2,1] (sscatter (stranspose @[4,5,9,8,7,6,0,1,2,3] (sscatter (stranspose @[2,7,6,5,3,8,0,4,1] (sscatter (stranspose @[4,7,3,0,5,6,1,2] (sscatter (ssdot1In (stranspose @[3,7,0,2,4,5,6,1] (sreplicate @7 w398)) (stranspose @[3,7,0,2,4,5,6,1] w446)) (\\[i449, i450] -> [i449, i449 + i450, i450]))) (\\[i451, i452] -> [i451, i452, i451 + i452]))) (\\[i453, i454, i455, i456, i457] -> [kfromS (smaxIndex (w379 !$ [i457 + i456, i455, i453, i454])), i454, i453, i455, i456, i457]))) (\\[i458, i459, i460, i461, i462, i463] -> [i459 + i458])))) (\\[i464, i465, i466, i467, i468, i469, i470, i471] -> [i464 + i468, i465 + i469, 2 * i466 + i470, 2 * i467 + i471]) in tpair (tpair (tpair (sscatter (ssum @23 (ssum @14 (ssdot1In (stranspose @[2,3,1,4,5,6,7,0] w358) (stranspose @[2,3,1,4,5,6,7,0] (sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 u472))))))) (\\[i473, i474] -> [i473 + i474])) (ssum @23 (ssum @14 (ssum @7 (stranspose @[0,2,3,1] u472))))) (tpair (sscatter (ssum @11 (ssum @7 (ssdot1In (stranspose @[2,3,1,4,5,6,7,0] w397) (stranspose @[2,3,1,4,5,6,7,0] w446)))) (\\[i447, i448] -> [i447 + i448])) (ssum @11 (ssum @7 (ssum @7 (stranspose @[0,2,3,1] u445)))))) (tpair (tpair (ssdot1In (str t424) (str (sreplicate @60 m431))) (ssum @7 (str m431))) (tpair (smatmul2 (sfromR dret) (str m428 * str m425)) (ssum @7 (str (sfromR dret))))))"

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
    @?= "\\u1 -> let u360 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [7,23,1,14] 7.0)) (\\[i623, i624] -> [i624 + i623]))) (\\[i627, i630] -> [i627 + i630]))) (\\[i354, i355] -> [i354 + i355])))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (sgather (tproject1 (tproject1 (tproject1 u1))) (\\[i356, i357] -> [i356 + i357]))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w379 = sreshape @[7,4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i361, i362, i363, i364, i365, i366, i367, i368] -> [ifH (sscalar -0.0 <=. negate (u360 !$ [i361 + i365, i362 + i366, 2 * i363 + i367, 2 * i364 + i368])) 0 1]) * sgather u360 (\\[i369, i370, i371, i372, i373, i374, i375, i376] -> [i369 + i373, i370 + i374, 2 * i371 + i375, 2 * i372 + i376])) ; u399 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w379) (\\[i380, i381, i382, i383, i384, i385] -> [i381 + i380]))) (\\[i605, i607, i608, i609, i611] -> [kfromS (smaxIndex (w379 !$ [i611 + i609, i608, i605, i607])), i607, i605, i608, i609, i611]))) (\\[i616, i619] -> [i616, i619, i616 + i619]))) (\\[i393, i394] -> [i393, i393 + i394, i394])))) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sgather (tproject1 (tproject2 (tproject1 u1))) (\\[i395, i396] -> [i395 + i396]))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w418 = sreshape @[7,4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifH (sscalar -0.0 <=. negate (u399 !$ [i400 + i404, i401 + i405, 2 * i402 + i406, 2 * i403 + i407])) 0 1]) * sgather u399 (\\[i408, i409, i410, i411, i412, i413, i414, i415] -> [i408 + i412, i409 + i413, 2 * i410 + i414, 2 * i411 + i415])) ; m425 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w418))) (\\[i419, i420, i421, i422] -> [i419, i420, i421, i422, kfromS (smaxIndex (w418 !$ [i419, i420, i421, i422]))])))) (\\[i423] -> [i423, i423]))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) in smatmul2 (tproject1 (tproject2 (tproject2 u1))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i426, i427] -> [ifH (sscalar -0.0 <=. negate (m425 !$ [i426, i427])) 0 1]) * m425) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w358 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [7,23,1,14] 7.0)) (\\[i350, i351] -> [i351 + i350]))) (\\[i352, i353] -> [i352 + i353]))) (\\[i354, i355] -> [i354 + i355])))) ; w359 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (sgather (tproject1 (tproject1 (tproject1 u1))) (\\[i356, i357] -> [i356 + i357])))))) ; u360 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w358 * w359))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w377 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i361, i362, i363, i364, i365, i366, i367, i368] -> [ifH (sscalar -0.0 <=. negate (u360 !$ [i361 + i365, i362 + i366, 2 * i363 + i367, 2 * i364 + i368])) 0 1]) ; w378 = sgather u360 (\\[i369, i370, i371, i372, i373, i374, i375, i376] -> [i369 + i373, i370 + i374, 2 * i371 + i375, 2 * i372 + i376]) ; w379 = sreshape @[7,4,7,11,4] (w377 * w378) ; w397 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w379) (\\[i380, i381, i382, i383, i384, i385] -> [i381 + i380]))) (\\[i386, i387, i388, i389, i390] -> [kfromS (smaxIndex (w379 !$ [i390 + i389, i388, i386, i387])), i387, i386, i388, i389, i390]))) (\\[i391, i392] -> [i391, i392, i391 + i392]))) (\\[i393, i394] -> [i393, i393 + i394, i394])))) ; w398 = sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sgather (tproject1 (tproject2 (tproject1 u1))) (\\[i395, i396] -> [i395 + i396])))))) ; u399 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w397 * w398))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w416 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifH (sscalar -0.0 <=. negate (u399 !$ [i400 + i404, i401 + i405, 2 * i402 + i406, 2 * i403 + i407])) 0 1]) ; w417 = sgather u399 (\\[i408, i409, i410, i411, i412, i413, i414, i415] -> [i408 + i412, i409 + i413, 2 * i410 + i414, 2 * i411 + i415]) ; w418 = sreshape @[7,4,3,5,4] (w416 * w417) ; t424 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w418))) (\\[i419, i420, i421, i422] -> [i419, i420, i421, i422, kfromS (smaxIndex (w418 !$ [i419, i420, i421, i422]))])))) (\\[i423] -> [i423, i423])))) ; m425 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t424) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m428 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i426, i427] -> [ifH (sscalar -0.0 <=. negate (m425 !$ [i426, i427])) 0 1]) ; t429 = str (sreplicate @10 (m428 * m425)) in ssum @5 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * t429) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w358 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [7,23,1,14] 7.0)) (\\[i350, i351] -> [i351 + i350]))) (\\[i352, i353] -> [i352 + i353]))) (\\[i354, i355] -> [i354 + i355])))) ; w359 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (sgather (tproject1 (tproject1 (tproject1 u1))) (\\[i356, i357] -> [i356 + i357])))))) ; u360 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w358 * w359))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w377 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i361, i362, i363, i364, i365, i366, i367, i368] -> [ifH (sscalar -0.0 <=. negate (u360 !$ [i361 + i365, i362 + i366, 2 * i363 + i367, 2 * i364 + i368])) 0 1]) ; w378 = sgather u360 (\\[i369, i370, i371, i372, i373, i374, i375, i376] -> [i369 + i373, i370 + i374, 2 * i371 + i375, 2 * i372 + i376]) ; w379 = sreshape @[7,4,7,11,4] (w377 * w378) ; w397 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w379) (\\[i380, i381, i382, i383, i384, i385] -> [i381 + i380]))) (\\[i386, i387, i388, i389, i390] -> [kfromS (smaxIndex (w379 !$ [i390 + i389, i388, i386, i387])), i387, i386, i388, i389, i390]))) (\\[i391, i392] -> [i391, i392, i391 + i392]))) (\\[i393, i394] -> [i393, i393 + i394, i394])))) ; w398 = sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sgather (tproject1 (tproject2 (tproject1 u1))) (\\[i395, i396] -> [i395 + i396])))))) ; u399 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w397 * w398))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w416 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifH (sscalar -0.0 <=. negate (u399 !$ [i400 + i404, i401 + i405, 2 * i402 + i406, 2 * i403 + i407])) 0 1]) ; w417 = sgather u399 (\\[i408, i409, i410, i411, i412, i413, i414, i415] -> [i408 + i412, i409 + i413, 2 * i410 + i414, 2 * i411 + i415]) ; w418 = sreshape @[7,4,3,5,4] (w416 * w417) ; t424 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w418))) (\\[i419, i420, i421, i422] -> [i419, i420, i421, i422, kfromS (smaxIndex (w418 !$ [i419, i420, i421, i422]))])))) (\\[i423] -> [i423, i423])))) ; m425 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t424) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m428 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i426, i427] -> [ifH (sscalar -0.0 <=. negate (m425 !$ [i426, i427])) 0 1]) ; t429 = str (sreplicate @10 (m428 * m425)) ; m431 = m428 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * sreplicate @5 dret)) ; u445 = sscatter (w416 * sreshape @[7,4,3,5,1,1,2,2] (stranspose @[4,3,2,1,0] (ssum @7 (stranspose @[5,4,3,2,1,0] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (str (ssum @5 (str (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * sreplicate @60 m431)))) (\\[i432] -> [i432, i432])))) (\\[i433, i434, i435, i436] -> [i433, i434, i435, i436, kfromS (smaxIndex (w418 !$ [i433, i434, i435, i436]))])))))) (\\[i437, i438, i439, i440, i441, i442, i443, i444] -> [i437 + i441, i438 + i442, 2 * i439 + i443, 2 * i440 + i444]) ; w446 = sreshape @[7,4,7,11,1,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 u445)) ; u472 = sscatter (w377 * sreshape @[7,4,7,11,1,1,2,2] (stranspose @[0,4,3,2,1] (sscatter (stranspose @[4,5,9,8,7,6,0,1,2,3] (sscatter (stranspose @[2,7,6,5,3,8,0,4,1] (sscatter (stranspose @[4,7,3,0,5,6,1,2] (sscatter (stranspose @[2,6,0,1,3,4,5] (ssum @4 (str (w398 * w446)))) (\\[i449, i450] -> [i449, i449 + i450, i450]))) (\\[i451, i452] -> [i451, i452, i451 + i452]))) (\\[i453, i454, i455, i456, i457] -> [kfromS (smaxIndex (w379 !$ [i457 + i456, i455, i453, i454])), i454, i453, i455, i456, i457]))) (\\[i458, i459, i460, i461, i462, i463] -> [i459 + i458])))) (\\[i464, i465, i466, i467, i468, i469, i470, i471] -> [i464 + i468, i465 + i469, 2 * i466 + i470, 2 * i467 + i471]) in tpair (tpair (tpair (sscatter (ssum @23 (str (ssum @14 (str (ssum @7 (w358 * sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 u472)))))))) (\\[i473, i474] -> [i473 + i474])) (ssum @23 (ssum @14 (stranspose @[1,2,0] (ssum @7 u472))))) (tpair (sscatter (ssum @11 (str (ssum @7 (str (ssum @7 (w397 * w446)))))) (\\[i447, i448] -> [i447 + i448])) (ssum @11 (ssum @7 (stranspose @[1,2,0] (ssum @7 u445)))))) (tpair (tpair (ssum @7 (stranspose @[2,1,0] (t424 * sreplicate @60 m431))) (ssum @7 (str m431))) (tpair (ssum @7 (stranspose @[2,1,0] (t429 * sreplicate @5 dret))) (ssum @7 (str dret))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> let w358 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[5,2,0,3,4,1] (sgather (stranspose @[4,1,0,3,2] (sgather (sconcrete (sreplicate [7,23,1,14] 7.0)) (\\[i701, i702] -> [i702 + i701]))) (\\[i705, i708] -> [i705 + i708]))) (\\[i354, i355] -> [i354 + i355])))) ; u360 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w358 * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (sgather (tproject1 (tproject1 (tproject1 u1))) (\\[i356, i357] -> [i356 + i357]))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w377 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i361, i362, i363, i364, i365, i366, i367, i368] -> [ifH (sscalar -0.0 <=. negate (u360 !$ [i361 + i365, i362 + i366, 2 * i363 + i367, 2 * i364 + i368])) 0 1]) ; w379 = sreshape @[7,4,7,11,4] (w377 * sgather u360 (\\[i369, i370, i371, i372, i373, i374, i375, i376] -> [i369 + i373, i370 + i374, 2 * i371 + i375, 2 * i372 + i376])) ; w397 = str (sreplicate @4 (stranspose @[2,3,0,4,5,6,1] (sgather (stranspose @[3,6,7,2,0,4,5,1] (sgather (stranspose @[6,8,0,4,7,3,2,1,5] (sgather (stranspose @[6,7,8,9,0,1,5,4,3,2] (sgather (stranspose @[0,4,3,2,1] w379) (\\[i380, i381, i382, i383, i384, i385] -> [i381 + i380]))) (\\[i683, i685, i686, i687, i689] -> [kfromS (smaxIndex (w379 !$ [i689 + i687, i686, i683, i685])), i685, i683, i686, i687, i689]))) (\\[i694, i697] -> [i694, i697, i694 + i697]))) (\\[i393, i394] -> [i393, i393 + i394, i394])))) ; w398 = str (sreplicate @7 (str (sreplicate @11 (sgather (tproject1 (tproject2 (tproject1 u1))) (\\[i395, i396] -> [i395 + i396]))))) ; u399 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w397 * sreplicate @7 w398))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w416 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i400, i401, i402, i403, i404, i405, i406, i407] -> [ifH (sscalar -0.0 <=. negate (u399 !$ [i400 + i404, i401 + i405, 2 * i402 + i406, 2 * i403 + i407])) 0 1]) ; w418 = sreshape @[7,4,3,5,4] (w416 * sgather u399 (\\[i408, i409, i410, i411, i412, i413, i414, i415] -> [i408 + i412, i409 + i413, 2 * i410 + i414, 2 * i411 + i415])) ; t424 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w418))) (\\[i419, i420, i421, i422] -> [i419, i420, i421, i422, kfromS (smaxIndex (w418 !$ [i419, i420, i421, i422]))])))) (\\[i423] -> [i423, i423])))) ; m425 = ssdot1In (str (sreplicate @7 (tproject1 (tproject1 (tproject2 u1))))) (stranspose @[1,2,0] t424) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m428 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i426, i427] -> [ifH (sscalar -0.0 <=. negate (m425 !$ [i426, i427])) 0 1]) ; m431 = m428 * smatmul2 (str (tproject1 (tproject2 (tproject2 u1)))) dret ; u445 = sscatter (w416 * sreshape @[7,4,3,5,1,1,2,2] (ssum @7 (stranspose @[5,0,1,2,3,4] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (smatmul2 (str m431) (tproject1 (tproject1 (tproject2 u1)))) (\\[i432] -> [i432, i432])))) (\\[i433, i434, i435, i436] -> [i433, i434, i435, i436, kfromS (smaxIndex (w418 !$ [i433, i434, i435, i436]))]))))) (\\[i437, i438, i439, i440, i441, i442, i443, i444] -> [i437 + i441, i438 + i442, 2 * i439 + i443, 2 * i440 + i444]) ; w446 = sreshape @[7,4,7,11,1,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 u445)) ; u472 = sscatter (w377 * sreshape @[7,4,7,11,1,1,2,2] (stranspose @[0,4,3,2,1] (sscatter (stranspose @[4,5,9,8,7,6,0,1,2,3] (sscatter (stranspose @[2,7,6,5,3,8,0,4,1] (sscatter (stranspose @[4,7,3,0,5,6,1,2] (sscatter (ssdot1In (stranspose @[3,7,0,2,4,5,6,1] (sreplicate @7 w398)) (stranspose @[3,7,0,2,4,5,6,1] w446)) (\\[i449, i450] -> [i449, i449 + i450, i450]))) (\\[i451, i452] -> [i451, i452, i451 + i452]))) (\\[i453, i454, i455, i456, i457] -> [kfromS (smaxIndex (w379 !$ [i457 + i456, i455, i453, i454])), i454, i453, i455, i456, i457]))) (\\[i458, i459, i460, i461, i462, i463] -> [i459 + i458])))) (\\[i464, i465, i466, i467, i468, i469, i470, i471] -> [i464 + i468, i465 + i469, 2 * i466 + i470, 2 * i467 + i471]) in tpair (tpair (tpair (sscatter (ssum @23 (ssum @14 (ssdot1In (stranspose @[2,3,1,4,5,6,7,0] w358) (stranspose @[2,3,1,4,5,6,7,0] (sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 u472))))))) (\\[i473, i474] -> [i473 + i474])) (ssum @23 (ssum @14 (ssum @7 (stranspose @[0,2,3,1] u472))))) (tpair (sscatter (ssum @11 (ssum @7 (ssdot1In (stranspose @[2,3,1,4,5,6,7,0] w397) (stranspose @[2,3,1,4,5,6,7,0] w446)))) (\\[i447, i448] -> [i447 + i448])) (ssum @11 (ssum @7 (ssum @7 (stranspose @[0,2,3,1] u445)))))) (tpair (tpair (ssdot1In (str t424) (str (sreplicate @60 m431))) (ssum @7 (str m431))) (tpair (smatmul2 dret (str m428 * str m425)) (ssum @7 (str dret))))"
