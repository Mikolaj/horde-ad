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
    @?= "\\v1 -> rfromS (let v15 = scast (recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1)))))) ; v19 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v15, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v15]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v22 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v19, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v19]) + tproject2 (tproject2 v1)) in sreplicate @10 (recip (ssum0 v22)) * v22)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\v1 -> let v9 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = sconcrete (sreplicate [3] 1.0) + v10 ; v12 = recip v11 ; v15 = scast v12 ; v16 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v15), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v15)])) + tproject2 (tproject2 (tproject1 v1)) ; v17 = exp (negate v16) ; v18 = sconcrete (sreplicate [4] 1.0) + v17 ; v19 = recip v18 ; v22 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v19), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v19)]) + tproject2 (tproject2 v1)) ; x23 = ssum @10 v22 ; v24 = sreplicate @10 (recip x23) in rfromS (v24 * v22)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret v1 -> let v9 = sfromVector (fromList [ssum @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @784 (sscalar 7.0)), ssum @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v10 = exp (negate v9) ; v11 = sconcrete (sreplicate [3] 1.0) + v10 ; v12 = recip v11 ; v13 = sconcrete (sreplicate [3] 1.0) + negate v12 ; v14 = v12 * v13 ; v15 = scast v12 ; v16 = scast (sfromVector (fromList [ssum @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v15), ssum @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v15), ssum @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v15)])) + tproject2 (tproject2 (tproject1 v1)) ; v17 = exp (negate v16) ; v18 = sconcrete (sreplicate [4] 1.0) + v17 ; v19 = recip v18 ; v20 = sconcrete (sreplicate [4] 1.0) + negate v19 ; v21 = v19 * v20 ; v22 = exp (sfromVector (fromList [ssum @4 (tproject1 (tproject1 (tproject2 v1)) * v19), ssum @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v19), ssum @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v19)]) + tproject2 (tproject2 v1)) ; x23 = ssum @10 v22 ; v24 = sreplicate @10 (recip x23) ; v26 = v22 * (sreplicate @10 (negate (recip (x23 * x23)) * ssum @10 (v22 * sfromR dret)) + v24 * sfromR dret) ; v27 = sreplicate @4 (v26 !$ [9]) ; v28 = sreplicate @4 (v26 !$ [8]) ; v29 = sreplicate @4 (v26 !$ [7]) ; v30 = sreplicate @4 (v26 !$ [6]) ; v31 = sreplicate @4 (v26 !$ [5]) ; v32 = sreplicate @4 (v26 !$ [4]) ; v33 = sreplicate @4 (v26 !$ [3]) ; v34 = sreplicate @4 (v26 !$ [2]) ; v35 = sreplicate @4 (v26 !$ [1]) ; v36 = sreplicate @4 (v26 !$ [0]) ; v37 = v21 * (tproject1 (tproject1 (tproject2 v1)) * v36 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v35 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v29 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v28 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v27))))))))) ; v38 = scast v37 ; v39 = sreplicate @3 (v38 !$ [3]) ; v40 = sreplicate @3 (v38 !$ [2]) ; v41 = sreplicate @3 (v38 !$ [1]) ; v42 = sreplicate @3 (v38 !$ [0]) ; v43 = v14 * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v42 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v41 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v40 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v39))) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v43 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v43 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v43 !$ [2])) Z0))) v43) (tpair (tpair (v15 * v42) (tpair (v15 * v41) (tpair (v15 * v40) (tpair (v15 * v39) Z0)))) v37)) (tpair (tpair (v19 * v36) (tpair (v19 * v35) (tpair (v19 * v34) (tpair (v19 * v33) (tpair (v19 * v32) (tpair (v19 * v31) (tpair (v19 * v30) (tpair (v19 * v29) (tpair (v19 * v28) (tpair (v19 * v27) Z0)))))))))) v26)"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret v1 -> let v12 = recip (sconcrete (sreplicate [3] 1.0) + exp (negate (sfromVector (fromList [sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject1 (tproject1 (tproject1 v1)))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))), sdot0 (sconcrete (sreplicate [784] 7.0)) (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))))])) + negate (tproject2 (tproject1 (tproject1 v1))))) ; v15 = scast v12 ; v19 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (scast (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v15, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v15, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v15]))) + negate (tproject2 (tproject2 (tproject1 v1))))) ; v22 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v19, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v19]) + tproject2 (tproject2 v1)) ; x23 = ssum0 v22 ; v26 = v22 * (sreplicate @10 (negate (recip (x23 * x23)) * sdot0 v22 (sfromR dret)) + sreplicate @10 (recip x23) * sfromR dret) ; x27 = v26 !$ [9] ; x28 = v26 !$ [8] ; x29 = v26 !$ [7] ; x30 = v26 !$ [6] ; x31 = v26 !$ [5] ; x32 = v26 !$ [4] ; x33 = v26 !$ [3] ; x34 = v26 !$ [2] ; x35 = v26 !$ [1] ; x36 = v26 !$ [0] ; v37 = (v19 * (sconcrete (sreplicate [4] 1.0) + negate v19)) * (tproject1 (tproject1 (tproject2 v1)) * sreplicate @4 x36 + (tproject1 (tproject2 (tproject1 (tproject2 v1))) * sreplicate @4 x35 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * sreplicate @4 x34 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * sreplicate @4 x33 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * sreplicate @4 x32 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * sreplicate @4 x31 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * sreplicate @4 x30 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * sreplicate @4 x29 + (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * sreplicate @4 x28 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * sreplicate @4 x27))))))))) ; v38 = scast v37 ; x39 = v38 !$ [3] ; x40 = v38 !$ [2] ; x41 = v38 !$ [1] ; x42 = v38 !$ [0] ; v43 = (v12 * (sconcrete (sreplicate [3] 1.0) + negate v12)) * scast (tproject1 (tproject1 (tproject2 (tproject1 v1))) * sreplicate @3 x42 + (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * sreplicate @3 x41 + (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * sreplicate @3 x40 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * sreplicate @3 x39))) in tpair (tpair (tpair (tpair (sreplicate @784 (sscalar 7.0 * v43 !$ [0])) (tpair (sreplicate @784 (sscalar 7.0 * v43 !$ [1])) (tpair (sreplicate @784 (sscalar 7.0 * v43 !$ [2])) Z0))) v43) (tpair (tpair (v15 * sreplicate @3 x42) (tpair (v15 * sreplicate @3 x41) (tpair (v15 * sreplicate @3 x40) (tpair (v15 * sreplicate @3 x39) Z0)))) v37)) (tpair (tpair (v19 * sreplicate @4 x36) (tpair (v19 * sreplicate @4 x35) (tpair (v19 * sreplicate @4 x34) (tpair (v19 * sreplicate @4 x33) (tpair (v19 * sreplicate @4 x32) (tpair (v19 * sreplicate @4 x31) (tpair (v19 * sreplicate @4 x30) (tpair (v19 * sreplicate @4 x29) (tpair (v19 * sreplicate @4 x28) (tpair (v19 * sreplicate @4 x27) Z0)))))))))) v26)"

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
    @?= "\\m1 -> rfromS (let v23 = exp (ssdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (sreplicate @5 (scast (recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in sreplicate @2 (recip (ssum0 v23)) * v23)"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; m16 = str (sreplicate @5 (scast v13)) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v23 = exp (ssum @5 (str (sreplicate @2 v20) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum @2 v23 ; v25 = sreplicate @2 (recip x24) in rfromS (v25 * v23)"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; v14 = sconcrete (sreplicate [4] 1.0) + negate v13 ; v15 = v13 * v14 ; m16 = str (sreplicate @5 (scast v13)) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v21 = sconcrete (sreplicate [5] 1.0) + negate v20 ; v22 = v20 * v21 ; v23 = exp (ssum @5 (str (sreplicate @2 v20) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum @2 v23 ; v25 = sreplicate @2 (recip x24) ; v27 = v23 * (sreplicate @2 (negate (recip (x24 * x24)) * ssum @2 (v23 * sfromR dret)) + v25 * sfromR dret) ; v28 = v22 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v27)) ; m29 = sreplicate @4 (scast v28) ; v30 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m29))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0) * v30)))) (rfromS v30)) (tpair (rfromS (str (m16 * m29))) (rfromS v28))) (tpair (rfromS (str (str (sreplicate @2 v20) * sreplicate @5 v27))) (rfromS v27))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v16 = scast v13 ; v20 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (sreplicate @5 v16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v23 = exp (ssdot1In (sreplicate @2 v20) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum0 v23 ; v27 = v23 * (sreplicate @2 (negate (recip (x24 * x24)) * sdot0 v23 (sfromR dret)) + sreplicate @2 (recip x24) * sfromR dret) ; v28 = (v20 * (sconcrete (sreplicate [5] 1.0) + negate v20)) * ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v27) ; v29 = scast v28 ; v30 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v29)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v30))) v30) (tpair (sreplicate @5 v16 * str (sreplicate @4 v29)) v28)) (tpair (sreplicate @2 v20 * str (sreplicate @5 v27)) v27))"

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
    @?= "\\m1 -> let v23 = exp (ssdot1In (sreplicate @2 (recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (sreplicate @5 (scast (recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1))))))))) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))))) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) in negate (kfromS (sdot0 (sconcrete (sreplicate [2] 8.0)) (log (sreplicate @2 (recip (ssum0 v23)) * v23))))"
  printArtifactPrimalPretty artifactRevnonLin
    @?= "\\m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; m16 = str (sreplicate @5 (scast v13)) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v23 = exp (ssum @5 (str (sreplicate @2 v20) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum @2 v23 ; v25 = sreplicate @2 (recip x24) ; v26 = v25 * v23 ; v27 = log v26 in negate (kfromS (ssum @2 (v27 * sreplicate @2 (sscalar 8.0))))"
  printArtifactPretty artifactRevnonLin
    @?= "\\dret m1 -> let v10 = ssum @3 (sreplicate @3 (sreplicate @4 (sscalar 7.0)) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v11 = exp (negate v10) ; v12 = sconcrete (sreplicate [4] 1.0) + v11 ; v13 = recip v12 ; v14 = sconcrete (sreplicate [4] 1.0) + negate v13 ; v15 = v13 * v14 ; m16 = str (sreplicate @5 (scast v13)) ; v17 = scast (ssum @4 (m16 * str (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v18 = exp (negate v17) ; v19 = sconcrete (sreplicate [5] 1.0) + v18 ; v20 = recip v19 ; v21 = sconcrete (sreplicate [5] 1.0) + negate v20 ; v22 = v20 * v21 ; v23 = exp (ssum @5 (str (sreplicate @2 v20) * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum @2 v23 ; v25 = sreplicate @2 (recip x24) ; v26 = v25 * v23 ; v29 = recip v26 * sreplicate @2 (sscalar 8.0 * sfromK ((-1.0) * dret)) ; v30 = v23 * (sreplicate @2 (negate (recip (x24 * x24)) * ssum @2 (v23 * v29)) + v25 * v29) ; v31 = v22 * ssum @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @5 v30)) ; m32 = sreplicate @4 (scast v31) ; v33 = v15 * scast (ssum @5 (str (str (sfromR (tproject1 (tproject2 (tproject1 m1)))) * m32))) in tpair (tpair (tpair (rfromS (str (sreplicate @3 (sreplicate @4 (sscalar 7.0) * v33)))) (rfromS v33)) (tpair (rfromS (str (m16 * m32))) (rfromS v31))) (tpair (rfromS (str (str (sreplicate @2 v20) * sreplicate @5 v30))) (rfromS v30))"
  printArtifactPretty (simplifyArtifact artifactRevnonLin)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let v13 = recip (sconcrete (sreplicate [4] 1.0) + exp (negate (ssdot1In (sconcrete (sreplicate [4,3] 7.0)) (sfromR (tproject1 (tproject1 (tproject1 m1))))) + negate (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v16 = scast v13 ; v20 = recip (sconcrete (sreplicate [5] 1.0) + exp (negate (scast (ssdot1In (sreplicate @5 v16) (sfromR (tproject1 (tproject2 (tproject1 m1)))))) + negate (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; v23 = exp (ssdot1In (sreplicate @2 v20) (sfromR (tproject1 (tproject2 m1))) + sfromR (tproject2 (tproject2 m1))) ; x24 = ssum0 v23 ; x25 = recip x24 ; v29 = recip (sreplicate @2 x25 * v23) * sreplicate @2 (sscalar (-8.0) * sfromK dret) ; v30 = v23 * (sreplicate @2 (negate (recip (x24 * x24)) * sdot0 v23 v29) + sreplicate @2 x25 * v29) ; v31 = (v20 * (sconcrete (sreplicate [5] 1.0) + negate v20)) * ssdot1In (str (sfromR (tproject1 (tproject2 m1)))) (sreplicate @5 v30) ; v32 = scast v31 ; v33 = (v13 * (sconcrete (sreplicate [4] 1.0) + negate v13)) * scast (ssdot1In (str (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @4 v32)) in tpair (tpair (tpair (str (sreplicate @3 (sconcrete (sreplicate [4] 7.0) * v33))) v33) (tpair (sreplicate @5 v16 * str (sreplicate @4 v32)) v31)) (tpair (sreplicate @2 v20 * str (sreplicate @5 v30)) v30))"

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
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar)) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let x18 = tanh (sscalar 7.0 * sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))) !$ [0, 0] + sfromR (tproject2 (tproject1 (tproject1 m1))) !$ [0]) ; x19 = sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))) !$ [0, 0] ; x21 = tanh (x19 * x18 + sfromR (tproject2 (tproject2 (tproject1 m1))) !$ [0]) ; x24 = (sscalar 1.0 + negate x21 * x21) * sdot0 (str (sfromR (tproject1 (tproject2 m1))) !$ [0]) (str (sfromR dret) !$ [0]) ; x25 = (sscalar 1.0 + negate x18 * x18) * (x19 * x24) in tpair (tpair (tpair (tpair (sreplicate @1 (sreplicate @1 (sscalar 7.0 * x25))) (sconcrete (sfromListLinear [1,1] [0.0]))) (sreplicate @1 x25)) (tpair (tpair (sreplicate @1 (sreplicate @1 (x18 * x24))) (sconcrete (sfromListLinear [1,1] [0.0]))) (sreplicate @1 x24))) (tpair (str (sreplicate @1 (sreplicate @10 x21 * str (sfromR dret) !$ [0]))) (str (sfromR dret) !$ [0])))"

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
    @?= "\\m1 -> rfromS (let m52 = sappend (tanh ((str (sreplicate @2 (ssdot1In (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 7.0)))) + ssdot1In (str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) (tanh ((str (sreplicate @2 (ssdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 (tanh ((ssdot1In (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 7.0)) + ssdot1In (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 0.0))) + sfromR (tproject2 (tproject1 (tproject1 m1)))))))) + ssdot1In (str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((str (sreplicate @2 (ssdot1In (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 7.0)))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (str (sgather (stranspose @[1,2,0] (sslice (SNat @0) (SNat @2) (str (sreplicate @2 m52)))) (\\[i53] -> [i53, i53])))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (str (sgather (stranspose @[1,2,0] (sslice (SNat @2) (SNat @2) (str (sreplicate @2 m52)))) (\\[i56] -> [i56, i56])))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let m49 = tanh ((str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * sreplicate @2 (sreplicate @2 (sscalar 7.0))))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v50 = tanh ((ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * sreplicate @2 (sreplicate @2 (sscalar 7.0))) + ssum @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * sreplicate @2 (sreplicate @2 (sscalar 0.0)))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m51 = tanh ((str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v50)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m52 = sappend m49 m51 ; t54 = stranspose @[2,1,0] (sreplicate @2 (sgather (stranspose @[1,2,0] (sslice (SNat @0) (SNat @2) (str (sreplicate @2 m52)))) (\\[i53] -> [i53, i53]))) ; m55 = tanh ((sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * t54)) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; t57 = stranspose @[2,0,1] (sreplicate @2 (sgather (stranspose @[1,2,0] (sslice (SNat @2) (SNat @2) (str (sreplicate @2 m52)))) (\\[i56] -> [i56, i56]))) ; m58 = tanh ((ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 m55)) + ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * t57)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) in rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * str (sreplicate @10 m58)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m49 = tanh ((str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * sreplicate @2 (sreplicate @2 (sscalar 7.0))))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v50 = tanh ((ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * sreplicate @2 (sreplicate @2 (sscalar 7.0))) + ssum @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) * sreplicate @2 (sreplicate @2 (sscalar 0.0)))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m51 = tanh ((str (sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * str (sreplicate @2 v50)))) + ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0))))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m52 = sappend m49 m51 ; t54 = stranspose @[2,1,0] (sreplicate @2 (sgather (stranspose @[1,2,0] (sslice (SNat @0) (SNat @2) (str (sreplicate @2 m52)))) (\\[i53] -> [i53, i53]))) ; m55 = tanh ((sreplicate @2 (ssum @2 (str (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) * sreplicate @2 (sreplicate @2 (sscalar 7.0)))) + ssum @2 (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * t54)) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; t57 = stranspose @[2,0,1] (sreplicate @2 (sgather (stranspose @[1,2,0] (sslice (SNat @2) (SNat @2) (str (sreplicate @2 m52)))) (\\[i56] -> [i56, i56]))) ; m58 = tanh ((ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * stranspose @[2,0,1] (sreplicate @2 m55)) + ssum @2 (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * t57)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m60 = (sconcrete (sreplicate [2,2] 1.0) + negate m58 * m58) * ssum @10 (str (stranspose @[2,1,0] (sreplicate @2 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @2 (sfromR dret))) ; m62 = (sconcrete (sreplicate [2,2] 1.0) + negate m55 * m55) * ssum @2 (stranspose @[1,2,0] (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m60)) ; m64 = ssum @2 (str (sappend (sconcrete (sfromListLinear [0,2,2] [])) (sappend (stranspose @[2,0,1] (sscatter (ssum @2 (stranspose @[2,1,0] (str (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) * sreplicate @2 m62))) (\\[i63] -> [i63, i63]))) (sconcrete (sreplicate [2,2,2] 0.0))))) + ssum @2 (str (sappend (sconcrete (sreplicate [2,2,2] 0.0)) (sappend (stranspose @[2,0,1] (sscatter (ssum @2 (stranspose @[1,2,0] (stranspose @[1,2,0] (sreplicate @2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) * sreplicate @2 m60))) (\\[i61] -> [i61, i61]))) (sconcrete (sfromListLinear [0,2,2] []))))) ; m65 = (sconcrete (sreplicate [2,2] 1.0) + negate m51 * m51) * sslice (SNat @2) (SNat @2) m64 ; m66 = sreplicate @2 (ssum @2 (str m65)) ; v67 = (sconcrete (sreplicate [2] 1.0) + negate v50 * v50) * ssum @2 (str (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) * m66)) ; m68 = (sconcrete (sreplicate [2,2] 1.0) + negate m49 * m49) * sslice (SNat @0) (SNat @2) m64 in tpair (tpair (tpair (tpair (rfromS (str (sreplicate @2 (sreplicate @2 (sscalar 7.0) * ssum @2 (str m68))) + (str (sreplicate @2 (sreplicate @2 (sscalar 7.0) * v67)) + str (sreplicate @2 (sreplicate @2 (sscalar 7.0) * ssum @2 m62))))) (rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)) * m68))) + (str (sreplicate @2 (sreplicate @2 (sscalar 0.0) * v67)) + str (ssum @2 (str (t54 * sreplicate @2 m62))))))) (rfromS (ssum @2 (str m68) + (v67 + ssum @2 m62)))) (tpair (tpair (rfromS (str (str (sreplicate @2 v50) * m66) + str (ssum @2 (stranspose @[2,0,1] (stranspose @[2,0,1] (sreplicate @2 m55) * sreplicate @2 m60))))) (rfromS (ssum @2 (stranspose @[2,1,0] (sreplicate @2 (sreplicate @2 (sreplicate @2 (sscalar 0.0)) * m65))) + str (ssum @2 (stranspose @[2,0,1] (t57 * sreplicate @2 m60)))))) (rfromS (ssum @2 (str m65) + ssum @2 (str m60))))) (tpair (rfromS (ssum @2 (stranspose @[2,1,0] (str (sreplicate @10 m58) * sreplicate @2 (sfromR dret))))) (rfromS (ssum @2 (str (sfromR dret)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar)) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @1) STKScalar))) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar))) (let m49 = tanh ((str (sreplicate @2 (ssdot1In (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 7.0)))) + ssdot1In (str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; v50 = tanh ((ssdot1In (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 7.0)) + ssdot1In (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 0.0))) + sfromR (tproject2 (tproject1 (tproject1 m1)))) ; m51 = tanh ((str (sreplicate @2 (ssdot1In (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (sreplicate @2 v50))) + ssdot1In (str (sreplicate @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))))) (sconcrete (sreplicate [2,2,2] 0.0))) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m52 = sappend m49 m51 ; m54 = sgather (stranspose @[1,2,0] (sslice (SNat @0) (SNat @2) (str (sreplicate @2 m52)))) (\\[i53] -> [i53, i53]) ; m55 = tanh ((sreplicate @2 (ssdot1In (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sreplicate [2,2] 7.0))) + smatmul2 m54 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))))) + sreplicate @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m57 = sgather (stranspose @[1,2,0] (sslice (SNat @2) (SNat @2) (str (sreplicate @2 m52)))) (\\[i56] -> [i56, i56]) ; m58 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (str m55) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (str m57)) + str (sreplicate @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m60 = (sconcrete (sreplicate [2,2] 1.0) + negate m58 * m58) * smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR dret) ; m62 = (sconcrete (sreplicate [2,2] 1.0) + negate m55 * m55) * smatmul2 (str m60) (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) ; m64 = ssum @2 (str (sappend (stranspose @[2,0,1] (sscatter (smatmul2 m62 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) (\\[i63] -> [i63, i63]))) (sconcrete (sreplicate [2,2,2] 0.0)))) + ssum @2 (str (sappend (sconcrete (sreplicate [2,2,2] 0.0)) (stranspose @[2,0,1] (sscatter (smatmul2 (str m60) (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) (\\[i61] -> [i61, i61]))))) ; m65 = (sconcrete (sreplicate [2,2] 1.0) + negate m51 * m51) * sslice (SNat @2) (SNat @2) m64 ; v66 = ssum @2 (str m65) ; v67 = (sconcrete (sreplicate [2] 1.0) + negate v50 * v50) * ssdot1In (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) (sreplicate @2 v66) ; m68 = (sconcrete (sreplicate [2,2] 1.0) + negate m49 * m49) * sslice (SNat @0) (SNat @2) m64 in tpair (tpair (tpair (tpair (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 (str m68))) + (str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * v67)) + str (sreplicate @2 (sconcrete (sreplicate [2] 7.0) * ssum @2 m62)))) (smatmul2 (str m62) m54)) (ssum @2 (str m68) + (v67 + ssum @2 m62))) (tpair (tpair (sreplicate @2 v50 * str (sreplicate @2 v66) + smatmul2 m60 m55) (smatmul2 m60 m57)) (ssum @2 (str m65) + ssum @2 (str m60)))) (tpair (smatmul2 (sfromR dret) (str m58)) (ssum @2 (str (sfromR dret)))))"

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
    @?= "\\u1 -> rfromS (let u269 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,7,9,4] (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [7,5,9] 7.0)) (\\[i485, i486] -> [i485 + i486]))) (\\[i265, i266] -> [i265 + i266])))))) * sreplicate @5 (sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; u281 = sreshape @[5,3,4,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i270, i271, i272, i273, i274] -> [ifH (sscalar -0.0 <=. negate (u269 !$ [i270, 0, 2 * i271 + i273, 2 * i272 + i274])) 0 1]) * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,3,0] u269 !$ [0]) (\\[i275, i276, i277, i278] -> [2 * i275 + i277, 2 * i276 + i278]))) ; u291 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,3,4,4] (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,4,5,2,0,1] (sgather (stranspose @[4,6,0,2,5,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[3,2,1,0] u281))))))) (\\[i468, i470, i472] -> [kfromS (smaxIndex (u281 !$ [i472, i468, i470])), i470, i468, i472]))) (\\[i477, i478] -> [i477, i478, i477 + i478]))) (\\[i287, i288] -> [i287, i287 + i288, i288])) * sreplicate @5 (sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0])))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; t300 = sreshape @[5,2,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i292, i293, i294, i295] -> [ifH (sscalar -0.0 <=. negate (u291 !$ [i292, 0, i294, 2 * i293 + i295])) 0 1]) * stranspose @[3,0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (stranspose @[1,2,3,0] u291 !$ [0]))) (\\[i296, i297] -> [2 * i296 + i297]))) ; m305 = sreplicate @1 (ssdot1In (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0])) (sreshape @[5,2] (str (sreplicate @1 (str (sreplicate @1 (sgather t300 (\\[i301, i302] -> [i301, i302, kfromS (smaxIndex (t300 !$ [i301, i302]))])))))))) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) * sreplicate @10 (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i306] -> [ifH (sscalar -0.0 <=. negate (m305 !$ [0, i306])) 0 1]) * m305 !$ [0]) + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w267 = stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [7,5,9] 7.0)) (\\[i263, i264] -> [i263 + i264]))) (\\[i265, i266] -> [i265 + i266])))))) ; w268 = sreplicate @5 (sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0]))))) ; u269 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,7,9,4] (w267 * w268))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w279 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i270, i271, i272, i273, i274] -> [ifH (sscalar -0.0 <=. negate (u269 !$ [i270, 0, 2 * i271 + i273, 2 * i272 + i274])) 0 1]) ; w280 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,3,0] u269 !$ [0]) (\\[i275, i276, i277, i278] -> [2 * i275 + i277, 2 * i276 + i278])) ; u281 = sreshape @[5,3,4,4] (w279 * w280) ; w289 = stranspose @[2,3,0,4,1] (sgather (stranspose @[3,4,5,2,0,1] (sgather (stranspose @[4,6,0,2,5,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[3,2,1,0] u281))))))) (\\[i282, i283, i284] -> [kfromS (smaxIndex (u281 !$ [i284, i282, i283])), i283, i282, i284]))) (\\[i285, i286] -> [i285, i286, i285 + i286]))) (\\[i287, i288] -> [i287, i287 + i288, i288])) ; w290 = sreplicate @5 (sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0]))) ; u291 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,3,4,4] (w289 * w290))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; u298 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i292, i293, i294, i295] -> [ifH (sscalar -0.0 <=. negate (u291 !$ [i292, 0, i294, 2 * i293 + i295])) 0 1]) ; u299 = stranspose @[3,0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (stranspose @[1,2,3,0] u291 !$ [0]))) (\\[i296, i297] -> [2 * i296 + i297])) ; t300 = sreshape @[5,2,4] (u298 * u299) ; m303 = str (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0])) ; m304 = str (sreshape @[5,2] (str (sreplicate @1 (str (sreplicate @1 (sgather t300 (\\[i301, i302] -> [i301, i302, kfromS (smaxIndex (t300 !$ [i301, i302]))]))))))) ; m305 = sreplicate @1 (ssum @2 (m303 * m304)) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v307 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i306] -> [ifH (sscalar -0.0 <=. negate (m305 !$ [0, i306])) 0 1]) ; v308 = m305 !$ [0] ; m309 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m310 = sreplicate @10 (v307 * v308) in rfromS (m309 * m310 + str (sreplicate @5 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w267 = stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [7,5,9] 7.0)) (\\[i263, i264] -> [i263 + i264]))) (\\[i265, i266] -> [i265 + i266])))))) ; w268 = sreplicate @5 (sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0]))))) ; u269 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,7,9,4] (w267 * w268))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w279 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i270, i271, i272, i273, i274] -> [ifH (sscalar -0.0 <=. negate (u269 !$ [i270, 0, 2 * i271 + i273, 2 * i272 + i274])) 0 1]) ; w280 = stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,3,0] u269 !$ [0]) (\\[i275, i276, i277, i278] -> [2 * i275 + i277, 2 * i276 + i278])) ; u281 = sreshape @[5,3,4,4] (w279 * w280) ; w289 = stranspose @[2,3,0,4,1] (sgather (stranspose @[3,4,5,2,0,1] (sgather (stranspose @[4,6,0,2,5,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[3,2,1,0] u281))))))) (\\[i282, i283, i284] -> [kfromS (smaxIndex (u281 !$ [i284, i282, i283])), i283, i282, i284]))) (\\[i285, i286] -> [i285, i286, i285 + i286]))) (\\[i287, i288] -> [i287, i287 + i288, i288])) ; w290 = sreplicate @5 (sreplicate @3 (sreplicate @4 (sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0]))) ; u291 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,3,4,4] (w289 * w290))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; u298 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i292, i293, i294, i295] -> [ifH (sscalar -0.0 <=. negate (u291 !$ [i292, 0, i294, 2 * i293 + i295])) 0 1]) ; u299 = stranspose @[3,0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (stranspose @[1,2,3,0] u291 !$ [0]))) (\\[i296, i297] -> [2 * i296 + i297])) ; t300 = sreshape @[5,2,4] (u298 * u299) ; m303 = str (sreplicate @5 (sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0])) ; m304 = str (sreshape @[5,2] (str (sreplicate @1 (str (sreplicate @1 (sgather t300 (\\[i301, i302] -> [i301, i302, kfromS (smaxIndex (t300 !$ [i301, i302]))]))))))) ; m305 = sreplicate @1 (ssum @2 (m303 * m304)) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v307 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i306] -> [ifH (sscalar -0.0 <=. negate (m305 !$ [0, i306])) 0 1]) ; v308 = m305 !$ [0] ; m309 = str (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) ; m310 = sreplicate @10 (v307 * v308) ; m312 = soneHot (v307 * ssum @10 (m309 * sfromR dret)) [0] ; u317 = stranspose @[3,0,1,2] (soneHot (sappend (sconcrete (sfromListLinear [0,4,5] [])) (sappend (str (sscatter (stranspose @[1,3,2,0] (u298 * sreshape @[5,2,2,2] (sscatter (ssum @1 (str (ssum @1 (str (sreshape @[5,1,1,2] (str (m303 * sreplicate @2 (ssum @1 m312)))))))) (\\[i313, i314] -> [i313, i314, kfromS (smaxIndex (t300 !$ [i313, i314]))])))) (\\[i315, i316] -> [2 * i315 + i316]))) (sconcrete (sreplicate [1,4,5] 0.0)))) [0]) ; w318 = sreshape @[5,3,4,2,2] (stranspose @[1,2,3,0] (sreplicate @4 (ssum @1 (str u317)))) ; u330 = stranspose @[3,0,1,2] (soneHot (sscatter (stranspose @[1,2,3,4,0] (w279 * sreshape @[5,3,4,2,2] (stranspose @[3,2,1,0] (ssum @2 (ssum @3 (ssum @4 (stranspose @[4,5,6,3,2,1,0] (ssum @2 (stranspose @[7,3,2,1,0,6,5,4] (sscatter (stranspose @[2,5,3,6,0,4,1] (sscatter (stranspose @[4,5,3,0,1,2] (sscatter (stranspose @[2,4,0,1,3] (w290 * w318)) (\\[i319, i320] -> [i319, i319 + i320, i320]))) (\\[i321, i322] -> [i321, i322, i321 + i322]))) (\\[i323, i324, i325] -> [kfromS (smaxIndex (u281 !$ [i325, i323, i324])), i324, i323, i325]))))))))))) (\\[i326, i327, i328, i329] -> [2 * i326 + i328, 2 * i327 + i329])) [0]) in tpair (tpair (tpair (rfromS (soneHot (ssum @1 (ssum @1 (ssum @9 (ssum @7 (ssum @5 (w267 * sreshape @[5,7,9,1,1,2,2] (stranspose @[1,2,3,0] (sreplicate @4 (ssum @1 (str u330)))))))))) [0, 0])) (rfromS (ssum @9 (ssum @7 (stranspose @[1,2,0] (ssum @5 u330)))))) (tpair (rfromS (soneHot (ssum @4 (ssum @3 (ssum @5 (w289 * w318)))) [0, 0])) (rfromS (ssum @4 (ssum @3 (stranspose @[1,2,0] (ssum @5 u317))))))) (tpair (tpair (rfromS (soneHot (ssum @5 (str (m304 * sreplicate @2 (ssum @1 m312)))) [0])) (rfromS (ssum @5 (str m312)))) (tpair (rfromS (str (soneHot (ssum @5 (str (m310 * sfromR dret))) [0]))) (rfromS (ssum @5 (str (sfromR dret))))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let w267 = sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [7,5,9] 7.0)) (\\[i571, i572] -> [i571 + i572]))) (\\[i265, i266] -> [i265 + i266]) ; u269 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,7,9,4] (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] w267)))) * sreplicate @5 (sreplicate @7 (sreplicate @9 (sreplicate @1 (sreplicate @1 (sfromR (tproject1 (tproject1 (tproject1 u1))) !$ [0, 0])))))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @9 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w279 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i270, i271, i272, i273, i274] -> [ifH (sscalar -0.0 <=. negate (u269 !$ [i270, 0, 2 * i271 + i273, 2 * i272 + i274])) 0 1]) ; u281 = sreshape @[5,3,4,4] (w279 * stranspose @[4,0,1,2,3] (sgather (stranspose @[1,2,3,0] u269 !$ [0]) (\\[i275, i276, i277, i278] -> [2 * i275 + i277, 2 * i276 + i278]))) ; w289 = sgather (stranspose @[3,4,5,2,0,1] (sgather (stranspose @[4,6,0,2,5,1,3] (sgather (stranspose @[4,3,2,1,7,6,5,0] (sreplicate @2 (stranspose @[6,5,4,3,0,1,2] (sreplicate @4 (sreplicate @3 (sreplicate @2 (stranspose @[3,2,1,0] u281))))))) (\\[i554, i556, i558] -> [kfromS (smaxIndex (u281 !$ [i558, i554, i556])), i556, i554, i558]))) (\\[i563, i564] -> [i563, i564, i563 + i564]))) (\\[i287, i288] -> [i287, i287 + i288, i288]) ; m290 = sfromR (tproject1 (tproject2 (tproject1 u1))) !$ [0, 0] ; u291 = str (sreplicate @1 (ssum @4 (stranspose @[3,0,1,2] (sreshape @[5,3,4,4] (stranspose @[2,3,0,4,1] w289 * sreplicate @5 (sreplicate @3 (sreplicate @4 m290))))))) + sreplicate @5 (stranspose @[2,0,1] (sreplicate @3 (sreplicate @4 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; u298 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i292, i293, i294, i295] -> [ifH (sscalar -0.0 <=. negate (u291 !$ [i292, 0, i294, 2 * i293 + i295])) 0 1]) ; t300 = sreshape @[5,2,4] (u298 * stranspose @[3,0,2,1] (sgather (str (sslice (SNat @0) (SNat @2) (stranspose @[1,2,3,0] u291 !$ [0]))) (\\[i296, i297] -> [2 * i296 + i297]))) ; v303 = sfromR (tproject1 (tproject1 (tproject2 u1))) !$ [0] ; m304 = sreshape @[5,2] (str (sreplicate @1 (str (sreplicate @1 (sgather t300 (\\[i301, i302] -> [i301, i302, kfromS (smaxIndex (t300 !$ [i301, i302]))])))))) ; m305 = sreplicate @1 (ssdot1In (sreplicate @5 v303) m304) + str (sreplicate @5 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; v307 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i306] -> [ifH (sscalar -0.0 <=. negate (m305 !$ [0, i306])) 0 1]) ; v312 = v307 * ssdot1In (sreplicate @5 (str (sfromR (tproject1 (tproject2 (tproject2 u1)))) !$ [0])) (str (sfromR dret)) ; t317 = sappend (str (sscatter (stranspose @[1,3,2,0] u298 * stranspose @[1,3,2,0] (sreshape @[5,2,2,2] (sscatter (stranspose @[1,2,0] (sreshape @[5,1,1,2] (sreplicate @5 v303 * str (sreplicate @2 v312))) !$ [0, 0]) (\\[i313, i314] -> [i313, i314, kfromS (smaxIndex (t300 !$ [i313, i314]))])))) (\\[i315, i316] -> [2 * i315 + i316]))) (sconcrete (sreplicate [1,4,5] 0.0)) ; w318 = sreshape @[5,3,4,2,2] (stranspose @[1,2,3,0] (sreplicate @4 (stranspose @[2,0,1] t317))) ; t330 = sscatter (stranspose @[1,2,3,4,0] w279 * stranspose @[1,2,3,4,0] (sreshape @[5,3,4,2,2] (ssum @2 (ssum @3 (ssum @4 (ssum @2 (stranspose @[7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,5,3,6,0,4,1] (sscatter (stranspose @[4,5,3,0,1,2] (sscatter (stranspose @[2,4,0,1,3] (sreplicate @5 (sreplicate @3 (sreplicate @4 m290))) * stranspose @[2,4,0,1,3] w318) (\\[i319, i320] -> [i319, i319 + i320, i320]))) (\\[i321, i322] -> [i321, i322, i321 + i322]))) (\\[i323, i324, i325] -> [kfromS (smaxIndex (u281 !$ [i325, i323, i324])), i324, i323, i325]))))))))) (\\[i326, i327, i328, i329] -> [2 * i326 + i328, 2 * i327 + i329]) in tpair (tpair (tpair (sreplicate @1 (sreplicate @1 (ssum @9 (ssum @7 (ssdot1In (stranspose @[3,0,4,1,2] w267) (stranspose @[3,4,1,2,5,6,0] (sreshape @[5,7,9,1,1,2,2] (stranspose @[1,2,3,0] (sreplicate @4 (stranspose @[2,0,1] t330)))) !$ [0, 0])))))) (ssum @9 (ssum @7 (ssum @5 (stranspose @[3,1,2,0] (sreplicate @1 t330)))))) (tpair (sreplicate @1 (sreplicate @1 (ssum @4 (ssum @3 (ssdot1In (stranspose @[3,0,4,1,2] w289) (stranspose @[1,2,3,4,0] w318)))))) (ssum @4 (ssum @3 (ssum @5 (stranspose @[3,1,2,0] (sreplicate @1 t317))))))) (tpair (tpair (sreplicate @1 (ssdot1In (str m304) (sreplicate @2 v312))) (ssum @5 (str (sreplicate @1 v312)))) (tpair (str (sreplicate @1 (ssdot1In (sreplicate @10 (v307 * m305 !$ [0])) (sfromR dret)))) (ssum @5 (str (sfromR dret))))))"

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
    @?= "\\u1 -> rfromS (let u328 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i597, i598] -> [i597 + i598]))) (\\[i324, i325] -> [i324 + i325])))))))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w341 = sreshape @[7,4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333, i334] -> [ifH (sscalar -0.0 <=. negate (u328 !$ [i329, i330, 2 * i331 + i333, 2 * i332 + i334])) 0 1]) * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u328) (\\[i335, i336, i337, i338] -> [2 * i335 + i337, 2 * i336 + i338]))) ; u351 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w341))))))) (\\[i576, i580, i581, i583] -> [kfromS (smaxIndex (w341 !$ [i583, i581, i576, i580])), i580, i576, i581, i583]))) (\\[i588, i590] -> [i588, i590, i588 + i590]))) (\\[i348, i349] -> [i348, i348 + i349, i349])))) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w364 = sreshape @[7,4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i352, i353, i354, i355, i356, i357] -> [ifH (sscalar -0.0 <=. negate (u351 !$ [i352, i353, 2 * i354 + i356, 2 * i355 + i357])) 0 1]) * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u351) (\\[i358, i359, i360, i361] -> [2 * i358 + i360, 2 * i359 + i361]))) ; m371 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w364))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, kfromS (smaxIndex (w364 !$ [i365, i366, i367, i368]))])))) (\\[i369] -> [i369, i369]))) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) in smatmul2 (sfromR (tproject1 (tproject2 (tproject2 u1)))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i372, i373] -> [ifH (sscalar -0.0 <=. negate (m371 !$ [i372, i373])) 0 1]) * m371) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w326 = str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i322, i323] -> [i322 + i323]))) (\\[i324, i325] -> [i324 + i325])))))))) ; w327 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))) ; u328 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w326 * w327))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w339 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333, i334] -> [ifH (sscalar -0.0 <=. negate (u328 !$ [i329, i330, 2 * i331 + i333, 2 * i332 + i334])) 0 1]) ; w340 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u328) (\\[i335, i336, i337, i338] -> [2 * i335 + i337, 2 * i336 + i338])) ; w341 = sreshape @[7,4,7,11,4] (w339 * w340) ; w350 = str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w341))))))) (\\[i342, i343, i344, i345] -> [kfromS (smaxIndex (w341 !$ [i345, i344, i342, i343])), i343, i342, i344, i345]))) (\\[i346, i347] -> [i346, i347, i346 + i347]))) (\\[i348, i349] -> [i348, i348 + i349, i349])))) ; u351 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w350 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w362 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i352, i353, i354, i355, i356, i357] -> [ifH (sscalar -0.0 <=. negate (u351 !$ [i352, i353, 2 * i354 + i356, 2 * i355 + i357])) 0 1]) ; w363 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u351) (\\[i358, i359, i360, i361] -> [2 * i358 + i360, 2 * i359 + i361])) ; w364 = sreshape @[7,4,3,5,4] (w362 * w363) ; t370 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w364))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, kfromS (smaxIndex (w364 !$ [i365, i366, i367, i368]))])))) (\\[i369] -> [i369, i369])))) ; m371 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * t370) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m374 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i372, i373] -> [ifH (sscalar -0.0 <=. negate (m371 !$ [i372, i373])) 0 1]) ; t375 = str (sreplicate @10 (m374 * m371)) in rfromS (ssum @5 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * t375) + str (sreplicate @7 (sfromR (tproject2 (tproject2 (tproject2 u1))))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w326 = str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i322, i323] -> [i322 + i323]))) (\\[i324, i325] -> [i324 + i325])))))))) ; w327 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0]))))))))) ; u328 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w326 * w327))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w339 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333, i334] -> [ifH (sscalar -0.0 <=. negate (u328 !$ [i329, i330, 2 * i331 + i333, 2 * i332 + i334])) 0 1]) ; w340 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u328) (\\[i335, i336, i337, i338] -> [2 * i335 + i337, 2 * i336 + i338])) ; w341 = sreshape @[7,4,7,11,4] (w339 * w340) ; w350 = str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w341))))))) (\\[i342, i343, i344, i345] -> [kfromS (smaxIndex (w341 !$ [i345, i344, i342, i343])), i343, i342, i344, i345]))) (\\[i346, i347] -> [i346, i347, i346 + i347]))) (\\[i348, i349] -> [i348, i348 + i349, i349])))) ; u351 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w350 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w362 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i352, i353, i354, i355, i356, i357] -> [ifH (sscalar -0.0 <=. negate (u351 !$ [i352, i353, 2 * i354 + i356, 2 * i355 + i357])) 0 1]) ; w363 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u351) (\\[i358, i359, i360, i361] -> [2 * i358 + i360, 2 * i359 + i361])) ; w364 = sreshape @[7,4,3,5,4] (w362 * w363) ; t370 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w364))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, kfromS (smaxIndex (w364 !$ [i365, i366, i367, i368]))])))) (\\[i369] -> [i369, i369])))) ; m371 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * t370) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m374 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i372, i373] -> [ifH (sscalar -0.0 <=. negate (m371 !$ [i372, i373])) 0 1]) ; t375 = str (sreplicate @10 (m374 * m371)) ; m377 = m374 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject2 (tproject2 u1))))) * sreplicate @5 (sfromR dret))) ; u387 = stranspose @[3,2,0,1] (sscatter (stranspose @[2,3,4,5,1,0] (w362 * sreshape @[7,4,3,5,2,2] (stranspose @[4,3,2,1,0] (ssum @7 (stranspose @[5,4,3,2,1,0] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (str (ssum @5 (str (stranspose @[2,1,0] (sreplicate @7 (sfromR (tproject1 (tproject1 (tproject2 u1))))) * sreplicate @60 m377)))) (\\[i378] -> [i378, i378])))) (\\[i379, i380, i381, i382] -> [i379, i380, i381, i382, kfromS (smaxIndex (w364 !$ [i379, i380, i381, i382]))]))))))) (\\[i383, i384, i385, i386] -> [2 * i383 + i385, 2 * i384 + i386])) ; w388 = sreshape @[7,4,7,11,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 u387)) ; u401 = stranspose @[3,2,0,1] (sscatter (stranspose @[2,3,4,5,1,0] (w339 * sreshape @[7,4,7,11,2,2] (stranspose @[4,3,2,1,0] (ssum @4 (ssum @7 (ssum @11 (stranspose @[5,6,7,4,3,2,1,0] (ssum @3 (stranspose @[8,4,3,2,1,0,7,6,5] (sscatter (stranspose @[2,6,5,3,7,0,4,1] (sscatter (stranspose @[4,6,3,0,5,1,2] (sscatter (stranspose @[2,5,0,1,3,4] (ssum @4 (str (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))) * w388)))) (\\[i389, i390] -> [i389, i389 + i390, i390]))) (\\[i391, i392] -> [i391, i392, i391 + i392]))) (\\[i393, i394, i395, i396] -> [kfromS (smaxIndex (w341 !$ [i396, i395, i393, i394])), i394, i393, i395, i396]))))))))))) (\\[i397, i398, i399, i400] -> [2 * i397 + i399, 2 * i398 + i400])) in tpair (tpair (tpair (rfromS (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (ssum @7 (w326 * sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 u401)))))))))))) [0]))) (rfromS (ssum @23 (ssum @14 (stranspose @[1,2,0] (ssum @7 u401)))))) (tpair (rfromS (ssum @11 (str (ssum @7 (str (ssum @7 (w350 * w388))))))) (rfromS (ssum @11 (ssum @7 (stranspose @[1,2,0] (ssum @7 u387))))))) (tpair (tpair (rfromS (ssum @7 (stranspose @[2,1,0] (t370 * sreplicate @60 m377)))) (rfromS (ssum @7 (str m377)))) (tpair (rfromS (ssum @7 (stranspose @[2,1,0] (t375 * sreplicate @5 (sfromR dret))))) (rfromS (ssum @7 (str (sfromR dret))))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> tfromS (STKProduct (STKProduct (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @4) STKScalar) (STKR (SNat @1) STKScalar))) (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)))) (let w326 = sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i710, i711] -> [i710 + i711]))) (\\[i324, i325] -> [i324 + i325]) ; u328 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] w326)))))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (sfromR (tproject1 (tproject1 (tproject1 u1)))) !$ [0])))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (sfromR (tproject2 (tproject1 (tproject1 u1))))))) ; w339 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333, i334] -> [ifH (sscalar -0.0 <=. negate (u328 !$ [i329, i330, 2 * i331 + i333, 2 * i332 + i334])) 0 1]) ; w341 = sreshape @[7,4,7,11,4] (w339 * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u328) (\\[i335, i336, i337, i338] -> [2 * i335 + i337, 2 * i336 + i338]))) ; w350 = sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w341))))))) (\\[i687, i691, i692, i694] -> [kfromS (smaxIndex (w341 !$ [i694, i692, i687, i691])), i691, i687, i692, i694]))) (\\[i699, i701] -> [i699, i701, i699 + i701]))) (\\[i348, i349] -> [i348, i348 + i349, i349]) ; u351 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,1] w350)) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (sfromR (tproject2 (tproject2 (tproject1 u1))))))) ; w362 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i352, i353, i354, i355, i356, i357] -> [ifH (sscalar -0.0 <=. negate (u351 !$ [i352, i353, 2 * i354 + i356, 2 * i355 + i357])) 0 1]) ; w364 = sreshape @[7,4,3,5,4] (w362 * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u351) (\\[i358, i359, i360, i361] -> [2 * i358 + i360, 2 * i359 + i361]))) ; m370 = sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w364))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, kfromS (smaxIndex (w364 !$ [i365, i366, i367, i368]))])))) (\\[i369] -> [i369, i369]) ; m371 = smatmul2 (sfromR (tproject1 (tproject1 (tproject2 u1)))) (str m370) + str (sreplicate @7 (sfromR (tproject2 (tproject1 (tproject2 u1))))) ; m374 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i372, i373] -> [ifH (sscalar -0.0 <=. negate (m371 !$ [i372, i373])) 0 1]) ; m377 = m374 * smatmul2 (str (sfromR (tproject1 (tproject2 (tproject2 u1))))) (sfromR dret) ; u387 = sscatter (stranspose @[2,3,4,5,1,0] w362 * stranspose @[2,3,4,5,1,0] (sreshape @[7,4,3,5,2,2] (ssum @7 (stranspose @[5,0,1,2,3,4] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (smatmul2 (str m377) (sfromR (tproject1 (tproject1 (tproject2 u1))))) (\\[i378] -> [i378, i378])))) (\\[i379, i380, i381, i382] -> [i379, i380, i381, i382, kfromS (smaxIndex (w364 !$ [i379, i380, i381, i382]))])))))) (\\[i383, i384, i385, i386] -> [2 * i383 + i385, 2 * i384 + i386]) ; w388 = sreshape @[7,4,7,11,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 (stranspose @[3,2,0,1] u387))) ; u401 = sscatter (stranspose @[2,3,4,5,1,0] w339 * stranspose @[2,3,4,5,1,0] (sreshape @[7,4,7,11,2,2] (ssum @4 (ssum @7 (ssum @11 (ssum @3 (stranspose @[8,7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,6,5,3,7,0,4,1] (sscatter (stranspose @[4,6,3,0,5,1,2] (sscatter (ssdot1In (stranspose @[3,6,0,2,4,5,1] (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (sfromR (tproject1 (tproject2 (tproject1 u1)))))))))) (stranspose @[3,6,0,2,4,5,1] w388)) (\\[i389, i390] -> [i389, i389 + i390, i390]))) (\\[i391, i392] -> [i391, i392, i391 + i392]))) (\\[i393, i394, i395, i396] -> [kfromS (smaxIndex (w341 !$ [i396, i395, i393, i394])), i394, i393, i395, i396]))))))))) (\\[i397, i398, i399, i400] -> [2 * i397 + i399, 2 * i398 + i400]) in tpair (tpair (tpair (str (sreplicate @1 (ssum @23 (ssum @14 (ssdot1In (stranspose @[1,5,0,4,3,2] (sreplicate @4 (stranspose @[3,2,1,4,0] w326))) (stranspose @[4,5,2,3,1,6,7,0] (sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 (stranspose @[3,2,0,1] u401)))) !$ [0, 0])))))) (ssum @23 (ssum @14 (ssum @7 (stranspose @[3,0,1,2] u401))))) (tpair (ssum @11 (ssum @7 (ssdot1In (stranspose @[2,3,0,4,5,6,1] (sreplicate @4 (stranspose @[2,3,0,4,5,1] w350))) (stranspose @[2,3,1,4,5,6,0] w388)))) (ssum @11 (ssum @7 (ssum @7 (stranspose @[3,0,1,2] u387)))))) (tpair (tpair (smatmul2 m377 m370) (ssum @7 (str m377))) (tpair (smatmul2 (sfromR dret) (str m374 * str m371)) (ssum @7 (str (sfromR dret))))))"

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
    @?= "\\u1 -> let u328 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i597, i598] -> [i597 + i598]))) (\\[i324, i325] -> [i324 + i325])))))))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w341 = sreshape @[7,4,7,11,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333, i334] -> [ifH (sscalar -0.0 <=. negate (u328 !$ [i329, i330, 2 * i331 + i333, 2 * i332 + i334])) 0 1]) * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u328) (\\[i335, i336, i337, i338] -> [2 * i335 + i337, 2 * i336 + i338]))) ; u351 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w341))))))) (\\[i576, i580, i581, i583] -> [kfromS (smaxIndex (w341 !$ [i583, i581, i576, i580])), i580, i576, i581, i583]))) (\\[i588, i590] -> [i588, i590, i588 + i590]))) (\\[i348, i349] -> [i348, i348 + i349, i349])))) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w364 = sreshape @[7,4,3,5,4] (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i352, i353, i354, i355, i356, i357] -> [ifH (sscalar -0.0 <=. negate (u351 !$ [i352, i353, 2 * i354 + i356, 2 * i355 + i357])) 0 1]) * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u351) (\\[i358, i359, i360, i361] -> [2 * i358 + i360, 2 * i359 + i361]))) ; m371 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w364))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, kfromS (smaxIndex (w364 !$ [i365, i366, i367, i368]))])))) (\\[i369] -> [i369, i369]))) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) in smatmul2 (tproject1 (tproject2 (tproject2 u1))) (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i372, i373] -> [ifH (sscalar -0.0 <=. negate (m371 !$ [i372, i373])) 0 1]) * m371) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\u1 -> let w326 = str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i322, i323] -> [i322 + i323]))) (\\[i324, i325] -> [i324 + i325])))))))) ; w327 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))) ; u328 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w326 * w327))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w339 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333, i334] -> [ifH (sscalar -0.0 <=. negate (u328 !$ [i329, i330, 2 * i331 + i333, 2 * i332 + i334])) 0 1]) ; w340 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u328) (\\[i335, i336, i337, i338] -> [2 * i335 + i337, 2 * i336 + i338])) ; w341 = sreshape @[7,4,7,11,4] (w339 * w340) ; w350 = str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w341))))))) (\\[i342, i343, i344, i345] -> [kfromS (smaxIndex (w341 !$ [i345, i344, i342, i343])), i343, i342, i344, i345]))) (\\[i346, i347] -> [i346, i347, i346 + i347]))) (\\[i348, i349] -> [i348, i348 + i349, i349])))) ; u351 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w350 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w362 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i352, i353, i354, i355, i356, i357] -> [ifH (sscalar -0.0 <=. negate (u351 !$ [i352, i353, 2 * i354 + i356, 2 * i355 + i357])) 0 1]) ; w363 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u351) (\\[i358, i359, i360, i361] -> [2 * i358 + i360, 2 * i359 + i361])) ; w364 = sreshape @[7,4,3,5,4] (w362 * w363) ; t370 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w364))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, kfromS (smaxIndex (w364 !$ [i365, i366, i367, i368]))])))) (\\[i369] -> [i369, i369])))) ; m371 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t370) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m374 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i372, i373] -> [ifH (sscalar -0.0 <=. negate (m371 !$ [i372, i373])) 0 1]) ; t375 = str (sreplicate @10 (m374 * m371)) in ssum @5 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * t375) + str (sreplicate @7 (tproject2 (tproject2 (tproject2 u1))))"
  printArtifactPretty artifactRev
    @?= "\\dret u1 -> let w326 = str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] (sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i322, i323] -> [i322 + i323]))) (\\[i324, i325] -> [i324 + i325])))))))) ; w327 = sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0]))))))))) ; u328 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (w326 * w327))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w339 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333, i334] -> [ifH (sscalar -0.0 <=. negate (u328 !$ [i329, i330, 2 * i331 + i333, 2 * i332 + i334])) 0 1]) ; w340 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u328) (\\[i335, i336, i337, i338] -> [2 * i335 + i337, 2 * i336 + i338])) ; w341 = sreshape @[7,4,7,11,4] (w339 * w340) ; w350 = str (sreplicate @4 (stranspose @[2,3,0,4,5,1] (sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w341))))))) (\\[i342, i343, i344, i345] -> [kfromS (smaxIndex (w341 !$ [i345, i344, i342, i343])), i343, i342, i344, i345]))) (\\[i346, i347] -> [i346, i347, i346 + i347]))) (\\[i348, i349] -> [i348, i348 + i349, i349])))) ; u351 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (w350 * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w362 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i352, i353, i354, i355, i356, i357] -> [ifH (sscalar -0.0 <=. negate (u351 !$ [i352, i353, 2 * i354 + i356, 2 * i355 + i357])) 0 1]) ; w363 = stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u351) (\\[i358, i359, i360, i361] -> [2 * i358 + i360, 2 * i359 + i361])) ; w364 = sreshape @[7,4,3,5,4] (w362 * w363) ; t370 = str (sreplicate @5 (str (sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w364))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, kfromS (smaxIndex (w364 !$ [i365, i366, i367, i368]))])))) (\\[i369] -> [i369, i369])))) ; m371 = ssum @60 (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * t370) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m374 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i372, i373] -> [ifH (sscalar -0.0 <=. negate (m371 !$ [i372, i373])) 0 1]) ; t375 = str (sreplicate @10 (m374 * m371)) ; m377 = m374 * ssum @10 (str (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject2 (tproject2 u1)))) * sreplicate @5 dret)) ; u387 = stranspose @[3,2,0,1] (sscatter (stranspose @[2,3,4,5,1,0] (w362 * sreshape @[7,4,3,5,2,2] (stranspose @[4,3,2,1,0] (ssum @7 (stranspose @[5,4,3,2,1,0] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (str (ssum @5 (str (stranspose @[2,1,0] (sreplicate @7 (tproject1 (tproject1 (tproject2 u1)))) * sreplicate @60 m377)))) (\\[i378] -> [i378, i378])))) (\\[i379, i380, i381, i382] -> [i379, i380, i381, i382, kfromS (smaxIndex (w364 !$ [i379, i380, i381, i382]))]))))))) (\\[i383, i384, i385, i386] -> [2 * i383 + i385, 2 * i384 + i386])) ; w388 = sreshape @[7,4,7,11,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 u387)) ; u401 = stranspose @[3,2,0,1] (sscatter (stranspose @[2,3,4,5,1,0] (w339 * sreshape @[7,4,7,11,2,2] (stranspose @[4,3,2,1,0] (ssum @4 (ssum @7 (ssum @11 (stranspose @[5,6,7,4,3,2,1,0] (ssum @3 (stranspose @[8,4,3,2,1,0,7,6,5] (sscatter (stranspose @[2,6,5,3,7,0,4,1] (sscatter (stranspose @[4,6,3,0,5,1,2] (sscatter (stranspose @[2,5,0,1,3,4] (ssum @4 (str (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))) * w388)))) (\\[i389, i390] -> [i389, i389 + i390, i390]))) (\\[i391, i392] -> [i391, i392, i391 + i392]))) (\\[i393, i394, i395, i396] -> [kfromS (smaxIndex (w341 !$ [i396, i395, i393, i394])), i394, i393, i395, i396]))))))))))) (\\[i397, i398, i399, i400] -> [2 * i397 + i399, 2 * i398 + i400])) in tpair (tpair (tpair (str (soneHot (ssum @1 (str (ssum @1 (str (ssum @23 (str (ssum @14 (str (ssum @7 (w326 * sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 u401)))))))))))) [0])) (ssum @23 (ssum @14 (stranspose @[1,2,0] (ssum @7 u401))))) (tpair (ssum @11 (str (ssum @7 (str (ssum @7 (w350 * w388)))))) (ssum @11 (ssum @7 (stranspose @[1,2,0] (ssum @7 u387)))))) (tpair (tpair (ssum @7 (stranspose @[2,1,0] (t370 * sreplicate @60 m377))) (ssum @7 (str m377))) (tpair (ssum @7 (stranspose @[2,1,0] (t375 * sreplicate @5 dret))) (ssum @7 (str dret))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret u1 -> let w326 = sgather (stranspose @[3,2,0,1] (sgather (sconcrete (sreplicate [14,7,23] 7.0)) (\\[i710, i711] -> [i710 + i711]))) (\\[i324, i325] -> [i324 + i325]) ; u328 = ssum @12 (stranspose @[4,0,1,2,3] (sreshape @[7,4,14,23,12] (str (sreplicate @4 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[1,2,3,0] (sreplicate @1 (stranspose @[2,3,0,4,1] w326)))))) * sreplicate @7 (str (sreplicate @14 (str (sreplicate @23 (str (sreplicate @1 (str (sreplicate @1 (str (tproject1 (tproject1 (tproject1 u1))) !$ [0])))))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @14 (sreplicate @23 (tproject2 (tproject1 (tproject1 u1)))))) ; w339 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i329, i330, i331, i332, i333, i334] -> [ifH (sscalar -0.0 <=. negate (u328 !$ [i329, i330, 2 * i331 + i333, 2 * i332 + i334])) 0 1]) ; w341 = sreshape @[7,4,7,11,4] (w339 * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u328) (\\[i335, i336, i337, i338] -> [2 * i335 + i337, 2 * i336 + i338]))) ; w350 = sgather (stranspose @[3,5,6,2,0,4,1] (sgather (stranspose @[5,7,0,3,6,2,1,4] (sgather (stranspose @[5,4,3,2,1,8,7,6,0] (sreplicate @3 (stranspose @[7,6,5,4,3,0,1,2] (sreplicate @11 (sreplicate @7 (sreplicate @4 (stranspose @[4,3,2,1,0] w341))))))) (\\[i687, i691, i692, i694] -> [kfromS (smaxIndex (w341 !$ [i694, i692, i687, i691])), i691, i687, i692, i694]))) (\\[i699, i701] -> [i699, i701, i699 + i701]))) (\\[i348, i349] -> [i348, i348 + i349, i349]) ; u351 = ssum @48 (stranspose @[4,0,1,2,3] (sreshape @[7,4,7,11,48] (str (sreplicate @4 (stranspose @[2,3,0,4,5,1] w350)) * sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1)))))))))) + sreplicate @7 (stranspose @[2,0,1] (sreplicate @7 (sreplicate @11 (tproject2 (tproject2 (tproject1 u1)))))) ; w362 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i352, i353, i354, i355, i356, i357] -> [ifH (sscalar -0.0 <=. negate (u351 !$ [i352, i353, 2 * i354 + i356, 2 * i355 + i357])) 0 1]) ; w364 = sreshape @[7,4,3,5,4] (w362 * stranspose @[5,4,0,1,2,3] (sgather (stranspose @[2,3,1,0] u351) (\\[i358, i359, i360, i361] -> [2 * i358 + i360, 2 * i359 + i361]))) ; m370 = sgather (sreshape @[7,7,60] (stranspose @[4,0,1,2,3] (sgather (stranspose @[5,4,3,2,1,0] (sreplicate @7 (stranspose @[4,3,2,1,0] w364))) (\\[i365, i366, i367, i368] -> [i365, i366, i367, i368, kfromS (smaxIndex (w364 !$ [i365, i366, i367, i368]))])))) (\\[i369] -> [i369, i369]) ; m371 = smatmul2 (tproject1 (tproject1 (tproject2 u1))) (str m370) + str (sreplicate @7 (tproject2 (tproject1 (tproject2 u1)))) ; m374 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i372, i373] -> [ifH (sscalar -0.0 <=. negate (m371 !$ [i372, i373])) 0 1]) ; m377 = m374 * smatmul2 (str (tproject1 (tproject2 (tproject2 u1)))) dret ; u387 = sscatter (stranspose @[2,3,4,5,1,0] w362 * stranspose @[2,3,4,5,1,0] (sreshape @[7,4,3,5,2,2] (ssum @7 (stranspose @[5,0,1,2,3,4] (sscatter (stranspose @[1,2,3,4,0] (sreshape @[7,7,4,3,5] (sscatter (smatmul2 (str m377) (tproject1 (tproject1 (tproject2 u1)))) (\\[i378] -> [i378, i378])))) (\\[i379, i380, i381, i382] -> [i379, i380, i381, i382, kfromS (smaxIndex (w364 !$ [i379, i380, i381, i382]))])))))) (\\[i383, i384, i385, i386] -> [2 * i383 + i385, 2 * i384 + i386]) ; w388 = sreshape @[7,4,7,11,4,3,4] (stranspose @[1,2,3,4,0] (sreplicate @48 (stranspose @[3,2,0,1] u387))) ; u401 = sscatter (stranspose @[2,3,4,5,1,0] w339 * stranspose @[2,3,4,5,1,0] (sreshape @[7,4,7,11,2,2] (ssum @4 (ssum @7 (ssum @11 (ssum @3 (stranspose @[8,7,6,5,4,3,2,1,0] (sscatter (stranspose @[2,6,5,3,7,0,4,1] (sscatter (stranspose @[4,6,3,0,5,1,2] (sscatter (ssdot1In (stranspose @[3,6,0,2,4,5,1] (sreplicate @7 (str (sreplicate @7 (str (sreplicate @11 (tproject1 (tproject2 (tproject1 u1))))))))) (stranspose @[3,6,0,2,4,5,1] w388)) (\\[i389, i390] -> [i389, i389 + i390, i390]))) (\\[i391, i392] -> [i391, i392, i391 + i392]))) (\\[i393, i394, i395, i396] -> [kfromS (smaxIndex (w341 !$ [i396, i395, i393, i394])), i394, i393, i395, i396]))))))))) (\\[i397, i398, i399, i400] -> [2 * i397 + i399, 2 * i398 + i400]) in tpair (tpair (tpair (str (sreplicate @1 (ssum @23 (ssum @14 (ssdot1In (stranspose @[1,5,0,4,3,2] (sreplicate @4 (stranspose @[3,2,1,4,0] w326))) (stranspose @[4,5,2,3,1,6,7,0] (sreshape @[7,4,14,23,1,1,3,4] (stranspose @[1,2,3,4,0] (sreplicate @12 (stranspose @[3,2,0,1] u401)))) !$ [0, 0])))))) (ssum @23 (ssum @14 (ssum @7 (stranspose @[3,0,1,2] u401))))) (tpair (ssum @11 (ssum @7 (ssdot1In (stranspose @[2,3,0,4,5,6,1] (sreplicate @4 (stranspose @[2,3,0,4,5,1] w350))) (stranspose @[2,3,1,4,5,6,0] w388)))) (ssum @11 (ssum @7 (ssum @7 (stranspose @[3,0,1,2] u387)))))) (tpair (tpair (smatmul2 m377 m370) (ssum @7 (str m377))) (tpair (smatmul2 dret (str m374 * str m371)) (ssum @7 (str dret))))"
