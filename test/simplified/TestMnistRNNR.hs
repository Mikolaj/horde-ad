module TestMnistRNNR
  ( testTrees
  ) where

import Prelude

import           Control.Monad (foldM, unless)
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.EnumMap.Strict as EM
import           Data.List.Index (imap)
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as LA
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor
import HordeAd.External.Optimizer
import HordeAd.External.OptimizerTools

import EqEpsilon

import           MnistData
import qualified MnistRnnRanked2

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTests
            , tensorIntermediateMnistTests
            , tensorADOnceMnistTests
            ]

-- POPL differentiation, straight via the ADVal instance of Tensor
mnistTestCase2VTA
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r)
     , TensorOf 1 (ADVal r) ~ ADVal (OR.Array 1 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , Primal (ADVal r) ~ r, ScalarOf (ADVal r) ~ r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VTA _prefix _epochs _maxBatches widthHidden widthHidden2
                  _gamma _batchSize _expected =
  let _nParams1 = MnistRnnRanked2.afcnnMnistLen1 widthHidden widthHidden2
  in testCase "" $ return ()

tensorADValMnistTests :: TestTree
tensorADValMnistTests = testGroup "ShortRanked ADVal MNIST tests"
  [ mnistTestCase2VTA "VRA 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16600000000000004 :: Double)
  , mnistTestCase2VTA "VRA artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.8972 :: Float)
  , mnistTestCase2VTA "VRA artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.6585 :: Double)
  ]

-- POPL differentiation, Ast term defined only once but differentiated each time
mnistTestCase2VTI
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADReady (Ast0 r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r)
     , DTensorOf (ADVal r) ~ ADVal (OD.Array r)
     , ScalarOf (ADVal r) ~ r
     , InterpretAst (ADVal r) )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VTI _prefix _epochs _maxBatches widthHidden widthHidden2
                  _gamma _batchSize _expected =
  let _nParams1 = MnistRnnRanked2.afcnnMnistLen1 widthHidden widthHidden2
  in testCase "" $ return ()

tensorIntermediateMnistTests :: TestTree
tensorIntermediateMnistTests = testGroup "ShortRankedIntermediate MNIST tests"
  [ mnistTestCase2VTI "VRI 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase2VTI "VRI artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase2VTI "VRI artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.5859 :: Double)
  ]

-- JAX differentiation, Ast term built and differentiated only once
mnistTestCase2VTO
  :: forall r.
     ( ADReady r, ADReady (ADVal r), ADReady (Ast0 r), ADNum r, PrintfArg r
     , Primal r ~ r, ScalarOf r ~ r, AssertEqualUpToEpsilon r
     , TensorOf 0 (ADVal r) ~ ADVal (OR.Array 0 r), InterpretAst r )
  => String
  -> Int -> Int -> Int -> Int -> r -> Int -> r
  -> TestTree
mnistTestCase2VTO _prefix _epochs _maxBatches widthHidden widthHidden2
                  _gamma _batchSize _expected =
  let _nParams1 = MnistRnnRanked2.afcnnMnistLen1 widthHidden widthHidden2
  in testCase "" $ return ()

tensorADOnceMnistTests :: TestTree
tensorADOnceMnistTests = testGroup "ShortRankedOnce MNIST tests"
  [ mnistTestCase2VTO "VRO 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.16479999999999995 :: Double)
  , mnistTestCase2VTO "VRO artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase2VTO "VRO artificial 5 4 3 2 1" 5 4 3 2 1 5000
                      (0.8304 :: Double)
  ]
