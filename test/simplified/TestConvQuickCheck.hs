{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
-- | QuickCheck tests of convolution AD derivatives vs handwritten derivatives.
module TestConvQuickCheck (testTrees) where

import Prelude

import Control.Arrow ((***))
import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Type.Ord (Compare)
import GHC.Exts (IsList (..))
import GHC.TypeLits
  (Div, KnownNat, SomeNat (..), sameNat, someNatVal, type (-), type (<=))
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.QuickCheck hiding (label, shuffle)
import Text.Printf

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (ixrFromIxS, ixsFromIxR')
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.Ops (tconcrete)
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.OpsTensor

import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "conv2d_dInp" test_conv2d_dInp
  , testCase "conv2d_dKrn" test_conv2d_dKrn
--  , testProperty "conv2d_quickcheck Double" (quickcheck_conv2d @Double)
--  , testProperty "conv2d_quickcheck Float" (quickcheck_conv2d @Float)
  ]

-- | Derivative of full convolution with respect to the input image,
-- where the output size is the same as the input size.
conv2d_dInp
  :: forall shK shA shB shB1 sh1 nImgs nCinp nCout nAh nAw nKh nKw
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw
     , KnownNat nKh, KnownNat nKw
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , shB1 ~ '[1,     1,     nAh, nAw]
     , sh1  ~ '[nCout] )
  => target (TKS shK r)
  -> target (TKS shB r)
  -> target (TKS shA r)
conv2d_dInp arrK arrB =
  let nKh = valueOf @nKh
      nKw = valueOf @nKw
  in sbuild @(Rank shA) $ \case
    [iImg, iCinp, iAh, iAw] ->
      let arr1 :: target (TKS sh1 r)
          arr1 = sbuild @(Rank sh1) $ \case
            [iCout] ->
              let arrBt = slicezS @shB1 arrB
                                  [iImg,  iCout, iAh - nKh + 1, iAw - nKw + 1]
                  arrKt = slicezS @shB1 arrK
                                  [iCout, iCinp, 0, 0]
              in sdot0 arrBt arrKt
            _ -> error "conv2d_dInp: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2d_dInp: impossible pattern needlessly required"

-- | Derivative of full convolution with respect to the kernels,
-- where the output size is the same as the input size.
conv2d_dKrn
  :: forall shK shA shB shB1 sh1 nImgs nCinp nCout nAh nAw nKh nKw
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh, KnownNat nKw
     , ADReady target, GoodScalar r
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , shB1 ~ '[1,     1,     nAh, nAw]
     , sh1  ~ '[nCout] )
  => target (TKS shA r)
  -> target (TKS shB r)
  -> target (TKS shK r)
conv2d_dKrn arrA arrB =
  sbuild @(Rank shK) $ \case
    [iCout, iCinp, iKh, iKw] ->
      let arr1 :: target (TKS sh1 r)
          arr1 = sbuild @(Rank sh1) $ \case
            [iImg] ->
              let arrBt = slicezS @shB1 arrB [iImg, iCout, 0,   0  ]
                  arrAt = slicezS @shB1 arrA [iImg, iCinp, iKh, iKw]
              in sdot0 arrBt arrAt
            _ -> error "conv2d_dKrn: impossible pattern needlessly required"
      in ssum arr1
    _ -> error "conv2d_dKrn: impossible pattern needlessly required"

test_conv2d_dInp :: Assertion
test_conv2d_dInp =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS  1
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 8] Double
      arrB = Nested.sreplicateScal knownShS 1
      -- Compare the AD version against the manual derivative.
      dInp :: Concrete (TKS '[5, 2, 4, 8] Double)
      dInp = conv2d_dInp (sconcrete arrK) (sconcrete arrB)
      vjpInp = cvjp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dInp vjpInp

test_conv2d_dKrn :: Assertion
test_conv2d_dKrn =
  let -- Input of shape: batch x chas x height x width
      arrA :: Nested.Shaped '[5, 2, 4, 8] Double
      arrA = Nested.sreplicateScal knownShS 1
      -- Filters of shape: num_filters x chas x kernel_height x kernel_width
      arrK :: Nested.Shaped '[7, 2, 1, 3] Double
      arrK = Nested.sreplicateScal knownShS 1
      -- Output gradient of shape: batch x chas x output_height x output_width
      arrB :: Nested.Shaped '[5, 7, 4, 8] Double
      arrB = Nested.sreplicateScal knownShS 1
      -- Compare the AD version against the manual derivative.
      dKrn :: Concrete (TKS '[7, 2, 1, 3] Double)
      dKrn = conv2d_dKrn (sconcrete arrA) (sconcrete arrB)
      vjpKrn = cvjp (`conv2dUnpaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in assertEqualUpToEpsilon 1e-7 dKrn vjpKrn

static_conv2d
  :: forall r nImgs nCinp nCout nAh nAw nKh nKw
            shK shA shB.
     ( GoodScalar r, ADTensorScalar r ~ r, Nested.FloatElt r
     , shK ~ '[nCout, nCinp, nKh, nKw]
     , shA ~ '[nImgs, nCinp, nAh, nAw]
     , shB ~ '[nImgs, nCout, nAh, nAw] )
  => SNat nImgs -> SNat nCinp -> SNat nCout
  -> SNat nAh -> SNat nAw -> SNat nKh -> SNat nKw
  -> Nested.Shaped shK r
       -- ^ Filters of shape: num_filters x chas x kernel_height x kernel_width
  -> Nested.Shaped shA r
       -- ^ Input of shape: batch x chas x height x width
  -> Nested.Shaped shB r
       -- ^ Output gradient of shape:
       --     batch x chas x output_height x output_width
  -> Bool
static_conv2d SNat SNat SNat SNat SNat SNat SNat arrK arrA arrB =
  let -- Compare the AD version against the manual derivative.
      -- Note that manual versions don't take one of the arguments (the point
      -- at which the gradient is taken), because maths (something about
      -- convolution being linear and so gradient the same everywhere).
      -- First, the gradient wrt the input image taken at point @arrA@.
      dInp = conv2d_dInp (sconcrete arrK) (sconcrete arrB)  -- handwritten
      vjpInp = cvjp (conv2dUnpaddedS (sconcrete arrK))
                    (sconcrete arrA) (sconcrete arrB)
      -- Second, the gradient wrt the kernels taken at point @arrK@.
      dKrn = conv2d_dKrn (sconcrete arrA) (sconcrete arrB) -- handwritten
      vjpKrn = cvjp (`conv2dUnpaddedS` (sconcrete arrA))
                    (sconcrete arrK) (sconcrete arrB)
  in abs (ssum0 (vjpInp - dInp)) <= 1e-7
     && abs (ssum0 (vjpKrn - dKrn)) <= 1e-7

{-
quickcheck_conv2d
  :: forall r.
     ( GoodScalar r, ADTensorScalar r ~ r, Nested.FloatElt r
     , Arbitrary r )
  => Property
quickcheck_conv2d =
  forAll (choose (0, 10)) $ \nImgs' ->
  forAll (choose (0, 10)) $ \nCinp' ->
  forAll (choose (0, 10)) $ \nCout' ->
  forAll (choose (0, 10)) $ \nAh' ->
  forAll (choose (0, 10)) $ \nAw' ->
  forAll (choose (0, 10)) $ \nKh' ->
  forAll (choose (0, 10)) $ \nKw' ->
    -- The glue below is needed to bridge the dependently-typed
    -- vs normal world.
    withSNat nImgs' $ \nImgs ->
    withSNat nCinp' $ \nCinp ->
    withSNat nCout' $ \nCout ->
    withSNat nAh' $ \nAh ->
    withSNat nAw' $ \nAw ->
    withSNat nKh' $ \nKh ->
    withSNat nKw' $ \nKw ->
      property $ static_conv2d @r nImgs nCinp nCout nAh nAw nKh nKw
-}
