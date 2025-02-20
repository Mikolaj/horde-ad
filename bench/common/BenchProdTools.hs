{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- {-# OPTIONS_GHC -ddump-stranal #-}
-- | A contrived benchmark: a product of a list of scalars.
module BenchProdTools where

import Prelude

--import Control.DeepSeq (NFData)
import Control.DeepSeq (NFData (..))
import Criterion.Main
import Data.Default qualified as Default
import Data.List (foldl1')
import GHC.Exts (IsList (..), WithDict)
import GHC.TypeLits (KnownNat)
import Numeric.LinearAlgebra (Numeric)
import Test.Inspection
import Type.Reflection (Typeable)

import Data.Array.Nested (ListR (..))
import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.Adaptor

bgroup100, bgroup1000, bgroup1e4, bgroup1e5, bgroup1e6, bgroup1e7, bgroup5e7 :: [Double] -> Benchmark
bgroup100 = envProd 100 $ \args -> bgroup "100" $ benchProd args

bgroup1000 = envProd 1000 $ \args -> bgroup "1000" $ benchProd args

bgroup1e4 = envProd 1e4 $ \args -> bgroup "1e4" $ benchProd args

bgroup1e5 = envProd 1e5 $ \args -> bgroup "1e5" $ benchProd args

bgroup1e6 = envProd 1e6 $ \args -> bgroup "1e6" $ benchProd args

bgroup1e7 = envProd 1e7 $ \args -> bgroup "1e7" $ benchProd args

bgroup5e7 = envProd 5e7 $ \args -> bgroup "5e7" $ benchProd args
  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8

envProd :: r ~ Double
        => Rational
        -> (forall n.
            ( SNat n
            , ListR n (RepN (TKScalar r))
            , ListR n (RepN (TKS '[] r))
            , RepN (TKS '[n] r) )
            -> Benchmark)
        -> [r]
        -> Benchmark
envProd rat f allxs =
  let k = round rat
  in withSNat k $ \(SNat @k) ->
    env (return $!
      let l = take k allxs
          lt = map sscalar l
      in ( SNat @k
         , fromList (map RepN l)
         , fromList lt
         , sfromList . fromList $ lt) )
        (f @k)

benchProd :: r ~ Double
          => ( SNat n
             , ListR n (RepN (TKScalar r))
             , ListR n (RepN (TKS '[] r))
             , RepN (TKS '[n] r) )
          -> [Benchmark]
benchProd ~(snat, l, lt, t) = case snat of
  SNat ->
    [ bench "ncrev ls" $ nf crevRankedLProd l
    , bench "nrev ls" $ nf revRankedLProd l
    , bench "r crev ls" $ nf crevRankedLProdr l
    , bench "r rev ls" $ nf revRankedLProdr l
    , bench "NotShared ls crev" $ nf crevRankedNotSharedLProd l
    , bench "ncrev lt" $ nf crevRankedLtProd lt
    , bench "nrev lt" $ nf revRankedLtProd lt
    , bench "r crev lt" $ nf crevRankedLtProdr lt
    , bench "r rev lt" $ nf revRankedLtProdr lt
    , bench "NotShared lt crev" $ nf crevRankedNotSharedLtProd lt
    , bench "crev t" $ nf crevRankedTProd t
    , bench "rev t" $ nf revRankedTProd t
    ]

rankedLProd :: (BaseTensor target, GoodScalar r, KnownNat n)
            => ListR n (target (TKScalar r)) -> target (TKScalar r)
rankedLProd = foldl1' (*) . toList

crevRankedLProd
  :: forall n. KnownNat n
  => ListR n (RepN (TKScalar Double)) -> ListR n (RepN (TKScalar Double))
crevRankedLProd =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) (SNat @n)) $
  crev rankedLProd

revRankedLProd
  :: forall n. KnownNat n
  => ListR n (RepN (TKScalar Double)) -> ListR n (RepN (TKScalar Double))
revRankedLProd =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) (SNat @n)) $
  rev rankedLProd

rankedLProdr :: (BaseTensor target, GoodScalar r)
             => ListR n (target (TKScalar r)) -> target (TKScalar r)
rankedLProdr = foldr1 (*)

crevRankedLProdr
  :: forall n. KnownNat n
  => ListR n (RepN (TKScalar Double)) -> ListR n (RepN (TKScalar Double))
crevRankedLProdr =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) (SNat @n)) $
  crev rankedLProdr

revRankedLProdr
  :: forall n. KnownNat n
  => ListR n (RepN (TKScalar Double)) -> ListR n (RepN (TKScalar Double))
revRankedLProdr =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) (SNat @n)) $
  rev rankedLProdr

rankedNotSharedLProd :: (BaseTensor target, GoodScalar r)
                    => ListR n (ADVal target (TKScalar r))
                    -> ADVal target (TKScalar r)
rankedNotSharedLProd = foldr1 multNotShared

crevRankedNotSharedLProd
  :: forall n. KnownNat n
  => ListR n (RepN (TKScalar Double)) -> ListR n (RepN (TKScalar Double))
crevRankedNotSharedLProd =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) (SNat @n)) $
  crev rankedNotSharedLProd

rankedLtProd :: (BaseTensor target, GoodScalar r, KnownNat n)
             => ListR n (target (TKS '[] r)) -> target (TKS '[] r)
rankedLtProd = foldl1' (*) . toList

crevRankedLtProd
  :: forall n. KnownNat n
  => ListR n (RepN (TKS '[] Double)) -> ListR n (RepN (TKS '[] Double))
crevRankedLtProd =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) (SNat @n)) $
  crev rankedLtProd

revRankedLtProd
  :: forall n. KnownNat n
  => ListR n (RepN (TKS '[] Double)) -> ListR n (RepN (TKS '[] Double))
revRankedLtProd =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) (SNat @n)) $
  rev rankedLtProd

rankedLtProdr :: (BaseTensor target, GoodScalar r)
              => ListR n (target (TKS '[] r)) -> target (TKS '[] r)
rankedLtProdr = foldr1 (*)

crevRankedLtProdr
  :: forall n. KnownNat n
  => ListR n (RepN (TKS '[] Double)) -> ListR n (RepN (TKS '[] Double))
crevRankedLtProdr =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) (SNat @n)) $
  crev rankedLtProdr

revRankedLtProdr
  :: forall n. KnownNat n
  => ListR n (RepN (TKS '[] Double)) -> ListR n (RepN (TKS '[] Double))
revRankedLtProdr =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) (SNat @n)) $
  rev rankedLtProdr

rankedNotSharedLtProd :: (BaseTensor target, GoodScalar r)
                      => ListR n (ADVal target (TKS '[] r))
                      -> ADVal target (TKS '[] r)
rankedNotSharedLtProd = foldr1 multNotShared

crevRankedNotSharedLtProd
  :: forall n. KnownNat n
  => ListR n (RepN (TKS '[] Double)) -> ListR n (RepN (TKS '[] Double))
crevRankedNotSharedLtProd =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) (SNat @n)) $
  crev rankedNotSharedLtProd

-- A potential further speedup would be to use tmapAccumL with TKS
-- and TKScalar, but I don't think we'd gain much, especially for rev.
-- Another variant, with foldl1' and indexing, would be a disaster.
-- We can define sproduct if this benchmark ends up used anywhere,
-- because the current codomain of gradientFromDelta rules out
-- low-level hacky pipeline tricks that could avoid indexing.
rankedTProd :: (BaseTensor target, LetTensor target, GoodScalar r, KnownNat n)
            => target (TKS '[n] r) -> target (TKS '[] r)
rankedTProd = sfold (*) (sscalar 1)

crevRankedTProd
  :: forall n. KnownNat n
  => RepN (TKS '[n] Double) -> RepN (TKS '[n] Double)
crevRankedTProd = crev rankedTProd

revRankedTProd
  :: forall n. KnownNat n
  => RepN (TKS '[n] Double) -> RepN (TKS '[n] Double)
revRankedTProd = rev rankedTProd

-- TODO: not enough specialized
-- TODO: outdated explanation:
-- The GoodScalar and it's component occurrences are due to creating
-- a value of an existential type that satisfies GoodScalar,
-- so it's intended and not a specialization failure.
-- OTOH, KnownNat and AstSpan are tag types, so it's fine not to specialize
-- for them.
-- The numeric type classes in two of the cases are needed due
-- to the existential variables in AstRanked that show up, e.g., when
-- pattern matching on that type, dictionaries seen in the datatype
-- constructors.
{-
inspect $ hasNoTypeClassesExcept 'revRankedTProd [''KnownNat, ''KnownSTK, ''BaseTensor, ''GoodScalar, ''AstSpan, ''Num, ''Show, ''Ord, ''Typeable, ''IfDifferentiable, ''Eq, ''NFData, ''Default.Default, ''Nested.Elt, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Nested.KnownShS, ''Boolean, ''EqF, ''OrdF, ''AllTargetShow, ''ShareTensor, ''LetTensor, ''(~), ''Nested.Storable, ''Nested.KnownShX, ''WithDict, ''RealFrac]
-}

{- with --ghc-options="-fpolymorphic-specialisation"
additional classes appear (at the end): -}
inspect $ hasNoTypeClassesExcept 'revRankedTProd [''KnownNat, ''KnownSTK, ''BaseTensor, ''GoodScalar, ''AstSpan, ''Num, ''Show, ''Ord, ''Typeable, ''IfDifferentiable, ''Eq, ''NFData, ''Default.Default, ''Nested.Elt, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Nested.KnownShS, ''Boolean, ''EqF, ''OrdF, ''AllTargetShow, ''ShareTensor, ''LetTensor, ''(~), ''Nested.Storable, ''Nested.KnownShX, ''WithDict, ''RealFrac, ''RealFloatF, ''Nested.FloatElt, ''IntegralF, ''Integral, ''Numeric, ''IsList, ''AdaptableTarget, ''Nested.KnownPerm, ''CommonTargetEqOrd]
