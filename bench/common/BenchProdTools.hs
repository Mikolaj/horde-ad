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
import Data.Foldable qualified as Foldable
import Data.List (foldl1')
import GHC.Exts (IsList (..), WithDict)
import GHC.TypeLits (KnownNat)
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
    [ bench "ncrev ls" $ nf (crevRankedLProd snat) l
    , bench "nrev ls" $ nf (revRankedLProd snat) l
    , bench "r crev ls" $ nf (crevRankedLProdr snat) l
    , bench "r rev ls" $ nf (revRankedLProdr snat) l
    , bench "NotShared ls crev" $ nf (crevRankedNotSharedLProd snat) l
    , bench "ncrev lt" $ nf (crevRankedLtProd snat) lt
    , bench "nrev lt" $ nf (revRankedLtProd snat) lt
    , bench "r crev lt" $ nf (crevRankedLtProdr snat) lt
    , bench "r rev lt" $ nf (revRankedLtProdr snat) lt
    , bench "NotShared lt crev" $ nf (crevRankedNotSharedLtProd snat) lt
    , bench "crev t" $ nf (crevRankedTProd snat) t
    , bench "rev t" $ nf (revRankedTProd snat) t
    ]

rankedLProd :: (BaseTensor target, GoodScalar r)
            => ListR n (target (TKScalar r)) -> target (TKScalar r)
rankedLProd = foldl1' (*) . Foldable.toList

crevRankedLProd
  :: SNat n -> ListR n (RepN (TKScalar Double))
  -> ListR n (RepN (TKScalar Double))
crevRankedLProd snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  crev rankedLProd

revRankedLProd
  :: SNat n -> ListR n (RepN (TKScalar Double))
  -> ListR n (RepN (TKScalar Double))
revRankedLProd snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  rev rankedLProd

rankedLProdr :: (BaseTensor target, GoodScalar r)
             => ListR n (target (TKScalar r)) -> target (TKScalar r)
rankedLProdr = foldr1 (*)

crevRankedLProdr
  :: SNat n -> ListR n (RepN (TKScalar Double))
  -> ListR n (RepN (TKScalar Double))
crevRankedLProdr snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  crev rankedLProdr

revRankedLProdr
  :: SNat n -> ListR n (RepN (TKScalar Double))
  -> ListR n (RepN (TKScalar Double))
revRankedLProdr snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  rev rankedLProdr

rankedNotSharedLProd :: (BaseTensor target, GoodScalar r)
                    => ListR n (ADVal target (TKScalar r))
                    -> ADVal target (TKScalar r)
rankedNotSharedLProd = foldr1 multNotShared

crevRankedNotSharedLProd
  :: SNat n -> ListR n (RepN (TKScalar Double))
  -> ListR n (RepN (TKScalar Double))
crevRankedNotSharedLProd snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  crev rankedNotSharedLProd

rankedLtProd :: (BaseTensor target, GoodScalar r)
             => ListR n (target (TKS '[] r)) -> target (TKS '[] r)
rankedLtProd = foldl1' (*) . Foldable.toList

crevRankedLtProd
  :: SNat n -> ListR n (RepN (TKS '[] Double))
  -> ListR n (RepN (TKS '[] Double))
crevRankedLtProd snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  crev rankedLtProd

revRankedLtProd
  :: SNat n -> ListR n (RepN (TKS '[] Double))
  -> ListR n (RepN (TKS '[] Double))
revRankedLtProd snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  rev rankedLtProd

rankedLtProdr :: (BaseTensor target, GoodScalar r)
              => ListR n (target (TKS '[] r)) -> target (TKS '[] r)
rankedLtProdr = foldr1 (*)

crevRankedLtProdr
  :: SNat n -> ListR n (RepN (TKS '[] Double))
  -> ListR n (RepN (TKS '[] Double))
crevRankedLtProdr snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  crev rankedLtProdr

revRankedLtProdr
  :: SNat n -> ListR n (RepN (TKS '[] Double))
  -> ListR n (RepN (TKS '[] Double))
revRankedLtProdr snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  rev rankedLtProdr

rankedNotSharedLtProd :: (BaseTensor target, GoodScalar r)
                      => ListR n (ADVal target (TKS '[] r))
                      -> ADVal target (TKS '[] r)
rankedNotSharedLtProd = foldr1 multNotShared

crevRankedNotSharedLtProd
  :: SNat n -> ListR n (RepN (TKS '[] Double))
  -> ListR n (RepN (TKS '[] Double))
crevRankedNotSharedLtProd snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  crev rankedNotSharedLtProd

-- A potential further speedup would be to use tmapAccumL with TKS
-- and TKScalar, but I don't think we'd gain much, especially for rev.
-- Another variant, with foldl1' and indexing, would be a disaster.
-- We can define sproduct if this benchmark ends up used anywhere,
-- because the current codomain of gradientFromDelta rules out
-- low-level hacky pipeline tricks that could avoid indexing.
rankedTProd :: (BaseTensor target, LetTensor target, GoodScalar r)
            => SNat n -> target (TKS '[n] r) -> target (TKS '[] r)
rankedTProd SNat = sfold (*) (sscalar 1)
{-# SPECIALIZE rankedTProd :: SNat n -> ADVal RepN (TKS '[n] Double) -> ADVal RepN (TKS '[] Double) #-}
{-# SPECIALIZE rankedTProd :: SNat n -> AstTensor AstMethodLet FullSpan (TKS '[n] Double) -> AstTensor AstMethodLet FullSpan (TKS '[] Double) #-}

crevRankedTProd
  :: SNat n -> RepN (TKS '[n] Double) -> RepN (TKS '[n] Double)
crevRankedTProd snat@SNat = crev (rankedTProd snat)

revRankedTProd
  :: SNat n -> RepN (TKS '[n] Double) -> RepN (TKS '[n] Double)
revRankedTProd snat@SNat = rev (rankedTProd snat)

-- TODO: not enough specialized
-- TODO: outdated explanation:
-- The GoodScalar and it's component occurrences are due to creating
-- a value of an existential type that satisfies GoodScalar,
-- so it's intended and not a specialization failure.
-- OTOH, KnownNat and AstSpan are tag types, so it's fine not to specialize
-- for them.
--
-- This is expected to fail with -O0 and to pass with -O1
-- and -fpolymorphic-specialisation.
-- This prevents running benchmarks without optimization, which is a good thing.
inspect $ hasNoTypeClassesExcept 'crevRankedLProd [''(~), ''KnownNat, ''WithDict, ''Nested.KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt]
inspect $ hasNoTypeClassesExcept 'revRankedLProd [''(~), ''KnownNat, ''WithDict, ''Nested.KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt]
inspect $ hasNoTypeClassesExcept 'crevRankedNotSharedLProd [''(~), ''KnownNat, ''WithDict, ''Nested.KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt]
inspect $ hasNoTypeClassesExcept 'crevRankedLtProd [''(~), ''KnownNat, ''WithDict, ''Nested.KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt, ''Nested.Storable]
inspect $ hasNoTypeClassesExcept 'revRankedLtProd [''(~), ''KnownNat, ''WithDict, ''Nested.KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt]
inspect $ hasNoTypeClassesExcept 'crevRankedTProd [''(~), ''KnownNat, ''WithDict, ''Nested.KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt, ''LetTensor, ''BaseTensor, ''ConvertTensor, ''Boolean, ''CommonTargetEqOrd, ''AllTargetShow, ''ShareTensor]
inspect $ hasNoTypeClassesExcept 'revRankedTProd [''(~), ''KnownNat, ''WithDict, ''Nested.KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt, ''LetTensor, ''BaseTensor, ''ConvertTensor, ''Boolean, ''CommonTargetEqOrd, ''AllTargetShow, ''ShareTensor]
-- inspect $ coreOf 'revRankedTProd
