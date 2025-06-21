{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- {-# OPTIONS_GHC -ddump-stranal #-}
-- | A contrived benchmark: a product of a list of scalars.
module BenchProdTools where

import Prelude

import Control.DeepSeq (NFData (..))
import Criterion.Main
import Data.Default qualified as Default
import Data.Foldable qualified as Foldable
import Data.List (foldl1')
import Data.Proxy (Proxy (Proxy))
import GHC.Exts (IsList (..), WithDict)
import GHC.TypeLits (KnownNat)
import Test.Inspection
import Type.Reflection (Typeable)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Ranked.Shape

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.Ops

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
            , [Concrete (TKScalar r)]
            , ListR n (Concrete (TKScalar r))
            , ListR n (Concrete (TKS '[] r))
            , Concrete (TKS '[n] r) )
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
         , map Concrete l
         , fromList (map Concrete l)
         , fromList lt
         , sfromList . fromList $ lt) )
        (f @k)

benchProd :: r ~ Double
          => ( SNat n
             , [Concrete (TKScalar r)]
             , ListR n (Concrete (TKScalar r))
             , ListR n (Concrete (TKS '[] r))
             , Concrete (TKS '[n] r) )
          -> [Benchmark]
benchProd ~(snat, list, l, lt, t) = case snat of
  SNat ->
    [ bench "cgrad s MapAccum" $ nf (crevSMapAccum snat) t
    , bench "grad s MapAccum" $ nf (revSMapAccum snat) t
    , bench "cgrad scalar MapAccum" $ nf (crevScalarMapAccum snat) t
    , bench "grad scalar MapAccum" $ nf (revScalarMapAccum snat) t
    , bench "cgrad scalar list" $ nf crevScalarList list
    , bench "grad scalar list" $ nf revScalarList list
    , bench "cgrad scalar L" $ nf (crevScalarL snat) l
-- TODO: OOMs, see https://github.com/Mikolaj/horde-ad/issues/117
--  , bench "grad scalar L" $ nf (revScalarL snat) l
    , bench "cgrad scalar R" $ nf (crevScalarR snat) l
-- TODO: OOMs, see https://github.com/Mikolaj/horde-ad/issues/117
--  , bench "grad scalar R" $ nf (revScalarR snat) l
    , bench "cgrad scalar NotShared" $ nf (crevScalarNotShared snat) l
    , bench "cgrad s L" $ nf (crevSL snat) lt
-- TODO: OOMs, see https://github.com/Mikolaj/horde-ad/issues/117
--  , bench "grad s L" $ nf (revSL snat) lt
    , bench "cgrad s R" $ nf (crevSR snat) lt
-- TODO: OOMs, see https://github.com/Mikolaj/horde-ad/issues/117
--  , bench "grad s R" $ nf (revSR snat) lt
    , bench "cgrad s NotShared" $ nf (crevSNotShared snat) lt
    ]

-- Another variant, with foldl1' and indexing, would be a disaster.
-- We can define sproduct if this benchmark ends up used anywhere,
-- because the current codomain of gradientFromDelta rules out
-- low-level hacky pipeline tricks that could avoid indexing.
multSMapAccum :: (BaseTensor target, LetTensor target, GoodScalar r)
              => SNat n -> target (TKS '[n] r) -> target (TKS '[] r)
multSMapAccum SNat = sfold (*) (sscalar 1)
{-# SPECIALIZE multSMapAccum :: SNat n -> ADVal Concrete (TKS '[n] Double) -> ADVal Concrete (TKS '[] Double) #-}
{-# SPECIALIZE multSMapAccum :: SNat n -> AstTensor AstMethodLet FullSpan (TKS '[n] Double) -> AstTensor AstMethodLet FullSpan (TKS '[] Double) #-}

crevSMapAccum
  :: SNat n -> Concrete (TKS '[n] Double) -> Concrete (TKS '[n] Double)
crevSMapAccum snat@SNat = cgrad (kfromS . multSMapAccum snat)

revSMapAccum
  :: SNat n -> Concrete (TKS '[n] Double) -> Concrete (TKS '[n] Double)
revSMapAccum snat@SNat = grad (kfromS . multSMapAccum snat)

multScalarMapAccum :: forall target n r.
                      (BaseTensor target, GoodScalar r)
                   => SNat n -> target (TKS '[n] r) -> target (TKScalar r)
multScalarMapAccum snat@SNat  =
  tproject1
  . tmapAccumL (Proxy @target)
     snat
     (FTKScalar @r)
     (FTKScalar @Z1)
     (FTKScalar @r)
     (let g :: forall f. ADReady f
            => f (TKScalar r) -> f (TKScalar r)
            -> f (TKProduct (TKScalar r) TKUnit)
          g !acc !e = tpair (acc * e) tunit
      in g)
     1
{-# SPECIALIZE multScalarMapAccum :: SNat n -> ADVal Concrete (TKS '[n] Double) -> ADVal Concrete (TKScalar Double) #-}
{-# SPECIALIZE multScalarMapAccum :: SNat n -> AstTensor AstMethodLet FullSpan (TKS '[n] Double) -> AstTensor AstMethodLet FullSpan (TKScalar Double) #-}

crevScalarMapAccum
  :: SNat n -> Concrete (TKS '[n] Double) -> Concrete (TKS '[n] Double)
crevScalarMapAccum snat@SNat = cgrad (multScalarMapAccum snat)

revScalarMapAccum
  :: SNat n -> Concrete (TKS '[n] Double) -> Concrete (TKS '[n] Double)
revScalarMapAccum snat@SNat = grad (multScalarMapAccum snat)

multScalarList :: (BaseTensor target, GoodScalar r)
               => [target (TKScalar r)] -> target (TKScalar r)
multScalarList = foldl1' (*)

crevScalarList
  :: [Concrete (TKScalar Double)] -> [Concrete (TKScalar Double)]
crevScalarList =
  cgrad multScalarList

revScalarList
  :: [Concrete (TKScalar Double)] -> [Concrete (TKScalar Double)]
revScalarList =
  grad multScalarList

multScalarL :: (BaseTensor target, GoodScalar r)
            => ListR n (target (TKScalar r)) -> target (TKScalar r)
multScalarL = foldl1' (*) . Foldable.toList

crevScalarL
  :: SNat n -> ListR n (Concrete (TKScalar Double))
  -> ListR n (Concrete (TKScalar Double))
crevScalarL snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  cgrad multScalarL

revScalarL
  :: SNat n -> ListR n (Concrete (TKScalar Double))
  -> ListR n (Concrete (TKScalar Double))
revScalarL snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  grad multScalarL

multScalarR :: (BaseTensor target, GoodScalar r)
            => ListR n (target (TKScalar r)) -> target (TKScalar r)
multScalarR = foldr1 (*)

crevScalarR
  :: SNat n -> ListR n (Concrete (TKScalar Double))
  -> ListR n (Concrete (TKScalar Double))
crevScalarR snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  cgrad multScalarR

revScalarR
  :: SNat n -> ListR n (Concrete (TKScalar Double))
  -> ListR n (Concrete (TKScalar Double))
revScalarR snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  grad multScalarR

multScalarNotShared :: (BaseTensor target, GoodScalar r)
                    => ListR n (ADVal target (TKScalar r))
                    -> ADVal target (TKScalar r)
multScalarNotShared = foldr1 multNotShared

crevScalarNotShared
  :: SNat n -> ListR n (Concrete (TKScalar Double))
  -> ListR n (Concrete (TKScalar Double))
crevScalarNotShared snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKScalar Double)) snat) $
  cgrad multScalarNotShared

multSL :: (BaseTensor target, GoodScalar r)
       => ListR n (target (TKS '[] r)) -> target (TKS '[] r)
multSL = foldl1' (*) . Foldable.toList

crevSL
  :: SNat n -> ListR n (Concrete (TKS '[] Double))
  -> ListR n (Concrete (TKS '[] Double))
crevSL snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  cgrad (kfromS . multSL)

revSL
  :: SNat n -> ListR n (Concrete (TKS '[] Double))
  -> ListR n (Concrete (TKS '[] Double))
revSL snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  grad (kfromS . multSL)

multSR :: (BaseTensor target, GoodScalar r)
       => ListR n (target (TKS '[] r)) -> target (TKS '[] r)
multSR = foldr1 (*)

crevSR
  :: SNat n -> ListR n (Concrete (TKS '[] Double))
  -> ListR n (Concrete (TKS '[] Double))
crevSR snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  cgrad (kfromS . multSR)

revSR
  :: SNat n -> ListR n (Concrete (TKS '[] Double))
  -> ListR n (Concrete (TKS '[] Double))
revSR snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  grad (kfromS . multSR)

multSNotShared :: (BaseTensor target, GoodScalar r)
               => ListR n (ADVal target (TKS '[] r))
               -> ADVal target (TKS '[] r)
multSNotShared = foldr1 multNotShared

crevSNotShared
  :: SNat n -> ListR n (Concrete (TKS '[] Double))
  -> ListR n (Concrete (TKS '[] Double))
crevSNotShared snat@SNat =
  withKnownSTK (stkOfListR (knownSTK @(TKS '[] Double)) snat) $
  cgrad (kfromS . multSNotShared)

{- TODO: re-enable once -fpolymorphic-specialisation works

-- KnownNat and AstSpan are tag types, so it's fine not to specialize
-- for them. Some of the other classes come from existential types,
-- some of which it's not advantageous to specialize.
--
-- This is expected to fail with -O0 and to pass with -O1
-- and -fpolymorphic-specialisation.
-- This prevents running benchmarks without optimization, which is a good thing.
inspect $ hasNoTypeClassesExcept 'crevScalarL [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt]
inspect $ hasNoTypeClassesExcept 'revScalarL [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt,      ''AstSpan, ''RealFloatH, ''Nested.FloatElt, ''Fractional, ''Floating, ''IntegralH, ''RealFrac, ''Real, ''Nested.Storable, ''Integral]
inspect $ hasNoTypeClassesExcept 'crevScalarNotShared [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt]
inspect $ hasNoTypeClassesExcept 'crevSL [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt, ''Nested.Storable,    ''ShareTensor]
inspect $ hasNoTypeClassesExcept 'revSL [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt,      ''AstSpan, ''RealFloatH, ''Nested.FloatElt, ''Fractional, ''Floating, ''IntegralH, ''RealFrac, ''Real, ''Nested.Storable, ''Integral]
inspect $ hasNoTypeClassesExcept 'crevSMapAccum [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt, ''LetTensor, ''BaseTensor, ''ConvertTensor, ''Boolean, ''CommonTargetEqOrd, ''AllTargetShow, ''ShareTensor]
inspect $ hasNoTypeClassesExcept 'revSMapAccum [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt, ''LetTensor, ''BaseTensor, ''ConvertTensor, ''Boolean, ''CommonTargetEqOrd, ''AllTargetShow, ''ShareTensor,      ''AstSpan, ''RealFloatH, ''Nested.FloatElt, ''Fractional, ''Floating, ''IntegralH, ''RealFrac, ''Real, ''Nested.Storable, ''Integral]
inspect $ hasNoTypeClassesExcept 'crevScalarMapAccum [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt, ''LetTensor, ''BaseTensor, ''ConvertTensor, ''Boolean, ''CommonTargetEqOrd, ''AllTargetShow, ''ShareTensor]
inspect $ hasNoTypeClassesExcept 'revScalarMapAccum [''(~), ''KnownNat, ''WithDict, ''KnownShS, ''AdaptableTarget, ''RandomValue, ''KnownSTK, ''GoodScalar, ''Num, ''Show, ''Ord, ''Eq, ''Nested.PrimElt, ''Nested.KnownElt, ''Nested.NumElt, ''Typeable, ''IfDifferentiable, ''NFData, ''Default.Default, ''Nested.Elt, ''LetTensor, ''BaseTensor, ''ConvertTensor, ''Boolean, ''CommonTargetEqOrd, ''AllTargetShow, ''ShareTensor,      ''AstSpan, ''RealFloatH, ''Nested.FloatElt, ''Fractional, ''Floating, ''IntegralH, ''RealFrac, ''Real, ''Nested.Storable, ''Integral]
-- inspect $ coreOf 'revScalarL
-}
