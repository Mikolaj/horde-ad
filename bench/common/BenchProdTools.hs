{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- {-# OPTIONS_GHC -ddump-stranal #-}
-- | A contrived benchmark: a product of a list of scalars.
module BenchProdTools where

import Prelude

import           Control.DeepSeq (NFData)
import           Criterion.Main
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.List (foldl1')
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Test.Inspection
import           Unsafe.Coerce (unsafeCoerce)

--import qualified Data.Array.ShapedS as OS
--import           HordeAd.Internal.TensorFFI (RowSum)
--import           Numeric.LinearAlgebra (Numeric)
--import           Type.Reflection (Typeable)

--import HordeAd.Core.Adaptor

import HordeAd
import HordeAd.Internal.TensorOps

deriving instance NFData (f a b) => NFData (Flip f b a)

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
        -> (([r], [Flip OR.Array r 0], Data.Vector.Vector (Flip OR.Array r 0))
            -> Benchmark)
        -> [r]
        -> Benchmark
envProd k f allxs =
  env (return $!
         let l = take (round k) allxs
             list = map (Flip . tscalarR) l
             vec :: Data.Vector.Vector (Flip OR.Array Double 0)
             vec = V.fromList list
         in (l, list, vec)) f

benchProd :: r ~ Double
          => ([r], [Flip OR.Array r 0], Data.Vector.Vector (Flip OR.Array r 0))
          -> [Benchmark]
benchProd ~(_l, list, vec) =
    [ bench "crev List" $ nf crevRankedListProd list
    , bench "rev List" $ nf revRankedListProd list
    , bench "r crev List" $ nf crevRankedListProdr list
    , bench "r rev List" $ nf revRankedListProdr list
-- commented out, because 5 times slower due to allocating a new vector
-- for each multiplication in fromDomains
--    , bench "crev Vec" $ nf (crev rankedVecProd) vec
-- and this costs the same, which means the initial creation of the vector
-- has a negligible cost, so we are creating such vectors below freely
--    , bench "crev List2Vec" $
--        nf (map (tunScalarR . runFlip) . V.toList . crev rankedVecProd)
--           (let list2 = map (Flip . tscalarR) l
--                vec2 :: Data.Vector.Vector (Flip OR.Array Double 0)
--                vec2 = V.fromList list2
--            in vec2)
    , bench "VecD crev" $
        let f :: DynamicExists OD.Array -> Flip OR.Array Double 0
            f = (\(DynamicExists @r2 d) ->
                   gcastWith (unsafeCoerce Refl :: r2 :~: Double) $
                   tfromD d)
        in nf (V.map f . fst
               . crevOnDomains @Double Nothing rankedVecDProd)
              (V.map (DynamicExists . dfromR) vec)
    , bench "NoShare List crev" $ nf (crev rankedNoShareListProd) list
    ]

rankedListProd :: (RankedTensor ranked, GoodScalar r)
               => [ranked r 0] -> ranked r 0
rankedListProd = foldl1' (*)

crevRankedListProd :: [Flip OR.Array Double 0] -> [Flip OR.Array Double 0]
crevRankedListProd = crev rankedListProd

revRankedListProd :: [Flip OR.Array Double 0] -> [Flip OR.Array Double 0]
revRankedListProd = rev @Double @0 @(AstRanked FullSpan) rankedListProd

rankedListProdr :: (RankedTensor ranked, GoodScalar r)
                => [ranked r 0] -> ranked r 0
rankedListProdr = foldr1 (*)

crevRankedListProdr :: [Flip OR.Array Double 0] -> [Flip OR.Array Double 0]
crevRankedListProdr = crev rankedListProdr

revRankedListProdr :: [Flip OR.Array Double 0] -> [Flip OR.Array Double 0]
revRankedListProdr = rev @Double @0 @(AstRanked FullSpan) rankedListProdr

_rankedVecProd :: (RankedTensor ranked, GoodScalar r)
               => Data.Vector.Vector (ranked r 0) -> ranked r 0
_rankedVecProd = V.foldl1' (*)

-- This one saves on running the adaptor and on comparing the scalar
-- type for each multiplication. The gain is small, the the major
-- cost must be the allocation and GC of a rank 0 tensor for each
-- minuscule operation that is benig performed.
--
-- Speeding up this one would require adding an extra API to Delta
-- that assumes a single r and so doesn't use DynamicExists.
-- Then we could try not converting to dynamic tensors.
-- Eventually, we could add another Delta GADT only for scalars
-- and use these instead of rank 0 tensors, but it's probably better
-- to add fold on tensors instead.
rankedVecDProd :: forall r ranked.
                  ( RankedTensor ranked, ConvertTensor ranked (ShapedOf ranked)
                  , GoodScalar r )
               => Domains (DynamicOf ranked) -> ranked r 0
rankedVecDProd = V.foldl' (\acc (DynamicExists @r2 d) ->
                             gcastWith (unsafeCoerce Refl :: r2 :~: r) $
                             tfromD d * acc) 0

rankedNoShareListProd :: GoodScalar r
                      => [ADVal (Flip OR.Array) r 0]
                      -> ADVal (Flip OR.Array) r 0
rankedNoShareListProd = foldl1' multNotShared

_rankedNoShareVecProd :: GoodScalar r
                      => Data.Vector.Vector (ADVal (Flip OR.Array) r 0)
                      -> ADVal (Flip OR.Array) r 0
_rankedNoShareVecProd = V.foldl1' multNotShared


-- Until new inspection-testing is released, this is commented out
-- belowis a dummy to prevent warnings.
{-
-- The GoodScalar and it's component occurrences are due to creating
-- a value of an existential type that satisfies GoodScalar,
-- so it's intended and not a specialization failure.
-- OTOH, KnownNat and AstSpan are tag types, so it's fine not to specialize
-- for them.
-- The numeric type classes in two of the cases are needed due
-- to the existential variables in AstRanked that show up, e.g., when
-- pattern matching on that type, dictionaries seen in the datatype
-- constructors.
inspect $ hasNoTypeClassesExcept 'crevRankedListProd [''GoodScalar, ''KnownNat, ''Sh.Shape, ''AstSpan, ''Show, ''Ord, ''Numeric, ''Num, ''RowSum, ''Typeable, ''IfDifferentiable, ''NFData, ''OD.Storable, ''AdaptableDomains, ''OS.Vector]
inspect $ hasNoTypeClassesExcept 'revRankedListProd [''GoodScalar, ''KnownNat, ''Sh.Shape, ''AstSpan, ''Show, ''Ord, ''Numeric, ''Num, ''RowSum, ''Typeable, ''IfDifferentiable, ''NFData, ''(~), ''OS.Permutation, ''OD.Storable, ''AdaptableDomains, ''OS.Vector]
inspect $ hasNoTypeClassesExcept 'crevRankedListProdr [''GoodScalar, ''KnownNat, ''Sh.Shape, ''AstSpan, ''Show, ''Ord, ''Numeric, ''Num, ''RowSum, ''Typeable, ''IfDifferentiable, ''NFData, ''OD.Storable, ''AdaptableDomains, ''OS.Vector]
inspect $ hasNoTypeClassesExcept 'revRankedListProdr [''GoodScalar, ''KnownNat, ''Sh.Shape, ''AstSpan, ''Show, ''Ord, ''Numeric, ''Num, ''RowSum, ''Typeable, ''IfDifferentiable, ''NFData, ''(~), ''OS.Permutation, ''OD.Storable, ''AdaptableDomains, ''OS.Vector]

-- OD.Storable is needed, for 9.4, only until new orthotope is released
-}

dummy :: ()
dummy = ()
inspect $ hasNoTypeClassesExcept 'dummy [''GoodScalar, ''KnownNat, ''AstSpan]
