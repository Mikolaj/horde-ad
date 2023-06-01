{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | 'Tensor' class instances for dual number. The dual numbers are built
-- either from concrete floats or from 'Ast' term.
module HordeAd.Core.TensorADVal
  (
  ) where

import Prelude hiding ((<*))

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Bifunctor.Tannen
import           Data.Boolean
import           Data.Functor.Compose
import           Data.List (foldl1')
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))

import HordeAd.Core.Ast
import HordeAd.Core.Delta
import HordeAd.Core.Adaptor
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

type instance BooleanOf (ADVal a) = BooleanOf a

instance (EqB a, IsPrimal a) => EqB (ADVal a) where
  D l1 u _ ==* D l2 v _ = letWrapPrimal l1 u ==* letWrapPrimal l2 v
  D l1 u _ /=* D l2 v _ = letWrapPrimal l1 u /=* letWrapPrimal l2 v

instance (OrdB a, IsPrimal a) => OrdB (ADVal a) where
  D l1 u _ <* D l2 v _ = letWrapPrimal l1 u <* letWrapPrimal l2 v
  D l1 u _ <=* D l2 v _ = letWrapPrimal l1 u <=* letWrapPrimal l2 v
  D l1 u _ >* D l2 v _ = letWrapPrimal l1 u >* letWrapPrimal l2 v
  D l1 u _ >=* D l2 v _ = letWrapPrimal l1 u >=* letWrapPrimal l2 v

instance IfB (ADVal (OR.Array n r)) where
  ifB b v w = if b then v else w

instance IfB (ADVal (Flip OR.Array r n)) where
  ifB b v w = if b then v else w

-- This requires the Tensor instance, hence the definitions must be here.
instance (KnownNat n, GoodScalar r)
         => IfB (ADVal (Ast n r)) where
  ifB b v w = indexZ (fromList [v, w]) (singletonIndex $ ifB b 0 1)

instance AdaptableDomains (Compose ADVal OD.Array) (ADVal Double) where
  type Underlying (ADVal Double) = Double
  type Value (ADVal Double) = Double
  toDomains = undefined
  fromDomains = undefined

instance AdaptableDomains (Compose ADVal OD.Array) (ADVal Float) where
  type Underlying (ADVal Float) = Float
  type Value (ADVal Float) = Float
  toDomains = undefined
  fromDomains = undefined

instance (KnownNat n, GoodScalar r)
         => AdaptableDomains (Compose ADVal OD.Array)
                             (ADVal (Flip OR.Array r n)) where
  type Underlying (ADVal (Flip OR.Array r n)) = r
  type Value (ADVal (Flip OR.Array r n)) = Flip OR.Array r n
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (a, rest) -> Just (fromD $ getCompose a, rest)
    Nothing -> Nothing

instance GoodScalar r
         => AdaptableDomains (Compose ADVal dynamic)
                             (Compose ADVal dynamic r) where
  type Underlying (Compose ADVal dynamic r) = r
  type Value (Compose ADVal dynamic r) = dynamic r
  toDomains = undefined
  fromDomains _aInit = V.uncons

instance ( KnownNat n, GoodScalar r
         , ConvertTensor dynamic ranked shaped, HasConversions dynamic ranked )
         => AdaptableDomains (Compose ADVal dynamic)
                             (Compose ADVal (ranked r) n) where
  type Underlying (Compose ADVal (ranked r) n) = r
  type Value (Compose ADVal (ranked r) n) = ranked r n
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (a, rest) -> Just (Compose $ fromD $ getCompose a, rest)
    Nothing -> Nothing

instance ( KnownNat n, GoodScalar r
         , ConvertTensor dynamic ranked shaped, HasConversions dynamic ranked )
         => AdaptableDomains (Compose ADVal dynamic)
                             (Tannen ADVal ranked r n) where
  type Underlying (Tannen ADVal ranked r n) = r
  type Value (Tannen ADVal ranked r n) = ranked r n
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (a, rest) -> Just (Tannen $ fromD $ getCompose a, rest)
    Nothing -> Nothing

instance (KnownNat n, GoodScalar r)
         => AdaptableDomains (Compose ADVal AstDynamic)
                             (ADVal (Ast n r)) where
  type Underlying (ADVal (Ast n r)) = r
  type Value (ADVal (Ast n r)) = Flip OR.Array r n
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (a, rest) -> Just (fromD $ getCompose a, rest)
    Nothing -> Nothing

class ( Dual (ranked r y) ~ DeltaR ranked r y
      , DeltaR ranked r y ~ Dual (ranked r y) )
      => DualIsDeltaR ranked r y where
instance ( Dual (ranked r y) ~ DeltaR ranked r y
         , DeltaR ranked r y ~ Dual (ranked r y) )
         => DualIsDeltaR ranked r y where

class (forall r12 y. (KnownNat y, GoodScalar r12) => c ranked r12 y) => CYRanked ranked c where
instance (forall r12 y. (KnownNat y, GoodScalar r12) => c ranked r12 y) => CYRanked ranked c where

class (Underlying a ~ Underlying b)  -- TODO:errors:Underlying b ~ Underlying a)
      => UnderlyingMatches2 a b where
instance (Underlying a ~ Underlying b)
         => UnderlyingMatches2 a b where

class (forall r13 x y. (KnownNat y, GoodScalar r13) => c (ranked r13 x) (ranked r13 y))
      => CRanked2 ranked c where
instance (forall r13 x y. (KnownNat y, GoodScalar r13) => c (ranked r13 x) (ranked r13 y))
         => CRanked2 ranked c where

class (Underlying a ~ b, b ~ Underlying a)
      => UnderlyingMatches a b where
instance (Underlying a ~ b, b ~ Underlying a)
         => UnderlyingMatches a b where

class (forall r14 y. (KnownNat y, GoodScalar r14) => c (ranked r14 y) r14)
      => CRankedR ranked c where
instance (forall r14 y. (KnownNat y, GoodScalar r14) => c (ranked r14 y) r14)
         => CRankedR ranked c where

class (forall r15 y. (KnownNat y, GoodScalar r15) => c (ranked r15 y))
      => CRanked ranked c where
instance (forall r15 y. (KnownNat y, GoodScalar r15) => c (ranked r15 y))
         => CRanked ranked c where

type instance IntOf (Tannen ADVal ranked r n) = IntOf (ranked r n)

type instance PrimalOf (Tannen ADVal ranked) = ranked

type instance DualOf (Tannen ADVal ranked) = Product (Clown ADShare)
                                                     (DeltaR ranked)

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( CRanked2 ranked UnderlyingMatches2
         , CYRanked ranked DualIsDeltaR
         , CRankedR ranked UnderlyingMatches
         , CRanked ranked IsPrimal
         , CRanked ranked Num
         , CRanked ranked Show
         , HasRanks ranked
         , Tensor ranked )
         => Tensor (Tannen ADVal ranked) where
  tlet (Tannen (D l u u')) f =
    let (l2, var2) = recordSharingPrimal u l
    in f (Tannen (D l2 var2 u'))
      -- TODO: What about sharing u'?

  tshape (Tannen (D _ u _)) = tshape u
  -- This is very slow, but is fortunately not needed:
  -- tshape (D l u _) = tshape (tletWrap l u)
  tminIndex0 (Tannen (D l u _)) = tminIndex0 (tletWrap l u)
  tmaxIndex0 (Tannen (D l u _)) = tmaxIndex0 (tletWrap l u)
  tfloor (Tannen (D l u _)) = tfloor (tletWrap l u)

  tindex v ix = Tannen $ indexZ (runTannen v) ix
  tsum = Tannen . sum' . runTannen
  tsum0 = Tannen . sum0 . runTannen
  tdot0 u v = Tannen $ dot0 (runTannen u) (runTannen v)
  tfromIndex0 ix = Tannen $ dDnotShared emptyADShare (tfromIndex0 ix) dZero
  tscatter sh t f = Tannen $ scatterNClosure sh (runTannen t) f

  tfromList = Tannen . fromList . map runTannen
--  tfromList0N = fromList0N
  tfromVector = Tannen . fromVector . V.map runTannen
--  tfromVector0N = fromVector0N
  treplicate k = Tannen . replicate' k . runTannen
--  treplicate0N sh = replicate0N sh . unScalar
  tappend u v = Tannen $ append (runTannen u) (runTannen v)
  tslice i k = Tannen . slice i k . runTannen
  treverse = Tannen . reverse' . runTannen
  ttranspose perm = Tannen . transpose perm . runTannen
  treshape sh = Tannen . reshape sh . runTannen
  tbuild1 k f = Tannen $ build1 k (runTannen . f)
  tgather sh t f = Tannen $ gatherNClosure sh (runTannen t) f

  tsumOfList lu =
    Tannen $ dD (flattenADShare $ map ((\(Tannen (D l _ _)) -> l)) lu)
                (tsumOfList $ map (\(Tannen (D _ u _)) -> u) lu)
                (foldl1' dAdd $ map (\(Tannen (D _ _ u')) -> u') lu)

  -- For whatever reason this signature is necessary to type-check this.
  tmult :: forall n r.
           (KnownNat n, GoodScalar r, Dual (ranked r n) ~ DeltaR ranked r n)
        => Tannen ADVal ranked r n -> Tannen ADVal ranked r n
        -> Tannen ADVal ranked r n
  tmult (Tannen (D l1 ue ZeroR)) (Tannen (D l2 ve v')) =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in Tannen $ dD l4 (u * v) (dScale u v')
  tmult (Tannen (D l1 ue u')) (Tannen (D l2 ve ZeroR)) =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in Tannen $ dD l4 (u * v) (dScale v u')
  tmult d e = Tannen $ runTannen d * runTannen e
  tconst t = Tannen $ dDnotShared emptyADShare (tconstBare t) dZero

  tconstant t = Tannen $ dDnotShared emptyADShare t dZero
  tprimalPart (Tannen (D l u _)) = tletWrap l u
  tdualPart (Tannen (D l _ u')) = Pair (Clown l) u'
  tD ast (Pair (Clown l) delta) = Tannen $ dD l ast delta
  tScale ast (Pair l delta) = Pair l (dScale ast delta)

instance (HasConversions dynamic ranked, ConvertTensor dynamic ranked shaped)
         => ConvertTensor (Compose ADVal dynamic)
                          (Tannen ADVal ranked)
                          (Tannen ADVal shaped) where
  tfromD = Tannen . fromD . getCompose
  tfromS = undefined
  dfromR = Compose . fromR . runTannen
  dfromS = undefined
  sfromR = undefined
  sfromD = undefined
  ddummy = undefined
  disDummy = undefined
  daddR = undefined
  dshape = undefined


-- * ADVal combinators generalizing ranked tensor operations

sum0 :: ( Tensor ranked, HasRanks ranked, IsPrimal (ranked r 0), KnownNat n, GoodScalar r
        , Underlying (ranked r 0) ~ Underlying (ranked r n) )
     => ADVal (ranked r n) -> ADVal (ranked r 0)
sum0 (D l u u') = dD l (tsum0 u) (dSum0 (tshape u) u')

dot0 :: ( Show (ranked r n), Tensor ranked, HasRanks ranked, IsPrimal (ranked r n), IsPrimal (ranked r 0)
        , KnownNat n, GoodScalar r, Underlying (ranked r 0) ~ Underlying (ranked r n) )
     => ADVal (ranked r n) -> ADVal (ranked r n) -> ADVal (ranked r 0)
dot0 (D l1 ue u') (D l2 ve v') =
  -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
  let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
      !(!l4, v) = recordSharingPrimal ve l3
  in dD l4 (tdot0 u v) (dAdd (dDot0 v u') (dDot0 u v'))

-- TODO: speed up by using tindex0R and dIndex0 if the codomain is 0
-- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
-- dimension affected.
--
-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
indexZ :: forall ranked m n r.
          ( Tensor ranked, HasRanks ranked, IsPrimal (ranked r n), KnownNat m, KnownNat n, GoodScalar r
          , Underlying (ranked r (m + n)) ~ Underlying (ranked r n) )
       => ADVal (ranked r (m + n)) -> IndexOf (ranked r 0) m
       -> ADVal (ranked r n)
indexZ (D l u u') ix = dD l (tindex u ix) (dIndexZ u' ix (tshape u))

sum' :: ( Tensor ranked, HasRanks ranked, IsPrimal (ranked r n), KnownNat n, GoodScalar r
        , Underlying (ranked r n) ~ Underlying (ranked r (1 + n)) )
     => ADVal (ranked r (1 + n)) -> ADVal (ranked r n)
sum' (D l u u') = dD l (tsum u) (dSumR (tlength u) u')

scatterNClosure
  :: ( Tensor ranked, HasRanks ranked, IsPrimal (ranked r (p + n))
     , KnownNat m, KnownNat p, KnownNat n, GoodScalar r
     , Underlying (ranked r (p + n)) ~ Underlying (ranked r (m + n)) )
  => ShapeInt (p + n) -> ADVal (ranked r (m + n))
  -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
  -> ADVal (ranked r (p + n))
scatterNClosure sh (D l u u') f =
  dD l (tscatter sh u f) (dScatterZ sh u' f (tshape u))

fromList :: ( Tensor ranked, HasRanks ranked, IsPrimal (ranked r (1 + n)), KnownNat n, GoodScalar r
            , Underlying (ranked r n) ~ Underlying (ranked r (1 + n)) )
         => [ADVal (ranked r n)]
         -> ADVal (ranked r (1 + n))
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (flattenADShare $ map ((\(D l _ _) -> l)) lu)
     (tfromList $ map (\(D _ u _) -> u) lu)
     (dFromListR $ map (\(D _ _ u') -> u') lu)

--fromList0N :: (Tensor ranked, KnownNat n)
--           => ShapeInt n -> [ADVal r]
--           -> ADVal (ranked r n)
--fromList0N sh l =
--  dD (tfromList0N sh $ map (\(D u _) -> u) l)  -- I hope this fuses
--     (dFromList01 sh $ map (\(D _ u') -> u') l)

fromVector :: ( Tensor ranked, HasRanks ranked, IsPrimal (ranked r (1 + n)), KnownNat n, GoodScalar r
              , Underlying (ranked r n) ~ Underlying (ranked r (1 + n)) )
           => Data.Vector.Vector (ADVal (ranked r n))
           -> ADVal (ranked r (1 + n))
fromVector lu =
  dD (flattenADShare $ map ((\(D l _ _) -> l)) $ V.toList lu)
     (tfromVector $ V.map (\(D _ u _) -> u) lu)
     (dFromVectorR $ V.map (\(D _ _ u') -> u') lu)

--fromVector0N :: (Tensor ranked, KnownNat n)
--             => ShapeInt n -> Data.Vector.Vector (ADVal r)
--             -> ADVal (ranked r n)
--fromVector0N sh l =
--  dD (tfromVector0N sh $ V.convert $ V.map (\(D u _) -> u) l)  -- hope it fuses
--     (dFromVector01 sh $ V.map (\(D _ u') -> u') l)

replicate' :: ( Tensor ranked, HasRanks ranked, IsPrimal (ranked r (1 + n)), KnownNat n, GoodScalar r
         , Underlying (ranked r n) ~ Underlying (ranked r (1 + n)) )
      => Int -> ADVal (ranked r n) -> ADVal (ranked r (1 + n))
replicate' k (D l u u') = dD l (treplicate k u) (dReplicateR k u')

--replicate0N :: (Tensor ranked, KnownNat n)
--        => ShapeInt n -> ADVal r -> ADVal (ranked r n)
--replicate0N sh (D u u') = dD (treplicate0N sh u) (dReplicate01 sh u')

append :: (Tensor ranked, HasRanks ranked, IsPrimal (ranked r (1 + n)), KnownNat n, GoodScalar r)
       => ADVal (ranked r (1 + n)) -> ADVal (ranked r (1 + n))
       -> ADVal (ranked r (1 + n))
append (D l1 u u') (D l2 v v') =
  dD (l1 `mergeADShare` l2) (tappend u v) (dAppendR u' (tlength u) v')

slice :: (Tensor ranked, HasRanks ranked, IsPrimal (ranked r (1 + n)), KnownNat n, GoodScalar r)
      => Int -> Int -> ADVal (ranked r (1 + n))
      -> ADVal (ranked r (1 + n))
slice i k (D l u u') = dD l (tslice i k u) (dSliceR i k u' (tlength u))

reverse' :: (Tensor ranked, HasRanks ranked, IsPrimal (ranked r (1 + n)), KnownNat n, GoodScalar r)
         => ADVal (ranked r (1 + n)) -> ADVal (ranked r (1 + n))
reverse' (D l u u') = dD l (treverse u) (dReverseR u')

transpose :: (Tensor ranked, HasRanks ranked, IsPrimal (ranked r n), KnownNat n, GoodScalar r)
          => Permutation -> ADVal (ranked r n) -> ADVal (ranked r n)
transpose perm (D l u u') = dD l (ttranspose perm u) (dTransposeR perm u')

reshape :: forall ranked n m r.
           ( Tensor ranked, HasRanks ranked, GoodScalar r, IsPrimal (ranked r m), KnownNat m, KnownNat n
           , Underlying (ranked r n) ~ Underlying (ranked r m) )
        => ShapeInt m -> ADVal (ranked r n) -> ADVal (ranked r m)
reshape sh t@(D l u u') = case sameNat (Proxy @m) (Proxy @n) of
  Just Refl | sh == tshape u -> t
  _ -> dD l (treshape sh u) (dReshapeR (tshape u) sh u')

build1
  :: ( Tensor ranked, HasRanks ranked, KnownNat n, GoodScalar r, IsPrimal (ranked r (1 + n))
     , Underlying (ranked r n) ~ Underlying (ranked r (1 + n)) )
  => Int -> (IntOf (ranked r 0) -> ADVal (ranked r n))
  -> ADVal (ranked r (1 + n))
build1 k f = fromList $ map (f . fromIntegral) [0 .. k - 1]
               -- element-wise (POPL) version

-- Strangely, this variant slows down simplifiedOnlyTest 3 times. Perhaps
-- that's because k is very low and the f functions are simple enough.
--
-- This does not work any more, because the dual numbers produced by f
-- are not simplified to transform ADShare, which breaks some pipelines.
-- Even if they were, the sharing would most likely be missing
-- or redundant or both.
--
-- This may be a problem with gatherNClosure, too, as soon as we have
-- integer sharing and it's shared in the whole transpose result.
_build1Closure
  :: (Tensor ranked, HasRanks ranked, KnownNat n, GoodScalar r, IsPrimal (ranked r (1 + n)))
  => Int -> (IntOf (ranked r 0) -> ADVal (ranked r n))
  -> ADVal (ranked r (1 + n))
_build1Closure k f =  -- stores closures on tape
  let g i = let D _ u _ = f i in u
      h i = let D _ _ u' = f i in u'
  in dD emptyADShare (tbuild1 k g) (dBuildR k h)

-- Note that if any index is out of bounds, the result of that particular
-- projection is defined and is 0 (but beware of vectorization).
gatherNClosure
  :: ( Tensor ranked, HasRanks ranked, IsPrimal (ranked r (m + n))
     , KnownNat m, KnownNat p, KnownNat n, GoodScalar r
     , Underlying (ranked r (p + n)) ~ Underlying (ranked r (m + n)) )
  => ShapeInt (m + n) -> ADVal (ranked r (p + n))
  -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
  -> ADVal (ranked r (m + n))
gatherNClosure sh (D l u u') f =
  dD l (tgather sh u f) (dGatherZ sh u' f (tshape u))

fromD :: forall dynamic ranked shaped n r.
         ( ConvertTensor dynamic ranked shaped, HasConversions dynamic ranked
         , KnownNat n, GoodScalar r )
       => ADVal (dynamic r) -> ADVal (ranked r n)
fromD (D l u u') = dDnotShared l (tfromD u) (dFromD u')

fromR :: ( ConvertTensor dynamic ranked shaped, HasConversions dynamic ranked
         , KnownNat n, GoodScalar r )
       => ADVal (ranked r n) -> ADVal (dynamic r)
fromR (D l u u') = dDnotShared l (dfromR u) (dFromR u')
