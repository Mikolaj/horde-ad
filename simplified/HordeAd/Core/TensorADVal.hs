{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | 'Tensor' class instances for dual number. The dual numbers are built
-- either from concrete floats or from 'Ast' term.
module HordeAd.Core.TensorADVal
  ( ADValClown
  ) where

import Prelude hiding ((<*))

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Boolean
import           Data.List (foldl1')
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.Delta
import           HordeAd.Core.DualClass
import           HordeAd.Core.DualNumber
import           HordeAd.Core.ShapedList (ShapedList (..))
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorClass
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)

-- * Assorted instances for any functor argument

type instance BooleanOf (ADVal f r z) = BooleanOf (f r z)

-- Boolean and numeric instances are easy to define for ADVal f r z
-- and then Clown, Flip and other instances are auto-derived on top of them.
-- OTOH, AdaptableDomains and other such instances are best defined
-- directly for Clown and others applied to ADVal.
instance (EqB (f r z), IsPrimal f r z) => EqB (ADVal f r z) where
  D l1 u _ ==* D l2 v _ = letWrapPrimal l1 u ==* letWrapPrimal l2 v
  D l1 u _ /=* D l2 v _ = letWrapPrimal l1 u /=* letWrapPrimal l2 v

instance (OrdB (f r z), IsPrimal f r z) => OrdB (ADVal f r z) where
  D l1 u _ <* D l2 v _ = letWrapPrimal l1 u <* letWrapPrimal l2 v
  D l1 u _ <=* D l2 v _ = letWrapPrimal l1 u <=* letWrapPrimal l2 v
  D l1 u _ >* D l2 v _ = letWrapPrimal l1 u >* letWrapPrimal l2 v
  D l1 u _ >=* D l2 v _ = letWrapPrimal l1 u >=* letWrapPrimal l2 v

instance IfB (ADVal (Flip OR.Array) r n) where
  ifB b v w = if b then v else w

type ADValClown dynamic = Flip (ADVal (Clown dynamic)) '()

type instance IntOf (ADVal f r n) = IntOf (f r n)

type instance PrimalOf (ADVal f) = f

type instance DualOf (ADVal f) = Product (Clown ADShare) (Dual f)

type instance DynamicOf (ADVal f) = ADValClown (DynamicOf f)


-- * Ranked tensor instances

-- This requires the Tensor instance, hence the definitions must in this module.
instance (KnownNat n, GoodScalar r)
         => IfB (ADVal AstRanked r n) where
  ifB b v w = index (fromList [v, w]) (singletonIndex $ ifB b 0 1)

-- TODO: speed up by using tindex0R and dIndex0 if the codomain is 0
-- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
-- dimension affected.
--
-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
index :: forall ranked shaped m n r.
         ( Tensor ranked, IsPrimal ranked r n
         , Dual ranked ~ DeltaR ranked shaped
         , KnownNat m, KnownNat n, GoodScalar r )
      => ADVal ranked r (m + n) -> IndexOf (ranked r 0) m
      -> ADVal ranked r n
index (D l u u') ix = dD l (tindex u ix) (IndexR u' ix (tshape u))

fromList :: ( Tensor ranked, IsPrimal ranked r (1 + n)
            , Dual ranked ~ DeltaR ranked shaped
            , KnownNat n, GoodScalar r )
         => [ADVal ranked r n]
         -> ADVal ranked r (1 + n)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (flattenADShare $ map ((\(D l _ _) -> l)) lu)
     (tfromList $ map (\(D _ u _) -> u) lu)
     (FromListR $ map (\(D _ _ u') -> u') lu)

instance ( KnownNat n, GoodScalar r, dynamic ~ DynamicOf ranked
         , Dual ranked ~ DeltaR ranked shaped
         , Dual (Clown dynamic) ~ DeltaD ranked shaped
         , ConvertTensor ranked shaped )
         => AdaptableDomains (ADValClown dynamic)
                             (ADVal ranked r n) where
  type Underlying (ADVal ranked r n) = r
  type Value (ADVal ranked r n) = Flip OR.Array r n  -- !!! not ranked
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (a, rest) -> Just (dToR (runFlip a), rest)
    Nothing -> Nothing

dToR :: forall ranked shaped n r.
        ( ConvertTensor ranked shaped
        , Dual ranked ~ DeltaR ranked shaped
        , Dual (Clown (DynamicOf ranked)) ~ DeltaD ranked shaped
        , KnownNat n, GoodScalar r )
      => ADVal (Clown (DynamicOf ranked)) r '() -> ADVal ranked r n
dToR (D l u u') = dDnotShared l (tfromD $ runClown u) (dDToR u')
 where
  dDToR (RToD @_ @_ @n1 d) =
    case sameNat (Proxy @n1) (Proxy @n) of
      Just Refl -> d
      _ -> error "dToR: different ranks in DToR(RToD)"
  dDToR d = DToR d

class (forall r15 y. (KnownNat y, GoodScalar r15) => c ranked r15 y)
      => CRankedIP ranked c where
instance (forall r15 y. (KnownNat y, GoodScalar r15) => c ranked r15 y)
         => CRankedIP ranked c where

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( Dual ranked ~ DeltaR ranked shaped
         , DeltaR ranked shaped ~ Dual ranked
         , CRankedIP ranked IsPrimalPart
         , CRankedIP ranked CanRecordSharing
         , Tensor ranked )
         => Tensor (ADVal ranked) where
  tlet (D l u u') f =
    let (l2, var2) = recordSharingPrimal u l
    in f (D l2 var2 u')
      -- TODO: What about sharing u'?

  tshape (D _ u _) = tshape u
  -- This is very slow, but is fortunately not needed:
  -- tshape (D l u _) = tshape (tletWrap l u)
  tminIndex0 (D l u _) = tminIndex0 (tletWrap l u)
  tmaxIndex0 (D l u _) = tmaxIndex0 (tletWrap l u)
  tfloor (D l u _) = tfloor (tletWrap l u)

  tindex v ix = index v ix
  tsum (D l u u') = dD l (tsum u) (SumR (tlength u) u')
  tsum0 (D l u u') = dD l (tsum0 u) (Sum0R (tshape u) u')
  tdot0 (D l1 ue u') (D l2 ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (tdot0 u v) (dAdd (Dot0R v u') (Dot0R u v'))
  tfromIndex0 = \ix -> dDnotShared emptyADShare (tfromIndex0 ix) dZero
  tscatter sh (D l u u') f =
    dD l (tscatter sh u f) (ScatterR sh u' f (tshape u))

  tfromList = fromList
  tfromVector lu =
    dD (flattenADShare $ map ((\(D l _ _) -> l)) $ V.toList lu)
       (tfromVector $ V.map (\(D _ u _) -> u) lu)
       (FromVectorR $ V.map (\(D _ _ u') -> u') lu)
  treplicate k (D l u u') = dD l (treplicate k u) (ReplicateR k u')
  tappend (D l1 u u') (D l2 v v') =
    dD (l1 `mergeADShare` l2) (tappend u v) (AppendR u' (tlength u) v')
  tslice i n (D l u u') = dD l (tslice i n u) (SliceR i n u' (tlength u))
  treverse (D l u u') = dD l (treverse u) (ReverseR u')
  ttranspose perm (D l u u') = dD l (ttranspose perm u) (TransposeR perm u')
  treshape :: forall n m r. (GoodScalar r, KnownNat n, KnownNat m)
           => ShapeInt m -> ADVal ranked r n -> ADVal ranked r m
  treshape sh t@(D l u u') = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == tshape u -> t
    _ -> dD l (treshape sh u) (ReshapeR (tshape u) sh u')
  tbuild1 k f = fromList $ map (f . fromIntegral) [0 .. k - 1]
                   -- element-wise (POPL) version
  tgather sh (D l u u') f =
    dD l (tgather sh u f) (GatherR sh u' f (tshape u))

  tsumOfList lu =
    dD (flattenADShare $ map (\(D l _ _) -> l) lu)
       (tsumOfList $ map (\(D _ u _) -> u) lu)
       (foldl1' dAdd $ map (\(D _ _ u') -> u') lu)
  tmult (D l1 ue ZeroR) (D l2 ve v') =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dScale u v')
  tmult (D l1 ue u') (D l2 ve ZeroR) =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dScale v u')
  tmult d e = d * e
  tconst t = dDnotShared emptyADShare (tconstBare t) dZero
  raddDynamic = undefined

  tconstant t = dDnotShared emptyADShare t dZero
  tprimalPart (D l u _) = tletWrap l u
  tdualPart (D l _ u') = Pair (Clown l) u'
  tD ast (Pair (Clown l) delta) = dD l ast delta
  tScale ast (Pair l delta) = Pair l (dScale ast delta)


-- * Shaped tensor instances

-- This requires the Tensor instance, hence the definitions must in this module.
instance (GoodScalar r, OS.Shape sh)
         => IfB (ADVal AstShaped r sh) where
  ifB b v w = indexS (fromListS @2 [v, w]) (ifB b 0 1 :$: ZSH)

-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
indexS :: forall ranked shaped sh1 sh2 r.
          ( ShapedTensor shaped, IsPrimal shaped r sh2
          , Dual shaped ~ DeltaS ranked shaped
          , OS.Shape sh1, OS.Shape sh2, OS.Shape (sh1 OS.++ sh2), GoodScalar r )
       => ADVal shaped r (sh1 OS.++ sh2) -> IndexSh (shaped r '[]) sh1
       -> ADVal shaped r sh2
indexS (D l u u') ix = dD l (sindex u ix) (IndexS u' ix)

fromListS :: forall n sh ranked shaped r.
             ( ShapedTensor shaped, IsPrimal shaped r (n ': sh)
             , Dual shaped ~ DeltaS ranked shaped
             , KnownNat n, OS.Shape sh, GoodScalar r )
           => [ADVal shaped r sh]
           -> ADVal shaped r (n ': sh)
fromListS lu =
  dD (flattenADShare $ map ((\(D l _ _) -> l)) lu)
     (sfromList $ map (\(D _ u _) -> u) lu)
     (FromListS $ map (\(D _ _ u') -> u') lu)

instance ( GoodScalar r, dynamic ~ DynamicOf shaped
         , ConvertTensor ranked shaped )
         => AdaptableDomains (ADValClown dynamic)
                             (ADVal shaped r sh) where
  type Underlying (ADVal shaped r sh) = r
  type Value (ADVal shaped r sh) = Flip OS.Array r sh  -- !!! not shaped
  toDomains = undefined
  fromDomains = undefined

dToS :: forall ranked shaped sh r.
        ( ConvertTensor ranked shaped
        , Dual shaped ~ DeltaS ranked shaped
        , Dual (Clown (DynamicOf ranked)) ~ DeltaD ranked shaped
        , OS.Shape sh, GoodScalar r )
      => ADVal (Clown (DynamicOf ranked)) r '() -> ADVal shaped r sh
dToS (D l u u') = dDnotShared l (sfromD $ runClown u) (dDToS u')
 where
  dDToS (SToD @_ @_ @sh1 d) =
    case sameShape @sh1 @sh of
      Just Refl -> d
      _ -> error "dToS: different ranks in DToS(SToD)"
  dDToS d = DToS d

class (forall r15 y. GoodScalar r15 => c shaped r15 y)
      => CRankedIPS shaped c where
instance (forall r15 y. GoodScalar r15 => c shaped r15 y)
         => CRankedIPS shaped c where

class (forall r55 y. (GoodScalar r55, OS.Shape y) => c shaped r55 y)
      => CRankedIPSh shaped c where
instance (forall r55 y. (GoodScalar r55, OS.Shape y) => c shaped r55 y)
         => CRankedIPSh shaped c where

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( Dual shaped ~ DeltaS ranked shaped
         , DeltaS ranked shaped ~ Dual shaped
         , CRankedIPSh shaped IsPrimalPart
         , CRankedIPS shaped CanRecordSharing
         , ShapedTensor shaped )
         => ShapedTensor (ADVal shaped) where
  slet (D l u u') f =
    let (l2, var2) = recordSharingPrimal u l
    in f (D l2 var2 u')
      -- TODO: What about sharing u'?

  -- This is very slow, but is fortunately not needed:
  -- tshape (D l u _) = tshape (tletWrap l u)
  sminIndex0 (D l u _) = sminIndex0 (sletWrap l u)
  smaxIndex0 (D l u _) = smaxIndex0 (sletWrap l u)
  sfloor (D l u _) = sfloor (sletWrap l u)

  sindex v ix = indexS v ix
  ssum (D l u u') = dD l (ssum u) (SumS u')
  ssum0 (D l u u') = dD l (ssum0 u) (Sum0S u')
  sdot0 (D l1 ue u') (D l2 ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (sdot0 u v) (dAdd (Dot0S v u') (Dot0S u v'))
  sfromIndex0 = \ix -> dDnotShared emptyADShare (sfromIndex0 ix) dZero
  sscatter (D l u u') f = dD l (sscatter u f) (ScatterS u' f)

  sfromList = fromListS
  sfromVector lu =
    dD (flattenADShare $ map ((\(D l _ _) -> l)) $ V.toList lu)
       (sfromVector $ V.map (\(D _ u _) -> u) lu)
       (FromVectorS $ V.map (\(D _ _ u') -> u') lu)
  sreplicate (D l u u') = dD l (sreplicate u) (ReplicateS u')
  sappend (D l1 u u') (D l2 v v') =
    dD (l1 `mergeADShare` l2) (sappend u v) (AppendS u' v')
  sslice (i_proxy :: Proxy i) n_proxy (D l u u') =
    dD l (sslice i_proxy n_proxy u) (SliceS @ranked @shaped @i u')
  sreverse (D l u u') = dD l (sreverse u) (ReverseS u')
  stranspose (perm_proxy :: Proxy perm) (D l u u') =
    dD l (stranspose perm_proxy u) (TransposeS @ranked @shaped @perm u')
  sreshape :: forall sh sh2 r.
              ( GoodScalar r, OS.Shape sh, OS.Shape sh2
              , OS.Size sh ~ OS.Size sh2 )
           => ADVal shaped r sh -> ADVal shaped r sh2
  sreshape t@(D l u u') = case sameShape @sh2 @sh of
    Just Refl -> t
    _ -> dD l (sreshape u) (ReshapeS u')
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, OS.Shape sh)
          => (IntSh (ADVal shaped r '[]) n -> ADVal shaped r sh)
          -> ADVal shaped r (n ': sh)
  sbuild1 f = fromListS $ map (f . ShapedList.shapedNat)
                              [0 .. valueOf @n - 1]
                   -- element-wise (POPL) version
  sgather (D l u u') f = dD l (sgather u f) (GatherS u' f)

  ssumOfList lu =
    dD (flattenADShare $ map (\(D l _ _) -> l) lu)
       (ssumOfList $ map (\(D _ u _) -> u) lu)
       (foldl1' dAdd $ map (\(D _ _ u') -> u') lu)
  smult (D l1 ue ZeroS) (D l2 ve v') =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dScale u v')
  smult (D l1 ue u') (D l2 ve ZeroS) =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dScale v u')
  smult d e = d * e
  sconst t = dDnotShared emptyADShare (sconstBare t) dZero
  saddDynamic = undefined

  sconstant t = dDnotShared emptyADShare t dZero
  sprimalPart (D l u _) = sletWrap l u
  sdualPart (D l _ u') = Pair (Clown l) u'
  sD ast (Pair (Clown l) delta) = dD l ast delta
  sScale ast (Pair l delta) = Pair l (dScale ast delta)


-- * ConvertTensor instance

instance ( Dual ranked ~ DeltaR ranked shaped
         , Dual shaped ~ DeltaS ranked shaped
         , Dual (Clown (DynamicOf ranked)) ~ DeltaD ranked shaped
         , ConvertTensor ranked shaped )
         => ConvertTensor (ADVal ranked)
                          (ADVal shaped) where
  tfromD = dToR . runFlip
  tfromS = sToR
   where
    sToR :: forall r sh. (GoodScalar r, OS.Shape sh)
         => ADVal shaped r sh -> ADVal ranked r (OS.Rank sh)
    sToR (D l u u') = dDnotShared l (tfromS u) (dSToR u')
     where
      dSToR (RToS @_ @_ @sh1 d) =
        case sameShape @sh1 @sh of
          Just Refl -> d
          _ -> error "sToR: different shapes in SToR(RToS)"
      dSToR d = SToR d
        -- TODO: add all the other optimizations about not storing
        -- trivial conversions on tape
  dfromR = Flip . rToD
   where
    rToD (D l u u') = dDnotShared l (Clown $ dfromR u) (RToD u')
  dfromS = Flip . sToD
   where
    sToD (D l u u') = dDnotShared l (Clown $ dfromS u) (SToD u')
  sfromD = dToS . runFlip
  sfromR = rToS
   where
    rToS (D l u u') = dDnotShared l (sfromR u) (RToS u')
  ddummy = undefined
  disDummy = undefined
  dshape = undefined


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
  :: ( Tensor ranked, KnownNat n, GoodScalar r
     , Dual ranked ~ DeltaR ranked shaped
     , IsPrimal ranked r (1 + n) )
  => Int -> (IntOf (ranked r 0) -> ADVal ranked r n)
  -> ADVal ranked r (1 + n)
_build1Closure k f =  -- stores closures on tape
  let g i = let D _ u _ = f i in u
      h i = let D _ _ u' = f i in u'
  in dD emptyADShare (tbuild1 k g) (BuildR k h)
