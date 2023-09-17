{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for dual numbers. Most of the definitions
-- are generic over whether the dual numbers are built from concrete arrays
-- of floats or from AST terms. However, since we are not using
-- a middle layer such as "DualClass", separate instances are given
-- for ranked tensors and shaped tensors.
module HordeAd.Core.TensorADVal
  ( ADValClown
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Functor.Const
import           Data.List (foldl')
import           Data.List.Index (imap)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))
import           Type.Reflection (typeRep)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.Delta
import           HordeAd.Core.DualClass
import           HordeAd.Core.DualNumber
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape)
import           HordeAd.Util.ShapedList (ShapedList (..), singletonShaped)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * Assorted instances

type instance SimpleBoolOf (ADVal f) = SimpleBoolOf f

instance EqF f => EqF (ADVal f) where
  D l1 u _ ==. D l2 v _ = (l1 `mergeADShare` l2, snd $ u ==. v)
  D l1 u _ /=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u /=. v)

instance OrdF f => OrdF (ADVal f) where
  D l1 u _ <. D l2 v _ = (l1 `mergeADShare` l2, snd $ u <. v)
  D l1 u _ <=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u <=. v)
  D l1 u _ >. D l2 v _ = (l1 `mergeADShare` l2, snd $ u >. v)
  D l1 u _ >=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u >=. v)

type ADValClown dynamic = Flip (ADVal (Clown dynamic)) '()

type instance RankedOf (ADVal f) = ADVal (RankedOf f)

type instance ShapedOf (ADVal f) = ADVal (ShapedOf f)

type instance DynamicOf (ADVal f) = ADValClown (DynamicOf f)

type instance PrimalOf (ADVal f) = f

type instance DualOf (ADVal f) = Product (Clown (Const ADShare)) (Dual f)


-- * Ranked tensor instances

instance IfF (ADVal (Flip OR.Array)) where
  ifF (_, b) v w = if b then v else w

-- This requires the RankedTensor instance for ADVal, hence it must be
-- in this module.
instance IfF (ADVal (AstRanked PrimalSpan)) where
  ifF (l1, b) v w =
    let D l2 u u' = index (fromList [v, w])
                          (singletonIndex $ ifF (emptyADShare, b) 0 1)
    in D (l1 `mergeADShare` l2) u u'

-- TODO: speed up by using tindex0R and dIndex0 if the codomain is 0
-- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
-- dimension affected.
--
-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
index :: forall ranked shaped m n r.
         ( RankedTensor ranked, IsPrimal ranked r n
         , Dual ranked ~ DeltaR ranked shaped
         , KnownNat m, KnownNat n, GoodScalar r )
      => ADVal ranked r (m + n) -> IndexOf ranked m
      -> ADVal ranked r n
index (D l u u') ix = dD l (tindex u ix) (IndexR u' ix)

fromList :: ( RankedTensor ranked, IsPrimal ranked r (1 + n)
            , Dual ranked ~ DeltaR ranked shaped
            , KnownNat n, GoodScalar r )
         => [ADVal ranked r n]
         -> ADVal ranked r (1 + n)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (flattenADShare $ map (\(D l _ _) -> l) lu)
     (tfromList $ map (\(D _ u _) -> u) lu)
     (FromListR $ map (\(D _ _ u') -> u') lu)

instance ( KnownNat n, GoodScalar r, dynamic ~ DynamicOf ranked
         , Dual ranked ~ DeltaR ranked shaped
         , Dual (Clown dynamic) ~ DeltaD ranked shaped
         , ConvertTensor ranked shaped )
         => AdaptableDomains (ADValClown dynamic)
                             (ADVal ranked r n) where
  {-# SPECIALIZE instance
      KnownNat y
      => AdaptableDomains (ADValClown OD.Array)
                          (ADVal (Flip OR.Array) Double y) #-}
  {-# SPECIALIZE instance
      KnownNat y
      => AdaptableDomains (ADValClown (AstDynamic PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double y) #-}
  type Value (ADVal ranked r n) = Flip OR.Array r n  -- ! not Value(ranked)
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (DynamicExists @r2 a, rest) ->
      case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> let !aR = dToR @r (runFlip a)
                     in Just (aR, rest)
        _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

-- This is temporarily moved from Adaptor in order to specialize manually
instance AdaptableDomains dynamic a
         => AdaptableDomains dynamic [a] where
  {-# SPECIALIZE instance
      (KnownNat n, AdaptableDomains OD.Array (OR.Array n Double))
      => AdaptableDomains OD.Array
                          [OR.Array n Double] #-}
  {-# SPECIALIZE instance
      ( KnownNat n, AstSpan s
      , AdaptableDomains (AstDynamic s)
                         (AstRanked s Double n) )
      => AdaptableDomains (AstDynamic s)
                          [AstRanked s Double n] #-}
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableDomains (ADValClown OD.Array)
                          [ADVal (Flip OR.Array) Double n] #-}
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableDomains (ADValClown (AstDynamic PrimalSpan))
                          [ADVal (AstRanked PrimalSpan) Double n] #-}
  type Value [a] = [Value a]
  toDomains = V.concat . map toDomains
  fromDomains lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromDomains aInit restAcc of
            Just (a, rest) -> (a : lAcc, rest)
            Nothing -> error "fromDomains [a]"
        (l, !restAll) = foldl' f ([], source) lInit
        !rl = reverse l
    in Just (rl, restAll)
    -- is the following as performant? benchmark:
    -- > fromDomains lInit source =
    -- >   let f = swap . flip fromDomains
    -- >   in swap $ mapAccumL f source lInit

dToR :: forall r ranked shaped n.
        ( ConvertTensor ranked shaped
        , Dual ranked ~ DeltaR ranked shaped
        , Dual (Clown (DynamicOf ranked)) ~ DeltaD ranked shaped
        , KnownNat n, GoodScalar r )
      => ADVal (Clown (DynamicOf ranked)) r '() -> ADVal ranked r n
dToR (D l u u') = dDnotShared l (tfromD $ runClown u) (dDToR u')
 where
  dDToR (RToD @n1 d) =
    case sameNat (Proxy @n1) (Proxy @n) of
      Just Refl -> d
      _ -> error "dToR: different ranks in DToR(RToD)"
  dDToR (SToD @sh1 d) =
    case matchingRank @sh1 @n of
      Just Refl -> SToR d
      _ -> error "dToR: different ranks in DToR(SToD)"

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
         , PrimalOf ranked ~ ranked
         , ranked ~ PrimalOf ranked
         , CRankedIP ranked IsPrimal
         , RankedTensor ranked )
         => RankedTensor (ADVal ranked) where
  tlet (D l u u') f =
    let !(!l2, var2) = recordSharingPrimal u l
    in f (D l2 var2 u')
      -- u' doesn't need to be shared, because deltas are shared separately

  tshape (D _ u _) = tshape u
  -- This is very slow, but is fortunately not needed:
  -- tshape (D l u _) = tshape (tletWrap l u)
  --
  -- All underlying scalars supporting these operations
  -- result in empty delta expression, but it's still advantageous to store
  -- @l@ in the @D@ triple instead of in @u@ via @letWrap@.
  -- When, later on, these are to be treated as indexes, sprimalPart needs
  -- to be called, which moves @l@ to @u@ via @letWrap@.
  tminIndex (D l u _) =
    let v = tminIndex u
    in dDnotShared l v (dZeroOfShape v)
  tmaxIndex (D l u _) =
    let v = tmaxIndex u
    in dDnotShared l v (dZeroOfShape v)
  tfloor (D l u _) =
    let v = tfloor u
    in dDnotShared l v (dZeroOfShape v)

  tindex = index
  tsum (D l u u') = dD l (tsum u) (SumR u')
  tsum0 (D l u u') = dD l (tsum0 u) (Sum0R u')
  tdot0 (D l1 ue u') (D l2 ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (tdot0 u v) (dAdd (Dot0R v u') (Dot0R u v'))
  tscatter sh (D l u u') f =
    dD l (tscatter sh u f) (ScatterR sh u' f)

  tfromList = fromList
  tfromVector lu =
    dD (flattenADShare $ map (\(D l _ _) -> l) $ V.toList lu)
       (tfromVector $ V.map (\(D _ u _) -> u) lu)
       (FromVectorR $ V.map (\(D _ _ u') -> u') lu)
  tunravelToList (D l u u') =
    let lu = tunravelToList u
        f i ui = dD l ui (IndexR u' (singletonIndex $ fromIntegral i))
    in imap f lu
  treplicate k (D l u u') = dD l (treplicate k u) (ReplicateR k u')
  tappend (D l1 u u') (D l2 v v') =
    dD (l1 `mergeADShare` l2) (tappend u v) (AppendR u' v')
  tslice i n (D l u u') = dD l (tslice i n u) (SliceR i n u')
  treverse (D l u u') = dD l (treverse u) (ReverseR u')
  ttranspose perm (D l u u') = dD l (ttranspose perm u) (TransposeR perm u')
  treshape :: forall n m r. (GoodScalar r, KnownNat n, KnownNat m)
           => ShapeInt m -> ADVal ranked r n -> ADVal ranked r m
  treshape sh t@(D l u u') = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == tshape u -> t
    _ -> dD l (treshape sh u) (ReshapeR sh u')
  tbuild1 k f = fromList $ map (f . fromIntegral) [0 .. k - 1]
                   -- element-wise (POPL) version
  tgather sh (D l u u') f =
    dD l (tgather sh u f) (GatherR sh u' f)
  tcast (D l u u') = dD l (tcast u) (CastR u')
  tfromIntegral (D l u _) =
    let v = tfromIntegral u
    in dDnotShared l v (dZeroOfShape v)
  tconst t = constantADVal (tconst t)

  raddDynamic = undefined

  tconstant t = let (l, r) = tletUnwrap t in dDnotShared l r (dZeroOfShape r)
  tprimalPart (D l u _) = tletWrap l u
  tdualPart (D l _ u') = Pair (Clown (Const l)) u'
  tD ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = tletUnwrap ast
    in dD (l `mergeADShare` l2) r delta
  tScale ast (Pair  (Clown (Const l)) delta) =
    let (l2, r) = tletUnwrap ast
    in Pair (Clown (Const (l `mergeADShare` l2))) (dScale r delta)


-- * Shaped tensor instances

instance IfF (ADVal (Flip OS.Array)) where
  ifF (_, b) v w = if b then v else w

-- This requires the Tensor instance, hence the definitions must in this module.
instance IfF (ADVal (AstShaped PrimalSpan)) where
  ifF (l1, b) v w =
    let D l2 u u' = indexS (fromListS @2 [v, w])
                           (ifF (emptyADShare, b) 0 1 :$: ZSH)
    in D (l1 `mergeADShare` l2) u u'

-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
indexS :: forall ranked shaped sh1 sh2 r.
          ( ShapedTensor shaped, IsPrimal shaped r sh2
          , Dual shaped ~ DeltaS ranked shaped
          , OS.Shape sh1, OS.Shape sh2, OS.Shape (sh1 OS.++ sh2), GoodScalar r )
       => ADVal shaped r (sh1 OS.++ sh2) -> IndexSh shaped sh1
       -> ADVal shaped r sh2
indexS (D l u u') ix = dD l (sindex u ix) (IndexS u' ix)

fromListS :: forall n sh ranked shaped r.
             ( ShapedTensor shaped, IsPrimal shaped r (n ': sh)
             , Dual shaped ~ DeltaS ranked shaped
             , KnownNat n, OS.Shape sh, GoodScalar r )
           => [ADVal shaped r sh]
           -> ADVal shaped r (n ': sh)
fromListS lu =
  dD (flattenADShare $ map (\(D l _ _) -> l) lu)
     (sfromList $ map (\(D _ u _) -> u) lu)
     (FromListS $ map (\(D _ _ u') -> u') lu)

instance ( OS.Shape sh, GoodScalar r, dynamic ~ DynamicOf shaped
         , Dual shaped ~ DeltaS ranked shaped
         , Dual (Clown dynamic) ~ DeltaD ranked shaped
         , ConvertTensor ranked shaped )
         => AdaptableDomains (ADValClown dynamic)
                             (ADVal shaped r sh) where
  type Value (ADVal shaped r sh) = Flip OS.Array r sh   -- ! not Value(shaped)
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (DynamicExists @r2 a, rest) ->
      case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> let !aS = dToS @r (runFlip a)
                     in Just (aS, rest)
        _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

dToS :: forall r ranked shaped sh.
        ( ConvertTensor ranked shaped
        , Dual shaped ~ DeltaS ranked shaped
        , Dual (Clown (DynamicOf ranked)) ~ DeltaD ranked shaped
        , OS.Shape sh, GoodScalar r )
      => ADVal (Clown (DynamicOf ranked)) r '() -> ADVal shaped r sh
dToS (D l u u') = dDnotShared l (sfromD $ runClown u) (dDToS u')
 where
  dDToS (SToD @sh1 d) =
    case sameShape @sh1 @sh of
      Just Refl -> d
      _ -> error "dToS: different ranks in DToS(SToD)"
  dDToS (RToD @n1 d) =
    case matchingRank @sh @n1 of
      Just Refl -> RToS d
      _ -> error "dToS: different ranks in DToS(RToD)"

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
         , PrimalOf shaped ~ shaped
         , shaped ~ PrimalOf shaped
         , CRankedIPSh shaped IsPrimal
         , ShapedTensor shaped )
         => ShapedTensor (ADVal shaped) where
  slet (D l u u') f =
    let !(!l2, var2) = recordSharingPrimal u l
    in f (D l2 var2 u')
      -- u' doesn't need to be shared, because deltas are shared separately

  -- This is very slow, but is fortunately not needed:
  -- tshape (D l u _) = tshape (tletWrap l u)
  --
  -- All underlying scalars supporting these operations
  -- result in empty delta expression, but it's still advantageous to store
  -- @l@ in the @D@ triple instead of in @u@ via @letWrap@.
  -- When, later on, these are to be treated as indexes, sprimalPart needs
  -- to be called, which moves @l@ to @u@ via @letWrap@.
  sminIndex (D l u _) =
    let v = sminIndex u
    in dDnotShared l v (dZeroOfShape v)
  smaxIndex (D l u _) =
    let v = smaxIndex u
    in dDnotShared l v (dZeroOfShape v)
  sfloor (D l u _) =
    let v = sfloor u
    in dDnotShared l v (dZeroOfShape v)

  siota = constantADVal siota
  sindex = indexS
  ssum (D l u u') = dD l (ssum u) (SumS u')
  ssum0 (D l u u') = dD l (ssum0 u) (Sum0S u')
  sdot0 (D l1 ue u') (D l2 ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (sdot0 u v) (dAdd (Dot0S v u') (Dot0S u v'))
  sscatter (D l u u') f = dD l (sscatter u f) (ScatterS u' f)

  sfromList = fromListS
  sfromVector lu =
    dD (flattenADShare $ map (\(D l _ _) -> l) $ V.toList lu)
       (sfromVector $ V.map (\(D _ u _) -> u) lu)
       (FromVectorS $ V.map (\(D _ _ u') -> u') lu)
  sunravelToList (D l u u') =
    let lu = sunravelToList u
        f i ui = dD l ui (IndexS u' (singletonShaped $ fromIntegral i))
    in imap f lu
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
          => (IntSh (ADVal shaped) n -> ADVal shaped r sh)
          -> ADVal shaped r (n ': sh)
  sbuild1 f = fromListS $ map (f . ShapedList.shapedNat)
                              [0 .. valueOf @n - 1]
                   -- element-wise (POPL) version
  sgather (D l u u') f = dD l (sgather u f) (GatherS u' f)
  scast (D l u u') = dD l (scast u) (CastS u')
  sfromIntegral (D l u _) =
    let v = sfromIntegral u
    in dDnotShared l v (dZeroOfShape v)
  sconst t = constantADVal (sconst t)

  saddDynamic = undefined

  sconstant t = let (l, r) = sletUnwrap t in dDnotShared l r (dZeroOfShape t)
  sprimalPart (D l u _) = sletWrap l u
  sdualPart (D l _ u') = Pair (Clown (Const l)) u'
  sD ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = sletUnwrap ast
    in dD (l `mergeADShare` l2) r delta
  sScale ast (Pair  (Clown (Const l)) delta) =
    let (l2, r) = sletUnwrap ast
    in Pair (Clown (Const (l `mergeADShare` l2))) (dScale r delta)


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
      dSToR (RToS d) = d  -- no information lost, so no checks
      dSToR d = SToR d
  dfromR = Flip . rToD
   where
    rToD :: forall r n. (GoodScalar r, KnownNat n)
         => ADVal ranked r n -> ADVal (Clown (DynamicOf ranked)) r '()
    rToD (D l u u') = dDnotShared l (Clown $ dfromR u) (dRToD u')
     where
      dRToD (DToR d) = d  -- no information lost, so no checks
      dRToD d = RToD d
  dfromS = Flip . sToD
   where
    sToD :: forall r sh. (GoodScalar r, OS.Shape sh)
         => ADVal shaped r sh -> ADVal (Clown (DynamicOf ranked)) r '()
    sToD (D l u u') = dDnotShared l (Clown $ dfromS u) (dSToD u')
     where
      dSToD (DToS d) = d  -- no information lost, so no checks
      dSToD d = SToD d
  sfromD = dToS . runFlip
  sfromR = rToS
   where
    rToS :: forall r sh. (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => ADVal ranked r (OS.Rank sh) -> ADVal shaped r sh
    rToS (D l u u') = dDnotShared l (sfromR u) (dRToS u')
     where
      dRToS (SToR @sh1 d) =
        case sameShape @sh1 @sh of
          Just Refl -> d
          _ -> error "rToS: different shapes in RToS(SToR)"
      dRToS d = RToS d
  ddummy = undefined
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
  :: ( RankedTensor ranked, KnownNat n, GoodScalar r
     , Dual ranked ~ DeltaR ranked shaped
     , IsPrimal ranked r (1 + n) )
  => Int -> (IntOf ranked -> ADVal ranked r n)
  -> ADVal ranked r (1 + n)
_build1Closure k f =  -- stores closures on tape
  let g i = let D _ u _ = f i in u
      h i = let D _ _ u' = f i in u'
  in dD emptyADShare (tbuild1 k g) (BuildR k h)
