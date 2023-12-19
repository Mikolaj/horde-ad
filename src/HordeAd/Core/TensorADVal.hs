{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for dual numbers. Most of the definitions
-- are generic over whether the dual numbers are built from concrete arrays
-- of floats or from AST terms. However, since we are not using
-- a middle layer such as "DualClass", separate instances are given
-- for ranked tensors and shaped tensors.
module HordeAd.Core.TensorADVal
  ( CRankedIP, CRankedIPSh, CRankedIPU
  ) where

import Prelude hiding (foldl')

import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Function ((&))
import           Data.Functor.Const
import           Data.Kind (Constraint, Type)
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
import           HordeAd.Internal.TensorOps
import           HordeAd.Util.ShapedList (singletonShaped)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * Ranked tensor instances

instance ( KnownNat n, GoodScalar r
         , dynamic ~ DynamicOf ranked, RankedOf shaped ~ ranked
         , Dual ranked ~ DeltaR ranked shaped
         , Dual (Clown dynamic) ~ DeltaD (Clown dynamic) ranked shaped
         , RankedTensor (ADVal ranked), ConvertTensor ranked shaped
         , CRankedIPU (Clown dynamic) IsPrimal )
         => AdaptableDomains (ADValClown dynamic)
                             (ADVal ranked r n) where
{- TODO: RULE left-hand side too complicated to desugar
  {-# SPECIALIZE instance
      KnownNat y
      => AdaptableDomains (ADValClown OD.Array)
                          (ADVal (Flip OR.Array) Double y) #-}
-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      KnownNat y
      => AdaptableDomains (ADValClown (AstDynamic PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double y) #-}
-}
  type Value (ADVal ranked r n) = Flip OR.Array r n  -- ! not Value(ranked)
  toDomains = undefined
  fromDomains aInit inputs = case V.uncons inputs of
    Just (DynamicExists @r2 a, rest) ->
      if dIsDummy @(ADVal ranked) a
      then Just (rzero (rshape aInit), rest)
      else
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
{- TODO: RULE left-hand side too complicated to desugar
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableDomains (ADValClown OD.Array)
                          [ADVal (Flip OR.Array) Double n] #-}
-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableDomains (ADValClown (AstDynamic PrimalSpan))
                          [ADVal (AstRanked PrimalSpan) Double n] #-}
-}
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
        , Dual (Clown (DynamicOf ranked))
          ~ DeltaD (Clown (DynamicOf ranked)) ranked shaped
        , KnownNat n, GoodScalar r )
      => ADVal (Clown (DynamicOf ranked)) r '() -> ADVal ranked r n
dToR (D l u u') = dDnotShared l (rfromD $ runClown u) (dDToR u')
 where
  dDToR (RToD @n1 d) =
    case sameNat (Proxy @n1) (Proxy @n) of
      Just Refl -> d
      _ -> error "dToR: different ranks in DToR(RToD)"
  dDToR (SToD @sh1 d) =
    case matchingRank @sh1 @n of
      Just Refl -> SToR d
      _ -> error "dToR: different ranks in DToR(SToD)"

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( Dual ranked ~ DeltaR ranked shaped
         , DeltaR ranked shaped ~ Dual ranked
         , RankedOf ranked ~ ranked
         , ranked ~ RankedOf ranked
         , RankedOf (PrimalOf ranked) ~ PrimalOf ranked
         , PrimalOf ranked ~ RankedOf (PrimalOf ranked)
         , RankedOf shaped ~ ranked
         , ranked ~ RankedOf shaped
         , RankedOf @() (Clown  (DynamicOf ranked)) ~ ranked
         , ranked ~ RankedOf @() (Clown (DynamicOf ranked))
         , ShapedOf @() (Clown  (DynamicOf ranked)) ~ shaped
         , shaped ~ ShapedOf @() (Clown  (DynamicOf ranked))
         , CRankedIP ranked IsPrimal
         , CRankedIPU (Clown (DynamicOf ranked)) IsPrimal
         , RankedTensor ranked, ConvertTensor ranked shaped )
         => RankedTensor (ADVal ranked) where
  rlet (D l u u') f =
    let !(!l2, var2) = recordSharingPrimal u l
    in f (D l2 var2 u')
      -- u' doesn't need to be shared, because deltas are shared separately

  rshape (D _ u _) = rshape u
  -- This is very slow, but is fortunately not needed:
  -- rshape (D l u _) = rshape (rletWrap l u)
  --
  -- All underlying scalars supporting these operations
  -- result in empty delta expression, but it's still advantageous to store
  -- @l@ in the @D@ triple instead of in @u@ via @letWrap@.
  -- When, later on, these are to be treated as indexes, sprimalPart needs
  -- to be called, which moves @l@ to @u@ via @letWrap@.
  rminIndex (D l u _) =
    let v = rminIndex u
    in dDnotShared l v (dZeroOfShape v)
  rmaxIndex (D l u _) =
    let v = rmaxIndex u
    in dDnotShared l v (dZeroOfShape v)
  rfloor (D l u _) =
    let v = rfloor u
    in dDnotShared l v (dZeroOfShape v)

  -- TODO: speed up by using tindex0R and dIndex0 if the codomain has rank 0
  -- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
  -- dimension affected.
  rindex d i = indexPrimal d (rprimalPart <$> i)
  rsum (D l u u') = dD l (rsum u) (SumR u')
  rsum0 (D l u u') = dD l (rsum0 u) (Sum0R u')
  rdot0 (D l1 ue u') (D l2 ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (rdot0 u v) (dAdd (Dot0R v u') (Dot0R u v'))
  rscatter sh (D l u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD l (rscatter sh u g) (ScatterR sh u' g)

  rfromList = fromList
  rfromVector lu =
    dD (flattenADShare $ map (\(D l _ _) -> l) $ V.toList lu)
       (rfromVector $ V.map (\(D _ u _) -> u) lu)
       (FromVectorR $ V.map (\(D _ _ u') -> u') lu)
  runravelToList (D l u u') =
    let lu = runravelToList u
        f i ui = dD l ui (IndexR u' (singletonIndex $ fromIntegral i))
    in imap f lu
  rreplicate k (D l u u') = dD l (rreplicate k u) (ReplicateR k u')
  rappend (D l1 u u') (D l2 v v') =
    dD (l1 `mergeADShare` l2) (rappend u v) (AppendR u' v')
  rslice i n (D l u u') = dD l (rslice i n u) (SliceR i n u')
  rreverse (D l u u') = dD l (rreverse u) (ReverseR u')
  rtranspose perm (D l u u') = dD l (rtranspose perm u) (TransposeR perm u')
  rreshape :: forall n m r. (GoodScalar r, KnownNat n, KnownNat m)
           => ShapeInt m -> ADVal ranked r n -> ADVal ranked r m
  rreshape sh t@(D l u u') = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == rshape u -> t
    _ -> dD l (rreshape sh u) (ReshapeR sh u')
  rbuild1 k f = fromList $ map (f . fromIntegral) [0 .. k - 1]
                   -- element-wise (POPL) version
  rgather sh (D l u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD l (rgather sh u g) (GatherR sh u' g)
      -- note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on
  rcast (D l u u') = dD l (rcast u) (CastR u')
  rfromIntegral (D l u _) =
    let v = rfromIntegral u
    in dDnotShared l v (dZeroOfShape v)
  rconst t = constantADVal (rconst t)
  rletDomainsIn _ = (&)

  raddDynamic :: forall r n. (GoodScalar r, KnownNat n)
              => ADVal ranked r n
              -> DynamicExists (ADValClown (DynamicOf ranked))
              -> DynamicExists (ADValClown (DynamicOf ranked))
  raddDynamic r (DynamicExists
                   @r2 d@(Flip (D _ (Clown dd) _))) = DynamicExists $
    if dIsDummy @ranked dd then dfromR r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> dfromR $ r + rfromD d
      _ -> error "raddDynamic: type mismatch"

  rconstant t = let (l, r) = rletUnwrap t in dDnotShared l r (dZeroOfShape r)
  rprimalPart (D l u _) = rletWrap l u
  rdualPart (D l _ u') = Pair (Clown (Const l)) u'
  rD ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = rletUnwrap ast
    in dD (l `mergeADShare` l2) r delta
  rScale ast (Pair  (Clown (Const l)) delta) =
    let (l2, r) = rletUnwrap ast
    in Pair (Clown (Const (l `mergeADShare` l2))) (dScale r delta)


-- * Shaped tensor instances

instance ( Sh.Shape sh, GoodScalar r
         , dynamic ~ DynamicOf shaped, ShapedOf ranked ~ shaped
         , Dual shaped ~ DeltaS ranked shaped
         , Dual (Clown dynamic) ~ DeltaD (Clown dynamic) ranked shaped
         , ShapedTensor (ADVal shaped), ConvertTensor ranked shaped
         , CRankedIPU (Clown dynamic) IsPrimal )
         => AdaptableDomains (ADValClown dynamic)
                             (ADVal shaped r sh) where
  type Value (ADVal shaped r sh) = Flip OS.Array r sh   -- ! not Value(shaped)
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (DynamicExists @r2 a, rest) ->
      if dIsDummy @(ADVal ranked) a then Just (0, rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> let !aS = dToS @r (runFlip a)
                       in Just (aS, rest)
          _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

dToS :: forall r ranked shaped sh.
        ( ConvertTensor ranked shaped
        , Dual shaped ~ DeltaS ranked shaped
        , Dual (Clown (DynamicOf ranked))
          ~ DeltaD (Clown (DynamicOf ranked)) ranked shaped
        , Sh.Shape sh, GoodScalar r )
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

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( Dual shaped ~ DeltaS ranked shaped
         , DeltaS ranked shaped ~ Dual shaped
         , RankedOf (PrimalOf shaped) ~ PrimalOf ranked
         , PrimalOf ranked ~ RankedOf (PrimalOf shaped)
         , DynamicOf ranked ~ DynamicOf shaped
         , DynamicOf shaped ~ DynamicOf ranked
         , ShapedOf ranked ~ shaped
         , shaped ~ ShapedOf ranked
         , RankedOf @() (Clown  (DynamicOf ranked)) ~ ranked
         , ranked ~ RankedOf @() (Clown (DynamicOf ranked))
         , ShapedOf @() (Clown  (DynamicOf ranked)) ~ shaped
         , shaped ~ ShapedOf @() (Clown  (DynamicOf ranked))
         , CRankedIPSh shaped IsPrimal
         , CRankedIPU (Clown (DynamicOf ranked)) IsPrimal
         , RankedTensor ranked, ShapedTensor shaped
         , ConvertTensor ranked shaped )
         => ShapedTensor (ADVal shaped) where
  slet (D l u u') f =
    let !(!l2, var2) = recordSharingPrimal u l
    in f (D l2 var2 u')
      -- u' doesn't need to be shared, because deltas are shared separately

  -- This is very slow, but is fortunately not needed:
  -- rshape (D l u _) = rshape (rletWrap l u)
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
  sindex d i = indexPrimalS d (rprimalPart <$> i)
  ssum (D l u u') = dD l (ssum u) (SumS u')
  ssum0 (D l u u') = dD l (ssum0 u) (Sum0S u')
  sdot0 (D l1 ue u') (D l2 ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (sdot0 u v) (dAdd (Dot0S v u') (Dot0S u v'))
  sscatter (D l u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD l (sscatter u g) (ScatterS u' g)

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
              ( GoodScalar r, Sh.Shape sh, Sh.Shape sh2
              , Sh.Size sh ~ Sh.Size sh2 )
           => ADVal shaped r sh -> ADVal shaped r sh2
  sreshape t@(D l u u') = case sameShape @sh2 @sh of
    Just Refl -> t
    _ -> dD l (sreshape u) (ReshapeS u')
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, Sh.Shape sh)
          => (IntSh (ADVal shaped) n -> ADVal shaped r sh)
          -> ADVal shaped r (n ': sh)
  sbuild1 f = fromListS $ map (f . ShapedList.shapedNat)
                              [0 .. valueOf @n - 1]
                   -- element-wise (POPL) version
  sgather (D l u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD l (sgather u g) (GatherS u' g)
  scast (D l u u') = dD l (scast u) (CastS u')
  sfromIntegral (D l u _) =
    let v = sfromIntegral u
    in dDnotShared l v (dZeroOfShape v)
  sconst t = constantADVal (sconst t)
  sletDomainsIn _ = (&)

  saddDynamic :: forall r sh. (GoodScalar r, Sh.Shape sh)
              => ADVal shaped r sh
              -> DynamicExists (ADValClown (DynamicOf shaped))
              -> DynamicExists (ADValClown (DynamicOf shaped))
  saddDynamic r (DynamicExists
                   @r2 d@(Flip (D _ (Clown dd) _))) = DynamicExists $
    if dIsDummy @ranked dd then dfromS r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> dfromS $ r + sfromD d
      _ -> error "saddDynamic: type mismatch"

  sconstant t = let (l, r) = sletUnwrap t in dDnotShared l r (dZeroOfShape t)
  sprimalPart (D l u _) = sletWrap l u
  sdualPart (D l _ u') = Pair (Clown (Const l)) u'
  sD ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = sletUnwrap ast
    in dD (l `mergeADShare` l2) r delta
  sScale ast (Pair  (Clown (Const l)) delta) =
    let (l2, r) = sletUnwrap ast
    in Pair (Clown (Const (l `mergeADShare` l2))) (dScale r delta)


-- * ConvertTensor and DomainsTensor instances

type CRankedIPU :: TensorKind ()
                -> (TensorKind () -> Type -> () -> Constraint)
                -> Constraint
class (forall r17. GoodScalar r17 => c ranked r17 '())
      => CRankedIPU ranked c where
instance (forall r17. GoodScalar r17 => c ranked r17 '())
         => CRankedIPU ranked c where

instance ( Dual ranked ~ DeltaR ranked shaped
         , Dual shaped ~ DeltaS ranked shaped
         , Dual (Clown (DynamicOf ranked))
           ~ DeltaD (Clown (DynamicOf ranked)) ranked shaped
         , ConvertTensor ranked shaped
         , CRankedIPU (Clown (DynamicOf ranked)) IsPrimal )
         => ConvertTensor (ADVal ranked) (ADVal shaped) where
  rfromD = dToR . runFlip
  rfromS = sToR
   where
    sToR :: forall r sh. (GoodScalar r, Sh.Shape sh)
         => ADVal shaped r sh -> ADVal ranked r (Sh.Rank sh)
    sToR (D l u u') = dDnotShared l (rfromS u) (dSToR u')
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
    sToD :: forall r sh. (GoodScalar r, Sh.Shape sh)
         => ADVal shaped r sh -> ADVal (Clown (DynamicOf ranked)) r '()
    sToD (D l u u') = dDnotShared l (Clown $ dfromS u) (dSToD u')
     where
      dSToD (DToS d) = d  -- no information lost, so no checks
      dSToD d = SToD d
  sfromD = dToS . runFlip
  sfromR = rToS
   where
    rToS :: forall r sh. (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Rank sh))
         => ADVal ranked r (Sh.Rank sh) -> ADVal shaped r sh
    rToS (D l u u') = dDnotShared l (sfromR u) (dRToS u')
     where
      dRToS (SToR @sh1 d) =
        case sameShape @sh1 @sh of
          Just Refl -> d
          _ -> error "rToS: different shapes in RToS(SToR)"
      dRToS d = RToS d
  ddummy = Flip (constantADVal (Clown (ddummy @ranked)))
  dIsDummy (Flip (D _ (Clown d) _)) = dIsDummy @ranked d
  dshape (Flip (D _ u _)) = dshape @ranked (runClown u)

instance ( ADReady ranked, ADReadySmall (ADVal ranked) (ADVal shaped)
         , UnletGradient ranked
         , Dual (Clown (DynamicOf (ADVal ranked)))
           ~ DeltaD (Clown (DynamicOf (ADVal ranked)))
                    (ADVal ranked) (ADVal shaped)
         , ShapedOf shaped ~ shaped )
         => DomainsTensor (ADVal ranked) (ADVal shaped) where
  dmkDomains = id
  dunDomains _ = id
  rletInDomains = (&)
  sletInDomains = (&)
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains (DynamicOf f) -> f r n)
       -> DomainsOD
       -> DomainsOf (ADVal ranked)
       -> DomainsOf (ADVal ranked)
  rrev f _parameters0 parameters =
    -- This computes the derivative of f again for each new @parmeters@.
    fst $ crevOnDomains False Nothing (f @(ADVal (ADVal ranked))) parameters
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => Domains (DynamicOf f) -> f r n)
         -> DomainsOD
         -> DomainsOf (ADVal ranked)
         -> ADVal ranked r n
         -> DomainsOf (ADVal ranked)
  rrevDt f _parameters0 parameters dt =
    fst $ crevOnDomains False (Just dt) (f @(ADVal (ADVal ranked))) parameters
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains (DynamicOf f) -> f r n)
       -> DomainsOD
       -> DomainsOf (ADVal ranked)
       -> DomainsOf (ADVal ranked)
       -> ADVal ranked r n
  rfwd f _parameters0 parameters ds =
    fst $ cfwdOnDomains parameters (f @(ADVal (ADVal ranked))) ds
  srev f _parameters0 parameters =
    fst $ crevOnDomains False Nothing (f @(ADVal (ADVal shaped))) parameters
  srevDt f _parameters0 parameters dt =
    fst $ crevOnDomains False (Just dt) (f @(ADVal (ADVal shaped))) parameters
  sfwd f _parameters0 parameters ds =
    fst $ cfwdOnDomains parameters (f @(ADVal (ADVal shaped))) ds
  rfold :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ADVal ranked rn n
        -> ADVal ranked rm (1 + m)
        -> ADVal ranked rn n
  rfold f (D l1 x0 x0') (D l2 as as') =
    let shn = rshape x0
        shm = tailShape $ rshape as
        odFromSh :: forall rk k. GoodScalar rk
                 => ShapeInt k -> DynamicExists OD.Array
        odFromSh sh = DynamicExists @rk $ OD.constant (shapeToList sh) 0
        domsOD = V.fromList [odFromSh @rn shn, odFromSh @rm shm]
        domsToPair :: forall f. ADReady f
                   => Domains (DynamicOf f) -> (f rn n, f rm m)
        domsToPair doms =
          let d0 = case doms V.! 0 of
                DynamicExists @rn2 ex
                  | Just Refl <- testEquality (typeRep @rn) (typeRep @rn2) ->
                    rfromD ex
                _ -> error "rfold: type mismatch"
              d1 = case doms V.! 1 of
                DynamicExists @rm2 ex
                  | Just Refl <- testEquality (typeRep @rm) (typeRep @rm2) ->
                    rfromD ex
                _ -> error "rfold: type mismatch"
          in (d0, d1)
        g :: Domains (DynamicOf (ADVal ranked)) -> ADVal ranked rn n
        g doms = uncurry (f @(ADVal ranked)) (domsToPair doms)
        -- This computes the derivative of f again for each new @x@ and @a@
        -- (not even once for @as@, but for each @a@ separately).
        -- Note that this function, and similarly @f@ instantiated
        -- and passed to FoldR, is not a function on dual numbers.
        -- Consequently, any dual number operations inserted there by the user
        -- are flattened away (which is represented in AST by @PrimalSpan@).
        -- TODO: what if the dual numbers are nested?
        -- TODO: do the dual number ops in f affect what df is computed? add
        -- a comment explaining that and tests that exemplify that
        df :: ranked rn n -> (ranked rn n, ranked rm m)
           -> (ranked rn n, ranked rm m)
        df dt (x, a) =
          domsToPair $ dunDomains @ranked domsOD $ fst
          $ crevOnDomains False (Just dt) g
                          (V.fromList [ DynamicExists @rn (dfromR x)
                                      , DynamicExists @rm (dfromR a) ])
    in D (l1 `mergeADShare` l2)
         (rfold @ranked f x0 as)
         (FoldR f x0 as df x0' as')
  rfoldRev :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> ADVal ranked rn n
           -> ADVal ranked rm (1 + m)
           -> ADVal ranked rn n
  rfoldRev f df (D l1 x0 x0') (D l2 as as') =
    -- This potentially duplicates some AST terms, but we do this here,
    -- in the context of sharing information, so let's hope all big things
    -- are shared. If not, we'd need to extend @rregister@ to also work
    -- on @DomainsOf f@.
    let shn = rshape x0
        shm = tailShape $ rshape as
        odFromSh :: forall rk k. GoodScalar rk
                 => ShapeInt k -> DynamicExists OD.Array
        odFromSh sh = DynamicExists @rk $ OD.constant (shapeToList sh) 0
        domsOD = V.fromList [odFromSh @rn shn, odFromSh @rm shm]
        -- Note that this function, and similarly @f@ instantiated
        -- and passed to FoldR, is not a function on dual numbers.
        h :: ranked rn n -> (ranked rn n, ranked rm m)
          -> (ranked rn n, ranked rm m)
        h dt (x, a) =
          let res = df dt x a  -- non-explicit sharing, so helps little
          in ( rletDomainsIn
                 domsOD res
                 (\doms -> case doms V.! 0 of
                   DynamicExists @rn2 ex
                     | Just Refl <- testEquality (typeRep @rn) (typeRep @rn2) ->
                       rfromD ex
                   _ -> error "rfoldRev: type mismatch")
             , rletDomainsIn
                 domsOD res
                 (\doms -> case doms V.! 1 of
                   DynamicExists @rm2 ea
                     | Just Refl <- testEquality (typeRep @rm) (typeRep @rm2) ->
                       rfromD ea
                   _ -> error "rfoldRev: type mismatch")
             )
    in D (l1 `mergeADShare` l2)
         (rfold @ranked f x0 as)
         (FoldR f x0 as h x0' as')


-- * DomainsTensor instance for concrete arrays

instance DomainsTensor (Flip OR.Array) (Flip OS.Array) where
  dmkDomains = id
  dunDomains _ = id
  rletInDomains = (&)
  sletInDomains = (&)
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains (DynamicOf f) -> f r n)
       -> DomainsOD
       -> DomainsOD
       -> DomainsOD
  rrev f _parameters0 parameters =
    fst $ crevOnDomains False Nothing (f @(ADVal (Flip OR.Array))) parameters
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => Domains (DynamicOf f) -> f r n)
         -> DomainsOD
         -> DomainsOD
         -> Flip OR.Array r n
         -> DomainsOD
  rrevDt f _parameters0 parameters dt =
    fst $ crevOnDomains False (Just dt) (f @(ADVal (Flip OR.Array))) parameters
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains (DynamicOf f) -> f r n)
       -> DomainsOD
       -> DomainsOD
       -> DomainsOD
       -> Flip OR.Array r n
  rfwd f _parameters0 parameters ds =
    fst $ cfwdOnDomains parameters (f @(ADVal (Flip OR.Array))) ds
  srev f _parameters0 parameters =
    fst $ crevOnDomains False Nothing (f @(ADVal (Flip OS.Array))) parameters
  srevDt f _parameters0 parameters dt =
    fst $ crevOnDomains False (Just dt) (f @(ADVal (Flip OS.Array))) parameters
  sfwd f _parameters0 parameters ds =
    fst $ cfwdOnDomains parameters (f @(ADVal (Flip OS.Array))) ds
  rfold :: GoodScalar rm
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> Flip OR.Array rn n
        -> Flip OR.Array rm (1 + m)
        -> Flip OR.Array rn n
  rfold f (Flip x0) (Flip as) =
    let g x a = runFlip $ f @(Flip OR.Array) (Flip x) (Flip a)
    in Flip $ foldl' g x0 (tunravelToListR as)
  rfoldRev :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> Flip OR.Array rn n
           -> Flip OR.Array rm (1 + m)
           -> Flip OR.Array rn n
  rfoldRev f _df (Flip x0) (Flip as) = rfold f (Flip x0) (Flip as)
