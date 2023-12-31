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
  ( CRankedIP, CRankedIPSh
  ) where

import Prelude hiding (foldl')

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Function ((&))
import           Data.Functor.Const
import           Data.List (foldl', scanl')
import           Data.List.Index (imap)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.Delta
import           HordeAd.Core.DualClass
import           HordeAd.Core.DualNumber
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)
import           HordeAd.Util.ShapedList (singletonShaped)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * Ranked tensor instances

instance ( KnownNat n, GoodScalar r
         , RankedTensor (ADVal ranked) )
         => AdaptableDomains (ADVal ranked)
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
  fromDomains _aInit params = fromDomainsR @r @n params

-- This is temporarily moved from Adaptor in order to specialize manually
instance AdaptableDomains ranked a
         => AdaptableDomains ranked [a] where
  {-# SPECIALIZE instance
      (KnownNat n, AdaptableDomains (Flip OR.Array) (OR.Array n Double))
      => AdaptableDomains (Flip OR.Array)
                          [OR.Array n Double] #-}
  {-# SPECIALIZE instance
      ( KnownNat n, AstSpan s
      , AdaptableDomains (AstRanked s)
                         (AstRanked s Double n) )
      => AdaptableDomains (AstRanked s)
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

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( Dual ranked ~ DeltaR ranked
         , DeltaR ranked ~ Dual ranked
         , RankedOf (ShapedOf ranked) ~ ranked
         , RankedOf ranked ~ ranked
         , ranked ~ RankedOf ranked
         , RankedOf (PrimalOf ranked) ~ PrimalOf ranked
         , PrimalOf ranked ~ RankedOf (PrimalOf ranked)
         , CRankedIP ranked IsPrimal
         , RankedTensor ranked )
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
  rfromS = sToR
   where
    sToR :: forall r sh. (GoodScalar r, Sh.Shape sh)
         => ADVal (ShapedOf ranked) r sh -> ADVal ranked r (Sh.Rank sh)
    sToR (D l u u') = dDnotShared l (rfromS u) (dSToR u')
     where
      dSToR (RToS d) = d  -- no information lost, so no checks
      dSToR d = SToR d

  rconstant t = let (l, r) = rletUnwrap t in dDnotShared l r (dZeroOfShape r)
  rprimalPart (D l u _) = rletWrap l u
  rdualPart (D l _ u') = Pair (Clown (Const l)) u'
  rD ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = rletUnwrap ast
    in dD (l `mergeADShare` l2) r delta
  rScale ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = rletUnwrap ast
    in Pair (Clown (Const (l `mergeADShare` l2))) (dScale r delta)


-- * Shaped tensor instances

instance ( Sh.Shape sh, GoodScalar r
         , ranked ~ RankedOf shaped, ShapedOf ranked ~ shaped
         , Dual shaped ~ DeltaS shaped
         , ShapedTensor (ADVal shaped) )
         => AdaptableDomains (ADVal ranked)
                             (ADVal shaped r sh) where
  type Value (ADVal shaped r sh) = Flip OS.Array r sh   -- ! not Value(shaped)
  toDomains = undefined
  fromDomains _aInit params = fromDomainsS @r @sh params

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( Dual shaped ~ DeltaS shaped
         , DeltaS shaped ~ Dual shaped
         , RankedOf (PrimalOf shaped) ~ PrimalOf (RankedOf shaped)
         , PrimalOf (RankedOf shaped) ~ RankedOf (PrimalOf shaped)
         , ShapedOf (RankedOf shaped) ~ shaped
         , shaped ~ ShapedOf (RankedOf shaped)
         , CRankedIPSh shaped IsPrimal
         , RankedTensor (RankedOf shaped), ShapedTensor shaped )
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
    dD l (sslice i_proxy n_proxy u) (SliceS @shaped @i u')
  sreverse (D l u u') = dD l (sreverse u) (ReverseS u')
  stranspose (perm_proxy :: Proxy perm) (D l u u') =
    dD l (stranspose perm_proxy u) (TransposeS @shaped @perm u')
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
  sfromR = rToS
   where
    rToS :: forall r sh. (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Rank sh))
         => ADVal (RankedOf shaped) r (Sh.Rank sh) -> ADVal shaped r sh
    rToS (D l u u') = dDnotShared l (sfromR u) (dRToS u')
     where
      dRToS (SToR @sh1 d) =
        case sameShape @sh1 @sh of
          Just Refl -> d
          _ -> error "rToS: different shapes in RToS(SToR)"
      dRToS d = RToS d

  sconstant t = let (l, r) = sletUnwrap t in dDnotShared l r (dZeroOfShape t)
  sprimalPart (D l u _) = sletWrap l u
  sdualPart (D l _ u') = Pair (Clown (Const l)) u'
  sD ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = sletUnwrap ast
    in dD (l `mergeADShare` l2) r delta
  sScale ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = sletUnwrap ast
    in Pair (Clown (Const (l `mergeADShare` l2))) (dScale r delta)


-- * DomainsTensor instance

instance ( ADReady ranked, ADReadySmall (ADVal ranked) (ADVal shaped)
         , UnletGradient ranked, UnletGradient shaped )
         => DomainsTensor (ADVal ranked) (ADVal shaped) where
  dmkDomains = id
  dunDomains _ = id
  rletInDomains = (&)
  sletInDomains = (&)
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains f -> f r n)
       -> DomainsOD
       -> DomainsOf (ADVal ranked)
       -> DomainsOf (ADVal ranked)
  rrev f _parameters0 parameters =
    -- This computes the derivative of f again for each new @parmeters@.
    fst $ crevOnDomains Nothing (f @(ADVal (ADVal ranked))) parameters
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => Domains f -> f r n)
         -> DomainsOD
         -> DomainsOf (ADVal ranked)
         -> ADVal ranked r n
         -> DomainsOf (ADVal ranked)
  rrevDt f _parameters0 parameters dt =
    fst $ crevOnDomains (Just dt) (f @(ADVal (ADVal ranked))) parameters
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains f -> f r n)
       -> DomainsOD
       -> DomainsOf (ADVal ranked)
       -> DomainsOf (ADVal ranked)
       -> ADVal ranked r n
  rfwd f _parameters0 parameters ds =
    fst $ cfwdOnDomains parameters (f @(ADVal (ADVal ranked))) ds
  srev f _parameters0 parameters =
    fst $ crevOnDomains Nothing (f @(ADVal (ADVal shaped))) parameters
  srevDt f _parameters0 parameters dt =
    fst $ crevOnDomains (Just dt) (f @(ADVal (ADVal shaped))) parameters
  sfwd f _parameters0 parameters ds =
    fst $ cfwdOnDomains parameters (f @(ADVal (ADVal shaped))) ds
  rfold :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ADVal ranked rn n
        -> ADVal ranked rm (1 + m)
        -> ADVal ranked rn n
  rfold f (D l1 x0 x0') (D l2 as as') =
    -- This can't call rfoldDer, because UnletGradient constraint is needed
    -- in the computed derivatives, while rfoldDer gets derivatives with
    -- looser constraints thanks to interpreting terms in arbitrary algebras.
    -- If the refactoring is really needed, e.g., to avoid computing derivatives
    -- for each nested level of ADVal, we can add UnletGradient to ADReady.
    let shn = rshape x0
        shm = tailShape $ rshape as
        domsOD = V.fromList [odFromSh @rn shn, odFromSh @rm shm]
        domsToPair :: forall f. ADReady f
                   => Domains f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: Domains (ADVal ranked) -> ADVal ranked rn n
        g doms = uncurry (f @(ADVal ranked)) (domsToPair doms)
        -- This computes the derivative of f again for each new @x@ and @a@
        -- (not even once for @as@, but for each @a@ separately).
        -- Note that this function, and similarly @rf and @f@ instantiated
        -- and passed to FoldR, is not a function on dual numbers.
        -- Consequently, any dual number operations inserted there by the user
        -- are flattened away (which is represented in AST by @PrimalSpan@).
        -- TODO: what if the dual numbers are nested?
        -- TODO: do the dual number ops in f affect what df is computed? add
        -- a comment explaining that and tests that exemplify that
        df :: ranked rn n -> (ranked rm m, ranked rn n, ranked rm m)
           -> ranked rn n
        df cx (ca, x, a) =
          fst $ cfwdOnDomains (V.fromList [DynamicRanked x, DynamicRanked a])
                              g
                              (V.fromList [DynamicRanked cx, DynamicRanked ca])
        rf :: ranked rn n -> (ranked rn n, ranked rm m)
           -> (ranked rn n, ranked rm m)
        rf dt (x, a) =
          domsToPair $ dunDomains @ranked domsOD $ fst
          $ crevOnDomains (Just dt) g
                          (V.fromList [DynamicRanked x, DynamicRanked a])
    in D (l1 `mergeADShare` l2)
         (rfold @ranked f x0 as)
         (FoldR f x0 as df rf x0' as')
  rfoldDer :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> ADVal ranked rn n
           -> ADVal ranked rm (1 + m)
           -> ADVal ranked rn n
  rfoldDer f df0 rf0 (D l1 x0 x0') (D l2 as as') =
    -- This potentially duplicates some AST terms, but we do this here,
    -- in the context of sharing information, so let's hope all big things
    -- are shared. If not, we'd need to extend @rregister@ to also work
    -- on @DomainsOf f@.
    let shn = rshape x0
        shm = tailShape $ rshape as
        domsOD = V.fromList [odFromSh @rn shn, odFromSh @rm shm]
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        -- Note that this function, and similarly @f@ and @rf@ instantiated
        -- and passed to FoldR, is not a function on dual numbers.
        df :: forall f. ADReady f
           => f rn n -> (f rm m, f rn n, f rm m) -> f rn n
        df cx (ca, x, a) = df0 cx ca x a
        rf :: forall f. ADReady f
           => f rn n -> (f rn n, f rm m) -> (f rn n, f rm m)
        rf cx (x, a) = domsToPair $ dunDomains domsOD $ rf0 cx x a
          -- TODO: add explicit sharing
    in D (l1 `mergeADShare` l2)
         (rfoldDer @ranked f df0 rf0 x0 as)
         (FoldR f x0 as df rf x0' as')
  rscan :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ADVal ranked rn n
        -> ADVal ranked rm (1 + m)
        -> ADVal ranked rn (1 + n)
  rscan f (D l1 x0 x0') (D l2 as as') =
    let shn = rshape x0
        shm = tailShape $ rshape as
        domsOD = V.fromList [odFromSh @rn shn, odFromSh @rm shm]
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: Domains (ADVal ranked) -> ADVal ranked rn n
        g doms = uncurry (f @(ADVal ranked)) (domsToPair doms)
        df :: ranked rn n -> (ranked rm m, ranked rn n, ranked rm m)
           -> ranked rn n
        df cx (ca, x, a) =
          fst $ cfwdOnDomains (V.fromList [DynamicRanked x, DynamicRanked a])
                              g
                              (V.fromList [DynamicRanked cx, DynamicRanked ca])
        rf :: ranked rn n -> (ranked rn n, ranked rm m)
           -> (ranked rn n, ranked rm m)
        rf dt (x, a) =
          domsToPair $ dunDomains @ranked domsOD $ fst
          $ crevOnDomains (Just dt) g
                          (V.fromList [DynamicRanked x, DynamicRanked a])
    in D (l1 `mergeADShare` l2)
         (rscan @ranked f x0 as)
         (ScanR f x0 as df rf x0' as')
  rscanDer :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> ADVal ranked rn n
           -> ADVal ranked rm (1 + m)
           -> ADVal ranked rn (1 + n)
  rscanDer f df0 rf0 (D l1 x0 x0') (D l2 as as') =
    let shn = rshape x0
        shm = tailShape $ rshape as
        domsOD = V.fromList [odFromSh @rn shn, odFromSh @rm shm]
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        df :: forall f. ADReady f
           => f rn n -> (f rm m, f rn n, f rm m) -> f rn n
        df cx (ca, x, a) = df0 cx ca x a
        rf :: forall f. ADReady f
           => f rn n -> (f rn n, f rm m) -> (f rn n, f rm m)
        rf cx (x, a) = domsToPair $ dunDomains domsOD $ rf0 cx x a
    in D (l1 `mergeADShare` l2)
         (rscanDer @ranked f df0 rf0 x0 as)
         (ScanR f x0 as df rf x0' as')
  rscanD :: forall rn n. (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> Domains f -> f rn n)
         -> DomainsOD
         -> ADVal ranked rn n
         -> Domains (ADVal ranked)
         -> ADVal ranked rn (1 + n)
  rscanD f od (D l1 x0 x0') asD =
    let (ll2, as, as') = V.unzip3 $ V.map unADValDomains asD
        shn = rshape x0
        domsOD = V.cons (odFromSh @rn shn) od
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, Domains f)
        domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
        g :: Domains (ADVal ranked) -> ADVal ranked rn n
        g doms = uncurry (f @(ADVal ranked)) (domsToPair doms)
        df :: ranked rn n -> (Domains ranked, ranked rn n, Domains ranked)
           -> ranked rn n
        df cx (ca, x, a) =
          fst $ cfwdOnDomains (V.cons (DynamicRanked x) a)
                              g
                              (V.cons (DynamicRanked cx) ca)
        rf :: (ranked rn n -> (ranked rn n, Domains ranked)
           -> (ranked rn n, Domains ranked))
        rf dt (x, a) =
          domsToPair $ dunDomains @ranked domsOD $ fst
          $ crevOnDomains (Just dt) g
                          (V.cons (DynamicRanked x) a)
    in D (flattenADShare $ l1 : V.toList ll2)
         (rscanD @ranked f od x0 as)
         (ScanDR f x0 as df rf x0' as')
  rscanDDer :: forall rn n. (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> Domains f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> Domains f -> f rn n -> Domains f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> Domains f
                -> DomainsOf f)
            -> DomainsOD
            -> ADVal ranked rn n
            -> Domains (ADVal ranked)
            -> ADVal ranked rn (1 + n)
  rscanDDer f df0 rf0 od (D l1 x0 x0') asD =
    let (ll2, as, as') = V.unzip3 $ V.map unADValDomains asD
        shn = rshape x0
        domsOD = V.cons (odFromSh @rn shn) od
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, Domains f)
        domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
        df :: forall f. ADReady f
           => f rn n -> (Domains f, f rn n, Domains f) -> f rn n
        df cx (ca, x, a) = df0 cx ca x a
        rf :: forall f. ADReady f
           => f rn n -> (f rn n, Domains f) -> (f rn n, Domains f)
        rf cx (x, a) = domsToPair $ dunDomains domsOD $ rf0 cx x a
    in D (flattenADShare $ l1 : V.toList ll2)
         (rscanDDer @ranked f df0 rf0 od x0 as)
         (ScanDR f x0 as df rf x0' as')
  sfold :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> ADVal shaped rn sh
        -> ADVal shaped rm (k ': shm)
        -> ADVal shaped rn sh
  sfold f (D l1 x0 x0') (D l2 as as') =
    let domsOD = V.fromList [odFromShS @rn @sh, odFromShS @rm @shm]
        domsToPair :: forall f. ADReadyS f
                   => Domains (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: Domains (ADVal (RankedOf shaped)) -> ADVal shaped rn sh
        g doms = uncurry (f @(ADVal shaped)) (domsToPair doms)
        df :: shaped rn sh -> (shaped rm shm, shaped rn sh, shaped rm shm)
           -> shaped rn sh
        df cx (ca, x, a) =
          fst $ cfwdOnDomains (V.fromList [DynamicShaped x, DynamicShaped a])
                              g
                              (V.fromList [DynamicShaped cx, DynamicShaped ca])
        rf :: shaped rn sh -> (shaped rn sh, shaped rm shm)
           -> (shaped rn sh, shaped rm shm)
        rf dt (x, a) =
          domsToPair $ dunDomains @ranked domsOD $ fst
          $ crevOnDomains (Just dt) g
                          (V.fromList [DynamicShaped x, DynamicShaped a])
    in D (l1 `mergeADShare` l2)
         (sfold @ranked f x0 as)
         (FoldS f x0 as df rf x0' as')
  sfoldDer :: forall rn rm sh shm k.
              ( GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm
              , KnownNat k )
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> DomainsOf f)
           -> ADVal shaped rn sh
           -> ADVal shaped rm (k ': shm)
           -> ADVal shaped rn sh
  sfoldDer f df0 rf0 (D l1 x0 x0') (D l2 as as') =
    let domsOD = V.fromList [odFromShS @rn @sh, odFromShS @rm @shm]
        domsToPair :: forall f. ADReadyS f
                   => Domains (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        df :: forall f. ADReadyS f
           => f rn sh -> (f rm shm, f rn sh, f rm shm) -> f rn sh
        df cx (ca, x, a) = df0 cx ca x a
        rf :: forall f. ADReadyS f
           => f rn sh -> (f rn sh, f rm shm) -> (f rn sh, f rm shm)
        rf cx (x, a) = domsToPair $ dunDomains domsOD $ rf0 cx x a
    in D (l1 `mergeADShare` l2)
         (sfoldDer @ranked f df0 rf0 x0 as)
         (FoldS f x0 as df rf x0' as')

unADValDomains :: DynamicTensor (ADVal f)
               -> (ADShare, DynamicTensor f, DynamicTensor (Dual f))
unADValDomains (DynamicRanked (D l t t')) =
  (l, DynamicRanked t, DynamicRanked t')
unADValDomains (DynamicShaped (D l t t')) =
  (l, DynamicShaped t, DynamicShaped t')
unADValDomains (DynamicRankedDummy p1 p2) =
  (emptyADShare, DynamicRankedDummy p1 p2, DynamicRankedDummy p1 p2)
unADValDomains (DynamicShapedDummy p1 p2) =
  (emptyADShare, DynamicShapedDummy p1 p2, DynamicShapedDummy p1 p2)


-- * DomainsTensor instance for concrete arrays

instance DomainsTensor (Flip OR.Array) (Flip OS.Array) where
  dmkDomains = id
  dunDomains _ = id
  rletInDomains = (&)
  sletInDomains = (&)
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains f -> f r n)
       -> DomainsOD
       -> DomainsOD
       -> DomainsOD
  rrev f _parameters0 parameters =
    fst $ crevOnDomains Nothing (f @(ADVal (Flip OR.Array))) parameters
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => Domains f -> f r n)
         -> DomainsOD
         -> DomainsOD
         -> Flip OR.Array r n
         -> DomainsOD
  rrevDt f _parameters0 parameters dt =
    fst $ crevOnDomains (Just dt) (f @(ADVal (Flip OR.Array))) parameters
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains f -> f r n)
       -> DomainsOD
       -> DomainsOD
       -> DomainsOD
       -> Flip OR.Array r n
  rfwd f _parameters0 parameters ds =
    fst $ cfwdOnDomains parameters (f @(ADVal (Flip OR.Array))) ds
  srev f _parameters0 parameters =
    fst $ crevOnDomains Nothing (f @(ADVal (Flip OS.Array))) parameters
  srevDt f _parameters0 parameters dt =
    fst $ crevOnDomains (Just dt) (f @(ADVal (Flip OS.Array))) parameters
  sfwd f _parameters0 parameters ds =
    fst $ cfwdOnDomains parameters (f @(ADVal (Flip OS.Array))) ds
  rfold :: (GoodScalar rm, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> Flip OR.Array rn n
        -> Flip OR.Array rm (1 + m)
        -> Flip OR.Array rn n
  rfold f x0 as = foldl' f x0 (runravelToList as)
  rfoldDer :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> Flip OR.Array rn n
           -> Flip OR.Array rm (1 + m)
           -> Flip OR.Array rn n
  rfoldDer f _df _rf x0 as = rfold f x0 as
  rscan f x0 as = rfromList $ scanl' f x0 (runravelToList as)
  rscanDer f _df _rf x0 as = rscan f x0 as
  rscanD f _od x0 as = rfromList $ scanl' f x0 (unravelDomains as)
  rscanDDer f _df _rf od x0 as = rscanD f od x0 as
  sfold :: (GoodScalar rm, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> Flip OS.Array rn sh
        -> Flip OS.Array rm (k ': shm)
        -> Flip OS.Array rn sh
  sfold f x0 as = foldl' f x0 (sunravelToList as)
  sfoldDer :: ( GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm
              , KnownNat k )
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> DomainsOf f)
           -> Flip OS.Array rn sh
           -> Flip OS.Array rm (k ': shm)
           -> Flip OS.Array rn sh
  sfoldDer f _df _dr x0 as = sfold f x0 as
