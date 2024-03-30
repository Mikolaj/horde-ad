{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for dual numbers. Most of the definitions
-- are generic over whether the dual numbers are built from concrete arrays
-- of floats or from AST terms. However, here we do not abstract over
-- the typing of tensors and so we give separate instances
-- for ranked tensors and shaped tensors.
module HordeAd.Core.TensorADVal
  ( aDValToHVector, hVectorADValToADVal, unADValHVector, unADValDynamicTensor
  , crevOnADInputs, crevOnHVector, cfwdOnADInputs, cfwdOnHVector
  ) where

import Prelude hiding (foldl')

import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Function ((&))
import           Data.Functor.Const
import           Data.List (foldl')
import           Data.List.Index (imap)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.Delta
import           HordeAd.Core.DualNumber
import           HordeAd.Core.HVector
import           HordeAd.Core.HVectorOps
import           HordeAd.Core.IsPrimal
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

-- * Non-symbolic reverse and forward derivative computation

crevOnADInputs
  :: ADReady ranked
  => Maybe (HVector ranked)
  -> (HVector (ADVal ranked)
      -> ADVal (HVectorPseudoTensor ranked) r y)
  -> HVector (ADVal ranked)
  -> (HVectorOf ranked, HVectorPseudoTensor ranked r y)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D l v deltaTopLevel) = f inputs in
  let rshapePrimal :: (GoodScalar r2, KnownNat n, ADReady g)
                   => ADVal g r2 n -> ShapeInt n
      rshapePrimal (D _ p _) = rshape p
      parameters0 = V.map (voidFromDynamicF (shapeToList . rshapePrimal)) inputs
      !gradient = gradientFromDeltaH parameters0 v mdt deltaTopLevel
  in (dunlet l (dmkHVector gradient), unletPseudo l v)

crevOnHVector
  :: ADReady ranked
  => Maybe (HVector ranked)
  -> (HVector (ADVal ranked)
      -> ADVal (HVectorPseudoTensor ranked) r y)
  -> HVector ranked
  -> (HVectorOf ranked, HVectorPseudoTensor ranked r y)
crevOnHVector mdt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in crevOnADInputs mdt f inputs

cfwdOnADInputs
  :: ADReady ranked
  => HVector (ADVal ranked)
  -> (HVector (ADVal ranked)
      -> ADVal (HVectorPseudoTensor ranked) r y)
  -> HVector ranked
  -> ( HVectorPseudoTensor ranked r y
     , HVectorPseudoTensor ranked r y )
{-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs inputs f ds =
  let !(D l v deltaTopLevel) = f inputs in
  let derivative = derivativeFromDeltaH (V.length inputs) deltaTopLevel ds
  in (unletPseudo l derivative, unletPseudo l v)

cfwdOnHVector
  :: ADReady ranked
  => HVector ranked
  -> (HVector (ADVal ranked)
      -> ADVal (HVectorPseudoTensor ranked) r y)
  -> HVector ranked
  -> ( HVectorPseudoTensor ranked r y
     , HVectorPseudoTensor ranked r y )
cfwdOnHVector parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in cfwdOnADInputs inputs f ds

unletPseudo
  :: ADReady ranked
  => ADShare -> HVectorPseudoTensor ranked r y
  -> HVectorPseudoTensor ranked r y
unletPseudo l =
  HVectorPseudoTensor . dunlet l . unHVectorPseudoTensor


-- * Ranked tensor instances

instance (KnownNat n, GoodScalar r, ADReady ranked)
         => AdaptableHVector (ADVal ranked)
                             (ADVal ranked r n) where
{- TODO: RULE left-hand side too complicated to desugar in GHC 9.6.4
    with -O0, but not -O1
  {-# SPECIALIZE instance
      (KnownNat n, ADReady (Flip OR.Array))
      => AdaptableHVector (ADVal (Flip OR.Array))
                          (ADVal (Flip OR.Array) Double n) #-}
  {-# SPECIALIZE instance
      (KnownNat n, ADReady (AstRanked PrimalSpan))
      => AdaptableHVector (ADVal (AstRanked PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit = fromHVectorR

instance (KnownNat n, GoodScalar r, ADReady ranked)
         => DualNumberValue (ADVal ranked r n) where
  type DValue (ADVal ranked r n) = Flip OR.Array r n  -- ! not Value(ranked)
  fromDValue t = constantADVal $ rconst $ runFlip t

-- This is temporarily moved from Adaptor in order to specialize manually
instance AdaptableHVector ranked a
         => AdaptableHVector ranked [a] where
  {-# SPECIALIZE instance
      AdaptableHVector (Flip OR.Array) (OR.Array n Double)
      => AdaptableHVector (Flip OR.Array)
                          [OR.Array n Double] #-}
  {-# SPECIALIZE instance
      AdaptableHVector (AstRanked s)
                       (AstRanked s Double n)
      => AdaptableHVector (AstRanked s)
                          [AstRanked s Double n] #-}
  toHVector = V.concat . map toHVector
  fromHVector lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromHVector aInit restAcc of
            Just (a, rest) -> (a : lAcc, rest)
            Nothing -> error "fromHVector [a]"
        (l, !restAll) = foldl' f ([], source) lInit
        !rl = reverse l
    in Just (rl, restAll)
    -- is the following as performant? benchmark:
    -- > fromHVector lInit source =
    -- >   let f = swap . flip fromHVector
    -- >   in swap $ mapAccumL f source lInit

instance TermValue a => TermValue [a] where
  type Value [a] = [Value a]
  fromValue = map fromValue

instance DualNumberValue a => DualNumberValue [a] where
  type DValue [a] = [DValue a]
  fromDValue = map fromDValue

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ADReady ranked => RankedTensor (ADVal ranked) where
  rlet (D l u u') f =
    let !(!l2, var2) = rsharePrimal u l
    in f (dDnotShared l2 var2 u')
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
    let !(!l3, u) = rsharePrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = rsharePrimal ve l3
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
  rletHVectorIn asD f = f asD
{- TODO: Verify if this really helps sharing.
         BTW, it's broken when simplification in astLetHVectorIn is disabled,
         probably because asUnshared has variables bound in ll2
         and so l3 has such variables, but an individual l doesn't provied
         them all, so some variables are dangling when interpreting terms.
         We'd need to flatten ll2 and put instead of l.
    let !(!ll2, asUnshared, as') = unADValHVector asD
        !(!l3, as) =
          dsharePrimal (dmkHVector asUnshared) emptyADShare
        aDValDynamicTensor3 l a a' =
          aDValDynamicTensor (mergeADShare l3 l) a a'
        doms = V.zipWith3 aDValDynamicTensor3 ll2 as as'
          -- This could be done with rsharePrimal,
          -- but more ADShare nodes would generated.
    in f doms
-}
  rletHFunIn = (&)
  rfromS :: forall r sh. (GoodScalar r, Sh.Shape sh)
         => ADVal (ShapedOf ranked) r sh -> ADVal ranked r (Sh.Rank sh)
  rfromS (D l u u') = dDnotShared l (rfromS u) (dRFromS u')
   where
    dRFromS (SFromR d) = d  -- no information lost, so no checks
    dRFromS d = RFromS d

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

instance ( ADReadyS shaped, Sh.Shape sh, GoodScalar r
         , ranked ~ RankedOf shaped )
         => AdaptableHVector (ADVal ranked)
                             (ADVal shaped r sh) where
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit = fromHVectorS

instance (ADReadyS shaped, Sh.Shape sh, GoodScalar r)
         => DualNumberValue (ADVal shaped r sh) where
  type DValue (ADVal shaped r sh) = Flip OS.Array r sh   -- ! not Value(shaped)
  fromDValue t = constantADVal $ sconst $ runFlip t

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ADReadyS shaped => ShapedTensor (ADVal shaped) where
  slet (D l u u') f =
    let !(!l2, var2) = ssharePrimal u l
    in f (dDnotShared l2 var2 u')
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
    let !(!l3, u) = ssharePrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = ssharePrimal ve l3
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
        f i ui = dD l ui (IndexS u' (ShapedList.singletonIndex
                                     $ fromIntegral i))
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
  sbuild1 f = fromListS $ map (f . ShapedList.shapedNat . fromIntegral)
                              [0 :: Int .. valueOf @n - 1]
                   -- element-wise (POPL) version
  sgather (D l u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD l (sgather u g) (GatherS u' g)
  scast (D l u u') = dD l (scast u) (CastS u')
  sfromIntegral (D l u _) =
    let v = sfromIntegral u
    in dDnotShared l v (dZeroOfShape v)
  sconst t = constantADVal (sconst t)
  sletHVectorIn asD f = f asD
{- TODO: See similar code above.
    let !(!ll2, asUnshared, as') = unADValHVector asD
        !(!l3, as) =
          dsharePrimal @(RankedOf shaped) @shaped
                       (dmkHVector asUnshared) emptyADShare
            -- This could be done with ssharePrimal, but the code
            -- would be more complex and more ADShare nodes generated.
            -- OTOH, f would be free to assume there are no dangling variables.
        !(D l u u') = f $ aDValHVector ll2 as as'
    in dDnotShared (mergeADShare l3 l) u u'
-}
  sletHFunIn = (&)
  sfromR :: forall r sh. (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Rank sh))
         => ADVal (RankedOf shaped) r (Sh.Rank sh) -> ADVal shaped r sh
  sfromR (D l u u') = dDnotShared l (sfromR u) (dSFromR u')
   where
    dSFromR (RFromS @sh1 d) =
      case sameShape @sh1 @sh of
        Just Refl -> d
        _ -> error "sfromR: different shapes in SFromR(RFromS)"
    dSFromR d = SFromR d

  sconstant t = let (l, r) = sletUnwrap t in dDnotShared l r (dZeroOfShape t)
  sprimalPart (D l u _) = sletWrap l u
  sdualPart (D l _ u') = Pair (Clown (Const l)) u'
  sD ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = sletUnwrap ast
    in dD (l `mergeADShare` l2) r delta
  sScale ast (Pair (Clown (Const l)) delta) =
    let (l2, r) = sletUnwrap ast
    in Pair (Clown (Const (l `mergeADShare` l2))) (dScale r delta)


-- * HVectorTensor instance

instance (ADReady ranked, HVectorOf ranked ~ HVector ranked)
         => AdaptableHVector (ADVal ranked)
                             (ADVal (HVectorPseudoTensor ranked)
                                    Float '()) where
  toHVector = aDValToHVector
  fromHVector (D _ (HVectorPseudoTensor h) _) params =
    let (portion, rest) = V.splitAt (V.length h) params
    in Just (hVectorADValToADVal portion, rest)

instance ADReadyBoth ranked shaped
         => HVectorTensor (ADVal ranked) (ADVal shaped) where
  dshape = voidFromHVector
  dmkHVector = id
  dlambda _ = id
  dHApply (HFun f) = f
  dunHVector = id
  dletHVectorInHVector asD f = f asD
{- TODO: See similar code above.
    let !(!ll2, asUnshared, as') = unADValHVector asD
        !(!l3, as) =
          dsharePrimal (dmkHVector asUnshared) emptyADShare
        aDValDynamicTensor3 l a a' =
          aDValDynamicTensor (mergeADShare l3 l) a a'
        doms = V.zipWith3 aDValDynamicTensor3 ll2 as as'
          -- This could be done with rsharePrimal,
          -- but more ADShare nodes would generated.
    in f doms
-}
  dletHFunInHVector = (&)
  rletInHVector (D l u u') f =
    let !(!l2, var2) = rsharePrimal u l
    in f (dDnotShared l2 var2 u')
  sletInHVector (D l u u') f =
    let !(!l2, var2) = ssharePrimal u l
    in f (dDnotShared l2 var2 u')
  dsharePrimal d l = (l, d)
  dbuild1 k f =
    ravelHVector $ map (f . fromIntegral) [0 .. (sNatValue k :: Int) - 1]
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (ADVal ranked)
       -> HVectorOf (ADVal ranked)
  rrev f _parameters0 parameters =
    -- This computes the derivative of g again for each new @parmeters@.
    let g :: HVector (ADVal (ADVal ranked))
          -> ADVal (HVectorPseudoTensor (ADVal ranked)) r y
        g !hv = let D l a a' = f hv
                in dDnotShared l
                               (HVectorPseudoTensor $ dmkHVector
                                $ V.singleton $ DynamicRanked a)
                               (HVectorPseudoTensor $ HToH
                                $ V.singleton $ DynamicRanked a')
    in fst $ crevOnHVector Nothing g parameters
  drevDt :: VoidHVector
         -> HFun
         -> HFun
  drevDt _shs h =
    let g :: ADReady f
          => HVector (ADVal f)
          -> ADVal (HVectorPseudoTensor f) r y
        g !hv = let (ll, as, as') = unADValHVector $ unHFun h [hv]
                in dDnotShared (flattenADShare $ V.toList ll)
                               (HVectorPseudoTensor $ dmkHVector as)
                               (HVectorPseudoTensor $ HToH as')
        rf :: forall f. ADReady f => [HVector f] -> HVectorOf f
        rf [!db, !a] =
          -- This computes the derivative of g again for each new db and a.
          fst $ crevOnHVector (Just db) g a
        rf _ = error "rf: wrong number of arguments"
    in HFun rf
  dfwd :: VoidHVector
       -> HFun
       -> HFun
  dfwd _shs h =
    let g :: ADReady f
          => HVector (ADVal f)
          -> ADVal (HVectorPseudoTensor f) r y
        g !hv = let (ll, as, as') = unADValHVector $ unHFun h [hv]
                in dDnotShared (flattenADShare $ V.toList ll)
                               (HVectorPseudoTensor $ dmkHVector as)
                               (HVectorPseudoTensor $ HToH as')
        df :: forall f. ADReady f => [HVector f] -> HVectorOf f
        df [!da, !a] = unHVectorPseudoTensor $ fst $ cfwdOnHVector a g da
          -- This computes the derivative of g again for each new da and a.
        df _ = error "df: wrong number of arguments"
    in HFun df
  dmapAccumRDer
    :: Proxy (ADVal ranked)
    -> SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> HFun
    -> HFun
    -> HFun
    -> HVectorOf (ADVal ranked)
    -> HVectorOf (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0D esD =
    assert (voidHVectorMatches (replicate1VoidHVector k eShs) esD
            && voidHVectorMatches accShs acc0D) $
    let (ll2, acc0, acc0') = unADValHVector acc0D
        (ll3, esUnshared, es') = unADValHVector esD
        (l4, es) =
          dsharePrimal (dmkHVector esUnshared)
                       (flattenADShare $ V.toList ll2 ++ V.toList ll3)
        codomainShs = accShs V.++ bShs
        accLen = V.length accShs
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair = V.splitAt accLen
        g :: forall f. ADReady f => [HVector f] -> HVectorOf f
        g [!acc, !e] =
          dletHVectorInHVector (unHFun f [acc, e]) $ \res ->
            let (accRes, bRes) = hvToPair res
            in dmkHVector $ V.concat [accRes, acc, bRes]
        g _ = error "g: wrong number of arguments"
        dg :: forall f. ADReady f => [HVector f] -> HVectorOf f
        dg [!dacc_de, !acc_e] =
          dletHVectorInHVector (unHFun df [dacc_de, acc_e]) $ \res ->
            let (accRes, bRes) = hvToPair res
            in dmkHVector $ V.concat [accRes, V.take accLen dacc_de, bRes]
        dg _ = error "dg: wrong number of arguments"
        rg :: forall f. ADReady f => [HVector f] -> HVectorOf f
        rg [!dx_db, !acc_e] =
          let (dx, db) = hvToPair dx_db
              (dbacc, dbRes) = hvToPair db
          in dletHVectorInHVector (unHFun rf [dx V.++ dbRes, acc_e]) $ \res ->
            let (dacc, de) = hvToPair res
            in dmkHVector $ V.concat [V.zipWith addDynamic dacc dbacc, de]
        rg _ = error "rg: wrong number of arguments"
        pUnshared :: HVectorOf ranked
        pUnshared = dmapAccumRDer (Proxy @ranked)
                                  k accShs codomainShs eShs
                                  (dlambda @ranked [accShs, eShs] $ HFun g)
                                  (dlambda @ranked
                                           [accShs V.++ eShs, accShs V.++ eShs]
                                   $ HFun dg)
                                  (dlambda @ranked
                                           [ accShs V.++ codomainShs
                                           , accShs V.++ eShs ]
                                   $ HFun rg)
                                  (dmkHVector acc0) (dmkHVector es)
        (l5, pShared) = dsharePrimal pUnshared l4
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        accFin = V.take accLen pShared
        q = V.slice accLen accLen pShared
        bs = V.drop (2 * accLen) pShared
        !_A = assert (voidHVectorMatches (replicate1VoidHVector k bShs) bs) ()
        primal = accFin V.++ bs
        dual = wrapDeltaH $ MapAccumR k accShs bShs eShs q es df rf acc0' es'
    in ahhToHVector l5 primal dual
  dmapAccumLDer
    :: Proxy (ADVal ranked)
    -> SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> HFun
    -> HFun
    -> HFun
    -> HVectorOf (ADVal ranked)
    -> HVectorOf (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0D esD =
    assert (voidHVectorMatches (replicate1VoidHVector k eShs) esD
            && voidHVectorMatches accShs acc0D
            `blame` ( shapeVoidHVector (replicate1VoidHVector k eShs)
                    , shapeVoidHVector (voidFromHVector esD)
                    , shapeVoidHVector accShs
                    , shapeVoidHVector (voidFromHVector acc0D) )) $
    let (ll2, acc0, acc0') = unADValHVector acc0D
        (ll3, esUnshared, es') = unADValHVector esD
        (l4, es) =
          dsharePrimal (dmkHVector esUnshared)
                       (flattenADShare $ V.toList ll2 ++ V.toList ll3)
        codomainShs = accShs V.++ bShs
        accLen = V.length accShs
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair = V.splitAt accLen
        g :: forall f. ADReady f => [HVector f] -> HVectorOf f
        g [!acc, !e] =
          dletHVectorInHVector (unHFun f [acc, e]) $ \res ->
            let (accRes, bRes) = hvToPair res
            in dmkHVector $ V.concat [accRes, acc, bRes]
        g _ = error "g: wrong number of arguments"
        dg :: forall f. ADReady f => [HVector f] -> HVectorOf f
        dg [!dacc_de, !acc_e] =
          dletHVectorInHVector (unHFun df [dacc_de, acc_e]) $ \res ->
            let (accRes, bRes) = hvToPair res
            in dmkHVector $ V.concat [accRes, V.take accLen dacc_de, bRes]
        dg _ = error "dg: wrong number of arguments"
        rg :: forall f. ADReady f => [HVector f] -> HVectorOf f
        rg [!dx_db, !acc_e] =
          let (dx, db) = hvToPair dx_db
              (dbacc, dbRes) = hvToPair db
          in dletHVectorInHVector (unHFun rf [dx V.++ dbRes, acc_e]) $ \res ->
            let (dacc, de) = hvToPair res
            in dmkHVector $ V.concat [V.zipWith addDynamic dacc dbacc, de]
        rg _ = error "rg: wrong number of arguments"
        pUnshared :: HVectorOf ranked
        pUnshared = dmapAccumLDer (Proxy @ranked)
                                  k accShs codomainShs eShs
                                  (dlambda @ranked [accShs, eShs] $ HFun g)
                                  (dlambda @ranked
                                           [accShs V.++ eShs, accShs V.++ eShs]
                                   $ HFun dg)
                                  (dlambda @ranked
                                           [ accShs V.++ codomainShs
                                           , accShs V.++ eShs ]
                                   $ HFun rg)
                                  (dmkHVector acc0) (dmkHVector es)
        (l5, pShared) = dsharePrimal pUnshared l4
        accFin = V.take accLen pShared
        q = V.slice accLen accLen pShared
        bs = V.drop (2 * accLen) pShared
        !_A = assert (voidHVectorMatches (replicate1VoidHVector k bShs) bs) ()
        primal = accFin V.++ bs
        dual = wrapDeltaH $ MapAccumL k accShs bShs eShs q es df rf acc0' es'
    in ahhToHVector l5 primal dual

-- Float and '() are placeholders here; they are reduced away.
ahhToHVector
  :: forall ranked. RankedOf (ShapedOf ranked) ~ ranked
  => ADShare -> HVector ranked -> DeltaH ranked -> HVector (ADVal ranked)
ahhToHVector l h h' =
  let selectDual :: Int -> DynamicTensor ranked -> DynamicTensor (ADVal ranked)
      selectDual i d = case d of
        DynamicRanked t -> DynamicRanked $ dDnotShared l t (RFromH h' i)
        DynamicShaped t -> DynamicShaped $ dDnotShared l t (SFromH h' i)
        DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
        DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
  in V.imap selectDual h
       -- TODO: write why these projections don't break any sharing

aDValToHVector
  :: (HVectorOf ranked ~ HVector ranked, RankedOf (ShapedOf ranked) ~ ranked)
  => ADVal (HVectorPseudoTensor ranked) r y -> HVector (ADVal ranked)
aDValToHVector (D l (HVectorPseudoTensor h) (HVectorPseudoTensor h')) =
  ahhToHVector l h h'

-- `Float '()` instead of `r y` is needed to avoid
-- `Ambiguous type variables ‘r1’, ‘y1’ arising from a use of ‘crev’`
-- in contexts like `crev (hVectorADValToADVal . f)`.
hVectorADValToADVal
  :: forall ranked. HVectorTensor ranked (ShapedOf ranked)
  => HVector (ADVal ranked) -> ADVal (HVectorPseudoTensor ranked) Float '()
hVectorADValToADVal hv =
  let (ll, as, as') = unADValHVector hv
  in dDnotShared (flattenADShare $ V.toList ll)
                 (HVectorPseudoTensor $ dmkHVector as)
                 (HVectorPseudoTensor $ HToH as')

unADValHVector
  :: HVector (ADVal f)
  -> (Data.Vector.Vector ADShare, HVector f, HVector (Dual f))
unADValHVector = V.unzip3 . V.map unADValDynamicTensor

unADValDynamicTensor
  :: DynamicTensor (ADVal f)
  -> (ADShare, DynamicTensor f, DynamicTensor (Dual f))
unADValDynamicTensor (DynamicRanked (D l t t')) =
  (l, DynamicRanked t, DynamicRanked t')
unADValDynamicTensor (DynamicShaped (D l t t')) =
  (l, DynamicShaped t, DynamicShaped t')
unADValDynamicTensor (DynamicRankedDummy p1 p2) =
  (emptyADShare, DynamicRankedDummy p1 p2, DynamicRankedDummy p1 p2)
unADValDynamicTensor (DynamicShapedDummy p1 p2) =
  (emptyADShare, DynamicShapedDummy p1 p2, DynamicShapedDummy p1 p2)
