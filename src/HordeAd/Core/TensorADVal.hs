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
  ( dDHVector, aDValHVector, aDValDynamicTensor
  , hVectorADValToADVal, unADValHVector, unADValDynamicTensor
  ) where

import Prelude hiding (foldl')

import           Control.Exception.Assert.Sugar
import           Data.Array.Convert
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Function ((&))
import           Data.Functor.Const
import           Data.List (foldl', mapAccumR, scanl')
import           Data.List.Index (imap)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import           Data.Type.Ord (Compare)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+), type (-))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.Delta
import           HordeAd.Core.DualClass
import           HordeAd.Core.DualNumber
import           HordeAd.Core.HVector
import           HordeAd.Core.HVectorOps
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape)
import           HordeAd.Util.ShapedList (ShapedList (..), singletonShaped)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * Ranked tensor instances

instance (KnownNat n, GoodScalar r, ADReady ranked)
         => AdaptableHVector (ADVal ranked)
                             (ADVal ranked r n) where
{- TODO: RULE left-hand side too complicated to desugar
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector (ADVal (Flip OR.Array))
                          (ADVal (Flip OR.Array) Double n) #-}
TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector (ADVal (AstRanked PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  type Value (ADVal ranked r n) = Flip OR.Array r n  -- ! not Value(ranked)
  toHVector = undefined
  fromHVector _aInit params = fromHVectorR @r @n params

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
  type Value [a] = [Value a]
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

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ADReady ranked => RankedTensor (ADVal ranked) where
  rlet (D l u u') f =
    let !(!l2, var2) = recordSharingPrimal u l
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
  rletHVectorIn _od asD f = f asD
{- TODO: Verify if this really helps sharing.
         BTW, it's broken when simplification in astLetHVectorIn is disabled,
         probably because asUnshared has variables bound in ll2
         and so l3 has such variables, but an individual l doesn't provied
         them all, so some variables are dangling when interpreting terms.
         We'd need to flatten ll2 and put instead of l.
    let !(!ll2, asUnshared, as') = unADValHVector asD
        !(!l3, as) =
          drecordSharingPrimal od (dmkHVector asUnshared) emptyADShare
        aDValDynamicTensor3 l a a' =
          aDValDynamicTensor (mergeADShare l3 l) a a'
        doms = V.zipWith3 aDValDynamicTensor3 ll2 as as'
          -- This could be done with recordSharingPrimal,
          -- but more ADShare nodes would generated.
    in f doms
-}
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

instance ( ADReadyS shaped, Sh.Shape sh, GoodScalar r
         , ranked ~ RankedOf shaped )
         => AdaptableHVector (ADVal ranked)
                             (ADVal shaped r sh) where
  type Value (ADVal shaped r sh) = Flip OS.Array r sh   -- ! not Value(shaped)
  toHVector = undefined
  fromHVector _aInit params = fromHVectorS @r @sh params

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ADReadyS shaped => ShapedTensor (ADVal shaped) where
  slet (D l u u') f =
    let !(!l2, var2) = recordSharingPrimal u l
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
  sletHVectorIn _od asD f = f asD
{- TODO: See similar code above.
    let !(!ll2, asUnshared, as') = unADValHVector asD
        !(!l3, as) =
          drecordSharingPrimal @(RankedOf shaped) @shaped
                               od (dmkHVector asUnshared) emptyADShare
            -- This could be done with recordSharingPrimal, but the code
            -- would be more complex and more ADShare nodes generated.
            -- OTOH, f would be free to assume there are no dangling variables.
        !(D l u u') = f $ aDValHVector ll2 as as'
    in dDnotShared (mergeADShare l3 l) u u'
-}
  sfromR = rToS
   where
    rToS :: forall r sh. (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Rank sh))
         => ADVal (RankedOf shaped) r (Sh.Rank sh) -> ADVal shaped r sh
    rToS (D l u u') = dDnotShared l (sfromR u) (dRToS u')
     where
      dRToS (SToR @sh1 d) =
        case sameShape @sh1 @sh of
          Just Refl -> d
          _ -> error "sfromR: different shapes in RToS(SToR)"
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


-- * HVectorTensor instance

instance ADReadyBoth ranked shaped
         => HVectorTensor (ADVal ranked) (ADVal shaped) where
  dshape = voidFromHVector
  dmkHVector = id
  dunHVector _ = id
  dletHVectorInHVector _od asD f = f asD
{- TODO: See similar code above.
    let !(!ll2, asUnshared, as') = unADValHVector asD
        !(!l3, as) =
          drecordSharingPrimal od (dmkHVector asUnshared) emptyADShare
        aDValDynamicTensor3 l a a' =
          aDValDynamicTensor (mergeADShare l3 l) a a'
        doms = V.zipWith3 aDValDynamicTensor3 ll2 as as'
          -- This could be done with recordSharingPrimal,
          -- but more ADShare nodes would generated.
    in f doms
-}
  rletInHVector (D l u u') f =
    let !(!l2, var2) = recordSharingPrimal u l
    in f (dDnotShared l2 var2 u')
  sletInHVector (D l u u') f =
    let !(!l2, var2) = recordSharingPrimal u l
    in f (dDnotShared l2 var2 u')
  drecordSharingPrimal _ d l = (l, d)
  dregister _ d l = (l, d)
  dbuild1 k f = ravelHVector $ map (f . fromIntegral) [0 .. k - 1]
  dzipWith1 f u = case V.unsnoc u of
    Nothing -> error "dzipWith1: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "dzipWith1: wrong rank of argument"
      width : _ -> dbuild1 @(ADVal ranked) width (\i -> f (index1HVector u i))
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (ADVal ranked)
       -> HVectorOf (ADVal ranked)
  rrev f _parameters0 parameters =
    -- This computes the derivative of f again for each new @parmeters@.
    fst $ crevOnHVector Nothing (f @(ADVal (ADVal ranked))) parameters
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => HVector f -> f r n)
         -> VoidHVector
         -> HVector (ADVal ranked)
         -> ADVal ranked r n
         -> HVectorOf (ADVal ranked)
  rrevDt f _parameters0 parameters dt =
    fst $ crevOnHVector (Just dt) (f @(ADVal (ADVal ranked))) parameters
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (ADVal ranked)
       -> HVector (ADVal ranked)
       -> ADVal ranked r n
  rfwd f _parameters0 parameters ds =
    fst $ cfwdOnHVector parameters (f @(ADVal (ADVal ranked))) ds
  srev f _parameters0 parameters =
    fst $ crevOnHVector Nothing (f @(ADVal (ADVal shaped))) parameters
  srevDt f _parameters0 parameters dt =
    fst $ crevOnHVector (Just dt) (f @(ADVal (ADVal shaped))) parameters
  sfwd f _parameters0 parameters ds =
    fst $ cfwdOnHVector parameters (f @(ADVal (ADVal shaped))) ds
  rfold :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ADVal ranked rn n
        -> ADVal ranked rm (1 + m)
        -> ADVal ranked rn n
  rfold f (D l1 x0 x0') (D l2 asUnshared as') =
    -- This can't call rfoldDer, because UnletGradient constraint is needed
    -- in the computed derivatives, while rfoldDer gets derivatives with
    -- looser constraints thanks to interpreting terms in arbitrary algebras.
    -- If the refactoring is really needed, e.g., to avoid computing derivatives
    -- for each nested level of ADVal, we can add UnletGradient to ADReady.
    -- Given this, we don't try to share subterms at all in this code.
    -- This only matters in the case of instantiating this method directly
    -- to dual numbers over terms, which however side-steps vectorization,
    -- and so it's not supposed to produce small terms anyway.
    let _ws :: (Int, ShapeInt m)
        _ws@(width, _shm) = case rshape asUnshared of
          hd :$ tl -> (hd, tl)
          _ -> error "rfold: impossible pattern needlessly required"
        domsToPair :: forall f. ADReady f
                   => HVector f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: HVector (ADVal ranked) -> ADVal ranked rn n
        g doms = uncurry f (domsToPair doms)
        -- This computes the derivative of f again for each new @x@ and @a@
        -- (not even once for @as@, but for each @a@ separately).
        -- Note that this function, and similarly @rf and @f@ instantiated
        -- and passed to FoldRC, is not a function on dual numbers.
        -- Consequently, any dual number operations inserted there by the user
        -- are flattened away (which is represented in AST by @PrimalSpan@).
        -- TODO: what if the dual numbers are nested?
        -- TODO: do the dual number ops in f affect what df is computed? add
        -- a comment explaining that and tests that exemplify that
        df :: ranked rn n -> ranked rm m -> ranked rn n -> ranked rm m
           -> ranked rn n
        df cx ca x a =
          fst $ cfwdOnHVector (V.fromList [DynamicRanked x, DynamicRanked a])
                              g
                              (V.fromList [DynamicRanked cx, DynamicRanked ca])
        rf :: ranked rn n -> ranked rn n -> ranked rm m
           -> HVectorOf ranked
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.fromList [DynamicRanked x, DynamicRanked a])
        (l3, as) = recordSharingPrimal asUnshared (l1 `mergeADShare` l2)
        p :: ranked rn (1 + n)
        p = rscan f x0 as
        (l4, pShared) = recordSharingPrimal p l3
    in dDnotShared l4 (pShared ! (fromIntegral width :. ZI))
                      (FoldRC pShared as df rf x0' as')
  rfoldDer :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f)
           -> ADVal ranked rn n
           -> ADVal ranked rm (1 + m)
           -> ADVal ranked rn n
  rfoldDer f df rf (D l1 x0 x0') (D l2 asUnshared as') =
    let (l3, as) = recordSharingPrimal asUnshared (l1 `mergeADShare` l2)
        p :: ranked rn (1 + n)
        p = rscanDer f df rf x0 as
        width = rlength p - 1
        (l4, pShared) = recordSharingPrimal p l3
    in dDnotShared l4 (pShared ! (fromIntegral width :. ZI))
                      (FoldR pShared as df rf x0' as')
  rfoldZip :: forall rn n. (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
         -> VoidHVector
         -> ADVal ranked rn n
         -> HVector (ADVal ranked)
         -> ADVal ranked rn n
  rfoldZip f domsOD (D l1 x0 x0') asD =
    let (ll2, asUnshared, as') = unADValHVector asD
        domsToPair :: forall f. ADReady f => HVector f -> (f rn n, HVector f)
        domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
        g :: HVector (ADVal ranked) -> ADVal ranked rn n
        g doms = uncurry f (domsToPair doms)
        df :: ranked rn n -> HVector ranked -> ranked rn n -> HVector ranked
           -> ranked rn n
        df cx ca x a =
          fst $ cfwdOnHVector (V.cons (DynamicRanked x) a)
                              g
                              (V.cons (DynamicRanked cx) ca)
        rf :: ranked rn n -> ranked rn n -> HVector ranked -> HVectorOf ranked
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.cons (DynamicRanked x) a)
        width = case V.unsnoc asUnshared of
          Nothing -> error "rfoldZip: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rfoldZip: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD)
                                   asD) $
        let (l3, as) =
              drecordSharingPrimal @ranked
                                   (replicate1VoidHVector (Proxy @k) domsOD)
                                   (dmkHVector asUnshared)
                                   (flattenADShare $ l1 : V.toList ll2)
              -- This could be done with many calls to recordSharingPrimal,
              -- but more ADShare nodes would generated. This reduces
              -- to normal lets as soon as rewriting is started, anyway.
            p :: ranked rn (1 + n)
            p = rscanZip f domsOD x0 as
            (l4, pShared) = recordSharingPrimal p l3
        in dDnotShared l4 (pShared ! (fromIntegral width :. ZI))
                          (FoldZipRC domsOD pShared as df rf x0' as')
      _ -> error "rfoldZip: impossible someNatVal"
  rfoldZipDer :: forall rn n. (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> HVector f -> f rn n -> HVector f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> HVector f
                -> HVectorOf f)
            -> VoidHVector
            -> ADVal ranked rn n
            -> HVector (ADVal ranked)
            -> ADVal ranked rn n
  rfoldZipDer f df rf domsOD (D l1 x0 x0') asD =
    let (ll2, asUnshared, as') = unADValHVector asD
        width = case V.unsnoc asUnshared of
          Nothing -> error "rfoldZipDer: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rfoldZipDer: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD)
                                   asD) $
        let (l3, as) =
              drecordSharingPrimal @ranked
                                   (replicate1VoidHVector (Proxy @k) domsOD)
                                   (dmkHVector asUnshared)
                                   (flattenADShare $ l1 : V.toList ll2)
            p :: ranked rn (1 + n)
            p = rscanZipDer f df rf domsOD x0 as
            (l4, pShared) = recordSharingPrimal p l3
        in dDnotShared l4 (pShared ! (fromIntegral width :. ZI))
                          (FoldZipR domsOD pShared as df rf x0' as')
      _ -> error "rfoldZipDer: impossible someNatVal"
  rscan :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ADVal ranked rn n
        -> ADVal ranked rm (1 + m)
        -> ADVal ranked rn (1 + n)
  rscan f (D l1 x0 x0') (D l2 asUnshared as') =
    let _ws :: (Int, ShapeInt m)
        _ws@(width, _shm) = case rshape asUnshared of
          hd :$ tl -> (hd, tl)
          _ -> error "rscan: impossible pattern needlessly required"
        domsToPair :: forall f. ADReady f => HVector f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: HVector (ADVal ranked) -> ADVal ranked rn n
        g doms = uncurry f (domsToPair doms)
        df :: ranked rn n -> ranked rm m -> ranked rn n -> ranked rm m
           -> ranked rn n
        df cx ca x a =
          fst $ cfwdOnHVector (V.fromList [DynamicRanked x, DynamicRanked a])
                              g
                              (V.fromList [DynamicRanked cx, DynamicRanked ca])
        rf :: ranked rn n -> ranked rn n -> ranked rm m
           -> HVectorOf ranked
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.fromList [DynamicRanked x, DynamicRanked a])
        (l3, as) = recordSharingPrimal asUnshared (l1 `mergeADShare` l2)
        p :: ranked rn (1 + n)
        p = rscan f x0 as
        (l4, pShared) = recordSharingPrimal p l3
        -- The following sugar won't work, because i in slice needs
        -- to be statically known. Indeed, vectorization would break down
        -- due to this i, even if baked into the semantics of rfold, etc.
        -- rscan f x0 as = rbuild1 (rlength as + 1)
        --                 $ \i -> rfold f x0 (rslice 0 i as)
        scanAsFold =
          let h (pPrefix, asPrefix, as'Prefix) =
                FoldRC pPrefix asPrefix df rf x0' as'Prefix
              -- starting from 0 would be better, but I'm
              -- getting "tfromListR: shape ambiguity, no arguments"
              initsViaSliceP = map (\k -> rslice @ranked 0 (1 + k) pShared)
                                   [1 .. width]
              initsViaSlice = map (\k -> rslice @ranked 0 k as) [1 .. width]
              initsViaSliceD = map (\k -> SliceR 0 k as') [1 .. width]
          in FromListR
             $ x0' : map h (zip3 initsViaSliceP initsViaSlice initsViaSliceD)
    in dDnotShared l4 pShared scanAsFold
  rscanDer :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f)
           -> ADVal ranked rn n
           -> ADVal ranked rm (1 + m)
           -> ADVal ranked rn (1 + n)
  rscanDer f df rf (D l1 x0 x0') (D l2 asUnshared as') =
    let (l3, as) = recordSharingPrimal asUnshared (l1 `mergeADShare` l2)
        p :: ranked rn (1 + n)
        p = rscanDer f df rf x0 as
        (l4, pShared) = recordSharingPrimal p l3
    in dDnotShared l4 pShared
                      (ScanR pShared as df rf x0' as')
  rscanZip :: forall rn n. (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
         -> VoidHVector
         -> ADVal ranked rn n
         -> HVector (ADVal ranked)
         -> ADVal ranked rn (1 + n)
  rscanZip f domsOD (D l1 x0 x0') asD =
    let (ll2, asUnshared, as') = unADValHVector asD
        domsToPair :: forall f. ADReady f => HVector f -> (f rn n, HVector f)
        domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
        g :: HVector (ADVal ranked) -> ADVal ranked rn n
        g doms = uncurry f (domsToPair doms)
        df :: ranked rn n -> HVector ranked -> ranked rn n -> HVector ranked
           -> ranked rn n
        df cx ca x a =
          fst $ cfwdOnHVector (V.cons (DynamicRanked x) a)
                              g
                              (V.cons (DynamicRanked cx) ca)
        rf :: ranked rn n -> ranked rn n -> HVector ranked -> HVectorOf ranked
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.cons (DynamicRanked x) a)
        width = case V.unsnoc asUnshared of
          Nothing -> error "rscanZip: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rscanZip: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD)
                                   asD) $
        let (l3, as) =
              drecordSharingPrimal @ranked
                                   (replicate1VoidHVector (Proxy @k) domsOD)
                                   (dmkHVector asUnshared)
                                   (flattenADShare $ l1 : V.toList ll2)
            p :: ranked rn (1 + n)
            p = rscanZip f domsOD x0 as
            (l4, pShared) = recordSharingPrimal p l3
            scanAsFold =
              let h (pPrefix, asPrefix, as'Prefix) =
                    FoldZipRC domsOD pPrefix asPrefix df rf x0' as'Prefix
                  initsViaSliceP = map (\k -> rslice @ranked 0 (1 + k) pShared)
                                       [1 .. width]
                  initsViaSlice =
                    map (\k -> mapHVectorRanked11 (rslice @ranked 0 k) as)
                        [1 .. width]
                  initsViaSliceD =
                    map (\k -> mapHVectorDeltaR11 (SliceR 0 k) as')
                        [1 .. width]
              in FromListR
              $ x0' : map h (zip3 initsViaSliceP initsViaSlice initsViaSliceD)
        in dDnotShared l4 pShared scanAsFold
      _ -> error "rscanZip: impossible someNatVal"
  rscanZipDer :: forall rn n. (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> HVector f -> f rn n -> HVector f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> HVector f
                -> HVectorOf f)
            -> VoidHVector
            -> ADVal ranked rn n
            -> HVector (ADVal ranked)
            -> ADVal ranked rn (1 + n)
  rscanZipDer f df rf domsOD (D l1 x0 x0') asD =
    let (ll2, asUnshared, as') = unADValHVector asD
        width = case V.unsnoc asUnshared of
          Nothing -> error "rscanZipDer: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rscanZipDer: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD)
                                   asD) $
        let (l3, as) =
              drecordSharingPrimal @ranked
                                   (replicate1VoidHVector (Proxy @k) domsOD)
                                   (dmkHVector asUnshared)
                                   (flattenADShare $ l1 : V.toList ll2)
            p :: ranked rn (1 + n)
            p = rscanZipDer f df rf domsOD x0 as
            (l4, pShared) = recordSharingPrimal p l3
        in dDnotShared l4 pShared
                          (ScanZipR domsOD pShared as df rf x0' as')
      _ -> error "rscanZipDer: impossible someNatVal"
  sfold :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> ADVal shaped rn sh
        -> ADVal shaped rm (k ': shm)
        -> ADVal shaped rn sh
  sfold f (D l1 x0 x0') (D l2 asUnshared as') =
    let domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: HVector (ADVal ranked) -> ADVal shaped rn sh
        g doms = uncurry f (domsToPair doms)
        df :: shaped rn sh -> shaped rm shm -> shaped rn sh -> shaped rm shm
           -> shaped rn sh
        df cx ca x a =
          fst $ cfwdOnHVector (V.fromList [DynamicShaped x, DynamicShaped a])
                              g
                              (V.fromList [DynamicShaped cx, DynamicShaped ca])
        rf :: shaped rn sh -> shaped rn sh -> shaped rm shm
           -> HVectorOf ranked
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.fromList [DynamicShaped x, DynamicShaped a])
        (l3, as) = recordSharingPrimal asUnshared (l1 `mergeADShare` l2)
        p :: shaped rn (1 + k ': sh)
        p = sscan f x0 as
        width = slength p - 1
        (l4, pShared) = recordSharingPrimal p l3
    in dDnotShared l4 (pShared !$ (fromIntegral width :$: ZSH))
                      (FoldSC pShared as df rf x0' as')
  sfoldDer :: forall rn rm sh shm k.
              ( GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm
              , KnownNat k )
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f))
           -> ADVal shaped rn sh
           -> ADVal shaped rm (k ': shm)
           -> ADVal shaped rn sh
  sfoldDer f df rf (D l1 x0 x0') (D l2 asUnshared as') =
    let (l3, as) = recordSharingPrimal asUnshared (l1 `mergeADShare` l2)
        p :: shaped rn (1 + k ': sh)
        p = sscanDer f df rf x0 as
        width = slength p - 1
        (l4, pShared) = recordSharingPrimal p l3
    in dDnotShared l4 (pShared !$ (fromIntegral width :$: ZSH))
                      (FoldS pShared as df rf x0' as')
  sfoldZip :: forall rn sh. (GoodScalar rn, Sh.Shape sh)
         => (forall f. ADReadyS f
             => f rn sh -> HVector (RankedOf f) -> f rn sh)
         -> VoidHVector
         -> ADVal shaped rn sh
         -> HVector (ADVal ranked)
         -> ADVal shaped rn sh
  sfoldZip f domsOD (D l1 x0 x0') asD =
    let (ll2, asUnshared, as') = unADValHVector asD
        domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, HVector (RankedOf f))
        domsToPair doms = (sfromD $ doms V.! 0, V.tail doms)
        g :: HVector (ADVal ranked) -> ADVal shaped rn sh
        g doms = uncurry f (domsToPair doms)
        df :: shaped rn sh -> HVector ranked -> shaped rn sh -> HVector ranked
           -> shaped rn sh
        df cx ca x a =
          fst $ cfwdOnHVector (V.cons (DynamicShaped x) a)
                              g
                              (V.cons (DynamicShaped cx) ca)
        rf :: shaped rn sh -> shaped rn sh -> HVector ranked
           -> HVectorOf ranked
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.cons (DynamicShaped x) a)
        width = case V.unsnoc asUnshared of
          Nothing -> error "sfoldZip: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "sfoldZip: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD)
                                   asD) $
        let (l3, as) =
              drecordSharingPrimal @ranked
                (replicate1VoidHVector (Proxy @k) domsOD)
                (dmkHVector asUnshared) (flattenADShare $ l1 : V.toList ll2)
            p :: shaped rn (1 + k ': sh)
            p = sscanZip f domsOD x0 as
            (l4, pShared) = recordSharingPrimal p l3
        in dDnotShared l4 (pShared !$ (fromIntegral width :$: ZSH))
                          (FoldZipSC domsOD pShared as df rf x0' as')
      _ -> error "sfoldZip: impossible someNatVal"
  sfoldZipDer :: forall rn sh. (GoodScalar rn, Sh.Shape sh)
            => (forall f. ADReadyS f
                => f rn sh -> HVector (RankedOf f) -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> HVector (RankedOf f) -> f rn sh
                -> HVector (RankedOf f)
                -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> f rn sh -> HVector (RankedOf f)
                -> HVectorOf (RankedOf f))
            -> VoidHVector
            -> ADVal shaped rn sh
            -> HVector (ADVal ranked)
            -> ADVal shaped rn sh
  sfoldZipDer f df rf domsOD (D l1 x0 x0') asD =
    let (ll2, asUnshared, as') = unADValHVector asD
        width = case V.unsnoc asUnshared of
          Nothing -> error "sfoldZipDer: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "sfoldZipDer: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD)
                                   asD) $
        let (l3, as) =
              drecordSharingPrimal @ranked
                (replicate1VoidHVector (Proxy @k) domsOD)
                (dmkHVector asUnshared) (flattenADShare $ l1 : V.toList ll2)
            p :: shaped rn (1 + k ': sh)
            p = sscanZip f domsOD x0 as
            (l4, pShared) = recordSharingPrimal p l3
        in dDnotShared l4 (pShared !$ (fromIntegral width :$: ZSH))
                          (FoldZipS domsOD pShared as df rf x0' as')
      _ -> error "sfoldZipDer: impossible someNatVal"
  sscan :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> ADVal shaped rn sh
        -> ADVal shaped rm (k ': shm)
        -> ADVal shaped rn (1 + k ': sh)
  sscan f (D l1 x0 x0') (D l2 asUnshared as') =
    let domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: HVector (ADVal ranked) -> ADVal shaped rn sh
        g doms = uncurry f (domsToPair doms)
        df :: shaped rn sh -> shaped rm shm -> shaped rn sh -> shaped rm shm
           -> shaped rn sh
        df cx ca x a =
          fst $ cfwdOnHVector (V.fromList [DynamicShaped x, DynamicShaped a])
                              g
                              (V.fromList [DynamicShaped cx, DynamicShaped ca])
        rf :: shaped rn sh -> shaped rn sh -> shaped rm shm
           -> HVectorOf ranked
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.fromList [DynamicShaped x, DynamicShaped a])
        (l3, as) = recordSharingPrimal asUnshared (l1 `mergeADShare` l2)
        p :: shaped rn (1 + k ': sh)
        p = sscan f x0 as
        width = slength p - 1
        (l4, pShared) = recordSharingPrimal p l3
        scanAsFold =
          let h :: KnownNat k2
                => shaped rn (1 + k2 ': sh) -> shaped rm (k2 ': shm)
                -> DeltaS shaped rm (k2 ': shm)
                -> DeltaS shaped rn sh
              h pPrefix asPrefix as'Prefix =
                FoldSC pPrefix asPrefix df rf x0' as'Prefix
              initsViaSlice :: Int -> DeltaS shaped rn sh
              initsViaSlice k2 = case someNatVal $ toInteger k2 of
                Just (SomeNat @k1 _) ->
                  gcastWith (unsafeCoerce Refl :: Compare k1 k :~: LT) $
                  h @k1 (sslice @_ @_ @_ @_ @(k - k1)
                                (Proxy @0) (Proxy @(1 + k1)) pShared)
                        (sslice @_ @_ @_ @_ @(k - k1)
                                (Proxy @0) (Proxy @k1) as)
                        (SliceS @_ @0 @k1 as')
                Nothing -> error "sscan: impossible someNatVal error"
          in FromListS
             $ x0' : map initsViaSlice [1 .. width]
    in dDnotShared l4 pShared scanAsFold
  sscanDer :: forall rn rm sh shm k.
              ( GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm
              , KnownNat k )
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f))
           -> ADVal shaped rn sh
           -> ADVal shaped rm (k ': shm)
           -> ADVal shaped rn (1 + k ': sh)
  sscanDer f df rf (D l1 x0 x0') (D l2 asUnshared as') =
    let (l3, as) = recordSharingPrimal asUnshared (l1 `mergeADShare` l2)
        p :: shaped rn (1 + k ': sh)
        p = sscanDer f df rf x0 as
        (l4, pShared) = recordSharingPrimal p l3
    in dDnotShared l4 pShared
                      (ScanS pShared as df rf x0' as')
  sscanZip :: forall rn sh k. (GoodScalar rn, Sh.Shape sh, KnownNat k)
         => (forall f. ADReadyS f
             => f rn sh -> HVector (RankedOf f) -> f rn sh)
         -> VoidHVector
         -> ADVal shaped rn sh
         -> HVector (ADVal ranked)
         -> ADVal shaped rn (1 + k ': sh)
  sscanZip f domsOD (D l1 x0 x0') asD =
    assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD) asD) $
    let (ll2, asUnshared, as') = unADValHVector asD
        domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, HVector (RankedOf f))
        domsToPair doms = (sfromD $ doms V.! 0, V.tail doms)
        g :: HVector (ADVal ranked) -> ADVal shaped rn sh
        g doms = uncurry f (domsToPair doms)
        df :: shaped rn sh -> HVector ranked -> shaped rn sh -> HVector ranked
           -> shaped rn sh
        df cx ca x a =
          fst $ cfwdOnHVector (V.cons (DynamicShaped x) a)
                              g
                              (V.cons (DynamicShaped cx) ca)
        rf :: shaped rn sh -> shaped rn sh -> HVector ranked
           -> HVectorOf ranked
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.cons (DynamicShaped x) a)
        (l3, as) =
          drecordSharingPrimal @ranked (replicate1VoidHVector (Proxy @k) domsOD)
                               (dmkHVector asUnshared)
                               (flattenADShare $ l1 : V.toList ll2)
        p :: shaped rn (1 + k ': sh)
        p = sscanZip f domsOD x0 as
        (l4, pShared) = recordSharingPrimal p l3
        width = slength p - 1
        scanAsFold =
          let h :: KnownNat k2
                => shaped rn (1 + k2 ': sh) -> HVector ranked
                -> HVector (DeltaR ranked)
                -> DeltaS shaped rn sh
              h pPrefix asPrefix as'Prefix =
                FoldZipSC domsOD pPrefix asPrefix df rf x0' as'Prefix
              initsViaSlice :: Int -> DeltaS shaped rn sh
              initsViaSlice k = case someNatVal $ toInteger k of
                Just (SomeNat @k1 _) ->
                  gcastWith (unsafeCoerce Refl :: Compare k1 k :~: LT) $
                  h @k1 (sslice @_ @_ @_ @_ @(k - k1)
                                (Proxy @0) (Proxy @(1 + k1)) pShared)
                        (mapHVectorShaped11 @k @k1
                           (sslice @_ @_ @_ @_ @(k - k1)
                                   (Proxy @0) (Proxy @k1)) as)
                        (mapHVectorDeltaS11 @k @k1
                           (SliceS @_ @0 @k1 @(k - k1)) as')
                Nothing -> error "sscanZip: impossible someNatVal error"
          in FromListS
             $ x0' : map initsViaSlice [1 .. width]
    in dDnotShared l4 pShared scanAsFold
  sscanZipDer :: forall rn sh k. (GoodScalar rn, Sh.Shape sh, KnownNat k)
            => (forall f. ADReadyS f
                => f rn sh -> HVector (RankedOf f) -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> HVector (RankedOf f) -> f rn sh
                -> HVector (RankedOf f)
                -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> f rn sh -> HVector (RankedOf f)
                -> HVectorOf (RankedOf f))
            -> VoidHVector
            -> ADVal shaped rn sh
            -> HVector (ADVal ranked)
            -> ADVal shaped rn (1 + k ': sh)
  sscanZipDer f df rf domsOD (D l1 x0 x0') asD =
    assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD) asD) $
    let (ll2, asUnshared, as') = unADValHVector asD
        (l3, as) =
          drecordSharingPrimal @ranked (replicate1VoidHVector (Proxy @k) domsOD)
                               (dmkHVector asUnshared)
                               (flattenADShare $ l1 : V.toList ll2)
        p :: shaped rn (1 + k ': sh)
        p = sscanZipDer f df rf domsOD x0 as
        (l4, pShared) = recordSharingPrimal p l3
    in dDnotShared l4 pShared
                      (ScanZipS domsOD pShared as df rf x0' as')
  rmapAccumR
    :: forall rn n. (GoodScalar rn, KnownNat n)
    => VoidHVector
    -> (forall f. ADReady f
        => f rn n -> HVector f -> HVectorOf f)
    -> VoidHVector
    -> ADVal ranked rn n
    -> HVector (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  rmapAccumR domB f domsOD (D l1 x0 x0') asD =
    let (ll2, asUnshared, as') = unADValHVector asD
        width = case V.unsnoc asUnshared of
          Nothing -> error "rmapAccumR: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rmapAccumR: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD)
                                   asD) $
        let shn = rshape x0
            odShn = voidFromSh @rn shn
            domsToPair :: forall f. ADReady f
                       => HVector f -> (f rn n, HVector f)
            domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
            g :: HVector (ADVal ranked)
              -> ADVal (HVectorPseudoTensor ranked) Float '()
            g doms = let (ll, as2, as2') =
                           unADValHVector $ uncurry f (domsToPair doms)
                     in dDnotShared (flattenADShare $ V.toList ll)
                                    (HVectorPseudoTensor $ dmkHVector as2)
                                    (HVectorPseudoTensor $ HToH as2')
            df :: ranked rn n -> HVector ranked
               -> ranked rn n -> HVector ranked
               -> HVectorOf ranked
            df cx ca x a =
              unHVectorPseudoTensor
              $ fst $ cfwdOnHVector (V.cons (DynamicRanked x) a)
                                    g
                                    (V.cons (DynamicRanked cx) ca)
            rf :: ranked rn n -> HVector ranked
               -> ranked rn n -> HVector ranked
               -> HVectorOf ranked
            rf dx dt x a =
              fst $ crevOnHVector (Just $ HVectorPseudoTensor
                                   $ dmkHVector $ V.cons (DynamicRanked dx) dt)
                                  g
                                  (V.cons (DynamicRanked x) a)
            (l3, as) =
              drecordSharingPrimal @ranked
                                   (replicate1VoidHVector (Proxy @k) domsOD)
                                   (dmkHVector asUnshared)
                                   (flattenADShare $ l1 : V.toList ll2)
            domsG = V.cons odShn domB
            f3 :: forall f. ADReady f => f rn n -> HVector f -> HVectorOf f
            f3 x a = dletHVectorInHVector @f domsG (f x a) $ \res ->
                       let x2 = res V.! 0
                           a2 = V.tail res
                       in dmkHVector $ V.cons x2 $ V.cons (DynamicRanked x) a2
            p :: HVectorOf ranked
            p = rmapAccumR domsG f3 domsOD x0 as
            odShnK = voidFromSh @rn (width :$ shn)
            domsF3 = V.cons odShn $ V.cons odShnK
                     $ replicate1VoidHVector (Proxy @k) domB
            (l4, pShared) = drecordSharingPrimal @ranked domsF3 p l3
            xFin = pShared V.! 0
            q = case pShared V.!? 1 of
              Just q2 -> rfromD q2
              Nothing -> rfromList []
            primal = V.cons xFin $ V.drop 2 pShared
            dual = wrapDeltaH $ MapAccumRRC domB q as df rf domsOD x0' as'
            selectDual i d = case d of
              DynamicRanked t -> DynamicRanked $ dDnotShared l4 t (HToR dual i)
              DynamicShaped t -> DynamicShaped $ dDnotShared l4 t (HToS dual i)
              DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
              DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
        in V.imap selectDual primal
      _ -> error "rmapAccumR: impossible someNatVal"
  rmapAccumRDer
    :: forall rn n. (GoodScalar rn, KnownNat n)
    => VoidHVector
    -> (forall f. ADReady f
        => f rn n
        -> HVector f
        -> HVectorOf f)
    -> (forall f. ADReady f
        => f rn n
        -> HVector f
        -> f rn n
        -> HVector f
        -> HVectorOf f)
    -> (forall f. ADReady f
        => f rn n
        -> HVector f
        -> f rn n
        -> HVector f
        -> HVectorOf f)
    -> VoidHVector
    -> ADVal ranked rn n
    -> HVector (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  rmapAccumRDer domB f df rf domsOD (D l1 x0 x0') asD =
    let (ll2, asUnshared, as') = unADValHVector asD
        width = case V.unsnoc asUnshared of
          Nothing -> error "rmapAccumRDer: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rmapAccumRDer: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (Proxy @k) domsOD)
                                   asD) $
        let (l3, as) =
              drecordSharingPrimal @ranked
                                   (replicate1VoidHVector (Proxy @k) domsOD)
                                   (dmkHVector asUnshared)
                                   (flattenADShare $ l1 : V.toList ll2)
            shn = rshape x0
            odShn = voidFromSh @rn shn
            domsG = V.cons odShn domB
            f3 :: forall f. ADReady f => f rn n -> HVector f -> HVectorOf f
            f3 x a = dletHVectorInHVector @f domsG (f x a) $ \res ->
                       let x2 = res V.! 0
                           a2 = V.tail res
                       in dmkHVector $ V.cons x2 $ V.cons (DynamicRanked x) a2
            p :: HVectorOf ranked
            p = rmapAccumR domsG f3 domsOD x0 as
            odShnK = voidFromSh @rn (width :$ shn)
            domsF3 = V.cons odShn $ V.cons odShnK
                     $ replicate1VoidHVector (Proxy @k) domB
            (l4, pShared) = drecordSharingPrimal @ranked domsF3 p l3
            xFin = pShared V.! 0
            q = rfromD $ pShared V.! 1
            primal = V.cons xFin $ V.drop 2 pShared
            dual = wrapDeltaH $ MapAccumRR domB q as df rf domsOD x0' as'
            selectDual i d = case d of
              DynamicRanked t -> DynamicRanked $ dDnotShared l4 t (HToR dual i)
              DynamicShaped t -> DynamicShaped $ dDnotShared l4 t (HToS dual i)
              DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
              DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
        in V.imap selectDual primal
      _ -> error "rmapAccumRDer: impossible someNatVal"
  smapAccumR
    :: forall k rn sh. (GoodScalar rn, Sh.Shape sh, KnownNat k)
    => Proxy k
    -> VoidHVector
    -> (forall f. ADReadyS f
        => f rn sh -> HVector (RankedOf f) -> HVectorOf (RankedOf f))
    -> VoidHVector
    -> ADVal shaped rn sh
    -> HVector (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  smapAccumR proxy_k domB f domsOD (D l1 x0 x0') asD =
    assert (voidHVectorMatches (replicate1VoidHVector proxy_k domsOD) asD) $
    let (ll2, asUnshared, as') = unADValHVector asD
        odShn = voidFromShS @rn @sh
        domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, HVector (RankedOf f))
        domsToPair doms = (sfromD $ doms V.! 0, V.tail doms)
        g :: HVector (ADVal ranked)
          -> ADVal (HVectorPseudoTensor ranked) Float '()
        g doms = let (ll, as2, as2') =
                       unADValHVector $ uncurry f (domsToPair doms)
                 in dDnotShared (flattenADShare $ V.toList ll)
                                (HVectorPseudoTensor $ dmkHVector as2)
                                (HVectorPseudoTensor $ HToH as2')
        df :: shaped rn sh -> HVector ranked -> shaped rn sh -> HVector ranked
           -> HVectorOf ranked
        df cx ca x a =
          unHVectorPseudoTensor
          $ fst $ cfwdOnHVector (V.cons (DynamicShaped x) a)
                                g
                                (V.cons (DynamicShaped cx) ca)
        rf :: shaped rn sh -> HVector ranked -> shaped rn sh -> HVector ranked
           -> HVectorOf ranked
        rf dx dt x a =
          fst $ crevOnHVector (Just $ HVectorPseudoTensor
                               $ dmkHVector $ V.cons (DynamicShaped dx) dt)
                              g
                              (V.cons (DynamicShaped x) a)
        (l3, as) =
          drecordSharingPrimal @ranked (replicate1VoidHVector proxy_k domsOD)
                               (dmkHVector asUnshared)
                               (flattenADShare $ l1 : V.toList ll2)
        domsG = V.cons odShn domB
        f3 :: forall f. ADReadyS f
           => f rn sh -> HVector (RankedOf f) -> HVectorOf (RankedOf f)
        f3 x a = dletHVectorInHVector @_ @f domsG (f x a) $ \res ->
                   let x2 = res V.! 0
                       a2 = V.tail res
                   in dmkHVector $ V.cons x2 $ V.cons (DynamicShaped x) a2
        p :: HVectorOf ranked
        p = smapAccumR proxy_k domsG f3 domsOD x0 as
        odShnK = voidFromShS @rn @(k ': sh)
        domsF3 = V.cons odShn $ V.cons odShnK
                 $ replicate1VoidHVector proxy_k domB
        (l4, pShared) = drecordSharingPrimal @ranked domsF3 p l3
        xFin = pShared V.! 0
        q = case pShared V.!? 1 of
          Just q2 -> sfromD q2
          Nothing -> sfromList []
        primal = V.cons xFin $ V.drop 2 pShared
        dual = wrapDeltaH $ MapAccumRSC @k domB q as df rf domsOD x0' as'
        selectDual i d = case d of
          DynamicRanked t -> DynamicRanked $ dDnotShared l4 t (HToR dual i)
          DynamicShaped t -> DynamicShaped $ dDnotShared l4 t (HToS dual i)
          DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
          DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
    in V.imap selectDual primal
  smapAccumRDer
    :: forall k rn sh. (GoodScalar rn, Sh.Shape sh, KnownNat k)
    => Proxy k
    -> VoidHVector
    -> (forall f. ADReadyS f
        => f rn sh
        -> HVector (RankedOf f)
        -> HVectorOf (RankedOf f))
    -> (forall f. ADReadyS f
        => f rn sh
        -> HVector (RankedOf f)
        -> f rn sh
        -> HVector (RankedOf f)
        -> HVectorOf (RankedOf f))
    -> (forall f. ADReadyS f
        => f rn sh
        -> HVector (RankedOf f)
        -> f rn sh
        -> HVector (RankedOf f)
        -> HVectorOf (RankedOf f))
    -> VoidHVector
    -> ADVal shaped rn sh
    -> HVector (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  smapAccumRDer proxy_k domB f df rf domsOD (D l1 x0 x0') asD =
    assert (voidHVectorMatches (replicate1VoidHVector proxy_k domsOD) asD) $
    let (ll2, asUnshared, as') = unADValHVector asD
        (l3, as) =
          drecordSharingPrimal @ranked (replicate1VoidHVector proxy_k domsOD)
                               (dmkHVector asUnshared)
                               (flattenADShare $ l1 : V.toList ll2)
        odShn = voidFromShS @rn @sh
        domsG = V.cons odShn domB
        f3 :: forall f. ADReadyS f
           => f rn sh -> HVector (RankedOf f) -> HVectorOf (RankedOf f)
        f3 x a = dletHVectorInHVector @_ @f domsG (f x a) $ \res ->
                   let x2 = res V.! 0
                       a2 = V.tail res
                   in dmkHVector $ V.cons x2 $ V.cons (DynamicShaped x) a2
        p :: HVectorOf ranked
        p = smapAccumR proxy_k domsG f3 domsOD x0 as
        odShnK = voidFromShS @rn @(k ': sh)
        domsF3 = V.cons odShn $ V.cons odShnK
                 $ replicate1VoidHVector proxy_k domB
        (l4, pShared) = drecordSharingPrimal @ranked domsF3 p l3
        xFin = pShared V.! 0
        q = sfromD $ pShared V.! 1
        primal = V.cons xFin $ V.drop 2 pShared
        dual = wrapDeltaH $ MapAccumRS @k domB q as df rf domsOD x0' as'
        selectDual i d = case d of
          DynamicRanked t -> DynamicRanked $ dDnotShared l4 t (HToR dual i)
          DynamicShaped t -> DynamicShaped $ dDnotShared l4 t (HToS dual i)
          DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
          DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
    in V.imap selectDual primal

dDHVector :: (RankedTensor f, ShapedTensor (ShapedOf f))
          => ADShare -> HVector f -> HVector (Dual f)
          -> HVector (ADVal f)
dDHVector l = V.zipWith (aDValDynamicTensor l)

aDValHVector :: (RankedTensor f, ShapedTensor (ShapedOf f))
             => Data.Vector.Vector ADShare -> HVector f -> HVector (Dual f)
             -> HVector (ADVal f)
aDValHVector = V.zipWith3 aDValDynamicTensor

aDValDynamicTensor :: (RankedTensor f, ShapedTensor (ShapedOf f))
                   => ADShare -> DynamicTensor f -> DynamicTensor (Dual f)
                   -> DynamicTensor (ADVal f)
aDValDynamicTensor l (DynamicRanked @r1 @n1 t) (DynamicRanked @r2 @n2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameNat (Proxy @n1) (Proxy @n2) =
    DynamicRanked (dDnotShared l t t')
aDValDynamicTensor l (DynamicShaped @r1 @sh1 t) (DynamicShaped @r2 @sh2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShaped (dDnotShared l t t')
aDValDynamicTensor l (DynamicRankedDummy @r1 @sh1 _ _)
                     (DynamicRanked @r2 @n2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- matchingRank @sh1 @n2 =
    withListShape (Sh.shapeT @sh1) $ \(sh4 :: ShapeInt n4) ->
      gcastWith (unsafeCoerce Refl :: n4 :~: Sh.Rank sh1) $
      DynamicRanked (dDnotShared l (rzero sh4) t')
aDValDynamicTensor l (DynamicShapedDummy @r1 @sh1 _ _)
                     (DynamicShaped @r2 @sh2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShaped (dDnotShared l 0 t')
aDValDynamicTensor _ _ _ = error "aDValDynamicTensor: wrong arguments"

-- Float and '() are placeholders here; they are reduced away.
hVectorADValToADVal
  :: forall ranked. HVectorTensor ranked (ShapedOf ranked)
  => HVector (ADVal ranked) -> ADVal (HVectorPseudoTensor ranked) Float '()
hVectorADValToADVal hv =
  let (ll, as, as') = unADValHVector hv
  in dDnotShared (flattenADShare $ V.toList ll)
                 (HVectorPseudoTensor
                  $ dmkHVector @ranked @(ShapedOf ranked) as)
                 (HVectorPseudoTensor
                  $ HToH as')

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


-- * HVectorTensor instance for concrete arrays

instance HVectorTensor (Flip OR.Array) (Flip OS.Array) where
  dshape = voidFromHVector
  dmkHVector = id
  dunHVector _ = id
  dletHVectorInHVector _ = (&)
  rletInHVector = (&)
  sletInHVector = (&)
  drecordSharingPrimal _ d l = (l, d)
  dregister _ d l = (l, d)
  dbuild1 k f = ravelHVector $ map (f . fromIntegral) [0 .. k - 1]
  dzipWith1 f u = case V.unsnoc u of
    Nothing -> error "dzipWith1: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "dzipWith1: wrong rank of argument"
      width : _ -> dbuild1 @(Flip OR.Array) width (\i -> f (index1HVector u i))
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (Flip OR.Array)
       -> HVector (Flip OR.Array)
  rrev f _parameters0 parameters =
    fst $ crevOnHVector Nothing (f @(ADVal (Flip OR.Array))) parameters
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => HVector f -> f r n)
         -> VoidHVector
         -> HVector (Flip OR.Array)
         -> Flip OR.Array r n
         -> HVector (Flip OR.Array)
  rrevDt f _parameters0 parameters dt =
    fst $ crevOnHVector (Just dt) (f @(ADVal (Flip OR.Array))) parameters
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (Flip OR.Array)
       -> HVector (Flip OR.Array)
       -> Flip OR.Array r n
  rfwd f _parameters0 parameters ds =
    fst $ cfwdOnHVector parameters (f @(ADVal (Flip OR.Array))) ds
  srev f _parameters0 parameters =
    fst $ crevOnHVector Nothing (f @(ADVal (Flip OS.Array))) parameters
  srevDt f _parameters0 parameters dt =
    fst $ crevOnHVector (Just dt) (f @(ADVal (Flip OS.Array))) parameters
  sfwd f _parameters0 parameters ds =
    fst $ cfwdOnHVector parameters (f @(ADVal (Flip OS.Array))) ds
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
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f)
           -> Flip OR.Array rn n
           -> Flip OR.Array rm (1 + m)
           -> Flip OR.Array rn n
  rfoldDer f _df _rf x0 as = rfold f x0 as
  rfoldZip f _od x0 as = foldl' f x0 (unravelHVector as)
  rfoldZipDer f _df _rf od x0 as = rfoldZip f od x0 as
  rscan f x0 as = rfromList $ scanl' f x0 (runravelToList as)
  rscanDer f _df _rf x0 as = rscan f x0 as
  rscanZip f _od x0 as = rfromList $ scanl' f x0 (unravelHVector as)
  rscanZipDer f _df _rf od x0 as = rscanZip f od x0 as
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
               => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f))
           -> Flip OS.Array rn sh
           -> Flip OS.Array rm (k ': shm)
           -> Flip OS.Array rn sh
  sfoldDer f _df _dr x0 as = sfold f x0 as
  sfoldZip f _od x0 as = foldl' f x0 (unravelHVector as)
  sfoldZipDer f _df _rf od x0 as = sfoldZip f od x0 as
  sscan f x0 as = sfromList $ scanl' f x0 (sunravelToList as)
  sscanDer f _df _rf x0 as = sscan f x0 as
  sscanZip f _od x0 as = sfromList $ scanl' f x0 (unravelHVector as)
  sscanZipDer f _df _rf od x0 as = sscanZip f od x0 as
  rmapAccumR
    :: forall rn n. (GoodScalar rn, KnownNat n)
    => VoidHVector
    -> (forall f. ADReady f
        => f rn n -> HVector f -> HVectorOf f)
    -> VoidHVector
    -> Flip OR.Array rn n
    -> HVector (Flip OR.Array)
    -> HVector (Flip OR.Array)
  rmapAccumR domB f _domsOD x0 as =
    let width = case V.unsnoc as of
          Nothing -> error "rmapAccumR: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rmapAccumRDer: wrong rank of argument"
            w : _shm -> w
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) -> case width of
        0 ->
          V.cons (DynamicRanked x0)
                 (replicate1HVector (Proxy @k) (V.map dynamicFromVoid domB))
        _ ->
          let domsToPair :: forall f. ADReady f
                         => HVector f -> (f rn n, HVector f)
              domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
              g :: Flip OR.Array rn n -> HVector (Flip OR.Array)
                -> (Flip OR.Array rn n, HVector (Flip OR.Array))
              g x a = domsToPair $ f x a
              (xout, lout) = mapAccumR g x0 (unravelHVector as)
          in V.cons (DynamicRanked xout) $ ravelHVector lout
      _ -> error "rmapAccumR: impossible someNatVal"
  rmapAccumRDer domB f _df _rf domsOD x0 as =
    rmapAccumR domB f domsOD x0 as
  smapAccumR
    :: forall k rn sh. (GoodScalar rn, Sh.Shape sh, KnownNat k)
    => Proxy k
    -> VoidHVector
    -> (forall f. ADReadyS f
        => f rn sh -> HVector (RankedOf f) -> HVectorOf (RankedOf f))
    -> VoidHVector
    -> Flip OS.Array rn sh
    -> HVector (Flip OR.Array)
    -> HVector (Flip OR.Array)
  smapAccumR proxy_k domB f _domsOD x0 as =
    case sameNat proxy_k (Proxy @0) of
      Just Refl ->
        V.cons (DynamicShaped x0)
               (replicate1HVector proxy_k (V.map dynamicFromVoid domB))
      _ ->
        let domsToPair :: forall f. ADReadyS f
                       => HVector (RankedOf f)
                       -> (f rn sh, HVector (RankedOf f))
            domsToPair doms = (sfromD $ doms V.! 0, V.tail doms)
            g :: Flip OS.Array rn sh -> HVector (Flip OR.Array)
              -> (Flip OS.Array rn sh, HVector (Flip OR.Array))
            g x a = domsToPair $ f x a
            (xout, lout) = mapAccumR g x0 (unravelHVector as)
        in V.cons (DynamicShaped xout) $ ravelHVector lout
  smapAccumRDer proxy_k domB f _df _rf domsOD x0 as =
    smapAccumR proxy_k domB f domsOD x0 as

instance (GoodScalar r, KnownNat n)
         => AdaptableHVector (Flip OR.Array) (Flip OR.Array r n) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector (Flip OR.Array) (Flip OR.Array Double n) #-}
  type Value (Flip OR.Array r n) = Flip OR.Array r n
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit params = fromHVectorR @r @n params

instance ForgetShape (Flip OR.Array r n) where
  type NoShape (Flip OR.Array r n) = Flip OR.Array r n
  forgetShape = id

instance (GoodScalar r, Sh.Shape sh)
         => AdaptableHVector (Flip OR.Array) (Flip OS.Array r sh) where
  type Value (Flip OS.Array r sh) = Flip OS.Array r sh
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit params = fromHVectorS @r @sh @(Flip OS.Array) params

instance Sh.Shape sh
         => ForgetShape (Flip OS.Array r sh) where
  type NoShape (Flip OS.Array r sh) = Flip OR.Array r (Sh.Rank sh)  -- key case
  forgetShape = Flip . Data.Array.Convert.convert . runFlip

instance (Sh.Shape sh, Numeric r, Fractional r, Random r, Num (Vector r))
         => RandomHVector (Flip OS.Array r sh) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * realToFrac range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OS.fromVector $ createRandomVector (OS.sizeP (Proxy @sh)) g1
    in (Flip arr, g2)

instance AdaptableHVector (Flip OR.Array) (DynamicTensor (Flip OR.Array)) where
  type Value (DynamicTensor (Flip OR.Array)) = DynamicTensor (Flip OR.Array)
  toHVector = V.singleton
  fromHVector _aInit params = V.uncons params

{- TODO: requires IncoherentInstances no matter what pragma I stick in
-- TODO2: benchmark this used for any scalar via @V.map realToFrac@
-- A special case, because for @Double@ we have faster @randomVals@,
-- though the quality of randomness is worse (going through a single @Int@).
instance {-# OVERLAPS #-} {-# OVERLAPPING #-}
         KnownNat n
         => AdaptableHVector (OR.Array n Double) where
  randomVals range g =
    let -- Note that hmatrix produces numbers from the range open at the top,
        -- unlike package random.
        createRandomVector n seedInt =
          LA.scale (2 * range)
          $ LA.randomVector seedInt LA.Uniform n - LA.scalar 0.5
        (i, g2) = random g
        arr = OR.fromVector $ createRandomVector (OR.sizeP (Proxy @n)) i
    in (arr, g2)
-}

-- This specialization is not possible where gradientFromDeltaR is defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDeltaR
  :: KnownNat y
  => VoidHVector -> Flip OR.Array Double y -> Maybe (Flip OR.Array Double y)
  -> DeltaR (Flip OR.Array) Double y
  -> (AstBindingsD (Flip OR.Array), HVector (Flip OR.Array) ) #-}
{-# SPECIALIZE gradientFromDeltaS
  :: Sh.Shape y
  => VoidHVector -> Maybe (Flip OS.Array Double y)
  -> DeltaS (Flip OS.Array) Double y
  -> (AstBindingsD (Flip OR.Array), HVector (Flip OR.Array)) #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (Flip OR.Array) -> EvalState (Flip OR.Array) #-}
