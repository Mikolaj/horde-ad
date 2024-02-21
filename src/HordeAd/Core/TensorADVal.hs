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
import           Data.List (foldl', mapAccumL, mapAccumR, scanl')
import           Data.List.Index (imap)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.Delta
import           HordeAd.Core.DualNumber
import           HordeAd.Core.HVector
import           HordeAd.Core.HVectorOps
import           HordeAd.Core.IsPrimal
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
  rletHVectorIn _od asD f = f asD
{- TODO: Verify if this really helps sharing.
         BTW, it's broken when simplification in astLetHVectorIn is disabled,
         probably because asUnshared has variables bound in ll2
         and so l3 has such variables, but an individual l doesn't provied
         them all, so some variables are dangling when interpreting terms.
         We'd need to flatten ll2 and put instead of l.
    let !(!ll2, asUnshared, as') = unADValHVector asD
        !(!l3, as) =
          dsharePrimal od (dmkHVector asUnshared) emptyADShare
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
          dsharePrimal @(RankedOf shaped) @shaped
                               od (dmkHVector asUnshared) emptyADShare
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

instance ADReadyBoth ranked shaped
         => HVectorTensor (ADVal ranked) (ADVal shaped) where
  dshape = voidFromHVector
  dmkHVector = id
  dlambda _ = id
  dHApply (HFun f) ll = f ll
  dunHVector shs hv = assert (voidHVectorMatches shs hv
                              `blame` ( shapeVoidHVector shs
                                      , shapeVoidHVector (voidFromHVector hv)))
                             hv
  dletHVectorInHVector _od asD f = f asD
{- TODO: See similar code above.
    let !(!ll2, asUnshared, as') = unADValHVector asD
        !(!l3, as) =
          dsharePrimal od (dmkHVector asUnshared) emptyADShare
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
  dsharePrimal _ d l = (l, d)
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
  rfold f x0 as =
    let domsToPair :: forall f. ADReady f
                   => HVector f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: forall f. ADReady f => HVector (ADVal f) -> ADVal f rn n
        g doms = uncurry f (domsToPair doms)
        -- This computes the derivative of f again for each new @x@ and @a@
        -- (not even once for @as@, but for each @a@ separately).
        -- Note that this function is not a function on dual numbers.
        -- Consequently, any dual number operations inserted there by the user
        -- are flattened away (which is represented in AST by @PrimalSpan@).
        -- TODO: what if the dual numbers are nested?
        -- TODO: do the dual number ops in f affect what df is computed? add
        -- a comment explaining that and tests that exemplify that
        df :: forall f. ADReady f
           => f rn n -> f rm m -> f rn n -> f rm m -> f rn n
        df cx ca x a =
          fst $ cfwdOnHVector (V.fromList [DynamicRanked x, DynamicRanked a])
                              g
                              (V.fromList [DynamicRanked cx, DynamicRanked ca])
        rf :: forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.fromList [DynamicRanked x, DynamicRanked a])
    in rfoldDer f df rf x0 as
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
    let (l3, as) = rsharePrimal asUnshared (l1 `mergeADShare` l2)
        p :: ranked rn (1 + n)
        p = rscanDer f df rf x0 as
        width = rlength p - 1
        (l4, pShared) = rsharePrimal p l3
    in dDnotShared l4 (pShared ! (fromIntegral width :. ZI))
                      (FoldR pShared as df rf x0' as')
  rscan :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ADVal ranked rn n
        -> ADVal ranked rm (1 + m)
        -> ADVal ranked rn (1 + n)
  rscan f x0 as =
    let domsToPair :: forall f. ADReady f
                   => HVector f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: forall f. ADReady f => HVector (ADVal f) -> ADVal f rn n
        g doms = uncurry f (domsToPair doms)
        -- This computes the derivative of f again for each new @x@ and @a@
        -- (not even once for @as@, but for each @a@ separately).
        -- Note that this function is not a function on dual numbers.
        -- Consequently, any dual number operations inserted there by the user
        -- are flattened away (which is represented in AST by @PrimalSpan@).
        -- TODO: what if the dual numbers are nested?
        -- TODO: do the dual number ops in f affect what df is computed? add
        -- a comment explaining that and tests that exemplify that
        df :: forall f. ADReady f
           => f rn n -> f rm m -> f rn n -> f rm m -> f rn n
        df cx ca x a =
          fst $ cfwdOnHVector (V.fromList [DynamicRanked x, DynamicRanked a])
                              g
                              (V.fromList [DynamicRanked cx, DynamicRanked ca])
        rf :: forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.fromList [DynamicRanked x, DynamicRanked a])
    in rscanDer f df rf x0 as
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
    let (l3, as) = rsharePrimal asUnshared (l1 `mergeADShare` l2)
        p :: ranked rn (1 + n)
        p = rscanDer f df rf x0 as
        (l4, pShared) = rsharePrimal p l3
    in dDnotShared l4 pShared
                      (ScanR pShared as df rf x0' as')
  sfold :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> ADVal shaped rn sh
        -> ADVal shaped rm (k ': shm)
        -> ADVal shaped rn sh
  sfold f x0 as =
    let domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: forall f. ADReadyS f
          => HVector (ADVal (RankedOf f)) -> ADVal f rn sh
        g doms = uncurry f (domsToPair doms)
        df :: forall f. ADReadyS f
           => f rn sh -> f rm shm -> f rn sh -> f rm shm -> f rn sh
        df cx ca x a =
          fst $ cfwdOnHVector (V.fromList [DynamicShaped x, DynamicShaped a])
                              g
                              (V.fromList [DynamicShaped cx, DynamicShaped ca])
        rf :: forall f. ADReadyS f
           => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f)
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.fromList [DynamicShaped x, DynamicShaped a])
    in sfoldDer f df rf x0 as
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
    let (l3, as) = ssharePrimal asUnshared (l1 `mergeADShare` l2)
        p :: shaped rn (1 + k ': sh)
        p = sscanDer f df rf x0 as
        width = slength p - 1
        (l4, pShared) = ssharePrimal p l3
    in dDnotShared l4 (pShared !$ (fromIntegral width :$: ZSH))
                      (FoldS pShared as df rf x0' as')
  sscan :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> ADVal shaped rn sh
        -> ADVal shaped rm (k ': shm)
        -> ADVal shaped rn (1 + k ': sh)
  sscan f x0 as =
    let domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: forall f. ADReadyS f
          => HVector (ADVal (RankedOf f)) -> ADVal f rn sh
        g doms = uncurry f (domsToPair doms)
        df :: forall f. ADReadyS f
           => f rn sh -> f rm shm -> f rn sh -> f rm shm -> f rn sh
        df cx ca x a =
          fst $ cfwdOnHVector (V.fromList [DynamicShaped x, DynamicShaped a])
                              g
                              (V.fromList [DynamicShaped cx, DynamicShaped ca])
        rf :: forall f. ADReadyS f
           => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f)
        rf dt x a =
          fst $ crevOnHVector (Just dt)
                              g
                              (V.fromList [DynamicShaped x, DynamicShaped a])
    in sscanDer f df rf x0 as
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
    let (l3, as) = ssharePrimal asUnshared (l1 `mergeADShare` l2)
        p :: shaped rn (1 + k ': sh)
        p = sscanDer f df rf x0 as
        (l4, pShared) = ssharePrimal p l3
    in dDnotShared l4 pShared
                      (ScanS pShared as df rf x0' as')
  dmapAccumR
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVector (ADVal ranked)
    -> HVector (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  dmapAccumR k accShs bShs eShs f acc0 es =
    let accLen = V.length accShs
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair hv = (V.take accLen hv, V.drop accLen hv)
        g :: forall f. ADReady f
          => HVector (ADVal f)
          -> ADVal (HVectorPseudoTensor f) Float '()
        g hv = let (ll, as, as') = unADValHVector $ uncurry f (hvToPair hv)
               in dDnotShared (flattenADShare $ V.toList ll)
                              (HVectorPseudoTensor $ dmkHVector as)
                              (HVectorPseudoTensor $ HToH as')
        df :: forall f. ADReady f
           => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f
        df dacc de acc e =
          unHVectorPseudoTensor
          $ fst $ cfwdOnHVector (acc V.++ e) g (dacc V.++ de)
        rf :: forall f. ADReady f
           => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f
        rf dx db acc e =
          fst $ crevOnHVector
                  (Just $ HVectorPseudoTensor $ dmkHVector $ dx V.++ db)
                  g
                  (acc V.++ e)
    in dmapAccumRDer k accShs bShs eShs f df rf acc0 es
  dmapAccumRDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f)
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f)
    -> HVector (ADVal ranked)
    -> HVector (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  dmapAccumRDer k accShs bShs eShs f df rf acc0D esD =
    assert (voidHVectorMatches (replicate1VoidHVector k eShs) esD
            && voidHVectorMatches accShs acc0D) $
    let (ll2, acc0, acc0') = unADValHVector acc0D
        (ll3, esUnshared, es') = unADValHVector esD
        (l4, es) =
          dsharePrimal @ranked
                       (replicate1VoidHVector k eShs)
                       (dmkHVector esUnshared)
                       (flattenADShare $ V.toList ll2 ++ V.toList ll3)
        codomainShs = accShs V.++ bShs
        codomainShs2 = accShs V.++ eShs
        accLen = V.length accShs
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair hv = (V.take accLen hv, V.drop accLen hv)
        g :: forall f. ADReady f => HVector f -> HVector f -> HVectorOf f
        g acc e = dletHVectorInHVector @f codomainShs (f acc e) $ \res ->
          let (accRes, bRes) = hvToPair res
          in dmkHVector $ V.concat [accRes, acc, bRes]
        dg :: forall f. ADReady f
           => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f
        dg dacc de acc e =
          dletHVectorInHVector @f codomainShs (df dacc de acc e) $ \res ->
            let (accRes, bRes) = hvToPair res
            in dmkHVector $ V.concat [accRes, dacc, bRes]
        rg :: forall f. ADReady f
           => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f
        rg dx db acc e =
          let (dbacc, dbRes) = hvToPair db
          in dletHVectorInHVector @f codomainShs2 (rf dx dbRes acc e) $ \res ->
            let (dacc, de) = hvToPair res
            in dmkHVector $ V.concat [V.zipWith addDynamic dacc dbacc, de]
        pUnshared :: HVectorOf ranked
        pUnshared = dmapAccumRDer k accShs codomainShs eShs g dg rg acc0 es
        pShs = accShs V.++ replicate1VoidHVector k codomainShs
        (l5, pShared) = dsharePrimal @ranked pShs pUnshared l4
        accFin = V.take accLen pShared
        q = V.slice accLen accLen pShared
        bs = V.drop (2 * accLen) pShared
        !_A = assert (voidHVectorMatches (replicate1VoidHVector k bShs) bs) ()
        primal = accFin V.++ bs
        dual = wrapDeltaH $ MapAccumR k accShs bShs eShs q es df rf acc0' es'
        selectDual i d = case d of
          DynamicRanked t -> DynamicRanked $ dDnotShared l5 t (RFromH dual i)
          DynamicShaped t -> DynamicShaped $ dDnotShared l5 t (SFromH dual i)
          DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
          DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
    in V.imap selectDual primal
  dmapAccumL
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVector (ADVal ranked)
    -> HVector (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  dmapAccumL k accShs bShs eShs f acc0 es =
    let accLen = V.length accShs
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair hv = (V.take accLen hv, V.drop accLen hv)
        g :: forall f. ADReady f
          => HVector (ADVal f)
          -> ADVal (HVectorPseudoTensor f) Float '()
        g hv = let (ll, as, as') = unADValHVector $ uncurry f (hvToPair hv)
               in dDnotShared (flattenADShare $ V.toList ll)
                              (HVectorPseudoTensor $ dmkHVector as)
                              (HVectorPseudoTensor $ HToH as')
        df :: forall f. ADReady f
           => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f
        df dacc de acc e =
          unHVectorPseudoTensor
          $ fst $ cfwdOnHVector (acc V.++ e) g (dacc V.++ de)
        rf :: forall f. ADReady f
           => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f
        rf dx db acc e =
          fst $ crevOnHVector
                  (Just $ HVectorPseudoTensor $ dmkHVector $ dx V.++ db)
                  g
                  (acc V.++ e)
    in dmapAccumLDer k accShs bShs eShs f df rf acc0 es
  dmapAccumLDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f)
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f)
    -> HVector (ADVal ranked)
    -> HVector (ADVal ranked)
    -> HVectorOf (ADVal ranked)
  dmapAccumLDer k accShs bShs eShs f df rf acc0D esD =
    assert (voidHVectorMatches (replicate1VoidHVector k eShs) esD
            && voidHVectorMatches accShs acc0D
            `blame` ( shapeVoidHVector (replicate1VoidHVector k eShs)
                    , shapeVoidHVector (voidFromHVector esD)
                    , shapeVoidHVector accShs
                    , shapeVoidHVector (voidFromHVector acc0D) )) $
    let (ll2, acc0, acc0') = unADValHVector acc0D
        (ll3, esUnshared, es') = unADValHVector esD
        (l4, es) =
          dsharePrimal @ranked
                       (replicate1VoidHVector k eShs)
                       (dmkHVector esUnshared)
                       (flattenADShare $ V.toList ll2 ++ V.toList ll3)
        codomainShs = accShs V.++ bShs
        codomainShs2 = accShs V.++ eShs
        accLen = V.length accShs
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair hv = (V.take accLen hv, V.drop accLen hv)
        g :: forall f. ADReady f => HVector f -> HVector f -> HVectorOf f
        g acc e = dletHVectorInHVector @f codomainShs (f acc e) $ \res ->
          let (accRes, bRes) = hvToPair res
          in dmkHVector $ V.concat [accRes, acc, bRes]
        dg :: forall f. ADReady f
           => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f
        dg dacc de acc e =
          dletHVectorInHVector @f codomainShs (df dacc de acc e) $ \res ->
            let (accRes, bRes) = hvToPair res
            in dmkHVector $ V.concat [accRes, dacc, bRes]
        rg :: forall f. ADReady f
           => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f
        rg dx db acc e =
          let (dbacc, dbRes) = hvToPair db
          in dletHVectorInHVector @f codomainShs2 (rf dx dbRes acc e) $ \res ->
            let (dacc, de) = hvToPair res
            in dmkHVector $ V.concat [V.zipWith addDynamic dacc dbacc, de]
        pUnshared :: HVectorOf ranked
        pUnshared = dmapAccumLDer k accShs codomainShs eShs g dg rg acc0 es
        pShs = accShs V.++ replicate1VoidHVector k codomainShs
        (l5, pShared) = dsharePrimal @ranked pShs pUnshared l4
        accFin = V.take accLen pShared
        q = V.slice accLen accLen pShared
        bs = V.drop (2 * accLen) pShared
        !_A = assert (voidHVectorMatches (replicate1VoidHVector k bShs) bs) ()
        primal = accFin V.++ bs
        dual = wrapDeltaH $ MapAccumL k accShs bShs eShs q es df rf acc0' es'
        selectDual i d = case d of
          DynamicRanked t -> DynamicRanked $ dDnotShared l5 t (RFromH dual i)
          DynamicShaped t -> DynamicShaped $ dDnotShared l5 t (SFromH dual i)
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
  dlambda _ = id
  dHApply (HFun f) ll = f ll
  dunHVector shs hv = assert (voidHVectorMatches shs hv
                              `blame` ( shapeVoidHVector shs
                                      , shapeVoidHVector (voidFromHVector hv)))
                             hv
  dletHVectorInHVector _ = (&)
  dletHFunInHVector = (&)
  rletInHVector = (&)
  sletInHVector = (&)
  dsharePrimal _ d l = (l, d)
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
  rscan f x0 as = rfromList $ scanl' f x0 (runravelToList as)
  rscanDer f _df _rf x0 as = rscan f x0 as
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
  sscan f x0 as = sfromList $ scanl' f x0 (sunravelToList as)
  sscanDer f _df _rf x0 as = sscan f x0 as
  dmapAccumR
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVector (Flip OR.Array)
    -> HVector (Flip OR.Array)
    -> HVector (Flip OR.Array)
  dmapAccumR k accShs bShs _eShs f acc0 es = case sNatValue k :: Int of
    0 -> acc0 V.++ replicate1HVector k (V.map dynamicFromVoid bShs)
    _ -> let accLen = V.length accShs
             hvToPair :: forall f. HVector f -> (HVector f, HVector f)
             hvToPair hv = (V.take accLen hv, V.drop accLen hv)
             g :: HVector (Flip OR.Array) -> HVector (Flip OR.Array)
               -> (HVector (Flip OR.Array), HVector (Flip OR.Array))
             g x a = hvToPair $ f x a
             (xout, lout) = mapAccumR g acc0 (unravelHVector es)
         in xout V.++ ravelHVector lout
  dmapAccumRDer k accShs bShs eShs f _df _rf acc0 es =
    dmapAccumR k accShs bShs eShs f acc0 es
  dmapAccumL
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVector (Flip OR.Array)
    -> HVector (Flip OR.Array)
    -> HVector (Flip OR.Array)
  dmapAccumL k accShs bShs _eShs f acc0 es = case sNatValue k :: Int of
    0 -> acc0 V.++ replicate1HVector k (V.map dynamicFromVoid bShs)
    _ -> let accLen = V.length accShs
             hvToPair :: forall f. HVector f -> (HVector f, HVector f)
             hvToPair hv = (V.take accLen hv, V.drop accLen hv)
             g :: HVector (Flip OR.Array) -> HVector (Flip OR.Array)
               -> (HVector (Flip OR.Array), HVector (Flip OR.Array))
             g x a = hvToPair $ f x a
             (xout, lout) = mapAccumL g acc0 (unravelHVector es)
         in xout V.++ ravelHVector lout
  dmapAccumLDer k accShs bShs eShs f _df _rf acc0 es =
    dmapAccumL k accShs bShs eShs f acc0 es

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
