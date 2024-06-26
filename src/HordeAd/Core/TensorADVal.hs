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
  , aDValHVector
  , crevOnADInputs, crevOnHVector, cfwdOnADInputs, cfwdOnHVector
  ) where

import Prelude hiding (foldl')

import Control.Exception.Assert.Sugar
import Data.Array.Internal (valueOf)
import Data.Array.RankedS qualified as OR
import Data.Function ((&))
import Data.List (foldl')
import Data.List.Index (imap)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape qualified as X
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.IsPrimal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..), FlipS (..))
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * Non-symbolic reverse and forward derivative computation

crevOnADInputs
  :: ADReady ranked
  => Maybe (HVector ranked)
  -> (HVector (ADVal ranked)
      -> ADVal (HVectorPseudoTensor ranked) r y)
  -> HVector (ADVal ranked)
  -> (HVectorOf ranked, HVectorOf ranked)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D (HVectorPseudoTensor v)
          (HVectorPseudoTensor deltaTopLevel)) = f inputs in
  let rshapePrimal :: (GoodScalar r2, KnownNat n, ADReady g)
                   => ADVal g r2 n -> IShR n
      rshapePrimal (D p _) = rshape p
      parameters0 = V.map (voidFromDynamicF (shapeToList . rshapePrimal)) inputs
      !gradient = gradientFromDeltaH parameters0 v mdt deltaTopLevel
  in (dunlet (dmkHVector gradient), dunlet v)

crevOnHVector
  :: ADReady ranked
  => Maybe (HVector ranked)
  -> (HVector (ADVal ranked)
      -> ADVal (HVectorPseudoTensor ranked) r y)
  -> HVector ranked
  -> (HVectorOf ranked, HVectorOf ranked)
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
  -> (HVectorOf ranked, HVectorOf ranked)
{-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs inputs f ds =
  let !(D (HVectorPseudoTensor v)
          (HVectorPseudoTensor deltaTopLevel)) = f inputs in
  let derivative = derivativeFromDeltaH (V.length inputs) deltaTopLevel ds
  in (dunlet derivative, dunlet v)

cfwdOnHVector
  :: ADReady ranked
  => HVector ranked
  -> (HVector (ADVal ranked)
      -> ADVal (HVectorPseudoTensor ranked) r y)
  -> HVector ranked
  -> (HVectorOf ranked, HVectorOf ranked)
cfwdOnHVector parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in cfwdOnADInputs inputs f ds


-- * Ranked tensor instances

instance (KnownNat n, GoodScalar r, ADReady ranked)
         => AdaptableHVector (ADVal ranked)
                             (ADVal ranked r n) where
{- TODO: RULE left-hand side too complicated to desugar in GHC 9.6.4
    with -O0, but not -O1
  {-# SPECIALIZE instance
      (KnownNat n, ADReady ORArray)
      => AdaptableHVector (ADVal ORArray)
                          (ADVal ORArray Double n) #-}
  {-# SPECIALIZE instance
      (KnownNat n, ADReady (AstRanked PrimalSpan))
      => AdaptableHVector (ADVal (AstRanked PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit = fromHVectorR

instance (KnownNat n, GoodScalar r, ADReady ranked)
         => DualNumberValue (ADVal ranked r n) where
  type DValue (ADVal ranked r n) = ORArray r n  -- ! not Value(ranked)
  fromDValue t = constantADVal $ rconst $ runFlipR t

-- This is temporarily moved from Adaptor in order to specialize manually
instance AdaptableHVector ranked a
         => AdaptableHVector ranked [a] where
  {-# SPECIALIZE instance
      AdaptableHVector ORArray (OR.Array n Double)
      => AdaptableHVector ORArray
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
            Nothing -> error "fromHVector: Nothing"
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
  rlet (D u u') f =
    let !var2 = rshare u
    in f (dDnotShared var2 u')
      -- u' doesn't need to be shared, because deltas are shared separately

  rshape (D u _) = rshape u
  rminIndex (D u _) =
    let v = rminIndex u
    in dDnotShared v (dZeroOfShape v)
  rmaxIndex (D u _) =
    let v = rmaxIndex u
    in dDnotShared v (dZeroOfShape v)
  rfloor (D u _) =
    let v = rfloor u
    in dDnotShared v (dZeroOfShape v)

  -- TODO: speed up by using tindex0R and dIndex0 if the codomain has rank 0
  -- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
  -- dimension affected.
  rindex d i = indexPrimal d (rprimalPart <$> i)
  rsum (D u u') = dD (rsum u) (SumR u')
  rsum0 (D u u') = dD (rsum0 u) (Sum0R u')
  rdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = rshare ue in
    let !v = rshare ve
    in dD (rdot0 u v) (dAdd (Dot0R v u') (Dot0R u v'))
  rscatter sh (D u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD (rscatter sh u g) (ScatterR sh u' g)

  rfromVector = fromVector
  runravelToList (D u u') =
    let lu = runravelToList u
        f i ui = dD ui (IndexR u' (singletonIndex $ fromIntegral i))
    in imap f lu
  rreplicate k (D u u') = dD (rreplicate k u) (ReplicateR k u')
  rappend (D u u') (D v v') =
    dD (rappend u v) (AppendR u' v')
  rslice i n (D u u') = dD (rslice i n u) (SliceR i n u')
  rreverse (D u u') = dD (rreverse u) (ReverseR u')
  rtranspose perm (D u u') = dD (rtranspose perm u) (TransposeR perm u')
  rreshape :: forall n m r. (GoodScalar r, KnownNat n, KnownNat m)
           => IShR m -> ADVal ranked r n -> ADVal ranked r m
  rreshape sh t@(D u u') = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == rshape u -> t
    _ -> dD (rreshape sh u) (ReshapeR sh u')
  rbuild1 :: forall r n. (GoodScalar r, KnownNat n)
          => Int -> (IntOf (ADVal ranked) -> ADVal ranked r n)
          -> ADVal ranked r (1 + n)
  rbuild1 0 _ = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> rconst $ Nested.Internal.rfromListPrimLinear (0 :$: ZSR) []
                   -- the only case where we can guess sh
    _ ->  error "rbuild1: shape ambiguity, no arguments"
  rbuild1 k f = rfromList $ NonEmpty.fromList
                          $ map (f . fromIntegral) [0 .. k - 1]
                   -- element-wise (POPL) version
  rgather sh (D u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD (rgather sh u g) (GatherR sh u' g)
      -- note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on
  rcast (D u u') = dD (rcast u) (CastR u')
  rfromIntegral (D u _) =
    let v = rfromIntegral u
    in dDnotShared v (dZeroOfShape v)
  rconst t = constantADVal (rconst t)
  rletHVectorIn asD f = f asD
{- TODO: Try again once we have tests that show this sharing is needed:
    let !(!asUnshared, as') = unADValHVector asD
        !as = dunHVector $ dshare $ dmkHVector asUnshared
          -- TODO: could this be done with rshare? Would it be better?
        doms = aDValHVector as as'
    in f doms -}
  rletHFunIn = (&)
  rfromS :: forall r sh. (GoodScalar r, KnownShS sh)
         => ADVal (ShapedOf ranked) r sh -> ADVal ranked r (X.Rank sh)
  rfromS (D u u') = dDnotShared (rfromS u) (dRFromS u')
   where
    dRFromS (SFromR d) = d  -- no information lost, so no checks
    dRFromS d = RFromS d

  rconstant t = dDnotShared t (dZeroOfShape t)
  rprimalPart (D u _) = u
  rdualPart (D _ u') = u'
  rD = dD
  rScale = dScale


-- * Shaped tensor instances

instance ( ADReadyS shaped, KnownShS sh, GoodScalar r
         , ranked ~ RankedOf shaped )
         => AdaptableHVector (ADVal ranked)
                             (ADVal shaped r sh) where
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit = fromHVectorS

instance (ADReadyS shaped, KnownShS sh, GoodScalar r)
         => DualNumberValue (ADVal shaped r sh) where
  type DValue (ADVal shaped r sh) = OSArray r sh   -- ! not Value(shaped)
  fromDValue t = constantADVal $ sconst $ runFlipS t

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ADReadyS shaped => ShapedTensor (ADVal shaped) where
  slet (D u u') f =
    let !var2 = sshare u
    in f (dDnotShared var2 u')
      -- u' doesn't need to be shared, because deltas are shared separately

  sminIndex (D u _) =
    let v = sminIndex u
    in dDnotShared v (dZeroOfShape v)
  smaxIndex (D u _) =
    let v = smaxIndex u
    in dDnotShared v (dZeroOfShape v)
  sfloor (D u _) =
    let v = sfloor u
    in dDnotShared v (dZeroOfShape v)

  siota = constantADVal siota
  sindex d i = indexPrimalS d (rprimalPart <$> i)
  ssum (D u u') = dD (ssum u) (SumS u')
  ssum0 (D u u') = dD (ssum0 u) (Sum0S u')
  sdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = sshare ue in
    let !v = sshare ve
    in dD (sdot0 u v) (dAdd (Dot0S v u') (Dot0S u v'))
  sscatter (D u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD (sscatter u g) (ScatterS u' g)

  sfromVector = fromVectorS
  sunravelToList (D u u') =
    let lu = sunravelToList u
        f i ui = dD ui (IndexS u' (ShapedList.singletonIndex
                                   $ fromIntegral i))
    in imap f lu
  sreplicate (D u u') = dD (sreplicate u) (ReplicateS u')
  sappend (D u u') (D v v') =
    dD (sappend u v) (AppendS u' v')
  sslice (i_proxy :: Proxy i) n_proxy (D u u') =
    dD (sslice i_proxy n_proxy u) (SliceS @shaped @i u')
  sreverse (D u u') = dD (sreverse u) (ReverseS u')

  stranspose :: forall perm r sh.
                ( PermC perm, KnownShS sh
                , X.Rank perm <= X.Rank sh, GoodScalar r )
             => Permutation.Perm perm -> ADVal shaped r sh
             -> ADVal shaped r (Permutation.PermutePrefix perm sh)
  stranspose perm (D u u') | Dict <- Nested.Internal.Shape.shsKnownShS (Nested.Internal.Shape.shsPermutePrefix perm (knownShS @sh)) =
    dD (stranspose perm u) (TransposeS @shaped perm u')
  sreshape :: forall sh sh2 r.
              ( GoodScalar r, KnownShS sh, KnownShS sh2
              , Nested.Internal.Shape.Product sh ~ Nested.Internal.Shape.Product sh2)
           => ADVal shaped r sh -> ADVal shaped r sh2
  sreshape t@(D u u') = case sameShape @sh2 @sh of
    Just Refl -> t
    _ -> dD (sreshape u) (ReshapeS u')
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (ADVal shaped) -> ADVal shaped r sh)
          -> ADVal shaped r (n ': sh)
  sbuild1 f = case valueOf @n of
    0 -> sconst $ Nested.Internal.sfromListPrimLinear knownShS []
    k -> sfromList $ NonEmpty.fromList
                   $ map (f . fromIntegral)
                         [0 :: Int .. k - 1]
           -- element-wise (POPL) version
  sgather (D u u') f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD (sgather u g) (GatherS u' g)
  scast (D u u') = dD (scast u) (CastS u')
  sfromIntegral (D u _) =
    let v = sfromIntegral u
    in dDnotShared v (dZeroOfShape v)
  sconst t = constantADVal (sconst t)
  sletHVectorIn asD f = f asD
{- TODO: Try again once we have tests that show this sharing is needed:
    let !(!asUnshared, as') = unADValHVector asD
        !as = dunHVector $ dshare $ dmkHVector asUnshared
          -- TODO: could this be done with rshare? Would it be better?
        doms = aDValHVector as as'
    in f doms -}
  sletHFunIn = (&)
  sfromR :: forall r sh. (GoodScalar r, KnownShS sh, KnownNat (X.Rank sh))
         => ADVal (RankedOf shaped) r (X.Rank sh) -> ADVal shaped r sh
  sfromR (D u u') = dDnotShared (sfromR u) (dSFromR u')
   where
    dSFromR (RFromS @sh1 d) =
      case sameShape @sh1 @sh of
        Just Refl -> d
        _ -> error "sfromR: different shapes in SFromR(RFromS)"
    dSFromR d = SFromR d

  sconstant t = dDnotShared t (dZeroOfShape t)
  sprimalPart (D u _) = u
  sdualPart (D _ u') = u'
  sD = dD
  sScale = dScale


-- * HVectorTensor instance

instance (ADReady ranked, HVectorOf ranked ~ HVector ranked)
         => AdaptableHVector (ADVal ranked)
                             (ADVal (HVectorPseudoTensor ranked)
                                    Float '()) where
  toHVector = aDValToHVector
  fromHVector (D (HVectorPseudoTensor h) _) params =
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
{- TODO: Try again once we have tests that show this sharing is needed:
    let !(!asUnshared, as') = unADValHVector asD
        !as = dunHVector $ dshare $ dmkHVector asUnshared
          -- TODO: could this be done with rshare? Would it be better?
        doms = aDValHVector as as'
    in f doms -}
  dletHFunInHVector = (&)
  rletInHVector (D u u') f =
    let !var2 = rshare u
    in f (dDnotShared var2 u')
  sletInHVector (D u u') f =
    let !var2 = sshare u
    in f (dDnotShared var2 u')
  dbuild1 k f =
    ravelHVector $ map (f . fromIntegral) [0 .. sNatValue k - 1]
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (ADVal ranked)
       -> HVectorOf (ADVal ranked)
  rrev f _parameters0 parameters =
    -- This computes the derivative of g again for each new @parmeters@.
    let g :: HVector (ADVal (ADVal ranked))
          -> ADVal (HVectorPseudoTensor (ADVal ranked)) r y
        g !hv = let D a a' = f hv
                in dDnotShared (HVectorPseudoTensor $ dmkHVector
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
        g !hv = let (as, as') = unADValHVector $ unHFun h [hv]
                in dDnotShared (HVectorPseudoTensor $ dmkHVector as)
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
        g !hv = let (as, as') = unADValHVector $ unHFun h [hv]
                in dDnotShared (HVectorPseudoTensor $ dmkHVector as)
                               (HVectorPseudoTensor $ HToH as')
        df :: forall f. ADReady f => [HVector f] -> HVectorOf f
        df [!da, !a] = fst $ cfwdOnHVector a g da
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
    let (acc0, acc0') = unADValHVector acc0D
        (esUnshared, es') = unADValHVector esD
        es = dshare (dmkHVector esUnshared)
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
                                  (dmkHVector acc0) es
        pShared = dunHVector $ dshare pUnshared
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        accFin = V.take accLen pShared
        q = V.slice accLen accLen pShared
        bs = V.drop (2 * accLen) pShared
        !_A = assert (voidHVectorMatches (replicate1VoidHVector k bShs) bs) ()
        primal = accFin V.++ bs
        dual = wrapDeltaH $ MapAccumR k accShs bShs eShs q (dunHVector es) df rf acc0' es'
    in ahhToHVector primal dual
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
    let (acc0, acc0') = unADValHVector acc0D
        (esUnshared, es') = unADValHVector esD
        es = dshare (dmkHVector esUnshared)
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
                                  (dmkHVector acc0) es
        pShared = dunHVector $ dshare pUnshared
        accFin = V.take accLen pShared
        q = V.slice accLen accLen pShared
        bs = V.drop (2 * accLen) pShared
        !_A = assert (voidHVectorMatches (replicate1VoidHVector k bShs) bs) ()
        primal = accFin V.++ bs
        dual = wrapDeltaH $ MapAccumL k accShs bShs eShs q (dunHVector es) df rf acc0' es'
    in ahhToHVector primal dual

ahhToHVector
  :: forall ranked. RankedOf (ShapedOf ranked) ~ ranked
  => HVector ranked -> DeltaH ranked -> HVector (ADVal ranked)
ahhToHVector h h' =
  let selectDual :: Int -> DynamicTensor ranked -> DynamicTensor (ADVal ranked)
      selectDual i d = case d of
        DynamicRanked t -> DynamicRanked $ dDnotShared t (RFromH h' i)
        DynamicShaped t -> DynamicShaped $ dDnotShared t (SFromH h' i)
        DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
        DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
  in V.imap selectDual h
       -- TODO: write why these projections don't break any sharing

aDValToHVector
  :: (HVectorOf ranked ~ HVector ranked, RankedOf (ShapedOf ranked) ~ ranked)
  => ADVal (HVectorPseudoTensor ranked) r y -> HVector (ADVal ranked)
aDValToHVector (D (HVectorPseudoTensor h) (HVectorPseudoTensor h')) =
  ahhToHVector h h'

-- `Float '()` instead of `r y` is needed to avoid
-- `Ambiguous type variables ‘r1’, ‘y1’ arising from a use of ‘crev’`
-- in contexts like `crev (hVectorADValToADVal . f)`.
hVectorADValToADVal
  :: forall ranked. HVectorTensor ranked (ShapedOf ranked)
  => HVector (ADVal ranked) -> ADVal (HVectorPseudoTensor ranked) Float '()
hVectorADValToADVal hv =
  let (as, as') = unADValHVector hv
  in dDnotShared (HVectorPseudoTensor $ dmkHVector as)
                 (HVectorPseudoTensor $ HToH as')

unADValHVector
  :: HVector (ADVal f)
  -> (HVector f, HVector (Dual f))
unADValHVector = V.unzip . V.map unADValDynamicTensor

unADValDynamicTensor
  :: DynamicTensor (ADVal f)
  -> (DynamicTensor f, DynamicTensor (Dual f))
unADValDynamicTensor (DynamicRanked (D t t')) =
  (DynamicRanked t, DynamicRanked t')
unADValDynamicTensor (DynamicShaped (D t t')) =
  (DynamicShaped t, DynamicShaped t')
unADValDynamicTensor (DynamicRankedDummy p1 p2) =
  (DynamicRankedDummy p1 p2, DynamicRankedDummy p1 p2)
unADValDynamicTensor (DynamicShapedDummy p1 p2) =
  (DynamicShapedDummy p1 p2, DynamicShapedDummy p1 p2)

-- TODO: not dead code: will be used in dletHVectorInHVector.
aDValHVector :: (RankedTensor f, ShapedTensor (ShapedOf f))
             => HVector f -> HVector (Dual f) -> HVector (ADVal f)
aDValHVector = V.zipWith aDValDynamicTensor

-- TODO: Apparently other combinations occur in dletHVectorInHVector. Why?
aDValDynamicTensor :: (RankedTensor f, ShapedTensor (ShapedOf f))
                   => DynamicTensor f -> DynamicTensor (Dual f)
                   -> DynamicTensor (ADVal f)
aDValDynamicTensor (DynamicRanked @r1 @n1 t) (DynamicRanked @r2 @n2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameNat (Proxy @n1) (Proxy @n2) =
    DynamicRanked (dDnotShared t t')
aDValDynamicTensor (DynamicShaped @r1 @sh1 t) (DynamicShaped @r2 @sh2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShaped (dDnotShared t t')
aDValDynamicTensor (DynamicRankedDummy @r1 @sh1 _ _)
                   (DynamicRanked @r2 @n2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- matchingRank @sh1 @n2 =
    withListShape (shapeT @sh1) $ \(sh4 :: IShR n4) ->
      gcastWith (unsafeCoerce Refl :: n4 :~: X.Rank sh1) $
      DynamicRanked (dDnotShared (rzero sh4) t')
aDValDynamicTensor (DynamicShapedDummy @r1 @sh1 _ _)
                   (DynamicShaped @r2 @sh2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShaped (dDnotShared (srepl 0) t')
aDValDynamicTensor _ _ = error "aDValDynamicTensor: wrong arguments"
