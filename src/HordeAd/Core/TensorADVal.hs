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
  ( unADValRep
  , crevOnADInputs, crevOnHVector, cfwdOnHVector
  ) where

import Prelude hiding (foldl')

import Data.List (foldl')
import Data.List.Index (imap)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Nested
  (IShR, KnownShS (..), Rank, ShR (..), pattern (:$:), pattern ZSR)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Adaptor
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Core.CarriersConcrete
import HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), FlipS (..), valueOf)
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * Non-symbolic reverse and forward derivative computation

crevOnADInputs
  :: forall x z target.
     ( TensorKind x, TensorKind z, ADReadyNoLet target
     , ShareTensor target, ShareTensor (PrimalOf target) )
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> ADVal target x
  -> (target (ADTensorKind x), target z)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(!v, !delta) = unADValRep (stensorKind @z) $ f inputs in
  let parameters0 = tshapeFull (stensorKind @x) inputs
      !gradient = gradientFromDelta parameters0 v mdt delta
  in (gradient, v)

crevOnHVector
  :: forall x z target.
     ( TensorKind x, TensorKind z, ADReadyNoLet target
     , ShareTensor target, ShareTensor (PrimalOf target) )
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> target x
  -> (target (ADTensorKind x), target z)
crevOnHVector mdt f parameters =
  let deltaInputs = generateDeltaInputs
                    $ tshapeFull (stensorKind @x) parameters
      inputs = makeADInputs parameters deltaInputs
  in crevOnADInputs mdt f inputs

cfwdOnADInputs
  :: forall x z target.
     (TensorKind x, TensorKind z, ADReadyNoLet target, ShareTensor target)
  => ADVal target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target (ADTensorKind z), target z)
{-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs inputs f ds =
  let !(!v, !delta) = unADValRep (stensorKind @z) $ f inputs in
  let !derivative = derivativeFromDelta @x delta ds
  in (derivative, v)

cfwdOnHVector
  :: forall x z target.
     (TensorKind x, TensorKind z, ADReadyNoLet target, ShareTensor target)
  => target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target (ADTensorKind z), target z)
cfwdOnHVector parameters f ds =
  let deltaInputs = generateDeltaInputs
                    $ tshapeFull (stensorKind @x) parameters
      inputs = makeADInputs parameters deltaInputs
  in cfwdOnADInputs inputs f ds


-- * Misc instances

instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => LetTensor (ADVal target) where
  tlet :: forall x z. TensorKind x
       => ADVal target x
       -> (ADVal target x -> ADVal target z)
       -> ADVal target z
  tlet (D u u') f =
    let !var2 = tshare u
    in f (dDnotShared var2 u')

  toShare = id
  tunshare = id

instance (ADReadyNoLet target, ShareTensor target, ShareTensor (PrimalOf target))
         => ShareTensor (ADVal target) where
  tshare = id
  tunpair (D u u') = let (u1, u2) = tunpair u
                         (d1, d2) = unPairG u'
                     in (dDnotShared u1 d1, dDnotShared u2 d2)
  tunvector (D u u') = let vh = tunvector u
                       in ahhToHVector vh u'
  taddShare stk t1 t2 = fromRepD $ addRepD (toRepDShare stk t1)
                                           (toRepDShare stk t2)


-- * Base tensor instance

instance ( KnownNat n, GoodScalar r, ADReadyNoLet target
         , ShareTensor target, ShareTensor (PrimalOf target) )
         => AdaptableHVector (ADVal target)
                             (ADVal target (TKR r n)) where
{- TODO: RULE left-hand side too complicated to desugar in GHC 9.6.4
    with -O0, but not -O1
  {-# SPECIALIZE instance
      (KnownNat n, ADReadyNoLet ORArray)
      => AdaptableHVector (ADVal ORArray)
                          (ADVal ORArray Double n) #-}
  {-# SPECIALIZE instance
      (KnownNat n, ADReadyNoLet (AstRanked PrimalSpan))
      => AdaptableHVector (ADVal (AstRanked PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  type X (ADVal target (TKR r n)) = TKR r n
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKR r n)) =
    case sameTensorKind @(TKR r n) @(ADTensorKind (TKR r n)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (rzero (rshape aInit), Nothing)

instance ( KnownNat n, GoodScalar r, ADReadyNoLet target
         , ShareTensor target, ShareTensor (PrimalOf target) )
         => AdaptableHVector (ADVal target)
                             (AsHVector (ADVal target (TKR r n))) where
  type X (AsHVector (ADVal target (TKR r n))) = TKUntyped
  toHVectorOf = dmkHVector . V.singleton . DynamicRanked . unAsHVector
  fromHVector _aInit params = case V.uncons $ tunvector params of
    Just (dynamic, rest) ->
      Just (AsHVector $ fromDynamicR rzero dynamic, Just $ dmkHVector rest)
    Nothing -> Nothing

instance (KnownNat n, GoodScalar r, ADReadyNoLet target)
         => DualNumberValue (ADVal target (TKR r n)) where
  type DValue (ADVal target (TKR r n)) = RepN (TKR r n)  -- ! not Value(target)
  fromDValue t = fromPrimalADVal $ rconcrete $ runFlipR $ unRepN t

instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target)
         , KnownShS sh, GoodScalar r )
         => AdaptableHVector (ADVal target)
                             (ADVal target (TKS r sh)) where
  type X (ADVal target (TKS r sh)) = TKS r sh
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD _aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKS r sh)) =
    case sameTensorKind @(TKS r sh) @(ADTensorKind (TKS r sh)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (srepl 0, Nothing)

instance (ADReadyNoLet target, KnownShS sh, GoodScalar r)
         => DualNumberValue (ADVal target (TKS r sh)) where
  type DValue (ADVal target (TKS r sh)) = RepN (TKS r sh)   -- ! not Value(shaped)
  fromDValue t = fromPrimalADVal $ sconcrete $ runFlipS $ unRepN t

-- This is temporarily moved from Adaptor in order to specialize manually
instance ( a ~ target (TKR r n), BaseTensor target
         , GoodScalar r, KnownNat n, AdaptableHVector target a )
         => AdaptableHVector target [a] where
{- TODO
  {-# SPECIALIZE instance
      AdaptableHVector ORArray (OR.Array n Double)
      => AdaptableHVector ORArray
                          [OR.Array n Double] #-}
-}
{- TODO: import loop:
  {-# SPECIALIZE instance
      AdaptableHVector (AstRanked s)
                       (AstRanked s Double n)
      => AdaptableHVector (AstRanked s)
                          [AstRanked s Double n] #-}
-}
  type X [a] = TKUntyped
  toHVectorOf =
    dmkHVector . V.concat
    . map (dunHVector . toHVectorOf . DynamicRanked)
  fromHVector lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromHVector (DynamicRanked aInit) restAcc of
            Just (a, mrest) -> (rfromD @r @n a : lAcc, fromMaybe (dmkHVector V.empty) mrest)
            _ -> error "fromHVector: Nothing"
        (l, !restAll) = foldl' f ([], source) lInit
        !rl = reverse l
    in Just (rl, if nullRep restAll then Nothing else Just restAll)
    -- is the following as performant? benchmark:
    -- > fromHVector lInit source =
    -- >   let f = swap . flip fromHVector
    -- >   in swap $ mapAccumL f source lInit

instance ( BaseTensor target
         , AdaptableHVector target (AsHVector a)
         , X (AsHVector a) ~ TKUntyped )
         => AdaptableHVector target (AsHVector [a]) where
  type X (AsHVector [a]) = TKUntyped
  toHVectorOf =
    dmkHVector . V.concat
    . map (dunHVector . toHVectorOf . AsHVector)
    . unAsHVector
  fromHVector (AsHVector lInit) source =
    let f (!lAcc, !restAcc) !aInit =
          case fromHVector (AsHVector aInit) restAcc of
            Just (AsHVector a, mrest) -> (a : lAcc, fromMaybe (dmkHVector V.empty) mrest)
            _ -> error "fromHVector: Nothing"
        (l, !restAll) = foldl' f ([], source) lInit
        !rl = reverse l
    in Just (AsHVector rl, Just restAll)

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance (ADReadyNoLet target, ShareTensor target, ShareTensor (PrimalOf target))
         => BaseTensor (ADVal target) where
  rmkRepScalar (D t d) = dDnotShared (rmkRepScalar t) (UnScalarG d)
  runRepScalar (D t d) = dDnotShared (runRepScalar t) (ScalarG d)

  rshape (D u _) = rshape u
  rminIndex (D u _) =
    let v = rminIndex u
    in fromPrimalADVal v
  rmaxIndex (D u _) =
    let v = rmaxIndex u
    in fromPrimalADVal v
  rfloor (D u _) =
    let v = rfloor u
    in fromPrimalADVal v

  -- TODO: speed up by using tindex0R and dIndex0 if the codomain has rank 0
  -- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
  -- dimension affected.
  rindex d i = indexPrimal d (sprimalPart <$> i)
  rsum (D u u') = dD (rsum u) (SumR u')
  rsum0 (D u u') = dD (rsum0 u) (Sum0R u')
  rdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (rdot0 u v) (AddG (Dot0R v u') (Dot0R u v'))
  rscatter sh (D u u') f =
    let g x = sprimalPart <$> f (sfromPrimal <$> x)
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
           => IShR m -> ADVal target (TKR r n) -> ADVal target (TKR r m)
  rreshape sh t@(D u u') = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == rshape u -> t
    _ -> dD (rreshape sh u) (ReshapeR sh u')
  rbuild1 :: forall r n. (GoodScalar r, KnownNat n)
          => Int -> (IntOf (ADVal target) -> ADVal target (TKR r n))
          -> ADVal target (TKR r (1 + n))
  rbuild1 0 _ = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> rconcrete $ Nested.rfromListPrimLinear (0 :$: ZSR) []
                   -- the only case where we can guess sh
    _ ->  error "rbuild1: shape ambiguity, no arguments"
  rbuild1 k f = rfromList $ NonEmpty.fromList
                          $ map (f . fromIntegral) [0 .. k - 1]
                   -- element-wise (POPL) version
  rgather sh (D u u') f =
    let g x = sprimalPart <$> f (sfromPrimal <$> x)
    in dD (rgather sh u g) (GatherR sh u' g)
      -- note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on
  rcast (D u u') = dD (rcast u) (CastR u')
  rfromIntegral (D u _) =
    let v = rfromIntegral u
    in fromPrimalADVal v
  rconcrete t = fromPrimalADVal (rconcrete t)
  rfromS :: forall r sh. (GoodScalar r, KnownShS sh)
         => ADVal target (TKS r sh) -> ADVal target (TKR r (Rank sh))
  rfromS (D u u') = dDnotShared (rfromS u) (dRFromS u')
   where
    dRFromS :: (GoodScalar r2, KnownShS sh2)
            => Delta target (TKS r2 sh2) -> Delta target (TKR r2 (Rank sh2))
    dRFromS (SFromR d) = d  -- no information lost, so no checks
    dRFromS d = RFromS d

  rfromPrimal t = fromPrimalADVal t
  rprimalPart (D u _) = u
  rdualPart (D _ u') = u'
  rD t d = dD t d
  rScale k = ScaleG k

  xshape (D u _) = xshape u
  xindex d i = indexPrimalX d (sprimalPart <$> i)
  xfromVector = fromVectorX
  -- xreplicate (D u (DeltaX u')) = dD (xreplicate u) (DeltaX $ ReplicateX u')
  xreplicate _ = error "TODO"
  xconcrete t = fromPrimalADVal (xconcrete t)
  xfromPrimal t = fromPrimalADVal t
  xprimalPart (D u _) = u
  xdualPart (D _ u') = u'
  xD t d = dD t d

  sminIndex (D u _) =
    let v = sminIndex u
    in fromPrimalADVal v
  smaxIndex (D u _) =
    let v = smaxIndex u
    in fromPrimalADVal v
  sfloor (D u _) =
    let v = sfloor u
    in fromPrimalADVal v

  siota = fromPrimalADVal siota
  sindex d i = indexPrimalS d (sprimalPart <$> i)
  ssum (D u u') = dD (ssum u) (SumS u')
  ssum0 (D u u') = dD (ssum0 u) (Sum0S u')
  sdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (sdot0 u v) (AddG (Dot0S v u') (Dot0S u v'))
  sscatter (D u u') f =
    let g x = sprimalPart <$> f (sfromPrimal <$> x)
    in dD (sscatter u g) (ScatterS u' g)

  sfromVector = fromVectorS
  sunravelToList (D u u') =
    let lu = sunravelToList u
        f i ui = dD ui (IndexS u' (ShapedList.singletonIndex $ fromIntegral i))
    in imap f lu
  sreplicate (D u u') = dD (sreplicate u) ( ReplicateS u')
  sappend (D u u') (D v v') =
    dD (sappend u v) (AppendS u' v')
  sslice (i_proxy :: Proxy i) n_proxy (D u u') =
    dD (sslice i_proxy n_proxy u) (SliceS @target @i u')
  sreverse (D u u') = dD (sreverse u) (ReverseS u')

  stranspose :: forall perm r sh.
                ( PermC perm, KnownShS sh
                , Rank perm <= Rank sh, GoodScalar r )
             => Permutation.Perm perm -> ADVal target (TKS r sh)
             -> ADVal target (TKS r (Permutation.PermutePrefix perm sh))
  stranspose perm (D u u') | Dict <- Nested.Internal.Shape.shsKnownShS (Nested.Internal.Shape.shsPermutePrefix perm (knownShS @sh)) =
    dD (stranspose perm u) (TransposeS @_ @_ @_ @target perm u')
  sreshape :: forall sh sh2 r.
              ( GoodScalar r, KnownShS sh, KnownShS sh2
              , Nested.Product sh ~ Nested.Product sh2)
           => ADVal target (TKS r sh) -> ADVal target (TKS r sh2)
  sreshape t@(D u u') = case sameShape @sh2 @sh of
    Just Refl -> t
    _ -> dD (sreshape u) (ReshapeS u')
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (ADVal target) -> ADVal target (TKS r sh))
          -> ADVal target (TKS r (n ': sh))
  sbuild1 f = case valueOf @n of
    0 -> sconcrete $ Nested.sfromListPrimLinear knownShS []
    k -> sfromList $ NonEmpty.fromList
                   $ map (f . fromIntegral)
                         [0 :: Int .. k - 1]
           -- element-wise (POPL) version
  sgather (D u u') f =
    let g x = sprimalPart <$> f (sfromPrimal <$> x)
    in dD (sgather u g) (GatherS u' g)
  scast (D u u') = dD (scast u) (CastS u')
  sfromIntegral (D u _) =
    let v = sfromIntegral u
    in fromPrimalADVal v
  sconcrete t = fromPrimalADVal (sconcrete t)
  sfromR :: forall r sh. (GoodScalar r, KnownShS sh, KnownNat (Rank sh))
         => ADVal target (TKR r (Rank sh)) -> ADVal target (TKS r sh)
  sfromR (D u u') = dDnotShared (sfromR u) (dSFromR u')
   where
    dSFromR (RFromS @sh1 d) =
      case sameShape @sh1 @sh of
        Just Refl -> d
        _ -> error "sfromR: different shapes in SFromR(RFromS)"
    dSFromR d = SFromR d

  sfromPrimal t = fromPrimalADVal t
  sprimalPart (D u _) = u
  sdualPart (D _ u') = u'
  sD t d = dD t d
  sScale k = ScaleG k

  tpair (D u u') (D v v') = dDnotShared (tpair u v) (PairG u' v')
  tproject1 (D u u') = dDnotShared (tproject1 u) (fst $ unPairGUnshared u')
  tproject2 (D u u') = dDnotShared (tproject2 u) (snd $ unPairGUnshared u')
  dshape (D u _) = dshape u
  tshapeFull stk (D u _) = tshapeFull stk u
  tcond stk b u v = case stk of
    STKScalar _ -> rmkRepScalar $ ifF b (runRepScalar u) (runRepScalar v)
    STKR STKScalar{} SNat -> ifF b u v
    STKS STKScalar{} sh -> withKnownShS sh $ ifF b u v
    STKX STKScalar{} sh -> withKnownShX sh $ ifF b u v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      let (u1, u2) = tunpair u
          (v1, v2) = tunpair v
          !t1 = tcond stk1 b u1 v1
          !t2 = tcond stk2 b u2 v2
      in tpair t1 t2
    STKUntyped ->
      let us = tunvector u
          vs = tunvector v
          fd = mapDynamic2 (ifF b) (ifF b)
      in dmkHVector $ V.zipWith fd us vs
    _ -> error "TODO"
  tfromPrimal :: STensorKindType y
            -> target y
            -> ADVal target y
  tfromPrimal stk t | Dict <- lemTensorKindOfS stk = fromPrimalADVal t
  tprimalPart :: STensorKindType y
              -> ADVal target y
              -> target y
  tprimalPart _stk (D u _) = u
  tdualPart _stk (D _ u') = u'
  tD stk t d | Dict <- lemTensorKindOfS stk = dD t d
  dmkHVector hv =
    let (!as, !as') = V.unzip $ V.map unADValDynamicTensor hv
    in dDnotShared (dmkHVector as) (HToH as')
  tlambda _ = id
  tApply (HFun f) = f
  dunHVector = tunvector
  dbuild1 k f =
    dmkHVector $ ravelHVector $ map (tunvector . f . fromIntegral) [0 .. sNatValue k - 1]
  drev :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
       -> HFun x z
       -> HFun x (ADTensorKind x)
  drev _ftk h | Dict <- lemTensorKindOfAD (stensorKind @x) =
    let rf :: forall f. ADReady f
           => f x
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new a.
        rf !a = tlet a $ \ !aShared ->
          tunshare $ fst $ crevOnHVector
                             Nothing
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare aShared)
    in HFun rf
  drevDt :: forall x z. (TensorKind x, TensorKind z)
         => TensorKindFull x
         -> HFun x z
         -> HFun (TKProduct (ADTensorKind z) x) (ADTensorKind x)
  drevDt _ftk h | Dict <- lemTensorKindOfAD (stensorKind @x)
                , Dict <- lemTensorKindOfAD (stensorKind @z) =
    let rf :: forall f. ADReady f
           => f (TKProduct (ADTensorKind z) x)
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new db and a.
        rf !db_a = tlet db_a $ \ !db_aShared ->
          tunshare $ fst $ crevOnHVector
                             (Just $ toShare $ tproject1 db_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject2 db_aShared)
    in HFun rf
  dfwd :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
       -> HFun x z
       -> HFun (TKProduct (ADTensorKind x) x) (ADTensorKind z)
  dfwd _ftk h | Dict <- lemTensorKindOfAD (stensorKind @x)
              , Dict <- lemTensorKindOfAD (stensorKind @z) =
    let df :: forall f. ADReady f
           => f (TKProduct (ADTensorKind x) x)
           -> f (ADTensorKind z)
        -- This computes the derivative of g again for each new da and a.
        df !da_a = tlet da_a $ \ !da_aShared ->
          tunshare $ fst $ cfwdOnHVector
                             (toShare $ tproject2 da_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject1 da_aShared)
    in HFun df
  dmapAccumRDer
    :: forall k accShs bShs eShs.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (ADVal target)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (ADVal target) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (ADVal target) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                        (TKProduct accShs eShs))
                             (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (ADVal target) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                        (TKProduct accShs eShs))
                             (ADTensorKind (TKProduct accShs eShs))
    -> ADVal target accShs
    -> ADVal target (BuildTensorKind k eShs)
    -> ADVal target (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumRDer _ !k accShs bShs eShs f df rf acc0D esD
   | Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @bShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs) =
    let (acc0, acc0') = unADValRep stensorKind acc0D
        (esNotShared, es') = unADValRep stensorKind esD
        es = tshare esNotShared
        codomainShs = FTKProduct accShs bShs
        g :: forall f. ADReady f
          => f (TKProduct accShs eShs)
          -> f (TKProduct accShs (TKProduct accShs bShs))
        g !acc_e =
          tlet acc_e $ \ !acc_e1 ->
          tlet (unHFun f acc_e) $ \ !accRes_bRes ->
            tpair (tproject1 accRes_bRes)
                  (tpair (tproject1 acc_e1) (tproject2 accRes_bRes))
        dg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accShs eShs))
                               (TKProduct accShs eShs))
           -> f (ADTensorKind (TKProduct accShs (TKProduct accShs bShs)))
        dg !dacc_de_acc_e =
          tlet dacc_de_acc_e $ \ !dacc_de_acc_e1 ->
            let (!dacc_de, !_acc_e) =
                  (tproject1 dacc_de_acc_e1, tproject2 dacc_de_acc_e1)
                !dacc1 = tproject1 dacc_de
            in tlet (unHFun df dacc_de_acc_e) $ \ !accRes_bRes ->
                 tpair (tproject1 accRes_bRes)
                       (tpair dacc1 (tproject2 accRes_bRes))
        rg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accShs
                                                        (TKProduct accShs bShs)))
                               (TKProduct accShs eShs))
           -> f (ADTensorKind (TKProduct accShs eShs))
        rg !args =
          tlet args $ \ args1 ->
            let (!dx_db, !acc_e) = (tproject1 args1, tproject2 args1)
            in tlet dx_db $ \ !dx_db1 ->
              let (!dx, !db) = (tproject1 dx_db1, tproject2 dx_db1)
              in tlet db $ \ !db1 ->
                let dx_dbRes = tpair dx (tproject2 db1)
                in tlet (unHFun rf (tpair dx_dbRes acc_e)) $ \ !daccRes_deRes ->
                  let added = taddLet stensorKind (tproject1 daccRes_deRes)
                                                  (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = dmapAccumRDer (Proxy @target)
                          k accShs codomainShs eShs
                          (tlambda @target (FTKProduct accShs eShs)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (aDTensorKind (FTKProduct accShs eShs))
                                         (FTKProduct accShs eShs))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (aDTensorKind (FTKProduct accShs codomainShs))
                                         (FTKProduct accShs eShs))
                           $ HFun rg)
                          acc0 es
        (accFin, qbs) = tunpair p
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        (q, bs) = tunpair qbs
        dual = MapAccumR k accShs bShs eShs
                         q es
                         df rf acc0' es'
    in dD (tpair accFin bs) dual
  dmapAccumLDer
    :: forall k accShs bShs eShs.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy (ADVal target)
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf (ADVal target) (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf (ADVal target) (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                        (TKProduct accShs eShs))
                             (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf (ADVal target) (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                        (TKProduct accShs eShs))
                             (ADTensorKind (TKProduct accShs eShs))
    -> ADVal target accShs
    -> ADVal target (BuildTensorKind k eShs)
    -> ADVal target (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumLDer _ !k accShs bShs eShs f df rf acc0D esD
   | Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @bShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs) =
    let (acc0, acc0') = unADValRep stensorKind acc0D
        (esNotShared, es') = unADValRep stensorKind esD
        es = tshare esNotShared
        codomainShs = FTKProduct accShs bShs
        g :: forall f. ADReady f
          => f (TKProduct accShs eShs)
          -> f (TKProduct accShs (TKProduct accShs bShs))
        g !acc_e =
          tlet acc_e $ \ !acc_e1 ->
          tlet (unHFun f acc_e) $ \ !accRes_bRes ->
            tpair (tproject1 accRes_bRes)
                  (tpair (tproject1 acc_e1) (tproject2 accRes_bRes))
        dg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accShs eShs))
                               (TKProduct accShs eShs))
           -> f (ADTensorKind (TKProduct accShs (TKProduct accShs bShs)))
        dg !dacc_de_acc_e =
          tlet dacc_de_acc_e $ \ !dacc_de_acc_e1 ->
            let (!dacc_de, !_acc_e) =
                  (tproject1 dacc_de_acc_e1, tproject2 dacc_de_acc_e1)
                !dacc1 = tproject1 dacc_de
            in tlet (unHFun df dacc_de_acc_e) $ \ !accRes_bRes ->
                 tpair (tproject1 accRes_bRes)
                       (tpair dacc1 (tproject2 accRes_bRes))
        rg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accShs
                                                        (TKProduct accShs bShs)))
                               (TKProduct accShs eShs))
           -> f (ADTensorKind (TKProduct accShs eShs))
        rg !args =
          tlet args $ \ args1 ->
            let (!dx_db, !acc_e) = (tproject1 args1, tproject2 args1)
            in tlet dx_db $ \ !dx_db1 ->
              let (!dx, !db) = (tproject1 dx_db1, tproject2 dx_db1)
              in tlet db $ \ !db1 ->
                let dx_dbRes = tpair dx (tproject2 db1)
                in tlet (unHFun rf (tpair dx_dbRes acc_e)) $ \ !daccRes_deRes ->
                  let added = taddLet stensorKind (tproject1 daccRes_deRes)
                                                  (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = dmapAccumLDer (Proxy @target)
                          k accShs codomainShs eShs
                          (tlambda @target (FTKProduct accShs eShs)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (aDTensorKind (FTKProduct accShs eShs))
                                         (FTKProduct accShs eShs))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (aDTensorKind (FTKProduct accShs codomainShs))
                                         (FTKProduct accShs eShs))
                           $ HFun rg)
                          acc0 es
        (accFin, qbs) = tunpair p
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        (q, bs) = tunpair qbs
        dual = MapAccumL k accShs bShs eShs
                         q es
                         df rf acc0' es'
    in dD (tpair accFin bs) dual

taddLet :: ADReady target
        => STensorKindType y -> target y -> target y -> target y
taddLet stk t1 t2 | Dict <- lemTensorKindOfS stk =
  tlet t1 $ \ !u1 ->
  tlet t2 $ \ !u2 ->
    fromRepD $ addRepD (toRepDDuplicable stk u1)
                       (toRepDDuplicable stk u2)

unADValDynamicTensor
  :: DynamicTensor (ADVal f)
  -> (DynamicTensor f, DynamicTensor (Delta f))
unADValDynamicTensor (DynamicRanked (D t t')) =
  (DynamicRanked t, DynamicRanked t')
unADValDynamicTensor (DynamicShaped (D t t')) =
  (DynamicShaped t, DynamicShaped t')
unADValDynamicTensor (DynamicRankedDummy p1 p2) =
  (DynamicRankedDummy p1 p2, DynamicRankedDummy p1 p2)
unADValDynamicTensor (DynamicShapedDummy p1 p2) =
  (DynamicShapedDummy p1 p2, DynamicShapedDummy p1 p2)

unADValRep
  :: forall y target.
     STensorKindType y
  -> ADVal target y
  -> (target y, Delta target y)
unADValRep _stk (D p d) = (p, d)
