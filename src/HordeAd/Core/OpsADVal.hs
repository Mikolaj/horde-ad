{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for dual numbers. Most of the definitions
-- are generic over whether the dual numbers are built from concrete arrays
-- of floats or from AST terms. However, here we do not abstract over
-- the typing of tensors and so we give separate instances
-- for ranked tensors and shaped tensors.
module HordeAd.Core.OpsADVal
  ( unADValRep
  , crevOnADInputs, crevOnHVector, cfwdOnHVector
  ) where

import Prelude hiding (foldl')

import Control.Exception.Assert.Sugar
import Data.List (foldl')
import Data.List.Index (imap)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import Type.Reflection (typeRep)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (StaticShX, ssxAppend, ssxFromShape, ssxReplicate)
import Data.Array.Nested
  (IShR, KnownShS (..), KnownShX (..), MapJust, Rank, Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shCvtSX)
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Adaptor
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
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
  let parameters0 = tftk (stensorKind @x) inputs
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
                    $ tftk (stensorKind @x) parameters
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
                    $ tftk (stensorKind @x) parameters
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

instance (ADReadyNoLet target, ShareTensor target)
         => ShareTensor (ADVal target) where
  tshare = id
  tunpair (D u u') = let (u1, u2) = tunpair u
                         (d1, d2) = unPairG u'
                     in (dDnotShared u1 d1, dDnotShared u2 d2)
  tunvector (D u u') = let vh = tunvector u
                       in ahhToHVector vh u'


-- * Base tensor instance

instance ( KnownNat n, GoodScalar r, ADReadyNoLet target
         , ShareTensor target, ShareTensor (PrimalOf target) )
         => AdaptableHVector (ADVal target)
                             (ADVal target (TKR n r)) where
{- TODO: RULE left-hand side too complicated to desugar in GHC 9.6.4
    with -O0, but not -O1
  {-# SPECIALIZE instance
      (KnownNat n, ADReadyNoLet Nested.Ranked)
      => AdaptableHVector (ADVal Nested.Ranked)
                          (ADVal Nested.Ranked Double n) #-}
  {-# SPECIALIZE instance
      (KnownNat n, ADReadyNoLet (AstRanked PrimalSpan))
      => AdaptableHVector (ADVal (AstRanked PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  type X (ADVal target (TKR n r)) = TKR n r
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKR n r)) =
    case sameTensorKind @(TKR n r) @(ADTensorKind (TKR n r)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (rzero (rshape aInit), Nothing)

instance ( KnownNat n, GoodScalar r, ADReadyNoLet target
         , ShareTensor target, ShareTensor (PrimalOf target) )
         => AdaptableHVector (ADVal target)
                             (AsHVector (ADVal target (TKR n r))) where
  type X (AsHVector (ADVal target (TKR n r))) = TKUntyped
  toHVectorOf = dmkHVector . V.singleton . DynamicRanked . unAsHVector
  fromHVector _aInit params = case V.uncons $ tunvector params of
    Just (dynamic, rest) ->
      Just (AsHVector $ fromDynamicR rzero dynamic, Just $ dmkHVector rest)
    Nothing -> Nothing

instance (KnownNat n, GoodScalar r, ADReadyNoLet target)
         => DualNumberValue (ADVal target (TKR n r)) where
  type DValue (ADVal target (TKR n r)) = RepN (TKR n r)  -- ! not Value(target)
  fromDValue t = fromPrimalADVal $ rconcrete $ unRepN t

instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target)
         , KnownShS sh, GoodScalar r )
         => AdaptableHVector (ADVal target)
                             (ADVal target (TKS sh r)) where
  type X (ADVal target (TKS sh r)) = TKS sh r
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD _aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKS sh r)) =
    case sameTensorKind @(TKS sh r) @(ADTensorKind (TKS sh r)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (srepl 0, Nothing)

instance (ADReadyNoLet target, KnownShS sh, GoodScalar r)
         => DualNumberValue (ADVal target (TKS sh r)) where
  type DValue (ADVal target (TKS sh r)) = RepN (TKS sh r)   -- ! not Value(shaped)
  fromDValue t = fromPrimalADVal $ sconcrete $ unRepN t

-- This is temporarily moved from Adaptor in order to specialize manually
instance ( a ~ target (TKR n r), BaseTensor target
         , GoodScalar r, KnownNat n, AdaptableHVector target a )
         => AdaptableHVector target [a] where
{- TODO
  {-# SPECIALIZE instance
      AdaptableHVector Nested.Ranked (OR.Array n Double)
      => AdaptableHVector Nested.Ranked
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
            Just (AsHVector a, mrest) -> (a : lAcc, fromMaybe (dmkHVector @target V.empty) mrest)
            _ -> error "fromHVector: Nothing"
        (l, !restAll) = foldl' f ([], source) lInit
        !rl = reverse l
    in Just (AsHVector rl, Just restAll)

indexPrimal :: ( ADReadyNoLet target, TensorKind r
               , KnownNat m, KnownNat n )
            => ADVal target (TKR2 (m + n) r) -> IxROf target m
            -> ADVal target (TKR2 n r)
indexPrimal (D u u') ix = dD (rindex u ix) (IndexR u' ix)

indexPrimalS :: ( ADReadyNoLet target, TensorKind r
                , KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2) )
             => ADVal target (TKS2 (sh1 ++ sh2) r) -> IxSOf target sh1
             -> ADVal target (TKS2 sh2 r)
indexPrimalS (D u u') ix = dD (sindex u ix) (IndexS u' ix)

indexPrimalX :: ( ADReadyNoLet target
                , TensorKind r, KnownShX sh1, KnownShX sh2
                , KnownShX (sh1 ++ sh2) )
             => ADVal target (TKX2 (sh1 ++ sh2) r) -> IxXOf target sh1
             -> ADVal target (TKX2 sh2 r)
indexPrimalX (D u u') ix = dD (xindex u ix) (IndexX u' ix)

instance (ADReadyNoLet target, ShareTensor target, ShareTensor (PrimalOf target))
         => IfF (ADVal target) where
  ifF :: forall y. TensorKind y
      => BoolOf target -> ADVal target y -> ADVal target y -> ADVal target y
  ifF = tcond (stensorKind @y)

{- TODO: use for speed-up, e.g,. by checking the type at runtime
instance IfF (ADVal (FlipR OR.Array)) where
  ifF (_, b) v w = if b then v else w

instance IfF (ADVal (FlipS OS.Array)) where
  ifF (_, b) v w = if b then v else w
-}

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance (ADReadyNoLet target, ShareTensor target, ShareTensor (PrimalOf target))
         => BaseTensor (ADVal target) where
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
  rindex d i = indexPrimal d (tprimalPart (STKScalar typeRep) <$> i)
  rsum (D u u') = dD (rsum u) (SumR u')
  rsum0 (D u u') = dD (rsum0 u) (Sum0R u')
  rdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (rdot0 u v) (AddG (Dot0R v u') (Dot0R u v'))
  rscatter sh (D u u') f =
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (rscatter sh u g) (ScatterR sh u' g)

  rfromVector :: forall n r. (KnownNat n, TensorKind r)
              => Data.Vector.Vector (ADVal target (TKR2 n r))
              -> ADVal target (TKR2 (1 + n) r)
  rfromVector lu =
    -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
    dD (rfromVector $ V.map (\(D u _) -> u) lu)
       (FromVectorR $ V.map (\(D _ u') -> u') lu)
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
  rreshape :: forall n m r. (TensorKind r, KnownNat n, KnownNat m)
           => IShR m -> ADVal target (TKR2 n r) -> ADVal target (TKR2 m r)
  rreshape sh t@(D u u') = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == rshape u -> t
    _ -> dD (rreshape sh u) (ReshapeR sh u')
  rbuild1 :: forall r n. (TensorKind r, KnownNat n)
          => Int -> (IntOf (ADVal target) -> ADVal target (TKR2 n r))
          -> ADVal target (TKR2 (1 + n) r)
  rbuild1 0 _ = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> case stensorKind @r of
      STKScalar{} -> rconcrete Nested.remptyArray
      _ -> error "rbuild1: empty nested array"
    Nothing -> error "rbuild1: shape ambiguity"
  rbuild1 k f = rfromList $ NonEmpty.map (f . fromIntegral)
                          $ (0 :: Int) :| [1 .. k - 1]
    -- element-wise (POPL) version
  rgather sh (D u u') f =
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (rgather sh u g) (GatherR sh u' g)
      -- note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on
  rcast (D u u') = dD (rcast u) (CastR u')
  rfromIntegral (D u _) =
    let v = rfromIntegral u
    in fromPrimalADVal v
  rzip (D u u') = dD (rzip u) (ZipR u')
  runzip (D u u') = dD (runzip u) (UnzipR u')
  rtoScalar (D t d) = dDnotShared (rtoScalar t) (ToScalarG $ SFromR d)
  rfromScalar (D t d) = dDnotShared (rfromScalar t) (RFromS $ FromScalarG d)

  rfromPrimal t = fromPrimalADVal t
  rprimalPart (D u _) = u
  rdualPart (D _ u') = u'
  rD t d = dD t d
  rScale k = ScaleG k

  xshape (D u _) = xshape u
  xindex d i = indexPrimalX d (tprimalPart (STKScalar typeRep) <$> i)

  xfromVector :: forall n sh r. (KnownNat n, KnownShX sh, TensorKind r)
              => Data.Vector.Vector (ADVal target (TKX2 sh r))
              -> ADVal target (TKX2 (Just n ': sh) r)
  xfromVector lu = assert (length lu == valueOf @n) $
    dD (xfromVector $ V.map (\(D u _) -> u) lu)
       (FromVectorX $ V.map (\(D _ u') -> u') lu)
  -- xreplicate (D u (DeltaX u')) = dD (xreplicate u) (DeltaX $ ReplicateX u')
  xreplicate _ = error "TODO"
  xzip (D u u') = dD (xzip u) (ZipX u')
  xunzip (D u u') = dD (xunzip u) (UnzipX u')
  xtoScalar (D t d) = dDnotShared (xtoScalar t) (ToScalarG $ SFromX d)
  xfromScalar (D t d) = dDnotShared (xfromScalar t) (XFromS $ FromScalarG d)
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
  sindex d i = indexPrimalS d (tprimalPart (STKScalar typeRep) <$> i)
  ssum (D u u') = dD (ssum u) (SumS u')
  ssum0 (D u u') = dD (ssum0 u) (Sum0S u')
  sdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (sdot0 u v) (AddG (Dot0S v u') (Dot0S u v'))
  sscatter (D u u') f =
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (sscatter u g) (ScatterS u' g)

  sfromVector :: forall n sh r. (KnownNat n, KnownShS sh, TensorKind r)
              => Data.Vector.Vector (ADVal target (TKS2 sh r))
              -> ADVal target (TKS2 (n ': sh) r)
  sfromVector lu = assert (length lu == valueOf @n) $
    dD (sfromVector $ V.map (\(D u _) -> u) lu)
       (FromVectorS $ V.map (\(D _ u') -> u') lu)
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
                , Rank perm <= Rank sh, TensorKind r )
             => Permutation.Perm perm -> ADVal target (TKS2 sh r)
             -> ADVal target (TKS2 (Permutation.PermutePrefix perm sh) r)
  stranspose perm (D u u') | Dict <- Nested.Internal.Shape.shsKnownShS (Nested.Internal.Shape.shsPermutePrefix perm (knownShS @sh)) =
    dD (stranspose perm u) (TransposeS @_ @_ @_ @target perm u')
  sreshape :: forall sh sh2 r.
              ( TensorKind r, KnownShS sh, KnownShS sh2
              , Nested.Product sh ~ Nested.Product sh2)
           => ADVal target (TKS2 sh r) -> ADVal target (TKS2 sh2 r)
  sreshape t@(D u u') = case sameShape @sh2 @sh of
    Just Refl -> t
    _ -> dD (sreshape u) (ReshapeS u')
  sbuild1 :: forall r n sh. (TensorKind r, KnownNat n, KnownShS sh)
          => (IntOf (ADVal target) -> ADVal target (TKS2 sh r))
          -> ADVal target (TKS2 (n ': sh) r)
  sbuild1 f = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> case stensorKind @r of
      STKScalar{} ->
        sconcrete $ Nested.semptyArray (knownShS @sh)
      _ -> error "sbuild1: empty nested array"
    Nothing -> sfromList $ NonEmpty.map (f . fromIntegral)
                         $ (0 :: Int) :| [1 .. valueOf @n - 1]
      -- element-wise (POPL) version
  sgather (D u u') f =
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (sgather u g) (GatherS u' g)
  scast (D u u') = dD (scast u) (CastS u')
  sfromIntegral (D u _) =
    let v = sfromIntegral u
    in fromPrimalADVal v
  stoScalar (D t d) = dDnotShared (stoScalar t) (ToScalarG d)
  sfromScalar (D t d) = dDnotShared (sfromScalar t) (FromScalarG d)
  szip (D u u') = dD (szip u) (ZipS u')
  sunzip (D u u') = dD (sunzip u) (UnzipS u')

  sfromPrimal t = fromPrimalADVal t
  sprimalPart (D u _) = u
  sdualPart (D _ u') = u'
  sD t d = dD t d
  sScale k = ScaleG k

  kfloor (D u _) =
    let v = kfloor u
    in fromPrimalADVal v
  kcast (D u u') = dD (kcast u) (Cast u')
  kfromIntegral (D u _) =
    let v = kfromIntegral u
    in fromPrimalADVal v

  rfromS (D u u') = dDnotShared (rfromS u) (dRFromS u')
   where
    dRFromS :: (TensorKind r2, KnownShS sh2)
            => Delta target (TKS2 sh2 r2) -> Delta target (TKR2 (Rank sh2) r2)
    dRFromS (SFromR d) = d  -- no information lost, so no checks
    dRFromS d = RFromS d
  rfromX (D u u') = dDnotShared (rfromX u) (dRFromX u')
   where
    dRFromX :: (TensorKind r2, KnownShX sh2)
            => Delta target (TKX2 sh2 r2) -> Delta target (TKR2 (Rank sh2) r2)
    dRFromX (XFromR d) = d  -- no information lost, so no checks
    dRFromX d = RFromX d
  sfromR :: forall r sh. (TensorKind r, KnownShS sh, KnownNat (Rank sh))
         => ADVal target (TKR2 (Rank sh) r) -> ADVal target (TKS2 sh r)
  sfromR (D u u') = dDnotShared (sfromR u) (dSFromR u')
   where
    dSFromR (RFromS @sh1 d) =
      case sameShape @sh1 @sh of
        Just Refl -> d
        _ -> error "sfromR: different shapes in SFromR(RFromS)"
    dSFromR d = SFromR d
  sfromX :: forall r sh sh'.
            ( KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r )
         => ADVal target (TKX2 sh' r) -> ADVal target (TKS2 sh r)
  sfromX (D u u') = dDnotShared (sfromX u) (dSFromX u')
   where
    dSFromX (XFromS @sh1 d) =
      case sameShape @sh1 @sh of
        Just Refl -> d
        _ -> error "sfromR: different shapes in SFromR(RFromS)"
    dSFromX d = SFromX d
  xfromR :: forall sh r. (KnownShX sh, TensorKind r)
         => ADVal target (TKR2 (Rank sh) r) -> ADVal target (TKX2 sh r)
  xfromR (D u u') | Dict <- lemKnownNatRankX (knownShX @sh) =
    dDnotShared (xfromR u) (XFromR u')
  xfromS (D u u') = dDnotShared (xfromS u) (XFromS u')

  xnestR :: forall sh1 m x.
            (TensorKind x, KnownNat m)
         => StaticShX sh1 -> ADVal target (TKX2 (sh1 ++ Replicate m Nothing) x)
         -> ADVal target (TKX2 sh1 (TKR2 m x))
  xnestR sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    dD (xnestR sh1 u) (XNestR u')
  xnestS :: forall sh1 sh2 x.
            (TensorKind x, KnownShS sh2)
         => StaticShX sh1 -> ADVal target (TKX2 (sh1 ++ MapJust sh2) x)
         -> ADVal target (TKX2 sh1 (TKS2 sh2 x))
  xnestS sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    dD (xnestS sh1 u) (XNestS u')
  xnest :: forall sh1 sh2 x.
           (TensorKind x, KnownShX sh2)
        => StaticShX sh1 -> ADVal target (TKX2 (sh1 ++ sh2) x)
        -> ADVal target (TKX2 sh1 (TKX2 sh2 x))
  xnest sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` knownShX @sh2) $
    dD (xnest sh1 u) (XNest u')

  xunNestR :: forall sh1 m x.
              (TensorKind x, KnownShX sh1, KnownNat m)
           => ADVal target (TKX2 sh1 (TKR2 m x))
           -> ADVal target (TKX2 (sh1 ++ Replicate m Nothing) x)
  xunNestR (D u u') =
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    dD (xunNestR u) (XUnNestR u')
  xunNestS :: forall sh1 sh2 x.
              (TensorKind x, KnownShX sh1, KnownShS sh2)
           => ADVal target (TKX2 sh1 (TKS2 sh2 x))
           -> ADVal target (TKX2 (sh1 ++ MapJust sh2) x)
  xunNestS (D u u') =
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    dD (xunNestS u) (XUnNestS u')
  xunNest :: forall sh1 sh2 x.
             (TensorKind x, KnownShX sh1, KnownShX sh2)
          => ADVal target (TKX2 sh1 (TKX2 sh2 x))
          -> ADVal target (TKX2 (sh1 ++ sh2) x)
  xunNest (D u u') =
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    dD (xunNest u) (XUnNest u')

  tpair (D u u') (D v v') = dDnotShared (tpair u v) (PairG u' v')
  tproject1 (D u u') = dDnotShared (tproject1 u) (fst $ unPairGUnshared u')
  tproject2 (D u u') = dDnotShared (tproject2 u) (snd $ unPairGUnshared u')
  dshape (D u _) = dshape u
  tftk stk (D u _) = tftk stk u
  -- Bangs are for the proper order of sharing stamps.
  tcond !stk !b !u !v = case stk of
    STKScalar _ -> rtoScalar $ ifF b (rfromScalar u) (rfromScalar v)
    STKR SNat x | Dict <- lemTensorKindOfSTK x ->
      indexPrimal (rfromVector $ V.fromList [u, v])
                  (fromList [ifF b 0 1])
    STKS sh x | Dict <- lemTensorKindOfSTK x -> withKnownShS sh $
      indexPrimalS @_ @_ @'[2]
                   (sfromVector $ V.fromList [u, v])
                   (fromList [ifF b 0 1])
    STKX sh x | Dict <- lemTensorKindOfSTK x -> withKnownShX sh $
      indexPrimalX @_ @_ @'[Just 2]
                   (xfromVector $ V.fromList [u, v])
                   (fromList [ifF b 0 1])
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                         , Dict <- lemTensorKindOfSTK stk2 ->
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
  tfromPrimal :: STensorKindType y
            -> target y
            -> ADVal target y
  tfromPrimal stk t | Dict <- lemTensorKindOfSTK stk = fromPrimalADVal t
  tprimalPart :: STensorKindType y
              -> ADVal target y
              -> target y
  tprimalPart _stk (D u _) = u
  tdualPart _stk (D _ u') = u'
  tD stk t d | Dict <- lemTensorKindOfSTK stk = dD t d
  tconcrete ftk t | Dict <- lemTensorKindOfSTK (ftkToStk ftk) =
    fromPrimalADVal $ tconcrete ftk t
  dmkHVector hv =
    let (!as, !as') = V.unzip $ V.map unADValDynamicTensor hv
    in dDnotShared (dmkHVector as) (HToH as')
  tlambda _ = id
  tApply (HFun f) = f
  dbuild1 k f =
    dmkHVector $ ravelHVector $ map (tunvector . f . fromIntegral) [0 .. sNatValue k - 1]
  drev :: forall x z. (TensorKind x, TensorKind z)
       => FullTensorKind x
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
         => FullTensorKind x
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
       => FullTensorKind x
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
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
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
                  let added = addTarget stensorKind (tproject1 daccRes_deRes)
                                                    (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = dmapAccumRDer (Proxy @target)
                          k accShs codomainShs eShs
                          (tlambda @target (FTKProduct accShs eShs)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (aDFTK (FTKProduct accShs eShs))
                                         (FTKProduct accShs eShs))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (aDFTK (FTKProduct accShs codomainShs))
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
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
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
                  let added = addTarget stensorKind (tproject1 daccRes_deRes)
                                                    (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = dmapAccumLDer (Proxy @target)
                          k accShs codomainShs eShs
                          (tlambda @target (FTKProduct accShs eShs)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (aDFTK (FTKProduct accShs eShs))
                                         (FTKProduct accShs eShs))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (aDFTK (FTKProduct accShs codomainShs))
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
