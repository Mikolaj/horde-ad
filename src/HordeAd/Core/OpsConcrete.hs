{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for concrete Storable Vector-backed arrays.
module HordeAd.Core.OpsConcrete
  () where

import Prelude hiding (foldl')

import Control.Arrow (second)
import Control.Exception.Assert.Sugar
import Data.Default
import Data.Foldable qualified as Foldable
import Data.Function ((&))
import Data.Int (Int64)
import Data.List (foldl', mapAccumL, mapAccumR, scanl')
import Data.List.Index (imap)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Storable qualified as VS
import GHC.Exts (IsList (..))
import GHC.IsList qualified as IsList
import GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import Numeric.LinearAlgebra (Numeric)
import Numeric.LinearAlgebra qualified as LA
import System.Random
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Internal.Arith qualified as Mixed.Internal.Arith
  (liftVEltwise1)
import Data.Array.Mixed.Lemmas
import Data.Array.Nested
  ( StaticShX(..), IShR
  , IxR, IShX
  , IxS
  , IxX
  , KnownShS (..)
  , KnownShX (..)
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , ShX (..)
  , pattern (:$:)
  , pattern ZSR
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal.Mixed
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape
  (shrRank, shrSize, shsTail, withKnownShS, shrTail, shsAppend, shsProduct, shsSize)
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal
import Data.Array.Mixed.Types (Init)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Mixed.Shape (shxSize, shxTakeSSX, shxTail, ssxFromShape, shxDropSSX, ssxAppend, withKnownShX)

import HordeAd.Core.Adaptor
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.HVectorOps
import HordeAd.Core.OpsADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

instance EqF RepN where
  (==.) :: forall y. TensorKind y => RepN y -> RepN y -> Bool
  RepN u ==. RepN v = case stensorKind @y of
    STKScalar _ -> u == v
    STKR SNat STKScalar{} -> u == v
    STKS sh STKScalar{} -> withKnownShS sh $ u == v
    STKX sh STKScalar{} -> withKnownShX sh $ u == v
    STKProduct @y1 @y2 stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                                 , Dict <- lemTensorKindOfSTK stk2 ->
      RepN @y1 (fst u) ==. RepN  @y1(fst v)
      && RepN @y2 (snd u) ==. RepN @y2 (snd v)
    _ -> error "TODO"

instance OrdF RepN where
  (<.) :: forall y. TensorKind y => RepN y -> RepN y -> Bool
  RepN u <. RepN v = case stensorKind @y of
    STKScalar _ -> u < v
    STKR SNat STKScalar{} -> u < v
    STKS sh STKScalar{} -> withKnownShS sh $ u < v
    STKX sh STKScalar{} -> withKnownShX sh $ u < v
    STKProduct @y1 @y2 stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                                 , Dict <- lemTensorKindOfSTK stk2 ->
      RepN @y1 (fst u) <. RepN @y1 (fst v)
      && RepN @y2 (snd u) <. RepN @y2 (snd v)
        -- lexicographic ordering  -- TODO: is this standard and the same as for <=. ? as for || ?
    _ -> error "TODO"

instance LetTensor RepN where
  tlet = (&)
  toShare = id
  tunshare = id

instance ShareTensor RepN where
  tshare = id
  tunpair (RepN (t1, t2)) = (RepN t1, RepN t2)

instance BaseTensor RepN where
  rshape @r | Dict <- eltDictRep (stensorKind @r) = Nested.rshape . unRepN
  rminIndex = RepN . tminIndexR . unRepN
  rmaxIndex = RepN . tmaxIndexR . unRepN
  rfloor = RepN . liftVR (V.map floor) . unRepN
  riota n = RepN $ Nested.rfromList1 $ NonEmpty.map fromInteger
            $ NonEmpty.fromList [0 .. fromIntegral n - 1]
  rindex = tindexZR
  rindex0 = tindex0R
  rsum t = case tftk stensorKind t of
    FTKR _ FTKScalar ->  -- optimized
      RepN . Nested.rsumOuter1 . unRepN $ t
    FTKR _ x ->
      let l = runravelToList t
          sh = shrTail $ rshape t
      in foldr (addTarget stensorKind) (constantTarget 0 (FTKR sh x)) l
  rsum0 t = case tftk stensorKind t of
    FTKR _ FTKScalar ->  -- optimized
      RepN . Nested.rscalar . Nested.rsumAllPrim . unRepN $ t
    FTKR _ _ ->
      rsum . rflatten $ t
  rdot0 u v = RepN $ Nested.rscalar $ Nested.rdot (unRepN u) (unRepN v)
  rmatmul2 m1 m2 = RepN $ tmatmul2R (unRepN m1) (unRepN m2)
  rscatter = tscatterZR
  rscatter1 = tscatterZ1R
  rfromList @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rfromListOuter . NonEmpty.map unRepN
      -- TODO: make this strict
  rfromList0N @r sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . tfromList0NR sh . map unRepN
  rfromVector @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rfromListOuter . NonEmpty.fromList . V.toList . V.map unRepN
  rfromVector0N @r sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . tfromList0NR sh . V.toList . V.map unRepN
  runravelToList @r | Dict <- eltDictRep (stensorKind @r) =
    map RepN . Nested.rtoListOuter . unRepN
  rreplicate @r k | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rreplicate (k :$: ZSR) . unRepN
  rreplicate0N @r sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rreplicate sh . unRepN
  rappend @r u v | Dict <- eltDictRep (stensorKind @r) =
    RepN $ Nested.rappend (unRepN u) (unRepN v)
  rslice @r i n | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rslice i n . unRepN
  rreverse @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rrev1 . unRepN
  rtranspose @r perm | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rtranspose perm . unRepN
  rreshape @r sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rreshape sh . unRepN
  rbuild1 @r k f | Dict <- eltDictRep (stensorKind @r) =
    RepN $ tbuild1R k (unRepN . f . RepN)
  rmap0N @r @r1 f t = case (stensorKind @r1, stensorKind @r) of
    (STKScalar{}, STKScalar{}) -> RepN $ tmap0NR (unRepN . f . RepN) (unRepN t)
    _ ->  -- TODO: how to call the default implementation?
      rbuild (rshape t) (f . rindex0 t)
  rzipWith0N @r1 @r2 @r f t u =
    case (stensorKind @r1, stensorKind @r2, stensorKind @r) of
      (STKScalar{}, STKScalar{}, STKScalar{}) ->
        RepN $ tzipWith0NR (\v w -> unRepN $ f (RepN v) (RepN w))
                           (unRepN t) (unRepN u)
      _ ->  -- TODO: how to call the default implementation?
        rbuild (rshape u) (\ix -> f (rindex0 t ix) (rindex0 u ix))
  rgather = tgatherZR
  rgather1 = tgatherZ1R
  rcast = RepN . liftVR (V.map realToFrac) . unRepN
  rfromIntegral = RepN . liftVR (V.map fromIntegral) . unRepN
  rzip (RepN (a, b)) = RepN $ Nested.rzip a b
  runzip = RepN . Nested.runzip . unRepN
  rtoScalar = RepN . Nested.runScalar . unRepN
  rfromScalar = RepN . Nested.rscalar . unRepN

  rscaleByScalar s v =
    RepN $ liftVR (V.map (* Nested.runScalar (unRepN s))) (unRepN v)
  rdot1In u v = RepN $ Nested.rdot1Inner (unRepN u) (unRepN v)

  rfromPrimal = id
  rprimalPart = id
  rdualPart _ = DummyDualTarget
  rD u _ = u
  rScale _ _ = DummyDualTarget

  sminIndex = RepN . tminIndexS . unRepN
  smaxIndex = RepN . tmaxIndexS . unRepN
  sfloor = RepN . liftVS (V.map floor) . unRepN
  siota @n = let n = valueOf @n
             in RepN $ Nested.sfromList1 SNat
                $ NonEmpty.map fromInteger $ NonEmpty.fromList [0 .. n - 1]
  sindex = tindexZS
  sindex0 = tindex0S
  ssum t = case tftk stensorKind t of
    FTKS _ FTKScalar ->  -- optimized
      RepN . Nested.ssumOuter1 . unRepN $ t
    FTKS _ x ->
      let l = sunravelToList t
          sh = shsTail $ sshape t
      in foldr (addTarget stensorKind) (constantTarget 0 (FTKS sh x)) l
  ssum0 @_ @sh t | SNat <- shsProduct (knownShS @sh)  = case tftk stensorKind t of
    FTKS _ FTKScalar ->  -- optimized
      RepN . Nested.sscalar . Nested.ssumAllPrim . unRepN $ t
    FTKS _ _ ->
      ssum . sflatten $ t
  sdot0 @_ @sh u v | SNat <- shsProduct (knownShS @sh)  =
    RepN $ Nested.sscalar $ Nested.sdot (unRepN u) (unRepN v)
  smatmul2 m1 m2 = RepN $ tmatmul2S (unRepN m1) (unRepN m2)
  -- Performance depends a lot on the number and size of tensors.
  -- If tensors are not tiny, memory taken by underlying vectors matters most
  -- and this implementation is probbaly optimal in this respect
  -- (the only new vectors are created by V.concat, but this is done on demand).
  -- TODO: optimize updateNS and make it consume and forget arguments
  -- one by one to make the above true
  --
  -- Note how ix being in bounds is checked. The semantics of the operation
  -- permits index out of bounds and then no tensors is added at such an index.
  sscatter @_ @shm @shn @shp t f =
    case shsProduct (knownShS @shp `shsAppend` knownShS @shn) of
      SNat ->
        withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
        case tftk stensorKind t of
          FTKS _ x@FTKScalar ->  -- optimized
            withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
            gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
            gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
            let zero = constantTarget 0 (FTKS knownShS x)
                shm = knownShS @shm
                s = shsSize shm
                g ix =
                  let ix2 = f $ fmap RepN ix
                  in if ixInBounds (map unRepN $ toList $ ix2)
                                   (toList $ knownShS @(shp ++ shn))
                     then M.insertWith (V.zipWith (+)) ix2
                            (Nested.stoVector
                             $ tindexNS @_ @shm @shn (unRepN t) ix)
                     else id
                ivs = foldr g M.empty [ fromLinearIdxS fromIntegral shm
                                        $ fromIntegral i
                                      | i <- [0 .. s - 1] ]
            in updateNS @(Rank shp) zero
               $ map (second $ RepN . Nested.sfromVector knownShS)
               $ M.assocs ivs
          FTKS _ x | Dict <- eltDictRep (ftkToStk x) ->
            withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
            gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
            gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
            let zero = constantTarget 0 (FTKS knownShS x)
                shm = knownShS @shm
                s = shsSize shm
                g ix =
                  let ix2 = f $ fmap RepN ix
                  in if ixInBounds (map unRepN $ toList $ ix2)
                                   (toList $ knownShS @(shp ++ shn))
                     then M.insertWith (addTarget stensorKind) ix2
                            (RepN
                             $ tindexNS @_ @shm @shn (unRepN t) ix)
                     else id
                ivs = foldr g M.empty [ fromLinearIdxS fromIntegral shm
                                        $ fromIntegral i
                                      | i <- [0 .. s - 1] ]
            in updateNS @(Rank shp) zero
               $ M.assocs ivs
  sscatter1 = tscatterZ1S
  sfromList @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.sfromListOuter SNat . NonEmpty.map unRepN
      -- TODO: make this strict
  sfromList0N @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . tfromList0NS . map unRepN
  sfromVector @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.sfromListOuter SNat . NonEmpty.fromList . V.toList
    . V.map unRepN
  sfromVector0N @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . tfromList0NS . V.toList . V.map unRepN
  sunravelToList @r | Dict <- eltDictRep (stensorKind @r) =
    map RepN . Nested.stoListOuter . unRepN
  sreplicate @_ @_ @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.sreplicate (SNat :$$ ZSS) . unRepN
  sreplicate0N @r @sh | Refl <- lemAppNil @sh
                      , Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.sreplicate (knownShS @sh) . unRepN
  sappend @r u v | Dict <- eltDictRep (stensorKind @r) =
    RepN $ Nested.sappend (unRepN u) (unRepN v)
  sslice @r @i _ _ | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.sslice (SNat @i) SNat . unRepN
  sreverse @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.srev1 . unRepN
  stranspose @_ @r perm | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.stranspose perm . unRepN
  sreshape @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.sreshape knownShS . unRepN
  sbuild1 @r f | Dict <- eltDictRep (stensorKind @r) =
    RepN $ tbuild1S (unRepN . f . RepN)
  smap0N @r1 @r @sh f v = case (stensorKind @r1, stensorKind @r) of
    (STKScalar{}, STKScalar{}) ->
      RepN $ tmap0NS (unRepN . f . RepN) (unRepN v)
    _ ->  -- TODO: how to call the default implementation?
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
      $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
      $ sbuild @RepN @r @(Rank sh) (f . sindex0 v)
  szipWith0N @r1 @r2 @r @sh f t u =
    case (stensorKind @r1, stensorKind @r2, stensorKind @r) of
      (STKScalar{}, STKScalar{}, STKScalar{}) ->
        RepN $ tzipWith0NS (\v w -> unRepN $ f (RepN v) (RepN w))
                           (unRepN t) (unRepN u)
      _ ->  -- TODO: how to call the default implementation?
        gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
        $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
        $ sbuild @RepN @_ @(Rank sh) (\ix -> f (sindex0 t ix) (sindex0 u ix))
  -- The semantics of the operation permits index out of bounds
  -- and the result of such indexing is def.
  sgather @r @shm @shn @shp t f =
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
    case stensorKind @r of
      STKScalar{} ->  -- optimized
        let shm = knownShS @shm
            s = sizeT @shm
            l = [ Nested.stoVector $ unRepN
                  $ sindex @_ @_ @_ @shn
                      t (f (fmap RepN
                            $ fromLinearIdxS fromIntegral shm i))
                | i <- [0 .. fromIntegral s - 1] ]
        in RepN $ Nested.sfromVector knownShS $ V.concat l
      _ ->
        sbuild @_ @_ @(Rank shm) (\ix -> t !$ f ix)
  sgather1 = tgatherZ1S
  scast = RepN . liftVS (V.map realToFrac) . unRepN
  sfromIntegral = RepN . liftVS (V.map fromIntegral) . unRepN
  szip (RepN (a, b)) = RepN $ Nested.szip a b
  sunzip = RepN . Nested.sunzip . unRepN
  stoScalar = RepN . Nested.sunScalar . unRepN
  sfromScalar = RepN . Nested.sscalar . unRepN

  sscaleByScalar s v =
    RepN $ liftVS (V.map (* Nested.sunScalar (unRepN s))) (unRepN v)
  sdot1In (SNat @n) u v =
    RepN $ Nested.sdot1Inner (Proxy @n) (unRepN u) (unRepN v)

  sfromPrimal = id
  sprimalPart = id
  sdualPart _ = DummyDualTarget
  sD u _ = u
  sScale _ _ = DummyDualTarget

  xshape @r | Dict <- eltDictRep (stensorKind @r) = Nested.mshape . unRepN
  xminIndex = RepN . tminIndexX . unRepN
  xmaxIndex = RepN . tmaxIndexX . unRepN
  xfloor = RepN . liftVX (V.map floor) . unRepN
  xiota @n = let n = valueOf @n
                 t = Nested.mfromList1 $ NonEmpty.map fromInteger
                     $ NonEmpty.fromList [0 .. n - 1]
             in RepN $ Nested.mcast (Nested.SKnown (SNat @n) :!% ZKX) t
  xindex = tindexZX
  xindex0 = tindex0X
  xsum t = case tftk stensorKind t of
    FTKX _ FTKScalar ->  -- optimized
      RepN . Nested.msumOuter1 . unRepN $ t
    FTKX _ x ->
      let l = xunravelToList t
          sh = shxTail $ xshape t
      in foldr (addTarget stensorKind) (constantTarget 0 (FTKX sh x)) l
  xsum0 t =
   case tftk stensorKind t of
    FTKX _ FTKScalar ->  -- optimized
      RepN . Nested.mscalar . Nested.msumAllPrim . unRepN $ t
    FTKX _ _ -> withSNat (shxSize $ xshape t) $ \snat ->
      xsum (xmcast (Nested.SKnown snat :!% ZKX) $ xflatten t)
  xdot0 u v =
    RepN $ Nested.mscalar $ Nested.mdot (unRepN u) (unRepN v)
  xmatmul2 m1 m2 = RepN $ tmatmul2X (unRepN m1) (unRepN m2)
  xscatter @_ @shm @shn @shp sh t f =
    withKnownShX (ssxFromShape sh) $
    withKnownShX (knownShX @shm `ssxAppend` knownShX @shn) $
    gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
    case tftk stensorKind t of
      FTKX _ x@FTKScalar ->  -- optimized
        let zero = constantTarget 0 (FTKX sh x)
            shm = shxTakeSSX (Proxy @shn) (xshape t) (knownShX @shm)
            shDropP = shxDropSSX (xshape t) (knownShX @shm)
            s = shxSize shm
            g ix =
              let ix2 = f $ fmap RepN ix
              in if ixInBounds (map unRepN $ toList $ ix2) (toList sh)
                 then M.insertWith (V.zipWith (+)) ix2
                        (Nested.mtoVector
                         $ tindexNX @_ @shm @shn (unRepN t) ix)
                 else id
            ivs = foldr g M.empty [ fromLinearIdxX fromIntegral shm
                                    $ fromIntegral i
                                  | i <- [0 .. s - 1] ]
        in updateNX @(Rank shp) zero
           $ map (second $ RepN . Nested.mfromVector shDropP)
           $ M.assocs ivs
      FTKX _ x | Dict <- eltDictRep (ftkToStk x) ->
        let zero = constantTarget 0 (FTKX sh x)
            shm = shxTakeSSX (Proxy @shn) (xshape t) (knownShX @shm)
            s = shxSize shm
            g ix =
              let ix2 = f $ fmap RepN ix
              in if ixInBounds (map unRepN $ toList $ ix2) (toList sh)
                 then M.insertWith (addTarget stensorKind) ix2
                        (RepN
                         $ tindexNX @_ @shm @shn (unRepN t) ix)
                 else id
            ivs = foldr g M.empty [ fromLinearIdxX fromIntegral shm
                                    $ fromIntegral i
                                  | i <- [0 .. s - 1] ]
        in updateNX @(Rank shp) zero
           $ M.assocs ivs
  xscatter1 = tscatterZ1X
  xfromList @r @n @sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mcast (Nested.SKnown (SNat @n) :!% knownShX @sh)
    . Nested.mfromListOuter . NonEmpty.map unRepN
      -- TODO: make this strict
  xfromList0N @r sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . tfromList0NX sh . map unRepN
  xfromVector @r @n @sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mcast (Nested.SKnown (SNat @n) :!% knownShX @sh)
    . Nested.mfromListOuter . NonEmpty.fromList . V.toList
    . V.map unRepN
  xfromVector0N @r sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . tfromList0NX sh . V.toList . V.map unRepN
  xunravelToList @r | Dict <- eltDictRep (stensorKind @r) =
    map RepN . Nested.mtoListOuter . unRepN
  xreplicate @_ @_ @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mreplicate (Nested.SKnown SNat :$% ZSX) . unRepN
  xreplicate0N @r @sh sh | Refl <- lemAppNil @sh
                         , Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mreplicate sh . unRepN
  xappend @r u v | Dict <- eltDictRep (stensorKind @r) =
    RepN $ Nested.mappend (unRepN u) (unRepN v)
  xslice @r @i _ _ | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mslice (SNat @i) SNat . unRepN
  xreverse @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mrev1 . unRepN
  xtranspose @_ @r perm | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mtranspose perm . unRepN
  xreshape @r sh | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mreshape sh . unRepN
  xbuild1 @r f | Dict <- eltDictRep (stensorKind @r) =
    RepN $ tbuild1X (unRepN . f . RepN)
  xgather @r @shm @shn @shp sh t f =
    withKnownShX (ssxFromShape sh) $
    withKnownShX (knownShX @shp `ssxAppend` knownShX @shn) $
    gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
    case stensorKind @r of
      STKScalar{} ->  -- optimized
        let shm = shxTakeSSX (Proxy @shn) sh (knownShX @shm)
            s = shxSize shm
            l = [ Nested.mtoVector $ unRepN
                  $ xindex @_ @_ @_ @shn
                      t (f (fmap RepN
                            $ fromLinearIdxX fromIntegral shm i))
                | i <- [0 .. fromIntegral s - 1] ]
        in RepN $ Nested.mfromVector sh $ V.concat l
      _ ->
        xbuild @_ @_ @(Rank shm) sh (\ix -> t `xindex` f ix)
  xgather1 = tgatherZ1X
  xcast = RepN . liftVX (V.map realToFrac) . unRepN
  xfromIntegral = RepN . liftVX (V.map fromIntegral) . unRepN
  xzip (RepN (a, b)) = RepN $ Nested.mzip a b
  xunzip = RepN . Nested.munzip . unRepN
  xtoScalar = RepN . Nested.munScalar . unRepN
  xfromScalar = RepN . Nested.mscalar . unRepN

  xscaleByScalar s v =
    RepN $ liftVX (V.map (* Nested.munScalar (unRepN s))) (unRepN v)
  xdot1In @_ @n u v =
    RepN $ Nested.mdot1Inner (Proxy @(Just n)) (unRepN u) (unRepN v)

  xfromPrimal = id
  xprimalPart = id
  xdualPart _ = DummyDualTarget
  xD u _ = u
  xScale _ _ = DummyDualTarget

  kfloor = RepN . floor . unRepN
  kcast = RepN . realToFrac . unRepN
  kfromIntegral = RepN . fromIntegral . unRepN

  rfromS @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.stoRanked . unRepN
  rfromX @_ @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.mtoRanked . unRepN
  sfromR @_ @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . flip Nested.rcastToShaped knownShS . unRepN
  sfromX @_ @_ @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . flip Nested.mcastToShaped knownShS . unRepN
  xfromR @sh @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.rcastToMixed (knownShX @sh) . unRepN
  xfromS @_ @sh' @r | Dict <- eltDictRep (stensorKind @r) =
    RepN . Nested.scastToMixed (knownShX @sh') . unRepN

  xnestR @sh1 @m @x sh | Dict <- eltDictRep (stensorKind @x) =
    RepN
    . (unsafeCoerce :: Nested.Mixed sh1 (Nested.Mixed (Replicate m Nothing)
                                                      (RepORArray x))
                    -> Nested.Mixed sh1 (Nested.Ranked m (RepORArray x)))
    . Nested.mnest sh
    . unRepN
  xnestS @sh1 @sh2 @x sh | Dict <- eltDictRep (stensorKind @x) =
    RepN
    . (unsafeCoerce :: Nested.Mixed sh1 (Nested.Mixed (MapJust sh2)
                                                      (RepORArray x))
                    -> Nested.Mixed sh1 (Nested.Shaped sh2 (RepORArray x)))
    . Nested.mnest sh
    . unRepN
  xnest @_ @_ @x sh | Dict <- eltDictRep (stensorKind @x) =
    RepN . Nested.mnest sh . unRepN

  xunNestR @sh1 @m @x =
    RepN
    . Nested.munNest
    . (unsafeCoerce :: Nested.Mixed sh1 (Nested.Ranked m (RepORArray x))
                    -> Nested.Mixed sh1 (Nested.Mixed (Replicate m Nothing)
                                                      (RepORArray x)))
    . unRepN
  xunNestS @sh1 @sh2 @x =
    RepN
    . Nested.munNest
    . (unsafeCoerce :: Nested.Mixed sh1 (Nested.Shaped m (RepORArray x))
                    -> Nested.Mixed sh1 (Nested.Mixed (MapJust sh2)
                                                      (RepORArray x)))
    . unRepN
  xunNest = RepN . Nested.munNest . unRepN

  tpair u v = RepN (unRepN u, unRepN v)
  tproject1 = RepN . fst . unRepN
  tproject2 = RepN . snd . unRepN
  tftk stk (RepN t) = tftkG stk t
  tcond _ b u v = if b then u else v
  tfromPrimal _ t = t
  tprimalPart _ = id
  tdualPart _stk _t = DummyDualTarget
  tD _stk t _d = t
  tconcrete _ = id
  tlambda _ f x = unRepN $ unHFun f $ RepN x
  tApply f x = RepN $ f $ unRepN x
  -- The code for drevDt and dfwd in this instance is similar as for the
  -- ADVal ranked instance, because the type family instance is the same.
  drev @x _ftk h =
    let rf :: RepORArray x -> RepORArray (ADTensorKind x)
        rf !a = unRepN $ fst $ crevOnHVector Nothing (unHFun h) (RepN a)
    in rf
  drevDt @x @z _ftk h =
    let rf :: RepORArray (TKProduct (ADTensorKind z) x) -> RepORArray (ADTensorKind x)
        rf !db_a = unRepN $ fst
                   $ crevOnHVector (Just $ RepN $ fst db_a) (unHFun h) (RepN $ snd db_a)
    in rf
  dfwd @x @z _shs h =
    let df :: RepORArray (TKProduct (ADTensorKind x) x)
          -> RepORArray (ADTensorKind z)
        df !da_a = unRepN $ fst
                   $ cfwdOnHVector (RepN $ snd da_a) (unHFun h) (RepN $ fst da_a)
    in df
  rfold f x0 as = foldl' f x0 (runravelToList as)
  rscan f x0 as =
    rfromList $ NonEmpty.fromList $ scanl' f x0 (runravelToList as)
  sfold f x0 as = foldl' f x0 (sunravelToList as)
  sscan f x0 as =
    sfromList $ NonEmpty.fromList $ scanl' f x0 (sunravelToList as)
  -- The eta-expansion below is needed for typing.
  dmapAccumR _ k accShs bShs eShs f acc0 es =
    oRdmapAccumR k accShs bShs eShs f acc0 es
  dmapAccumRDer _ k accShs bShs eShs f _df _rf acc0 es =
    oRdmapAccumR k accShs bShs eShs (\ !(RepN a) !(RepN b) -> RepN $ f (a, b)) acc0 es
  dmapAccumL _ k accShs bShs eShs f acc0 es =
    oRdmapAccumL k accShs bShs eShs f acc0 es
  dmapAccumLDer _ k accShs bShs eShs f _df _rf acc0 es =
    oRdmapAccumL k accShs bShs eShs (\ !(RepN a) !(RepN b) -> RepN $ f (a, b)) acc0 es

instance Eq (RepORArray y) => Eq (RepN y) where
  RepN u == RepN v = u == v

instance Ord (RepORArray y) => Ord (RepN y) where
  RepN u <= RepN v = u <= v

instance Num (RepORArray y) => Num (RepN y) where
  RepN t + RepN u = RepN $ t + u
  RepN t - RepN u = RepN $ t - u
  RepN t * RepN u = RepN $ t * u
  negate (RepN t) = RepN $ negate t
  abs (RepN t) = RepN $ abs t
  signum (RepN t) = RepN $ signum t
  fromInteger = RepN . fromInteger

instance IntegralF (RepORArray y) => IntegralF (RepN y) where
  quotF (RepN t) (RepN u) = RepN $ quotF t u
  remF (RepN t) (RepN u) = RepN $ remF t u

instance Fractional (RepORArray y) => Fractional (RepN y) where
  RepN u / RepN v = RepN $ u / v
  recip (RepN t) = RepN $ recip t
  fromRational = RepN . fromRational

instance Floating (RepORArray y) => Floating (RepN y) where
  pi = RepN pi
  exp (RepN t) = RepN $ exp t
  log (RepN t) = RepN $ log t
  sqrt (RepN t) = RepN $ sqrt t
  (**) (RepN t) (RepN u) = RepN $ (**) t u
  logBase (RepN t) (RepN u) = RepN $ logBase t u
  sin (RepN t) = RepN $ sin t
  cos (RepN t) = RepN $ cos t
  tan (RepN t) = RepN $ tan t
  asin (RepN t) = RepN $ asin t
  acos (RepN t) = RepN $ acos t
  atan (RepN t) = RepN $ atan t
  sinh (RepN t) = RepN $ sinh t
  cosh (RepN t) = RepN $ cosh t
  tanh (RepN t) = RepN $ tanh t
  asinh (RepN t) = RepN $ asinh t
  acosh (RepN t) = RepN $ acosh t
  atanh (RepN t) = RepN $ atanh t

instance RealFloatF (RepORArray y) => RealFloatF (RepN y) where
  atan2F (RepN t) (RepN u) = RepN $ atan2F t u

ravel :: forall k y. TensorKind y
      => SNat k -> [RepN y]
      -> RepN (BuildTensorKind k y)
ravel k@SNat t = case stensorKind @y of
  STKScalar{} -> sfromList $ sfromScalar <$> NonEmpty.fromList t
  STKR SNat x | Dict <- lemTensorKindOfSTK x ->
    rfromList $ NonEmpty.fromList t
  STKS sh x | Dict <- lemTensorKindOfSTK x ->
    withKnownShS sh $ sfromList $ NonEmpty.fromList t
  STKX sh x | Dict <- lemTensorKindOfSTK x ->
    withKnownShX sh $ xfromList $ NonEmpty.fromList t
  STKProduct @y1 @y2 stk1 stk2
    | Dict <- lemTensorKindOfSTK stk1
    , Dict <- lemTensorKindOfSTK stk2
    , Dict <- lemTensorKindOfBuild k (stensorKind @y1)
    , Dict <- lemTensorKindOfBuild k (stensorKind @y2) ->
      let (lt1, lt2) = unzip $ map (\u -> (tproject1 u, tproject2 u)) t
      in tpair (ravel k lt1) (ravel k lt2)

unravel :: forall k y. TensorKind y
        => SNat k -> RepN (BuildTensorKind k y)
        -> [RepN y]
unravel k@SNat t = case stensorKind @y of
  STKScalar{} -> map stoScalar $ sunravelToList t
  STKR SNat x | Dict <- lemTensorKindOfSTK x ->
    runravelToList t
  STKS sh x | Dict <- lemTensorKindOfSTK x ->
    withKnownShS sh $ sunravelToList t
  STKX sh x | Dict <- lemTensorKindOfSTK x ->
    withKnownShX sh $ xunravelToList t
  STKProduct @y1 @y2 stk1 stk2
    | Dict <- lemTensorKindOfSTK stk1
    , Dict <- lemTensorKindOfSTK stk2
    , Dict <- lemTensorKindOfBuild k (stensorKind @y1)
    , Dict <- lemTensorKindOfBuild k (stensorKind @y2) ->
      let lt1 = unravel k $ tproject1 t
          lt2 = unravel k $ tproject2 t
      in zipWith tpair lt1 lt2

oRdmapAccumR
  :: forall k accShs bShs eShs.
     (TensorKind accShs, TensorKind bShs, TensorKind eShs)
  => SNat k
  -> FullTensorKind accShs
  -> FullTensorKind bShs
  -> FullTensorKind eShs
  -> (RepN accShs -> RepN eShs
      -> RepN (TKProduct accShs bShs))
  -> RepN accShs
  -> RepN (BuildTensorKind k eShs)
  -> RepN (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumR k _ bShs _ f acc0 es
 | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) = case sNatValue k of
  0 -> tpair acc0 (treplicate k (stensorKind @bShs) (constantTarget 0 bShs))
  _ ->
    let g a b = let res = f a b
                in (tproject1 res, tproject2 res)
        (xout, lout) = mapAccumR g acc0 (unravel k es)
    in tpair xout (ravel k lout)
      -- TODO: reimplement not with Haskell's mapAccumR to avoid the ravels

oRdmapAccumL
  :: forall k accShs bShs eShs.
     (TensorKind accShs, TensorKind bShs, TensorKind eShs)
  => SNat k
  -> FullTensorKind accShs
  -> FullTensorKind bShs
  -> FullTensorKind eShs
  -> (RepN accShs -> RepN eShs
      -> RepN (TKProduct accShs bShs))
  -> RepN accShs
  -> RepN (BuildTensorKind k eShs)
  -> RepN (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumL k _ bShs _ f acc0 es
 | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) = case sNatValue k of
  0 -> tpair acc0 (treplicate k (stensorKind @bShs) (constantTarget 0 bShs))
  _ ->
    let g a b = let res = f a b
                in (tproject1 res, tproject2 res)
        (xout, lout) = mapAccumL g acc0 (unravel k es)
    in tpair xout (ravel k lout)

instance (y ~ TKR n r, TensorKind y)
         => AdaptableHVector RepN (RepN (TKR n r)) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector RepN (RepN (TKR n Double)) #-}
  type X (RepN (TKR n r)) = TKR n r
  toHVectorOf = id
  fromHVector _aInit t = Just t
  fromHVectorAD aInit t =
    let stk = stensorKind @y
    in case sameSTK stk (aDSTK stk) of
      Just Refl -> Just t
      _ -> Just (constantTarget 0 $ tftkG stk (unRepN aInit))

instance ForgetShape (RepN (TKR n r)) where
  type NoShape (RepN (TKR n r)) = RepN (TKR n r)
  forgetShape = id

instance (y ~ TKS sh r, TensorKind y)
         => AdaptableHVector RepN (RepN (TKS sh r)) where
  {-# SPECIALIZE instance
      KnownShS sh
      => AdaptableHVector RepN (RepN (TKS sh Double)) #-}
  type X (RepN (TKS sh r)) = TKS sh r
  toHVectorOf = id
  fromHVector _aInit t = Just t
  fromHVectorAD aInit t =
    let stk = stensorKind @y
    in case sameSTK stk (aDSTK stk) of
      Just Refl -> Just t
      _ -> Just (constantTarget 0 $ tftkG stk (unRepN aInit))

instance GoodScalar r
         => ForgetShape (RepN (TKS sh r)) where
  type NoShape (RepN (TKS sh r)) = RepN (TKR (Rank sh) r)  -- key case
  forgetShape = RepN . Nested.stoRanked . unRepN

instance (KnownShS sh, GoodScalar r, Fractional r, Random r)
         => RandomHVector (RepN (TKS sh r)) where
  randomVals @g range g =
    let createRandomVector :: Int -> g -> Nested.Shaped sh r
        createRandomVector n seed =
          unRepN (srepl (2 * realToFrac range))
          * (Nested.sfromVector knownShS (V.fromListN n (randoms seed))
             - unRepN (srepl 0.5))
        (g1, g2) = splitGen g
        arr = createRandomVector (sizeP (Proxy @sh)) g1
    in (RepN arr, g2)
{-
-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: FullTensorKind TKUntyped
  -> RepN TKUntyped
  -> Maybe (RepN TKUntyped)
  -> Delta RepN TKUntyped
  -> RepN TKUntyped #-}
{-# SPECIALIZE evalRevFromnMap
  :: EvalState RepN -> EvalState RepN #-}
-}

-- TODO: check what the following did in tsum0R and if worth emulating
-- (also in sum1Inner and extremum and maybe tdot0R):
-- LA.sumElements $ OI.toUnorderedVectorT sh t
{-
tdot0R t u = OR.toVector t LA.<.> OR.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0R (t * u) -}


-- * Internal definitions

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall n m x. (KnownNat n, KnownNat m, TensorKind x)
         => RepN (TKR2 (n + m) x) -> [(IxROf RepN n, RepN (TKR2 m x))]
         -> RepN (TKR2 (n + m) x)
updateNR arr upd = case stensorKind @x of
  STKScalar{} ->  -- optimized
    let values = Nested.rtoVector $ unRepN arr
        sh = rshape arr
        f !t (ix, u) =
          let v = Nested.rtoVector $ unRepN u
              i = fromIntegral $ unRepN $ toLinearIdx @n @m fromIntegral sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in RepN $ Nested.rfromVector sh (foldl' f values upd)
  _ ->
    let arrNested = rnest (SNat @n) arr
        shNested = rshape arrNested
        f i v = case lookup (fromLinearIdx
                               @n (RepN . fromIntegral)
                               shNested ((RepN . fromIntegral) i)) upd of
          Just u -> rnest (SNat @0) u
          Nothing -> v
    in runNest $ rfromList0N shNested
       $ imap f $ runravelToList $ rflatten arrNested

tminIndexR
  :: forall r r2 n.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2, KnownNat n)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
tminIndexR =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . Nested.Internal.Shape.ixrHead
          . Nested.rminIndexPrim
  in Nested.rrerank SNat ZSR f

tmaxIndexR
  :: forall r r2 n.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2, KnownNat n)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
tmaxIndexR =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . Nested.Internal.Shape.ixrHead
          . Nested.rmaxIndexPrim
  in Nested.rrerank SNat ZSR f

-- We could generalize by unwinding and only then doing the PrimElt things,
-- but we'd need a type family that says "replace this underlying scalars
-- by this one", which makes things too complicated.
--
-- We could also expose `liftVR` in the user API, but in addition
-- to the main function argument, such as floor or cast, it'd need the function's
-- derivative, just as with mapAccums. Maybe it's better to generalize even more
-- and permit arbitrary extra ops if given their derivatives.
liftVR
  :: (Nested.PrimElt r1, Nested.PrimElt r2)
  => (VS.Vector r1 -> VS.Vector r2)
  -> Nested.Ranked n r1 -> Nested.Ranked n r2
liftVR f =
  Nested.Internal.arithPromoteRanked
    (Nested.Internal.Mixed.mliftNumElt1
       (`Mixed.Internal.Arith.liftVEltwise1` f))

ixInBounds :: [Int64] -> [Int] -> Bool
ixInBounds ix sh =
  and $ zipWith (\i dim -> 0 <= i && i < fromIntegral dim) ix sh

tindexNR
  :: (Nested.Elt r, Show r, KnownNat m, KnownNat n)
  => Nested.Ranked (m + n) r -> IxR m Int64 -> Nested.Ranked n r
tindexNR v ix = let sh = Nested.rshape v
                    !_A = assert (ixInBounds (toList ix) (toList sh)
                                  `blame` (v, ix)) ()
                in Nested.rindexPartial v (fmap fromIntegral ix)
{- TODO: benchmark if this is faster enough for its complexity;
         probably not, becasue orthotope's index does no canonicalization either
tindexNR v@(RS.A (RG.A sh OI.T{strides, offset, values})) ix =
  let l = indexToList ix
      linear = offset + sum (zipWith (*) (map fromIntegral l) strides)
      plen = valueOf @m  -- length of prefix being indexed out of
      !_A = assert (ixInBounds l sh `blame` (ix, sh, v)) ()
  in
    RS.A (RG.A (drop plen sh) OI.T{ strides = drop plen strides
                                  , offset = linear
                                  , values })
-}

tindexZR
  :: forall r m n. (TensorKind r, KnownNat m, KnownNat n)
  => RepN (TKR2 (m + n) r) -> IxROf RepN m -> RepN (TKR2 n r)
tindexZR v ixRepN | Dict <- showDictRep (stensorKind @r)
                  , Dict <- eltDictRep (stensorKind @r) =
  let ix = fmap unRepN ixRepN
  in case tftk stensorKind v of
    FTKR sh x | SNat <- shrRank sh ->
     if ixInBounds (toList ix) (toList sh)
     then RepN $ tindexNR (unRepN v) ix
     else constantTarget def (FTKR (dropShape @m sh) x)

tindex0R
  :: forall r m. (TensorKind r, KnownNat m)
  => RepN (TKR2 m r) -> IxROf RepN m -> RepN (TKR2 0 r)
tindex0R v ixRepN | Dict <- eltDictRep (stensorKind @r) =
  let ix = fmap unRepN ixRepN
  in case tftk stensorKind v of
    FTKR sh x ->
     if ixInBounds (toList ix) (toList sh)
     then rscalar $ Nested.rindex (unRepN v) (fmap fromIntegral ix)
     else constantTarget def (FTKR ZSR x)
{- TODO: see above
tindex0R (RS.A (RG.A _ OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral $ indexToList ix)
                                        strides))
-}

tmatmul2R
  :: (Nested.PrimElt r, Numeric r)
  => Nested.Ranked 2 r -> Nested.Ranked 2 r -> Nested.Ranked 2 r
tmatmul2R t u =
  let t2 = Nested.rtoVector t
      u2 = Nested.rtoVector u
      (trows, tcols) = case Foldable.toList $ Nested.rshape t of
        [r, c] -> (r, c)
        _ -> error "tmatmul2R: impossible wrong shape"
      ucols = case Foldable.toList $ Nested.rshape u of
        [_, c] -> c
        _ -> error "tmatmul2R: impossible wrong shape"
  in Nested.rfromVector (IsList.fromList [trows, ucols]) $ LA.flatten
     $ LA.reshape tcols t2 LA.<> LA.reshape ucols u2

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probbaly optimal in this respect
-- (the only new vectors are created by V.concat, but this is done on demand).
-- TODO: optimize updateNR and make it consume and forget arguments
-- one by one to make the above true
--
-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensors is added at such an index.
tscatterZR :: forall m p n r.
              (KnownNat p, KnownNat m, KnownNat n, TensorKind r)
           => IShR (p + n) -> RepN (TKR2 (m + n) r)
           -> (IxROf RepN m -> IxROf RepN p)
           -> RepN (TKR2 (p + n) r)
tscatterZR sh t f
 | Dict <- eltDictRep (stensorKind @r) = case tftk stensorKind t of
  FTKR _ x@FTKScalar ->  -- optimized
    let zero = constantTarget 0 (FTKR sh x)
        (shm, shDropP) = splitAt_Shape @m $ rshape t
        s = shrSize shm
        g ix =
          let ix2 = f $ fmap RepN ix
          in if ixInBounds (map unRepN $ toList ix2) (toList sh)
             then M.insertWith (V.zipWith (+)) ix2
                               (Nested.rtoVector $ unRepN t `tindexNR` ix)
             else id
        ivs = foldr g M.empty [ fromLinearIdx fromIntegral shm i
                              | i <- [0 .. fromIntegral s - 1] ]
    in updateNR zero
       $ map (second $ RepN . Nested.rfromVector shDropP)
       $ M.assocs ivs
  FTKR _ x | Dict <- showDictRep (ftkToStk x) ->
    let zero = constantTarget 0 (FTKR sh x)
        (shm, _) = splitAt_Shape @m $ rshape t
        s = shrSize shm
        g ix =
          let ix2 = f $ fmap RepN ix
          in if ixInBounds (map unRepN $ toList ix2) (toList sh)
             then M.insertWith (addTarget stensorKind) ix2
                               (RepN $ unRepN t `tindexNR` ix)
             else id
        ivs = foldr g M.empty [ fromLinearIdx fromIntegral shm i
                              | i <- [0 .. fromIntegral s - 1] ]
    in updateNR zero
       $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling Nested.rfromVector
-- or optimize tscatterNR and instantiate it instead
tscatterZ1R :: (TensorKind r, KnownNat p, KnownNat n)
            => IShR (p + n) -> RepN (TKR2 (1 + n) r)
            -> (IntOf RepN -> IxROf RepN p)
            -> RepN (TKR2 (p + n) r)
tscatterZ1R sh t f = case tftk stensorKind t of
  FTKR _ x ->
    let zero = constantTarget 0 (FTKR sh x)
        lt = runravelToList t
        g i ti = let ix2 = f $ RepN $ fromIntegral i
                 in if ixInBounds (map unRepN $ toList ix2) (toList sh)
                    then updateNR zero [(ix2, ti)]
                    else zero
        lu = imap g lt
    in foldr (addTarget stensorKind) zero lu

-- TODO: make this strict
tfromList0NR
  :: Nested.KnownElt r
  => IShR n -> [Nested.Ranked 0 r] -> Nested.Ranked n r
tfromList0NR sh l = case NonEmpty.nonEmpty l of
  Nothing -> Nested.rreshape sh Nested.remptyArray
  Just nl -> Nested.rfromListLinear sh $ NonEmpty.map Nested.runScalar nl

tbuild1R
  :: forall n r. Nested.Elt r
  => Int -> (Int64 -> Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tbuild1R k f =
  Nested.rfromListOuter
  $ NonEmpty.map f
  $ NonEmpty.fromList [0 .. fromIntegral k - 1]  -- hope this fuses

tmap0NR
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r) -> Nested.Ranked n r1 -> Nested.Ranked n r
tmap0NR f =
  Nested.Internal.arithPromoteRanked
    (Nested.Internal.Mixed.mliftPrim (Nested.runScalar . f . Nested.rscalar ))
      -- too slow: tbuildNR (Nested.rshape v) (\ix -> f $ v `tindexNR` ix)

tzipWith0NR
  :: (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r2 -> Nested.Ranked 0 r)
  -> Nested.Ranked n r1 -> Nested.Ranked n r2 -> Nested.Ranked n r
tzipWith0NR f =
  Nested.Internal.arithPromoteRanked2
    (Nested.Internal.Mixed.mliftPrim2
       (\x y -> Nested.runScalar $ f (Nested.rscalar x) (Nested.rscalar y)))

-- The semantics of the operation permits index out of bounds
-- and the result of such indexing is def.
tgatherZR :: forall m p n r.
             (KnownNat m, KnownNat p, KnownNat n, TensorKind r)
          => IShR (m + n) -> RepN (TKR2 (p + n) r)
          -> (IxROf RepN m -> IxROf RepN p)
          -> RepN (TKR2 (m + n) r)
tgatherZR sh t f = case stensorKind @r of
  STKScalar{} ->  -- optimized
    let shm = takeShape @m sh
        s = shrSize shm
        l = [ Nested.rtoVector $ unRepN
              $ t `rindex` f (fmap RepN $ fromLinearIdx fromIntegral shm i)
            | i <- [0 .. fromIntegral s - 1] ]
    in RepN $ Nested.rfromVector sh $ V.concat l
  _ -> rbuild sh (\ix -> t ! f ix)

tgatherZ1R :: forall p n r.
              (KnownNat p, KnownNat n, TensorKind r)
           => Int -> RepN (TKR2 (p + n) r)
           -> (IntOf RepN -> IxROf RepN p)
           -> RepN (TKR2 (1 + n) r)
tgatherZ1R k t f = case stensorKind @r of
  STKScalar{} ->  -- optimized
    rfromList $ NonEmpty.map (\i -> t `rindex` f (RepN i))
                             (NonEmpty.fromList [0 .. fromIntegral k - 1])
  _ -> rbuild1 k (\ix -> t ! f ix)

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNS :: forall n sh r.
            ( TensorKind r, KnownShS sh, KnownShS (Drop n sh)
            , KnownShS (Take n sh) )
         => RepN (TKS2 sh r)
         -> [(IxSOf RepN (Take n sh), RepN (TKS2 (Drop n sh) r))]
         -> RepN (TKS2 sh r)
updateNS arr upd = case stensorKind @r of
  STKScalar{} ->
    let values = Nested.stoVector $ unRepN arr
        sh = knownShS @sh
        f !t (ix, u) =
          let v = Nested.stoVector $ unRepN u
              i = gcastWith (unsafeCoerceRefl
                             :: sh :~: Take n sh ++ Drop n sh)
                  $ fromIntegral $ unRepN
                  $ toLinearIdxS @(Take n sh) @(Drop n sh)
                                 fromIntegral sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in RepN $ Nested.sfromVector knownShS (foldl' f values upd)
  _ -> case shsProduct (knownShS @(Take n sh)) of
    SNat ->
      gcastWith (unsafeCoerceRefl :: sh :~: Take n sh ++ Drop n sh) $
      let arrNested = snest (knownShS @(Take n sh)) arr
          shNested = sshape arrNested
          f i v = case lookup (fromLinearIdxS
                                 @(Take n sh) (RepN . fromIntegral)
                                 shNested ((RepN . fromIntegral) i)) upd of
            Just u -> snest (knownShS @'[]) u
            Nothing -> v
      in sunNest @_ @(Take n sh) $ sfromList0N
         $ imap f $ sunravelToList $ sflatten arrNested

tminIndexS
  :: forall n sh r r2.
     ( Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2, KnownShS sh
     , KnownShS (Init (n ': sh)) )
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) r2
tminIndexS =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] r2
      f = Nested.sscalar . fromIntegral . Nested.Internal.Shape.ixsHead
          . Nested.sminIndexPrim
  in case sameShape @sh @'[] of
    Just Refl -> f @n
    _ ->
      let sh = toList $ knownShS @sh
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat _proxy) ->
              gcastWith (unsafeCoerceRefl
                         :: Init (n ': sh) ++ '[m] :~: n ': sh) $
              gcastWith (unsafeCoerceRefl
                         :: Init (n ': sh) :~: Init (n ': sh) ++ '[]) $
              Nested.srerank @'[m] @'[] @(Init (n ': sh)) knownShS knownShS (f @m)
            Nothing -> error "tminIndexS: impossible someNatVal error"
        Nothing -> error "tminIndexS: impossible someNatVal error"

tmaxIndexS
  :: forall n sh r r2.
     ( Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2, KnownShS sh
     , KnownShS (Init (n ': sh)) )
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) r2
tmaxIndexS =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] r2
      f = Nested.sscalar . fromIntegral . Nested.Internal.Shape.ixsHead
          . Nested.smaxIndexPrim
  in case sameShape @sh @'[] of
    Just Refl -> f @n
    _ ->
      let sh = toList $ knownShS @sh
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat _proxy) ->
              gcastWith (unsafeCoerceRefl
                         :: Init (n ': sh) ++ '[m] :~: n ': sh) $
              gcastWith (unsafeCoerceRefl
                         :: Init (n ': sh) :~: Init (n ': sh) ++ '[]) $
              Nested.srerank @'[m] @'[] @(Init (n ': sh)) knownShS knownShS (f @m)
            Nothing -> error "tmaxIndexS: impossible someNatVal error"
        Nothing -> error "tmaxIndexS: impossible someNatVal error"

liftVS
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r
liftVS f =
  Nested.Internal.arithPromoteShaped
    (Nested.Internal.Mixed.mliftNumElt1
       (`Mixed.Internal.Arith.liftVEltwise1` f))

tindexNS
  :: Nested.Elt r
  => Nested.Shaped (sh1 ++ sh2) r -> IxS sh1 Int64 -> Nested.Shaped sh2 r
tindexNS v ix = Nested.sindexPartial v (fmap fromIntegral ix)
{- TODO
tindexNS (SS.A (SG.A OI.T{strides, offset, values})) ix =
  let l = ShapedList.indexToList ix
      linear = offset + sum (zipWith (*) (map fromIntegral l) strides)
      plen = length l  -- length of prefix being indexed out of
  in
    SS.A (SG.A OI.T{ strides = drop plen strides
                   , offset = linear
                   , values })
-}

-- Note that after vectorization, the index may not fit within
-- the type-level shape, which we catch in the @ixInBounds@
-- and return def, so it's fine. Similarly in gather and scatter.
tindexZS
  :: forall r sh1 sh2. (TensorKind r, KnownShS sh1, KnownShS sh2)
  => RepN (TKS2 (sh1 ++ sh2) r) -> IxSOf RepN sh1 -> RepN (TKS2 sh2 r)
tindexZS v ixRepN | Dict <- eltDictRep (stensorKind @r) =
  let ix = fmap unRepN ixRepN
  in withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
     case tftk stensorKind v of
       FTKS sh x ->
         if ixInBounds (toList ix) (toList sh)
         then RepN $ tindexNS (unRepN v) ix
         else constantTarget def (FTKS knownShS x)

tindex0S
  :: forall r sh. (TensorKind r, KnownShS sh)
  => RepN (TKS2 sh r) -> IxSOf RepN sh -> RepN (TKS2 '[] r)
tindex0S v ixRepN | Dict <- eltDictRep (stensorKind @r) =
  let ix = fmap unRepN ixRepN
  in case tftk stensorKind v of
    FTKS sh x ->
      if ixInBounds (toList ix) (toList sh)
      then sscalar $ Nested.sindex (unRepN v) (fmap fromIntegral ix)
      else constantTarget def (FTKS ZSS x)
{- TODO: benchmark if this is faster enough for its complexity;
         probably not, becasue orthotope's index does no canonicalization either
tindex0S (SS.A (SG.A OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral
                                         $ ShapedList.indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way
-}

tmatmul2S
  :: forall m n p r.
     (Nested.PrimElt r, KnownNat m, KnownNat n, KnownNat p, Numeric r)
  => Nested.Shaped '[m, n] r -> Nested.Shaped '[n, p] r -> Nested.Shaped '[m, p] r
tmatmul2S t u =
  let t2 = Nested.stoVector t
      u2 = Nested.stoVector u
  in Nested.sfromVector knownShS $ LA.flatten
     $ LA.reshape (valueOf @n) t2 LA.<> LA.reshape (valueOf @p) u2

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OS.fromVector
-- or optimize tscatterNS and instantiate it instead
tscatterZ1S
  :: forall r n2 shn shp.
     (TensorKind r, KnownNat n2, KnownShS shn, KnownShS shp)
  => RepN (TKS2 (n2 ': shn) r)
  -> (IntOf RepN -> IxSOf RepN shp)
  -> RepN (TKS2 (shp ++ shn) r)
tscatterZ1S t f = case shsProduct (knownShS @shp `shsAppend` knownShS @shn) of
  SNat -> case tftk stensorKind t of
    FTKS _ x ->
      withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
      gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
      gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
      let zero = constantTarget 0 (FTKS knownShS x)
          lt = sunravelToList t
          g i ti = let ix2 = f $ RepN $ fromIntegral i
                   in if ixInBounds (map unRepN $ toList ix2)
                                    (toList $ knownShS @(shp ++ shn))
                      then updateNS @(Rank shp) zero [(ix2, ti)]
                      else zero
          lu = imap g lt
      in foldr (addTarget stensorKind) zero lu

-- TODO: make this strict
tfromList0NS
  :: forall r sh. (Nested.KnownElt r, KnownShS sh, KnownNat (Nested.Product sh))
  => [Nested.Shaped '[] r] -> Nested.Shaped sh r
tfromList0NS l = case NonEmpty.nonEmpty l of
  Nothing -> case sameNat (Proxy @(Nested.Product sh)) (Proxy @0) of
    Just Refl -> Nested.sreshape (knownShS @sh)
                 $ Nested.semptyArray (knownShS @sh)
    Nothing -> error "tfromList0NS: empty list, but not shape"
  Just nl -> Nested.sfromListLinear knownShS $ NonEmpty.map Nested.sunScalar nl

tbuild1S
  :: forall n sh r. (KnownNat n, Nested.Elt r)
  => (Int64 -> Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tbuild1S f =
  let k = valueOf @n
  in Nested.sfromListOuter SNat
     $ NonEmpty.map f
     $ NonEmpty.fromList [0 .. k - 1]  -- hope this fuses

tmap0NS
  :: forall r1 r sh. (Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r) -> Nested.Shaped sh r1 -> Nested.Shaped sh r
tmap0NS f =
  Nested.Internal.arithPromoteShaped
    (Nested.Internal.Mixed.mliftPrim (Nested.sunScalar . f . Nested.sscalar))
      -- too slow: tbuildNS (tshapeS v) (\ix -> f $ v `tindexNS` ix)

tzipWith0NS
  :: forall r1 r2 r sh. (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r2 -> Nested.Shaped '[] r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r2 -> Nested.Shaped sh r
tzipWith0NS f =
  Nested.Internal.arithPromoteShaped2
    (Nested.Internal.Mixed.mliftPrim2
       (\x y -> Nested.sunScalar $ f (Nested.sscalar x) (Nested.sscalar y)))

tgatherZ1S
  :: forall r n2 shn shp.
     (TensorKind r, KnownNat n2, KnownShS shn, KnownShS shp)
  => RepN (TKS2 (shp ++ shn) r)
  -> (IntOf RepN -> IxSOf RepN shp)
  -> RepN (TKS2 (n2 ': shn) r)
tgatherZ1S t f =
  withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
  case stensorKind @r of
    STKScalar{} ->  -- optimized
      sfromList $ NonEmpty.map (\i -> t !$ f (RepN i))
                               (NonEmpty.fromList [0 .. valueOf @n2 - 1])
    _ -> sbuild1 (\ix -> t !$ f ix)

updateNX :: forall n sh r.
            (TensorKind r, KnownShX (Drop n sh), KnownShX (Take n sh))
         => RepN (TKX2 sh r)
         -> [(IxXOf RepN (Take n sh), RepN (TKX2 (Drop n sh) r))]
         -> RepN (TKX2 sh r)
updateNX arr upd = case stensorKind @r of
  STKScalar{} ->
    let values = Nested.mtoVector $ unRepN arr
        sh = xshape arr
        f !t (ix, u) =
          let v = Nested.mtoVector $ unRepN u
              i = gcastWith (unsafeCoerceRefl
                             :: sh :~: Take n sh ++ Drop n sh)
                  $ fromIntegral $ unRepN
                  $ toLinearIdxX @(Take n sh) @(Drop n sh)
                                 fromIntegral sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in RepN $ Nested.mfromVector (xshape arr) (foldl' f values upd)
  _ | Dict <- eltDictRep (stensorKind @r) ->
      gcastWith (unsafeCoerceRefl :: sh :~: Take n sh ++ Drop n sh) $
      let arrNested = xnest (knownShX @(Take n sh)) arr
          shNested = xshape arrNested
          f i v = case lookup (fromLinearIdxX
                                 @(Take n sh) (RepN . fromIntegral)
                                 shNested ((RepN . fromIntegral) i)) upd of
            Just u -> xnest (knownShX @'[]) u
            Nothing -> v
      in withSNat (shxSize shNested) $ \snat ->
           xunNest @_ @(Take n sh) $ xfromList0N shNested
           $ imap f $ xunravelToList
           $ RepN $ Nested.mcast (Nested.SKnown snat :!% ZKX)
           $ unRepN $ xflatten arrNested

tminIndexX
  :: forall mn sh r r2.
     ( Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2, KnownShX sh
     , KnownShX (Init (mn ': sh)) )
  => Nested.Mixed (mn ': sh) r -> Nested.Mixed (Init (mn ': sh)) r2
tminIndexX t =
  let f :: Nested.Mixed '[mm] r -> Nested.Mixed '[] r2
      f = Nested.mscalar . fromIntegral . ixxHead
          . Nested.mminIndexPrim
  in case testEquality (knownShX @sh) ZKX of
    Just Refl -> f @mn t
    _ ->
      let sh = toList $ shxTail $ Nested.mshape t
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat _proxy) ->
              gcastWith (unsafeCoerceRefl
                         :: Init (mn ': sh) ++ '[Just m] :~: mn ': sh) $
              gcastWith (unsafeCoerceRefl
                         :: Init (mn ': sh) :~: Init (mn ': sh) ++ '[]) $
              Nested.mrerank @'[Just m] @'[] @(Init (mn ': sh)) knownShX ZSX (f @(Just m)) t
            Nothing -> error "tminIndexX: impossible someNatVal error"
        Nothing -> error "tminIndexX: impossible someNatVal error"

tmaxIndexX
  :: forall mn sh r r2.
     ( Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2, KnownShX sh
     , KnownShX (Init (mn ': sh)) )
  => Nested.Mixed (mn ': sh) r -> Nested.Mixed (Init (mn ': sh)) r2
tmaxIndexX t =
  let f :: Nested.Mixed '[mm] r -> Nested.Mixed '[] r2
      f = Nested.mscalar . fromIntegral . ixxHead
          . Nested.mmaxIndexPrim
  in case testEquality (knownShX @sh) ZKX of
    Just Refl -> f @mn t
    _ ->
      let sh = toList $ shxTail $ Nested.mshape t
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat _proxy) ->
              gcastWith (unsafeCoerceRefl
                         :: Init (mn ': sh) ++ '[Just m] :~: mn ': sh) $
              gcastWith (unsafeCoerceRefl
                         :: Init (mn ': sh) :~: Init (mn ': sh) ++ '[]) $
              Nested.mrerank @'[Just m] @'[] @(Init (mn ': sh)) knownShX ZSX (f @(Just m)) t
            Nothing -> error "tminIndexX: impossible someNatVal error"
        Nothing -> error "tminIndexX: impossible someNatVal error"

liftVX
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Mixed sh r1 -> Nested.Mixed sh r
liftVX f =
  Nested.Internal.Mixed.mliftNumElt1
    (`Mixed.Internal.Arith.liftVEltwise1` f)

tindexNX
  :: Nested.Elt r
  => Nested.Mixed (sh1 ++ sh2) r -> IxX sh1 Int64 -> Nested.Mixed sh2 r
tindexNX v ix = Nested.mindexPartial v (fmap fromIntegral ix)

tindexZX
  :: forall r sh1 sh2. (TensorKind r, KnownShX sh1, KnownShX sh2)
  => RepN (TKX2 (sh1 ++ sh2) r) -> IxXOf RepN sh1 -> RepN (TKX2 sh2 r)
tindexZX v ixRepN | Dict <- eltDictRep (stensorKind @r) =
  let ix = fmap unRepN ixRepN
  in withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
     case tftk stensorKind v of
       FTKX sh x ->
         if ixInBounds (toList ix) (toList sh)
         then RepN $ tindexNX (unRepN v) ix
         else constantTarget def (FTKX (shxDropSSX sh (knownShX @sh1)) x)

tindex0X
  :: forall r sh. (TensorKind r, KnownShX sh)
  => RepN (TKX2 sh r) -> IxXOf RepN sh -> RepN (TKX2 '[] r)
tindex0X v ixRepN | Dict <- eltDictRep (stensorKind @r) =
  let ix = fmap unRepN ixRepN
  in case tftk stensorKind v of
    FTKX sh x ->
      if ixInBounds (toList ix) (toList sh)
      then xscalar $ Nested.mindex (unRepN v) (fmap fromIntegral ix)
      else constantTarget def (FTKX ZSX x)

tmatmul2X
  :: forall m n p r.
     (Nested.PrimElt r, KnownNat m, KnownNat n, KnownNat p, Numeric r)
  => Nested.Mixed '[Just m, Just n] r -> Nested.Mixed '[Just n, Just p] r
  -> Nested.Mixed '[Just m, Just p] r
tmatmul2X t u =
  let t2 = Nested.mtoVector t
      u2 = Nested.mtoVector u
  in Nested.mfromVector (IsList.fromList [valueOf @m, valueOf @p]) $ LA.flatten
     $ LA.reshape (valueOf @n) t2 LA.<> LA.reshape (valueOf @p) u2

tscatterZ1X
  :: forall r n2 shn shp.
     (TensorKind r, KnownNat n2, KnownShX shn, KnownShX shp)
  => IShX (shp ++ shn) -> RepN (TKX2 (Just n2 ': shn) r)
  -> (IntOf RepN -> IxXOf RepN shp)
  -> RepN (TKX2 (shp ++ shn) r)
tscatterZ1X sh t f =
  case tftk stensorKind t of
    FTKX _ x ->
      withKnownShX (ssxFromShape sh) $
      gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
      gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
      let zero = constantTarget 0 (FTKX sh x)
          lt = xunravelToList t
          g i ti = let ix2 = f $ RepN $ fromIntegral i
                   in if ixInBounds (map unRepN $ toList ix2) (toList sh)
                      then updateNX @(Rank shp) zero [(ix2, ti)]
                      else zero
          lu = imap g lt
      in foldr (addTarget stensorKind) zero lu

tfromList0NX
  :: forall r sh. Nested.KnownElt r
  => IShX sh -> [Nested.Mixed '[] r] -> Nested.Mixed sh r
tfromList0NX sh l = case NonEmpty.nonEmpty l of
  Nothing -> if shxSize sh == 0
             then Nested.mreshape sh $ Nested.memptyArray sh
             else error "tfromList0NS: empty list, but not shape"
  Just nl -> Nested.mfromListLinear sh $ NonEmpty.map Nested.munScalar nl

tbuild1X
  :: forall r n sh. (Nested.Elt r, KnownNat n, KnownShX sh)
  => (Int64 -> Nested.Mixed sh r)
  -> Nested.Mixed (Just n ': sh) r
tbuild1X f =
  Nested.mcast (Nested.SKnown (SNat @n) :!% knownShX)
  $ Nested.mfromListOuter $ NonEmpty.map f
  $ NonEmpty.fromList [0 .. valueOf @n - 1]  -- hope this fuses

tgatherZ1X
  :: forall r n2 shn shp.
     (TensorKind r, KnownShX shn, KnownShX shp)
  => SNat n2 -> RepN (TKX2 (shp ++ shn) r)
  -> (IntOf RepN -> IxXOf RepN shp)
  -> RepN (TKX2 (Just n2 ': shn) r)
tgatherZ1X SNat t f =
  withKnownShX (knownShX @shp `ssxAppend` knownShX @shn) $
  case stensorKind @r of
    STKScalar{} ->  -- optimized
      xfromList $ NonEmpty.map (\i -> t `xindex` f (RepN i))
                               (NonEmpty.fromList [0 .. valueOf @n2 - 1])
    _ -> xbuild1 @_ @_ @n2 (\ix -> t `xindex` f ix)
