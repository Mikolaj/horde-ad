{-# LANGUAGE AllowAmbiguousTypes, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for concrete arrays backed
-- by 'Data.Vector.Storable.Vector'
-- and defined in @ox-arrays@ on the basis of @orthotope@.
module HordeAd.Core.OpsConcrete
  () where

import Prelude

import Control.Monad (forM_)
import Control.Monad.ST
import Data.Array.Internal.ShapedS qualified as SS
import Data.Coerce (Coercible, coerce)
import Data.Default
import Data.Function ((&))
import Data.Int (Int16, Int32, Int64, Int8)
import Data.IntMap.Strict qualified as IM
import Data.List (scanl')
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import Foreign.C (CInt)
import GHC.TypeLits (KnownNat, Nat, type (+))
import Type.Reflection (Typeable, typeRep)

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (shxFromShR, shxFromShS)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed qualified as Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked qualified as Ranked
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped qualified as Shaped
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Init, fromSNat', unsafeCoerceRefl)
import Data.Array.Strided.Orthotope (liftVEltwise1)

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Conversion
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.OpsADVal
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.UnwindNum

-- * Tensor classes instance

instance LetTensor Concrete where
  ttlet = (&)  -- doesn't have to be strict, just as tcond
  ttletPrimal = (&)
  ttletPlain = (&)
  toShare = id
  tunshare = id
  tD _stk t DummyDualTarget{} = t
  {-# INLINE tfold #-}
  tfold k _ stk f x0 es = foldl' f x0 (tunravelToListShare k stk es)
   {- This is worse than the above when the vector needs to be allocated
      due to complex strides. Apparently this happens often enough
      and checking strides is costly for small folds (but do we care?
      but then, how often do big folds work on rank 1 arrays anyway?).
   case stk of
    STKScalar ->
      let g !yn !ym = f yn (Concrete ym)
      in VS.foldl' g x0 (stoVector es)
    STKR (SNat' @0) STKScalar ->
      let g !yn !ym = f yn (rfromK $ Concrete ym)
      in VS.foldl' g x0 (rtoVector es)
    STKS ZSS STKScalar ->
      let g !yn !ym = f yn (sfromK $ Concrete ym)
      in VS.foldl' g x0 (stoVector es)
    STKX ZKX STKScalar ->
      let g !yn !ym = f yn (xfromK $ Concrete ym)
      in VS.foldl' g x0 (xtoVector es)
    _ -> foldl' f x0 (tunravelToListShare k stk es) -}
  {-# INLINE tscan #-}
  tscan k nstk stk f x0 as =
    case NonEmpty.nonEmpty $ scanl' f x0 $ tunravelToListShare k stk as of
      Just nl -> tfromList (snatSucc k) nstk nl
      Nothing -> error "tscan: impossible"

instance ShareTensor Concrete where
  tshare = id
  {-# INLINE tunpair #-}
  tunpair (Concrete (t1, t2)) = (Concrete t1, Concrete t2)

instance BaseTensor Concrete where
  {-# INLINE rshape #-}
  rshape @_ @x | Dict <- eltDictRep (knownSTK @x) = Nested.rshape . unConcrete
  {-# INLINE sshape #-}
  sshape @_ @x | Dict <- eltDictRep (knownSTK @x) = Nested.sshape . unConcrete
  {-# INLINE xshape #-}
  xshape @_ @x | Dict <- eltDictRep (knownSTK @x) = Nested.mshape . unConcrete
  {-# INLINE tftk #-}
  tftk stk (Concrete t) = tftkG stk t
  {-# INLINE tpair #-}
  tpair u v = u `seq` v `seq` Concrete (unConcrete u, unConcrete v)
  {-# INLINE tproject1 #-}
  tproject1 = Concrete . fst . unConcrete
  {-# INLINE tproject2 #-}
  tproject2 = Concrete . snd . unConcrete
  {-# INLINE tcond #-}
  tcond _ b u v = if unConcrete b then u else v
    -- doesn't have to be strict, just as tlet
  tkconcrete = Concrete
  trconcrete = Concrete
  tsconcrete = Concrete
  txconcrete = Concrete
  tconcrete _ = id
  {-# INLINE tkunravelToList #-}
  tkunravelToList =
    fmapConcrete . SS.toList . Nested.stoOrthotope . unConcrete
  {-# INLINE trfromVector #-}
  trfromVector @_ @x v | Dict <- eltDictRep (knownSTK @x) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.rfromListOuterN (V.length v) l
      Nothing -> error "rfromVector: empty vector"
  {-# INLINE trunravelToList #-}
  trunravelToList @_ @x | Dict <- eltDictRep (knownSTK @x) =
    fmapConcrete . Nested.rtoListOuter . unConcrete
  {-# INLINE tsfromVector #-}
  tsfromVector @_ @_ @x v | Dict <- eltDictRep (knownSTK @x) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.sfromListOuter SNat l
      Nothing -> error "sfromVector: empty vector"
  {-# INLINE tsunravelToList #-}
  tsunravelToList @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    fmapConcrete . Nested.stoListOuter . unConcrete
  {-# INLINE txfromVector #-}
  txfromVector @n @_ @x v | Dict <- eltDictRep (knownSTK @x) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.mfromListOuterSN (SNat @n) l
      Nothing -> error "xfromVector: empty vector"
  {-# INLINE txunravelToList #-}
  txunravelToList @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    fmapConcrete . Nested.mtoListOuter . unConcrete
  tfromVector snat stk v = case NonEmpty.nonEmpty $ V.toList v of
    Just nl -> tfromList snat stk nl
    Nothing -> error "tfromVector: empty vector"
  {-# INLINE tfromList #-}
  tfromList snat@SNat stk l = case stk of
    STKScalar ->
      Concrete $ Nested.sfromList1Prim snat $ fmapUnConcrete $ NonEmpty.toList l
    STKR SNat x | Dict <- eltDictRep x ->
      Concrete $ Nested.rfromListOuterN (fromSNat' snat) $ fmapUnConcrete l
    STKS _sh x | Dict <- eltDictRep x ->
      Concrete $ Nested.sfromListOuter snat $ fmapUnConcrete l
    STKX _sh x | Dict <- eltDictRep x ->
      Concrete $ Nested.mfromListOuterSN snat $ fmapUnConcrete l
    STKProduct stk1 stk2 ->
      let (l1, l2) = NonEmpty.unzip $ coerce l  -- NonEmpty.map tunpair l
          a1 = tfromList snat stk1 l1
          a2 = tfromList snat stk2 l2
          -- This processes a list of trivial primitive elements first,
          -- which does not force the list, which prevents forcing
          -- the other (tuple of) list prematurely, which makes streaming
          -- possible (sometimes).
      in case stk2 of
           STKScalar @r2 | Just Refl <- testEquality (typeRep @r2)
                                                     (typeRep @Z1) ->
             a2 `seq` tpair a1 a2
           _ -> tpair a1 a2
             -- TODO: instead construct both (tuples of) tensors at once,
             -- element by element to stream even when more than one
             -- list of nontrivial elements is present; use mvecsWrite?
  trsum @_ @x t = case knownSTK @x of
    STKScalar @r | Dict0 <- numFromTKAllNum (Proxy @r) ->
      Concrete . Nested.rsumOuter1Prim . unConcrete $ t  -- optimized
    _ -> case tftk knownSTK t of
      FTKR sh x ->  -- GHC 9.14 says (_ :$: rest) not exhaustive
        let l = trunravelToList t
        in foldl' (taddTarget knownSTK) (tdefTarget (FTKR (shrTail sh) x)) l
          -- Concrete has a ShareTensor instance, so taddTarget arguments
          -- don't need to be duplicable
  {-# INLINE trsum0 #-}
  trsum0 = Concrete . Nested.rsumAllPrim . unConcrete
  {-# INLINE trdot0 #-}
  trdot0 u v = Concrete $ Nested.rdot (unConcrete u) (unConcrete v)
  {-# INLINE trdot1In #-}
  trdot1In u v = Concrete $ Nested.rdot1Inner (unConcrete u) (unConcrete v)
  trmatvecmul m v = trdot1In m (trreplicate (rwidth m) v)
  trmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR ->
      trdot1In (trtranspose [1, 0] (trreplicate width2 m1))
               (trtranspose [0, 2, 1] (trreplicate (rwidth m1) m2))
  {-# INLINE trreplicate #-}
  trreplicate @_ @x k | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rreplicate (k :$: ZSR) . unConcrete
  {-# INLINE trreplicate0N #-}
  trreplicate0N sh = Concrete . Nested.rreplicatePrim sh . unConcrete
  tssum @_ @_ @x t = case knownSTK @x of
    STKScalar @r | Dict0 <- numFromTKAllNum (Proxy @r) ->
      Concrete . Nested.ssumOuter1Prim . unConcrete $ t  -- optimized
    _ -> case tftk knownSTK t of
      FTKS (_ :$$ rest) x ->
        let l = tsunravelToList t
        in foldl' (taddTarget knownSTK) (tdefTarget (FTKS rest x)) l
  {-# INLINE tssum0 #-}
  tssum0 = Concrete . Nested.ssumAllPrim . unConcrete
  {-# INLINE tsdot0 #-}
  tsdot0 u v = Concrete $ Nested.sdot (unConcrete u) (unConcrete v)
  {-# INLINE tsdot1In #-}
  tsdot1In @_ (SNat @n) u v =
    Concrete $ Nested.sdot1Inner (Proxy @n) (unConcrete u) (unConcrete v)
  tsmatvecmul m v = tsdot1In SNat m (tsreplicate SNat knownShS v)
  tsmatmul2 m1 m2 =
    tsdot1In SNat
             (tstranspose (Permutation.makePerm @'[1, 0])
                          (tsreplicate SNat knownShS m1))
             (tstranspose (Permutation.makePerm @'[0, 2, 1])
                          (tsreplicate SNat knownShS m2))
  {-# INLINE tsreplicate #-}
  tsreplicate @_ @_ @x snat@SNat _sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.sreplicate (snat :$$ ZSS) . unConcrete
  {-# INLINE tsreplicate0N #-}
  tsreplicate0N sh = Concrete . Nested.sreplicatePrim sh . unConcrete
  txsum @_ @_ @x t = case knownSTK @x of
    STKScalar @r | Dict0 <- numFromTKAllNum (Proxy @r) ->
      Concrete . Nested.msumOuter1Prim . unConcrete $ t  -- optimized
    _ -> case tftk knownSTK t of
      FTKX (_ :$% rest) x ->
        let l = txunravelToList t
        in foldl' (taddTarget knownSTK) (tdefTarget (FTKX rest x)) l
  {-# INLINE txsum0 #-}
  txsum0 = Concrete . Nested.msumAllPrim . unConcrete
  {-# INLINE txdot0 #-}
  txdot0 u v = Concrete $ Nested.mdot (unConcrete u) (unConcrete v)
  {-# INLINE txdot1In #-}
  txdot1In @_ (SNat @n) u v =
    Concrete $ Nested.mdot1Inner (Proxy @(Just n)) (unConcrete u) (unConcrete v)
  txmatvecmul mm mn m v =
    withKnownShX (ssxFromShX $ mn :$% ZSX) $
    withKnownShX (ssxFromShX $ mm :$% mn :$% ZSX) $
    withSNat (fromSMayNat' mm) $ \(SNat @m) ->
    withSNat (fromSMayNat' mn) $ \(SNat @n) ->
      xmcast (ssxFromShX (mm :$% ZSX))
      $ txsum (xtr (txreplicate (SNat @m) knownShX
                      (xmcast (ssxFromShX (Nested.SKnown (SNat @n)
                                             :$% ZSX)) v)
                    * xmcast (ssxFromShX (Nested.SKnown (SNat @m)
                                            :$% Nested.SKnown (SNat @n)
                                            :$% ZSX)) m))
  txmatmul2 m1 m2 =
    txdot1In SNat
             (txtranspose (Permutation.makePerm @'[1, 0])
                          (txreplicate SNat knownShX m1))
             (txtranspose (Permutation.makePerm @'[0, 2, 1])
                          (txreplicate SNat knownShX m2))
  {-# INLINE txreplicate #-}
  txreplicate @_ @_ @x snat _sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mreplicate (Nested.SKnown snat :$% ZSX) . unConcrete
  {-# INLINE txreplicate0N #-}
  txreplicate0N sh = Concrete . Nested.mreplicatePrim sh . unConcrete
  {-# INLINE trindex #-}
  trindex = tindexZR
  {-# INLINE trindex0 #-}
  trindex0 = tindex0R
  {-# INLINE troneHot #-}
  troneHot = toneHotR
  {-# INLINE trscatter #-}
  trscatter = tscatterZR
  -- no meaningful optimization here so far: trscatter1 = tscatterZ1R
  {-# INLINE trgather #-}
  trgather = tgatherZR
  {-# INLINE trgather1 #-}
  trgather1 = tgatherZ1R
  {-# INLINE tsindex #-}
  tsindex @_ @shn = tindexZS (knownShS @shn)
  {-# INLINE tsindex0 #-}
  tsindex0 = tindex0S
  {-# INLINE tsoneHot #-}
  tsoneHot @shp @shn = toneHotS (knownShS @shn) (knownShS @shp)
  {-# INLINE tsscatter #-}
  tsscatter @shm @shn @shp =
    tscatterZS (knownShS @shm) (knownShS @shn) (knownShS @shp)
  {-# INLINE tsgather #-}
  tsgather @shm @shn =
    tgatherZS (knownShS @shm) (knownShS @shn)
  {-# INLINE tsgather1 #-}
  tsgather1 @_ @shn = tgatherZ1S (knownShS @shn)
  {-# INLINE txindex #-}
  txindex = tindexZX
  {-# INLINE txindex0 #-}
  txindex0 = tindex0X
  {-# INLINE txoneHot #-}
  txoneHot = toneHotX
  {-# INLINE txscatter #-}
  txscatter @shm @shn = tscatterZX @shm @shn
  {-# INLINE txgather #-}
  txgather @shm @shn = tgatherZX @shm @shn
  {-# INLINE txgather1 #-}
  txgather1 = tgatherZ1X
  {-# INLINE tkfloor #-}
  tkfloor = Concrete . floor . unConcrete
  {-# INLINE tkfromIntegral #-}
  tkfromIntegral = fromIntegral . unConcrete
    -- Here runtime specialization would be questionable. It can take several
    -- comparisons to make a single scalar operation (much) faster.
    -- The only big gain is when/if this gets inlined into the interpreter
    -- and so the interpretation resulting in @a@ is performed at a concrete
    -- type, e.g., it may be a big arithmetic expression, which we never
    -- runtime-specialize. Or when/if this op is repeated in a loop
    -- and the comparison is floated up out of the loop.
    --
    -- Benchmarks indicate this lowers allocation considerably, but increases
    -- runtime just as considerably, so it's disabled for now.
  {-# INLINE tkcast #-}
  tkcast @r1 @r2 a =
    let cast :: (Differentiable r1', Differentiable r2')
             => Concrete (TKScalar r1') -> Concrete (TKScalar r2')
        {-# INLINE cast #-}
        cast = Concrete . realToFrac . unConcrete
    -- Specializing just for the cases covered by realToFrac rules
    -- in GHC.Internal.Float, except for the Int cases that the RealFrac
    -- constraint required by reverse differenciation precludes.
    in case typeRep @r1 of
      Is @Double -> case typeRep @r2 of
        Is @Float -> cast @Double @Float a
        _ -> cast a
      Is @Float -> case typeRep @r2 of
        Is @Double -> cast @Float @Double a
        _ -> cast a
      _ -> cast a
  {-# INLINE trfloor #-}
  trfloor = Concrete . liftVR (V.map floor) . unConcrete
  {-# INLINE trfromIntegral #-}
  trfromIntegral @r1 @r2 a =
    let cast :: (GoodScalar r1', Integral r1', NumScalar r2')
             => Concrete (TKR n r1') -> Concrete (TKR n r2')
        {-# INLINE cast #-}
        cast = Concrete . liftVR (V.map fromIntegral) . unConcrete
    in case typeRep @r1 of
        Is @Int -> case typeRep @r2 of
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int8 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int16 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int32 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int64 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @CInt -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          _ -> cast a
        _ -> cast a
  {-# INLINE trcast #-}
  trcast @r1 @r2 a =
    let cast :: ( Differentiable r1', NumScalar r1'
                , Differentiable r2', NumScalar r2' )
             => Concrete (TKR n r1') -> Concrete (TKR n r2')
        {-# INLINE cast #-}
        cast = Concrete . liftVR (V.map realToFrac) . unConcrete
    in case typeRep @r1 of
      Is @Double -> case typeRep @r2 of
        Is @Float -> cast @Double @Float a
        _ -> cast a
      Is @Float -> case typeRep @r2 of
        Is @Double -> cast @Float @Double a
        _ -> cast a
      _ -> cast a
  trminIndex = Concrete . tminIndexR . unConcrete
  trmaxIndex = Concrete . tmaxIndexR . unConcrete
  {-# INLINE triota #-}
  triota n = trfromIntegral $ Concrete $ Nested.riota @Int n
  {-# INLINE tsfloor #-}
  tsfloor = Concrete . liftVS (V.map floor) . unConcrete
  {-# INLINE tsfromIntegral #-}
  tsfromIntegral @r1 @r2 a =
    let cast :: (GoodScalar r1', Integral r1', NumScalar r2')
             => Concrete (TKS sh r1') -> Concrete (TKS sh r2')
        {-# INLINE cast #-}
        cast = Concrete . liftVS (V.map fromIntegral) . unConcrete
    in case typeRep @r1 of
        Is @Int -> case typeRep @r2 of
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int8 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int16 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int32 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int64 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @CInt -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          _ -> cast a
        _ -> cast a
  {-# INLINE tscast #-}
  tscast @r1 @r2 a =
    let cast :: ( Differentiable r1', NumScalar r1'
                , Differentiable r2', NumScalar r2' )
             => Concrete (TKS sh r1') -> Concrete (TKS sh r2')
        {-# INLINE cast #-}
        cast = Concrete . liftVS (V.map realToFrac) . unConcrete
    in case typeRep @r1 of
      Is @Double -> case typeRep @r2 of
        Is @Float -> cast @Double @Float a
        _ -> cast a
      Is @Float -> case typeRep @r2 of
        Is @Double -> cast @Float @Double a
        _ -> cast a
      _ -> cast a
  tsminIndex = Concrete . tminIndexS . unConcrete
  tsmaxIndex = Concrete . tmaxIndexS . unConcrete
  {-# INLINE tsiota #-}
  tsiota @n = tsfromIntegral $ Concrete $ Nested.siota @Int (SNat @n)
  {-# INLINE txfloor #-}
  txfloor = Concrete . liftVX (V.map floor) . unConcrete
  {-# INLINE txfromIntegral #-}
  txfromIntegral @r1 @r2 a =
    let cast :: (GoodScalar r1', Integral r1', NumScalar r2')
             => Concrete (TKX sh r1') -> Concrete (TKX sh r2')
        {-# INLINE cast #-}
        cast = Concrete . liftVX (V.map fromIntegral) . unConcrete
    in case typeRep @r1 of
        Is @Int -> case typeRep @r2 of
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int8 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int16 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int32 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int64 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @Int64 -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @CInt -> cast a
          _ -> cast a
        Is @CInt -> case typeRep @r2 of
          Is @Int -> cast a
          Is @Double -> cast a
          Is @Float -> cast a
          Is @Int8 -> cast a
          Is @Int16 -> cast a
          Is @Int32 -> cast a
          Is @Int64 -> cast a
          _ -> cast a
        _ -> cast a
  {-# INLINE txcast #-}
  txcast @r1 @r2 a =
    let cast :: ( Differentiable r1', NumScalar r1'
                , Differentiable r2', NumScalar r2' )
             => Concrete (TKX sh r1') -> Concrete (TKX sh r2')
        {-# INLINE cast #-}
        cast = Concrete . liftVX (V.map realToFrac) . unConcrete
    in case typeRep @r1 of
      Is @Double -> case typeRep @r2 of
        Is @Float -> cast @Double @Float a
        _ -> cast a
      Is @Float -> case typeRep @r2 of
        Is @Double -> cast @Float @Double a
        _ -> cast a
      _ -> cast a
  txminIndex = Concrete . tminIndexX . unConcrete
  txmaxIndex = Concrete . tmaxIndexX . unConcrete
  {-# INLINE txiota #-}
  txiota @n = txfromIntegral $ Concrete $ Nested.miota @Int (SNat @n)
  {-# INLINE trappend #-}
  trappend @_ @x u v | Dict <- eltDictRep (knownSTK @x) =
    Concrete $ Nested.rappend (unConcrete u) (unConcrete v)
  {-# INLINE trslice #-}
  trslice @_ @x i n | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rslice i n . unConcrete
  {-# INLINE trreverse #-}
  trreverse @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rrev1 . unConcrete
  {-# INLINE trtranspose #-}
  trtranspose @_ @x perm | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rtranspose perm . unConcrete
  {-# INLINE trreshape #-}
  trreshape @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rreshape sh . unConcrete
  {-# INLINE tsappend #-}
  tsappend @_ @_ @_ @x u v | Dict <- eltDictRep (knownSTK @x) =
    Concrete $ Nested.sappend (unConcrete u) (unConcrete v)
  {-# INLINE tsslice #-}
  tsslice @_ @_ @_ @_ @x i n _ | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.sslice i n . unConcrete
  {-# INLINE tsreverse #-}
  tsreverse @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.srev1 . unConcrete
  {-# INLINE tstranspose #-}
  tstranspose @_ @_ @x perm | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.stranspose perm . unConcrete
  {-# INLINE tsreshape #-}
  tsreshape @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.sreshape sh . unConcrete
  {-# INLINE txappend #-}
  txappend @_ @_ @_ @x u v | Dict <- eltDictRep (knownSTK @x) =
    Concrete $ Nested.mappend (unConcrete u) (unConcrete v)
  {-# INLINE txslice #-}
  txslice @_ @_ @_ @_ @x i n _ | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.msliceSN i n . unConcrete
  {-# INLINE txreverse #-}
  txreverse @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mrev1 . unConcrete
  {-# INLINE txtranspose #-}
  txtranspose @_ @_ @x perm | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mtranspose perm . unConcrete
  {-# INLINE txreshape #-}
  txreshape @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mreshape sh . unConcrete
  {-# INLINE tkbuild1 #-}
  tkbuild1 f = tbuild1K f
  {-# INLINE tkbuild #-}
  tkbuild @sh f = tbuildK (knownShS @sh) f
  {-# INLINE trbuild1 #-}
  trbuild1 @n @x k f =
    let g :: Int -> RepConcrete (TKR2 n x)
        g i = unConcrete $ f (Concrete i)
    in case knownSTK @x of
      STKScalar | SNat' @0 <- SNat @n ->
        Concrete $ Nested.rfromVector (k :$: ZSR)
        $ VS.generate k (Nested.runScalar . g)
      _ | Dict <- eltDictRep (knownSTK @x) -> case k of
        0 ->
          Concrete $ Nested.runNest $ Nested.remptyArray
        _ ->
          Concrete $ Nested.rfromListOuterN k $ NonEmpty.fromList
          $ map g [0 .. k - 1]
  {-# INLINE trbuild #-}
  trbuild @_ @n @x shm f =
    let g ix = unConcrete $ f (fmapConcrete ix)
    in case knownSTK @x of
      STKScalar | SNat' @0 <- SNat @n ->
        Concrete $ Nested.rgeneratePrim shm (Nested.runScalar . g)
      _ | Dict <- eltDictRep (knownSTK @x) ->
        Concrete $ Nested.runNest $ Nested.rgenerate shm g
  {-# INLINE trmap0N #-}
  trmap0N f t = Concrete $ tmap0NR (unConcrete . f . Concrete) (unConcrete t)
  {-# INLINE trzipWith0N #-}
  trzipWith0N f t u =
    Concrete
    $ tzipWith0NR (\v w -> unConcrete $ f (Concrete v) (Concrete w))
                  (unConcrete t) (unConcrete u)
  {-# INLINE tsbuild1 #-}
  tsbuild1 @_ @sh f = tbuild1S (knownShS @sh) f
  {-# INLINE tsbuild #-}
  tsbuild @shm @shn f = tbuildS (knownShS @shm) (knownShS @shn) f
  {-# INLINE tsmap0N #-}
  tsmap0N f v = Concrete $ tmap0NS (unConcrete . f . Concrete) (unConcrete v)
  {-# INLINE tszipWith0N #-}
  tszipWith0N f t u =
    Concrete
    $ tzipWith0NS (\v w -> unConcrete $ f (Concrete v) (Concrete w))
                  (unConcrete t) (unConcrete u)
  {-# INLINE txbuild1 #-}
  txbuild1 @k @sh @x f =
    let g :: Int -> RepConcrete (TKX2 sh x)
        g i = unConcrete $ f (Concrete i)
    in case knownSTK @x of
      STKScalar | ZKX <- knownShX @sh ->
        Concrete $ Nested.mfromVector (Nested.SKnown SNat :$% ZSX)
        $ VS.generate (valueOf @k) (Nested.munScalar . g)
          -- this is somewhat faster and not much more complex than if
          -- done with mgeneratePrim
      _ | Dict <- eltDictRep (knownSTK @x) -> case SNat @k of
        SNat' @0 ->
          Concrete $ Nested.munNest $ Nested.memptyArray ZSX
        _ ->
          Concrete $ Nested.mfromListOuterSN SNat $ NonEmpty.fromList
          $ map g [0 .. valueOf @k - 1]
  {-# INLINE txbuild #-}
  txbuild @shm @shn @x shm f =
    let g ix = unConcrete $ f (fmapConcrete ix)
    in case knownSTK @x of
      STKScalar | ZKX <- knownShX @shn
                , Refl <- lemAppNil @shm ->
        Concrete $ Nested.mgeneratePrim shm (Nested.munScalar . g)
      _ | Dict <- eltDictRep (knownSTK @x) ->
        Concrete $ Nested.munNest $ Nested.mgenerate shm g
  {-# INLINE tmapAccumLDer #-}
  tmapAccumLDer _ k _ bftk eftk (ConcreteFun f) _df _rf =
    tmapAccumLC k bftk eftk f
  {-# INLINE tapply #-}
  tapply (ConcreteFun f) = Concrete . f . unConcrete
  {-# INLINE tlambda #-}
  tlambda _ f = ConcreteFun $ unConcrete . unHFun f . Concrete
  -- The code for tvjp and tjvp in this instance is similar as for the
  -- ADVal ranked instance, because the type family instance is the same.
  {-# INLINE tgrad #-}
  tgrad @_ @r xftk h | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
    ConcreteFun
    $ unConcrete . snd . crevOnParams Nothing (unHFun h) xftk . Concrete
  {-# INLINE tvjp #-}
  tvjp xftk h = ConcreteFun $ \db_a ->
    unConcrete $ snd
    $ crevOnParamsDt (Concrete $ fst db_a) (unHFun h) xftk (Concrete $ snd db_a)
  {-# INLINE tjvp #-}
  tjvp xftk h = ConcreteFun $ \da_a ->
    unConcrete $ snd
    $ cfwdOnParams xftk (Concrete $ snd da_a) (unHFun h) (Concrete $ fst da_a)
  tprimalPart = id
  {-# INLINE tdualPart #-}
  tdualPart stk t = DummyDualTarget (tftk stk t)
  tplainPart = id
  tfromPrimal _ t = t
  {-# INLINE tfromDual #-}
  tfromDual (DummyDualTarget ftk) = tdefTarget ftk
  tfromPlain _ t = t
  tScale _ _ t = t
  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target


instance ConvertTensor Concrete where
  {-# INLINE tconvert #-}
  tconvert c astk a | Dict <- eltDictRep astk
                    , Dict <- eltDictRep (convertSTK c astk) =
    Concrete $ Nested.convert (interpretTKConversion c) (unConcrete a)

  {-# INLINE kfromR #-}
  kfromR = Concrete . Nested.runScalar . unConcrete
  {-# INLINE kfromS #-}
  kfromS = Concrete . Nested.sunScalar . unConcrete
  {-# INLINE kfromX #-}
  kfromX = Concrete . Nested.munScalar . unConcrete
  {-# INLINE rfromK #-}
  rfromK = Concrete . Nested.rscalar . unConcrete
  {-# INLINE rfromS #-}
  rfromS @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.stoRanked . unConcrete
  {-# INLINE rfromX #-}
  rfromX @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mtoRanked . unConcrete
  {-# INLINE sfromK #-}
  sfromK = Concrete . Nested.sscalar . unConcrete
  {-# INLINE sfromR #-}
  sfromR @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . flip Nested.rcastToShaped knownShS . unConcrete
  {-# INLINE sfromX #-}
  sfromX @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mcastToShaped knownShS . unConcrete
  {-# INLINE xfromK #-}
  xfromK = Concrete . Nested.mscalar . unConcrete
  {-# INLINE xfromR #-}
  xfromR @sh @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rcastToMixed (knownShX @sh) . unConcrete
  {-# INLINE xfromS #-}
  xfromS @_ @sh' @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.scastToMixed (knownShX @sh') . unConcrete

  {-# INLINE rzip #-}
  rzip @y @z (Concrete (a, b)) | Dict <- eltDictRep (knownSTK @y)
                               , Dict <- eltDictRep (knownSTK @z) =
    Concrete $ Nested.rzip a b
  {-# INLINE runzip #-}
  runzip a = let (!a1, !a2) = Nested.runzip $ unConcrete a
             in Concrete (a1, a2)
  {-# INLINE szip #-}
  szip @y @z (Concrete (a, b)) | Dict <- eltDictRep (knownSTK @y)
                               , Dict <- eltDictRep (knownSTK @z) =
    Concrete $ Nested.szip a b
  {-# INLINE sunzip #-}
  sunzip a = let (!a1, !a2) = Nested.sunzip $ unConcrete a
             in Concrete (a1, a2)
  {-# INLINE xzip #-}
  xzip @y @z (Concrete (a, b)) | Dict <- eltDictRep (knownSTK @y)
                               , Dict <- eltDictRep (knownSTK @z) =
    Concrete $ Nested.mzip a b
  {-# INLINE xunzip #-}
  xunzip a = let (!a1, !a2) = Nested.munzip $ unConcrete a
             in Concrete (a1, a2)

  {-# INLINE xnestR #-}
  xnestR @sh1 @m @x sh | Dict <- eltDictRep (knownSTK @x)
                       , Refl <- lemRankReplicate (SNat @m) =
    Concrete
    . Nested.convert
        @(Nested.Mixed sh1 (Nested.Mixed (Replicate m Nothing) (RepConcrete x)))
        (Nested.ConvXX Nested.ConvXR)
    . Nested.mnest sh
    . unConcrete
  {-# INLINE xnestS #-}
  xnestS @sh1 @sh2 @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete
    . Nested.convert
        @(Nested.Mixed sh1 (Nested.Mixed (MapJust sh2) (RepConcrete x)))
        (Nested.ConvXX Nested.ConvXS)
    . Nested.mnest sh
    . unConcrete
  {-# INLINE xnest #-}
  xnest @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mnest sh . unConcrete
  {-# INLINE xunNestR #-}
  xunNestR @sh1 @m @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete
    . Nested.munNest
    . Nested.convert
        @(Nested.Mixed sh1 (Nested.Ranked m (RepConcrete x)))
        (Nested.ConvXX Nested.ConvRX)
    . unConcrete
  {-# INLINE xunNestS #-}
  xunNestS @sh1 @sh2 @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete
    . Nested.munNest
    . Nested.convert
        @(Nested.Mixed sh1 (Nested.Shaped sh2 (RepConcrete x)))
        (Nested.ConvXX Nested.ConvSX)
    . unConcrete
  {-# INLINE xunNest #-}
  xunNest = Concrete . Nested.munNest . unConcrete

  tpairConv = tpair
  tunpairConv = tunpair

interpretTKConversion :: TKConversion a b
                      -> Nested.Conversion (RepConcrete a) (RepConcrete b)
interpretTKConversion c0 = case c0 of
  ConvId -> Nested.ConvId
  ConvCmp c1 c2 -> Nested.ConvCmp (interpretTKConversion c1)
                                  (interpretTKConversion c2)
  ConvRX -> Nested.ConvRX
  ConvSX -> Nested.ConvSX
  ConvXR stk | Dict <- eltDictRep stk -> Nested.ConvXR
  ConvXS -> Nested.ConvXS
  ConvXS' (FTKS sh' ftk) | Dict <- eltDictRep (ftkToSTK ftk) ->
    Nested.ConvXS' sh'
  ConvXX' (FTKX shx ftk) | Dict <- eltDictRep (ftkToSTK ftk) ->
    Nested.ConvXX' (ssxFromShX shx)
  ConvRR c -> Nested.ConvRR (interpretTKConversion c)
  ConvSS c -> Nested.ConvSS (interpretTKConversion c)
  ConvXX c -> Nested.ConvXX (interpretTKConversion c)
  ConvT2 c1 c2 ->
    Nested.ConvT2 (interpretTKConversion c1) (interpretTKConversion c2)
  Conv0X stk | Dict <- eltDictRep stk -> Nested.Conv0X
  ConvX0 -> Nested.ConvX0
  ConvNest (STKX sh x) | Dict <- eltDictRep x -> Nested.ConvNest sh
  ConvUnnest -> Nested.ConvUnnest
  ConvZip stk1 stk2 | Dict <- eltDictRep stk1
                    , Dict <- eltDictRep stk2 -> Nested.ConvZip
  ConvUnzip stk1 stk2 | Dict <- eltDictRep stk1
                      , Dict <- eltDictRep stk2 -> Nested.ConvUnzip


-- * Misc

fmapConcrete :: Coercible (f (RepConcrete y)) (f (Concrete y))
               => f (RepConcrete y) -> f (Concrete y)
fmapConcrete = coerce

fmapUnConcrete :: Coercible (f (Concrete y)) (f (RepConcrete y))
               => f (Concrete y) -> f (RepConcrete y)
fmapUnConcrete = coerce

-- Depite the warning, the pattern match is exhaustive.
ixInBoundsR :: IShR n -> IxROf Concrete n -> Bool
ixInBoundsR ZSR ZIR = True
ixInBoundsR (n :$: sh) (Concrete i :.: ix) =
  0 <= i && i < n && ixInBoundsR sh ix

ixInBoundsS :: ShS sh -> IxSOf Concrete sh -> Bool
ixInBoundsS ZSS ZIS = True
ixInBoundsS ((fromSNat' -> n) :$$ sh) (Concrete i :.$ ix) =
  0 <= i && i < n && ixInBoundsS sh ix

ixInBoundsX :: IShX sh -> IxXOf Concrete sh -> Bool
ixInBoundsX ZSX ZIX = True
ixInBoundsX ((fromSMayNat' -> n) :$% sh) (Concrete i :.% ix) =
  0 <= i && i < n && ixInBoundsX sh ix

-- Depite the warning, the pattern match is exhaustive.
ixrToLinearMaybe :: IShR n -> IxROf Concrete n -> Maybe Int
ixrToLinearMaybe = \sh ix -> goR sh ix 0
  where
    goR :: IShR n -> IxROf Concrete n -> Int -> Maybe Int
    goR ZSR ZIR !a = Just a
    goR (n :$: sh) (Concrete i :.: ix) a =
      if 0 <= i && i < n then goR sh ix (n * a + i) else Nothing

-- This would be shorter, but a bit more expensive:
--   ixxToLinearMaybe (ixxFromIxS ix)
ixsToLinearMaybe :: ShS sh -> IxSOf Concrete sh -> Maybe Int
ixsToLinearMaybe = \sh ix -> goS sh ix 0
  where
    goS :: ShS sh -> IxSOf Concrete sh -> Int -> Maybe Int
    goS ZSS ZIS !a = Just a
    goS ((fromSNat' -> n) :$$ sh) (Concrete i :.$ ix) a =
      if 0 <= i && i < n then goS sh ix (n * a + i) else Nothing

ixxToLinearMaybe :: IShX sh -> IxXOf Concrete sh -> Maybe Int
ixxToLinearMaybe = \sh ix -> goX sh ix 0
  where
    goX :: IShX sh -> IxXOf Concrete sh -> Int -> Maybe Int
    goX ZSX ZIX !a = Just a
    goX ((fromSMayNat' -> n) :$% sh) (Concrete i :.% ix) a =
      if 0 <= i && i < n then goX sh ix (n * a + i) else Nothing

tmapAccumLC
  :: forall k accy by ey.
     SNat k
  -> FullShapeTK by
  -> FullShapeTK ey
  -> (RepConcrete (TKProduct accy ey) -> RepConcrete (TKProduct accy by))
  -> Concrete accy
  -> Concrete (BuildTensorKind k ey)
  -> Concrete (TKProduct accy (BuildTensorKind k by))
{-# INLINE tmapAccumLC #-}
tmapAccumLC k (FTKScalar @z1) eftk f acc0 es
  | Just Refl <- testEquality (typeRep @z1) (typeRep @Z1) =
    let h :: Concrete accy -> Concrete ey -> Concrete accy
        h !acc !e = Concrete $ fst $ f (unConcrete acc, unConcrete e)
        xout = foldl' h acc0 (tunravelToListShare k (ftkToSTK eftk) es)
        lout2 = tsreplicate0N (k :$$ ZSS) (Concrete Z1)
    in tpair xout lout2
tmapAccumLC k bftk eftk f !acc0 !es =
  let (xout, lout) =
        mapAccumL' (curry $ coerce f) acc0
                   (tunravelToListShare k (ftkToSTK eftk) es)
  in case NonEmpty.nonEmpty lout of
    Just nl ->
      -- The bang is needed to stream the list, which may still partially
      -- fail if the output is a tuple of non-Z1 lists and then only
      -- the first of them is streamed. Such tuples are common
      -- in gradients of non-fold mapAccums.
      let !lout2 = tfromList k (ftkToSTK bftk) nl
      in tpair xout lout2
    Nothing -> tpair xout (tdefTarget (buildFTK k bftk))

-- The explicit dictionary is needed to trick GHC into specializing f at types
-- Int, Double, etc. insteasd of at type r, to simpify away the dictionaries
-- emerging from the constraints in the signature of f.
--
-- Despite what GHC says, TKAllNum (TKScalar r) is not redundant,
-- because it ensures the error case can't appear.
contFromTKAllNum :: forall r a. (Typeable r, TKAllNum (TKScalar r))
                 => (Dict0 (Num r, Nested.NumElt r, GoodScalar r) -> a) -> a
{-# INLINE contFromTKAllNum #-}  -- needed for the specialization hack
contFromTKAllNum f = case typeRep @r of
  Is @Int -> f Dict0
  Is @Double -> f Dict0
  Is @Float -> f Dict0
  Is @Z1 -> f Dict0
  Is @Int64 -> f Dict0
  Is @Int32-> f Dict0
  Is @Int16 -> f Dict0
  Is @Int8 -> f Dict0
  Is @CInt -> f Dict0
  _ -> error "contFromTKAllNum: impossible type"

-- See above. The list comes from ox-arrays at [PRIMITIVE ELEMENT TYPES LIST].
contFromTypeable :: forall r a. Typeable r
                 => (Dict GoodScalar r -> a) -> a
{-# INLINE contFromTypeable #-}  -- needed for the specialization hack
contFromTypeable f = case typeRep @r of
  Is @Int -> f Dict
  Is @Double -> f Dict
  Is @Float -> f Dict
  Is @Z1 -> f Dict
  Is @Int64 -> f Dict
  Is @Int32 -> f Dict
  Is @Int16-> f Dict
  Is @Int8 -> f Dict
  Is @CInt -> f Dict
  Is @Bool -> f Dict
  Is @() -> f Dict
  _ -> error "contFromTypeable: unexpected type"

tbuild1K :: (KnownNat k, GoodScalar r)
         => (IntOf Concrete -> Concrete (TKScalar r))
         -> Concrete (TKS '[k] r)
{-# INLINE tbuild1K #-}
tbuild1K @k f =
  let g i = unConcrete $ f (Concrete i)
  in Concrete $ Nested.sfromVector (SNat :$$ ZSS)
     $ VS.generate (valueOf @k) g

tbuildK :: GoodScalar r
        => ShS sh -> (IxSOf Concrete sh -> Concrete (TKScalar r))
        -> Concrete (TKS sh r)
{-# INLINE tbuildK #-}
tbuildK sh f =
  let g ix = unConcrete $ f (fmapConcrete ix)
  in Concrete $ Nested.sgeneratePrim sh g


-- * Ranked internal definitions

{-
tdot0R t u = OR.toVector t LA.<.> OR.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0R (t * u) -}

-- We could generalize by unwinding and only then doing the PrimElt things,
-- but we'd need a type family that says "replace this underlying scalars
-- by this one", which makes things too complicated.
--
-- We could also expose `liftVR` in the user API, but in addition
-- to the main function argument such as floor or cast, it'd need the function's
-- derivative, just as with mapAccums. Maybe it's better to generalize even more
-- and permit arbitrary extra ops if given their derivatives.
liftVR
  :: (Nested.PrimElt r1, Nested.PrimElt r2)
  => (VS.Vector r1 -> VS.Vector r2)
  -> Nested.Ranked n r1 -> Nested.Ranked n r2
{-# INLINE liftVR #-}
liftVR f = Ranked.liftRanked1 (Mixed.mliftNumElt1 (`liftVEltwise1` f))

manyHotNR :: forall m n x. (KnownNat m, KnownSTK x)
          => FullShapeTK (TKR2 (m + n) x)
          -> [(Int, Concrete (TKR2 n x))]
          -> Concrete (TKR2 (m + n) x)
{-# INLINE manyHotNR #-}
manyHotNR (FTKR shRanked x) upd | Dict <- eltDictRep (knownSTK @x)
                                , Refl <- lemRankReplicate (Proxy @(m + n))
                                , Refl <- lemReplicatePlusApp
                                            (SNat @m)
                                            (Proxy @n)
                                            (Proxy @(Nothing @Nat)) = runST $ do
  let zero = unConcrete $ tdefTarget x
      sh = shxFromShR shRanked
  vecs <- Mixed.mvecsReplicate sh zero
    -- this avoids the slow case of mvecsReplicate if x is TKScalar
  forM_ upd $ \(ix, Concrete v) ->
    Mixed.mvecsWritePartialLinear
      (Proxy @(Replicate m Nothing)) ix (Nested.rtoMixed v) vecs
  Concrete . Nested.mtoRanked <$> Mixed.mvecsUnsafeFreeze sh vecs

tindexZR :: forall m n x. (KnownNat m, KnownNat n, KnownSTK x)
         => Concrete (TKR2 (m + n) x) -> IxROf Concrete m
         -> Concrete (TKR2 n x)
{-# INLINE tindexZR #-}
tindexZR = case knownSTK @x of
  STKScalar @r -> contFromTypeable @r tindexZRDict
  _ -> tindexZRSlow

tindexZRSlow :: forall m n x. (KnownNat m, KnownNat n, KnownSTK x)
             => Concrete (TKR2 (m + n) x) -> IxROf Concrete m
             -> Concrete (TKR2 n x)
{-# NOINLINE tindexZRSlow #-}  -- the rare slow case
tindexZRSlow (Concrete v) ix | Dict <- eltDictRep (knownSTK @x) =
  if ixInBoundsR (shrTake @m $ Nested.rshape v) ix
  then Concrete $ Nested.rindexPartial v (fmapUnConcrete ix)
  else case tftkG (STKR SNat (knownSTK @x)) v of
         FTKR sh x -> tdefTarget (FTKR (shrDrop @m sh) x)

-- See the comment about tscatterZSDict.
tindexZRDict :: forall m n r. (KnownNat m, KnownNat n)
             => Dict GoodScalar r
             -> Concrete (TKR (m + n) r)
             -> IxROf Concrete m
             -> Concrete (TKR n r)
{-# INLINE tindexZRDict #-}
tindexZRDict Dict = tindexZRScalar

tindexZRScalar :: forall m n r. (KnownNat m, KnownNat n, GoodScalar r)
               => Concrete (TKR (m + n) r) -> IxROf Concrete m
               -> Concrete (TKR n r)
{-# INLINE tindexZRScalar #-}
tindexZRScalar (Concrete v) ix = case SNat @n of
  SNat' @0 ->  -- an optimized common case
    rfromK $ Concrete v `tindex0RImpl` ix
  _ ->
    Concrete
    $ if ixInBoundsR (shrTake @m $ Nested.rshape v) ix
      then Nested.rindexPartial v (fmapUnConcrete ix)
      else Nested.rreplicatePrim (shrDrop @m (Nested.rshape v)) def

tindex0R :: forall m r. GoodScalar r
         => Concrete (TKR m r) -> IxROf Concrete m
         -> Concrete (TKScalar r)
{-# INLINE tindex0R #-}
tindex0R = contFromTypeable @r tindex0RDict

tindex0RImpl :: forall m r. GoodScalar r
             => Concrete (TKR m r) -> IxROf Concrete m
             -> Concrete (TKScalar r)
{-# INLINE tindex0RImpl #-}
tindex0RImpl (Concrete v) ix =
  Concrete
  $ if ixInBoundsR (Nested.rshape v) ix
    then Nested.rindex v (fmapUnConcrete ix)
    else def

tindex0RDict :: forall m r.
                Dict GoodScalar r
             -> Concrete (TKR m r)
             -> IxROf Concrete m
             -> Concrete (TKScalar r)
{-# INLINE tindex0RDict #-}
tindex0RDict Dict = tindex0RImpl

toneHotR :: forall m n x. (KnownNat m, KnownNat n, KnownSTK x)
         => IShR m -> Concrete (TKR2 n x) -> IxROf Concrete m
         -> Concrete (TKR2 (m + n) x)
{-# INLINE toneHotR #-}
toneHotR sh1 !v ix = case tftk knownSTK v of
  FTKR sh2 x ->
    let ftk = FTKR (sh1 `shrAppend` sh2) x
    in case ixrToLinearMaybe sh1 ix of
         Nothing -> tdefTarget ftk
         Just i2 -> manyHotNR ftk [(i2, v)]

-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensor is added at such an index.
tscatterZR
  :: forall m n p x.
     (KnownNat m, KnownNat n, KnownNat p, TKAllNum x, KnownSTK x)
  => IShR p -> Concrete (TKR2 (m + n) x)
  -> (IxROf Concrete m -> IxROf Concrete p)
  -> Concrete (TKR2 (p + n) x)
{-# INLINE tscatterZR #-}
tscatterZR = case knownSTK @x of
  STKScalar @r ->  -- we don't use full dictionary from FTKScalar
    contFromTKAllNum @r tscatterZRDict
      -- Optimized: using (+) instead of taddTarget
  _ -> tscatterZRSlow

tscatterZRSlow
  :: forall m n p x.
     (KnownNat m, KnownNat n, KnownNat p, TKAllNum x, KnownSTK x)
  => IShR p -> Concrete (TKR2 (m + n) x)
  -> (IxROf Concrete m -> IxROf Concrete p)
  -> Concrete (TKR2 (p + n) x)
{-# NOINLINE tscatterZRSlow #-}  -- the rare slow case
tscatterZRSlow shp (Concrete v) f | Dict <- eltDictRep (knownSTK @x) =
  case tftkG (STKR SNat (knownSTK @x)) v of
    FTKR sht x ->
      let shm = shrTake @m sht
          shn = shrDrop @m sht
          ftk = FTKR (shp `shrAppend` shn) x
          g :: IIxR m
            -> IM.IntMap (Concrete (TKR2 n x))
            -> IM.IntMap (Concrete (TKR2 n x))
          g ix =
            let ix2 = f $ fmapConcrete ix
            in case ixrToLinearMaybe shp ix2 of
              Nothing -> id
              Just i2 ->
                IM.insertWith (taddTarget knownSTK) i2
                  (Concrete $ Nested.rindexPartial v ix)
          !ivs = foldl' (flip g) IM.empty (shrEnum shm)
      in manyHotNR ftk $ IM.assocs ivs

-- See the comment about tscatterZSDict.
tscatterZRDict
  :: forall m n p r. (KnownNat m, KnownNat n)
  => Dict0 (Num r, Nested.NumElt r, GoodScalar r)
  -> IShR p -> Concrete (TKR (m + n) r)
  -> (IxROf Concrete m -> IxROf Concrete p)
  -> Concrete (TKR (p + n) r)
{-# INLINE [1] tscatterZRDict #-}
tscatterZRDict Dict0 = tscatterZRScalar

tscatterZRScalar
  :: forall m n p r.
     (KnownNat m, KnownNat n, GoodScalar r, Num r, Nested.NumElt r)
  => IShR p -> Concrete (TKR (m + n) r)
  -> (IxROf Concrete m -> IxROf Concrete p)
  -> Concrete (TKR (p + n) r)
{-# INLINE tscatterZRScalar #-}
tscatterZRScalar shp !(Concrete v) f =
  let sht = Nested.rshape v
      shm = shrTake @m sht
  in case SNat @n of
       SNat' @0 -> runST $ do
         -- Optimized: using Nested.rindex instesad of Nested.rindexPartial.
         vec <- VSM.replicate (shrSize shp) 0
         forM_ (shrEnum shm) $ \ix -> do
           let ix2 = f $ fmapConcrete ix
           case ixrToLinearMaybe shp ix2 of
             Nothing -> return ()
             Just i2 -> do
               let u = Nested.rindex v ix
               u2 <- VSM.read vec i2
               VSM.write vec i2 (u + u2)
         Concrete . Nested.rfromVector shp <$> VS.unsafeFreeze vec
       _ -> runST $ do
         let g :: IIxR m
               -> IM.IntMap (Nested.Ranked n r)
               -> IM.IntMap (Nested.Ranked n r)
             g ix =
               let ix2 = f $ fmapConcrete ix
               in case ixrToLinearMaybe shp ix2 of
                 Nothing -> id
                 Just i2 ->
                   IM.insertWith (+) i2 (Nested.rindexPartial v ix)
             ivs = foldl' (flip g) IM.empty (shrEnum shm)
             shn = shrDrop @m sht
             shnSize = shrSize shn
         vec <- VSM.replicate (shrSize shp * shnSize) 0
         forM_ (IM.assocs ivs) $ \(i, u) ->
           VS.copy (VSM.slice (i * shnSize) shnSize vec) (Nested.rtoVector u)
             -- TODO: use toVectorList instead
         Concrete . Nested.rfromVector (shp `shrAppend` shn)
           <$> VS.unsafeFreeze vec

-- The semantics of the operation permits index out of bounds
-- and the result of such indexing is def, which is 0.
tgatherZR
  :: forall m n p x. (KnownNat m, KnownNat n, KnownNat p, KnownSTK x)
  => IShR m -> Concrete (TKR2 (p + n) x)
  -> (IxROf Concrete m -> IxROf Concrete p)
  -> Concrete (TKR2 (m + n) x)
{-# INLINE tgatherZR #-}
tgatherZR = case knownSTK @x of
  STKScalar @r ->  -- we don't use full dictionary from FTKScalar
    contFromTypeable @r tgatherZRDict
      -- Code gets specialized to a particular underlying scalar.
  _ -> tgatherZRSlow

tgatherZRSlow
  :: forall m n p x. (KnownNat m, KnownNat n, KnownNat p, KnownSTK x)
  => IShR m -> Concrete (TKR2 (p + n) x)
  -> (IxROf Concrete m -> IxROf Concrete p)
  -> Concrete (TKR2 (m + n) x)
{-# NOINLINE tgatherZRSlow #-}
tgatherZRSlow shm !t f =
  trbuild shm (\ix -> t `tindexZRSlow` f ix)

tgatherZRDict
  :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
  => Dict GoodScalar r
  -> IShR m -> Concrete (TKR (p + n) r)
  -> (IxROf Concrete m -> IxROf Concrete p)
  -> Concrete (TKR (m + n) r)
{-# INLINE tgatherZRDict #-}
tgatherZRDict Dict = tgatherZRScalar

tgatherZRScalar
  :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p, GoodScalar r)
  => IShR m -> Concrete (TKR (p + n) r)
  -> (IxROf Concrete m -> IxROf Concrete p)
  -> Concrete (TKR (m + n) r)
{-# INLINE tgatherZRScalar #-}
tgatherZRScalar shm !t f = case SNat @n of
  SNat' @0 ->  -- an optimized common case
    let g ix = unConcrete $ t `tindex0RImpl` (f $ fmapConcrete ix)
    in Concrete $ Nested.rgeneratePrim shm g
  _ -> trbuild shm (\ix -> t `tindexZRScalar` f ix)

tgatherZ1R
  :: forall n p x. (KnownNat n, KnownNat p, KnownSTK x)
  => Int -> Concrete (TKR2 (p + n) x)
  -> (IntOf Concrete -> IxROf Concrete p)
  -> Concrete (TKR2 (1 + n) x)
{-# INLINE tgatherZ1R #-}
tgatherZ1R = case knownSTK @x of
  STKScalar @r ->  -- we don't use full dictionary from FTKScalar
    contFromTypeable @r tgatherZ1RDict
      -- Code gets specialized to a particular underlying scalar.
  _ -> tgatherZ1RSlow

tgatherZ1RSlow
  :: forall n p x. (KnownNat n, KnownNat p, KnownSTK x)
  => Int -> Concrete (TKR2 (p + n) x)
  -> (IntOf Concrete -> IxROf Concrete p)
  -> Concrete (TKR2 (1 + n) x)
{-# NOINLINE tgatherZ1RSlow #-}
tgatherZ1RSlow k !t f =
  trbuild1 k (\ix -> t `tindexZRSlow` f ix)

tgatherZ1RDict
  :: forall n p r. (KnownNat n, KnownNat p)
  => Dict GoodScalar r
  -> Int -> Concrete (TKR (p + n) r)
  -> (IntOf Concrete -> IxROf Concrete p)
  -> Concrete (TKR (1 + n) r)
{-# INLINE tgatherZ1RDict #-}
tgatherZ1RDict Dict = tgatherZ1RScalar

tgatherZ1RScalar
  :: forall n p r. (KnownNat n, KnownNat p, GoodScalar r)
  => Int -> Concrete (TKR (p + n) r)
  -> (IntOf Concrete -> IxROf Concrete p)
  -> Concrete (TKR (1 + n) r)
{-# INLINE tgatherZ1RScalar #-}
tgatherZ1RScalar k !t f = case SNat @n of
  SNat' @0 ->  -- an optimized common case
    let shm = k :$: shrDrop (rshape t)
        g i = unConcrete $ t `tindex0RImpl` (f $ Concrete i)
    in Concrete $ Nested.rfromVector shm $ VS.generate k g
  _ -> trbuild1 k (\ix -> t `tindexZRScalar` f ix)

tminIndexR
  :: forall r n. (Nested.PrimElt r, Nested.NumElt r)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n Int
{-# INLINE tminIndexR #-}
tminIndexR v | SNat <- Nested.rrank v =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 Int
      f = Nested.rscalar . ixrHead . Nested.rminIndexPrim
  in Nested.runNest $ Nested.rrerankPrim ZSR f (Nested.rnest SNat v)

tmaxIndexR
  :: forall r n. (Nested.PrimElt r, Nested.NumElt r)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n Int
{-# INLINE tmaxIndexR #-}
tmaxIndexR v | SNat <- Nested.rrank v =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 Int
      f = Nested.rscalar . ixrHead . Nested.rmaxIndexPrim
  in Nested.runNest $ Nested.rrerankPrim ZSR f (Nested.rnest SNat v)

tmap0NR
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (r1 -> r) -> Nested.Ranked n r1 -> Nested.Ranked n r
{-# INLINE tmap0NR #-}
tmap0NR f = Ranked.liftRanked1 (Mixed.mliftPrim f)

tzipWith0NR
  :: (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (r1 -> r2 -> r) -> Nested.Ranked n r1 -> Nested.Ranked n r2
  -> Nested.Ranked n r
{-# INLINE tzipWith0NR #-}
tzipWith0NR f = Ranked.liftRanked2 (Mixed.mliftPrim2 f)


-- * Shaped internal definitions

liftVS
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r
{-# INLINE liftVS #-}
liftVS f = Shaped.liftShaped1 (Mixed.mliftNumElt1 (`liftVEltwise1` f))

manyHotNS :: forall shn shp x.
             ShS shn -> ShS shp -> FullShapeTK x
          -> [(Int, Concrete (TKS2 shn x))]
          -> Concrete (TKS2 (shp ++ shn) x)
{-# INLINE manyHotNS #-}
manyHotNS shn shp x upd | Dict <- eltDictRep (ftkToSTK x)
                        , let shShaped = shp `shsAppend` shn
                        , Refl <- lemRankMapJust shShaped
                        , Refl <- lemMapJustApp shp (Proxy @shn) = runST $ do
  let zero = unConcrete $ tdefTarget x
      sh = shxFromShS shShaped
  vecs <- Mixed.mvecsReplicate sh zero
    -- this avoids the slow case of mvecsReplicate if x is TKScalar
  forM_ upd $ \(ix, Concrete v) ->
    Mixed.mvecsWritePartialLinear
      (Proxy @(MapJust shp)) ix (Nested.stoMixed v) vecs
  Concrete . Nested.mcastToShaped shShaped <$> Mixed.mvecsUnsafeFreeze sh vecs

-- Note that after vectorization, the index may not fit within
-- the type-level shape, which we catch in the @ixInBounds@
-- and return def, so it's fine. Similarly in gather and scatter.
tindexZS :: forall shm shn x. KnownSTK x
         => ShS shn -> Concrete (TKS2 (shm ++ shn) x) -> IxSOf Concrete shm
         -> Concrete (TKS2 shn x)
{-# INLINE tindexZS #-}
tindexZS = case knownSTK @x of
  STKScalar @r -> contFromTypeable @r tindexZSDict
  _ -> tindexZSSlow

tindexZSSlow :: forall shm shn x. KnownSTK x
             => ShS shn -> Concrete (TKS2 (shm ++ shn) x) -> IxSOf Concrete shm
             -> Concrete (TKS2 shn x)
{-# NOINLINE tindexZSSlow #-}  -- the rare slow case
tindexZSSlow shn (Concrete v) ix | Dict <- eltDictRep (knownSTK @x) =
  if ixInBoundsS (Shaped.shsTakeIx @shn @shm Proxy (Nested.sshape v) ix) ix
  then Concrete $ Nested.sindexPartial v (fmapUnConcrete ix)
  else case tftkG (STKS (Nested.sshape v) (knownSTK @x)) v of
         FTKS _sh x -> tdefTarget (FTKS shn x)

tindexZSDict :: forall shm shn r.
                Dict GoodScalar r
             -> ShS shn -> Concrete (TKS (shm ++ shn) r)
             -> IxSOf Concrete shm
             -> Concrete (TKS shn r)
{-# INLINE tindexZSDict #-}
tindexZSDict Dict = tindexZSScalar

tindexZSScalar :: forall shm shn r. GoodScalar r
               => ShS shn -> Concrete (TKS (shm ++ shn) r) -> IxSOf Concrete shm
               -> Concrete (TKS shn r)
{-# INLINE tindexZSScalar #-}
tindexZSScalar shn (Concrete v) ix = case shn of
  ZSS | Refl <- lemAppNil @shm ->  -- an optimized common case
    sfromK $ tindex0SImpl (Concrete v) ix
      -- TODO: benchmark and possibly duplicate the Concrete instance
      -- to avoid this overhead in symbolic pipeline; also in tindexZRScalar
  _ ->
    Concrete
    $ if ixInBoundsS (Shaped.shsTakeIx @shn @shm Proxy (Nested.sshape v) ix) ix
      then Nested.sindexPartial v (fmapUnConcrete ix)
      else Nested.sreplicatePrim shn def

tindex0S :: forall sh1 r. GoodScalar r
         => Concrete (TKS sh1 r) -> IxSOf Concrete sh1
         -> Concrete (TKScalar r)
{-# INLINE tindex0S #-}
tindex0S = contFromTypeable @r tindex0SDict

tindex0SImpl :: forall sh1 r. GoodScalar r
             => Concrete (TKS sh1 r) -> IxSOf Concrete sh1
             -> Concrete (TKScalar r)
{-# INLINE tindex0SImpl #-}
tindex0SImpl (Concrete v) ix =
  Concrete
  $ if ixInBoundsS (Nested.sshape v) ix
    then Nested.sindex v (fmapUnConcrete ix)
    else def

tindex0SDict :: forall sh1 r.
                Dict GoodScalar r
             -> Concrete (TKS sh1 r)
             -> IxSOf Concrete sh1
             -> Concrete (TKScalar r)
{-# INLINE tindex0SDict #-}
tindex0SDict Dict = tindex0SImpl

toneHotS :: forall shp shn x. KnownSTK x
         => ShS shn -> ShS shp -> Concrete (TKS2 shn x) -> IxSOf Concrete shp
         -> Concrete (TKS2 (shp ++ shn) x)
{-# INLINE toneHotS #-}
toneHotS shn shp !v ix = case tftk (STKS shn knownSTK) v of
  FTKS _ x ->
    let ftk = FTKS (shp `shsAppend` shn) x
    in case ixsToLinearMaybe shp ix of
         Nothing -> tdefTarget ftk
         Just i2 -> manyHotNS shn shp x [(i2, v)]

-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensor is added at such an index.
tscatterZS
  :: forall shm shn shp x. (TKAllNum x, KnownSTK x)
  => ShS shm -> ShS shn -> ShS shp
  -> Concrete (TKS2 (shm ++ shn) x)
  -> (IxSOf Concrete shm -> IxSOf Concrete shp)
  -> Concrete (TKS2 (shp ++ shn) x)
{-# INLINE tscatterZS #-}
tscatterZS = case knownSTK @x of
  STKScalar @r ->  -- we don't use full dictionary from FTKScalar
    contFromTKAllNum @r (tscatterZSDict @shm @shn)
      -- Optimized: using (+) instead of taddTarget
  _ -> tscatterZSSlow @shm @shn

tscatterZSSlow
  :: forall shm shn shp x. (TKAllNum x, KnownSTK x)
  => ShS shm -> ShS shn -> ShS shp
  -> Concrete (TKS2 (shm ++ shn) x)
  -> (IxSOf Concrete shm -> IxSOf Concrete shp)
  -> Concrete (TKS2 (shp ++ shn) x)
{-# NOINLINE tscatterZSSlow #-}  -- the rare slow case
tscatterZSSlow shm shn shp (Concrete v) f | Dict <- eltDictRep (knownSTK @x) =
  case tftkG (STKS (shm `shsAppend` shn) (knownSTK @x)) v of
    FTKS _sht x ->
      let g :: IIxS shm
            -> IM.IntMap (Concrete (TKS2 shn x))
            -> IM.IntMap (Concrete (TKS2 shn x))
          g ix =
            let ix2 = f $ fmapConcrete ix
            in case ixsToLinearMaybe shp ix2 of
              Nothing -> id
              Just i2 ->
                IM.insertWith (taddTarget $ STKS shn (ftkToSTK x)) i2
                  (Concrete $ Nested.sindexPartial @shm @shn v ix)
          !ivs = foldl' (flip g) IM.empty (shsEnum shm)
      in manyHotNS shn shp x $ IM.assocs ivs

-- The inlining phase control and the explicit dictionaryy argument
-- are required for GHC to consistently specialize the inlined
-- tscatterZSDict code to Int, Double, etc.
-- Phase 99 suffices in GHC 9.14.1, but a later phase is set for a good measure.
-- Maybe what needs to happen is that tscatterZSDict gets specialized
-- before it's inlined.
tscatterZSDict
  :: forall shm shn shp r.
     Dict0 (Num r, Nested.NumElt r, GoodScalar r)
  -> ShS shm -> ShS shn -> ShS shp
  -> Concrete (TKS (shm ++ shn) r)
  -> (IxSOf Concrete shm -> IxSOf Concrete shp)
  -> Concrete (TKS (shp ++ shn) r)
{-# INLINE [1] tscatterZSDict #-}
tscatterZSDict Dict0 = tscatterZSScalar @shm @shn

tscatterZSScalar
  :: forall shm shn shp r. (GoodScalar r, Num r, Nested.NumElt r)
  => ShS shm -> ShS shn -> ShS shp
  -> Concrete (TKS (shm ++ shn) r)
  -> (IxSOf Concrete shm -> IxSOf Concrete shp)
  -> Concrete (TKS (shp ++ shn) r)
{-# INLINE tscatterZSScalar #-}
tscatterZSScalar shm shn shp !(Concrete v) f =
  case shn of
    ZSS | Refl <- lemAppNil @shp
        , Refl <- lemAppNil @shm -> runST $ do
      -- Optimized: using Nested.sindex instead of Nested.sindexPartial.
      vec <- VSM.replicate (shsSize shp) 0
      forM_ (shsEnum shm) $ \ix -> do
        let ix2 = f $ fmapConcrete ix
        case ixsToLinearMaybe shp ix2 of
          Nothing -> return ()
          Just i2 -> do
            let u = Nested.sindex v ix
            u2 <- VSM.read vec i2
            VSM.write vec i2 (u + u2)
      Concrete . Nested.sfromVector shp <$> VS.unsafeFreeze vec
    _ -> runST $ do
      let g :: IIxS shm
            -> IM.IntMap (Nested.Shaped shn r)
            -> IM.IntMap (Nested.Shaped shn r)
          g ix =
            let ix2 = f $ fmapConcrete ix
            in case ixsToLinearMaybe shp ix2 of
              Nothing -> id
              Just i2 ->
                IM.insertWith (+) i2 (Nested.sindexPartial @shm @shn v ix)
          ivs = foldl' (flip g) IM.empty (shsEnum shm)
          shnSize = shsSize shn
      vec <- VSM.replicate (shsSize shp * shnSize) 0
      forM_ (IM.assocs ivs) $ \(i, u) ->
        VS.copy (VSM.slice (i * shnSize) shnSize vec) (Nested.stoVector u)
      Concrete . Nested.sfromVector (shp `shsAppend` shn)
        <$> VS.unsafeFreeze vec

tgatherZS
  :: forall shm shn shp x. KnownSTK x
  => ShS shm -> ShS shn
  -> Concrete (TKS2 (shp ++ shn) x)
  -> (IxSOf Concrete shm -> IxSOf Concrete shp)
  -> Concrete (TKS2 (shm ++ shn) x)
{-# INLINE tgatherZS #-}
tgatherZS = case knownSTK @x of
  STKScalar @r ->  -- we don't use full dictionary from FTKScalar
    contFromTypeable @r (tgatherZSDict @shm @shn)
      -- Code gets specialized to a particular underlying scalar.
  _ -> tgatherZSSlow @shm @shn

tgatherZSSlow
  :: forall shm shn shp x. KnownSTK x
  => ShS shm -> ShS shn
  -> Concrete (TKS2 (shp ++ shn) x)
  -> (IxSOf Concrete shm -> IxSOf Concrete shp)
  -> Concrete (TKS2 (shm ++ shn) x)
{-# NOINLINE tgatherZSSlow #-}
tgatherZSSlow shm shn !t f =
  tbuildS shm shn (\ix -> tindexZSSlow shn t (f ix))

tgatherZSDict
  :: forall shm shn shp r.
     Dict GoodScalar r
  -> ShS shm -> ShS shn
  -> Concrete (TKS (shp ++ shn) r)
  -> (IxSOf Concrete shm -> IxSOf Concrete shp)
  -> Concrete (TKS (shm ++ shn) r)
{-# INLINE tgatherZSDict #-}
tgatherZSDict Dict = tgatherZSScalar @shm @shn

tgatherZSScalar
  :: forall shm shn shp r. GoodScalar r
  => ShS shm -> ShS shn
  -> Concrete (TKS (shp ++ shn) r)
  -> (IxSOf Concrete shm -> IxSOf Concrete shp)
  -> Concrete (TKS (shm ++ shn) r)
{-# INLINE tgatherZSScalar #-}
tgatherZSScalar shm shn !t f = case shn of
  ZSS | Refl <- lemAppNil @shm
      , Refl <- lemAppNil @shp ->  -- an optimized common case
    tbuildK shm (\ix -> t `tindex0SImpl` f ix)
  _ -> tbuildS shm shn (\ix -> tindexZSScalar shn t (f ix))

tgatherZ1S
  :: forall k shn shp x. (KnownNat k, KnownSTK x)
  => ShS shn
  -> Concrete (TKS2 (shp ++ shn) x)
  -> (IntOf Concrete -> IxSOf Concrete shp)
  -> Concrete (TKS2 (k ': shn) x)
{-# INLINE tgatherZ1S #-}
tgatherZ1S = case knownSTK @x of
  STKScalar @r ->  -- we don't use full dictionary from FTKScalar
    contFromTypeable @r (tgatherZ1SDict @k @shn)
      -- Code gets specialized to a particular underlying scalar.
  _ -> tgatherZ1SSlow @k @shn

tgatherZ1SSlow
  :: forall k shn shp x. (KnownNat k, KnownSTK x)
  => ShS shn
  -> Concrete (TKS2 (shp ++ shn) x)
  -> (IntOf Concrete -> IxSOf Concrete shp)
  -> Concrete (TKS2 (k ': shn) x)
{-# NOINLINE tgatherZ1SSlow #-}
tgatherZ1SSlow shn !t f =
  tbuild1S shn (\ix -> tindexZSSlow shn t (f ix))

tgatherZ1SDict
  :: forall k shn shp r. KnownNat k
  => Dict GoodScalar r
  -> ShS shn
  -> Concrete (TKS (shp ++ shn) r)
  -> (IntOf Concrete -> IxSOf Concrete shp)
  -> Concrete (TKS (k ': shn) r)
{-# INLINE tgatherZ1SDict #-}
tgatherZ1SDict Dict = tgatherZ1SScalar @k @shn

tgatherZ1SScalar
  :: forall k shn shp r. (KnownNat k, GoodScalar r)
  => ShS shn
  -> Concrete (TKS (shp ++ shn) r)
  -> (IntOf Concrete -> IxSOf Concrete shp)
  -> Concrete (TKS (k ': shn) r)
{-# INLINE tgatherZ1SScalar #-}
tgatherZ1SScalar shn !t f = case shn of
  ZSS | Refl <- lemAppNil @shp ->  -- an optimized common case
    tkbuild1 @_ @k (\ix -> t `tindex0SImpl` f ix)
  _ -> tbuild1S shn (\ix -> tindexZSScalar shn t (f ix))

tminIndexS
  :: forall n sh r. (Nested.PrimElt r, Nested.NumElt r)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) Int
{-# INLINE tminIndexS #-}
tminIndexS v | sh1@(_ :$$ sh) <- Nested.sshape v =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] Int
      f = Nested.sscalar . ixsHead . Nested.sminIndexPrim
  in case sh of
    ZSS -> f @n v
    _ | SNat @m <- shsLast sh1 ->
      gcastWith (unsafeCoerceRefl
                 :: Init (n ': sh) ++ '[m] :~: n ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (n ': sh) :~: Init (n ': sh) ++ '[]) $
      Nested.sunNest $
        Nested.srerankPrim @'[m] @'[] @(Init (n ': sh)) ZSS (f @m) $
          Nested.snest (shsInit sh1) v

tmaxIndexS
  :: forall n sh r. (Nested.PrimElt r, Nested.NumElt r)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) Int
{-# INLINE tmaxIndexS #-}
tmaxIndexS v | sh1@(_ :$$ sh) <- Nested.sshape v =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] Int
      f = Nested.sscalar . ixsHead . Nested.smaxIndexPrim
  in case sh of
    ZSS -> f @n v
    _ | SNat @m <- shsLast sh1 ->
      gcastWith (unsafeCoerceRefl
                 :: Init (n ': sh) ++ '[m] :~: n ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (n ': sh) :~: Init (n ': sh) ++ '[]) $
      Nested.sunNest $
        Nested.srerankPrim @'[m] @'[] @(Init (n ': sh)) ZSS (f @m) $
          Nested.snest (shsInit sh1) v

tmap0NS
  :: forall r1 r sh. (Nested.PrimElt r1, Nested.PrimElt r)
  => (r1 -> r) -> Nested.Shaped sh r1 -> Nested.Shaped sh r
{-# INLINE tmap0NS #-}
tmap0NS f = Shaped.liftShaped1 (Mixed.mliftPrim f)

tzipWith0NS
  :: forall r1 r2 r sh. (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (r1 -> r2 -> r) -> Nested.Shaped sh r1 -> Nested.Shaped sh r2
  -> Nested.Shaped sh r
{-# INLINE tzipWith0NS #-}
tzipWith0NS f = Shaped.liftShaped2 (Mixed.mliftPrim2 f)

tbuild1S :: forall k sh x. (KnownNat k, KnownSTK x)
         => ShS sh -> (IntOf Concrete -> Concrete (TKS2 sh x))
         -> Concrete (TKS2 (k ': sh) x)
{-# INLINE tbuild1S #-}
tbuild1S sh f = case knownSTK @x of
  STKScalar | ZSS <- sh ->
    tbuild1K (Concrete . Nested.sunScalar . unConcrete . f)
  _ | Dict <- eltDictRep (knownSTK @x) -> case SNat @k of
    SNat' @0 ->
      Concrete $ Nested.semptyArray sh
    _ ->
      let g i = unConcrete $ f (Concrete i)
      in Concrete $ Nested.sfromListOuter SNat $ NonEmpty.fromList
         $ map g [0 .. valueOf @k - 1]

tbuildS :: forall shm shn x. KnownSTK x
        => ShS shm -> ShS shn -> (IxSOf Concrete shm -> Concrete (TKS2 shn x))
        -> Concrete (TKS2 (shm ++ shn) x)
{-# INLINE tbuildS #-}
tbuildS shm shn f = case knownSTK @x of
  STKScalar | ZSS <- shn
            , Refl <- lemAppNil @shm ->
    tbuildK shm (Concrete . Nested.sunScalar . unConcrete . f)
  _ | Dict <- eltDictRep (knownSTK @x) ->
    withKnownShS shn $  -- TODO: why exactly is this needed?
    let h ix = unConcrete $ f (fmapConcrete ix)
    in Concrete $ Nested.sunNest $ Nested.sgenerate shm h


-- * Mixed internal definitions

liftVX
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Mixed sh r1 -> Nested.Mixed sh r
{-# INLINE liftVX #-}
liftVX f = Mixed.mliftNumElt1 (`liftVEltwise1` f)

manyHotNX :: forall sh1 sh2 x. KnownSTK x
          => FullShapeTK (TKX2 (sh1 ++ sh2) x)
          -> [(Int, Concrete (TKX2 sh2 x))]
          -> Concrete (TKX2 (sh1 ++ sh2) x)
{-# INLINE manyHotNX #-}
manyHotNX (FTKX sh x) upd | Dict <- eltDictRep (knownSTK @x) = runST $ do
  let zero = unConcrete $ tdefTarget x
  vecs <- Mixed.mvecsReplicate sh zero
    -- this avoids the slow case of mvecsReplicate if x is TKScalar
  forM_ upd $ \(ix, Concrete v) ->
    Mixed.mvecsWritePartialLinear (Proxy @sh1) ix v vecs
  Concrete <$> Mixed.mvecsUnsafeFreeze sh vecs

tindexZX :: (KnownShX sh1, KnownShX sh2, KnownSTK x)
         => Concrete (TKX2 (sh1 ++ sh2) x) -> IxXOf Concrete sh1
         -> Concrete (TKX2 sh2 x)
{-# INLINE tindexZX #-}
tindexZX @sh1 @sh2 @x (Concrete v) ix | Dict <- eltDictRep (knownSTK @x) =
  if ixInBoundsX (shxTakeSSX (Proxy @sh2) (knownShX @sh1) (Nested.mshape v)) ix
  then Concrete $ Nested.mindexPartial v (fmapUnConcrete ix)
  else case tftkG (STKX (knownShX @sh1 `ssxAppend` knownShX @sh2)
                        (knownSTK @x)) v of
         FTKX sh x -> tdefTarget (FTKX (shxDropSSX (knownShX @sh1) sh) x)

tindex0X :: GoodScalar r
         => Concrete (TKX sh1 r) -> IxXOf Concrete sh1 -> Concrete (TKScalar r)
{-# INLINE tindex0X #-}
tindex0X (Concrete v) ix =
  Concrete
  $ if ixInBoundsX (Nested.mshape v) ix
    then Nested.mindex v (fmapUnConcrete ix)
    else def

toneHotX :: forall sh1 sh2 x. (KnownShX sh2, KnownSTK x)
         => IShX sh1 -> Concrete (TKX2 sh2 x) -> IxXOf Concrete sh1
         -> Concrete (TKX2 (sh1 ++ sh2) x)
{-# INLINE toneHotX #-}
toneHotX sh1 !v ix = case tftk knownSTK v of
  FTKX sh2 x ->
    let ftk = FTKX (sh1 `shxAppend` sh2) x
    in case ixxToLinearMaybe sh1 ix of
         Nothing -> tdefTarget ftk
         Just i2 -> manyHotNX @sh1 ftk [(i2, v)]

tscatterZX :: forall shm shn shp x.
              (KnownShX shm, KnownShX shn, TKAllNum x, KnownSTK x)
           => IShX shp -> Concrete (TKX2 (shm ++ shn) x)
           -> (IxXOf Concrete shm -> IxXOf Concrete shp)
           -> Concrete (TKX2 (shp ++ shn) x)
{-# INLINE tscatterZX #-}  -- this function takes a function as an argument
tscatterZX shp !v0@(Concrete v) f | Dict <- eltDictRep (knownSTK @x) =
  let sht = Nested.mshape v
      shm = shxTakeSSX (Proxy @shn) (knownShX @shm) sht
      shn = shxDropSSX @_ @shn (knownShX @shm) sht
  in withKnownShX (knownShX @shm `ssxAppend` knownShX @shn) $
     case (knownShX @shn, tftk knownSTK v0) of
       (ZKX, FTKX _ (FTKScalar @r)) | Dict0 <- numFromTKAllNum (Proxy @r)
                                    , Refl <- lemAppNil @shp
                                    , Refl <- lemAppNil @shm -> runST $ do
         -- Optimized: using (+) instead of taddTarget and using mindex.
         vec <- VSM.replicate (shxSize shp) 0
         forM_ (shxEnum shm) $ \ix -> do
           let ix2 = f $ fmapConcrete ix
           case ixxToLinearMaybe shp ix2 of
             Nothing -> return ()
             Just i2 -> do
               let u = Nested.mindex v ix
               u2 <- VSM.read vec i2
               VSM.write vec i2 (u + u2)
         Concrete . Nested.mfromVector shp <$> VS.unsafeFreeze vec
       (_, FTKX _ (FTKScalar @r)) | Dict0 <- numFromTKAllNum (Proxy @r) ->
         -- Optimized: using (+) instead of taddTarget.
         -- TODO: write to vecs and use a bitmap to record the written indexes
         -- and the intmap only for subsequent writes
         let ftk = FTKX (shp `shxAppend` shn) FTKScalar
             g :: IIxX shm
               -> IM.IntMap (Concrete (TKX2 shn x))
               -> IM.IntMap (Concrete (TKX2 shn x))
             g ix =
               let ix2 = f $ fmapConcrete ix
               in case ixxToLinearMaybe shp ix2 of
                 Nothing -> id
                 Just i2 ->
                   IM.insertWith (+) i2
                     (Concrete $ Nested.mindexPartial @_ @shm @shn v ix)
             !ivs = foldl' (flip g) IM.empty (shxEnum shm)
         in manyHotNX @shp ftk $ IM.assocs ivs
       (_, FTKX _ x) ->
         -- TODO: write to vecs and use a bitmap to record the written indexes
         -- and the intmap only for subsequent writes
         let ftk = FTKX (shp `shxAppend` shn) x
             g :: IIxX shm
               -> IM.IntMap (Concrete (TKX2 shn x))
               -> IM.IntMap (Concrete (TKX2 shn x))
             g ix =
               let ix2 = f $ fmapConcrete ix
               in case ixxToLinearMaybe shp ix2 of
                 Nothing -> id
                 Just i2 ->
                   IM.insertWith (taddTarget knownSTK) i2
                     (Concrete $ Nested.mindexPartial @_ @shm @shn v ix)
             !ivs = foldl' (flip g) IM.empty (shxEnum shm)
         in manyHotNX @shp ftk $ IM.assocs ivs

tgatherZX :: (KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x)
          => IShX shm
          -> Concrete (TKX2 (shp ++ shn) x)
          -> (IxXOf Concrete shm -> IxXOf Concrete shp)
          -> Concrete (TKX2 (shm ++ shn) x)
{-# INLINE tgatherZX #-}  -- this function takes a function as an argument
tgatherZX @shm @shn @shp @x shm !t f =
  gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
  case (knownShX @shn, knownSTK @x) of
    (ZKX, STKScalar) | Refl <- lemAppNil @shm
                     , Refl <- lemAppNil @shp ->  -- an optimized common case
      let g ix = unConcrete $ t `txindex0` (f $ fmapConcrete ix)
      in Concrete $ Nested.mgeneratePrim shm g
    _ ->
      case ssxRank (knownShX @shm) of
        SNat -> -- needed only for GHC 9.10
          txbuild @_ @shm @shn shm (\ix -> t `txindex` f ix)

tgatherZ1X :: forall k shn shp x.
              (KnownNat k, KnownShX shn, KnownShX shp, KnownSTK x)
           => SNat k -> Concrete (TKX2 (shp ++ shn) x)
           -> (IntOf Concrete -> IxXOf Concrete shp)
           -> Concrete (TKX2 (Just k ': shn) x)
{-# INLINE tgatherZ1X #-}   -- this function takes a function as an argument
tgatherZ1X _ !t f = case (knownShX @shn, knownSTK @x) of
  (ZKX, STKScalar) | Refl <- lemAppNil @shp ->  -- an optimized common case
    let shm = SKnown SNat :$% shxDropSSX (knownShX @shp)
                                         (Nested.mshape $ unConcrete t)
        g i = unConcrete $ t `txindex0` (f $ Concrete i)
    in Concrete $ Nested.mfromVector shm $ VS.generate (valueOf @k) g
  _ -> txbuild1 @_ @k (\ix -> t `txindex` f ix)

tminIndexX
  :: forall mn sh r. (Nested.PrimElt r, Nested.NumElt r)
  => Nested.Mixed (mn ': sh) r -> Nested.Mixed (Init (mn ': sh)) Int
{-# INLINE tminIndexX #-}
tminIndexX v | sh1@(_ :$% sh) <- Nested.mshape v =
  let f :: Nested.Mixed '[mm] r -> Nested.Mixed '[] Int
      f = Nested.mscalar . ixxHead . Nested.mminIndexPrim
  in case sh of
    ZSX -> f @mn v
    _ -> withSNat (fromSMayNat' (shxLast sh1)) $ \(_ :: SNat m) ->
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) ++ '[Just m] :~: mn ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) :~: Init (mn ': sh) ++ '[]) $
      Nested.munNest $
        Nested.mrerankPrim @'[Just m] @'[] @(Init (mn ': sh))
                           ZSX (f @(Just m)) $
          Nested.mnest (ssxFromShX $ shxInit sh1) v

tmaxIndexX
  :: forall mn sh r. (Nested.PrimElt r, Nested.NumElt r)
  => Nested.Mixed (mn ': sh) r -> Nested.Mixed (Init (mn ': sh)) Int
{-# INLINE tmaxIndexX #-}
tmaxIndexX v | sh1@(_ :$% sh) <- Nested.mshape v =
  let f :: Nested.Mixed '[mm] r -> Nested.Mixed '[] Int
      f = Nested.mscalar . ixxHead . Nested.mmaxIndexPrim
  in case sh of
    ZSX -> f @mn v
    _ -> withSNat (fromSMayNat' (shxLast sh1)) $ \(_ :: SNat m) ->
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) ++ '[Just m] :~: mn ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) :~: Init (mn ': sh) ++ '[]) $
      Nested.munNest $
        Nested.mrerankPrim @'[Just m] @'[] @(Init (mn ': sh))
                           ZSX (f @(Just m)) $
          Nested.mnest (ssxFromShX $ shxInit sh1) v
