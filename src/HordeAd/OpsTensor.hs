{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The tensor operations intended for the library user. The less user-friendly
-- prototypes of most of these operation can be found in "HordeAd.Core.Ops"
-- where some additional rarely used operations reside as well.
module HordeAd.OpsTensor
  ( -- * Shape manipulation
    rshape, rlength, rsize, rwidth
  , sshape, slength, ssize, swidth
  , xshape, xlength, xsize, xwidth
  , tsize, tftk
    -- * Constructing arrays from concrete values, lists and vectors
  , rconcrete, rscalar, rrepl, ringestData, rfromListLinear
  , sconcrete, sscalar, srepl, singestData, sfromListLinear
  , xconcrete, xscalar, xrepl, xingestData, xfromListLinear
  , kconcrete
  , rfromList, rfromVector, rfromVector0N, rfromList0N, runravelToList
  , sfromList, sfromVector, sfromVector0N, sfromList0N, sunravelToList
  , xfromList, xfromVector, xfromVector0N, xfromList0N, xunravelToList
    -- * Main array operations
  , tunit, tlet, ifH, minH, maxH, tpair, tproject1, tproject2
  , rsum, rsum0, rdot0, rdot1In, rmatvecmul, rmatmul2, rreplicate, rreplicate0N
  , ssum, ssum0, sdot0, sdot1In, smatvecmul, smatmul2, sreplicate, sreplicate0N
  , xsum, xsum0, xdot0, xdot1In, xmatvecmul, xmatmul2, xreplicate, xreplicate0N
  , rindex, (!), rindex0, roneHot, rscatter, rscatter1, rgather, rgather1
  , sindex, (!$), sindex0, soneHot, sscatter, sscatter1, sgather, sgather1
  , xindex, xindex0, xoneHot, xscatter, xscatter1, xgather, xgather1
  , rtr, rtranspose, rflatten, rreshape
  , str, stranspose, sflatten, sreshape
  , xtr, xtranspose, xflatten, xreshape
   -- * Auxiliary array operations
  , rfloor, rfromIntegral, rcast, rminIndex, rmaxIndex, riota
  , sfloor, sfromIntegral, scast, sminIndex, smaxIndex, siota
  , xfloor, xfromIntegral, xcast, xminIndex, xmaxIndex, xiota
  , kfloor, kfromIntegral, kcast
  , rappend, rconcat, rslice, runcons, rreverse
  , sappend, sslice, suncons, sreverse
  , xappend, xappend0, xconcat, xslice, xuncons, xreverse
    -- * Array operations derived from `build`
  , rbuild, rbuild1, rmap, rmap1, rmap0N, rzipWith, rzipWith1, rzipWith0N
  , rzipWith3, rzipWith31, rzipWith30N, rzipWith4, rzipWith41, rzipWith40N
  , sbuild, sbuild1, smap, smap1, smap0N, szipWith, szipWith1, szipWith0N
  , szipWith3, szipWith31, szipWith30N, szipWith4, szipWith41, szipWith40N
  , xbuild, xbuild1
    -- * Array operations derived from `mapAccum`
  , rfold, rscan, sfold, sscan, xfold, xscan, tmapAccumR, tmapAccumL
    -- * Array operations producing derivatives
  , kgrad, rvjp, rjvp, svjp, sjvp
    -- * Operations dealing with dual numbers
  , rprimalPart, rdualPart, rfromPrimal, rfromDual, rScale
  , sprimalPart, sdualPart, sfromPrimal, sfromDual, sScale
  , xprimalPart, xdualPart, xfromPrimal, xfromDual, xScale
  , kprimalPart, kdualPart, kfromPrimal, kfromDual, kScale
    -- * Array operations that utilize unwinding of nested arrays
  , treplTarget, tdefTarget, taddTarget, tmultTarget, tdotTarget
    -- * Minimal re-exports to make this module a higher level replacement for "HordeAd.Core.Ops"
  , ADReady
  , LetTensor, BaseTensor
  ) where

import Prelude

import Data.Int (Int64)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:))
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.TypeLits
  ( KnownNat
  , OrderingI (..)
  , cmpNat
  , type (+)
  , type (-)
  , type (<=)
  )

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (Init, unsafeCoerceRefl)
import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Ops
import HordeAd.Core.ConvertTensor

rconcrete :: (GoodScalar r, BaseTensor target)
          => Nested.Ranked n r -> target (TKR n r)
rconcrete = trconcrete
rscalar :: (GoodScalar r, BaseTensor target)
        => r -> target (TKR 0 r)
rscalar r = rconcrete $ Nested.rscalar r
rrepl :: forall n r target. (GoodScalar r, BaseTensor target)
      => IShR n -> r -> target (TKR n r)
rrepl sh a = tconcrete (FTKR sh FTKScalar) (Concrete $ Nested.rreplicateScal sh a)
ringestData :: forall n r target. (GoodScalar r, BaseTensor target)
            => IShR n -> [r] -> target (TKR n r)
ringestData sh l =
  tconcrete (FTKR sh FTKScalar) (Concrete $ Nested.rfromListPrimLinear sh l)
rfromListLinear :: forall n r target. (GoodScalar r, BaseTensor target)
                => IShR n -> NonEmpty r -> target (TKR n r)
rfromListLinear sh = ringestData sh . NonEmpty.toList
  -- used by ox-arrays to pretty-print values, so the type has to agree

sconcrete :: (GoodScalar r, BaseTensor target)
          => Nested.Shaped sh r -> target (TKS sh r)
sconcrete = tsconcrete
sscalar :: (GoodScalar r, BaseTensor target)
        => r -> target (TKS '[] r)
sscalar r = sconcrete $ Nested.sscalar r
srepl :: (KnownShS sh, GoodScalar r, BaseTensor target)
      => r -> target (TKS sh r)
srepl = sconcrete . Nested.sreplicateScal knownShS
singestData :: (KnownShS sh, GoodScalar r, BaseTensor target)
            => [r] -> target (TKS sh r)
singestData l = sconcrete $ Nested.sfromListPrimLinear knownShS l
sfromListLinear :: forall sh r target. (GoodScalar r, BaseTensor target)
                => ShS sh -> NonEmpty r -> target (TKS sh r)
sfromListLinear sh = sconcrete . Nested.sfromListPrimLinear sh . NonEmpty.toList

xconcrete :: (GoodScalar r, BaseTensor target)
          => Nested.Mixed sh r -> target (TKX sh r)
xconcrete = txconcrete
xscalar :: (GoodScalar r, BaseTensor target)
        => r -> target (TKX '[] r)
xscalar r = xconcrete $ Nested.mscalar r
xrepl :: forall sh r target. (GoodScalar r, BaseTensor target)
      => IShX sh -> r -> target (TKX sh r)
xrepl sh a = tconcrete (FTKX sh FTKScalar) (Concrete $ Nested.mreplicateScal sh a)
xingestData :: forall sh r target. (GoodScalar r, BaseTensor target)
            => IShX sh -> [r] -> target (TKX sh r)
xingestData sh l =
  tconcrete (FTKX sh FTKScalar) (Concrete $ Nested.mfromListPrimLinear sh l)
xfromListLinear :: forall sh r target. (GoodScalar r, BaseTensor target)
                => IShX sh -> NonEmpty r -> target (TKX sh r)
xfromListLinear sh = xingestData sh . NonEmpty.toList

kconcrete :: (GoodScalar r, BaseTensor target)
          => r -> target (TKScalar r)
kconcrete = tkconcrete

rfromList :: (KnownNat n, KnownSTK x, BaseTensor target)
          => NonEmpty (target (TKR2 n x)) -> target (TKR2 (1 + n) x)
rfromList = trfromVector . V.fromList . NonEmpty.toList
  -- going through strict vectors, because laziness is risky with impurity
-- | Create a tensor from a boxed vector treated as the outermost dimension.
rfromVector :: (KnownNat n, KnownSTK x, BaseTensor target)
            => Data.Vector.Vector (target (TKR2 n x))
            -> target (TKR2 (1 + n) x)
rfromVector = trfromVector
rfromVector0N :: forall n x target. (KnownSTK x, BaseTensor target)
              => IShR n -> Data.Vector.Vector (target (TKR2 0 x))
              -> target (TKR2 n x)
rfromVector0N = trfromVector0N
rfromList0N :: forall n x target. (KnownSTK x, BaseTensor target)
            => IShR n -> [target (TKR2 0 x)]
            -> target (TKR2 n x)
rfromList0N sh = trfromVector0N sh . V.fromList
runravelToList :: forall n x target.
                  (KnownSTK x, KnownNat n, BaseTensor target)
               => target (TKR2 (1 + n) x) -> [target (TKR2 n x)]
runravelToList = trunravelToList

sfromList :: (KnownNat n, KnownShS sh, KnownSTK x, BaseTensor target)
          => NonEmpty (target (TKS2 sh x)) -> target (TKS2 (n ': sh) x)
sfromList = tsfromVector . V.fromList . NonEmpty.toList
-- This is morally non-empty strict vectors:
sfromVector :: (KnownNat n, KnownShS sh, KnownSTK x, BaseTensor target)
            => Data.Vector.Vector (target (TKS2 sh x))
            -> target (TKS2 (n ': sh) x)
sfromVector = tsfromVector
sfromVector0N :: (KnownShS sh, KnownSTK x, BaseTensor target)
              => Data.Vector.Vector (target (TKS2 '[] x))
              -> target (TKS2 sh x)
sfromVector0N = tsfromVector0N
sfromList0N :: (KnownShS sh, KnownSTK x, BaseTensor target)
            => [target (TKS2 '[] x)]
            -> target (TKS2 sh x)
sfromList0N = tsfromVector0N . V.fromList
sunravelToList :: (KnownNat n, KnownShS sh, KnownSTK x, BaseTensor target)
               => target (TKS2 (n ': sh) x) -> [target (TKS2 sh x)]
sunravelToList = tsunravelToList

xfromList :: (KnownNat n, KnownShX sh, KnownSTK x, BaseTensor target)
          => NonEmpty (target (TKX2 sh x)) -> target (TKX2 (Just n ': sh) x)
xfromList = txfromVector . V.fromList . NonEmpty.toList
  -- going through strict vectors, because laziness is risky with impurity
xfromVector :: (KnownNat n, KnownShX sh, KnownSTK x, BaseTensor target)
            => Data.Vector.Vector (target (TKX2 sh x))
            -> target (TKX2 (Just n ': sh) x)
xfromVector = txfromVector
xfromVector0N :: forall sh x target. (KnownSTK x, BaseTensor target)
              => IShX sh -> Data.Vector.Vector (target (TKX2 '[] x))
              -> target (TKX2 sh x)
xfromVector0N = txfromVector0N
xfromList0N :: forall sh x target. (KnownSTK x, BaseTensor target)
            => IShX sh -> [target (TKX2 '[] x)]
            -> target (TKX2 sh x)
xfromList0N sh = txfromVector0N sh . V.fromList
xunravelToList :: (KnownNat n, KnownShX sh, KnownSTK x, BaseTensor target)
               => target (TKX2 (Just n ': sh) x) -> [target (TKX2 sh x)]
xunravelToList = txunravelToList

tunit :: BaseTensor target
      => target TKUnit
tunit = kconcrete Z0

tlet :: forall x z target. LetTensor target
     => target x -> (target x -> target z) -> target z
tlet = ttlet

ifH :: (KnownSTK y, Boolean (BoolOf target), BaseTensor target)
    => BoolOf target -> target y -> target y -> target y
ifH = tcond knownSTK
minH :: (KnownSTK y, OrdH target y, BaseTensor target)
     => target y -> target y -> target y
minH u v = ifH (u <=. v) u v
maxH :: (KnownSTK y, OrdH target y, BaseTensor target)
     => target y -> target y -> target y
maxH u v = ifH (u >=. v) u v

rsum :: (KnownNat n, KnownSTK x, BaseTensor target)
     => target (TKR2 (1 + n) x) -> target (TKR2 n x)
rsum = trsum
rsum0 :: (KnownNat n, KnownSTK x, BaseTensor target)
      => target (TKR2 n x) -> target (TKR2 0 x)
rsum0 = trsum0
rdot0 :: ( KnownNat n, GoodScalar r, BaseTensor target)
      => target (TKR n r) -> target (TKR n r) -> target (TKR 0 r)
rdot0 = trdot0
rdot1In :: (GoodScalar r, BaseTensor target)
        => target (TKR 2 r) -> target (TKR 2 r)
        -> target (TKR 1 r)
rdot1In = trdot1In
rmatvecmul :: (GoodScalar r, BaseTensor target)
           => target (TKR 2 r) -> target (TKR 1 r) -> target (TKR 1 r)
rmatvecmul = trmatvecmul
rmatmul2 :: (GoodScalar r, BaseTensor target)
         => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
rmatmul2 = trmatmul2
-- | Copy the given tensor along the new, outermost dimension.
rreplicate :: (KnownNat n, KnownSTK x, BaseTensor target)
           => Int -> target (TKR2 n x) -> target (TKR2 (1 + n) x)
rreplicate = trreplicate
rreplicate0N :: (KnownNat n, KnownSTK x, BaseTensor target)
             => IShR n -> target (TKR2 0 x) -> target (TKR2 n x)
rreplicate0N = trreplicate0N

ssum :: (KnownNat n, KnownShS sh, KnownSTK x, BaseTensor target)
     => target (TKS2 (n ': sh) x) -> target (TKS2 sh x)
ssum = tssum
ssum0 :: (KnownShS sh, KnownSTK x, BaseTensor target)
      => target (TKS2 sh x) -> target (TKS2 '[] x)
ssum0 = tssum0
sdot0 :: (KnownShS sh, GoodScalar r, BaseTensor target)
      => target (TKS sh r) -> target (TKS sh r) -> target (TKS '[] r)
sdot0 = tsdot0
sdot1In :: (KnownNat m, KnownNat n, GoodScalar r, BaseTensor target)
        => target (TKS '[m, n] r) -> target (TKS '[m, n] r)
        -> target (TKS '[m] r)  -- TODO: generalize
sdot1In = tsdot1In
smatvecmul :: (KnownNat m, KnownNat n, GoodScalar r, BaseTensor target)
           => target (TKS '[m, n] r) -> target (TKS '[n] r)
           -> target (TKS '[m] r)
smatvecmul = tsmatvecmul
smatmul2 :: (KnownNat m, KnownNat n, KnownNat p, GoodScalar r, BaseTensor target)
         => target (TKS '[m, n] r) -> target (TKS '[n, p] r)
         -> target (TKS '[m, p] r)
smatmul2 = tsmatmul2
sreplicate :: (KnownNat k, KnownShS sh, KnownSTK x, BaseTensor target)
           => target (TKS2 sh x) -> target (TKS2 (k ': sh) x)
sreplicate = tsreplicate SNat knownShS
sreplicate0N :: (KnownShS sh, KnownSTK x, BaseTensor target)
             => target (TKS2 '[] x) -> target (TKS2 sh x)
sreplicate0N = tsreplicate0N knownShS

xsum :: (KnownNat n, KnownShX sh, KnownSTK x, BaseTensor target)
     => target (TKX2 (Just n ': sh) x) -> target (TKX2 sh x)
xsum = txsum
xsum0 :: (KnownShX sh, KnownSTK x, BaseTensor target, ConvertTensor target)
      => target (TKX2 sh x) -> target (TKX2 '[] x)
xsum0 = txsum0
xdot0 :: ( KnownShX sh, GoodScalar r
         , BaseTensor target, ConvertTensor target )
      => target (TKX sh r) -> target (TKX sh r) -> target (TKX '[] r)
xdot0 = txdot0
xdot1In :: (KnownNat m, KnownNat n, GoodScalar r, BaseTensor target)
        => target (TKX '[Just m, Just n] r)
        -> target (TKX '[Just m, Just n] r)
        -> target (TKX '[Just m] r)
xdot1In = txdot1In
xmatvecmul :: forall mm mn r target.
              (GoodScalar r, BaseTensor target, ConvertTensor target)
           => Nested.SMayNat Int SNat mm -> Nested.SMayNat Int SNat mn
           -> target (TKX '[mm, mn] r) -> target (TKX '[mn] r)
           -> target (TKX '[mm] r)
xmatvecmul = txmatvecmul
xmatmul2 :: ( KnownNat m, KnownNat n, KnownNat p
            , GoodScalar r, BaseTensor target, ConvertTensor target )
         => target (TKX '[Just m, Just n] r)
         -> target (TKX '[Just n, Just p] r)
         -> target (TKX '[Just m, Just p] r)
xmatmul2 = txmatmul2
xreplicate :: (KnownNat k, KnownShX sh, KnownSTK x, BaseTensor target)
           => target (TKX2 sh x) -> target (TKX2 (Just k ': sh) x)
xreplicate = txreplicate SNat knownShX
xreplicate0N :: (KnownShX sh, KnownSTK x, BaseTensor target)
             => IShX sh -> target (TKX2 '[] x) -> target (TKX2 sh x)
xreplicate0N = txreplicate0N

-- | The sub-tensor at the given index. If index is out of bounds,
-- the result is defined and is @def@.
rindex, (!) :: (KnownNat m, KnownNat n, KnownSTK x, BaseTensor target)
            => target (TKR2 (m + n) x) -> IxROf target m -> target (TKR2 n x)
rindex = trindex
infixl 9 !
(!) = rindex  -- prefix form better when type applications are necessary
rindex0 :: (KnownNat m, KnownSTK x, BaseTensor target)
        => target (TKR2 m x) -> IxROf target m -> target (TKR2 0 x)
rindex0 = trindex0
roneHot :: ( KnownNat m, KnownNat n, KnownSTK x
           , BoolOf (PrimalOf target) ~ BoolOf target
           , EqH (PrimalOf target) (TKScalar Int64), BaseTensor target)
        => IShR m -> target (TKR2 n x) -> IxROf target m
        -> target (TKR2 (m + n) x)
roneHot = troneHot
rscatter :: (KnownNat m, KnownNat n, KnownNat p, KnownSTK x, BaseTensor target)
         => IShR (p + n) -> target (TKR2 (m + n) x)
         -> (IxROf target m -> IxROf target p)
         -> target (TKR2 (p + n) x)
rscatter = trscatter
-- | Build a tensor by adding up tensors of rank @n@ taken from
-- the second argument and inserted in a zero tensor
-- at indexes of length @p@.
-- The semantics of the operation permits index out of bounds
-- and then no tensor is added at such an index.
rscatter1 :: (KnownNat n, KnownNat p, KnownSTK x, BaseTensor target)
          => IShR (p + n) -> target (TKR2 (1 + n) x)
          -> (IntOf target -> IxROf target p)
          -> target (TKR2 (p + n) x)
rscatter1 = trscatter1
rgather :: (KnownNat m, KnownNat n, KnownNat p, KnownSTK x, BaseTensor target)
        => IShR (m + n) -> target (TKR2 (p + n) x)
        -> (IxROf target m -> IxROf target p)
        -> target (TKR2 (m + n) x)
rgather = trgather
-- | Build a tensor by collecting tensors of rank @n@ obtained by indexing
-- in the second argument at the given indexes of length @p@.
-- The semantics of the operation permits index out of bounds
-- and the result of such indexing is zero.
rgather1 :: (KnownNat n, KnownNat p, KnownSTK x, BaseTensor target)
         => Int -> target (TKR2 (p + n) x)
         -> (IntOf target -> IxROf target p)
         -> target (TKR2 (1 + n) x)
rgather1 = trgather1

sindex, (!$) :: (KnownShS shm, KnownShS shn, KnownSTK x, BaseTensor target)
             => target (TKS2 (shm ++ shn) x) -> IxSOf target shm
             -> target (TKS2 shn x)
sindex = tsindex
infixl 9 !$
(!$) = sindex  -- prefix form better when type applications are necessary
sindex0 :: (KnownShS sh1, KnownSTK x, BaseTensor target)
        => target (TKS2 sh1 x) -> IxSOf target sh1
        -> target (TKS2 '[] x)
sindex0 = tsindex0
soneHot :: ( KnownShS sh1, KnownShS sh2, KnownSTK x
           , BoolOf (PrimalOf target) ~ BoolOf target
           , EqH (PrimalOf target) (TKScalar Int64), BaseTensor target )
        => target (TKS2 sh2 x) -> IxSOf target sh1
        -> target (TKS2 (sh1 ++ sh2) x)
soneHot = tsoneHot
sscatter
  :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x, BaseTensor target)
  => target (TKS2 (shm ++ shn) x)
  -> (IxSOf target shm -> IxSOf target shp)
  -> target (TKS2 (shp ++ shn) x)
sscatter @shm @shn @shp = tsscatter @_ @shm @shn @shp
sscatter1
  :: (KnownNat n2, KnownShS shn, KnownShS shp, KnownSTK x, BaseTensor target)
  => target (TKS2 (n2 ': shn) x)
  -> (IntOf target -> IxSOf target shp)
  -> target (TKS2 (shp ++ shn) x)
sscatter1 = tsscatter1
sgather
  :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x, BaseTensor target)
  => target (TKS2 (shp ++ shn) x)
  -> (IxSOf target shm -> IxSOf target shp)
  -> target (TKS2 (shm ++ shn) x)
sgather @shm @shn @shp = tsgather @_ @shm @shn @shp
sgather1
  :: (KnownNat n2, KnownShS shn, KnownShS shp, KnownSTK x, BaseTensor target)
  => target (TKS2 (shp ++ shn) x)
  -> (IntOf target -> IxSOf target shp)
  -> target (TKS2 (n2 ': shn) x)
sgather1 = tsgather1

xindex :: (KnownShX sh1, KnownShX sh2, KnownSTK x, BaseTensor target)
       => target (TKX2 (sh1 ++ sh2) x) -> IxXOf target sh1
       -> target (TKX2 sh2 x)
xindex = txindex
xindex0 :: (KnownShX sh1, KnownSTK x, BaseTensor target)
        => target (TKX2 sh1 x) -> IxXOf target sh1
        -> target (TKX2 '[] x)
xindex0 = txindex0
xoneHot :: ( KnownShX sh1, KnownShX sh2, KnownSTK x
           , BoolOf (PrimalOf target) ~ BoolOf target
           , EqH (PrimalOf target) (TKScalar Int64)
           , BaseTensor target, ConvertTensor target )
        => IShX sh1 -> target (TKX2 sh2 x) -> IxXOf target sh1
        -> target (TKX2 (sh1 ++ sh2) x)
xoneHot = txoneHot
xscatter :: ( KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x
            , BaseTensor target )
         => IShX (shp ++ shn) -> target (TKX2 (shm ++ shn) x)
         -> (IxXOf target shm -> IxXOf target shp)
         -> target (TKX2 (shp ++ shn) x)
xscatter @shm @shn @shp = txscatter @_ @shm @shn @shp
xscatter1 :: ( KnownNat n2, KnownShX shn, KnownShX shp, KnownSTK x
             , BaseTensor target )
          => IShX (shp ++ shn) -> target (TKX2 (Just n2 ': shn) x)
          -> (IntOf target -> IxXOf target shp)
          -> target (TKX2 (shp ++ shn) x)
xscatter1 = txscatter1
xgather :: ( KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x
           , BaseTensor target )
        => IShX (shm ++ shn)
        -> target (TKX2 (shp ++ shn) x)
        -> (IxXOf target shm -> IxXOf target shp)
        -> target (TKX2 (shm ++ shn) x)
xgather @shm @shn @shp = txgather @_ @shm @shn @shp
xgather1 :: ( KnownNat n2, KnownShX shn, KnownShX shp, KnownSTK x
            , BaseTensor target )
         => SNat n2 -> target (TKX2 (shp ++ shn) x)
         -> (IntOf target -> IxXOf target shp)
         -> target (TKX2 (Just n2 ': shn) x)
xgather1 = txgather1

-- | Transpose according to the permutation.
rtranspose :: forall n x target. (KnownSTK x, BaseTensor target)
           => Permutation.PermR -> target (TKR2 n x) -> target (TKR2 n x)
rtranspose = trtranspose
-- | Change the shape of the tensor to the given one.
rreshape :: forall n m x target. (KnownSTK x, BaseTensor target)
         => IShR m -> target (TKR2 n x) -> target (TKR2 m x)
rreshape = trreshape
stranspose :: ( Permutation.KnownPerm perm, Permutation.IsPermutation perm
              , Rank perm <= Rank sh, KnownSTK x, BaseTensor target )
           => target (TKS2 sh x)
           -> target (TKS2 (Permutation.PermutePrefix perm sh) x)
stranspose @perm = tstranspose (Permutation.makePerm @perm)
sreshape :: ( Nested.Product sh ~ Nested.Product sh2, KnownShS sh2
            , KnownSTK x, BaseTensor target )
         => target (TKS2 sh x) -> target (TKS2 sh2 x)
sreshape = tsreshape knownShS
xtranspose :: ( Permutation.KnownPerm perm, Permutation.IsPermutation perm
              , Rank perm <= Rank sh, KnownSTK x, BaseTensor target )
           => target (TKX2 sh x)
           -> target (TKX2 (Permutation.PermutePrefix perm sh) x)
xtranspose @perm = txtranspose (Permutation.makePerm @perm)
xreshape :: forall sh sh2 x target. (KnownSTK x, BaseTensor target)
         => IShX sh2 -> target (TKX2 sh x) -> target (TKX2 sh2 x)
xreshape = txreshape

rfloor :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
          , BaseTensor target )
       => target (TKR n r) -> target (TKR n r2)
rfloor = trfloor
rfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, BaseTensor target)
              => target (TKR n r1) -> target (TKR n r2)
rfromIntegral = trfromIntegral
rcast :: ( RealFrac r1, GoodScalar r1, RealFrac r2, GoodScalar r2
         , BaseTensor target )
      => target (TKR n r1) -> target (TKR n r2)
rcast = trcast
rminIndex, rmaxIndex  -- partial
  :: forall n r r2 target. (GoodScalar r, GoodScalar r2, BaseTensor target)
  => target (TKR (1 + n) r) -> target (TKR n r2)
rminIndex = trminIndex
rmaxIndex = trmaxIndex
riota :: (GoodScalar r, BaseTensor target)
      => Int -> target (TKR 1 r)  -- from 0 to n - 1
riota = triota

sfloor :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
          , BaseTensor target )
       => target (TKS sh r) -> target (TKS sh r2)
sfloor = tsfloor
sfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, BaseTensor target)
              => target (TKS sh r1) -> target (TKS sh r2)
sfromIntegral = tsfromIntegral
scast :: ( RealFrac r1, GoodScalar r1, RealFrac r2, GoodScalar r2
         , BaseTensor target )
      => target (TKS sh r1) -> target (TKS sh r2)
scast = tscast
sminIndex, smaxIndex  -- partial
  :: forall n sh r r2 target. (GoodScalar r, GoodScalar r2, BaseTensor target)
  => target (TKS (n ': sh) r) -> target (TKS (Init (n ': sh)) r2)
sminIndex = tsminIndex
smaxIndex = tsmaxIndex
siota :: (KnownNat n, GoodScalar r, BaseTensor target)
      => target (TKS '[n] r)  -- from 0 to n - 1
siota = tsiota

xfloor :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
          , BaseTensor target )
       => target (TKX sh r) -> target (TKX sh r2)
xfloor = txfloor
xfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, BaseTensor target)
              => target (TKX sh r1) -> target (TKX sh r2)
xfromIntegral = txfromIntegral
xcast :: ( RealFrac r1, GoodScalar r1, RealFrac r2, GoodScalar r2
         , BaseTensor target )
      => target (TKX sh r1) -> target (TKX sh r2)
xcast = txcast
xminIndex, xmaxIndex  -- partial
  :: forall mn sh r r2 target. (GoodScalar r, GoodScalar r2, BaseTensor target)
  => target (TKX (mn ': sh) r) -> target (TKX (Init (mn ': sh)) r2)
xminIndex = txminIndex
xmaxIndex = txmaxIndex
xiota :: (KnownNat n, GoodScalar r, BaseTensor target)
      => target (TKX '[Just n] r)  -- from 0 to n - 1
xiota = txiota

kfloor :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
          , BaseTensor target )
       => target (TKScalar r) -> target (TKScalar r2)
kfloor = tkfloor
kfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, BaseTensor target)
              => target (TKScalar r1) -> target (TKScalar r2)
kfromIntegral = tkfromIntegral
kcast :: ( RealFrac r1, GoodScalar r1, RealFrac r2, GoodScalar r2
         , BaseTensor target )
      => target (TKScalar r1) -> target (TKScalar r2)
kcast = tkcast

-- | Append two arrays along the outermost dimension.
-- All dimensions, except the outermost, must be the same.
rappend :: forall n x target. (KnownSTK x, BaseTensor target)
        => target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
        -> target (TKR2 (1 + n) x)
rappend = trappend
rconcat :: forall n x target. (KnownSTK x, BaseTensor target)
        => NonEmpty (target (TKR2 (1 + n) x)) -> target (TKR2 (1 + n) x)
rconcat = foldr1 rappend
-- | Extract a slice of an array along the outermost dimension.
-- The extracted slice must fall within the dimension.
rslice :: forall n x target. (KnownSTK x, BaseTensor target)
       => Int -> Int -> target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
rslice = trslice
runcons :: (KnownNat n, KnownSTK x, BaseTensor target)
        => target (TKR2 (1 + n) x)
        -> Maybe (target (TKR2 n x), target (TKR2 (1 + n) x))
runcons v = case rshape v of
              len :$: _ -> Just (v ! [0], rslice 1 (len - 1) v)
-- | Reverse elements of the outermost dimension.
rreverse :: forall n x target. (KnownSTK x, BaseTensor target)
         => target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
rreverse = trreverse

sappend :: forall m n sh x target. (KnownSTK x, BaseTensor target)
        => target (TKS2 (m ': sh) x) -> target (TKS2 (n ': sh) x)
        -> target (TKS2 ((m + n) ': sh) x)
sappend = tsappend
sslice :: forall i n k sh x target. (KnownSTK x, BaseTensor target)
       => SNat i -> SNat n -> SNat k
       -> target (TKS2 (i + n + k ': sh) x) -> target (TKS2 (n ': sh) x)
sslice = tsslice
suncons :: (KnownNat n, KnownShS sh, KnownSTK x, BaseTensor target)
        => target (TKS2 (n ': sh) x)
        -> Maybe (target (TKS2 sh x), target (TKS2 (n - 1 ': sh) x))
suncons @n v = case cmpNat (Proxy @1) (Proxy @n) of
 EQI -> Just ( v !$ (0 :.$ ZIS)
             , sslice @1 @(n - 1) @0 SNat SNat SNat v )
 LTI -> Just ( v !$ (0 :.$ ZIS)
             , sslice @1 @(n - 1) @0 SNat SNat SNat v )
 _ -> Nothing
sreverse :: forall n sh x target. (KnownSTK x, BaseTensor target)
         => target (TKS2 (n ': sh) x) -> target (TKS2 (n ': sh) x)
sreverse = tsreverse

xappend :: forall m n sh x target. (KnownSTK x, BaseTensor target)
        => target (TKX2 (Just m ': sh) x) -> target (TKX2 (Just n ': sh) x)
        -> target (TKX2 (Just (m + n) ': sh) x)
xappend = txappend
xappend0 :: forall sh x target.
            (KnownSTK x, BaseTensor target, ConvertTensor target)
         => target (TKX2 (Nothing ': sh) x) -> target (TKX2 (Nothing ': sh) x)
        -> target (TKX2 (Nothing ': sh) x)
xappend0 a b = case xshape a of
 mmsnat :$% sh ->
   withSNat (fromSMayNat' mmsnat) $ \msnat ->
   withSNat (shxLength $ xshape b) $ \nsnat ->
   let sh0 = Nested.SUnknown () :!% ssxFromShape sh
       sha = Nested.SKnown msnat :!% ssxFromShape sh
       shb = Nested.SKnown nsnat :!% ssxFromShape sh
   in withKnownShX (ssxFromShape sh) $
      xmcast sh0 $ xappend (xmcast sha a) (xmcast shb b)
xconcat :: forall sh x target.
           (KnownSTK x, BaseTensor target, ConvertTensor target)
        => NonEmpty (target (TKX2 (Nothing ': sh) x))
        -> target (TKX2 (Nothing ': sh) x)
xconcat = foldr1 xappend0
xslice :: forall i n k sh x target. (KnownSTK x, BaseTensor target)
       => SNat i -> SNat n -> SNat k
       -> target (TKX2 (Just (i + n + k) ': sh) x)
       -> target (TKX2 (Just n ': sh) x)
xslice = txslice
xuncons :: (KnownNat n, KnownShX sh, KnownSTK x, BaseTensor target)
        => target (TKX2 (Just n ': sh) x)
        -> Maybe (target (TKX2 sh x), target (TKX2 (Just (n - 1) ': sh) x))
xuncons @n v = case cmpNat (Proxy @1) (Proxy @n) of
 EQI -> Just ( v `xindex` (0 :.% ZIX)
             , xslice @1 @(n - 1) @0 SNat SNat SNat v )
 LTI -> Just ( v `xindex` (0 :.% ZIX)
             , xslice @1 @(n - 1) @0 SNat SNat SNat v )
 _ -> Nothing
xreverse :: forall mn sh x target. (KnownSTK x, BaseTensor target)
         => target (TKX2 (mn ': sh) x) -> target (TKX2 (mn ': sh) x)
xreverse = txreverse

rbuild1 :: (KnownNat n, KnownSTK x, BaseTensor target)
        => Int  -- ^ width of the outermost dimension of the created tensor
        -> (IntOf target -> target (TKR2 n x))
             -- ^ the function to build with
        -> target (TKR2 (1 + n) x)
rbuild1 = trbuild1
rmap :: (KnownNat m, KnownNat n, KnownSTK x, KnownSTK x2, BaseTensor target)
     => (target (TKR2 n x) -> target (TKR2 n x2))
          -- ^ the function to map with
     -> target (TKR2 (m + n) x)  -- ^ the tensor to map over
     -> target (TKR2 (m + n) x2)
rmap f v = rbuild (rshape v) (\ix -> f (v ! ix))
rmap1 :: (KnownNat n, KnownSTK x, KnownSTK x2, BaseTensor target)
      => (target (TKR2 n x) -> target (TKR2 n x2))
           -- ^ the function to map with
      -> target (TKR2 (1 + n) x)  -- ^ the tensor to map over
      -> target (TKR2 (1 + n) x2)
rmap1 f u = rbuild1 (rwidth u) (\i -> f (u ! [i]))
rmap0N :: (KnownNat n, KnownSTK x, KnownSTK x1, BaseTensor target)
       => (target (TKR2 0 x1) -> target (TKR2 0 x))
            -- ^ the function to map with
       -> target (TKR2 n x1)  -- ^ the tensor to map over
       -> target (TKR2 n x)
rmap0N = trmap0N
rzipWith :: ( KnownNat m, KnownNat n1, KnownNat n2, KnownNat n, KnownSTK x
            , KnownSTK x1, KnownSTK x2, BaseTensor target )
         => IShR (m + n)  -- ^ the shape of the resulting tensor
         -> (target (TKR2 n1 x1) -> target (TKR2 n2 x2) -> target (TKR2 n x))
              -- ^ the function to zip with
         -> target (TKR2 (m + n1) x1)  -- ^ the first tensor to zip over
         -> target (TKR2 (m + n2) x2)  -- ^ the second tensor to zip over
         -> target (TKR2 (m + n) x)
rzipWith sh f u v = rbuild sh (\ix -> f (u ! ix) (v ! ix))
rzipWith1 :: ( KnownNat n1, KnownNat n2, KnownNat n, KnownSTK x
             , KnownSTK x1, KnownSTK x2, BaseTensor target)
          => (target (TKR2 n1 x1) -> target (TKR2 n2 x2) -> target (TKR2 n x))
               -- ^ the function to zip with
          -> target (TKR2 (1 + n1) x1)  -- ^ the first tensor to zip over
          -> target (TKR2 (1 + n2) x2)  -- ^ the second tensor to zip over
          -> target (TKR2 (1 + n) x)
rzipWith1 f u v = rbuild1 (rwidth u) (\i -> f (u ! [i]) (v ! [i]))
rzipWith0N :: ( KnownNat n, KnownSTK x, KnownSTK x1, KnownSTK x2
              , BaseTensor target )
           => (target (TKR2 0 x1) -> target (TKR2 0 x2) -> target (TKR2 0 x))
                -- ^ the function to zip with
           -> target (TKR2 n x1)  -- ^ the first tensor to zip over
           -> target (TKR2 n x2)  -- ^ the second tensor to zip over
           -> target (TKR2 n x)
rzipWith0N  = trzipWith0N
rzipWith3 :: ( KnownNat m, KnownNat n1, KnownNat n2, KnownNat n3
             , KnownNat n, KnownSTK x
             , KnownSTK x1, KnownSTK x2, KnownSTK x3, BaseTensor target )
          => IShR (m + n)  -- ^ the shape of the resulting tensor
          -> (target (TKR2 n1 x1) -> target (TKR2 n2 x2) -> target (TKR2 n3 x3)
              -> target (TKR2 n x))
               -- ^ the function to zip with
          -> target (TKR2 (m + n1) x1)  -- ^ the first tensor to zip over
          -> target (TKR2 (m + n2) x2)  -- ^ the second tensor to zip over
          -> target (TKR2 (m + n3) x3)  -- ^ the third tensor to zip over
          -> target (TKR2 (m + n) x)
rzipWith3 sh f u v w = rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix))
rzipWith31 :: ( KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n, KnownSTK x
              , KnownSTK x1, KnownSTK x2, KnownSTK x3, BaseTensor target )
           => (target (TKR2 n1 x1) -> target (TKR2 n2 x2) -> target (TKR2 n3 x3)
               -> target (TKR2 n x))
                -- ^ the function to zip with
           -> target (TKR2 (1 + n1) x1)  -- ^ the first tensor to zip over
           -> target (TKR2 (1 + n2) x2)  -- ^ the second tensor to zip over
           -> target (TKR2 (1 + n3) x3)  -- ^ the third tensor to zip over
           -> target (TKR2 (1 + n) x)
rzipWith31 f u v w =
  rbuild1 (rwidth u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]))
rzipWith30N :: ( KnownNat n, KnownSTK x
               , KnownSTK x1, KnownSTK x2, KnownSTK x3, BaseTensor target )
            => (target (TKR2 0 x1) -> target (TKR2 0 x2) -> target (TKR2 0 x3)
                -> target (TKR2 0 x))
                -- ^ the function to zip with
            -> target (TKR2 n x1)  -- ^ the first tensor to zip over
            -> target (TKR2 n x2)  -- ^ the second tensor to zip over
            -> target (TKR2 n x3)  -- ^ the third tensor to zip over
            -> target (TKR2 n x)
rzipWith30N f u v w =
  rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix))
rzipWith4 :: ( KnownNat m
             , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
             , KnownNat n, KnownSTK x
             , KnownSTK x1, KnownSTK x2, KnownSTK x3, KnownSTK x4
             , BaseTensor target )
          => IShR (m + n)  -- ^ the shape of the resulting tensor
          -> (target (TKR2 n1 x1) -> target (TKR2 n2 x2)
              -> target (TKR2 n3 x3) -> target (TKR2 n4 x4)
              -> target (TKR2 n x))
               -- ^ the function to zip with
          -> target (TKR2 (m + n1) x1)  -- ^ the first tensor to zip over
          -> target (TKR2 (m + n2) x2)  -- ^ the second tensor to zip over
          -> target (TKR2 (m + n3) x3)  -- ^ the third tensor to zip over
          -> target (TKR2 (m + n4) x4)  -- ^ the fourth tensor to zip over
          -> target (TKR2 (m + n) x)
rzipWith4 sh f u v w x =
  rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix) (x ! ix))
rzipWith41 :: ( KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
              , KnownNat n, KnownSTK x
              , KnownSTK x1, KnownSTK x2, KnownSTK x3, KnownSTK x4
              , BaseTensor target )
           => (target (TKR2 n1 x1) -> target (TKR2 n2 x2)
               -> target (TKR2 n3 x3) -> target (TKR2 n4 x4)
               -> target (TKR2 n x))
                -- ^ the function to zip with
           -> target (TKR2 (1 + n1) x1)  -- ^ the first tensor to zip over
           -> target (TKR2 (1 + n2) x2)  -- ^ the second tensor to zip over
           -> target (TKR2 (1 + n3) x3)  -- ^ the third tensor to zip over
           -> target (TKR2 (1 + n4) x4)  -- ^ the fourth tensor to zip over
           -> target (TKR2 (1 + n) x)
rzipWith41 f u v w x =
  rbuild1 (rwidth u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]) (x ! [i]))
rzipWith40N :: ( KnownNat n, KnownSTK x
               , KnownSTK x1, KnownSTK x2, KnownSTK x3, KnownSTK x4
               , BaseTensor target )
            => (target (TKR2 0 x1) -> target (TKR2 0 x2)
                -> target (TKR2 0 x3) -> target (TKR2 0 x4)
                -> target (TKR2 0 x))
                 -- ^ the function to zip with
            -> target (TKR2 n x1)  -- ^ the first tensor to zip over
            -> target (TKR2 n x2)  -- ^ the second tensor to zip over
            -> target (TKR2 n x3)  -- ^ the third tensor to zip over
            -> target (TKR2 n x4)  -- ^ the fourth tensor to zip over
            -> target (TKR2 n x)
rzipWith40N f u v w x =
  rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix)
                              (rindex0 x ix))

sbuild1 :: (KnownNat k, KnownShS sh, KnownSTK x, BaseTensor target)
        => (IntOf target -> target (TKS2 sh x))
             -- ^ the function to build with
        -> target (TKS2 (k ': sh) x)
sbuild1 = tsbuild1
smap :: ( KnownShS (Take m sh), KnownShS (Drop m sh), KnownShS sh
        , KnownSTK x, KnownSTK x2
        , BaseTensor target )
     => (target (TKS2 (Drop m sh) x) -> target (TKS2 (Drop m sh) x2))
          -- ^ the function to map with
     -> target (TKS2 sh x)  -- ^ the tensor to map over
     -> target (TKS2 sh x2)
smap @m @sh f v = gcastWith (unsafeCoerceRefl
                             :: sh :~: Take m sh ++ Drop m sh)
                  $ sbuild (\ix -> f (v !$ ix))
smap1 :: (KnownNat n, KnownShS sh, KnownSTK x, KnownSTK x2, BaseTensor target)
      => (target (TKS2 sh x) -> target (TKS2 sh x2))
           -- ^ the function to map with
      -> target (TKS2 (n ': sh) x)  -- ^ the tensor to map over
      -> target (TKS2 (n ': sh) x2)
smap1 f u = sbuild1 (\i -> f (u !$ (i :.$ ZIS)))
smap0N :: (KnownShS sh, KnownSTK x1, KnownSTK x, BaseTensor target)
       => (target (TKS2 '[] x1) -> target (TKS2 '[] x))
            -- ^ the function to map with
       -> target (TKS2 sh x1)  -- ^ the tensor to map over
       -> target (TKS2 sh x)
smap0N = tsmap0N
szipWith :: ( KnownShS (Drop m sh1), KnownShS (Drop m sh2), KnownShS (Take m sh)
            , KnownSTK x, KnownSTK x1, KnownSTK x2, KnownShS sh
            , sh1 ~ Take m sh ++ Drop m sh1
            , sh2 ~ Take m sh ++ Drop m sh2, BaseTensor target )
         => (target (TKS2 (Drop m sh1) x1) -> target (TKS2 (Drop m sh2) x2)
             -> target (TKS2 (Drop m sh) x))
              -- ^ the function to zip with
         -> target (TKS2 sh1 x1)  -- ^ the first tensor to zip over
         -> target (TKS2 sh2 x2)  -- ^ the second tensor to zip over
         -> target (TKS2 sh x)
szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
szipWith1 :: ( KnownNat n, KnownShS sh1, KnownShS sh2, KnownShS sh
             , KnownSTK x, KnownSTK x1, KnownSTK x2, BaseTensor target )
          => (target (TKS2 sh1 x1) -> target (TKS2 sh2 x2)
              -> target (TKS2 sh x))
               -- ^ the function to zip with
          -> target (TKS2 (n ': sh1) x1)  -- ^ the first tensor to zip over
          -> target (TKS2 (n ': sh2) x2)  -- ^ the second tensor to zip over
          -> target (TKS2 (n ': sh) x)
szipWith1 f u v = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                   (v !$ (i :.$ ZIS)))
szipWith0N :: ( KnownShS sh, KnownSTK x, KnownSTK x1, KnownSTK x2
              , BaseTensor target )
           => (target (TKS2 '[] x1) -> target (TKS2 '[] x2)
               -> target (TKS2 '[] x))
                -- ^ the function to zip with
           -> target (TKS2 sh x1)  -- ^ the first tensor to zip over
           -> target (TKS2 sh x2)  -- ^ the second tensor to zip over
           -> target (TKS2 sh x)
szipWith0N = tszipWith0N
szipWith3 :: ( KnownShS (Drop m sh1), KnownShS (Drop m sh2)
             , KnownShS (Drop m sh3), KnownShS (Take m sh), KnownShS sh
             , KnownSTK x, KnownSTK x1, KnownSTK x2, KnownSTK x3
             , sh1 ~ Take m sh ++ Drop m sh1
             , sh2 ~ Take m sh ++ Drop m sh2
             , sh3 ~ Take m sh ++ Drop m sh3, BaseTensor target )
          => (target (TKS2 (Drop m sh1) x1) -> target (TKS2 (Drop m sh2) x2)
              -> target (TKS2 (Drop m sh3) x3)
              -> target (TKS2 (Drop m sh) x))
               -- ^ the function to zip with
          -> target (TKS2 sh1 x1)  -- ^ the first tensor to zip over
          -> target (TKS2 sh2 x2)  -- ^ the second tensor to zip over
          -> target (TKS2 sh3 x3)  -- ^ the third tensor to zip over
          -> target (TKS2 sh x)
szipWith3 f u v w = sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix))
szipWith31 :: ( KnownNat n
              , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh
              , KnownSTK x, KnownSTK x1, KnownSTK x2, KnownSTK x3
              , BaseTensor target )
           => (target (TKS2 sh1 x1) -> target (TKS2 sh2 x2)
               -> target (TKS2 sh3 x3)
               -> target (TKS2 sh x))
                -- ^ the function to zip with
           -> target (TKS2 (n ': sh1) x1)  -- ^ the first tensor to zip over
           -> target (TKS2 (n ': sh2) x2)  -- ^ the second tensor to zip over
           -> target (TKS2 (n ': sh3) x3)  -- ^ the third tensor to zip over
           -> target (TKS2 (n ': sh) x)
szipWith31 f u v w = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                      (v !$ (i :.$ ZIS))
                                      (w !$ (i :.$ ZIS)))
szipWith30N :: ( KnownShS sh, KnownSTK x, KnownSTK x1, KnownSTK x2, KnownSTK x3
               , BaseTensor target )
            => (target (TKS2 '[] x1) -> target (TKS2 '[] x2)
                -> target (TKS2 '[] x3)
                -> target (TKS2 '[] x))
                 -- ^ the function to zip with
            -> target (TKS2 sh x1)  -- ^ the first tensor to zip over
            -> target (TKS2 sh x2)  -- ^ the second tensor to zip over
            -> target (TKS2 sh x3)  -- ^ the third tensor to zip over
            -> target (TKS2 sh x)
szipWith30N @sh f u v w =
  gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
  $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
  $ sbuild @(Rank sh) (\ix -> f (sindex0 u ix)
                                (sindex0 v ix)
                                (sindex0 w ix))
szipWith4 :: ( KnownShS (Drop m sh1), KnownShS (Drop m sh2)
             , KnownShS (Drop m sh3), KnownShS (Drop m sh4)
             , KnownShS (Take m sh), KnownShS sh
             , KnownSTK x, KnownSTK x1, KnownSTK x2, KnownSTK x3, KnownSTK x4
             , sh1 ~ Take m sh ++ Drop m sh1
             , sh2 ~ Take m sh ++ Drop m sh2
             , sh3 ~ Take m sh ++ Drop m sh3
             , sh4 ~ Take m sh ++ Drop m sh4, BaseTensor target )
          => (target (TKS2 (Drop m sh1) x1) -> target (TKS2 (Drop m sh2) x2)
              -> target (TKS2 (Drop m sh3) x3) -> target (TKS2 (Drop m sh4) x4)
              -> target (TKS2 (Drop m sh) x))
               -- ^ the function to zip with
          -> target (TKS2 sh1 x1)  -- ^ the first tensor to zip over
          -> target (TKS2 sh2 x2)  -- ^ the second tensor to zip over
          -> target (TKS2 sh3 x3)  -- ^ the third tensor to zip over
          -> target (TKS2 sh4 x4)  -- ^ the fourth tensor to zip over
          -> target (TKS2 sh x)
szipWith4 f u v w x =
  sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix) (x !$ ix))
szipWith41 :: ( KnownNat n
              , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
              , KnownShS sh
              , KnownSTK x, KnownSTK x1, KnownSTK x2, KnownSTK x3, KnownSTK x4
              , BaseTensor target )
           => (target (TKS2 sh1 x1) -> target (TKS2 sh2 x2)
               -> target (TKS2 sh3 x3) -> target (TKS2 sh4 x4)
               -> target (TKS2 sh x))
                -- ^ the function to zip with
           -> target (TKS2 (n ': sh1) x1)  -- ^ the first tensor to zip over
           -> target (TKS2 (n ': sh2) x2)  -- ^ the second tensor to zip over
           -> target (TKS2 (n ': sh3) x3)  -- ^ the third tensor to zip over
           -> target (TKS2 (n ': sh4) x4)  -- ^ the fourth tensor to zip over
           -> target (TKS2 (n ': sh) x)
szipWith41 f u v w x = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                        (v !$ (i :.$ ZIS))
                                        (w !$ (i :.$ ZIS))
                                        (x !$ (i :.$ ZIS)))
szipWith40N :: ( KnownShS sh, KnownSTK x
               , KnownSTK x1, KnownSTK x2, KnownSTK x3, KnownSTK x4
               , BaseTensor target )
            => (target (TKS2 '[] x1) -> target (TKS2 '[] x2)
                -> target (TKS2 '[] x3) -> target (TKS2 '[] x4)
                -> target (TKS2 '[] x))
                 -- ^ the function to zip with
            -> target (TKS2 sh x1)  -- ^ the first tensor to zip over
            -> target (TKS2 sh x2)  -- ^ the second tensor to zip over
            -> target (TKS2 sh x3)  -- ^ the third tensor to zip over
            -> target (TKS2 sh x4)  -- ^ the fourth tensor to zip over
            -> target (TKS2 sh x)
szipWith40N @sh f u v w x =
  gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
  $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
  $ sbuild @(Rank sh) (\ix -> f (sindex0 u ix)
                                (sindex0 v ix)
                                (sindex0 w ix)
                                (sindex0 x ix))

xbuild1 :: (KnownNat k, KnownShX sh, KnownSTK x, BaseTensor target)
        => (IntOf target -> target (TKX2 sh x))
             -- ^ the function to build with
        -> target (TKX2 (Just k ': sh) x)
xbuild1 = txbuild1
-- xmap and other special cases of build can be defined by the user.

rfold
  :: ( KnownNat n, KnownNat m, KnownSTK xn, KnownSTK xm
     , BaseTensor target, LetTensor target )
  => (forall f. ADReady f => f (TKR2 n xn) -> f (TKR2 m xm) -> f (TKR2 n xn))
       -- ^ the function to fold with
  -> target (TKR2 n xn)  -- ^ the initial accumulator
  -> target (TKR2 (1 + m) xm)  -- ^ the inputs
  -> target (TKR2 n xn)
{-# INLINE rfold #-}
rfold f acc0 es =
  withSNat (rwidth es) $ \k -> tfold k knownSTK knownSTK f acc0 es
rscan
  :: ( KnownNat n, KnownNat m, KnownSTK xn, KnownSTK xm
     , BaseTensor target, LetTensor target )
  => (forall f. ADReady f => f (TKR2 n xn) -> f (TKR2 m xm) -> f (TKR2 n xn))
       -- ^ the function to fold with
  -> target (TKR2 n xn)  -- ^ the initial accumulator
  -> target (TKR2 (1 + m) xm)  -- ^ the inputs
  -> target (TKR2 (1 + n) xn)
{-# INLINE rscan #-}
rscan f acc0 es =
  withSNat (rwidth es) $ \k -> tscan k knownSTK knownSTK f acc0 es
sfold
  :: ( KnownNat k, KnownShS sh, KnownShS shm, KnownSTK xn, KnownSTK xm
     , BaseTensor target, LetTensor target )
  => (forall f. ADReady f
      => f (TKS2 sh xn) -> f (TKS2 shm xm) -> f (TKS2 sh xn))
       -- ^ the function to fold with
  -> target (TKS2 sh xn)  -- ^ the initial accumulator
  -> target (TKS2 (k ': shm) xm)  -- ^ the inputs
  -> target (TKS2 sh xn)
{-# INLINE sfold #-}
sfold @k = tfold (SNat @k) knownSTK knownSTK
sscan
  :: ( KnownNat k, KnownShS sh, KnownShS shm, KnownSTK xn, KnownSTK xm
     , BaseTensor target, LetTensor target )
  => (forall f. ADReady f
      => f (TKS2 sh xn) -> f (TKS2 shm xm) -> f (TKS2 sh xn))
       -- ^ the function to scan with
  -> target (TKS2 sh xn)  -- ^ the initial accumulator
  -> target (TKS2 (k ': shm) xm)  -- ^ the inputs
  -> target (TKS2 (1 + k ': sh) xn)
{-# INLINE sscan #-}
sscan @k = tscan (SNat @k) knownSTK knownSTK
xfold
  :: ( KnownNat k, KnownShX sh, KnownShX shm, KnownSTK xn, KnownSTK xm
     , BaseTensor target, LetTensor target )
  => (forall f. ADReady f
      => f (TKX2 sh xn) -> f (TKX2 shm xm) -> f (TKX2 sh xn))
       -- ^ the function to scan with
  -> target (TKX2 sh xn)  -- ^ the initial accumulator
  -> target (BuildTensorKind k (TKX2 shm xm))  -- ^ the inputs
  -> target (TKX2 sh xn)
{-# INLINE xfold #-}
xfold @k = tfold (SNat @k) knownSTK knownSTK
xscan
  :: ( KnownNat k, KnownShX sh, KnownShX shm, KnownSTK xn, KnownSTK xm
     , BaseTensor target, LetTensor target )
  => (forall f. ADReady f
      => f (TKX2 sh xn) -> f (TKX2 shm xm) -> f (TKX2 sh xn))
       -- ^ the function to scan with
  -> target (TKX2 sh xn)  -- ^ the initial accumulator
  -> target (BuildTensorKind k (TKX2 shm xm))  -- ^ the inputs
  -> target (BuildTensorKind (1 + k) (TKX2 sh xn))
{-# INLINE xscan #-}
xscan @k = tscan (SNat @k) knownSTK knownSTK

-- | Reverse derivative.
--
-- The function argument needs to be quantified,
-- because otherwise in the ADVal instance one could put an illegal
-- @DeltaInput@ there, confusing the two levels of contangents.
kgrad :: forall x r target. BaseTensor target
     => (forall f. ADReady f => f x -> f (TKScalar r))  -- ^ x |-> TKScalar r
     -> FullShapeTK x  -- ^ shape of x and dx
     -> target x  -- ^ input x
     -> target (ADTensorKind x)  -- ^ gradient dx
kgrad f xftk =
  \ !es -> tApply (tgrad @target xftk (HFun f)) es
rvjp :: forall n x r target. BaseTensor target
       => (forall f. ADReady f => f x -> f (TKR2 n r))  -- ^ x |-> z
       -> FullShapeTK x  -- ^ shape of x and dx
       -> target x  -- ^ input x
       -> target (ADTensorKind (TKR2 n r))  -- ^ incoming cotangent dz
       -> target (ADTensorKind x)  -- ^ gradient dx
rvjp f xftk =
  \ !es !dt -> tApply (tvjp @target xftk $ HFun f) (tpair dt es)
rjvp :: forall n x r target. BaseTensor target
     => (forall f. ADReady f => f x -> f (TKR2 n r))  -- ^ x |-> z
     -> FullShapeTK x  -- ^ shape of x and dx
     -> target x  -- ^ input x
     -> target (ADTensorKind x)  -- ^ incoming tangent dx
     -> target (ADTensorKind (TKR2 n r))  -- ^ derivative dz
rjvp f xftk =
  \ !es !ds -> tApply (tjvp @target xftk $ HFun f) (tpair ds es)
svjp :: forall sh x r target. BaseTensor target
       => (forall f. ADReady f => f x -> f (TKS2 sh r))  -- ^ x |-> z
       -> FullShapeTK x  -- ^ shape of x and dx
       -> target x  -- ^ input x
       -> target (ADTensorKind (TKS2 sh r))  -- ^ incoming cotangent dz
       -> target (ADTensorKind x)  -- ^ gradient dx
svjp f xftk =
  \ !es !dt -> tApply (tvjp @target xftk $ HFun f) (tpair dt es)  -- ^ x |-> z
sjvp :: forall sh x r target. BaseTensor target
     => (forall f. ADReady f => f x -> f (TKS2 sh r))
     -> FullShapeTK x  -- ^ shape of x and dx
     -> target x  -- ^ input x
     -> target (ADTensorKind x)  -- ^ incoming tangent dx
     -> target (ADTensorKind (TKS2 sh r))  -- ^ derivative dz
sjvp f xftk =
  \ !es !ds -> tApply (tjvp @target xftk $ HFun f) (tpair ds es)

-- These take @target@ first, because they change the target.
rprimalPart :: BaseTensor target
            => target (TKR2 n x) -> PrimalOf target (TKR2 n x)
rprimalPart = tprimalPart
rdualPart :: (BaseTensor target, KnownNat n, KnownSTK x)
          => target (TKR2 n x) -> DualOf target (TKR2 n x)
rdualPart = tdualPart knownSTK
rfromPrimal :: (BaseTensor target, KnownNat n, KnownSTK x)
            => PrimalOf target (TKR2 n x) -> target (TKR2 n x)
rfromPrimal = tfromPrimal knownSTK
rfromDual :: BaseTensor target
          => DualOf target (TKR2 n x) -> target (TKR2 n x)
rfromDual = tfromDual
rScale :: ( BaseTensor target, KnownNat n, GoodScalar r
          , Num (target (TKR n r)), Num (PrimalOf target (TKR n r)) )
       => PrimalOf target (TKR n r) -> DualOf target (TKR n r)
       -> DualOf target (TKR n r)
rScale @target = tScale @target knownSTK

sprimalPart :: BaseTensor target
            => target (TKS2 sh x) -> PrimalOf target (TKS2 sh x)
sprimalPart = tprimalPart
sdualPart :: (BaseTensor target, KnownShS sh, KnownSTK x)
          => target (TKS2 sh x) -> DualOf target (TKS2 sh x)
sdualPart = tdualPart knownSTK
sfromPrimal :: (BaseTensor target, KnownShS sh, KnownSTK x)
            => PrimalOf target (TKS2 sh x) -> target (TKS2 sh x)
sfromPrimal = tfromPrimal knownSTK
sfromDual :: BaseTensor target
          => DualOf target (TKS2 sh x) -> target (TKS2 sh x)
sfromDual = tfromDual
sScale :: ( BaseTensor target, KnownShS sh, GoodScalar r
          , Num (target (TKS sh r)), Num (PrimalOf target (TKS sh r)) )
       => PrimalOf target (TKS sh r) -> DualOf target (TKS sh r)
       -> DualOf target (TKS sh r)
sScale @target = tScale @target knownSTK

xprimalPart :: BaseTensor target
            => target (TKX2 sh x) -> PrimalOf target (TKX2 sh x)
xprimalPart = tprimalPart
xdualPart :: (BaseTensor target, KnownShX sh, KnownSTK x)
          => target (TKX2 sh x) -> DualOf target (TKX2 sh x)
xdualPart = tdualPart knownSTK
xfromPrimal :: (BaseTensor target, KnownShX sh, KnownSTK x)
            => PrimalOf target (TKX2 sh x) -> target (TKX2 sh x)
xfromPrimal = tfromPrimal knownSTK
xfromDual :: BaseTensor target
          => DualOf target (TKX2 sh x) -> target (TKX2 sh x)
xfromDual = tfromDual
xScale :: ( BaseTensor target, KnownShX sh, GoodScalar r
          , Num (target (TKX sh r)), Num (PrimalOf target (TKX sh r)) )
       => PrimalOf target (TKX sh r) -> DualOf target (TKX sh r)
       -> DualOf target (TKX sh r)
xScale @target = tScale @target knownSTK

kprimalPart :: BaseTensor target
            => target (TKScalar r) -> PrimalOf target (TKScalar r)
kprimalPart = tprimalPart
kdualPart :: (BaseTensor target, GoodScalar r)
          => target (TKScalar r) -> DualOf target (TKScalar r)
kdualPart = tdualPart knownSTK
kfromPrimal :: (BaseTensor target, GoodScalar r)
            => PrimalOf target (TKScalar r) -> target (TKScalar r)
kfromPrimal = tfromPrimal knownSTK
kfromDual :: BaseTensor target
          => DualOf target (TKScalar r) -> target (TKScalar r)
kfromDual = tfromDual
kScale :: ( BaseTensor target, GoodScalar r
          , Num (target (TKScalar r)), Num (PrimalOf target (TKScalar r)) )
       => PrimalOf target (TKScalar r) -> DualOf target (TKScalar r)
       -> DualOf target (TKScalar r)
kScale @target = tScale @target knownSTK
