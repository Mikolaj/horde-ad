{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The mixed tensor operations intended for the library user.
-- All these operations together with operations of the remaining two tensor
-- variants are gathered in "HordeAd.OpsTensor". The less user-friendly
-- prototypes of most of these operation can be found in "HordeAd.Core.Ops"
-- where some additional rarely used operations reside as well.
module HordeAd.OpsTensorMixed
  ( -- * Shape manipulation
    xshape, xlength, xsize, xwidth
  , tsize, tftk
    -- * Constructing arrays from concrete values, lists and vectors
  , xconcrete, xscalar, xrepl, xingestData, xfromListLinear
  , kconcrete
  , xfromList, xfromVector, xfromVector0N, xfromList0N, xunravelToList
    -- * Main array operations
  , tunit, tlet, ifH, minH, maxH, tpair, tproject1, tproject2
  , xsum, xsum0, xdot0, xdot1In, xmatvecmul, xmatmul2, xreplicate, xreplicate0N
  , xindex, xindex0, xoneHot, xscatter, xscatter1, xgather, xgather1
  , xtr, xtranspose, xflatten, xreshape
   -- * Auxiliary array operations
  , xfloor, xfromIntegral, xcast, xminIndex, xmaxIndex, xiota
  , kfloor, kfromIntegral, kcast
  , xappend, xappend0, xconcat, xslice, xuncons, xreverse
    -- * Array operations derived from `build`
  , xbuild, xbuild1
    -- * Array operations derived from `mapAccum`
  , xfold, xscan, tmapAccumR, tmapAccumL
    -- * Array operations producing derivatives
  , kgrad
    -- * Operations dealing with dual numbers
  , xprimalPart, xdualPart, xfromPrimal, xfromDual, xScale
  , kprimalPart, kdualPart, kfromPrimal, kfromDual, kScale
    -- * Array operations that utilize unwinding of nested arrays
  , treplTarget, tdefTarget, taddTarget, tmultTarget, tdot0Target
    -- * Minimal re-exports to make this module a higher level replacement for the mixed part of "HordeAd.Core.Ops"
  , ADReady
  , LetTensor, BaseTensor
  ) where

import Prelude ()

import HordeAd.OpsTensor
