{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The ranked tensor operations intended for the library user.
-- All these operations together with operations of the remaining two tensor
-- variants are gathered in "HordeAd.OpsTensor". The less user-friendly
-- prototypes of most of these operation can be found in "HordeAd.Core.Ops"
-- where some additional rarely used operations reside as well.
module HordeAd.OpsTensorRanked
  ( -- * Shape manipulation
    rshape, rlength, rsize, rwidth
  , tsize, tftk
    -- * Constructing arrays from concrete values, lists and vectors
  , rconcrete, rscalar, rrepl, ringestData, rfromListLinear
  , kconcrete
  , rfromList, rfromVector, rfromVector0N, rfromList0N, runravelToList
    -- * Main array operations
  , tunit, tlet, ifH, minH, maxH, tpair, tproject1, tproject2
  , rsum, rsum0, rdot0, rdot1In, rmatvecmul, rmatmul2, rreplicate, rreplicate0N
  , rindex, (!), rindex0, roneHot, rscatter, rscatter1, rgather, rgather1
  , rtr, rtranspose, rflatten, rreshape
   -- * Auxiliary array operations
  , rfloor, rfromIntegral, rcast, rminIndex, rmaxIndex, riota
  , kfloor, kfromIntegral, kcast
  , rappend, rconcat, rslice, runcons, rreverse
    -- * Array operations derived from `build`
  , rbuild, rbuild1, rmap, rmap1, rmap0N, rzipWith, rzipWith1, rzipWith0N
  , rzipWith3, rzipWith31, rzipWith30N, rzipWith4, rzipWith41, rzipWith40N
    -- * Array operations derived from `mapAccum`
  , rfold, rscan, tmapAccumR, tmapAccumL
    -- * Array operations producing derivatives
  , kgrad, rvjp, rjvp
    -- * Operations dealing with dual numbers
  , rprimalPart, rdualPart, rfromPrimal, rfromDual, rScale
  , kprimalPart, kdualPart, kfromPrimal, kfromDual, kScale
    -- * Array operations that utilize unwinding of nested arrays
  , treplTarget, tdefTarget, taddTarget, tmultTarget, tsum0Target, tdot0Target
    -- * Minimal re-exports to make this module a higher level replacement for the ranked part of "HordeAd.Core.Ops"
  , ADReady
  , LetTensor, BaseTensor
  ) where

import Prelude ()

import HordeAd.OpsTensor
