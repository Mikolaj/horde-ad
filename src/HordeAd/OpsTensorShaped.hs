{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The shaped tensor operations intended for the casual library user.
-- All these operations together with operations of the remaining two tensor
-- variants are gathered in "HordeAd.OpsTensor".
--
-- The less user-friendly
-- prototypes of most of these operation can be found in "HordeAd.Core.Ops"
-- where some additional rarely used operations reside.
-- All these operations, together with instances of numerical classes
-- such as @Num@, @Fractional@, @IntegralH@, @RealFloatH@, @EqH@ and others
-- (see class instances of type 'HordeAd.Core.Ast.AstTensor' for the full list),
-- are a major part of the high-level API of the horde-ad library,
-- which is relatively orthogonal to the other major part,
-- the differentiation interface exposed in "HordeAd.ADEngine".
module HordeAd.OpsTensorShaped
  ( -- * Shape manipulation
    sshape, slength, ssize, swidth
  , tsize, tftk
    -- * Constructing arrays from concrete values, lists and vectors
  , sconcrete, sscalar, srepl, singestData, sfromListLinear
  , kconcrete
  , sfromList, sfromVector, sfromVector0N, sfromList0N, sunravelToList
    -- * Main array operations
  , tunit, tlet, tletPrimal, tletPlain, ifH, minH, maxH
  , tpair, tproject1, tproject2
  , ssum, ssum0, sdot0, sdot1In, smatvecmul, smatmul2, sreplicate, sreplicate0N
  , sindex, (!$), sindex0, soneHot, sscatter, sscatter1, sgather, sgather1
  , str, stranspose, sflatten, sreshape
   -- * Auxiliary array operations
  , sfloor, sfromIntegral, scast, sminIndex, smaxIndex, siota
  , kfloor, kfromIntegral, kcast
  , sappend, sslice, suncons, sreverse
    -- * Array operations derived from @build@
  , sbuild, sbuild1, smap, smap1, smap0N, szipWith, szipWith1, szipWith0N
  , szipWith3, szipWith31, szipWith30N, szipWith4, szipWith41, szipWith40N
    -- * Array operations derived from @mapAccum@
  , sfold, sscan, tfold, tscan, tmapAccumR, tmapAccumL
    -- * Array operations producing derivatives
  , kgrad, svjp, sjvp
    -- * Operations dealing with dual numbers
  , sprimalPart, sdualPart, sfromPrimal, sfromDual, sScale
  , kprimalPart, kdualPart, kfromPrimal, kfromDual, kScale
    -- * Array operations that utilize unwinding of nested arrays
  , treplTarget, tdefTarget, taddTarget, tmultTarget, tsum0Target, tdot0Target
    -- * Minimal re-exports to make this module a higher level replacement for the shaped part of "HordeAd.Core.Ops"
  , ADReady, ADReadyNoLet, ShareTensor
  , LetTensor, BaseTensor
  ) where

import Prelude ()

import HordeAd.OpsTensor
