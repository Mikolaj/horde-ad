{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS -Wno-simplifiable-class-constraints #-}
{-|
This module is API-compatible with "Data.Array.Nested", except that inputs and
outputs of the methods are traced to 'stderr'. Thus the methods also have
additional 'Show' constraints.

>>> rtranspose [1, 0] (rreshape (2 :$: 3 :$: ZSR) (riota @Int 6)) * rreshape (3 :$: 2 :$: ZSR) (rreplicate (6 :$: ZSR) (rscalar @Int 7))
oxtrace: (riota _ ... = rfromListLinear [6] [0,1,2,3,4,5])
oxtrace: (rreshape [2,3] (rfromListLinear [6] [0,1,2,3,4,5]) ... = rfromListLinear [2,3] [0,1,2,3,4,5])
oxtrace: (rtranspose [1,0] (rfromListLinear [2,3] [0,1,2,3,4,5]) ... = rfromListLinear [3,2] [0,3,1,4,2,5])
oxtrace: (rscalar _ ... = rfromListLinear [] [7])
oxtrace: (rreplicate [6] (rfromListLinear [] [7]) ... = rreplicate [6] 7)
oxtrace: (rreshape [3,2] (rreplicate [6] 7) ... = rreplicate [3,2] 7)
rfromListLinear [3,2] [0,21,7,28,14,35]

The part up until and including the @...@ is printed after @seq@ing the
arguments; the @=@ and further is printed after @seq@ing the result of the
operation. Do note that tracing means that the functions in this module are
potentially __stricter__ than the plain ones in "Data.Array.Nested".

Arguments that this module does not know how to @show@, probably due to
laziness on my side, are printed as @_@.
-}
module Data.Array.Nested.Trace (
  -- * Traced variants
  module Data.Array.Nested.Trace,

  -- * Re-exports from the plain "Data.Array.Nested" module
  Ranked(Ranked),
  ListR(ZR, (:::)),
  IxR(..), IIxR,
  ShR(..), IShR,

  Shaped(Shaped),
  ListS(ZS, (::$)),
  IxS(..), IIxS,
  ShS(..), KnownShS(..),

  Mixed,
  ListX(ZX, (::%)),
  IxX(..), IIxX,
  ShX(..), KnownShX(..), IShX,
  StaticShX(..),
  SMayNat(..),
  Conversion(..),

  Elt,
  PrimElt,
  Primitive(..),
  KnownElt,

  type (++),
  Storable,
  SNat, pattern SNat,
  pattern SZ, pattern SS,
  Perm(..), PermR,
  IsPermutation,
  KnownPerm(..),
  NumElt, IntElt, FloatElt,
  Rank, Product,
  Replicate,
  MapJust,
) where

import Prelude hiding (mappend, mconcat)

import Data.Array.Nested
import Data.Array.Nested.Trace.TH


$(concat <$> mapM convertFun
    ['rshape, 'rrank, 'rsize, 'rindex, 'rindexPartial, 'rgenerate, 'rgeneratePrim, 'rsumOuter1Prim, 'rsumAllPrim, 'rtranspose, 'rappend, 'rconcat, 'rscalar, 'rfromVector, 'rtoVector, 'runScalar, 'remptyArray, 'rrerankPrim, 'rreplicate, 'rreplicatePrim, 'rfromListOuter, 'rfromListOuterN, 'rfromList1, 'rfromList1N, 'rfromListLinear, 'rfromList1Prim, 'rfromList1PrimN, 'rfromListPrimLinear, 'rtoList, 'rtoListOuter, 'rtoListLinear, 'rslice, 'rrev1, 'rreshape, 'rflatten, 'riota, 'rminIndexPrim, 'rmaxIndexPrim, 'rdot1Inner, 'rdot, 'rnest, 'runNest, 'rzip, 'runzip, 'rlift, 'rlift2, 'rtoXArrayPrim, 'rfromXArrayPrim, 'rtoMixed, 'rcastToMixed, 'rcastToShaped, 'rfromOrthotope, 'rtoOrthotope, 'rquotArray, 'rremArray, 'ratan2Array, 'sshape, 'srank, 'ssize, 'sindex, 'sindexPartial, 'sgenerate, 'sgeneratePrim, 'ssumOuter1Prim, 'ssumAllPrim, 'stranspose, 'sappend, 'sscalar, 'sfromVector, 'stoVector, 'sunScalar, 'semptyArray, 'srerankPrim, 'sreplicate, 'sreplicatePrim, 'sfromListOuter, 'sfromList1, 'sfromListLinear, 'sfromList1Prim, 'sfromListPrimLinear, 'stoList, 'stoListOuter, 'stoListLinear, 'sslice, 'srev1, 'sreshape, 'sflatten, 'siota, 'sminIndexPrim, 'smaxIndexPrim, 'sdot1Inner, 'sdot, 'snest, 'sunNest, 'szip, 'sunzip, 'slift, 'slift2, 'stoXArrayPrim, 'sfromXArrayPrim, 'stoMixed, 'scastToMixed, 'stoRanked, 'sfromOrthotope, 'stoOrthotope, 'squotArray, 'sremArray, 'satan2Array, 'mshape, 'mrank, 'msize, 'mindex, 'mindexPartial, 'mgenerate, 'mgeneratePrim, 'msumOuter1Prim, 'msumAllPrim, 'mtranspose, 'mappend, 'mconcat, 'mscalar, 'mfromVector, 'mtoVector, 'munScalar, 'memptyArray, 'mrerankPrim, 'mreplicate, 'mreplicatePrim, 'mfromListOuter, 'mfromListOuterN, 'mfromListOuterSN, 'mfromList1, 'mfromList1N, 'mfromList1SN, 'mfromListLinear, 'mfromList1Prim, 'mfromList1PrimN, 'mfromList1PrimSN, 'mfromListPrimLinear, 'mtoList, 'mtoListOuter, 'mtoListLinear, 'msliceN, 'msliceSN, 'mrev1, 'mreshape, 'mflatten, 'miota, 'mminIndexPrim, 'mmaxIndexPrim, 'mdot1Inner, 'mdot, 'mnest, 'munNest, 'mzip, 'munzip, 'mlift, 'mlift2, 'mtoXArrayPrim, 'mfromXArrayPrim, 'mcast, 'mcastToShaped, 'mtoRanked, 'convert, 'mquotArray, 'mremArray, 'matan2Array])
