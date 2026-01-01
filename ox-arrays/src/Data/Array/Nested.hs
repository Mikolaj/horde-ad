{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}
module Data.Array.Nested (
  -- * Ranked arrays
  Ranked(Ranked),
  ListR(ZR, (:::)),
  IxR(.., ZIR, (:.:)), IIxR,
  ShR(.., ZSR, (:$:)), IShR,
  rshape, rrank, rsize, rindex, rindexPartial, rgenerate, rgeneratePrim, rsumOuter1Prim, rsumAllPrim,
  rtranspose, rappend, rconcat, rscalar, rfromVector, rtoVector, runScalar,
  remptyArray,
  rrerankPrim,
  rreplicate, rreplicatePrim,
  rfromListOuter, rfromListOuterN,
  rfromList1, rfromList1N,
  rfromListLinear,
  rfromList1Prim, rfromList1PrimN,
  rfromListPrimLinear,
  rtoList, rtoListOuter, rtoListLinear,
  rslice, rrev1, rreshape, rflatten, riota,
  rminIndexPrim, rmaxIndexPrim, rdot1Inner, rdot,
  rnest, runNest, rzip, runzip,
  -- ** Lifting orthotope operations to 'Ranked' arrays
  rlift, rlift2,
  -- ** Conversions
  rtoXArrayPrim, rfromXArrayPrim,
  rtoMixed, rcastToMixed, rcastToShaped,
  rfromOrthotope, rtoOrthotope,
  -- ** Additional arithmetic operations
  --
  -- $integralRealFloat
  rquotArray, rremArray, ratan2Array,

  -- * Shaped arrays
  Shaped(Shaped),
  ListS(ZS, (::$)),
  IxS(.., ZIS, (:.$)), IIxS,
  ShS(.., ZSS, (:$$)), KnownShS(..),
  sshape, srank, ssize, sindex, sindexPartial, sgenerate, sgeneratePrim, ssumOuter1Prim, ssumAllPrim,
  stranspose, sappend, sscalar, sfromVector, stoVector, sunScalar,
  -- TODO: sconcat? What should its type be?
  semptyArray,
  srerankPrim,
  sreplicate, sreplicatePrim,
  sfromListOuter, sfromList1, sfromListLinear, sfromList1Prim, sfromListPrimLinear,
  stoList, stoListOuter, stoListLinear,
  sslice, srev1, sreshape, sflatten, siota,
  sminIndexPrim, smaxIndexPrim, sdot1Inner, sdot,
  snest, sunNest, szip, sunzip,
  -- ** Lifting orthotope operations to 'Shaped' arrays
  slift, slift2,
  -- ** Conversions
  stoXArrayPrim, sfromXArrayPrim,
  stoMixed, scastToMixed, stoRanked,
  sfromOrthotope, stoOrthotope,
  -- ** Additional arithmetic operations
  --
  -- $integralRealFloat
  squotArray, sremArray, satan2Array,

  -- * Mixed arrays
  Mixed,
  ListX(ZX, (::%)),
  IxX(.., ZIX, (:.%)), IIxX,
  ShX(.., ZSX, (:$%)), KnownShX(..), IShX,
  StaticShX(.., ZKX, (:!%)),
  SMayNat(..),
  mshape, mrank, msize, mindex, mindexPartial, mgenerate, mgeneratePrim, msumOuter1Prim, msumAllPrim,
  mtranspose, mappend, mconcat, mscalar, mfromVector, mtoVector, munScalar,
  memptyArray,
  mrerankPrim,
  mreplicate, mreplicatePrim,
  mfromListOuter, mfromListOuterN, mfromListOuterSN,
  mfromList1, mfromList1N, mfromList1SN,
  mfromListLinear,
  mfromList1Prim, mfromList1PrimN, mfromList1PrimSN,
  mfromListPrimLinear,
  mtoList, mtoListOuter, mtoListLinear,
  msliceN, msliceSN, mrev1, mreshape, mflatten, miota,
  mminIndexPrim, mmaxIndexPrim, mdot1Inner, mdot,
  mnest, munNest, mzip, munzip,
  -- ** Lifting orthotope operations to 'Mixed' arrays
  mlift, mlift2,
  -- ** Conversions
  mtoXArrayPrim, mfromXArrayPrim,
  mcast,
  mcastToShaped, mtoRanked,
  convert, Conversion(..),
  -- ** Additional arithmetic operations
  --
  -- $integralRealFloat
  mquotArray, mremArray, matan2Array,

  -- * Array elements
  Elt,
  PrimElt,
  Primitive(..),
  KnownElt,

  -- * Further utilities / re-exports
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

import Data.Array.Nested.Convert
import Data.Array.Nested.Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation
import Data.Array.Nested.Ranked
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types
import Data.Array.Strided.Arith
import Foreign.Storable
import GHC.TypeLits

-- $integralRealFloat
--
-- These functions are separate top-level functions, and not exposed in
-- instances for 'RealFloat' and 'Integral', because those classes include a
-- variety of other functions that make no sense for arrays.
-- This problem already occurs with 'fromInteger', 'fromRational' and 'pi', but
-- having 'Num', 'Fractional' and 'Floating' available is just too useful.
