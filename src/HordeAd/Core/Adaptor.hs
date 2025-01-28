{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Adaptors for working with types of collections of tensors
-- that are isomorphic to products, that is, tuples, sized lists
-- and user types of statically known size, as long as they have
-- the proper instances defined.
--
-- The collectionsare necessary as a representation of the domains
-- of objective functions that become the codomains of the reverse
-- derivative functions and also to handle multiple arguments
-- and results of fold-like operations.
module HordeAd.Core.Adaptor
  ( AdaptableHVector(..), TermValue(..), DualNumberValue(..)
  , ForgetShape(..), RandomHVector(..)
  , stkOfListR
  ) where

import Prelude

import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:))
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat, type (-), type (<=?))
import System.Random
import Data.Vector.Generic qualified as V

import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested (ListR (..), KnownShS (..), Rank)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shsSize)

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Adaptor classes

-- Inspired by adaptors from @tomjaguarpaw's branch.
class AdaptableHVector (target :: Target) vals where
  type X vals :: TensorKindType
  toHVectorOf :: vals -> target (X vals)
    -- ^ represent a collection of tensors
  parseHVector :: target (X vals) -> vals
    -- ^ recovers a collection of tensors from its canonical representation,
    -- using the general shape recorded in another collection of the same type;
    -- the remaining data may be used in a another structurally recursive
    -- call working on the same data to build a larger compound collection
  parseHVectorAD :: target (ADTensorKind (X vals)) -> vals

class TermValue vals where
  type Value vals = result | result -> vals
                    -- ^ a helper type, with the same general shape,
                    -- but possibly more concrete, e.g., arrays instead of terms
                    -- where the injectivity is crucial to limit the number
                    -- of type applications the library user has to supply
  fromValue :: Value vals -> vals  -- ^ an embedding

class DualNumberValue vals where
  type DValue vals  -- ^ a helper type, with the same general shape,
                    -- but possibly more concrete, e.g., arrays instead of terms
                    -- where the injectivity is hard to obtain, but is not
                    -- so important, because the type is used more internally
                    -- and for tests rather than by the library users
  fromDValue :: DValue vals -> vals  -- ^ an embedding

-- | A helper class for for converting all tensors inside a type
-- from shaped to ranked.
class ForgetShape vals where
  type NoShape vals
  forgetShape :: vals -> NoShape vals

-- | A helper class for randomly generating initial parameters.
class RandomHVector vals where
  randomVals :: SplitGen g => Double -> g -> (vals, g)


-- * Basic Adaptor class instances

instance (TensorKind y, BaseTensor target)
         => AdaptableHVector target (target y) where
{-
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstTensor AstMethodLet s) (AstTensor AstMethodLet s (TKR n Double)) #-}
  TODO: RULE left-hand side too complicated to desugar in GHC 9.6.4
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
  type X (target y) = y
  toHVectorOf = id
  parseHVector t = t
  parseHVectorAD t = fromADTensorKindShared (stensorKind @y) t

instance (BaseTensor target, BaseTensor (PrimalOf target), TensorKind y)
         => DualNumberValue (target y) where
  type DValue (target y) = RepN y
  fromDValue t = tfromPrimal (stensorKind @y)
                 $ tconcrete (tftkG (stensorKind @y) $ unRepN t) t

instance ForgetShape (target (TKR n r)) where
  type NoShape (target (TKR n r)) = target (TKR n r)
  forgetShape = id

instance (KnownShS sh, GoodScalar r, BaseTensor target)
         => ForgetShape (target (TKS sh r)) where
  type NoShape (target (TKS sh r)) = target (TKR (Rank sh) r)
  forgetShape = rfromS

instance ForgetShape (target (TKX sh r)) where
  type NoShape (target (TKX sh r)) = target (TKX sh r)
  forgetShape = id

instance ( KnownShS sh, GoodScalar r, Fractional r, Random r
         , BaseTensor target )
         => RandomHVector (target (TKS sh r)) where
  randomVals @g range g =
    let createRandomVector :: Int -> g -> target (TKS sh r)
        createRandomVector n seed =
          srepl (2 * realToFrac range)
          * (sconcrete
               (Nested.sfromVector knownShS (V.fromListN n (randoms seed)))
             - srepl 0.5)
        (g1, g2) = splitGen g
        arr = createRandomVector (shsSize (knownShS @sh)) g1
    in (arr, g2)


-- * Compound instances

type family Tups n t where
  Tups 0 t = TKUnit
  Tups n t = TKProduct t (Tups (n - 1) t)

stkOfListR :: forall t n.
              STensorKindType t -> SNat n -> STensorKindType (Tups n t)
stkOfListR _ (SNat' @0) = stensorKind
stkOfListR stk SNat =
  gcastWith (unsafeCoerceRefl :: (1 <=? n) :~: True) $
  gcastWith (unsafeCoerceRefl :: Tups n t :~: TKProduct t (Tups (n - 1) t)) $
  STKProduct stk (stkOfListR stk (SNat @(n - 1)))

instance ( BaseTensor target, KnownNat n, AdaptableHVector target a
         , TensorKind (X a), TensorKind (ADTensorKind (X a)) )
         => AdaptableHVector target (ListR n a) where
  type X (ListR n a) = Tups n (X a)
  toHVectorOf ZR = tunit
  toHVectorOf ((:::) @n1 a rest)
   | Dict <- lemTensorKindOfSTK (stkOfListR (stensorKind @(X a)) (SNat @n1)) =
    gcastWith (unsafeCoerceRefl
               :: X (ListR n a) :~: TKProduct (X a) (X (ListR n1 a))) $
    let a1 = toHVectorOf a
        rest1 = toHVectorOf rest
    in tpair a1 rest1
  parseHVector tups = case SNat @n of
    SNat' @0 -> ZR
    _ ->
      gcastWith (unsafeCoerceRefl :: (1 <=? n) :~: True) $
      gcastWith (unsafeCoerceRefl
                 :: X (ListR n a) :~: TKProduct (X a) (X (ListR (n - 1) a))) $
      withTensorKind (stkOfListR (stensorKind @(X a)) (SNat @(n - 1))) $
      let (a1, rest1) = (tproject1 tups, tproject2 tups)
          a = parseHVector a1
          rest = parseHVector rest1
      in (a ::: rest)
  parseHVectorAD tups = case SNat @n of
    SNat' @0 -> ZR
    _ ->
      gcastWith (unsafeCoerceRefl :: (1 <=? n) :~: True) $
      gcastWith (unsafeCoerceRefl
                 :: ADTensorKind (Tups (n - 1) (X a))
                    :~: Tups (n - 1) (ADTensorKind (X a))) $
      gcastWith (unsafeCoerceRefl
                 :: X (ListR n a) :~: TKProduct (X a) (X (ListR (n - 1) a))) $
      withTensorKind (stkOfListR (stensorKind
                                    @(ADTensorKind (X a))) (SNat @(n - 1))) $
      let (a1, rest1) = (tproject1 tups, tproject2 tups)
          a = parseHVectorAD a1
          rest = parseHVectorAD @_ @(ListR (n - 1) a) rest1
      in (a ::: rest)

instance TermValue a => TermValue (ListR n a) where
  type Value (ListR n a) = ListR n (Value a)
  fromValue ZR = ZR
  fromValue (a ::: rest) = fromValue a ::: fromValue rest

instance DualNumberValue a => DualNumberValue (ListR n a) where
  type DValue (ListR n a) = ListR n (DValue a)
  fromDValue ZR = ZR
  fromDValue (a ::: rest) = fromDValue a ::: fromDValue rest

instance ForgetShape a => ForgetShape (ListR n a) where
  type NoShape (ListR n a) = ListR n (NoShape a)
  forgetShape ZR = ZR
  forgetShape (a ::: rest) = forgetShape a ::: forgetShape rest

instance (RandomHVector a, KnownNat n) => RandomHVector (ListR n a) where
  randomVals range g = case cmpNat (Proxy @n) (Proxy @0)  of
    LTI -> error "randomVals: impossible"
    EQI -> (ZR, g)
    GTI -> gcastWith (unsafeCoerceRefl :: (1 <=? n) :~: True) $
           let (v, g1) = randomVals range g
               (rest, g2) = randomVals @(ListR (n - 1) a) range g1
           in (v ::: rest, g2)

instance ( BaseTensor target
         , AdaptableHVector target a, TensorKind (X a), TensorKind (ADTensorKind (X a))
         , AdaptableHVector target b, TensorKind (X b), TensorKind (ADTensorKind (X b)) )
         => AdaptableHVector target (a, b) where
  type X (a, b) = TKProduct (X a) (X b)
  toHVectorOf (a, b) =
    let a1 = toHVectorOf a
        b1 = toHVectorOf b
    in tpair a1 b1
  parseHVector ab =
    let (a1, b1) =
          ( tproject1 ab
          , tproject2 ab )
        a = parseHVector a1
        b = parseHVector b1
    in (a, b)
  parseHVectorAD ab =
    let (a1, b1) =
          ( tproject1 ab
          , tproject2 ab )
        a = parseHVectorAD a1
        b = parseHVectorAD b1
    in (a, b)

instance (TermValue a, TermValue b) => TermValue (a, b) where
  type Value (a, b) = (Value a, Value b)
  fromValue (va, vb) = (fromValue va, fromValue vb)

instance (DualNumberValue a, DualNumberValue b) => DualNumberValue (a, b) where
  type DValue (a, b) = (DValue a, DValue b)
  fromDValue (va, vb) = (fromDValue va, fromDValue vb)

instance ( ForgetShape a
         , ForgetShape b ) => ForgetShape (a, b) where
  type NoShape (a, b) = (NoShape a, NoShape b)
  forgetShape (a, b) = (forgetShape a, forgetShape b)

instance ( RandomHVector a
         , RandomHVector b ) => RandomHVector (a, b) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
    in ((v1, v2), g2)

instance ( BaseTensor target
         , AdaptableHVector target a, TensorKind (X a), TensorKind (ADTensorKind (X a))
         , AdaptableHVector target b, TensorKind (X b), TensorKind (ADTensorKind (X b))
         , AdaptableHVector target c, TensorKind (X c), TensorKind (ADTensorKind (X c)) )
         => AdaptableHVector target (a, b, c) where
  type X (a, b, c) = TKProduct (TKProduct (X a) (X b)) (X c)
  toHVectorOf (a, b, c) =
    let a1 = toHVectorOf a
        b1 = toHVectorOf b
        c1 = toHVectorOf c
    in tpair (tpair a1 b1) c1
  parseHVector abc =
    let (a1, b1, c1) =
          ( tproject1 (tproject1 abc)
          , tproject2 (tproject1 abc)
          , tproject2 abc )
        a = parseHVector a1
        b = parseHVector b1
        c = parseHVector c1
    in (a, b, c)
  parseHVectorAD abc =
    let (a1, b1, c1) =
          ( tproject1 (tproject1 abc)
          , tproject2 (tproject1 abc)
          , tproject2 abc )
        a = parseHVectorAD a1
        b = parseHVectorAD b1
        c = parseHVectorAD c1
    in (a, b, c)

instance (TermValue a, TermValue b, TermValue c)
         => TermValue (a, b, c) where
  type Value (a, b, c) = (Value a, Value b, Value c)
  fromValue (va, vb, vc) = (fromValue va, fromValue vb, fromValue vc)

instance (DualNumberValue a, DualNumberValue b, DualNumberValue c)
         => DualNumberValue (a, b, c) where
  type DValue (a, b, c) = (DValue a, DValue b, DValue c)
  fromDValue (va, vb, vc) = (fromDValue va, fromDValue vb, fromDValue vc)

instance ( ForgetShape a
         , ForgetShape b
         , ForgetShape c ) => ForgetShape (a, b, c) where
  type NoShape (a, b, c) = (NoShape a, NoShape b, NoShape c)
  forgetShape (a, b, c) = (forgetShape a, forgetShape b, forgetShape c)

instance ( RandomHVector a
         , RandomHVector b
         , RandomHVector c ) => RandomHVector (a, b, c) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
    in ((v1, v2, v3), g3)

instance ( BaseTensor target
         , AdaptableHVector target a, TensorKind (X a), TensorKind (ADTensorKind (X a))
         , AdaptableHVector target b, TensorKind (X b), TensorKind (ADTensorKind (X b))
         , AdaptableHVector target c, TensorKind (X c), TensorKind (ADTensorKind (X c))
         , AdaptableHVector target d, TensorKind (X d), TensorKind (ADTensorKind (X d)) )
         => AdaptableHVector target (a, b, c, d) where
  type X (a, b, c, d) = TKProduct (TKProduct (X a) (X b))
                                  (TKProduct (X c) (X d))
  toHVectorOf (a, b, c, d) =
    let a1 = toHVectorOf a
        b1 = toHVectorOf b
        c1 = toHVectorOf c
        d1 = toHVectorOf d
    in  tpair (tpair a1 b1) (tpair c1 d1)
  parseHVector abcd =
    let (a1, b1, c1, d1) =
          ( tproject1 (tproject1 abcd)
          , tproject2 (tproject1 abcd)
          , tproject1 (tproject2 abcd)
          , tproject2 (tproject2 abcd) )
        a = parseHVector a1
        b = parseHVector b1
        c = parseHVector c1
        d = parseHVector d1
    in (a, b, c, d)
  parseHVectorAD abcd =
    let (a1, b1, c1, d1) =
          ( tproject1 (tproject1 abcd)
          , tproject2 (tproject1 abcd)
          , tproject1 (tproject2 abcd)
          , tproject2 (tproject2 abcd) )
        a = parseHVectorAD a1
        b = parseHVectorAD b1
        c = parseHVectorAD c1
        d = parseHVectorAD d1
    in (a, b, c, d)

instance (TermValue a, TermValue b, TermValue c, TermValue d)
         => TermValue (a, b, c, d) where
  type Value (a, b, c, d) = (Value a, Value b, Value c, Value d)
  fromValue (va, vb, vc, vd) =
    (fromValue va, fromValue vb, fromValue vc, fromValue vd)

instance ( DualNumberValue a, DualNumberValue b, DualNumberValue c
         , DualNumberValue d )
         => DualNumberValue (a, b, c, d) where
  type DValue (a, b, c, d) = (DValue a, DValue b, DValue c, DValue d)
  fromDValue (va, vb, vc, vd) =
    (fromDValue va, fromDValue vb, fromDValue vc, fromDValue vd)

instance ( ForgetShape a
         , ForgetShape b
         , ForgetShape c
         , ForgetShape d ) => ForgetShape (a, b, c, d) where
  type NoShape (a, b, c, d) =
    (NoShape a, NoShape b, NoShape c, NoShape d)
  forgetShape (a, b, c, d) =
    (forgetShape a, forgetShape b, forgetShape c, forgetShape d)

instance ( RandomHVector a
         , RandomHVector b
         , RandomHVector c
         , RandomHVector d ) => RandomHVector (a, b, c, d) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
        (v4, g4) = randomVals range g3
    in ((v1, v2, v3, v4), g4)

instance ( BaseTensor target
         , AdaptableHVector target a, TensorKind (X a), TensorKind (ADTensorKind (X a))
         , AdaptableHVector target b, TensorKind (X b), TensorKind (ADTensorKind (X b))
         , AdaptableHVector target c, TensorKind (X c), TensorKind (ADTensorKind (X c))
         , AdaptableHVector target d, TensorKind (X d), TensorKind (ADTensorKind (X d))
         , AdaptableHVector target e, TensorKind (X e), TensorKind (ADTensorKind (X e)) )
         => AdaptableHVector target (a, b, c, d, e) where
  type X (a, b, c, d, e) = TKProduct (TKProduct (TKProduct (X a) (X b)) (X c))
                                     (TKProduct (X d) (X e))
  toHVectorOf (a, b, c, d, e) =
    let a1 = toHVectorOf a
        b1 = toHVectorOf b
        c1 = toHVectorOf c
        d1 = toHVectorOf d
        e1 = toHVectorOf e
    in tpair (tpair (tpair a1 b1) c1) (tpair d1 e1)
  parseHVector abcde =
    let (a1, b1, c1, d1, e1) =
          ( tproject1 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 abcde)
          , tproject1 (tproject2 abcde)
          , tproject2 (tproject2 abcde) )
        a = parseHVector a1
        b = parseHVector b1
        c = parseHVector c1
        d = parseHVector d1
        e = parseHVector e1
    in (a, b, c, d, e)
  parseHVectorAD abcde =
    let (a1, b1, c1, d1, e1) =
          ( tproject1 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 abcde)
          , tproject1 (tproject2 abcde)
          , tproject2 (tproject2 abcde) )
        a = parseHVectorAD a1
        b = parseHVectorAD b1
        c = parseHVectorAD c1
        d = parseHVectorAD d1
        e = parseHVectorAD e1
    in (a, b, c, d, e)

instance (TermValue a, TermValue b, TermValue c, TermValue d, TermValue e)
         => TermValue (a, b, c, d, e) where
  type Value (a, b, c, d, e) = (Value a, Value b, Value c, Value d, Value e)
  fromValue (va, vb, vc, vd, ve) =
    (fromValue va, fromValue vb, fromValue vc, fromValue vd, fromValue ve)

instance ( DualNumberValue a, DualNumberValue b, DualNumberValue c
         , DualNumberValue d, DualNumberValue e )
         => DualNumberValue (a, b, c, d, e) where
  type DValue (a, b, c, d, e) =
    (DValue a, DValue b, DValue c, DValue d, DValue e)
  fromDValue (va, vb, vc, vd, ve) =
    (fromDValue va, fromDValue vb, fromDValue vc, fromDValue vd, fromDValue ve)

instance ( ForgetShape a
         , ForgetShape b
         , ForgetShape c
         , ForgetShape d
         , ForgetShape e ) => ForgetShape (a, b, c, d, e) where
  type NoShape (a, b, c, d, e) =
    (NoShape a, NoShape b, NoShape c, NoShape d, NoShape e)
  forgetShape (a, b, c, d, e) =
    (forgetShape a, forgetShape b, forgetShape c, forgetShape d, forgetShape e)

instance ( RandomHVector a
         , RandomHVector b
         , RandomHVector c
         , RandomHVector d
         , RandomHVector e ) => RandomHVector (a, b, c, d, e) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
        (v4, g4) = randomVals range g3
        (v5, g5) = randomVals range g4
    in ((v1, v2, v3, v4, v5), g5)
