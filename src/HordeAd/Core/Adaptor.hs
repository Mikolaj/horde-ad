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
  ( AdaptableTarget(..), TermValue(..), DualNumberValue(..)
  , ForgetShape(..), RandomValue(..)
  , stkOfListR
  ) where

import Prelude

import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat, type (-), type (<=?))
import System.Random

import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested (KnownShS (..), ListR (..), Rank)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shsSize)

import HordeAd.Core.Ast
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Ops
import HordeAd.Core.OpsAst ()
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Adaptor classes

-- Inspired by adaptors from @tomjaguarpaw's branch.
class AdaptableTarget (target :: Target) vals where
  type X vals :: TensorKindType
  toTarget :: vals -> target (X vals)
    -- ^ represent a collection of tensors
  fromTarget :: target (X vals) -> vals
    -- ^ recovers a collection of tensors from its canonical representation

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
class RandomValue vals where
  randomValue :: Double -> StdGen -> (vals, StdGen)


-- * Base instances

-- TODO: these instances are messy and hard to use
instance DualNumberValue Double where
  type DValue Double = RepN (TKScalar Double)
  fromDValue (RepN d) = d

instance DualNumberValue Float where
  type DValue Float = RepN (TKScalar Float)
  fromDValue (RepN d) = d

instance TermValue (RepN (TKScalar Double)) where
  type Value (RepN (TKScalar Double)) = Double
  fromValue = RepN

instance TermValue (RepN (TKScalar Float)) where
  type Value (RepN (TKScalar Float)) = Float
  fromValue = RepN

instance AdaptableTarget target (target y) where
{-
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableTarget (AstTensor AstMethodLet s) (AstTensor AstMethodLet s (TKR n Double)) #-}
  TODO: RULE left-hand side too complicated to desugar in GHC 9.6.4
    with -O0, but not -O1
  {-# SPECIALIZE instance
      (KnownNat n, ADReadyNoLet Nested.Ranked)
      => AdaptableTarget (ADVal Nested.Ranked)
                          (ADVal Nested.Ranked Double n) #-}
  {-# SPECIALIZE instance
      (KnownNat n, ADReadyNoLet (AstRanked PrimalSpan))
      => AdaptableTarget (ADVal (AstRanked PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  type X (target y) = y
  toTarget = id
  fromTarget t = t
  {-# SPECIALIZE instance AdaptableTarget RepN (RepN (TKS sh Double)) #-}
  {-# SPECIALIZE instance AdaptableTarget RepN (RepN (TKS sh Float)) #-}
    -- a failed attempt to specialize without -fpolymorphic-specialisation

instance (BaseTensor target, BaseTensor (PrimalOf target), KnownSTK y)
         => DualNumberValue (target y) where
  type DValue (target y) = RepN y
  fromDValue t = tfromPrimal (knownSTK @y)
                 $ tconcrete (tftkG (knownSTK @y) $ unRepN t) t

instance ForgetShape (target (TKScalar r)) where
  type NoShape (target (TKScalar r)) = target (TKScalar r)
  forgetShape = id

instance ForgetShape (target (TKR n r)) where
  type NoShape (target (TKR n r)) = target (TKR n r)
  forgetShape = id

instance (KnownShS sh, GoodScalar r, ConvertTensor target)
         => ForgetShape (target (TKS sh r)) where
  type NoShape (target (TKS sh r)) = target (TKR (Rank sh) r)
  forgetShape = rfromS

instance ForgetShape (target (TKX sh r)) where
  type NoShape (target (TKX sh r)) = target (TKX sh r)
  forgetShape = id

instance (GoodScalar r, Fractional r, Random r, BaseTensor target)
         => RandomValue (target (TKScalar r)) where
  randomValue range g =
    let (r, g2) = random g
        m = 2 * realToFrac range * (r - 0.5)
    in (kconcrete m, g2)

instance ( KnownShS sh, GoodScalar r, Fractional r, Random r
         , BaseTensor target )
         => RandomValue (target (TKS sh r)) where
  randomValue range g =
    let createRandomVector :: Int -> StdGen -> target (TKS sh r)
        createRandomVector n seed =
          srepl (2 * realToFrac range)
          * (sconcrete
               (Nested.sfromVector knownShS (V.fromListN n (randoms seed)))
             - srepl 0.5)
        (g1, g2) = splitGen g
        arr = createRandomVector (shsSize (knownShS @sh)) g1
    in (arr, g2)
  -- {-# SPECIALIZE instance (KnownShS sh, GoodScalar r, Fractional r, Random r) => RandomValue (RepN (TKS sh r)) #-}
  {-# SPECIALIZE instance KnownShS sh => RandomValue (RepN (TKS sh Double)) #-}
  {-# SPECIALIZE instance KnownShS sh => RandomValue (RepN (TKS sh Float)) #-}


-- * Compound instances

type family NoShapeTensorKind tk where
  NoShapeTensorKind (TKScalar r) = TKScalar r
  NoShapeTensorKind (TKR2 n r) = TKR2 n r
  NoShapeTensorKind (TKS2 sh r) = TKR2 (Rank sh) r
  NoShapeTensorKind (TKX2 sh r) = TKX2 sh r
  NoShapeTensorKind (TKProduct y z) =
    TKProduct (NoShapeTensorKind y) (NoShapeTensorKind z)

instance ( ForgetShape (target a)
         , ForgetShape (target b)
         , target (NoShapeTensorKind a) ~ NoShape (target a)
         , target (NoShapeTensorKind b) ~ NoShape (target b)
         , BaseTensor target, LetTensor target )
         => ForgetShape (target (TKProduct a b)) where
  type NoShape (target (TKProduct a b)) =
    target (TKProduct (NoShapeTensorKind a) (NoShapeTensorKind b))
  forgetShape ab =
    tlet ab $ \abShared ->
      tpair (forgetShape (tproject1 abShared))
            (forgetShape (tproject2 abShared))

instance (RandomValue (target a), RandomValue (target b), BaseTensor target)
         => RandomValue (target (TKProduct a b)) where
  randomValue range g =
    let (v1, g1) = randomValue range g
        (v2, g2) = randomValue range g1
    in (tpair v1 v2, g2)

type family Tups n t where
  Tups 0 t = TKUnit
  Tups n t = TKProduct t (Tups (n - 1) t)

stkOfListR :: forall t n.
              STensorKind t -> SNat n -> STensorKind (Tups n t)
stkOfListR _ (SNat' @0) = stkUnit
stkOfListR stk SNat =
  gcastWith (unsafeCoerceRefl :: (1 <=? n) :~: True) $
  gcastWith (unsafeCoerceRefl :: Tups n t :~: TKProduct t (Tups (n - 1) t)) $
  STKProduct stk (stkOfListR stk (SNat @(n - 1)))

instance (BaseTensor target, KnownNat n, AdaptableTarget target a)
         => AdaptableTarget target (ListR n a) where
  type X (ListR n a) = Tups n (X a)
  toTarget ZR = tunit
  toTarget ((:::) @n1 a rest) =
    gcastWith (unsafeCoerceRefl
               :: X (ListR n a) :~: TKProduct (X a) (X (ListR n1 a))) $
    let a1 = toTarget a
        rest1 = toTarget rest
    in tpair a1 rest1
  fromTarget tups = case SNat @n of
    SNat' @0 -> ZR
    _ ->
      gcastWith (unsafeCoerceRefl :: (1 <=? n) :~: True) $
      gcastWith (unsafeCoerceRefl
                 :: X (ListR n a) :~: TKProduct (X a) (X (ListR (n - 1) a))) $
      let (a1, rest1) = (tproject1 tups, tproject2 tups)
          a = fromTarget a1
          rest = fromTarget rest1
      in (a ::: rest)
  {-# SPECIALIZE instance (KnownNat n, AdaptableTarget (AstTensor AstMethodLet FullSpan) a) => AdaptableTarget (AstTensor AstMethodLet FullSpan) (ListR n a) #-}

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

instance (RandomValue a, KnownNat n) => RandomValue (ListR n a) where
  randomValue range g = case cmpNat (Proxy @n) (Proxy @0)  of
    LTI -> error "randomValue: impossible"
    EQI -> (ZR, g)
    GTI -> gcastWith (unsafeCoerceRefl :: (1 <=? n) :~: True) $
           let (v, g1) = randomValue range g
               (rest, g2) = randomValue @(ListR (n - 1) a) range g1
           in (v ::: rest, g2)

instance ( BaseTensor target
         , AdaptableTarget target a
         , AdaptableTarget target b )
         => AdaptableTarget target (a, b) where
  type X (a, b) = TKProduct (X a) (X b)
  toTarget (a, b) =
    let a1 = toTarget a
        b1 = toTarget b
    in tpair a1 b1
  fromTarget ab =
    let (a1, b1) =
          ( tproject1 ab
          , tproject2 ab )
        a = fromTarget a1
        b = fromTarget b1
    in (a, b)
  {-# SPECIALIZE instance (AdaptableTarget (AstTensor AstMethodLet FullSpan) a, AdaptableTarget (AstTensor AstMethodLet FullSpan) b) => AdaptableTarget (AstTensor AstMethodLet FullSpan) (a, b) #-}

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

instance ( RandomValue a
         , RandomValue b ) => RandomValue (a, b) where
  randomValue range g =
    let (v1, g1) = randomValue range g
        (v2, g2) = randomValue range g1
    in ((v1, v2), g2)

instance ( BaseTensor target
         , AdaptableTarget target a
         , AdaptableTarget target b
         , AdaptableTarget target c )
         => AdaptableTarget target (a, b, c) where
  type X (a, b, c) = TKProduct (TKProduct (X a) (X b)) (X c)
  toTarget (a, b, c) =
    let a1 = toTarget a
        b1 = toTarget b
        c1 = toTarget c
    in tpair (tpair a1 b1) c1
  fromTarget abc =
    let (a1, b1, c1) =
          ( tproject1 (tproject1 abc)
          , tproject2 (tproject1 abc)
          , tproject2 abc )
        a = fromTarget a1
        b = fromTarget b1
        c = fromTarget c1
    in (a, b, c)
  {-# SPECIALIZE instance (AdaptableTarget (AstTensor AstMethodLet FullSpan) a, AdaptableTarget (AstTensor AstMethodLet FullSpan) b, AdaptableTarget (AstTensor AstMethodLet FullSpan) c) => AdaptableTarget (AstTensor AstMethodLet FullSpan) (a, b, c) #-}

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

instance ( RandomValue a
         , RandomValue b
         , RandomValue c ) => RandomValue (a, b, c) where
  randomValue range g =
    let (v1, g1) = randomValue range g
        (v2, g2) = randomValue range g1
        (v3, g3) = randomValue range g2
    in ((v1, v2, v3), g3)

instance ( BaseTensor target
         , AdaptableTarget target a
         , AdaptableTarget target b
         , AdaptableTarget target c
         , AdaptableTarget target d)
         => AdaptableTarget target (a, b, c, d) where
  type X (a, b, c, d) = TKProduct (TKProduct (X a) (X b))
                                  (TKProduct (X c) (X d))
  toTarget (a, b, c, d) =
    let a1 = toTarget a
        b1 = toTarget b
        c1 = toTarget c
        d1 = toTarget d
    in  tpair (tpair a1 b1) (tpair c1 d1)
  fromTarget abcd =
    let (a1, b1, c1, d1) =
          ( tproject1 (tproject1 abcd)
          , tproject2 (tproject1 abcd)
          , tproject1 (tproject2 abcd)
          , tproject2 (tproject2 abcd) )
        a = fromTarget a1
        b = fromTarget b1
        c = fromTarget c1
        d = fromTarget d1
    in (a, b, c, d)
  {-# SPECIALIZE instance (AdaptableTarget (AstTensor AstMethodLet FullSpan) a, AdaptableTarget (AstTensor AstMethodLet FullSpan) b, AdaptableTarget (AstTensor AstMethodLet FullSpan) c, AdaptableTarget (AstTensor AstMethodLet FullSpan) d) => AdaptableTarget (AstTensor AstMethodLet FullSpan) (a, b, c, d) #-}

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

instance ( RandomValue a
         , RandomValue b
         , RandomValue c
         , RandomValue d ) => RandomValue (a, b, c, d) where
  randomValue range g =
    let (v1, g1) = randomValue range g
        (v2, g2) = randomValue range g1
        (v3, g3) = randomValue range g2
        (v4, g4) = randomValue range g3
    in ((v1, v2, v3, v4), g4)

instance ( BaseTensor target
         , AdaptableTarget target a
         , AdaptableTarget target b
         , AdaptableTarget target c
         , AdaptableTarget target d
         , AdaptableTarget target e)
         => AdaptableTarget target (a, b, c, d, e) where
  type X (a, b, c, d, e) = TKProduct (TKProduct (TKProduct (X a) (X b)) (X c))
                                     (TKProduct (X d) (X e))
  toTarget (a, b, c, d, e) =
    let a1 = toTarget a
        b1 = toTarget b
        c1 = toTarget c
        d1 = toTarget d
        e1 = toTarget e
    in tpair (tpair (tpair a1 b1) c1) (tpair d1 e1)
  fromTarget abcde =
    let (a1, b1, c1, d1, e1) =
          ( tproject1 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 abcde)
          , tproject1 (tproject2 abcde)
          , tproject2 (tproject2 abcde) )
        a = fromTarget a1
        b = fromTarget b1
        c = fromTarget c1
        d = fromTarget d1
        e = fromTarget e1
    in (a, b, c, d, e)
  {-# SPECIALIZE instance (AdaptableTarget (AstTensor AstMethodLet FullSpan) a, AdaptableTarget (AstTensor AstMethodLet FullSpan) b, AdaptableTarget (AstTensor AstMethodLet FullSpan) c, AdaptableTarget (AstTensor AstMethodLet FullSpan) d, AdaptableTarget (AstTensor AstMethodLet FullSpan) e) => AdaptableTarget (AstTensor AstMethodLet FullSpan) (a, b, c, d, e) #-}

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

instance ( RandomValue a
         , RandomValue b
         , RandomValue c
         , RandomValue d
         , RandomValue e ) => RandomValue (a, b, c, d, e) where
  randomValue range g =
    let (v1, g1) = randomValue range g
        (v2, g2) = randomValue range g1
        (v3, g3) = randomValue range g2
        (v4, g4) = randomValue range g3
        (v5, g5) = randomValue range g4
    in ((v1, v2, v3, v4, v5), g5)
