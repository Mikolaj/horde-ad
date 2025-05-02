{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Adaptors for working with types of collections of tensors,
-- e.g., tuples, sized lists and user types of statically known size,
-- as long as they have the proper instances defined.
-- The collections are used as representations of the domains
-- of objective functions that become the codomains of the reverse
-- derivative functions and also to handle multiple arguments
-- and results of fold-like operations.
module HordeAd.Core.Adaptor
  ( AdaptableTarget(..), TermValue(..), DualNumberValue(..)
  , ForgetShape(..), RandomValue(..)
  , stkOfListR
  ) where

import Prelude

import Data.Default
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:))
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat, type (-), type (<=?))
import System.Random

import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.Ast
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.OpsAst ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Adaptor classes

-- Inspired by adaptors from @tomjaguarpaw's branch.
--
-- | The class that makes it possible to treat @vals@ (e.g., a tuple of tensors)
-- as a @target@-based (e.g., concrete or symbolic) value
-- of tensor kind @X vals@.
class AdaptableTarget (target :: Target) vals where
  type X vals :: TK  -- ^ what tensor kind represents the collection
  toTarget :: vals -> target (X vals)
    -- ^ represent a collection of tensors
  fromTarget :: target (X vals) -> vals
    -- ^ recovers a collection of tensors from its canonical representation;
    --   requires a duplicable argument

-- | An embedding of a concrete collection of tensors to a non-concrete
-- counterpart of the same shape and containing the same data.
class TermValue vals where
  type Value vals = result | result -> vals
    -- ^ a helper type, with the same general shape,
    -- but possibly more concrete, e.g., arrays instead of terms,
    -- where the injectivity is crucial to limit the number
    -- of type applications the library user has to supply
  fromValue :: Value vals -> vals  -- ^ an embedding

-- | An embedding of a concrete collection of tensors to a non-concrete
-- counterpart of the same shape and containing the same data.
-- This variant is possible to define more often, but the associated
-- type family is not injective.
class DualNumberValue vals where
  type DValue vals
    -- ^ a helper type, with the same general shape,
    -- but possibly more concrete, e.g., arrays instead of terms,
    -- where the injectivity is hard to obtain, but is not so important,
    -- because the type is not used in the best pipeline
  fromDValue :: DValue vals -> vals  -- ^ an embedding

-- | A helper class for for converting all tensors inside a type
-- from shaped to ranked. It's useful when a collection of parameters
-- is defined as shaped tensor for 'RandomValue' but then is going
-- to be used as ranked tensor to make type reconstruction easier.
class ForgetShape vals where
  type NoShape vals
  forgetShape :: vals -> NoShape vals

-- | A helper class for randomly generating initial parameters.
-- Only instance for collections of shaped tensors and scalars are possible,
-- because only then the shapes of the tensors to generate are known
-- from their types.
class RandomValue vals where
  randomValue :: Double -> StdGen -> (vals, StdGen)


-- * Base instances

instance AdaptableTarget target (target y) where
  type X (target y) = y
  toTarget = id
  fromTarget t = t
  {-# SPECIALIZE instance AdaptableTarget Concrete (Concrete (TKS sh Double)) #-}
  {-# SPECIALIZE instance AdaptableTarget Concrete (Concrete (TKS sh Float)) #-}
    -- a failed attempt to specialize without -fpolymorphic-specialisation

instance KnownSTK y
         => TermValue (AstTensor AstMethodLet FullSpan y) where
  type Value (AstTensor AstMethodLet FullSpan y) = Concrete y
  fromValue t = tconcrete (tftkG (knownSTK @y) $ unConcrete t) t

instance (BaseTensor target, BaseTensor (PrimalOf target), KnownSTK y)
         => DualNumberValue (target y) where
  type DValue (target y) = Concrete y
  fromDValue t = tfromPrimal (knownSTK @y)
                 $ tconcrete (tftkG (knownSTK @y) $ unConcrete t) t

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
    target (NoShapeTensorKind (TKProduct a b))
  forgetShape ab =
    ttlet ab $ \abShared ->
      tpair (forgetShape (tproject1 abShared))
            (forgetShape (tproject2 abShared))

instance forall r target. (GoodScalar r, BaseTensor target)
         => RandomValue (target (TKScalar r)) where
  randomValue range g =
    ifDifferentiable @r
      (let (r, g2) = random g
           m = 2 * realToFrac range * (r - 0.5)
       in (tkconcrete m, g2))
      (tkconcrete def, g)

instance forall sh r target. (KnownShS sh, GoodScalar r, BaseTensor target)
         => RandomValue (target (TKS sh r)) where
  randomValue range g =
    ifDifferentiable @r
      (let createRandomVector :: Int -> StdGen -> target (TKS sh r)
           createRandomVector n seed =
             srepl (2 * realToFrac range)
             * (tsconcrete
                  (Nested.sfromVector knownShS (V.fromListN n (randoms seed)))
                - srepl 0.5)
           (g1, g2) = splitGen g
           arr = createRandomVector (shsSize (knownShS @sh)) g1
       in (arr, g2))
      (srepl def, g)
   where srepl = tsconcrete . Nested.sreplicateScal knownShS
  -- {-# SPECIALIZE instance (KnownShS sh, GoodScalar r, Fractional r, Random r) => RandomValue (Concrete (TKS sh r)) #-}
  {-# SPECIALIZE instance KnownShS sh => RandomValue (Concrete (TKS sh Double)) #-}
  {-# SPECIALIZE instance KnownShS sh => RandomValue (Concrete (TKS sh Float)) #-}

instance (RandomValue (target a), RandomValue (target b), BaseTensor target)
         => RandomValue (target (TKProduct a b)) where
  randomValue range g =
    let (v1, g1) = randomValue range g
        (v2, g2) = randomValue range g1
    in (tpair v1 v2, g2)

-- These instances are messy and hard to use, but we probably can't do better.
instance DualNumberValue Double where
  type DValue Double = Concrete (TKScalar Double)
  fromDValue (Concrete d) = d

instance DualNumberValue Float where
  type DValue Float = Concrete (TKScalar Float)
  fromDValue (Concrete d) = d

instance TermValue (Concrete (TKScalar Double)) where
  type Value (Concrete (TKScalar Double)) = Double
  fromValue = Concrete

instance TermValue (Concrete (TKScalar Float)) where
  type Value (Concrete (TKScalar Float)) = Float
  fromValue = Concrete


-- * Compound instances

instance (BaseTensor target, ConvertTensor target, GoodScalar r)
         => AdaptableTarget target [target (TKScalar r)] where
  type X [target (TKScalar r)] = TKR 1 r
  toTarget l = if null l
               then trconcrete Nested.remptyArray
               else trfromVector $ V.fromList $ map rfromK l
  fromTarget = map kfromR . trunravelToList
                              -- inefficient, but we probably can't do better

instance (BaseTensor target, ConvertTensor target, GoodScalar r)
         => AdaptableTarget target
                            (Data.Vector.Vector (target (TKScalar r))) where
  type X (Data.Vector.Vector (target (TKScalar r))) = TKR 1 r
  toTarget v = if V.null v
               then trconcrete Nested.remptyArray
               else trfromVector $ V.map rfromK v
  fromTarget =
    V.fromList . map kfromR . trunravelToList
                                -- inefficient, but we probably can't do better

type family Tups n t where
  Tups 0 t = TKUnit
  Tups n t = TKProduct t (Tups (n - 1) t)

stkOfListR :: forall t n.
              SingletonTK t -> SNat n -> SingletonTK (Tups n t)
stkOfListR _ (SNat' @0) = stkUnit
stkOfListR stk SNat =
  gcastWith (unsafeCoerceRefl :: (1 <=? n) :~: True) $
  gcastWith (unsafeCoerceRefl :: Tups n t :~: TKProduct t (Tups (n - 1) t)) $
  STKProduct stk (stkOfListR stk (SNat @(n - 1)))

instance (BaseTensor target, KnownNat n, AdaptableTarget target a)
         => AdaptableTarget target (ListR n a) where
  type X (ListR n a) = Tups n (X a)
  toTarget ZR = tkconcrete Z0
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
  {-# SPECIALIZE instance (KnownNat n, AdaptableTarget (ADVal Concrete) a) => AdaptableTarget (ADVal Concrete) (ListR n a) #-}

instance TermValue a => TermValue [a] where
  type Value [a] = [Value a]
  fromValue = map fromValue

instance TermValue a => TermValue (Data.Vector.Vector a) where
  type Value (Data.Vector.Vector a) = Data.Vector.Vector (Value a)
  fromValue = V.map fromValue

instance TermValue a => TermValue (ListR n a) where
  type Value (ListR n a) = ListR n (Value a)
  fromValue ZR = ZR
  fromValue (a ::: rest) = fromValue a ::: fromValue rest

instance DualNumberValue a => DualNumberValue [a] where
  type DValue [a] = [DValue a]
  fromDValue = map fromDValue

instance DualNumberValue a => DualNumberValue (Data.Vector.Vector a) where
  type DValue (Data.Vector.Vector a) = Data.Vector.Vector (DValue a)
  fromDValue = V.map fromDValue

instance DualNumberValue a => DualNumberValue (ListR n a) where
  type DValue (ListR n a) = ListR n (DValue a)
  fromDValue ZR = ZR
  fromDValue (a ::: rest) = fromDValue a ::: fromDValue rest

instance ForgetShape [a] where
  type NoShape [a] = [a]
  forgetShape = id

instance ForgetShape (Data.Vector.Vector a) where
  type NoShape (Data.Vector.Vector a) = Data.Vector.Vector a
  forgetShape = id

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


-- * Tuple instances

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
    let a = fromTarget $ tproject1 ab
        b = fromTarget $ tproject2 ab
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
    let a = fromTarget $ tproject1 $ tproject1 abc
        b = fromTarget $ tproject2 $ tproject1 abc
        c = fromTarget $ tproject2 abc
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
    let a = fromTarget $ tproject1 $ tproject1 abcd
        b = fromTarget $ tproject2 $ tproject1 abcd
        c = fromTarget $ tproject1 $ tproject2 abcd
        d = fromTarget $ tproject2 $ tproject2 abcd
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
    let a = fromTarget $ tproject1 $ tproject1 $ tproject1 abcde
        b = fromTarget $ tproject2 $ tproject1 $ tproject1 abcde
        c = fromTarget $ tproject2 $ tproject1 abcde
        d = fromTarget $ tproject1 $ tproject2 abcde
        e = fromTarget $ tproject2 $ tproject2 abcde
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
