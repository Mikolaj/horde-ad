{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Operations on the untyped product (heterogeneous vector) of tensors.
-- In particular, adaptors for working with types of collections of tensors
-- that are isomorphic to products.
--
-- This is necessary as a representation of the domains of objective functions
-- that become the codomains of the reverse derivative functions
-- and also to handle multiple arguments and results of fold-like operations.
module HordeAd.Core.Adaptor
  ( AdaptableHVector(..), parseHVector, parseHVectorAD
  , TermValue(..), DualNumberValue(..)
  , ForgetShape(..), RandomHVector(..)
  , stkOfListR
  ) where

import Prelude

import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:))
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat, type (-), type (<=?))
import System.Random

-- import qualified Data.Array.RankedS as OR
-- import           Data.List (foldl')
-- import HordeAd.Core.Ast
-- import           GHC.TypeLits (KnownNat)

import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested (ListR (..))

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
  fromHVector :: vals -> target (X vals) -> Maybe vals
    -- ^ recovers a collection of tensors from its canonical representation,
    -- using the general shape recorded in another collection of the same type;
    -- the remaining data may be used in a another structurally recursive
    -- call working on the same data to build a larger compound collection
  fromHVectorAD :: vals -> target (ADTensorKind (X vals)) -> Maybe vals
  default fromHVectorAD :: X vals ~ ADTensorKind (X vals)
                        => vals -> target (ADTensorKind (X vals))
                        -> Maybe vals
  fromHVectorAD = fromHVector
    -- TODO: figure out and comment  whether the first argument
    -- is really needed and what for (maybe only for convenience? speed?)

-- | Recovers a value of a collection of tensors type and asserts
-- there is no remainder. This is the main call of the recursive
-- procedure where @fromHVector@ calls itself recursively for sub-values
-- across mutliple instances.
parseHVector
  :: forall vals target. AdaptableHVector target vals
  => vals -> target (X vals) -> vals
parseHVector aInit hVector =
  case fromHVector aInit hVector of
    Just vals -> vals
    Nothing -> error "parseHVector: truncated product of tensors"

parseHVectorAD
  :: forall vals target. AdaptableHVector target vals
  => vals -> target (ADTensorKind (X vals)) -> vals
parseHVectorAD aInit hVector =
  case fromHVectorAD aInit hVector of
    Just vals -> vals
    Nothing -> error "parseHVectorAD: truncated product of tensors"

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
         => AdaptableHVector target
                             (target y) where
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
  fromHVector _aInit t = Just t
  fromHVectorAD _aInit t = Just $ fromADTensorKindShared (stensorKind @y) t

type family Tups n t where
  Tups 0 t = TKUnit
  Tups n t = TKProduct t (Tups (n - 1) t)

stkOfListR :: forall t n x.
              STensorKindType t -> ListR n x -> STensorKindType (Tups n t)
stkOfListR _ ZR = stensorKind
stkOfListR stk ((:::) @n1 _ rest) =
  gcastWith (unsafeCoerceRefl :: Tups n t :~: TKProduct t (Tups n1 t)) $
  STKProduct stk (stkOfListR stk rest)

instance ( BaseTensor target
         , AdaptableHVector target a, TensorKind (X a), TensorKind (ADTensorKind (X a)) )
         => AdaptableHVector target (ListR n a) where
  type X (ListR n a) = Tups n (X a)
  toHVectorOf ZR = tunit
  toHVectorOf ((:::) @n1 a rest)
   | Dict <- lemTensorKindOfSTK (stkOfListR (stensorKind @(X a)) rest) =
    gcastWith (unsafeCoerceRefl
               :: X (ListR n a) :~: TKProduct (X a) (X (ListR n1 a))) $
    let a1 = toHVectorOf a
        rest1 = toHVectorOf rest
    in tpair a1 rest1
  fromHVector ZR _ = Just ZR
  fromHVector ((:::) @n1 aInit restInit) a1rest1
   | Dict <- lemTensorKindOfSTK (stkOfListR (stensorKind @(X a)) restInit) =
    gcastWith (unsafeCoerceRefl
              :: X (ListR n a) :~: TKProduct (X a) (X (ListR n1 a))) $ do
      let (a1, rest1) = (tproject1 a1rest1, tproject2 a1rest1)
      a <- fromHVector aInit a1
      rest <- fromHVector restInit rest1
      return (a ::: rest)
  fromHVectorAD ZR _ = Just ZR
  fromHVectorAD ((:::) @n1 aInit restInit) a1rest1
   | Dict <- lemTensorKindOfSTK (stkOfListR (stensorKind
                                               @(ADTensorKind (X a))) restInit) =
    gcastWith (unsafeCoerceRefl
              :: ADTensorKind (Tups n1 (X a)) :~: Tups n1 (ADTensorKind (X a))) $
    gcastWith (unsafeCoerceRefl
              :: X (ListR n a) :~: TKProduct (X a) (X (ListR n1 a))) $ do
      let (a1, rest1) = (tproject1 a1rest1, tproject2 a1rest1)
      a <- fromHVectorAD aInit a1
      rest <- fromHVectorAD restInit rest1
      return (a ::: rest)

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
  fromHVector ~(aInit, bInit)
              ab = do
    let (a1, b1) =
          ( tproject1 ab
          , tproject2 ab )
    a <- fromHVector aInit a1
    b <- fromHVector bInit b1
    return (a, b)
  fromHVectorAD ~(aInit, bInit)
              ab = do
    let (a1, b1) =
          ( tproject1 ab
          , tproject2 ab )
    a <- fromHVectorAD aInit a1
    b <- fromHVectorAD bInit b1
    return (a, b)

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
  fromHVector ~(aInit, bInit, cInit)
              abc = do
    let (a1, b1, c1) =
          ( tproject1 (tproject1 abc)
          , tproject2 (tproject1 abc)
          , tproject2 abc )
    a <- fromHVector aInit a1
    b <- fromHVector bInit b1
    c <- fromHVector cInit c1
    return (a, b, c)
  fromHVectorAD ~(aInit, bInit, cInit)
              abc = do
    let (a1, b1, c1) =
          ( tproject1 (tproject1 abc)
          , tproject2 (tproject1 abc)
          , tproject2 abc )
    a <- fromHVectorAD aInit a1
    b <- fromHVectorAD bInit b1
    c <- fromHVectorAD cInit c1
    return (a, b, c)

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
  fromHVector ~(aInit, bInit, cInit, dInit)
              abcd = do
    let (a1, b1, c1, d1) =
          ( tproject1 (tproject1 abcd)
          , tproject2 (tproject1 abcd)
          , tproject1 (tproject2 abcd)
          , tproject2 (tproject2 abcd) )
    a <- fromHVector aInit a1
    b <- fromHVector bInit b1
    c <- fromHVector cInit c1
    d <- fromHVector dInit d1
    return (a, b, c, d)
  fromHVectorAD ~(aInit, bInit, cInit, dInit)
              abcd = do
    let (a1, b1, c1, d1) =
          ( tproject1 (tproject1 abcd)
          , tproject2 (tproject1 abcd)
          , tproject1 (tproject2 abcd)
          , tproject2 (tproject2 abcd) )
    a <- fromHVectorAD aInit a1
    b <- fromHVectorAD bInit b1
    c <- fromHVectorAD cInit c1
    d <- fromHVectorAD dInit d1
    return (a, b, c, d)

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
  fromHVector ~(aInit, bInit, cInit, dInit, eInit)
              abcde = do
    let (a1, b1, c1, d1, e1) =
          ( tproject1 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 abcde)
          , tproject1 (tproject2 abcde)
          , tproject2 (tproject2 abcde) )
    a <- fromHVector aInit a1
    b <- fromHVector bInit b1
    c <- fromHVector cInit c1
    d <- fromHVector dInit d1
    e <- fromHVector eInit e1
    return (a, b, c, d, e)
  fromHVectorAD ~(aInit, bInit, cInit, dInit, eInit)
              abcde = do
    let (a1, b1, c1, d1, e1) =
          ( tproject1 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 (tproject1 abcde))
          , tproject2 (tproject1 abcde)
          , tproject1 (tproject2 abcde)
          , tproject2 (tproject2 abcde) )
    a <- fromHVectorAD aInit a1
    b <- fromHVectorAD bInit b1
    c <- fromHVectorAD cInit c1
    d <- fromHVectorAD dInit d1
    e <- fromHVectorAD eInit e1
    return (a, b, c, d, e)

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
