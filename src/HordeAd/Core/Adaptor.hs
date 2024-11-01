{-# LANGUAGE UndecidableInstances #-}
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
  , AsHVector(..)
  ) where

import Prelude

import Control.Exception (assert)
import Data.Maybe (fromMaybe)
import Data.Strict.Vector qualified as Data.Vector
import Data.Vector qualified as Data.NonStrict.Vector
import Data.Vector.Generic qualified as V
import System.Random

-- import qualified Data.Array.RankedS as OR
-- import           Data.List (foldl')
-- import HordeAd.Core.Ast
-- import           GHC.TypeLits (KnownNat)

import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

-- * Adaptor classes

-- Inspired by adaptors from @tomjaguarpaw's branch.
class AdaptableHVector (ranked :: RankedTensorType) vals where
  type X vals :: TensorKindType
  toHVectorOf :: vals -> Rep ranked (X vals)
    -- ^ represent a collection of tensors
  fromHVector :: vals -> RepDeep ranked (X vals) -> Maybe (vals, Maybe (RepDeep ranked (X vals)))
    -- ^ recovers a collection of tensors from its canonical representation,
    -- using the general shape recorded in another collection of the same type;
    -- the remaining data may be used in a another structurally recursive
    -- call working on the same data to build a larger compound collection
  fromHVectorAD :: vals -> RepDeep ranked (ADTensorKind (X vals)) -> Maybe (vals, Maybe (RepDeep ranked (ADTensorKind (X vals))))
  default fromHVectorAD :: X vals ~ ADTensorKind (X vals)
                        => vals -> RepDeep ranked (ADTensorKind (X vals))
                        -> Maybe (vals, Maybe (RepDeep ranked (ADTensorKind (X vals))))
  fromHVectorAD = fromHVector

-- | Recovers a value of a collection of tensors type and asserts
-- there is no remainder. This is the main call of the recursive
-- procedure where @fromHVector@ calls itself recursively for sub-values
-- across mutliple instances.
parseHVector
  :: (TensorKind (X vals), AdaptableHVector ranked vals)
  => vals -> RepDeep ranked (X vals) -> vals
parseHVector aInit hVector =
  case fromHVector aInit hVector of
    Just (vals, mrest) -> assert (maybe True nullRepDeep mrest) vals
    Nothing -> error "parseHVector: truncated product of tensors"

parseHVectorAD
  :: forall vals ranked. (TensorKind (X vals), AdaptableHVector ranked vals)
  => vals -> RepDeep ranked (ADTensorKind (X vals)) -> vals
parseHVectorAD aInit hVector | Dict <- lemTensorKindOfAD (stensorKind @(X vals)) =
  case fromHVectorAD aInit hVector of
    Just (vals, mrest) -> assert (maybe True nullRepDeep mrest) vals
    Nothing -> error "parseHVector: truncated product of tensors"

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
  randomVals :: RandomGen g => Double -> g -> (vals, g)


-- * Basic Adaptor class instances

{- This is temporarily moved to TensorADVal in order to specialize manually
instance AdaptableHVector ranked a
         => AdaptableHVector ranked [a] where
-}

instance TermValue a => TermValue [a] where
  type Value [a] = [Value a]
  fromValue = map fromValue

instance DualNumberValue a => DualNumberValue [a] where
  type DValue [a] = [DValue a]
  fromDValue = map fromDValue

instance ForgetShape a
         => ForgetShape [a] where
  type NoShape [a] = [NoShape a]
  forgetShape = map forgetShape

instance (X a ~ TKUntyped, AdaptableHVector ranked a, ProductTensor ranked)
         => AdaptableHVector ranked (Data.Vector.Vector a) where
  type X (Data.Vector.Vector a) = TKUntyped
  toHVectorOf =
    HVectorPseudoTensor . dmkHVector
    . V.concatMap (dunHVector . unHVectorPseudoTensor . toHVectorOf)
  fromHVector lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromHVector aInit restAcc of
            Just (a, mrest) -> (V.snoc lAcc a, fromMaybe V.empty mrest)
              -- this snoc, if the vector is long, is very costly;
              -- a solution might be to define Value to be a list
            _ -> error "fromHVector (Data.Vector.Vector a)"
        (!l, !restAll) = V.foldl' f (V.empty, source) lInit
    in Just (l, if V.null restAll then Nothing else Just restAll)

instance TermValue a => TermValue (Data.Vector.Vector a) where
  type Value (Data.Vector.Vector a) = Data.Vector.Vector (Value a)
  fromValue = V.map fromValue

instance DualNumberValue a => DualNumberValue (Data.Vector.Vector a) where
  type DValue (Data.Vector.Vector a) = Data.Vector.Vector (DValue a)
  fromDValue = V.map fromDValue

instance ForgetShape a
         => ForgetShape (Data.Vector.Vector a) where
  type NoShape (Data.Vector.Vector a) = Data.Vector.Vector (NoShape a)
  forgetShape = V.map forgetShape

instance (X a ~ TKUntyped, AdaptableHVector ranked a, ProductTensor ranked)
         => AdaptableHVector ranked (Data.NonStrict.Vector.Vector a) where
  type X (Data.NonStrict.Vector.Vector a) = TKUntyped
  toHVectorOf =
    HVectorPseudoTensor . dmkHVector
    . V.concat . map (dunHVector . unHVectorPseudoTensor . toHVectorOf) . V.toList
  fromHVector lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromHVector aInit restAcc of
            Just (a, mrest) -> (V.snoc lAcc a, fromMaybe V.empty mrest)
              -- this snoc, if the vector is long, is very costly;
              -- a solution might be to define Value to be a list
            _ -> error "fromHVector: Nothing"
        (!l, !restAll) = V.foldl' f (V.empty, source) lInit
    in Just (l, if V.null restAll then Nothing else Just restAll)

instance ProductTensor ranked
         => AdaptableHVector ranked (DynamicTensor ranked) where
  type X (DynamicTensor ranked) = TKUntyped
  toHVectorOf = HVectorPseudoTensor . dmkHVector . V.singleton
  fromHVector _aInit v = case V.uncons v of
    Just (t, rest) -> Just (t, if V.null rest then Nothing else Just rest)
    Nothing -> Nothing

instance ( ProductTensor ranked
         , AdaptableHVector ranked a, TensorKind (X a)
         , AdaptableHVector ranked b, TensorKind (X b) )
         => AdaptableHVector ranked (a, b) where
  type X (a, b) = TKProduct (X a) (X b)
  toHVectorOf (a, b) =
    let a1 = toHVectorOf a
        b1 = toHVectorOf b
    in tpair a1 b1
  fromHVector ~(aInit, bInit) (a1, b1) = do
    (a, Nothing) <- fromHVector aInit a1
    (b, Nothing) <- fromHVector bInit b1
    return ((a, b), Nothing)
  fromHVectorAD ~(aInit, bInit) (a1, b1) = do
    (a, Nothing) <- fromHVectorAD aInit a1
    (b, Nothing) <- fromHVectorAD bInit b1
    return ((a, b), Nothing)

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

instance ( ProductTensor ranked
         , AdaptableHVector ranked a, TensorKind (X a)
         , AdaptableHVector ranked b, TensorKind (X b)
         , AdaptableHVector ranked c, TensorKind (X c) )
         => AdaptableHVector ranked (a, b, c) where
  type X (a, b, c) = TKProduct (TKProduct (X a) (X b)) (X c)
  toHVectorOf (a, b, c) =
    let a1 = toHVectorOf a
        b1 = toHVectorOf b
        c1 = toHVectorOf c
    in tpair (tpair a1 b1) c1
  fromHVector ~(aInit, bInit, cInit) ((a1, b1), c1) = do
    (a, Nothing) <- fromHVector aInit a1
    (b, Nothing) <- fromHVector bInit b1
    (c, Nothing) <- fromHVector cInit c1
    return ((a, b, c), Nothing)
  fromHVectorAD ~(aInit, bInit, cInit) ((a1, b1), c1) = do
    (a, Nothing) <- fromHVectorAD aInit a1
    (b, Nothing) <- fromHVectorAD bInit b1
    (c, Nothing) <- fromHVectorAD cInit c1
    return ((a, b, c), Nothing)

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

instance ( ProductTensor ranked
         , AdaptableHVector ranked a, TensorKind (X a)
         , AdaptableHVector ranked b, TensorKind (X b)
         , AdaptableHVector ranked c, TensorKind (X c)
         , AdaptableHVector ranked d, TensorKind (X d) )
         => AdaptableHVector ranked (a, b, c, d) where
  type X (a, b, c, d) = TKProduct (TKProduct (X a) (X b))
                                  (TKProduct (X c) (X d))
  toHVectorOf (a, b, c, d) =
    let a1 = toHVectorOf a
        b1 = toHVectorOf b
        c1 = toHVectorOf c
        d1 = toHVectorOf d
    in  tpair (tpair a1 b1) (tpair c1 d1)
  fromHVector ~(aInit, bInit, cInit, dInit) ((a1, b1), (c1, d1)) = do
    (a, Nothing) <- fromHVector aInit a1
    (b, Nothing) <- fromHVector bInit b1
    (c, Nothing) <- fromHVector cInit c1
    (d, Nothing) <- fromHVector dInit d1
    return ((a, b, c, d), Nothing)
  fromHVectorAD ~(aInit, bInit, cInit, dInit) ((a1, b1), (c1, d1)) = do
    (a, Nothing) <- fromHVectorAD aInit a1
    (b, Nothing) <- fromHVectorAD bInit b1
    (c, Nothing) <- fromHVectorAD cInit c1
    (d, Nothing) <- fromHVectorAD dInit d1
    return ((a, b, c, d), Nothing)

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

instance ( ProductTensor ranked
         , AdaptableHVector ranked a, TensorKind (X a)
         , AdaptableHVector ranked b, TensorKind (X b)
         , AdaptableHVector ranked c, TensorKind (X c)
         , AdaptableHVector ranked d, TensorKind (X d)
         , AdaptableHVector ranked e, TensorKind (X e) )
         => AdaptableHVector ranked (a, b, c, d, e) where
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
              (((a1, b1), c1), (d1, e1)) = do
    (a, Nothing) <- fromHVector aInit a1
    (b, Nothing) <- fromHVector bInit b1
    (c, Nothing) <- fromHVector cInit c1
    (d, Nothing) <- fromHVector dInit d1
    (e, Nothing) <- fromHVector eInit e1
    return ((a, b, c, d, e), Nothing)
  fromHVectorAD ~(aInit, bInit, cInit, dInit, eInit)
              (((a1, b1), c1), (d1, e1)) = do
    (a, Nothing) <- fromHVectorAD aInit a1
    (b, Nothing) <- fromHVectorAD bInit b1
    (c, Nothing) <- fromHVectorAD cInit c1
    (d, Nothing) <- fromHVectorAD dInit d1
    (e, Nothing) <- fromHVectorAD eInit e1
    return ((a, b, c, d, e), Nothing)

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

type role AsHVector representational
newtype AsHVector a =
  AsHVector {unAsHVector :: a}

instance ( ProductTensor ranked
         , AdaptableHVector ranked (AsHVector a), X (AsHVector a) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector b), X (AsHVector b) ~ TKUntyped )
         => AdaptableHVector ranked (AsHVector (a, b)) where
  type X (AsHVector (a, b)) = TKUntyped
  toHVectorOf (AsHVector (a, b)) =
    let a1 = toHVectorOf $ AsHVector a
        b1 = toHVectorOf $ AsHVector b
    in hvappend a1 b1
  fromHVector ~(AsHVector (aInit, bInit)) source = do
    (AsHVector a, Just aRest) <- fromHVector (AsHVector aInit) source
    (AsHVector b, Just bRest) <- fromHVector (AsHVector bInit) aRest
    return (AsHVector (a, b), Just bRest)

hvappend :: ProductTensor f
         => HVectorPseudoTensor f Float '() -> HVectorPseudoTensor f Float '()
         -> HVectorPseudoTensor f Float '()
hvappend v u = HVectorPseudoTensor $ dmkHVector $
  dunHVector (unHVectorPseudoTensor v) V.++ dunHVector (unHVectorPseudoTensor u)

instance (TermValue a, TermValue b)
         => TermValue (AsHVector (a, b)) where
  type Value (AsHVector (a, b)) =
    AsHVector (Value a, Value b)
  fromValue (AsHVector (va, vb)) =
    AsHVector (fromValue va, fromValue vb)

instance ( ProductTensor ranked
         , AdaptableHVector ranked (AsHVector a), X (AsHVector a) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector b), X (AsHVector b) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector c), X (AsHVector c) ~ TKUntyped)
         => AdaptableHVector ranked (AsHVector (a, b, c)) where
  type X (AsHVector (a, b, c)) = TKUntyped
  toHVectorOf (AsHVector (a, b, c)) =
    let a1 = toHVectorOf $ AsHVector a
        b1 = toHVectorOf $ AsHVector b
        c1 = toHVectorOf $ AsHVector c
    in hvappend (hvappend a1 b1) c1
  fromHVector ~(AsHVector (aInit, bInit, cInit)) source = do
    (AsHVector a, Just aRest) <- fromHVector (AsHVector aInit) source
    (AsHVector b, Just bRest) <- fromHVector (AsHVector bInit) aRest
    (AsHVector c, Just cRest) <- fromHVector (AsHVector cInit) bRest
    return (AsHVector (a, b, c), Just cRest)

instance (TermValue a, TermValue b, TermValue c)
         => TermValue (AsHVector (a, b, c)) where
  type Value (AsHVector (a, b, c)) =
    AsHVector (Value a, Value b, Value c)
  fromValue (AsHVector (va, vb, vc)) =
    AsHVector (fromValue va, fromValue vb, fromValue vc)

instance ( ProductTensor ranked
         , AdaptableHVector ranked (AsHVector a), X (AsHVector a) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector b), X (AsHVector b) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector c), X (AsHVector c) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector d), X (AsHVector d) ~ TKUntyped )
         => AdaptableHVector ranked (AsHVector (a, b, c, d)) where
  type X (AsHVector (a, b, c, d)) = TKUntyped
  toHVectorOf (AsHVector (a, b, c, d)) =
    let a1 = toHVectorOf $ AsHVector a
        b1 = toHVectorOf $ AsHVector b
        c1 = toHVectorOf $ AsHVector c
        d1 = toHVectorOf $ AsHVector d
    in hvappend (hvappend a1 b1) (hvappend c1 d1)
  fromHVector ~(AsHVector (aInit, bInit, cInit, dInit)) source = do
    (AsHVector a, Just aRest) <- fromHVector (AsHVector aInit) source
    (AsHVector b, Just bRest) <- fromHVector (AsHVector bInit) aRest
    (AsHVector c, Just cRest) <- fromHVector (AsHVector cInit) bRest
    (AsHVector d, Just dRest) <- fromHVector (AsHVector dInit) cRest
    return (AsHVector (a, b, c, d), Just dRest)

instance (TermValue a, TermValue b, TermValue c, TermValue d)
         => TermValue (AsHVector (a, b, c, d)) where
  type Value (AsHVector (a, b, c, d)) =
    AsHVector (Value a, Value b, Value c, Value d)
  fromValue (AsHVector (va, vb, vc, vd)) =
    AsHVector (fromValue va, fromValue vb, fromValue vc, fromValue vd)

instance ( ProductTensor ranked
         , AdaptableHVector ranked (AsHVector a), X (AsHVector a) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector b), X (AsHVector b) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector c), X (AsHVector c) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector d), X (AsHVector d) ~ TKUntyped
         , AdaptableHVector ranked (AsHVector e), X (AsHVector e) ~ TKUntyped )
         => AdaptableHVector ranked (AsHVector (a, b, c, d, e)) where
  type X (AsHVector (a, b, c, d, e)) = TKUntyped
  toHVectorOf (AsHVector (a, b, c, d, e)) =
    let a1 = toHVectorOf $ AsHVector a
        b1 = toHVectorOf $ AsHVector b
        c1 = toHVectorOf $ AsHVector c
        d1 = toHVectorOf $ AsHVector d
        e1 = toHVectorOf $ AsHVector e
    in hvappend (hvappend (hvappend a1 b1) c1) (hvappend d1 e1)
  fromHVector ~(AsHVector (aInit, bInit, cInit, dInit, eInit)) source = do
    (AsHVector a, Just aRest) <- fromHVector (AsHVector aInit) source
    (AsHVector b, Just bRest) <- fromHVector (AsHVector bInit) aRest
    (AsHVector c, Just cRest) <- fromHVector (AsHVector cInit) bRest
    (AsHVector d, Just dRest) <- fromHVector (AsHVector dInit) cRest
    (AsHVector e, Just eRest) <- fromHVector (AsHVector eInit) dRest
    return (AsHVector (a, b, c, d, e), Just eRest)

instance (TermValue a, TermValue b, TermValue c, TermValue d, TermValue e)
         => TermValue (AsHVector (a, b, c, d, e)) where
  type Value (AsHVector (a, b, c, d, e)) =
    AsHVector (Value a, Value b, Value c, Value d, Value e)
  fromValue (AsHVector (va, vb, vc, vd, ve)) =
    AsHVector
      (fromValue va, fromValue vb, fromValue vc, fromValue vd, fromValue ve)
