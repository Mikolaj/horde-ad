{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor operations implementation using the ox-arrays package.
module HordeAd.Core.CarriersConcrete
  ( -- * RepORArray and its operations and instances
    RepORArray, tftkG, eltDictRep, showDictRep
    -- * RepN and its instances
  , RepN(..)
  ) where

import Prelude hiding (foldl')

import Control.DeepSeq (NFData (..))
import Data.Vector.Generic qualified as V

import Data.Array.Mixed.Internal.Arith qualified as Mixed.Internal.Arith
  (liftVEltwise2)
import Data.Array.Mixed.Shape (withKnownShX)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed as Mixed
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal.Mixed
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape (withKnownShS)
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Orphan ox-arrays instances

instance (Nested.NumElt r, Nested.PrimElt r, Eq r, IntegralF r)
         => IntegralF (Nested.Ranked n r) where
  -- These can't be partial, because our conditionals are not lazy
  -- and so the counterfactual branches, with zeros, may get executed
  -- even though they are subsequently ignored.
  quotF = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quotF a b) x y)))
                            -- TODO: do better somehow
  remF = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else remF a b) x y)))
                            -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, Eq r, IntegralF r)
         => IntegralF (Nested.Shaped sh r) where
  quotF = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quotF a b) x y)))
                            -- TODO: do better somehow
  remF = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else remF a b) x y)))
                            -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, Eq r, IntegralF r)
         => IntegralF (Nested.Mixed sh r) where
  quotF =   (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quotF a b) x y)))
                            -- TODO: do better somehow
  remF =    (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else remF a b) x y)))
                            -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloatF r, Nested.FloatElt r)
         => RealFloatF (Nested.Ranked n r) where
  atan2F = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2F x y)))  -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloatF r, Nested.FloatElt r)
         => RealFloatF (Nested.Shaped sh r) where
  atan2F = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2F x y)))  -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloatF r, Nested.FloatElt r)
         => RealFloatF (Nested.Mixed sh r) where
  atan2F =   (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2F x y)))  -- TODO: do better somehow


-- * RepORArray and its operations

type family RepORArray (y :: TensorKindType) where
  RepORArray (TKScalar r) = r
  RepORArray (TKR2 n x) = Nested.Ranked n (RepORArray x)
  RepORArray (TKS2 sh x) = Nested.Shaped sh (RepORArray x)
  RepORArray (TKX2 sh x) = Nested.Mixed sh (RepORArray x)
  RepORArray (TKProduct x z) = (RepORArray x, RepORArray z)

tftkG :: STensorKind y -> RepORArray y -> FullTensorKind y
tftkG stk t =
  let repackShapeTree :: STensorKind y -> Mixed.ShapeTree (RepORArray y)
                      -> FullTensorKind y
      repackShapeTree stk0 tree = case stk0 of
        STKScalar _ -> FTKScalar
        STKR _ stk1 -> let (sh, rest) = tree
                       in FTKR sh $ repackShapeTree stk1 rest
        STKS _ stk1 -> let (sh, rest) = tree
                       in FTKS sh $ repackShapeTree stk1 rest
        STKX _ stk1 -> let (sh, rest) = tree
                       in FTKX sh $ repackShapeTree stk1 rest
        STKProduct stk1 stk2 ->
                       let (tree1, tree2) = tree
                       in FTKProduct (repackShapeTree stk1 tree1)
                                     (repackShapeTree stk2 tree2)
  in case stk of
    STKScalar _ -> FTKScalar
    STKR _ stk1 | Dict <- eltDictRep stk1 ->
      FTKR (Nested.rshape t) $ repackShapeTree stk1
      $ snd $ Mixed.mshapeTree t
    STKS sh stk1 | Dict <- eltDictRep stk1 ->
      FTKS sh $ repackShapeTree stk1
      $ snd $ Mixed.mshapeTree t
    STKX _ stk1 | Dict <- eltDictRep stk1 ->
      FTKX (Nested.mshape t) $ repackShapeTree stk1
      $ snd $ Mixed.mshapeTree t
    STKProduct stk1 stk2 | Dict <- lemKnownSTK stk1
                         , Dict <- lemKnownSTK stk2 ->
      FTKProduct (tftkG stk1 (fst t))
                 (tftkG stk2 (snd t))

eltDictRep :: STensorKind y -> Dict Nested.KnownElt (RepORArray y)
eltDictRep = \case
    STKScalar{} -> Dict
    STKR SNat x | Dict <- eltDictRep x -> Dict
    STKS sh x | Dict <- eltDictRep x -> withKnownShS sh Dict
    STKX sh x | Dict <- eltDictRep x -> withKnownShX sh Dict
    STKProduct stk1 stk2 | Dict <- eltDictRep stk1
                         , Dict <- eltDictRep stk2 -> Dict

showDictRep :: STensorKind y -> Dict Show (RepORArray y)
showDictRep = \case
    STKScalar{} -> Dict
    STKR _ x | Dict <- showDictRep x
             , Dict <- eltDictRep x -> Dict
    STKS _ x | Dict <- showDictRep x
             , Dict <- eltDictRep x -> Dict
    STKX _ x | Dict <- showDictRep x
             , Dict <- eltDictRep x -> Dict
    STKProduct stk1 stk2 | Dict <- showDictRep stk1
                         , Dict <- showDictRep stk2 -> Dict

nfdataDictRep :: STensorKind y -> Dict NFData (RepORArray y)
nfdataDictRep = \case
    STKScalar{} -> Dict
    STKR _ x | Dict <- nfdataDictRep x
             , Dict <- eltDictRep x -> Dict
    STKS _ x | Dict <- nfdataDictRep x
             , Dict <- eltDictRep x -> Dict
    STKX _ x | Dict <- nfdataDictRep x
             , Dict <- eltDictRep x -> Dict
    STKProduct stk1 stk2 | Dict <- nfdataDictRep stk1
                         , Dict <- nfdataDictRep stk2 -> Dict


-- * RepN and its instances

-- Needed because `RepORArray` can't be partially applied.
-- This type also lets us work around the woes with defining Show
-- for the Rep type family. It gives us a concrete thing
-- to attach a Show instance to.
type role RepN nominal
newtype RepN y = RepN {unRepN :: RepORArray y}

instance KnownSTK y => Show (RepN y) where
  showsPrec d (RepN t) | Dict <- showDictRep (stensorKind @y) = showsPrec d t

instance KnownSTK y => NFData (RepN y) where
  rnf (RepN t) | Dict <- nfdataDictRep (stensorKind @y) = rnf t

type instance BoolOf RepN = Bool

type instance HFunOf RepN x z = RepORArray x -> RepORArray z

type instance PrimalOf RepN = RepN

type instance DualOf RepN = DummyDualTarget

type instance ShareOf RepN = RepN

instance EqF RepN where
  (==.) :: forall y. KnownSTK y => RepN y -> RepN y -> Bool
  RepN u ==. RepN v = case stensorKind @y of
    STKScalar _ -> u == v
    STKR SNat STKScalar{} -> u == v
    STKS sh STKScalar{} -> withKnownShS sh $ u == v
    STKX sh STKScalar{} -> withKnownShX sh $ u == v
    STKProduct @y1 @y2 stk1 stk2 | Dict <- lemKnownSTK stk1
                                 , Dict <- lemKnownSTK stk2 ->
      RepN @y1 (fst u) ==. RepN @y1 (fst v)
      && RepN @y2 (snd u) ==. RepN @y2 (snd v)
    _ -> error "TODO"

instance OrdF RepN where
  (<.) :: forall y. KnownSTK y => RepN y -> RepN y -> Bool
  RepN u <. RepN v = case stensorKind @y of
    STKScalar _ -> u < v
    STKR SNat STKScalar{} -> u < v
    STKS sh STKScalar{} -> withKnownShS sh $ u < v
    STKX sh STKScalar{} -> withKnownShX sh $ u < v
    STKProduct @y1 @y2 stk1 stk2 | Dict <- lemKnownSTK stk1
                                 , Dict <- lemKnownSTK stk2 ->
      RepN @y1 (fst u) <. RepN @y1 (fst v)
      && RepN @y2 (snd u) <. RepN @y2 (snd v)
        -- lexicographic ordering  -- TODO: is this standard and the same as for <=. ? as for || ?
    _ -> error "TODO"

deriving instance Eq (RepORArray y) => Eq (RepN y)
deriving instance Ord (RepORArray y) => Ord (RepN y)
deriving instance Num (RepORArray y) => Num (RepN y)
deriving instance IntegralF (RepORArray y) => IntegralF (RepN y)
deriving instance Fractional (RepORArray y) => Fractional (RepN y)
deriving instance Floating (RepORArray y) => Floating (RepN y)
deriving instance RealFloatF (RepORArray y) => RealFloatF (RepN y)
