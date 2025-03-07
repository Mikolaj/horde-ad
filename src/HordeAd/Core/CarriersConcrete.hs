{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor operations implementation using the ox-arrays package.
module HordeAd.Core.CarriersConcrete
  ( -- * RepORArray and its operations
    RepORArray, tftkG, eltDictRep, showDictRep
    -- * RepN its operations
  , RepN(..), rtoVector, stoVector, xtoVector
  ) where

import Prelude hiding (foldl')

import Control.DeepSeq (NFData (..))
import Data.Vector.Generic qualified as V
import Data.Vector.Storable qualified as VS

import Data.Array.Mixed.Internal.Arith qualified as Nested.Internal.Arith
  (liftVEltwise2)
import Data.Array.Mixed.Shape
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Orphan ox-arrays instances

instance (Nested.NumElt r, Nested.PrimElt r, Eq r, IntegralH r)
         => IntegralH (Nested.Ranked n r) where
  -- These can't be partial, because our conditionals are not lazy
  -- and so the counterfactual branches, with zeros, may get executed
  -- even though they are subsequently ignored.
  quotH = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quotH a b) x y)))
                            -- TODO: do better somehow
  remH = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else remH a b) x y)))
                            -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, Eq r, IntegralH r)
         => IntegralH (Nested.Shaped sh r) where
  quotH = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quotH a b) x y)))
                            -- TODO: do better somehow
  remH = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else remH a b) x y)))
                            -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, Eq r, IntegralH r)
         => IntegralH (Nested.Mixed sh r) where
  quotH =   (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quotH a b) x y)))
                            -- TODO: do better somehow
  remH =    (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else remH a b) x y)))
                            -- TODO: do better somehow'

instance GoodScalar r
         => Real (Nested.Ranked n r) where
  toRational = error "horde-ad: operation not defined for tensor"

instance GoodScalar r
         => Real (Nested.Shaped sh r) where
  toRational = error "horde-ad: operation not defined for tensor"

instance GoodScalar r
         => Real (Nested.Mixed sh r) where
  toRational = error "horde-ad: operation not defined for tensor"

instance (GoodScalar r, Nested.FloatElt r)
         => RealFrac (Nested.Ranked n r) where
  properFraction = error "horde-ad: operation not defined for tensor"

instance (GoodScalar r, RealFrac r, Nested.FloatElt r)
         => RealFrac (Nested.Shaped sh r) where
  properFraction = error "horde-ad: operation not defined for tensor"

instance (GoodScalar r, Nested.FloatElt r)
         => RealFrac (Nested.Mixed sh r) where
  properFraction = error "horde-ad: operation not defined for tensor"

instance (Nested.NumElt r, Nested.PrimElt r, RealFloatH r, Nested.FloatElt r)
         => RealFloatH (Nested.Ranked n r) where
  atan2H = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2H x y)))  -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloatH r, Nested.FloatElt r)
         => RealFloatH (Nested.Shaped sh r) where
  atan2H = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2H x y)))  -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloatH r, Nested.FloatElt r)
         => RealFloatH (Nested.Mixed sh r) where
  atan2H =   (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2H x y)))  -- TODO: do better somehow

instance (GoodScalar r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloat (Nested.Ranked n r) where
  atan2 = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow
  floatRadix = error "horde-ad: operation not defined for tensor"
  floatDigits = error "horde-ad: operation not defined for tensor"
  floatRange = error "horde-ad: operation not defined for tensor"
  decodeFloat = error "horde-ad: operation not defined for tensor"
  encodeFloat = error "horde-ad: operation not defined for tensor"
  isNaN = error "horde-ad: operation not defined for tensor"
  isInfinite = error "horde-ad: operation not defined for tensor"
  isDenormalized = error "horde-ad: operation not defined for tensor"
  isNegativeZero = error "horde-ad: operation not defined for tensor"
  isIEEE = error "horde-ad: operation not defined for tensor"

instance (GoodScalar r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloat (Nested.Shaped sh r) where
  atan2 = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow
  floatRadix = error "horde-ad: operation not defined for tensor"
  floatDigits = error "horde-ad: operation not defined for tensor"
  floatRange = error "horde-ad: operation not defined for tensor"
  decodeFloat = error "horde-ad: operation not defined for tensor"
  encodeFloat = error "horde-ad: operation not defined for tensor"
  isNaN = error "horde-ad: operation not defined for tensor"
  isInfinite = error "horde-ad: operation not defined for tensor"
  isDenormalized = error "horde-ad: operation not defined for tensor"
  isNegativeZero = error "horde-ad: operation not defined for tensor"
  isIEEE = error "horde-ad: operation not defined for tensor"

instance (GoodScalar r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloat (Nested.Mixed sh r) where
  atan2 =   (Nested.Internal.mliftNumElt2
               (flip Nested.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow
  floatRadix = error "horde-ad: operation not defined for tensor"
  floatDigits = error "horde-ad: operation not defined for tensor"
  floatRange = error "horde-ad: operation not defined for tensor"
  decodeFloat = error "horde-ad: operation not defined for tensor"
  encodeFloat = error "horde-ad: operation not defined for tensor"
  isNaN = error "horde-ad: operation not defined for tensor"
  isInfinite = error "horde-ad: operation not defined for tensor"
  isDenormalized = error "horde-ad: operation not defined for tensor"
  isNegativeZero = error "horde-ad: operation not defined for tensor"
  isIEEE = error "horde-ad: operation not defined for tensor"


-- * RepORArray and its operations

type family RepORArray (y :: TK) where
  RepORArray (TKScalar r) = r
  RepORArray (TKR2 n x) = Nested.Ranked n (RepORArray x)
  RepORArray (TKS2 sh x) = Nested.Shaped sh (RepORArray x)
  RepORArray (TKX2 sh x) = Nested.Mixed sh (RepORArray x)
  RepORArray (TKProduct x z) = (RepORArray x, RepORArray z)

tftkG :: SingletonTK y -> RepORArray y -> FullShapeTK y
tftkG stk t =
  let repackShapeTree :: SingletonTK y
                      -> Nested.Internal.ShapeTree (RepORArray y)
                      -> FullShapeTK y
      repackShapeTree stk0 tree = case stk0 of
        STKScalar -> FTKScalar
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
    STKScalar -> FTKScalar
    STKR _ stk1 | Dict <- eltDictRep stk1 ->
      FTKR (Nested.rshape t) $ repackShapeTree stk1
      $ snd $ Nested.Internal.mshapeTree t
    STKS sh stk1 | Dict <- eltDictRep stk1 ->
      FTKS sh $ repackShapeTree stk1
      $ snd $ Nested.Internal.mshapeTree t
    STKX _ stk1 | Dict <- eltDictRep stk1 ->
      FTKX (Nested.mshape t) $ repackShapeTree stk1
      $ snd $ Nested.Internal.mshapeTree t
    STKProduct stk1 stk2 ->
      FTKProduct (tftkG stk1 (fst t))
                 (tftkG stk2 (snd t))

eltDictRep :: SingletonTK y -> Dict Nested.KnownElt (RepORArray y)
eltDictRep = \case
    STKScalar -> Dict
    STKR SNat x | Dict <- eltDictRep x -> Dict
    STKS sh x | Dict <- eltDictRep x -> withKnownShS sh Dict
    STKX sh x | Dict <- eltDictRep x -> withKnownShX sh Dict
    STKProduct stk1 stk2 | Dict <- eltDictRep stk1
                         , Dict <- eltDictRep stk2 -> Dict

showDictRep :: SingletonTK y -> Dict Show (RepORArray y)
showDictRep = \case
    STKScalar -> Dict
    STKR _ x | Dict <- showDictRep x
             , Dict <- eltDictRep x -> Dict
    STKS _ x | Dict <- showDictRep x
             , Dict <- eltDictRep x -> Dict
    STKX _ x | Dict <- showDictRep x
             , Dict <- eltDictRep x -> Dict
    STKProduct stk1 stk2 | Dict <- showDictRep stk1
                         , Dict <- showDictRep stk2 -> Dict

nfdataDictRep :: SingletonTK y -> Dict NFData (RepORArray y)
nfdataDictRep = \case
    STKScalar -> Dict
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
  showsPrec d (RepN t) | Dict <- showDictRep (knownSTK @y) = showsPrec d t

instance KnownSTK y => NFData (RepN y) where
  rnf (RepN t) | Dict <- nfdataDictRep (knownSTK @y) = rnf t

type instance BoolOf RepN = Bool

type instance HFunOf RepN x z = RepORArray x -> RepORArray z

type instance PrimalOf RepN = RepN

type instance DualOf RepN = DummyDualTarget

type instance ShareOf RepN = RepN

instance GoodScalar r => EqH RepN (TKScalar r) where
  RepN u ==. RepN v = u == v

instance GoodScalar r => OrdH RepN (TKScalar r) where
  RepN u <. RepN v = u < v

instance GoodScalar r => EqH RepN (TKR n r) where
  RepN u ==. RepN v = u == v

instance GoodScalar r => OrdH RepN (TKR n r) where
  RepN u <. RepN v = u < v

instance GoodScalar r => EqH RepN (TKS sh r) where
  RepN u ==. RepN v = u == v

instance GoodScalar r => OrdH RepN (TKS sh r) where
  RepN u <. RepN v = u < v

instance GoodScalar r => EqH RepN (TKX sh r) where
  RepN u ==. RepN v = u == v

instance GoodScalar r => OrdH RepN (TKX sh r) where
  RepN u <. RepN v = u < v

deriving instance Eq (RepORArray y) => Eq (RepN y)
deriving instance Ord (RepORArray y) => Ord (RepN y)
deriving instance Num (RepORArray y) => Num (RepN y)
deriving instance IntegralH (RepORArray y) => IntegralH (RepN y)
deriving instance Real (RepORArray y) => Real (RepN y)
deriving instance Fractional (RepORArray y) => Fractional (RepN y)
deriving instance Floating (RepORArray y) => Floating (RepN y)
deriving instance RealFrac (RepORArray y) => RealFrac (RepN y)
deriving instance RealFloatH (RepORArray y) => RealFloatH (RepN y)
deriving instance RealFloat (RepORArray y) => RealFloat (RepN y)

rtoVector :: GoodScalar r => RepN (TKR n r) -> VS.Vector r
rtoVector  = Nested.rtoVector . unRepN

stoVector :: GoodScalar r => RepN (TKS sh r) -> VS.Vector r
stoVector = Nested.stoVector . unRepN

xtoVector :: GoodScalar r => RepN (TKX sh r) -> VS.Vector r
xtoVector = Nested.mtoVector . unRepN
