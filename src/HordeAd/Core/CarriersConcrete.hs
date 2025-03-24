{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor operations implementation using the ox-arrays package.
-- These definitions, mostly class instances, are needed to make concrete
-- arrays a valid carrier for a tensor class algebra (instance) defined in
-- "OpsConcrete".
module HordeAd.Core.CarriersConcrete
  ( -- * RepConcrete and its operations
    RepConcrete, tftkG, eltDictRep, showDictRep
    -- * Concrete and its operations
  , Concrete(..), rtoVector, stoVector, xtoVector
  ) where

import Prelude hiding (foldl')

import Control.DeepSeq (NFData (..))
import Data.Vector.Storable qualified as VS

import Data.Array.Mixed.Internal.Arith qualified as Nested.Internal.Arith
  (liftVEltwise1)
import Data.Array.Mixed.Shape
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Orphan ox-arrays instances

instance (Nested.IntElt r, Nested.PrimElt r, Eq r, Num r)
         => IntegralH (Nested.Ranked n r) where
  -- These can't be partial, because our conditionals are not lazy
  -- and so the counterfactual branches, with zeros, may get executed
  -- even though they are subsequently ignored.
  quotH a b = Nested.rquotArray a (Nested.Internal.liftRanked1 mmakeNonZero b)
  remH a b = Nested.rremArray a (Nested.Internal.liftRanked1 mmakeNonZero b)

instance (Nested.IntElt r, Nested.PrimElt r, Eq r, Num r)
         => IntegralH (Nested.Shaped sh r) where
  quotH a b = Nested.squotArray a (Nested.Internal.liftShaped1 mmakeNonZero b)
  remH a b = Nested.sremArray a (Nested.Internal.liftShaped1 mmakeNonZero b)

instance (Nested.IntElt r, Nested.PrimElt r, Eq r, Num r)
         => IntegralH (Nested.Mixed sh r) where
  quotH a b = Nested.mquotArray a (mmakeNonZero b)
  remH a b = Nested.mremArray a (mmakeNonZero b)

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

instance (Nested.PrimElt r, Nested.FloatElt r)
         => RealFloatH (Nested.Ranked n r) where
  atan2H = Nested.ratan2Array

instance (Nested.PrimElt r, Nested.FloatElt r)
         => RealFloatH (Nested.Shaped sh r) where
  atan2H = Nested.satan2Array

instance (Nested.PrimElt r, Nested.FloatElt r)
         => RealFloatH (Nested.Mixed sh r) where
  atan2H = Nested.matan2Array

instance (GoodScalar r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloat (Nested.Ranked n r) where
  atan2 = Nested.ratan2Array
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
  atan2 = Nested.satan2Array
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
  atan2 = Nested.matan2Array
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

-- TODO: make more efficient somehow?
mmakeNonZero :: (Nested.PrimElt r, Eq r, Num r)
             => Nested.Mixed sh r -> Nested.Mixed sh r
mmakeNonZero =
  Nested.Internal.mliftNumElt1
    (flip Nested.Internal.Arith.liftVEltwise1
      (VS.map (\x -> if x == 0 then 1 else x)))


-- * RepConcrete and its operations

type family RepConcrete (y :: TK) where
  RepConcrete (TKScalar r) = r
  RepConcrete (TKR2 n x) = Nested.Ranked n (RepConcrete x)
  RepConcrete (TKS2 sh x) = Nested.Shaped sh (RepConcrete x)
  RepConcrete (TKX2 sh x) = Nested.Mixed sh (RepConcrete x)
  RepConcrete (TKProduct x z) = (RepConcrete x, RepConcrete z)

tftkG :: SingletonTK y -> RepConcrete y -> FullShapeTK y
tftkG stk t =
  let repackShapeTree :: SingletonTK y
                      -> Nested.Internal.ShapeTree (RepConcrete y)
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

eltDictRep :: SingletonTK y -> Dict Nested.KnownElt (RepConcrete y)
eltDictRep = \case
    STKScalar -> Dict
    STKR SNat x | Dict <- eltDictRep x -> Dict
    STKS sh x | Dict <- eltDictRep x -> withKnownShS sh Dict
    STKX sh x | Dict <- eltDictRep x -> withKnownShX sh Dict
    STKProduct stk1 stk2 | Dict <- eltDictRep stk1
                         , Dict <- eltDictRep stk2 -> Dict

showDictRep :: SingletonTK y -> Dict Show (RepConcrete y)
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

nfdataDictRep :: SingletonTK y -> Dict NFData (RepConcrete y)
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


-- * Concrete and its instances

-- Needed because `RepConcrete` can't be partially applied.
-- This type also lets us work around the woes with defining Show
-- for the Rep type family. It gives us a concrete thing
-- to attach a Show instance to.
type role Concrete nominal
newtype Concrete y = Concrete {unConcrete :: RepConcrete y}

instance KnownSTK y => Show (Concrete y) where
  showsPrec d (Concrete t) | Dict <- showDictRep (knownSTK @y) = showsPrec d t

instance KnownSTK y => NFData (Concrete y) where
  rnf (Concrete t) | Dict <- nfdataDictRep (knownSTK @y) = rnf t

type instance BoolOf Concrete = Bool

type instance HFunOf Concrete x z = RepConcrete x -> RepConcrete z

type instance PrimalOf Concrete = Concrete

type instance DualOf Concrete = DummyDualTarget

type instance ShareOf Concrete = Concrete

instance GoodScalar r => EqH Concrete (TKScalar r) where
  Concrete u ==. Concrete v = u == v

instance GoodScalar r => OrdH Concrete (TKScalar r) where
  Concrete u <. Concrete v = u < v

instance GoodScalar r => EqH Concrete (TKR n r) where
  Concrete u ==. Concrete v = u == v

instance GoodScalar r => OrdH Concrete (TKR n r) where
  Concrete u <. Concrete v = u < v

instance GoodScalar r => EqH Concrete (TKS sh r) where
  Concrete u ==. Concrete v = u == v

instance GoodScalar r => OrdH Concrete (TKS sh r) where
  Concrete u <. Concrete v = u < v

instance GoodScalar r => EqH Concrete (TKX sh r) where
  Concrete u ==. Concrete v = u == v

instance GoodScalar r => OrdH Concrete (TKX sh r) where
  Concrete u <. Concrete v = u < v

deriving instance Eq (RepConcrete y) => Eq (Concrete y)
deriving instance Ord (RepConcrete y) => Ord (Concrete y)
deriving instance Num (RepConcrete y) => Num (Concrete y)
deriving instance IntegralH (RepConcrete y) => IntegralH (Concrete y)
deriving instance Real (RepConcrete y) => Real (Concrete y)
deriving instance Fractional (RepConcrete y) => Fractional (Concrete y)
deriving instance Floating (RepConcrete y) => Floating (Concrete y)
deriving instance RealFrac (RepConcrete y) => RealFrac (Concrete y)
deriving instance RealFloatH (RepConcrete y) => RealFloatH (Concrete y)
deriving instance RealFloat (RepConcrete y) => RealFloat (Concrete y)

rtoVector :: GoodScalar r => Concrete (TKR n r) -> VS.Vector r
rtoVector  = Nested.rtoVector . unConcrete

stoVector :: GoodScalar r => Concrete (TKS sh r) -> VS.Vector r
stoVector = Nested.stoVector . unConcrete

xtoVector :: GoodScalar r => Concrete (TKX sh r) -> VS.Vector r
xtoVector = Nested.mtoVector . unConcrete
