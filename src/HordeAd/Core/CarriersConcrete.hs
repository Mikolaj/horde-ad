{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor operations implementation using the ox-arrays package.
-- These definitions, mostly class instances, are needed to make concrete
-- arrays a valid carrier for a tensor class algebra (instance) defined in
-- "HordeAd.Core.OpsConcrete".
module HordeAd.Core.CarriersConcrete
  ( -- * RepConcrete and its operations
    RepConcrete, tftkG, eltDictRep, showDictRep
  , replTargetRep, defTargetRep
    -- * Concrete and its instances
  , Concrete(..), rtoVector, stoVector, xtoVector
  ) where

import Prelude hiding (foldl')

import Control.DeepSeq (NFData (..))
import Data.Default
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Storable qualified as VS

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed qualified as Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked qualified as Ranked
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped qualified as Shaped
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (fromSNat')
import Data.Array.Strided.Orthotope (liftVEltwise1)

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Orphan ox-arrays instances

instance (Nested.IntElt r, Nested.PrimElt r, Eq r, Num r)
         => IntegralH (Nested.Ranked n r) where
  -- These can't be partial, because our conditionals are not lazy
  -- and so the counterfactual branches, with zeros, may get executed
  -- even though they are subsequently ignored.
  quotH a b = Nested.rquotArray a (Ranked.liftRanked1 mmakeNonZero b)
  remH a b = Nested.rremArray a (Ranked.liftRanked1 mmakeNonZero b)

instance (Nested.IntElt r, Nested.PrimElt r, Eq r, Num r)
         => IntegralH (Nested.Shaped sh r) where
  quotH a b = Nested.squotArray a (Shaped.liftShaped1 mmakeNonZero b)
  remH a b = Nested.sremArray a (Shaped.liftShaped1 mmakeNonZero b)

instance (Nested.IntElt r, Nested.PrimElt r, Eq r, Num r)
         => IntegralH (Nested.Mixed sh r) where
  quotH a b = Nested.mquotArray a (mmakeNonZero b)
  remH a b = Nested.mremArray a (mmakeNonZero b)

instance NumScalar r
         => Real (Nested.Ranked n r) where
  toRational = error "toRational is not defined for tensors"

instance NumScalar r
         => Real (Nested.Shaped sh r) where
  toRational = error "toRational is not defined for tensors"

instance NumScalar r
         => Real (Nested.Mixed sh r) where
  toRational = error "toRational is not defined for tensors"

instance (NumScalar r, Nested.FloatElt r)
         => RealFrac (Nested.Ranked n r) where
  properFraction = error "properFraction is not defined for tensors"

instance (NumScalar r, Nested.FloatElt r)
         => RealFrac (Nested.Shaped sh r) where
  properFraction = error "properFraction is not defined for tensors"

instance (NumScalar r, Nested.FloatElt r)
         => RealFrac (Nested.Mixed sh r) where
  properFraction = error "properFraction is not defined for tensors"

instance (Nested.PrimElt r, Nested.FloatElt r)
         => RealFloatH (Nested.Ranked n r) where
  atan2H = Nested.ratan2Array

instance (Nested.PrimElt r, Nested.FloatElt r)
         => RealFloatH (Nested.Shaped sh r) where
  atan2H = Nested.satan2Array

instance (Nested.PrimElt r, Nested.FloatElt r)
         => RealFloatH (Nested.Mixed sh r) where
  atan2H = Nested.matan2Array

instance (NumScalar r, Nested.PrimElt r, Nested.FloatElt r)
         => RealFloat (Nested.Ranked n r) where
  atan2 = Nested.ratan2Array
  floatRadix = error "operation not defined for tensors"
  floatDigits = error "operation not defined for tensors"
  floatRange = error "operation not defined for tensors"
  decodeFloat = error "operation not defined for tensors"
  encodeFloat = error "operation not defined for tensors"
  isNaN = error "operation not defined for tensors"
  isInfinite = error "operation not defined for tensors"
  isDenormalized = error "operation not defined for tensors"
  isNegativeZero = error "operation not defined for tensors"
  isIEEE = error "operation not defined for tensors"

instance (NumScalar r, Nested.PrimElt r, Nested.FloatElt r)
         => RealFloat (Nested.Shaped sh r) where
  atan2 = Nested.satan2Array
  floatRadix = error "operation not defined for tensors"
  floatDigits = error "operation not defined for tensors"
  floatRange = error "operation not defined for tensors"
  decodeFloat = error "operation not defined for tensors"
  encodeFloat = error "operation not defined for tensors"
  isNaN = error "operation not defined for tensors"
  isInfinite = error "operation not defined for tensors"
  isDenormalized = error "operation not defined for tensors"
  isNegativeZero = error "operation not defined for tensors"
  isIEEE = error "operation not defined for tensors"

instance (NumScalar r, Nested.PrimElt r, Nested.FloatElt r)
         => RealFloat (Nested.Mixed sh r) where
  atan2 = Nested.matan2Array
  floatRadix = error "operation not defined for tensors"
  floatDigits = error "operation not defined for tensors"
  floatRange = error "operation not defined for tensors"
  decodeFloat = error "operation not defined for tensors"
  encodeFloat = error "operation not defined for tensors"
  isNaN = error "operation not defined for tensors"
  isInfinite = error "operation not defined for tensors"
  isDenormalized = error "operation not defined for tensors"
  isNegativeZero = error "operation not defined for tensors"
  isIEEE = error "operation not defined for tensors"

-- TODO: make more efficient somehow?
mmakeNonZero :: (Nested.PrimElt r, Eq r, Num r)
             => Nested.Mixed sh r -> Nested.Mixed sh r
mmakeNonZero =
  Mixed.mliftNumElt1
    (`liftVEltwise1` (VS.map (\x -> if x == 0 then 1 else x)))


-- * RepConcrete and its operations

-- | The type family that represents tensor kinds in concrete arrays.
type family RepConcrete (y :: TK) where
  RepConcrete (TKScalar r) = r
  RepConcrete (TKR2 n x) = Nested.Ranked n (RepConcrete x)
  RepConcrete (TKS2 sh x) = Nested.Shaped sh (RepConcrete x)
  RepConcrete (TKX2 sh x) = Nested.Mixed sh (RepConcrete x)
  RepConcrete (TKProduct x z) = (RepConcrete x, RepConcrete z)

-- TODO: check if we can get errors due to the made-up shapes
-- and if the errors are early and clear. Maybe for nested fully shaped tensors
-- no errors are possible? Statically known dimensions are preserved fine
-- also in mixed arrays.
-- | Compute the full shape tensor kind for a concrete array.
-- If the array is empty and not shaped, shapes can be made up
-- (defaulting to zero dimensions).
tftkG :: SingletonTK y -> RepConcrete y -> FullShapeTK y
{-# INLINE tftkG #-}
tftkG stk t =
  let repackShapeTree :: SingletonTK y
                      -> Mixed.ShapeTree (RepConcrete y)
                      -> FullShapeTK y
      {-# NOINLINE repackShapeTree #-}
      repackShapeTree stk0 tree = case stk0 of
        STKScalar -> FTKScalar
        STKR _ stk1 -> let (sh, rest) = tree
                       in FTKR sh $ if shrSize sh == 0  -- rest crashes
                                    then zeroShapes stk1
                                    else repackShapeTree stk1 rest
        STKS _ stk1 -> let (sh, rest) = tree
                       in FTKS sh $ if shsSize sh == 0  -- rest crashes
                                    then zeroShapes stk1
                                    else repackShapeTree stk1 rest
        STKX _ stk1 -> let (sh, rest) = tree
                       in FTKX sh $ if shxSize sh == 0  -- rest crashes
                                    then zeroShapes stk1
                                    else repackShapeTree stk1 rest
        STKProduct stk1 stk2 ->
                       let (tree1, tree2) = tree
                       in FTKProduct (repackShapeTree stk1 tree1)
                                     (repackShapeTree stk2 tree2)
      zeroShapes :: SingletonTK y -> FullShapeTK y
      {-# NOINLINE zeroShapes #-}
      zeroShapes stk0 = case stk0 of
        STKScalar -> FTKScalar
        STKR n stk1 -> FTKR (shrFromList n (replicate (fromSNat' n) 0))
                            (zeroShapes stk1)
        STKS sh stk1 -> FTKS sh $ zeroShapes stk1  -- not made up in this case
        STKX ssx stk1 -> FTKX (shxCompleteZeros ssx) $ zeroShapes stk1
                           -- statically known shapes not made up
        STKProduct stk1 stk2 -> FTKProduct (zeroShapes stk1) (zeroShapes stk2)
  in case stk of  -- this starts with non-recursive shorthands
    STKScalar -> FTKScalar
    STKR _ STKScalar -> FTKR (Nested.rshape t) FTKScalar
    STKS sh STKScalar -> FTKS sh FTKScalar
    STKX _ STKScalar -> FTKX (Nested.mshape t) FTKScalar
    _ | Dict <- eltDictRep stk -> repackShapeTree stk (Mixed.mshapeTree t)

eltDictRep :: SingletonTK y -> Dict Nested.KnownElt (RepConcrete y)
{-# INLINE eltDictRep #-}
eltDictRep stk =
  let eltDictRec :: SingletonTK y -> Dict Nested.KnownElt (RepConcrete y)
      {-# NOINLINE eltDictRec #-}
      eltDictRec = \case
        STKScalar -> Dict
        STKR SNat x | Dict <- eltDictRec x -> Dict
        STKS sh x | Dict <- eltDictRec x -> withKnownShS sh Dict
        STKX sh x | Dict <- eltDictRec x -> withKnownShX sh Dict
        STKProduct stk1 stk2 | Dict <- eltDictRec stk1
                             , Dict <- eltDictRec stk2 -> Dict
  in case stk of
    STKScalar -> Dict  -- the prevalent case
    _ -> eltDictRec stk

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

replTargetRep :: TKAllNum y
              => (forall r. NumScalar r => r) -> FullShapeTK y -> RepConcrete y
replTargetRep r = \case
  FTKScalar @r | Dict0 <- numFromTKAllNum (Proxy @r) -> r
  FTKR sh (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
    Nested.rreplicatePrim sh r
  FTKS @sh sh (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r)
                             , Refl <- lemAppNil @sh ->
    Nested.sreplicatePrim sh r
  FTKX @sh sh (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r)
                             , Refl <- lemAppNil @sh ->
    Nested.mreplicatePrim sh r
  FTKR sh x | Dict <- eltDictRep (ftkToSTK x) ->
    Nested.rreplicate sh $ Nested.rscalar $ replTargetRep r x
  FTKS @sh sh x | Dict <- eltDictRep (ftkToSTK x)
                , Refl <- lemAppNil @sh ->
    Nested.sreplicate sh $ Nested.sscalar $ replTargetRep r x
  FTKX @sh sh x | Dict <- eltDictRep (ftkToSTK x)
                , Refl <- lemAppNil @sh ->
    Nested.mreplicate sh $ Nested.mscalar $ replTargetRep r x
  FTKProduct ftk1 ftk2 -> (replTargetRep r ftk1, replTargetRep r ftk2)

defTargetRep :: FullShapeTK y -> RepConcrete y
defTargetRep = \case
  FTKScalar -> def
  FTKR sh FTKScalar ->
    Nested.rreplicatePrim sh def
  FTKS @sh sh FTKScalar | Refl <- lemAppNil @sh ->
    Nested.sreplicatePrim sh def
  FTKX @sh sh FTKScalar | Refl <- lemAppNil @sh ->
    Nested.mreplicatePrim sh def
  FTKR sh x | Dict <- eltDictRep (ftkToSTK x) ->
    Nested.rreplicate sh $ Nested.rscalar $ defTargetRep x
  FTKS @sh sh x | Dict <- eltDictRep (ftkToSTK x)
                , Refl <- lemAppNil @sh ->
    Nested.sreplicate sh $ Nested.sscalar $ defTargetRep x
  FTKX @sh sh x | Dict <- eltDictRep (ftkToSTK x)
                , Refl <- lemAppNil @sh ->
    Nested.mreplicate sh $ Nested.mscalar $ defTargetRep x
  FTKProduct ftk1 ftk2 -> (defTargetRep ftk1, defTargetRep ftk2)


-- * Concrete and its instances

-- | A newtype wrapper over 'RepConcrete'.
-- It's needed because @RepConcrete@ can't be partially applied.
-- This type also lets us work around the woes with defining 'Show'
-- for the @RepConcrete@ type family. It gives us a concrete thing
-- to attach a @Show@ instance to.
type role Concrete nominal
newtype Concrete y = Concrete {unConcrete :: RepConcrete y}

instance KnownSTK y => Show (Concrete y) where
  showsPrec d (Concrete t) | Dict <- showDictRep (knownSTK @y) = showsPrec d t

instance KnownSTK y => NFData (Concrete y) where
  rnf (Concrete t) | Dict <- nfdataDictRep (knownSTK @y) = rnf t

type instance HFunOf Concrete x z = RepConcrete x -> RepConcrete z
type instance PrimalOf Concrete = Concrete
type instance DualOf Concrete = DummyDualTarget
type instance PlainOf Concrete = Concrete
type instance ShareOf Concrete = Concrete

instance GoodScalar r => EqH Concrete (TKScalar r) where
  Concrete u ==. Concrete v = Concrete $ u == v
instance GoodScalar r => OrdH Concrete (TKScalar r) where
  Concrete u <=. Concrete v = Concrete $ u <= v
instance GoodScalar r => EqH Concrete (TKR n r) where
  Concrete u ==. Concrete v = Concrete $ u == v
instance GoodScalar r => OrdH Concrete (TKR n r) where
  Concrete u <=. Concrete v = Concrete $ u <= v
instance GoodScalar r => EqH Concrete (TKS sh r) where
  Concrete u ==. Concrete v = Concrete $ u == v
instance GoodScalar r => OrdH Concrete (TKS sh r) where
  Concrete u <=. Concrete v = Concrete $ u <= v
instance GoodScalar r => EqH Concrete (TKX sh r) where
  Concrete u ==. Concrete v = Concrete $ u == v
instance GoodScalar r => OrdH Concrete (TKX sh r) where
  Concrete u <=. Concrete v = Concrete $ u <= v

deriving instance Boolean (Concrete (TKScalar Bool))
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
rtoVector = Nested.rtoVector . unConcrete

stoVector :: GoodScalar r => Concrete (TKS sh r) -> VS.Vector r
stoVector = Nested.stoVector . unConcrete

xtoVector :: GoodScalar r => Concrete (TKX sh r) -> VS.Vector r
xtoVector = Nested.mtoVector . unConcrete
