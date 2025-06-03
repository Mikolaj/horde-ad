{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Two kinds of singletons for tensor kindss and constraints
-- and lemmas associated with the singletons.
module HordeAd.Core.TensorKind
  ( -- * Tensor kind singletons
    SingletonTK(..), KnownSTK(..), TKCastable(..), castSTK
  , withKnownSTK, lemKnownSTK, sameKnownSTK, sameSTK
  , stkUnit, buildSTK, razeSTK, adSTK
  , lemKnownSTKOfBuild, lemKnownSTKOfAD, lemBuildOfAD, lengthSTK, widthSTK
    -- * Full shape tensor kind quasi-singletons
  , FullShapeTK(..)
  , matchingFTK, ftkToSTK, ftkUnit, buildFTK, razeFTK, adFTK, differentiableFTK
  , DummyDualTarget(..)
  ) where

import Prelude hiding ((.))

import Control.Category
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import GHC.Exts (withDict)
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat, fromSNat)
import Type.Reflection (typeRep)

import Data.Array.Nested (MapJust, Replicate)
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)
import Data.Array.Nested.Convert (shxFromShS)

import HordeAd.Core.Types

-- * Tensor kind singletons

-- | Tensor kind singleton type.
type role SingletonTK nominal
data SingletonTK y where
  STKScalar :: GoodScalar r
            => SingletonTK (TKScalar r)
  STKR :: SNat n -> SingletonTK x -> SingletonTK (TKR2 n x)
  STKS :: ShS sh -> SingletonTK x -> SingletonTK (TKS2 sh x)
  STKX :: StaticShX sh -> SingletonTK x -> SingletonTK (TKX2 sh x)
  STKProduct :: SingletonTK y -> SingletonTK z
             -> SingletonTK (TKProduct y z)

deriving instance Show (SingletonTK y)

-- | The constraints corresponding to 'SingletonTK'.
class KnownSTK (y :: TK) where
  knownSTK :: SingletonTK y

instance GoodScalar r => KnownSTK (TKScalar r) where
  knownSTK = STKScalar

instance (KnownSTK x, KnownNat n)
         => KnownSTK (TKR2 n x) where
  knownSTK = STKR SNat knownSTK

instance (KnownSTK x, KnownShS sh)
         => KnownSTK (TKS2 sh x) where
  knownSTK = STKS knownShS knownSTK

instance (KnownSTK x, KnownShX sh)
         => KnownSTK (TKX2 sh x) where
  knownSTK = STKX knownShX knownSTK

instance (KnownSTK y, KnownSTK z)
         => KnownSTK (TKProduct y z) where
  knownSTK = STKProduct (knownSTK @y) (knownSTK @z)

-- | Turning a singleton into a constraint via a continuation.
withKnownSTK :: forall y r. SingletonTK y -> (KnownSTK y => r) -> r
withKnownSTK = withDict @(KnownSTK y)

-- | Turning a singleton into a dictionary containing constraint.
lemKnownSTK :: SingletonTK y -> Dict KnownSTK y
lemKnownSTK = \case
  STKScalar -> Dict
  STKR SNat x | Dict <- lemKnownSTK x -> Dict
  STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh Dict
  STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemKnownSTK stk1
                       , Dict <- lemKnownSTK stk2 -> Dict

sameKnownSTK :: forall y1 y2. (KnownSTK y1, KnownSTK y2)
             => Maybe (y1 :~: y2)
sameKnownSTK = sameSTK (knownSTK @y1) (knownSTK @y2)

-- | A plausible implementation of `testEquality` on `SingletonTK`.
sameSTK :: SingletonTK y1 -> SingletonTK y2 -> Maybe (y1 :~: y2)
sameSTK stk1 stk2 = case (stk1, stk2) of
  (STKScalar @r1, STKScalar @r2)
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      Just Refl
  (STKR snat1 x1, STKR snat2 x2)
    | Just Refl <- sameSTK x1 x2, Just Refl <- testEquality snat1 snat2 ->
      Just Refl
  (STKS sh1 x1, STKS sh2 x2)
    | Just Refl <- sameSTK x1 x2, Just Refl <- testEquality sh1 sh2 ->
      Just Refl
  (STKX sh1 x1, STKX sh2 x2)
    | Just Refl <- sameSTK x1 x2, Just Refl <- testEquality sh1 sh2 ->
      Just Refl
  (STKProduct x1 y1, STKProduct x2 y2)
    | Just Refl <- sameSTK x1 x2, Just Refl <- sameSTK y1 y2 ->
      Just Refl
  _ -> Nothing

stkUnit :: SingletonTK TKUnit
stkUnit = STKScalar

buildSTK :: SNat k -> SingletonTK y -> SingletonTK (BuildTensorKind k y)
buildSTK snat@SNat = \case
  stk@STKScalar -> STKS (snat :$$ ZSS) stk
  STKR SNat x -> STKR SNat x
  STKS sh x -> STKS (snat :$$ sh) x
  STKX sh x -> STKX (SKnown snat :!% sh) x
  STKProduct stk1 stk2 -> STKProduct (buildSTK snat stk1) (buildSTK snat stk2)

razeSTK :: SingletonTK z -> SingletonTK (RazeTensorKind z)
razeSTK = \case
  STKScalar -> error "razeSTK: impossible argument"
  STKR snat@SNat x ->
    case cmpNat (SNat @1) snat of
      LTI -> STKR SNat x
      EQI -> STKR SNat x
      _ -> error "razeSTK: impossible argument"
  STKS ZSS _ -> error "razeSTK: impossible argument"
  STKS (_ :$$ sh) x -> STKS sh x
  STKX ZKX _ -> error "razeSTK: impossible argument"
  STKX (SUnknown _ :!% _) _ -> error "razeSTK: impossible argument"
  STKX (SKnown _ :!% sh) x -> STKX sh x
  STKProduct stk1 stk2 -> STKProduct (razeSTK stk1) (razeSTK stk2)

adSTK :: SingletonTK y -> SingletonTK (ADTensorKind y)
adSTK = \case
  t@(STKScalar @r) -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0)
           STKScalar
  STKR sh x -> STKR sh $ adSTK x
  STKS sh x -> STKS sh $ adSTK x
  STKX sh x -> STKX sh $ adSTK x
  STKProduct stk1 stk2 -> STKProduct (adSTK stk1) (adSTK stk2)

lemKnownSTKOfBuild :: SNat k -> SingletonTK y
                     -> Dict KnownSTK (BuildTensorKind k y)
lemKnownSTKOfBuild snat = lemKnownSTK . buildSTK snat

lemKnownSTKOfAD :: SingletonTK y
                  -> Dict KnownSTK (ADTensorKind y)
lemKnownSTKOfAD = lemKnownSTK . adSTK

lemBuildOfAD :: SNat k -> SingletonTK y
             -> BuildTensorKind k (ADTensorKind y)
                :~: ADTensorKind (BuildTensorKind k y)
lemBuildOfAD snat@SNat = \case
  STKScalar -> Refl
  STKR{} -> unsafeCoerceRefl
  STKS{} -> unsafeCoerceRefl
  STKX{} -> unsafeCoerceRefl
  STKProduct stk1 stk2 | Refl <- lemBuildOfAD snat stk1
                       , Refl <- lemBuildOfAD snat stk2 -> Refl

lengthSTK :: SingletonTK x -> Int
lengthSTK STKScalar = 0
lengthSTK (STKR snat _) = fromInteger $ fromSNat snat
lengthSTK (STKS sh _) = shsLength sh
lengthSTK (STKX sh _) = ssxLength sh
lengthSTK (STKProduct sy sz) = lengthSTK sy `max` lengthSTK sz

widthSTK :: SingletonTK y -> Int
widthSTK stk = case stk of
  STKScalar @r -> case testEquality (typeRep @r) (typeRep @Z0) of
    Just Refl -> 0
    _ -> 1
  STKR{} -> 1
  STKS{} -> 1
  STKX{} -> 1
  STKProduct stk1 stk2 -> widthSTK stk1 + widthSTK stk2

type role TKCastable nominal nominal
data TKCastable (a :: TK) (b :: TK) where
  CastId  :: TKCastable a a
  CastCmp :: TKCastable b c -> TKCastable a b -> TKCastable a c

  CastRX  :: TKCastable (TKR2 n a) (TKX2 (Replicate n Nothing) a)
  CastSX  :: TKCastable (TKS2 sh a) (TKX2 (MapJust sh) a)

  CastXR  :: SingletonTK a -> TKCastable (TKX2 sh a) (TKR2 (Rank sh) a)
  CastXS  :: TKCastable (TKX2 (MapJust sh) a) (TKS2 sh a)
  CastXS' :: Rank sh ~ Rank sh'
          => SingletonTK (TKS2 sh' a)
          -> TKCastable (TKX2 sh a) (TKS2 sh' a)

  CastXX' :: Rank sh ~ Rank sh'
          => SingletonTK (TKX2 sh' a)
          -> TKCastable (TKX2 sh a) (TKX2 sh' a)

  CastRR  :: TKCastable a b -> TKCastable (TKR2 n a) (TKR2 n b)
  CastSS  :: TKCastable a b -> TKCastable (TKS2 sh a) (TKS2 sh b)
  CastXX  :: TKCastable a b -> TKCastable (TKX2 sh a) (TKX2 sh b)
  CastT2  :: TKCastable a a'
          -> TKCastable b b'
          -> TKCastable (TKProduct a b) (TKProduct a' b')

  Cast0X  :: SingletonTK (TKScalar a)
          -> TKCastable (TKScalar a) (TKX2 '[] (TKScalar a))
  CastX0  :: TKCastable (TKX2 '[] (TKScalar a)) (TKScalar a)

deriving instance Show (TKCastable a b)

instance Category TKCastable where
  id = CastId
  (.) = CastCmp

castSTK :: TKCastable a b -> SingletonTK a -> SingletonTK b
castSTK = \cases
  CastId astk -> astk
  (CastCmp c1 c2) astk -> castSTK c1 (castSTK c2 astk)
  CastRX (STKR n a) -> STKX (ssxReplicate n) a
  CastSX (STKS sh a) -> STKX (ssxFromShX $ shxFromShS sh) a
  (CastXR _stk) (STKX ssx a) -> STKR (ssxRank ssx) a
  CastXS (STKX ssx a) -> STKS (shsFromStaticShX ssx) a
  (CastXS' (STKS sh _x)) (STKX _ssx2 a) -> STKS sh a
  (CastXX' (STKX ssx _x)) (STKX _ssx2 a) -> STKX ssx a
  (CastRR c) (STKR n a) -> STKR n (castSTK c a)
  (CastSS c) (STKS sh a) -> STKS sh (castSTK c a)
  (CastXX c) (STKX ssx a) -> STKX ssx (castSTK c a)
  (CastT2 c1 c2) (STKProduct stk1 stk2) ->
    STKProduct (castSTK c1 stk1) (castSTK c2 stk2)
  (Cast0X _stk) stk -> STKX ZKX stk
  CastX0 (STKX ZKX stk) -> stk


-- * Full shape tensor kind quasi-singletons

-- | Full shape tensor kind singleton type.
type role FullShapeTK nominal
data FullShapeTK y where
  FTKScalar :: GoodScalar r
            => FullShapeTK (TKScalar r)
  FTKR :: IShR n -> FullShapeTK x -> FullShapeTK (TKR2 n x)
  FTKS :: ShS sh -> FullShapeTK x -> FullShapeTK (TKS2 sh x)
  FTKX :: IShX sh -> FullShapeTK x -> FullShapeTK (TKX2 sh x)
  FTKProduct :: FullShapeTK y -> FullShapeTK z
             -> FullShapeTK (TKProduct y z)

deriving instance Show (FullShapeTK y)
deriving instance Eq (FullShapeTK y)

-- | A plausible implementation of `testEquality` on `FullShapeTK`. It does not
-- take into account shape difference in ranked and mixed tensors
-- that `FullShapeTK`, but not `SingletonTK`, captures.
matchingFTK :: FullShapeTK y1 -> FullShapeTK y2 -> Maybe (y1 :~: y2)
matchingFTK ftk1 ftk2 = case (ftk1, ftk2) of
  (FTKScalar @r1, FTKScalar @r2)
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      Just Refl
  (FTKR sh1 x1, FTKR sh2 x2)
    | Just Refl <- matchingFTK x1 x2
    , Just Refl <- testEquality (shrRank sh1) (shrRank sh2) ->  -- weaker!!!
      Just Refl
  (FTKS sh1 x1, FTKS sh2 x2)
    | Just Refl <- matchingFTK x1 x2
    , Just Refl <- testEquality sh1 sh2 ->
      Just Refl
  (FTKX sh1 x1, FTKX sh2 x2)
    | Just Refl <- matchingFTK x1 x2
    , Just Refl <- testEquality (ssxFromShX sh1) (ssxFromShX sh2) ->  -- !!!
      Just Refl
  (FTKProduct x1 y1, FTKProduct x2 y2)
    | Just Refl <- matchingFTK x1 x2, Just Refl <- matchingFTK y1 y2 ->
      Just Refl
  _ -> Nothing

-- | A conversion that is fully determined by the property that it
-- commutes with the `testEquality` implementations.
ftkToSTK :: FullShapeTK y -> SingletonTK y
ftkToSTK = \case
  FTKScalar -> STKScalar
  FTKR sh x -> STKR (shrRank sh) (ftkToSTK x)
  FTKS sh x -> STKS sh (ftkToSTK x)
  FTKX sh x -> STKX (ssxFromShX sh) (ftkToSTK x)
  FTKProduct ftk1 ftk2 -> STKProduct (ftkToSTK ftk1) (ftkToSTK ftk2)

ftkUnit :: FullShapeTK TKUnit
ftkUnit = FTKScalar

buildFTK :: SNat k -> FullShapeTK y -> FullShapeTK (BuildTensorKind k y)
buildFTK snat@SNat = \case
  FTKScalar -> FTKS (snat :$$ ZSS) FTKScalar
  FTKR sh x -> FTKR (sNatValue snat :$: sh) x
  FTKS sh x -> FTKS (snat :$$ sh) x
  FTKX sh x -> FTKX (SKnown snat :$% sh) x
  FTKProduct ftk1 ftk2 -> FTKProduct (buildFTK snat ftk1) (buildFTK snat ftk2)

razeFTK :: forall y k.
           SNat k -> SingletonTK y
        -> FullShapeTK (BuildTensorKind k y)
        -> FullShapeTK y
razeFTK snat@SNat stk ftk = case (stk, ftk) of
  (STKScalar, FTKS (_ :$$ ZSS) FTKScalar) -> FTKScalar
  (STKR{}, FTKR (_ :$: sh) x) -> FTKR sh x
  (STKR{}, FTKR ZSR _) -> error "razeFTK: impossible built tensor kind"
  (STKS{}, FTKS (_ :$$ sh) x) -> FTKS sh x
  (STKX{}, FTKX (_ :$% sh) x) -> FTKX sh x
  (STKProduct stk1 stk2, FTKProduct ftk1 ftk2) ->
    FTKProduct (razeFTK snat stk1 ftk1) (razeFTK snat stk2 ftk2)

adFTK :: FullShapeTK y
      -> FullShapeTK (ADTensorKind y)
adFTK = \case
  t@(FTKScalar @r) -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0) $
           FTKScalar @Z0
  FTKR sh x -> FTKR sh $ adFTK x
  FTKS sh x -> FTKS sh $ adFTK x
  FTKX sh x -> FTKX sh $ adFTK x
  FTKProduct ftk1 ftk2 -> FTKProduct (adFTK ftk1) (adFTK ftk2)

-- A test whether the argument tensor collection is free
-- from any non-differentiable types, such as integers.
differentiableFTK :: FullShapeTK y -> Bool
differentiableFTK = \case
  FTKScalar @r -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> True
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> True
      _ -> False
  FTKR _ x -> differentiableFTK x
  FTKS _ x -> differentiableFTK x
  FTKX _ x -> differentiableFTK x
  FTKProduct ftk1 ftk2 -> differentiableFTK ftk1 && differentiableFTK ftk2

type role DummyDualTarget nominal
type DummyDualTarget :: Target
newtype DummyDualTarget y = DummyDualTarget (FullShapeTK y)
