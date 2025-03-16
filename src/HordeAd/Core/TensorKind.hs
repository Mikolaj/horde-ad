{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Various singletons for tensors and their associated constraints and lemmas.
module HordeAd.Core.TensorKind
  ( -- * Singletons
    SingletonTK(..), KnownSTK(..)
  , withKnownSTK, lemKnownSTK, sameKnownSTK, sameSTK
  , stkUnit, buildSTK, razeSTK, adSTK
  , lemKnownSTKOfBuild, lemKnownSTKOfAD, lemBuildOfAD, rankSTK, widthSTK
  , FullShapeTK(..), KnownFTK(..)
  , matchingFTK, ftkToSTK, ftkUnit, buildFTK, razeFTK, adFTK, differentiableFTK
  , DummyDualTarget(..)
    -- * Generic types of booleans and related class definitions
  , BoolOf, Boolean(..), EqH(..), OrdH(..)
  ) where

import Prelude

import Data.Boolean (Boolean (..))
import Data.Kind (Type)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import GHC.Exts (withDict)
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat, fromSNat)
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.Types

-- * Singletons

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

withKnownSTK :: forall y r. SingletonTK y -> (KnownSTK y => r) -> r
withKnownSTK = withDict @(KnownSTK y)

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
  stk@(STKScalar) -> STKS (snat :$$ ZSS) stk
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

adSTK :: SingletonTK y
      -> SingletonTK (ADTensorKind y)
adSTK = \case
  t@(STKScalar @r) -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0) $
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

rankSTK :: SingletonTK x -> Int
rankSTK (STKScalar) = 0
rankSTK (STKR snat _) = fromInteger $ fromSNat snat
rankSTK (STKS sh _) = fromInteger $ fromSNat $ shsRank sh
rankSTK (STKX sh _) = fromInteger $ fromSNat $ ssxRank sh
rankSTK (STKProduct sy sz) = rankSTK sy `max` rankSTK sz

widthSTK :: SingletonTK y -> Int
widthSTK stk = case stk of
  STKScalar @r -> case testEquality (typeRep @r) (typeRep @Z0) of
    Just Refl -> 0
    _ -> 1
  STKR{} -> 1
  STKS{} -> 1
  STKX{} -> 1
  STKProduct stk1 stk2 -> widthSTK stk1 + widthSTK stk2

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

class KnownFTK (y :: TK) where
  knownFTK :: FullShapeTK y

instance GoodScalar r => KnownFTK (TKScalar r) where
  knownFTK = FTKScalar

instance (KnownFTK x, KnownShS sh)
         => KnownFTK (TKS2 sh x) where
  knownFTK = FTKS knownShS knownFTK

instance (KnownFTK y, KnownFTK z)
         => KnownFTK (TKProduct y z) where
  knownFTK = FTKProduct (knownFTK @y) (knownFTK @z)

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
    , Just Refl <- testEquality (ssxFromShape sh1) (ssxFromShape sh2) ->  -- !!!
      Just Refl
  (FTKProduct x1 y1, FTKProduct x2 y2)
    | Just Refl <- matchingFTK x1 x2, Just Refl <- matchingFTK y1 y2 ->
      Just Refl
  _ -> Nothing

ftkToSTK :: FullShapeTK y -> SingletonTK y
ftkToSTK = \case
  FTKScalar -> STKScalar
  FTKR sh x -> STKR (shrRank sh) (ftkToSTK x)
  FTKS sh x -> STKS sh (ftkToSTK x)
  FTKX sh x -> STKX (ssxFromShape sh) (ftkToSTK x)
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
data DummyDualTarget y = DummyDualTarget (FullShapeTK y)


-- * Generic types of booleans and related class definitions

type family BoolOf (t :: Target) :: Type

infix 4 ==., /=.
class Boolean (BoolOf f) => EqH (f :: Target) y where
  (==.), (/=.) :: f y -> f y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (BoolOf f) => OrdH (f :: Target) y where
  (<.), (<=.), (>.), (>=.) :: f y -> f y -> BoolOf f
  u >. v = v <. u
  u >=. v = notB (u <. v)
  u <=. v = v >=. u
