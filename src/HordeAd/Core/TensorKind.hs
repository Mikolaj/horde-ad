{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Various singletons for tensors and their associated constraints and lemmas.
module HordeAd.Core.TensorKind
  ( -- * Singletons
    STensorKind(..), KnownSTK(..)
  , withKnownSTK, lemKnownSTK, sameKnownSTS, sameSTK
  , stkUnit, buildSTK, razeSTK, aDSTK
  , lemKnownSTKOfBuild, lemKnownSTKOfAD, lemBuildOfAD
  , FullTensorKind(..), ftkToSTK
  , ftkUnit, buildFTK, razeFTK, aDFTK
  , DummyDualTarget(..)
    -- * Generic types of booleans and related class definitions
  , BoolOf, Boolean(..), EqF(..), OrdF(..)
  ) where

import Prelude

import Data.Boolean (Boolean (..))
import Data.Kind (Type)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import GHC.Exts (withDict)
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat)
import Type.Reflection (TypeRep, typeRep)

import Data.Array.Mixed.Shape (ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , IShX
  , KnownShS (..)
  , KnownShX (..)
  , SMayNat (..)
  , ShR (..)
  , ShS (..)
  , ShX (..)
  , StaticShX (..)
  )
import Data.Array.Nested.Internal.Shape (shrRank, withKnownShS)

import HordeAd.Core.Types

-- * Singletons

type role STensorKind nominal
data STensorKind y where
  STKScalar :: GoodScalar r
            => TypeRep r -> STensorKind (TKScalar r)
  STKR :: SNat n -> STensorKind x -> STensorKind (TKR2 n x)
  STKS :: ShS sh -> STensorKind x -> STensorKind (TKS2 sh x)
  STKX :: StaticShX sh -> STensorKind x -> STensorKind (TKX2 sh x)
  STKProduct :: STensorKind y -> STensorKind z
             -> STensorKind (TKProduct y z)

deriving instance Show (STensorKind y)

class KnownSTK (y :: TensorKindType) where
  stensorKind :: STensorKind y

instance GoodScalar r => KnownSTK (TKScalar r) where
  stensorKind = STKScalar typeRep

instance (KnownSTK x, KnownNat n)
         => KnownSTK (TKR2 n x) where
  stensorKind = STKR SNat stensorKind

instance (KnownSTK x, KnownShS sh)
         => KnownSTK (TKS2 sh x) where
  stensorKind = STKS knownShS stensorKind

instance (KnownSTK x, KnownShX sh)
         => KnownSTK (TKX2 sh x) where
  stensorKind = STKX knownShX stensorKind

instance (KnownSTK y, KnownSTK z)
         => KnownSTK (TKProduct y z) where
  stensorKind = STKProduct (stensorKind @y) (stensorKind @z)

withKnownSTK :: forall y r. STensorKind y -> (KnownSTK y => r) -> r
withKnownSTK = withDict @(KnownSTK y)

lemKnownSTK :: STensorKind y -> Dict KnownSTK y
lemKnownSTK = \case
  STKScalar _ -> Dict
  STKR SNat x | Dict <- lemKnownSTK x -> Dict
  STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh Dict
  STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemKnownSTK stk1
                       , Dict <- lemKnownSTK stk2 -> Dict

sameKnownSTS :: forall y1 y2. (KnownSTK y1, KnownSTK y2)
               => Maybe (y1 :~: y2)
sameKnownSTS = sameSTK (stensorKind @y1) (stensorKind @y2)

sameSTK :: STensorKind y1' -> STensorKind y2' -> Maybe (y1' :~: y2')
sameSTK y1 y2 = case (y1, y2) of
  (STKScalar tr1, STKScalar tr2) ->
    case testEquality tr1 tr2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
  (STKR snat1 r1, STKR snat2 r2) ->
    case (sameSTK r1 r2, testEquality snat1 snat2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
  (STKS shs1 r1, STKS shs2 r2) ->
    case (sameSTK r1 r2, testEquality shs1 shs2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
  (STKX shs1 r1, STKX shs2 r2) ->
    case (sameSTK r1 r2, testEquality shs1 shs2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
  (STKProduct x1 z1, STKProduct x2 z2) -> case (sameSTK x1 x2, sameSTK z1 z2) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
  _ -> Nothing

stkUnit :: STensorKind TKUnit
stkUnit = STKScalar typeRep

buildSTK :: SNat k -> STensorKind y -> STensorKind (BuildTensorKind k y)
buildSTK snat@SNat = \case
  stk@(STKScalar{}) -> STKS (snat :$$ ZSS) stk
  STKR SNat x -> STKR SNat x
  STKS sh x -> STKS (snat :$$ sh) x
  STKX sh x -> STKX (SKnown snat :!% sh) x
  STKProduct stk1 stk2 -> STKProduct (buildSTK snat stk1) (buildSTK snat stk2)

razeSTK :: STensorKind z -> STensorKind (RazeTensorKind z)
razeSTK = \case
  STKScalar{} -> error "razeSTK: impossible argument"
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

aDSTK :: STensorKind y
      -> STensorKind (ADTensorKind y)
aDSTK = \case
  t@(STKScalar @r tr) -> case testEquality tr (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality tr (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0) $
           STKScalar (typeRep @Z0)
  STKR sh x -> STKR sh $ aDSTK x
  STKS sh x -> STKS sh $ aDSTK x
  STKX sh x -> STKX sh $ aDSTK x
  STKProduct stk1 stk2 -> STKProduct (aDSTK stk1) (aDSTK stk2)

lemKnownSTKOfBuild :: SNat k -> STensorKind y
                     -> Dict KnownSTK (BuildTensorKind k y)
lemKnownSTKOfBuild snat = lemKnownSTK . buildSTK snat

lemKnownSTKOfAD :: STensorKind y
                  -> Dict KnownSTK (ADTensorKind y)
lemKnownSTKOfAD = lemKnownSTK . aDSTK

lemBuildOfAD :: SNat k -> STensorKind y
             -> BuildTensorKind k (ADTensorKind y)
                :~: ADTensorKind (BuildTensorKind k y)
lemBuildOfAD snat@SNat = \case
  STKScalar{} -> Refl
  STKR{} -> unsafeCoerceRefl
  STKS{} -> unsafeCoerceRefl
  STKX{} -> unsafeCoerceRefl
  STKProduct stk1 stk2 | Refl <- lemBuildOfAD snat stk1
                       , Refl <- lemBuildOfAD snat stk2 -> Refl

type role FullTensorKind nominal
data FullTensorKind y where
  FTKScalar :: GoodScalar r
            => FullTensorKind (TKScalar r)
  FTKR :: IShR n -> FullTensorKind x -> FullTensorKind (TKR2 n x)
  FTKS :: ShS sh -> FullTensorKind x -> FullTensorKind (TKS2 sh x)
  FTKX :: IShX sh -> FullTensorKind x -> FullTensorKind (TKX2 sh x)
  FTKProduct :: FullTensorKind y -> FullTensorKind z
             -> FullTensorKind (TKProduct y z)

deriving instance Show (FullTensorKind y)
deriving instance Eq (FullTensorKind y)

ftkToSTK :: FullTensorKind y -> STensorKind y
ftkToSTK = \case
  FTKScalar -> STKScalar typeRep
  FTKR sh x -> STKR (shrRank sh) (ftkToSTK x)
  FTKS sh x -> STKS sh (ftkToSTK x)
  FTKX sh x -> STKX (ssxFromShape sh) (ftkToSTK x)
  FTKProduct ftk1 ftk2 -> STKProduct (ftkToSTK ftk1) (ftkToSTK ftk2)

ftkUnit :: FullTensorKind TKUnit
ftkUnit = FTKScalar

buildFTK :: SNat k -> FullTensorKind y -> FullTensorKind (BuildTensorKind k y)
buildFTK snat@SNat = \case
  FTKScalar -> FTKS (snat :$$ ZSS) FTKScalar
  FTKR sh x -> FTKR (sNatValue snat :$: sh) x
  FTKS sh x -> FTKS (snat :$$ sh) x
  FTKX sh x -> FTKX (SKnown snat :$% sh) x
  FTKProduct ftk1 ftk2 -> FTKProduct (buildFTK snat ftk1) (buildFTK snat ftk2)

razeFTK :: forall y k.
           SNat k -> STensorKind y
        -> FullTensorKind (BuildTensorKind k y)
        -> FullTensorKind y
razeFTK snat@SNat stk ftk = case (stk, ftk) of
  (STKScalar{}, FTKS (_ :$$ ZSS) FTKScalar) -> FTKScalar
  (STKR{}, FTKR (_ :$: sh) x) -> FTKR sh x
  (STKR{}, FTKR ZSR _) -> error "razeFTK: impossible built tensor kind"
  (STKS{}, FTKS (_ :$$ sh) x) -> FTKS sh x
  (STKX{}, FTKX (_ :$% sh) x) -> FTKX sh x
  (STKProduct stk1 stk2, FTKProduct ftk1 ftk2)
    | Dict <- lemKnownSTK stk1
    , Dict <- lemKnownSTK stk2 ->
      FTKProduct (razeFTK snat stk1 ftk1) (razeFTK snat stk2 ftk2)

aDFTK :: FullTensorKind y
      -> FullTensorKind (ADTensorKind y)
aDFTK = \case
  t@(FTKScalar @r) -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0) $
           FTKScalar @Z0
  FTKR sh x -> FTKR sh $ aDFTK x
  FTKS sh x -> FTKS sh $ aDFTK x
  FTKX sh x -> FTKX sh $ aDFTK x
  FTKProduct ftk1 ftk2 -> FTKProduct (aDFTK ftk1) (aDFTK ftk2)

type role DummyDualTarget nominal
type DummyDualTarget :: Target
data DummyDualTarget y = DummyDualTarget (FullTensorKind y)


-- * Generic types of booleans and related class definitions

type family BoolOf (t :: Target) :: Type

infix 4 ==., /=.
class Boolean (BoolOf f) => EqF (f :: Target) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
  (==.), (/=.) :: KnownSTK y => f y -> f y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (BoolOf f) => OrdF (f :: Target) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
  (<.), (<=.), (>.), (>=.) :: KnownSTK y => f y -> f y -> BoolOf f
  u >. v = v <. u
  u >=. v = notB (u <. v)
  u <=. v = v >=. u
