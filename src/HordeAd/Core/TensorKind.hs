{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Various singletons for tensors and their associated constraints and lemmas.
module HordeAd.Core.TensorKind
  ( -- * Singletons
    STensorKindType(..), TensorKind(..)
  , withTensorKind, lemTensorKindOfSTK, sameTensorKind, sameSTK
  , stkUnit, buildSTK, razeSTK, aDSTK
  , lemTensorKindOfBuild, lemTensorKindOfAD, lemBuildOfAD
  , FullTensorKind(..), ftkToStk
  , ftkUnit, buildFTK, razeFTK, aDFTK, tftkG
    -- * Type family RepORArray
  , RepORArray, RepN(..), eltDictRep, showDictRep  -- only temporarily here
    -- * Generic types of booleans and related class definitions
  , BoolOf, Boolean(..), EqF(..), OrdF(..)
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
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
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed as Mixed
import Data.Array.Nested.Internal.Shape (shrRank, withKnownShS)

import HordeAd.Core.Types

-- * Singletons

type role STensorKindType nominal
data STensorKindType y where
  STKScalar :: GoodScalar r
            => TypeRep r -> STensorKindType (TKScalar r)
  STKR :: SNat n -> STensorKindType x -> STensorKindType (TKR2 n x)
  STKS :: ShS sh -> STensorKindType x -> STensorKindType (TKS2 sh x)
  STKX :: StaticShX sh -> STensorKindType x -> STensorKindType (TKX2 sh x)
  STKProduct :: STensorKindType y -> STensorKindType z
             -> STensorKindType (TKProduct y z)

deriving instance Show (STensorKindType y)

class TensorKind (y :: TensorKindType) where
  stensorKind :: STensorKindType y

instance GoodScalar r => TensorKind (TKScalar r) where
  stensorKind = STKScalar typeRep

instance (TensorKind x, KnownNat n)
         => TensorKind (TKR2 n x) where
  stensorKind = STKR SNat stensorKind

instance (TensorKind x, KnownShS sh)
         => TensorKind (TKS2 sh x) where
  stensorKind = STKS knownShS stensorKind

instance (TensorKind x, KnownShX sh)
         => TensorKind (TKX2 sh x) where
  stensorKind = STKX knownShX stensorKind

instance (TensorKind y, TensorKind z)
         => TensorKind (TKProduct y z) where
  stensorKind = STKProduct (stensorKind @y) (stensorKind @z)

withTensorKind :: forall y r. STensorKindType y -> (TensorKind y => r) -> r
withTensorKind = withDict @(TensorKind y)

lemTensorKindOfSTK :: STensorKindType y -> Dict TensorKind y
lemTensorKindOfSTK = \case
  STKScalar _ -> Dict
  STKR SNat x | Dict <- lemTensorKindOfSTK x -> Dict
  STKS sh x | Dict <- lemTensorKindOfSTK x -> withKnownShS sh Dict
  STKX sh x | Dict <- lemTensorKindOfSTK x -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                       , Dict <- lemTensorKindOfSTK stk2 -> Dict

sameTensorKind :: forall y1 y2. (TensorKind y1, TensorKind y2)
               => Maybe (y1 :~: y2)
sameTensorKind = sameSTK (stensorKind @y1) (stensorKind @y2)

sameSTK :: STensorKindType y1' -> STensorKindType y2' -> Maybe (y1' :~: y2')
sameSTK y1 y2 = case (y1, y2) of
  (STKScalar r1, STKScalar r2) ->
    case testEquality r1 r2 of
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

stkUnit :: STensorKindType TKUnit
stkUnit = STKScalar typeRep

buildSTK :: SNat k -> STensorKindType y -> STensorKindType (BuildTensorKind k y)
buildSTK snat@SNat = \case
  stk@(STKScalar{}) -> STKS (snat :$$ ZSS) stk
  STKR SNat x -> STKR SNat x
  STKS sh x -> STKS (snat :$$ sh) x
  STKX sh x -> STKX (SKnown snat :!% sh) x
  STKProduct stk1 stk2 -> STKProduct (buildSTK snat stk1) (buildSTK snat stk2)

razeSTK :: STensorKindType z -> STensorKindType (RazeTensorKind z)
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

aDSTK :: STensorKindType y
      -> STensorKindType (ADTensorKind y)
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

lemTensorKindOfBuild :: SNat k -> STensorKindType y
                     -> Dict TensorKind (BuildTensorKind k y)
lemTensorKindOfBuild snat = lemTensorKindOfSTK . buildSTK snat

lemTensorKindOfAD :: STensorKindType y
                  -> Dict TensorKind (ADTensorKind y)
lemTensorKindOfAD = lemTensorKindOfSTK . aDSTK

lemBuildOfAD :: SNat k -> STensorKindType y
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

ftkToStk :: FullTensorKind y -> STensorKindType y
ftkToStk = \case
  FTKScalar -> STKScalar typeRep
  FTKR sh x -> STKR (shrRank sh) (ftkToStk x)
  FTKS sh x -> STKS sh (ftkToStk x)
  FTKX sh x -> STKX (ssxFromShape sh) (ftkToStk x)
  FTKProduct ftk1 ftk2 -> STKProduct (ftkToStk ftk1) (ftkToStk ftk2)

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
           SNat k -> STensorKindType y
        -> FullTensorKind (BuildTensorKind k y)
        -> FullTensorKind y
razeFTK snat@SNat stk ftk = case (stk, ftk) of
  (STKScalar{}, FTKS (_ :$$ ZSS) FTKScalar) -> FTKScalar
  (STKR{}, FTKR (_ :$: sh) x) -> FTKR sh x
  (STKR{}, FTKR ZSR _) -> error "razeFTK: impossible built tensor kind"
  (STKS{}, FTKS (_ :$$ sh) x) -> FTKS sh x
  (STKX{}, FTKX (_ :$% sh) x) -> FTKX sh x
  (STKProduct stk1 stk2, FTKProduct ftk1 ftk2)
    | Dict <- lemTensorKindOfSTK stk1
    , Dict <- lemTensorKindOfSTK stk2 ->
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

tftkG :: STensorKindType y -> RepORArray y -> FullTensorKind y
tftkG stk t =
  let repackShapeTree :: STensorKindType y -> Mixed.ShapeTree (RepORArray y)
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
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                         , Dict <- lemTensorKindOfSTK stk2 ->
      FTKProduct (tftkG stk1 (fst t))
                 (tftkG stk2 (snd t))


-- * Type family RepORArray

type family RepORArray (y :: TensorKindType) where
  RepORArray (TKScalar r) = r
  RepORArray (TKR2 n x) = Nested.Ranked n (RepORArray x)
  RepORArray (TKS2 sh x) = Nested.Shaped sh (RepORArray x)
  RepORArray (TKX2 sh x) = Nested.Mixed sh (RepORArray x)
  RepORArray (TKProduct x z) = (RepORArray x, RepORArray z)

eltDictRep :: STensorKindType y -> Dict Nested.KnownElt (RepORArray y)
eltDictRep = \case
    STKScalar{} -> Dict
    STKR SNat x | Dict <- eltDictRep x -> Dict
    STKS sh x | Dict <- eltDictRep x -> withKnownShS sh Dict
    STKX sh x | Dict <- eltDictRep x -> withKnownShX sh Dict
    STKProduct stk1 stk2 | Dict <- eltDictRep stk1
                         , Dict <- eltDictRep stk2 -> Dict

showDictRep :: STensorKindType y -> Dict Show (RepORArray y)
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

nfdataDictRep :: STensorKindType y -> Dict NFData (RepORArray y)
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

-- TODO: move back to HordeAd.Core.CarriersConcrete as soon as TKUntyped is gone
--
-- Needed because `RepORArray` can't be partially applied.
-- This type also lets us work around the woes with defining Show
-- for the Rep type family. It gives us a concrete thing
-- to attach a Show instance to.
type role RepN nominal
newtype RepN y = RepN {unRepN :: RepORArray y}

instance TensorKind y => Show (RepN y) where
  showsPrec d (RepN t) | Dict <- showDictRep (stensorKind @y) = showsPrec d t

instance TensorKind y => NFData (RepN y) where
  rnf (RepN t) | Dict <- nfdataDictRep (stensorKind @y) = rnf t

type instance BoolOf RepN = Bool

type instance HFunOf RepN x z = RepORArray x -> RepORArray z

type instance PrimalOf RepN = RepN

type instance DualOf RepN = DummyDualTarget

type instance ShareOf RepN = RepN


-- * Generic types of booleans and related class definitions

type family BoolOf (t :: Target) :: Type

infix 4 ==., /=.
class Boolean (BoolOf f) => EqF (f :: Target) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
  (==.), (/=.) :: TensorKind y => f y -> f y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (BoolOf f) => OrdF (f :: Target) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
  (<.), (<=.), (>.), (>=.) :: TensorKind y => f y -> f y -> BoolOf f
  u >. v = v <. u
  u >=. v = notB (u <. v)
  u <=. v = v >=. u
