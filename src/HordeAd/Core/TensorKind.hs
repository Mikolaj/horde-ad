{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Two kinds of singletons for tensor kindss and constraints
-- and lemmas associated with the singletons.
module HordeAd.Core.TensorKind
  ( -- * Tensor kind singletons
    SingletonTK(..), KnownSTK(..)
  , withKnownSTK, lemKnownSTK, sameKnownSTK, sameSTK
  , Dict0(..), lemTKAllNumAD, lemTKScalarAllNumAD
  , lemTKAllNumBuild, lemTKAllNumRaze
  , numFromTKAllNum, contFromTKAllNum, contFromTypeable
  , stkUnit, buildSTK, razeSTK, adSTK
  , lemKnownSTKOfBuild, lemKnownSTKOfAD, lemBuildOfAD, lengthSTK, widthSTK
    -- * Full shape tensor kind quasi-singletons
  , FullShapeTK(..)
  , matchingFTK, ftkToSTK, ftkUnit, buildFTK, razeFTK, adFTK, differentiableFTK
  , DummyDualTarget(..)
  ) where

import Prelude hiding ((.))

import Control.Category
import Data.Int (Int16, Int32, Int64, Int8)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Foreign.C (CInt)
import GHC.Exts (withDict)
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat)
import Type.Reflection (Typeable, typeRep)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (fromSNat', unsafeCoerceRefl)

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

-- | Turn a singleton into a constraint via a continuation.
withKnownSTK :: forall y r. SingletonTK y -> (KnownSTK y => r) -> r
withKnownSTK = withDict @(KnownSTK y)

-- | Turn a singleton into a dictionary.
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
{-# INLINE sameSTK #-}
sameSTK = \cases
  (STKScalar @r1) (STKScalar @r2)
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      Just Refl
  -- A common non-recursive case as a shorthand:
  (STKS sh1 (STKScalar @r1)) (STKS sh2 (STKScalar @r2))
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
    , Just Refl <- testEquality sh1 sh2 ->
      Just Refl
  (STKR snat1 x1) (STKR snat2 x2)
    | Just Refl <- sameSTK x1 x2, Just Refl <- testEquality snat1 snat2 ->
      Just Refl
  (STKS sh1 x1) (STKS sh2 x2)
    | Just Refl <- sameSTK x1 x2, Just Refl <- testEquality sh1 sh2 ->
      Just Refl
  (STKX sh1 x1) (STKX sh2 x2)
    | Just Refl <- sameSTK x1 x2, Just Refl <- testEquality sh1 sh2 ->
      Just Refl
  (STKProduct x1 y1) (STKProduct x2 y2)
    | Just Refl <- sameSTK x1 x2, Just Refl <- sameSTK y1 y2 ->
      Just Refl
  _ _ -> Nothing

-- | Evidence for the constraint @c@. Works for type families,
-- such as @TKAllNum@.
type role Dict0 representational
data Dict0 c where
  Dict0 :: c => Dict0 c

lemTKAllNumAD :: SingletonTK y -> Dict0 (TKAllNum (ADTensorKind y))
lemTKAllNumAD = \case
  STKScalar @r | Dict0 <- lemTKScalarAllNumAD (Proxy @r) -> Dict0
  STKR _ x | Dict0 <- lemTKAllNumAD x -> Dict0
  STKS _ x | Dict0 <- lemTKAllNumAD x -> Dict0
  STKX _ x | Dict0 <- lemTKAllNumAD x -> Dict0
  STKProduct stk1 stk2 | Dict0 <- lemTKAllNumAD stk1
                       , Dict0 <- lemTKAllNumAD stk2 -> Dict0

lemTKScalarAllNumAD :: forall r. GoodScalar r
                    => Proxy r
                    -> Dict0 ( TKAllNum (TKScalar (ADTensorScalar r))
                             , Num (ADTensorScalar r)
                             , Nested.NumElt (ADTensorScalar r) )
lemTKScalarAllNumAD Proxy =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> Dict0
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> Dict0
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z1) $
           Dict0

lemTKAllNumBuild :: TKAllNum y
                 => SNat k -> SingletonTK y
                 -> Dict0 (TKAllNum (BuildTensorKind k y))
lemTKAllNumBuild k = \case
  STKScalar -> Dict0
  STKR{} -> Dict0
  STKS{} -> Dict0
  STKX{} -> Dict0
  STKProduct stk1 stk2 | Dict0 <- lemTKAllNumBuild k stk1
                       , Dict0 <- lemTKAllNumBuild k stk2 -> Dict0

lemTKAllNumRaze :: TKAllNum (BuildTensorKind k y)
                => SNat k -> SingletonTK y
                -> Dict0 (TKAllNum y)
lemTKAllNumRaze k = \case
  STKScalar -> Dict0
  STKR{} -> Dict0
  STKS{} -> Dict0
  STKX{} -> Dict0
  STKProduct stk1 stk2 | Dict0 <- lemTKAllNumRaze k stk1
                       , Dict0 <- lemTKAllNumRaze k stk2 -> Dict0

-- Despite what GHC says, TKAllNum (TKScalar r) is not redundant,
-- because it ensures the error case can't appear.
numFromTKAllNum :: forall r. (GoodScalar r, TKAllNum (TKScalar r))
                => Proxy r -> Dict0 (Num r, Nested.NumElt r)
numFromTKAllNum _ =
  case testEquality (typeRep @r) (typeRep @Int) of
    Just Refl -> Dict0
    _ -> case testEquality (typeRep @r) (typeRep @Double) of
      Just Refl -> Dict0
      _ -> case testEquality (typeRep @r) (typeRep @Float) of
        Just Refl -> Dict0
        _ -> case testEquality (typeRep @r) (typeRep @Z1) of
          Just Refl -> Dict0
          _ -> case testEquality (typeRep @r) (typeRep @Int64) of
            Just Refl -> Dict0
            _ -> case testEquality (typeRep @r) (typeRep @Int32) of
              Just Refl -> Dict0
              _ -> case testEquality (typeRep @r) (typeRep @Int16) of
                Just Refl -> Dict0
                _ -> case testEquality (typeRep @r) (typeRep @Int8) of
                  Just Refl -> Dict0
                  _ -> case testEquality (typeRep @r) (typeRep @CInt) of
                    Just Refl -> Dict0
                    _ -> error "numFromTKAllNum: impossible type"

-- The explicit dictionary is needed to trick GHC into specializing f at types
-- Int, Double, etc. insteasd of at type r, to simpify away the dictionaries
-- emerging from the constraints in the signature of f.
--
-- Despite what GHC says, TKAllNum (TKScalar r) is not redundant,
-- because it ensures the error case can't appear.
contFromTKAllNum :: forall r a. (Typeable r, TKAllNum (TKScalar r))
                 => (Dict0 (Num r, Nested.NumElt r, GoodScalar r) -> a) -> a
{-# INLINE contFromTKAllNum #-}  -- takes a function as an argument
contFromTKAllNum f = case typeRep @r of
  Is @Int -> f Dict0
  Is @Double -> f Dict0
  Is @Float -> f Dict0
  Is @Z1 -> f Dict0
  Is @Int64 -> f Dict0
  Is @Int32-> f Dict0
  Is @Int16 -> f Dict0
  Is @Int8 -> f Dict0
  Is @CInt -> f Dict0
  _ -> error "contFromTKAllNum: impossible type"

-- See above. The list comes from ox-arrays at [PRIMITIVE ELEMENT TYPES LIST].
contFromTypeable :: forall r a. Typeable r
                 => (Dict GoodScalar r -> a) -> a
{-# INLINE contFromTypeable #-}  -- takes a function as an argument
contFromTypeable f = case typeRep @r of
  Is @Int -> f Dict
  Is @Double -> f Dict
  Is @Float -> f Dict
  Is @Z1 -> f Dict
  Is @Int64 -> f Dict
  Is @Int32 -> f Dict
  Is @Int16-> f Dict
  Is @Int8 -> f Dict
  Is @CInt -> f Dict
  Is @Bool -> f Dict
  Is @() -> f Dict
  _ -> error "contFromTypeable: impossible type"

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
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z1)
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
lengthSTK (STKR snat _) = fromSNat' snat
lengthSTK (STKS sh _) = shsLength sh
lengthSTK (STKX sh _) = ssxLength sh
lengthSTK (STKProduct sy sz) = lengthSTK sy `max` lengthSTK sz

widthSTK :: SingletonTK y -> Int
widthSTK stk = case stk of
  STKScalar @r -> case testEquality (typeRep @r) (typeRep @Z1) of
    Just Refl -> 0
    _ -> 1
  STKR{} -> 1
  STKS{} -> 1
  STKX{} -> 1
  STKProduct stk1 stk2 -> widthSTK stk1 + widthSTK stk2


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
{-# INLINE matchingFTK #-}
matchingFTK = \cases
  (FTKScalar @r1) (FTKScalar @r2)
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) ->
      Just Refl
  -- A common non-recursive case as a shorthand:
  (FTKS sh1 (FTKScalar @r1)) (FTKS sh2 (FTKScalar @r2))
    | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
    , Just Refl <- testEquality sh1 sh2 ->
      Just Refl
  (FTKR sh1 x1) (FTKR sh2 x2)
    | Just Refl <- matchingFTK x1 x2
    , Just Refl <- testEquality (shrRank sh1) (shrRank sh2) ->  -- weaker!!!
      Just Refl
  (FTKS sh1 x1) (FTKS sh2 x2)
    | Just Refl <- matchingFTK x1 x2
    , Just Refl <- testEquality sh1 sh2 ->
      Just Refl
  (FTKX sh1 x1) (FTKX sh2 x2)
    | Just Refl <- matchingFTK x1 x2
    , Just Refl <- testEquality (ssxFromShX sh1) (ssxFromShX sh2) ->  -- !!!
      Just Refl
  (FTKProduct x1 y1) (FTKProduct x2 y2)
    | Just Refl <- matchingFTK x1 x2, Just Refl <- matchingFTK y1 y2 ->
      Just Refl
  _ _ -> Nothing

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
  FTKR sh x -> FTKR (fromSNat' snat :$: sh) x
  FTKS sh x -> FTKS (snat :$$ sh) x
  FTKX sh x -> FTKX (SKnown snat :$% sh) x
  FTKProduct ftk1 ftk2 -> FTKProduct (buildFTK snat ftk1) (buildFTK snat ftk2)

-- Depite the warning, the pattern match is exhaustive and if a dummy
-- pattern is added, GHC 9.14.1 complains about that, in turn.
razeFTK :: forall y k.
           SNat k -> SingletonTK y -> FullShapeTK (BuildTensorKind k y)
        -> FullShapeTK y
razeFTK snat@SNat stk ftk = case (stk, ftk) of
  (STKScalar, FTKS (_ :$$ ZSS) FTKScalar) -> FTKScalar
  (STKR{}, FTKR (_ :$: sh) x) -> FTKR sh x
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
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z1) $
           FTKScalar @Z1
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
