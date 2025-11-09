{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Two kinds of singletons for tensor kindss and constraints
-- and lemmas associated with the singletons.
module HordeAd.Core.TensorKind
  ( -- * Tensor kind singletons
    SingletonTK(..), KnownSTK(..)
  , TKConversion(..), convCmp, lemTKAllNumConvert, lemTKAllNumConvertForward
  , lemTKAllNumBuild, lemTKAllNumRaze
  , numFromTKAllNum, convertSTK, convertFTK, buildTKConversion
  , withKnownSTK, lemKnownSTK, sameKnownSTK, sameSTK
  , Dict0(..), lemTKAllNumAD, lemTKScalarAllNumAD
  , stkUnit, buildSTK, razeSTK, adSTK
  , lemKnownSTKOfBuild, lemKnownSTKOfAD, lemBuildOfAD, lengthSTK, widthSTK
    -- * Full shape tensor kind quasi-singletons
  , FullShapeTK(..)
  , matchingFTK, ftkToSTK, ftkUnit, buildFTK, razeFTK, adFTK, differentiableFTK
  , DummyDualTarget(..)
  ) where

import Prelude hiding ((.))

import Control.Category
import Data.Int (Int64)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Foreign.C (CInt)
import GHC.Exts (withDict)
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat, fromSNat, type (+))
import Type.Reflection (typeRep)

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert
  (shrFromShX, shsFromSSX, shsFromShX, shxFromShR, shxFromShS)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

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
-- because it ensure the error case can't appear.
numFromTKAllNum :: forall r. (GoodScalar r, TKAllNum (TKScalar r))
                => Proxy r -> Dict0 (Num r, Nested.NumElt r)
numFromTKAllNum Proxy =
  case testEquality (typeRep @r) (typeRep @Int64) of
    Just Refl -> Dict0
    _ -> case testEquality (typeRep @r) (typeRep @CInt) of
      Just Refl -> Dict0
      _ -> case testEquality (typeRep @r) (typeRep @Double) of
        Just Refl -> Dict0
        _ -> case testEquality (typeRep @r) (typeRep @Float) of
          Just Refl -> Dict0
          _ -> case testEquality (typeRep @r) (typeRep @Z1) of
            Just Refl -> Dict0
            _ -> error "numFromTKAllNum: impossible type"

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
lengthSTK (STKR snat _) = fromInteger $ fromSNat snat
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

-- | This is copied, with modifications, from ox-arrays.
--
-- This is a recipe for converting arrays, not always followed,
-- and a proof a conversion is possible, with some proof obligations
-- delayed to runtime (in ConvXS' and ConvXX', where not only the ranks
-- of the shapes need to agree, but also the dimensions of the input
-- array and of the output shape, which is not all captured in the type).
-- As in ox-arrays, conversions only change the meta-data, not the underlying
-- vector representation of the array.
type role TKConversion nominal nominal
data TKConversion (a :: TK) (b :: TK) where
  ConvId  :: TKConversion a a
  ConvCmp :: TKConversion b c -> TKConversion a b -> TKConversion a c

  ConvRX  :: TKConversion (TKR2 n a) (TKX2 (Replicate n Nothing) a)
  ConvSX  :: TKConversion (TKS2 sh a) (TKX2 (MapJust sh) a)

  ConvXR  :: SingletonTK a -> TKConversion (TKX2 sh a) (TKR2 (Rank sh) a)
  ConvXS  :: TKConversion (TKX2 (MapJust sh) a) (TKS2 sh a)
  ConvXS' :: Rank sh ~ Rank sh'
          => FullShapeTK (TKS2 sh' a)
          -> TKConversion (TKX2 sh a) (TKS2 sh' a)

  ConvXX' :: Rank sh ~ Rank sh'
          => FullShapeTK (TKX2 sh' a)
          -> TKConversion (TKX2 sh a) (TKX2 sh' a)

  ConvRR  :: TKConversion a b -> TKConversion (TKR2 n a) (TKR2 n b)
  ConvSS  :: TKConversion a b -> TKConversion (TKS2 sh a) (TKS2 sh b)
  ConvXX  :: TKConversion a b -> TKConversion (TKX2 sh a) (TKX2 sh b)
  ConvT2  :: TKConversion a a'
          -> TKConversion b b'
          -> TKConversion (TKProduct a b) (TKProduct a' b')

  Conv0X  :: SingletonTK a -> TKConversion a (TKX2 '[] a)
  ConvX0  :: TKConversion (TKX2 '[] a) a

  ConvNest :: SingletonTK (TKX2 sh a)
           -> TKConversion (TKX2 (sh ++ sh') a) (TKX2 sh (TKX2 sh' a))
  ConvUnnest :: TKConversion (TKX2 sh (TKX2 sh' a)) (TKX2 (sh ++ sh') a)

  ConvZip   :: SingletonTK a -> SingletonTK b
            -> TKConversion (TKProduct (TKX2 sh a) (TKX2 sh b))
                            (TKX2 sh (TKProduct a b))
  ConvUnzip :: SingletonTK a -> SingletonTK b
            -> TKConversion (TKX2 sh (TKProduct a b))
                            (TKProduct (TKX2 sh a) (TKX2 sh b))

deriving instance Show (TKConversion a b)

instance Category TKConversion where
  id = ConvId
  (.) = convCmp

-- TODO: expand
convCmp :: TKConversion b c -> TKConversion a b -> TKConversion a c
convCmp a b = case (a, b) of
  (_, ConvId) -> a
  (ConvId, _) -> b
  (ConvCmp a1 a2, _) -> a1 . (a2 . b)
  (ConvSX, ConvXS) -> ConvId
  (ConvXR{}, ConvRX @n) | Refl <- lemRankReplicate (Proxy @n) -> ConvId
  (ConvXS @sh, ConvSX @sh') ->
    gcastWith (unsafeCoerceRefl :: sh :~: sh') $
    ConvId
  (ConvXS' @_ @sh' _, ConvSX @sh) ->
    gcastWith (unsafeCoerceRefl :: sh :~: sh') $
    ConvId
  (ConvXS' (FTKS ZSS _), Conv0X stk) -> ConvXS . Conv0X stk
  (ConvXX' (FTKX ZSX _), Conv0X stk) -> Conv0X stk
  (Conv0X{}, ConvX0) -> ConvId
  (ConvX0, ConvXX' @sh (FTKX ZSX _)) ->
    gcastWith (unsafeCoerceRefl :: sh :~: '[]) $
    ConvX0
  (ConvX0, Conv0X{}) -> ConvId
  (ConvT2 a1 a2, ConvT2 b1 b2) -> ConvT2 (convCmp a1 b1) (convCmp a2 b2)
  _ -> ConvCmp a b

lemTKAllNumConvert :: TKAllNum b
                   => TKConversion a b -> Dict0 (TKAllNum a)
lemTKAllNumConvert = \case
  ConvId -> Dict0
  ConvCmp c1 c2 | Dict0 <- lemTKAllNumConvert c1 ->
    lemTKAllNumConvert c2
  ConvRX -> Dict0
  ConvSX -> Dict0
  ConvXR{}  -> Dict0
  ConvXS -> Dict0
  ConvXS'{} -> Dict0
  ConvXX'{} -> Dict0
  ConvRR c | Dict0 <- lemTKAllNumConvert c -> Dict0
  ConvSS c | Dict0 <- lemTKAllNumConvert c -> Dict0
  ConvXX c | Dict0 <- lemTKAllNumConvert c -> Dict0
  ConvT2 c1 c2 | Dict0 <- lemTKAllNumConvert c1
               , Dict0 <- lemTKAllNumConvert c2 -> Dict0
  Conv0X{} -> Dict0
  ConvX0 -> Dict0
  ConvNest{} -> Dict0
  ConvUnnest -> Dict0
  ConvZip{} -> Dict0
  ConvUnzip{} -> Dict0

lemTKAllNumConvertForward :: TKAllNum a
                          => TKConversion a b -> Dict0 (TKAllNum b)
lemTKAllNumConvertForward = \case
  ConvId -> Dict0
  ConvCmp c1 c2 | Dict0 <- lemTKAllNumConvertForward c2 ->
    lemTKAllNumConvertForward c1
  ConvRX -> Dict0
  ConvSX -> Dict0
  ConvXR{}  -> Dict0
  ConvXS -> Dict0
  ConvXS'{} -> Dict0
  ConvXX'{} -> Dict0
  ConvRR c | Dict0 <- lemTKAllNumConvertForward c -> Dict0
  ConvSS c | Dict0 <- lemTKAllNumConvertForward c -> Dict0
  ConvXX c | Dict0 <- lemTKAllNumConvertForward c -> Dict0
  ConvT2 c1 c2 | Dict0 <- lemTKAllNumConvertForward c1
               , Dict0 <- lemTKAllNumConvertForward c2 -> Dict0
  Conv0X{} -> Dict0
  ConvX0 -> Dict0
  ConvNest{} -> Dict0
  ConvUnnest -> Dict0
  ConvZip{} -> Dict0
  ConvUnzip{} -> Dict0

convertSTK :: TKConversion a b -> SingletonTK a -> SingletonTK b
convertSTK = \cases
  ConvId astk -> astk
  (ConvCmp c1 c2) astk -> convertSTK c1 (convertSTK c2 astk)
  ConvRX (STKR n a) -> STKX (ssxReplicate n) a
  ConvSX (STKS sh a) -> STKX (ssxFromShX $ shxFromShS sh) a
  (ConvXR _stk) (STKX ssx a) -> STKR (ssxRank ssx) a
  ConvXS (STKX ssx a) -> STKS (shsFromSSX ssx) a
  (ConvXS' (FTKS sh _x)) (STKX _ssx2 a) -> STKS sh a
  (ConvXX' (FTKX shx _x)) (STKX _ssx2 a) -> STKX (ssxFromShX shx) a
  (ConvRR c) (STKR n a) -> STKR n (convertSTK c a)
  (ConvSS c) (STKS sh a) -> STKS sh (convertSTK c a)
  (ConvXX c) (STKX ssx a) -> STKX ssx (convertSTK c a)
  (ConvT2 c1 c2) (STKProduct stk1 stk2) ->
    STKProduct (convertSTK c1 stk1) (convertSTK c2 stk2)
  (Conv0X _stk) stk -> STKX ZKX stk
  ConvX0 (STKX ZKX stk) -> stk
  (ConvNest (STKX ssx x)) (STKX shsh' _x) ->
    STKX ssx (STKX (ssxDropSSX ssx shsh') x)
  ConvUnnest (STKX sh (STKX sh' x)) -> STKX (sh `ssxAppend` sh') x
  (ConvZip _ _) (STKProduct (STKX sh a1) (STKX _sh a2)) ->
    STKX sh (STKProduct a1 a2)
  (ConvUnzip _ _) (STKX sh (STKProduct a1 a2)) ->
    STKProduct (STKX sh a1) (STKX sh a2)

convertFTK :: TKConversion a b -> FullShapeTK a -> FullShapeTK b
convertFTK = \cases
  ConvId aftk -> aftk
  (ConvCmp c1 c2) aftk -> convertFTK c1 (convertFTK c2 aftk)
  ConvRX (FTKR shr a) -> FTKX (shxFromShR shr) a
  ConvSX (FTKS sh a) -> FTKX (shxFromShS sh) a
  (ConvXR _stk) (FTKX shx a) -> FTKR (shrFromShX shx) a
  ConvXS (FTKX shx a) -> FTKS (shsFromShX shx) a
  (ConvXS' ftk) _ -> ftk
  (ConvXX' ftk) _ -> ftk
  (ConvRR c) (FTKR shr a) -> FTKR shr (convertFTK c a)
  (ConvSS c) (FTKS sh a) -> FTKS sh (convertFTK c a)
  (ConvXX c) (FTKX shx a) -> FTKX shx (convertFTK c a)
  (ConvT2 c1 c2) (FTKProduct ftk1 ftk2) ->
    FTKProduct (convertFTK c1 ftk1) (convertFTK c2 ftk2)
  (Conv0X _stk) ftk -> FTKX ZSX ftk
  ConvX0 (FTKX ZSX ftk) -> ftk
  (ConvNest @_ @_ @sh' (STKX ssx _x)) (FTKX shsh' x) ->
    FTKX (shxTakeSSX (Proxy @sh') ssx shsh') (FTKX (shxDropSSX ssx shsh') x)
  ConvUnnest (FTKX sh (FTKX sh' x)) -> FTKX (sh `shxAppend` sh') x
  (ConvZip _ _) (FTKProduct (FTKX sh a1) (FTKX _sh a2)) ->
    FTKX sh (FTKProduct a1 a2)
  (ConvUnzip _ _) (FTKX sh (FTKProduct a1 a2)) ->
    FTKProduct (FTKX sh a1) (FTKX sh a2)

buildTKConversion :: SNat k -> FullShapeTK a
                  -> TKConversion a b
                  -> TKConversion (BuildTensorKind k a) (BuildTensorKind k b)
buildTKConversion k aftk c0 = case c0 of
  ConvId -> ConvId
  ConvCmp c1 c2 -> buildTKConversion k (convertFTK c2 aftk) c1
                   . buildTKConversion k aftk c2
  ConvRX | FTKR @n shr xstk <- aftk
         , Refl <- lemRankReplicate (Proxy @n)
         , Refl <- lemRankReplicate (Proxy @(1 + n)) ->
    convCmp (ConvXX' (FTKX (SKnown k :$% shxFromShR shr) xstk)) ConvRX
  ConvSX -> ConvSX
  ConvXR stk -> ConvXR stk
  ConvXS -> ConvXS
  ConvXS' ftk -> ConvXS' (buildFTK k ftk)
  ConvXX' ftk -> ConvXX' (buildFTK k ftk)
  ConvRR c -> ConvRR c
  ConvSS c -> ConvSS c
  ConvXX c -> ConvXX c
  ConvT2 c1 c2 | FTKProduct ftk1 ftk2 <- aftk ->
    ConvT2 (buildTKConversion k ftk1 c1) (buildTKConversion k ftk2 c2)
  Conv0X _astk -> case aftk of
    FTKScalar -> ConvSX
    FTKR @n shr x | Refl <- lemRankReplicate (Proxy @n)
                  , Refl <- lemRankReplicate (Proxy @(1 + n)) ->
      convCmp (ConvXX (ConvXR (ftkToSTK x)))
              (convCmp (ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x)))
                       (convCmp
                          (ConvXX' (FTKX (SKnown k :$% shxFromShR shr) x))
                          ConvRX))
    FTKS _sh x ->
      convCmp (ConvXX ConvXS)
              (convCmp (ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x)))
                       ConvSX)
    FTKX _ssx x -> ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x))
    FTKProduct aftk1 aftk2 ->
      buildTKConversion
        k aftk (convCmp (ConvZip (ftkToSTK aftk1) (ftkToSTK aftk2))
                        (ConvT2 (Conv0X (ftkToSTK aftk1))
                                (Conv0X (ftkToSTK aftk2))))
  ConvX0 -> case aftk of
    FTKX ZSX FTKScalar -> ConvXS
    FTKX ZSX (FTKR @n _n x) | Refl <- lemRankReplicate (Proxy @n) ->
      convCmp (ConvXR (ftkToSTK x))
              (convCmp ConvUnnest (ConvXX ConvRX))
    FTKX ZSX FTKS{} ->
      convCmp ConvXS
              (convCmp ConvUnnest (ConvXX ConvSX))
    FTKX ZSX FTKX{} -> ConvUnnest
    FTKX ZSX (FTKProduct aftk1 aftk2) ->
      buildTKConversion
        k aftk (convCmp (ConvT2 ConvX0 ConvX0)
                        (ConvUnzip (ftkToSTK aftk1) (ftkToSTK aftk2)))
  ConvNest (STKX sh x) -> ConvNest (STKX (SKnown k :!% sh) x)
  ConvUnnest -> ConvUnnest
  ConvZip astk1 astk2 -> ConvZip astk1 astk2
  ConvUnzip astk1 astk2 -> ConvUnzip astk1 astk2


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
           SNat k -> SingletonTK y -> FullShapeTK (BuildTensorKind k y)
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
