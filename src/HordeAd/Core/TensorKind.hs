{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Two kinds of singletons for tensor kindss and constraints
-- and lemmas associated with the singletons.
module HordeAd.Core.TensorKind
  ( -- * Tensor kind singletons
    SingletonTK(..), KnownSTK(..)
  , TKConversion(..), castSTK, castFTK, buildTKConversion
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
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import GHC.Exts (withDict)
import GHC.TypeLits (KnownNat, OrderingI (..), cmpNat, fromSNat, type (+))
import Type.Reflection (typeRep)

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested.Convert (shrFromShX, shsFromShX, shxFromShS, shxFromShR)
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
  (.) = ConvCmp

castSTK :: TKConversion a b -> SingletonTK a -> SingletonTK b
castSTK = \cases
  ConvId astk -> astk
  (ConvCmp c1 c2) astk -> castSTK c1 (castSTK c2 astk)
  ConvRX (STKR n a) -> STKX (ssxReplicate n) a
  ConvSX (STKS sh a) -> STKX (ssxFromShX $ shxFromShS sh) a
  (ConvXR _stk) (STKX ssx a) -> STKR (ssxRank ssx) a
  ConvXS (STKX ssx a) -> STKS (shsFromStaticShX ssx) a
  (ConvXS' (FTKS sh _x)) (STKX _ssx2 a) -> STKS sh a
  (ConvXX' (FTKX shx _x)) (STKX _ssx2 a) -> STKX (ssxFromShX shx) a
  (ConvRR c) (STKR n a) -> STKR n (castSTK c a)
  (ConvSS c) (STKS sh a) -> STKS sh (castSTK c a)
  (ConvXX c) (STKX ssx a) -> STKX ssx (castSTK c a)
  (ConvT2 c1 c2) (STKProduct stk1 stk2) ->
    STKProduct (castSTK c1 stk1) (castSTK c2 stk2)
  (Conv0X _stk) stk -> STKX ZKX stk
  ConvX0 (STKX ZKX stk) -> stk
  (ConvNest (STKX ssx x)) (STKX shsh' _x) ->
    STKX ssx (STKX (ssxDropSSX shsh' ssx) x)
  ConvUnnest (STKX sh (STKX sh' x)) -> STKX (sh `ssxAppend` sh') x
  (ConvZip _ _) (STKProduct (STKX sh a1) (STKX _sh a2)) ->
    STKX sh (STKProduct a1 a2)
  (ConvUnzip _ _) (STKX sh (STKProduct a1 a2)) ->
    STKProduct (STKX sh a1) (STKX sh a2)

castFTK :: TKConversion a b -> FullShapeTK a -> FullShapeTK b
castFTK = \cases
  ConvId aftk -> aftk
  (ConvCmp c1 c2) aftk -> castFTK c1 (castFTK c2 aftk)
  ConvRX (FTKR shr a) -> FTKX (shxFromShR shr) a
  ConvSX (FTKS sh a) -> FTKX (shxFromShS sh) a
  (ConvXR _stk) (FTKX shx a) -> FTKR (shrFromShX shx) a
  ConvXS (FTKX shx a) -> FTKS (shsFromShX shx) a
  (ConvXS' ftk) _ -> ftk
  (ConvXX' ftk) _ -> ftk
  (ConvRR c) (FTKR shr a) -> FTKR shr (castFTK c a)
  (ConvSS c) (FTKS sh a) -> FTKS sh (castFTK c a)
  (ConvXX c) (FTKX shx a) -> FTKX shx (castFTK c a)
  (ConvT2 c1 c2) (FTKProduct ftk1 ftk2) ->
    FTKProduct (castFTK c1 ftk1) (castFTK c2 ftk2)
  (Conv0X _stk) ftk -> FTKX ZSX ftk
  ConvX0 (FTKX ZSX ftk) -> ftk
  (ConvNest @_ @_ @sh' (STKX ssx _x)) (FTKX shsh' x) ->
    FTKX (shxTakeSSX (Proxy @sh') shsh' ssx) (FTKX (shxDropSSX shsh' ssx) x)
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
  ConvCmp c1 c2 -> ConvCmp (buildTKConversion k (castFTK c2 aftk) c1)
                           (buildTKConversion k aftk c2)
  ConvRX | FTKR @n shr xstk <- aftk
         , Refl <- lemRankReplicate (Proxy @n)
         , Refl <- lemRankReplicate (Proxy @(1 + n)) ->
    ConvCmp (ConvXX' (FTKX (SKnown k :$% shxFromShR shr) xstk)) ConvRX
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
      ConvCmp (ConvXX (ConvXR (ftkToSTK x)))
              (ConvCmp (ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x)))
                       (ConvCmp
                          (ConvXX' (FTKX (SKnown k :$% shxFromShR shr) x))
                          ConvRX))
    FTKS _sh x ->
      ConvCmp (ConvXX ConvXS)
              (ConvCmp (ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x)))
                       ConvSX)
    FTKX _ssx x -> ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x))
    FTKProduct aftk1 aftk2 ->
      buildTKConversion
        k aftk (ConvCmp (ConvZip (ftkToSTK aftk1) (ftkToSTK aftk2))
                        (ConvT2 (Conv0X (ftkToSTK aftk1))
                                (Conv0X (ftkToSTK aftk2))))
  ConvX0 -> case aftk of
    FTKX ZSX FTKScalar -> ConvXS
    FTKX ZSX (FTKR @n _n x) | Refl <- lemRankReplicate (Proxy @n) ->
      ConvCmp (ConvXR (ftkToSTK x))
              (ConvCmp ConvUnnest (ConvXX ConvRX))
    FTKX ZSX FTKS{} ->
      ConvCmp ConvXS
              (ConvCmp ConvUnnest (ConvXX ConvSX))
    FTKX ZSX FTKX{} -> ConvUnnest
    FTKX ZSX (FTKProduct aftk1 aftk2) ->
      buildTKConversion
        k aftk (ConvCmp (ConvT2 ConvX0 ConvX0)
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
