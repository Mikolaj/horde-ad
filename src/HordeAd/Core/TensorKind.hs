{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Various singletons for tensors and their associated constraints and lemmas.
module HordeAd.Core.TensorKind
  ( -- * Singletons
    STensorKindType(..), TensorKind(..)
  , lemTensorKindOfS, sameTensorKind, sameTK, lemTensorKindOfBuild
  , lemTensorKindOfAD, lemTensorKind1OfAD, lemBuildOfAD
  , FullTensorKind(..), lemTensorKindOfF, buildFullTensorKind
  , aDTensorKind, aDTensorKind1
    -- * Type family RepORArray
  , RepORArray, TensorKind2
  , RepN(..)  -- only temporarily here
    -- * Misc
  , RepD(..)
  , DynamicTensor(..)
  , HVector
  , VoidTensor, absurdTensor, VoidHVector, DynamicScalar(..)
  , scalarDynamic, shapeVoidDynamic, shapeVoidHVector, shapeDynamicF
  , rankDynamic, isDynamicRanked, voidFromShL, voidFromSh, voidFromShS
  , voidFromDynamicF, replicate1VoidHVector, index1HVectorF, replicate1HVectorF
    -- * Generic types of booleans and related class definitions
  , BoolOf, Boolean(..)
  , IfF(..), EqF(..), OrdF(..), minF, maxF
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Data.Boolean (Boolean (..))
import Data.Default
import Data.Kind (Type)
import Data.Maybe (isJust)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, type (+))
import Type.Reflection (TypeRep, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Shape
  (IShX, KnownShX (..), StaticShX (..), ssxFromShape)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , KnownShS (..)
  , SMayNat (..)
  , ShR (..)
  , ShS (..)
  , ShX (..)
  , pattern (:$:)
  , pattern ZSR
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shrRank)

import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * Singletons

type role STensorKindType nominal
data STensorKindType y where
  STKScalar :: GoodScalar r
            => TypeRep r -> STensorKindType (TKScalar r)
  STKR :: forall n x. Nested.Elt (RepORArray x)
          => SNat n -> STensorKindType x -> STensorKindType (TKR2 n x)
  STKS :: forall sh x. Nested.Elt (RepORArray x)
          => ShS sh -> STensorKindType x -> STensorKindType (TKS2 sh x)
  STKX :: forall sh x. Nested.Elt (RepORArray x)
          => StaticShX sh -> STensorKindType x -> STensorKindType (TKX2 sh x)
  STKProduct :: STensorKindType y -> STensorKindType z
             -> STensorKindType (TKProduct y z)
  STKUntyped :: STensorKindType TKUntyped

deriving instance Show (STensorKindType y)

class TensorKind (y :: TensorKindType) where
  stensorKind :: STensorKindType y

instance GoodScalar r => TensorKind (TKScalar r) where
  stensorKind = STKScalar typeRep

instance (TensorKind x, Nested.Elt (RepORArray x), KnownNat n)
         => TensorKind (TKR2 n x) where
  stensorKind = STKR SNat stensorKind

instance (TensorKind x, Nested.Elt (RepORArray x), KnownShS sh)
         => TensorKind (TKS2 sh x) where
  stensorKind = STKS knownShS stensorKind

instance (TensorKind x, Nested.Elt (RepORArray x), KnownShX sh)
         => TensorKind (TKX2 sh x) where
  stensorKind = STKX knownShX stensorKind

instance (TensorKind y, TensorKind z)
         => TensorKind (TKProduct y z) where
  stensorKind = STKProduct (stensorKind @y) (stensorKind @z)

instance TensorKind TKUntyped where
  stensorKind = STKUntyped

lemTensorKindOfS :: STensorKindType y -> Dict TensorKind y
lemTensorKindOfS = \case
  STKScalar _ -> Dict
  STKR SNat x -> case lemTensorKindOfS x of
    Dict -> Dict
  STKS sh x -> case lemTensorKindOfS x of
    Dict -> withKnownShS sh Dict
  STKX sh x -> case lemTensorKindOfS x of
    Dict -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 -> Dict
  STKUntyped -> Dict

sameTensorKind :: forall y1 y2. (TensorKind y1, TensorKind y2) => Maybe (y1 :~: y2)
sameTensorKind = sameTK (stensorKind @y1) (stensorKind @y2)

sameTK :: STensorKindType y1' -> STensorKindType y2' -> Maybe (y1' :~: y2')
sameTK y1 y2 = case (y1, y2) of
    (STKScalar r1, STKScalar r2) ->
      case testEquality r1 r2 of
        Just Refl -> Just Refl
        Nothing -> Nothing
    (STKR snat1 r1, STKR snat2 r2) ->
      case (sameTK r1 r2, testEquality snat1 snat2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKS shs1 r1, STKS shs2 r2) ->
      case (sameTK r1 r2, testEquality shs1 shs2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKX shs1 r1, STKX shs2 r2) ->
      case (sameTK r1 r2, testEquality shs1 shs2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKProduct x1 z1, STKProduct x2 z2) -> case (sameTK x1 x2, sameTK z1 z2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
    (STKUntyped, STKUntyped) -> Just Refl
    _ -> Nothing

lemTensorKindOfBuild :: SNat k -> STensorKindType y
                     -> Dict TensorKind (BuildTensorKind k y)
lemTensorKindOfBuild snat@SNat = \case
  STKScalar{} -> Dict
  STKR SNat x -> case lemTensorKindOfS x of
    Dict -> Dict
  STKS sh x -> case lemTensorKindOfS x of
    Dict -> withKnownShS sh Dict
  STKX sh x -> case lemTensorKindOfS x of
    Dict -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfBuild snat stk1
                       , Dict <- lemTensorKindOfBuild snat stk2 -> Dict
  STKUntyped -> Dict

lemTensorKindOfAD :: forall y.
                     STensorKindType y
                  -> Dict TensorKind (ADTensorKind y)
lemTensorKindOfAD = fst . lemTensorKind1OfAD

lemTensorKind1OfAD :: forall y.
                      STensorKindType y
                   -> ( Dict TensorKind (ADTensorKind y)
                      , Dict Nested.Elt (RepORArray (ADTensorKind y)) )
lemTensorKind1OfAD = \case
  STKScalar @r rep -> case testEquality rep (typeRep @Double) of
    Just Refl -> (Dict, Dict)
    _ -> case testEquality rep (typeRep @Float) of
      Just Refl -> (Dict, Dict)
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           (Dict @TensorKind @(TKScalar Z0), Dict)
  STKR SNat rs -> case lemTensorKind1OfAD rs of
    (Dict, Dict) -> (Dict, Dict)
  STKS sh rs -> withKnownShS sh $ case lemTensorKind1OfAD rs of
    (Dict, Dict) -> (Dict, Dict)
  STKX sh rs -> withKnownShX sh $ case lemTensorKind1OfAD rs of
    (Dict, Dict) -> (Dict, Dict)
  STKProduct stk1 stk2 | (Dict, Dict) <- lemTensorKind1OfAD stk1
                       , (Dict, Dict) <- lemTensorKind1OfAD stk2 ->
    (Dict, Dict)
  STKUntyped ->
    (Dict, unsafeCoerce (Dict @Nested.Elt @Double))  -- never nested in arrays

lemBuildOfAD :: forall k y.
                SNat k -> STensorKindType y
             -> Maybe (BuildTensorKind k (ADTensorKind y)
                       :~: ADTensorKind (BuildTensorKind k y))
lemBuildOfAD snat@SNat = \case
  STKScalar{} -> Just unsafeCoerceRefl
  STKR{} -> Just unsafeCoerceRefl
  STKS{} -> Just unsafeCoerceRefl
  STKX{} -> Just unsafeCoerceRefl
  STKProduct stk1 stk2 ->
    case (lemBuildOfAD snat stk1, lemBuildOfAD snat stk2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
  STKUntyped -> Just Refl

type role FullTensorKind nominal
data FullTensorKind y where
  FTKScalar :: GoodScalar r => FullTensorKind (TKScalar r)
  FTKR :: forall n x. Nested.Elt (RepORArray x)
          => IShR n -> FullTensorKind x -> FullTensorKind (TKR2 n x)
  FTKS :: forall sh x. Nested.Elt (RepORArray x)
          => ShS sh -> FullTensorKind x -> FullTensorKind (TKS2 sh x)
  FTKX :: forall sh x. Nested.Elt (RepORArray x)
          => IShX sh -> FullTensorKind x -> FullTensorKind (TKX2 sh x)
  FTKProduct :: FullTensorKind y -> FullTensorKind z
             -> FullTensorKind (TKProduct y z)
  FTKUntyped :: VoidHVector -> FullTensorKind TKUntyped

deriving instance Show (FullTensorKind y)
deriving instance Eq (FullTensorKind y)

lemTensorKindOfF :: FullTensorKind y -> Dict TensorKind y
lemTensorKindOfF = \case
  FTKScalar -> Dict
  FTKR sh x | SNat <- shrRank sh -> case lemTensorKindOfF x of
    Dict -> Dict
  FTKS sh x -> case lemTensorKindOfF x of
    Dict -> withKnownShS sh Dict
  FTKX sh x -> case lemTensorKindOfF x of
    Dict -> withKnownShX (ssxFromShape sh) Dict
  FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfF ftk1
                       , Dict <- lemTensorKindOfF ftk2 -> Dict
  FTKUntyped{} -> Dict

buildFullTensorKind :: SNat k -> FullTensorKind y
                    -> FullTensorKind (BuildTensorKind k y)
buildFullTensorKind snat@SNat = \case
  FTKScalar -> FTKScalar
  FTKR sh x -> FTKR (sNatValue snat :$: sh) x
  FTKS sh x -> FTKS (snat :$$ sh) x
  FTKX sh x -> FTKX (SKnown snat :$% sh) x
  FTKProduct ftk1 ftk2 ->
      FTKProduct (buildFullTensorKind snat ftk1)
                 (buildFullTensorKind snat ftk2)
  FTKUntyped shs -> FTKUntyped $ replicate1VoidHVector snat shs

aDTensorKind :: FullTensorKind y
             -> FullTensorKind (ADTensorKind y)
aDTensorKind = fst . aDTensorKind1

aDTensorKind1 :: FullTensorKind y
                 -> ( FullTensorKind (ADTensorKind y)
                    , Dict Nested.Elt (RepORArray (ADTensorKind y)) )
aDTensorKind1 t = case t of
  FTKScalar @r -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> (t, Dict)
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> (t, Dict)
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           (FTKScalar @Z0, Dict)
  FTKR sh x -> case aDTensorKind1 x of
    (ftk, Dict) -> (FTKR sh ftk, Dict)
  FTKS sh x -> case aDTensorKind1 x of
    (ftk, Dict) -> (FTKS sh ftk, Dict)
  FTKX sh x -> case aDTensorKind1 x of
    (ftk, Dict) -> (FTKX sh ftk, Dict)
  FTKProduct ftk1 ftk2 -> case aDTensorKind1 ftk1 of
    (gtk1, Dict) -> case aDTensorKind1 ftk2 of
      (gtk2, Dict) -> (FTKProduct gtk1 gtk2, Dict)
  FTKUntyped{} ->
    (t, unsafeCoerce (Dict @Nested.Elt @Double))  -- never nested in arrays


-- * Type family RepORArray

type TensorKind2 y =
  ( TensorKind y, Default (RepORArray y), Nested.KnownElt (RepORArray y)
  , Show (RepORArray y), Num (RepORArray (ADTensorKind y)) )

type family RepORArray (y :: TensorKindType) where
  RepORArray (TKScalar r) = r
  RepORArray (TKR2 n x) = Nested.Ranked n (RepORArray x)
  RepORArray (TKS2 sh x) = Nested.Shaped sh (RepORArray x)
  RepORArray (TKX2 sh x) = Nested.Mixed sh (RepORArray x)
  RepORArray (TKProduct x z) = (RepORArray x, RepORArray z)
  RepORArray TKUntyped = HVector RepN

-- TODO: move back to HordeAd.Core.CarriersConcrete as soon as TKUntyped is gone
--
-- Needed because `RepORArray` can't be partially applied.
-- This type also lets us work around the woes with defining Show
-- for the Rep type family. It gives us a concrete thing
-- to attach a Show instance to.
type role RepN nominal
newtype RepN y = RepN {unRepN :: RepORArray y}


-- * Misc

type role RepD nominal nominal
data RepD target y where
  DTKScalar :: GoodScalar r
            => target (TKScalar r)
            -> RepD target (TKScalar r)
  DTKR :: (GoodScalar r, KnownNat n)
       => target (TKR n r)
       -> RepD target (TKR n r)
  DTKS :: (GoodScalar r, KnownShS sh)
       => target (TKS sh r)
       -> RepD target (TKS sh r)
  DTKX :: (GoodScalar r, KnownShX sh)
       => target (TKX sh r)
       -> RepD target (TKX sh r)
  DTKProduct :: forall x z target. (TensorKind x, TensorKind z)
             => RepD target x -> RepD target z
             -> RepD target (TKProduct x z)
  DTKUntyped :: HVector target
             -> RepD target TKUntyped

-- For thousands of tensor parameters, orthotope's dynamic tensors
-- are faster than the datatype below and the special dummy values are faster
-- than ordinary zero values. However, the library has become complex enough
-- that simplicity is the bottlenet, not speed, so we compromise,
-- keeping dummy values, but removing dynamic tensors.
--
-- Warning: r is an existential variable, a proper specialization needs
-- to be picked explicitly at runtime.
type role DynamicTensor nominal
data DynamicTensor (target :: Target) where
  DynamicRanked :: (GoodScalar r, KnownNat n)
                => target (TKR n r) -> DynamicTensor target
  DynamicShaped :: (GoodScalar r, KnownShS sh)
                => target (TKS sh r) -> DynamicTensor target
  DynamicRankedDummy :: (GoodScalar r, KnownShS sh)
                     => Proxy r -> Proxy sh -> DynamicTensor target
  DynamicShapedDummy :: (GoodScalar r, KnownShS sh)
                     => Proxy r -> Proxy sh -> DynamicTensor target

-- Ignores the contents of tensors --- to be used only for VoidHVector.
instance Eq (DynamicTensor VoidTensor) where
  (==) = dynamicsMatchVoid

dynamicsMatchVoid :: DynamicTensor VoidTensor -> DynamicTensor VoidTensor -> Bool
dynamicsMatchVoid t u = case (scalarDynamic t, scalarDynamic u) of
  (DynamicScalar @ru _, DynamicScalar @rt _) ->
    isJust (testEquality (typeRep @rt) (typeRep @ru))
    && shapeVoidDynamic t == shapeVoidDynamic u
    && isDynamicRanked t == isDynamicRanked u

deriving instance
  (forall y. TensorKind y => Show (target y))
  => Show (DynamicTensor target)

instance (forall y. TensorKind y => NFData (target y))
         => NFData (DynamicTensor target) where
  rnf (DynamicRanked x) = rnf x
  rnf (DynamicShaped x) = rnf x
  rnf (DynamicRankedDummy{}) = ()
  rnf (DynamicShapedDummy{}) = ()

-- | This is a heterogeneous vector, used as represenation of tuples
-- of tensors that need to have the same Haskell type regardless
-- of their arity and component types/shapes. This is a struct of arrays
-- representation, both as seen through its operations API and internally
-- and we convert to this representation ASAP whenever computations
-- result in another representation. Such tuples are also expressed via
-- an AST type `AstHVector` with a similar API. Both are used for arguments
-- and the result in the internal representation of lambdas (closed functions)
-- as used in fold-like and rev-like operations in the main library API.
-- The `target` assigns this or the AST implementation
-- based on the nature (symbolic or not) of the tensor type given to it.
type HVector (target :: Target) =
  Data.Vector.Vector (DynamicTensor target)
    -- When @target@ is terms, `HVector AstHVector` is a mixed half-symbolic
    -- representation, usually used for vectors composed of variables only,
    -- to adapt them into more complex types and back again.
    -- This representation is not used for vectors of large terms,
    -- since they'd share values, so AstHVector is used there instead.
    -- Operations such as AstHVectorLet serve to convert between
    -- the two, preserving sharing whenever possible. The only reason
    -- this exists is to express and preserve sharing, which is
    -- not possible with `HVector AstHVector` alone.

type role VoidTensor nominal
data VoidTensor :: Target

absurdTensor :: VoidTensor y -> a
absurdTensor = \case

instance Show (VoidTensor y) where
  showsPrec _d = absurdTensor

-- This is a tuple of void tensor, which incidentally makes this more like
-- a unit type (the only values beeing the dummy DynamicTensor constructors),
-- where the only values carry only the shapes/ranks and the scalar type.
type VoidHVector = HVector VoidTensor

type role DynamicScalar representational
data DynamicScalar (target :: Target) where
  DynamicScalar :: GoodScalar r
                => Proxy r -> DynamicScalar target

instance Show (DynamicScalar target) where
  showsPrec d (DynamicScalar (Proxy @t)) =
    showsPrec d (typeRep @t)  -- abuse for better error messages

scalarDynamic :: DynamicTensor target -> DynamicScalar target
scalarDynamic (DynamicRanked @r2 _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicShaped @r2 _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicRankedDummy @r2 _ _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicShapedDummy @r2 _ _) = DynamicScalar @r2 Proxy

shapeVoidDynamic :: DynamicTensor VoidTensor -> [Int]
shapeVoidDynamic  = shapeDynamicF absurdTensor

shapeVoidHVector :: VoidHVector -> [[Int]]
shapeVoidHVector = V.toList . V.map shapeVoidDynamic

shapeDynamicF :: (forall r n. (GoodScalar r, KnownNat n) => target (TKR n r) -> [Int])
              -> DynamicTensor target -> [Int]
{-# INLINE shapeDynamicF #-}
shapeDynamicF f (DynamicRanked t) = f t
shapeDynamicF _ (DynamicShaped @_ @sh _) = shapeT @sh
shapeDynamicF _ (DynamicRankedDummy _ proxy_sh) = shapeP proxy_sh
shapeDynamicF _ (DynamicShapedDummy _ proxy_sh) = shapeP proxy_sh

rankDynamic :: DynamicTensor target -> Int
rankDynamic (DynamicRanked @_ @n _) = valueOf @n
rankDynamic (DynamicShaped @_ @sh _) = length $ shapeT @sh
rankDynamic (DynamicRankedDummy _ proxy_sh) = length $ shapeP proxy_sh
rankDynamic (DynamicShapedDummy _ proxy_sh) = length $ shapeP proxy_sh

isDynamicRanked :: DynamicTensor target -> Bool
isDynamicRanked DynamicRanked{} = True
isDynamicRanked DynamicShaped{} = False
isDynamicRanked DynamicRankedDummy{} = True
isDynamicRanked DynamicShapedDummy{} = False

voidFromShL :: forall r. GoodScalar r
            => [Int] -> DynamicTensor VoidTensor
voidFromShL sh = withShapeP sh $ \proxySh ->
                   DynamicRankedDummy (Proxy @r) proxySh

voidFromSh :: forall r n. GoodScalar r
           => IShR n -> DynamicTensor VoidTensor
voidFromSh sh = voidFromShL @r (shapeToList sh)

voidFromShS :: forall r sh. (GoodScalar r, KnownShS sh)
            => DynamicTensor VoidTensor
voidFromShS = DynamicShapedDummy @r @sh Proxy Proxy

voidFromDynamicF
  :: forall target.
     (forall r n. (GoodScalar r, KnownNat n) => target (TKR n r) -> [Int])
  -> DynamicTensor target -> DynamicTensor VoidTensor
{-# INLINE voidFromDynamicF #-}
voidFromDynamicF f (DynamicRanked @r2 t) =
  let sh = f t
  in withShapeP sh $ \proxySh ->
       DynamicRankedDummy (Proxy @r2) proxySh
voidFromDynamicF _ (DynamicShaped @r2 @sh2 _) =
  DynamicShapedDummy @r2 @sh2 Proxy Proxy
voidFromDynamicF _ (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
voidFromDynamicF _ (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2

replicate1VoidHVector :: SNat k -> VoidHVector -> VoidHVector
replicate1VoidHVector k = V.map (replicate1VoidTensor k)

replicate1VoidTensor :: SNat k -> DynamicTensor VoidTensor
                     -> DynamicTensor VoidTensor
replicate1VoidTensor (SNat @k) u = case u of
  DynamicRankedDummy @r @sh p1 _ -> DynamicRankedDummy @r @(k ': sh) p1 Proxy
  DynamicShapedDummy @r @sh p1 _ -> DynamicShapedDummy @r @(k ': sh) p1 Proxy

index1HVectorF :: (forall r n. (GoodScalar r, KnownNat n)
                   => target (TKR n r) -> IShR n)
               -> (forall sh r. (GoodScalar r, KnownShS sh)
                   => target (TKS sh r) -> ShS sh)
               -> (forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
                   => target (TKR (m + n) r) -> IxROf target m -> target (TKR n r))
               -> (forall sh1 r sh2.
                   ( GoodScalar r, KnownShS sh1, KnownShS sh2
                   , KnownShS (sh1 ++ sh2) )
                   => target (TKS (sh1 ++ sh2) r) -> IxSOf target sh1
                   -> target (TKS sh2 r))
               -> HVector target -> IntOf target -> HVector target
{-# INLINE index1HVectorF #-}
index1HVectorF rshape sshape rindex sindex u i =
  V.map (flip (index1DynamicF rshape sshape rindex sindex) i) u

index1DynamicF :: (forall r n. (GoodScalar r, KnownNat n)
                   => target (TKR n r) -> IShR n)
               -> (forall sh r. (GoodScalar r, KnownShS sh)
                   => target (TKS sh r) -> ShS sh)
               -> (forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
                   => target (TKR (m + n) r) -> IxROf target m -> target (TKR n r))
               -> (forall sh1 r sh2.
                   ( GoodScalar r, KnownShS sh1, KnownShS sh2
                   , KnownShS (sh1 ++ sh2) )
                   => target (TKS (sh1 ++ sh2) r) -> IxSOf target sh1
                   -> target (TKS sh2 r))
               -> DynamicTensor target -> IntOf target -> DynamicTensor target
{-# INLINE index1DynamicF #-}
index1DynamicF rshape sshape rindex sindex u i = case u of
  DynamicRanked t -> case rshape t of
    ZSR -> error "index1Dynamic: rank 0"
    _ :$: _ -> DynamicRanked $ rindex t (singletonIndex i)
  DynamicShaped t -> case sshape t of
    ZSS -> error "index1Dynamic: rank 0"
    (:$$) SNat tl | Dict <- sshapeKnown tl ->
      DynamicShaped $ sindex t (ShapedList.singletonIndex i)
  DynamicRankedDummy @r @sh p1 _ -> case knownShS @sh of
    ZSS -> error "index1Dynamic: rank 0"
    (:$$) @_ @sh2 _ tl | Dict <- sshapeKnown tl ->
                         DynamicRankedDummy @r @sh2 p1 Proxy
  DynamicShapedDummy @r @sh p1 _ -> case knownShS @sh of
    ZSS -> error "index1Dynamic: rank 0"
    (:$$) @_ @sh2 _ tl | Dict <- sshapeKnown tl ->
                         DynamicShapedDummy @r @sh2 p1 Proxy

replicate1HVectorF :: (forall r n. (GoodScalar r, KnownNat n)
                       => Int -> target (TKR n r) -> target (TKR (1 + n) r))
                   -> (forall n sh r. (KnownNat n, KnownShS sh, GoodScalar r)
                       => target (TKS sh r) -> target (TKS (n ': sh) r))
                   -> SNat k -> HVector target -> HVector target
{-# INLINE replicate1HVectorF #-}
replicate1HVectorF rreplicate sreplicate k =
  V.map (replicate1DynamicF rreplicate sreplicate k)

replicate1DynamicF :: (forall r n. (GoodScalar r, KnownNat n)
                       => Int -> target (TKR n r) -> target (TKR (1 + n) r))
                   -> (forall n sh r. (KnownNat n, KnownShS sh, GoodScalar r)
                       => target (TKS sh r) -> target (TKS (n ': sh) r))
                   -> SNat k -> DynamicTensor target -> DynamicTensor target
{-# INLINE replicate1DynamicF #-}
replicate1DynamicF rreplicate sreplicate k@(SNat @k) u = case u of
  DynamicRanked t -> DynamicRanked $ rreplicate (sNatValue k) t
  DynamicShaped t -> DynamicShaped $ sreplicate @k t
  DynamicRankedDummy @r @sh p1 _ -> DynamicRankedDummy @r @(k ': sh) p1 Proxy
  DynamicShapedDummy @r @sh p1 _ -> DynamicShapedDummy @r @(k ': sh) p1 Proxy


-- * Generic types of booleans and related class definitions

type family BoolOf (t :: Target) :: Type

class Boolean (BoolOf f) => IfF (f :: Target) where
  ifF :: TensorKind y => BoolOf f -> f y -> f y -> f y

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

minF :: (IfF f, OrdF f, TensorKind y)
     => f y -> f y -> f y
minF u v = ifF (u <=. v) u v

maxF :: (IfF f, OrdF f, TensorKind y)
     => f y -> f y -> f y
maxF u v = ifF (u >=. v) u v
