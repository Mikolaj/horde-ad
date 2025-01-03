{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Various singletons for tensors and their associated constraints and lemmas.
module HordeAd.Core.TensorKind
  ( -- * Singletons
    STensorKindType(..), TensorKind(..)
  , lemTensorKindOfSTK, sameTensorKind, sameSTK
  , lemTensorKindOfBuild, aDSTK, lemTensorKindOfAD, lemBuildOfAD
  , FullTensorKind(..), ftkToStk
  , buildFTK, razeFTK, aDFTK, tftkG
    -- * Type family RepORArray
  , RepORArray, RepN(..), eltDictRep, showDictRep  -- only temporarily here
    -- * Misc
  , DynamicTensor(..)
  , HVector
  , VoidTensor, absurdTensor, VoidHVector, DynamicScalar(..)
  , scalarDynamic, shapeVoidDynamic, shapeVoidHVector, shapeDynamicF
  , rankDynamic, isDynamicRanked, voidFromShL, voidFromSh, voidFromShS
  , voidFromDynamicF, replicate1VoidHVector, index1HVectorF, replicate1HVectorF
    -- * Generic types of booleans and related class definitions
  , BoolOf, Boolean(..), EqF(..), OrdF(..)
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Control.Exception.Assert.Sugar
import Data.Boolean (Boolean (..))
import Data.GADT.Compare
import Data.Kind (Type)
import Data.Maybe (isJust)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, type (+))
import Type.Reflection (TypeRep, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Shape
  (IShX, KnownShX (..), StaticShX (..), ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , IxR (..)
  , IxS (..)
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
import Data.Array.Nested.Internal.Mixed as Mixed
import Data.Array.Nested.Internal.Shape
  (shrRank, shsKnownShS, shsRank, withKnownShS)

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
  STKUntyped :: STensorKindType TKUntyped

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

instance TensorKind TKUntyped where
  stensorKind = STKUntyped

lemTensorKindOfSTK :: STensorKindType y -> Dict TensorKind y
lemTensorKindOfSTK = \case
  STKScalar _ -> Dict
  STKR SNat x | Dict <- lemTensorKindOfSTK x -> Dict
  STKS sh x | Dict <- lemTensorKindOfSTK x -> withKnownShS sh Dict
  STKX sh x | Dict <- lemTensorKindOfSTK x -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                       , Dict <- lemTensorKindOfSTK stk2 -> Dict
  STKUntyped -> Dict

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
  (STKUntyped, STKUntyped) -> Just Refl
  _ -> Nothing

lemTensorKindOfBuild :: SNat k -> STensorKindType y
                     -> Dict TensorKind (BuildTensorKind k y)
lemTensorKindOfBuild snat@SNat = \case
  STKScalar{} -> Dict
  STKR SNat x | Dict <- lemTensorKindOfSTK x -> Dict
  STKS sh x | Dict <- lemTensorKindOfSTK x  -> withKnownShS sh Dict
  STKX sh x | Dict <- lemTensorKindOfSTK x -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfBuild snat stk1
                       , Dict <- lemTensorKindOfBuild snat stk2 -> Dict
  STKUntyped -> Dict

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
  t@STKUntyped{} -> t

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
  STKUntyped -> Refl

type role FullTensorKind nominal
data FullTensorKind y where
  FTKScalar :: GoodScalar r
            => FullTensorKind (TKScalar r)
  FTKR :: IShR n -> FullTensorKind x -> FullTensorKind (TKR2 n x)
  FTKS :: ShS sh -> FullTensorKind x -> FullTensorKind (TKS2 sh x)
  FTKX :: IShX sh -> FullTensorKind x -> FullTensorKind (TKX2 sh x)
  FTKProduct :: FullTensorKind y -> FullTensorKind z
             -> FullTensorKind (TKProduct y z)
  FTKUntyped :: VoidHVector -> FullTensorKind TKUntyped

deriving instance Show (FullTensorKind y)
deriving instance Eq (FullTensorKind y)

ftkToStk :: FullTensorKind y -> STensorKindType y
ftkToStk = \case
  FTKScalar -> STKScalar typeRep
  FTKR sh x -> STKR (shrRank sh) (ftkToStk x)
  FTKS sh x -> STKS sh (ftkToStk x)
  FTKX sh x -> STKX (ssxFromShape sh) (ftkToStk x)
  FTKProduct ftk1 ftk2 -> STKProduct (ftkToStk ftk1) (ftkToStk ftk2)
  FTKUntyped{} -> STKUntyped

buildFTK :: SNat k -> FullTensorKind y -> FullTensorKind (BuildTensorKind k y)
buildFTK snat@SNat = \case
  FTKScalar -> FTKScalar
  FTKR sh x -> FTKR (sNatValue snat :$: sh) x
  FTKS sh x -> FTKS (snat :$$ sh) x
  FTKX sh x -> FTKX (SKnown snat :$% sh) x
  FTKProduct ftk1 ftk2 -> FTKProduct (buildFTK snat ftk1) (buildFTK snat ftk2)
  FTKUntyped shs -> FTKUntyped $ replicate1VoidHVector snat shs

razeFTK :: forall y k.
           SNat k -> STensorKindType y
        -> FullTensorKind (BuildTensorKind k y)
        -> FullTensorKind y
razeFTK snat@SNat stk ftk = case (stk, ftk) of
  (STKScalar{}, FTKScalar) -> FTKScalar
  (STKR{}, FTKR (_ :$: sh) x) -> FTKR sh x
  (STKR{}, FTKR ZSR _) -> error "razeFTK: impossible built tensor kind"
  (STKS{}, FTKS (_ :$$ sh) x) -> FTKS sh x
  (STKX{}, FTKX (_ :$% sh) x) -> FTKX sh x
  (STKProduct stk1 stk2, FTKProduct ftk1 ftk2)
    | Dict <- lemTensorKindOfSTK stk1
    , Dict <- lemTensorKindOfSTK stk2 ->
      FTKProduct (razeFTK snat stk1 ftk1) (razeFTK snat stk2 ftk2)
  (STKUntyped, FTKUntyped shs) -> FTKUntyped $ unreplicate1VoidHVector snat shs

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
  t@FTKUntyped{} -> t

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
        STKUntyped -> error "STKUntyped can be nested in arrays"
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
    STKUntyped ->
      FTKUntyped
      $ V.map (voidFromDynamicF (toList . Nested.rshape . unRepN)) t


-- * Type family RepORArray

type family RepORArray (y :: TensorKindType) where
  RepORArray (TKScalar r) = r
  RepORArray (TKR2 n x) = Nested.Ranked n (RepORArray x)
  RepORArray (TKS2 sh x) = Nested.Shaped sh (RepORArray x)
  RepORArray (TKX2 sh x) = Nested.Mixed sh (RepORArray x)
  RepORArray (TKProduct x z) = (RepORArray x, RepORArray z)
  RepORArray TKUntyped = HVector RepN

eltDictRep :: STensorKindType y -> Dict Nested.KnownElt (RepORArray y)
eltDictRep = \case
    STKScalar{} -> Dict
    STKR SNat x | Dict <- eltDictRep x -> Dict
    STKS sh x | Dict <- eltDictRep x -> withKnownShS sh Dict
    STKX sh x | Dict <- eltDictRep x -> withKnownShX sh Dict
    STKProduct stk1 stk2 | Dict <- eltDictRep stk1
                         , Dict <- eltDictRep stk2 -> Dict
    STKUntyped ->
      unsafeCoerce (Dict @Nested.KnownElt @Double)
        -- these are never nested in arrays, so this hack is fine

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
    STKUntyped -> Dict

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

type instance BoolOf RepN = Bool

type instance HFunOf RepN x z = RepORArray x -> RepORArray z

type instance PrimalOf RepN = RepN

type instance DualOf RepN = DummyDualTarget

type instance ShareOf RepN = RepN


-- * Misc

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
shapeDynamicF _ (DynamicShaped @_ @sh _) = toList $ knownShS @sh
shapeDynamicF _ (DynamicRankedDummy _ proxy_sh) = shapeP proxy_sh
shapeDynamicF _ (DynamicShapedDummy _ proxy_sh) = shapeP proxy_sh

rankDynamic :: DynamicTensor target -> Int
rankDynamic (DynamicRanked @_ @n _) = valueOf @n
rankDynamic (DynamicShaped @_ @sh _) = sNatValue $ shsRank $ knownShS @sh
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

voidFromSh :: forall r n. (GoodScalar r, KnownNat n)
           => IShR n -> DynamicTensor VoidTensor
voidFromSh sh = voidFromShL @r (toList sh)

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

unreplicate1VoidHVector :: SNat k -> VoidHVector -> VoidHVector
unreplicate1VoidHVector k = V.map (unreplicate1VoidTensor k)

unreplicate1VoidTensor :: SNat k -> DynamicTensor VoidTensor
                       -> DynamicTensor VoidTensor
unreplicate1VoidTensor snat u = case u of
  DynamicRankedDummy @r @sh' p1 _ -> case knownShS @sh' of
    (:$$) @_ @sh snat' sh' -> withKnownShS sh' $
                              assert (isJust $ geq snat snat')
                              $ DynamicRankedDummy @r @sh p1 Proxy
    _ -> error "unreplicate1VoidTensor: impossible shape"
  DynamicShapedDummy @r @sh' p1 _ -> case knownShS @sh' of
    (:$$) @_ @sh snat' sh' -> withKnownShS sh' $
                              assert (isJust $ geq snat snat')
                              $ DynamicShapedDummy @r @sh p1 Proxy
    _ -> error "unreplicate1VoidTensor: impossible shape"

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
    _ :$: _ -> DynamicRanked $ rindex t (i :.: ZIR)
  DynamicShaped t -> case sshape t of
    ZSS -> error "index1Dynamic: rank 0"
    (:$$) SNat tl | Dict <- shsKnownShS tl ->
      DynamicShaped $ sindex t (i :.$ ZIS)
  DynamicRankedDummy @r @sh p1 _ -> case knownShS @sh of
    ZSS -> error "index1Dynamic: rank 0"
    (:$$) @_ @sh2 _ tl | Dict <- shsKnownShS tl ->
                         DynamicRankedDummy @r @sh2 p1 Proxy
  DynamicShapedDummy @r @sh p1 _ -> case knownShS @sh of
    ZSS -> error "index1Dynamic: rank 0"
    (:$$) @_ @sh2 _ tl | Dict <- shsKnownShS tl ->
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
