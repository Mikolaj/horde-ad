{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The product (heterogeneous list) object for tensors.
--
-- This is used as a representation of the domains of objective functions
-- that become the codomains of the reverse derivative functions
-- and also to hangle multiple arguments and results of fold-like operations.
module HordeAd.Core.HVector
  ( HVectorOf, HVectorPseudoTensor(..)
  , InterpretationTarget, InterpretationTargetN(..), Cheese2(..), ConcreteTarget
  , InterpretationTargetD(..), InterpretationTargetM(..)
  , TensorKindFull(..), lemTensorKindOfF, buildTensorKindFull
  , DynamicTensor(..)
  , CRanked, CShaped, CHFun, CHFun2, CInterpretationTargetProduct
  , HVector
  , VoidTensor, absurdTensor, VoidHVector, DynamicScalar(..)
  , scalarDynamic, shapeVoidDynamic, shapeVoidHVector, shapeDynamicF
  , rankDynamic, isDynamicRanked, isDynamicDummy
  , voidFromShL, voidFromSh, voidFromShS
  , voidFromDynamicF, replicate1VoidHVector, index1HVectorF, replicate1HVectorF
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Data.Array.Internal (valueOf)
import Data.Kind (Constraint, Type)
import Data.Maybe (isJust)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (testEquality)
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, type (+))
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape qualified as X
import Data.Array.Mixed.Types qualified as X
import Data.Array.Nested (ShR (..))

import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances ()
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

type HVectorOf :: RankedTensorType -> Type
type family HVectorOf f = result | result -> f

type role HVectorPseudoTensor nominal phantom phantom
type HVectorPseudoTensor :: RankedTensorType -> TensorType ()
newtype HVectorPseudoTensor ranked r y =
  HVectorPseudoTensor {unHVectorPseudoTensor :: HVectorOf ranked}

deriving instance Show (HVectorOf ranked)
                  => Show (HVectorPseudoTensor ranked r y)

type instance RankedOf (HVectorPseudoTensor ranked) = ranked

type family InterpretationTarget (ranked :: RankedTensorType)
                                 (y :: TensorKindType)
  = result | result -> ranked y

type instance InterpretationTarget ranked (TKR r n) = ranked r n
type instance InterpretationTarget ranked (TKS r sh) = ShapedOf ranked r sh
-- The TKProduct case is defined separately for each ranked argument.
type instance InterpretationTarget ranked TKUntyped =
  HVectorPseudoTensor ranked Float '()
    -- HVectorPseudoTensor instead of HVectorOf required for injectivity

-- TODO: can also InterpretationTargetD be replaced by cheese?
-- This type lets us work around the woes with defining Show
-- for the InterpretationTarget type family. It gives us a concrete thing
-- to attach a Show instance to.
type role InterpretationTargetN nominal nominal
newtype InterpretationTargetN ranked y = InterpretationTargetN (InterpretationTarget ranked y)

instance ( CRanked ranked Show, CShaped (ShapedOf ranked) Show
         , Show (HVectorOf ranked), CInterpretationTargetProduct ranked Show
         , TensorKind y )
         => Show (InterpretationTargetN ranked y) where
  showsPrec d (InterpretationTargetN t) = case stensorKind @y of
    STKR{} -> showsPrec d t
    STKS{} -> showsPrec d t
    STKProduct{} -> showsPrec d (Cheese2 t)
    STKUntyped -> showsPrec d t

type role Cheese2 nominal nominal nominal
newtype Cheese2 ranked x y = Cheese2 (InterpretationTarget ranked (TKProduct x y))

-- This is concrete only in the outermost layer.
type family ConcreteTarget ranked y = result | result -> ranked y where
  ConcreteTarget ranked (TKR r n) = ranked r n
  ConcreteTarget ranked (TKS r sh) = ShapedOf ranked r sh
  ConcreteTarget ranked (TKProduct x z) =
    (InterpretationTarget ranked x, InterpretationTarget ranked z)
  ConcreteTarget ranked TKUntyped = HVector ranked

-- Needed because `InterpretationTarget` can't be partially applied.
type role InterpretationTargetD nominal nominal
data InterpretationTargetD ranked y where
  DTKR :: (GoodScalar r, KnownNat n)
       => InterpretationTarget ranked (TKR r n)
       -> InterpretationTargetD ranked (TKR r n)
  DTKS :: (GoodScalar r, KnownShS sh)
       => InterpretationTarget ranked (TKS r sh)
       -> InterpretationTargetD ranked (TKS r sh)
  DTKProduct :: forall x z ranked. (TensorKind x, TensorKind z)
             => InterpretationTarget ranked (TKProduct x z)
             -> InterpretationTargetD ranked (TKProduct x z)
  DTKUntyped :: InterpretationTarget ranked TKUntyped
             -> InterpretationTargetD ranked TKUntyped

type role InterpretationTargetM nominal nominal
data InterpretationTargetM ranked y where
  MTKR :: (GoodScalar r, KnownNat n)
       => InterpretationTarget ranked (TKR r n)
       -> InterpretationTargetM ranked (TKR r n)
  MTKS :: (GoodScalar r, KnownShS sh)
       => InterpretationTarget ranked (TKS r sh)
       -> InterpretationTargetM ranked (TKS r sh)
  MTKProduct :: forall x z ranked. (TensorKind x, TensorKind z)
             => InterpretationTarget ranked (TKProduct x z)
             -> InterpretationTargetM ranked (TKProduct x z)
  MTKUntyped :: InterpretationTarget ranked TKUntyped
             -> InterpretationTargetM ranked TKUntyped
  MTKRDummy :: (GoodScalar r, KnownShS sh)
            => InterpretationTargetM ranked (TKR r (X.Rank sh))
  MTKSDummy  :: (GoodScalar r, KnownShS sh)
             => InterpretationTargetM ranked (TKS r sh)
  MTKProductDummy :: forall x z ranked. (TensorKind x, TensorKind z)
                  => InterpretationTargetM ranked (TKProduct x z)

-- TODO: the constraints should not be necessary
type role TensorKindFull nominal
data TensorKindFull y where
  FTKR :: (GoodScalar r, KnownNat n) => ShR n Int -> TensorKindFull (TKR r n)
  FTKS :: (GoodScalar r, KnownShS sh) => TensorKindFull (TKS r sh)
  FTKProduct :: (TensorKind y, TensorKind z)
             => TensorKindFull y -> TensorKindFull z
             -> TensorKindFull (TKProduct y z)
  FTKUntyped :: VoidHVector -> TensorKindFull TKUntyped

deriving instance Show (TensorKindFull y)
deriving instance Eq (TensorKindFull y)

lemTensorKindOfF :: TensorKindFull y -> Dict TensorKind y
lemTensorKindOfF = \case
  FTKR{} -> Dict
  FTKS -> Dict
  FTKProduct stk1 stk2 | Dict <- lemTensorKindOfF stk1
                       , Dict <- lemTensorKindOfF stk2 -> Dict
  FTKUntyped{} -> Dict

buildTensorKindFull :: SNat k -> TensorKindFull y
                    -> TensorKindFull (BuildTensorKind k y)
buildTensorKindFull snat@SNat = \case
  FTKR sh -> FTKR $ sNatValue snat :$: sh
  FTKS -> FTKS
  FTKProduct @z1 @z2 ftk1 ftk2
    | Dict <- lemTensorKindOfBuild snat (stensorKind @z1)
    , Dict <- lemTensorKindOfBuild snat (stensorKind @z2) ->
      FTKProduct (buildTensorKindFull snat ftk1)
                 (buildTensorKindFull snat ftk2)
  FTKUntyped shs -> FTKUntyped $ replicate1VoidHVector snat shs

-- For thousands of tensor parameters, orthotope's dynamic tensors
-- are faster than the datatype below and the special dummy values are faster
-- than ordinary zero values. However, the library has become complex enough
-- that simplicity is the bottlenet, not speed, so we compromise,
-- keeping dummy values, but removing dynamic tensors.
--
-- Warning: r is an existential variable, a proper specialization needs
-- to be picked explicitly at runtime.
type role DynamicTensor nominal
data DynamicTensor (ranked :: RankedTensorType) where
  DynamicRanked :: (GoodScalar r, KnownNat n)
                => ranked r n -> DynamicTensor ranked
  DynamicShaped :: (GoodScalar r, KnownShS sh)
                => ShapedOf ranked r sh -> DynamicTensor ranked
  DynamicRankedDummy :: (GoodScalar r, KnownShS sh)
                     => Proxy r -> Proxy sh -> DynamicTensor ranked
  DynamicShapedDummy :: (GoodScalar r, KnownShS sh)
                     => Proxy r -> Proxy sh -> DynamicTensor ranked

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
  (CRanked ranked Show, CShaped (ShapedOf ranked) Show)
  => Show (DynamicTensor ranked)

instance (CRanked ranked NFData, CShaped (ShapedOf ranked) NFData)
         => NFData (DynamicTensor ranked) where
  rnf (DynamicRanked x) = rnf x
  rnf (DynamicShaped x) = rnf x
  rnf (DynamicRankedDummy{}) = ()
  rnf (DynamicShapedDummy{}) = ()

type CRanked :: RankedTensorType -> (Type -> Constraint) -> Constraint
class (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
      => CRanked ranked c where
instance (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
      => CRanked ranked c where

type CShaped :: ShapedTensorType -> (Type -> Constraint) -> Constraint
class (forall r30 y30. (KnownShS y30, GoodScalar r30) => c (shaped r30 y30))
      => CShaped shaped c where
instance
      (forall r30 y30. (KnownShS y30, GoodScalar r30) => c (shaped r30 y30))
      => CShaped shaped c where

type CHFun :: RankedTensorType -> (Type -> Constraint) -> TensorKindType
           -> Constraint
class (forall x. c (HFunOf ranked x y)) => CHFun ranked c y where
instance
      (forall x. c (HFunOf ranked x y)) => CHFun ranked c y where

type CHFun2 :: RankedTensorType -> (Type -> Constraint)
            -> Constraint
class (forall x y. c (HFunOf ranked x y)) => CHFun2 ranked c where
instance
      (forall x y. c (HFunOf ranked x y)) => CHFun2 ranked c where

type CInterpretationTargetProduct :: RankedTensorType -> (Type -> Constraint)
                                  -> Constraint
class (forall x y. (TensorKind x, TensorKind y) => c (Cheese2 ranked x y))
       => CInterpretationTargetProduct ranked c where
instance
      (forall x y. (TensorKind x, TensorKind y) => c (Cheese2 ranked x y))
       => CInterpretationTargetProduct ranked c where

-- | This is a heterogeneous vector, used as represenation of tuples
-- of tensors that need to have the same Haskell type regardless
-- of their arity and component types/shapes. This is a struct of arrays
-- representation, both as seen through its operations API and internally
-- and we convert to this representation ASAP whenever computations
-- result in another representation. Such tuples are also expressed via
-- an AST type `AstHVector` with a similar API. Both are used for arguments
-- and the result in the internal representation of lambdas (closed functions)
-- as used in fold-like and rev-like operations in the main library API.
-- The type family `HVectorOf` assigns this or the AST implementation
-- based on the nature (symbolic or not) of the tensor type given to it.
type HVector (ranked :: RankedTensorType) =
  Data.Vector.Vector (DynamicTensor ranked)
    -- When @ranked@ is terms, `HVector AstHVector` is a mixed half-symbolic
    -- representation, usually used for vectors composed of variables only,
    -- to adapt them into more complex types and back again.
    -- This representation is not used for vectors of large terms,
    -- since they'd share values, so AstHVector is used there instead.
    -- Operations such as AstHVectorLet serve to convert between
    -- the two, preserving sharing whenever possible. The only reason
    -- HVectorOf exists is to express and preserve sharing, which is
    -- not possible with `HVector AstHVector` alone.

type role VoidTensor nominal nominal
data VoidTensor :: TensorType ty

absurdTensor :: VoidTensor r y -> a
absurdTensor = \case

instance Show (VoidTensor t u) where
  showsPrec _d = absurdTensor

type instance RankedOf VoidTensor = VoidTensor

type instance ShapedOf VoidTensor = VoidTensor

-- This is a tuple of void tensor, which incidentally makes this more like
-- a unit type (the only values beeing the dummy DynamicTensor constructors),
-- where the only values carry only the shapes/ranks and the scalar type.
type VoidHVector = HVector VoidTensor

type role DynamicScalar representational
data DynamicScalar (ranked :: RankedTensorType) where
  DynamicScalar :: GoodScalar r
                => Proxy r -> DynamicScalar ranked

instance Show (DynamicScalar ranked) where
  showsPrec d (DynamicScalar (Proxy @t)) =
    showsPrec d (typeRep @t)  -- abuse for better error messages

scalarDynamic :: DynamicTensor ranked -> DynamicScalar ranked
scalarDynamic (DynamicRanked @r2 _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicShaped @r2 _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicRankedDummy @r2 _ _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicShapedDummy @r2 _ _) = DynamicScalar @r2 Proxy

shapeVoidDynamic :: DynamicTensor VoidTensor -> [Int]
shapeVoidDynamic  = shapeDynamicF absurdTensor

shapeVoidHVector :: VoidHVector -> [[Int]]
shapeVoidHVector = V.toList . V.map shapeVoidDynamic

shapeDynamicF :: (forall r n. (GoodScalar r, KnownNat n) => ranked r n -> [Int])
              -> DynamicTensor ranked -> [Int]
{-# INLINE shapeDynamicF #-}
shapeDynamicF f (DynamicRanked t) = f t
shapeDynamicF _ (DynamicShaped @_ @sh _) = shapeT @sh
shapeDynamicF _ (DynamicRankedDummy _ proxy_sh) = shapeP proxy_sh
shapeDynamicF _ (DynamicShapedDummy _ proxy_sh) = shapeP proxy_sh

rankDynamic :: DynamicTensor ranked -> Int
rankDynamic (DynamicRanked @_ @n _) = valueOf @n
rankDynamic (DynamicShaped @_ @sh _) = length $ shapeT @sh
rankDynamic (DynamicRankedDummy _ proxy_sh) = length $ shapeP proxy_sh
rankDynamic (DynamicShapedDummy _ proxy_sh) = length $ shapeP proxy_sh

isDynamicRanked :: DynamicTensor ranked -> Bool
isDynamicRanked DynamicRanked{} = True
isDynamicRanked DynamicShaped{} = False
isDynamicRanked DynamicRankedDummy{} = True
isDynamicRanked DynamicShapedDummy{} = False

isDynamicDummy :: DynamicTensor ranked -> Bool
isDynamicDummy DynamicRanked{} = False
isDynamicDummy DynamicShaped{} = False
isDynamicDummy DynamicRankedDummy{} = True
isDynamicDummy DynamicShapedDummy{} = True

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
  :: forall ranked.
     (forall r n. (GoodScalar r, KnownNat n) => ranked r n -> [Int])
  -> DynamicTensor ranked -> DynamicTensor VoidTensor
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

index1HVectorF :: ( shaped ~ ShapedOf ranked
                  , RankedOf (PrimalOf shaped) ~ RankedOf (PrimalOf ranked) )
               => (forall r n. (GoodScalar r, KnownNat n)
                   => ranked r n -> IShR n)
               -> (forall sh r. (GoodScalar r, KnownShS sh)
                   => shaped r sh -> ShS sh)
               -> (forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
                   => ranked r (m + n) -> IndexOf ranked m -> ranked r n)
               -> (forall r sh1 sh2.
                   ( GoodScalar r, KnownShS sh1, KnownShS sh2
                   , KnownShS (sh1 X.++ sh2) )
                   => shaped r (sh1 X.++ sh2) -> ShapedList.IndexSh shaped sh1
                   -> shaped r sh2)
               -> HVector ranked -> IntOf ranked -> HVector ranked
{-# INLINE index1HVectorF #-}
index1HVectorF rshape sshape rindex sindex u i =
  V.map (flip (index1DynamicF rshape sshape rindex sindex) i) u

index1DynamicF :: ( shaped ~ ShapedOf ranked
                  , RankedOf (PrimalOf shaped) ~ RankedOf (PrimalOf ranked) )
               => (forall r n. (GoodScalar r, KnownNat n)
                   => ranked r n -> IShR n)
               -> (forall sh r. (GoodScalar r, KnownShS sh)
                   => shaped r sh -> ShS sh)
               -> (forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
                   => ranked r (m + n) -> IndexOf ranked m -> ranked r n)
               -> (forall r sh1 sh2.
                   ( GoodScalar r, KnownShS sh1, KnownShS sh2
                   , KnownShS (sh1 X.++ sh2) )
                   => shaped r (sh1 X.++ sh2) -> ShapedList.IndexSh shaped sh1
                   -> shaped r sh2)
               -> DynamicTensor ranked -> IntOf ranked -> DynamicTensor ranked
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

replicate1HVectorF :: shaped ~ ShapedOf ranked
                   => (forall r n. (GoodScalar r, KnownNat n)
                       => Int -> ranked r n -> ranked r (1 + n))
                   -> (forall n sh r. (KnownNat n, KnownShS sh, GoodScalar r)
                       => shaped r sh -> shaped r (n ': sh))
                   -> SNat k -> HVector ranked -> HVector ranked
{-# INLINE replicate1HVectorF #-}
replicate1HVectorF rreplicate sreplicate k =
  V.map (replicate1DynamicF rreplicate sreplicate k)

replicate1DynamicF :: shaped ~ ShapedOf ranked
                   => (forall r n. (GoodScalar r, KnownNat n)
                       => Int -> ranked r n -> ranked r (1 + n))
                   -> (forall n sh r. (KnownNat n, KnownShS sh, GoodScalar r)
                       => shaped r sh -> shaped r (n ': sh))
                   -> SNat k -> DynamicTensor ranked -> DynamicTensor ranked
{-# INLINE replicate1DynamicF #-}
replicate1DynamicF rreplicate sreplicate k@(SNat @k) u = case u of
  DynamicRanked t -> DynamicRanked $ rreplicate (sNatValue k) t
  DynamicShaped t -> DynamicShaped $ sreplicate @k t
  DynamicRankedDummy @r @sh p1 _ -> DynamicRankedDummy @r @(k ': sh) p1 Proxy
  DynamicShapedDummy @r @sh p1 _ -> DynamicShapedDummy @r @(k ': sh) p1 Proxy
