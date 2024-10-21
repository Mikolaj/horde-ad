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
  , Rep, RepN(..), RepScalar(..), RepProductN(..)
  , RepShallow, RepDeep, RepD(..)
  , TensorKindFull(..), nullRepDeep, lemTensorKindOfF, buildTensorKindFull
  , aDTensorKind
  , DynamicTensor(..)
  , CRanked, CShaped, CMixed, CMixedSupports, CHFun, CHFun2, CRepProduct
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
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, type (+))
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Shape (IShX, ssxFromShape)
import Data.Array.Nested (KnownShX, SMayNat (..), ShX (..), type (++))
import Data.Array.Nested.Internal.Shape (shrRank)

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

type family Rep (ranked :: RankedTensorType) (y :: TensorKindType)

type instance Rep ranked (TKScalar r) = RepScalar ranked r
type instance Rep ranked (TKR r n) = ranked r n
type instance Rep ranked (TKS r sh) = ShapedOf ranked r sh
type instance Rep ranked (TKX r sh) = MixedOf ranked r sh
-- The TKProduct case is defined separately for each ranked argument.
type instance Rep ranked TKUntyped =
  HVectorPseudoTensor ranked Float '()
    -- HVectorPseudoTensor instead of HVectorOf required for injectivity

-- Needed because `Rep` can't be partially applied.
-- This type also lets us work around the woes with defining Show
-- for the Rep type family. It gives us a concrete thing
-- to attach a Show instance to.
type role RepN nominal nominal
newtype RepN ranked y =
  RepN {unRepN :: Rep ranked y}

type role RepScalar nominal nominal
type RepScalar :: RankedTensorType -> Type -> Type
newtype RepScalar ranked r = RepScalar {unRepScalar :: ranked r 0}

deriving instance Show (ranked r 0) => Show (RepScalar ranked r)

instance ( CRanked ranked Show, CShaped (ShapedOf ranked) Show
         , CMixed (MixedOf ranked) Show
         , Show (HVectorOf ranked), CRepProduct ranked Show
         , TensorKind y )
         => Show (RepN ranked y) where
  showsPrec d (RepN t) = case stensorKind @y of
    STKScalar _ -> showsPrec d t
    STKR STKScalar{} SNat -> showsPrec d t
    STKS STKScalar{} sh -> withKnownShS sh $ showsPrec d t
    STKX STKScalar{} sh -> withKnownShX sh $ showsPrec d t
    STKProduct @y1 @y2 stk1 stk2 | Dict <- lemTensorKindOfS stk1
                                 , Dict <- lemTensorKindOfS stk2 ->
      showsPrec d (RepProductN @ranked @y1 @y2 t)
    STKUntyped -> showsPrec d t
    _ -> error "TODO"

type role RepProductN nominal nominal nominal
newtype RepProductN ranked x y =
  RepProductN {unRepProductN :: Rep ranked (TKProduct x y)}

-- This is concrete only in the outermost layer.
type family RepShallow ranked y where
  RepShallow ranked (TKScalar r) = RepScalar ranked r
  RepShallow ranked (TKR r n) = ranked r n
  RepShallow ranked (TKS r sh) = ShapedOf ranked r sh
  RepShallow ranked (TKX r sh) = MixedOf ranked r sh
  RepShallow ranked (TKProduct x z) =
    (Rep ranked x, Rep ranked z)
  RepShallow ranked TKUntyped = HVector ranked

-- This is concrete throughout.
type family RepDeep ranked y where
  RepDeep ranked (TKScalar r) = RepScalar ranked r
  RepDeep ranked (TKR r n) = ranked r n
  RepDeep ranked (TKS r sh) = ShapedOf ranked r sh
  RepDeep ranked (TKX r sh) = MixedOf ranked r sh
  RepDeep ranked (TKProduct x z) =
    (RepDeep ranked x, RepDeep ranked z)
  RepDeep ranked TKUntyped = HVector ranked

-- A datatype matching RepDeep.
type role RepD nominal nominal
data RepD ranked y where
  DTKScalar :: GoodScalar r
            => Rep ranked (TKScalar r)
            -> RepD ranked (TKScalar r)
  DTKR :: (GoodScalar r, KnownNat n)
       => Rep ranked (TKR r n)
       -> RepD ranked (TKR r n)
  DTKS :: (GoodScalar r, KnownShS sh)
       => Rep ranked (TKS r sh)
       -> RepD ranked (TKS r sh)
  DTKX :: (GoodScalar r, KnownShX sh)
       => Rep ranked (TKX r sh)
       -> RepD ranked (TKX r sh)
  DTKProduct :: forall x z ranked. (TensorKind x, TensorKind z)
             => RepD ranked x -> RepD ranked z
             -> RepD ranked (TKProduct x z)
  DTKUntyped :: HVector ranked
             -> RepD ranked TKUntyped

-- TODO: the constraints should not be necessary if we instead add ShS singleton
-- to FTKS
type role TensorKindFull nominal
data TensorKindFull y where
  FTKScalar :: GoodScalar r => TensorKindFull (TKScalar r)
  FTKR :: GoodScalar r => IShR n -> TensorKindFull (TKR r n)
  FTKS :: GoodScalar r => ShS sh -> TensorKindFull (TKS r sh)
  FTKX :: GoodScalar r => IShX sh -> TensorKindFull (TKX r sh)
  FTKProduct :: TensorKindFull y -> TensorKindFull z
             -> TensorKindFull (TKProduct y z)
  FTKUntyped :: VoidHVector -> TensorKindFull TKUntyped

deriving instance Show (TensorKindFull y)
deriving instance Eq (TensorKindFull y)

nullRepDeep :: forall y ranked. TensorKind y
            => RepDeep ranked y -> Bool
nullRepDeep t = case stensorKind @y of
  STKScalar{} -> False
  STKR{} -> False
  STKS{} -> False
  STKX{} -> False
  STKProduct{} -> False
  STKUntyped -> null t

lemTensorKindOfF :: TensorKindFull y -> Dict TensorKind y
lemTensorKindOfF = \case
  FTKScalar -> Dict
  FTKR sh | SNat <- shrRank sh -> Dict
  FTKS sh -> withKnownShS sh Dict
  FTKX sh -> withKnownShX (ssxFromShape sh) Dict
  FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfF ftk1
                       , Dict <- lemTensorKindOfF ftk2 -> Dict
  FTKUntyped{} -> Dict

buildTensorKindFull :: SNat k -> TensorKindFull y
                    -> TensorKindFull (BuildTensorKind k y)
buildTensorKindFull snat@SNat = \case
  FTKScalar -> FTKR $ sNatValue snat :$: ZSR
  FTKR sh -> FTKR $ sNatValue snat :$: sh
  FTKS sh -> FTKS $ snat :$$ sh
  FTKX sh -> FTKX $ SKnown snat :$% sh
  FTKProduct ftk1 ftk2 ->
      FTKProduct (buildTensorKindFull snat ftk1)
                 (buildTensorKindFull snat ftk2)
  FTKUntyped shs -> FTKUntyped $ replicate1VoidHVector snat shs

aDTensorKind :: TensorKindFull y
             -> TensorKindFull (ADTensorKind y)
aDTensorKind t = case t of
  FTKScalar @r -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: ()) $
           FTKScalar @()
  FTKR @r shr -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: ()) $
           FTKR @() shr
  FTKS @r shs -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: ()) $
           FTKS @() shs
  FTKX @r shx -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: ()) $
           FTKX @() shx
  FTKProduct ftk1 ftk2 ->
    let gtk1 = aDTensorKind ftk1
        gtk2 = aDTensorKind ftk2
    in case (lemTensorKindOfF gtk1, lemTensorKindOfF gtk2) of
      (Dict, Dict) -> FTKProduct gtk1 gtk2
  FTKUntyped{} -> t

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

type CMixed :: MixedTensorType -> (Type -> Constraint) -> Constraint
class (forall r40 y40. (KnownShX y40, GoodScalar r40) => c (mixed r40 y40))
      => CMixed mixed c where
instance
      (forall r40 y40. (KnownShX y40, GoodScalar r40) => c (mixed r40 y40))
      => CMixed mixed c where

type CMixedSupports :: (Type -> Constraint) -> (Type -> Constraint) -> MixedTensorType -> Constraint
class (forall r40 y40. (KnownShX y40, GoodScalar r40)
       => (c1 r40 => c2 (mixed r40 y40)))
      => CMixedSupports c1 c2 mixed where
instance
      (forall r40 y40. (KnownShX y40, GoodScalar r40)
       => (c1 r40 => c2 (mixed r40 y40)))
      => CMixedSupports c1 c2 mixed where

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

type CRepProduct :: RankedTensorType -> (Type -> Constraint)
                                  -> Constraint
class (forall x y. (TensorKind x, TensorKind y) => c (RepProductN ranked x y))
       => CRepProduct ranked c where
instance
      (forall x y. (TensorKind x, TensorKind y) => c (RepProductN ranked x y))
       => CRepProduct ranked c where

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
                   , KnownShS (sh1 ++ sh2) )
                   => shaped r (sh1 ++ sh2) -> ShapedList.IndexSh shaped sh1
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
                   , KnownShS (sh1 ++ sh2) )
                   => shaped r (sh1 ++ sh2) -> ShapedList.IndexSh shaped sh1
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

replicate1HVectorF :: forall ranked shaped  k. shaped ~ ShapedOf ranked
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
