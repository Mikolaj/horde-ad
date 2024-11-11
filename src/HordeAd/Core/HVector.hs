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
  ( RepD(..)
  , TensorKindFull(..), lemTensorKindOfF, buildTensorKindFull
  , aDTensorKind
  , DynamicTensor(..)
  , CRanked
  , HVector
  , VoidTensor, absurdTensor, VoidHVector, DynamicScalar(..)
  , scalarDynamic, shapeVoidDynamic, shapeVoidHVector, shapeDynamicF
  , rankDynamic, isDynamicRanked, voidFromShL, voidFromSh, voidFromShS
  , voidFromDynamicF, replicate1VoidHVector, index1HVectorF, replicate1HVectorF
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
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
import HordeAd.Internal.OrthotopeOrphanInstances (valueOf)
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

type role RepD nominal nominal
data RepD target y where
  DTKScalar :: GoodScalar r
            => target (TKScalar r)
            -> RepD target (TKScalar r)
  DTKR :: (GoodScalar r, KnownNat n)
       => target (TKR r n)
       -> RepD target (TKR r n)
  DTKS :: (GoodScalar r, KnownShS sh)
       => target (TKS r sh)
       -> RepD target (TKS r sh)
  DTKX :: (GoodScalar r, KnownShX sh)
       => target (TKX r sh)
       -> RepD target (TKX r sh)
  DTKProduct :: forall x z target. (TensorKind x, TensorKind z)
             => RepD target x -> RepD target z
             -> RepD target (TKProduct x z)
  DTKUntyped :: HVector target
             -> RepD target TKUntyped

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
data DynamicTensor (target :: Target) where
  DynamicRanked :: (GoodScalar r, KnownNat n)
                => target (TKR r n) -> DynamicTensor target
  DynamicShaped :: (GoodScalar r, KnownShS sh)
                => target (TKS r sh) -> DynamicTensor target
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
  CRanked target Show
  => Show (DynamicTensor target)

instance CRanked target NFData
         => NFData (DynamicTensor target) where
  rnf (DynamicRanked x) = rnf x
  rnf (DynamicShaped x) = rnf x
  rnf (DynamicRankedDummy{}) = ()
  rnf (DynamicShapedDummy{}) = ()

type CRanked :: Target -> (Type -> Constraint) -> Constraint
class (forall y20. TensorKind y20 => c (target y20))
      => CRanked target c where
instance
      (forall y20. TensorKind y20 => c (target y20))
      => CRanked target c where

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

shapeDynamicF :: (forall r n. (GoodScalar r, KnownNat n) => target (TKR r n) -> [Int])
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
     (forall r n. (GoodScalar r, KnownNat n) => target (TKR r n) -> [Int])
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
                   => target (TKR r n) -> IShR n)
               -> (forall sh r. (GoodScalar r, KnownShS sh)
                   => target (TKS r sh) -> ShS sh)
               -> (forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
                   => target (TKR r (m + n)) -> IndexOf target m -> target (TKR r n))
               -> (forall r sh1 sh2.
                   ( GoodScalar r, KnownShS sh1, KnownShS sh2
                   , KnownShS (sh1 ++ sh2) )
                   => target (TKS r (sh1 ++ sh2)) -> ShapedList.IndexSh target sh1
                   -> target (TKS r sh2))
               -> HVector target -> IntOf target -> HVector target
{-# INLINE index1HVectorF #-}
index1HVectorF rshape sshape rindex sindex u i =
  V.map (flip (index1DynamicF rshape sshape rindex sindex) i) u

index1DynamicF :: (forall r n. (GoodScalar r, KnownNat n)
                   => target (TKR r n) -> IShR n)
               -> (forall sh r. (GoodScalar r, KnownShS sh)
                   => target (TKS r sh) -> ShS sh)
               -> (forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
                   => target (TKR r (m + n)) -> IndexOf target m -> target (TKR r n))
               -> (forall r sh1 sh2.
                   ( GoodScalar r, KnownShS sh1, KnownShS sh2
                   , KnownShS (sh1 ++ sh2) )
                   => target (TKS r (sh1 ++ sh2)) -> ShapedList.IndexSh target sh1
                   -> target (TKS r sh2))
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
                       => Int -> target (TKR r n) -> target (TKR r (1 + n)))
                   -> (forall n sh r. (KnownNat n, KnownShS sh, GoodScalar r)
                       => target (TKS r sh) -> target (TKS r (n ': sh)))
                   -> SNat k -> HVector target -> HVector target
{-# INLINE replicate1HVectorF #-}
replicate1HVectorF rreplicate sreplicate k =
  V.map (replicate1DynamicF rreplicate sreplicate k)

replicate1DynamicF :: (forall r n. (GoodScalar r, KnownNat n)
                       => Int -> target (TKR r n) -> target (TKR r (1 + n)))
                   -> (forall n sh r. (KnownNat n, KnownShS sh, GoodScalar r)
                       => target (TKS r sh) -> target (TKS r (n ': sh)))
                   -> SNat k -> DynamicTensor target -> DynamicTensor target
{-# INLINE replicate1DynamicF #-}
replicate1DynamicF rreplicate sreplicate k@(SNat @k) u = case u of
  DynamicRanked t -> DynamicRanked $ rreplicate (sNatValue k) t
  DynamicShaped t -> DynamicShaped $ sreplicate @k t
  DynamicRankedDummy @r @sh p1 _ -> DynamicRankedDummy @r @(k ': sh) p1 Proxy
  DynamicShapedDummy @r @sh p1 _ -> DynamicShapedDummy @r @(k ': sh) p1 Proxy
