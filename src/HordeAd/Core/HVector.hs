{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
-- | The product (heterogeneous list) object for tensors.
--
-- This is used as a representation of the domains of objective functions
-- that become the codomains of the reverse derivative functions
-- and also to hangle multiple arguments and results of fold-like operations.
module HordeAd.Core.HVector
  ( -- * Fynamic tensors and heterogeneous tensor collections
    DynamicTensor(..), CRanked, CShaped
  , HVector, HVectorPseudoTensor(..)
  , VoidTensor, absurdTensor, VoidHVector, DynamicScalar(..)
  , scalarDynamic, shapeDynamicVoid, shapeDynamicF, rankDynamic
  , isDynamicRanked, isDynamicDummy
  , voidFromVar, voidFromVars, voidFromShL, voidFromSh, voidFromShS
  , voidFromDynamicF, replicate1VoidHVector
    -- * ADShare definition
  , AstVarId, intToAstVarId, AstDynamicVarName(..), dynamicVarNameToAstVarId
  , AstBindingsCase(..), AstBindingsD, ADShareD
  , emptyADShare, insertADShare, mergeADShare, subtractADShare
  , flattenADShare, assocsADShare, varInADShareF, nullADShare
  ) where

import Prelude

import           Control.DeepSeq (NFData (..))
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Constraint, Type)
import           Data.List (foldl')
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat)
import           System.IO.Unsafe (unsafePerformIO)
import           Type.Reflection (Typeable, typeRep)

import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances ()
import HordeAd.Util.SizedIndex

-- * Type definitions for dynamic tensors and tensor collections

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
  DynamicShaped :: (GoodScalar r, Sh.Shape sh)
                => ShapedOf ranked r sh -> DynamicTensor ranked
  DynamicRankedDummy :: (GoodScalar r, Sh.Shape sh)
                     => Proxy r -> Proxy sh -> DynamicTensor ranked
  DynamicShapedDummy :: (GoodScalar r, Sh.Shape sh)
                     => Proxy r -> Proxy sh -> DynamicTensor ranked

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
class (forall r30 y30. (Sh.Shape y30, GoodScalar r30) => c (shaped r30 y30))
      => CShaped shaped c where
instance
      (forall r30 y30. (Sh.Shape y30, GoodScalar r30) => c (shaped r30 y30))
      => CShaped shaped c where

-- This is a heterogeneous vector, used for our tuples that need to have
-- the same type regardless of their arity and component types,
-- to be represented by terms with sane typing, to be taken as arguments
-- of functions that operate on all such tuples, etc.
--
-- Data invariant: the vector is non-empty.
--
-- When r is Ast, this is used for hVector composed of variables only,
-- to adapt them into more complex types and back again. This is not used
-- for vectors of large terms, since they'd share values, so we'd need
-- AstHVectorLet, but these would make adapting the vector costly.
-- HVectorOf is used for that and the only reasons HVectorOf exists
-- is to prevent mixing up the two (and complicating the definition
-- below with errors in the AstHVectorLet case).
type HVector (ranked :: RankedTensorType) =
  Data.Vector.Vector (DynamicTensor ranked)

type role HVectorPseudoTensor nominal phantom phantom
type HVectorPseudoTensor :: RankedTensorType -> TensorType ()
newtype HVectorPseudoTensor ranked r y =
  HVectorPseudoTensor {unHVectorPseudoTensor :: HVectorOf ranked}

type instance RankedOf (HVectorPseudoTensor ranked) = ranked

type instance ShapedOf (HVectorPseudoTensor ranked) = ShapedOf ranked

type role VoidTensor nominal nominal
data VoidTensor :: TensorType ty

absurdTensor :: VoidTensor r y -> a
absurdTensor = \case

instance Show (VoidTensor t u) where
  showsPrec _d = absurdTensor

type instance RankedOf VoidTensor = VoidTensor

type instance ShapedOf VoidTensor = VoidTensor

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

shapeDynamicVoid :: DynamicTensor VoidTensor -> [Int]
shapeDynamicVoid  = shapeDynamicF absurdTensor

shapeDynamicF :: (forall r n. (GoodScalar r, KnownNat n) => ranked r n -> [Int])
              -> DynamicTensor ranked -> [Int]
shapeDynamicF f (DynamicRanked t) = f t
shapeDynamicF _ (DynamicShaped @_ @sh _) = Sh.shapeT @sh
shapeDynamicF _ (DynamicRankedDummy _ proxy_sh) = Sh.shapeP proxy_sh
shapeDynamicF _ (DynamicShapedDummy _ proxy_sh) = Sh.shapeP proxy_sh

rankDynamic :: DynamicTensor ranked -> Int
rankDynamic (DynamicRanked @_ @n _) = valueOf @n
rankDynamic (DynamicShaped @_ @sh _) = length $ Sh.shapeT @sh
rankDynamic (DynamicRankedDummy _ proxy_sh) = length $ Sh.shapeP proxy_sh
rankDynamic (DynamicShapedDummy _ proxy_sh) = length $ Sh.shapeP proxy_sh

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

voidFromVar :: AstDynamicVarName -> DynamicTensor VoidTensor
voidFromVar (AstDynamicVarName @ty @rD @shD _) =
  case testEquality (typeRep @ty) (typeRep @Nat) of
    Just Refl -> DynamicRankedDummy @rD @shD Proxy Proxy
    _ -> DynamicShapedDummy @rD @shD Proxy Proxy

voidFromVars :: [AstDynamicVarName] -> VoidHVector
voidFromVars = V.fromList . map voidFromVar

voidFromShL :: forall r. GoodScalar r
            => [Int] -> DynamicTensor VoidTensor
voidFromShL sh = Sh.withShapeP sh $ \proxySh ->
                   DynamicRankedDummy (Proxy @r) proxySh

voidFromSh :: forall r n. GoodScalar r
           => ShapeInt n -> DynamicTensor VoidTensor
voidFromSh sh = voidFromShL @r (shapeToList sh)

voidFromShS :: forall r sh. (GoodScalar r, Sh.Shape sh)
            => DynamicTensor VoidTensor
voidFromShS = DynamicShapedDummy @r @sh Proxy Proxy

voidFromDynamicF
  :: forall ranked.
     (forall r n. (GoodScalar r, KnownNat n) => ranked r n -> [Int])
  -> DynamicTensor ranked -> DynamicTensor VoidTensor
voidFromDynamicF f (DynamicRanked @r2 @n2 t) =
  let sh = f t
  in Sh.withShapeP sh $ \(Proxy @sh2) ->
    DynamicRankedDummy @r2 @sh2 Proxy Proxy
voidFromDynamicF _ (DynamicShaped @r2 @sh2 _) =
  DynamicShapedDummy @r2 @sh2 Proxy Proxy
voidFromDynamicF _ (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
voidFromDynamicF _ (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2

replicate1VoidHVector :: forall k. KnownNat k
                      => Proxy k -> VoidHVector -> VoidHVector
replicate1VoidHVector i u = V.map (replicate1VoidTensor i) u

replicate1VoidTensor :: forall k. KnownNat k
                     => Proxy k -> DynamicTensor VoidTensor
                     -> DynamicTensor VoidTensor
replicate1VoidTensor _i u = case u of
  DynamicRankedDummy @r @sh p1 _ -> DynamicRankedDummy @r @(k ': sh) p1 Proxy
  DynamicShapedDummy @r @sh p1 _ -> DynamicShapedDummy @r @(k ': sh) p1 Proxy


-- * ADShare definition

-- We avoid adding a phantom type denoting the tensor functor,
-- because it can't be easily compared (even fully applies) and so the phantom
-- is useless. We don't add the underlying scalar nor the rank/shape,
-- because some collections differ in those too, e.g., HVector,
-- e.g. in AstLetHVectorS. We don't add a phantom span, because
-- carrying around type constructors that need to be applied to span
-- complicates the system greatly for moderate type safety gain
-- and also such a high number of ID types induces many conversions.
newtype AstVarId = AstVarId Int
 deriving (Eq, Ord, Show, Enum)

intToAstVarId :: Int -> AstVarId
intToAstVarId = AstVarId

-- This can't be replaced by AstVarId. because in some places it's used
-- to record the type, scalar and shape of arguments in a HVector.
--
-- A lot of the variables are existential, but there's no nesting,
-- so no special care about picking specializations at runtime is needed.
data AstDynamicVarName where
  AstDynamicVarName :: forall (ty :: Type) r sh.
                       (Typeable ty, GoodScalar r, Sh.Shape sh)
                    => AstVarId -> AstDynamicVarName
deriving instance Show AstDynamicVarName

dynamicVarNameToAstVarId :: AstDynamicVarName -> AstVarId
dynamicVarNameToAstVarId (AstDynamicVarName varId) = varId

type role AstBindingsCase nominal
data AstBindingsCase ranked =
    AstBindingsSimple (DynamicTensor ranked)
  | AstBindingsHVector [AstDynamicVarName] (HVectorOf ranked)
deriving instance ( Show (HVectorOf ranked)
                  , CRanked ranked Show, CShaped (ShapedOf ranked) Show )
                  => Show (AstBindingsCase ranked)

type AstBindingsD (ranked :: RankedTensorType) =
  [(AstVarId, AstBindingsCase ranked)]

unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshId :: IO Int
{-# INLINE unsafeGetFreshId #-}
unsafeGetFreshId = atomicAddCounter_ unsafeGlobalCounter 1

-- Data invariant: the list is reverse-sorted wrt keys.
-- This permits not inspecting too long a prefix of the list, usually,
-- which is crucial for performance. The strictness is crucial for correctness
-- in the presence of impurity for generating fresh variables.
-- The first integer field permits something akin to pointer equality
-- but with less false negatives, because it's stable.
--
-- The r variable is existential, but operations that depends on it instance
-- are rarely called and relatively cheap, so no picking specializations
-- at runtime is needed.
type role ADShareD nominal
type ADShareD :: RankedTensorType -> Type
data ADShareD ranked =
    ADShareNil
  | ADShareCons Int AstVarId (AstBindingsCase ranked) (ADShareD ranked)
deriving instance ( Show (HVectorOf ranked)
                  , CRanked ranked Show, CShaped (ShapedOf ranked) Show )
                  => Show (ADShareD ranked)

emptyADShare :: ADShareD d
emptyADShare = ADShareNil

insertADShare :: forall d.
                 AstVarId -> AstBindingsCase d -> ADShareD d -> ADShareD d
insertADShare !key !t !s =
  -- The Maybe over-engineering ensures that we never refresh an id
  -- unnecessarily. In theory, when merging alternating equal lists
  -- with different ids, this improves runtime from quadratic to linear,
  -- but we apparently don't have such tests or they are too small,
  -- so this causes a couple percent overhead instead.
  let insertAD :: ADShareD d -> Maybe (ADShareD d)
      insertAD ADShareNil =
        Just $ ADShareCons (- fromEnum key) key t ADShareNil
      insertAD l2@(ADShareCons _id2 key2 t2 rest2) =
        case compare key key2 of
          EQ -> Nothing
                  -- the lists only ever grow and only in fresh/unique way,
                  -- so identical key means identical payload
          LT -> case insertAD rest2 of
            Nothing -> Nothing
            Just l3 -> Just $ freshInsertADShare key2 t2 l3
          GT -> Just $ freshInsertADShare key t l2
  in fromMaybe s (insertAD s)

freshInsertADShare :: AstVarId -> AstBindingsCase d -> ADShareD d -> ADShareD d
{-# NOINLINE freshInsertADShare #-}
freshInsertADShare !key !t !s = unsafePerformIO $ do
  id0 <- unsafeGetFreshId
  return $! ADShareCons id0 key t s

mergeADShare :: ADShareD d -> ADShareD d -> ADShareD d
mergeADShare !s1 !s2 =
  let mergeAD :: ADShareD d -> ADShareD d -> Maybe (ADShareD d)
      mergeAD ADShareNil ADShareNil = Nothing
      mergeAD l ADShareNil = Just l
      mergeAD ADShareNil l = Just l
      mergeAD l1@(ADShareCons id1 key1 t1 rest1)
              l2@(ADShareCons id2 key2 t2 rest2) =
        if id1 == id2
        then -- This assert is quadratic, so can only be enabled when debugging:
             -- assert (_lengthADShare l1 == _lengthADShare l2) $
             Nothing
               -- the lists only ever grow and only in fresh/unique way,
               -- so an identical id means the rest is the same
        else case compare key1 key2 of
          EQ -> case mergeAD rest1 rest2 of
             Nothing -> Nothing
             Just l3 -> Just $ freshInsertADShare key2 t2 l3
          LT -> case mergeAD l1 rest2 of
             Nothing -> Just l2
             Just l3 -> Just $ freshInsertADShare key2 t2 l3
          GT -> case mergeAD rest1 l2 of
             Nothing -> Just l1
             Just l3 -> Just $ freshInsertADShare key1 t1 l3
  in fromMaybe s1 (mergeAD s1 s2)

-- The result type is not as expected. The result is as if assocsADShare
-- was applied to the expected one.
subtractADShare :: ADShareD d -> ADShareD d -> AstBindingsD d
{-# INLINE subtractADShare #-}  -- help list fusion
subtractADShare !s1 !s2 =
  let subAD :: ADShareD d -> ADShareD d -> AstBindingsD d
      subAD !l ADShareNil = assocsADShare l
      subAD ADShareNil _ = []
      subAD l1@(ADShareCons id1 key1 t1 rest1)
            l2@(ADShareCons id2 key2 _ rest2) =
        if id1 == id2
        then []  -- the lists only ever grow and only in fresh/unique way,
                 -- so an identical id means the rest is the same
        else case compare key1 key2 of
          EQ -> subAD rest1 rest2
          LT -> subAD l1 rest2
          GT -> (key1, t1) : subAD rest1 l2
  in subAD s1 s2

-- TODO: rename to concat? make it a monoid?
flattenADShare :: [ADShareD d] -> ADShareD d
flattenADShare = foldl' mergeADShare emptyADShare

assocsADShare :: ADShareD d -> AstBindingsD d
{-# INLINE assocsADShare #-}  -- help list fusion
assocsADShare ADShareNil = []
assocsADShare (ADShareCons _ key t rest) =
  (key, t) : assocsADShare rest

_lengthADShare :: Int -> ADShareD d -> Int
_lengthADShare acc ADShareNil = acc
_lengthADShare acc (ADShareCons _ _ _ rest) = _lengthADShare (acc + 1) rest

varInADShareF :: (AstVarId -> DynamicTensor d -> Bool)
                -> (AstVarId -> HVectorOf d -> Bool)
                -> AstVarId -> ADShareD d
                -> Bool
{-# INLINE varInADShareF #-}
varInADShareF _ _ _ ADShareNil = False
varInADShareF varInAstDynamic varInAstHVector var (ADShareCons _ _ d rest) =
  varInAstBindingsCase varInAstDynamic varInAstHVector var d
  || varInADShareF varInAstDynamic varInAstHVector var rest
    -- TODO: for good Core, probably a local recursive 'go' is needed

varInAstBindingsCase :: (AstVarId -> DynamicTensor d -> Bool)
                     -> (AstVarId -> HVectorOf d -> Bool)
                     -> AstVarId -> AstBindingsCase d
                     -> Bool
{-# INLINE varInAstBindingsCase #-}
varInAstBindingsCase varInAstDynamic _varInAstHVector var
                     (AstBindingsSimple t) = varInAstDynamic var t
varInAstBindingsCase _varInAstDynamic varInAstHVector var
                     (AstBindingsHVector _ t) = varInAstHVector var t

nullADShare :: ADShareD d -> Bool
{-# INLINE nullADShare #-}
nullADShare ADShareNil = True
nullADShare ADShareCons{} = False
