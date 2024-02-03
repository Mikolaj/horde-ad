{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and arithmetic operations on them. This is a part of
-- the mid-level API of the horde-ad library, together with
-- the safely impure "HordeAd.Core.DualClass".
module HordeAd.Core.DualNumber
  ( -- * The main dual number type
    ADVal, dD, pattern D, dDnotShared, constantADVal
    -- * Auxiliary definitions
  , CRankedIP, indexPrimal, fromList, CRankedIPSh, indexPrimalS, fromListS
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
--  , addParameters, dotParameters
    -- * Reverse and forward derivative stages class and instances
  , DerivativeStages (..), UnletGradient (..)
  , crevOnADInputs, crevOnHVector, cfwdOnADInputs, cfwdOnHVector
  , generateDeltaInputs, makeADInputs
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Functor.Const
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, sameNat, type (+))
import           Type.Reflection (typeRep)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.Delta
import HordeAd.Core.DualClass
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (sameShape)
import HordeAd.Util.ShapedList (singletonShaped)
import HordeAd.Util.SizedIndex

-- * The main dual number type

-- | Values that the objective functions operate on when they are being
-- differentiated. The values are, in general, tensors.
-- The first type argument is the functor determining the structure
-- of the tensors (whether ranked, shaped, dynamic, storable, unboxed, etc.).
-- The second argument is the underlying scalar type. The third
-- is the rank or shape of the tensor value.
--
-- The datatype is implemented as dual numbers (hence @D@),
-- where @ADShare@ holds the sharing information if the values are,
-- in fact, AST terms. The @f r z@ value is the primal component,
-- which is the normal, the basic value. The exact type of the dual component
-- is determined by a definition of type family @Dual@ provided elsewhere.
type role ADVal nominal nominal nominal
data ADVal (f :: TensorType ty) (r :: Type) (z :: ty) =
  ADVal ADShare (f r z) (Dual f r z)

pattern D :: ADShare -> f r z -> Dual f r z -> ADVal f r z
pattern D l t u <- ADVal l t u  -- enforces only pattern matching
{-# COMPLETE D #-}

deriving instance (Show (f r z), Show (Dual f r z))
                  => Show (ADVal f r z)

-- | Smart constructor for 'D' of 'ADVal' that additionally records delta
-- expression sharing information (regardless if the basic value
-- of the dual number is an AST term or not).
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: IsPrimal f r z
   => ADShare -> f r z -> Dual f r z -> ADVal f r z
dD !l !a !dual = dDnotShared l a (recordSharing dual)

-- | This a not so smart a constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: ADShare -> f r z -> Dual f r z -> ADVal f r z
dDnotShared = ADVal

constantADVal :: IsPrimal f r z => f r z -> ADVal f r z
constantADVal a = dDnotShared emptyADShare a (dZeroOfShape a)


-- * Assorted instances

type instance SimpleBoolOf (ADVal f) = SimpleBoolOf f

instance EqF f => EqF (ADVal f) where
  D l1 u _ ==. D l2 v _ = (l1 `mergeADShare` l2, snd $ u ==. v)
  D l1 u _ /=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u /=. v)

instance OrdF f => OrdF (ADVal f) where
  D l1 u _ <. D l2 v _ = (l1 `mergeADShare` l2, snd $ u <. v)
  D l1 u _ <=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u <=. v)
  D l1 u _ >. D l2 v _ = (l1 `mergeADShare` l2, snd $ u >. v)
  D l1 u _ >=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u >=. v)

type CRankedIP :: RankedTensorType
               -> (RankedTensorType -> Type -> Nat -> Constraint)
               -> Constraint
class (forall r15 y. (KnownNat y, GoodScalar r15) => c ranked r15 y)
      => CRankedIP ranked c where
instance (forall r15 y. (KnownNat y, GoodScalar r15) => c ranked r15 y)
         => CRankedIP ranked c where

indexPrimal :: ( RankedTensor ranked, IsPrimal ranked r n
               , KnownNat m, KnownNat n, GoodScalar r )
            => ADVal ranked r (m + n) -> IndexOf ranked m
            -> ADVal ranked r n
indexPrimal (D l u u') ix = dD l (rindex u ix) (IndexR u' ix)

fromList :: ( RankedTensor ranked, IsPrimal ranked r (1 + n)
            , KnownNat n, GoodScalar r )
         => [ADVal ranked r n]
         -> ADVal ranked r (1 + n)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (flattenADShare $ map (\(D l _ _) -> l) lu)
     (rfromList $ map (\(D _ u _) -> u) lu)
     (FromListR $ map (\(D _ _ u') -> u') lu)

instance ( RankedTensor ranked, CRankedIP ranked IsPrimal
         , IfF (RankedOf (PrimalOf ranked))
         , Boolean (SimpleBoolOf ranked)
         , SimpleBoolOf (RankedOf (PrimalOf ranked)) ~ SimpleBoolOf ranked )
         => IfF (ADVal ranked) where
  ifF (l1, b) v w =
    let D l2 u u' = indexPrimal (fromList [v, w])
                                (singletonIndex $ ifF (emptyADShare, b) 0 1)
    in dDnotShared (l1 `mergeADShare` l2) u u'

type CRankedIPSh :: ShapedTensorType
                 -> (ShapedTensorType -> Type -> [Nat] -> Constraint)
                 -> Constraint
class (forall r55 y. (GoodScalar r55, Sh.Shape y) => c shaped r55 y)
      => CRankedIPSh shaped c where
instance (forall r55 y. (GoodScalar r55, Sh.Shape y) => c shaped r55 y)
         => CRankedIPSh shaped c where

indexPrimalS :: ( ShapedTensor shaped, IsPrimal shaped r sh2
                , Sh.Shape sh1, Sh.Shape sh2, Sh.Shape (sh1 Sh.++ sh2)
                , GoodScalar r )
             => ADVal shaped r (sh1 Sh.++ sh2) -> IndexSh shaped sh1
             -> ADVal shaped r sh2
indexPrimalS (D l u u') ix = dD l (sindex u ix) (IndexS u' ix)

fromListS :: forall n sh shaped r.
             ( ShapedTensor shaped, IsPrimal shaped r (n ': sh)
             , KnownNat n, Sh.Shape sh, GoodScalar r )
           => [ADVal shaped r sh]
           -> ADVal shaped r (n ': sh)
fromListS lu = assert (length lu == valueOf @n) $
  dD (flattenADShare $ map (\(D l _ _) -> l) lu)
     (sfromList $ map (\(D _ u _) -> u) lu)
     (FromListS $ map (\(D _ _ u') -> u') lu)

instance ( ShapedTensor shaped, CRankedIPSh shaped IsPrimal
         , IfF (RankedOf (PrimalOf shaped))
         , Boolean (SimpleBoolOf shaped)
         , SimpleBoolOf (RankedOf (PrimalOf shaped)) ~ SimpleBoolOf shaped )
         => IfF (ADVal shaped) where
  ifF (l1, b) v w =
    let D l2 u u' = indexPrimalS (fromListS @2 [v, w])
                                 (singletonShaped $ ifF (emptyADShare, b) 0 1)
    in dDnotShared (l1 `mergeADShare` l2) u u'

{- TODO: use for speed-up, e.g,. by checking the type at runtime
instance IfF (ADVal (Flip OR.Array)) where
  ifF (_, b) v w = if b then v else w

instance IfF (ADVal (Flip OS.Array)) where
  ifF (_, b) v w = if b then v else w
-}

type instance RankedOf (ADVal f) = ADVal (RankedOf f)

type instance ShapedOf (ADVal f) = ADVal (ShapedOf f)

type instance HVectorOf (ADVal f) = HVector (ADVal f)

type instance PrimalOf (ADVal f) = f

type instance DualOf (ADVal f) = Product (Clown (Const ADShare)) (Dual f)

instance (GoodScalar r, KnownNat n, RankedTensor (ADVal ranked))
         => IsPrimal (ADVal ranked) r n where
  dZeroOfShape tsh = ZeroR (rshape tsh)
  dScale _ (ZeroR sh) = ZeroR sh
  dScale v u' = ScaleR v u'
  dAdd ZeroR{} w = w
  dAdd v ZeroR{} = v
  dAdd v w = AddR v w
  intOfShape tsh c =
    rconst $ OR.constant (shapeToList $ rshape tsh) (fromIntegral c)
  recordSharingPrimal r l = (l, r)
  recordSharing d = case d of
    ZeroR{} -> d
    InputR{} -> d
    SToR{} -> d
    LetR{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaR d

instance (GoodScalar r, Sh.Shape sh, ShapedTensor (ADVal shaped))
         => IsPrimal (ADVal shaped) r sh where
  dZeroOfShape _tsh = ZeroS
  dScale _ ZeroS = ZeroS
  dScale v u' = ScaleS v u'
  dAdd ZeroS w = w
  dAdd v ZeroS = v
  dAdd v w = AddS v w
  intOfShape _tsh c =  -- this is not needed for OS, but OR needs it
    sconst $ fromIntegral c
  recordSharingPrimal r l = (l, r)
  recordSharing d = case d of
    ZeroS -> d
    InputS{} -> d
    RToS{} -> d
    LetS{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaS d

instance AdaptableHVector (ADVal ranked) (DynamicTensor (ADVal ranked)) where
  type Value (DynamicTensor (ADVal ranked)) = DynamicTensor ranked
  toHVector = V.singleton
  fromHVector _aInit params = V.uncons params


-- * Auxiliary definitions

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: IsPrimal f r z => ADVal f r z -> ADVal f r z
ensureToplevelSharing (D l u u') = dD l u u'

scaleNotShared :: (Num (f r z), IsPrimal f r z)
               => f r z -> ADVal f r z -> ADVal f r z
scaleNotShared !a (D l u u') = dDnotShared l (a * u) (dScale a u')

addNotShared :: (Num (f r z), IsPrimal f r z)
             => ADVal f r z -> ADVal f r z -> ADVal f r z
addNotShared (D l1 u u') (D l2 v v') =
  dDnotShared (l1 `mergeADShare` l2) (u + v) (dAdd u' v')

multNotShared :: (Num (f r z), IsPrimal f r z)
              => ADVal f r z -> ADVal f r z -> ADVal f r z
multNotShared (D l1 u u') (D l2 v v') =
  dDnotShared (l1 `mergeADShare` l2) (u * v) (dAdd (dScale v u') (dScale u v'))
{-
addParameters :: (Numeric r, Num (Vector r), DTensorOf r ~ OD.Array r)
              => HVector r -> HVector r -> HVector r
addParameters (HVector a0 a1) (HVector b0 b1) =
  HVector (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: (Numeric r, DTensorOf r ~ OD.Array r)
              => HVector r -> HVector r -> r
dotParameters (HVector a0 a1) (HVector b0 b1) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1) a1 b1)
-}

crevOnADInputs
  :: forall ty (f :: TensorType ty) r y.
     ( RankedTensor (ADVal (RankedOf f))
     , HVectorTensor (RankedOf f) (ShapedOf f)
     , DualPart f, UnletGradient f, GoodScalar r, HasSingletonDict y)
  => Maybe (f r y)
  -> (HVector (ADVal (RankedOf f)) -> ADVal f r y)
  -> HVector (ADVal (RankedOf f))
  -> (HVectorOf (RankedOf f), f r y)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D l v deltaTopLevel) = f inputs in
  let parameters0 = voidFromHVector inputs
      (!astBindings, !gradient) =
        reverseDervative parameters0 v mdt deltaTopLevel
  in ( unletGradient @ty @f l astBindings (dmkHVector gradient)
     , unletValue l [] v )

crevOnHVector
  :: forall r y f.
     ( RankedTensor (RankedOf f), RankedTensor (ADVal (RankedOf f))
     , HVectorTensor (RankedOf f) (ShapedOf f)
     , DualPart f, UnletGradient f, GoodScalar r, HasSingletonDict y )
  => Maybe (f r y)
  -> (HVector (ADVal (RankedOf f)) -> ADVal f r y)
  -> HVector (RankedOf f)
  -> (HVectorOf (RankedOf f), f r y)
crevOnHVector mdt f parameters =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in crevOnADInputs mdt f inputs

cfwdOnADInputs
  :: (DualPart f, UnletGradient f, GoodScalar r, HasSingletonDict y)
  => HVector (ADVal (RankedOf f))
  -> (HVector (ADVal (RankedOf f)) -> ADVal f r y)
  -> HVector (RankedOf f)
  -> (f r y, f r y)
{-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs inputs f ds =
  let !(D l v deltaTopLevel) = f inputs in
  let (astBindings, derivative) =
        forwardDerivative (V.length inputs) deltaTopLevel ds
  in (unletValue l astBindings derivative, unletValue l [] v)

cfwdOnHVector
  :: forall r y f.
     ( RankedTensor (RankedOf f)
     , DualPart f, UnletGradient f, GoodScalar r, HasSingletonDict y )
  => HVector (RankedOf f)
  -> (HVector (ADVal (RankedOf f)) -> ADVal f r y)
  -> HVector (RankedOf f)
  -> (f r y, f r y)
cfwdOnHVector parameters f ds =
  let deltaInputs = generateDeltaInputs parameters
      inputs = makeADInputs parameters deltaInputs
  in cfwdOnADInputs inputs f ds

generateDeltaInputs
  :: forall ranked ranked2 shaped2.
     (RankedTensor ranked, shaped2 ~ ShapedOf ranked2)
  => HVector ranked
  -> HVector (Dual ranked2)
generateDeltaInputs =
  let f :: Int -> DynamicTensor ranked -> DynamicTensor (Dual ranked2)
      f i (DynamicRanked @r @n t) =
        case rshape t of
          (sh :: ShapeInt n2) | Just Refl <- sameNat (Proxy @n) (Proxy @n2) ->
            DynamicRanked $ InputR @ranked2 @r @n sh (toInputId i)
          _ -> error "generateDeltaInputs: wrong rank"
      f i (DynamicShaped @r @sh _) =
        DynamicShaped $ InputS @shaped2 @r @sh (toInputId i)
      f i (DynamicRankedDummy @r @sh _ _) =
        withListShape (Sh.shapeT @sh) $ \(sh :: ShapeInt n) ->
          DynamicRanked $ InputR @ranked2 @r @n sh (toInputId i)
      f i (DynamicShapedDummy @r @sh _ _) =
        DynamicShaped $ InputS @shaped2 @r @sh (toInputId i)
  in V.imap f
{-# SPECIALIZE generateDeltaInputs
  :: HVector (Flip OR.Array) -> HVector (Dual (Flip OR.Array)) #-}

-- Not specialized, because not overloaded (HVector is a type synonym).
makeADInputs
  :: HVector ranked -> HVector (Dual ranked)
  -> HVector (ADVal ranked)
makeADInputs =
  let f :: DynamicTensor ranked -> DynamicTensor (Dual ranked)
        -> DynamicTensor (ADVal ranked)
      f (DynamicRanked @r @n t) (DynamicRanked @r2 @n2 d)
        | Just Refl <- sameNat (Proxy @n) (Proxy @n2)
        , Just Refl <- testEquality (typeRep @r) (typeRep @r2) =
          DynamicRanked $ dDnotShared emptyADShare t d
      f (DynamicShaped @r @sh t) (DynamicShaped @r2 @sh2 d)
        | Just Refl <- sameShape @sh @sh2
        , Just Refl <- testEquality (typeRep @r) (typeRep @r2) =
          DynamicShaped $ dDnotShared emptyADShare t d
      f _ _ = error "makeADInputs: non-matching arguments"
  in V.zipWith f


-- * Reverse and forward derivative stages class and instances

type DerivativeStages :: TensorType ty -> Constraint
class DerivativeStages g where
  forwardPassByInterpretation
    :: (GoodScalar r, HasSingletonDict y)
    => (HVector (RankedOf g) -> g r y)
    -> AstEnv (ADVal (RankedOf (PrimalOf g)))
    -> HVector (RankedOf (PrimalOf g))
    -> [AstDynamicVarName]
    -> HVector (RankedOf g)
    -> ADVal (PrimalOf g) r y

  revArtifactFromForwardPass
    :: (GoodScalar r, HasSingletonDict y)
    => TensorToken g
    -> Bool
    -> (HVector (RankedOf (PrimalOf g))
        -> [AstDynamicVarName]
        -> HVector (RankedOf g)
        -> ADVal (PrimalOf g) r y)
    -> VoidHVector
    -> (AstArtifactRev (PrimalOf g) r y, Dual (PrimalOf g) r y)

  revProduceArtifact
    :: (GoodScalar r, HasSingletonDict y)
    => TensorToken g -> Bool
    -> (HVector (RankedOf g) -> g r y)
    -> AstEnv (ADVal (RankedOf (PrimalOf g)))
    -> VoidHVector
    -> (AstArtifactRev (PrimalOf g) r y, Dual (PrimalOf g) r y)
  {-# INLINE revProduceArtifact #-}
  revProduceArtifact tf hasDt g envInit =
    revArtifactFromForwardPass tf hasDt (forwardPassByInterpretation g envInit)

  revEvalArtifact
    :: (GoodScalar r, HasSingletonDict y)
    => AstArtifactRev (PrimalOf g) r y -> HVector (Flip OR.Array)
    -> Maybe (ConcreteOf g r y)
    -> (HVector (Flip OR.Array), ConcreteOf g r y)

  fwdArtifactFromForwardPass
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => TensorToken g
    -> (HVector (RankedOf (PrimalOf g))
        -> [AstDynamicVarName]
        -> HVector (RankedOf g)
        -> ADVal (PrimalOf g) r y)
    -> VoidHVector
    -> (AstArtifactFwd (PrimalOf g) r y, Dual (PrimalOf g) r y)

  fwdEvalArtifact
    :: (GoodScalar r, HasSingletonDict y)
    => AstArtifactFwd (PrimalOf g) r y -> HVector (Flip OR.Array)
    -> HVector (Flip OR.Array)
    -> (ConcreteOf g r y, ConcreteOf g r y)

  fwdProduceArtifact
    :: (DerivativeStages g, GoodScalar r, HasSingletonDict y)
    => TensorToken g -> (HVector (RankedOf g) -> g r y)
    -> AstEnv (ADVal (RankedOf (PrimalOf g)))
    -> VoidHVector
    -> (AstArtifactFwd (PrimalOf g) r y, Dual (PrimalOf g) r y)
  {-# INLINE fwdProduceArtifact #-}
  fwdProduceArtifact tf g envInit =
    fwdArtifactFromForwardPass tf (forwardPassByInterpretation g envInit)

-- TODO: this is an ad-hoc class with an ad-hoc name
type UnletGradient :: TensorType ty -> Constraint
class UnletGradient g where
  unletGradient
    :: ADShare -> AstBindingsD (RankedOf g) -> HVectorOf (RankedOf g)
    -> HVectorOf (RankedOf g)
  unletValue
    :: (GoodScalar r, HasSingletonDict y)
    => ADShare -> AstBindingsD (RankedOf g) -> g r y
    -> g r y

instance UnletGradient (Flip OR.Array) where
  unletGradient l astBindings gradient =
    assert (nullADShare l && null astBindings) gradient
  unletValue l astBindings primalBody =
    assert (nullADShare l && null astBindings) primalBody

instance UnletGradient (Flip OS.Array) where
  unletGradient l astBindings gradient =
    assert (nullADShare l && null astBindings) gradient
  unletValue l astBindings primalBody =
    assert (nullADShare l && null astBindings) primalBody

instance UnletGradient (HVectorPseudoTensor (Flip OR.Array)) where
  unletGradient l astBindings gradient =
    assert (nullADShare l && null astBindings) gradient
  unletValue l astBindings primalBody =
    assert (nullADShare l && null astBindings) primalBody

instance UnletGradient (ADVal f) where
  unletGradient l astBindings gradient =
    assert (nullADShare l && null astBindings) gradient
  unletValue l astBindings primalBody =
    assert (nullADShare l && null astBindings) primalBody

instance UnletGradient (HVectorPseudoTensor (ADVal f)) where
  unletGradient l astBindings gradient =
    assert (nullADShare l && null astBindings) gradient
  unletValue l astBindings primalBody =
    assert (nullADShare l && null astBindings) primalBody

-- * Numeric instances for ADVal

-- These two instances are required for the numeric tensor instances.
-- They can't be made valid for AST, because they require interpretation before
-- they can be compared with an instant Bool result, so let's fail early
-- also here.
instance Eq (ADVal f r z) where
  (==) = error "AST requires that EqB be used instead"
  (/=) = error "AST requires that EqB be used instead"

instance Ord (ADVal f r z) where
  (<=) = error "AST requires that OrdB be used instead"

instance (Num (f r z), IsPrimal f r z) => Num (ADVal f r z) where
  -- The 0 cases are needed to get GHC 9.6 to use the specialization
  -- (only at rank 0, though; we'd need many more for common ranks and shapes).
  {-# SPECIALIZE instance Num (ADVal (Flip OR.Array) Double 0) #-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance Num (ADVal (AstRanked PrimalSpan) Double 0) #-}
-}
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (Flip OR.Array) Double n) #-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  D l1 u u' + D l2 v v' = dD (l1 `mergeADShare` l2) (u + v) (dAdd u' v')
  D l1 u u' - D l2 v v' =
    dD (l1 `mergeADShare` l2) (u - v) (dAdd u' (dScale (intOfShape v (-1)) v'))
  D l1 ue u' * D l2 ve v' =
    -- The bangs are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D l v v') = dD l (negate v) (dScale (intOfShape v (-1)) v')
  abs (D l ve v') = let !(!l2, v) = recordSharingPrimal ve l
                    in dD l2 (abs v) (dScale (signum v) v')
  signum (D l v _) = dD l (signum v) (dZeroOfShape v)
  fromInteger = constantADVal . fromInteger

instance (Real (f r z), IsPrimal f r z) => Real (ADVal f r z) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum (ADVal f r z) where  -- dummy, to satisfy Integral below
  toEnum = undefined
  fromEnum = undefined

instance (Integral (f r z), IsPrimal f r z)
         => Integral (ADVal f r z) where
  quot (D l1 u _) (D l2 v _) =
    dD (l1 `mergeADShare` l2) (quot u v) (dZeroOfShape u)
  rem (D l1 u _) (D l2 v _) =
    dD (l1 `mergeADShare` l2) (rem u v) (dZeroOfShape u)
  quotRem x y = (quot x y, rem x y)
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Fractional (f r z), IsPrimal f r z) => Fractional (ADVal f r z) where
  {-# SPECIALIZE instance
      Fractional (ADVal (Flip OR.Array) Double 0) #-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      Fractional (ADVal (AstRanked PrimalSpan) Double 0) #-}
-}
  {-# SPECIALIZE instance
      KnownNat n
      => Fractional (ADVal (Flip OR.Array) Double n) #-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      KnownNat n
      => Fractional (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  D l1 ue u' / D l2 ve v' =
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (u / v)
             (dAdd (dScale (recip v) u') (dScale (- u / (v * v)) v'))
  recip (D l ve v') =
    let !(!l2, v) = recordSharingPrimal ve l
        minusRecipSq = - recip (v * v)
    in dD l2 (recip v) (dScale minusRecipSq v')
  fromRational = constantADVal . fromRational

instance (Floating (f r z), IsPrimal f r z) => Floating (ADVal f r z) where
  {-# SPECIALIZE instance
      Floating (ADVal (Flip OR.Array) Double 0) #-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      Floating (ADVal (AstRanked PrimalSpan) Double 0) #-}
-}
  {-# SPECIALIZE instance
      KnownNat n
      => Floating (ADVal (Flip OR.Array) Double n) #-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      KnownNat n
      => Floating (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  pi = constantADVal pi
  exp (D l ue u') = let !(!l2, expU) = recordSharingPrimal (exp ue) l
                    in dD l2 expU (dScale expU u')
  log (D l ue u') = let !(!l2, u) = recordSharingPrimal ue l
                    in dD l2 (log u) (dScale (recip u) u')
  sqrt (D l ue u') = let !(!l2, sqrtU) = recordSharingPrimal (sqrt ue) l
                     in dD l2 sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D l1 ue u' ** D l2 ve v' =
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (u ** v) (dAdd (dScale (v * (u ** (v - intOfShape v 1))) u')
                            (dScale ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                    in dD l2 (sin u) (dScale (cos u) u')
  cos (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                    in dD l2 (cos u) (dScale (- (sin u)) u')
  tan (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                        (l3, cosU) = recordSharingPrimal (cos u) l2
                    in dD l3 (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (asin u)
                           (dScale (recip (sqrt (intOfShape u 1 - u * u))) u')
  acos (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (acos u)
                           (dScale (- recip (sqrt (intOfShape u 1 - u * u))) u')
  atan (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (atan u)
                           (dScale (recip (intOfShape u 1 + u * u)) u')
  sinh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (sinh u) (dScale (cosh u) u')
  cosh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (cosh u) (dScale (sinh u) u')
  tanh (D l ue u') = let (l2, y) = recordSharingPrimal (tanh ue) l
                     in dD l2 y (dScale (intOfShape y 1 - y * y) u')
  asinh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (asinh u)
                            (dScale (recip (sqrt (intOfShape u 1 + u * u))) u')
  acosh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (acosh u)
                            (dScale (recip (sqrt (u * u - intOfShape u 1))) u')
  atanh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (atanh u)
                            (dScale (recip (intOfShape u 1 - u * u)) u')

instance (RealFrac (f r z), IsPrimal f r z) => RealFrac (ADVal f r z) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (RealFloat (f r z), IsPrimal f r z) => RealFloat (ADVal f r z) where
  {-# SPECIALIZE instance
      RealFloat (ADVal (Flip OR.Array) Double 0) #-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      RealFloat (ADVal (AstRanked PrimalSpan) Double 0) #-}
-}
  {-# SPECIALIZE instance
      KnownNat n
      => RealFloat (ADVal (Flip OR.Array) Double n) #-}
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      KnownNat n
      => RealFloat (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  atan2 (D l1 ue u') (D l2 ve v') =
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3 in
    let !(!l5, t) = recordSharingPrimal (recip (u * u + v * v)) l4
    in dD l5 (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
  -- Note that for term types @a@ this is invalid without an extra let
  -- containing the first field of @D@. However, for terms this is
  -- unimplemented anyway.
  floatRadix (D _ u _) = floatRadix u
  floatDigits (D _ u _) = floatDigits u
  floatRange (D _ u _) = floatRange u
  decodeFloat (D _ u _) = decodeFloat u
  encodeFloat i j = constantADVal (encodeFloat i j)
  isNaN (D _ u _) = isNaN u
  isInfinite (D _ u _) = isInfinite u
  isDenormalized (D _ u _) = isDenormalized u
  isNegativeZero (D _ u _) = isNegativeZero u
  isIEEE (D _ u _) = isIEEE u
