{-# LANGUAGE UndecidableInstances #-}
-- | Dual numbers type and operations on it.
-- These definitions, mostly class instances, are needed to make dual numbers
-- a valid carrier for a tensor class algebra (instance) defined
-- in "HordeAd.Core.OpsADVal" so that user programs can be instantiated to
-- or interpreted into it (which corresponds to the forward pass)
-- and subsequently differentiated by evaluating the resulting
-- delta expressions (which corresponds to the backpropagation phase
-- in case of reverse derivatives).
module HordeAd.Core.CarriersADVal
  ( -- * The dual number type
    ADVal, pattern D, dD, dDnotShared
    -- * Auxiliary definitions
  , unDeltaPair, unDeltaPairUnshared, dScale, dAdd
  , dSFromR, dSFromX, dXFromS
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
  , generateDeltaInputs
  ) where

import Prelude

import Data.Int (Int64)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))

import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape

import Data.Array.Nested.Lemmas
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.DeltaFreshId
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The dual number type

-- | The type of dual numbers that are the values of objective functions
-- when they are being differentiated. In general, the primal parts
-- of the dual numbers represent tensors or tuples of tensors.
-- The dual parts are fixed to be delta expressions.
-- The first type argument is the functor determining the nature
-- of the tensors (concrete, symbolic, etc.).
-- The second argument is the tensor kind, which constraints the shapes
-- of the particular tensor (or tensor tuple).
type role ADVal nominal nominal
data ADVal (f :: Target) y = ADVal (f y) (Delta f y)

pattern D :: f z -> Delta f z -> ADVal f z
pattern D t u <- ADVal t u  -- enforces only pattern matching
{-# COMPLETE D #-}

deriving instance (Show (f z), Show (Delta f z))
                  => Show (ADVal f z)

-- | Smart constructor for t'ADVal' that additionally records delta
-- expression sharing information (regardless if the primal part
-- of the dual number is an AST term or not).
-- The bare constructor should not (and cannot) be used for constructing
-- values, but only for deconstructing dual numbers via pattern-matching.
dD :: forall f z.
      f z -> Delta f z -> ADVal f z
dD !a !dual = dDnotShared a (shareDelta dual)

-- | This is a not so smart constructor for t'ADVal' that does not record
-- sharing information. If used in contexts where duplication occurs,
-- it may cause exponential blowup when a delta expression is evaluated
-- in backpropagation phase. In contexts without duplication, it saves
-- some evaluation time and memory (in delta term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: f z -> Delta f z -> ADVal f z
dDnotShared = ADVal


-- * Auxiliary definitions

-- TODO: maybe create a separate module of Delta smart constructors
-- and then use the following haddocks for the module:

-- The instances are impure, because 'shareDelta'
-- adorns terms with an @Int@ identifier from a counter that is afterwards
-- incremented (and never changed in any other way).
--
-- The identifiers are not part of any non-internal module API
-- and the impure counter that gets incremented is not exposed
-- (except for low level tests). The identifiers are assigned here once
-- and ever accessed read-only.
-- Their uniqueness ensures that subterms that are shared in memory
-- are evaluated only once. If pointer equality worked efficiently
-- (e.g., if compact regions with sharing were cheaper), we wouldn't need
-- the impurity.
--
-- Given that we have to use impurity anyway, we make the implementation
-- faster by ensuring the order of identifiers reflects data dependency,
-- that is, parent nodes always have higher identifier than child nodes.
-- The @StrictData@ extension ensures that the delta constructors
-- are call by value, which is needed for that identifier ordering.
--
-- As long as "HordeAd.Core.Delta" is used exclusively through
-- smart constructors from this API, the impurity is completely safe
-- (currently, it's enough that @DeltaShare@ is used exclusively
-- via @shareDelta@). Even compiler optimizations, e.g., cse and full-laziness,
-- can't break the required invariants. On the contrary,
-- they increase sharing and make evaluation yet cheaper.

unDeltaPair :: Delta target (TKProduct x y) -> (Delta target x, Delta target y)
unDeltaPair (DeltaPair a b) = (a, b)
unDeltaPair (DeltaZero (FTKProduct ftk1 ftk2)) =
  (DeltaZero ftk1, DeltaZero ftk2)
unDeltaPair d = let dShared = shareDelta d
                in (DeltaProject1 dShared, DeltaProject2 dShared)

unDeltaPairUnshared :: Delta target (TKProduct x y)
                    -> (Delta target x, Delta target y)
unDeltaPairUnshared (DeltaPair a b) = (a, b)
unDeltaPairUnshared (DeltaZero (FTKProduct ftk1 ftk2)) =
  (DeltaZero ftk1, DeltaZero ftk2)
unDeltaPairUnshared d = (DeltaProject1 d, DeltaProject2 d)  -- duplicated

dScale :: Num (f z) => f z -> Delta f z -> Delta f z
dScale _ (DeltaZero ftk) = DeltaZero ftk
dScale v u' = DeltaScale (NestedTarget v) u'

dAdd :: Num (f z) => Delta f z -> Delta f z -> Delta f z
dAdd DeltaZero{} w = w
dAdd v DeltaZero{} = v
dAdd v w = DeltaAdd v w

-- Prevents building huge Delta terms, not only evaluating them.
dSFromR :: forall sh x target.
           ShS sh -> Delta target (TKR2 (Rank sh) x)
        -> Delta target (TKS2 sh x)
dSFromR sh w@(DeltaConvert _c d)
  | FTKR _ x <- ftkDelta w
  , Just Refl <- matchingFTK (ftkDelta d) (FTKS sh x) = d
dSFromR sh d | FTKR _ x <- ftkDelta d
             , Refl <- lemRankReplicate (Proxy @(Rank sh)) =
  let c2 = ConvCmp (ConvXS' (FTKS sh x)) ConvRX
  in DeltaConvert c2 d

dSFromX :: forall sh sh' x target. Rank sh ~ Rank sh'
        => ShS sh -> Delta target (TKX2 sh' x)
        -> Delta target (TKS2 sh x)
dSFromX sh w@(DeltaConvert _c d)
  | FTKX _ x <- ftkDelta w
  , Just Refl <- matchingFTK (ftkDelta d) (FTKS sh x) = d
dSFromX sh d | FTKX _ x <- ftkDelta d =
  let c2 = ConvXS' (FTKS sh x)
  in DeltaConvert c2 d

dXFromS :: forall sh sh' x target. Rank sh ~ Rank sh'
        => StaticShX sh' -> Delta target (TKS2 sh x)
        -> Delta target (TKX2 sh' x)
dXFromS ssx w@(DeltaConvert _c d)
  | FTKS sh x <- ftkDelta w
  , let shx = shCastSX ssx sh
  , Just Refl <- matchingFTK (ftkDelta d) (FTKX shx x) = d
dXFromS ssx d
  | FTKS sh x <- ftkDelta d
  , let shx = shCastSX ssx sh
  , Refl <- lemRankMapJust sh =
    let c2 = ConvCmp (ConvXX' (FTKX shx x)) ConvSX
    in DeltaConvert c2 d

-- This hack is needed to recover shape from tensors,
-- in particular in case of numeric literals and also for forward derivative.
intOfShape :: forall z f. ADReadyNoLet f
           => Delta f z -> Int -> f z
intOfShape tsh c = treplTarget (fromIntegral c) (ftkDelta tsh)

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: ADVal f z -> ADVal f z
ensureToplevelSharing (D u u') = dD u u'

scaleNotShared :: Num (f z)
               => f z -> ADVal f z -> ADVal f z
scaleNotShared !a (D u u') = dDnotShared (a * u) (dScale a u')

addNotShared :: forall f z. Num (f z)
             => ADVal f z -> ADVal f z -> ADVal f z
addNotShared (D u u') (D v v') = dDnotShared (u + v) (dAdd u' v')

multNotShared :: forall f z. Num (f z)
              => ADVal f z -> ADVal f z -> ADVal f z
multNotShared (D u u') (D v v') =
  dDnotShared (u * v) (dAdd (dScale v u') (dScale u v'))

generateDeltaInputs :: forall x target.
                       FullShapeTK x -> Delta target x
generateDeltaInputs =
  let gen :: Int -> FullShapeTK y -> (Delta target y, Int)
      gen j ftk = case ftk of
        FTKProduct ftk1 ftk2 ->
          let (d1, j1) = gen j ftk1
              (d2, j2) = gen j1 ftk2
          in (DeltaPair d1 d2, j2)
        _ | differentiableFTK ftk -> (DeltaInput (mkInputId ftk j), j + 1)
        _ -> (DeltaZero ftk, j)
  in fst . gen 0


-- * Assorted instances

type instance BoolOf (ADVal f) = BoolOf f

instance EqH f (TKScalar r) => EqH (ADVal f) (TKScalar r) where
  D u _ ==. D v _ = u ==. v

instance OrdH f (TKScalar r) => OrdH (ADVal f) (TKScalar r) where
  D u _ <=. D v _ = u <=. v

instance EqH f (TKR n r) => EqH (ADVal f) (TKR n r) where
  D u _ ==. D v _ = u ==. v

instance OrdH f (TKR n r) => OrdH (ADVal f) (TKR n r) where
  D u _ <=. D v _ = u <=. v

instance EqH f (TKS sh r) => EqH (ADVal f) (TKS sh r) where
  D u _ ==. D v _ = u ==. v

instance OrdH f (TKS sh r) => OrdH (ADVal f) (TKS sh r) where
  D u _ <=. D v _ = u <=. v

instance EqH f (TKX sh r) => EqH (ADVal f) (TKX sh r) where
  D u _ ==. D v _ = u ==. v

instance OrdH f (TKX sh r) => OrdH (ADVal f) (TKX sh r) where
  D u _ <=. D v _ = u <=. v

type instance HFunOf (ADVal f) x y = HFun x y

type instance PrimalOf (ADVal f) = f

type instance DualOf (ADVal f) = Delta f

type instance ShareOf (ADVal f) = ADVal f
  -- Maybe this should be ADVal (ShareOf f), but we'd need tests
  -- that use this, probably tests with ADVal (AST) nested in ADVal


-- * Numeric instances

-- These two instances are required for the numeric tensor instances.
-- They can't be made valid for AST, because they require interpretation before
-- they can be compared with an instant Bool result, so let's fail early
-- also here.
instance Eq (ADVal f z) where
  (==) = error "Eq is not defined for ADVal; please use EqH instead"
  (/=) = error "Eq is not defined for ADVal; please use EqH instead"

instance Ord (ADVal f z) where
  (<=) = error "Ord is not defined for ADVal; please use OrdH instead"

-- This is copied from below to permit fromInteger for TKScalar.
-- This OVERLAPPABLE seems to work 100% reliably for indexes
-- and not at all for a variant of rfromListLinear that takes scalars.
instance (GoodScalar r, ShareTensor f, ADReadyNoLet f)
         => Num (ADVal f (TKScalar r)) where
  D u u' + D v v' = dD (u + v) (dAdd u' v')
  D u u' - D v v' =
    dD (u - v) (dAdd u' (dScale (intOfShape v' (-1)) v'))
  D ue u' * D ve v' =
    -- The bangs are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = dD (negate v) (dScale (intOfShape v' (-1)) v')
  abs (D ve v') = let !v = tshare ve
                  in dD (abs v) (dScale (signum v) v')
  signum (D v v') = dDnotShared (signum v) (DeltaZero $ ftkDelta v')
  fromInteger i = dDnotShared (fromInteger i) (DeltaZero FTKScalar)
  -- The constraints in the pragmas below are needed only to avoid
  -- module import cycles.
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKScalar Double)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKScalar Float)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKScalar Int64)) #-}

instance {-# OVERLAPPABLE #-}
         (Num (f z), ShareTensor f, ADReadyNoLet f)
         => Num (ADVal f z) where
  D u u' + D v v' = dD (u + v) (dAdd u' v')
  D u u' - D v v' =
    dD (u - v) (dAdd u' (dScale (intOfShape v' (-1)) v'))
  D ue u' * D ve v' =
    -- The bangs are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = dD (negate v) (dScale (intOfShape v' (-1)) v')
  abs (D ve v') = let !v = tshare ve
                  in dD (abs v) (dScale (signum v) v')
  signum (D v v') = dDnotShared (signum v) (DeltaZero $ ftkDelta v')
  fromInteger = error "fromInteger is not defined for tensors in general"
  -- The constraints in the pragmas below are needed only to avoid
  -- module import cycles.
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKR n Double)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKR n Float)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKR n Int64)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKS sh Double)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKS sh Float)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKS sh Int64)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKX sh Double)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKX sh Float)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => Num (ADVal Concrete (TKX sh Int64)) #-}

instance (Real (f z), ShareTensor f, ADReadyNoLet f)
         => Real (ADVal f z) where
  toRational (D v _) = toRational v
    -- this is most probably not what the user expects, but the type
    -- of the result (Rational) doesn't permit any better solution

instance (IntegralH (f z), ShareTensor f, ADReadyNoLet f)
         => IntegralH (ADVal f z) where
  quotH (D u _) (D v v') = dDnotShared (quotH u v) (DeltaZero $ ftkDelta v')
  remH (D u _) (D v v') = dDnotShared (remH u v) (DeltaZero $ ftkDelta v')
  -- The constraints in the pragmas below are needed only to avoid
  -- module import cycles.
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => IntegralH (ADVal Concrete (TKR n Int64)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => IntegralH (ADVal Concrete (TKS sh Int64)) #-}
  {-# SPECIALIZE instance (ShareTensor Concrete, ADReadyNoLet Concrete) => IntegralH (ADVal Concrete (TKX sh Int64)) #-}

-- This is copied from below to permit fromRational for TKScalar.
instance ( GoodScalar r, Fractional (f (TKScalar r)), ShareTensor f
         , ADReadyNoLet f )
         => Fractional (ADVal f (TKScalar r)) where
  D ue u' / D ve v' =
    let !u = tshare ue in
    let !v = tshare ve
    in dD (u / v) (dAdd (dScale (recip v) u') (dScale ((- u) / (v * v)) v'))
  recip (D ve v') =
    let !v = tshare ve
        minusRecipSq = - recip (v * v)
    in dD (recip v) (dScale minusRecipSq v')
  fromRational r = dDnotShared (fromRational r) (DeltaZero FTKScalar)

instance {-# OVERLAPPABLE #-}
         (Fractional (f z), ShareTensor f, ADReadyNoLet f)
         => Fractional (ADVal f z) where
  D ue u' / D ve v' =
    let !u = tshare ue in
    let !v = tshare ve
    in dD (u / v) (dAdd (dScale (recip v) u') (dScale ((- u) / (v * v)) v'))
  recip (D ve v') =
    let !v = tshare ve
        minusRecipSq = - recip (v * v)
    in dD (recip v) (dScale minusRecipSq v')
  fromRational = error "fromRational is not defined for tensors in general"

instance (Floating (f z), ShareTensor f, ADReadyNoLet f)
         => Floating (ADVal f z) where
  pi = error "pi is not defined for tensors"
  exp (D ue u') = let !expU = tshare (exp ue)
                  in dD expU (dScale expU u')
  log (D ue u') = let !u = tshare ue
                  in dD (log u) (dScale (recip u) u')
  sqrt (D ue u') = let !sqrtU = tshare (sqrt ue)
                   in dD sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D ue u' ** D ve v' =
    let !u = tshare ue in
    let !v = tshare ve
    in dD (u ** v) (dAdd (dScale (v * (u ** (v - intOfShape v' 1))) u')
                         (dScale ((u ** v) * log u) v'))
  -- logBase x y = log y / log x
  sin (D ue u') = let !u = tshare ue
                  in dD (sin u) (dScale (cos u) u')
  cos (D ue u') = let !u = tshare ue
                  in dD (cos u) (dScale (- (sin u)) u')
  tan (D ue u') = let !u = tshare ue in
                  let !cosU = tshare (cos u)
                  in dD (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D ue u') = let !u = tshare ue
                   in dD (asin u)
                         (dScale (recip (sqrt (intOfShape u' 1 - u * u))) u')
  acos (D ue u') = let !u = tshare ue
                   in dD (acos u)
                         (dScale (- recip (sqrt (intOfShape u' 1 - u * u))) u')
  atan (D ue u') = let !u = tshare ue
                   in dD (atan u)
                         (dScale (recip (intOfShape u' 1 + u * u)) u')
  sinh (D ue u') = let !u = tshare ue
                   in dD (sinh u) (dScale (cosh u) u')
  cosh (D ue u') = let !u = tshare ue
                   in dD (cosh u) (dScale (sinh u) u')
  tanh (D ue u') = let !y = tshare (tanh ue)
                   in dD y (dScale (intOfShape u' 1 - y * y) u')
  asinh (D ue u') = let !u = tshare ue
                    in dD (asinh u)
                          (dScale (recip (sqrt (intOfShape u' 1 + u * u))) u')
  acosh (D ue u') = let !u = tshare ue
                    in dD (acosh u)
                          (dScale (recip (sqrt (u * u - intOfShape u' 1))) u')
  atanh (D ue u') = let !u = tshare ue
                    in dD (atanh u)
                          (dScale (recip (intOfShape u' 1 - u * u)) u')

instance (RealFrac (f z), ShareTensor f, ADReadyNoLet f)
         => RealFrac (ADVal f z) where
  properFraction = error "properFraction is not defined for tensors"
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Fractional (f z), RealFloatH (f z), ShareTensor f, ADReadyNoLet f)
         => RealFloatH (ADVal f z) where
  atan2H (D ue u') (D ve v') =
    let !u = tshare ue in
    let !v = tshare ve in
    let !t = tshare (recip (u * u + v * v))
    in dD (atan2H u v) (dAdd (dScale ((- u) * t) v') (dScale (v * t) u'))

instance (RealFloat (f z), ShareTensor f, ADReadyNoLet f)
         => RealFloat (ADVal f z) where
  atan2 (D ue u') (D ve v') =
    let !u = tshare ue in
    let !v = tshare ve in
    let !t = tshare (recip (u * u + v * v))
    in dD (atan2 u v) (dAdd (dScale ((- u) * t) v') (dScale (v * t) u'))
  floatRadix (D u _) = floatRadix u
  floatDigits (D u _) = floatDigits u
  floatRange (D u _) = floatRange u
  decodeFloat (D u _) = decodeFloat u
  encodeFloat _i _j = error "encodeFloat is not defined for tensors"
  isNaN (D u _) = isNaN u
  isInfinite (D u _) = isInfinite u
  isDenormalized (D u _) = isDenormalized u
  isNegativeZero (D u _) = isNegativeZero u
  isIEEE (D u _) = isIEEE u
