{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and arithmetic operations on them.
module HordeAd.Core.CarriersADVal
  ( -- * The main dual number type
    ADVal, pattern D, dD, dDnotShared
    -- * Auxiliary definitions
  , unDeltaPair, unDeltaPairUnshared, dScale, dAdd
  , dFromS, dSFromR, dSFromX
  , fromPrimalADVal
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
--  , addParameters, dotParameters
  , generateDeltaInputs
  ) where

import Prelude

import Data.Type.Equality ((:~:) (Refl))
import GHC.TypeLits (KnownNat)

import Data.Array.Nested (KnownShS (..), KnownShX (..), Rank)

import HordeAd.Core.Delta
import HordeAd.Core.DeltaFreshId
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * The main dual number type

-- | Values that the objective functions operate on when they are being
-- differentiated. The values are, in general, tensors.
-- The first type argument is the functor determining the structure
-- of the tensors (whether ranked, shaped, dynamic, storable, unboxed, etc.).
-- The second argument is the underlying scalar type. The third
-- is the rank or shape of the tensor value.
--
-- The datatype is implemented as dual numbers (hence @D@).,
-- The @f z@ value is the primal component, which is the normal,
-- the basic value.
type role ADVal nominal nominal
data ADVal (f :: Target) y = ADVal (f y) (Delta f y)

pattern D :: f z -> Delta f z -> ADVal f z
pattern D t u <- ADVal t u  -- enforces only pattern matching
{-# COMPLETE D #-}

deriving instance (Show (f z), Show (Delta f z))
                  => Show (ADVal f z)

-- | Smart constructor for 'D' of 'ADVal' that additionally records delta
-- expression sharing information (regardless if the basic value
-- of the dual number is an AST term or not).
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: forall f z. KnownSTK z
   => f z -> Delta f z -> ADVal f z
dD !a !dual = dDnotShared a (shareDelta dual)

-- | This a not so smart a constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: f z -> Delta f z -> ADVal f z
dDnotShared = ADVal


-- * Auxiliary definitions

-- TODO: maybe create a separate module of Delta smart constructors
-- and then use the following haddocks for the module:
--
-- | The impurity in this module, stemming from the use of this operation
-- under @unsafePerformIO@, is thread-safe, admits parallel tests
-- and does not require @-fno-full-laziness@ nor @-fno-cse@.
-- The only tricky point is mandatory use of the smart constructors
-- above and that any new smart constructors should be similarly
-- call-by-value to ensure proper order of identifiers of subterms.
--
-- | This module uses and rather safely encapsulates impure side-effects.
-- The impurity produces pure data with a particular property.
-- The property is an order of per-node integer identifiers that represents
-- data dependencies and sharing between delta expressions. The low-level API
-- depends on this property, but is completely isolated from the impurity.
-- The high-level API triggers the impurity but can't observe
-- any impure behaviour. Neither can any other module in the package,
-- except for the testing modules that import testing-exclusive class instances
-- and operations for reading or reseting the impure counter.

-- | The instances are impure, because 'shareDelta'
-- adorns terms with an @Int@ identifier from a counter that is afterwards
-- incremented (and never changed in any other way).
--
-- The identifiers are not part of any non-internal module API
-- and the impure counter that gets incremented is not exposed
-- (except for low level tests). The identifiers are read only in internal
-- modules. They are assigned here once and ever accessed read-only.
-- Their uniqueness ensures that subterms that are shared in memory
-- are evaluated only once. If pointer equality worked efficiently
-- (e.g., if compact regions with sharing were cheaper), we wouldn't need
-- the impurity.
--
-- Given that we have to use impurity anyway, we make the implementation
-- faster by ensuring the order of identifiers reflects data dependency,
-- that is, parent nodes always have higher identifier than child nodes.
-- The @StrictData@ extension ensures that the implementation of the instances
-- are call by value, which is needed for that identifier ordering.
--
-- As long as "HordeAd.Core.Delta" is used exclusively through
-- smart constructors from this API, the impurity is completely safe.
-- Even compiler optimizations, e.g., cse and full-laziness,
-- can't break the required invariants. On the contrary,
-- they increase sharing and make evaluation yet cheaper.
-- Of course, if the compiler, e.g., stops honouring @NOINLINE@,
-- all this breaks down.
--
-- The pattern-matching in 'shareDelta' is a crucial optimization
-- and it could, presumably, be extended to further limit which
-- terms get an identifier. Alternatively, 'HordeAd.Core.CarriersADVal.dD'
-- or library definitions that use it could be made smarter.

unDeltaPair :: (KnownSTK x, KnownSTK y)
            => Delta target (TKProduct x y) -> (Delta target x, Delta target y)
unDeltaPair (DeltaPair a b) = (a, b)
unDeltaPair (DeltaZero (FTKProduct ftk1 ftk2)) = (DeltaZero ftk1, DeltaZero ftk2)
unDeltaPair d = let dShared = shareDelta d  -- TODO: more cases
                in (DeltaProject1 dShared, DeltaProject2 dShared)

unDeltaPairUnshared :: (KnownSTK x, KnownSTK y)
                    => Delta target (TKProduct x y)
                    -> (Delta target x, Delta target y)
unDeltaPairUnshared (DeltaPair a b) = (a, b)
unDeltaPairUnshared (DeltaZero (FTKProduct ftk1 ftk2)) =
  (DeltaZero ftk1, DeltaZero ftk2)
unDeltaPairUnshared d = (DeltaProject1 d, DeltaProject2 d)

dScale :: Num (f z) => f z -> Delta f z -> Delta f z
dScale _ (DeltaZero ftk) = DeltaZero ftk
dScale v u' = DeltaScale v u'

dAdd :: Num (f z) => Delta f z -> Delta f z -> Delta f z
dAdd DeltaZero{} w = w
dAdd v DeltaZero{} = v
dAdd v w = DeltaAdd v w

-- Avoids building huge Delta terms, not only evaluating them.
dFromS :: forall y z target. (KnownSTK y, KnownSTK z)
       => Delta target y -> Delta target z
dFromS (DeltaSFromR @sh @x d)
  | Just Refl <- sameKnownSTS @z @(TKR2 (Rank sh) x) = d
dFromS (DeltaSFromX @_ @sh' @x d)
  | Just Refl <- sameKnownSTS @z @(TKX2 sh' x) = d
dFromS d = DeltaFromS d

dSFromR :: forall sh x target.
           (KnownShS sh, KnownNat (Rank sh), KnownSTK x)
        => Delta target (TKR2 (Rank sh) x)
        -> Delta target (TKS2 sh x)
dSFromR (DeltaFromS @y d) =
  case sameKnownSTS @y @(TKS2 sh x) of
    Just Refl -> d
    _ -> error "sfromR: different shapes in DeltaSFromR(DeltaFromS)"
dSFromR d = DeltaSFromR d

dSFromX :: forall sh sh' x target.
           (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', KnownSTK x)
        => Delta target (TKX2 sh' x)
        -> Delta target (TKS2 sh x)
dSFromX (DeltaFromS @y d) =
  case sameKnownSTS @y @(TKS2 sh x) of
    Just Refl -> d
    _ -> error "sfromR: different shapes in DeltaSFromX(DeltaFromS)"
dSFromX d = DeltaSFromX d

-- This hack is needed to recover shape from tensors,
-- in particular in case of numeric literals and also for forward derivative.
intOfShape :: forall z f. (ADReadyNoLet f, KnownSTK z)
           => f z -> Int -> f z
intOfShape tsh c = constantTarget (fromIntegral c) (tftk knownSTK tsh)

fromPrimalADVal :: (KnownSTK z, BaseTensor f) => f z -> ADVal f z
fromPrimalADVal a = dDnotShared a (DeltaZero $ tftk knownSTK a)

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: KnownSTK z => ADVal f z -> ADVal f z
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
{-
addParameters :: (DTensorOf r ~ OD.Array r)
              => HVector r -> HVector r -> HVector r
addParameters (HVector a0 a1) (HVector b0 b1) =
  HVector (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: (DTensorOf r ~ OD.Array r)
              => HVector r -> HVector r -> r
dotParameters (HVector a0 a1) (HVector b0 b1) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1) a1 b1)
-}

generateDeltaInputs
  :: forall x target.
     FullTensorKind x -> Delta target x
generateDeltaInputs =
  let gen :: Int -> FullTensorKind y -> (Delta target y, Int)
      gen j ftk| Dict <- lemKnownSTK (ftkToSTK ftk) = case ftk of
        FTKProduct ftk1 ftk2 | Dict <- lemKnownSTK (ftkToSTK ftk1)
                             , Dict <- lemKnownSTK (ftkToSTK ftk2) ->
          let (d1, j1) = gen j ftk1
              (d2, j2) = gen j1 ftk2
          in (DeltaPair d1 d2, j2)
        _ -> (DeltaInput ftk (toInputId ftk j), j + 1)
  in fst . gen 0
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE generateDeltaInputs
  :: HVector (FlipR OR.Array) -> HVector (Delta (FlipR OR.Array)) #-}
-}


-- * Assorted instances

type instance BoolOf (ADVal f) = BoolOf f

instance EqF f => EqF (ADVal f) where
  D u _ ==. D v _ = u ==. v
  D u _ /=. D v _ = u /=. v

instance OrdF f => OrdF (ADVal f) where
  D u _ <. D v _ = u <. v
  D u _ <=. D v _ = u <=. v
  D u _ >. D v _ = u >. v
  D u _ >=. D v _ = u >=. v

type instance HFunOf (ADVal f) x y = HFun x y

type instance PrimalOf (ADVal f) = f

type instance DualOf (ADVal f) = Delta f

type instance ShareOf (ADVal f) = ADVal f


-- * Numeric instances

-- These two instances are required for the numeric tensor instances.
-- They can't be made valid for AST, because they require interpretation before
-- they can be compared with an instant Bool result, so let's fail early
-- also here.
instance Eq (ADVal f z) where
  (==) = error "AST requires that EqB be used instead"
  (/=) = error "AST requires that EqB be used instead"

instance Ord (ADVal f z) where
  (<=) = error "AST requires that OrdB be used instead"

instance (Num (f z), KnownSTK z, ShareTensor f, ADReadyNoLet f)
         => Num (ADVal f z) where
  -- The 0 cases are needed to get GHC 9.6 to use the specialization
  -- (only at rank 0, though; we'd need many more for common ranks and shapes).
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance Num (ADVal (FlipR OR.Array) Double 0) #-}
  {-# SPECIALIZE instance Num (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (FlipR OR.Array) Double n) #-}
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  D u u' + D v v' = dD (u + v) (dAdd u' v')
  D u u' - D v v' =
    dD (u - v) (dAdd u' (dScale (intOfShape v (-1)) v'))
  D ue u' * D ve v' =
    -- The bangs are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = dD (negate v) (dScale (intOfShape v (-1)) v')
  abs (D ve v') = let !v = tshare ve
                  in dD (abs v) (dScale (signum v) v')
  signum (D v _) = dDnotShared (signum v) (DeltaZero $ tftk knownSTK v)
  fromInteger = fromPrimalADVal . fromInteger

instance (Real (f z), KnownSTK z, ShareTensor f, ADReadyNoLet f)
         => Real (ADVal f z) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (IntegralF (f z), KnownSTK z, ShareTensor f, ADReadyNoLet f)
         => IntegralF (ADVal f z) where
  quotF (D u _) (D v _) = dDnotShared (quotF u v) ((DeltaZero $ tftk knownSTK u))
  remF (D u _) (D v _) = dDnotShared (remF u v) ((DeltaZero $ tftk knownSTK u))

instance (Fractional (f z), KnownSTK z, ShareTensor f, ADReadyNoLet f)
         => Fractional (ADVal f z) where
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      Fractional (ADVal (FlipR OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      Fractional (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Fractional (ADVal (FlipR OR.Array) Double n) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Fractional (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  D ue u' / D ve v' =
    let !u = tshare ue in
    let !v = tshare ve
    in dD (u / v)
          (dAdd (dScale (recip v) u') (dScale ((- u) / (v * v)) v'))
  recip (D ve v') =
    let !v = tshare ve
        minusRecipSq = - recip (v * v)
    in dD (recip v) (dScale minusRecipSq v')
  fromRational = fromPrimalADVal . fromRational

instance (Floating (f z), KnownSTK z, ShareTensor f, ADReadyNoLet f)
         => Floating (ADVal f z) where
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      Floating (ADVal (FlipR OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      Floating (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Floating (ADVal (FlipR OR.Array) Double n) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Floating (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  pi = fromPrimalADVal pi
  exp (D ue u') = let !expU = tshare (exp ue)
                  in dD expU (dScale expU u')
  log (D ue u') = let !u = tshare ue
                  in dD (log u) (dScale (recip u) u')
  sqrt (D ue u') = let !sqrtU = tshare (sqrt ue)
                   in dD sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D ue u' ** D ve v' =
    let !u = tshare ue in
    let !v = tshare ve
    in dD (u ** v) (dAdd (dScale (v * (u ** (v - intOfShape v 1))) u')
                         (dScale ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D ue u') = let !u = tshare ue
                  in dD (sin u) (dScale (cos u) u')
  cos (D ue u') = let !u = tshare ue
                  in dD (cos u) (dScale (- (sin u)) u')
  tan (D ue u') = let !u = tshare ue in
                  let !cosU = tshare (cos u)
                  in dD (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D ue u') = let !u = tshare ue
                   in dD (asin u)
                         (dScale (recip (sqrt (intOfShape u 1 - u * u))) u')
  acos (D ue u') = let !u = tshare ue
                   in dD (acos u)
                         (dScale (- recip (sqrt (intOfShape u 1 - u * u))) u')
  atan (D ue u') = let !u = tshare ue
                   in dD (atan u)
                         (dScale (recip (intOfShape u 1 + u * u)) u')
  sinh (D ue u') = let !u = tshare ue
                   in dD (sinh u) (dScale (cosh u) u')
  cosh (D ue u') = let !u = tshare ue
                   in dD (cosh u) (dScale (sinh u) u')
  tanh (D ue u') = let !y = tshare (tanh ue)
                   in dD y (dScale (intOfShape y 1 - y * y) u')
  asinh (D ue u') = let !u = tshare ue
                    in dD (asinh u)
                          (dScale (recip (sqrt (intOfShape u 1 + u * u))) u')
  acosh (D ue u') = let !u = tshare ue
                    in dD (acosh u)
                          (dScale (recip (sqrt (u * u - intOfShape u 1))) u')
  atanh (D ue u') = let !u = tshare ue
                    in dD (atanh u)
                          (dScale (recip (intOfShape u 1 - u * u)) u')

instance (RealFrac (f z), KnownSTK z, ShareTensor f, ADReadyNoLet f)
         => RealFrac (ADVal f z) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Fractional (f z), RealFloatF (f z), KnownSTK z, ShareTensor f, ADReadyNoLet f)
         => RealFloatF (ADVal f z) where
  atan2F (D ue u') (D ve v') =
    let !u = tshare ue in
    let !v = tshare ve in
    let !t = tshare (recip (u * u + v * v))
    in dD (atan2F u v) (dAdd (dScale ((- u) * t) v') (dScale (v * t) u'))

instance (RealFloat (f z), KnownSTK z, ShareTensor f, ADReadyNoLet f)
         => RealFloat (ADVal f z) where
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      RealFloat (ADVal (FlipR OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      RealFloat (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => RealFloat (ADVal (FlipR OR.Array) Double n) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => RealFloat (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  atan2 (D ue u') (D ve v') =
    let !u = tshare ue in
    let !v = tshare ve in
    let !t = tshare (recip (u * u + v * v))
    in dD (atan2 u v) (dAdd (dScale ((- u) * t) v') (dScale (v * t) u'))
  -- Note that for term types @a@ this is invalid without an extra let
  -- containing the first field of @D@. However, for terms this is
  -- unimplemented anyway.
  floatRadix (D u _) = floatRadix u
  floatDigits (D u _) = floatDigits u
  floatRange (D u _) = floatRange u
  decodeFloat (D u _) = decodeFloat u
  encodeFloat i j = fromPrimalADVal (encodeFloat i j)
  isNaN (D u _) = isNaN u
  isInfinite (D u _) = isInfinite u
  isDenormalized (D u _) = isDenormalized u
  isNegativeZero (D u _) = isNegativeZero u
  isIEEE (D u _) = isIEEE u
