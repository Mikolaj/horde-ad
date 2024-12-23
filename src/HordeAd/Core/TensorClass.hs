{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library and it's relatively orthogonal to the
-- differentiation interface in "HordeAd.Core.Engine".
module HordeAd.Core.TensorClass
  ( ) where

import Prelude

import Data.Default
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , cmpNat
  , sameNat
  , type (+)
  , type (-)
  , type (<=)
  )
import Numeric.LinearAlgebra (Numeric)
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Lemmas
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  (IShX, StaticShX (..), ssxAppend, ssxFromShape, ssxReplicate)
import Data.Array.Nested
  ( IShR
  , IxS (..)
  , KnownShS (..)
  , KnownShX (..)
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , pattern (:$:)
  , pattern (:.$)
  , pattern (:.:)
  , pattern ZIR
  , pattern ZIS
  , pattern ZSR
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shCvtSX, shsAppend)

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- Note that no Ast* module except AstInterpret and AstEnv
-- depends on any Tensor*, Carriers* and Ops* modules
-- and vice versa except CarriersAst and OpsAst.
-- Syntax is separated from semantics and they meet in the interpreter
-- and in the semantic model constructed from syntax (TensorAst).

type TensorSupports :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupports c1 c2 f =
  forall r. GoodScalar r
            => c1 r => c2 (f (TKScalar r))

type TensorSupportsR :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsR c1 c2 f =
  forall r n. (GoodScalar r, KnownNat n)
              => c1 r => c2 (f (TKR n r))

type TensorSupportsS :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsS c1 c2 f =
  forall r sh. (GoodScalar r, KnownShS sh)
               => c1 r => c2 (f (TKS sh r))

type TensorSupportsX :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsX c1 c2 f =
  forall r sh. (GoodScalar r, KnownShX sh)
               => c1 r => c2 (f (TKX sh r))

class (RealFloat r, Nested.FloatElt r)
      => RealFloatAndFloatElt r
instance (RealFloat r, Nested.FloatElt r)
         => RealFloatAndFloatElt r

class LetTensor (target :: Target) where
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => target x
       -> (target x -> target z)
       -> target z
  treplicate :: BaseTensor target
             => SNat k -> STensorKindType z
             -> target z
             -> target (BuildTensorKind k z)
  treplicate snat@SNat stk u = case stk of
    STKScalar{} -> u
-- TODO?      error "treplicate: type family BuildTensorKind stuck at TKScalar"
    STKR SNat STKScalar{} -> rreplicate (sNatValue snat) u
    STKS sh STKScalar{} -> withKnownShS sh $ sreplicate u
-- TODO:    STKS sh (STKS _ STKScalar{}) -> withKnownShS sh $ sreplicate u
    STKX sh STKScalar{} -> withKnownShX sh $ xreplicate u
    STKProduct @z1 @z2 stk1 stk2
      | Dict <- lemTensorKindOfSTK stk1
      , Dict <- lemTensorKindOfSTK stk2
      , Dict <- eltDictRep stk1
      , Dict <- eltDictRep stk2
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z1)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z2) ->
        tlet u $ \ !u1 ->
          tpair (treplicate snat stk1 (tproject1 u1))
                (treplicate snat stk2 (tproject2 u1))
    STKUntyped ->
      tlet u $ \ !u1 ->
        dmkHVector
        $ replicate1HVectorF rreplicate sreplicate snat
        $ dunHVector u1
    _ -> error "TODO"

  toShare :: TensorKind y
          => target y
          -> ShareOf target y
  tunshare :: TensorKind y
           => ShareOf target y
           -> target y
  tunshare = error "tunshare: this instance should never be used"

class ShareTensor (target :: Target) where
  tshare :: forall y. TensorKind y
         => target y -> target y
  tunpair :: (TensorKind x, TensorKind z)
          => target (TKProduct x z) -> (target x, target z)
  tunvector :: target TKUntyped -> HVector target

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Num (IntOf target)
      , IntegralF (IntOf target)
      , TensorSupports Num Num target
      , TensorSupports RealFloatF Floating target
      , TensorSupports RealFloatF RealFloatF target
      , TensorSupports IntegralF IntegralF target
      , TensorSupportsR Num Num target
      , TensorSupportsR RealFloatAndFloatElt Floating target
      , TensorSupportsR RealFloatAndFloatElt RealFloatF target
      , TensorSupportsR Integral IntegralF target
      , TensorSupportsS Num Num target
      , TensorSupportsS RealFloatAndFloatElt Floating target
      , TensorSupportsS RealFloatAndFloatElt RealFloatF target
      , TensorSupportsS Integral IntegralF target
      , TensorSupportsX Num Num target
      , TensorSupportsX RealFloatAndFloatElt Floating target
      , TensorSupportsX RealFloatAndFloatElt RealFloatF target
      , TensorSupportsX Integral IntegralF target )
      => BaseTensor (target :: Target) where

  -- Integer codomain
  rshape :: TensorKind r => target (TKR2 n r) -> IShR n
  rrank :: forall r n. (TensorKind r, KnownNat n) => target (TKR2 n r) -> Int
  rrank _ = valueOf @n
  rsize :: TensorKind r => target (TKR2 n r) -> Int
  rsize = sizeShape . rshape
  rlength :: TensorKind r => target (TKR2 (1 + n) r) -> Int
  rlength v = case rshape v of
    ZSR -> error "rlength: impossible pattern needlessly required"
    k :$: _ -> k
  rminIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => target (TKR (1 + n) r) -> target (TKR n r2)  -- partial
  rmaxIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => target (TKR (1 + n) r) -> target (TKR n r2)  -- partial
  rfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownNat n)
         => target (TKR n r) -> target (TKR n r2)
  riota :: GoodScalar r => target (TKR 1 r)  -- 0, 1 .. infinity
  riota = undefined  -- infinite, hence diverges; don't override

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- may indicate the rank of the codomain, if bounded.

  -- First index is for outermost dimension; empty index means identity,
  -- index ouf of bounds produces zero (but beware of vectorization).
  rindex, (!) :: (TensorKind r, KnownNat m, KnownNat n)
              => target (TKR2 (m + n) r) -> IxROf target m -> target (TKR2 n r)
  infixl 9 !
  (!) = rindex  -- prefix form better when type applications are necessary
  rindex0 :: (TensorKind r, KnownNat m)
          => target (TKR2 m r) -> IxROf target m -> target (TKR2 0 r)
  rindex0 = rindex
  rsum :: (GoodScalar r, KnownNat n) => target (TKR (1 + n) r) -> target (TKR n r)
  rsum0 :: (GoodScalar r, KnownNat n) => target (TKR n r) -> target (TKR 0 r)
  rsum0 = rsum . rflatten
  rdot0 :: (GoodScalar r, KnownNat n) => target (TKR n r) -> target (TKR n r) -> target (TKR 0 r)
  rdot0 t u = rsum (rflatten (t * u))
  rmatvecmul :: GoodScalar r => target (TKR 2 r) -> target (TKR 1 r) -> target (TKR 1 r)
-- How to generalize (#69)? The few straightforward generalizations
-- differ in types but all are far from matmul2.
  rmatvecmul m v = rbuild1 (rlength m) (\i -> rdot0 v (m ! [i]))
-- rmatvecmul m v = rflatten $ rmap1 (rreplicate 1 . rdot0 v) m
  rmatmul2 :: (GoodScalar r, Numeric r)
           => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
-- How to generalize to tmatmul (#69)?
-- Just rmatmul2 the two outermost dimensions?
-- rmatmul2 m1 m2 = rmap1 (rmatvecmul (rtr m2)) m1
-- rmatmul2 m1 m2 = rbuild1 (rlength m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
  rmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR -> rsum (rtranspose [2,1,0] (rreplicate width2 m1)
                                  * rtranspose [1,0] (rreplicate (rlength m1) m2))
    _ -> error "rmatmul2: impossible pattern needlessly required"
  rscatter :: (TensorKind r, KnownNat m, KnownNat n, KnownNat p)
           => IShR (p + n) -> target (TKR2 (m + n) r)
           -> (IxROf target m -> IxROf target p)
           -> target (TKR2 (p + n) r)
  rscatter1 :: forall r n p. (TensorKind r, KnownNat n, KnownNat p)
            => IShR (p + n) -> target (TKR2 (1 + n) r)
            -> (IntOf target -> IxROf target p)
            -> target (TKR2 (p + n) r)
  rscatter1 sh v f = rscatter @target @r @1 sh v
                              (\(i :.: ZIR) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  rfromList :: (TensorKind r, KnownNat n)
            => NonEmpty (target (TKR2 n r)) -> target (TKR2 (1 + n) r)
  rfromList = rfromVector . V.fromList . NonEmpty.toList
    -- going through strict vectors, because laziness is risky with impurity
  rfromList0N :: (TensorKind r, KnownNat n)
              => IShR n -> [target (TKR2 0 r)] -> target (TKR2 n r)
  rfromList0N sh = rfromVector0N sh . V.fromList
  -- This is morally non-empty strict vectors:
  rfromVector :: (TensorKind r, KnownNat n)
              => Data.Vector.Vector (target (TKR2 n r)) -> target (TKR2 (1 + n) r)
  rfromVector0N :: (TensorKind r, KnownNat n)
                => IShR n -> Data.Vector.Vector (target (TKR2 0 r))
                -> target (TKR2 n r)
  rfromVector0N sh = rreshape sh . rfromVector
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'tlet'.
  runravelToList :: forall r n. (TensorKind r, KnownNat n)
                 => target (TKR2 (1 + n) r) -> [target (TKR2 n r)]
  runravelToList t =
    let f :: Int -> target (TKR2 n r)
        f i = rindex t (singletonIndex $ fromIntegral i)
    in map f [0 .. rlength t - 1]
  rreplicate :: (GoodScalar r, KnownNat n)
             => Int -> target (TKR n r) -> target (TKR (1 + n) r)
  rreplicate0N :: (GoodScalar r, KnownNat n)
               => IShR n -> target (TKR 0 r) -> target (TKR n r)
  rreplicate0N sh = rreshape sh . rreplicate (sizeShape sh)
  rappend :: (TensorKind r, KnownNat n)
          => target (TKR2 (1 + n) r) -> target (TKR2 (1 + n) r)
          -> target (TKR2 (1 + n) r)
  rconcat :: (TensorKind r, KnownNat n)
          => [target (TKR2 (1 + n) r)] -> target (TKR2 (1 + n) r)
  rconcat = foldr1 rappend
  rslice :: (TensorKind r, KnownNat n)
         => Int -> Int -> target (TKR2 (1 + n) r) -> target (TKR2 (1 + n) r)
  runcons :: (TensorKind r, KnownNat n)
          => target (TKR2 (1 + n) r)
          -> Maybe (target (TKR2 n r), target (TKR2 (1 + n) r))
  runcons v = case rshape v of
                ZSR -> Nothing
                len :$: _ -> Just (v ! [0], rslice 1 (len - 1) v)
  rreverse :: (TensorKind r, KnownNat n)
           => target (TKR2 (1 + n) r) -> target (TKR2 (1 + n) r)
  rtr :: (TensorKind r, KnownNat n)
      => target (TKR2 (2 + n) r) -> target (TKR2 (2 + n) r)
  rtr = rtranspose [1, 0]
  rtranspose :: (TensorKind r, KnownNat n)
             => Permutation.PermR -> target (TKR2 n r) -> target (TKR2 n r)
  rflatten :: (TensorKind r, KnownNat n) => target (TKR2 n r) -> target (TKR2 1 r)
  rflatten u = rreshape (flattenShape $ rshape u) u
  rreshape :: (TensorKind r, KnownNat n, KnownNat m)
           => IShR m -> target (TKR2 n r) -> target (TKR2 m r)
  rbuild :: forall r m n. (TensorKind r, KnownNat m, KnownNat n)
         => IShR (m + n) -> (IxROf target m -> target (TKR2 n r))
         -> target (TKR2 (m + n) r)
  rbuild sh0 f0 =
    let buildSh :: IShR m1 -> (IxROf target m1 -> target (TKR2 n r))
                -> target (TKR2 (m1 + n) r)
        buildSh ZSR f = f ZIR
        buildSh (k :$: sh) f | Dict <- knownShR sh =
          let g i = buildSh sh (\ix -> f (i :.: ix))
          in rbuild1 k g
    in buildSh (takeShape @m @n sh0) f0
  rbuild1 :: (TensorKind r, KnownNat n)  -- this form needs less typeapps
          => Int -> (IntOf target -> target (TKR2 n r)) -> target (TKR2 (1 + n) r)
  rmap :: (TensorKind r, TensorKind r2, KnownNat m, KnownNat n)
       => (target (TKR2 n r) -> target (TKR2 n r2))
       -> target (TKR2 (m + n) r) -> target (TKR2 (m + n) r2)
  rmap f v = rbuild (rshape v) (\ix -> f (v ! ix))
  rmap1 :: (TensorKind r, TensorKind r2, KnownNat n)
        => (target (TKR2 n r) -> target (TKR2 n r2))
        -> target (TKR2 (1 + n) r) -> target (TKR2 (1 + n) r2)
  rmap1 f u = rbuild1 (rlength u) (\i -> f (u ! [i]))
  rmap0N :: (TensorKind r, TensorKind r1, KnownNat n)
         => (target (TKR2 0 r1) -> target (TKR2 0 r)) -> target (TKR2 n r1)
         -> target (TKR2 n r)
  rmap0N f v = rbuild (rshape v) (f . rindex0 v)
  rzipWith :: ( TensorKind r1, TensorKind r2, TensorKind r
              , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n )
           => IShR (m + n)
           -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n r))
           -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2)
           -> target (TKR2 (m + n) r)
  rzipWith sh f u v = rbuild sh (\ix -> f (u ! ix) (v ! ix))
  rzipWith1 :: ( TensorKind r1, TensorKind r2, TensorKind r
               , KnownNat n1, KnownNat n2, KnownNat n )
            => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n r))
            -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n) r)
  rzipWith1 f u v = rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]))
  rzipWith0N :: (TensorKind r1, TensorKind r2, TensorKind r, KnownNat n)
             => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r))
             -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r)
  rzipWith0N f u v = rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix))
  rzipWith3 :: ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r
               , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n )
            => IShR (m + n)
            -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n r))
            -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2) -> target (TKR2 (m + n3) r3)
            -> target (TKR2 (m + n) r)
  rzipWith3 sh f u v w = rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix))
  rzipWith31 :: ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r
                , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n )
             => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n r))
             -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n3) r3)
             -> target (TKR2 (1 + n) r)
  rzipWith31 f u v w =
    rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]))
  rzipWith30N :: ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r
                 , KnownNat n )
              => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r3) -> target (TKR2 0 r))
              -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r3) -> target (TKR2 n r)
  rzipWith30N f u v w =
    rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix))
  rzipWith4 :: ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r4
               , TensorKind r, KnownNat m
               , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
               , KnownNat n )
            => IShR (m + n)
            -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n4 r4)
                -> target (TKR2 n r))
            -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2) -> target (TKR2 (m + n3) r3)
            -> target (TKR2 (m + n4) r4)
            -> target (TKR2 (m + n) r)
  rzipWith4 sh f u v w x =
    rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix) (x ! ix))
  rzipWith41 :: ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r4
                , TensorKind r
                , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
                , KnownNat n )
             => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n4 r4)
                 -> target (TKR2 n r))
             -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n3) r3)
             -> target (TKR2 (1 + n4) r4)
             -> target (TKR2 (1 + n) r)
  rzipWith41 f u v w x =
    rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]) (x ! [i]))
  rzipWith40N :: ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r4
                 , TensorKind r
                 , KnownNat n )
              => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r3) -> target (TKR2 0 r4)
                  -> target (TKR2 0 r))
              -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r3) -> target (TKR2 n r4)
              -> target (TKR2 n r)
  rzipWith40N f u v w x =
    rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix)
                                (rindex0 x ix))
  rgather :: (TensorKind r, KnownNat m, KnownNat n, KnownNat p)
          => IShR (m + n) -> target (TKR2 (p + n) r)
          -> (IxROf target m -> IxROf target p)
          -> target (TKR2 (m + n) r)
  rgather1 :: forall r n p. (TensorKind r, KnownNat n, KnownNat p)
           => Int -> target (TKR2 (p + n) r)
           -> (IntOf target -> IxROf target p)
           -> target (TKR2 (1 + n) r)
  rgather1 k v f = rgather @target @r @1
                           (k :$: dropShape (rshape v)) v
                           (\(i :.: ZIR) -> f i)
  rcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownNat n)
        => target (TKR n r1) -> target (TKR n r2)
  rfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                => target (TKR n r1) -> target (TKR n r2)
  rconcrete :: (TensorKind r, KnownNat n)
            => Nested.Ranked n (RepORArray r) -> target (TKR2 n r)
  rconcrete a = tconcrete (tftkG (STKR SNat stensorKind) a) (RepN a)
  rzip :: (TensorKind y, TensorKind z, KnownNat n)
       => target (TKProduct (TKR2 n y) (TKR2 n z))
       -> target (TKR2 n (TKProduct y z))
  runzip :: (TensorKind y, TensorKind z, KnownNat n)
         => target (TKR2 n (TKProduct y z))
         -> target (TKProduct (TKR2 n y) (TKR2 n z))
  rtoScalar :: GoodScalar r => target (TKR 0 r) -> target (TKScalar r)
  rfromScalar :: GoodScalar r => target (TKScalar r) -> target (TKR 0 r)
  -- Prevents wrong shape in @0@ with ranked (but not shaped) tensors
  -- at any rank greater than zero.
  rzero :: (GoodScalar r, KnownNat n)
        => IShR n -> target (TKR n r)
  rzero sh = rreplicate0N sh (rscalar 0)

  -- ** No serviceable parts beyond this point ** --

  rscaleByScalar :: (GoodScalar r, KnownNat n)
                 => target (TKR 0 r) -> target (TKR n r) -> target (TKR n r)
  rscaleByScalar s v = v * rreplicate0N (rshape v) s
  rdot1In :: GoodScalar r
          => target (TKR 2 r) -> target (TKR 2 r)
          -> target (TKR 1 r)  -- TODO: generalize
  rdot1In t u = rsum $ rtr (t * u)

  -- Primal/dual things.
  rfromPrimal :: (TensorKind r, KnownNat n)
              => PrimalOf target (TKR2 n r) -> target (TKR2 n r)
  rprimalPart :: (TensorKind r, KnownNat n)
              => target (TKR2 n r) -> PrimalOf target (TKR2 n r)
  rdualPart :: (TensorKind r, KnownNat n)
            => target (TKR2 n r) -> DualOf target (TKR2 n r)
  rD :: (TensorKind r, KnownNat n)
     => PrimalOf target (TKR2 n r) -> DualOf target (TKR2 n r) -> target (TKR2 n r)
  rScale :: (GoodScalar r, KnownNat n)
         => PrimalOf target (TKR n r) -> DualOf target (TKR n r)
         -> DualOf target (TKR n r)
  -- TODO: we'd probably also need dZero, dIndex0 and others from IsPrimal,
  -- because IsPrimal has subtly different types, operating on Deltas (Dual)
  -- instead of on terms (DualOf) that denote Deltas
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

  xshape :: (TensorKind r, KnownShX sh) => target (TKX2 sh r) -> IShX sh
  xindex :: forall r sh1 sh2.
            ( GoodScalar r, KnownShX sh1, KnownShX sh2
            , KnownShX (sh1 ++ sh2) )
         => target (TKX (sh1 ++ sh2) r) -> IxXOf target sh1
         -> target (TKX sh2 r)
  xfromVector :: (GoodScalar r, KnownNat n, KnownShX sh)
              => Data.Vector.Vector (target (TKX sh r))
              -> target (TKX (Just n ': sh) r)
  xreplicate :: (KnownNat n, KnownShX sh, GoodScalar r)
             => target (TKX sh r) -> target (TKX (Just n ': sh) r)
  xconcrete :: (GoodScalar r, KnownShX sh)
            => Nested.Mixed sh r -> target (TKX sh r)
  xconcrete a = tconcrete (FTKX (Nested.mshape a) FTKScalar) (RepN a)
  xzip :: (TensorKind y, TensorKind z, KnownShX sh)
       => target (TKProduct (TKX2 sh y) (TKX2 sh z))
       -> target (TKX2 sh (TKProduct y z))
  xunzip :: (TensorKind y, TensorKind z, KnownShX sh)
         => target (TKX2 sh (TKProduct y z))
         -> target (TKProduct (TKX2 sh y) (TKX2 sh z))
  xtoScalar :: GoodScalar r => target (TKX '[] r) -> target (TKScalar r)
  xfromScalar :: GoodScalar r => target (TKScalar r) -> target (TKX '[] r)
  xzero :: forall r sh. (GoodScalar r, KnownShX sh)
        => IShX sh -> target (TKX sh r)
  xzero sh = xrepl sh 0
  xfromPrimal :: (GoodScalar r, KnownShX sh)
              => PrimalOf target (TKX sh r) -> target (TKX sh r)
  xprimalPart :: (GoodScalar r, KnownShX sh)
              => target (TKX sh r) -> PrimalOf target (TKX sh r)
  xdualPart :: (GoodScalar r, KnownShX sh)
            => target (TKX sh r) -> DualOf target (TKX sh r)
  xD :: (GoodScalar r, KnownShX sh)
     => PrimalOf target (TKX sh r)-> DualOf target (TKX sh r)
     -> target (TKX sh r)
  -- Integer codomain
  sshape :: forall sh r. (TensorKind r, KnownShS sh)
         => target (TKS2 sh r) -> ShS sh
  sshape _ = knownShS @sh
  srank :: forall sh r. (TensorKind r, KnownNat (Rank sh))
        => target (TKS2 sh r) -> Int
  srank _ = valueOf @(Rank sh)
  ssize :: forall sh r. (TensorKind r, KnownShS sh) => target (TKS2 sh r) -> Int
  ssize _ = sizeT @sh
  slength :: forall r n sh. (TensorKind r, KnownNat n)
          => target (TKS2 (n ': sh) r) -> Int
  slength _ = valueOf @n
  sminIndex :: ( GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n
               , KnownShS (Init (n ': sh)) )  -- partial
            => target (TKS (n ': sh) r) -> target (TKS (Init (n ': sh)) r2)
  smaxIndex :: ( GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n
               , KnownShS (Init (n ': sh)) )  -- partial
            => target (TKS (n ': sh) r) -> target (TKS (Init (n ': sh)) r2)
  sfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownShS sh)
         => target (TKS sh r) -> target (TKS sh r2)
    -- the integer can be negative
    -- TODO: shall we make it abs (floor v)?
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => target (TKS '[n] r)  -- from 0 to n - 1

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- indicates the rank of the codomain, if bounded.
  sindex, (!$) :: forall r sh1 sh2.
                  ( TensorKind r, KnownShS sh1, KnownShS sh2
                  , KnownShS (sh1 ++ sh2) )
               => target (TKS2 (sh1 ++ sh2) r) -> IxSOf target sh1
               -> target (TKS2 sh2 r)
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall sh1 r. (TensorKind r, KnownShS sh1)
          => target (TKS2 sh1 r) -> IxSOf target sh1
          -> target (TKS2 '[] r)
  sindex0 | Refl <- lemAppNil @sh1 = sindex
  ssum :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
       => target (TKS (n ': sh) r) -> target (TKS sh r)
  ssum0 :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => target (TKS sh r) -> target (TKS '[] r)
  ssum0 = ssum . sflatten
  sdot0 :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => target (TKS sh r) -> target (TKS sh r) -> target (TKS '[] r)
  sdot0 t u = ssum (sflatten (t * u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => target (TKS '[m, n] r) -> target (TKS '[n] r) -> target (TKS '[m] r)
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ (i :.$ ZIS)))
  smatmul2 :: forall r n m p.
              (GoodScalar r, Numeric r, KnownNat n, KnownNat m, KnownNat p)
           => target (TKS '[m, n] r) -> target (TKS '[n, p] r) -> target (TKS '[m, p] r)
  smatmul2 m1 m2 =
    ssum (stranspose (Permutation.makePerm @'[2, 1, 0]) (sreplicate @target @p m1)
          * stranspose (Permutation.makePerm @'[1, 0]) (sreplicate @target @m m2))
  sscatter
    :: forall r sh2 p sh.
       ( TensorKind r, KnownShS sh2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh)
       , KnownShS (sh2 ++ Drop p sh) )
    => target (TKS2 (sh2 ++ Drop p sh) r)
    -> (IxSOf target sh2 -> IxSOf target (Take p sh))
    -> target (TKS2 sh r)
  sscatter1
    :: forall r n2 p sh.
       ( TensorKind r, KnownNat n2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh) )
    => target (TKS2 (n2 ': Drop p sh) r)
    -> (IntOf target -> IxSOf target (Take p sh))
    -> target (TKS2 sh r)
  sscatter1 v f = sscatter @target @r @'[n2] v (\(i :.$ _) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  sfromList :: (TensorKind r, KnownNat n, KnownShS sh)
            => NonEmpty (target (TKS2 sh r)) -> target (TKS2 (n ': sh) r)
  sfromList = sfromVector . V.fromList . NonEmpty.toList
  sfromList0N :: forall r sh.
                 (TensorKind r, KnownShS sh, KnownNat (Nested.Product sh))
              => [target (TKS2 '[] r)] -> target (TKS2 sh r)
  sfromList0N = sfromVector0N . V.fromList
  -- This is morally non-empty strict vectors:
  sfromVector :: (TensorKind r, KnownNat n, KnownShS sh)
              => Data.Vector.Vector (target (TKS2 sh r))
              -> target (TKS2 (n ': sh) r)
  sfromVector0N :: forall r sh.
                   (TensorKind r, KnownShS sh, KnownNat (Nested.Product sh))
                => Data.Vector.Vector (target (TKS2 '[] r))
                -> target (TKS2 sh r)
  sfromVector0N =
    sreshape @target @r @'[Nested.Product sh] @sh . sfromVector
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'tlet'.
  sunravelToList :: forall r n sh. (TensorKind r, KnownNat n, KnownShS sh)
                 => target (TKS2 (n ': sh) r) -> [target (TKS2 sh r)]
  sunravelToList t =
    let f :: Int -> target (TKS2 sh r)
        f i = sindex t (ShapedList.singletonIndex $ fromIntegral i)
    in map f [0 .. slength t - 1]
  sreplicate :: (KnownNat n, KnownShS sh, GoodScalar r)
             => target (TKS sh r) -> target (TKS (n ': sh) r)
  sreplicate0N :: forall r sh.
                  (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
               => target (TKS '[] r) -> target (TKS sh r)
  sreplicate0N = sreshape @target @(TKScalar r) @'[Nested.Product sh] @sh
                 . sreplicate @target @(Nested.Product sh)
  sappend :: (TensorKind r, KnownNat m, KnownNat n, KnownShS sh)
          => target (TKS2 (m ': sh) r) -> target (TKS2 (n ': sh) r)
          -> target (TKS2 ((m + n) ': sh) r)
  sslice :: (TensorKind r, KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
         => Proxy i -> Proxy n
         -> target (TKS2 (i + n + k ': sh) r) -> target (TKS2 (n ': sh) r)
  suncons :: forall r n sh. (TensorKind r, KnownNat n, KnownShS sh)
          => target (TKS2 (n ': sh) r)
          -> Maybe (target (TKS2 sh r), target (TKS2 (n - 1 ': sh) r))
  suncons v = case cmpNat (Proxy @1) (Proxy @n) of
    EQI -> Just ( v !$ (0 :.$ ZIS)
                , sslice @target @r @1 @(n - 1) @0 Proxy Proxy v )
    LTI -> Just ( v !$ (0 :.$ ZIS)
                , sslice @target @r @1 @(n - 1) @0 Proxy Proxy v )
    _ -> Nothing
  sreverse :: (TensorKind r, KnownNat n, KnownShS sh)
           => target (TKS2 (n ': sh) r) -> target (TKS2 (n ': sh) r)
  str :: ( TensorKind r, KnownNat n, KnownNat m, KnownShS sh
         , KnownNat (Rank sh) )
      => target (TKS2 (n ': m ': sh) r) -> target (TKS2 (m ': n ': sh) r)
  str = stranspose (Permutation.makePerm @'[1, 0])
  stranspose :: forall perm r sh.
                ( PermC perm, KnownShS sh
                , Rank perm <= Rank sh, TensorKind r )
             => Permutation.Perm perm -> target (TKS2 sh r)
             -> target (TKS2 (Permutation.PermutePrefix perm sh) r)
  sflatten :: (TensorKind r, KnownShS sh, KnownNat (Nested.Product sh))
           => target (TKS2 sh r) -> target (TKS2 '[Nested.Product sh] r)
  sflatten = sreshape
  sreshape :: ( TensorKind r, KnownShS sh, KnownShS sh2
              , Nested.Product sh ~ Nested.Product sh2 )
           => target (TKS2 sh r) -> target (TKS2 sh2 r)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  sbuild :: forall r m sh. (TensorKind r, KnownShS sh, KnownShS (Take m sh))
         => (IxSOf target (Take m sh) -> target (TKS2 (Drop m sh) r))
         -> target (TKS2 sh r)
  sbuild =
    let buildSh
          :: forall sh1.
             ShS sh1 -> ShS (sh1 ++ Drop m sh)
          -> (IxSOf target sh1 -> target (TKS2 (Drop m sh) r))
          -> target (TKS2 (sh1 ++ Drop m sh) r)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSS, _) -> f ZIS
          ((:$$) SNat sh2, (:$$) _ sh2m) | Dict <- sshapeKnown sh2m ->
            let g i = buildSh sh2 sh2m (f . (i :.$))
            in sbuild1 g
    in gcastWith (unsafeCoerce Refl
                  :: sh :~: Take m sh ++ Drop m sh)
       $ buildSh (knownShS @(Take m sh))
                 (knownShS @sh)
  sbuild1 :: forall r n sh. (TensorKind r, KnownNat n, KnownShS sh)
          => (IntOf target -> target (TKS2 sh r))
          -> target (TKS2 (n ': sh) r)
  smap :: forall r r2 m sh.
          ( TensorKind r, TensorKind r2, KnownNat m
          , KnownShS sh, KnownShS (Take m sh), KnownShS (Drop m sh) )
       => (target (TKS2 (Drop m sh) r) -> target (TKS2 (Drop m sh) r2))
       -> target (TKS2 sh r) -> target (TKS2 sh r2)
  smap f v = gcastWith (unsafeCoerce Refl
                        :: sh :~: Take m sh ++ Drop m sh)
             $ sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r sh n r2.
           (TensorKind r, TensorKind r2, KnownNat n, KnownShS sh)
        => (target (TKS2 sh r) -> target (TKS2 sh r2))
        -> target (TKS2 (n ': sh) r) -> target (TKS2 (n ': sh) r2)
  smap1 f u = sbuild1 (\i -> f (u !$ (i :.$ ZIS)))
  smap0N :: forall r1 r sh.
            (TensorKind r1, TensorKind r, KnownShS sh)
         => (target (TKS2 '[] r1) -> target (TKS2 '[] r)) -> target (TKS2 sh r1)
         -> target (TKS2 sh r)
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @r @(Rank sh) (f . sindex0 v)
  szipWith :: forall r1 r2 r m sh1 sh2 sh.
              ( TensorKind r1, TensorKind r2, TensorKind r
              , KnownNat m, KnownShS sh1, KnownShS sh2, KnownShS sh
              , KnownShS (Take m sh), KnownShS (Drop m sh1)
              , KnownShS (Drop m sh2), KnownShS (Drop m sh)
              , sh1 ~ Take m sh ++ Drop m sh1
              , sh2 ~ Take m sh ++ Drop m sh2 )
           => (target (TKS2 (Drop m sh1) r1)
               -> target (TKS2 (Drop m sh2) r2)
               -> target (TKS2 (Drop m sh) r))
           -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh r)
  szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r1 r2 r n sh1 sh2 sh.
               ( TensorKind r1, TensorKind r2, TensorKind r
               , KnownNat n, KnownShS sh1, KnownShS sh2, KnownShS sh )
            => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh r))
            -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
            -> target (TKS2 (n ': sh) r)
  szipWith1 f u v = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                     (v !$ (i :.$ ZIS)))
  szipWith0N :: forall r1 r2 r sh.
                (TensorKind r1, TensorKind r2, TensorKind r, KnownShS sh)
             => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r))
             -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r)
  szipWith0N f u v =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))
  szipWith3 :: forall r1 r2 r3 r m sh1 sh2 sh3 sh.
               ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r
               , KnownNat m
               , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh
               , KnownShS (Take m sh), KnownShS (Drop m sh1)
               , KnownShS (Drop m sh2), KnownShS (Drop m sh3)
               , KnownShS (Drop m sh)
               , sh1 ~ Take m sh ++ Drop m sh1
               , sh2 ~ Take m sh ++ Drop m sh2
               , sh3 ~ Take m sh ++ Drop m sh3 )
            => (target (TKS2 (Drop m sh1) r1)
                -> target (TKS2 (Drop m sh2) r2)
                -> target (TKS2 (Drop m sh3) r3)
                -> target (TKS2 (Drop m sh) r))
            -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh r)
  szipWith3 f u v w = sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix))
  szipWith31 :: forall r1 r2 r3 r n sh1 sh2 sh3 sh.
                ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r
                , KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh )
             => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh r))
             -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
             -> target (TKS2 (n ': sh3) r3)
             -> target (TKS2 (n ': sh) r)
  szipWith31 f u v w = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                        (v !$ (i :.$ ZIS))
                                        (w !$ (i :.$ ZIS)))
  szipWith30N :: forall r1 r2 r3 r sh.
                 ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r
                 , KnownShS sh, KnownNat (Rank sh) )
              => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r3)
                  -> target (TKS2 '[] r))
              -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r3) -> target (TKS2 sh r)
  szipWith30N f u v w =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix))
  szipWith4 :: forall r1 r2 r3 r4 r m sh1 sh2 sh3 sh4 sh.
               ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r4
               , TensorKind r, KnownNat m
               , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
               , KnownShS sh
               , KnownShS (Take m sh), KnownShS (Drop m sh1)
               , KnownShS (Drop m sh2), KnownShS (Drop m sh3)
               , KnownShS (Drop m sh4), KnownShS (Drop m sh)
               , sh1 ~ Take m sh ++ Drop m sh1
               , sh2 ~ Take m sh ++ Drop m sh2
               , sh3 ~ Take m sh ++ Drop m sh3
               , sh4 ~ Take m sh ++ Drop m sh4 )
            => (target (TKS2 (Drop m sh1) r1)
                -> target (TKS2 (Drop m sh2) r2)
                -> target (TKS2 (Drop m sh3) r3)
                -> target (TKS2 (Drop m sh4) r4)
                -> target (TKS2 (Drop m sh) r))
            -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh4 r4)
            -> target (TKS2 sh r)
  szipWith4 f u v w x =
    sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix) (x !$ ix))
  szipWith41 :: forall r1 r2 r3 r4 r n sh1 sh2 sh3 sh4 sh.
                ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r4
                , TensorKind r, KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
                , KnownShS sh )
             => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3)
                 -> target (TKS2 sh4 r4) -> target (TKS2 sh r))
             -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
             -> target (TKS2 (n ': sh3) r3) -> target (TKS2 (n ': sh4) r4)
             -> target (TKS2 (n ': sh) r)
  szipWith41 f u v w x = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                          (v !$ (i :.$ ZIS))
                                          (w !$ (i :.$ ZIS))
                                          (x !$ (i :.$ ZIS)))
  szipWith40N :: forall r1 r2 r3 sh r4 r.
                 ( TensorKind r1, TensorKind r2, TensorKind r3, TensorKind r4
                 , TensorKind r, KnownShS sh, KnownNat (Rank sh) )
              => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r3)
                  -> target (TKS2 '[] r4) -> target (TKS2 '[] r))
              -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r3) -> target (TKS2 sh r4)
              -> target (TKS2 sh r)
  szipWith40N f u v w x =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix)
                                                (sindex0 x ix))
  tpair :: (TensorKind x, TensorKind z)
         => target x -> target z
         -> target (TKProduct x z)
  tproject1 :: (TensorKind x, TensorKind z)
            => target (TKProduct x z)
            -> target x
  tproject2 :: (TensorKind x, TensorKind z)
            => target (TKProduct x z)
            -> target z
  dshape :: target TKUntyped -> VoidHVector
  tftk :: STensorKindType y -> target y -> FullTensorKind y
  tcond :: IfF target
        => STensorKindType y
        -> BoolOf target
        -> target y -> target y
        -> target y
  tfromPrimal :: STensorKindType y
              -> PrimalOf target y
              -> target y
  tprimalPart :: STensorKindType y
              -> target y
              -> PrimalOf target y
  tdualPart :: STensorKindType y
            -> target y
            -> DualOf target y
  tD :: STensorKindType y
     -> PrimalOf target y -> DualOf target y
     -> target y
  tconcrete :: FullTensorKind y -> RepN y -> target y
  dmkHVector :: HVector target -> target TKUntyped
  tlambda :: (TensorKind x, TensorKind z)
          => FullTensorKind x -> HFun x z -> HFunOf target x z
  tApply :: (TensorKind x, TensorKind z)
         => HFunOf target x z -> target x
         -> target z
  dunHVector :: target TKUntyped -> HVector target
  default dunHVector :: ShareTensor target => target TKUntyped -> HVector target
  dunHVector = tunvector
    -- ^ Warning: this operation easily breaks sharing.
    -- The operation can't usually be implemented to preserve
    -- sharing, because it's type signature doesn't fit the let
    -- and share operations available.
  tunpairDup :: (TensorKind x, TensorKind z)
             => target (TKProduct x z) -> (target x, target z)
  default tunpairDup :: (ShareTensor target, TensorKind x, TensorKind z)
                     => target (TKProduct x z) -> (target x, target z)
  tunpairDup = tunpair
  drev
    :: (TensorKind x, TensorKind z)
    => FullTensorKind x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target x (ADTensorKind x)  -- a |-> da
  drevDt
    :: (TensorKind x, TensorKind z)
    => FullTensorKind x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target (TKProduct (ADTensorKind z) x) (ADTensorKind x)
                 -- [db, a] |-> da
  dfwd
    :: (TensorKind x, TensorKind z)
    => FullTensorKind x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target (TKProduct (ADTensorKind x) x) (ADTensorKind z)
                 -- [da, a] |-> db
  sfold
    :: forall rn rm sh shm k.
       (TensorKind rn, TensorKind rm, KnownShS sh, KnownShS shm, KnownNat k)
    => (forall f. ADReady f => f (TKS2 sh rn) -> f (TKS2 shm rm) -> f (TKS2 sh rn))
    -> target (TKS2 sh rn)
    -> target (TKS2 (k ': shm) rm)
    -> target (TKS2 sh rn)
  sfold f acc0 es =
    let xm = case tftk stensorKind es of
          FTKS _ x2 -> x2
        x = case tftk stensorKind acc0 of
          FTKS _ x2 -> x2
    in tproject1
      (dmapAccumL (Proxy @target)
         (SNat @k)


-- this is the only error
         (FTKS @sh knownShS (FTKScalar @rn))
-- this fixes it:
--         (FTKS @sh knownShS x)



         (FTKScalar @Z0)
         (FTKS @shm knownShS xm)
         (let g :: forall f. ADReady f
                => f (TKS2 sh rn) -> f (TKS2 shm rm)
                -> f (TKProduct (TKS2 sh rn) TKUnit)
              g !acc !e = tpair (f acc e) tunit
          in g)
         acc0
         es)
  dmapAccumL
    :: forall k accShs bShs eShs.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy target
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> (forall f. ADReady f
        => f accShs -> f eShs
        -> f (TKProduct accShs bShs))
    -> target accShs
    -> target (BuildTensorKind k eShs)
    -> target (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumL proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = FTKProduct accShs eShs
        fl :: forall f. ADReady f
           => f (TKProduct accShs eShs)
           -> f (TKProduct accShs bShs)
        fl !args = tlet args $ \ !args1 ->
                     f (tproject1 args1) (tproject2 args1)
    in dmapAccumLDer proxy k accShs bShs eShs
                     (tlambda @target shs (HFun fl))
                     (dfwd @target shs $ HFun fl)
                     (drevDt @target shs $ HFun fl)
                     acc0 es
  dmapAccumLDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy target
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> HFunOf target (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs eShs))
    -> target accShs
    -> target (BuildTensorKind k eShs)
    -> target (TKProduct accShs (BuildTensorKind k bShs))

tunit :: BaseTensor target
      => target TKUnit
tunit = rtoScalar $ rscalar Z0

rscalar :: forall r target. (TensorKind r, BaseTensor target)
        => RepORArray r -> target (TKR2 0 r)
rscalar r | Dict <- eltDictRep (stensorKind @r) =
  let a = Nested.rscalar r
  in tconcrete (tftkG (STKR (SNat @0) (stensorKind @r)) a) (RepN a)

xrepl :: forall sh r target.
         (GoodScalar r, KnownShX sh, BaseTensor target)
      => IShX sh -> r -> target (TKX sh r)
xrepl sh =
  xconcrete . Nested.mreplicateScal sh

-- These are user-accessible, so the constraint is `ADReady`, which means
-- lets, but no shares.
type role HFun nominal nominal
newtype HFun (x :: TensorKindType) (z :: TensorKindType) =
  HFun {unHFun :: forall f. ADReady f
               => f x -> f z}

instance Show (HFun x y) where
  show _ = "<lambda>"


-- * The mega-constraint

type ADReady target =
  ( ADReadyNoLet target
  , LetTensor target
-- The following can't be added, because we have instances like ADVal (AstRaw),
-- so AstRaw would need to have a LetTensor instance:
--  , LetTensor (PrimalOf target)
  )

type ADReadyNoLet target =
  ( ADReadyEqsClasses target
  , ADReadyEqsClasses (ShareOf target)
  , ShareTensor (ShareOf target)
  , ShareTensor (PrimalOf (ShareOf target))
  , ShareOf (ShareOf target) ~ ShareOf target
  )

type ADReadyEqsClasses target =
  ( ADReadyEqs target
  , ADReadyClasses target
  , ADReadyClasses (PrimalOf target)
  )

type ADReadyEqs target =
  ( BoolOf (PrimalOf target) ~ BoolOf target
  )

type ADReadyClasses target =
  ( Boolean (BoolOf target)
  , IfF target
  , EqF target
  , OrdF target
  , BaseTensor target
  , AllTargetShow target
  )

-- This is illegal:
-- type AllTargetShow target = forall y. TensorKind y => Show (target y)

type AllTargetShow :: Target -> Constraint
class (forall y. TensorKind y => Show (target y))
      => AllTargetShow target where
instance
      (forall y. TensorKind y => Show (target y))
      => AllTargetShow target where
