{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | A collection of classes containing array operations,
-- with some extra algebraic operations and dual numbers
-- operations added in.
--
-- Note that @Ast*@ modules rarely depend on @Ops*@ and @Carriers*@ modules
-- (except for "HordeAd.Core.AstInterpret" and "HordeAd.Core.AstEnv"
-- that describe how to go from @Ast*@ to @Ops*@). Similarly, @Ops*@
-- and @Carriers*@ modules rarely depend on @Ast*@ modules
-- (except for "HordeAd.Core.OpsAst" and "HordeAd.Core.CarriersAst"
-- that describe how to define @Ops*@ in terms of @Ast*@).
-- Syntax is relatively separated from semantics and they meet
-- in the interpreter ("HordeAd.Core.AstInterpret")
-- and in the semantic model constructed from syntax ("HordeAd.Core.OpsAst").
--
-- (A copy of the text above is in "HordeAd.Core.Ast".)
module HordeAd.Core.Ops
  ( -- * The tensor classes and support datatypes
    LetTensor(..), ShareTensor(..), BaseTensor(..), HFun(..)
    -- * The giga-constraint
  , ADReady, ADReadyNoLet, ADReadyEqs, ADReadyClasses, ADReadyEqsClasses
  , AllTargetShow, CommonTargetEqOrd
    -- * Helper functions
  , rtr, rflatten, str, sflatten, xtr, xflatten
  , tmapAccumR, tmapAccumL, treplTarget, tdefTarget
    -- * Helper classes and types
  , IntegralHAndIntElt, RealFloatAndFloatElt
  , TensorSupportsX, TensorSupportsS, TensorSupportsR, TensorSupports
  ) where

import Prelude

import Data.Foldable qualified as Foldable
import Data.Kind (Constraint, Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.TypeLits (KnownNat, type (+), type (<=), type (<=?))
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (withShsFromShX)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Init, unsafeCoerceRefl)

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- These user API functions are used in default definitions of methods,
-- so they have to be defined already here:

rtr :: forall n x target. (KnownSTK x, BaseTensor target)
    => target (TKR2 (2 + n) x) -> target (TKR2 (2 + n) x)
rtr = trtranspose [1, 0]
rflatten :: forall n x target. (KnownSTK x, BaseTensor target)
         => target (TKR2 n x) -> target (TKR2 1 x)
rflatten u = trreshape (rsize u :$: ZSR) u
str :: forall n m sh x target. (KnownSTK x, BaseTensor target)
    => target (TKS2 (n ': m ': sh) x) -> target (TKS2 (m ': n ': sh) x)
str = gcastWith (unsafeCoerceRefl :: (2 <=? Rank (n ': m ': sh)) :~: True) $
      tstranspose (Permutation.makePerm @'[1, 0])
sflatten :: (KnownShS sh, KnownSTK x, BaseTensor target )
         => target (TKS2 sh x) -> target (TKS2 '[Product sh] x)
sflatten @sh | SNat <- shsProduct (knownShS @sh) = tsreshape knownShS
xtr :: forall n m sh x target. (KnownSTK x, BaseTensor target)
    => target (TKX2 (Just n ': Just m ': sh) x)
    -> target (TKX2 (Just m ': Just n ': sh) x)
xtr = gcastWith (unsafeCoerceRefl
                 :: (2 <=? Rank (Just n ': Just m ': sh)) :~: True) $
      txtranspose (Permutation.makePerm @'[1, 0])
xflatten :: forall sh x target. (KnownSTK x, BaseTensor target)
         => target (TKX2 sh x) -> target (TKX2 '[Nothing] x)
xflatten u = txreshape (Nested.SUnknown (xsize u) :$% ZSX) u

-- | A strict right mapAccum.
tmapAccumR
  :: forall accy by ey k target. BaseTensor target
  => Proxy target
  -> SNat k  -- ^ length of the input
  -> FullShapeTK accy  -- ^ shape of the accumulator
  -> FullShapeTK by  -- ^ shape of the output
  -> FullShapeTK ey  -- ^ shape of an individual input
  -> (forall f. ADReady f
      => f accy -> f ey -> f (TKProduct accy by))
       -- ^ the function to mapAccum with
  -> target accy  -- ^ the initial accumulator
  -> target (BuildTensorKind k ey)  -- ^ the inputs
  -> target (TKProduct accy (BuildTensorKind k by))
{-# INLINE tmapAccumR #-}  -- this doesn't want to specialize
tmapAccumR proxy !k !accftk !bftk !eftk f acc0 es =
  let xftk = FTKProduct accftk eftk
      fl :: forall f. ADReady f
         => f (TKProduct accy ey)
         -> f (TKProduct accy by)
      fl !args = ttlet args $ \ !args1 ->
                   f (tproject1 args1) (tproject2 args1)
  in tmapAccumRDer proxy k accftk bftk eftk
                   (tlambda @target xftk (HFun fl))
                   (tjvp @target xftk $ HFun fl)
                   (tvjp @target xftk $ HFun fl)
                   acc0 es
-- | A strict left mapAccum.
tmapAccumL
  :: forall accy by ey k target. BaseTensor target
  => Proxy target
  -> SNat k  -- ^ length of the input
  -> FullShapeTK accy  -- ^ shape of the accumulator
  -> FullShapeTK by  -- ^ shape of the output
  -> FullShapeTK ey  -- ^ shape of an individual input
  -> (forall f. ADReady f
      => f accy -> f ey -> f (TKProduct accy by))
       -- ^ the function to mapAccum with
  -> target accy  -- ^ the initial accumulator
  -> target (BuildTensorKind k ey)  -- ^ the inputs
  -> target (TKProduct accy (BuildTensorKind k by))
{-# INLINE tmapAccumL #-}  -- this doesn't want to specialize
tmapAccumL proxy !k !accftk !bftk !eftk f acc0 es =
  let xftk = FTKProduct accftk eftk
      fl :: forall f. ADReady f
         => f (TKProduct accy ey)
         -> f (TKProduct accy by)
      fl !args = ttlet args $ \ !args1 ->
                   f (tproject1 args1) (tproject2 args1)
  in tmapAccumLDer proxy k accftk bftk eftk
                   (tlambda @target xftk (HFun fl))
                   (tjvp @target xftk $ HFun fl)
                   (tvjp @target xftk $ HFun fl)
                   acc0 es

-- | Construct tensors with the given constant in each cell.
treplTarget :: (TKAllNum y, BaseTensor target)
            => (forall r. NumScalar r => r) -> FullShapeTK y -> target y
treplTarget r ftk = tconcrete ftk $ Concrete $ replTargetRep r ftk

-- | Construct tensors with @def@ in each cell.
tdefTarget :: BaseTensor target
           => FullShapeTK y -> target y
tdefTarget ftk = tconcrete ftk $ Concrete $ defTargetRep ftk

type TensorSupports :: (Type -> Constraint) -> (Type -> Constraint)
                    -> Target -> Constraint
type TensorSupports c1 c2 f =
  forall r. NumScalar r
            => c1 r => c2 (f (TKScalar r))

type TensorSupportsR :: (Type -> Constraint) -> (Type -> Constraint)
                     -> Target -> Constraint
type TensorSupportsR c1 c2 f =
  forall r n. NumScalar r
              => c1 r => c2 (f (TKR n r))

type TensorSupportsS :: (Type -> Constraint) -> (Type -> Constraint)
                     -> Target -> Constraint
type TensorSupportsS c1 c2 f =
  forall r sh. NumScalar r
               => c1 r => c2 (f (TKS sh r))

type TensorSupportsX :: (Type -> Constraint) -> (Type -> Constraint)
                     -> Target -> Constraint
type TensorSupportsX c1 c2 f =
  forall r sh. NumScalar r
               => c1 r => c2 (f (TKX sh r))

class (RealFloatH r, Nested.FloatElt r)
      => RealFloatAndFloatElt r
instance (RealFloatH r, Nested.FloatElt r)
         => RealFloatAndFloatElt r

class (IntegralH r, Nested.IntElt r)
      => IntegralHAndIntElt r
instance (IntegralH r, Nested.IntElt r)
      => IntegralHAndIntElt r

class LetTensor (target :: Target) where
  ttlet :: target x -> (target x -> target z) -> target z
  ttletPrimal :: PrimalOf target x -> (PrimalOf target x -> target z)
              -> target z
  ttletPlain :: PlainOf target x -> (PlainOf target x -> target z)
             -> target z
  toShare :: target y -> ShareOf target y
  tunshare :: ShareOf target y -> target y
  tunshare = error "tunshare: this instance should never be used"
  tappend :: forall m n y. BaseTensor target
          => SNat m -> SNat n -> SingletonTK y
          -> target (BuildTensorKind m y) -> target (BuildTensorKind n y)
          -> target (BuildTensorKind (m + n) y)
  tappend msnat@SNat nsnat@SNat stk a b = case stk of
    STKScalar -> tsappend a b
    STKR _ x | Dict <- lemKnownSTK x -> trappend a b
    STKS _ x | Dict <- lemKnownSTK x -> tsappend a b
    STKX _ x | Dict <- lemKnownSTK x -> txappend a b
    STKProduct stk1 stk2 ->
      ttlet a $ \ !aShared -> ttlet b $ \ !bShared ->
        tpair (tappend msnat nsnat stk1 (tproject1 aShared) (tproject1 bShared))
              (tappend msnat nsnat stk2 (tproject2 aShared) (tproject2 bShared))
  tD :: (TKAllNum y, BaseTensor target)
     => SingletonTK y -> PrimalOf target y -> DualOf target y
     -> target y
  tD stk p d =
    -- Lets needed, because taddTarget requires duplicable arguments.
    ttletPrimal p $ \pShared ->
    ttlet (tfromDual d) $ \dShared ->
      taddTarget stk (tfromPrimal stk pShared) dShared
  -- | A strict left fold.
  tfold
    :: forall yn ym k. BaseTensor target
    => SNat k  -- ^ length of the input
    -> SingletonTK yn  -- ^ partial shape of the accumulator
    -> SingletonTK ym  -- ^ partial shape of an individual input
    -> (forall f. ADReady f => f yn -> f ym -> f yn)
         -- ^ the function to fold with
    -> target yn  -- ^ the initial accumulator
    -> target (BuildTensorKind k ym)  -- ^ the inputs
    -> target yn
  {-# INLINE tfold #-}  -- this doesn't want to specialize
  tfold k nstk mstk f acc0 es =
    tproject1
    $ tmapAccumL (Proxy @target)
       k
       (tftk nstk acc0)
       (FTKScalar @Z1)
       (razeFTK k mstk (tftk (buildSTK k mstk) es))
       (let g :: forall f. ADReady f
              => f yn -> f ym -> f (TKProduct yn TKUnit)
            g !acc !e = tpair (f acc e) (tkconcrete Z1)
        in g)
       acc0
       es
  -- | A strict left scan.
  tscan
    :: forall yn ym k. BaseTensor target
    => SNat k  -- ^ length of the input
    -> SingletonTK yn  -- ^ partial shape of the accumulator
    -> SingletonTK ym  -- ^ partial shape of an individual input
    -> (forall f. ADReady f => f yn -> f ym -> f yn)
         -- ^ the function to scan with
    -> target yn  -- ^ the initial accumulator
    -> target (BuildTensorKind k ym)  -- ^ the inputs
    -> target (BuildTensorKind (1 + k) yn)
  {-# INLINE tscan #-}  -- this doesn't want to specialize
  tscan k nstk mstk f acc0 es =
    let bs :: target (BuildTensorKind k yn)
        bs = tproject2
             $ tmapAccumL (Proxy @target)
                k
                (tftk nstk acc0)
                (tftk nstk acc0)
                (razeFTK k mstk (tftk (buildSTK k mstk) es))
              (let g :: forall f. ADReady f
                     => f yn -> f ym -> f (TKProduct yn yn)
                   g !acc !e = ttlet (f acc e) $ \ !res -> tpair res res
               in g)
              acc0
              es
    in tappend (SNat @1) k nstk (tfromList (SNat @1) nstk [acc0]) bs

class ShareTensor (target :: Target) where
  tshare :: target y -> target y
  tunpair :: target (TKProduct x z) -> (target x, target z)
  -- This would suffer from lack of sharing if in LetTensor, because
  -- ttlet doesn't work over a list. With sharing it's fine.
  tunravelToListShare :: forall y k. (BaseTensor target, ConvertTensor target)
                      => SNat k -> SingletonTK y
                      -> target (BuildTensorKind k y)
                      -> [target y]
  tunravelToListShare snat@SNat stk u = case stk of
    STKScalar -> let !uShared = tshare u
                 in tkunravelToList uShared
    STKR SNat x | Dict <- lemKnownSTK x -> let !uShared = tshare u
                                           in trunravelToList uShared
    STKS sh x | Dict <- lemKnownSTK x -> let !uShared = tshare u
                                         in withKnownShS sh
                                            $ tsunravelToList uShared
    STKX sh x | Dict <- lemKnownSTK x -> let !uShared = tshare u
                                         in withKnownShX sh
                                            $ txunravelToList uShared
    STKProduct stk1 stk2 ->
      -- TODO: prevent the proliferation of sharing, maybe via
      -- the unnest (unzip) trick, similarly as in vectorization,
      -- though ox-arrays has two recurseive calls as well
      -- (but not sharing):
      -- mtoListOuter (M_Tup2 a b) =
      --   zipWith M_Tup2 (mtoListOuter a) (mtoListOuter b)
      let (!u1, !u2) = tunpair u
      in zipWith tpair (tunravelToListShare snat stk1 u1)
                       (tunravelToListShare snat stk2 u2)

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Num (IntOf target)
          -- This is not redundant, because it constrains @PrimaOf f@,
          -- not @f@, as below, and so the user doesn't need
          -- to require @ADReady@ instead of @BaseTensor@ as often.
          -- Also, it leads to a choice of the more specific
          -- @Num (ADVal f (TKScalar r))@ instance (in GHC 9.12 at least),
          -- making some more cases of @fromInteger@ usage accepted.
      , TensorSupports Num Num target
      , TensorSupports RealFloatAndFloatElt Floating target
      , TensorSupports RealFloatAndFloatElt RealFloatH target
      , TensorSupports IntegralHAndIntElt IntegralH target
      , TensorSupportsR Num Num target
      , TensorSupportsR RealFloatAndFloatElt Floating target
      , TensorSupportsR RealFloatAndFloatElt RealFloatH target
      , TensorSupportsR IntegralHAndIntElt IntegralH target
      , TensorSupportsS Num Num target
      , TensorSupportsS RealFloatAndFloatElt Floating target
      , TensorSupportsS RealFloatAndFloatElt RealFloatH target
      , TensorSupportsS IntegralHAndIntElt IntegralH target
      , TensorSupportsX Num Num target
      , TensorSupportsX RealFloatAndFloatElt Floating target
      , TensorSupportsX RealFloatAndFloatElt RealFloatH target
      , TensorSupportsX IntegralHAndIntElt IntegralH target )
      => BaseTensor (target :: Target) where

  -- First type argument being @target@ is acceptable here, since these
  -- operations are mostly used when the shape is not known at the type level,
  -- so it can't be used as an explicit type argument.
  rshape :: forall n x. KnownSTK x
         => target (TKR2 n x) -> IShR n
  rlength :: forall n x. KnownSTK x
          => target (TKR2 n x) -> Int
  rlength = shrLength . rshape
  rsize :: forall n x. KnownSTK x
        => target (TKR2 n x) -> Int
  rsize = shrSize . rshape
  rwidth :: forall n x. KnownSTK x
          => target (TKR2 (1 + n) x) -> Int
  rwidth a = case rshape a of
    k :$: _ -> k

  sshape :: forall sh x. KnownSTK x
         => target (TKS2 sh x) -> ShS sh
  slength :: forall sh x. KnownSTK x
          => target (TKS2 sh x) -> Int
  slength = shsLength . sshape
  ssize :: forall sh x. KnownSTK x
        => target (TKS2 sh x) -> Int
  ssize = shsSize . sshape
  swidth :: forall n sh x. KnownSTK x
          => target (TKS2 (n ': sh) x) -> Int
  swidth a = case sshape a of
    n :$$ _ -> sNatValue n

  xshape :: forall sh x. KnownSTK x
         => target (TKX2 sh x) -> IShX sh
  xlength :: forall sh x. KnownSTK x
          => target (TKX2 sh x) -> Int
  xlength = shxLength . xshape
  xsize :: forall sh x. KnownSTK x
        => target (TKX2 sh x) -> Int
  xsize = shxSize . xshape
  xwidth :: forall mn sh x. KnownSTK x
          => target (TKX2 (mn ': sh) x) -> Int
  xwidth a = case xshape a of
    mn :$% _ -> fromSMayNat' mn

  tsize :: SingletonTK y -> target y -> Int
  tsize stk a = case stk of
    STKScalar @r -> case testEquality (typeRep @r) (typeRep @Z1) of
      Just Refl -> 0
      _ -> 1
    STKR _ x | Dict <- lemKnownSTK x -> rsize a
    STKS _ x | Dict <- lemKnownSTK x -> ssize a
    STKX _ x | Dict <- lemKnownSTK x -> xsize a
    STKProduct stk1 stk2 ->
      tsize stk1 (tproject1 a) + tsize stk2 (tproject2 a)
  tftk :: SingletonTK y -> target y -> FullShapeTK y

  -- Unlikely to require type applications at all
  tpair :: target x -> target z -> target (TKProduct x z)
  tproject1 :: target (TKProduct x z) -> target x
  tproject2 :: target (TKProduct x z) -> target z

  -----------
  -- Everything below is indended to be rarely used and usually there are
  -- more specific and/or more convienient functions that do the same job
  -- in other modules.
  -----------------

  -- | The operation is potentially strict in all arguments.
  tcond :: Boolean (BoolOf target)
        => SingletonTK y
        -> BoolOf target -> target y -> target y -> target y

  -- A more precise type would have `PrimalOf target`, but it's require
  -- the user to convert, so we leave that precision to the AST only
  -- which means the AST instance will automatically insert such
  -- conversions as needed. The same holds for trfloor and many others.
  tkconcrete :: GoodScalar r
             => r -> target (TKScalar r)
  trconcrete :: GoodScalar r
             => Nested.Ranked n r -> target (TKR n r)
  tsconcrete :: GoodScalar r
             => Nested.Shaped sh r -> target (TKS sh r)
  txconcrete :: GoodScalar r
             => Nested.Mixed sh r -> target (TKX sh r)
  tconcrete :: FullShapeTK y -> Concrete y -> target y

  tkunravelToList :: forall n r.(KnownNat n, GoodScalar r)
                  => target (TKS '[n] r) -> [target (TKScalar r)]
  tkunravelToList t =
    let f :: Int -> target (TKScalar r)
        f i = tsindex0 t (fromIntegral i :.$ ZIS)
    in map f [0 .. valueOf @n - 1]

  -- The argument is assumed to be a non-empty strict vector:
  trfromVector :: (KnownNat n, KnownSTK x)
               => Data.Vector.Vector (target (TKR2 n x))
               -> target (TKR2 (1 + n) x)
  trfromVector v = withSNat (V.length v) $ \k ->
    tfromVector k (STKR SNat knownSTK) v
  trunravelToList :: (KnownNat n, KnownSTK x)
                  => target (TKR2 (1 + n) x) -> [target (TKR2 n x)]
  trunravelToList @n @x t =
    let f :: Int -> target (TKR2 n x)
        f i = trindex t (fromIntegral i :.: ZIR)
    in map f [0 .. rwidth t - 1]

  tsfromVector :: (KnownNat n, KnownShS sh, KnownSTK x)
               => Data.Vector.Vector (target (TKS2 sh x))
               -> target (TKS2 (n ': sh) x)
  tsfromVector = tfromVector SNat (STKS knownShS knownSTK)
  tsunravelToList :: (KnownNat n, KnownShS sh, KnownSTK x)
                  => target (TKS2 (n ': sh) x) -> [target (TKS2 sh x)]
  tsunravelToList @_ @sh @x t =
    let f :: Int -> target (TKS2 sh x)
        f i = tsindex t (fromIntegral i :.$ ZIS)
    in map f [0 .. swidth t - 1]

  txfromVector :: (KnownNat n, KnownShX sh, KnownSTK x)
               => Data.Vector.Vector (target (TKX2 sh x))
               -> target (TKX2 (Just n ': sh) x)
  txfromVector = tfromVector SNat (STKX knownShX knownSTK)
  txunravelToList :: (KnownNat n, KnownShX sh, KnownSTK x)
                  => target (TKX2 (Just n ': sh) x) -> [target (TKX2 sh x)]
  txunravelToList @_ @sh @x t =
    let f :: Int -> target (TKX2 sh x)
        f i = txindex t (fromIntegral i :.% ZIX)
    in map f [0 .. xwidth t - 1]

  tfromVector :: forall y k.
                 SNat k -> SingletonTK y -> Data.Vector.Vector (target y)
              -> target (BuildTensorKind k y)
  tfromList :: forall y k.
               SNat k -> SingletonTK y -> [target y]
            -> target (BuildTensorKind k y)
  tfromList k stk l = tfromVector k stk $ V.fromListN (sNatValue k) l
  tfromListR :: forall y k.
                SingletonTK y -> ListR k (target y)
             -> target (BuildTensorKind k y)
  tfromListR stk l =
    tfromList (listrRank l) stk  -- not valueOf @k, because k ambiguous
    . Foldable.toList $ l

  -- A number suffix in the name may indicate the rank of the codomain,
  -- if bounded. Suffix 1 may also mean the operations builds up codomain
  -- by 1 dimension.
  trsum :: (KnownNat n, TKAllNum x, KnownSTK x)
        => target (TKR2 (1 + n) x) -> target (TKR2 n x)
  -- This op (and it's Delta constructor) is worthwhile, because flattening
  -- is O(n) sometimes, unlike transpose, etc.
  trsum0 :: (KnownNat n, NumScalar r, ConvertTensor target)
         => target (TKR n r) -> target (TKScalar r)
  trsum0 = kfromR . trsum . rflatten
  trdot0 :: (KnownNat n, NumScalar r, ConvertTensor target)
         => target (TKR n r) -> target (TKR n r) -> target (TKScalar r)
  trdot0 t u = trsum0 (t * u)
  trdot1In :: (KnownNat n, NumScalar r)
           => target (TKR (1 + n) r) -> target (TKR (1 + n) r)
           -> target (TKR n r)
  trdot1In @n t u = trsum $ trtranspose (permCycle $ 1 + valueOf @n) (t * u)
  trmatvecmul :: (NumScalar r, ConvertTensor target)
              => target (TKR 2 r) -> target (TKR 1 r) -> target (TKR 1 r)
-- How to generalize (#69)? The few straightforward generalizations
-- differ in types but all are far from matmul2.
-- rmatvecmul m v = rflatten $ rmap1 (rreplicate 1 . rdot0 v) m
  trmatvecmul m v =
    trbuild1 (rwidth m) (\i -> rfromK $ trdot0 v (m `trindex` [i]))
  trmatmul2 :: (NumScalar r, ConvertTensor target)
            => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
-- How to generalize to tmatmul (#69)?
-- Just rmatmul2 the two outermost dimensions?
-- rmatmul2 m1 m2 = rmap1 (rmatvecmul (rtr m2)) m1
  trmatmul2 m1 m2 =
    trbuild1 (rwidth m1) (\i -> trmatvecmul (rtr m2) (m1 `trindex` [i]))
  trreplicate :: (KnownNat n, KnownSTK x)
              => Int -> target (TKR2 n x) -> target (TKR2 (1 + n) x)
  trreplicate0N :: (KnownNat n, KnownSTK x)
                => IShR n -> target (TKR2 0 x) -> target (TKR2 n x)
  trreplicate0N sh = trreshape sh . trreplicate (shrSize sh)

  tssum :: (KnownNat n, KnownShS sh, TKAllNum x, KnownSTK x)
        => target (TKS2 (n ': sh) x) -> target (TKS2 sh x)
  tssum0 :: (KnownShS sh, NumScalar r, ConvertTensor target)
         => target (TKS sh r) -> target (TKScalar r)
  tssum0 @sh | SNat <- shsProduct (knownShS @sh) =
    kfromS . tssum . sflatten
  tsdot0 :: (KnownShS sh, NumScalar r, ConvertTensor target)
         => target (TKS sh r) -> target (TKS sh r) -> target (TKScalar r)
  tsdot0 @sh t u | SNat <- shsProduct (knownShS @sh) =
    tssum0 (t * u)
  tsdot1In :: (KnownShS sh, NumScalar r)
           => SNat n -> target (TKS (sh ++ '[n]) r)
           -> target (TKS (sh ++ '[n]) r)
           -> target (TKS sh r)
  tsdot1In @sh (SNat @n) t u =
    let cpermR = permCycle $ 1 + shsLength (knownShS @sh)
    in Permutation.permFromListCont cpermR $ \(cperm :: Permutation.Perm cperm) ->
         gcastWith (unsafeCoerceRefl :: Rank cperm :~: Rank (sh ++ '[n])) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix cperm (sh ++ '[n])
                       :~: n : sh) $
         fromMaybe (error "tsdot1In: impossible non-permutation")
         $ Permutation.permCheckPermutation cperm
         $ tssum $ tstranspose cperm (t * u)
  tsmatvecmul :: (KnownNat m, KnownNat n, NumScalar r, ConvertTensor target)
              => target (TKS '[m, n] r) -> target (TKS '[n] r)
              -> target (TKS '[m] r)
  tsmatvecmul @m m v =
    tkbuild1 @_ @m (\i -> tsdot0 v (m `tsindex` (i :.$ ZIS)))
  tsmatmul2 :: ( KnownNat m, KnownNat n, KnownNat p, NumScalar r
               , ConvertTensor target )
            => target (TKS '[m, n] r) -> target (TKS '[n, p] r)
            -> target (TKS '[m, p] r)
  tsmatmul2 @m m1 m2 =
    tsbuild1 @_ @m (\i -> tsmatvecmul (str m2) (m1 `tsindex` (i :.$ ZIS)))
  tsreplicate :: forall sh k x. KnownSTK x
              => SNat k -> ShS sh -> target (TKS2 sh x)
              -> target (TKS2 (k ': sh) x)
  tsreplicate0N :: forall sh x. KnownSTK x
                => ShS sh -> target (TKS2 '[] x)
                -> target (TKS2 sh x)
  tsreplicate0N sh = tsreshape sh . tsreplicate (shsProduct sh) ZSS

  -- The choice in BuildTensorKind makes it hard to support this one,
  -- due to DeltaSum and AstSum being typed with BuildTensorKind:
  -- xsum :: (KnownShX sh, KnownShX (mn ': sh), KnownSTK x)
  --     => target (TKX2 (mn ': sh) x) -> target (TKX2 sh x)
  txsum :: (KnownNat n, KnownShX sh, TKAllNum x, KnownSTK x)
        => target (TKX2 (Just n ': sh) x) -> target (TKX2 sh x)
  txsum0 :: (KnownShX sh, NumScalar r, ConvertTensor target)
         => target (TKX sh r) -> target (TKScalar r)
  txsum0 t = withSNat (shxSize $ xshape t) $ \snat ->
    kfromX $ txsum (xmcast (Nested.SKnown snat :!% ZKX) $ xflatten t)
  txdot0 :: (KnownShX sh, NumScalar r, ConvertTensor target)
         => target (TKX sh r) -> target (TKX sh r) -> target (TKScalar r)
  txdot0 t u = txsum0 (t * u)
  txdot1In :: (KnownShX sh, NumScalar r)
           => SNat n -> target (TKX (sh ++ '[Just n]) r)
           -> target (TKX (sh ++ '[Just n]) r)
           -> target (TKX sh r)
  txdot1In @sh (SNat @n) t u =
    let cpermR = permCycle $ 1 + sNatValue (ssxRank (knownShX @sh))
    in Permutation.permFromListCont cpermR $ \(cperm :: Permutation.Perm cperm) ->
         gcastWith (unsafeCoerceRefl :: Rank cperm :~: Rank (sh ++ '[Just n])) $
         gcastWith (unsafeCoerceRefl
                    :: Permutation.PermutePrefix cperm (sh ++ '[Just n])
                       :~: Just n : sh) $
         fromMaybe (error "txdot1In: impossible non-permutation")
         $ Permutation.permCheckPermutation cperm
         $ txsum $ txtranspose cperm (t * u)
  txmatvecmul :: forall mm mn r.
                 (NumScalar r, ConvertTensor target)
              => Nested.SMayNat Int SNat mm -> Nested.SMayNat Int SNat mn
              -> target (TKX '[mm, mn] r) -> target (TKX '[mn] r)
              -> target (TKX '[mm] r)
  txmatvecmul mm mn m v =
    withKnownShX (ssxFromShX $ mm :$% ZSX) $
    withKnownShX (ssxFromShX $ mn :$% ZSX) $
    withSNat (fromSMayNat' mm) $ \(SNat @k) ->
      xmcast (ssxFromShX $ mm :$% ZSX)
      $ txbuild1 @_ @k (\i -> xfromK $ txdot0 v (m `txindex` (i :.% ZIX)))
  txmatmul2 :: ( KnownNat m, KnownNat n, KnownNat p
               , NumScalar r, ConvertTensor target )
            => target (TKX '[Just m, Just n] r)
            -> target (TKX '[Just n, Just p] r)
            -> target (TKX '[Just m, Just p] r)
  txmatmul2 @m @n @p m1 m2 =
    txbuild1 @_ @m (\i ->
      txmatvecmul (Nested.SKnown (SNat @p)) (Nested.SKnown (SNat @n))
                  (xtr m2) (m1 `txindex` (i :.% ZIX)))
  txreplicate :: forall sh k x. KnownSTK x
              => SNat k -> StaticShX sh -> target (TKX2 sh x)
              -> target (TKX2 (Just k ': sh) x)
  txreplicate0N :: (KnownShX sh, KnownSTK x)
                => IShX sh -> target (TKX2 '[] x) -> target (TKX2 sh x)
  txreplicate0N sh = withSNat (shxSize sh) $ \snat ->
    txreshape sh . txreplicate snat knownShX

  trindex :: (KnownNat m, KnownNat n, KnownSTK x)
          => target (TKR2 (m + n) x) -> IxROf target m -> target (TKR2 n x)
  trindex0 :: (KnownNat m, GoodScalar r)
           => target (TKR m r) -> IxROf target m -> target (TKScalar r)
  troneHot :: ( KnownNat m, KnownNat n, TKAllNum x, KnownSTK x
              , PlainOf (PlainOf target) ~ PlainOf target
              , EqH (PlainOf target) (TKScalar Int))
           => IShR m -> target (TKR2 n x) -> IxROf target m
           -> target (TKR2 (m + n) x)
  {-# INLINE troneHot #-}
  troneHot sh v ix =
    trscatter @_ @0 (shrAppend sh (rshape v)) v (const ix)
      -- this code is often better for differentiable contexts, because
      -- a gather results, though this code is problematic if vectorization
      -- blows up the dimensions
    {- _ ->
      -- TODO: def at out of bounds and handle empty arrays
      let f ix2 = tcond knownSTK
                        (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                         $ zip (Foldable.toList ix) (Foldable.toList ix2))
                        v
                        (tdefTarget (tftk knownSTK v))
      in trbuild (shrAppend sh (rshape v)) f
        -- this code is probably better for non-differentiable contexts
        -- (even though it seems to do more work than the scatter above),
        -- because this code vectorizes better, often to the same size gather
        -- TODO: so maybe check if all scalars in v are non-differentiable
        -- and choose this if so?
        -- TODO: if this is used often, maybe express this as the gather that
        -- would come out of vectorization, to help it simplify well -}
  trscatter :: (KnownNat m, KnownNat n, KnownNat p, TKAllNum x, KnownSTK x)
            => IShR (p + n) -> target (TKR2 (m + n) x)
            -> (IxROf target m -> IxROf target p)
            -> target (TKR2 (p + n) x)
  trscatter1 :: (KnownNat n, KnownNat p, TKAllNum x, KnownSTK x)
             => IShR (p + n) -> target (TKR2 (1 + n) x)
             -> (IntOf target -> IxROf target p)
             -> target (TKR2 (p + n) x)
  {-# INLINE trscatter1 #-}
  trscatter1 sh v f = trscatter @target @1 sh v (\(i :.: ZIR) -> f i)
  trgather :: (KnownNat m, KnownNat n, KnownNat p, KnownSTK x)
           => IShR (m + n) -> target (TKR2 (p + n) x)
           -> (IxROf target m -> IxROf target p)
           -> target (TKR2 (m + n) x)
  trgather1 :: (KnownNat n, KnownNat p, KnownSTK x)
            => Int -> target (TKR2 (p + n) x)
            -> (IntOf target -> IxROf target p)
            -> target (TKR2 (1 + n) x)
  {-# INLINE trgather1 #-}
  trgather1 k v f = trgather @target @1
                             (k :$: shrDrop (rshape v)) v
                             (\(i :.: ZIR) -> f i)

  tsindex :: (KnownShS shm, KnownShS shn, KnownSTK x)
          => target (TKS2 (shm ++ shn) x) -> IxSOf target shm
          -> target (TKS2 shn x)
  tsindex0 :: (KnownShS sh1, GoodScalar r)
           => target (TKS sh1 r) -> IxSOf target sh1 -> target (TKScalar r)
  tsoneHot :: ( KnownShS sh1, KnownShS sh2, TKAllNum x, KnownSTK x
              , PlainOf (PlainOf target) ~ PlainOf target
              , EqH (PlainOf target) (TKScalar Int) )
           => target (TKS2 sh2 x) -> IxSOf target sh1
           -> target (TKS2 (sh1 ++ sh2) x)
  {-# INLINE tsoneHot #-}  -- this doesn't want to specialize
  tsoneHot v ix =
    tsscatter @_ @'[] v (const ix)
    {- _ | SNat <- shsRank (knownShS @sh1)
         , Refl <- lemAppNil @sh2 ->
      -- TODO: def at out of bounds and handle empty arrays
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
      gcastWith (unsafeCoerceRefl :: Take (Rank sh1) (sh1 ++ sh2) :~: sh1) $
      withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
      case shsRank (knownShS @(sh1 ++ sh2)) of
        SNat -> -- needed only for GHC 9.10
          let f ix2 = tcond knownSTK
                            (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                             $ zip (Foldable.toList ix) (Foldable.toList ix2))
                            v
                            (tdefTarget (tftk knownSTK v))
          in tsbuild @_ @(Rank sh1) SNat f -}
  tsscatter
     :: (KnownShS shm, KnownShS shn, KnownShS shp, TKAllNum x, KnownSTK x)
     => target (TKS2 (shm ++ shn) x)
     -> (IxSOf target shm -> IxSOf target shp)
     -> target (TKS2 (shp ++ shn) x)
  tsscatter1
     :: (KnownNat n2, KnownShS shn, KnownShS shp, TKAllNum x, KnownSTK x)
     => target (TKS2 (n2 ': shn) x)
     -> (IntOf target -> IxSOf target shp)
     -> target (TKS2 (shp ++ shn) x)
  {-# INLINE tsscatter1 #-}
  tsscatter1 @n2 v f = tsscatter @_ @'[n2] v (\(i :.$ _) -> f i)
  tsgather
     :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x)
     => target (TKS2 (shp ++ shn) x)
     -> (IxSOf target shm -> IxSOf target shp)
     -> target (TKS2 (shm ++ shn) x)
  tsgather1
     :: (KnownNat n2, KnownShS shn, KnownShS shp, KnownSTK x)
     => target (TKS2 (shp ++ shn) x)
     -> (IntOf target -> IxSOf target shp)
     -> target (TKS2 (n2 ': shn) x)
  {-# INLINE tsgather1 #-}
  tsgather1 @n2 v f = tsgather @target @'[n2] v (\(i :.$ _) -> f i)

  txindex :: (KnownShX sh1, KnownShX sh2, KnownSTK x)
          => target (TKX2 (sh1 ++ sh2) x) -> IxXOf target sh1
          -> target (TKX2 sh2 x)
  txindex0 :: (KnownShX sh1, GoodScalar r)
           => target (TKX sh1 r) -> IxXOf target sh1 -> target (TKScalar r)
  txoneHot :: ( KnownShX sh1, KnownShX sh2, TKAllNum x, KnownSTK x
              , PlainOf (PlainOf target) ~ PlainOf target
              , EqH (PlainOf target) (TKScalar Int), ConvertTensor target )
           => IShX sh1 -> target (TKX2 sh2 x) -> IxXOf target sh1
           -> target (TKX2 (sh1 ++ sh2) x)
  {-# INLINE txoneHot #-}
  txoneHot sh1 v ix =
    txscatter @_ @'[] (shxAppend sh1 (xshape v)) v (const ix)
    {- _ | SNat <- ssxRank (knownShX @sh1)
         , Refl <- lemAppNil @sh2 ->
      -- TODO: def at out of bounds and handle empty arrays
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
      gcastWith (unsafeCoerceRefl :: Take (Rank sh1) (sh1 ++ sh2) :~: sh1) $
      withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
      case ssxRank (knownShX @(sh1 ++ sh2)) of
        SNat -> -- needed only for GHC 9.10
          let f ix2 = tcond knownSTK
                            (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                             $ zip (Foldable.toList ix) (Foldable.toList ix2))
                            v
                            (tdefTarget (tftk knownSTK v))
          in txbuild @_ @(Rank sh1) SNat (shxAppend sh1 (xshape v)) f -}
  txscatter :: ( KnownShX shm, KnownShX shn, KnownShX shp
               , TKAllNum x, KnownSTK x )
            => IShX (shp ++ shn) -> target (TKX2 (shm ++ shn) x)
            -> (IxXOf target shm -> IxXOf target shp)
            -> target (TKX2 (shp ++ shn) x)
  -- TODO: generalize this to non-Just types.
  txscatter1 :: ( KnownNat n2, KnownShX shn, KnownShX shp
                , TKAllNum x, KnownSTK x )
             => IShX (shp ++ shn) -> target (TKX2 (Just n2 ': shn) x)
             -> (IntOf target -> IxXOf target shp)
             -> target (TKX2 (shp ++ shn) x)
  {-# INLINE txscatter1 #-}
  txscatter1 @n2 @_ @shp @x sh v f = txscatter @_ @'[Just n2] @_ @shp @x sh v
                                               (\(i :.% _) -> f i)
  txgather :: (KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x)
           => IShX (shm ++ shn)
           -> target (TKX2 (shp ++ shn) x)
           -> (IxXOf target shm -> IxXOf target shp)
           -> target (TKX2 (shm ++ shn) x)
  txgather1 :: (KnownNat n2, KnownShX shn, KnownShX shp, KnownSTK x)
            => SNat n2 -> target (TKX2 (shp ++ shn) x)
            -> (IntOf target -> IxXOf target shp)
            -> target (TKX2 (Just n2 ': shn) x)
  {-# INLINE txgather1 #-}
  txgather1 @n2 @_ @shp k v f =
    txgather @target @'[Just n2]
             (Nested.SKnown k :$% shxDropSSX (knownShX @shp) (xshape v)) v
             (\(i :.% ZIX) -> f i)

  tkfloor :: (GoodScalar r, RealFrac r, NumScalar r2, Integral r2)
          => target (TKScalar r) -> target (TKScalar r2)
  tkfromIntegral :: (GoodScalar r1, Integral r1, NumScalar r2)
                 => target (TKScalar r1) -> target (TKScalar r2)
  tkcast :: (RealFrac r1, NumScalar r1, RealFrac r2, NumScalar r2)
         => target (TKScalar r1) -> target (TKScalar r2)

  trfloor :: (GoodScalar r, RealFrac r, NumScalar r2, Integral r2)
          => target (TKR n r) -> target (TKR n r2)
  trfromIntegral :: (GoodScalar r1, Integral r1, NumScalar r2)
                 => target (TKR n r1) -> target (TKR n r2)
  trcast :: (RealFrac r1, NumScalar r1, RealFrac r2, NumScalar r2)
         => target (TKR n r1) -> target (TKR n r2)
  trminIndex, trmaxIndex  -- partial
    :: forall n r r2. (NumScalar r, NumScalar r2)
    => target (TKR (1 + n) r) -> target (TKR n r2)
  triota :: NumScalar r => Int -> target (TKR 1 r)  -- from 0 to n - 1

  tsfloor :: (GoodScalar r, RealFrac r, NumScalar r2, Integral r2)
          => target (TKS sh r) -> target (TKS sh r2)
  tsfromIntegral :: (GoodScalar r1, Integral r1, NumScalar r2)
                 => target (TKS sh r1) -> target (TKS sh r2)
  tscast :: (RealFrac r1, NumScalar r1, RealFrac r2, NumScalar r2)
         => target (TKS sh r1) -> target (TKS sh r2)
  tsminIndex, tsmaxIndex  -- partial
    :: forall n sh r r2. (NumScalar r, NumScalar r2)
    => target (TKS (n ': sh) r) -> target (TKS (Init (n ': sh)) r2)
  tsiota :: (KnownNat n, NumScalar r)
         => target (TKS '[n] r)  -- from 0 to n - 1

  txfloor :: (GoodScalar r, RealFrac r, NumScalar r2, Integral r2)
          => target (TKX sh r) -> target (TKX sh r2)
  txfromIntegral :: (GoodScalar r1, Integral r1, NumScalar r2)
                 => target (TKX sh r1) -> target (TKX sh r2)
  txcast :: (RealFrac r1, NumScalar r1, RealFrac r2, NumScalar r2)
         => target (TKX sh r1) -> target (TKX sh r2)
  txminIndex, txmaxIndex  -- partial
    :: forall mn sh r r2. (NumScalar r, NumScalar r2)
    => target (TKX (mn ': sh) r) -> target (TKX (Init (mn ': sh)) r2)
  txiota :: (KnownNat n, NumScalar r)
         => target (TKX '[Just n] r)  -- from 0 to n - 1

  trappend :: forall n x. KnownSTK x
           => target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
           -> target (TKR2 (1 + n) x)
  trslice :: forall n x. KnownSTK x
          => Int -> Int -> target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
  trreverse :: forall n x. KnownSTK x
            => target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
  trtranspose :: forall n x. KnownSTK x
              => Permutation.PermR -> target (TKR2 n x) -> target (TKR2 n x)
  trreshape :: forall n m x. KnownSTK x
            => IShR m -> target (TKR2 n x) -> target (TKR2 m x)

  tsappend :: forall m n sh x. KnownSTK x
           => target (TKS2 (m ': sh) x) -> target (TKS2 (n ': sh) x)
           -> target (TKS2 ((m + n) ': sh) x)
  tsslice :: forall i n k sh x. KnownSTK x
          => SNat i -> SNat n -> SNat k
          -> target (TKS2 (i + n + k ': sh) x) -> target (TKS2 (n ': sh) x)
  tsreverse :: forall n sh x. KnownSTK x
            => target (TKS2 (n ': sh) x) -> target (TKS2 (n ': sh) x)
  tstranspose :: ( Permutation.IsPermutation perm
                 , Rank perm <= Rank sh, KnownSTK x )
              => Permutation.Perm perm -> target (TKS2 sh x)
              -> target (TKS2 (Permutation.PermutePrefix perm sh) x)
  tsreshape :: (Product sh ~ Product sh2, KnownSTK x)
            => ShS sh2 -> target (TKS2 sh x) -> target (TKS2 sh2 x)

  txappend :: forall m n sh x. KnownSTK x
           => target (TKX2 (Just m ': sh) x) -> target (TKX2 (Just n ': sh) x)
           -> target (TKX2 (Just (m + n) ': sh) x)
  txslice :: forall i n k sh x. KnownSTK x
          => SNat i -> SNat n -> SNat k
          -> target (TKX2 (Just (i + n + k) ': sh) x)
          -> target (TKX2 (Just n ': sh) x)
  txreverse :: forall mn sh x. KnownSTK x
            => target (TKX2 (mn ': sh) x) -> target (TKX2 (mn ': sh) x)
  txtranspose :: ( Permutation.IsPermutation perm
                 , Rank perm <= Rank sh, KnownSTK x )
              => Permutation.Perm perm -> target (TKX2 sh x)
              -> target (TKX2 (Permutation.PermutePrefix perm sh) x)
  txreshape :: forall sh sh2 x. KnownSTK x
            => IShX sh2 -> target (TKX2 sh x) -> target (TKX2 sh2 x)

  tkbuild1 :: (KnownNat k, GoodScalar r)
           => (IntOf target -> target (TKScalar r))
           -> target (TKS '[k] r)
  tkbuild :: (KnownShS sh, GoodScalar r, ConvertTensor target)
          => (IxSOf target sh -> target (TKScalar r))
          -> target (TKS sh r)
  {-# INLINE tkbuild #-}
  tkbuild @sh @r =
    gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[]) $
    let buildSh
          :: forall sh1.
             ShS sh1
          -> (IxSOf target sh1 -> target (TKScalar r))
          -> target (TKS sh1 r)
        buildSh sh1 f = case sh1 of
          ZSS -> sfromK $ f ZIS
          SNat :$$ ZSS ->
            tkbuild1 (\i -> f (i :.$ ZIS))
          SNat :$$ sh2 ->
            withKnownShS sh2 $
            let g i = buildSh sh2 (f . (i :.$))
            in tsbuild1 g
    in buildSh (knownShS @sh)
  trbuild1 :: (KnownNat n, KnownSTK x)
           => Int -> (IntOf target -> target (TKR2 n x))
           -> target (TKR2 (1 + n) x)
  trbuild :: (KnownNat m, KnownNat n, KnownSTK x)
          => IShR (m + n)
          -> (IxROf target m -> target (TKR2 n x))
          -> target (TKR2 (m + n) x)
  {-# INLINE trbuild #-}
  trbuild @m @n @x sh0 f0 =
    let buildSh :: IShR m1 -> (IxROf target m1 -> target (TKR2 n x))
                -> target (TKR2 (m1 + n) x)
        buildSh ZSR f = f ZIR
        buildSh (k :$: sh) f | SNat <- shrRank sh =
          let g i = buildSh sh (\ix -> f (i :.: ix))
          in trbuild1 k g
    in buildSh (shrTake @m @n sh0) f0
  trmap0N :: (KnownNat n, GoodScalar r1, GoodScalar r, ConvertTensor target)
          => (target (TKScalar r1) -> target (TKScalar r)) -> target (TKR n r1)
          -> target (TKR n r)
  {-# INLINE trmap0N #-}
  trmap0N f v = trbuild (rshape v) (rfromK . f . trindex0 v)
  trzipWith0N :: ( KnownNat n, GoodScalar r, GoodScalar r1, GoodScalar r2
                 , ConvertTensor target )
              => (target (TKScalar r1) -> target (TKScalar r2)
                  -> target (TKScalar r))
              -> target (TKR n r1) -> target (TKR n r2) -> target (TKR n r)
  {-# INLINE trzipWith0N #-}
  trzipWith0N f u v =
    trbuild (rshape v) (\ix -> rfromK $ f (trindex0 u ix) (trindex0 v ix))

  tsbuild1 :: (KnownNat k, KnownShS sh, KnownSTK x)
           => (IntOf target -> target (TKS2 sh x))
           -> target (TKS2 (k ': sh) x)
  tsbuild :: ( KnownShS (Take m sh), KnownShS (Drop m sh), KnownShS sh
             , KnownSTK x )  -- needed only for GHC 9.10
          => SNat m -- needed only for GHC 9.10
          -> (IxSOf target (Take m sh) -> target (TKS2 (Drop m sh) x))
          -> target (TKS2 sh x)
  {-# INLINE tsbuild #-}
  tsbuild @m @sh @x SNat =
    let buildSh
          :: forall sh1.
             ShS sh1 -> ShS (sh1 ++ Drop m sh)
          -> (IxSOf target sh1 -> target (TKS2 (Drop m sh) x))
          -> target (TKS2 (sh1 ++ Drop m sh) x)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSS, _) -> f ZIS
          (SNat :$$ sh2, _ :$$ sh2m) ->
            withKnownShS sh2m $
            let g i = buildSh sh2 sh2m (f . (i :.$))
            in tsbuild1 g
    in gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh)
       $ buildSh (knownShS @(Take m sh)) (knownShS @sh)
  tsmap0N :: (KnownShS sh, GoodScalar r1, GoodScalar r, ConvertTensor target)
          => (target (TKScalar r1) -> target (TKScalar r))
          -> target (TKS sh r1)
          -> target (TKS sh r)
  {-# INLINE tsmap0N #-}
  tsmap0N @sh f v | Refl <- lemAppNil @sh =
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[]) $
    gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh) $
    case shsRank (knownShS @sh) of  -- needed only for GHC 9.10
      SNat -> tkbuild (f . tsindex0 v)
  tszipWith0N :: ( KnownShS sh, GoodScalar r, GoodScalar r1, GoodScalar r2
                 , ConvertTensor target )
              => (target (TKScalar r1) -> target (TKScalar r2)
                  -> target (TKScalar r))
              -> target (TKS sh r1) -> target (TKS sh r2)
              -> target (TKS sh r)
  {-# INLINE tszipWith0N #-}
  tszipWith0N @sh f u v | Refl <- lemAppNil @sh =
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[]) $
    gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh) $
    case shsRank (knownShS @sh) of  -- needed only for GHC 9.10
      SNat ->
        tkbuild (\ix -> f (tsindex0 u ix) (tsindex0 v ix))

  txbuild1 :: (KnownNat k, KnownShX sh, KnownSTK x)
           => (IntOf target -> target (TKX2 sh x))
           -> target (TKX2 (Just k ': sh) x)

  txbuild :: ( KnownShX (Take m sh), KnownShX (Drop m sh), KnownSTK x
             , ConvertTensor target)
          => SNat m -- needed only for GHC 9.10
          -> IShX sh
          -> (IxXOf target (Take m sh) -> target (TKX2 (Drop m sh) x))
          -> target (TKX2 sh x)
  {-# INLINE txbuild #-}
  txbuild @m @sh @x SNat sh0 f0 =
    let buildSh :: IShX sh1 -> IShX (sh1 ++ Drop m sh)
                -> (IxXOf target sh1 -> target (TKX2 (Drop m sh) x))
                -> target (TKX2 (sh1 ++ Drop m sh) x)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSX, _) -> f ZIX
          (k :$% sh2, _ :$% sh2m) ->
            withKnownShX (ssxFromShX sh2m) $
            let g i = buildSh sh2 sh2m (f . (i :.%))
            in withSNat (fromSMayNat' k) $ \(SNat @n) ->
                 xmcast (ssxFromShX sh1m) $ txbuild1 @_ @n g
    in gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh)
       $ buildSh (shxTakeSSX (Proxy @(Drop m sh))
                 (knownShX @(Take m sh)) sh0) sh0 f0
  tbuild1 :: forall y k. ConvertTensor target
               -- y comes first, because k easy to set via SNat
          => SNat k -> SingletonTK y -> (IntOf target -> target y)
          -> target (BuildTensorKind k y)
  {-# INLINE tbuild1 #-}
  tbuild1 snat@SNat stk0 f =
    let replSTK :: SingletonTK z -> (IntOf target -> target z)
                -> target (BuildTensorKind k z)
        replSTK stk g = case stk of
          STKScalar -> tkbuild1 g
          STKR SNat x | Dict <- lemKnownSTK x -> trbuild1 (sNatValue snat) g
          STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tsbuild1 g
          STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txbuild1 g
          STKProduct @z1 @z2 stk1 stk2 ->
              let f1 i = tproject1 @_ @z1 @z2 $ g i
                  f2 i = tproject2 @_ @z1 @z2 $ g i
                    -- TODO: looks expensive, but hard to do better,
                    -- so let's hope g is full of variables
              in tpair (replSTK stk1 f1) (replSTK stk2 f2)
    in replSTK stk0 f

  -- | A strict right mapAccum.
  --
  -- The applications of 'tjvp' and 'tvjp' performed already at this point
  -- ensure that the computation of a derivative is not repeated
  -- and that its result is shared. However, most of the time
  -- the computation is unnneeded, so the AST instance uses a non-strict
  -- constructor 'HordeAd.Core.Ast.AstLambda' for it's instance of 'HFunOf'.
  --
  -- If the same argument functions are passed to many mapAccum calls, as in
  -- > let f = ... in ... (tmapAccumR ... f ...) ... (tmapAccumL ... f ...)
  -- extra care is needed to prevent double derivative computation.
  -- One needs to use tmapAccumRDer manually as in (simplified)
  -- > let f = ...; df = tjvp f; rf = tgrad f
  -- > in ... (tmapAccumRDer f df rf ...) ... (tmapAccumLDer f df rf ...)
  tmapAccumRDer
    :: forall accy by ey k.
       Proxy target
    -> SNat k  -- ^ length of the input
    -> FullShapeTK accy  -- ^ shape of the accumulator
    -> FullShapeTK by  -- ^ shape of the output
    -> FullShapeTK ey  -- ^ shape of an individual input
    -> HFunOf target (TKProduct accy ey) (TKProduct accy by)
         -- ^ the function to mapAccum with
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accy ey))
                                (TKProduct accy ey))
                     (ADTensorKind (TKProduct accy by))
         -- ^ the derivative of the function to mapAccum with
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accy by))
                                (TKProduct accy ey))
                     (ADTensorKind (TKProduct accy ey))
         -- ^ the reverse derivative of the function to mapAccum with
    -> target accy  -- ^ the initial accumulator
    -> target (BuildTensorKind k ey)  -- ^ the inputs
    -> target (TKProduct accy (BuildTensorKind k by))
  -- | A strict left mapAccum.
  tmapAccumLDer
    :: forall accy by ey k.
       Proxy target
    -> SNat k  -- ^ length of the input
    -> FullShapeTK accy  -- ^ shape of the accumulator
    -> FullShapeTK by  -- ^ shape of the output
    -> FullShapeTK ey  -- ^ shape of an individual input
    -> HFunOf target (TKProduct accy ey) (TKProduct accy by)
         -- ^ the function to mapAccum with
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accy ey))
                                (TKProduct accy ey))
                     (ADTensorKind (TKProduct accy by))
         -- ^ the derivative of the function to mapAccum with
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accy by))
                                (TKProduct accy ey))
                     (ADTensorKind (TKProduct accy ey))
         -- ^ the reverse derivative of the function to mapAccum with
    -> target accy  -- ^ the initial accumulator
    -> target (BuildTensorKind k ey)  -- ^ the inputs
    -> target (TKProduct accy (BuildTensorKind k by))
  tapply :: HFunOf target x z -> target x -> target z
  tlambda :: FullShapeTK x -> HFun x z -> HFunOf target x z

  -- | Reverse derivative.
  --
  -- The followign methods (and tlambda) are exactly what is needed as arguments
  -- of tmapAccumRDer.
  tgrad
    :: forall x r. GoodScalar r
    => FullShapeTK x  -- ^ shape of x and dx
    -> HFun x (TKScalar r)  -- ^ x |-> TKScalar r
    -> HFunOf target x (ADTensorKind x)  -- ^ x |-> dx
  tvjp
    :: FullShapeTK x  -- ^ shape of x and dx
    -> HFun x z  -- ^ x |-> z
    -> HFunOf target (TKProduct (ADTensorKind z) x) (ADTensorKind x)
         -- ^ (dz, x) |-> dx
  tjvp
    :: FullShapeTK x  -- ^ shape of x and dx
    -> HFun x z  -- ^ x |-> z
    -> HFunOf target (TKProduct (ADTensorKind x) x) (ADTensorKind z)
         -- ^ (dx, x) |-> dz

  tprimalPart :: target y -> PrimalOf target y
  tdualPart :: SingletonTK y -> target y -> DualOf target y
  tplainPart :: target y -> PlainOf target y
  tfromPrimal :: SingletonTK y -> PrimalOf target y -> target y
  tfromDual :: DualOf target y -> target y
  tfromPlain :: SingletonTK y -> PlainOf target y -> target y
  tScale :: (Num (target y), Num (PrimalOf target y))
         => SingletonTK y -> PrimalOf target y -> DualOf target y
         -> DualOf target y
  tScale stk s t =
    tdualPart stk $ tfromPrimal @target stk s * tfromDual t

  -- General operations that use ShareTensor if available, LetTensor otherwise
  tsum
    :: forall z k. (ConvertTensor target, TKAllNum z)
    => SNat k -> SingletonTK z -> target (BuildTensorKind k z)
    -> target z
  default tsum
    :: forall z k. (ShareTensor target, ConvertTensor target, TKAllNum z)
    => SNat k -> SingletonTK z -> target (BuildTensorKind k z)
    -> target z
  tsum snat@SNat stk u = case stk of
    STKScalar -> kfromS $ tssum u
    STKR SNat x | Dict <- lemKnownSTK x -> trsum u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tssum u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txsum u
    STKProduct stk1 stk2 ->
      let (u1, u2) = tunpair u
      in tpair (tsum snat stk1 u1)
               (tsum snat stk2 u2)
  treplicate
    :: forall z k. ConvertTensor target
    => SNat k -> SingletonTK z -> target z
    -> target (BuildTensorKind k z)
  default treplicate
    :: forall z k. (ShareTensor target, ConvertTensor target)
    => SNat k -> SingletonTK z -> target z
    -> target (BuildTensorKind k z)
  treplicate snat@SNat stk u = case stk of
    STKScalar -> tsreplicate snat ZSS $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> trreplicate (sNatValue snat) u
    STKS sh x | Dict <- lemKnownSTK x -> tsreplicate snat sh u
    STKX sh x | Dict <- lemKnownSTK x -> txreplicate snat sh u
    STKProduct stk1 stk2 ->
      let (u1, u2) = tunpair u
      in tpair (treplicate snat stk1 u1)
               (treplicate snat stk2 u2)
  tindexBuild
    :: forall z k. ConvertTensor target
    => SNat k -> SingletonTK z -> target (BuildTensorKind k z) -> IntOf target
    -> target z
  default tindexBuild
    :: forall z k. (ShareTensor target, ConvertTensor target)
    => SNat k -> SingletonTK z -> target (BuildTensorKind k z) -> IntOf target
    -> target z
  tindexBuild snat@SNat stk u i = case stk of
    STKScalar -> kfromS $ tsindex u (i :.$ ZIS)
    STKR SNat x | Dict <- lemKnownSTK x -> trindex u (i :.: ZIR)
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tsindex u (i :.$ ZIS)
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txindex u (i :.% ZIX)
    STKProduct stk1 stk2 ->
      let (u1, u2) = tunpair u
      in tpair (tindexBuild snat stk1 u1 i)
               (tindexBuild snat stk2 u2 i)

  -- Unwinding methods, needed mostly to split off the Unwind module.
  -- | Add pointwise all corresponding tensors within nested product, if any.
  --
  -- Requires duplicable arguments or a ShareTensor instance.
  taddTarget :: TKAllNum y
             => SingletonTK y -> target y -> target y -> target y
  -- | Multiply pointwise all corresponding tensors within nested products,
  -- if any.
  --
  -- Requires duplicable arguments or a ShareTensor instance.
  tmultTarget :: TKAllNum y
              => SingletonTK y -> target y -> target y -> target y
  -- | Sum all dimensions of each component and then sum it all. Ignore all
  -- tensors with non-differentiable elements.
  --
  -- Requires duplicable arguments or a ShareTensor instance.
  tsum0Target :: TKAllNum y
              => FullShapeTK y -> target y
              -> target (TKScalar Double)
  -- | Dot product each component and then sum it all. Ignore all
  -- tensors with non-differentiable elements.
  --
  -- Requires duplicable arguments or a ShareTensor instance.
  tdot0Target :: TKAllNum y
              => FullShapeTK y -> target y -> target y
              -> target (TKScalar Double)

  -- TODO: express without ConvertTensor or move there
  xmcast :: (KnownSTK x, KnownShX sh, Rank sh ~ Rank sh2, ConvertTensor target)
         => StaticShX sh2 -> target (TKX2 sh x) -> target (TKX2 sh2 x)
  xmcast sh2 a = case tftk knownSTK a of
    FTKX sh' _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        withKnownShX sh2 $
        withKnownShS sh $
        xfromS $ sfromX @_ @sh a

-- These are user-accessible, so the constraint is `ADReady`, which means
-- lets, but no shares.
type role HFun nominal nominal
newtype HFun (x :: TK) (z :: TK) =
  HFun {unHFun :: forall f. ADReady f
               => f x -> f z}

instance Show (HFun x y) where
  show _ = "<lambda>"


-- * The mega-constraint

type ADReady target =
  ( ADReadyNoLet target
  , LetTensor target
  )

type ADReadyNoLet target =
  ( ADReadyEqsClasses target
  , ADReadyEqsClasses (ShareOf target)
  , ShareTensor (ShareOf target)
  , ShareTensor (PrimalOf (ShareOf target))
  , ShareTensor (PlainOf (ShareOf target))
  , ShareOf (ShareOf target) ~ ShareOf target
  )

type ADReadyEqsClasses f =
  ( ADReadyEqs f
  , LetTensor (PlainOf f)
  , ADReadyClasses f
  , ADReadyClasses (PrimalOf f)
  , ADReadyClasses (PlainOf f)
  )

type ADReadyEqs f =
  ( PlainOf (PlainOf f) ~ PlainOf f
  , PlainOf (PrimalOf f) ~ PlainOf f
  )

type ADReadyClasses f =
  ( BaseTensor f
  , ConvertTensor f
  , Boolean (BoolOf f)
  , AllTargetShow f
  , CommonTargetEqOrd f
  )

-- This is illegal:
-- type AllTargetShow target = forall y. KnownSTK y => Show (target y)

type AllTargetShow :: Target -> Constraint
class (forall y. KnownSTK y => Show (target y))
      => AllTargetShow target where
instance
      (forall y. KnownSTK y => Show (target y))
      => AllTargetShow target where

type CommonTargetEqOrd :: Target -> Constraint
class ( forall r. NumScalar r => EqH target (TKScalar r)
      , forall r. NumScalar r => OrdH target (TKScalar r)
      , forall r n. NumScalar r => EqH target (TKR n r)
      , forall r n. NumScalar r => OrdH target (TKR n r)
      , forall r sh. NumScalar r => EqH target (TKS sh r)
      , forall r sh. NumScalar r => OrdH target (TKS sh r)
      , forall r sh. NumScalar r => EqH target (TKX sh r)
      , forall r sh. NumScalar r => OrdH target (TKX sh r) )
      => CommonTargetEqOrd target where
instance
      ( forall r. NumScalar r => EqH target (TKScalar r)
      , forall r. NumScalar r => OrdH target (TKScalar r)
      , forall r n. NumScalar r => EqH target (TKR n r)
      , forall r n. NumScalar r => OrdH target (TKR n r)
      , forall r sh. NumScalar r => EqH target (TKS sh r)
      , forall r sh. NumScalar r => OrdH target (TKS sh r)
      , forall r sh. NumScalar r => EqH target (TKX sh r)
      , forall r sh. NumScalar r => OrdH target (TKX sh r) )
      => CommonTargetEqOrd target where
