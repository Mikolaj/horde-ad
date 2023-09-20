{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module HordeAd.Core.Again (module HordeAd.Core.Again) where

import Control.Monad.Trans.State
  ( State,
    StateT (StateT),
    evalState,
    get,
    modify,
    put,
    runState,
  )
import qualified Data.Array.ShapedS as OS
import qualified Data.Array.ShapedS.MatMul
import Data.Biapplicative ((<<*>>))
import qualified Data.Biapplicative as B
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Kind (Type)
import Data.List (foldl')
import qualified Data.Monoid as Monoid
import Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Map as Map
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import Data.Vector.Storable (Storable)
import GHC.TypeLits (KnownNat, natVal)
import GHC.TypeNats (type (+))
import Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import Prelude

class Known t where
  known :: t

instance HM.Numeric a => Known (a `IsScalarOf` a) where
  known = SScalar

instance HM.Numeric a => Known (a `IsScalarOf` Vector a) where
  known = SVector

instance
  (HM.Numeric a, OS.Shape sh, Storable a) =>
  Known (a `IsScalarOf` OS.Array sh a)
  where
  known = SShapedS

knowIsScalarOf :: s `IsScalarOf` t -> (Known (s `IsScalarOf` t) => r) -> r
knowIsScalarOf s r = case s of
  SScalar -> r
  SVector -> r
  SShapedS -> r

-- At some point we'll replace the HM.Numeric constraint with
-- something particular to our case.  Perhaps just even the ability to
-- add!
data IsScalarOf (s :: Type) (t :: Type) where
  SScalar :: HM.Numeric s => IsScalarOf s s
  SVector :: HM.Numeric s => IsScalarOf s (Vector s)
  -- I'm doubtful this Storable constraint is really needed.
  -- OS.toVector and OS.fromVector shouldn't require it.  See, for
  -- example,
  --
  -- https://github.com/tomjaguarpaw/orthotope/commit/10a65b60daa6b072093490275818afe0f8d38c09
  SShapedS ::
    (OS.Shape sh, Storable s, HM.Numeric s) =>
    IsScalarOf s (OS.Array sh s)

deriving instance Show (IsScalarOf s t)

-- Dot products for the types of DeltaF
deltaFDot :: forall s t. (Known (s `IsScalarOf` t), HM.Numeric s) => t -> t -> s
deltaFDot = case known :: s `IsScalarOf` t of
  SScalar -> (*)
  SVector -> (HM.<.>)
  SShapedS -> \t t' -> OS.sumA $ OS.zipWithA (*) t t'

data DeltaF (s :: Type) (dual :: Type -> Type) (t :: Type) where
  Zero0 :: DeltaF s dual s
  Add0 :: dual s -> dual s -> DeltaF s dual s
  Scale0 :: s -> dual s -> DeltaF s dual s
  Index0 :: dual (Vector s) -> Int -> Int -> DeltaF s dual s
  Add1 :: dual (Vector s) -> dual (Vector s) -> DeltaF s dual (Vector s)
  Scale1 :: s -> dual (Vector s) -> DeltaF s dual (Vector s)
  Konst1 :: dual s -> Int -> DeltaF s dual (Vector s)
  Dot1 :: Vector s -> dual (Vector s) -> DeltaF s dual s
  SumElements1 :: dual (Vector s) -> Int -> DeltaF s dual s
  Seq1 :: Data.Vector.Vector (dual s) -> DeltaF s dual (Vector s)
  AddS ::
    (OS.Shape sh, Storable s) =>
    dual (OS.Array sh s) ->
    dual (OS.Array sh s) ->
    DeltaF s dual (OS.Array sh s)
  NegateS ::
    (OS.Shape sh, Storable s) =>
    dual (OS.Array sh s) ->
    DeltaF s dual (OS.Array sh s)
  KonstS :: (OS.Shape sh, Storable s) => dual s -> DeltaF s dual (OS.Array sh s)
  ZeroS :: (OS.Shape sh, Storable s) => DeltaF s dual (OS.Array sh s)
  AppendS ::
    (OS.Shape sh, Storable s, KnownNat m, KnownNat n) =>
    dual (OS.Array (m : sh) s) ->
    dual (OS.Array (n : sh) s) ->
    DeltaF s dual (OS.Array ((m + n) : sh) s)
  MulS1 ::
    (Storable s, KnownNat m, KnownNat n, KnownNat p) =>
    dual (OS.Array [m, n] s) ->
    OS.Array [n, p] s ->
    DeltaF s dual (OS.Array [m, p] s)
  MulS2 ::
    (Storable s, KnownNat m, KnownNat n, KnownNat p) =>
    OS.Array [m, n] s ->
    dual (OS.Array [n, p] s) ->
    DeltaF s dual (OS.Array [m, p] s)
  ScalePointwiseS ::
    (OS.Shape sh, Storable s) =>
    dual (OS.Array sh s) ->
    OS.Array sh s ->
    DeltaF s dual (OS.Array sh s)
  SumElementsS ::
    (OS.Shape sh, Storable s) =>
    dual (OS.Array sh s) ->
    DeltaF s dual s

mapDeltaF ::
  HM.Numeric s =>
  (forall tt. dual tt -> dual' tt) ->
  DeltaF s dual t ->
  DeltaF s dual' t
mapDeltaF f = mapDeltaFG (\_ -> f)

mapDeltaFG ::
  HM.Numeric s =>
  (forall tt. s `IsScalarOf` tt -> dual tt -> dual' tt) ->
  DeltaF s dual t ->
  DeltaF s dual' t
mapDeltaFG f = \case
  Zero0 -> Zero0
  Add0 duals duals' -> Add0 (f known duals') (f known duals)
  Scale0 s duals -> Scale0 s (f known duals)
  Index0 dual n i -> Index0 (f known dual) n i
  Add1 dual dual' -> Add1 (f known dual') (f known dual)
  Scale1 s dual -> Scale1 s (f known dual)
  Konst1 duals n -> Konst1 (f known duals) n
  Dot1 vec dual -> Dot1 vec (f known dual)
  SumElements1 dual n -> SumElements1 (f known dual) n
  Seq1 vec -> Seq1 (fmap (f known) vec)
  AddS d1 d2 -> AddS (f known d1) (f known d2)
  NegateS d -> NegateS (f known d)
  KonstS s -> KonstS (f known s)
  ZeroS -> ZeroS
  AppendS a1 a2 -> AppendS (f known a1) (f known a2)
  MulS1 d a -> MulS1 (f known d) a
  MulS2 a d -> MulS2 a (f known d)
  ScalePointwiseS d a -> ScalePointwiseS (f known d) a
  SumElementsS d -> SumElementsS (f known d)

newtype DeltaId (s :: Type) (t :: Type) where
  DeltaId :: Int -> DeltaId s t

deriving instance Eq (DeltaId s t)

deriving instance Ord (DeltaId s t)

deriving instance Show (DeltaId s t)

succDeltaId :: DeltaId s t -> DeltaId s t
succDeltaId (DeltaId i) = DeltaId (i + 1)

data DeltaBinding s where
  DeltaBinding ::
    Known (s `IsScalarOf` t) =>
    DeltaId s t ->
    Delta DeltaF s t ->
    DeltaBinding s

type Delta :: (Type -> (Type -> Type) -> Type -> Type) -> Type -> Type -> Type
data Delta df (s :: Type) (t :: Type) where
  Delta :: df s (Delta df s) t -> Delta df s t
  Var :: DeltaId s t -> Delta df s t

data DeltaMap s = DeltaMap
  { dmScalar :: Map.Map (DeltaId s s) s,
    dmVector :: Map.Map (DeltaId s (Vector s)) (Vector s),
    dmShapedS :: Map.Map Int (Vector s)
  }
  deriving (Show)

singleton ::
  forall s t. Known (s `IsScalarOf` t) => DeltaId s t -> t -> DeltaMap s
singleton dId t = case known @(s `IsScalarOf` t) of
  SScalar -> DeltaMap (Map.singleton dId t) Map.empty Map.empty
  SVector -> DeltaMap Map.empty (Map.singleton dId t) Map.empty
  SShapedS -> DeltaMap Map.empty Map.empty (Map.singleton i (OS.toVector t))
    where
      DeltaId i = dId

deltaMapLookup ::
  forall s t.
  Known (s `IsScalarOf` t) =>
  DeltaId s t ->
  DeltaMap s ->
  Maybe t
deltaMapLookup dId m = case known @(s `IsScalarOf` t) of
  SScalar -> Map.lookup dId (dmScalar m)
  SVector -> Map.lookup dId (dmVector m)
  SShapedS -> fmap OS.fromVector (Map.lookup i (dmShapedS m))
    where
      DeltaId i = dId

deltaMapDelete ::
  forall s t.
  Known (s `IsScalarOf` t) =>
  DeltaId s t ->
  DeltaMap s ->
  DeltaMap s
deltaMapDelete dId (DeltaMap ms mv msh) = case known @(s `IsScalarOf` t) of
  SScalar -> DeltaMap (Map.delete dId ms) mv msh
  SVector -> DeltaMap ms (Map.delete dId mv) msh
  SShapedS -> DeltaMap ms mv (Map.delete i msh)
    where
      DeltaId i = dId

deltaMapAlter ::
  forall s t.
  Known (s `IsScalarOf` t) =>
  (Maybe t -> Maybe t) ->
  DeltaId s t ->
  DeltaMap s ->
  DeltaMap s
deltaMapAlter f di m = case known @(s `IsScalarOf` t) of
  SScalar -> m {dmScalar = Map.alter f di (dmScalar m)}
  SVector -> m {dmVector = Map.alter f di (dmVector m)}
  SShapedS ->
    m
      { dmShapedS =
          Map.alter
            (fmap OS.toVector . f . fmap OS.fromVector)
            i
            (dmShapedS m)
      }
    where
      DeltaId i = di

-- Definiton:
--
-- We say that "f has the special property" when
--
-- f :: d s -> t -> DeltaMap s -> DeltaMap s
--
-- and
--
-- 1. f d t . f d' t' = f d' t' . f d t
-- 2. f d (t + t') = f d t . f d t'
-- 3. f d (t + t') (m + m') = (f d t m) + (f d t' m')
-- 4. f d (k * t) (k * m) = k * (f d t m)
--
-- In our examples 'd s' is one of
--

-- * DeltaF s dual t

-- * DeltaId s t

-- * Delta s t

-- 'evalDeltaF f' has the special property when f does

-- FIXME: (.) should probably instead be strict composition,
--
--     (f .! g) x = let !y = g x in f y
evalDeltaF ::
  forall s dual t deltaMap_s.
  HM.Numeric s =>
  ( forall tt.
    Known (s `IsScalarOf` tt) =>
    dual tt ->
    tt ->
    deltaMap_s ->
    deltaMap_s
  ) ->
  DeltaF s dual t ->
  t ->
  deltaMap_s ->
  deltaMap_s
evalDeltaF f deltaF t = case deltaF of
  Zero0 -> id
  Add0 de de' ->
    f de t . f de' t
  Scale0 t' de -> f de (t' * t)
  Index0 de i n ->
    f
      de
      (HM.fromList (map (\n' -> if n' == i then t else 0) [0 .. n - 1]))
  Dot1 de de' -> f de' (t `HM.scale` de)
  Add1 de de' -> f de t . f de' t
  Scale1 s de -> f de (s `HM.scale` t)
  Konst1 de _ -> f de (HM.sumElements t)
  SumElements1 de n -> f de (HM.konst t n)
  Seq1 des -> \dm -> foldl' (flip (uncurry f)) dm (zip desl tl)
    where
      desl = Data.Vector.toList des
      tl = HM.toList t
  AddS de de' -> f de t . f de' t
  NegateS d -> f d (OS.mapA negate t)
  KonstS de -> f de (OS.sumA t)
  ZeroS -> id
  AppendS
    (de :: dual (OS.Array (k : rest) s))
    (de' :: dual (OS.Array (l : rest) s)) ->
      f de (OS.slice @'[ '(0, k)] t) . f de' (OS.slice @'[ '(k, l)] t)
  MulS1 de a -> f de (mulS t (transposeS a))
  MulS2 a de -> f de (mulS (transposeS a) t)
  ScalePointwiseS de a -> f de (OS.zipWithA (*) a t)
  SumElementsS de -> f de (OS.constant t)

newtype MonoidMap m s t = MonoidMap {unMonoidMap :: t -> m}

-- A more abstract way of writing evalDeltaF
evalDeltaFM ::
  forall dual s m t r.
  (HM.Numeric s, Monoid m) =>
  (forall tt. dual tt -> MonoidMap m r tt) ->
  DeltaF s dual t ->
  MonoidMap m r t
evalDeltaFM f' = evalDeltaFM1 . mapDeltaF f'

evalDeltaFM1 ::
  forall s m t r.
  (HM.Numeric s, Monoid m) =>
  DeltaF s (MonoidMap m r) t ->
  MonoidMap m r t
evalDeltaFM1 deltaF = MonoidMap $ \t -> case deltaF of
  Zero0 -> mempty
  Add0 de de' ->
    f de t <> f de' t
  Scale0 t' de -> f de (t' * t)
  Index0 de i n ->
    f
      de
      (HM.fromList (map (\n' -> if n' == i then t else 0) [0 .. n - 1]))
  Dot1 de de' -> f de' (t `HM.scale` de)
  Add1 de de' -> f de t <> f de' t
  Scale1 s de -> f de (s `HM.scale` t)
  Konst1 de _ -> f de (HM.sumElements t)
  ZeroS -> mempty
  SumElements1 de n -> f de (HM.konst t n)
  Seq1 des -> foldMap (uncurry f) (zip desl tl)
    where
      desl = Data.Vector.toList des
      tl = HM.toList t
  AddS de de' -> f de t <> f de' t
  NegateS d -> f d (OS.mapA negate t)
  KonstS de -> f de (OS.sumA t)
  AppendS
    (de :: dual (OS.Array (k : rest) s))
    (de' :: dual (OS.Array (l : rest) s)) ->
      f de (OS.slice @'[ '(0, k)] t) <> f de' (OS.slice @'[ '(k, l)] t)
  MulS1 de a -> f de (mulS t (transposeS a))
  MulS2 a de -> f de (mulS (transposeS a) t)
  ScalePointwiseS de a -> f de (OS.zipWithA (*) a t)
  SumElementsS de -> f de (OS.constant t)
  where
    f = unMonoidMap

-- Could implement evalDeltaFM1 in terms of this
evalDeltaFMod ::
  forall s t mod.
  HM.Numeric s =>
  (forall tt. mod tt) ->
  (forall tt. mod tt -> mod tt -> mod tt) ->
  (forall tt tt'. mod tt -> (tt' -> tt) -> mod tt') ->
  DeltaF s mod t ->
  mod t
evalDeltaFMod mempty' (<>.) ($$) deltaF = case deltaF of
  Zero0 -> mempty'
  Add0 de de' -> de <>. de'
  Scale0 t' de -> de $$ (t' *)
  Index0 de i n ->
      de $$ \t -> HM.fromList (map (\n' -> if n' == i then t else 0) [0 .. n - 1])
  Dot1 de de' -> de' $$ (`HM.scale` de)
  Add1 de de' -> de <>. de'
  Scale1 s de -> de $$ (s `HM.scale`)
  Konst1 de _ -> de $$ HM.sumElements
  ZeroS -> mempty'
  SumElements1 de n -> de $$ (\t -> HM.konst t n)
  Seq1 des -> -- TODO: Be better than foldl'
    -- TODO: Would be great if we didn't have to convert to list and then index!
    foldl' (<>.) mempty' (fmap (\(i, desl1) -> desl1 $$ (\t -> HM.toList t !! i)) (zip [0..] desl))
    where
      desl = Data.Vector.toList des
  AddS de de' -> de <>. de'
  NegateS d -> d $$ OS.mapA negate
  KonstS de -> de $$ OS.sumA
  AppendS
    (de :: dual (OS.Array (k : rest) s))
    (de' :: dual (OS.Array (l : rest) s)) ->
      (de $$ (OS.slice @'[ '(0, k)])) <>. (de' $$ (OS.slice @'[ '(k, l)]))
  MulS1 de a -> de $$ (\t -> mulS t (transposeS a))
  MulS2 a de -> de $$ mulS (transposeS a)
  ScalePointwiseS de a -> de $$ OS.zipWithA (*) a
  SumElementsS de -> de $$ OS.constant

instance (HM.Numeric r, Monoid m) => Ops r DeltaF (MonoidMap m) where
  ops = evalDeltaFM1

-- The correctness condition on Ops is that the two tuple components
-- should be equal.
--
-- f ~ DeltaF s
-- dual1 ~ C
-- dual2 ~ MonoidMap m
--
-- The need for the "constraint" c is rather unfortunate.  We need it
-- in order to get hold of a dot product for t.
compatibleOps ::
  forall f dual1 dual2 t' c.
  -- | ops @C
  (forall t. c t -> f dual1 t -> dual1 t) ->
  -- | ops @MonoidMap (i.e. evalDeltaFM1)
  (forall t. c t -> f dual2 t -> dual2 t) ->
  -- | Functor instance, (i.e. mapDeltaF)
  ((forall t. c t -> dual1 t -> dual2 t) -> (forall t. c t -> f dual1 t -> f dual2 t)) ->
  -- | Homomorphism (i.e. "dot with argument then sum")
  (forall t. c t -> dual1 t -> dual2 t) ->
  (c t' -> f dual1 t' -> dual2 t', c t' -> f dual1 t' -> dual2 t')
compatibleOps f1 f2 mapp f = (\c -> f c . f1 c, \c -> f2 c . mapp f c)

useCompatibleOps ::
  forall s t.
  HM.Numeric s =>
  ( s `IsScalarOf` t -> DeltaF s (Concrete s) t -> MonoidMap (Monoid.Sum s) s t,
    s `IsScalarOf` t -> DeltaF s (Concrete s) t -> MonoidMap (Monoid.Sum s) s t
  )
useCompatibleOps =
  compatibleOps
    @(DeltaF s)
    @(Concrete s)
    @(MonoidMap (Monoid.Sum s) s)
    (\_ -> ops)
    (\_ -> ops)
    (\f _ -> mapDeltaFG f)
    (\s (C t) -> knowIsScalarOf s (MonoidMap (\t' -> Monoid.Sum (t `deltaFDot` t'))))

-- accumulate has the special property
accumulate ::
  forall s t.
  Known (s `IsScalarOf` t) =>
  DeltaId s t ->
  t ->
  DeltaMap s ->
  DeltaMap s
accumulate di t = deltaMapAlter (Just . accumulateMaybe @s t) di

accumulateMaybe ::
  forall s t. Known (s `IsScalarOf` t) => t -> Maybe t -> t
accumulateMaybe t = \case
  Nothing -> t
  Just t' -> accumulate1 @s t t'

accumulate1 ::
  forall s t. Known (s `IsScalarOf` t) => t -> t -> t
accumulate1 t t' = case known @(s `IsScalarOf` t) of
  SScalar -> t + t'
  SVector -> t `HM.add` t'
  SShapedS -> t `addS` t'

-- eval has the special property
eval ::
  forall s t.
  Known (s `IsScalarOf` t) =>
  HM.Numeric s =>
  Delta DeltaF s t ->
  t ->
  DeltaMap s ->
  DeltaMap s
eval delta = case delta of
  Delta df -> evalDeltaF eval df
  Var di -> accumulate di

-- evalLet satsifies
--
-- evalLet b (m + m') = evalLet b m + evalLet b m'
-- evalLet b (k * m) = k * evalLet b m
--
-- i.e. 'evalLet b' is mathematically linear
evalLet :: HM.Numeric s => DeltaBinding s -> DeltaMap s -> DeltaMap s
evalLet (DeltaBinding di de) m = case deltaMapLookup di m of
  Nothing -> m
  Just x -> eval de x (deltaMapDelete di m)

-- runDelta satsifies
--
-- runDelta b (m + m') = runDelta b m + runDelta b m'
-- runDelta b (k * m) = k * runDelta b m
runDelta ::
  HM.Numeric s =>
  [DeltaBinding s] ->
  DeltaMap s ->
  DeltaMap s
runDelta = flip (foldl' (flip evalLet))

runDualMonadM :: DualMonadGradient s a -> (a, DeltaState s)
runDualMonadM m = runState (runDualMonadGradient m) initialState
  where
    initialState =
      DeltaState
        { deltaCounter0 = DeltaId 0,
          deltaCounter1 = DeltaId 0,
          deltaCounter2 = 0,
          deltaBindings = []
        }

runDualMonadAdapt ::
  (HM.Numeric s, Known (IsScalarOf s t)) =>
  ArgAdaptor s arg dual ->
  t ->
  (dual -> DualMonadGradient s (D t' (Delta DeltaF s t))) ->
  (t', arg)
runDualMonadAdapt aa g f =
  let (lookup', arg) = runArgAdaptor aa
      m = f arg
      (t', dm) = runDualMonadS g m
   in (t', lookup' dm)

runDualMonadS ::
  (HM.Numeric s, Known (IsScalarOf s t)) =>
  t ->
  DualMonadGradient s (D t' (Delta DeltaF s t)) ->
  (t', DeltaMap s)
runDualMonadS g e =
  let ((t, dId), bs) = runDualMonadM $ do
        D t' delta <- e
        dId' <- deltaLetId delta
        pure (t', dId')
   in (t, runDelta (deltaBindings bs) (singleton dId g))

runDualMonad ::
  (HM.Numeric s, Known (IsScalarOf s t)) =>
  t ->
  DualMonadGradient s (D s (Delta DeltaF s t)) ->
  (s, DeltaMap s)
runDualMonad = runDualMonadS

data DeltaState s = DeltaState
  { deltaCounter0 :: DeltaId s s,
    deltaCounter1 :: DeltaId s (Vector s),
    deltaCounter2 :: Int,
    deltaBindings :: [DeltaBinding s]
  }

newtype DualMonadGradient s t = DualMonadGradient
  {runDualMonadGradient :: State (DeltaState s) t}
  deriving newtype (Monad, Functor, Applicative)

class
  (forall s. Monad (m s)) =>
  DualMonad (dual :: Type -> Type -> Type) m
  where
  deltaLet :: Known (s `IsScalarOf` t) => dual s t -> m s (dual s t)

dLet ::
  forall (dual :: Type -> Type -> Type) t m s.
  (DualMonad dual m, Known (IsScalarOf s t)) =>
  Dual (dual s) t ->
  m s (Dual (dual s) t)
dLet (D x y) = do
  y' <- deltaLet y
  pure (D x y')

fresh :: s `IsScalarOf` t -> DualMonadGradient s (DeltaId s t)
fresh sd = DualMonadGradient $ do
  st <- get
  case sd of
    SScalar -> do
      let this = deltaCounter0 st
          next = succDeltaId this
      put (st {deltaCounter0 = next})
      pure this
    SVector -> do
      let this = deltaCounter1 st
          next = succDeltaId this
      put (st {deltaCounter1 = next})
      pure this
    SShapedS -> do
      let this = deltaCounter2 st
          !next = this + 1
      put (st {deltaCounter2 = next})
      pure (DeltaId this)

bind ::
  Known (s `IsScalarOf` t) => DeltaId s t -> Delta DeltaF s t -> DualMonadGradient s ()
bind dId delta =
  DualMonadGradient $
    modify
      ( \st ->
          st {deltaBindings = DeltaBinding dId delta : deltaBindings st}
      )

deltaLetId ::
  Known (s `IsScalarOf` t) => Delta DeltaF s t -> DualMonadGradient s (DeltaId s t)
deltaLetId delta = do
  dId <- fresh known
  bind dId delta
  pure dId

instance DualMonad (Delta DeltaF) DualMonadGradient where
  deltaLet delta = fmap Var (deltaLetId delta)

type DualMonadValue :: Type -> Type -> Type
newtype DualMonadValue s a = DualMonadValue
  {runDualMonadValue :: Identity a}
  deriving newtype (Monad, Functor, Applicative)

type Unit :: Type -> Type -> Type
data Unit s t = Unit

instance DualMonad Unit DualMonadValue where
  deltaLet = pure

newtype DualMonadForward s a = DualMonadForward (Identity a)
  deriving newtype (Monad, Functor, Applicative)

runDualMonadForward :: DualMonadForward s a -> a
runDualMonadForward (DualMonadForward m) = runIdentity m

instance DualMonad Concrete DualMonadForward where
  deltaLet = pure

dSingleArgForward ::
  t ->
  t ->
  ( Dual (Concrete s) t ->
    DualMonadForward s (D r (Concrete s r))
  ) ->
  (r, r)
dSingleArgForward t t' f =
  let D r d = runDualMonadForward (f (D t (concrete t')))
   in (r, unConcrete d)

dDoubleArgForward ::
  (t1, t2) ->
  (t1, t2) ->
  ( (Dual (Concrete s) t1, Dual (Concrete s) t2) ->
    DualMonadForward s (D r (Concrete s r))
  ) ->
  (r, r)
dDoubleArgForward (t, t') (dt, dt') f =
  let D r d = runDualMonadForward (f (D t (concrete dt), D t' (concrete dt')))
   in (r, unConcrete d)

dMultiArgForward ::
  (Data.Vector.Vector t, Data.Vector.Vector t) ->
  (Data.Vector.Vector t', Data.Vector.Vector t') ->
  ( ( Data.Vector.Vector (D t (Concrete s t)),
      Data.Vector.Vector (D t' (Concrete s t'))
    ) ->
    DualMonadForward s (D r (Concrete s r))
  ) ->
  (r, r)
dMultiArgForward (t, dt) (t', dt') f =
  let D r d =
        runDualMonadForward
          ( f
              ( Data.Vector.zipWith (\a da -> D a (concrete da)) t dt,
                Data.Vector.zipWith (\a da -> D a (concrete da)) t' dt'
              )
          )
   in (r, unConcrete d)

dValue :: DualMonadValue s (D t (Unit s t)) -> t
dValue = (\case D r _ -> r) . runIdentity . runDualMonadValue

newtype DualMonadIO s a = DualMonadIO (IO a)
  deriving newtype (Monad, Functor, Applicative)

runDualMonadIO :: DualMonadIO s a -> IO a
runDualMonadIO (DualMonadIO a) = a

type DeltaIO :: Type -> Type -> Type
data DeltaIO s t where
  DeltaIO :: {accumulateIO :: t -> IO (), triggerIO :: IO ()} -> DeltaIO s t

-- TODO: Just derive this?
instance Semigroup (DeltaIO s t) where
  DeltaIO acc1 go1 <> DeltaIO acc2 go2 = DeltaIO (acc1 <> acc2) (go1 <> go2)

-- TODO: Just derive this?
instance Monoid (DeltaIO s t) where
  mempty = DeltaIO mempty mempty

instance DualMonad DeltaIO DualMonadIO where
  deltaLet = \(deltaIO :: DeltaIO s t) -> DualMonadIO $ do
    ref <- newIORef Nothing
    pure
      ( DeltaIO
          { accumulateIO = \t -> modifyIORef' ref (Just . accumulateMaybe @s t),
            triggerIO = do
              readIORef ref >>= \case
                Nothing -> pure ()
                Just r -> accumulateIO deltaIO r
              triggerIO deltaIO
          }
      )

instance Ops Double DeltaF DeltaIO where
  ops = evalDeltaFMod mempty (<>) (\(DeltaIO acc go) f -> DeltaIO (acc . f) go)

exampleIO :: IO (Double, (Double, Double))
exampleIO = do
  r1 <- newIORef (0 :: Double)
  r2 <- newIORef 0
  D r (DeltaIO acc go) <- case foo
           (D 10 (DeltaIO (\t -> modifyIORef' r1 (+ t)) (pure ())))
           (D 20 (DeltaIO (\t -> modifyIORef' r2 (+ t)) (pure ()))) of
    DualMonadIO io -> io

  acc 1
  go

  x1 <- readIORef r1
  x2 <- readIORef r2

  pure (r, (x1, x2))

newtype ArgAdaptor s t pd = ArgAdaptor (State Int (DeltaMap s -> t, pd))

instance B.Bifunctor (ArgAdaptor s) where
  bimap = bimapArgAdaptor

instance B.Biapplicative (ArgAdaptor s) where
  bipure = pureArgAdaptor
  f <<*>> x = B.bimap (uncurry ($)) (uncurry ($)) (liftB2 f x)

runArgAdaptor ::
  ArgAdaptor s t pd ->
  (DeltaMap s -> t, pd)
runArgAdaptor (ArgAdaptor s) = evalState s (-1)

adaptArg ::
  Known (IsScalarOf s t) =>
  t ->
  ArgAdaptor s t (Dual (Delta DeltaF s) t)
adaptArg t = ArgAdaptor $ do
  i <- get
  put (i - 1)
  let lookup' m = case deltaMapLookup (DeltaId i) m of
        Nothing -> error ("No such DeltaId: " ++ show i)
        Just j -> j

  pure (lookup', D t (Var (DeltaId i)))

pureArgAdaptor ::
  t ->
  pd ->
  ArgAdaptor s t pd
pureArgAdaptor t pd = ArgAdaptor (pure (pure t, pd))

bimapArgAdaptor ::
  (t -> t') ->
  (pd -> pd') ->
  ArgAdaptor s t pd ->
  ArgAdaptor s t' pd'
bimapArgAdaptor ft fpd (ArgAdaptor a) = ArgAdaptor $ do
  (t, pd) <- a
  pure (fmap ft t, fpd pd)

liftB2 ::
  ArgAdaptor s t1 pd1 ->
  ArgAdaptor s t2 pd2 ->
  ArgAdaptor s (t1, t2) (pd1, pd2)
liftB2 (ArgAdaptor a1) (ArgAdaptor a2) = ArgAdaptor $ do
  (lookup1, arg1) <- a1
  (lookup2, arg2) <- a2
  pure (\m -> (lookup1 m, lookup2 m), (arg1, arg2))

sequenceArgAdaptor ::
  [ArgAdaptor s t pd] ->
  ArgAdaptor s [t] [pd]
sequenceArgAdaptor = \case
  [] -> pureArgAdaptor [] []
  ArgAdaptor a : as -> ArgAdaptor $ do
    (t, pd) <- a
    let ArgAdaptor ts_pds = sequenceArgAdaptor as
    (ts, pds) <- ts_pds
    pure ((:) <$> t <*> ts, pd : pds)

sequenceArgAdaptorVector ::
  Data.Vector.Vector (ArgAdaptor s a1 a2) ->
  ArgAdaptor s (Data.Vector.Vector a1) (Data.Vector.Vector a2)
sequenceArgAdaptorVector =
  bimapArgAdaptor Data.Vector.fromList Data.Vector.fromList
    . sequenceArgAdaptor
    . Data.Vector.toList

data D a b = D a b
  deriving (Show)

type Dual dual t = D t (dual t)

class Ops s f dual where
  ops :: f s (dual s) t -> dual s t

type Concrete :: Type -> Type -> Type
newtype Concrete s t where
  C :: {unConcrete :: t} -> Concrete s t

concrete :: t -> Concrete s t
concrete = C

instance (Num r, HM.Numeric r) => Ops r DeltaF Concrete where
  ops = \case
    Zero0 -> C 0
    Add0 (C x1) (C x2) -> C (x1 + x2)
    Scale0 r (C x) -> C (r * x)
    Index0 (C v) i _n -> C (HM.atIndex v i)
    Add1 (C x1) (C x2) -> C (x1 `HM.add` x2)
    Scale1 r (C x) -> C (HM.scale r x)
    Konst1 (C k) i -> C (HM.konst k i)
    ZeroS -> C (OS.constant 0)
    Dot1 v1 (C v2) -> C (v1 `HM.dot` v2)
    SumElements1 (C v) _ -> C (HM.sumElements v)
    Seq1 v -> C (HM.fromList $ map (\case C x -> x) $ Data.Vector.toList v)
    AddS (C de) (C de') -> C (addS de de')
    NegateS (C d) -> C (OS.mapA negate d)
    KonstS (C s) -> C (OS.constant s)
    AppendS (C a1) (C a2) -> C (OS.append a1 a2)
    MulS1 (C de) a -> C (mulS de a)
    MulS2 a (C de) -> C (mulS a de)
    ScalePointwiseS (C de) a -> C (OS.zipWithA (*) de a)
    SumElementsS (C de) -> C (OS.sumA de)

instance Ops r DeltaF Unit where
  ops = \case
    Zero0 {} -> Unit
    Add0 {} -> Unit
    Scale0 {} -> Unit
    Index0 {} -> Unit
    Add1 {} -> Unit
    Scale1 {} -> Unit
    Konst1 {} -> Unit
    Dot1 {} -> Unit
    SumElements1 {} -> Unit
    Seq1 {} -> Unit
    AddS {} -> Unit
    NegateS {} -> Unit
    KonstS {} -> Unit
    ZeroS {} -> Unit
    AppendS {} -> Unit
    MulS1 {} -> Unit
    MulS2 {} -> Unit
    ScalePointwiseS {} -> Unit
    SumElementsS {} -> Unit

instance Ops r DeltaF (Delta DeltaF) where
  ops = Delta

baz ::
  ( Ops s DeltaF dual,
    HM.Numeric s,
    KnownNat l,
    KnownNat n,
    KnownNat m,
    KnownNat p,
    Applicative dualMonadGradient
  ) =>
  ( Dual (dual s) (OS.Array '[m, n] s),
    Dual (dual s) (OS.Array '[n, p] s)
  ) ->
  dualMonadGradient (Dual (dual s) (OS.Array '[l, p] s))
baz (x, y) = pure (konstS 2 `mulSDual` x `mulSDual` y)

data ARecord a b c = ARecord a b c

bazRecord ::
  ( Applicative f,
    Ops s DeltaF dual,
    HM.Numeric s,
    KnownNat l,
    KnownNat m,
    KnownNat n,
    KnownNat p,
    KnownNat q
  ) =>
  ARecord
    (Dual (dual s) (OS.Array '[m, n] s))
    (Dual (dual s) (OS.Array '[n, p] s))
    (Dual (dual s) (OS.Array '[p, q] s)) ->
  f (Dual (dual s) (OS.Array '[l, q] s))
bazRecord (ARecord x y z) = pure (konstS 2 `mulSDual` x `mulSDual` y `mulSDual` z)

bar ::
  (HM.Numeric s, DualMonad dual m, Ops s DeltaF dual) =>
  Dual (dual s) (Vector s) ->
  m s (Dual (dual s) s)
bar v = do
  x <- index v 0
  y <- index v 1
  foo x y

foo ::
  (DualMonad dual m, HM.Numeric s, Ops s DeltaF dual) =>
  Dual (dual s) s ->
  Dual (dual s) s ->
  m s (Dual (dual s) s)
foo x y = do
  x2 <- x .* x
  x2y <- x2 .* y
  x2y .+ y

-- d Functions (meaning, dual s s -> dual s s, low-level API)

-- I'm not sure it's actually useful to have these, rather than just
-- using ops and the constructors directly.
--
-- MK: If things like @ops (SumElements1 v n)@ work fine, without requiring
-- any change, for gradients, forward derivatives, values, etc.,
-- (and in case of @ops (Scale0 x y)@ also for scalars, vectors, tensors, etc.)
-- then indeed they are fine and `dSumElements` is spurious,
-- especially that it's the low-level API, so some extra verbosity
-- is not problematic. However, e.g., @sumElements@, belonging
-- to the high-level API, would ideally be succinct in both type
-- and usage (and it is, except for the rather long type ATM).
-- Similarly, @scale@.
--
-- So, I guess, if we forgo the rank-polymorhic scale, etc.,
-- there is indeed no point to @dScale0@-like functions and the user-facing
-- API (@ops@ and the constructors; anything else?) should be delimited
-- by different means, while exposing the rest for the engine, optimizers, etc.

dAdd0 :: Ops s DeltaF dual => dual s s -> dual s s -> dual s s
dAdd0 x y = ops (Add0 x y)

dScale0 :: Ops s DeltaF dual => s -> dual s s -> dual s s
dScale0 x y = ops (Scale0 x y)

dZero0 :: Ops s DeltaF dual => dual s s
dZero0 = ops Zero0

dSumElements :: Ops s DeltaF dual => dual s (Vector s) -> Int -> dual s s
dSumElements v n = ops (SumElements1 v n)

-- D number functions (meaning, D -> Dual, high level API)

instance (Num s, Ops s DeltaF dual) => Num (D s (dual s s)) where
  D x x' + D y y' = D (x + y) (dAdd0 x' y')
  D x x' - D y y' = D (x - y) (dAdd0 x' (dScale0 (-1) y'))
  D x x' * D y y' = D (x * y) (dAdd0 (dScale0 x y') (dScale0 y x'))
  negate (D x x') = D (- x) (dScale0 (-1) x')
  abs = undefined
  signum = undefined
  fromInteger = constant . fromInteger

-- These instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (D s (dual s))

instance Ord (D s (dual s))

instance (Real s, Ops s DeltaF dual) => Real (D s (dual s s))

instance (Fractional s, Ops s DeltaF dual) => Fractional (D s (dual s s)) where
  D u u' / D v v' =
    let recipSq = recip (v * v)
     in D
          (u / v)
          (dAdd0 (dScale0 (v * recipSq) u') (dScale0 (- u * recipSq) v'))

instance (Floating s, Ops s DeltaF dual) => Floating (D s (dual s s)) where
  sin (D u u') = D (sin u) (dScale0 (cos u) u')

instance (RealFrac s, Ops s DeltaF dual) => RealFrac (D s (dual s s))

instance (RealFloat s, Ops s DeltaF dual) => RealFloat (D s (dual s s)) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
     in D (atan2 u v) (dAdd0 (dScale0 (- u * t) v') (dScale0 (v * t) u'))

-- TODO (not really needed on its own, but something like that
-- would be required for scale1 and Num on Vectors):
dScale1 ::
  (HM.Numeric s, Ops s DeltaF dual) =>
  (Vector s) ->
  dual s (Vector s) ->
  dual s (Vector s)
dScale1 x y = ops (Scale1 (HM.sumElements x) y) -- TODO

-- This causes "Overlapping instances". Perhaps the above Num should be
-- only defined for Double and Float, not for @s@?
{-
instance (Num (Vector s), Ops (DeltaF s) dual)
         => Num (D (Vector s) (dual (Vector s))) where
  D x x' * D y y' =
    D (x * y) (ops (Add1 (dScale1 x y') (dScale1 y x')))
-}

constant :: Ops s DeltaF dual => a -> D a (dual s s)
constant k = D k dZero0

-- TODO: this is probably not the right type for both scalars and vectors?
scale0 ::
  (Num s, Ops s DeltaF dual) =>
  s ->
  Dual (dual s) s ->
  Dual (dual s) s
scale0 a (D u u') = D (a * u) (dScale0 a u')

scale1 ::
  (HM.Numeric s, Num (Vector s), Ops s DeltaF dual) =>
  Vector s ->
  Dual (dual s) (Vector s) ->
  Dual (dual s) (Vector s)
scale1 a (D u u') = D (a * u) (dScale1 a u')

-- MK: if this cannot work on vectors, perhaps @square0@ would be a better name
-- and then we can add @square1@.
square :: (Num s, Ops s DeltaF dual) => Dual (dual s) s -> Dual (dual s) s
square (D u u') = D (u * u) (dScale0 (2 * u) u')

squaredDifference ::
  (Num s, Ops s DeltaF dual) =>
  s ->
  Dual (dual s) s ->
  Dual (dual s) s
squaredDifference targ res = square $ res - constant targ

(.+) ::
  (DualMonad dual m, HM.Numeric s, Ops s DeltaF dual) =>
  Dual (dual s) s ->
  Dual (dual s) s ->
  m s (Dual (dual s) s)
D x x' .+ D y y' =
  dLet $ D (x + y) (ops (Add0 x' y'))

(.*) ::
  (DualMonad dual m, HM.Numeric s, Ops s DeltaF dual) =>
  Dual (dual s) s ->
  Dual (dual s) s ->
  m s (Dual (dual s) s)
D x x' .* D y y' =
  dLet $ D (x * y) (ops (Add0 (ops (Scale0 y x')) (ops (Scale0 x y'))))

index ::
  (HM.Numeric s, Ops s DeltaF dual, DualMonad dual m) =>
  Dual (dual s) (Vector s) ->
  Int ->
  m s (Dual (dual s) s)
index (D v v') i = dLet $ D (HM.atIndex v i) (ops (Index0 v' i (HM.size v)))

sumElements ::
  (HM.Numeric s, Ops s DeltaF dual) =>
  Dual (dual s) (Vector s) ->
  Dual (dual s) s
sumElements (D u u') = D (HM.sumElements u) (dSumElements u' (HM.size u))

sumElementsS ::
  (HM.Numeric s, Ops s DeltaF dual, OS.Shape sh) =>
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) s
sumElementsS (D u u') = D (OS.sumA u) (ops (SumElementsS u'))

konstS ::
  (Storable s, OS.Shape sh, Ops s DeltaF dual) =>
  Dual (dual s) s ->
  Dual (dual s) (OS.Array sh s)
konstS (D u u') = D (OS.constant u) (ops (KonstS u'))

mkonstS ::
  ( HM.Numeric s,
    OS.Shape sh,
    Ops s DeltaF dual,
    DualMonad dual m
  ) =>
  Dual (dual s) s ->
  m s (Dual (dual s) (OS.Array sh s))
mkonstS (D u u') = dLet $ D (OS.constant u) (ops (KonstS u'))

mulSDual ::
  (Ops s DeltaF dual, HM.Numeric s, KnownNat p, KnownNat m, KnownNat n) =>
  Dual (dual s) (OS.Array [m, n] s) ->
  Dual (dual s) (OS.Array [n, p] s) ->
  Dual (dual s) (OS.Array [m, p] s)
mulSDual (D x dx) (D y dy) =
  D (mulS x y) (ops (AddS (ops (MulS1 dx y)) (ops (MulS2 x dy))))

addSDual ::
  ( HM.Numeric s,
    OS.Shape sh,
    Ops s DeltaF dual
  ) =>
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s)
addSDual (D x dx) (D y dy) = D (addS x y) (ops (AddS dx dy))

negateSDual ::
  ( Num s,
    Ops s DeltaF dual,
    OS.Shape sh,
    Storable s
  ) =>
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s)
negateSDual (D x dx) = D (OS.mapA negate x) (ops (NegateS dx))

minusSDual ::
  (HM.Numeric s, OS.Shape sh, Ops s DeltaF dual) =>
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s)
minusSDual x y = addSDual x (negateSDual y)

reluSDual ::
  ( Num s,
    Ord s,
    Ops s DeltaF dual,
    OS.Shape sh,
    Storable s
  ) =>
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s)
reluSDual (D x dx) =
  D
    (reluS x)
    (ops (ScalePointwiseS dx (OS.mapA (\s -> if s > 0 then 1 else 0) x)))

expSDual ::
  (Storable s, OS.Shape sh, Floating s, Ops s DeltaF dual) =>
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s)
expSDual (D x dx) =
  D exp_x (ops (ScalePointwiseS dx exp_x))
  where
    exp_x = OS.mapA exp x

logSDual ::
  (Storable s, OS.Shape sh, Floating s, Ops s DeltaF dual) =>
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s)
logSDual (D x dx) =
  D (OS.mapA log x) (ops (ScalePointwiseS dx (OS.mapA recip x)))

logSumExpDual ::
  ( Floating s,
    Ops s DeltaF dual,
    HM.Numeric s,
    KnownNat m,
    KnownNat n
  ) =>
  Dual (dual s) (OS.Array '[m, n] s) ->
  Dual (dual s) (OS.Array '[m, 1] s)
logSumExpDual =
  logSDual . sumAcross . expSDual

constS ::
  (Ops s DeltaF dual, OS.Shape sh, Storable s) =>
  OS.Array sh s ->
  Dual (dual s) (OS.Array sh s)
constS x = D x (ops ZeroS)

sumAcross ::
  ( Ops s DeltaF dual,
    HM.Numeric s,
    KnownNat m,
    KnownNat n
  ) =>
  Dual (dual s) (OS.Array '[m, n] s) ->
  Dual (dual s) (OS.Array '[m, 1] s)
sumAcross = (`mulSDual` constS (OS.constant 1))

dotAcross ::
  (Ops s DeltaF dual, HM.Numeric s, KnownNat m, KnownNat n) =>
  Dual (dual s) (OS.Array '[m, n] s) ->
  Dual (dual s) (OS.Array '[m, n] s) ->
  Dual (dual s) (OS.Array '[m, 1] s)
dotAcross x y = sumAcross (pointwiseMulSDual x y)

pointwiseMulSDual ::
  (Storable s, OS.Shape sh, Num s, Ops s DeltaF dual) =>
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s) ->
  Dual (dual s) (OS.Array sh s)
pointwiseMulSDual (D x dx) (D y dy) =
  D
    (OS.zipWithA (*) x y)
    (ops (AddS (ops (ScalePointwiseS dy x)) (ops (ScalePointwiseS dx y))))

softMaxCrossEntropy ::
  forall s dual labels samples m.
  ( Floating s,
    Ops s DeltaF dual,
    KnownNat labels,
    KnownNat samples,
    HM.Numeric s,
    DualMonad dual m
  ) =>
  -- | Log predicted probability
  Dual (dual s) (OS.Array [samples, labels] s) ->
  -- | One hot
  OS.Array [samples, labels] s ->
  m s (Dual (dual s) s)
softMaxCrossEntropy logProbs groundTruth = do
  r <- partialsoftMaxCrossEntropy logProbs groundTruth
  pure (sumElementsS r)

partialsoftMaxCrossEntropy ::
  forall s dual labels samples m.
  ( Floating s,
    Ops s DeltaF dual,
    KnownNat labels,
    KnownNat samples,
    HM.Numeric s,
    DualMonad dual m
  ) =>
  -- | Log predicted probability
  Dual (dual s) (OS.Array [samples, labels] s) ->
  -- | One hot
  OS.Array [samples, labels] s ->
  m s (Dual (dual s) (OS.Array [samples, 1] s))
partialsoftMaxCrossEntropy logProbs' groundTruth = do
  logProbs <- dLet logProbs'

  let totalLogProb :: Dual (dual s) (OS.Array [samples, 1] s)
      totalLogProb = logSumExpDual logProbs

      crossEntropyComponents :: Dual (dual s) (OS.Array [samples, 1] s)
      crossEntropyComponents = logProbs `dotAcross` constS groundTruth

  pure (crossEntropyComponents `minusSDual` totalLogProb)

test =
  let x = OS.fromList [1, 2, 3, 4, 5, 6] :: OS.Array [3, 2] Double
      y = OS.fromList [7, 8, 9, 10, 11, 12]
      dy = OS.mapA (/ 1000000) $ OS.fromList [-7, 8, -9, 10, -11, 1200]

      d_dr = 1.0

      (_, d_dy) = dSingleArg y d_dr (flip softMaxCrossEntropy x)
      (r, dr) = dSingleArgForward y dy (flip softMaxCrossEntropy x)
      (r_plus_dr, _) =
        dSingleArgForward
          (y `addS` dy)
          dy
          (flip softMaxCrossEntropy x)

      p1 = OS.fromList [10, 0] :: OS.Array [1, 2] Double
      pb = OS.fromList [0, 0] :: OS.Array [1, 2] Double
      p2 = OS.fromList [0, 10] :: OS.Array [1, 2] Double

      c1 = OS.fromList [1, 0] :: OS.Array [1, 2] Double
      c2 = OS.fromList [0, 1] :: OS.Array [1, 2] Double
   in ( dr * d_dr,
        OS.sumA (OS.zipWithA (*) dy d_dy),
        dr,
        r_plus_dr - r,
        do
          p <- [p1, pb, p2]
          c <- [c1, c2]

          let (rr, _) =
                dSingleArgForward
                  p
                  (OS.mapA (const 0) p)
                  (flip softMaxCrossEntropy c)

          pure rr
      )

--

example :: (Double, (Double, Double))
example = dDoubleArg (10, 20) 1 (uncurry foo)

example2 ::
  ( OS.Array [2, 2] Double,
    (OS.Array [3, 1] Double, OS.Array [1, 2] Double)
  )
example2 =
  dDoubleArg
    ( OS.fromList [5, 6, 7] :: OS.Array [3, 1] Double,
      OS.fromList [10, 20] :: OS.Array [1, 2] Double
    )
    (OS.fromList [1, 2, 3, 4] :: OS.Array [2, 2] Double)
    baz

example2Record ::
  ( HM.Numeric s,
    KnownNat q,
    KnownNat l,
    KnownNat n,
    KnownNat m,
    KnownNat p
  ) =>
  ARecord
    (OS.Array '[m, n] s)
    (OS.Array '[n, p] s)
    (OS.Array '[p, q] s) ->
  OS.Array '[l, q] s ->
  ( OS.Array '[l, q] s,
    ARecord
      (OS.Array '[m, n] s)
      (OS.Array '[n, p] s)
      (OS.Array '[p, q] s)
  )
example2Record (ARecord x y z) t =
  runDualMonadAdapt (B.bipure ARecord ARecord <<*>> adaptArg x <<*>> adaptArg y <<*>> adaptArg z) t bazRecord

example3 :: (Double, Vector Double)
example3 = dSingleArg (HM.fromList [10, 20]) 1 bar

example3Forward1 :: (Double, Double)
example3Forward1 =
  dSingleArgForward (HM.fromList [10, 20]) (HM.fromList [1, 0]) bar

example3Forward2 :: (Double, Double)
example3Forward2 =
  dSingleArgForward (HM.fromList [10, 20]) (HM.fromList [0, 1]) bar

dSingleArg ::
  (HM.Numeric s, Known (IsScalarOf s t), Known (IsScalarOf s r)) =>
  -- | Primal argument
  t ->
  -- | Incoming gradient (usually r ~ Double and r = 1)
  r ->
  -- | Function to be differentiated
  (Dual (Delta DeltaF s) t -> DualMonadGradient s (Dual (Delta DeltaF s) r)) ->
  -- | Result of original function, and its gradient
  (r, t)
dSingleArg = runDualMonadAdapt . adaptArg

dDoubleArg ::
  ( HM.Numeric s,
    Known (IsScalarOf s t1),
    Known (IsScalarOf s t2),
    Known (IsScalarOf s r)
  ) =>
  (t1, t2) ->
  r ->
  ( (D t1 (Delta DeltaF s t1), Dual (Delta DeltaF s) t2) ->
    DualMonadGradient s (Dual (Delta DeltaF s) r)
  ) ->
  (r, (t1, t2))
dDoubleArg (t1, t2) = runDualMonadAdapt (liftB2 (adaptArg t1) (adaptArg t2))

dMultiArg ::
  ( HM.Numeric s,
    Known (IsScalarOf s t1),
    Known (IsScalarOf s t2),
    Known (IsScalarOf s r)
  ) =>
  Data.Vector.Vector t1 ->
  Data.Vector.Vector t2 ->
  r ->
  ( ( Data.Vector.Vector (Dual (Delta DeltaF s) t1),
      Data.Vector.Vector (Dual (Delta DeltaF s) t2)
    ) ->
    DualMonadGradient s (Dual (Delta DeltaF s) r)
  ) ->
  (r, (Data.Vector.Vector t1, Data.Vector.Vector t2))
dMultiArg t1s t2s =
  runDualMonadAdapt
    ( liftB2
        (sequenceArgAdaptorVector (fmap adaptArg t1s))
        (sequenceArgAdaptorVector (fmap adaptArg t2s))
    )

-- We have test results recorded for the tests below in TestSingleGradient
-- and for quad also in TestSimpleDescent (but for that one we need
-- the simplest gradient descent optimizer).

testAgain :: [(String, (Double, Vector Double), (Double, Vector Double))]
testAgain =
  testThreeVariantsOfSumElement
    ++ testTwoVariantsOfatanReadme
    ++ testQuadSimple

testAgainForward :: [(String, (Double, Double), (Double, Double))]
testAgainForward =
  testTwoVariantsOfatanReadmeForward
    ++ testTwoVariantsOfatanReadmeForward
    ++ testQuadSimpleForward

quad ::
  (DualMonad dual m, HM.Numeric s, Ops s DeltaF dual) =>
  Dual (dual s) s ->
  Dual (dual s) s ->
  m s (Dual (dual s) s)
quad x y = do
  x2 <- dLet $ square x
  y2 <- y .* y
  tmp <- x2 .+ y2
  tmp .+ 5

quadVariables ::
  (DualMonad dual m, HM.Numeric s, Ops s DeltaF dual) =>
  ( Data.Vector.Vector (Dual (dual s) s),
    Data.Vector.Vector (Dual (dual s) t2)
  ) ->
  m s (Dual (dual s) s)
quadVariables (xyzVector, _) = do
  let x = xyzVector V.! 0
      y = xyzVector V.! 1
  quad x y

testQuadSimple ::
  [(String, (Double, Vector Double), (Double, Vector Double))]
testQuadSimple =
  let t = V.fromList [2, 3]
      result = (18, V.fromList [4, 6])
      (r, (res1, _ :: Data.Vector.Vector Double)) =
        dMultiArg t V.empty 1 quadVariables
   in [ ("quadSimple", (r, V.convert res1), result)
      ]

testQuadSimpleForward ::
  [(String, (Double, Double), (Double, Double))]
testQuadSimpleForward =
  let t = V.fromList [2, 3]
      result = (18, 26)
   in [ ( "quadSimple",
          dMultiArgForward (t, t) (V.empty, V.empty) quadVariables,
          result
        )
      ]

foldl'0 ::
  (HM.Numeric s, Ops s DeltaF dual) =>
  (Dual (dual s) s -> Dual (dual s) s -> Dual (dual s) s) ->
  Dual (dual s) s ->
  Dual (dual s) (Vector s) ->
  Dual (dual s) s
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (D p (ops (Index0 v' ix k))) acc
   in V.ifoldl' g uu' v

altSumElements0 ::
  (HM.Numeric s, Ops s DeltaF dual) =>
  Dual (dual s) (Vector s) ->
  Dual (dual s) s
altSumElements0 = foldl'0 (+) 0

vec_omit_scalarSum ::
  (RealFloat s, Ops s DeltaF dual) =>
  ( Data.Vector.Vector (Dual (dual s) s),
    Data.Vector.Vector (Dual (dual s) t2)
  ) ->
  Dual (dual s) s
vec_omit_scalarSum (v, _) = V.foldl' (+) 0 v

testThreeVariantsOfSumElement ::
  [(String, (Double, Vector Double), (Double, Vector Double))]
testThreeVariantsOfSumElement =
  let sumElementsV = dLet . sumElements
      altSumElementsV = dLet . altSumElements0
      vec_omit_scalarSumM = dLet . vec_omit_scalarSum
      t = V.fromList [1, 1, 3]
      tMulti = V.fromList [1, 1, 3]
      result = (5, V.fromList [1, 1, 1])
      (r, (res1, _ :: Data.Vector.Vector Double)) =
        dMultiArg tMulti V.empty 1 vec_omit_scalarSumM
   in [ ("sumElement", dSingleArg t 1 sumElementsV, result),
        ("altSumElement", dSingleArg t 1 altSumElementsV, result),
        ("vec_omit_scalarSum", (r, V.convert res1), result)
      ]

testThreeVariantsOfSumElementForward ::
  [(String, (Double, Double), (Double, Double))]
testThreeVariantsOfSumElementForward =
  let sumElementsV = dLet . sumElements
      altSumElementsV = dLet . altSumElements0
      vec_omit_scalarSumM = dLet . vec_omit_scalarSum
      t = V.fromList [1.1, 2.2, 3.3 :: Double]
      tMulti = V.fromList [1, 1, 3]
      result = (4.9375516951604155, 7.662345305800865)
   in [ ("sumElementForward", dSingleArgForward t t sumElementsV, result),
        ("altSumElementForward", dSingleArgForward t t altSumElementsV, result),
        ( "vec_omit_scalarSumForward",
          dMultiArgForward (tMulti, tMulti) (V.empty, V.empty) vec_omit_scalarSumM,
          result
        )
      ]

atanReadmeOriginal :: RealFloat a => a -> a -> a -> Data.Vector.Vector a
atanReadmeOriginal x y z =
  let w = x * sin y
   in V.fromList [atan2 z w, z * x]

atanReadmeD ::
  (RealFloat s, Ops s DeltaF dual) =>
  Dual (dual s) s ->
  Dual (dual s) s ->
  Dual (dual s) s ->
  Data.Vector.Vector (Dual (dual s) s)
atanReadmeD x y z = atanReadmeOriginal x y z

atanReadmeVariables ::
  (RealFloat s, Ops s DeltaF dual) =>
  ( Data.Vector.Vector (Dual (dual s) s),
    Data.Vector.Vector (Dual (dual t2) t2)
  ) ->
  Data.Vector.Vector (Dual (dual s) s)
atanReadmeVariables (xyzVector, _) =
  let x = xyzVector V.! 0
      y = xyzVector V.! 1
      z = xyzVector V.! 2
   in atanReadmeOriginal x y z

sumElementsOfDualNumbers ::
  (Num s, Ops s DeltaF dual) =>
  Data.Vector.Vector (Dual (dual s) s) ->
  Dual (dual s) s
sumElementsOfDualNumbers = V.foldl' (+) 0

atanReadmeScalar ::
  (RealFloat s, Ops s DeltaF dual) =>
  ( Data.Vector.Vector (Dual (dual s) s),
    Data.Vector.Vector (Dual (dual s) s)
  ) ->
  Dual (dual s) s
atanReadmeScalar = sumElementsOfDualNumbers . atanReadmeVariables

atanReadmeM ::
  (DualMonad dual m, Ops s DeltaF dual, HM.Numeric s, RealFloat s) =>
  ( Data.Vector.Vector (Dual (dual s) s),
    Data.Vector.Vector (Dual (dual s) s)
  ) ->
  m s (Dual (dual s) s)
atanReadmeM = dLet . atanReadmeScalar

indexNoM ::
  (HM.Numeric s, Ops s DeltaF dual) =>
  Dual (dual s) (Vector s) ->
  Int ->
  Dual (dual s) s
indexNoM (D v v') i =
  D (HM.atIndex v i) (ops (Index0 v' i (HM.size v)))

seq1 ::
  (HM.Numeric s, Ops s DeltaF dual) =>
  Data.Vector.Vector (Dual (dual s) s) ->
  Dual (dual s) (Vector s)
seq1 v =
  D
    (HM.fromList $ map (\(D x _) -> x) $ Data.Vector.toList v)
    (ops $ Seq1 $ fmap (\(D _ x) -> x) v)

vatanReadmeM ::
  (DualMonad dual m, HM.Numeric s, RealFloat s, Ops s DeltaF dual) =>
  Dual (dual s) (Vector s) ->
  m s (Dual (dual s) s)
vatanReadmeM xyzVector = do
  let x = indexNoM xyzVector 0
      y = indexNoM xyzVector 1
      z = indexNoM xyzVector 2
      v = seq1 $ atanReadmeOriginal x y z
  dLet $ sumElements v

-- Dot product with a constant vector. Was used in a previous version
-- of the test.
infixr 8 <.>!!

(<.>!!) ::
  (HM.Numeric s, Ops s DeltaF dual) =>
  Dual (dual s) (Vector s) ->
  Vector s ->
  Dual (dual s) s
(<.>!!) (D u u') v = D (u HM.<.> v) (ops (Dot1 v u'))

testTwoVariantsOfatanReadme ::
  [(String, (Double, Vector Double), (Double, Vector Double))]
testTwoVariantsOfatanReadme =
  let t = V.fromList [1.1, 2.2, 3.3]
      tMulti = V.fromList [1.1, 2.2, 3.3]
      result =
        ( 4.9375516951604155,
          V.fromList
            [3.071590389300859, 0.18288422990948425, 1.1761365368997136]
        )
      (r, (res1, _ :: Data.Vector.Vector Double)) =
        dMultiArg tMulti V.empty 1 atanReadmeM
   in [ ("atanReadme", (r, V.convert res1), result),
        ("vatanReadme", dSingleArg t 1 vatanReadmeM, result)
      ]

testTwoVariantsOfatanReadmeForward ::
  [(String, (Double, Double), (Double, Double))]
testTwoVariantsOfatanReadmeForward =
  let t = V.fromList [1.1, 2.2, 3.3]
      tMulti = V.fromList [1.1, 2.2, 3.3]
      result = (4.9375516951604155, 7.662345305800865)
   in [ ( "atanReadmeForward",
          dMultiArgForward (tMulti, tMulti) (V.empty, V.empty) atanReadmeM,
          result
        ),
        ("vatanReadmeForward", dSingleArgForward t t vatanReadmeM, result)
      ]

-- These belong in some Shaped module

addS ::
  (OS.Shape sh, HM.Numeric s) =>
  OS.Array sh s ->
  OS.Array sh s ->
  OS.Array sh s
addS = OS.zipWithA (+)

mulS ::
  (HM.Numeric s, KnownNat m, KnownNat n, KnownNat p) =>
  OS.Array [m, n] s ->
  OS.Array [n, p] s ->
  OS.Array [m, p] s
mulS = Data.Array.ShapedS.MatMul.matMul

transposeS :: forall s m n. (HM.Numeric s, KnownNat n, KnownNat m) => OS.Array [m, n] s -> OS.Array [n, m] s
transposeS = OS.fromVector . HM.flatten . HM.tr' . matrixS

reluS ::
  (Storable s, OS.Shape sh, Num s, Ord s) =>
  OS.Array sh s ->
  OS.Array sh s
reluS = OS.mapA (\x -> if x > 0 then x else 0)

matrixS ::
  forall s m n.
  (HM.Numeric s, KnownNat n, KnownNat m) =>
  OS.Array [m, n] s ->
  HM.Matrix s
matrixS =
  let n = fromIntegral $ natVal (Proxy :: Proxy n)
   in (HM.reshape n . OS.toVector)