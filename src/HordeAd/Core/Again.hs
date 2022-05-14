{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
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
import Data.Kind (Type)
import Data.List (foldl')
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

knownDeltaId :: DeltaId s t -> s `IsScalarOf` t
knownDeltaId DeltaId {} = known

instance Known (a `IsScalarOf` a) where
  known = SScalar

instance Known (a `IsScalarOf` Vector a) where
  known = SVector

instance (OS.Shape sh, Storable a) => Known (a `IsScalarOf` OS.Array sh a) where
  known = SShapedS

instance Known (Unit a) where
  known = Unit

data IsScalarOf (s :: Type) (t :: Type) where
  SScalar :: IsScalarOf s s
  SVector :: IsScalarOf s (Vector s)
  -- I'm doubtful this Storable constraint is really needed.
  -- OS.toVector and OS.fromVector shouldn't require it.  See, for
  -- example,
  --
  -- https://github.com/tomjaguarpaw/orthotope/commit/10a65b60daa6b072093490275818afe0f8d38c09
  SShapedS :: (OS.Shape sh, Storable s) => IsScalarOf s (OS.Array sh s)

deriving instance Show (IsScalarOf s t)

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
  (forall tt. dual tt -> dual' tt) ->
  DeltaF s dual t ->
  DeltaF s dual' t
mapDeltaF f = \case
  Zero0 -> Zero0
  Add0 duals duals' -> Add0 (f duals') (f duals)
  Scale0 s duals -> Scale0 s (f duals)
  Index0 dual n i -> Index0 (f dual) n i
  Add1 dual dual' -> Add1 (f dual') (f dual)
  Scale1 s dual -> Scale1 s (f dual)
  Konst1 duals n -> Konst1 (f duals) n
  Dot1 vec dual -> Dot1 vec (f dual)
  SumElements1 dual n -> SumElements1 (f dual) n
  Seq1 vec -> Seq1 (fmap f vec)
  AddS d1 d2 -> AddS (f d1) (f d2)
  NegateS d -> NegateS (f d)
  KonstS s -> KonstS (f s)
  ZeroS -> ZeroS
  AppendS a1 a2 -> AppendS (f a1) (f a2)
  MulS1 d a -> MulS1 (f d) a
  MulS2 a d -> MulS2 a (f d)
  ScalePointwiseS d a -> ScalePointwiseS (f d) a
  SumElementsS d -> SumElementsS (f d)

data DeltaId (s :: Type) (t :: Type) where
  DeltaId :: Known (s `IsScalarOf` t) => Int -> DeltaId s t

deriving instance Eq (DeltaId s t)

deriving instance Ord (DeltaId s t)

deriving instance Show (DeltaId s t)

succDeltaId :: DeltaId s t -> DeltaId s t
succDeltaId (DeltaId i) = DeltaId (i + 1)

data DeltaBinding s where
  DeltaBinding :: DeltaId s t -> Delta s t -> DeltaBinding s

data Delta (s :: Type) (t :: Type) where
  Delta :: DeltaF s (Delta s) t -> Delta s t
  Var :: DeltaId s t -> Delta s t

knownDelta :: Delta s t -> s `IsScalarOf` t
knownDelta = \case
  Delta df -> case df of
    Zero0 -> SScalar
    Add0 {} -> SScalar
    Scale0 {} -> SScalar
    Index0 {} -> SScalar
    Add1 {} -> SVector
    Scale1 {} -> SVector
    Konst1 {} -> SVector
    Dot1 {} -> SScalar
    SumElements1 {} -> SScalar
    Seq1 {} -> SVector
    AddS {} -> SShapedS
    NegateS {} -> SShapedS
    KonstS {} -> SShapedS
    ZeroS {} -> SShapedS
    AppendS {} -> SShapedS
    MulS1 {} -> SShapedS
    MulS2 {} -> SShapedS
    ScalePointwiseS {} -> SShapedS
    SumElementsS {} -> SScalar
  Var di -> case di of (DeltaId _) -> known

data DeltaMap s = DeltaMap
  { dmScalar :: Map.Map (DeltaId s s) s,
    dmVector :: Map.Map (DeltaId s (Vector s)) (Vector s),
    dmShapedS :: Map.Map Int (Vector s)
  }
  deriving (Show)

singleton :: DeltaId s t -> t -> DeltaMap s
singleton dId t = case knownDeltaId dId of
  SScalar -> DeltaMap (Map.singleton dId t) Map.empty Map.empty
  SVector -> DeltaMap Map.empty (Map.singleton dId t) Map.empty
  SShapedS -> DeltaMap Map.empty Map.empty (Map.singleton i (OS.toVector t))
    where
      DeltaId i = dId

deltaMapLookup ::
  DeltaId s t ->
  DeltaMap s ->
  Maybe t
deltaMapLookup dId m = case knownDeltaId dId of
  SScalar -> Map.lookup dId (dmScalar m)
  SVector -> Map.lookup dId (dmVector m)
  SShapedS -> fmap OS.fromVector (Map.lookup i (dmShapedS m))
    where
      DeltaId i = dId

deltaMapDelete ::
  DeltaId s t ->
  DeltaMap s ->
  DeltaMap s
deltaMapDelete dId (DeltaMap ms mv msh) = case knownDeltaId dId of
  SScalar -> DeltaMap (Map.delete dId ms) mv msh
  SVector -> DeltaMap ms (Map.delete dId mv) msh
  SShapedS -> DeltaMap ms mv (Map.delete i msh)
    where
      DeltaId i = dId

deltaMapAlter ::
  (Maybe t -> Maybe t) ->
  DeltaId s t ->
  DeltaMap s ->
  DeltaMap s
deltaMapAlter f di m = case knownDeltaId di of
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
  (forall tt. dual tt -> tt -> deltaMap_s -> deltaMap_s) ->
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

-- Somewhat annoying that we need this r parameter to satisfy
-- functional dependencies.
newtype MonoidMap r m t = MonoidMap {unMonoidMap :: t -> m}

-- A more abstract way of writing evalDeltaF
evalDeltaFM ::
  forall dual s m t.
  (HM.Numeric s, Monoid m) =>
  (forall tt. dual tt -> MonoidMap s m tt) ->
  DeltaF s dual t ->
  MonoidMap s m t
evalDeltaFM f' = evalDeltaFM1 . mapDeltaF f'

evalDeltaFM1 ::
  forall s m t.
  (HM.Numeric s, Monoid m) =>
  DeltaF s (MonoidMap s m) t ->
  MonoidMap s m t
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

instance (HM.Numeric r, Monoid m) => Ops (DeltaF r) (MonoidMap r m) where
  ops = evalDeltaFM1

-- accumulate has the special property
accumulate ::
  HM.Numeric s =>
  DeltaId s t ->
  t ->
  DeltaMap s ->
  DeltaMap s
accumulate di t =
  deltaMapAlter
    ( \case
        Nothing -> Just t
        Just t' -> case knownDeltaId di of
          SScalar -> Just (t + t')
          SVector -> Just (t `HM.add` t')
          SShapedS -> Just (t `addS` t')
    )
    di

-- eval has the special property
eval ::
  HM.Numeric s =>
  Delta s t ->
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
  HM.Numeric s =>
  ArgAdaptor s arg dual ->
  t ->
  (dual -> DualMonadGradient s (D t' (Delta s t))) ->
  (t', arg)
runDualMonadAdapt aa g f =
  let (lookup', arg) = runArgAdaptor aa
      m = f arg
      (t', dm) = runDualMonadS g m
   in (t', lookup' dm)

runDualMonadS ::
  HM.Numeric s =>
  t ->
  DualMonadGradient s (D t' (Delta s t)) ->
  (t', DeltaMap s)
runDualMonadS g e =
  let ((t, dId), bs) = runDualMonadM $ do
        D t' delta <- e
        dId' <- deltaLetId delta
        pure (t', dId')
   in (t, runDelta (deltaBindings bs) (singleton dId g))

runDualMonad ::
  HM.Numeric s =>
  t ->
  DualMonadGradient s (D s (Delta s t)) ->
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

class Monad m => DualMonad (dual :: Type -> Type) m where
  deltaLet :: dual t -> m (dual t)

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

bind :: DeltaId s t -> Delta s t -> DualMonadGradient s ()
bind dId delta =
  DualMonadGradient $
    modify
      ( \st ->
          st {deltaBindings = DeltaBinding dId delta : deltaBindings st}
      )

deltaLetId :: Delta s t -> DualMonadGradient s (DeltaId s t)
deltaLetId delta = do
  dId <- fresh (knownDelta delta)
  bind dId delta
  pure dId

instance DualMonad (Delta s) (DualMonadGradient s) where
  deltaLet delta = fmap Var (deltaLetId delta)

newtype DualMonadValue r a = DualMonadValue
  {runDualMonadValue :: Identity a}
  deriving newtype (Monad, Functor, Applicative)

data Unit (t :: Type) = Unit

instance DualMonad Unit (DualMonadValue r) where
  deltaLet = pure

newtype DualMonadForward a = DualMonadForward (Identity a)
  deriving newtype (Monad, Functor, Applicative)

runDualMonadForward :: DualMonadForward a -> a
runDualMonadForward (DualMonadForward m) = runIdentity m

instance DualMonad Concrete DualMonadForward where
  deltaLet = pure

dSingleArgForward ::
  t ->
  t ->
  ( Dual Concrete t ->
    DualMonadForward (D r (Concrete r))
  ) ->
  (r, r)
dSingleArgForward t t' f =
  let D r d = runDualMonadForward (f (D t (concrete t')))
   in (r, unConcrete d)

dMultiArgForward ::
  (Data.Vector.Vector t, Data.Vector.Vector t) ->
  (Data.Vector.Vector t', Data.Vector.Vector t') ->
  ( ( Data.Vector.Vector (D t (Concrete t)),
      Data.Vector.Vector (D t' (Concrete t'))
    ) ->
    DualMonadForward (D r (Concrete r))
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

dLetS ::
  forall (dual :: Type -> Type) t m.
  DualMonad dual m =>
  Dual dual t ->
  m (Dual dual t)
dLetS (D x y) = do
  y' <- deltaLet y
  pure (D x y')

dLet ::
  forall dual t m.
  DualMonad dual m =>
  Dual dual t ->
  m (Dual dual t)
dLet = dLetS

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
  ArgAdaptor s t (D t (Delta s t))
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

class Ops f dual where
  ops :: f dual t -> dual t

newtype Concrete (t :: Type) where
  C :: {unConcrete :: t} -> Concrete t

concrete :: t -> Concrete t
concrete = C

instance (Num r, HM.Numeric r) => Ops (DeltaF r) Concrete where
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

instance r' ~ r => Ops (DeltaF r') (Delta r) where
  ops = Delta

baz ::
  ( Ops (DeltaF s) dual,
    HM.Numeric s,
    KnownNat l,
    KnownNat n,
    KnownNat m,
    KnownNat p,
    Applicative dualMonadGradient
  ) =>
  ( Dual dual (OS.Array '[m, n] s),
    Dual dual (OS.Array '[n, p] s)
  ) ->
  dualMonadGradient (Dual dual (OS.Array '[l, p] s))
baz (x, y) = pure (konstS 2 `mulSDual` x `mulSDual` y)

data ARecord a b c = ARecord a b c

bazRecord ::
  ( Applicative f,
    Ops (DeltaF s) dual,
    HM.Numeric s,
    KnownNat l,
    KnownNat m,
    KnownNat n,
    KnownNat p,
    KnownNat q
  ) =>
  ARecord
    (Dual dual (OS.Array '[m, n] s))
    (Dual dual (OS.Array '[n, p] s))
    (Dual dual (OS.Array '[p, q] s)) ->
  f (Dual dual (OS.Array '[l, q] s))
bazRecord (ARecord x y z) = pure (konstS 2 `mulSDual` x `mulSDual` y `mulSDual` z)

bar ::
  (HM.Numeric s, DualMonad dual m, Ops (DeltaF s) dual) =>
  Dual dual (Vector s) ->
  m (Dual dual s)
bar v = do
  x <- index v 0
  y <- index v 1
  foo x y

foo ::
  (DualMonad dual m, Num s, Ops (DeltaF s) dual) =>
  Dual dual s ->
  Dual dual s ->
  m (Dual dual s)
foo x y = do
  x2 <- x .* x
  x2y <- x2 .* y
  x2y .+ y

-- d Functions (meaning, dual s -> dual s, low-level API)

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

dAdd0 :: Ops (DeltaF s) dual => dual s -> dual s -> dual s
dAdd0 x y = ops (Add0 x y)

dScale0 :: Ops (DeltaF s) dual => s -> dual s -> dual s
dScale0 x y = ops (Scale0 x y)

dZero0 :: Ops (DeltaF s) dual => dual s
dZero0 = ops Zero0

dSumElements :: Ops (DeltaF s) dual => dual (Vector s) -> Int -> dual s
dSumElements v n = ops (SumElements1 v n)

-- D number functions (meaning, D -> Dual, high level API)

instance (Num s, Ops (DeltaF s) dual) => Num (D s (dual s)) where
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

instance (Real s, Ops (DeltaF s) dual) => Real (D s (dual s))

instance (Fractional s, Ops (DeltaF s) dual) => Fractional (D s (dual s)) where
  D u u' / D v v' =
    let recipSq = recip (v * v)
     in D
          (u / v)
          (dAdd0 (dScale0 (v * recipSq) u') (dScale0 (- u * recipSq) v'))

instance (Floating s, Ops (DeltaF s) dual) => Floating (D s (dual s)) where
  sin (D u u') = D (sin u) (dScale0 (cos u) u')

instance (RealFrac s, Ops (DeltaF s) dual) => RealFrac (D s (dual s))

instance (RealFloat s, Ops (DeltaF s) dual) => RealFloat (D s (dual s)) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
     in D (atan2 u v) (dAdd0 (dScale0 (- u * t) v') (dScale0 (v * t) u'))

-- TODO (not really needed on its own, but something like that
-- would be required for scale1 and Num on Vectors):
dScale1 ::
  (HM.Numeric s, Ops (DeltaF s) dual) =>
  (Vector s) ->
  dual (Vector s) ->
  dual (Vector s)
dScale1 x y = ops (Scale1 (HM.sumElements x) y) -- TODO

-- This causes "Overlapping instances". Perhaps the above Num should be
-- only defined for Double and Float, not for @s@?
{-
instance (Num (Vector s), Ops (DeltaF s) dual)
         => Num (D (Vector s) (dual (Vector s))) where
  D x x' * D y y' =
    D (x * y) (ops (Add1 (dScale1 x y') (dScale1 y x')))
-}

constant :: Ops (DeltaF s) dual => a -> D a (dual s)
constant k = D k dZero0

-- TODO: this is probably not the right type for both scalars and vectors?
scale0 ::
  (Num s, Ops (DeltaF s) dual) =>
  s ->
  Dual dual s ->
  Dual dual s
scale0 a (D u u') = D (a * u) (dScale0 a u')

scale1 ::
  (HM.Numeric s, Num (Vector s), Ops (DeltaF s) dual) =>
  Vector s ->
  Dual dual (Vector s) ->
  Dual dual (Vector s)
scale1 a (D u u') = D (a * u) (dScale1 a u')

-- MK: if this cannot work on vectors, perhaps @square0@ would be a better name
-- and then we can add @square1@.
square :: (Num s, Ops (DeltaF s) dual) => Dual dual s -> Dual dual s
square (D u u') = D (u * u) (dScale0 (2 * u) u')

squaredDifference ::
  (Num s, Ops (DeltaF s) dual) =>
  s ->
  Dual dual s ->
  Dual dual s
squaredDifference targ res = square $ res - constant targ

(.+) ::
  (DualMonad dual m, Num s, Ops (DeltaF s) dual) =>
  Dual dual s ->
  Dual dual s ->
  m (Dual dual s)
D x x' .+ D y y' =
  dLet $ D (x + y) (ops (Add0 x' y'))

(.*) ::
  (DualMonad dual m, Num s, Ops (DeltaF s) dual) =>
  Dual dual s ->
  Dual dual s ->
  m (Dual dual s)
D x x' .* D y y' =
  dLet $ D (x * y) (ops (Add0 (ops (Scale0 y x')) (ops (Scale0 x y'))))

index ::
  (HM.Numeric s, Ops (DeltaF s) dual, DualMonad dual m) =>
  Dual dual (Vector s) ->
  Int ->
  m (Dual dual s)
index (D v v') i = dLet $ D (HM.atIndex v i) (ops (Index0 v' i (HM.size v)))

sumElements ::
  (HM.Numeric s, Ops (DeltaF s) dual) =>
  Dual dual (Vector s) ->
  Dual dual s
sumElements (D u u') = D (HM.sumElements u) (dSumElements u' (HM.size u))

sumElementsS ::
  (HM.Numeric s, Ops (DeltaF s) dual, OS.Shape sh) =>
  Dual dual (OS.Array sh s) ->
  Dual dual s
sumElementsS (D u u') = D (OS.sumA u) (ops (SumElementsS u'))

konstS ::
  (Storable s, OS.Shape sh, Ops (DeltaF s) dual) =>
  Dual dual s ->
  Dual dual (OS.Array sh s)
konstS (D u u') = D (OS.constant u) (ops (KonstS u'))

mkonstS ::
  ( Storable s,
    OS.Shape sh,
    Ops (DeltaF s) dual,
    DualMonad dual m
  ) =>
  Dual dual s ->
  m (Dual dual (OS.Array sh s))
mkonstS (D u u') = dLet $ D (OS.constant u) (ops (KonstS u'))

mulSDual ::
  (Ops (DeltaF s) dual, HM.Numeric s, KnownNat p, KnownNat m, KnownNat n) =>
  Dual dual (OS.Array [m, n] s) ->
  Dual dual (OS.Array [n, p] s) ->
  Dual dual (OS.Array [m, p] s)
mulSDual (D x dx) (D y dy) =
  D (mulS x y) (ops (AddS (ops (MulS1 dx y)) (ops (MulS2 x dy))))

addSDual ::
  ( HM.Numeric s,
    OS.Shape sh,
    Ops (DeltaF s) dual
  ) =>
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s)
addSDual (D x dx) (D y dy) = D (addS x y) (ops (AddS dx dy))

negateSDual ::
  ( Num s,
    Ops (DeltaF s) dual,
    OS.Shape sh,
    Storable s
  ) =>
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s)
negateSDual (D x dx) = D (OS.mapA negate x) (ops (NegateS dx))

minusSDual ::
  (HM.Numeric s, OS.Shape sh, Ops (DeltaF s) dual) =>
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s)
minusSDual x y = addSDual x (negateSDual y)

reluSDual ::
  ( Num s,
    Ord s,
    Ops (DeltaF s) dual,
    OS.Shape sh,
    Storable s
  ) =>
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s)
reluSDual (D x dx) =
  D
    (reluS x)
    (ops (ScalePointwiseS dx (OS.mapA (\s -> if s > 0 then 1 else 0) x)))

expSDual ::
  (Storable s, OS.Shape sh, Floating s, Ops (DeltaF s) dual) =>
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s)
expSDual (D x dx) =
  D exp_x (ops (ScalePointwiseS dx exp_x))
  where
    exp_x = OS.mapA exp x

logSDual ::
  (Storable s, OS.Shape sh, Floating s, Ops (DeltaF s) dual) =>
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s)
logSDual (D x dx) =
  D (OS.mapA log x) (ops (ScalePointwiseS dx (OS.mapA recip x)))

logSumExpDual ::
  ( Floating s,
    Ops (DeltaF s) dual,
    HM.Numeric s,
    KnownNat m,
    KnownNat n
  ) =>
  Dual dual (OS.Array '[m, n] s) ->
  Dual dual (OS.Array '[m, 1] s)
logSumExpDual =
  logSDual . sumAcross . expSDual

constS ::
  (Ops (DeltaF s) dual, OS.Shape sh, Storable s) =>
  OS.Array sh s ->
  Dual dual (OS.Array sh s)
constS x = D x (ops ZeroS)

sumAcross ::
  ( Ops (DeltaF s) dual,
    HM.Numeric s,
    KnownNat m,
    KnownNat n
  ) =>
  Dual dual (OS.Array '[m, n] s) ->
  Dual dual (OS.Array '[m, 1] s)
sumAcross = (`mulSDual` constS (OS.constant 1))

dotAcross ::
  (Ops (DeltaF s) dual, HM.Numeric s, KnownNat m, KnownNat n) =>
  Dual dual (OS.Array '[m, n] s) ->
  Dual dual (OS.Array '[m, n] s) ->
  Dual dual (OS.Array '[m, 1] s)
dotAcross x y = sumAcross (pointwiseMulSDual x y)

pointwiseMulSDual ::
  (Storable s, OS.Shape sh, Num s, Ops (DeltaF s) dual) =>
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s) ->
  Dual dual (OS.Array sh s)
pointwiseMulSDual (D x dx) (D y dy) =
  D
    (OS.zipWithA (*) x y)
    (ops (AddS (ops (ScalePointwiseS dy x)) (ops (ScalePointwiseS dx y))))

softMaxCrossEntropy ::
  forall s dual labels samples m.
  ( Floating s,
    Ops (DeltaF s) dual,
    KnownNat labels,
    KnownNat samples,
    HM.Numeric s,
    DualMonad dual m
  ) =>
  Dual dual (OS.Array [samples, labels] s) ->
  Dual dual (OS.Array [samples, labels] s) ->
  m (Dual dual s)
softMaxCrossEntropy predictions' groundTruth = do
  predictions <- dLet predictions'

  let totalProb :: Dual dual (OS.Array [samples, 1] s)
      totalProb = logSumExpDual predictions

      logs :: Dual dual (OS.Array '[samples, labels] s)
      logs = logSDual predictions

      crossEntropyComponents :: Dual dual (OS.Array '[samples, 1] s)
      crossEntropyComponents = dotAcross groundTruth logs

  pure (sumElementsS (crossEntropyComponents `minusSDual` totalProb))

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
  (HM.Numeric s, Known (IsScalarOf s t)) =>
  -- | Primal argument
  t ->
  -- | Incoming gradient (usually r ~ Double and r = 1)
  r ->
  -- | Function to be differentiated
  (Dual (Delta s) t -> DualMonadGradient s (Dual (Delta s) r)) ->
  -- | Result of original function, and its gradient
  (r, t)
dSingleArg = runDualMonadAdapt . adaptArg

dDoubleArg ::
  ( HM.Numeric s,
    Known (IsScalarOf s t1),
    Known (IsScalarOf s t2)
  ) =>
  (t1, t2) ->
  r ->
  ( (D t1 (Delta s t1), Dual (Delta s) t2) ->
    DualMonadGradient s (Dual (Delta s) r)
  ) ->
  (r, (t1, t2))
dDoubleArg (t1, t2) = runDualMonadAdapt (liftB2 (adaptArg t1) (adaptArg t2))

dMultiArg ::
  ( HM.Numeric s,
    Known (IsScalarOf s t1),
    Known (IsScalarOf s t2)
  ) =>
  Data.Vector.Vector t1 ->
  Data.Vector.Vector t2 ->
  r ->
  ( ( Data.Vector.Vector (Dual (Delta s) t1),
      Data.Vector.Vector (Dual (Delta s) t2)
    ) ->
    DualMonadGradient s (Dual (Delta s) r)
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
  (DualMonad dual m, Num s, Ops (DeltaF s) dual) =>
  Dual dual s ->
  Dual dual s ->
  m (Dual dual s)
quad x y = do
  x2 <- dLet $ square x
  y2 <- y .* y
  tmp <- x2 .+ y2
  tmp .+ 5

quadVariables ::
  (DualMonad dual m, Num s, Ops (DeltaF s) dual) =>
  ( Data.Vector.Vector (Dual dual s),
    Data.Vector.Vector (Dual dual t2)
  ) ->
  m (Dual dual s)
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
  (HM.Numeric s, Ops (DeltaF s) dual) =>
  (Dual dual s -> Dual dual s -> Dual dual s) ->
  Dual dual s ->
  Dual dual (Vector s) ->
  Dual dual s
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (D p (ops (Index0 v' ix k))) acc
   in V.ifoldl' g uu' v

altSumElements0 ::
  (HM.Numeric s, Ops (DeltaF s) dual) =>
  Dual dual (Vector s) ->
  Dual dual s
altSumElements0 = foldl'0 (+) 0

vec_omit_scalarSum ::
  (RealFloat s, Ops (DeltaF s) dual) =>
  ( Data.Vector.Vector (Dual dual s),
    Data.Vector.Vector (Dual dual t2)
  ) ->
  Dual dual s
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
  (RealFloat s, Ops (DeltaF s) dual) =>
  Dual dual s ->
  Dual dual s ->
  Dual dual s ->
  Data.Vector.Vector (Dual dual s)
atanReadmeD x y z = atanReadmeOriginal x y z

atanReadmeVariables ::
  (RealFloat s, Ops (DeltaF s) dual) =>
  ( Data.Vector.Vector (Dual dual s),
    Data.Vector.Vector (D t2 (dual t2))
  ) ->
  Data.Vector.Vector (Dual dual s)
atanReadmeVariables (xyzVector, _) =
  let x = xyzVector V.! 0
      y = xyzVector V.! 1
      z = xyzVector V.! 2
   in atanReadmeOriginal x y z

sumElementsOfDualNumbers ::
  (Num s, Ops (DeltaF s) dual) =>
  Data.Vector.Vector (Dual dual s) ->
  Dual dual s
sumElementsOfDualNumbers = V.foldl' (+) 0

atanReadmeScalar ::
  (RealFloat s, Ops (DeltaF s) dual) =>
  ( Data.Vector.Vector (Dual dual s),
    Data.Vector.Vector (Dual dual t2)
  ) ->
  Dual dual s
atanReadmeScalar = sumElementsOfDualNumbers . atanReadmeVariables

atanReadmeM ::
  (DualMonad dual m, Ops (DeltaF s) dual, RealFloat s) =>
  ( Data.Vector.Vector (Dual dual s),
    Data.Vector.Vector (Dual dual t2)
  ) ->
  m (Dual dual s)
atanReadmeM = dLet . atanReadmeScalar

indexNoM ::
  (HM.Numeric s, Ops (DeltaF s) dual) =>
  Dual dual (Vector s) ->
  Int ->
  Dual dual s
indexNoM (D v v') i =
  D (HM.atIndex v i) (ops (Index0 v' i (HM.size v)))

seq1 ::
  (HM.Numeric s, Ops (DeltaF s) dual) =>
  Data.Vector.Vector (Dual dual s) ->
  Dual dual (Vector s)
seq1 v =
  D
    (HM.fromList $ map (\(D x _) -> x) $ Data.Vector.toList v)
    (ops $ Seq1 $ fmap (\(D _ x) -> x) v)

vatanReadmeM ::
  (DualMonad dual m, HM.Numeric s, RealFloat s, Ops (DeltaF s) dual) =>
  Dual dual (Vector s) ->
  m (Dual dual s)
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
  (HM.Numeric s, Ops (DeltaF s) dual) =>
  Dual dual (Vector s) ->
  Vector s ->
  Dual dual s
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
transposeS a =
  let n = fromIntegral $ natVal (Proxy :: Proxy n)
   in (OS.fromVector . HM.flatten . HM.tr' . HM.reshape n . OS.toVector) a

reluS ::
  (Storable s, OS.Shape sh, Num s, Ord s) =>
  OS.Array sh s ->
  OS.Array sh s
reluS = OS.mapA (\x -> if x > 0 then x else 0)
