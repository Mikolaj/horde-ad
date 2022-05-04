{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

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
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Kind (Type)
import Data.List (foldl')
import qualified Data.Strict.Map as Map
import Data.Vector.Storable (Storable)
import Numeric.LinearAlgebra
  ( Vector,
  )
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

data IsScalarOf (s :: Type) (t :: Type) where
  SScalar :: IsScalarOf s s
  SVector :: IsScalarOf s (Vector s)

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

deriving instance
  (Show s, Show (dual s), Show (dual (Vector s)), Storable s) =>
  Show (DeltaF s dual t)

data DeltaId (s :: Type) (t :: Type) where
  DeltaId :: Known (s `IsScalarOf` t) => Int -> DeltaId s t

deriving instance Eq (DeltaId s t)

deriving instance Ord (DeltaId s t)

deriving instance Show (DeltaId s t)

succDeltaId :: DeltaId s t -> DeltaId s t
succDeltaId (DeltaId i) = DeltaId (i + 1)

data DeltaBinding s where
  DeltaBinding :: DeltaId s t -> Delta s t -> DeltaBinding s

deriving instance (Storable s, Show s) => Show (DeltaBinding s)

data Delta (s :: Type) (t :: Type) where
  Delta :: DeltaF s (Delta s) t -> Delta s t
  Var :: DeltaId s t -> Delta s t

deriving instance (Show s, Storable s) => Show (Delta s t)

data DeltaMap s = DeltaMap
  { dmScalar :: Map.Map (DeltaId s s) s,
    dmVector :: Map.Map (DeltaId s (Vector s)) (Vector s)
  }
  deriving (Show)

singleton :: DeltaId s t -> t -> DeltaMap s
singleton dId t = case knownDeltaId dId of
  SScalar -> DeltaMap (Map.singleton dId t) Map.empty
  SVector -> DeltaMap Map.empty (Map.singleton dId t)

deltaMapLookup ::
  DeltaId s t ->
  DeltaMap s ->
  Maybe t
deltaMapLookup dId m = case knownDeltaId dId of
  SScalar -> Map.lookup dId (dmScalar m)
  SVector -> Map.lookup dId (dmVector m)

deltaMapDelete ::
  DeltaId s t ->
  DeltaMap s ->
  DeltaMap s
deltaMapDelete dId (DeltaMap ms mv) = case knownDeltaId dId of
  SScalar -> DeltaMap (Map.delete dId ms) mv
  SVector -> DeltaMap ms (Map.delete dId mv)

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
evalDeltaF ::
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
      (HM.fromList (map (\n' -> if n' == i then t else 0) [0 .. n -1]))
  Dot1 de de' -> f de' (t `HM.scale` de)
  Add1 de de' -> f de t . f de' t
  Scale1 s de -> f de (s `HM.scale` t)
  Konst1 de _ -> f de (HM.sumElements t)
  SumElements1 de n -> f de (HM.konst t n)

-- accumulate has the special property
accumulate ::
  HM.Numeric s =>
  DeltaId s t ->
  t ->
  DeltaMap s ->
  DeltaMap s
accumulate di t m = case knownDeltaId di of
  SScalar ->
    m
      { dmScalar =
          Map.alter
            ( \case
                Nothing -> Just t
                Just t' -> Just (t + t')
            )
            di
            (dmScalar m)
      }
  SVector ->
    m
      { dmVector =
          Map.alter
            ( \case
                Nothing -> Just t
                Just t' -> Just (t `HM.add` t')
            )
            di
            (dmVector m)
      }

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
          deltaBindings = []
        }

runDualMonadAdapt ::
  ( HM.Numeric s,
    Known (s `IsScalarOf` t)
  ) =>
  ArgAdaptor s arg dual ->
  t ->
  (dual -> DualMonadGradient s (Dual t' (Delta s t))) ->
  (t', arg)
runDualMonadAdapt aa g f =
  let (lookup', arg) = runArgAdaptor aa
      m = f arg
      (t', dm) = runDualMonadS known g m
   in (t', lookup' dm)

runDualMonadS ::
  HM.Numeric s =>
  s `IsScalarOf` t ->
  t ->
  DualMonadGradient s (Dual t' (Delta s t)) ->
  (t', DeltaMap s)
runDualMonadS st g m =
  let ((Dual t delta, dId), bs) = runDualMonadM $ do
        r <- m
        dId' <- fresh st
        pure (r, dId')
      bs' = DeltaBinding dId delta
      m' = singleton dId g
   in (t, runDelta (bs' : deltaBindings bs) m')

runDualMonad ::
  (HM.Numeric s, Known (s `IsScalarOf` t)) =>
  t ->
  DualMonadGradient s (Dual s (Delta s t)) ->
  (s, DeltaMap s)
runDualMonad = runDualMonadS known

data DeltaState s = DeltaState
  { deltaCounter0 :: DeltaId s s,
    deltaCounter1 :: DeltaId s (Vector s),
    deltaBindings :: [DeltaBinding s]
  }
  deriving (Show)

newtype DualMonadGradient s t = DualMonadGradient
  {runDualMonadGradient :: State (DeltaState s) t}
  deriving newtype (Monad, Functor, Applicative)

class Monad m => DualMonad s (dual :: Type -> Type) m | m -> s where
  deltaLet :: s `IsScalarOf` t -> dual t -> m (dual t)

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

bind :: DeltaId s t -> Delta s t -> DualMonadGradient s ()
bind dId delta =
  DualMonadGradient $
    modify (\st -> st {deltaBindings = DeltaBinding dId delta : deltaBindings st})

instance DualMonad s (Delta s) (DualMonadGradient s) where
  deltaLet sd delta = do
    dId <- fresh sd
    bind dId delta
    pure (Var dId)

newtype DualMonadValue r a = DualMonadValue
  {runDualMonadValue :: Identity a}
  deriving newtype (Monad, Functor, Applicative)

data Unit (t :: Type) = Unit

instance DualMonad r Unit (DualMonadValue r) where
  deltaLet _ = pure

newtype DualMonadForward r a = DualMonadForward (Identity a)
  deriving newtype (Monad, Functor, Applicative)

runDualMonadForward :: DualMonadForward r a -> a
runDualMonadForward (DualMonadForward m) = runIdentity m

instance DualMonad r (Concrete r) (DualMonadForward r) where
  deltaLet _ = pure

dSingleArgForward ::
  t ->
  t ->
  ( Dual t (Concrete s t) ->
    DualMonadForward s (Dual r (Concrete s r))
  ) ->
  (r, r)
dSingleArgForward t t' f =
  let Dual r d = runDualMonadForward (f (Dual t (concrete t')))
   in (r, unConcrete d)

dLetS ::
  forall (dual :: Type -> Type) t m s.
  DualMonad s dual m =>
  s `IsScalarOf` t ->
  Dual t (dual t) ->
  m (Dual t (dual t))
dLetS si (Dual x y) = do
  y' <- deltaLet si y
  pure (Dual x y')

dLet ::
  forall s dual t m.
  (DualMonad s dual m, Known (s `IsScalarOf` t)) =>
  Dual t (dual t) ->
  m (Dual t (dual t))
dLet = dLetS known

newtype ArgAdaptor s t pd = ArgAdaptor (State Int (DeltaMap s -> t, pd))

runArgAdaptor ::
  ArgAdaptor s t pd ->
  (DeltaMap s -> t, pd)
runArgAdaptor (ArgAdaptor s) = evalState s (-1)

adaptArg ::
  Known (IsScalarOf s t) =>
  t ->
  ArgAdaptor s t (Dual t (Delta s t))
adaptArg t = ArgAdaptor $ do
  i <- get
  put (i - 1)
  let lookup' m = case deltaMapLookup (DeltaId i) m of
        Nothing -> error ("No such DeltaId: " ++ show i)
        Just j -> j

  pure (lookup', Dual t (Var (DeltaId i)))

liftB2 ::
  ArgAdaptor s t1 pd1 ->
  ArgAdaptor s t2 pd2 ->
  ArgAdaptor s (t1, t2) (pd1, pd2)
liftB2 (ArgAdaptor a1) (ArgAdaptor a2) = ArgAdaptor $ do
  (lookup1, arg1) <- a1
  (lookup2, arg2) <- a2
  pure (\m -> (lookup1 m, lookup2 m), (arg1, arg2))

data Dual a b = Dual a b
  deriving (Show)

class Ops f s dual | dual -> s where
  ops :: f s dual t -> dual t

data Concrete r (t :: Type) where
  C :: {unConcrete :: t} -> Concrete r t

concrete :: t -> Concrete s t
concrete = C

instance (Num r, HM.Numeric r) => Ops DeltaF r (Concrete r) where
  ops = \case
    Zero0 -> C 0
    Add0 (C x1) (C x2) -> C (x1 + x2)
    Scale0 r (C x) -> C (r * x)
    Index0 (C v) i _n -> C (HM.atIndex v i)
    Add1 (C x1) (C x2) -> C (x1 `HM.add` x2)
    Scale1 r (C x) -> C (HM.scale r x)
    Konst1 (C k) i -> C (HM.konst k i)
    Dot1 v1 (C v2) -> C (v1 `HM.dot` v2)
    SumElements1 (C v) _ -> C (HM.sumElements v)

instance Ops DeltaF r (Delta r) where
  ops = Delta

bar ::
  (HM.Numeric s, DualMonad s dual m, Ops DeltaF s dual) =>
  Dual (Vector s) (dual (Vector s)) ->
  m (Dual s (dual s))
bar v = do
  x <- index v 0
  y <- index v 1
  foo x y

foo ::
  (DualMonad s dual m, Num s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  m (Dual s (dual s))
foo x y = do
  x2 <- x .* x
  x2y <- x2 .* y
  x2y .+ y

-- d Functions

-- I'm not sure it's actually useful to have these, rather than just
-- using ops and the constructors directly.

dAdd0 :: Ops DeltaF s dual => dual s -> dual s -> dual s
dAdd0 x y = ops (Add0 x y)

dScale0 :: Ops DeltaF s dual => s -> dual s -> dual s
dScale0 x y = ops (Scale0 x y)

dZero0 :: Ops DeltaF s dual => dual s
dZero0 = ops Zero0

dSumElements :: Ops DeltaF s dual => dual (Vector s) -> Int -> dual s
dSumElements v n = ops (SumElements1 v n)

constant :: Ops DeltaF s dual => a -> Dual a (dual s)
constant k = Dual k dZero0

--

instance (Num s, Ops DeltaF s dual) => Num (Dual s (dual s)) where
  Dual x x' + Dual y y' = Dual (x + y) (dAdd0 x' y')
  Dual x x' - Dual y y' = Dual (x - y) (dAdd0 x' (dScale0 (-1) y'))
  Dual x x' * Dual y y' = Dual (x * y) (dAdd0 (dScale0 x y') (dScale0 y x'))
  negate (Dual x x') = Dual (- x) (dScale0 (-1) x')
  abs = undefined
  signum = undefined
  fromInteger = constant . fromInteger

square :: (Num s, Ops DeltaF s dual) => Dual s (dual s) -> Dual s (dual s)
square (Dual u u') = Dual (u * u) (dScale0 (2 * u) u')

squaredDifference ::
  (Num s, Ops DeltaF s dual) =>
  s ->
  Dual s (dual s) ->
  Dual s (dual s)
squaredDifference targ res = square $ res - constant targ

(.+) ::
  (DualMonad s dual m, Num s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  m (Dual s (dual s))
Dual x x' .+ Dual y y' =
  dLet $
    Dual (x + y) (ops (Add0 x' y'))

(.*) ::
  (DualMonad s dual m, Num s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  m (Dual s (dual s))
Dual x x' .* Dual y y' =
  dLet $
    Dual (x * y) (ops (Add0 (ops (Scale0 y x')) (ops (Scale0 x y'))))

index ::
  (HM.Numeric s, Ops DeltaF s dual, DualMonad s dual m) =>
  Dual (Vector s) (dual (Vector s)) ->
  Int ->
  m (Dual s (dual s))
index (Dual v v') i =
  dLet $
    Dual (HM.atIndex v i) (ops (Index0 v' i (HM.size v)))

sumElements ::
  (HM.Numeric s, Ops DeltaF s dual) =>
  Dual (Vector s) (dual (Vector s)) ->
  Dual s (dual s)
sumElements (Dual u u') = Dual (HM.sumElements u) (dSumElements u' (HM.size u))

example :: (Double, (Double, Double))
example = runDualMonadAdapt (liftB2 (adaptArg 10) (adaptArg 20)) 1 (uncurry foo)

example3 :: (Double, Vector Double)
example3 = dSingleArg (HM.fromList [10, 20]) 1 bar

example3Forward1 :: (Double, Double)
example3Forward1 = dSingleArgForward (HM.fromList [10, 20]) (HM.fromList [1, 0]) bar

example3Forward2 :: (Double, Double)
example3Forward2 = dSingleArgForward (HM.fromList [10, 20]) (HM.fromList [0, 1]) bar

dSingleArg ::
  (HM.Numeric s, Known (IsScalarOf s r), Known (IsScalarOf s t)) =>
  -- | Primal argument
  t ->
  -- | Incoming gradient (usually r ~ Double and r = 1)
  r ->
  -- | Function to be differentiated
  (Dual t (Delta s t) -> DualMonadGradient s (Dual r (Delta s r))) ->
  -- | Result of original function, and its gradient
  (r, t)
dSingleArg = runDualMonadAdapt . adaptArg
