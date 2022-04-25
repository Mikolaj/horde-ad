{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module HordeAd.Core.Again (module HordeAd.Core.Again) where

import Control.Monad.Trans.State
  ( State,
    StateT (StateT),
    get,
    put,
    runState,
  )
import Data.Functor.Identity (Identity (Identity))
import Data.Kind (Type)
import qualified Data.Strict.Map as Map
import Data.Vector.Storable (Storable)
import Numeric.LinearAlgebra
  ( Vector,
  )
import qualified Numeric.LinearAlgebra as HM
import Prelude

class Known t where
  known :: t

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

deriving instance
  (Show s, Show (dual s), Show (dual (Vector s)), Storable s) =>
  Show (DeltaF s dual t)

newtype DeltaId (r :: Type) where
  DeltaId :: Int -> DeltaId r
  deriving (Eq, Ord, Show)

succDeltaId :: DeltaId d -> DeltaId d
succDeltaId (DeltaId i) = DeltaId (i + 1)

data DeltaBinding s where
  DeltaBinding :: s `IsScalarOf` t -> DeltaId t -> Delta s t -> DeltaBinding s

deriving instance (Storable s, Show s) => Show (DeltaBinding s)

data Delta (s :: Type) (t :: Type) where
  Delta :: DeltaF s (Delta s) t -> Delta s t
  Var :: DeltaId t -> Delta s t
  deriving (Show)

type DeltaMap s = (Map.Map (DeltaId s) s, Map.Map (DeltaId (Vector s)) (Vector s))

eval ::
  HM.Numeric s =>
  s `IsScalarOf` t ->
  t ->
  Delta s t ->
  DeltaMap s ->
  DeltaMap s
eval st t delta m = case delta of
  Delta df -> case st of
    SScalar -> case df of
      Zero0 -> m
      Add0 de de' ->
        eval st t de $
          eval st t de' m
      Scale0 t' de -> eval SScalar (t' * t) de m
      Index0 de i n ->
        eval
          SVector
          (HM.fromList (map (\n' -> if n' == i then t else 0) [0 .. n -1]))
          de
          m
      Dot1 de de' -> eval SVector (t `HM.scale` de) de' m
    SVector -> case df of
      Add1 de de' -> eval SVector t de (eval st t de' m)
      Scale1 s de -> eval SVector (s `HM.scale` t) de m
      Konst1 de _ -> eval SScalar (HM.sumElements t) de m
  Var di -> case st of
    SScalar ->
      let (ms, mv) = m
       in ( Map.alter
              ( \case
                  Nothing -> Just t
                  Just t' -> Just (t + t')
              )
              di
              ms,
            mv
          )
    SVector ->
      let (ms, mv) = m
       in ( ms,
            Map.alter
              ( \case
                  Nothing -> Just t
                  Just t' -> Just (t `HM.add` t')
              )
              di
              mv
          )

evalLet :: HM.Numeric s => DeltaBinding s -> DeltaMap s -> DeltaMap s
evalLet binding (ms, mv) = case binding of
  (DeltaBinding st di de) -> case st of
    SScalar -> case Map.lookup di ms of
      Nothing -> (ms, mv)
      Just x -> eval st x de (Map.delete di ms, mv)
    SVector -> case Map.lookup di mv of
      Nothing -> (ms, mv)
      Just x -> eval st x de (ms, Map.delete di mv)

runDelta ::
  HM.Numeric s =>
  [DeltaBinding s] ->
  DeltaMap s ->
  DeltaMap s
runDelta binds m = case binds of
  [] -> m
  b : rest -> runDelta rest (evalLet b m)

runDeltaMonadM :: DualMonadGradient s a -> (a, DeltaState s)
runDeltaMonadM m = runState (runDualMonadGradient m) initialState
  where
    initialState =
      DeltaState
        { deltaCounter0 = DeltaId 0,
          deltaCounter1 = DeltaId 0,
          deltaBindings = []
        }

runDeltaMonadS ::
  HM.Numeric s =>
  s `IsScalarOf` t ->
  t ->
  DualMonadGradient s (Dual s (Delta s t)) ->
  (s, DeltaMap s)
runDeltaMonadS st g m =
  let (Dual t delta, bs) = runDeltaMonadM m
      (bs', m') = case st of
        SScalar ->
          let dId = succDeltaId (deltaCounter0 bs)
           in ( DeltaBinding st dId delta,
                (Map.singleton dId g, Map.empty)
              )
        SVector ->
          let dId = succDeltaId (deltaCounter1 bs)
           in ( DeltaBinding st dId delta,
                (Map.empty, Map.singleton dId g)
              )
   in (t, runDelta (bs' : deltaBindings bs) m')

runDeltaMonad ::
  (HM.Numeric s, Known (s `IsScalarOf` t)) =>
  t ->
  DualMonadGradient s (Dual s (Delta s t)) ->
  (s, DeltaMap s)
runDeltaMonad = runDeltaMonadS known

data DeltaState s = DeltaState
  { deltaCounter0 :: DeltaId s,
    deltaCounter1 :: DeltaId (Vector s),
    deltaBindings :: [DeltaBinding s]
  }
  deriving (Show)

newtype DualMonadGradient s t = DualMonadGradient
  {runDualMonadGradient :: State (DeltaState s) t}
  deriving newtype (Monad, Functor, Applicative)

class Monad m => DeltaMonad s (dual :: Type -> Type) m | m -> s where
  deltaLet :: s `IsScalarOf` t -> dual t -> m (dual t)

instance DeltaMonad s (Delta s) (DualMonadGradient s) where
  deltaLet sd delta = DualMonadGradient $ do
    st <- get
    case sd of
      SScalar -> do
        put
          ( st
              { deltaCounter0 = succDeltaId (deltaCounter0 st),
                deltaBindings =
                  DeltaBinding sd (deltaCounter0 st) delta :
                  deltaBindings st
              }
          )
        pure (Var (deltaCounter0 st))
      SVector -> do
        put
          ( st
              { deltaCounter1 = succDeltaId (deltaCounter1 st),
                deltaBindings =
                  DeltaBinding SVector (deltaCounter1 st) delta :
                  deltaBindings st
              }
          )
        pure (Var (deltaCounter1 st))

newtype DualMonadValue r a = DualMonadValue
  {runDualMonadValue :: Identity a}
  deriving newtype (Monad, Functor, Applicative)

data Unit (t :: Type) = Unit

instance DeltaMonad r Unit (DualMonadValue r) where
  deltaLet _ = pure

dLetS ::
  forall (dual :: Type -> Type) t m s.
  DeltaMonad s dual m =>
  s `IsScalarOf` t ->
  Dual t (dual t) ->
  m (Dual t (dual t))
dLetS si (Dual x y) = do
  y' <- deltaLet si y
  pure (Dual x y')

dLet ::
  forall s dual t m.
  (DeltaMonad s dual m, Known (s `IsScalarOf` t)) =>
  Dual t (dual t) ->
  m (Dual t (dual t))
dLet = dLetS known

data Dual a b = Dual a b
  deriving (Show)

class Ops f s dual | dual -> s where
  ops :: f s dual t -> dual t

data Concrete r (t :: Type) where
  C0 :: r -> Concrete r r
  C1 :: Vector r -> Concrete r (Vector r)

instance (Num r, HM.Numeric r) => Ops DeltaF r (Concrete r) where
  ops = \case
    Zero0 -> C0 0
    Add0 (C0 x1) (C0 x2) -> C0 (x1 + x2)
    Scale0 r (C0 x) -> C0 (r * x)
    Index0 (C1 v) i _n -> C0 (HM.atIndex v i)
    Add1 (C1 x1) (C1 x2) -> C1 (x1 `HM.add` x2)
    Scale1 r (C1 x) -> C1 (HM.scale r x)
    Konst1 (C0 k) i -> C1 (HM.konst k i)
    Dot1 v1 (C1 v2) -> C0 (v1 `HM.dot` v2)

zero :: (Num r, Ops DeltaF r d) => Dual r (d r)
zero = Dual 0 (ops Zero0)

instance Ops DeltaF r (Delta r) where
  ops = Delta

bar ::
  (HM.Numeric s, DeltaMonad s dual m, Ops DeltaF s dual) =>
  Dual (Vector s) (dual (Vector s)) ->
  m (Dual s (dual s))
bar v = do
  x <- index v 0
  y <- index v 1
  foo x y

foo ::
  (DeltaMonad s dual m, Num s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  m (Dual s (dual s))
foo x y = do
  x2 <- x .* x
  x2y <- x2 .* y
  x2y .+ y

(.+) ::
  (DeltaMonad s dual m, Num s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  m (Dual s (dual s))
Dual x x' .+ Dual y y' =
  dLet $
    Dual (x + y) (ops (Add0 x' y'))

(.*) ::
  (DeltaMonad s dual m, Num s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  m (Dual s (dual s))
Dual x x' .* Dual y y' =
  dLet $
    Dual (x * y) (ops (Add0 (ops (Scale0 y x')) (ops (Scale0 x y'))))

index ::
  (HM.Numeric s, Ops DeltaF s dual, DeltaMonad s dual m) =>
  Dual (Vector s) (dual (Vector s)) ->
  Int ->
  m (Dual s (dual s))
index (Dual v v') i =
  dLet $
    Dual (HM.atIndex v i) (ops (Index0 v' i (HM.size v)))

myFoo ::
  (Num a, DeltaMonad a (Delta a) m) =>
  m (Dual a (Delta a a))
myFoo = foo (Dual 10 (Var (DeltaId (-1)))) (Dual 20 (Var (DeltaId (-2))))

example :: HM.Numeric Double => (Double, DeltaMap Double)
example = runDeltaMonad 1 myFoo

example2 :: (Dual Double (Delta Double Double), DeltaState Double)
example2 = runDeltaMonadM myFoo

example3 :: (Double, DeltaMap Double)
example3 = runDeltaMonad 1 (bar (Dual (HM.fromList [10, 20]) (Var (DeltaId (-1)))))
