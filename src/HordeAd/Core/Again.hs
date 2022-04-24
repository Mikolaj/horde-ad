{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module HordeAd.Core.Again (module HordeAd.Core.Again) where

import Control.Monad.Trans.State
import Data.Functor.Identity
import Data.Kind (Type)
import Numeric.LinearAlgebra
  ( Numeric,
    Vector,
    add,
    atIndex,
    dot,
    konst,
    scale,
  )
import Prelude

class Known t where
  known :: t

instance Known (a `IsScalarOf` a) where
  known = SScalar

instance Known (a `IsScalarOf` Vector a) where
  known = SVector

knownP :: Known t => proxy t -> t
knownP _ = known

data IsScalarOf (s :: Type) (t :: Type) where
  SScalar :: IsScalarOf s s
  SVector :: IsScalarOf s (Vector s)

data DeltaF (s :: Type) (dual :: Type -> Type) (t :: Type) where
  Zero0 :: DeltaF s dual s
  Add0 :: dual s -> dual s -> DeltaF s dual s
  Scale0 :: s -> dual s -> DeltaF s dual s
  Index0 :: dual (Vector s) -> Int -> DeltaF s dual s
  Add1 :: dual (Vector s) -> dual (Vector s) -> DeltaF s dual (Vector s)
  Scale1 :: s -> dual (Vector s) -> DeltaF s dual (Vector s)
  Konst1 :: dual s -> Int -> DeltaF s dual (Vector s)
  Dot1 :: dual (Vector s) -> dual (Vector s) -> DeltaF s dual s

newtype DeltaId (r :: Type) where
  DeltaId :: Int -> DeltaId r

succDeltaId :: DeltaId d -> DeltaId d
succDeltaId (DeltaId i) = DeltaId (i + 1)

data DeltaBinding r where
  DeltaBinding :: s `IsScalarOf` t -> DeltaId t -> Delta r t -> DeltaBinding r

data Delta (s :: Type) (dual :: Type) where
  Delta :: DeltaF s (Delta s) dual -> Delta s dual
  Var :: DeltaId dual -> Delta s dual

data DeltaState s = DeltaState
  { deltaCounter0 :: DeltaId s,
    deltaCounter1 :: DeltaId (Vector s),
    deltaBindings :: [DeltaBinding s]
  }

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
                deltaBindings = DeltaBinding sd (deltaCounter0 st) delta : deltaBindings st
              }
          )
        pure (Var (deltaCounter0 st))
      SVector -> do
        put
          ( st
              { deltaCounter1 = succDeltaId (deltaCounter1 st),
                deltaBindings = DeltaBinding SVector (deltaCounter1 st) delta : deltaBindings st
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

class Ops f s dual | dual -> s where
  ops :: f s dual t -> dual t

data Concrete r (t :: Type) where
  C0 :: r -> Concrete r r
  C1 :: Vector r -> Concrete r (Vector r)

instance (Num r, Numeric r) => Ops DeltaF r (Concrete r) where
  ops = \case
    Zero0 -> C0 0
    Add0 (C0 x1) (C0 x2) -> C0 (x1 + x2)
    Scale0 r (C0 x) -> C0 (r * x)
    Index0 (C1 v) i -> C0 (atIndex v i)
    Add1 (C1 x1) (C1 x2) -> C1 (x1 `add` x2)
    Scale1 r (C1 x) -> C1 (scale r x)
    Konst1 (C0 k) i -> C1 (konst k i)
    Dot1 (C1 v1) (C1 v2) -> C0 (v1 `dot` v2)

zero :: (Num r, Ops DeltaF r d) => Dual r (d r)
zero = Dual 0 (ops Zero0)

instance Ops DeltaF r (Delta r) where
  ops = Delta

foo ::
  (DeltaMonad s dual m, Num t, Ops DeltaF t dual, Known (s `IsScalarOf` t)) =>
  Dual t (dual t) ->
  Dual t (dual t) ->
  m (Dual t (dual t))
foo x y = do
  x2 <- x .* x
  x2y <- x2 .* y
  x2y .+ y

(.+) ::
  (DeltaMonad s dual m, Known (s `IsScalarOf` t), Num t, Ops DeltaF t dual) =>
  Dual t (dual t) ->
  Dual t (dual t) ->
  m (Dual t (dual t))
Dual x x' .+ Dual y y' =
  dLet $
    Dual (x + y) (ops (Add0 x' y'))

(.*) ::
  (DeltaMonad s dual m, Known (s `IsScalarOf` t), Num t, Ops DeltaF t dual) =>
  Dual t (dual t) ->
  Dual t (dual t) ->
  m (Dual t (dual t))
Dual x x' .* Dual y y' =
  dLet $
    Dual (x * y) (ops (Add0 (ops (Scale0 y x')) (ops (Scale0 x y'))))

index ::
  (Numeric t, Ops DeltaF t dual, DeltaMonad s dual m, Known (s `IsScalarOf` t)) =>
  Dual (Vector t) (dual (Vector t)) ->
  Int ->
  m (Dual t (dual t))
index (Dual v v') i =
  dLet $
    Dual (atIndex v i) (ops (Index0 v' i))

myFoo ::
  (Num a, DeltaMonad a (Delta a) m) =>
  m (Dual a (Delta a a))
myFoo = foo (Dual 10 (Var (DeltaId 0))) (Dual 20 (Var (DeltaId 1)))
