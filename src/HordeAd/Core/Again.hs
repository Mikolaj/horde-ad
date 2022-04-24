{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module HordeAd.Core.Again (Dim(..)) where

import Prelude
import Data.Kind (Type)
import Control.Monad.Trans.State
import Data.Functor.Identity
import Numeric.LinearAlgebra (add, scale, dot, konst, atIndex,
                              Numeric, Vector)

class KnownDim (d :: Dim) where
  known :: SDim d

data Dim = D0 | D1

data SDim (a :: Dim) where
  SD0 :: SDim 'D0
  SD1 :: SDim 'D1

data DeltaF (r :: Type) (delta :: Dim -> Type) (d :: Dim) where
  Zero0 :: DeltaF r delta 'D0

  Add :: delta d -> delta d -> DeltaF r delta d
  Scale :: r -> delta d -> DeltaF r delta d

  Index0 :: delta 'D1 -> Int -> DeltaF r delta 'D0
  Konst1 :: delta 'D0 -> Int -> DeltaF r delta 'D1
  Dot1 :: delta d -> delta d -> DeltaF r delta 'D0

newtype DeltaId (d :: Dim) where
  DeltaId :: Int -> DeltaId d

succDeltaId :: DeltaId d -> DeltaId d
succDeltaId (DeltaId i) = DeltaId (i + 1)

data DeltaBinding r where
  DeltaBinding :: SDim d -> DeltaId d -> Delta r d -> DeltaBinding r

data Delta (r :: Type) (d :: Dim) where
  Delta :: DeltaF r (Delta r) d -> Delta r d
  Var :: DeltaId d -> Delta r d

data DeltaState r = DeltaState
  { deltaCounter0 :: DeltaId 'D0
  , deltaCounter1 :: DeltaId 'D1
  , deltaBindings :: [DeltaBinding r]
  }

newtype DualMonadGradient r a = DualMonadGradient
  { runDualMonadGradient :: State (DeltaState r) a }
  deriving newtype (Monad, Functor, Applicative)

class Monad m => DeltaMonad m (delta :: Dim -> Type) where
  deltaLet :: SDim d -> delta d -> m (delta d)

instance DeltaMonad (DualMonadGradient r) (Delta r) where
  deltaLet sd delta = DualMonadGradient $ do
    st <- get
    case sd of
          SD0 -> do
            put (st { deltaCounter0 = succDeltaId (deltaCounter0 st)
                    , deltaBindings = DeltaBinding sd (deltaCounter0 st) delta : deltaBindings st
                    })
            pure (Var (deltaCounter0 st))
          SD1 -> do
            put (st { deltaCounter1 = succDeltaId (deltaCounter1 st)
                    , deltaBindings = DeltaBinding sd (deltaCounter1 st) delta : deltaBindings st
                    })
            pure (Var (deltaCounter1 st))

newtype DualMonadValue a = DualMonadValue
  { runDualMonadValue :: Identity a }
  deriving newtype (Monad, Functor, Applicative)

data Unit (d :: Dim) = Unit

instance DeltaMonad DualMonadValue Unit where
  deltaLet _ = pure

dLet :: forall (t :: Dim -> Type) a d m.
        (KnownDim d, DeltaMonad m t)
     => Dual a (t d)
     -> m (Dual a (t d))
dLet  (Dual x y) = do
  y' <- deltaLet known y
  pure (Dual x y')

data Dual a b = Dual a b

class Ops r t | t -> r where
  ops :: DeltaF r t d -> t d

zero :: (Num r, Ops r t) => Dual r (t 'D0)
zero = Dual 0 (ops Zero0)

(.+) :: (Ops r t, Num a, KnownDim d, DeltaMonad m t) =>
        Dual a (t d)
     -> Dual a (t d)
     -> m (Dual a (t d))
Dual x x' .+ Dual y y' = dLet $
  Dual (x + y) (ops (Add x' y'))

(.*) :: (Ops a t, Num a, KnownDim d, DeltaMonad m t) =>
        Dual a (t d) -> Dual a (t d) -> m (Dual a (t d))
Dual x x' .* Dual y y' = dLet $
  Dual (x * y) (ops (Add (ops (Scale y x')) (ops (Scale x y'))))

instance Ops r (Delta r) where
  ops = Delta

data Concrete r (d :: Dim) where
  C0 :: r -> Concrete r 'D0
  C1 :: Vector r -> Concrete r 'D1

instance (Num r, Numeric r) => Ops r (Concrete r) where
  ops = \case
    Zero0 -> C0 0
    Add (C0 x1) (C0 x2) -> C0 (x1 + x2)
    Add (C1 x1) (C1 x2) -> C1 (x1 `add` x2)
    Scale r (C0 x) -> C0 (r * x)
    Scale r (C1 x) -> C1 (scale r x)

    Index0 (C1 v) i -> C0 (atIndex v i)
    Konst1 (C0 k) i -> C1 (konst k i)
    Dot1 (C1 v1) (C1 v2) -> C0 (v1 `dot` v2)
    Dot1 (C0 v1) (C0 v2) -> C0 (v1 * v2)


foo :: (Ops r t, DeltaMonad m t, KnownDim d, Num r)
    => Dual r (t d) -> Dual r (t d) -> m (Dual r (t d))
foo x y = do
  x2 <- x .* x
  x2y <- x2 .* y
  x2y_p_y <- x2y .+ y
  pure x2y_p_y
