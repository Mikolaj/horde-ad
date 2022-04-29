{-# LANGUAGE DataKinds, DerivingStrategies, FlexibleInstances,
             FunctionalDependencies, GADTs, GeneralizedNewtypeDeriving,
             KindSignatures, RankNTypes, StandaloneDeriving, TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

module HordeAd.Core.Again (module HordeAd.Core.Again) where

import           Control.Monad.Trans.State
  (State, StateT (StateT), evalState, get, modify, put, runState)
import           Data.Functor.Identity (Identity (Identity))
import           Data.Kind (Type)
import           Data.List (foldl')
import qualified Data.Strict.Map as Map
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Data.Vector.Storable (Storable)
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import           Prelude

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
evalLet binding (DeltaMap ms mv) = case binding of
  (DeltaBinding di de) -> case knownDeltaId di of
    SScalar -> case Map.lookup di ms of
      Nothing -> DeltaMap ms mv
      Just x -> eval de x (DeltaMap (Map.delete di ms) mv)
    SVector -> case Map.lookup di mv of
      Nothing -> DeltaMap ms mv
      Just x -> eval de x (DeltaMap ms (Map.delete di mv))

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
  (HM.Numeric s,
  Known (s `IsScalarOf` t)) =>
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
  let (Dual t delta, bs) = runDualMonadM m
      (bs', m') = case st of
        SScalar ->
          let dId = succDeltaId (deltaCounter0 bs)
           in ( DeltaBinding dId delta,
                singleton dId g
              )
        SVector ->
          let dId = succDeltaId (deltaCounter1 bs)
           in ( DeltaBinding dId delta,
                singleton dId g
              )
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
    SumElements1 (C1 v) _ -> C0 (HM.sumElements v)

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

dAdd0 :: Ops DeltaF s dual => dual s -> dual s -> dual s
dAdd0 x y = ops (Add0 x y)

dScale0 :: Ops DeltaF s dual => s -> dual s -> dual s
dScale0 x y = ops (Scale0 x y)

dZero0 :: Ops DeltaF s dual => dual s
dZero0 = ops Zero0

dSumElements :: Ops DeltaF s dual => dual (Vector s) -> Int -> dual s
dSumElements v n = ops (SumElements1 v n)

-- Dual number functions (meaning, Dual -> Dual, high level API)

instance (Num s, Ops DeltaF s dual) => Num (Dual s (dual s)) where
  Dual x x' + Dual y y' = Dual (x + y) (dAdd0 x' y')
  Dual x x' - Dual y y' = Dual (x - y) (dAdd0 x' (dScale0 (-1) y'))
  Dual x x' * Dual y y' = Dual (x * y) (dAdd0 (dScale0 x y') (dScale0 y x'))
  negate (Dual x x') = Dual (- x) (dScale0 (-1) x')
  abs = undefined
  signum = undefined
  fromInteger = constant . fromInteger

-- These instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (Dual s (dual s)) where

instance Ord (Dual s (dual s)) where

instance (Real s, Ops DeltaF s dual) => Real (Dual s (dual s)) where

instance (Fractional s, Ops DeltaF s dual) => Fractional (Dual s (dual s)) where
  Dual u u' / Dual v v' =
    let recipSq = recip (v * v)
    in Dual (u / v)
            (dAdd0 (dScale0 (v * recipSq) u') (dScale0 (- u * recipSq) v'))

instance (Floating s, Ops DeltaF s dual) => Floating (Dual s (dual s)) where
  sin (Dual u u') = Dual (sin u) (dScale0 (cos u) u')

instance (RealFrac s, Ops DeltaF s dual) => RealFrac (Dual s (dual s)) where

instance (RealFloat s, Ops DeltaF s dual) => RealFloat (Dual s (dual s)) where
  atan2 (Dual u u') (Dual v v') =
    let t = 1 / (u * u + v * v)
    in Dual (atan2 u v) (dAdd0 (dScale0 (- u * t) v') (dScale0 (v * t) u'))

-- TODO (not really needed on its own, but something like that
-- would be required for scale1 and Num on Vectors):
dScale1 :: (HM.Numeric s, Ops DeltaF s dual)
        => (Vector s) -> dual (Vector s) -> dual (Vector s)
dScale1 x y = ops (Scale1 (HM.sumElements x) y) -- TODO

-- This causes "Overlapping instances". Perhaps the above Num should be
-- only defined for Double and Float, not for @s@?
{-
instance (Num (Vector s), Ops DeltaF s dual)
         => Num (Dual (Vector s) (dual (Vector s))) where
  Dual x x' * Dual y y' =
    Dual (x * y) (ops (Add1 (dScale1 x y') (dScale1 y x')))
-}

constant :: Ops DeltaF s dual => a -> Dual a (dual s)
constant k = Dual k dZero0

-- TODO: this is probably not the right type for both scalars and vectors?
scale0 :: (Num s, Ops DeltaF s dual)
       => s -> Dual s (dual s) -> Dual s (dual s)
scale0 a (Dual u u') = Dual (a * u) (dScale0 a u')

scale1 :: (HM.Numeric s, Num (Vector s), Ops DeltaF s dual)
       => Vector s
       -> Dual (Vector s) (dual (Vector s))
       -> Dual (Vector s) (dual (Vector s))
scale1 a (Dual u u') = Dual (a * u) (dScale1 a u')

-- MK: if this cannot work on vectors, perhaps @square0@ would be a better name
-- and then we can add @square1@.
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

--

example :: (Double, (Double, Double))
example = runDualMonadAdapt (liftB2 (adaptArg 10) (adaptArg 20)) 1 (uncurry foo)

example3 :: (Double, Vector Double)
example3 = runDualMonadAdapt (adaptArg (HM.fromList [10, 20])) 1 bar

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

liftB2 :: ArgAdaptor s t1 pd1
       -> ArgAdaptor s t2 pd2
       -> ArgAdaptor s (t1, t2) (pd1, pd2)
liftB2 (ArgAdaptor a1) (ArgAdaptor a2) = ArgAdaptor $ do
  (lookup1, arg1) <- a1
  (lookup2, arg2) <- a2
  pure (\m -> (lookup1 m, lookup2 m), (arg1, arg2))

-- We have test results recorded for the tests below in TestSingleGradient
-- and for quad also in TestSimpleDescent (but for that one we need
-- the simplest gradient descent optimizer).

quad ::
  (DualMonad s dual m, Num s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  m (Dual s (dual s))
quad x y = do
  x2 <- dLet $ square x
  y2 <- y .* y
  tmp <- x2 .+ y2
  tmp .+ 5

foldl'0 :: (HM.Numeric s, Ops DeltaF s dual)
        => (Dual s (dual s) -> Dual s (dual s) -> Dual s (dual s))
        -> Dual s (dual s)
        -> Dual (Vector s) (dual (Vector s))
        -> Dual s (dual s)
foldl'0 f uu' (Dual v v') =
  let k = V.length v
      g !acc ix p = f (Dual p (ops (Index0 v' ix k))) acc
  in V.ifoldl' g uu' v

altSumElements0 :: (HM.Numeric s, Ops DeltaF s dual)
                => Dual (Vector s) (dual (Vector s)) -> Dual s (dual s)
altSumElements0 = foldl'0 (+) 0

atanReadmePoly ::
  (RealFloat s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  Dual s (dual s) ->
  Data.Vector.Vector (Dual s (dual s))
atanReadmePoly x y z =
  let w = x * sin y
  in V.fromList [atan2 z w, z * x]

sumElementsVectorOfDual :: (Num s, Ops DeltaF s dual)
                        => Data.Vector.Vector (Dual s (dual s))
                        -> Dual s (dual s)
sumElementsVectorOfDual = V.foldl' (+) 0

atanReadmeMPoly ::
  (DualMonad s dual m, RealFloat s, Ops DeltaF s dual) =>
  Dual s (dual s) ->
  Dual s (dual s) ->
  Dual s (dual s) ->
  m (Dual s (dual s))
atanReadmeMPoly x y z =
  dLet $ sumElementsVectorOfDual $ atanReadmePoly x y z

indexNoM ::
  (HM.Numeric s, Ops DeltaF s dual) =>
  Dual (Vector s) (dual (Vector s)) ->
  Int ->
  Dual s (dual s)
indexNoM (Dual v v') i =
  Dual (HM.atIndex v i) (ops (Index0 v' i (HM.size v)))

-- TODO
seq1 ::  -- (HM.Numeric s, Ops DeltaF s dual)
        Data.Vector.Vector (Dual s (dual s))
     -> Dual (Vector s) (dual (Vector s))
seq1 = undefined

atanReadmePolyV :: (HM.Numeric s, RealFloat s, Ops DeltaF s dual)
                => Dual (Vector s) (dual (Vector s))
                -> Dual (Vector s) (dual (Vector s))
atanReadmePolyV xyzVector =
  let x = indexNoM xyzVector 0
      y = indexNoM xyzVector 1
      z = indexNoM xyzVector 2
      w = x * sin y
  in seq1 $ V.fromList [atan2 z w, z * x]

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: (HM.Numeric s, Ops DeltaF s dual)
        => Dual (Vector s) (dual (Vector s)) -> Vector s -> Dual s (dual s)
(<.>!!) (Dual u u') v = Dual (u HM.<.> v) (ops (Dot1 v u'))

atanReadmeMPolyV ::
  (DualMonad s dual m, HM.Numeric s, RealFloat s, Ops DeltaF s dual) =>
  Dual (Vector s) (dual (Vector s)) ->
  m (Dual s (dual s))
atanReadmeMPolyV xyzVector =
  dLet $ atanReadmePolyV xyzVector <.>!! HM.konst 1 2
