{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, StandaloneDeriving, TypeFamilyDependencies,
             UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
-- | The class defining dual components of dual numbers and
-- the dual number type itself, hiding its constructor, but exposing
-- a couple of smart constructors.
--
-- This module defines the relevant classes, type families,
-- constraints and instances for the dual numbers data structure.
-- This is a mid-level API ("HordeAd.Internal.Delta" is low level)
-- used to define types and operations in "HordeAd.Core.DualNumber"
-- that is the foundation of the high-level API.
--
-- This module contains impurity, which produces pure data with a particular
-- property. The property is an order of per-node integer identifiers
-- that represents data dependencies and sharing. The low-level API
-- depends on this property, but is completely isolated from the impurity.
-- The high-level API invokes the impurity through smart constructors,
-- but can't observe any impure behaviour. Neither can any other module
-- in the package, except for the testing modules that import
-- testing-exclusive operations and instances.
--
-- @Show@ is such a testing-only instance and so should be used
-- only in debugging or testing. Similarly, instances such as @Eq@
-- or @Read@ should not be auto-derived, but carefully crafted to respect
-- sharing. This applies regardless of impurity, because repeated processing
-- of the same shared terms is prohibitive expensive.
module HordeAd.Core.Ast
  ( -- * The most often used part of the mid-level API that gets re-exported in high-level API
    ADVal(..), ADMode(..), Dual, DummyDual(..), Under, IsPrimal(..), astToD, LiftToAst(..)  -- TODO
  , Ast(..), Ast0, Ast1, AstVarName(..), AstVar(..), AstInt(..), AstBool(..)
  , CodeOut(..), CodeIntOut(..), CodeBoolOut(..), RelOut(..)
  ) where

import Prelude

import           Data.Kind (Type)
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import qualified Data.Strict.Vector as Data.Vector
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Text.Show.Functions ()

import HordeAd.Internal.Delta
-- TODO
data ADVal (d :: ADMode) a = D a (Dual d a)
data ADMode =
    ADModeGradient
  | ADModeDerivative
  | ADModeValue
  deriving Show
type family Dual (d :: ADMode) a = result | result -> d a where
  Dual 'ADModeGradient Double = Delta0 Double
  Dual 'ADModeGradient Float = Delta0 Float
  Dual 'ADModeGradient (Ast r 'ADModeGradient a) =
    DummyDual r 'ADModeGradient a
  Dual 'ADModeGradient (Vector r) = Delta1 r
-- not injective:  Dual 'ADModeDerivative r = r
  Dual 'ADModeDerivative Double = Double
  Dual 'ADModeDerivative Float = Float
  Dual 'ADModeDerivative (Ast r 'ADModeDerivative a) =
    DummyDual r 'ADModeDerivative a
  Dual 'ADModeDerivative (Vector r) = Vector r
  Dual 'ADModeValue a = DummyDual a 'ADModeValue a
newtype DummyDual r (d :: ADMode) a = DummyDual ()
  deriving Show
class IsPrimal d a where
  dZero :: Dual d a
  dScale :: a -> Dual d a -> Dual d a
  dAdd :: Dual d a -> Dual d a -> Dual d a
  recordSharing :: Dual d a -> Dual d a
type family Under a where
  Under Double = Double
  Under Float = Float
  Under (Ast u d a) = u
  Under (Vector u) = u
dD :: IsPrimal d a => a -> Dual d a -> ADVal d a
dD a dual = D a (recordSharing dual)

-- * Definitions

astToD :: IsPrimal d (Ast r d a) => Ast r d a -> ADVal d (Ast r d a)
astToD ast = dD ast undefined

class LiftToAst d r a where
  liftToAst :: ADVal d r -> ADVal d (Ast (Under r) d a)

instance IsPrimal d (Ast Double d Double)
         => LiftToAst d Double Double where
  liftToAst = astToD . undefined

instance IsPrimal d (Ast Float d Float)
         => LiftToAst d Float Float where
  liftToAst = astToD . undefined

instance LiftToAst d (Ast Double d Double) Double where
  liftToAst = id

instance LiftToAst d (Ast Float d Float) Float where
  liftToAst = id

instance IsPrimal d (Ast u d (Vector u))
         => LiftToAst d (Vector u) (Vector u) where
  liftToAst = astToD . undefined

instance LiftToAst d (Ast u d (Vector u)) (Vector u) where
  liftToAst = id

-- TODO: consider sharing Ast expressions, both within the primal part
-- and between primal and dual
-- | @Ast@ turns primal values and their operations into AST-building
-- counterparts.
data Ast :: Type -> ADMode -> Type -> Type where
  AstOp :: CodeOut -> [Ast r d a] -> Ast r d a
  AstCond :: AstBool r d -> Ast r d a -> Ast r d a -> Ast r d a
  AstSelect :: AstInt r d -> (AstVarName Int, AstBool r d)
            -> Ast r d (Vector r) -> Ast r d (Vector r) -> Ast r d (Vector r)
  AstConst :: a -> Ast r d a

  AstVar :: AstVarName (ADVal d r) -> Ast r d r

  AstMinElement :: Ast r d (Vector r) -> Ast r d r
  AstMaxElement :: Ast r d (Vector r) -> Ast r d r

  AstSumElements10 :: Ast r d (Vector r) -> Ast r d r
  AstIndex10 :: Ast r d (Vector r) -> AstInt r d -> Ast r d r
  AstDot0 :: Ast r d (Vector r) -> Ast r d (Vector r) -> Ast r d r

  AstFromList1 :: [Ast r d r] -> Ast r d (Vector r)
  AstFromVector1 :: Data.Vector.Vector (Ast r d r) -> Ast r d (Vector r)
  AstKonst1 :: Ast r d r -> AstInt r d -> Ast r d (Vector r)
  AstAppend1 :: Ast r d (Vector r) -> Ast r d (Vector r) -> Ast r d (Vector r)
  AstSlice1 :: AstInt r d -> AstInt r d -> Ast r d (Vector r)
            -> Ast r d (Vector r)
  AstReverse1 :: Ast r d (Vector r) -> Ast r d (Vector r)

  AstBuildPair1 :: AstInt r d -> (AstVarName Int, Ast r d r)
                -> Ast r d (Vector r)
  AstMapPair1 :: (AstVarName (ADVal d r), Ast r d r) -> Ast r d (Vector r)
              -> Ast r d (Vector r)

  AstOMap1 :: (Ast r d r -> Ast r d r) -> Ast r d (Vector r)
           -> Ast r d (Vector r)
    -- TODO: this is necessary for MonoFunctor and so for a particularly
    -- fast implementation of relu, but this introduces a closure on tape;
    -- we may need to hack around this by substituting MonoFunctor
    -- with something similar to AstVectorLike or by optimizing map1 enough
    -- that it's as fast in such a simple case

type Ast0 d r = Ast r d r

type Ast1 d r = Ast r d (Vector r)

newtype AstVarName t = AstVarName Int
  deriving (Show, Eq)

data AstVar r d =
    AstVar0 (ADVal d r)
  | AstVarI Int

data AstInt :: Type -> ADMode -> Type where
  AstIntOp :: CodeIntOut -> [AstInt r d] -> AstInt r d
  AstIntCond :: AstBool r d -> AstInt r d -> AstInt r d -> AstInt r d
  AstIntConst :: Int -> AstInt r d
  AstIntVar :: AstVarName Int -> AstInt r d

  AstLength :: Ast r d (Vector r) -> AstInt r d
  AstMinIndex :: Ast r d (Vector r) -> AstInt r d
  AstMaxIndex :: Ast r d (Vector r) -> AstInt r d

data AstBool :: Type -> ADMode -> Type where
  AstBoolOp :: CodeBoolOut -> [AstBool r d] -> AstBool r d
  AstBoolConst :: Bool -> AstBool r d
  AstRel :: RelOut -> [Ast r d r] -> AstBool r d  -- TODO: Vector?
  AstRelInt :: RelOut -> [AstInt r d] -> AstBool r d

deriving instance ( Show a, Show r, Numeric r
                  , Show (ADVal d a), Show (ADVal d r)
                  , Show (ADVal d (Vector r))
                  , Show (AstInt r d), Show (AstBool r d) )
                  => Show (Ast r d a)

deriving instance (Show (ADVal d r), Show (ADVal d (Vector r)))
                  => Show (AstVar r d)

deriving instance ( Show r, Numeric r
                  , Show (ADVal d r)
                  , Show (ADVal d (Vector r))
                  , Show (AstInt r d), Show (AstBool r d) )
                  => Show (AstInt r d)

deriving instance ( Show r, Numeric r
                  , Show (ADVal d r)
                  , Show (ADVal d (Vector r))
                  , Show (AstInt r d), Show (AstBool r d) )
                  => Show (AstBool r d)

-- @Out@ is a leftover from the outlining mechanism deleted in
-- https://github.com/Mikolaj/horde-ad/commit/c59947e13082c319764ec35e54b8adf8bc01691f
data CodeOut =
    PlusOut | MinusOut | TimesOut | NegateOut | AbsOut | SignumOut
  | DivideOut | RecipOut
  | ExpOut | LogOut | SqrtOut | PowerOut | LogBaseOut
  | SinOut | CosOut | TanOut | AsinOut | AcosOut | AtanOut
  | SinhOut | CoshOut | TanhOut | AsinhOut | AcoshOut | AtanhOut
  | Atan2Out
  | MaxOut | MinOut
  deriving Show

data CodeIntOut =
    PlusIntOut | MinusIntOut | TimesIntOut | NegateIntOut
  | AbsIntOut | SignumIntOut
  | MaxIntOut | MinIntOut
  deriving Show

data CodeBoolOut =
    NotOut | AndOut | OrOut | IffOut
  deriving Show

data RelOut =
    EqOut | NeqOut
  | LeqOut| GeqOut | LsOut | GtOut
  deriving Show


-- * Unlawful instances of AST types; they are lawful modulo evaluation

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (Ast r d a) where

instance Ord a => Ord (Ast r d a) where
  max u v = AstOp MaxOut [u, v]
  min u v = AstOp MinOut [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num a => Num (Ast r d a) where
  u + v = AstOp PlusOut [u, v]
  u - v = AstOp MinusOut [u, v]
  u * v = AstOp TimesOut [u, v]
  negate u = AstOp NegateOut [u]
  abs v = AstOp AbsOut [v]
  signum v = AstOp SignumOut [v]
  fromInteger = AstConst . fromInteger

instance Real a => Real (Ast r d a) where
  toRational = undefined  -- TODO?

instance Fractional a => Fractional (Ast r d a) where
  u / v = AstOp DivideOut  [u, v]
  recip v = AstOp RecipOut [v]
  fromRational = AstConst . fromRational

instance Floating a => Floating (Ast r d a) where
  pi = AstConst pi
  exp u = AstOp ExpOut [u]
  log u = AstOp LogOut [u]
  sqrt u = AstOp SqrtOut [u]
  u ** v = AstOp PowerOut [u, v]
  logBase u v = AstOp LogBaseOut [u, v]
  sin u = AstOp SinOut [u]
  cos u = AstOp CosOut [u]
  tan u = AstOp TanOut [u]
  asin u = AstOp AsinOut [u]
  acos u = AstOp AcosOut [u]
  atan u = AstOp AtanOut [u]
  sinh u = AstOp SinhOut [u]
  cosh u = AstOp CoshOut [u]
  tanh u = AstOp TanhOut [u]
  asinh u = AstOp AsinhOut [u]
  acosh u = AstOp AcoshOut [u]
  atanh u = AstOp AtanhOut [u]

instance RealFrac a => RealFrac (Ast r d a) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance RealFloat a => RealFloat (Ast r d a) where
  atan2 u v = AstOp Atan2Out [u, v]
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

instance Eq (AstInt r d) where

instance Ord (AstInt r d) where
  max u v = AstIntOp MaxIntOut [u, v]
  min u v = AstIntOp MinIntOut [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num (AstInt r d) where
  u + v = AstIntOp PlusIntOut [u, v]
  u - v = AstIntOp MinusIntOut [u, v]
  u * v = AstIntOp TimesIntOut [u, v]
  negate u = AstIntOp NegateIntOut [u]
  abs v = AstIntOp AbsIntOut [v]
  signum v = AstIntOp SignumIntOut [v]
  fromInteger = AstIntConst . fromInteger

instance Real (AstInt r d) where
  toRational = undefined  -- TODO

instance Enum (AstInt r d) where
  -- TODO

instance Integral (AstInt r d) where
  -- TODO

type instance Element (Ast r d (Vector r)) = Ast r d r

type instance Element (Ast Double d Double) = Ast Double d Double

type instance Element (Ast Float d Float) = Ast Float d Float

instance MonoFunctor (Ast r d (Vector r)) where
  omap = AstOMap1

instance MonoFunctor (Ast Double d Double) where
  omap f = f

instance MonoFunctor (Ast Float d Float) where
  omap f = f
