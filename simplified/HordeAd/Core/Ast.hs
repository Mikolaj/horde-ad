{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, GADTs, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, PolyKinds, QuantifiedConstraints,
             StandaloneDeriving, TypeFamilyDependencies,
             UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, but can be used
-- for arbitrary code transformations at the cost of limiting
-- expressiveness of transformed fragments to what AST captures.
module HordeAd.Core.Ast
  ( Ast(..), AstPrimalPart(..), AstVarName(..), AstVar(..)
  , AstInt(..), AstBool(..)
  , CodeOut(..), CodeIntOut(..), CodeBoolOut(..), RelOut(..)
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import qualified Data.Strict.Vector as Data.Vector
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Show.Functions ()

import HordeAd.Internal.OrthotopeOrphanInstances ()

-- * Definitions

-- TODO: consider sharing Ast expressions, both within the primal part
-- and between primal and dual
-- | AST of the code to be differentiated. The first argument is the underlying
-- scalar. It's necessary to type-check AstVar0. (TODO: try to remove it)
data Ast :: Type -> Type -> Type where
  AstOp :: CodeOut -> [Ast r a] -> Ast r a
  AstCond :: AstBool r -> Ast r a -> Ast r a -> Ast r a
  AstSelect :: AstInt r -> (AstVarName Int, AstBool r)
            -> Ast r (OR.Array 1 r) -> Ast r (OR.Array 1 r)
            -> Ast r (OR.Array 1 r)
  AstInt :: AstInt r -> Ast r a
  AstConst :: a -> Ast r a  -- sort of partially evaluated @AstConstant@
  AstConstant :: AstPrimalPart r a -> Ast r a
  AstScale :: AstPrimalPart r a -> Ast r a -> Ast r a

  AstVar0 :: AstVarName r -> Ast r r
  AstVar1 :: AstVarName (OR.Array 1 r) -> Ast r (OR.Array 1 r)

  -- Taken from VectorLike:
  AstSumElements10 :: Ast r (OR.Array 1 r) -> Ast r r
  AstIndex10 :: Ast r (OR.Array 1 r) -> AstInt r -> Ast r r
  AstMinimum0 :: Ast r (OR.Array 1 r) -> Ast r r
  AstMaximum0 :: Ast r (OR.Array 1 r) -> Ast r r
  AstDot0 :: Ast r (OR.Array 1 r) -> Ast r (OR.Array 1 r) -> Ast r r

  AstFromList1 :: [Ast r r] -> Ast r (OR.Array 1 r)
  AstFromVector1 :: Data.Vector.Vector (Ast r r) -> Ast r (OR.Array 1 r)
  AstKonst1 :: AstInt r -> Ast r r -> Ast r (OR.Array 1 r)
  AstAppend1 :: Ast r (OR.Array 1 r) -> Ast r (OR.Array 1 r)
             -> Ast r (OR.Array 1 r)
  AstSlice1 :: AstInt r -> AstInt r -> Ast r (OR.Array 1 r)
            -> Ast r (OR.Array 1 r)
  AstReverse1 :: Ast r (OR.Array 1 r) -> Ast r (OR.Array 1 r)

  AstBuildPair1 :: AstInt r -> (AstVarName Int, Ast r r)
                -> Ast r (OR.Array 1 r)
  AstMapPair1 :: (AstVarName r, Ast r r) -> Ast r (OR.Array 1 r)
              -> Ast r (OR.Array 1 r)

  AstOMap1 :: (AstVarName r, Ast r r) -> Ast r (OR.Array 1 r)
           -> Ast r (OR.Array 1 r)
    -- this is necessary for MonoFunctor and so for a particularly
    -- fast implementation of relu
    -- TODO: this is really only needed in AstPrimalPart, but making
    -- AstPrimalPart data instead of a newtype would complicate a lot of code

newtype AstPrimalPart r a = AstPrimalPart (Ast r a)

newtype AstVarName t = AstVarName Int
  deriving (Show, Eq)

data AstVar a0 a1 =
    AstVarR0 a0
  | AstVarR1 a1
  | AstVarI Int

-- Like the first argument of @Ast@, the argument is the underlying scalar.
-- TODO: change Ast below to AstPrimalPart in case AstPrimalPart get
-- more constructors.
data AstInt :: Type -> Type where
  AstIntOp :: CodeIntOut -> [AstInt r] -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntVar :: AstVarName Int -> AstInt r

  -- Taken from VectorLike:
  AstLength :: Ast r (OR.Array 1 r) -> AstInt r
  AstMinIndex :: Ast r (OR.Array 1 r) -> AstInt r
  AstMaxIndex :: Ast r (OR.Array 1 r) -> AstInt r

-- Like the first argument of @Ast@, the argument is the underlying scalar.
-- TODO: change Ast below to AstPrimalPart in case AstPrimalPart get
-- more constructors.
data AstBool :: Type -> Type where
  AstBoolOp :: CodeBoolOut -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: RelOut -> [Ast r r] -> AstBool r  -- TODO: Vector?
  AstRelInt :: RelOut -> [AstInt r] -> AstBool r

{-
deriving instance ( Show a, Show r, Numeric r
                  , Show (ADVal d a), Show (ADVal d r)
                  , Show (ADVal d (OR.Array 1 r))
                  , Show (AstInt r), Show (AstBool r) )
                  => Show (Ast r a)

deriving instance (Show (ADVal d r), Show (ADVal d (OR.Array 1 r)))
                  => Show (AstVar r)

deriving instance ( Show r, Numeric r
                  , Show (ADVal d r)
                  , Show (ADVal d (OR.Array 1 r))
                  , Show (AstInt r), Show (AstBool r) )
                  => Show (AstInt r)

deriving instance ( Show r, Numeric r
                  , Show (ADVal d r)
                  , Show (ADVal d (OR.Array 1 r))
                  , Show (AstInt r), Show (AstBool r) )
                  => Show (AstBool r)
-}

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
instance Eq (Ast r a) where

instance Ord a => Ord (Ast r a) where
  max u v = AstOp MaxOut [u, v]
  min u v = AstOp MinOut [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num a => Num (Ast r a) where
  u + v = AstOp PlusOut [u, v]
  u - v = AstOp MinusOut [u, v]
  u * v = AstOp TimesOut [u, v]
  negate u = AstOp NegateOut [u]
  abs v = AstOp AbsOut [v]
  signum v = AstOp SignumOut [v]
  fromInteger = AstConst . fromInteger

instance Real a => Real (Ast r a) where
  toRational = undefined  -- TODO?

instance Fractional a => Fractional (Ast r a) where
  u / v = AstOp DivideOut  [u, v]
  recip v = AstOp RecipOut [v]
  fromRational = AstConst . fromRational

instance Floating a => Floating (Ast r a) where
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

instance RealFrac a => RealFrac (Ast r a) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance RealFloat a => RealFloat (Ast r a) where
  atan2 u v = AstOp Atan2Out [u, v]
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

instance Eq (AstInt r) where

instance Ord (AstInt r) where
  max u v = AstIntOp MaxIntOut [u, v]
  min u v = AstIntOp MinIntOut [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num (AstInt r) where
  u + v = AstIntOp PlusIntOut [u, v]
  u - v = AstIntOp MinusIntOut [u, v]
  u * v = AstIntOp TimesIntOut [u, v]
  negate u = AstIntOp NegateIntOut [u]
  abs v = AstIntOp AbsIntOut [v]
  signum v = AstIntOp SignumIntOut [v]
  fromInteger = AstIntConst . fromInteger

instance Real (AstInt r) where
  toRational = undefined  -- TODO

instance Enum (AstInt r) where
  -- TODO

instance Integral (AstInt r) where
  -- TODO

instance Eq (AstPrimalPart r a) where

instance Ord a => Ord (AstPrimalPart r a) where
  max (AstPrimalPart u) (AstPrimalPart v) = AstPrimalPart (AstOp MaxOut [u, v])
  min (AstPrimalPart u) (AstPrimalPart v) = AstPrimalPart (AstOp MinOut [u, v])
    -- unfortunately, the others can't be made to return @AstBool@

deriving instance Num (Ast r a) => Num (AstPrimalPart r a)
deriving instance (Real (Ast r a), Ord a) => Real (AstPrimalPart r a)
deriving instance Fractional (Ast r a) => Fractional (AstPrimalPart r a)
-- TODO: etc.

type instance Element (AstPrimalPart r a) = AstPrimalPart r (Element a)

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

astOmap :: (Ast r r -> Ast r r) -> Ast r (OR.Array 1 r) -> Ast r (OR.Array 1 r)
{-# NOINLINE astOmap #-}
astOmap f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap1 (freshAstVar, f (AstVar0 freshAstVar)) e

instance MonoFunctor (AstPrimalPart r (OR.Array 1 r)) where
  omap f (AstPrimalPart x) =
    let g y = let AstPrimalPart z = f (AstPrimalPart y)
              in z
    in AstPrimalPart (astOmap g x)

instance MonoFunctor (AstPrimalPart Double Double) where
  omap f = f

instance MonoFunctor (AstPrimalPart Float Float) where
  omap f = f
