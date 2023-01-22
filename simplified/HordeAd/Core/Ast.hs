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
  ( Ast0(..), AstPrimalPart0(..), Ast1(..), AstPrimalPart1(..)
  , AstVarName(..), AstVar(..)
  , AstInt(..), AstBool(..)
  , CodeOut(..), CodeIntOut(..), CodeBoolOut(..), RelOut(..)
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import qualified Data.Strict.Vector as Data.Vector
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Show.Functions ()

import HordeAd.Internal.OrthotopeOrphanInstances ()

-- * Definitions

-- TODO: consider sharing Ast expressions, both within the primal part
-- and between primal and dual
-- | AST of the code to be differentiated. The argument is the underlying
-- scalar.
data Ast0 :: Type -> Type where
  AstOp0 :: CodeOut -> [Ast0 r] -> Ast0 r
  AstCond0 :: AstBool r -> Ast0 r -> Ast0 r -> Ast0 r
  AstInt0 :: AstInt r -> Ast0 r
  AstConst0 :: r -> Ast0 r  -- sort of partially evaluated @AstConstant0@
  AstConstant0 :: AstPrimalPart0 r -> Ast0 r
  AstScale0 :: AstPrimalPart0 r -> Ast0 r -> Ast0 r

  AstVar0 :: AstVarName r -> Ast0 r

  -- Rank temporarily fixed to 1, to avoid hard type-level programming.
  AstIndex10 :: Ast1 1 r -> [AstInt r] -> Ast0 r
  AstSum10 :: Ast1 1 r -> Ast0 r
  AstDot10 :: Ast1 1 r -> Ast1 1 r -> Ast0 r
  AstFrom10 :: Ast1 0 r -> Ast0 r

  AstOMap0 :: (AstVarName r, Ast0 r) -> Ast0 r -> Ast0 r
    -- see AstOMap1; this is needed even at rank 0 to capture and interpret
    -- the function instead of evaluating it on terms (e.g., comparing them)

newtype AstPrimalPart0 r = AstPrimalPart0 (Ast0 r)

data Ast1 :: Nat -> Type -> Type where
  AstOp1 :: CodeOut -> [Ast1 n r] -> Ast1 n r
  AstCond1 :: AstBool r -> Ast1 n r -> Ast1 n r -> Ast1 n r
  AstSelect1 :: AstInt r -> (AstVarName Int, AstBool r) -> Ast1 n r -> Ast1 n r
             -> Ast1 n r
  AstInt1 :: AstInt r -> Ast1 n r
  AstConst1 :: OR.Array n r -> Ast1 n r
    -- sort of partially evaluated @AstConstant1@
  AstConstant1 :: AstPrimalPart1 n r -> Ast1 n r
  AstScale1 :: AstPrimalPart1 n r -> Ast1 n r -> Ast1 n r

  AstVar1 :: AstVarName (OR.Array 1 r) -> Ast1 1 r

  AstIndex1 :: Ast1 (1 + n) r -> AstInt r -> Ast1 n r
  AstSum1 :: Ast1 (1 + n) r -> Ast1 n r
  -- No shape argument, because we'd need [AstInt], because it changes
  -- during vectorization. The trade-off is a crash when the argument is empty,
  -- but the user wants n =\ 1. TODO: perhaps just use List.NonEmpty,
  -- but is there Vector.NonEmpty and, in the future, Tensor.NonEmpty?
  -- For now, it crashes for empty arguments always.
  AstFromList1 :: [Ast1 n r] -> Ast1 (1 + n) r
  AstFromVector1 :: Data.Vector.Vector (Ast1 n r)
                 -> Ast1 (1 + n) r
  AstKonst1 :: AstInt r -> Ast1 n r -> Ast1 (1 + n) r
  AstAppend1 :: Ast1 n r -> Ast1 n r -> Ast1 n r
  AstSlice1 :: AstInt r -> AstInt r -> Ast1 n r -> Ast1 n r
  AstReverse1 :: Ast1 n r -> Ast1 n r
  AstBuildPair1 :: AstInt r -> (AstVarName Int, Ast1 n r) -> Ast1 (1 + n) r
  AstTranspose1 :: Ast1 n r -> Ast1 n r
  -- TODO: how to handle the shape argument?
  AstReshape1 :: KnownNat n
              => OR.ShapeL -> Ast1 n r -> Ast1 m r

  -- Rank temporarily fixed to 1, to avoid hard type-level programming.
  AstFromList01 :: [Ast0 r] -> Ast1 1 r
  AstFromVector01 :: Data.Vector.Vector (Ast0 r) -> Ast1 1 r
  AstKonst01 :: AstInt r -> Ast0 r -> Ast1 1 r
  -- We don't have AstVarName for list variables, so only rank 1 for now:
  AstBuildPair01 :: AstInt r -> (AstVarName Int, Ast0 r)
                 -> Ast1 1 r
  AstMapPair01 :: (AstVarName r, Ast0 r) -> Ast1 1 r
               -> Ast1 1 r
  AstZipWithPair01 :: (AstVarName r, AstVarName r, Ast0 r)
                   -> Ast1 1 r -> Ast1 1 r
                   -> Ast1 1 r
  AstFrom01 :: Ast0 r -> Ast1 0 r

  AstOMap1 :: (AstVarName r, Ast0 r) -> Ast1 1 r -> Ast1 1 r
    -- this is necessary for MonoFunctor and so for a particularly
    -- fast implementation of relu
    -- TODO: this is really only needed in AstPrimalPart, but making
    -- AstPrimalPart data instead of a newtype would complicate a lot of code

newtype AstPrimalPart1 n r = AstPrimalPart1 (Ast1 n r)

newtype AstVarName t = AstVarName Int
  deriving (Show, Eq)

data AstVar a0 a1 =
    AstVarR0 a0
  | AstVarR1 a1
  | AstVarI Int

-- In AstInt and AstBool, the Ast0 and Ast1 terms are morally AstPrimalPart,
-- since their derivative part is not used.
-- TODO: introduce AstPrimalPart explicitly when convenient, e.g.,
-- as soon as AstPrimalPart gets more constructors.

-- Like the argument to @Ast0@, the argument is the underlying scalar.
data AstInt :: Type -> Type where
  AstIntOp :: CodeIntOut -> [AstInt r] -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntVar :: AstVarName Int -> AstInt r

  AstLength :: Ast1 1 r -> AstInt r  -- makes no sense for n == 0
  AstMinIndex :: Ast1 1 r -> AstInt r  -- list output needed for n /= 1
  AstMaxIndex :: Ast1 1 r -> AstInt r  -- list output needed for n /= 1

data AstBool :: Type -> Type where
  AstBoolOp :: CodeBoolOut -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: RelOut -> [Ast0 r] -> AstBool r  -- TODO: Ast1, too?
  AstRelInt :: RelOut -> [AstInt r] -> AstBool r

{-
deriving instance ( Show a, Show r, Numeric r
                  , Show (ADVal d a), Show (ADVal d r)
                  , Show (ADVal d (OR.Array 1 r))
                  , Show (AstInt r), Show (AstBool r) )
                  => Show (Ast1 n r)

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
instance Eq (Ast0 r) where

instance Ord r => Ord (Ast0 r) where
  max u v = AstOp0 MaxOut [u, v]
  min u v = AstOp0 MinOut [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num r => Num (Ast0 r) where
  u + v = AstOp0 PlusOut [u, v]
  u - v = AstOp0 MinusOut [u, v]
  u * v = AstOp0 TimesOut [u, v]
  negate u = AstOp0 NegateOut [u]
  abs v = AstOp0 AbsOut [v]
  signum v = AstOp0 SignumOut [v]
  fromInteger = AstConst0 . fromInteger

instance Real r => Real (Ast0 r) where
  toRational = undefined  -- TODO?

instance Fractional r => Fractional (Ast0 r) where
  u / v = AstOp0 DivideOut  [u, v]
  recip v = AstOp0 RecipOut [v]
  fromRational = AstConst0 . fromRational

instance Floating r => Floating (Ast0 r) where
  pi = AstConst0 pi
  exp u = AstOp0 ExpOut [u]
  log u = AstOp0 LogOut [u]
  sqrt u = AstOp0 SqrtOut [u]
  u ** v = AstOp0 PowerOut [u, v]
  logBase u v = AstOp0 LogBaseOut [u, v]
  sin u = AstOp0 SinOut [u]
  cos u = AstOp0 CosOut [u]
  tan u = AstOp0 TanOut [u]
  asin u = AstOp0 AsinOut [u]
  acos u = AstOp0 AcosOut [u]
  atan u = AstOp0 AtanOut [u]
  sinh u = AstOp0 SinhOut [u]
  cosh u = AstOp0 CoshOut [u]
  tanh u = AstOp0 TanhOut [u]
  asinh u = AstOp0 AsinhOut [u]
  acosh u = AstOp0 AcoshOut [u]
  atanh u = AstOp0 AtanhOut [u]

instance RealFrac r => RealFrac (Ast0 r) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance RealFloat r => RealFloat (Ast0 r) where
  atan2 u v = AstOp0 Atan2Out [u, v]
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

instance Eq (AstPrimalPart0 r) where

instance Ord r => Ord (AstPrimalPart0 r) where
  max (AstPrimalPart0 u) (AstPrimalPart0 v) =
    AstPrimalPart0 (AstOp0 MaxOut [u, v])
  min (AstPrimalPart0 u) (AstPrimalPart0 v) =
    AstPrimalPart0 (AstOp0 MinOut [u, v])
    -- unfortunately, the others can't be made to return @AstBool@

deriving instance Num (Ast0 r) => Num (AstPrimalPart0 r)
deriving instance (Real (Ast0 r), Ord r) => Real (AstPrimalPart0 r)
deriving instance Fractional (Ast0 r) => Fractional (AstPrimalPart0 r)
-- TODO: etc.

type instance Element (AstPrimalPart0 r) = AstPrimalPart0 r


-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (Ast1 n r) where

instance Ord (OR.Array n r) => Ord (Ast1 n r) where
  max u v = AstOp1 MaxOut [u, v]
  min u v = AstOp1 MinOut [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num (OR.Array n r) => Num (Ast1 n r) where
  u + v = AstOp1 PlusOut [u, v]
  u - v = AstOp1 MinusOut [u, v]
  u * v = AstOp1 TimesOut [u, v]
  negate u = AstOp1 NegateOut [u]
  abs v = AstOp1 AbsOut [v]
  signum v = AstOp1 SignumOut [v]
  fromInteger = AstConst1 . fromInteger

instance Real (OR.Array n r) => Real (Ast1 n r) where
  toRational = undefined  -- TODO?

instance Fractional (OR.Array n r) => Fractional (Ast1 n r) where
  u / v = AstOp1 DivideOut  [u, v]
  recip v = AstOp1 RecipOut [v]
  fromRational = AstConst1 . fromRational

instance Floating (OR.Array n r) => Floating (Ast1 n r) where
  pi = AstConst1 pi
  exp u = AstOp1 ExpOut [u]
  log u = AstOp1 LogOut [u]
  sqrt u = AstOp1 SqrtOut [u]
  u ** v = AstOp1 PowerOut [u, v]
  logBase u v = AstOp1 LogBaseOut [u, v]
  sin u = AstOp1 SinOut [u]
  cos u = AstOp1 CosOut [u]
  tan u = AstOp1 TanOut [u]
  asin u = AstOp1 AsinOut [u]
  acos u = AstOp1 AcosOut [u]
  atan u = AstOp1 AtanOut [u]
  sinh u = AstOp1 SinhOut [u]
  cosh u = AstOp1 CoshOut [u]
  tanh u = AstOp1 TanhOut [u]
  asinh u = AstOp1 AsinhOut [u]
  acosh u = AstOp1 AcoshOut [u]
  atanh u = AstOp1 AtanhOut [u]

instance RealFrac (OR.Array n r) => RealFrac (Ast1 n r) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance RealFloat (OR.Array n r) => RealFloat (Ast1 n r) where
  atan2 u v = AstOp1 Atan2Out [u, v]
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

instance Eq (AstPrimalPart1 n r) where

instance Ord r => Ord (AstPrimalPart1 n r) where
  max (AstPrimalPart1 u) (AstPrimalPart1 v) =
    AstPrimalPart1 (AstOp1 MaxOut [u, v])
  min (AstPrimalPart1 u) (AstPrimalPart1 v) =
    AstPrimalPart1 (AstOp1 MinOut [u, v])
    -- unfortunately, the others can't be made to return @AstBool@

deriving instance Num (Ast1 n r) => Num (AstPrimalPart1 n r)
deriving instance (Real (Ast1 n r), Ord r) => Real (AstPrimalPart1 n r)
deriving instance Fractional (Ast1 n r) => Fractional (AstPrimalPart1 n r)
-- TODO: etc.

type instance Element (AstPrimalPart1 n r) = AstPrimalPart0 r


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


-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

astOmap0 :: (Ast0 r -> Ast0 r) -> Ast0 r -> Ast0 r
{-# NOINLINE astOmap0 #-}
astOmap0 f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap0 (freshAstVar, f (AstVar0 freshAstVar)) e

astOmap1 :: (Ast0 r -> Ast0 r) -> Ast1 1 r -> Ast1 1 r
{-# NOINLINE astOmap1 #-}
astOmap1 f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap1 (freshAstVar, f (AstVar0 freshAstVar)) e

instance MonoFunctor (AstPrimalPart1 1 r) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart0 z = f (AstPrimalPart0 y)
              in z
    in AstPrimalPart1 (astOmap1 g x)

instance MonoFunctor (AstPrimalPart0 Double) where
  omap f (AstPrimalPart0 x) =
    let g y = let AstPrimalPart0 z = f (AstPrimalPart0 y)
              in z
    in AstPrimalPart0 (astOmap0 g x)

instance MonoFunctor (AstPrimalPart0 Float) where
  omap f (AstPrimalPart0 x) =
    let g y = let AstPrimalPart0 z = f (AstPrimalPart0 y)
              in z
    in AstPrimalPart0 (astOmap0 g x)
