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
  ( Ast(..), AstPrimalPart1(..)
  , AstVarName(..), AstVar(..)
  , AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
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
data Ast :: Nat -> Type -> Type where
  AstOp1 :: OpCode -> [Ast n r] -> Ast n r
  AstCond1 :: AstBool r -> Ast n r -> Ast n r -> Ast n r
  AstSelect1 :: AstInt r -> (AstVarName Int, AstBool r) -> Ast n r -> Ast n r
             -> Ast n r
  AstInt1 :: AstInt r -> Ast n r
  AstConst1 :: OR.Array n r -> Ast n r
    -- sort of partially evaluated @AstConstant1@
  AstConstant1 :: AstPrimalPart1 n r -> Ast n r
  AstScale1 :: AstPrimalPart1 n r -> Ast n r -> Ast n r

  AstVar0 :: AstVarName r -> Ast 0 r
  AstVar1 :: AstVarName (OR.Array 1 r) -> Ast 1 r

  AstIndex1 :: Ast (1 + n) r -> AstInt r -> Ast n r
  AstSum1 :: Ast (1 + n) r -> Ast n r
  -- No shape argument, because we'd need [AstInt], because it changes
  -- during vectorization. The trade-off is a crash when the argument is empty,
  -- but the user wants n =\ 1. TODO: perhaps just use List.NonEmpty,
  -- but is there Vector.NonEmpty and, in the future, Tensor.NonEmpty?
  -- For now, it crashes for empty arguments always.
  AstFromList1 :: [Ast n r] -> Ast (1 + n) r
  AstFromVector1 :: Data.Vector.Vector (Ast n r)
                 -> Ast (1 + n) r
  AstKonst1 :: AstInt r -> Ast n r -> Ast (1 + n) r
  AstAppend1 :: KnownNat n
             => Ast n r -> Ast n r -> Ast n r
  AstSlice1 :: AstInt r -> AstInt r -> Ast n r -> Ast n r
  AstReverse1 :: KnownNat n
              => Ast n r -> Ast n r
  AstBuildPair1 :: AstInt r -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
  AstTranspose1 :: Ast n r -> Ast n r
  AstTransposeGeneral1 :: [Int] -> Ast n r -> Ast n r
  AstFlatten :: KnownNat n
             => Ast n r -> Ast 1 r
  AstReshape1 :: KnownNat n
              => [AstInt r] -> Ast n r -> Ast m r

  -- Syntactic sugar with much more efficient non-sugar implementations.
  -- If we give the user access to tensors, not just vectors, these
  -- operations will be necessary.
  -- Rank temporarily fixed to 1, to avoid the AstShape constructor.
  AstIndex0 :: Ast 1 r -> [AstInt r] -> Ast 0 r  -- TODO: land on m?
  AstSum0 :: KnownNat n
          => Ast n r -> Ast 0 r
  AstDot0 :: KnownNat n
          => Ast n r -> Ast n r -> Ast 0 r

  -- If we give the user access to tensors, not just vectors, these
  -- operations will be necessary.
  -- Rank temporarily fixed to 1, to avoid hard type-level programming
  -- and/or the AstShape constructor.
  AstFromList01 :: [AstInt r] -> [Ast 0 r] -> Ast 1 r
  AstFromVector01 :: [AstInt r] -> Data.Vector.Vector (Ast 0 r) -> Ast 1 r
  AstKonst01 :: [AstInt r] -> Ast 0 r -> Ast 1 r
  -- We don't have AstVarName for list variables, so only rank 1 for now:
  AstBuildPair01 :: AstInt r -> (AstVarName Int, Ast 0 r)
                 -> Ast 1 r

  AstOMap0 :: (AstVarName r, Ast 0 r) -> Ast 0 r -> Ast 0 r
  AstOMap1 :: (AstVarName r, Ast 0 r) -> Ast 1 r -> Ast 1 r
    -- this is necessary for MonoFunctor and so for a particularly
    -- fast implementation of relu
    -- TODO: this is really only needed in AstPrimalPart, but making
    -- AstPrimalPart data instead of a newtype would complicate a lot of code

newtype AstPrimalPart1 n r = AstPrimalPart1 (Ast n r)

newtype AstVarName t = AstVarName Int
  deriving (Show, Eq)

data AstVar a0 a1 =
    AstVarR0 a0
  | AstVarR1 a1
  | AstVarI Int

-- In AstInt and AstBool, the Ast terms are morally AstPrimalPart,
-- since their derivative part is not used.
-- TODO: introduce AstPrimalPart explicitly when convenient, e.g.,
-- as soon as AstPrimalPart gets more constructors.

-- The argument is the underlying scalar.
data AstInt :: Type -> Type where
  AstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntVar :: AstVarName Int -> AstInt r

  AstLength :: KnownNat n
            => Ast (1 + n) r -> AstInt r  -- length of the outermost dimension
  AstMinIndex :: Ast 1 r -> AstInt r  -- list output needed for n /= 1
  AstMaxIndex :: Ast 1 r -> AstInt r  -- list output needed for n /= 1

data AstBool :: Type -> Type where
  AstBoolOp :: OpCodeBool -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: OpCodeRel -> [Ast 0 r] -> AstBool r  -- TODO: Ast 1, too?
  AstRelInt :: OpCodeRel -> [AstInt r] -> AstBool r

{-
deriving instance ( Show a, Show r, Numeric r
                  , Show (ADVal d a), Show (ADVal d r)
                  , Show (ADVal d (OR.Array 1 r))
                  , Show (AstInt r), Show (AstBool r) )
                  => Show (Ast n r)

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

-- Copied from the outlining mechanism deleted in
-- https://github.com/Mikolaj/horde-ad/commit/c59947e13082c319764ec35e54b8adf8bc01691f
data OpCode =
    PlusOp | MinusOp | TimesOp | NegateOp | AbsOp | SignumOp
  | DivideOp | RecipOp
  | ExpOp | LogOp | SqrtOp | PowerOp | LogBaseOp
  | SinOp | CosOp | TanOp | AsinOp | AcosOp | AtanOp
  | SinhOp | CoshOp | TanhOp | AsinhOp | AcoshOp | AtanhOp
  | Atan2Op
  | MaxOp | MinOp
  deriving Show

data OpCodeInt =
    PlusIntOp | MinusIntOp | TimesIntOp | NegateIntOp
  | AbsIntOp | SignumIntOp
  | MaxIntOp | MinIntOp
  deriving Show

data OpCodeBool =
    NotOp | AndOp | OrOp | IffOp
  deriving Show

data OpCodeRel =
    EqOp | NeqOp
  | LeqOp| GeqOp | LsOp | GtOp
  deriving Show


-- * Unlawful instances of AST types; they are lawful modulo evaluation

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (Ast n r) where

instance Ord (OR.Array n r) => Ord (Ast n r) where
  max u v = AstOp1 MaxOp [u, v]
  min u v = AstOp1 MinOp [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num (OR.Array n r) => Num (Ast n r) where
  u + v = AstOp1 PlusOp [u, v]
  u - v = AstOp1 MinusOp [u, v]
  u * v = AstOp1 TimesOp [u, v]
  negate u = AstOp1 NegateOp [u]
  abs v = AstOp1 AbsOp [v]
  signum v = AstOp1 SignumOp [v]
  fromInteger = AstConst1 . fromInteger

instance Real (OR.Array n r) => Real (Ast n r) where
  toRational = undefined  -- TODO?

instance Fractional (OR.Array n r) => Fractional (Ast n r) where
  u / v = AstOp1 DivideOp  [u, v]
  recip v = AstOp1 RecipOp [v]
  fromRational = AstConst1 . fromRational

instance Floating (OR.Array n r) => Floating (Ast n r) where
  pi = AstConst1 pi
  exp u = AstOp1 ExpOp [u]
  log u = AstOp1 LogOp [u]
  sqrt u = AstOp1 SqrtOp [u]
  u ** v = AstOp1 PowerOp [u, v]
  logBase u v = AstOp1 LogBaseOp [u, v]
  sin u = AstOp1 SinOp [u]
  cos u = AstOp1 CosOp [u]
  tan u = AstOp1 TanOp [u]
  asin u = AstOp1 AsinOp [u]
  acos u = AstOp1 AcosOp [u]
  atan u = AstOp1 AtanOp [u]
  sinh u = AstOp1 SinhOp [u]
  cosh u = AstOp1 CoshOp [u]
  tanh u = AstOp1 TanhOp [u]
  asinh u = AstOp1 AsinhOp [u]
  acosh u = AstOp1 AcoshOp [u]
  atanh u = AstOp1 AtanhOp [u]

instance RealFrac (OR.Array n r) => RealFrac (Ast n r) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance RealFloat (OR.Array n r) => RealFloat (Ast n r) where
  atan2 u v = AstOp1 Atan2Op [u, v]
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

instance Eq (AstPrimalPart1 n r) where

instance Ord r => Ord (AstPrimalPart1 n r) where
  max (AstPrimalPart1 u) (AstPrimalPart1 v) =
    AstPrimalPart1 (AstOp1 MaxOp [u, v])
  min (AstPrimalPart1 u) (AstPrimalPart1 v) =
    AstPrimalPart1 (AstOp1 MinOp [u, v])
    -- unfortunately, the others can't be made to return @AstBool@

deriving instance Num (Ast n r) => Num (AstPrimalPart1 n r)
deriving instance (Real (Ast n r), Ord r) => Real (AstPrimalPart1 n r)
deriving instance Fractional (Ast n r) => Fractional (AstPrimalPart1 n r)
-- TODO: etc.

type instance Element (AstPrimalPart1 n r) = AstPrimalPart1 0 r


instance Eq (AstInt r) where

instance Ord (AstInt r) where
  max u v = AstIntOp MaxIntOp [u, v]
  min u v = AstIntOp MinIntOp [u, v]
    -- unfortunately, the others can't be made to return @AstBool@

instance Num (AstInt r) where
  u + v = AstIntOp PlusIntOp [u, v]
  u - v = AstIntOp MinusIntOp [u, v]
  u * v = AstIntOp TimesIntOp [u, v]
  negate u = AstIntOp NegateIntOp [u]
  abs v = AstIntOp AbsIntOp [v]
  signum v = AstIntOp SignumIntOp [v]
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

astOmap0 :: (Ast 0 r -> Ast 0 r) -> Ast 0 r -> Ast 0 r
{-# NOINLINE astOmap0 #-}
astOmap0 f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap0 (freshAstVar, f (AstVar0 freshAstVar)) e

astOmap1 :: (Ast 0 r -> Ast 0 r) -> Ast 1 r -> Ast 1 r
{-# NOINLINE astOmap1 #-}
astOmap1 f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap1 (freshAstVar, f (AstVar0 freshAstVar)) e

instance MonoFunctor (AstPrimalPart1 1 r) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart1 z = f (AstPrimalPart1 y)
              in z
    in AstPrimalPart1 (astOmap1 g x)

instance MonoFunctor (AstPrimalPart1 0 Double) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart1 z = f (AstPrimalPart1 y)
              in z
    in AstPrimalPart1 (astOmap0 g x)

instance MonoFunctor (AstPrimalPart1 0 Float) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart1 z = f (AstPrimalPart1 y)
              in z
    in AstPrimalPart1 (astOmap0 g x)
