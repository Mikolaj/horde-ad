{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances, GADTs,
             GeneralizedNewtypeDeriving, KindSignatures, MultiParamTypeClasses,
             PolyKinds, QuantifiedConstraints, StandaloneDeriving,
             TypeFamilyDependencies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, but can be used
-- for arbitrary code transformations at the cost of limiting
-- expressiveness of transformed fragments to what AST captures.
module HordeAd.Core.Ast
  ( AstShape, AstPath, AstPermutation
  , Ast(..), AstPrimalPart1(..)
  , AstVarName(..), AstVar(..)
  , AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  , shapeAst, lengthAst, substituteAst, substituteAstInt, substituteAstBool
  , toIxAst
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.Monoid (All (..))
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Show.Functions ()

import HordeAd.Internal.OrthotopeOrphanInstances ()

-- * GHC.Nat-indexed lists, originally by Tom Smeding

-- This needs to be moved to a better place, probably its own module,
-- once its clear which other modules depend on it.

-- | An index in an n-dimensional array. The fastest-moving index is at the
-- last position; thus the index 'Z :. i :. j' represents 'a[i][j]' in
-- traditional C notation.
data Index (n :: Nat) i where
  Z :: Index 0 i
  (:.) :: Index n i  -> i -> Index (n + 1) i
infixl 3 :.
-- This fixity is stolen from Accelerate:
--   https://hackage.haskell.org/package/accelerate-1.3.0.0/docs/Data-Array-Accelerate.html#t::.

instance Show i => Show (Index n i) where
  showsPrec _ Z = showString "Z"
  showsPrec d (idx :. i) = showParen (d > 3) $
    showsPrec 3 idx . showString " :. " . showsPrec 4 i

-- | The shape of an n-dimensional array. Represented by an index to not
-- duplicate representations and convert easily between each. It seems unlikely
-- enough to make mistakes even with this dumb wrapper, so it might be fine.
newtype Shape n i = Shape (Index n i)
  deriving (Show)

-- | The number of elements in an array of this shape
shapeSize :: Shape n Int -> Int
shapeSize (Shape Z) = 1
shapeSize (Shape (sh :. i)) = shapeSize (Shape sh) * i

toLinearIdx :: Shape n Int -> Index n Int -> Int
toLinearIdx (Shape Z) Z = 0
toLinearIdx (Shape (sh :. n)) (idx :. i) = n * toLinearIdx (Shape sh) idx + i

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index
fromLinearIdx :: Shape n Int -> Int -> Index n Int
fromLinearIdx (Shape Z) 0 = Z
fromLinearIdx (Shape Z) _ = error "Index out of range"
fromLinearIdx (Shape (sh :. n)) idx =
  let (idx', i) = idx `quotRem` n
  in fromLinearIdx (Shape sh) idx' :. i

-- | The zero index in this shape (not dependent on the actual integers)
zeroOf :: Num i => Shape n i -> Index n i
zeroOf (Shape Z) = Z
zeroOf (Shape (sh :. _)) = zeroOf (Shape sh) :. 0

-- | Pairwise comparison of two index values. The comparison function is invoked
-- once for each rank on the corresponding pair of indices.
idxCompare :: Monoid m => (Int -> Int -> m) -> Index n Int -> Index n Int -> m
idxCompare _ Z Z = mempty
idxCompare f (idx :. i) (idx' :. j) = f i j <> idxCompare f idx idx'

-- | A multidimensional array of rank @n@ containing elements of type @a@
data Array n a = Array (Shape n Int) (Vector a)
  deriving (Show)

-- | Generate an array by specifying the element that goes at each index
build ::  Numeric a => Shape n Int -> (Index n Int -> a) -> Array n a
build sh f = Array sh (V.generate (shapeSize sh) (\i -> f (fromLinearIdx sh i)))

-- | Index into an array
(!) :: Numeric a => Array n a -> Index n Int -> a
(!) (Array sh@(Shape shIdx) vec) idx
  -- just some bounds checks
  | getAll $ idxCompare ((All .) . (>=)) idx (zeroOf sh)
  , getAll $ idxCompare ((All .) . (<)) idx shIdx
  -- the actual indexing operation
  = vec V.! toLinearIdx sh idx
  | otherwise
  = error "Index out of bounds in (!)"

-- | Sum along the inner, fastest-moving dimension
sum' :: Numeric a => Array (n + 1) a -> Array n a
sum' arr@(Array (Shape (sh :. n)) _) =
  build (Shape sh) (\idx -> sum [arr ! (idx :. i) | i <- [0 .. n-1]])

main :: IO ()
main = do
  let b :: Array 2 Double
      b = build (Shape (Z :. 3 :. 2)) (\(Z :. i :. j) -> fromIntegral i + fromIntegral j)
  print (sum' b)


-- * Ast definitions

-- @[AstInt r]@ gives more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents statically known shapes.
-- However, if we switched to @Data.Array.Shaped@ and moved most of the shapes
-- to the type level, we'd recover some of the expressiveness, while retaining
-- statically known (type-parameterized) shapes.
type AstShape r = [Int]

type AstPath r = [AstInt r]

type AstPermutation = [Int]

-- TODO: consider sharing Ast expressions, both within the primal part
-- and between primal and dual


-- | AST for a tensor of rank n and elements r that is meant
-- to be differentiated.
data Ast :: Nat -> Type -> Type where
  -- For the numeric classes:
  AstOp :: OpCode -> [Ast n r] -> Ast n r

  -- For HasPrimal class and the future Conditional/Boolean/Eq'/Ord' classes:
  AstCond :: AstBool r -> Ast n r -> Ast n r -> Ast n r
  AstConstInt :: AstInt r -> Ast n r
  AstConst :: OR.Array n r -> Ast n r
    -- sort of partially evaluated @AstConstant@
  AstConstant :: AstPrimalPart1 n r -> Ast n r
  AstScale :: AstPrimalPart1 n r -> Ast n r -> Ast n r
  AstVar :: [Int] -> AstVarName (OR.Array n r) -> Ast n r

  -- For VectorLike and Tensor class:
  AstIndex :: Ast (1 + n) r -> AstInt r -> Ast n r
  AstIndexN :: forall m n r. KnownNat m
            => Ast (1 + m + n) r -> AstPath r -> Ast n r
    -- emerges from vectorizing AstIndex;
    -- first ix is for outermost dimension; @1 + m@ is the length of the list;
    -- empty list means identity
  AstSum :: Ast (1 + n) r -> Ast n r
  AstFromList :: [Ast n r] -> Ast (1 + n) r
  AstFromVector :: Data.Vector.Vector (Ast n r) -> Ast (1 + n) r
  AstKonst :: Int -> Ast n r -> Ast (1 + n) r
  AstAppend :: KnownNat n
            => Ast (1 + n) r -> Ast (1 + n) r -> Ast (1 + n) r
  AstSlice :: Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
  AstReverse :: KnownNat n
             => Ast n r -> Ast n r
  AstTranspose :: Ast n r -> Ast n r
  AstTransposeGeneral :: AstPermutation -> Ast n r -> Ast n r
    -- emerges from vectorizing AstTranspose
  AstFlatten :: KnownNat n
             => Ast n r -> Ast 1 r
  AstReshape :: KnownNat n
             => AstShape r -> Ast n r -> Ast m r
    -- emerges from vectorizing AstFlatten
  AstBuildPair :: Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
  AstGatherPair :: KnownNat m
                => Int -> (AstVarName Int, AstPath r) -> Ast (m + n) r
                -> Ast (1 + n) r
    -- emerges from vectorizing AstIndexN applied to term with no build variable

  -- If we give the user access to tensors, not just vectors, these
  -- operations will be necessary.
  -- This is treated as syntactic sugar for now, but these have
  -- much more efficient non-sugar implementations
  -- (and possibly more efficient vectorizations).
  AstSum0 :: KnownNat n
          => Ast n r -> Ast 0 r
  AstDot0 :: KnownNat n
          => Ast n r -> Ast n r -> Ast 0 r
  AstFromList0N :: AstShape r -> [Ast 0 r] -> Ast n r
  AstFromVector0N :: AstShape r -> Data.Vector.Vector (Ast 0 r) -> Ast n r
  AstKonst0N :: AstShape r -> Ast 0 r -> Ast (1 + n) r
  AstBuildPair0N :: AstShape r -> ([AstVarName Int], Ast 0 r) -> Ast n r

  -- For MonoFunctor class, which is needed for a particularly
  -- fast implementation of relu and offers fast, primal-part only, mapping.
  -- TODO: this is really only needed in AstPrimalPart, but making
  -- AstPrimalPart data instead of a newtype would complicate a lot of code.
  AstOMap :: (AstVarName (OR.Array 0 r), Ast 0 r) -> Ast n r -> Ast n r
deriving instance (Show r, Numeric r) => Show (Ast n r)

newtype AstPrimalPart1 n r = AstPrimalPart1 (Ast n r)
 deriving Show

newtype AstVarName t = AstVarName Int
 deriving (Show, Eq)

data AstVar a =
    AstVarR a
  | AstVarI Int
 deriving Show

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

  AstMinIndex :: Ast 1 r -> AstInt r
  AstMaxIndex :: Ast 1 r -> AstInt r
deriving instance (Show r, Numeric r) => Show (AstInt r)

data AstBool :: Type -> Type where
  AstBoolOp :: OpCodeBool -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: OpCodeRel -> [Ast 0 r] -> AstBool r
  AstRelInt :: OpCodeRel -> [AstInt r] -> AstBool r
 deriving Show

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
  | QuotIntOp | RemIntOp | DivIntOp | ModIntOp
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
  _ == _ = error "Ast: can't evaluate terms for Eq"

instance Ord (OR.Array n r) => Ord (Ast n r) where
  max u v = AstOp MaxOp [u, v]
  min u v = AstOp MinOp [u, v]
  -- Unfortunately, the others can't be made to return @AstBool@.
  _ <= _ = error "Ast: can't evaluate terms for Ord"

instance Num (OR.Array n r) => Num (Ast n r) where
  u + v = AstOp PlusOp [u, v]
  u - v = AstOp MinusOp [u, v]
  u * v = AstOp TimesOp [u, v]
  negate u = AstOp NegateOp [u]
  abs v = AstOp AbsOp [v]
  signum v = AstOp SignumOp [v]
  fromInteger = AstConst . fromInteger

instance Real (OR.Array n r) => Real (Ast n r) where
  toRational = undefined  -- TODO?

instance Fractional (OR.Array n r) => Fractional (Ast n r) where
  u / v = AstOp DivideOp  [u, v]
  recip v = AstOp RecipOp [v]
  fromRational = AstConst . fromRational

instance Floating (OR.Array n r) => Floating (Ast n r) where
  pi = AstConst pi
  exp u = AstOp ExpOp [u]
  log u = AstOp LogOp [u]
  sqrt u = AstOp SqrtOp [u]
  u ** v = AstOp PowerOp [u, v]
  logBase u v = AstOp LogBaseOp [u, v]
  sin u = AstOp SinOp [u]
  cos u = AstOp CosOp [u]
  tan u = AstOp TanOp [u]
  asin u = AstOp AsinOp [u]
  acos u = AstOp AcosOp [u]
  atan u = AstOp AtanOp [u]
  sinh u = AstOp SinhOp [u]
  cosh u = AstOp CoshOp [u]
  tanh u = AstOp TanhOp [u]
  asinh u = AstOp AsinhOp [u]
  acosh u = AstOp AcoshOp [u]
  atanh u = AstOp AtanhOp [u]

instance RealFrac (OR.Array n r) => RealFrac (Ast n r) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance RealFloat (OR.Array n r) => RealFloat (Ast n r) where
  atan2 u v = AstOp Atan2Op [u, v]
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

instance Eq (AstPrimalPart1 n r) where
  _ == _ = error "AstPrimalPart1: can't evaluate terms for Eq"

instance Ord r => Ord (AstPrimalPart1 n r) where
  max (AstPrimalPart1 u) (AstPrimalPart1 v) =
    AstPrimalPart1 (AstOp MaxOp [u, v])
  min (AstPrimalPart1 u) (AstPrimalPart1 v) =
    AstPrimalPart1 (AstOp MinOp [u, v])
  _ <= _ = error "AstPrimalPart1: can't evaluate terms for Ord"

deriving instance Num (Ast n r) => Num (AstPrimalPart1 n r)
deriving instance (Real (Ast n r), Ord r) => Real (AstPrimalPart1 n r)
deriving instance Fractional (Ast n r) => Fractional (AstPrimalPart1 n r)
-- TODO: etc.

type instance Element (AstPrimalPart1 n r) = AstPrimalPart1 0 r


instance Eq (AstInt r) where
  _ == _ = error "AstInt: can't evaluate terms for Eq"

instance Ord (AstInt r) where
  max u v = AstIntOp MaxIntOp [u, v]
  min u v = AstIntOp MinIntOp [u, v]
  _ <= _ = error "AstInt: can't evaluate terms for Ord"

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

-- Warning: this class lacks toInteger, which also makes it impossible
-- to include AstInt in Ast via fromIntegral, hence AstConstInt.
instance Integral (AstInt r) where
  quot u v = AstIntOp QuotIntOp [u, v]
  rem u v = AstIntOp RemIntOp [u, v]
  div u v = AstIntOp DivIntOp [u, v]
  mod u v = AstIntOp ModIntOp [u, v]
  quotRem u v = (AstIntOp QuotIntOp [u, v], AstIntOp RemIntOp [u, v])
  divMod u v = (AstIntOp DivIntOp [u, v], AstIntOp ModIntOp [u, v])
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

astOmap :: (Ast 0 r -> Ast 0 r) -> Ast n r -> Ast n r
{-# NOINLINE astOmap #-}
astOmap f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap (freshAstVar, f (AstVar [] freshAstVar)) e

instance MonoFunctor (AstPrimalPart1 n r) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart1 z = f (AstPrimalPart1 y)
              in z
    in AstPrimalPart1 (astOmap g x)

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: (Show r, Numeric r) => Ast n r -> AstShape r
shapeAst v1 = case v1 of
  AstOp _opCode args -> case args of
    [] -> error "shapeAst: AstOp with no arguments"
    t : _ -> shapeAst t
  AstCond _b a1 _a2 -> shapeAst a1
  AstConstInt _i -> []
  AstConst a -> OR.shapeL a
  AstConstant (AstPrimalPart1 a) -> shapeAst a
  AstScale (AstPrimalPart1 r) _d -> shapeAst r
  AstVar sh _var -> sh
  AstIndex v _i -> tail $ shapeAst v  -- types ensure this @tail@ is total
  AstIndexN v is ->
    let sh = shapeAst v
    in assert (length sh >= length is `blame` v1)
       $ drop (length is) sh
  AstSum v -> tail $ shapeAst v
  AstFromList l -> case l of
    [] -> error "shapeAst: AstFromList with no arguments"
    t : _ -> length l : shapeAst t
  AstFromVector l -> case V.toList l of
    [] -> error "shapeAst: AstFromVector with no arguments"
    t : _ -> V.length l : shapeAst t
  AstKonst n v -> n : shapeAst v
  AstAppend x y -> case shapeAst x of
    [] -> error "shapeAst: AstAppend applied to scalars"
    xi : xsh -> case shapeAst y of
      [] -> error "shapeAst: AstAppend applied to scalars"
      yi : _ -> xi + yi : xsh
  AstSlice _n k v -> k : tail (shapeAst v)
  AstReverse v -> shapeAst v
  AstTranspose v -> case shapeAst v of
    i : k : sh -> k : i : sh
    sh -> sh  -- the operation is an identity if rank too small
  AstTransposeGeneral perm v ->
    let permutePrefix :: AstPermutation -> AstShape r -> AstShape r
        permutePrefix p l = V.toList $ VS.fromList l V.// zip p l
        sh = shapeAst v
    in if length sh < length perm
       then sh  -- the operation is an identity if rank too small
       else permutePrefix perm sh
  AstFlatten v -> [product $ shapeAst v]
  AstReshape sh _v -> sh
  AstBuildPair n (_var, v) -> n : shapeAst v
  AstGatherPair n (_var, is) v ->
    let sh = shapeAst v
    in assert (length sh >= length is `blame` v1)
       $ n : drop (length is) sh
  AstSum0 _v -> []
  AstDot0 _x _y -> []
  AstFromList0N sh _l -> sh
  AstFromVector0N sh _l -> sh
  AstKonst0N sh _r -> sh
  AstBuildPair0N sh (_vars, _r) -> sh
  AstOMap (_var, _r) e -> shapeAst e

lengthAst :: (Show r, Numeric r) => Ast (1 + n) r -> Int
lengthAst v1 = case shapeAst v1 of
  [] -> error "lengthAst: impossible rank 0 found"
  n : _ -> n

substituteAst :: (Show r, Numeric r)
              => AstInt r -> AstVarName Int -> Ast n r -> Ast n r
substituteAst i var v1 = case v1 of
  AstOp opCode args -> AstOp opCode $ map (substituteAst i var) args
  AstCond b a1 a2 -> AstCond (substituteAstBool i var b)
                             (substituteAst i var a1) (substituteAst i var a2)
  AstConstInt i2 -> AstConstInt $ substituteAstInt i var i2
  AstConst _a -> v1
  AstConstant (AstPrimalPart1 a) ->
    AstConstant (AstPrimalPart1 $ substituteAst i var a)
  AstScale (AstPrimalPart1 r) d ->
    AstScale (AstPrimalPart1 $ substituteAst i var r) (substituteAst i var d)
  AstVar _sh _var -> v1
  AstIndex v i2 -> AstIndex (substituteAst i var v) (substituteAstInt i var i2)
  AstIndexN v is ->
    AstIndexN (substituteAst i var v) (map (substituteAstInt i var) is)
  AstSum v -> AstSum (substituteAst i var v)
  AstFromList l -> AstFromList $ map (substituteAst i var) l
  AstFromVector l -> AstFromVector $ V.map (substituteAst i var) l
  AstKonst n v -> AstKonst n (substituteAst i var v)
  AstAppend x y -> AstAppend (substituteAst i var x) (substituteAst i var y)
  AstSlice n k v -> AstSlice n k (substituteAst i var v)
  AstReverse v -> AstReverse (substituteAst i var v)
  AstTranspose v -> AstTranspose (substituteAst i var v)
  AstTransposeGeneral perm v -> AstTransposeGeneral perm (substituteAst i var v)
  AstFlatten v -> AstFlatten (substituteAst i var v)
  AstReshape sh v -> AstReshape sh (substituteAst i var v)
  AstBuildPair n (var2, v) ->
    AstBuildPair n (var2, substituteAst i var v)
  AstGatherPair n (var2, is) v ->
    AstGatherPair n (var2, map (substituteAstInt i var) is)
                  (substituteAst i var v)
  AstSum0 v -> AstSum0 (substituteAst i var v)
  AstDot0 x y -> AstDot0 (substituteAst i var x) (substituteAst i var y)
  AstFromList0N sh l -> AstFromList0N sh $ map (substituteAst i var) l
  AstFromVector0N sh l -> AstFromVector0N sh $ V.map (substituteAst i var) l
  AstKonst0N sh r -> AstKonst0N sh (substituteAst i var r)
  AstBuildPair0N sh (vars, r) -> AstBuildPair0N sh (vars, substituteAst i var r)
  AstOMap (var2, r) e ->
    AstOMap (var2, substituteAst i var r) (substituteAst i var e)

substituteAstInt :: (Show r, Numeric r)
                 => AstInt r -> AstVarName Int -> AstInt r -> AstInt r
substituteAstInt i var i2 = case i2 of
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt $ map (substituteAstInt i var) args
  AstIntCond b a1 a2 ->
    AstIntCond (substituteAstBool i var b)
               (substituteAstInt i var a1) (substituteAstInt i var a2)
  AstIntConst _a -> i2
  AstIntVar var2 -> if var == var2 then i else i2
  AstMinIndex v -> AstMinIndex (substituteAst i var v)
  AstMaxIndex v -> AstMaxIndex (substituteAst i var v)

substituteAstBool :: (Show r, Numeric r)
                  => AstInt r -> AstVarName Int -> AstBool r -> AstBool r
substituteAstBool i var b1 = case b1 of
  AstBoolOp opCodeBool args ->
    AstBoolOp opCodeBool $ map (substituteAstBool i var) args
  AstBoolConst _a -> b1
  AstRel opCodeRel args ->
    AstRel opCodeRel $ map (substituteAst i var) args
  AstRelInt opCodeRel args ->
    AstRelInt opCodeRel $ map (substituteAstInt i var) args

-- This is toIx generalized to AstInt.
toIxAst :: [Int] -> AstInt r -> AstPath r
toIxAst [] _ = []
toIxAst (n : ns) i = q : toIxAst ns r where (q, r) = quotRem i (AstIntConst n)
