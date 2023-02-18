{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving,
             StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, but can be used
-- for arbitrary code transformations at the cost of limiting
-- expressiveness of transformed fragments to what AST captures.
module HordeAd.Core.Ast
  ( AstIndex, AstVarList
  , AstVarName(..)
  , Ast(..), AstPrimalPart(..), AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  , unsafeGetFreshAstVar, reshapeAsGather
  , shapeAst, lengthAst
  , intVarInAst, intVarInAstInt, intVarInAstBool
  , substituteAst, substituteAstInt, substituteAstBool
  , astCond, astIndexZ, astKonst, astTr, astTranspose, permCycle
  , astGather1, astGatherN
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (replicateM)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- * Ast definitions

type AstIndex n r = Index n (AstInt r)

type AstVarList n = SizedList n (AstVarName Int)

-- We use here @ShapeInt@ for simplicity. @Shape n (AstInt r)@ gives
-- more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents statically known shapes.
-- However, if we switched to @Data.Array.Shaped@ and moved most of the shapes
-- to the type level, we'd recover some of the expressiveness, while retaining
-- statically known (type-parameterized) shapes.

-- TODO: consider sharing Ast expressions, both within the primal part
-- and between primal and dual
-- | AST for a tensor of rank n and elements r that is meant
-- to be differentiated.
data Ast :: Nat -> Type -> Type where
  -- To permit defining objective functions in Ast, not just constants:
  AstVar :: ShapeInt n -> AstVarName (OR.Array n r) -> Ast n r

  -- For the numeric classes:
  AstOp :: OpCode -> [Ast n r] -> Ast n r

  -- For HasPrimal class:
  AstConst :: OR.Array n r -> Ast n r
  AstConstant :: AstPrimalPart n r -> Ast n r

  -- For Tensor class:
  AstConstInt :: AstInt r -> Ast 0 r
    -- needed, because toInteger and so fromIntegral is not defined for Ast
  AstIndexZ :: forall m n r. KnownNat m
            => Ast (m + n) r -> AstIndex m r -> Ast n r
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0;
    -- however, vectorization is permitted to change the value
  AstSum :: Ast (1 + n) r -> Ast n r
  AstFromList :: [Ast n r] -> Ast (1 + n) r
  AstFromVector :: Data.Vector.Vector (Ast n r) -> Ast (1 + n) r
  AstKonst :: Int -> Ast n r -> Ast (1 + n) r
  AstAppend :: KnownNat n
            => Ast (1 + n) r -> Ast (1 + n) r -> Ast (1 + n) r
  AstSlice :: Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
  AstReverse :: KnownNat n
             => Ast (1 + n) r -> Ast (1 + n) r
  AstTranspose :: Permutation -> Ast n r -> Ast n r
    -- emerges from vectorizing AstTr
  AstFlatten :: KnownNat n
             => Ast n r -> Ast 1 r
  AstReshape :: KnownNat n
             => ShapeInt m -> Ast n r -> Ast m r
    -- emerges from vectorizing AstFlatten
  AstBuild1 :: Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
    -- indicates a failure in vectorization, but may be recoverable later on
  AstGather1 :: forall p n r. KnownNat p
             => (AstVarName Int, AstIndex p r) -> Ast (p + n) r
             -> Int -> Ast (1 + n) r
    -- emerges from vectorizing AstIndexZ applied to a term with no build
    -- variable; out of bounds indexing is permitted
  AstGatherN :: forall m p n r. (KnownNat m, KnownNat p, KnownNat n)
             => (AstVarList m, AstIndex p r) -> Ast (p + n) r
             -> ShapeInt (m + n) -> Ast (m + n) r
    -- emerges from vectorizing AstGather1; out of bounds indexing is permitted

  -- Spurious, but can be re-enabled at any time:
--  AstBuildN :: forall m n r.
--               ShapeInt (m + n) -> (AstVarList m, Ast n r) -> Ast (m + n) r
    -- not needed for anythihg, but an extra pass may join nested AstBuild1
    -- into these for better performance on some hardware

deriving instance (Show r, Numeric r) => Show (Ast n r)

-- Combinators are provided instead of some constructors in order
-- to lower the number of constructors and/or simplify terms.

astCond :: AstBool r -> Ast n r -> Ast n r -> Ast n r
astCond b v w = AstIndexZ (AstFromList [v, w])
                          (singletonIndex $ AstIntCond b 0 1)

astIndexZ :: forall m n r. (KnownNat m, Show r, Numeric r)
          => Ast (m + n) r -> AstIndex m r -> Ast n r
astIndexZ v0 ZI = v0
astIndexZ v0 ix@(i1 :. (rest1 :: AstIndex m1 r)) = case v0 of
  AstKonst _k v -> astIndexZ v rest1
  AstTranspose perm v | valueOf @m >= length perm ->
    astIndexZ v (permutePrefixIndex perm ix)
  AstGather1 (var2, ix2) v _n2 ->
    let ix3 = fmap (substituteAstInt i1 var2) ix2
    in astIndexZ v (appendIndex ix3 rest1)
  AstGatherN (Z, ix2) v _sh -> astIndexZ v (appendIndex ix ix2)
  AstGatherN (var2 ::: vars, ix2) v (_ :$ sh') ->
    let ix3 = fmap (substituteAstInt i1 var2) ix2
        w :: Ast (m1 + n) r
        w = unsafeCoerce $ astGatherN (vars, ix3) v sh'
    in astIndexZ @m1 @n w rest1
  _ -> AstIndexZ v0 ix
    -- a lot more can be added, but how not to duplicate build1VIx?

astKonst :: KnownNat n => Int -> Ast n r -> Ast (1 + n) r
astKonst k = \case
  AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astKonst k v
  AstReshape sh v ->
    AstReshape (k :$ sh) $ astKonst k v
  v -> AstKonst k v

astTr :: forall n r. KnownNat n => Ast (2 + n) r -> Ast (2 + n) r
astTr v = astTranspose [1, 0] v

astTranspose :: forall n r. KnownNat n
             => Permutation -> Ast n r -> Ast n r
astTranspose perm t | isIdentityPerm perm = t
astTranspose perm1 (AstTranspose perm2 t) =
  let perm2Matched =
        perm2 ++ take (length perm1 - length perm2) (drop (length perm2) [0 ..])
      perm = permutePrefixList perm1 perm2Matched
  in astTranspose perm t
astTranspose perm u = AstTranspose perm u

isIdentityPerm :: Permutation -> Bool
isIdentityPerm = and . zipWith (==) [0 ..]

permCycle :: Int -> Permutation
permCycle 0 = []
permCycle 1 = []
permCycle n = [k `mod` n | k <- [1 .. n]]

-- Assumption: var does not occur in v0.
astGather1 :: forall p n r. (KnownNat p, KnownNat n, Show r, Numeric r)
           => (AstVarName Int, AstIndex p r) -> Ast (p + n) r
           -> Int -> Ast (1 + n) r
astGather1 (var, ix) v0 k = case astIndexZ v0 ix of
  AstIndexZ v2 ix2@(iN :. restN) ->
    if | any (intVarInAstInt var) restN -> AstGather1 (var, ix2) v2 k
       | intVarInAstInt var iN ->
         let w :: Ast (1 + n) r
             w = AstIndexZ v2 restN
         in case build1VSimplify k var w iN of
              Just u -> u  -- an extremely simple form found
              Nothing -> AstGather1 (var, ix2) v2 k
                -- we didn't really need it anyway
       | otherwise -> astKonst k (AstIndexZ v2 ix2)
  v3 -> astKonst k v3

astGatherN :: forall m p n r.
              (KnownNat m, KnownNat p, KnownNat n, Show r, Numeric r)
           => (AstVarList m, AstIndex p r) -> Ast (p + n) r
           -> ShapeInt (m + n) -> Ast (m + n) r
astGatherN (Z, ix) v0 _sh = astIndexZ v0 ix
astGatherN (_ ::: vars, ZI) v0 (k :$ sh') =
  astKonst k (astGatherN (vars, ZI) v0 sh')  -- a shortcut
astGatherN (var ::: vars, ix@(_ :. _)) v0
           sh@(k :$ sh') = case astIndexZ @p @n v0 ix of
  AstIndexZ v2 ix2 ->
    if any (intVarInAstInt var) ix2 then AstGatherN (var ::: vars, ix2) v2 sh
    else astKonst k (astGatherN (vars, ix2) v2 sh')
      -- a generalization of build1VSimplify needed to simplify more
      -- or we could run astGather1 repeatedly, but even then we can't
      -- get into fromList, which may simplify or complicate a term,
      -- and sometimes is not possible without leaving a small gather outside
  v3 -> astGatherN (var ::: vars, ZI) v3 sh
astGatherN _ _ _ =
  error "astGatherN: AstGatherN: impossible pattern needlessly required"

-- TODO: we probably need to simplify iN to some normal form, but possibly
-- this would be even better to do and take advantage of earlier,
-- perhaps even avoiding pushing all the other indexing down
-- | The application @build1VSimplify k var v iN@ vectorizes and simplifies
-- the term @AstBuild1 k (var, AstIndexZ v [iN])@, where it's known that
-- @var@ does not occur in @v@ but occurs in @iN@. This is done by pattern
-- matching on @iN@ as opposed to on @v@.
build1VSimplify
  :: (KnownNat n, Show r, Numeric r)
  => Int -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Maybe (Ast (1 + n) r)
build1VSimplify k var v0 iN =
  case iN of
    AstIntVar var2 | var2 == var ->
      Just $ astSliceLax 0 k v0
    AstIntOp PlusIntOp [AstIntVar var2, AstIntConst i2]
      | var2 == var ->
        Just $ astSliceLax i2 k v0
    AstIntOp PlusIntOp [AstIntConst i2, AstIntVar var2]
      | var2 == var ->
        Just $ astSliceLax i2 k v0
    _ -> Nothing
      -- TODO: many more cases; not sure how systematic it can be;
      -- more cases arise if shapes can contain Ast variables;
      -- @Data.Array.Shaped@ doesn't help in these extra cases;
      -- however, AstGather* covers all this, at the cost of (relatively
      -- simple) expressions on tape

-- This is to be used only in build1VSimplify. The normal slice
-- still crashes with illegal parameters.
-- This function is so complex in order to guarantee that even though
-- vectorization changes tensor values, it doesn't change their shapes.
astSliceLax :: (KnownNat n, Show r, Numeric r)
            => Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
astSliceLax i k v =
  let len = lengthAst v
      kMax = len - i
      sh = shapeToList $ shapeAst v
      v2 = AstConst $ OR.constant (k - kMax : tail sh) 0
      !_A = assert (i < len
                    `blame` "astSlice: offset not smaller than tensor length"
                    `swith` (i, len)) ()
  in if | i == 0 && k == len -> v
        | k <= kMax -> AstSlice i k v
        | i == 0 -> AstAppend v v2
        | otherwise -> AstAppend (AstSlice i kMax v) v2

newtype AstPrimalPart n r = AstPrimalPart {unAstPrimalPart :: Ast n r}
 deriving Show

newtype AstVarName t = AstVarName Int
 deriving Eq

-- An unlawful instance to prevent spam when tracing and debugging.
instance Show (AstVarName t) where
  show (AstVarName n) = "Var" ++ show n

-- In AstInt and AstBool, the Ast terms are morally AstPrimalPart,
-- since their derivative part is not used.
-- TODO: introduce AstPrimalPart explicitly when convenient, e.g.,
-- as soon as AstPrimalPart gets more constructors.

-- The argument is the underlying scalar.
data AstInt :: Type -> Type where
  AstIntVar :: AstVarName Int -> AstInt r
  AstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntFloor :: Ast 0 r -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
  AstMinIndex :: Ast 1 r -> AstInt r
  AstMaxIndex :: Ast 1 r -> AstInt r
deriving instance (Show r, Numeric r) => Show (AstInt r)

data AstBool :: Type -> Type where
  AstBoolOp :: OpCodeBool -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: KnownNat n
         => OpCodeRel -> [Ast n r] -> AstBool r
  AstRelInt :: OpCodeRel -> [AstInt r] -> AstBool r
deriving instance (Show r, Numeric r) => Show (AstBool r)

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
    NotOp | AndOp | OrOp
 deriving Show

data OpCodeRel =
    EqOp | NeqOp
  | LeqOp| GeqOp | LsOp | GtOp
 deriving Show


-- * Generating variables

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 1)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

reshapeAsGather :: forall p m r. (KnownNat p, KnownNat m, Show r, Numeric r)
                => Ast p r -> ShapeInt m -> Ast m r
{-# NOINLINE reshapeAsGather #-}
reshapeAsGather v shOut = unsafePerformIO $ do
  varList <- replicateM (lengthShape shOut) unsafeGetFreshAstVar
  let vars :: AstVarList m
      vars = listToSized varList
      ix :: AstIndex m r
      ix = listToIndex $ map AstIntVar varList
      shIn = shapeAst v
      asts :: AstIndex p r
      asts = let i = toLinearIdx @m @0 (fmap AstIntConst shOut) ix
             in fromLinearIdx (fmap AstIntConst shIn) i
  return $! AstGatherN @m @p @0 (vars, asts) v shOut


-- * Unlawful instances of AST types; they are lawful modulo evaluation

type instance BooleanOf (AstInt r) = AstBool r

instance IfB (AstInt r) where
  ifB = AstIntCond

instance EqB (AstInt r) where
  v ==* u = AstRelInt EqOp [v, u]
  v /=* u = AstRelInt NeqOp [v, u]

instance OrdB (AstInt r) where
  v <* u = AstRelInt LsOp [v, u]
  v <=* u = AstRelInt LeqOp [v, u]
  v >* u = AstRelInt GtOp [v, u]
  v >=* u = AstRelInt GeqOp [v, u]

type instance BooleanOf (Ast n r) = AstBool r

instance IfB (Ast n r) where
  ifB = astCond

instance KnownNat n => EqB (Ast n r) where
  v ==* u = AstRel EqOp [v, u]
  v /=* u = AstRel NeqOp [v, u]

instance KnownNat n => OrdB (Ast n r) where
  v <* u = AstRel LsOp [v, u]
  v <=* u = AstRel LeqOp [v, u]
  v >* u = AstRel GtOp [v, u]
  v >=* u = AstRel GeqOp [v, u]

type instance BooleanOf (AstPrimalPart n r) = AstBool r

instance IfB (AstPrimalPart n r) where
  ifB b v w = AstPrimalPart $ astCond b (unAstPrimalPart v) (unAstPrimalPart w)

instance KnownNat n => EqB (AstPrimalPart n r) where
  v ==* u = AstRel EqOp [unAstPrimalPart v, unAstPrimalPart u]
  v /=* u = AstRel NeqOp [unAstPrimalPart v, unAstPrimalPart u]

instance KnownNat n => OrdB (AstPrimalPart n r) where
  v <* u = AstRel LsOp [unAstPrimalPart v, unAstPrimalPart u]
  v <=* u = AstRel LeqOp [unAstPrimalPart v, unAstPrimalPart u]
  v >* u = AstRel GtOp [unAstPrimalPart v, unAstPrimalPart u]
  v >=* u = AstRel GeqOp [unAstPrimalPart v, unAstPrimalPart u]

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
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

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
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance RealFloat (OR.Array n r) => RealFloat (Ast n r) where
  atan2 u v = AstOp Atan2Op [u, v]
  -- We can be selective here and omit the other methods,
  -- most of which don't even have a differentiable codomain.
  floatRadix = undefined
  floatDigits = undefined
  floatRange = undefined
  decodeFloat = undefined
  encodeFloat = undefined
  isNaN = undefined
  isInfinite = undefined
  isDenormalized = undefined
  isNegativeZero = undefined
  isIEEE = undefined

instance Eq (AstPrimalPart n r) where
  _ == _ = error "AstPrimalPart: can't evaluate terms for Eq"

instance Ord (Ast n r) => Ord (AstPrimalPart n r) where
  max (AstPrimalPart u) (AstPrimalPart v) =
    AstPrimalPart (AstOp MaxOp [u, v])
  min (AstPrimalPart u) (AstPrimalPart v) =
    AstPrimalPart (AstOp MinOp [u, v])
  _ <= _ = error "AstPrimalPart: can't evaluate terms for Ord"

deriving instance Num (Ast n r) => Num (AstPrimalPart n r)
deriving instance Real (Ast n r) => Real (AstPrimalPart n r)
deriving instance Fractional (Ast n r) => Fractional (AstPrimalPart n r)
deriving instance Floating (Ast n r) => Floating (AstPrimalPart n r)
deriving instance RealFrac (Ast n r) => RealFrac (AstPrimalPart n r)
deriving instance RealFloat (Ast n r) => RealFloat (AstPrimalPart n r)


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
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum (AstInt r) where
  toEnum = AstIntConst
  fromEnum = undefined  -- do we need to define out own Enum for this?

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

instance Boolean (AstBool r) where
  true = AstBoolConst True
  false = AstBoolConst False
  notB b = AstBoolOp NotOp [b]
  b &&* c = AstBoolOp AndOp [b, c]
  b ||* c = AstBoolOp OrOp [b, c]

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: forall n r. (KnownNat n, Show r, Numeric r)
         => Ast n r -> ShapeInt n
shapeAst v1 = case v1 of
  AstVar sh _var -> sh
  AstOp _opCode args -> case args of
    [] -> error "shapeAst: AstOp with no arguments"
    t : _ -> shapeAst t
  AstConst a -> listShapeToShape $ OR.shapeL a
  AstConstant (AstPrimalPart a) -> shapeAst a
  AstConstInt _i -> ZS
  AstIndexZ v (_is :: Index m (AstInt r)) -> dropShape @m (shapeAst v)
  AstSum v -> tailShape $ shapeAst v
  AstFromList l -> case l of
    [] -> error "shapeAst: AstFromList with no arguments"
    t : _ -> length l :$ shapeAst t
  AstFromVector l -> case V.toList l of
    [] -> error "shapeAst: AstFromVector with no arguments"
    t : _ -> V.length l :$ shapeAst t
  AstKonst s v -> s :$ shapeAst v
  AstAppend x y -> case shapeAst x of
    ZS -> error "shapeAst: impossible pattern needlessly required"
    xi :$ xsh -> case shapeAst y of
      ZS -> error "shapeAst: impossible pattern needlessly required"
      yi :$ _ -> xi + yi :$ xsh
  AstSlice _n k v -> k :$ tailShape (shapeAst v)
  AstReverse v -> shapeAst v
  AstTranspose perm v -> permutePrefixShape perm (shapeAst v)
  AstFlatten v -> flattenShape (shapeAst v)
  AstReshape sh _v -> sh
  AstBuild1 k (_var, v) -> k :$ shapeAst v
  AstGather1 (_var, _is :: Index p (AstInt r)) v k ->
    k :$ dropShape @p (shapeAst v)
  AstGatherN (_var, _is) _v sh -> sh

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, Show r, Numeric r) => Ast (1 + n) r -> Int
lengthAst v1 = case shapeAst v1 of
  ZS -> error "lengthAst: impossible pattern needlessly required"
  k :$ _ -> k

intVarInAst :: AstVarName Int -> Ast n r -> Bool
intVarInAst var = \case
  AstVar{} -> False  -- not an int variable
  AstOp _ l -> any (intVarInAst var) l
  AstConst{} -> False
  AstConstant (AstPrimalPart v) -> intVarInAst var v
  AstConstInt k -> intVarInAstInt var k
  AstIndexZ v is -> intVarInAst var v || any (intVarInAstInt var) is
  AstSum v -> intVarInAst var v
  AstFromList l -> any (intVarInAst var) l  -- down from rank 1 to 0
  AstFromVector vl -> any (intVarInAst var) $ V.toList vl
  AstKonst _ v -> intVarInAst var v
  AstAppend v u -> intVarInAst var v || intVarInAst var u
  AstSlice _ _ v -> intVarInAst var v
  AstReverse v -> intVarInAst var v
  AstTranspose _ v -> intVarInAst var v
  AstFlatten v -> intVarInAst var v
  AstReshape _ v -> intVarInAst var v
  AstBuild1 _ (_, v) -> intVarInAst var v
  AstGather1 (_, is) v _ -> any (intVarInAstInt var) is || intVarInAst var v
  AstGatherN (_, is) v _ -> any (intVarInAstInt var) is || intVarInAst var v

intVarInAstInt :: AstVarName Int -> AstInt r -> Bool
intVarInAstInt var = \case
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstIntOp _ l -> any (intVarInAstInt var) l
  AstIntConst{} -> False
  AstIntFloor v -> intVarInAst var v
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstMinIndex v -> intVarInAst var v
  AstMaxIndex v -> intVarInAst var v

intVarInAstBool :: AstVarName Int -> AstBool r -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> any (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (intVarInAst var) l
  AstRelInt _ l  -> any (intVarInAstInt var) l

substituteAst :: (Show r, Numeric r)
              => AstInt r -> AstVarName Int -> Ast n r -> Ast n r
substituteAst i var v1 = case v1 of
  AstVar _sh _var -> v1
  AstOp opCode args -> AstOp opCode $ map (substituteAst i var) args
  AstConst _a -> v1
  AstConstant (AstPrimalPart a) ->
    AstConstant (AstPrimalPart $ substituteAst i var a)
  AstConstInt i2 -> AstConstInt $ substituteAstInt i var i2
  AstIndexZ v is ->
    AstIndexZ (substituteAst i var v) (fmap (substituteAstInt i var) is)
  AstSum v -> AstSum (substituteAst i var v)
  AstFromList l -> AstFromList $ map (substituteAst i var) l
  AstFromVector l -> AstFromVector $ V.map (substituteAst i var) l
  AstKonst s v -> AstKonst s (substituteAst i var v)
  AstAppend x y -> AstAppend (substituteAst i var x) (substituteAst i var y)
  AstSlice k s v -> AstSlice k s (substituteAst i var v)
  AstReverse v -> AstReverse (substituteAst i var v)
  AstTranspose perm v -> AstTranspose perm (substituteAst i var v)
  AstFlatten v -> AstFlatten (substituteAst i var v)
  AstReshape sh v -> AstReshape sh (substituteAst i var v)
  AstBuild1 k (var2, v) ->
    AstBuild1 k (var2, substituteAst i var v)
  AstGather1 (var2, is) v k ->
    AstGather1 (var2, fmap (substituteAstInt i var) is)
               (substituteAst i var v) k
  AstGatherN (vars, is) v sh ->
    AstGatherN (vars, fmap (substituteAstInt i var) is)
               (substituteAst i var v) sh

substituteAstInt :: (Show r, Numeric r)
                 => AstInt r -> AstVarName Int -> AstInt r -> AstInt r
substituteAstInt i var i2 = case i2 of
  AstIntVar var2 -> if var == var2 then i else i2
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt $ map (substituteAstInt i var) args
  AstIntConst _a -> i2
  AstIntFloor v -> AstIntFloor $ substituteAst i var v
  AstIntCond b a1 a2 ->
    AstIntCond (substituteAstBool i var b)
               (substituteAstInt i var a1) (substituteAstInt i var a2)
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
