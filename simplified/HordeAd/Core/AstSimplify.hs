{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving,
             StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Term-simplifying combinators corresponding to the Ast constructors.
-- They simplify only on the basis of inspecting the roots of their
-- argument term trees. If the arguments get modified as a result,
-- the modified forms are again inspected and may be simplified.
-- However, no unbounded depth inspection nor simplification of terms
-- takes place. This limited simplification is enough to uncover redexes
-- for the vectorization rules to fire and to undo some of the complication
-- introduced by vectorization. The intention is to leave as much
-- of the original terms provided by the user as possible while making
-- sure everything introduced by vectorization is maximally simplified.
--
-- The combinator can also be used to simplify a whole term, bottom-up.
module HordeAd.Core.AstSimplify
  ( isIdentityPerm, permCycle, permSwapSplit
  , unsafeGetFreshAstVar, funToAstR, funToAstI
  , astReshape
  , astIndexZ, astSum, astFromList, astFromVector, astKonst
  , astAppend, astSlice, astReverse, astTranspose, astFlatten
  , astGather1, astGatherN
  , astIntCond
  , simplifyAst
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (replicateM)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.List (elemIndex)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- * Permutation operations

isIdentityPerm :: Permutation -> Bool
isIdentityPerm = and . zipWith (==) [0 ..]

permCycle :: Int -> Permutation
permCycle 0 = []
permCycle 1 = []
permCycle n = [k `mod` n | k <- [1 .. n]]

-- | Produces a (possibly trival) two-element swap involving the first element
-- and the permutation that needs to be applied first, before the swap,
-- to produce the same result as the original permutation.
-- Addtionally, the latter permutation is represented as operating
-- on all but the first element of a list (the first element is fixed)
-- and so is one element shorter than the original permutation.
permSwapSplit :: Permutation -> Maybe (Int, Permutation)
permSwapSplit = \case
  [] -> Nothing
  perm | isIdentityPerm perm -> Nothing
  i : rest -> case elemIndex 0 rest of
    Nothing -> assert (i == 0) $ Just (0, map (\k -> k - 1) rest)
    Just j -> let f k = if k == 0 then i - 1 else k - 1
              in Just (j, map f rest)


-- * Generating variables names

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 1)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

funToAstR :: ShapeInt n -> (Ast n r -> Ast m r)
          -> (AstVarName (OR.Array n r), Ast m r)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return (freshAstVar, f (AstVar sh freshAstVar))

funToAstI :: (AstInt r -> Ast m r) -> (AstVarName Int, Ast m r)
{-# NOINLINE funToAstI #-}
funToAstI f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return (freshAstVar, f (AstIntVar freshAstVar))


-- * Combinators that simplify but introduce new variable names

-- TODO: decide whether to use always and perhaps remove AstFlatten
-- or not to use for Flatten, but fuse with Flatten, etc.
astReshape :: forall p m r. (KnownNat p, KnownNat m, Show r, Numeric r)
           => ShapeInt m -> Ast p r -> Ast m r
{-# NOINLINE astReshape #-}
astReshape shOut v = unsafePerformIO $ do
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


-- * The simplifying combinators

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

astSum :: Ast (1 + n) r -> Ast n r
astSum = AstSum

astFromList :: KnownNat n
            => [Ast n r] -> Ast (1 + n) r
astFromList = AstFromList

astFromVector :: KnownNat n
              => Data.Vector.Vector (Ast n r) -> Ast (1 + n) r
astFromVector = AstFromVector

astKonst :: KnownNat n => Int -> Ast n r -> Ast (1 + n) r
astKonst k = \case
  AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astKonst k v
  AstReshape sh v ->
    AstReshape (k :$ sh) $ astKonst k v
  v -> AstKonst k v

astAppend :: KnownNat n
          => Ast (1 + n) r -> Ast (1 + n) r -> Ast (1 + n) r
astAppend = AstAppend

astSlice :: KnownNat n
         => Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
astSlice = AstSlice

astReverse :: KnownNat n
           => Ast (1 + n) r -> Ast (1 + n) r
astReverse = AstReverse

astTranspose :: forall n r. KnownNat n
             => Permutation -> Ast n r -> Ast n r
astTranspose perm t | isIdentityPerm perm = t
astTranspose perm1 (AstTranspose perm2 t) =
  let perm2Matched =
        perm2 ++ take (length perm1 - length perm2) (drop (length perm2) [0 ..])
      perm = permutePrefixList perm1 perm2Matched
  in astTranspose perm t
astTranspose perm u = AstTranspose perm u

astFlatten :: KnownNat n
           => Ast n r -> Ast 1 r
astFlatten = AstFlatten

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
         in case gatherSimplify k var w iN of
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
      -- a generalization of gatherSimplify needed to simplify more
      -- or we could run astGather1 repeatedly, but even then we can't
      -- get into fromList, which may simplify or complicate a term,
      -- and sometimes is not possible without leaving a small gather outside
  v3 -> astGatherN (var ::: vars, ZI) v3 sh
astGatherN _ _ _ =
  error "astGatherN: AstGatherN: impossible pattern needlessly required"

-- TODO: we probably need to simplify iN to some normal form, but possibly
-- this would be even better to do and take advantage of earlier,
-- perhaps even avoiding pushing all the other indexing down
-- | The application @gatherSimplify k var v iN@ vectorizes and simplifies
-- the term @AstBuild1 k (var, AstIndexZ v [iN])@, where it's known that
-- @var@ does not occur in @v@ but occurs in @iN@. This is done by pattern
-- matching on @iN@ as opposed to on @v@.
gatherSimplify
  :: (KnownNat n, Show r, Numeric r)
  => Int -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Maybe (Ast (1 + n) r)
gatherSimplify k var v0 iN =
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

-- This is to be used only in gatherSimplify. The normal slice
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

astIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
astIntCond = AstIntCond

astMinIndex1 :: Ast 1 r -> AstInt r
astMinIndex1 = AstMinIndex1

astMaxIndex1 :: Ast 1 r -> AstInt r
astMaxIndex1 = AstMaxIndex1


-- * The simplifying bottom-up pass

-- The constant, primal-part only terms are not vectorized, never
-- introduced by vectorization (let's keep checking it's true)
-- and so don't need to be simplified.
simplifyAstPrimal :: AstPrimalPart n r -> AstPrimalPart n r
simplifyAstPrimal (AstPrimalPart t) = AstPrimalPart t

simplifyAst
  :: (KnownNat n, Show r, Numeric r)
  => Ast n r -> Ast n r
simplifyAst t = case t of
  AstVar{} -> t
  AstOp opCode args -> AstOp opCode (map simplifyAst args)
    -- We do not simplify, e.g., addition or multiplication by zero.
    -- There are too many cases and values are often unknown.
  AstConst{} -> t
  AstConstant a -> AstConstant $ simplifyAstPrimal a
  AstConstInt i -> AstConstInt $ simplifyAstInt i
  AstIndexZ v ix -> astIndexZ (simplifyAst v) (fmap (simplifyAstInt) ix)
  AstSum v -> astSum (simplifyAst v)
  AstFromList l -> astFromList (map (simplifyAst) l)
  AstFromVector l -> astFromVector (V.map (simplifyAst) l)
  AstKonst k v -> astKonst k (simplifyAst v)
  AstAppend x y -> astAppend (simplifyAst x) (simplifyAst y)
  AstSlice i k v -> astSlice i k (simplifyAst v)
  AstReverse v -> astReverse (simplifyAst v)
  AstTranspose perm v -> astTranspose perm $ simplifyAst v
  AstFlatten v -> astFlatten $ simplifyAst v
  AstReshape sh v -> astReshape sh (simplifyAst v)
  AstBuild1{} -> t  -- should never appear outside test runs
  AstGather1 (var, ix) v k ->
    astGather1 (var, fmap (simplifyAstInt) ix) (simplifyAst v) k
  AstGatherN (vars, ix) v sh ->
    astGatherN (vars, fmap (simplifyAstInt) ix) (simplifyAst v) sh

-- Integer terms need to be simplified, because they are sometimes
-- created by vectorization and can be a deciding factor in whether
-- dual terms can be simplified in turn.
simplifyAstInt :: (Show r, Numeric r)
               => AstInt r -> AstInt r
simplifyAstInt t = case t of
  AstIntVar{} -> t
  AstIntOp opCodeInt args -> AstIntOp opCodeInt (map simplifyAstInt args)
    -- We do not simplify, e.g., addition or multiplication by zero.
    -- Arriving at some normal form is worth considering for the sake
    -- of gatherSimplify.
  AstIntConst{} -> t
  AstIntFloor v -> AstIntFloor $ simplifyAst v
    -- Equality of floats is suspect, so no attempt to simplify.
  AstIntCond b a1 a2 -> astIntCond (simplifyAstBool b)
                                   (simplifyAstInt a1)
                                   (simplifyAstInt a2)
  AstMinIndex1 v -> astMinIndex1 $ simplifyAst v
  AstMaxIndex1 v -> astMaxIndex1 $ simplifyAst v

simplifyAstBool :: (Show r, Numeric r)
                => AstBool r -> AstBool r
simplifyAstBool t = case t of
  AstBoolOp opCodeBool args -> AstBoolOp opCodeBool (map simplifyAstBool args)
    -- We do not simplify, e.g., conjunction with False. Worth considering.
  AstBoolConst{} -> t
  AstRel{} -> t
    -- these are primal part expressions, so never vectorized but potentially
    -- large, so we ignore them, even if rarely they could contribute
    -- to simplifying the dual expressions affected by vectorization
    -- in which they are nested; if we ever notice such large expressions
    -- that are actually *introduced* into AstRel by vectorization,
    -- we are going to need to start simplifyign them as well
    -- even just to try to reduce their size
  AstRelInt opCodeRel args -> AstRelInt opCodeRel (map simplifyAstInt args)
    -- We do not simplify, e.g., equality of syntactically equal terms.
    -- There are too many cases and values are often unknown.
