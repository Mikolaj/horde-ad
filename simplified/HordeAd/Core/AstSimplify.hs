{-# LANGUAGE DataKinds, GADTs #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
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
  , funToAstR, funToAstI, funToAstIndex
  , astIndexStep
  , astReshape, astTranspose
  , astIndexZ, astSum, astFromList, astFromVector, astKonst
  , astAppend, astSlice, astReverse, astGather1, astGatherN
  , astIntCond
  , simplifyAst
  , substituteAst, substituteAstInt, substituteAstBool
  , resetVarCOunter
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (replicateM)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.List (elemIndex)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  ( KnownNat
  , OrderingI (..)
  , SomeNat (..)
  , cmpNat
  , sameNat
  , someNatVal
  , type (+)
  , type (-)
  )
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

-- Only for tests.
resetVarCOunter :: IO ()
resetVarCOunter = writeIORefU unsafeAstVarCounter 1

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

funToAstR :: ShapeInt n -> (Ast n r -> Ast m r)
          -> (AstVarName (OR.Array n r), Ast m r)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return (freshAstVar, f (AstVar sh freshAstVar))

funToAstI :: (AstInt r -> t) -> (AstVarName Int, t)
{-# NOINLINE funToAstI #-}
funToAstI f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return (freshAstVar, f (AstIntVar freshAstVar))

funToAstIndex :: forall m p r. KnownNat m
              => (AstIndex m r -> AstIndex p r) -> (AstVarList m, AstIndex p r)
{-# NOINLINE funToAstIndex #-}
funToAstIndex f = unsafePerformIO $ do
  varList <- replicateM (valueOf @m) unsafeGetFreshAstVar
  return (listToSized varList, f (listToIndex $ map AstIntVar varList))


-- * Expressing operations as Gather; introduces new variable names

-- This generates big terms that don't simplify well,
-- so we keep the AstReshape form until simplification gets stuck.
astReshapeAsGather :: forall p m r. (KnownNat p, KnownNat m, Show r, Numeric r)
                   => ShapeInt m -> Ast p r -> Ast m r
{-# NOINLINE astReshapeAsGather #-}
astReshapeAsGather shOut v = unsafePerformIO $ do
  varList <- replicateM (lengthShape shOut) unsafeGetFreshAstVar
  let shIn = shapeAst v
      vars :: AstVarList m
      vars = listToSized varList
      ix :: AstIndex m r
      ix = listToIndex $ map AstIntVar varList
      asts :: AstIndex p r
      asts = let i = toLinearIdx @m @0 (fmap AstIntConst shOut) ix
             in fmap simplifyAstInt
                $ fromLinearIdx (fmap AstIntConst shIn) i
                  -- we generate these, so we simplify
  return $! astGatherN @m @0 shOut v (vars, asts)

-- We keep AstTranspose terms for as long as possible, because
-- they are small and fuse nicely in many cases. For some forms of indexing
-- and nesting with reshape and gather they don't fuse, which is when
-- this function is invoked.
astTransposeAsGather :: forall n r. (KnownNat n, Show r, Numeric r)
                     => Permutation -> Ast n r -> Ast n r
{-# NOINLINE astTransposeAsGather #-}
astTransposeAsGather perm v = unsafePerformIO $ do
  let p = length perm
  varList <- replicateM p unsafeGetFreshAstVar
  return $! case someNatVal $ toInteger p of
    Just (SomeNat (_proxy :: Proxy p)) ->
      let vars :: AstVarList p
          vars = listToSized varList
          intVars = listToIndex $ map AstIntVar varList
          asts :: AstIndex p r
          asts = permutePrefixIndex perm intVars
      in case cmpNat (Proxy @p) (Proxy @n) of
           EQI -> astGatherN @p @(n - p)
                             (permutePrefixShape perm (shapeAst v)) v
                             (vars, asts)
           LTI -> astGatherN @p @(n - p)
                             (permutePrefixShape perm (shapeAst v)) v
                             (vars, asts)
           _ -> error "astTransposeAsGather: permutation longer than rank"
    Nothing -> error "astTransposeAsGather: impossible someNatVal error"

-- * The simplifying combinators

astIndexZ :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
          => Ast (m + n) r -> AstIndex m r -> Ast n r
astIndexZ = astIndexZOrStepOnly False

astIndexStep :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
             => Ast (m + n) r -> AstIndex m r -> Ast n r
astIndexStep v ix = astIndexZOrStepOnly True v (fmap (simplifyAstInt) ix)

-- None of the cases duplicate terms or enlarge them a lot, except AstOp,
-- AstFromList AstFromVector and AstAppend. However, we can't refuse to simplify
-- those. The best we can do is, if the stepOnly flag is set, to refuse
-- to outright recursively apply the procedure when we know the application
-- would be to many copies. We push down indexing on demand instead.
astIndexZOrStepOnly :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
                    => Bool -> Ast (m + n) r -> AstIndex m r -> Ast n r
astIndexZOrStepOnly _ v0 ZI = v0
astIndexZOrStepOnly stepOnly v0 ix@(i1 :. (rest1 :: AstIndex m1 r)) =
 let astIndex :: forall m' n'. (KnownNat m', KnownNat n')
              => Ast (m' + n') r -> AstIndex m' r -> Ast n' r
     astIndex = astIndexZOrStepOnly stepOnly
 in case v0 of
  AstVar{} -> AstIndexZ v0 ix
  AstOp opCode args ->
    -- For operations with more than argument, this bloats the term,
    -- duplicating the projection, potentially recursively.
    -- Therefore, if the goal is to uncover the constructor under projection,
    -- we do this by one step only.
    -- However, to guarantee all redexes involving this projection are reduced
    -- (e.g., because the projection is created during the vectorization
    -- and we want to simplify all that we introduce), we need to push
    -- the indexing arbitrarily deep. This is because we can't have
    -- a normal form that does not have the capacity to hide redexes
    -- arbitrarily deep inside AstOp. Fortunately, as long as redexes get
    -- reduced, pushing down is beneficial. The worst case is variables
    -- in the index expression or the projected term that prevent reduction.
    -- This leads to a bloated term and to performing the indexing many times
    -- once the value of the variables is know. The latter is beneficial
    -- as long as the tensors are large enough and the dimension at which
    -- we index has more than one element. But the bloated term is bad for AD,
    -- regardless of the likely speedup of the forward computation.
    -- This is a complex trade-off, so we need to benchmarked often.
    let project = if stepOnly && length args > 1 then AstIndexZ else astIndex
    in AstOp opCode (map (`project` ix) args)
  AstConst{} -> AstIndexZ v0 ix
  AstConstant (AstPrimalPart v) -> AstConstant $ AstPrimalPart $ AstIndexZ v ix
  AstConstInt{} ->
    error "astIndexZOrStepOnly: impossible pattern needlessly required"
  AstIndexZ v ix2 ->
    astIndex v (appendIndex ix2 ix)
  AstSum v ->  -- almost neutral; transposition is likely to fuse away
    let perm3 = permCycle $ valueOf @m + 1
    in astSum $ astIndex (astTranspose perm3 v) ix
  AstFromList l | AstIntConst i <- i1 ->
    astIndex (l !! i) rest1
  AstFromList l ->
    let project = if stepOnly && length l > 1 then AstIndexZ else astIndex
    in AstIndexZ (astFromList $ map (`project` rest1) l) (singletonIndex i1)
  AstFromVector l | AstIntConst i <- i1 ->
    astIndex (l V.! i) rest1
  AstFromVector l ->
    let project = if stepOnly && length l > 1 then AstIndexZ else astIndex
    in AstIndexZ (astFromVector $ V.map (`project` rest1) l) (singletonIndex i1)
  AstKonst _k v ->
    astIndex v rest1
  AstAppend v w ->
    let vlen = AstIntConst $ lengthAst v
        ix2 = simplifyAstInt (AstIntOp MinusIntOp [i1, vlen]) :. rest1
        project = if stepOnly then AstIndexZ else astIndex
    in case simplifyAstBool $ AstRelInt LsOp [i1, vlen] of
      AstBoolConst b -> if b then astIndex v ix else astIndex w ix2
      bExpr -> astCond bExpr (project v ix) (project w ix2)
  AstSlice i _k v ->
    astIndex v (simplifyAstInt (AstIntOp PlusIntOp [i1, AstIntConst i])
                 :. rest1)
  AstReverse v ->
    let revIs = simplifyAstInt (AstIntOp MinusIntOp
                                         [AstIntConst (lengthAst v - 1), i1])
                :. rest1
    in astIndex v revIs
  AstTranspose perm v | valueOf @m >= length perm ->
    astIndex v (permutePrefixIndex perm ix)
  AstTranspose perm v ->
    astIndex (astTransposeAsGather perm v) ix
  AstReshape sh v ->
    if stepOnly
    then case astReshape sh v of
      AstReshape sh2 v2 -> astIndex (astReshapeAsGather sh2 v2) ix
      v3 -> astIndex v3 ix
    else  -- we assume the term is already simplified
      astIndex (astReshapeAsGather sh v) ix
  AstBuild1 _n2 (var2, v) ->  -- only possible tests
    astIndex (substituteAst i1 var2 v) rest1
  AstGather1 _n2 v (var2, ix2) ->
    let ix3 = fmap (substituteAstInt i1 var2) ix2
    in astIndex v (appendIndex ix3 rest1)
  AstGatherN _sh v (Z, ix2) -> astIndex v (appendIndex ix2 ix)
  AstGatherN (_ :$ sh') v (var2 ::: vars, ix2) ->
    -- TODO: does astGatherN need the stepOnly parameter?
    let ix3 = fmap (substituteAstInt i1 var2) ix2
        w :: Ast (m1 + n) r
        w = unsafeCoerce $ astGatherN sh' v (vars, ix3)
    in astIndex @m1 @n w rest1
  AstGatherN{} ->
    error "astIndex: AstGatherN: impossible pattern needlessly required"

astSum :: Ast (1 + n) r -> Ast n r
astSum (AstReverse v) = AstSum v
astSum v = AstSum v

astFromList :: KnownNat n
            => [Ast n r] -> Ast (1 + n) r
astFromList [a] = astKonst 1 a
astFromList l = AstFromList l

astFromVector :: KnownNat n
              => Data.Vector.Vector (Ast n r) -> Ast (1 + n) r
astFromVector v | V.length v == 1 = astKonst 1 (v V.! 1)
astFromVector l = AstFromVector l

astKonst :: KnownNat n => Int -> Ast n r -> Ast (1 + n) r
astKonst k = \case
  AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astKonst k v
  AstReshape sh v ->
    AstReshape (k :$ sh) $ astKonst k v
  v -> AstKonst k v

astKonstN :: forall n p r. (KnownNat n, KnownNat p)
          => ShapeInt (n + p) -> Ast p r -> Ast (n + p) r
astKonstN sh =
  let go :: KnownNat n' => ShapeInt n' -> Ast p r -> Ast (n' + p) r
      go ZS v = v
      go (k :$ sh') v = astKonst k $ go sh' v
  in go (takeShape sh)

astAppend :: KnownNat n
          => Ast (1 + n) r -> Ast (1 + n) r -> Ast (1 + n) r
astAppend (AstFromList l1) (AstFromList l2) = AstFromList $ l1 ++ l2
astAppend (AstFromList l1) (AstFromVector l2) = AstFromList $ l1 ++ V.toList l2
astAppend (AstFromVector l1) (AstFromList l2) = AstFromList $ V.toList l1 ++ l2
astAppend (AstFromVector l1) (AstFromVector l2) = AstFromVector $ l1 V.++ l2
astAppend u v = AstAppend u v

astSlice :: forall n r. (KnownNat n, Show r, Numeric r)
         => Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
astSlice 0 k v | k == lengthAst v = v
astSlice i k (AstFromList l) = astFromList $ take k (drop i l)
astSlice i k (AstFromVector l) = astFromVector $ V.take k (V.drop i l)
astSlice _i k (AstKonst _k2 v) = astKonst k v
astSlice i k w@(AstAppend (u :: Ast (1 + n) r) (v :: Ast (1 + n) r)) =
  -- GHC 9.4.4 and 9.2.6 with the plugins demans so much verbiage ^^^
  -- TODO: test with 9.6 ASAP.
  -- It seems this is caused by only having (1 + n) in the type
  -- signature and + not being injective. Quite hopless in cases
  -- where swithing to n -> n is not an option. Perhaps it fixes itself
  -- whenever n -> n is wrong, because a function that requires 1 + n
  -- is used.
  let ulen = lengthAst u
  in if | i + k <= ulen -> astSlice @n i k u
        | i >= ulen -> astSlice @n (i - ulen) k v
        | otherwise -> AstSlice @n i k w  -- cheap iff fits in one
astSlice i k v = AstSlice i k v

astReverse :: forall n r. KnownNat n
           => Ast (1 + n) r -> Ast (1 + n) r
astReverse (AstFromList l) = AstReverse @n $ AstFromList $ reverse l
astReverse (AstFromVector l) = AstReverse @n $ AstFromVector $ V.reverse l
astReverse (AstKonst k v) = AstKonst k v
astReverse (AstReverse v) = AstReverse @n v
astReverse v = AstReverse v

astTranspose :: forall n r. KnownNat n
             => Permutation -> Ast n r -> Ast n r
astTranspose perm t | isIdentityPerm perm = t
astTranspose perm1 (AstTranspose perm2 t) =
  let perm2Matched =
        perm2 ++ take (length perm1 - length perm2) (drop (length perm2) [0 ..])
      perm = permutePrefixList perm1 perm2Matched
  in astTranspose perm t
    -- this rule can be disabled to test fusion of gathers.
astTranspose perm u = AstTranspose perm u

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshape :: forall p m r. (KnownNat p, KnownNat m, Show r, Numeric r)
           => ShapeInt m -> Ast p r -> Ast m r
astReshape shOut (AstConst t) = AstConst $ OR.reshape (shapeToList shOut) t
astReshape shOut (AstConstant (AstPrimalPart v)) =
  AstConstant $ AstPrimalPart $ AstReshape shOut v
astReshape shOut (AstReshape _ v) = astReshape shOut v
  -- this rule can be disabled to test fusion of gathers.
astReshape shOut v =
  let shIn = shapeAst v
  in case sameNat (Proxy @p) (Proxy @m) of
    Just Refl -> if shIn == shOut
                 then v
                 else AstReshape shOut v
    _ -> AstReshape shOut v

-- Assumption: var does not occur in v0.
astGather1 :: forall p n r. (KnownNat p, KnownNat n, Show r, Numeric r)
           => Int -> Ast (p + n) r -> (AstVarName Int, AstIndex p r)
           -> Ast (1 + n) r
astGather1 k v0 (var, ix) =
  let v3 = astIndexZ v0 ix
  in if intVarInAst var v3
     then case v3 of
       AstIndexZ v2 ix2@(i1 :. rest1) ->
         if | intVarInAst var v2 ->
              AstGather1 k v0 (var, ix)
            | intVarInIndex var rest1 ->
              AstGather1 k v2 (var, ix2)
            | intVarInAstInt var i1 ->
--                let w :: Ast (1 + n) r
--                    w = astIndexZ v2 rest1
--                in case gatherSimplify k var w i1 of
--                  Just u -> u  -- an extremely simple form found
--                  Nothing ->
                    AstGather1 k v2 (var, ix2)
                    -- we didn't really need it anyway
            | otherwise -> astKonst k (AstIndexZ v2 ix2)
       _ -> AstGather1 k v0 (var, ix)  -- e.g., AstSum
     else astKonst k v3

-- Assumption: (var ::: vars) don't not occur in v0.
astGatherN :: forall m n p r.
              (KnownNat m, KnownNat p, KnownNat n, Show r, Numeric r)
           => ShapeInt (m + n) -> Ast (p + n) r -> (AstVarList m, AstIndex p r)
           -> Ast (m + n) r
astGatherN _sh v0 (Z, ix) = astIndexZ v0 ix
astGatherN sh@(_ :$ _) v0 (_ ::: _, ZI) = astKonstN sh v0
astGatherN sh@(k :$ sh') v0 (var ::: vars, ix@(_ :. _)) =
  let v3 = astIndexZ @p @n v0 ix
  in if any (flip intVarInAst v3) (var ::: vars)
     then case v3 of
       AstIndexZ v2 ix2 ->
         if | any (flip intVarInAst v2) (var ::: vars) ->
              AstGatherN sh v0 (var ::: vars, ix)
            | intVarInIndex var ix2 ->
              AstGatherN sh v2 (var ::: vars, ix2)
            | any (flip intVarInIndex ix2) vars ->
              astKonst k (astGatherN sh' v2 (vars, ix2))
            | otherwise -> astKonstN sh (AstIndexZ v2 ix2)
              -- a generalization of gatherSimplify needed to simplify more
              -- or we could run astGather1 repeatedly, but even then we can't
              -- get into fromList, which may simplify or complicate a term,
              -- and sometimes is not possible without leaving a small
              -- gather outside
       AstGatherN sh2 v2 (vars2, ix2) ->
         if | any (flip intVarInAst v2) (var ::: vars) ->  -- can this happen?
              AstGatherN sh v0 (var ::: vars, ix)
            | otherwise ->
              AstGatherN (appendShape (takeShape @m sh) sh2)
                         v2 (appendSized (var ::: vars) vars2, ix2)
       _ -> AstGatherN sh v0 (var ::: vars, ix)  -- e.g., AstSum
     else astKonstN sh v3
astGatherN _ _ _ =
  error "astGatherN: AstGatherN: impossible pattern needlessly required"

-- To apply this to astGatherN. we'd need to take the last variable
-- and the first index element in place of var and i1.
-- If var does not occur in the remaining index elements,
-- this simplification is valid.
{-
            | intVarInAstInt var i1 ->
                let w :: Ast (1 + n) r
                    w = astIndexZ v2 rest1
                in case gatherSimplify k var w i1 of
                  Just u -> u  -- an extremely simple form found
                    -- for AstGatherN instead:
                    -- AstGatherN ... u (initN, rest1)
                  Nothing ->
                    AstGather1 k v2 (var, ix2)
                    -- we didn't really need it anyway
            | otherwise -> astKonst k (AstIndexZ v2 ix2)
-}
-- Let's instead wait and see if we can come up with more general
-- simplifications, involving all variables. Especially that
-- astSliceLax is so complex. Perhaps instead of recovering slices
-- and the identity, transpositions and the identity would be better.
-- | The application @gatherSimplify k var v i1@ vectorizes and simplifies
-- the term @AstBuild1 k (var, AstIndexZ v [i1])@, where it's known that
-- @var@ does not occur in @v@ but occurs in @i1@. This is done by pattern
-- matching on @i1@ as opposed to on @v@.
gatherSimplify
  :: (KnownNat n, Show r, Numeric r)
  => Int -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Maybe (Ast (1 + n) r)
gatherSimplify k var v0 i1 =
  case i1 of
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
astIntCond (AstBoolConst b) v w = if b then v else w
astIntCond b v w = AstIntCond b v w

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

-- This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexZ.
simplifyAst
  :: (Show r, Numeric r, KnownNat n)
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
  AstTranspose perm v -> case astTranspose perm $ simplifyAst v of
    AstTranspose perm2 v2 -> astTransposeAsGather perm2 v2
      -- this is expensive, but the only way to guarantee full simplification
    u -> u
  AstReshape sh v -> case astReshape sh (simplifyAst v) of
    AstReshape sh2 v2 -> astReshapeAsGather sh2 v2
      -- this is terribly expensive, but the only way to fully simplify
    u -> u
  AstBuild1 k (var, v) -> AstBuild1 k (var, simplifyAst v)
    -- should never appear outside test runs, but let's test the inside, too
  AstGather1 k v (var, ix) ->
    astGather1 k (simplifyAst v) (var, fmap (simplifyAstInt) ix)
  AstGatherN sh v (vars, ix) ->
    astGatherN sh (simplifyAst v) (vars, fmap (simplifyAstInt) ix)

-- Integer terms need to be simplified, because they are sometimes
-- created by vectorization and can be a deciding factor in whether
-- dual terms can be simplified in turn.
simplifyAstInt :: (Show r, Numeric r)
               => AstInt r -> AstInt r
simplifyAstInt t = case t of
  AstIntVar{} -> t
  AstIntOp opCodeInt args ->
    simplifyAstIntOp opCodeInt (map simplifyAstInt args)
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
  AstBoolOp opCodeBool args ->
    simplifyAstBoolOp opCodeBool (map simplifyAstBool args)
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
    -- TODO: evaluate if arguments are constants

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right
-- and let's push negation down.
simplifyAstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
simplifyAstIntOp PlusIntOp [AstIntConst u, AstIntConst v] = AstIntConst $ u + v
simplifyAstIntOp PlusIntOp [ AstIntConst u
                           , AstIntOp PlusIntOp [AstIntConst v, w] ] =
  simplifyAstIntOp PlusIntOp [AstIntConst $ u + v, w]
simplifyAstIntOp PlusIntOp [AstIntConst 0, v] = v
simplifyAstIntOp PlusIntOp [u, AstIntConst 0] = u
simplifyAstIntOp PlusIntOp [AstIntOp PlusIntOp [u, v], w] =
  simplifyAstIntOp PlusIntOp [u, simplifyAstIntOp PlusIntOp [v, w]]

simplifyAstIntOp MinusIntOp [u, v] =
  simplifyAstIntOp PlusIntOp [u, simplifyAstIntOp NegateIntOp [v]]

simplifyAstIntOp TimesIntOp [AstIntConst u, AstIntConst v] = AstIntConst $ u * v
simplifyAstIntOp TimesIntOp [ AstIntConst u
                            , AstIntOp TimesIntOp [AstIntConst v, w] ] =
  simplifyAstIntOp TimesIntOp [AstIntConst $ u * v, w]
simplifyAstIntOp TimesIntOp [AstIntConst 0, _v] = AstIntConst 0
simplifyAstIntOp TimesIntOp [_u, AstIntConst 0] = AstIntConst 0
simplifyAstIntOp TimesIntOp [AstIntConst 1, v] = v
simplifyAstIntOp TimesIntOp [u, AstIntConst 1] = u
simplifyAstIntOp TimesIntOp [AstIntOp TimesIntOp [u, v], w] =
  simplifyAstIntOp TimesIntOp [u, simplifyAstIntOp TimesIntOp [v, w]]
simplifyAstIntOp TimesIntOp [AstIntOp PlusIntOp [u, v], w] =
  simplifyAstIntOp PlusIntOp [ simplifyAstIntOp TimesIntOp [u, w]
                             , simplifyAstIntOp TimesIntOp [v, w] ]
simplifyAstIntOp TimesIntOp [u, AstIntOp PlusIntOp [v, w]] =
  simplifyAstIntOp PlusIntOp [ simplifyAstIntOp TimesIntOp [u, v]
                             , simplifyAstIntOp TimesIntOp [u, w] ]

-- Almost complete. TODO: given choice, prefer to negate a constant.
simplifyAstIntOp NegateIntOp [AstIntConst u] = AstIntConst $ negate u
simplifyAstIntOp NegateIntOp [AstIntOp PlusIntOp [u, v]] =
  simplifyAstIntOp PlusIntOp [ simplifyAstIntOp NegateIntOp [u]
                             , simplifyAstIntOp NegateIntOp [v] ]
simplifyAstIntOp NegateIntOp [AstIntOp TimesIntOp [u, v]] =
  simplifyAstIntOp TimesIntOp [u, simplifyAstIntOp NegateIntOp [v]]
simplifyAstIntOp NegateIntOp [AstIntOp NegateIntOp [u]] = u
simplifyAstIntOp NegateIntOp [AstIntOp SignumIntOp [u]] =
  simplifyAstIntOp SignumIntOp [simplifyAstIntOp NegateIntOp [u]]
simplifyAstIntOp NegateIntOp [AstIntOp MaxIntOp [u, v]] =
  simplifyAstIntOp MinIntOp [ simplifyAstIntOp NegateIntOp [u]
                            , simplifyAstIntOp NegateIntOp [v] ]
simplifyAstIntOp NegateIntOp [AstIntOp MinIntOp [u, v]] =
  simplifyAstIntOp MaxIntOp [ simplifyAstIntOp NegateIntOp [u]
                            , simplifyAstIntOp NegateIntOp [v] ]
simplifyAstIntOp NegateIntOp [AstIntOp QuotIntOp [u, v]] =
  simplifyAstIntOp QuotIntOp [u, simplifyAstIntOp NegateIntOp [v]]
simplifyAstIntOp NegateIntOp [AstIntOp RemIntOp [u, v]] =
  simplifyAstIntOp RemIntOp [u, simplifyAstIntOp NegateIntOp [v]]

simplifyAstIntOp AbsIntOp [AstIntConst u] = AstIntConst $ abs u
simplifyAstIntOp AbsIntOp [AstIntOp AbsIntOp [u]] = AstIntOp AbsIntOp [u]
simplifyAstIntOp AbsIntOp [AstIntOp NegateIntOp [u]] =
  simplifyAstIntOp AbsIntOp [u]
simplifyAstIntOp SignumIntOp [AstIntConst u] = AstIntConst $ signum u
simplifyAstIntOp MaxIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ max u v
simplifyAstIntOp MinIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ min u v

simplifyAstIntOp QuotIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ quot u v
simplifyAstIntOp QuotIntOp [AstIntConst 0, _v] = AstIntConst 0
simplifyAstIntOp QuotIntOp [u, AstIntConst 1] = u
simplifyAstIntOp QuotIntOp [ AstIntOp RemIntOp [_u, AstIntConst v]
                           , AstIntConst v' ]
  | v' >= v && v >= 0 = 0
simplifyAstIntOp QuotIntOp [AstIntOp QuotIntOp [u, v], w] =
  simplifyAstIntOp QuotIntOp [u, simplifyAstIntOp TimesIntOp [v, w]]

simplifyAstIntOp RemIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ rem u v
simplifyAstIntOp RemIntOp [AstIntConst 0, _v] = 0
simplifyAstIntOp RemIntOp [_u, AstIntConst 1] = 0
simplifyAstIntOp RemIntOp [AstIntOp RemIntOp [u, AstIntConst v], AstIntConst v']
  | v' >= v && v >= 0 = AstIntOp RemIntOp [u, AstIntConst v]
simplifyAstIntOp RemIntOp [AstIntOp RemIntOp [u, AstIntConst v], AstIntConst v']
  | rem v v' == 0 && v > 0 = simplifyAstIntOp RemIntOp [u, AstIntConst v']

simplifyAstIntOp opCodeInt arg = AstIntOp opCodeInt arg

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right.
simplifyAstBoolOp :: OpCodeBool -> [AstBool r] -> AstBool r
simplifyAstBoolOp NotOp [AstBoolConst b] = AstBoolConst $ not b
simplifyAstBoolOp AndOp [AstBoolConst True, b] = b
simplifyAstBoolOp AndOp [AstBoolConst False, _b] = AstBoolConst False
simplifyAstBoolOp AndOp [b, AstBoolConst True] = b
simplifyAstBoolOp AndOp [_b, AstBoolConst False] = AstBoolConst False
simplifyAstBoolOp OrOp [AstBoolConst True, _b] = AstBoolConst True
simplifyAstBoolOp OrOp [AstBoolConst False, b] = b
simplifyAstBoolOp OrOp [_b, AstBoolConst True] = AstBoolConst True
simplifyAstBoolOp OrOp [b, AstBoolConst False] = b
simplifyAstBoolOp opCodeBool arg = AstBoolOp opCodeBool arg

-- We have to simplify after substitution or simplifying is not idempotent.
substituteAst :: (Show r, Numeric r, KnownNat n)
              => AstInt r -> AstVarName Int -> Ast n r -> Ast n r
substituteAst i var v1 = simplifyAst $ substitute1Ast i var v1

substituteAstInt :: (Show r, Numeric r)
                 => AstInt r -> AstVarName Int -> AstInt r -> AstInt r
substituteAstInt i var i2 = simplifyAstInt $ substitute1AstInt i var i2

substituteAstBool :: (Show r, Numeric r)
                  => AstInt r -> AstVarName Int -> AstBool r -> AstBool r
substituteAstBool i var b1 = simplifyAstBool $ substitute1AstBool i var b1
