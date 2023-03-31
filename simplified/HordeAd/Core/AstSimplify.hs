{-# LANGUAGE AllowAmbiguousTypes #-}
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
  ( simplifyPermutation
  , funToAstR, funToAstD, funToAstI, funToAstIndex
  , simplifyStepNonIndex, astIndexStep, astGatherStep
  , astReshape, astTranspose
  , astConstant, astSum, astScatter, astFromList, astFromVector, astKonst
  , astAppend, astSlice, astReverse, astFromDynamic
  , astIntCond
  , ShowAstSimplify, simplifyAst
  , substituteAst, substituteAstInt, substituteAstBool
  , resetVarCounter
  ) where

import Prelude

import           Control.Monad (replicateM)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.List (dropWhileEnd)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import           Data.Type.Ord (Compare)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , SomeNat (..)
  , cmpNat
  , sameNat
  , someNatVal
  , type (+)
  , type (-)
  , type (<=)
  )
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.Internal.SizedList
import HordeAd.Internal.TensorOps

type ShowAstSimplify r = (ShowAst r, Num (Vector r))


-- * Permutation operations

simplifyPermutation :: Permutation -> Permutation
simplifyPermutation perm =
  map fst $ dropWhileEnd (uncurry (==)) $ zip perm [0 ..]

permCycle :: Int -> Permutation
permCycle 0 = []
permCycle 1 = []
permCycle n = [k `mod` n | k <- [1 .. n]]

permBackCycle :: Int -> Permutation
permBackCycle 0 = []
permBackCycle 1 = []
permBackCycle n = [k `mod` n | k <- [-1, 0 .. n - 2]]


-- * Generating variables names

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 1)

-- Only for tests, e.g., to ensure show applied to terms has stable length.
-- Tests using this need to be run with -ftest_seq to avoid variable confusion.
resetVarCounter :: IO ()
resetVarCounter = writeIORefU unsafeAstVarCounter 1000

unsafeGetFreshAstVarId :: IO AstVarId
{-# INLINE unsafeGetFreshAstVarId #-}
unsafeGetFreshAstVarId =
  intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

funToAstR :: ShapeInt n -> (Ast n r -> Ast m r)
          -> (AstVarName (TensorOf n r), Ast m r)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  return (AstVarName freshId, f (AstVar sh freshId))

-- The "fun"ction in this case is fixed to be @id@.
funToAstD :: forall r. [Int] -> (AstDynamicVarName r, AstDynamic r)
{-# NOINLINE funToAstD #-}
funToAstD sh = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  return $! case someNatVal $ toInteger $ length sh of
    Just (SomeNat (_proxy :: Proxy p)) ->
      let shn = listShapeToShape @p sh
          varName = AstVarName @(TensorOf p r) freshId
      in (AstDynamicVarName varName, AstDynamicVar shn freshId)
    Nothing -> error "funToAstD: impossible someNatVal error"

funToAstI :: (AstInt r -> t) -> (AstVarId, t)
{-# NOINLINE funToAstI #-}
funToAstI f = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  return (freshId, f (AstIntVar freshId))

funToAstIndex :: forall m p r. KnownNat m
              => (AstIndex m r -> AstIndex p r) -> (AstVarList m, AstIndex p r)
{-# NOINLINE funToAstIndex #-}
funToAstIndex f = unsafePerformIO $ do
  varList <- replicateM (valueOf @m) unsafeGetFreshAstVarId
  return (listToSized varList, f (listToIndex $ map AstIntVar varList))


-- * Expressing operations as Gather; introduces new variable names

-- This generates big terms that don't simplify well,
-- so we keep the AstReshape form until simplification gets stuck.
-- In fact, to simplify the terms we'd need advanced solving of equations
-- in integer arithmetic modulo. Moreover, when solving, we'd need to know
-- the range of all integer variables (taken from shapes) and the floor
-- and minimum/maximum terms (obtained by analysing the embedded Ast term),
-- because many of the emerging terms are not equal to their simplifed
-- forms without this data. Probably we could just subsitute @var `rem` range@
-- for each variable.
--
-- TODO: To make this less disastrous, we need to add an extra constructor
-- to AstIndex with the semantics "this index reshaped from shIn to shOut"
-- that fuses perfectly with itself and absorbs normal indexes
-- by substitution. Or perhaps make this the only constructor, with normal
-- indexes represented as "this index reshaped from sh to sh".
-- Or only extend AstGatherZ and possibly also AstIndexZ with the extra
-- shIn and shOut arguments. This complicates any code related to
-- AstGatherZ and AstIndexZ, but often prevents nested reshapes from affecting
-- term size in any way. But we'd need to be careful to avoid breaking such
-- an index into components, because that forces index normalization,
-- e.g., index(gather) can no longer simplify recursively by one index
-- component at a time (probably possible only if the index is shorter
-- that the list of variables fo the gather). There are probably bad cases
-- where term size blowup can't be avoided, because the index has to be
-- normalized between each reshape.
astReshapeAsGather
  :: forall p m r. (KnownNat p, KnownNat m, ShowAstSimplify r)
  => ShapeInt m -> Ast p r -> Ast m r
{-# NOINLINE astReshapeAsGather #-}
astReshapeAsGather shOut v = unsafePerformIO $ do
  varList <- replicateM (lengthShape shOut) unsafeGetFreshAstVarId
  let shIn = shapeAst v
      vars :: AstVarList m
      vars = listToSized varList
      ix :: AstIndex m r
      ix = listToIndex $ map AstIntVar varList
      asts :: AstIndex p r
      asts = let i = toLinearIdx @m @0 shOut ix
             in fmap simplifyAstInt $ fromLinearIdx shIn i
                  -- we generate these, so we simplify
  return $! astGatherZ @m @0 shOut v (vars, asts)

-- We keep AstTranspose terms for as long as possible, because
-- they are small and fuse nicely in many cases. For some forms of indexing
-- and nesting with reshape and gather they don't fuse, which is when
-- this function is invoked.
astTransposeAsGather
  :: forall n r. (KnownNat n, ShowAstSimplify r)
  => Permutation -> Ast n r -> Ast n r
{-# NOINLINE astTransposeAsGather #-}
astTransposeAsGather perm v = unsafePerformIO $ do
  let p = length perm
  varList <- replicateM p unsafeGetFreshAstVarId
  return $! case someNatVal $ toInteger p of
    Just (SomeNat (_proxy :: Proxy p)) ->
      let vars :: AstVarList p
          vars = listToSized varList
          intVars = listToIndex $ map AstIntVar varList
          asts :: AstIndex p r
          asts = permutePrefixIndex perm intVars
      in case cmpNat (Proxy @p) (Proxy @n) of
           EQI -> astGatherZ @p @(n - p)
                             (permutePrefixShape perm (shapeAst v)) v
                             (vars, asts)
           LTI -> astGatherZ @p @(n - p)
                             (permutePrefixShape perm (shapeAst v)) v
                             (vars, asts)
           _ -> error "astTransposeAsGather: permutation longer than rank"
    Nothing -> error "astTransposeAsGather: impossible someNatVal error"


-- * The simplifying combinators

-- This does a single step of simplification of any non-indexing term
-- (many steps if guaranteed net beneficial).
-- AstInt and AstBool terms are simplified fully.
simplifyStepNonIndex
  :: (KnownNat n, ShowAstSimplify r)
  => Ast n r -> Ast n r
simplifyStepNonIndex t = case t of
  AstVar{} -> t
  AstLet{} -> t
  AstOp{} -> t
  AstConst{} -> t
  AstConstant v -> astConstant v
  AstIndexZ{} -> t
  AstSum v -> astSum v
  AstConstInt0 i -> AstConstInt0 $ simplifyAstInt i
  AstScatter sh v (vars2, ix2) -> astScatter sh v (vars2, ix2)
  AstFromList l -> astFromList l
  AstFromVector l -> astFromVector l
  AstKonst k v -> astKonst k v
  AstAppend x y -> astAppend x y
  AstSlice i k v -> astSlice i k v
  AstReverse v -> astReverse v
  AstTranspose perm v -> astTranspose perm v
  AstReshape sh v -> astReshape sh v
  AstBuild1{} -> t
  AstGatherZ _ v0 (Z, ix) -> AstIndexZ v0 ix
  AstGatherZ sh v0 (_, ZI) -> astKonstN sh v0
  AstGatherZ {} -> t
  AstD{} -> t  -- TODO

astIndexZ
  :: forall m n r.
     (KnownNat m, KnownNat n, ShowAstSimplify r)
  => Ast (m + n) r -> AstIndex m r -> Ast n r
astIndexZ = astIndexZOrStepOnly False

astIndexStep
  :: forall m n r.
     (KnownNat m, KnownNat n, ShowAstSimplify r)
  => Ast (m + n) r -> AstIndex m r -> Ast n r
astIndexStep v ix = astIndexZOrStepOnly True (simplifyStepNonIndex v)
                                             (fmap simplifyAstInt ix)

-- If stepOnly is set, we reduce only as long as needed to reveal
-- a non-indexing constructor or one of the normal forms (one-element
-- indexing applied to AstFromList or AstFromVector or indexing
-- of a term with no possible occurences of Int variables). Otherwise,
-- we simplify exhaustively.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astIndexStep.
astIndexZOrStepOnly
  :: forall m n r.
     (KnownNat m, KnownNat n, ShowAstSimplify r)
  => Bool -> Ast (m + n) r -> AstIndex m r -> Ast n r
astIndexZOrStepOnly stepOnly (AstIndexZ v ix) ZI =
  astIndexZOrStepOnly stepOnly v ix  -- no non-indexing constructor yet revealed
astIndexZOrStepOnly _ v0 ZI = v0
astIndexZOrStepOnly stepOnly v0 ix@(i1 :. (rest1 :: AstIndex m1 r)) =
 let astIndexRec, astIndex :: forall m' n'. (KnownNat m', KnownNat n')
                           => Ast (m' + n') r -> AstIndex m' r -> Ast n' r
     astIndexRec vRec ZI = vRec
     astIndexRec vRec ixRec =
       if stepOnly then AstIndexZ vRec ixRec else astIndexZ vRec ixRec
     astIndex = if stepOnly then astIndexStep else astIndexZ
     astGather
       :: forall m' n' p'.
          (KnownNat m', KnownNat p', KnownNat n')
       => ShapeInt (m' + n') -> Ast (p' + n') r
       -> (AstVarList m', AstIndex p' r)
       -> Ast (m' + n') r
     astGather = if stepOnly then astGatherStep else astGatherZ
 in case v0 of
  AstVar{} -> AstIndexZ v0 ix
  AstLet var u v -> AstLet var u (astIndexRec v ix)
  AstOp opCode args ->
    AstOp opCode (map (`astIndexRec` ix) args)
  AstConst t ->
    let unConst (AstIntConst i) (Just l) = Just $ fromIntegral i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> AstConst $ tindexZR t $ listToIndex ixInt
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> AstIndexZ v0 ix
  AstConstant (AstPrimalPart v) ->
    astConstant $ AstPrimalPart $ astIndexRec v ix
  AstIndexZ v ix2 ->
    astIndex v (appendIndex ix2 ix)
  AstSum v ->  -- almost neutral; transposition is likely to fuse away
    let perm3 = permCycle $ valueOf @m + 1
    in astSum $ astIndex (astTranspose perm3 v) ix
  AstConstInt0{} ->
    error "astIndex: impossible pattern needlessly required"
  -- AstScatter sh v (Z, ix2) -> ifB (ix2 ==* ixHead) (index v ixTail) 0
  -- AstScatter sh v (vars2, ZI) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZI)
  AstScatter{} ->  -- nothing can be simplified at all, so this is a normal form
    AstIndexZ v0 ix
  AstFromList l | AstIntConst i <- i1 ->
    astIndex (if length l > i then l !! i else 0) rest1
  AstFromList{} | ZI <- rest1 ->  -- normal form
    AstIndexZ v0 ix
  AstFromList l ->
    AstIndexZ (astFromList $ map (`astIndexRec` rest1) l)
              (singletonIndex i1)
  AstFromVector l | AstIntConst i <- i1 ->
    astIndex (if V.length l > i then l V.! i else 0) rest1
  AstFromVector{} | ZI <- rest1 ->  -- normal form
    AstIndexZ v0 ix
  AstFromVector l ->
    AstIndexZ (astFromVector $ V.map (`astIndexRec` rest1) l)
              (singletonIndex i1)
  AstKonst _k v ->
    astIndex v rest1
  AstAppend v w ->
    let vlen = AstIntConst $ lengthAst v
        ix2 = simplifyAstInt (AstIntOp MinusIntOp [i1, vlen]) :. rest1
    in case simplifyAstBool $ AstRelInt LsOp [i1, vlen] of
      AstBoolConst b -> if b then astIndex v ix else astIndex w ix2
      bExpr -> astCond bExpr (astIndexRec v ix) (astIndexRec w ix2)
  AstSlice i _k v ->
    let ii = simplifyAstInt (AstIntOp PlusIntOp [i1, AstIntConst i])
    in astIndex v (ii :. rest1)
  AstReverse v ->
    let iRev = simplifyAstInt (AstIntOp MinusIntOp
                                        [AstIntConst (lengthAst v - 1), i1])
    in astIndex v (iRev :. rest1)
  AstTranspose perm v | valueOf @m >= length perm ->
    astIndex v (permutePrefixIndex perm ix)
  AstTranspose perm v ->
    astIndex (astTransposeAsGather perm v) ix
  AstReshape sh v ->
    astIndex (astReshapeAsGather sh v) ix
  AstBuild1 _n2 (var2, v) ->
    astIndex (substituteAst i1 var2 v) rest1
  AstGatherZ _sh v (Z, ix2) -> astIndex v (appendIndex ix2 ix)
  AstGatherZ (_ :$ sh') v (var2 ::: vars, ix2) ->
    let ix3 = fmap (substituteAstInt i1 var2) ix2
        w :: Ast (m1 + n) r
        w = unsafeCoerce $ astGather sh' v (vars, ix3)
    in astIndex @m1 @n w rest1
  AstGatherZ{} ->
    error "astIndex: AstGatherZ: impossible pattern needlessly required"
  AstD (AstPrimalPart u) (AstDualPart u') ->
    AstD (AstPrimalPart $ astIndexRec u ix)
         (AstDualPart $ astIndexRec u' ix)

astConstant :: AstPrimalPart n r -> Ast n r
astConstant (AstPrimalPart (AstConstant t)) = astConstant t
astConstant v = AstConstant v

astSum :: (KnownNat n, Numeric r, Num (Vector r))
       => Ast (1 + n) r -> Ast n r
astSum (AstConst t) = AstConst $ tsumR t
astSum (AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astSum v
astSum (AstReverse v) = AstSum v
astSum v = AstSum v

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatter :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
           => ShapeInt (p + n) -> Ast (m + n) r
           -> (AstVarList m, AstIndex p r)
           -> Ast (p + n) r
-- astScatter sh v (Z, ix) = update (tzero sh 0) ix v
-- astScatter sh v (_, ZI) = astSumN sh v  -- no benefit
astScatter sh (AstConstant (AstPrimalPart v)) (vars, ix) =
  astConstant $ AstPrimalPart $ astScatter sh v (vars, ix)
astScatter sh v (vars, ix) = AstScatter sh v (vars, ix)

astFromList :: (KnownNat n, Numeric r)
            => [Ast n r] -> Ast (1 + n) r
astFromList [a] = astKonst 1 a
astFromList l =
  let unConstant (AstConstant (AstPrimalPart t)) = Just t
      unConstant _ = Nothing
  in case mapM unConstant l of
    Just [] -> AstFromList []
    Just l2 ->
      astConstant $ AstPrimalPart $ astFromList l2
    Nothing ->
      let unConst (AstConst t) = Just t
          unConst _ = Nothing
      in case mapM unConst l of
        Just l3 -> AstConst $ tfromListR l3
        Nothing -> AstFromList l

astFromVector :: (KnownNat n, Numeric r)
              => Data.Vector.Vector (Ast n r) -> Ast (1 + n) r
astFromVector v | V.length v == 1 = astKonst 1 (v V.! 1)
astFromVector l =
  let unConstant (AstConstant (AstPrimalPart t)) = Just t
      unConstant _ = Nothing
  in case V.mapM unConstant l of
    Just l2 | V.null l2 -> AstFromVector l2
    Just l2 ->
      astConstant $ AstPrimalPart $ astFromVector l2
    Nothing ->
      let unConst (AstConst t) = Just t
          unConst _ = Nothing
      in case V.mapM unConst l of
        Just l3 -> AstConst $ tfromVectorR l3
        Nothing -> AstFromVector l

astKonst :: (KnownNat n, Numeric r)
         => Int -> Ast n r -> Ast (1 + n) r
astKonst k = \case
-- This allocates a big tensor too early, while it's still possible
-- a projection reduces this away. The cost to AD should not be too high.
--  AstConst t -> AstConst $ tkonstR k t
  AstConstant (AstPrimalPart v) ->
    astConstant $ AstPrimalPart $ astKonst k v
{- TODO: these may be counterproductive with many gathers and their fusion
         though these let transpose cancel out with each other sometimes
         (instead we should try to cancel out inside konst and only move
          if they don't)
  AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astKonst k v
  AstReshape sh v ->
    AstReshape (k :$ sh) $ astKonst k v
-}
  v -> AstKonst k v

astKonstN :: forall n p r. (KnownNat n, KnownNat p, Numeric r)
          => ShapeInt (n + p) -> Ast p r -> Ast (n + p) r
astKonstN sh =
  let go :: KnownNat n' => ShapeInt n' -> Ast p r -> Ast (n' + p) r
      go ZS v = v
      go (k :$ sh') v = astKonst k $ go sh' v
  in go (takeShape sh)

astAppend :: (KnownNat n, Numeric r)
          => Ast (1 + n) r -> Ast (1 + n) r -> Ast (1 + n) r
astAppend (AstConst u) (AstConst v) = AstConst $ tappendR u v
astAppend (AstConstant (AstPrimalPart u)) (AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astAppend u v
astAppend (AstFromList l1) (AstFromList l2) = astFromList $ l1 ++ l2
astAppend (AstFromList l1) (AstFromVector l2) = astFromList $ l1 ++ V.toList l2
astAppend (AstFromVector l1) (AstFromList l2) = astFromList $ V.toList l1 ++ l2
astAppend (AstFromVector l1) (AstFromVector l2) = astFromVector $ l1 V.++ l2
astAppend u v = AstAppend u v

astSlice :: forall n r. (KnownNat n, ShowAstSimplify r)
         => Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
astSlice i k (AstConst t) = AstConst $ tsliceR i k t
astSlice i k (AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astSlice i k v
astSlice 0 k v | k == lengthAst v = v
astSlice i k (AstFromList l) = astFromList $ take k (drop i l)
astSlice i k (AstFromVector l) = astFromVector $ V.take k (V.drop i l)
astSlice _i k (AstKonst _k2 v) = astKonst k v
astSlice i k w@(AstAppend (u :: Ast (1 + n) r) (v :: Ast (1 + n) r)) =
  -- GHC 9.2.7 -- 9.6.1 with the plugins demand so much verbiage ^^^
  -- It seems this is caused by only having (1 + n) in the type
  -- signature and + not being injective. Quite hopless in cases
  -- where swithing to n -> n is not an option. Perhaps it fixes itself
  -- whenever n -> n is wrong, because a function that requires 1 + n
  -- is used.
  let ulen = lengthAst u
  in if | i + k <= ulen -> astSlice @n i k u
        | i >= ulen -> astSlice @n (i - ulen) k v
        | otherwise -> AstSlice @n i k w  -- cheap iff fits in one
astSlice i k (AstGatherZ (_ :$ sh') v (var ::: vars, ix)) =
  let ivar = AstIntOp PlusIntOp [AstIntVar var, AstIntConst i]
      ix2 = fmap (substituteAstInt ivar var) ix
  in astGatherZ (k :$ sh') v (var ::: vars, ix2)
astSlice i k v = AstSlice i k v

astReverse :: forall n r. (KnownNat n, ShowAstSimplify r)
           => Ast (1 + n) r -> Ast (1 + n) r
astReverse (AstConst t) = AstConst $ treverseR t
astReverse (AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astReverse v
astReverse (AstFromList l) = AstFromList $ reverse l
astReverse (AstFromVector l) = AstFromVector $ V.reverse l
astReverse (AstKonst k v) = AstKonst k v
astReverse (AstReverse v) = v
astReverse (AstGatherZ sh@(k :$ _) v (var ::: vars, ix)) =
  let ivar = AstIntOp MinusIntOp [AstIntConst k, AstIntVar var]
      ix2 = fmap (substituteAstInt ivar var) ix
  in astGatherZ sh v (var ::: vars, ix2)
astReverse v = AstReverse v

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTranspose :: forall n r. KnownNat n
             => Permutation -> Ast n r -> Ast n r
astTranspose perm0 t0 = case (perm0, t0) of
  ([], t) -> t
  (perm, AstConst t) ->
    AstConst $ ttransposeR perm t
  (perm, AstConstant (AstPrimalPart v)) ->
    astConstant $ AstPrimalPart $ astTranspose perm v
  (perm1, AstTranspose perm2 t) ->
    let perm2Matched =
          perm2
          ++ take (length perm1 - length perm2) (drop (length perm2) [0 ..])
        perm = simplifyPermutation $ permutePrefixList perm1 perm2Matched
    in astTranspose perm t
      -- this rule can be disabled to test fusion of gathers.
  (perm1, AstGatherZ @m sh v (vars, ix)) | length perm1 <= valueOf @m ->
    AstGatherZ (permutePrefixShape perm1 sh) v
               (permutePrefixSized perm1 vars, ix)
  (perm, u) -> AstTranspose perm u

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshape :: forall p m r. (KnownNat p, KnownNat m, ShowAstSimplify r)
           => ShapeInt m -> Ast p r -> Ast m r
astReshape shOut (AstConst t) = AstConst $ OR.reshape (shapeToList shOut) t
astReshape shOut (AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astReshape shOut v
astReshape shOut (AstReshape _ v) = astReshape shOut v
  -- this rule can be disabled to test fusion of gathers.
astReshape shOut v =
  let shIn = shapeAst v
  in case sameNat (Proxy @p) (Proxy @m) of
    Just Refl -> if shIn == shOut
                 then v
                 else AstReshape shOut v
    _ -> AstReshape shOut v

astGatherZ
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, ShowAstSimplify r)
  => ShapeInt (m + n) -> Ast (p + n) r -> (AstVarList m, AstIndex p r)
  -> Ast (m + n) r
astGatherZ = astGatherZOrStepOnly False

astGatherStep
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, ShowAstSimplify r)
  => ShapeInt (m + n) -> Ast (p + n) r -> (AstVarList m, AstIndex p r)
  -> Ast (m + n) r
astGatherStep sh v (vars, ix) =
  astGatherZOrStepOnly True sh (simplifyStepNonIndex v)
                            (vars, fmap simplifyAstInt ix)

-- Assumption: vars0 don't not occur in v0. The assumption only holds
-- when newly generated variables are fresh, which is the case as long
-- as resetVarCounter is not used. The assumption makes it easier to spot
-- bugs or corruption, hence we assert it in the code below.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astGatherStep.
astGatherZOrStepOnly
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, ShowAstSimplify r)
  => Bool -> ShapeInt (m + n) -> Ast (p + n) r -> (AstVarList m, AstIndex p r)
  -> Ast (m + n) r
astGatherZOrStepOnly stepOnly sh0 v0 (vars0, ix0) =
  case (sh0, (vars0, ix0)) of
    _ | any (`intVarInAst` v0) vars0 ->
      error $ "astGather: gather vars in v0: "
              ++ show (vars0, v0)
    (_, (Z, _)) -> astIndex v0 ix0
    (sh, (_, ZI)) -> astKonstN sh v0
    (k :$ sh', (var ::: vars, i1 :. rest1)) ->
      if | not (any (`intVarInAstInt` i1) vars0) ->
           astGatherZOrStepOnly stepOnly sh0 (astIndex v0 (i1 :. ZI))
                                (vars0, rest1)
         | case iN of
             AstIntVar varN' ->
               varN' == varN
               && not (any (varN `intVarInAstInt`) restN)
               && case ( dropShape @(m - 1) sh0
                       , dropShape @(p - 1) (shapeAst v0) ) of
                 (kN :$ _, vkN :$ _) -> kN == vkN
                 _ -> error "impossible pattern needlessly required"
             _ -> False
           -> astGatherZOrStepOnly stepOnly sh0 v0 (varsN, restN)
         | intVarInIndex var ix0 ->
           astGatherCase sh0 v0 (vars0, ix0)
         | any (`intVarInIndex` ix0) vars ->
           astKonst k (astGatherZOrStepOnly stepOnly sh' v0 (vars, ix0))
         | otherwise ->
           astKonstN sh0 (astIndex v0 ix0)
       where
        (restN, iN) = unsnocIndex1 ix0
        (varsN, varN) = unsnocSized1 vars0
    _ ->
      error "astGather: impossible pattern needlessly required"
 where
  astIndex :: forall m' n'. (KnownNat m', KnownNat n')
           => Ast (m' + n') r -> AstIndex m' r -> Ast n' r
  astIndex = if stepOnly then astIndexStep else astIndexZ
  astGatherRec, astGather
    :: forall m' n' p'.
       (KnownNat m', KnownNat p', KnownNat n')
    => ShapeInt (m' + n') -> Ast (p' + n') r
    -> (AstVarList m', AstIndex p' r)
    -> Ast (m' + n') r
  astGatherRec = if stepOnly then AstGatherZ else astGatherZ
  astGather = if stepOnly then astGatherStep else astGatherZ
  -- Note that v4 is in weak head normal form and so can't one-step reduce
  -- and so we don't have to reduce it to expose any top redexes.
  astGatherCase
    :: forall m' n' p'. (KnownNat m', KnownNat p', KnownNat n')
    => ShapeInt (m' + n') -> Ast (p' + n') r -> (AstVarList m', AstIndex p' r)
    -> Ast (m' + n') r
  astGatherCase sh4 v4 (_, ZI) = astKonstN sh4 v4  -- not really possible
  astGatherCase sh4 v4 (vars4, ix4@(i4 :. rest4)) = case v4 of
    AstVar{} -> AstGatherZ sh4 v4 (vars4, ix4)
    AstLet var u v -> AstLet var u (astGatherCase sh4 v (vars4, ix4))
    AstOp opCode args ->
      AstOp opCode (map (\v -> astGatherRec sh4 v (vars4, ix4)) args)
    AstConst{} ->  -- free variables possible, so can't compute the tensor
      AstGatherZ sh4 v4 (vars4, ix4)
    AstConstant (AstPrimalPart v) ->
      astConstant $ AstPrimalPart $ astGatherRec sh4 v (vars4, ix4)
    AstIndexZ v2 ix2 -> case (v2, ix2) of
      (AstFromList{}, i2 :. ZI) -> astGather sh4 v2 (vars4, i2 :. ix4)
      (AstFromVector{}, i2 :. ZI) -> astGather sh4 v2 (vars4, i2 :. ix4)
      _ ->  -- AstVar, AstConst
        AstGatherZ sh4 v4 (vars4, ix4)
    AstSum v ->
      let perm3 = permCycle $ valueOf @p' + 1
          perm4 = permBackCycle $ valueOf @m' + 1
          (sh41, sh42) = splitAt_Shape @m' sh4
          sh5 = appendShape sh41 (lengthAst v :$ sh42)
      in astSum $ astTransposeAsGather perm4  -- TODO: inline and simplify less
         $ astGather sh5 (astTransposeAsGather perm3 v) (vars4, ix4)
             -- TODO: why is simplification not idempotent without AsGather?
    AstConstInt0{} ->
      error "astGather: impossible pattern needlessly required"
    AstScatter{} ->  -- probably nothing can be simplified; a normal form
      AstGatherZ sh4 v4 (vars4, ix4)
    AstFromList l | AstIntConst i <- i4 ->
      astGather sh4 (if length l > i then l !! i else 0) (vars4, rest4)
    AstFromList{} | gatherFromNF vars4 ix4 -> AstGatherZ sh4 v4 (vars4, ix4)
    AstFromList l ->
      let f v = astGatherRec sh4 v (vars4, rest4)
      in astGather sh4 (astFromList $ map f l)
                   (vars4, i4 :. sizedListToIndex (fmap AstIntVar vars4))
    AstFromVector l | AstIntConst i <- i4 ->
      astGather sh4 (if V.length l > i then l V.! i else 0) (vars4, rest4)
    AstFromVector{} | gatherFromNF vars4 ix4 -> AstGatherZ sh4 v4 (vars4, ix4)
    AstFromVector l ->
      let f v = astGatherRec sh4 v (vars4, rest4)
      in astGather sh4 (astFromVector $ V.map f l)
                   (vars4, i4 :. sizedListToIndex (fmap AstIntVar vars4))
    AstKonst _k v -> astGather sh4 v (vars4, rest4)
    AstAppend v w ->
      -- We can't express append as gather, because AstFromList needs
      -- arguments of the same shape, so here we need to inline a lot of code.
      let vlen = AstIntConst $ lengthAst v
          iw = simplifyAstInt (AstIntOp MinusIntOp [i4, vlen])
          v2 = astGatherRec sh4 v (vars4, i4 :. rest4)
          w2 = astGatherRec sh4 w (vars4, iw :. rest4)
      in case simplifyAstBool $ AstRelInt LsOp [i4, vlen] of
        AstBoolConst b -> if b
                          then astGather sh4 v (vars4, i4 :. rest4)
                          else astGather sh4 w (vars4, iw :. rest4)
        b -> astGather sh4 (astFromList [v2, w2])
                       (vars4, AstIntCond b 0 1
                               :. sizedListToIndex (fmap AstIntVar vars4))
    AstSlice i _k v ->
      let ii = simplifyAstInt (AstIntOp PlusIntOp [i4, AstIntConst i])
      in astGather sh4 v (vars4, ii :. rest4)
    AstReverse v ->
      let iRev = simplifyAstInt (AstIntOp MinusIntOp
                                          [AstIntConst (lengthAst v - 1), i4])
      in astGather sh4 v (vars4, iRev :. rest4)
    AstTranspose perm v | valueOf @p' >= length perm ->
      astGather sh4 v (vars4, permutePrefixIndex perm ix4)
    AstTranspose perm v ->
      astGather sh4 (astTransposeAsGather perm v) (vars4, ix4)
    AstReshape sh v ->
      astGather sh4 (astReshapeAsGather sh v) (vars4, ix4)
    AstBuild1{} -> AstGatherZ sh4 v4 (vars4, ix4)
    AstGatherZ @m2 @n2 _sh2 v2 (vars2, ix2) ->
      let subst :: AstIndex m7 r -> AstVarList m7 -> AstInt r -> AstInt r
          subst ix vars i =
            foldr (uncurry substituteAstInt) i
                  (zipSized (indexToSizedList ix) vars)
          composedGather :: p' <= m2 => Ast (m' + n') r
          composedGather =
            let (vars2p, vars22) = splitAt_Sized @p' @(m2 - p') vars2
                ix22 = fmap (subst ix4 vars2p) ix2
            in gcastWith (unsafeCoerce Refl :: m2 + n2 - p' :~: n')
               $ astGather sh4 v2 (appendSized vars4 vars22, ix22)
          assimilatedGather :: m2 <= p' => Ast (m' + n') r
          assimilatedGather =
            let (ix42, ix44) = splitAt_Index @m2 @(p' - m2) ix4
                ix22 = fmap (subst ix42 vars2) ix2
            in gcastWith (unsafeCoerce Refl :: n' + p' - m2 :~: n2)
               $ astGather sh4 v2 (vars4, appendIndex ix22 ix44)
      in case cmpNat (Proxy @p') (Proxy @m2) of
        LTI -> composedGather
        EQI -> assimilatedGather
        GTI -> gcastWith (flipCompare @p' @m2) assimilatedGather
    AstD (AstPrimalPart u) (AstDualPart u') ->
      AstD (AstPrimalPart $ astGatherRec sh4 u (vars4, ix4))
           (AstDualPart $ astGatherRec sh4 u' (vars4, ix4))

gatherFromNF :: forall m p r. (KnownNat m, KnownNat p)
             => AstVarList m -> AstIndex (1 + p) r -> Bool
gatherFromNF _ ZI = error "gatherFromNF: impossible pattern needlessly required"
gatherFromNF vars (i :. rest) = case cmpNat (Proxy @p) (Proxy @m) of
  LTI ->
    let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
        cmp _ = False
        (varsP, varsPM) = splitAt_Sized @p @(m - p) vars
    in all cmp (zipIndex rest (sizedListToIndex (fmap AstIntVar varsP)))
       && not (any (`intVarInAstInt` i) varsPM)
  EQI ->
    let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
        cmp _ = False
    in all cmp (zipIndex rest (sizedListToIndex (fmap AstIntVar vars)))
  GTI -> False

flipCompare :: forall (a :: Nat) b. Compare a b ~ GT => Compare b a :~: LT
flipCompare = unsafeCoerce Refl

astFromDynamic :: forall n r. KnownNat n
               => AstDynamic r -> Ast n r
astFromDynamic AstDynamicDummy = error "astFromDynamic: AstDynamicDummy"
astFromDynamic (AstDynamicPlus u v) =
  AstOp PlusOp [astFromDynamic u, astFromDynamic v]
astFromDynamic (AstDynamicFrom @n2 t) =
  case sameNat (Proxy @n) (Proxy @n2) of
    Just Refl -> t
    _ -> error "astFromDynamic: different rank expected and uncovered"
astFromDynamic (AstDynamicVar @n2 sh var) =
  case sameNat (Proxy @n) (Proxy @n2) of
    Just Refl -> AstVar sh var
    _ -> error "astFromDynamic: different var rank expected and uncovered"

{-
-- TODO: To apply this to astGatherZ. we'd need to take the last variable
-- and the first index element in place of var and i1.
-- If var does not occur in the remaining index elements,
-- this simplification is valid.
--
-- An old blurb:
                  -- a generalization of gatherSimplify needed to simplify more
                  -- or we could run astGather1 repeatedly,
                  -- but even then we can't
                  -- get into fromList, which may simplify or complicate a term,
                  -- and sometimes is not possible without leaving a small
                  -- gather outside
{-
            | intVarInAstInt var i1 ->
                let w :: Ast (1 + n) r
                    w = astIndexZ v2 rest1
                in case gatherSimplify k var w i1 of
                  Just u -> u  -- an extremely simple form found
                    -- for AstGatherZ instead:
                    -- AstGatherZ ... u (initN, rest1)
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
  => Int -> AstVarId -> Ast (1 + n) r -> AstInt r
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
-}

astIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
astIntCond (AstBoolConst b) v w = if b then v else w
astIntCond b v w = AstIntCond b v w

astMinIndex1 :: AstPrimalPart 1 r -> AstInt r
astMinIndex1 = AstMinIndex1

astMaxIndex1 :: AstPrimalPart 1 r -> AstInt r
astMaxIndex1 = AstMaxIndex1


-- * The simplifying bottom-up pass

simplifyAstPrimal
  :: (ShowAstSimplify r, KnownNat n)
  => AstPrimalPart n r -> AstPrimalPart n r
simplifyAstPrimal (AstPrimalPart t) = AstPrimalPart $ simplifyAst t

-- This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexZ.
simplifyAst
  :: (ShowAstSimplify r, KnownNat n)
  => Ast n r -> Ast n r
simplifyAst t = case t of
  AstVar{} -> t
  AstLet var u v -> AstLet var (simplifyAst u) (simplifyAst v)
  AstOp opCode args -> AstOp opCode (map simplifyAst args)
    -- We do not simplify, e.g., addition or multiplication by zero.
    -- There are too many cases and values are often unknown.
  AstConst{} -> t
  AstConstant v -> astConstant (simplifyAstPrimal v)
  AstIndexZ v ix -> astIndexZ (simplifyAst v) (fmap simplifyAstInt ix)
  AstSum v -> astSum (simplifyAst v)
  AstConstInt0 i -> AstConstInt0 $ simplifyAstInt i
  AstScatter sh v (var, ix) ->
    astScatter sh (simplifyAst v) (var, fmap simplifyAstInt ix)
  AstFromList l -> astFromList (map simplifyAst l)
  AstFromVector l -> astFromVector (V.map simplifyAst l)
  AstKonst k v -> astKonst k (simplifyAst v)
  AstAppend x y -> astAppend (simplifyAst x) (simplifyAst y)
  AstSlice i k v -> astSlice i k (simplifyAst v)
  AstReverse v -> astReverse (simplifyAst v)
  AstTranspose perm v ->
    -- The first attempt is for the case of v being a transpose, which would
    -- simplify to a huge gather, but instead we may fuse it at once.
    case astTranspose (simplifyPermutation perm) v of
      AstTranspose perm2 v2 ->  -- no luck, let's try simplifying the argument
        case astTranspose perm2 (simplifyAst v2) of
          AstTranspose perm3 v3 ->  -- nope, let's express all as gather
            astTransposeAsGather perm3 v3
              -- this is expensive, but the only way to guarantee
              -- full simplification
          u -> simplifyAst u
      u -> simplifyAst u
  AstReshape sh v ->
    case astReshape sh v of  -- see above
      AstReshape sh2 v2 ->
        case astReshape sh2 (simplifyAst v2) of
          AstReshape sh3 v3 -> astReshapeAsGather sh3 v3
            -- this is terribly expensive, but the only way to fully simplify
          u -> simplifyAst u
      u -> simplifyAst u
  AstBuild1 k (var, v) -> AstBuild1 k (var, simplifyAst v)
  AstGatherZ sh v (vars, ix) ->
    astGatherZ sh (simplifyAst v) (vars, fmap simplifyAstInt ix)
  AstD u (AstDualPart u') -> AstD (simplifyAstPrimal u)
                                  (AstDualPart $ simplifyAst u')

-- Integer terms need to be simplified, because they are sometimes
-- created by vectorization and can be a deciding factor in whether
-- dual terms can be simplified in turn.
simplifyAstInt :: ShowAstSimplify r
               => AstInt r -> AstInt r
simplifyAstInt t = case t of
  AstIntVar{} -> t
  AstIntOp opCodeInt args ->
    simplifyAstIntOp opCodeInt (map simplifyAstInt args)
  AstIntConst{} -> t
  AstIntFloor v -> AstIntFloor $ simplifyAstPrimal v
    -- Equality of floats is suspect, so no attempt to simplify.
  AstIntCond b a1 a2 -> astIntCond (simplifyAstBool b)
                                   (simplifyAstInt a1)
                                   (simplifyAstInt a2)
  AstMinIndex1 v -> astMinIndex1 $ simplifyAstPrimal v
  AstMaxIndex1 v -> astMaxIndex1 $ simplifyAstPrimal v

simplifyAstBool :: ShowAstSimplify r
                => AstBool r -> AstBool r
simplifyAstBool t = case t of
  AstBoolOp opCodeBool args ->
    simplifyAstBoolOp opCodeBool (map simplifyAstBool args)
  AstBoolConst{} -> t
  AstRel opCodeRel args -> AstRel opCodeRel (map simplifyAstPrimal args)
    -- these are primal part expressions, so never vectorized but potentially
    -- large, so we simplify and ignore them
  AstRelInt opCodeRel args -> AstRelInt opCodeRel (map simplifyAstInt args)
    -- TODO: evaluate if arguments are constants

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right
-- and let's push negation down.
-- Not considered are rules that would require comparing non-constant terms
-- or that would duplicate a non-constant term, as well as most rules
-- informed by inequalities, expressed via max or min, such as
-- max n (signum (abs x)) | n <= 0 --> signum (abs x).
simplifyAstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
simplifyAstIntOp PlusIntOp [AstIntConst u, AstIntConst v] = AstIntConst $ u + v
simplifyAstIntOp PlusIntOp [AstIntConst 0, v] = v
simplifyAstIntOp PlusIntOp [u, AstIntConst 0] = u
simplifyAstIntOp PlusIntOp [ AstIntConst u
                           , AstIntOp PlusIntOp [AstIntConst v, w] ] =
  simplifyAstIntOp PlusIntOp [AstIntConst $ u + v, w]
simplifyAstIntOp PlusIntOp [u, AstIntConst n] =
  simplifyAstIntOp PlusIntOp [AstIntConst n, u]  -- make the constant available
simplifyAstIntOp PlusIntOp [AstIntOp PlusIntOp [u, v], w] =
  simplifyAstIntOp PlusIntOp [u, simplifyAstIntOp PlusIntOp [v, w]]
simplifyAstIntOp
  PlusIntOp [ AstIntOp NegateIntOp [AstIntVar var]
            , AstIntVar var' ] | var == var' = 0
simplifyAstIntOp
  PlusIntOp [ AstIntVar var'
            , AstIntOp NegateIntOp [AstIntVar var] ] | var == var' = 0
simplifyAstIntOp
  PlusIntOp [ AstIntOp RemIntOp [ AstIntOp NegateIntOp [AstIntVar var]
                                , AstIntConst v ]
            , AstIntOp RemIntOp [ AstIntVar var'
                                , AstIntConst v' ] ] | var == var'
                                                       && v == v' = 0
simplifyAstIntOp
  PlusIntOp [ AstIntOp RemIntOp [ AstIntVar var'
                                , AstIntConst v' ]
            , AstIntOp RemIntOp [ AstIntOp NegateIntOp [AstIntVar var]
                                , AstIntConst v ] ] | var == var' && v == v' = 0

simplifyAstIntOp MinusIntOp [u, v] =
  simplifyAstIntOp PlusIntOp [u, simplifyAstIntOp NegateIntOp [v]]

simplifyAstIntOp TimesIntOp [AstIntConst u, AstIntConst v] = AstIntConst $ u * v
simplifyAstIntOp TimesIntOp [AstIntConst 0, _v] = AstIntConst 0
simplifyAstIntOp TimesIntOp [_u, AstIntConst 0] = AstIntConst 0
simplifyAstIntOp TimesIntOp [AstIntConst 1, v] = v
simplifyAstIntOp TimesIntOp [u, AstIntConst 1] = u
simplifyAstIntOp TimesIntOp [ AstIntConst u
                            , AstIntOp TimesIntOp [AstIntConst v, w] ] =
  simplifyAstIntOp TimesIntOp [AstIntConst $ u * v, w]
simplifyAstIntOp TimesIntOp [u, AstIntConst n] =
  simplifyAstIntOp TimesIntOp [AstIntConst n, u]
simplifyAstIntOp TimesIntOp [AstIntOp TimesIntOp [u, v], w] =
  simplifyAstIntOp TimesIntOp [u, simplifyAstIntOp TimesIntOp [v, w]]
simplifyAstIntOp TimesIntOp [AstIntOp PlusIntOp [u, v], w] =
  simplifyAstIntOp PlusIntOp [ simplifyAstIntOp TimesIntOp [u, w]
                             , simplifyAstIntOp TimesIntOp [v, w] ]
simplifyAstIntOp TimesIntOp [u, AstIntOp PlusIntOp [v, w]] =
  simplifyAstIntOp PlusIntOp [ simplifyAstIntOp TimesIntOp [u, v]
                             , simplifyAstIntOp TimesIntOp [u, w] ]

-- With static shapes, the second argument to QuotIntOp and RemIntOp
-- is always a constant, which makes such rules worth including,
-- since they are likely to fire. To help them fire, we avoid changing
-- that constant, if possible, e.g., in rules for NegateIntOp.
simplifyAstIntOp
  TimesIntOp [ AstIntConst v
             , AstIntOp QuotIntOp [AstIntVar var, AstIntConst v'] ] | v == v' =
    simplifyAstIntOp MinusIntOp
                     [ AstIntVar var
                     , AstIntOp RemIntOp [AstIntVar var, AstIntConst v] ]

simplifyAstIntOp NegateIntOp [AstIntConst u] = AstIntConst $ negate u
simplifyAstIntOp NegateIntOp [AstIntOp PlusIntOp [u, v]] =
  simplifyAstIntOp PlusIntOp [ simplifyAstIntOp NegateIntOp [u]
                             , simplifyAstIntOp NegateIntOp [v] ]
simplifyAstIntOp NegateIntOp [AstIntOp TimesIntOp [AstIntConst u, v]] =
  simplifyAstIntOp TimesIntOp [AstIntConst $ negate u, v]
    -- given a choice, prefer to negate a constant
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
simplifyAstIntOp NegateIntOp [AstIntOp QuotIntOp [AstIntConst u, v]] =
  simplifyAstIntOp QuotIntOp [AstIntConst $ negate u, v]
simplifyAstIntOp NegateIntOp [AstIntOp QuotIntOp [u, v]] =
  simplifyAstIntOp QuotIntOp [simplifyAstIntOp NegateIntOp [u], v]
simplifyAstIntOp NegateIntOp [AstIntOp RemIntOp [AstIntConst u, v]] =
  simplifyAstIntOp RemIntOp [AstIntConst $ negate u, v]
simplifyAstIntOp NegateIntOp [AstIntOp RemIntOp [u, v]] =
  simplifyAstIntOp RemIntOp [simplifyAstIntOp NegateIntOp [u], v]

simplifyAstIntOp AbsIntOp [AstIntConst u] = AstIntConst $ abs u
simplifyAstIntOp AbsIntOp [AstIntOp AbsIntOp [u]] = AstIntOp AbsIntOp [u]
simplifyAstIntOp AbsIntOp [AstIntOp NegateIntOp [u]] =
  simplifyAstIntOp AbsIntOp [u]
simplifyAstIntOp SignumIntOp [AstIntConst u] = AstIntConst $ signum u
simplifyAstIntOp SignumIntOp [AstIntOp SignumIntOp [u]] =
  AstIntOp SignumIntOp [u]
simplifyAstIntOp SignumIntOp [AstIntOp AbsIntOp [u]] =
  simplifyAstIntOp AbsIntOp [AstIntOp SignumIntOp [u]]
simplifyAstIntOp MaxIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ max u v
simplifyAstIntOp MaxIntOp [ AstIntConst u
                          , AstIntOp MaxIntOp [AstIntConst v, w] ] =
  simplifyAstIntOp MaxIntOp [AstIntConst $ max u v, w]
simplifyAstIntOp MaxIntOp [u, AstIntConst n] =
  AstIntOp MaxIntOp [AstIntConst n, u]
simplifyAstIntOp MaxIntOp [AstIntOp MaxIntOp [u, v], w] =
  simplifyAstIntOp MaxIntOp [u, simplifyAstIntOp MaxIntOp [v, w]]
simplifyAstIntOp MinIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ min u v
simplifyAstIntOp MinIntOp [ AstIntConst u
                          , AstIntOp MinIntOp [AstIntConst v, w] ] =
  simplifyAstIntOp MinIntOp [AstIntConst $ min u v, w]
simplifyAstIntOp MinIntOp [u, AstIntConst n] =
  AstIntOp MinIntOp [AstIntConst n, u]
simplifyAstIntOp MinIntOp [AstIntOp MinIntOp [u, v], w] =
  simplifyAstIntOp MinIntOp [u, simplifyAstIntOp MinIntOp [v, w]]

simplifyAstIntOp QuotIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ quot u v
simplifyAstIntOp QuotIntOp [AstIntConst 0, _v] = AstIntConst 0
simplifyAstIntOp QuotIntOp [u, AstIntConst 1] = u
simplifyAstIntOp QuotIntOp [ AstIntOp RemIntOp [_u, AstIntConst v]
                           , AstIntConst v' ]
  | v' >= v && v >= 0 = 0
simplifyAstIntOp QuotIntOp [AstIntOp QuotIntOp [u, v], w] =
  simplifyAstIntOp QuotIntOp [u, simplifyAstIntOp TimesIntOp [v, w]]
simplifyAstIntOp QuotIntOp [ AstIntOp TimesIntOp [AstIntConst u, v]
                           , AstIntConst u' ]
    | u == u' = v

simplifyAstIntOp RemIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ rem u v
simplifyAstIntOp RemIntOp [AstIntConst 0, _v] = 0
simplifyAstIntOp RemIntOp [_u, AstIntConst 1] = 0
simplifyAstIntOp RemIntOp [AstIntOp RemIntOp [u, AstIntConst v], AstIntConst v']
  | v' >= v && v >= 0 = AstIntOp RemIntOp [u, AstIntConst v]
simplifyAstIntOp RemIntOp [AstIntOp RemIntOp [u, AstIntConst v], AstIntConst v']
  | rem v v' == 0 && v > 0 = simplifyAstIntOp RemIntOp [u, AstIntConst v']
simplifyAstIntOp RemIntOp [ AstIntOp TimesIntOp [AstIntConst u, _v]
                          , AstIntConst u' ]
  | rem u u' == 0 = 0

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
substituteAst :: (KnownNat n, ShowAstSimplify r)
              => AstInt r -> AstVarId -> Ast n r -> Ast n r
substituteAst i var v1 = simplifyAst $ substitute1Ast i var v1

substituteAstInt :: ShowAstSimplify r
                 => AstInt r -> AstVarId -> AstInt r -> AstInt r
substituteAstInt i var i2 = simplifyAstInt $ substitute1AstInt i var i2

substituteAstBool :: ShowAstSimplify r
                  => AstInt r -> AstVarId -> AstBool r -> AstBool r
substituteAstBool i var b1 = simplifyAstBool $ substitute1AstBool i var b1
