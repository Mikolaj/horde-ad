{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Term-simplifying combinators corresponding to the Ast constructors
-- and complete bottom-up simplifying functions. The former
-- simplify only on the basis of inspecting the roots of their
-- argument term trees. If the arguments get modified as a result,
-- the modified forms are again inspected and may be simplified.
-- The latter traverse and simplify the whole term.
-- The limited simplification via combinators is enough to uncover redexes
-- for the vectorization rules to fire and to undo some of the complication
-- introduced by vectorization. The intention is to leave as much
-- of the original terms provided by the user as possible while making
-- sure everything introduced by vectorization is maximally simplified.
module HordeAd.Core.AstSimplify
  ( simplifyPermutation
  , simplifyStepNonIndex, astIndexStep, astGatherStep
  , astReshape, astTranspose
  , astLet, astSum, astScatter, astFromList, astFromVector, astReplicate
  , astAppend, astSlice, astReverse, astFromDynamic, astConstant, astDomainsLet
  , astIntCond
  , simplifyArtifact6, simplifyAst6, simplifyAstDomains6
  , unletAstDomains6, unletAst6
  , substituteAst, substituteAstDomains, substituteAstInt, substituteAstBool
  ) where

import Prelude

import           Control.Arrow (second)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.EnumMap.Strict as EM
import qualified Data.EnumSet as ES
import           Data.List (dropWhileEnd, mapAccumR)
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
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast
  ( AstBool (AstBoolConst)
  , AstDomains
  , AstInt (AstIntConst, AstIntOp, AstIntVar)
  , AstRanked
  )
import           HordeAd.Core.Ast hiding
  (AstBool (..), AstDomains (..), AstInt (..), AstRanked (..))
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstTools
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorClass
import           HordeAd.Internal.SizedList
import           HordeAd.Internal.TensorOps


-- * Expressing operations as Gather; introduces new variable names

-- We keep AstTranspose terms for as long as possible, because
-- they are small and fuse nicely in many cases. For some forms of indexing
-- and nesting with reshape and gather they don't fuse, which is when
-- this function is invoked.
astTransposeAsGather
  :: forall n r. (KnownNat n, GoodScalar r)
  => Permutation -> AstRanked r n -> AstRanked r n
{-# NOINLINE astTransposeAsGather #-}
astTransposeAsGather perm v = unsafePerformIO $ do
  let p = length perm
  case someNatVal $ toInteger p of
    Just (SomeNat (_proxy :: Proxy p)) -> do
      (vars, ix) <- funToAstIndexIO p id
      let asts :: AstIndex p r
          asts = permutePrefixIndex perm ix
      return $! case cmpNat (Proxy @p) (Proxy @n) of
        EQI -> astGatherZ @p @(n - p)
                          (backpermutePrefixShape perm (shapeAst v)) v
                          (vars, asts)
        LTI -> astGatherZ @p @(n - p)
                          (backpermutePrefixShape perm (shapeAst v)) v
                          (vars, asts)
        _ -> error "astTransposeAsGather: permutation longer than rank"
    Nothing -> error "astTransposeAsGather: impossible someNatVal error"

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
  :: forall p m r. (KnownNat p, KnownNat m, GoodScalar r)
  => ShapeInt m -> AstRanked r p -> AstRanked r m
{-# NOINLINE astReshapeAsGather #-}
astReshapeAsGather shOut v = unsafePerformIO $ do
  (vars, ix) <- funToAstIndexIO (lengthShape shOut) id
  let shIn = shapeAst v
      asts :: AstIndex p r
      asts = let i = toLinearIdx @m @0 shOut ix
             in fmap simplifyAstInt $ fromLinearIdx shIn i
                  -- we generate these, so we simplify
  return $! astGatherZ @m @0 shOut v (vars, asts)


-- * Permutation operations

simplifyPermutation :: Permutation -> Permutation
simplifyPermutation perm =
  map fst $ dropWhileEnd (uncurry (==)) $ zip perm [0 ..]

-- A representation of a cycle backpermutation.
backpermCycle :: Int -> Permutation
backpermCycle 0 = []
backpermCycle 1 = []
backpermCycle n = [k `mod` n | k <- [1 .. n]]

-- A representation of a cycle permutation.
-- TODO: make sure and state if it's reverse to the above and, if not, why.
permCycle :: Int -> Permutation
permCycle 0 = []
permCycle 1 = []
permCycle n = [k `mod` n | k <- [-1, 0 .. n - 2]]


-- * The simplifying combinators

-- This does a single step of simplification of any non-indexing term
-- (many steps if guaranteed net beneficial).
-- AstInt and AstBool terms are simplified fully.
simplifyStepNonIndex
  :: (KnownNat n, GoodScalar r)
  => AstRanked r n -> AstRanked r n
simplifyStepNonIndex t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var u v
  Ast.AstLetADShare{} -> error "simplifyStepNonIndex: AstLetADShare"
  Ast.AstOp{} -> t
  Ast.AstSumOfList{} -> t
  Ast.AstIota -> t
  Ast.AstIndexZ{} -> t
  Ast.AstSum v -> astSum v
  Ast.AstScatter sh v (vars, ix) -> astScatter sh v (vars, ix)
  Ast.AstFromList l -> astFromList l
  Ast.AstFromVector l -> astFromVector l
  Ast.AstReplicate k v -> astReplicate k v
  Ast.AstAppend x y -> astAppend x y
  Ast.AstSlice i k v -> astSlice i k v
  Ast.AstReverse v -> astReverse v
  Ast.AstTranspose perm v -> astTranspose perm v
  Ast.AstReshape sh v -> astReshape sh v
  Ast.AstBuild1{} -> t
  Ast.AstGatherZ _ v0 (Z, ix) -> Ast.AstIndexZ v0 ix
  Ast.AstGatherZ sh v0 (_, ZI) -> astReplicateN sh v0
  Ast.AstGatherZ {} -> t
  Ast.AstConst{} -> t
  Ast.AstConstant v -> astConstant v
  Ast.AstD{} -> t
  Ast.AstLetDomains{} -> t

astLet :: forall n m r. (KnownNat m, KnownNat n, ShowAst r)
       => AstVarId -> AstRanked r n -> AstRanked r m -> AstRanked r m
astLet var u v | astIsSmall u = substitute1Ast (Left u) var v
  -- we use the substitution that does not simplify, which is sad,
  -- because very low hanging fruits may be left hanging, but we
  -- don't want to simplify the whole term; a better alternative
  -- would be a substitution that only simplifies the touched
  -- terms with one step lookahead, as normally when vectorizing
astLet var u v@(Ast.AstVar _ var2) =
  if var2 == var
  then case sameNat (Proxy @n) (Proxy @m) of
    Just Refl -> u
    _ -> error "astLet: rank mismatch"
  else v
astLet var u v = Ast.AstLet var u v

astIndexZ
  :: forall m n r.
     (KnownNat m, KnownNat n, GoodScalar r)
  => AstRanked r (m + n) -> AstIndex m r -> AstRanked r n
astIndexZ = astIndexZOrStepOnly False

astIndexStep
  :: forall m n r.
     (KnownNat m, KnownNat n, GoodScalar r)
  => AstRanked r (m + n) -> AstIndex m r -> AstRanked r n
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
     (KnownNat m, KnownNat n, GoodScalar r)
  => Bool -> AstRanked r (m + n) -> AstIndex m r -> AstRanked r n
astIndexZOrStepOnly stepOnly (Ast.AstIndexZ v ix) ZI =
  astIndexZOrStepOnly stepOnly v ix  -- no non-indexing constructor yet revealed
astIndexZOrStepOnly _ v0 ZI = v0
astIndexZOrStepOnly stepOnly v0 ix@(i1 :. (rest1 :: AstIndex m1 r)) =
 let astIndexRec, astIndex :: forall m' n'. (KnownNat m', KnownNat n')
                           => AstRanked r (m' + n') -> AstIndex m' r
                           -> AstRanked r n'
     astIndexRec vRec ZI = vRec
     astIndexRec vRec ixRec =
       if stepOnly then Ast.AstIndexZ vRec ixRec else astIndexZ vRec ixRec
     astIndex = if stepOnly then astIndexStep else astIndexZ
     astGather
       :: forall m' n' p'.
          (KnownNat m', KnownNat p', KnownNat n')
       => ShapeInt (m' + n') -> AstRanked r (p' + n')
       -> (AstVarList m', AstIndex p' r)
       -> AstRanked r (m' + n')
     astGather = if stepOnly then astGatherStep else astGatherZ
 in case v0 of
  Ast.AstVar{} -> Ast.AstIndexZ v0 ix
  Ast.AstLet var u v -> astLet var u (astIndexRec v ix)
  Ast.AstLetADShare{} -> error "astIndexZOrStepOnly: AstLetADShare"
  Ast.AstOp opCode args ->
    Ast.AstOp opCode (map (`astIndexRec` ix) args)
  Ast.AstSumOfList args ->
    Ast.AstSumOfList (map (`astIndexRec` ix) args)
  Ast.AstIota | AstIntConst i <- i1 -> case sameNat (Proxy @m) (Proxy @1) of
    Just Refl -> Ast.AstConst $ OR.scalar $ fromIntegral i
    _ -> error "astIndex: AstIota: impossible pattern needlessly required"
  Ast.AstIota -> Ast.AstIndexZ v0 ix
  Ast.AstIndexZ v ix2 ->
    astIndex v (appendIndex ix2 ix)
  Ast.AstSum v ->  -- almost neutral; transposition is likely to fuse away
    let perm3 = backpermCycle $ valueOf @m + 1
    in astSum $ astIndex (astTranspose perm3 v) ix
  Ast.AstScatter (_ :$ sh) v (vars, AstIntVar var5 :. ix2)
    | AstIntVar var6 <- i1, var6 == var5 ->
        astIndex (unsafeCoerce $ astScatter sh v (vars, ix2)) rest1
  Ast.AstScatter (_ :$ sh) v (vars, AstIntConst i5 :. ix2)
    | AstIntConst i6 <- i1 ->
        if i6 == i5
        then astIndex (unsafeCoerce $ astScatter sh v (vars, ix2)) rest1
          -- see analogous code in astGatherCase for how a million
          -- type applications is still not enough to make it type-check
        else astIndex (astReplicateN @(m1 + n) @0 (unsafeCoerce sh) 0) rest1
  -- AstScatter sh v (vars2, ZI) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZI)
  Ast.AstScatter{} ->  -- a normal form
    Ast.AstIndexZ v0 ix
  Ast.AstFromList l | AstIntConst i <- i1 ->
    astIndex (if 0 <= i && i < length l then l !! i else 0) rest1
  Ast.AstFromList{} | ZI <- rest1 ->  -- normal form
    Ast.AstIndexZ v0 ix
  Ast.AstFromList l ->
    Ast.AstIndexZ (astFromList $ map (`astIndexRec` rest1) l)
                  (singletonIndex i1)
  Ast.AstFromVector l | AstIntConst i <- i1 ->
    astIndex (if 0 <= i && i < V.length l then l V.! i else 0) rest1
  Ast.AstFromVector{} | ZI <- rest1 ->  -- normal form
    Ast.AstIndexZ v0 ix
  Ast.AstFromVector l ->
    Ast.AstIndexZ (astFromVector $ V.map (`astIndexRec` rest1) l)
                  (singletonIndex i1)
  Ast.AstReplicate _k v ->
    astIndex v rest1
  Ast.AstAppend{} ->
    {- We can't do the following, because we can get, e.g., division
       by zero in the index in the counterfactual branch and sometimes
       all branches are materialized. Similarly for gather of append
       and see the TODO there.
    let vlen = AstIntConst $ lengthAst v
        ix2 = simplifyAstInt (AstIntOp MinusIntOp [i1, vlen]) :. rest1
    in case simplifyAstBool $ AstRelInt LsOp [i1, vlen] of
      AstBoolConst b -> if b then astIndex v ix else astIndex w ix2
      bExpr -> astCond bExpr (astIndexRec v ix) (astIndexRec w ix2)
    -}
    Ast.AstIndexZ v0 ix
  Ast.AstSlice i _k v ->
    let ii = simplifyAstInt (AstIntOp PlusIntOp [i1, AstIntConst i])
    in astIndex v (ii :. rest1)
  Ast.AstReverse v ->
    let iRev = simplifyAstInt (AstIntOp MinusIntOp
                                        [AstIntConst (lengthAst v - 1), i1])
    in astIndex v (iRev :. rest1)
  Ast.AstTranspose perm v | valueOf @m >= length perm ->
    astIndex v (permutePrefixIndex perm ix)
  Ast.AstTranspose perm v ->
    astIndex (astTransposeAsGather perm v) ix
  Ast.AstReshape sh v ->
    astIndex (astReshapeAsGather sh v) ix
  Ast.AstBuild1 _n2 (var2, v) ->
    astIndex (substituteAst @0 (Right i1) var2 v) rest1
  Ast.AstGatherZ _sh v (Z, ix2) -> astIndex v (appendIndex ix2 ix)
  Ast.AstGatherZ (_ :$ sh') v (var2 ::: vars, ix2) ->
    let ix3 = fmap (substituteAstInt @0 (Right i1) var2) ix2
        w :: AstRanked r (m1 + n)
        w = unsafeCoerce $ astGather sh' v (vars, ix3)
    in astIndex @m1 @n w rest1
  Ast.AstGatherZ{} ->
    error "astIndex: AstGatherZ: impossible pattern needlessly required"
  Ast.AstConst t ->
    let unConst (AstIntConst i) (Just l) = Just $ fromIntegral i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> Ast.AstConst $ tindexZR t $ listToIndex ixInt
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndexZ v0 ix
  Ast.AstConstant (AstPrimalPart v) ->
    astConstant $ AstPrimalPart $ astIndex v ix
  Ast.AstD (AstPrimalPart u) (AstDualPart u') ->
    Ast.AstD (AstPrimalPart $ astIndexRec u ix)
             (AstDualPart $ astIndexRec u' ix)
  Ast.AstLetDomains vars l v ->
    Ast.AstLetDomains vars l (astIndexRec v ix)

astSum :: (KnownNat n, GoodScalar r)
       => AstRanked r (1 + n) -> AstRanked r n
astSum (Ast.AstConst t) = Ast.AstConst $ tsumR t
astSum (Ast.AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astSum v
astSum (Ast.AstReverse v) = Ast.AstSum v
astSum v = Ast.AstSum v

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatter :: forall m n p r.
              (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
           => ShapeInt (p + n) -> AstRanked r (m + n)
           -> (AstVarList m, AstIndex p r)
           -> AstRanked r (p + n)
astScatter _sh v (Z, ZI) = v
astScatter sh v (var ::: vars, ix) | not $ var `intVarInIndex` ix =
  astScatter sh (astSum v) (vars, ix)
-- astScatter sh v (Z, ix) = update (tzero sh 0) ix v
astScatter sh (Ast.AstConstant (AstPrimalPart v)) (vars, ix) =
  astConstant $ AstPrimalPart $ astScatter sh v (vars, ix)
astScatter sh v (vars, ix) = Ast.AstScatter sh v (vars, ix)

astFromList :: (KnownNat n, GoodScalar r)
            => [AstRanked r n] -> AstRanked r (1 + n)
astFromList [a] = astReplicate 1 a
astFromList l =
  let unConstant (Ast.AstConstant (AstPrimalPart t)) = Just t
      unConstant _ = Nothing
  in case mapM unConstant l of
    Just [] -> Ast.AstFromList []
    Just l2 ->
      astConstant $ AstPrimalPart $ astFromList l2
    Nothing ->
      let unConst (Ast.AstConst t) = Just t
          unConst _ = Nothing
      in case mapM unConst l of
        Just l3 -> Ast.AstConst $ tfromListR l3
        Nothing -> Ast.AstFromList l

astFromVector :: (KnownNat n, GoodScalar r)
              => Data.Vector.Vector (AstRanked r n) -> AstRanked r (1 + n)
astFromVector v | V.length v == 1 = astReplicate 1 (v V.! 0)
astFromVector l =
  let unConstant (Ast.AstConstant (AstPrimalPart t)) = Just t
      unConstant _ = Nothing
  in case V.mapM unConstant l of
    Just l2 | V.null l2 -> Ast.AstFromVector l2
    Just l2 ->
      astConstant $ AstPrimalPart $ astFromVector l2
    Nothing ->
      let unConst (Ast.AstConst t) = Just t
          unConst _ = Nothing
      in case V.mapM unConst l of
        Just l3 -> Ast.AstConst $ tfromVectorR l3
        Nothing -> Ast.AstFromVector l

astReplicate :: (KnownNat n, GoodScalar r)
         => Int -> AstRanked r n -> AstRanked r (1 + n)
astReplicate k = \case
-- This allocates a big tensor too early, while it's still possible
-- a projection reduces this away. The cost to AD should not be too high.
-- This would also hide AstReplicate from hacks that recover tmatmul2, etc.
--  Ast.AstConst t -> Ast.AstConst $ treplicateR k t
  Ast.AstConstant (AstPrimalPart v) ->
    astConstant $ AstPrimalPart $ astReplicate k v
{- TODO: these may be counterproductive with many gathers and their fusion
         though these let transpose cancel out with each other sometimes
         (instead we should try to cancel out inside replicate and only move
          if they don't)
-}
  Ast.AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astReplicate k v
{- see the previous comment
  Ast.AstReshape sh v ->
    AstReshape (k :$ sh) $ astReplicate k v
-}
  v -> Ast.AstReplicate k v

astReplicateN :: forall n p r. (KnownNat n, KnownNat p, GoodScalar r)
          => ShapeInt (n + p) -> AstRanked r p -> AstRanked r (n + p)
astReplicateN sh =
  let go :: KnownNat n' => ShapeInt n' -> AstRanked r p -> AstRanked r (n' + p)
      go ZS v = v
      go (k :$ sh') v = astReplicate k $ go sh' v
  in go (takeShape sh)

astAppend :: (KnownNat n, GoodScalar r)
          => AstRanked r (1 + n) -> AstRanked r (1 + n) -> AstRanked r (1 + n)
astAppend (Ast.AstConst u) (Ast.AstConst v) = Ast.AstConst $ tappendR u v
astAppend (Ast.AstConstant (AstPrimalPart u))
          (Ast.AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astAppend u v
astAppend (Ast.AstFromList l1) (Ast.AstFromList l2) = astFromList $ l1 ++ l2
astAppend (Ast.AstFromList l1) (Ast.AstFromVector l2) =
  astFromList $ l1 ++ V.toList l2
astAppend (Ast.AstFromVector l1) (Ast.AstFromList l2) =
  astFromList $ V.toList l1 ++ l2
astAppend (Ast.AstFromVector l1) (Ast.AstFromVector l2) =
  astFromVector $ l1 V.++ l2
astAppend u v = Ast.AstAppend u v

astSlice :: forall n r. (KnownNat n, GoodScalar r)
         => Int -> Int -> AstRanked r (1 + n) -> AstRanked r (1 + n)
astSlice i k (Ast.AstConst t) = Ast.AstConst $ tsliceR i k t
astSlice i k (Ast.AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astSlice i k v
astSlice 0 k v | k == lengthAst v = v
astSlice i k (Ast.AstFromList l) = astFromList $ take k (drop i l)
astSlice i k (Ast.AstFromVector l) = astFromVector $ V.take k (V.drop i l)
astSlice _i k (Ast.AstReplicate _k2 v) = astReplicate k v
astSlice i k w@(Ast.AstAppend (u :: AstRanked r (1 + n)) (v :: AstRanked r (1 + n))) =
  -- GHC 9.2.7 -- 9.6.1 with the plugins demand so much verbiage ^^^
  -- It seems this is caused by only having (1 + n) in the type
  -- signature and + not being injective. Quite hopless in cases
  -- where swithing to n -> n is not an option. Perhaps it fixes itself
  -- whenever n -> n is wrong, because a function that requires 1 + n
  -- is used.
  let ulen = lengthAst u
  in if | i + k <= ulen -> astSlice @n i k u
        | i >= ulen -> astSlice @n (i - ulen) k v
        | otherwise -> Ast.AstSlice @n i k w  -- cheap iff fits in one
astSlice i k (Ast.AstGatherZ (_ :$ sh') v (var ::: vars, ix)) =
  let ivar = AstIntOp PlusIntOp [AstIntVar var, AstIntConst i]
      ix2 = fmap (substituteAstInt @0 (Right ivar) var) ix
  in astGatherZ (k :$ sh') v (var ::: vars, ix2)
astSlice i k v = Ast.AstSlice i k v

astReverse :: forall n r. (KnownNat n, GoodScalar r)
           => AstRanked r (1 + n) -> AstRanked r (1 + n)
astReverse (Ast.AstConst t) = Ast.AstConst $ treverseR t
astReverse (Ast.AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astReverse v
astReverse (Ast.AstFromList l) = Ast.AstFromList $ reverse l
astReverse (Ast.AstFromVector l) = Ast.AstFromVector $ V.reverse l
astReverse (Ast.AstReplicate k v) = Ast.AstReplicate k v
astReverse (Ast.AstReverse v) = v
astReverse (Ast.AstGatherZ sh@(k :$ _) v (var ::: vars, ix)) =
  let ivar = AstIntOp Ast.MinusIntOp [AstIntConst k, AstIntVar var]
      ix2 = fmap (substituteAstInt @0 (Right ivar) var) ix
  in astGatherZ sh v (var ::: vars, ix2)
astReverse v = Ast.AstReverse v

isVar :: AstRanked r n -> Bool
isVar Ast.AstVar{} = True
isVar _ = False

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTranspose :: forall n r. (GoodScalar r, KnownNat n)
             => Permutation -> AstRanked r n -> AstRanked r n
astTranspose perm0 t0 = case (perm0, t0) of
  ([], t) -> t
  (perm, Ast.AstLet var u v) -> astLet var u (astTranspose perm v)
  (perm, Ast.AstOp opCode args@[Ast.AstTranspose{}, _]) ->
    Ast.AstOp opCode (map (astTranspose perm) args)
  (perm, Ast.AstOp opCode args@[_,  Ast.AstTranspose{}]) ->
    Ast.AstOp opCode (map (astTranspose perm) args)
  (perm, Ast.AstOp opCode args) | not (length args > 1 || all isVar args) ->
    Ast.AstOp opCode (map (astTranspose perm) args)
  (perm, Ast.AstSumOfList args) | not (length args > 1 || all isVar args) ->
    Ast.AstSumOfList (map (astTranspose perm) args)
  (perm, Ast.AstSum v) -> astSum $ astTranspose (0 : map succ perm) v
  (perm, Ast.AstScatter @_ @_ @p sh v (vars, ix)) | length perm <= valueOf @p ->
    astScatter (backpermutePrefixShape perm sh) v
               (vars, backpermutePrefixIndex perm ix)
  (perm1, Ast.AstTranspose perm2 t) ->
    let perm2Matched =
          perm2
          ++ take (length perm1 - length perm2) (drop (length perm2) [0 ..])
        perm = simplifyPermutation $ backpermutePrefixList perm1 perm2Matched
    in astTranspose perm t
      -- this rule can be disabled to test fusion of gathers
  -- Note that the following would be wrong, becuase transpose really
  -- changes the linearisation order, while reshape only modifies indexing:
  -- (perm, AstReshape sh v) -> astReshape (backpermutePrefixShape perm sh) v
  (perm, Ast.AstGatherZ @m sh v (vars, ix)) | length perm <= valueOf @m ->
    astGatherZ (backpermutePrefixShape perm sh) v
               (backpermutePrefixSized perm vars, ix)
  (perm, Ast.AstConst t) ->
    Ast.AstConst $ ttransposeR perm t
  (perm, Ast.AstConstant (AstPrimalPart v)) ->
    astConstant $ AstPrimalPart $ astTranspose perm v
  (perm, u) -> Ast.AstTranspose perm u

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshape :: forall p m r. (KnownNat p, KnownNat m, GoodScalar r)
           => ShapeInt m -> AstRanked r p -> AstRanked r m
astReshape shOut (Ast.AstLet var u v) = astLet var u (astReshape shOut v)
astReshape shOut (Ast.AstOp opCode args@[Ast.AstReshape{}, _]) =
  Ast.AstOp opCode (map (astReshape shOut) args)
astReshape shOut (Ast.AstOp opCode args@[_, Ast.AstReshape{}]) =
  Ast.AstOp opCode (map (astReshape shOut) args)
astReshape shOut (Ast.AstOp opCode args)
  | not (length args > 1 || all isVar args) =
      Ast.AstOp opCode (map (astReshape shOut) args)
astReshape shOut (Ast.AstSumOfList args)
  | not (length args > 1 || all isVar args) =
      Ast.AstSumOfList (map (astReshape shOut) args)
astReshape shOut (Ast.AstReshape _ v) = astReshape shOut v
  -- this rule can be disabled to test fusion of gathers
astReshape shOut (Ast.AstConst t) =
  Ast.AstConst $ OR.reshape (shapeToList shOut) t
astReshape shOut (Ast.AstConstant (AstPrimalPart v)) =
  astConstant $ AstPrimalPart $ astReshape shOut v
astReshape shOut v =
  let shIn = shapeAst v
  in case sameNat (Proxy @p) (Proxy @m) of
    Just Refl -> if shIn == shOut
                 then v
                 else Ast.AstReshape shOut v
    _ -> Ast.AstReshape shOut v

astGatherZ
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, GoodScalar r)
  => ShapeInt (m + n) -> AstRanked r (p + n) -> (AstVarList m, AstIndex p r)
  -> AstRanked r (m + n)
astGatherZ = astGatherZOrStepOnly False

astGatherStep
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, GoodScalar r)
  => ShapeInt (m + n) -> AstRanked r (p + n) -> (AstVarList m, AstIndex p r)
  -> AstRanked r (m + n)
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
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, GoodScalar r)
  => Bool -> ShapeInt (m + n) -> AstRanked r (p + n) -> (AstVarList m, AstIndex p r)
  -> AstRanked r (m + n)
astGatherZOrStepOnly stepOnly sh0 v0 (vars0, ix0) =
  case (sh0, (vars0, ix0)) of
    _ | any (`intVarInAst` v0) vars0 ->
      error $ "astGather: gather vars in v0: "
              ++ show (vars0, v0)
    (_, (Z, _)) -> astIndex v0 ix0
    (sh, (_, ZI)) -> astReplicateN sh v0
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
         | otherwise ->
           astReplicate k (astGatherZOrStepOnly stepOnly sh' v0 (vars, ix0))
       where
        (restN, iN) = unsnocIndex1 ix0
        (varsN, varN) = unsnocSized1 vars0
    _ ->
      error "astGather: impossible pattern needlessly required"
 where
  astIndex :: forall m' n'. (KnownNat m', KnownNat n')
           => AstRanked r (m' + n') -> AstIndex m' r -> AstRanked r n'
  astIndex = if stepOnly then astIndexStep else astIndexZ
  astGatherRec, astGather
    :: forall m' n' p'.
       (KnownNat m', KnownNat p', KnownNat n')
    => ShapeInt (m' + n') -> AstRanked r (p' + n')
    -> (AstVarList m', AstIndex p' r)
    -> AstRanked r (m' + n')
  astGatherRec = if stepOnly then Ast.AstGatherZ else astGatherZ
  astGather = if stepOnly then astGatherStep else astGatherZ
  -- Note that v4 is in weak head normal form and so can't one-step reduce
  -- and so we don't have to reduce it to expose any top redexes.
  astGatherCase
    :: forall m' n' p'. (KnownNat m', KnownNat p', KnownNat n')
    => ShapeInt (m' + n') -> AstRanked r (p' + n')
    -> (AstVarList m', AstIndex p' r)
    -> AstRanked r (m' + n')
  astGatherCase sh4 v4 (_, ZI) = astReplicateN sh4 v4  -- not really possible
  astGatherCase sh4 v4 ( vars4
                       , ix4@(i4 :. (rest4 :: AstIndex p1' r)) ) = case v4 of
    Ast.AstVar{} -> Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstLet var u v -> astLet var u (astGatherCase sh4 v (vars4, ix4))
    Ast.AstLetADShare{} -> error "astGatherCase: AstLetADShare"
    Ast.AstOp opCode args | not (length args > 1 || all isVar args) ->
      -- Going inside AstOp usually makes the term more expensive to interpret
      -- and reverting this transformation requires comparing many arguments,
      -- so it's not practical.
      Ast.AstOp opCode (map (\v -> astGatherRec sh4 v (vars4, ix4)) args)
    Ast.AstOp{} -> Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstSumOfList args | not (length args > 1 || all isVar args) ->
      Ast.AstSumOfList (map (\v -> astGatherRec sh4 v (vars4, ix4)) args)
    Ast.AstSumOfList{} -> Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstIota | AstIntConst i <- i4 -> case sameNat (Proxy @p') (Proxy @1) of
      Just Refl -> astReplicateN sh4 $ Ast.AstConst $ OR.scalar $ fromIntegral i
      _ -> error "astGather: AstIota: impossible pattern needlessly required"
    Ast.AstIota ->  -- probably nothing can be simplified; a normal form
      Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstIndexZ v2 ix2 -> case (v2, ix2) of
      (Ast.AstFromList{}, i2 :. ZI) -> astGather sh4 v2 (vars4, i2 :. ix4)
      (Ast.AstFromVector{}, i2 :. ZI) -> astGather sh4 v2 (vars4, i2 :. ix4)
      _ ->  -- AstVar, AstConst
        Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstSum v ->
      let perm3 = backpermCycle $ valueOf @p' + 1
          perm4 = permCycle $ valueOf @m' + 1
          (sh41, sh42) = splitAt_Shape @m' sh4
          sh5 = appendShape sh41 (lengthAst v :$ sh42)
      in astSum $ astTransposeAsGather perm4  -- TODO: inline and simplify less
         $ astGather sh5 (astTransposeAsGather perm3 v) (vars4, ix4)
             -- TODO: why is simplification not idempotent without AsGather?
    Ast.AstScatter (_ :$ sh) v (vars, AstIntVar var5 :. ix2)
      | AstIntVar var6 <- i4, var6 == var5 ->
          astGather sh4 (unsafeCoerce $ astScatter sh v (vars, ix2))
                        (vars4, rest4)
    Ast.AstScatter @m4 @n4 (_ :$ sh) v (vars, AstIntConst i5
                                              :. (ix2 :: AstIndex p1 r))
      | AstIntConst i6 <- i4 ->
          if i6 == i5
          then astGather @m' @n' @p1' sh4
                         (unsafeCoerce
                          $ astScatter @m4 @n4 @p1 sh v (vars, ix2))
                         (vars4, rest4)
          else astGather sh4 (astReplicateN @(p1' + n') @0 (unsafeCoerce sh) 0)
                         (vars4, rest4)
    Ast.AstScatter{} ->  -- a normal form
      Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstFromList l | AstIntConst i <- i4 ->
      astGather sh4 (if 0 <= i && i < length l then l !! i else 0)
                    (vars4, rest4)
    Ast.AstFromList{} | gatherFromNF vars4 ix4 ->
      Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstFromList l ->
      let f v = astGatherRec sh4 v (vars4, rest4)
          (varsFresh, ixFresh) = funToAstIndex @m' id
          subst i =
            foldr (uncurry (substituteAstInt @0)) i
                  (zipSized (fmap Right $ indexToSizedList ixFresh) vars4)
          i5 = subst i4
      in astGather sh4 (astFromList $ map f l) (varsFresh, i5 :. ixFresh)
    Ast.AstFromVector l | AstIntConst i <- i4 ->
      astGather sh4 (if 0 <= i && i < V.length l then l V.! i else 0)
                    (vars4, rest4)
    Ast.AstFromVector{} | gatherFromNF vars4 ix4 ->
      Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstFromVector l ->
      let f v = astGatherRec sh4 v (vars4, rest4)
          (varsFresh, ixFresh) = funToAstIndex @m' id
          subst i =
            foldr (uncurry (substituteAstInt @0)) i
                  (zipSized (fmap Right $ indexToSizedList ixFresh) vars4)
          i5 = subst i4
     in astGather sh4 (astFromVector $ V.map f l) (varsFresh, i5 :. ixFresh)
    Ast.AstReplicate _k v -> astGather sh4 v (vars4, rest4)
    Ast.AstAppend{} ->
      {- This is wrong, see astIndexZOrStepOnly:
         We can't express append as gather, because AstFromList needs
         arguments of the same shape, so here we need to inline a lot of code.
         TODO: The normal form is not acceptable, because fusion is halted
         and can't get inside AstAppend, unlike inside AstFromList.
         Let's see if we can do the same trick as with AstFromList
         and get all the remaining indexes inside AstGatherZ.
         BTW, probably fusion is halted also due to NF with AstScatter.
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
      -}
      Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstSlice i _k v ->
      let ii = simplifyAstInt (AstIntOp Ast.PlusIntOp
                                            [i4, AstIntConst i])
      in astGather sh4 v (vars4, ii :. rest4)
    Ast.AstReverse v ->
      let iRev = simplifyAstInt (AstIntOp Ast.MinusIntOp
                                   [AstIntConst (lengthAst v - 1), i4])
      in astGather sh4 v (vars4, iRev :. rest4)
    Ast.AstTranspose perm v | valueOf @p' >= length perm ->
      astGather sh4 v (vars4, permutePrefixIndex perm ix4)
    Ast.AstTranspose perm v ->
      astGather sh4 (astTransposeAsGather perm v) (vars4, ix4)
    Ast.AstReshape sh v ->
      astGather sh4 (astReshapeAsGather sh v) (vars4, ix4)
    Ast.AstBuild1{} -> Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstGatherZ @m2 @n2 _sh2 v2 (vars2, ix2) ->
      let subst :: AstIndex m7 r -> AstVarList m7 -> AstInt r -> AstInt r
          subst ix vars i =
            foldr (uncurry (substituteAstInt @0)) i
                  (zipSized (fmap Right $ indexToSizedList ix) vars)
          composedGather :: p' <= m2 => AstRanked r (m' + n')
          composedGather =
            let (vars2p, vars22) = splitAt_Sized @p' @(m2 - p') vars2
                ix22 = fmap (subst ix4 vars2p) ix2
            in gcastWith (unsafeCoerce Refl :: m2 + n2 - p' :~: n')
               $ astGather sh4 v2 (appendSized vars4 vars22, ix22)
          assimilatedGather :: m2 <= p' => AstRanked r (m' + n')
          assimilatedGather =
            let (ix42, ix44) = splitAt_Index @m2 @(p' - m2) ix4
                ix22 = fmap (subst ix42 vars2) ix2
            in gcastWith (unsafeCoerce Refl :: n' + p' - m2 :~: n2)
               $ astGather sh4 v2 (vars4, appendIndex ix22 ix44)
      in case cmpNat (Proxy @p') (Proxy @m2) of
        LTI -> composedGather
        EQI -> assimilatedGather
        GTI -> gcastWith (flipCompare @p' @m2) assimilatedGather
    Ast.AstConst{} ->  -- free variables possible, so can't compute the tensor
      Ast.AstGatherZ sh4 v4 (vars4, ix4)
    Ast.AstConstant (AstPrimalPart v) ->
      astConstant $ AstPrimalPart $ astGather sh4 v (vars4, ix4)
    Ast.AstD (AstPrimalPart u) (AstDualPart u') ->
      let (varsFresh, ixFresh) = funToAstIndex @m' id
          subst i =
            foldr (uncurry (substituteAstInt @0)) i
                  (zipSized (fmap Right $ indexToSizedList ixFresh) vars4)
          ix5 = fmap subst ix4
      in Ast.AstD (AstPrimalPart $ astGatherRec sh4 u (vars4, ix4))
                  (AstDualPart $ astGatherRec sh4 u' (varsFresh, ix5))
    Ast.AstLetDomains vars l v ->
      Ast.AstLetDomains vars l (astGatherCase sh4 v (vars4, ix4))

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
               => AstDynamic r -> AstRanked r n
astFromDynamic (AstDynamic Ast.AstIota) = error "astFromDynamic: dummy"
astFromDynamic (AstDynamic @n2 v) =
  case sameNat (Proxy @n) (Proxy @n2) of
    Just Refl -> v
    _ -> error "astFromDynamic: different rank expected and uncovered"

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
                let w :: AstRanked r (1 + n)
                    w = astIndexZ v2 rest1
                in case gatherSimplify k var w i1 of
                  Just u -> u  -- an extremely simple form found
                    -- for AstGatherZ instead:
                    -- AstGatherZ ... u (initN, rest1)
                  Nothing ->
                    AstGather1 k v2 (var, ix2)
                    -- we didn't really need it anyway
            | otherwise -> astReplicate k (AstIndexZ v2 ix2)
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
  :: (KnownNat n, ShowAst r)
  => Int -> AstVarId -> AstRanked r (1 + n) -> AstInt r
  -> Maybe (AstRanked r (1 + n))
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
astSliceLax :: (KnownNat n, ShowAst r)
            => Int -> Int -> AstRanked r (1 + n) -> AstRanked r (1 + n)
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

astConstant :: AstPrimalPart r n -> AstRanked r n
astConstant (AstPrimalPart (Ast.AstConstant t)) = astConstant t
astConstant v = Ast.AstConstant v

astDomainsLet :: forall n r. (KnownNat n, ShowAst r)
              => AstVarId -> AstRanked r n -> AstDomains r -> AstDomains r
astDomainsLet var u v | astIsSmall u = substitute1AstDomains (Left u) var v
  -- we use the substitution that does not simplify, which is sad,
  -- because very low hanging fruits may be left hanging, but we
  -- don't want to simplify the whole term; a better alternative
  -- would be a substitution that only simplifies the touched
  -- terms with one step lookahead, as normally when vectorizing
astDomainsLet var u v = Ast.AstDomainsLet var u v

astIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
astIntCond (AstBoolConst b) v w = if b then v else w
astIntCond b v w = Ast.AstIntCond b v w

astMinIndex1 :: AstPrimalPart r 1 -> AstInt r
astMinIndex1 = Ast.AstMinIndex1

astMaxIndex1 :: AstPrimalPart r 1 -> AstInt r
astMaxIndex1 = Ast.AstMaxIndex1


-- * Simplification pass applied to code with eliminated nested lets

simplifyArtifact6 :: (GoodScalar r, KnownNat n)
                  => ADAstArtifact6 n r -> ADAstArtifact6 n r
simplifyArtifact6 (vars, gradient, primal) =
  (vars, simplifyAstDomains6 gradient, simplifyAst6 primal)

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyAst6
  :: (GoodScalar r, KnownNat n)
  => AstRanked r n -> AstRanked r n
simplifyAst6 = simplifyAst . snd . inlineAst () EM.empty . simplifyAst

simplifyAstDomains6
  :: GoodScalar r
  => AstDomains r -> AstDomains r
simplifyAstDomains6 =
  simplifyAstDomains . snd . inlineAstDomains () EM.empty . simplifyAstDomains


-- * The pass inlining lets with the bottom-up strategy

type AstEnv a = ()  -- unused for now

type AstMemo = EM.EnumMap AstVarId Int

inlineAstPrimal
  :: forall n r. (GoodScalar r, KnownNat n)
  => AstEnv r -> AstMemo
  -> AstPrimalPart r n -> (AstMemo, AstPrimalPart r n)
inlineAstPrimal env memo (AstPrimalPart v1) =
  second AstPrimalPart $ inlineAst env memo v1

inlineAstDual
  :: forall n r. (GoodScalar r, KnownNat n)
  => AstEnv r -> AstMemo
  -> AstDualPart r n -> (AstMemo, AstDualPart r n)
inlineAstDual env memo (AstDualPart v1) =
  second AstDualPart $ inlineAst env memo v1

inlineAst
  :: forall n r. (GoodScalar r, KnownNat n)
  => AstEnv r -> AstMemo
  -> AstRanked r n -> (AstMemo, AstRanked r n)
inlineAst env memo v0 = case v0 of
  Ast.AstVar _ var -> let f Nothing = Just 1
                          f (Just count) = Just $ succ count
                      in (EM.alter f var memo, v0)
  Ast.AstLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let (memo1, v2) = inlineAst env memo v
        memo1NoVar = EM.delete var memo1
        (memo2, u2) = inlineAst env memo1NoVar u
    in case EM.findWithDefault 0 var memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substitute1Ast (Left u2) var v2)
        -- this is the substitution that doesn't simplify, so that
        -- inlining can be applied with and without simplification
      count | astIsSmall u ->
        let (memoU0, u0) = inlineAst env EM.empty u
            memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
                      -- u is small, so the union is fast
        in (memo3, substitute1Ast (Left u0) var v2)
      _ -> (memo2, Ast.AstLet var u2 v2)
  Ast.AstLetADShare{} -> error "inlineAst: AstLetADShare"
  Ast.AstOp opCode args ->
    let (memo2, args2) = mapAccumR (inlineAst env) memo args
    in (memo2, Ast.AstOp opCode args2)
  Ast.AstSumOfList args ->
    let (memo2, args2) = mapAccumR (inlineAst env) memo args
    in (memo2, Ast.AstSumOfList args2)
  Ast.AstIota -> (memo, v0)
  Ast.AstIndexZ v ix ->
    let (memo1, v2) = inlineAst env memo v
        (memo2, ix2) = mapAccumR (inlineAstInt env) memo1 (indexToList ix)
    in (memo2, Ast.AstIndexZ v2 (listToIndex ix2))
  Ast.AstSum v -> second Ast.AstSum (inlineAst env memo v)
  Ast.AstScatter sh v (vars, ix) ->
    let (memo1, v2) = inlineAst env memo v
        (memoI0, ix2) = mapAccumR (inlineAstInt env) EM.empty (indexToList ix)
        count = sizeShape sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatter sh v2 (vars, listToIndex ix2))
  Ast.AstFromList l ->
    let (memo2, l2) = mapAccumR (inlineAst env) memo l
    in (memo2, Ast.AstFromList l2)
  Ast.AstFromVector l ->
    let (memo2, l2) = mapAccumR (inlineAst env) memo (V.toList l)
    in (memo2, Ast.AstFromVector $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstReplicate k v -> second (Ast.AstReplicate k) (inlineAst env memo v)
  Ast.AstAppend x y ->
    let (memo1, t1) = inlineAst env memo x
        (memo2, t2) = inlineAst env memo1 y
    in (memo2, Ast.AstAppend t1 t2)
  Ast.AstSlice i k v -> second (Ast.AstSlice i k) (inlineAst env memo v)
  Ast.AstReverse v -> second Ast.AstReverse (inlineAst env memo v)
  Ast.AstTranspose perm v ->
    second (Ast.AstTranspose perm) $ inlineAst env memo v
  Ast.AstReshape sh v -> second (Ast.AstReshape sh) (inlineAst env memo v)
  Ast.AstBuild1 k (var, v) ->
    let (memoV0, v2) = inlineAst env EM.empty v
        memo1 = EM.unionWith (\c1 c0 -> c1 + k * c0) memo memoV0
    in (memo1, Ast.AstBuild1 k (var, v2))
  Ast.AstGatherZ sh v (vars, ix) ->
    let (memo1, v2) = inlineAst env memo v
        (memoI0, ix2) = mapAccumR (inlineAstInt env) EM.empty (indexToList ix)
        count = sizeShape sh
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGatherZ sh v2 (vars, listToIndex ix2))
  Ast.AstConst{} -> (memo, v0)
  Ast.AstConstant a -> second Ast.AstConstant $ inlineAstPrimal env memo a
  Ast.AstD u u' ->
    let (memo1, t1) = inlineAstPrimal env memo u
        (memo2, t2) = inlineAstDual env memo1 u'
    in (memo2, Ast.AstD t1 t2)
  Ast.AstLetDomains vars l v ->  -- TODO: actually inline
    let (memo1, l2) = inlineAstDomains env memo l
        (memo2, v2) = inlineAst env memo1 v
    in (memo2, Ast.AstLetDomains vars l2 v2)

inlineAstDynamic
  :: GoodScalar r
  => AstEnv r -> AstMemo
  -> AstDynamic r -> (AstMemo, AstDynamic r)
inlineAstDynamic env memo = \case
  AstDynamic w -> second AstDynamic $ inlineAst env memo w

inlineAstDomains
  :: GoodScalar r
  => AstEnv r -> AstMemo
  -> AstDomains r -> (AstMemo, AstDomains r)
inlineAstDomains env memo v0 = case v0 of
  Ast.AstDomains l ->
    second Ast.AstDomains $ mapAccumR (inlineAstDynamic env) memo l
  Ast.AstDomainsLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let (memo1, v2) = inlineAstDomains env memo v
        memo1NoVar = EM.delete var memo1
        (memo2, u2) = inlineAst env memo1NoVar u
    in case EM.findWithDefault 0 var memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substitute1AstDomains (Left u2) var v2)
        -- this is the substitution that doesn't simplify, so that
        -- inlining can be applied with and without simplification
      count | astIsSmall u ->
        let (memoU0, u0) = inlineAst env EM.empty u
        in ( EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
               -- u is small, so the union is fast
           , substitute1AstDomains (Left u0) var v2 )
      _ -> (memo2, Ast.AstDomainsLet var u2 v2)

inlineAstInt :: GoodScalar r
             => AstEnv r -> AstMemo
             -> AstInt r -> (AstMemo, AstInt r)
inlineAstInt env memo v0 = case v0 of
  AstIntVar{} -> (memo, v0)
  AstIntOp opCodeInt args ->
    let (memo2, args2) = mapAccumR (inlineAstInt env) memo args
    in (memo2, AstIntOp opCodeInt args2)
  AstIntConst{} -> (memo, v0)
  Ast.AstIntFloor v -> second Ast.AstIntFloor $ inlineAstPrimal env memo v
  Ast.AstIntCond b a2 a3 ->
    -- This is the only place where our inlining may increase code size
    -- by enlarging both branches due to not considering number of syntactic
    -- occurences, but only dynamic occurences. Tensor expressions
    -- in integer conditionals are problematic and special enough
    -- that we can let it be until problems are encountered in the wild.
    -- See https://github.com/VMatthijs/CHAD/blob/main/src/Count.hs#L88-L152.
    let (memo1, b1) = inlineAstBool env memo b
        (memoA2, t2) = inlineAstInt env EM.empty a2
        (memoA3, t3) = inlineAstInt env EM.empty a3
        memo4 = EM.unionWith max memoA2 memoA3
        memo5 = EM.unionWith (+) memo1 memo4
    in (memo5, Ast.AstIntCond b1 t2 t3)
  Ast.AstMinIndex1 v -> second Ast.AstMinIndex1 $ inlineAstPrimal env memo v
  Ast.AstMaxIndex1 v -> second Ast.AstMaxIndex1 $ inlineAstPrimal env memo v

inlineAstBool :: forall r. GoodScalar r
              => AstEnv r -> AstMemo
              -> AstBool r -> (AstMemo, AstBool r)
inlineAstBool env memo v0 = case v0 of
  Ast.AstBoolOp opCodeBool args ->
    let (memo2, args2) = mapAccumR (inlineAstBool env) memo args
    in (memo2, Ast.AstBoolOp opCodeBool args2)
  AstBoolConst{} -> (memo, v0)
  Ast.AstRel @n opCodeRel args ->
    let (memo2, args2) =  mapAccumR (inlineAstPrimal env) memo args
    in (memo2, Ast.AstRel opCodeRel args2)
  Ast.AstRelInt opCodeRel args ->
    let (memo2, args2) = mapAccumR (inlineAstInt env) memo args
    in (memo2, Ast.AstRelInt opCodeRel args2)


-- * The pass eliminating nested lets bottom-up

data UnletEnv r = UnletEnv
  { unletSet     :: ES.EnumSet AstVarId
  , unletADShare :: ADShare r }

emptyUnletEnv :: ADShare r -> UnletEnv r
emptyUnletEnv l = UnletEnv ES.empty l

unletAst6
  :: (GoodScalar r, KnownNat n)
  => ADShare r -> AstRanked r n -> AstRanked r n
unletAst6 l t = unletAst (emptyUnletEnv l)
                $ bindsToLet t (assocsADShare l)

unletAstDomains6
  :: GoodScalar r
  => [(AstVarId, AstDynamic r)] -> ADShare r -> AstDomains r
  -> AstDomains r
unletAstDomains6 astBindings l t =
  unletAstDomains (emptyUnletEnv l)
  $ bindsToDomainsLet (bindsToDomainsLet t astBindings) (assocsADShare l)

-- TODO: if a nested let is alone, eliminate the nesting let instead;
-- this probably requires many passes though
unletAstPrimal
  :: (GoodScalar r, KnownNat n)
  => UnletEnv r -> AstPrimalPart r n -> AstPrimalPart r n
unletAstPrimal env (AstPrimalPart t) = AstPrimalPart $ unletAst env t

unletAst
  :: (GoodScalar r, KnownNat n)
  => UnletEnv r -> AstRanked r n -> AstRanked r n
unletAst env t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v ->
    -- This optimization is sound, because there is no mechanism
    -- that would nest lets with the same variable (e.g., our lets always
    -- bind fresh variables at creation time and we never substitute
    -- a term into the same term). If that changes, let's refresh
    -- let variables whenever substituting into let bodies.
    -- See the same assumption in AstInterpret.
    if var `ES.member` unletSet env
    then unletAst env v
    else let env2 = env {unletSet = ES.insert var (unletSet env)}
         in Ast.AstLet var (unletAst env u) (unletAst env2 v)
  Ast.AstLetADShare l v ->
    let lassocs = subtractADShare l $ unletADShare env
          -- potentially prevents quadratic cost induced by tletWrap
          -- duplicating the global ADShare; may induce overhead when
          -- the same lets are verified for removal twice, in subtractADShare
          -- and via unletAst, but if many lets can be eliminated,
          -- subtractADShare does it much faster
    in unletAst env $ bindsToLet v lassocs
  Ast.AstOp opCode args -> Ast.AstOp opCode (map (unletAst env) args)
  Ast.AstSumOfList args -> Ast.AstSumOfList (map (unletAst env) args)
  Ast.AstIota -> t
  Ast.AstIndexZ v ix ->
    Ast.AstIndexZ (unletAst env v) (fmap (unletAstInt env) ix)
  Ast.AstSum v -> Ast.AstSum (unletAst env v)
  Ast.AstScatter sh v (var, ix) ->
    Ast.AstScatter sh (unletAst env v) (var, fmap (unletAstInt env) ix)
  Ast.AstFromList l -> Ast.AstFromList (map (unletAst env) l)
  Ast.AstFromVector l -> Ast.AstFromVector (V.map (unletAst env) l)
  Ast.AstReplicate k v -> Ast.AstReplicate k (unletAst env v)
  Ast.AstAppend x y -> Ast.AstAppend (unletAst env x) (unletAst env y)
  Ast.AstSlice i k v -> Ast.AstSlice i k (unletAst env v)
  Ast.AstReverse v -> Ast.AstReverse (unletAst env v)
  Ast.AstTranspose perm v -> Ast.AstTranspose perm (unletAst env v)
  Ast.AstReshape sh v -> Ast.AstReshape sh (unletAst env v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, unletAst env v)
  Ast.AstGatherZ sh v (vars, ix) ->
    Ast.AstGatherZ sh (unletAst env v) (vars, fmap (unletAstInt env) ix)
  Ast.AstConst{} -> t
  Ast.AstConstant v -> Ast.AstConstant (unletAstPrimal env v)
  Ast.AstD u (AstDualPart u') -> Ast.AstD (unletAstPrimal env u)
                                  (AstDualPart $ unletAst env u')
  Ast.AstLetDomains vars l v ->
    let env2 = env {unletSet = unletSet env
                               `ES.union` ES.fromList (V.toList vars)}
    in Ast.AstLetDomains vars (unletAstDomains env l) (unletAst env2 v)

unletAstDynamic
  :: GoodScalar r
  => UnletEnv r -> AstDynamic r -> AstDynamic r
unletAstDynamic env (AstDynamic u) = AstDynamic $ unletAst env u

unletAstDomains
  :: GoodScalar r
  => UnletEnv r -> AstDomains r -> AstDomains r
unletAstDomains env = \case
  Ast.AstDomains l -> Ast.AstDomains $ V.map (unletAstDynamic env) l
  Ast.AstDomainsLet var u v ->
    if var `ES.member` unletSet env
    then unletAstDomains env v
    else let env2 = env {unletSet = ES.insert var (unletSet env)}
         in Ast.AstDomainsLet var (unletAst env u)
                                  (unletAstDomains env2 v)

-- Integer terms need to be simplified, because they are sometimes
-- created by vectorization and can be a deciding factor in whether
-- a tensor terms can be simplified in turn.
unletAstInt :: GoodScalar r
            => UnletEnv r -> AstInt r -> AstInt r
unletAstInt env t = case t of
  AstIntVar{} -> t
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt (map (unletAstInt env) args)
  AstIntConst{} -> t
  Ast.AstIntFloor v -> Ast.AstIntFloor $ unletAstPrimal env v
  Ast.AstIntCond b a1 a2 ->
    Ast.AstIntCond
      (unletAstBool env b) (unletAstInt env a1) (unletAstInt env a2)
  Ast.AstMinIndex1 v -> Ast.AstMinIndex1 $ unletAstPrimal env v
  Ast.AstMaxIndex1 v -> Ast.AstMaxIndex1 $ unletAstPrimal env v

unletAstBool :: GoodScalar r
             => UnletEnv r -> AstBool r -> AstBool r
unletAstBool env t = case t of
  Ast.AstBoolOp opCodeBool args ->
    Ast.AstBoolOp opCodeBool (map (unletAstBool env) args)
  AstBoolConst{} -> t
  Ast.AstRel opCodeRel args ->
    Ast.AstRel opCodeRel (map (unletAstPrimal env) args)
  Ast.AstRelInt opCodeRel args ->
    Ast.AstRelInt opCodeRel (map (unletAstInt env) args)


-- * The simplifying bottom-up pass

simplifyAstPrimal
  :: (GoodScalar r, KnownNat n)
  => AstPrimalPart r n -> AstPrimalPart r n
simplifyAstPrimal (AstPrimalPart t) = AstPrimalPart $ simplifyAst t

-- This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexZ.
simplifyAst
  :: (GoodScalar r, KnownNat n)
  => AstRanked r n -> AstRanked r n
simplifyAst t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)
  Ast.AstLetADShare{} -> error "simplifyAst: AstLetADShare"
  Ast.AstOp opCode args -> Ast.AstOp opCode (map simplifyAst args)
  Ast.AstSumOfList args -> Ast.AstSumOfList (map simplifyAst args)
    -- We do not simplify, e.g., addition or multiplication by zero.
    -- There are too many cases and values are often unknown.
  Ast.AstIota -> t
  Ast.AstIndexZ v ix -> astIndexZ (simplifyAst v) (fmap simplifyAstInt ix)
  Ast.AstSum v -> astSum (simplifyAst v)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (simplifyAst v) (var, fmap simplifyAstInt ix)
  Ast.AstFromList l -> astFromList (map simplifyAst l)
  Ast.AstFromVector l -> astFromVector (V.map simplifyAst l)
  Ast.AstReplicate k v -> astReplicate k (simplifyAst v)
  Ast.AstAppend x y -> astAppend (simplifyAst x) (simplifyAst y)
  Ast.AstSlice i k v -> astSlice i k (simplifyAst v)
  Ast.AstReverse v -> astReverse (simplifyAst v)
  Ast.AstTranspose perm v ->
    -- The first attempt is for the case of v being a transpose, which would
    -- simplify to a huge gather, but instead we may fuse it at once
    -- or leave it to be executed via changing only the strides.
    let perm1 = simplifyPermutation perm
    in case astTranspose perm1 v of
      Ast.AstTranspose perm2 v2 | perm2 == perm1 ->
        -- no luck, let's try simplifying the argument
        case astTranspose perm2 (simplifyAst v2) of
          u@(Ast.AstTranspose _ Ast.AstVar{}) -> u  -- normal form
          u@(Ast.AstTranspose _ (Ast.AstOp _ args))
            | length args > 1 || all isVar args -> u  -- normal form
          u@(Ast.AstTranspose _ (Ast.AstSumOfList args))
            | length args > 1 || all isVar args -> u  -- normal form
          u@(Ast.AstTranspose _ Ast.AstScatter{}) -> u  -- normal form
          u@(Ast.AstTranspose _ Ast.AstReplicate{}) -> u  -- normal form
          Ast.AstTranspose perm3 v3 ->  -- not nf, let's express all as gather
            astTransposeAsGather perm3 v3
              -- this is expensive, but the only way to guarantee
              -- full simplification
          u -> simplifyAst u
      u -> simplifyAst u
  Ast.AstReshape sh v ->
    case astReshape sh v of  -- see above
      Ast.AstReshape sh2 v2 ->
        case astReshape sh2 (simplifyAst v2) of
          u@(Ast.AstReshape _ Ast.AstVar{}) -> u  -- normal form
          u@(Ast.AstReshape _ (Ast.AstOp _ args))
            | length args > 1 || all isVar args -> u
              -- normal form, because gather doesn't go inside such AstOp either
          u@(Ast.AstReshape _ (Ast.AstSumOfList args))
            | length args > 1 || all isVar args -> u  -- normal form
          u@(Ast.AstReshape _ Ast.AstScatter{}) -> u  -- normal form
          -- Not a normal form, because often AstReshape scan be eliminated:
          -- u@(Ast.AstReshape _ Ast.AstReplicate{}) -> u  -- normal form
          Ast.AstReshape sh3 v3 -> astReshapeAsGather sh3 v3
            -- this is terribly expensive, but the only way to fully simplify
          u -> simplifyAst u
      u -> simplifyAst u
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, simplifyAst v)
  Ast.AstGatherZ sh v (vars, ix) ->
    astGatherZ sh (simplifyAst v) (vars, fmap simplifyAstInt ix)
  Ast.AstConst{} -> t
  Ast.AstConstant v -> astConstant (simplifyAstPrimal v)
  Ast.AstD u (AstDualPart u') -> Ast.AstD (simplifyAstPrimal u)
                                  (AstDualPart $ simplifyAst u')
  Ast.AstLetDomains vars l v ->
    Ast.AstLetDomains vars (simplifyAstDomains l) (simplifyAst v)

simplifyAstDynamic
  :: GoodScalar r
  => AstDynamic r -> AstDynamic r
simplifyAstDynamic (AstDynamic u) = AstDynamic $ simplifyAst u

simplifyAstDomains
  :: GoodScalar r
  => AstDomains r -> AstDomains r
simplifyAstDomains = \case
  Ast.AstDomains l -> Ast.AstDomains $ V.map simplifyAstDynamic l
  Ast.AstDomainsLet var u v ->
    astDomainsLet var (simplifyAst u) (simplifyAstDomains v)

-- Integer terms need to be simplified, because they are sometimes
-- created by vectorization and can be a deciding factor in whether
-- a tensor terms can be simplified in turn.
simplifyAstInt :: GoodScalar r
               => AstInt r -> AstInt r
simplifyAstInt t = case t of
  AstIntVar{} -> t
  AstIntOp opCodeInt args ->
    simplifyAstIntOp opCodeInt (map simplifyAstInt args)
  AstIntConst{} -> t
  Ast.AstIntFloor v -> Ast.AstIntFloor $ simplifyAstPrimal v
    -- Equality of floats is suspect, so no attempt to simplify.
  Ast.AstIntCond b a1 a2 ->
    astIntCond (simplifyAstBool b) (simplifyAstInt a1) (simplifyAstInt a2)
  Ast.AstMinIndex1 v -> astMinIndex1 $ simplifyAstPrimal v
  Ast.AstMaxIndex1 v -> astMaxIndex1 $ simplifyAstPrimal v

simplifyAstBool :: GoodScalar r
                => AstBool r -> AstBool r
simplifyAstBool t = case t of
  Ast.AstBoolOp opCodeBool args ->
    simplifyAstBoolOp opCodeBool (map simplifyAstBool args)
  AstBoolConst{} -> t
  Ast.AstRel opCodeRel args -> Ast.AstRel opCodeRel (map simplifyAstPrimal args)
    -- these expressions potentially represent large tensors that are
    -- expensive to compute even when constant, so we simplify and ignore them,
    -- because computation should be done on GPU, not on CPU when simplifying;
    -- we'd need a flag to control how much we pre-compute
  Ast.AstRelInt opCodeRel args ->
    simplifyRelIntOp opCodeRel (map simplifyAstInt args)

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
simplifyAstBoolOp opCodeBool arg = Ast.AstBoolOp opCodeBool arg

simplifyRelIntOp :: OpCodeRel -> [AstInt r] -> AstBool r
simplifyRelIntOp EqOp [AstIntConst u, AstIntConst v] = AstBoolConst $ u == v
simplifyRelIntOp NeqOp [AstIntConst u, AstIntConst v] = AstBoolConst $ u /= v
simplifyRelIntOp LeqOp [AstIntConst u, AstIntConst v] = AstBoolConst $ u <= v
simplifyRelIntOp GeqOp [AstIntConst u, AstIntConst v] = AstBoolConst $ u >= v
simplifyRelIntOp LsOp [AstIntConst u, AstIntConst v] = AstBoolConst $ u < v
simplifyRelIntOp GtOp [AstIntConst u, AstIntConst v] = AstBoolConst $ u > v
simplifyRelIntOp EqOp [AstIntVar u, AstIntVar v] | u == v = AstBoolConst True
simplifyRelIntOp LeqOp [AstIntVar u, AstIntVar v] | u == v = AstBoolConst True
simplifyRelIntOp GeqOp [AstIntVar u, AstIntVar v] | u == v = AstBoolConst True
simplifyRelIntOp NeqOp [AstIntVar u, AstIntVar v] | u == v = AstBoolConst False
simplifyRelIntOp LsOp [AstIntVar u, AstIntVar v] | u == v = AstBoolConst False
simplifyRelIntOp GtOp [AstIntVar u, AstIntVar v] | u == v = AstBoolConst False
simplifyRelIntOp opCodeRel arg = Ast.AstRelInt opCodeRel arg

-- We have to simplify after substitution or simplifying is not idempotent.
substituteAst :: forall m n r. (GoodScalar r, KnownNat m, KnownNat n)
              => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstRanked r n
              -> AstRanked r n
substituteAst i var v1 = simplifyAst $ substitute1Ast i var v1

substituteAstDomains
  :: (GoodScalar r, KnownNat m)
  => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstDomains r
  -> AstDomains r
substituteAstDomains i var v1 =
  simplifyAstDomains $ substitute1AstDomains i var v1

substituteAstInt :: forall m r. (GoodScalar r, KnownNat m)
                 => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstInt r
                 -> AstInt r
substituteAstInt i var i2 = simplifyAstInt $ substitute1AstInt i var i2

substituteAstBool :: forall m r. (GoodScalar r, KnownNat m)
                  => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstBool r
                  -> AstBool r
substituteAstBool i var b1 = simplifyAstBool $ substitute1AstBool i var b1
