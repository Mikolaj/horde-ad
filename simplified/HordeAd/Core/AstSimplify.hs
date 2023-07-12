{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
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
  , simplifyStepNonIndex, simplifyStepNonIndexS, astIndexStep, astGatherStep
  , astIndexStepS, astGatherStepS
  , astReshape, astTranspose, astReshapeS, astTransposeS
  , astLet, astSum, astScatter, astFromList, astFromVector, astReplicate
  , astAppend, astSlice, astSliceS, astReverse, astFromDynamic, astFromDynamicS
  , astDomainsLet, astCond
  , simplifyArtifact6, simplifyArtifact6S
  , simplifyAstPrimal6, simplifyAst6, simplifyAstPrimal6S, simplifyAst6S
  , simplifyAstDomains6
  , unletAstDomains6, unletAst6, unletAst6S
  , substituteAstPrimal, substituteAst, substituteAstDomains
  , substituteAstBool, substituteAstS
  , astLetS, astSumS, astScatterS, astFromListS, astFromVectorS, astReplicateS
  , astAppendS, astReverseS
  , astDomainsLetS, astCondS
  ) where

import Prelude

import           Control.Arrow (second)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import qualified Data.EnumSet as ES
import           Data.Int (Int64)
import           Data.List (dropWhileEnd, foldl1', mapAccumR)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
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
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast
  ( AstBool (AstBoolConst)
  , AstDomains
  , AstRanked (AstConst, AstNm, AstSumOfList)
  , AstShaped (AstConstS, AstNmS, AstSumOfListS)
  )
import           HordeAd.Core.Ast hiding
  (AstBool (..), AstDomains (..), AstRanked (..), AstShaped (..))
import qualified HordeAd.Core.Ast as Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstTools
import           HordeAd.Core.ShapedList (ShapedList (..))
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.SizedList
import           HordeAd.Core.TensorOps
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape, trustMeThisIsAPermutation)

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
      let asts :: AstIndex p
          asts = permutePrefixIndex perm ix
      return $! case cmpNat (Proxy @p) (Proxy @n) of
        EQI -> astGatherR @p @(n - p)
                          (backpermutePrefixShape perm (shapeAst v)) v
                          (vars, asts)
        LTI -> astGatherR @p @(n - p)
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
-- Or only extend AstGather and possibly also AstIndex with the extra
-- shIn and shOut arguments. This complicates any code related to
-- AstGather and AstIndex, but often prevents nested reshapes from affecting
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
      asts :: AstIndex p
      asts = let i = toLinearIdx @m @0 shOut ix
             in fmap simplifyAstPrimal $ fromLinearIdx shIn i
                  -- we generate these, so we simplify
  return $! astGatherR @m @0 shOut v (vars, asts)


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
-- (many steps if guaranteed net beneficial). Terms representing integers
-- and and AstBool terms are simplified as much as possible.
simplifyStepNonIndex
  :: (KnownNat n, GoodScalar r)
  => AstRanked r n -> AstRanked r n
simplifyStepNonIndex t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var u v
  Ast.AstLetADShare{} -> error "simplifyStepNonIndex: AstLetADShare"
  AstNm{} -> t
  Ast.AstOp{} -> t
  Ast.AstOpIntegral{} -> t
  AstSumOfList l -> astSumOfList l
  Ast.AstIota -> t
  Ast.AstIndex{} -> t
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
  Ast.AstGather _ v0 (Z, ix) -> Ast.AstIndex v0 ix
  Ast.AstGather sh v0 (_, ZI) -> astReplicateN sh v0
  Ast.AstGather{} -> t
  Ast.AstCast{} -> t
  Ast.AstSToR{} -> t  -- TODO
  AstConst{} -> t
  Ast.AstConstant{} -> t
  Ast.AstD{} -> t
  Ast.AstLetDomains{} -> t
  Ast.AstFloor{} -> t
  Ast.AstCond a b c -> astCond a b c
  Ast.AstMinIndex{} -> t
  Ast.AstMaxIndex{} -> t

simplifyStepNonIndexS
  :: ()
  => AstShaped r sh -> AstShaped r sh
simplifyStepNonIndexS t = t  -- TODO

astLet :: forall n m r r2. (KnownNat m, KnownNat n, GoodScalar r, GoodScalar r2)
       => AstVarId -> AstRanked r n -> AstRanked r2 m -> AstRanked r2 m
astLet var u v | astIsSmall True u =
  substitute1Ast (SubstitutionPayloadRanked u) var v
  -- we use the substitution that does not simplify, which is sad,
  -- because very low hanging fruits may be left hanging, but we
  -- don't want to simplify the whole term; a better alternative
  -- would be a substitution that only simplifies the touched
  -- terms with one step lookahead, as normally when vectorizing
astLet var u v@(Ast.AstVar _ var2) =
  if var2 == var
  then case sameNat (Proxy @n) (Proxy @m) of
    Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> u
      _ -> error "astLet: type mismatch"
    _ -> error "astLet: rank mismatch"
  else v
astLet var u v = Ast.AstLet var u v

astSumOfList :: (KnownNat n, GoodScalar r)
             => [AstRanked r n] -> AstRanked r n
astSumOfList = foldr1 (+)
  -- TODO: try that and if it helps, define Num (AstRanked r n)
  -- the same as for AstPrimalPart
  -- foldl1' (\i j -> unAstPrimalPart $ AstPrimalPart i + AstPrimalPart j)
  -- also try foldl1' instead of foldlr everywhere

astIndexR
  :: forall m n r.
     (KnownNat m, KnownNat n, GoodScalar r)
  => AstRanked r (m + n) -> AstIndex m -> AstRanked r n
astIndexR = astIndexROrStepOnly False

astIndexStep
  :: forall m n r.
     (KnownNat m, KnownNat n, GoodScalar r)
  => AstRanked r (m + n) -> AstIndex m -> AstRanked r n
astIndexStep v ix = astIndexROrStepOnly True (simplifyStepNonIndex v)
                                             (fmap simplifyAstPrimal ix)

astIndexStepS
  :: forall sh1 sh2 r.
     (OS.Shape sh1, OS.Shape sh2, OS.Shape (sh1 OS.++ sh2))
  => AstShaped r (sh1 OS.++ sh2) -> AstIndexS sh1
  -> AstShaped r sh2
astIndexStepS v ix = Ast.AstIndexS v ix  -- TODO

-- If stepOnly is set, we reduce only as long as needed to reveal
-- a non-indexing constructor or one of the normal forms (one-element
-- indexing applied to AstFromList or AstFromVector or indexing
-- of a term with no possible occurences of Int variables). Otherwise,
-- we simplify exhaustively.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astIndexStep.
astIndexROrStepOnly
  :: forall m n r.
     (KnownNat m, KnownNat n, GoodScalar r)
  => Bool -> AstRanked r (m + n) -> AstIndex m -> AstRanked r n
astIndexROrStepOnly stepOnly (Ast.AstIndex v ix) ZI =
  astIndexROrStepOnly stepOnly v ix  -- no non-indexing constructor yet revealed
astIndexROrStepOnly _ v0 ZI = v0
astIndexROrStepOnly stepOnly v0 ix@(i1 :. (rest1 :: AstIndex m1)) =
 let astIndexRec, astIndex :: forall m' n'. (KnownNat m', KnownNat n')
                           => AstRanked r (m' + n') -> AstIndex m'
                           -> AstRanked r n'
     astIndexRec vRec ZI = vRec
     astIndexRec vRec ixRec =
       if stepOnly then Ast.AstIndex vRec ixRec else astIndexR vRec ixRec
     astIndex = if stepOnly then astIndexStep else astIndexR
     astGather
       :: forall m' n' p'.
          (KnownNat m', KnownNat p', KnownNat n')
       => ShapeInt (m' + n') -> AstRanked r (p' + n')
       -> (AstVarList m', AstIndex p')
       -> AstRanked r (m' + n')
     astGather = if stepOnly then astGatherStep else astGatherR
 in case v0 of
  Ast.AstVar{} -> Ast.AstIndex v0 ix
  Ast.AstLet var u v -> astLet var u (astIndexRec v ix)
  Ast.AstLetADShare{} -> error "astIndexROrStepOnly: AstLetADShare"
  AstNm opCode args ->
    AstNm opCode (map (`astIndexRec` ix) args)
  Ast.AstOp opCode args ->
    Ast.AstOp opCode (map (`astIndexRec` ix) args)
  Ast.AstOpIntegral opCode args ->
    Ast.AstOpIntegral opCode (map (`astIndexRec` ix) args)
  AstSumOfList args ->
    astSumOfList (map (`astIndexRec` ix) args)
  Ast.AstIota | AstIntConst i <- i1 -> case sameNat (Proxy @m) (Proxy @1) of
    Just Refl ->
      -- AstConstant not needed, because when AstIota is introduced
      -- in tfromIndex0, AstConstant is wrapped over it.
      AstConst $ OR.scalar $ fromIntegral i
    _ -> error "astIndex: AstIota: impossible pattern needlessly required"
  Ast.AstIota -> Ast.AstIndex v0 ix
  Ast.AstIndex v ix2 ->
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
        else astIndex (astReplicate0N @(m1 + n) (unsafeCoerce sh) 0) rest1
  -- AstScatter sh v (vars2, ZI) ->
  --   AstScatter sh (astIndex (astTranspose perm3 v) ix) (vars2, ZI)
  Ast.AstScatter{} ->  -- a normal form
    Ast.AstIndex v0 ix
  Ast.AstFromList l | AstIntConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in astIndex (if 0 <= i && i < length l
                then l !! i
                else astReplicate0N @(m1 + n)
                                    (dropShape $ shapeAst v0) 0) rest1
  Ast.AstFromList{} | ZI <- rest1 ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromList l ->
    -- TODO: we need integer let to preserve sharing of ix here and elsewhere:
    Ast.AstIndex (astFromList $ map (`astIndexRec` rest1) l)
                  (singletonIndex i1)
  Ast.AstFromVector l | AstIntConst it <- i1 ->
    let i = fromIntegral $ OR.unScalar it
    in astIndex (if 0 <= i && i < V.length l
                 then l V.! i
                 else astReplicate0N @(m1 + n)
                                     (dropShape $ shapeAst v0) 0) rest1
  Ast.AstFromVector{} | ZI <- rest1 ->  -- normal form
    Ast.AstIndex v0 ix
  Ast.AstFromVector l ->
    Ast.AstIndex (astFromVector $ V.map (`astIndexRec` rest1) l)
                 (singletonIndex i1)
  Ast.AstReplicate _k v ->
    astIndex v rest1
  Ast.AstAppend{} ->
    {- We can't do the following, because we can get, e.g., division
       by zero in the index in the counterfactual branch and sometimes
       all branches are materialized. Similarly for gather of append
       and see the TODO there.
    let vlen = AstIntConst $ lengthAst v
        ix2 = simplifyAst (AstIntOp MinusIntOp [i1, vlen]) :. rest1
    in case simplifyAstBool $ AstRelInt LsOp [i1, vlen] of
      AstBoolConst b -> if b then astIndex v ix else astIndex w ix2
      bExpr -> astCond bExpr (astIndexRec v ix) (astIndexRec w ix2)
    -}
    Ast.AstIndex v0 ix
  Ast.AstSlice i _k v ->
    let ii = simplifyAst (astSumOfList
                           [ unAstPrimalPart i1
                           , AstConst $ OR.scalar $ fromIntegral i ])
    in astIndex v (astPrimalPart ii :. rest1)
  Ast.AstReverse v ->
    let iRev = simplifyAst (AstNm MinusOp
                                  [ AstConst $ OR.scalar
                                    $ fromIntegral (lengthAst v - 1)
                                  , unAstPrimalPart i1 ])
    in astIndex v (astPrimalPart iRev :. rest1)
  Ast.AstTranspose perm v | valueOf @m >= length perm ->
    astIndex v (permutePrefixIndex perm ix)
  Ast.AstTranspose perm v ->
    astIndex (astTransposeAsGather perm v) ix
  Ast.AstReshape sh v ->
    astIndex (astReshapeAsGather sh v) ix
  Ast.AstBuild1 _n2 (var2, v) ->
    astIndex (substituteAst (SubstitutionPayloadInt i1) var2 v) rest1
  Ast.AstGather _sh v (Z, ix2) -> astIndex v (appendIndex ix2 ix)
  Ast.AstGather (_ :$ sh') v (var2 ::: vars, ix2) ->
    -- TODO: we need integer let to preserve sharing while substituting here:
    let ix3 = fmap (substituteAstPrimal (SubstitutionPayloadInt i1) var2) ix2
        w :: AstRanked r (m1 + n)
        w = unsafeCoerce $ astGather sh' v (vars, ix3)
    in astIndex @m1 @n w rest1
  Ast.AstGather{} ->
    error "astIndex: AstGather: impossible pattern needlessly required"
  Ast.AstCast t -> Ast.AstCast $ astIndexROrStepOnly stepOnly t ix  -- TODO
  Ast.AstSToR{} ->  -- TODO
    Ast.AstIndex v0 ix
  AstConst t ->
    let unConst (AstIntConst i) (Just l) = Just $ i : l
        unConst _ _ = Nothing
    in case foldr unConst (Just []) ix of
      Just ixInt -> AstConst $ tindexZR t $ listToIndex
                    $ map OR.unScalar ixInt
        -- TODO: we'd need mapM for Index to keep this rank-typed
      Nothing -> Ast.AstIndex v0 ix
  Ast.AstConstant (AstPrimalPart v) ->
    Ast.AstConstant $ astPrimalPart $ astIndex v ix
  Ast.AstD (AstPrimalPart u) (AstDualPart u') ->
    -- TODO: we need integer let to preserve sharing while substituting here:
    Ast.AstD (astPrimalPart $ astIndexRec u ix)
             (AstDualPart $ astIndexRec u' ix)
  Ast.AstLetDomains vars l v ->
    Ast.AstLetDomains vars l (astIndexRec v ix)
  Ast.AstFloor (AstPrimalPart v) ->
    Ast.AstFloor $ astPrimalPart $ astIndexROrStepOnly stepOnly v ix
  Ast.AstCond b v w -> astCond b (astIndexRec v ix) (astIndexRec w ix)
  Ast.AstMinIndex (AstPrimalPart v) ->
    Ast.AstMinIndex $ astPrimalPart $ astIndexROrStepOnly stepOnly v ix
  Ast.AstMaxIndex (AstPrimalPart v) ->
    Ast.AstMaxIndex $ astPrimalPart $ astIndexROrStepOnly stepOnly v ix

astSum :: (KnownNat n, GoodScalar r)
       => AstRanked r (1 + n) -> AstRanked r n
astSum (AstConst t) = AstConst $ tsumR t
astSum (Ast.AstConstant (AstPrimalPart v)) =
  Ast.AstConstant $ astPrimalPart $ astSum v
astSum (Ast.AstScatter (_ :$ sh) v (vars, _ :. ix)) = astScatter sh v (vars, ix)
astSum (Ast.AstReverse v) = Ast.AstSum v
astSum v = Ast.AstSum v

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatter :: forall m n p r.
              (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
           => ShapeInt (p + n) -> AstRanked r (m + n)
           -> (AstVarList m, AstIndex p)
           -> AstRanked r (p + n)
astScatter _sh v (Z, ZI) = v
astScatter sh v (var ::: vars, ix) | not $ var `intVarInIndex` ix =
  astScatter sh (astSum v) (vars, ix)
-- astScatter sh v (Z, ix) = update (tzero sh 0) ix v
astScatter sh (Ast.AstConstant (AstPrimalPart v)) (vars, ix) =
  Ast.AstConstant $ astPrimalPart $ astScatter sh v (vars, ix)
astScatter sh v (vars, ix) = Ast.AstScatter sh v (vars, ix)

astFromList :: (KnownNat n, GoodScalar r)
            => [AstRanked r n] -> AstRanked r (1 + n)
astFromList [a] = astReplicate 1 a
astFromList l =
  let unConstant (Ast.AstConstant (AstPrimalPart t)) = Just t
      unConstant _ = Nothing
  in case mapM unConstant l of
    Just [] -> Ast.AstFromList []
    Just l2 -> Ast.AstConstant $ astPrimalPart $ astFromList l2
    Nothing ->
      let unConst (AstConst t) = Just t
          unConst _ = Nothing
      in case mapM unConst l of
        Just l3 -> AstConst $ tfromListR l3
        Nothing -> Ast.AstFromList l

astFromVector :: (KnownNat n, GoodScalar r)
              => Data.Vector.Vector (AstRanked r n) -> AstRanked r (1 + n)
astFromVector v | V.length v == 1 = astReplicate 1 (v V.! 0)
astFromVector l =
  let unConstant (Ast.AstConstant (AstPrimalPart t)) = Just t
      unConstant _ = Nothing
  in case V.mapM unConstant l of
    Just l2 | V.null l2 -> Ast.AstFromVector l2
    Just l2 -> Ast.AstConstant $ astPrimalPart $ astFromVector l2
    Nothing ->
      let unConst (AstConst t) = Just t
          unConst _ = Nothing
      in case V.mapM unConst l of
        Just l3 -> AstConst $ tfromVectorR l3
        Nothing -> Ast.AstFromVector l

astReplicate :: (KnownNat n, GoodScalar r)
             => Int -> AstRanked r n -> AstRanked r (1 + n)
astReplicate k = \case
-- This allocates a big tensor too early, while it's still possible
-- a projection reduces this away. The cost to AD should not be too high.
-- This would also hide AstReplicate from hacks that recover tmatmul2, etc.
--  AstConst t -> AstConst $ treplicateR k t
  Ast.AstConstant (AstPrimalPart v) ->
    Ast.AstConstant $ astPrimalPart $ astReplicate k v
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

astReplicate0N :: forall n r. (KnownNat n, GoodScalar r)
               => ShapeInt n -> AstRanked r 0 -> AstRanked r n
astReplicate0N sh =
  let go :: KnownNat n' => ShapeInt n' -> AstRanked r 0 -> AstRanked r n'
      go ZS v = v
      go (k :$ sh') v = astReplicate k $ go sh' v
  in go sh

astAppend :: (KnownNat n, GoodScalar r)
          => AstRanked r (1 + n) -> AstRanked r (1 + n) -> AstRanked r (1 + n)
astAppend (AstConst u) (AstConst v) = AstConst $ tappendR u v
astAppend (Ast.AstConstant (AstPrimalPart u))
          (Ast.AstConstant (AstPrimalPart v)) =
  Ast.AstConstant $ astPrimalPart $ astAppend u v
astAppend (Ast.AstFromList l1) (Ast.AstFromList l2) = astFromList $ l1 ++ l2
astAppend (Ast.AstFromList l1) (Ast.AstFromVector l2) =
  astFromList $ l1 ++ V.toList l2
astAppend (Ast.AstFromVector l1) (Ast.AstFromList l2) =
  astFromList $ V.toList l1 ++ l2
astAppend (Ast.AstFromVector l1) (Ast.AstFromVector l2) =
  astFromVector $ l1 V.++ l2
astAppend u v = Ast.AstAppend u v

astSlice :: forall k r. (KnownNat k, GoodScalar r)
         => Int -> Int -> AstRanked r (1 + k) -> AstRanked r (1 + k)
astSlice i n (AstConst t) = AstConst $ tsliceR i n t
astSlice i n (Ast.AstConstant (AstPrimalPart v)) =
  Ast.AstConstant $ astPrimalPart $ astSlice i n v
astSlice 0 n v | n == lengthAst v = v
astSlice i n (Ast.AstFromList l) = astFromList $ take n (drop i l)
astSlice i n (Ast.AstFromVector l) = astFromVector $ V.take n (V.drop i l)
astSlice _i n (Ast.AstReplicate _n2 v) = astReplicate n v
astSlice i n w@(Ast.AstAppend (u :: AstRanked r (1 + k)) (v :: AstRanked r (1 + k))) =
  -- GHC 9.2.7 -- 9.6.1 with the plugins demand so much verbiage ^^^
  -- It seems this is caused by only having (1 + n) in the type
  -- signature and + not being injective. Quite hopless in cases
  -- where swithing to n -> n is not an option. Perhaps it fixes itself
  -- whenever n -> n is wrong, because a function that requires 1 + n
  -- is used.
  let ulen = lengthAst u
  in if | i + n <= ulen -> astSlice @k i n u
        | i >= ulen -> astSlice @k (i - ulen) n v
        | otherwise -> Ast.AstSlice @k i n w  -- cheap iff fits in one
astSlice i n (Ast.AstGather (_ :$ sh') v (var ::: vars, ix)) =
  let ivar = astPrimalPart
             $ astSumOfList [ Ast.AstVar ZS var
                            , AstConst $ OR.scalar $ fromIntegral i ]
      ix2 = fmap (substituteAstPrimal (SubstitutionPayloadInt ivar) var) ix
  in astGatherR (n :$ sh') v (var ::: vars, ix2)
astSlice i n v = Ast.AstSlice i n v

astSliceS :: forall i n k sh r.
             (KnownNat i, KnownNat k, KnownNat n, OS.Shape sh)
          => AstShaped r (i + n + k ': sh) -> AstShaped r (n ': sh)
astSliceS = Ast.AstSliceS @i  -- TODO

astReverse :: forall n r. (KnownNat n, GoodScalar r)
           => AstRanked r (1 + n) -> AstRanked r (1 + n)
astReverse (AstConst t) = AstConst $ treverseR t
astReverse (Ast.AstConstant (AstPrimalPart v)) =
  Ast.AstConstant $ astPrimalPart $ astReverse v
astReverse (Ast.AstFromList l) = Ast.AstFromList $ reverse l
astReverse (Ast.AstFromVector l) = Ast.AstFromVector $ V.reverse l
astReverse (Ast.AstReplicate k v) = Ast.AstReplicate k v
astReverse (Ast.AstReverse v) = v
astReverse (Ast.AstGather sh@(k :$ _) v (var ::: vars, ix)) =
  let ivar = astPrimalPart
             $ AstNm Ast.MinusOp [ AstConst $ OR.scalar $ fromIntegral k
                                 , Ast.AstVar ZS var ]
      ix2 = fmap (substituteAstPrimal (SubstitutionPayloadInt ivar) var) ix
  in astGatherR sh v (var ::: vars, ix2)
astReverse v = Ast.AstReverse v

isVar :: AstRanked r n -> Bool
isVar Ast.AstVar{} = True
isVar (Ast.AstConstant (AstPrimalPart Ast.AstVar{})) = True
isVar _ = False

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astTransposeAsGather needs to be called in addition
-- if full simplification is required.
astTranspose :: forall n r. (GoodScalar r, KnownNat n)
             => Permutation -> AstRanked r n -> AstRanked r n
astTranspose perm0 t0 = case (perm0, t0) of
  ([], t) -> t
  (perm, Ast.AstLet var u v) -> astLet var u (astTranspose perm v)
  (perm, AstNm opCode args@[Ast.AstTranspose{}, _]) ->
    AstNm opCode (map (astTranspose perm) args)
  (perm, AstNm opCode args@[Ast.AstConstant
                                  (AstPrimalPart Ast.AstTranspose{}), _]) ->
    AstNm opCode (map (astTranspose perm) args)
  (perm, AstNm opCode args@[_, Ast.AstTranspose{}]) ->
    AstNm opCode (map (astTranspose perm) args)
  (perm, AstNm opCode args@[_, Ast.AstConstant
                                     (AstPrimalPart Ast.AstTranspose{})]) ->
    AstNm opCode (map (astTranspose perm) args)
  (perm, AstNm opCode args) | not (length args > 1 || all isVar args) ->
    AstNm opCode (map (astTranspose perm) args)
  (perm, Ast.AstOp opCode args@[Ast.AstTranspose{}, _]) ->
    Ast.AstOp opCode (map (astTranspose perm) args)
  (perm, Ast.AstOp opCode args@[Ast.AstConstant
                                  (AstPrimalPart Ast.AstTranspose{}), _]) ->
    Ast.AstOp opCode (map (astTranspose perm) args)
  (perm, Ast.AstOp opCode args@[_, Ast.AstTranspose{}]) ->
    Ast.AstOp opCode (map (astTranspose perm) args)
  (perm, Ast.AstOp opCode args@[_, Ast.AstConstant
                                     (AstPrimalPart Ast.AstTranspose{})]) ->
    Ast.AstOp opCode (map (astTranspose perm) args)
  (perm, Ast.AstOp opCode args) | not (length args > 1 || all isVar args) ->
    Ast.AstOp opCode (map (astTranspose perm) args)
  (perm, AstSumOfList args) | not (length args > 1 || all isVar args) ->
    astSumOfList (map (astTranspose perm) args)
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
  (perm, Ast.AstGather @m sh v (vars, ix)) | length perm <= valueOf @m ->
    astGatherR (backpermutePrefixShape perm sh) v
               (backpermutePrefixSized perm vars, ix)
  (perm, AstConst t) ->
    AstConst $ ttransposeR perm t
  (perm, Ast.AstConstant (AstPrimalPart v)) ->
    Ast.AstConstant $ astPrimalPart $ astTranspose perm v
  (perm, u) -> Ast.AstTranspose perm u

astTransposeS :: forall perm sh r.
                 ( OS.Permutation perm, OS.Shape perm, OS.Shape sh
                 , KnownNat (OS.Rank sh), OS.Rank perm <= OS.Rank sh )
              => AstShaped r sh -> AstShaped r (OS.Permute perm sh)
astTransposeS = Ast.AstTransposeS @perm

-- Beware, this does not do full simplification, which often requires
-- the gather form, so astReshapeAsGather needs to be called in addition
-- if full simplification is required.
astReshape :: forall p m r. (KnownNat p, KnownNat m, GoodScalar r)
           => ShapeInt m -> AstRanked r p -> AstRanked r m
astReshape shOut (Ast.AstLet var u v) = astLet var u (astReshape shOut v)
astReshape shOut (AstNm opCode args@[Ast.AstReshape{}, _]) =
  AstNm opCode (map (astReshape shOut) args)
astReshape shOut (AstNm opCode
                            args@[Ast.AstConstant
                                    (AstPrimalPart Ast.AstReshape{}), _]) =
  AstNm opCode (map (astReshape shOut) args)
astReshape shOut (AstNm opCode args@[_, Ast.AstReshape{}]) =
  AstNm opCode (map (astReshape shOut) args)
astReshape shOut (AstNm opCode
                            args@[_, Ast.AstConstant
                                       (AstPrimalPart Ast.AstReshape{})]) =
  AstNm opCode (map (astReshape shOut) args)
astReshape shOut (AstNm opCode args)
  | not (length args > 1 || all isVar args) =
      AstNm opCode (map (astReshape shOut) args)
astReshape shOut (Ast.AstOp opCode args@[Ast.AstReshape{}, _]) =
  Ast.AstOp opCode (map (astReshape shOut) args)
astReshape shOut (Ast.AstOp opCode
                            args@[Ast.AstConstant
                                    (AstPrimalPart Ast.AstReshape{}), _]) =
  Ast.AstOp opCode (map (astReshape shOut) args)
astReshape shOut (Ast.AstOp opCode
                            args@[_, Ast.AstConstant
                                       (AstPrimalPart Ast.AstReshape{})]) =
  Ast.AstOp opCode (map (astReshape shOut) args)
astReshape shOut (Ast.AstOp opCode args@[_, Ast.AstReshape{}]) =
  Ast.AstOp opCode (map (astReshape shOut) args)
astReshape shOut (Ast.AstOp opCode args)
  | not (length args > 1 || all isVar args) =
      Ast.AstOp opCode (map (astReshape shOut) args)
astReshape shOut (AstSumOfList args)
  | not (length args > 1 || all isVar args) =
      astSumOfList (map (astReshape shOut) args)
astReshape shOut (Ast.AstReshape _ v) = astReshape shOut v
  -- this rule can be disabled to test fusion of gathers
astReshape shOut (AstConst t) =
  AstConst $ OR.reshape (shapeToList shOut) t
astReshape shOut (Ast.AstConstant (AstPrimalPart v)) =
  Ast.AstConstant $ astPrimalPart $ astReshape shOut v
astReshape shOut v =
  let shIn = shapeAst v
  in case sameNat (Proxy @p) (Proxy @m) of
    Just Refl -> if shIn == shOut
                 then v
                 else Ast.AstReshape shOut v
    _ -> Ast.AstReshape shOut v

astReshapeS :: (OS.Shape sh, OS.Size sh ~ OS.Size sh2)
            => AstShaped r sh -> AstShaped r sh2
astReshapeS = Ast.AstReshapeS  -- TODO

astGatherR
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, GoodScalar r)
  => ShapeInt (m + n) -> AstRanked r (p + n) -> (AstVarList m, AstIndex p)
  -> AstRanked r (m + n)
astGatherR = astGatherROrStepOnly False

astGatherStep
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, GoodScalar r)
  => ShapeInt (m + n) -> AstRanked r (p + n) -> (AstVarList m, AstIndex p)
  -> AstRanked r (m + n)
astGatherStep sh v (vars, ix) =
  astGatherROrStepOnly True sh (simplifyStepNonIndex v)
                            (vars, fmap simplifyAstPrimal ix)

astGatherStepS
  :: forall sh2 p sh r.
     ( OS.Shape sh, OS.Shape sh2
     , OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh) )
  => AstShaped r sh
  -> (AstVarListS sh2, AstIndexS (OS.Take p sh))
  -> AstShaped r (sh2 OS.++ OS.Drop p sh)
astGatherStepS v (vars, ix) = Ast.AstGatherS v (vars, ix)  -- TODO

-- Assumption: vars0 don't not occur in v0. The assumption only holds
-- when newly generated variables are fresh, which is the case as long
-- as resetVarCounter is not used. The assumption makes it easier to spot
-- bugs or corruption, hence we assert it in the code below.
--
-- The v0 term is already at least one step simplified,
-- either from full recursive simplification or from astGatherStep.
astGatherROrStepOnly
  :: forall m n p r. (KnownNat m, KnownNat p, KnownNat n, GoodScalar r)
  => Bool -> ShapeInt (m + n) -> AstRanked r (p + n)
  -> (AstVarList m, AstIndex p)
  -> AstRanked r (m + n)
astGatherROrStepOnly stepOnly sh0 v0 (vars0, ix0) =
  case (sh0, (vars0, ix0)) of
    _ | any (`intVarInAst` v0) vars0 ->
      error $ "astGather: gather vars in v0: "
              ++ show (vars0, v0)
    (_, (Z, _)) -> astIndex v0 ix0
    (sh, (_, ZI)) -> astReplicateN sh v0
    (k :$ sh', (var ::: vars, i1 :. rest1)) ->
      if | not (any (`intVarInAstPrimal` i1) vars0) ->
           astGatherROrStepOnly stepOnly sh0 (astIndex v0 (i1 :. ZI))
                                (vars0, rest1)
         | case iN of
             AstIntVar varN' ->
               varN' == varN
               && not (any (varN `intVarInAstPrimal`) restN)
               && case ( dropShape @(m - 1) sh0
                       , dropShape @(p - 1) (shapeAst v0) ) of
                 (kN :$ _, vkN :$ _) -> kN == vkN
                 _ -> error "impossible pattern needlessly required"
             _ -> False
           -> astGatherROrStepOnly stepOnly sh0 v0 (varsN, restN)
         | intVarInIndex var ix0 ->
           astGatherCase sh0 v0 (vars0, ix0)
         | otherwise ->
           astReplicate k (astGatherROrStepOnly stepOnly sh' v0 (vars, ix0))
       where
        (restN, iN) = unsnocIndex1 ix0
        (varsN, varN) = unsnocSized1 vars0
    _ ->
      error "astGather: impossible pattern needlessly required"
 where
  astIndex :: forall m' n'. (KnownNat m', KnownNat n')
           => AstRanked r (m' + n') -> AstIndex m' -> AstRanked r n'
  astIndex = if stepOnly then astIndexStep else astIndexR
  astGatherRec, astGather
    :: forall m' n' p'.
       (KnownNat m', KnownNat p', KnownNat n')
    => ShapeInt (m' + n') -> AstRanked r (p' + n')
    -> (AstVarList m', AstIndex p')
    -> AstRanked r (m' + n')
  astGatherRec = if stepOnly then Ast.AstGather else astGatherR
  astGather = if stepOnly then astGatherStep else astGatherR
  -- Note that v4 is in weak head normal form and so can't one-step reduce
  -- and so we don't have to reduce it to expose any top redexes.
  astGatherCase
    :: forall m' n' p'. (KnownNat m', KnownNat p', KnownNat n')
    => ShapeInt (m' + n') -> AstRanked r (p' + n')
    -> (AstVarList m', AstIndex p')
    -> AstRanked r (m' + n')
  astGatherCase sh4 v4 (_, ZI) = astReplicateN sh4 v4  -- not really possible
  astGatherCase sh4 v4 ( vars4
                       , ix4@(i4 :. (rest4 :: AstIndex p1')) ) = case v4 of
    Ast.AstVar{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstLet var u v -> astLet var u (astGatherCase sh4 v (vars4, ix4))
    Ast.AstLetADShare{} -> error "astGatherCase: AstLetADShare"
    AstNm opCode args | not (length args > 1 || all isVar args) ->
      -- Going inside AstOp usually makes the term more expensive to interpret
      -- and reverting this transformation requires comparing many arguments,
      -- so it's not practical.
      AstNm opCode (map (\v -> astGatherRec sh4 v (vars4, ix4)) args)
    AstNm{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstOp opCode args | not (length args > 1 || all isVar args) ->
      Ast.AstOp opCode (map (\v -> astGatherRec sh4 v (vars4, ix4)) args)
    Ast.AstOp{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstOpIntegral opCode args | not (length args > 1 || all isVar args) ->
      Ast.AstOpIntegral
        opCode (map (\v -> astGatherRec sh4 v (vars4, ix4)) args)
    Ast.AstOpIntegral{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    AstSumOfList args | not (length args > 1 || all isVar args) ->
      astSumOfList (map (\v -> astGatherRec sh4 v (vars4, ix4)) args)
    AstSumOfList{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstIota | AstIntConst i <- i4 -> case sameNat (Proxy @p') (Proxy @1) of
      Just Refl -> astReplicate0N sh4 $ AstConst
                   $ OR.scalar $ fromIntegral i
      _ -> error "astGather: AstIota: impossible pattern needlessly required"
    Ast.AstIota ->  -- probably nothing can be simplified; a normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstIndex v2 ix2 -> case (v2, ix2) of
      (Ast.AstFromList{}, i2 :. ZI) -> astGather sh4 v2 (vars4, i2 :. ix4)
      (Ast.AstFromVector{}, i2 :. ZI) -> astGather sh4 v2 (vars4, i2 :. ix4)
      _ ->  -- AstVar, AstConst
        Ast.AstGather sh4 v4 (vars4, ix4)
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
                                              :. (ix2 :: AstIndex p1))
      | AstIntConst i6 <- i4 ->
          if i6 == i5
          then astGather @m' @n' @p1' sh4
                         (unsafeCoerce
                          $ astScatter @m4 @n4 @p1 sh v (vars, ix2))
                         (vars4, rest4)
          else astGather sh4 (astReplicate0N @(p1' + n') (unsafeCoerce sh) 0)
                         (vars4, rest4)
    Ast.AstScatter{} ->  -- a normal form
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromList l | AstIntConst it <- i4 ->
      let i = fromIntegral $ OR.unScalar it
      in astGather sh4 (if 0 <= i && i < length l
                       then l !! i
                       else astReplicate0N @(p1' + n')
                                           (dropShape $ shapeAst v4) 0)
                       (vars4, rest4)
    Ast.AstFromList{} | gatherFromNF vars4 ix4 ->
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromList l ->
      let f v = astGatherRec sh4 v (vars4, rest4)
          (varsFresh, ixFresh) = funToAstIndex @m' id
          subst i =
            foldr (uncurry substituteAstPrimal) i
                  (zipSized (fmap SubstitutionPayloadInt
                             $ indexToSizedList ixFresh) vars4)
          i5 = subst i4
      in astGather sh4 (astFromList $ map f l) (varsFresh, i5 :. ixFresh)
    Ast.AstFromVector l | AstIntConst it <- i4 ->
      let i = fromIntegral $ OR.unScalar it
      in astGather sh4 (if 0 <= i && i < V.length l
                       then l V.! i
                       else astReplicate0N @(p1' + n')
                                           (dropShape $ shapeAst v4) 0)
                       (vars4, rest4)
    Ast.AstFromVector{} | gatherFromNF vars4 ix4 ->
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstFromVector l ->
      let f v = astGatherRec sh4 v (vars4, rest4)
          (varsFresh, ixFresh) = funToAstIndex @m' id
          subst i =
            foldr (uncurry substituteAstPrimal) i
                  (zipSized (fmap SubstitutionPayloadInt
                             $ indexToSizedList ixFresh) vars4)
          i5 = subst i4
     in astGather sh4 (astFromVector $ V.map f l) (varsFresh, i5 :. ixFresh)
    Ast.AstReplicate _k v -> astGather sh4 v (vars4, rest4)
    Ast.AstAppend{} ->
      {- This is wrong, see astIndexROrStepOnly:
         We can't express append as gather, because AstFromList needs
         arguments of the same shape, so here we need to inline a lot of code.
         TODO: The normal form is not acceptable, because fusion is halted
         and can't get inside AstAppend, unlike inside AstFromList.
         Let's see if we can do the same trick as with AstFromList
         and get all the remaining indexes inside AstGather.
         BTW, probably fusion is halted also due to NF with AstScatter.
      let vlen = AstIntConst $ lengthAst v
          iw = simplifyAst (AstIntOp MinusIntOp [i4, vlen])
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
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstSlice i _k v ->
      let ii = simplifyAst (astSumOfList
                              [ unAstPrimalPart i4
                              , AstConst $ OR.scalar $ fromIntegral i ])
      in astGather sh4 v (vars4, astPrimalPart ii :. rest4)
    Ast.AstReverse v ->
      let iRev = simplifyAst (AstNm Ast.MinusOp
                                    [ AstConst (OR.scalar $ fromIntegral
                                                    $ lengthAst v - 1)
                                    , unAstPrimalPart i4 ])
      in astGather sh4 v (vars4, astPrimalPart iRev :. rest4)
    Ast.AstTranspose perm v | valueOf @p' >= length perm ->
      astGather sh4 v (vars4, permutePrefixIndex perm ix4)
    Ast.AstTranspose perm v ->
      astGather sh4 (astTransposeAsGather perm v) (vars4, ix4)
    Ast.AstReshape sh v ->
      astGather sh4 (astReshapeAsGather sh v) (vars4, ix4)
    Ast.AstBuild1{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstGather @m2 @n2 _sh2 v2 (vars2, ix2) ->
      -- TODO: we need integer let to preserve sharing while substituting here:
      let subst :: AstIndex m7 -> AstVarList m7 -> AstInt -> AstInt
          subst ix vars i =
            foldr (uncurry substituteAstPrimal) i
                  (zipSized (fmap SubstitutionPayloadInt
                             $ indexToSizedList ix) vars)
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
    Ast.AstCast{} -> Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstSToR{} ->  -- TODO
      Ast.AstGather sh4 v4 (vars4, ix4)
    AstConst{} ->  -- free variables possible, so can't compute the tensor
      Ast.AstGather sh4 v4 (vars4, ix4)
    Ast.AstConstant (AstPrimalPart v) ->
      Ast.AstConstant $ astPrimalPart $ astGather sh4 v (vars4, ix4)
    Ast.AstD (AstPrimalPart u) (AstDualPart u') ->
      let (varsFresh, ixFresh) = funToAstIndex @m' id
          subst i =
            foldr (uncurry substituteAstPrimal) i
                  (zipSized (fmap SubstitutionPayloadInt
                             $ indexToSizedList ixFresh) vars4)
          ix5 = fmap subst ix4
      in Ast.AstD (astPrimalPart $ astGatherRec sh4 u (vars4, ix4))
                  (AstDualPart $ astGatherRec sh4 u' (varsFresh, ix5))
    Ast.AstLetDomains vars l v ->
      Ast.AstLetDomains vars l (astGatherCase sh4 v (vars4, ix4))
    Ast.AstFloor (AstPrimalPart v) ->
      Ast.AstFloor $ astPrimalPart
      $ astGatherROrStepOnly stepOnly sh4 v (vars4, ix4)
    Ast.AstCond b v w -> astCond b (astGather sh4 v (vars4, ix4))
                                   (astGather sh4 w (vars4, ix4))
    Ast.AstMinIndex (AstPrimalPart v) ->
      Ast.AstMinIndex $ astPrimalPart
      $ astGatherROrStepOnly stepOnly
          (sh4 `appendShape` singletonShape (lastShape (shapeAst v)))
          v (vars4, ix4)
    Ast.AstMaxIndex (AstPrimalPart v) ->
      Ast.AstMaxIndex $ astPrimalPart
      $ astGatherROrStepOnly stepOnly
          (sh4 `appendShape` singletonShape (lastShape (shapeAst v)))
          v (vars4, ix4)

gatherFromNF :: forall m p. (KnownNat m, KnownNat p)
             => AstVarList m -> AstIndex (1 + p) -> Bool
gatherFromNF _ ZI = error "gatherFromNF: impossible pattern needlessly required"
gatherFromNF vars (i :. rest) = case cmpNat (Proxy @p) (Proxy @m) of
  LTI ->
    let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
        cmp _ = False
        (varsP, varsPM) = splitAt_Sized @p @(m - p) vars
    in all cmp (zipIndex rest (sizedListToIndex (fmap AstIntVar varsP)))
       && not (any (`intVarInAstPrimal` i) varsPM)
  EQI ->
    let cmp (AstIntVar var1, AstIntVar var2) = var1 == var2
        cmp _ = False
    in all cmp (zipIndex rest (sizedListToIndex (fmap AstIntVar vars)))
  GTI -> False

flipCompare :: forall (a :: Nat) b. Compare a b ~ GT => Compare b a :~: LT
flipCompare = unsafeCoerce Refl

astFromDynamic :: forall n r. KnownNat n
               => AstDynamic r -> AstRanked r n
astFromDynamic (AstRToD Ast.AstIota) = error "astFromDynamic: dummy"
astFromDynamic (AstRToD @n2 v) =
  case sameNat (Proxy @n) (Proxy @n2) of
    Just Refl -> v
    _ -> error "astFromDynamic: different rank expected and uncovered"
astFromDynamic (AstSToD @sh2 v) =
  case matchingRank @sh2 @n of
    Just Refl -> Ast.AstSToR v
    _ -> error "astFromDynamic: different rank expected and uncovered"

astFromDynamicS :: forall sh r. OS.Shape sh
                => AstDynamic r -> AstShaped r sh
astFromDynamicS (AstSToD Ast.AstIotaS) = error "astFromDynamicS: dummy"
astFromDynamicS (AstSToD @sh2 v) =
  case sameShape @sh @sh2 of
    Just Refl -> v
    _ -> error "astFromDynamicS: different shape expected and uncovered"
astFromDynamicS (AstRToD @n2 v) =
  case matchingRank @sh @n2 of
    Just Refl -> Ast.AstRToS v
    _ -> error "astFromDynamicS: different rank expected and uncovered"

{-
-- TODO: To apply this to astGatherR. we'd need to take the last variable
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
            | intVarInAst var i1 ->
                let w :: AstRanked r (1 + n)
                    w = astIndexR v2 rest1
                in case gatherSimplify k var w i1 of
                  Just u -> u  -- an extremely simple form found
                    -- for AstGather instead:
                    -- AstGather ... u (initN, rest1)
                  Nothing ->
                    AstGather1 k v2 (var, ix2)
                    -- we didn't really need it anyway
            | otherwise -> astReplicate k (AstIndex v2 ix2)
-}
-- Let's instead wait and see if we can come up with more general
-- simplifications, involving all variables. Especially that
-- astSliceLax is so complex. Perhaps instead of recovering slices
-- and the identity, transpositions and the identity would be better.
-- | The application @gatherSimplify k var v i1@ vectorizes and simplifies
-- the term @AstBuild1 k (var, AstIndex v [i1])@, where it's known that
-- @var@ does not occur in @v@ but occurs in @i1@. This is done by pattern
-- matching on @i1@ as opposed to on @v@.
gatherSimplify
  :: (KnownNat n, GoodScalar r)
  => Int -> AstVarId -> AstRanked r (1 + n) -> AstInt
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
astSliceLax :: (KnownNat n, GoodScalar r)
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

astDomainsLet :: forall n r. (KnownNat n, GoodScalar r)
              => AstVarId -> AstRanked r n -> AstDomains -> AstDomains
astDomainsLet var u v | astIsSmall True u =
  substitute1AstDomains (SubstitutionPayloadRanked u) var v
  -- we use the substitution that does not simplify, which is sad,
  -- because very low hanging fruits may be left hanging, but we
  -- don't want to simplify the whole term; a better alternative
  -- would be a substitution that only simplifies the touched
  -- terms with one step lookahead, as normally when vectorizing
astDomainsLet var u v = Ast.AstDomainsLet var u v

astCond :: AstBool -> AstRanked r n -> AstRanked r n -> AstRanked r n
astCond (AstBoolConst b) v w = if b then v else w
astCond b (Ast.AstConstant (AstPrimalPart v))
          (Ast.AstConstant (AstPrimalPart w)) =
  Ast.AstConstant $ astPrimalPart $ astCond b v w
astCond b v w = Ast.AstCond b v w


-- * Simplification pass applied to code with eliminated nested lets

simplifyArtifact6 :: (GoodScalar r, KnownNat n)
                  => ADAstArtifact6 (Flip OR.Array) r n
                  -> ADAstArtifact6 (Flip OR.Array) r n
simplifyArtifact6 (vars, gradient, primal) =
  (vars, simplifyAstDomains6 gradient, simplifyAstPrimal6 primal)

simplifyArtifact6S :: (GoodScalar r, OS.Shape sh)
                   => ADAstArtifact6 (Flip OS.Array) r sh
                   -> ADAstArtifact6 (Flip OS.Array) r sh
simplifyArtifact6S (vars, gradient, primal) =
  (vars, simplifyAstDomains6 gradient, simplifyAstPrimal6S primal)

-- Potentially, some more inlining could be triggered after the second
-- simplification, but it's probably rare, so we don't insisit on a fixpoint.
-- The second simplification is very likely to trigger, because substitution
-- often reveals redexes.
simplifyAstPrimal6
  :: (GoodScalar r, KnownNat n)
  => AstPrimalPart r n -> AstPrimalPart r n
simplifyAstPrimal6 =
  simplifyAstPrimal . snd . inlineAstPrimal EM.empty . simplifyAstPrimal

simplifyAst6
  :: (GoodScalar r, KnownNat n)
  => AstRanked r n -> AstRanked r n
simplifyAst6 = simplifyAst . snd . inlineAst EM.empty . simplifyAst

simplifyAstPrimal6S
  :: (GoodScalar r, OS.Shape sh)
  => AstPrimalPartS r sh -> AstPrimalPartS r sh
simplifyAstPrimal6S =
  simplifyAstPrimalS . snd . inlineAstPrimalS EM.empty . simplifyAstPrimalS

simplifyAst6S
  :: (GoodScalar r, OS.Shape sh)
  => AstShaped r sh -> AstShaped r sh
simplifyAst6S = simplifyAstS . snd . inlineAstS EM.empty . simplifyAstS

simplifyAstDomains6
  :: AstDomains -> AstDomains
simplifyAstDomains6 =
  simplifyAstDomains . snd . inlineAstDomains EM.empty . simplifyAstDomains


-- * The pass inlining lets with the bottom-up strategy

type AstMemo = EM.EnumMap AstVarId Int

inlineAstPrimal
  :: forall n r. (GoodScalar r, KnownNat n)
  => AstMemo
  -> AstPrimalPart r n -> (AstMemo, AstPrimalPart r n)
inlineAstPrimal memo (AstPrimalPart v1) =
  second astPrimalPart $ inlineAst memo v1

inlineAstDual
  :: forall n r. (GoodScalar r, KnownNat n)
  => AstMemo
  -> AstDualPart r n -> (AstMemo, AstDualPart r n)
inlineAstDual memo (AstDualPart v1) =
  second AstDualPart $ inlineAst memo v1

inlineAst
  :: forall n r. (GoodScalar r, KnownNat n)
  => AstMemo
  -> AstRanked r n -> (AstMemo, AstRanked r n)
inlineAst memo v0 = case v0 of
  Ast.AstVar _ var -> let f Nothing = Just 1
                          f (Just count) = Just $ succ count
                      in (EM.alter f var memo, v0)
  Ast.AstLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let (memo1, v2) = inlineAst memo v
        memo1NoVar = EM.delete var memo1
        (memo2, u2) = inlineAst memo1NoVar u
    in case EM.findWithDefault 0 var memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substitute1Ast (SubstitutionPayloadRanked u2) var v2)
        -- this is the substitution that doesn't simplify, so that
        -- inlining can be applied with and without simplification
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
            memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
                      -- u is small, so the union is fast
        in (memo3, substitute1Ast (SubstitutionPayloadRanked u0) var v2)
      _ -> (memo2, Ast.AstLet var u2 v2)
  Ast.AstLetADShare{} -> error "inlineAst: AstLetADShare"
  AstNm opCode args ->
    let (memo2, args2) = mapAccumR inlineAst memo args
    in (memo2, AstNm opCode args2)
  Ast.AstOp opCode args ->
    let (memo2, args2) = mapAccumR inlineAst memo args
    in (memo2, Ast.AstOp opCode args2)
  Ast.AstOpIntegral opCode args ->
    let (memo2, args2) = mapAccumR inlineAst memo args
    in (memo2, Ast.AstOpIntegral opCode args2)
  AstSumOfList args ->
    let (memo2, args2) = mapAccumR inlineAst memo args
    in (memo2, AstSumOfList args2)
  Ast.AstIota -> (memo, v0)
  Ast.AstIndex v ix ->
    let (memo1, v2) = inlineAst memo v
        (memo2, ix2) = mapAccumR inlineAstPrimal EM.empty (indexToList ix)
        count = 10  -- don't inline into integer expressions until we share them
        memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memo2
    in (memo3, Ast.AstIndex v2 (listToIndex ix2))
  Ast.AstSum v -> second Ast.AstSum (inlineAst memo v)
  Ast.AstScatter sh v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAstPrimal EM.empty (indexToList ix)
        count = sizeShape sh + 10  -- don't inline into integer expressions
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatter sh v2 (vars, listToIndex ix2))
  Ast.AstFromList l ->
    let (memo2, l2) = mapAccumR inlineAst memo l
    in (memo2, Ast.AstFromList l2)
  Ast.AstFromVector l ->
    let (memo2, l2) = mapAccumR inlineAst memo (V.toList l)
    in (memo2, Ast.AstFromVector $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstReplicate k v -> second (Ast.AstReplicate k) (inlineAst memo v)
  Ast.AstAppend x y ->
    let (memo1, t1) = inlineAst memo x
        (memo2, t2) = inlineAst memo1 y
    in (memo2, Ast.AstAppend t1 t2)
  Ast.AstSlice i k v -> second (Ast.AstSlice i k) (inlineAst memo v)
  Ast.AstReverse v -> second Ast.AstReverse (inlineAst memo v)
  Ast.AstTranspose perm v ->
    second (Ast.AstTranspose perm) $ inlineAst memo v
  Ast.AstReshape sh v -> second (Ast.AstReshape sh) (inlineAst memo v)
  Ast.AstBuild1 k (var, v) ->
    let (memoV0, v2) = inlineAst EM.empty v
        memo1 = EM.unionWith (\c1 c0 -> c1 + k * c0) memo memoV0
    in (memo1, Ast.AstBuild1 k (var, v2))
  Ast.AstGather sh v (vars, ix) ->
    let (memo1, v2) = inlineAst memo v
        (memoI0, ix2) = mapAccumR inlineAstPrimal EM.empty (indexToList ix)
        count = sizeShape sh + 10  -- don't inline into integer expressions
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGather sh v2 (vars, listToIndex ix2))
  Ast.AstCast v -> second Ast.AstCast $ inlineAst memo v
  Ast.AstSToR v -> second Ast.AstSToR $ inlineAstS memo v
  AstConst{} -> (memo, v0)
  Ast.AstConstant a -> second Ast.AstConstant $ inlineAstPrimal memo a
  Ast.AstD u u' ->
    let (memo1, t1) = inlineAstPrimal memo u
        (memo2, t2) = inlineAstDual memo1 u'
    in (memo2, Ast.AstD t1 t2)
  Ast.AstLetDomains vars l v ->  -- TODO: actually inline
    let (memo1, l2) = inlineAstDomains memo l
        (memo2, v2) = inlineAst memo1 v
    in (memo2, Ast.AstLetDomains vars l2 v2)
  Ast.AstFloor a -> second Ast.AstFloor $ inlineAstPrimal memo a
  Ast.AstCond b a2 a3 ->
    -- This is a place where our inlining may increase code size
    -- by enlarging both branches due to not considering number of syntactic
    -- occurences, but only dynamic occurences. Tensor expressions
    -- in conditionals are problematic and special enough
    -- that we can let it be until problems are encountered in the wild.
    -- See https://github.com/VMatthijs/CHAD/blob/main/src/Count.hs#L88-L152.
    let (memo1, b1) = inlineAstBool memo b
        (memoA2, t2) = inlineAst EM.empty a2
        (memoA3, t3) = inlineAst EM.empty a3
        memo4 = EM.unionWith max memoA2 memoA3
        memo5 = EM.unionWith (+) memo1 memo4
    in (memo5, Ast.AstCond b1 t2 t3)
  Ast.AstMinIndex a -> second Ast.AstMinIndex $ inlineAstPrimal memo a
  Ast.AstMaxIndex a -> second Ast.AstMaxIndex $ inlineAstPrimal memo a

inlineAstDynamic
  :: AstMemo -> DynamicExists AstDynamic -> (AstMemo, DynamicExists AstDynamic)
inlineAstDynamic memo = \case
  DynamicExists (AstRToD w) ->
    second (DynamicExists . AstRToD) $ inlineAst memo w
  DynamicExists (AstSToD w) ->
    second (DynamicExists . AstSToD) $ inlineAstS memo w

inlineAstDomains
  :: AstMemo -> AstDomains -> (AstMemo, AstDomains)
inlineAstDomains memo v0 = case v0 of
  Ast.AstDomains l ->
    second Ast.AstDomains $ mapAccumR inlineAstDynamic memo l
  Ast.AstDomainsLet var u v ->
    -- We assume there are no nested lets with the same variable.
    let (memo1, v2) = inlineAstDomains memo v
        memo1NoVar = EM.delete var memo1
        (memo2, u2) = inlineAst memo1NoVar u
    in case EM.findWithDefault 0 var memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substitute1AstDomains (SubstitutionPayloadRanked u2) var v2)
        -- this is the substitution that doesn't simplify, so that
        -- inlining can be applied with and without simplification
      count | astIsSmall (count < 10) u ->
        let (memoU0, u0) = inlineAst EM.empty u
        in ( EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
               -- u is small, so the union is fast
           , substitute1AstDomains (SubstitutionPayloadRanked u0) var v2 )
      _ -> (memo2, Ast.AstDomainsLet var u2 v2)
  Ast.AstDomainsLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let (memo1, v2) = inlineAstDomains memo v
        memo1NoVar = EM.delete var memo1
        (memo2, u2) = inlineAstS memo1NoVar u
    in case EM.findWithDefault 0 var memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substitute1AstDomains (SubstitutionPayloadShaped u2) var v2)
        -- this is the substitution that doesn't simplify, so that
        -- inlining can be applied with and without simplification
      count | astIsSmallS (count < 10) u ->
        let (memoU0, u0) = inlineAstS EM.empty u
        in ( EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
               -- u is small, so the union is fast
           , substitute1AstDomains (SubstitutionPayloadShaped u0) var v2 )
      _ -> (memo2, Ast.AstDomainsLetS var u2 v2)

inlineAstBool :: AstMemo -> AstBool -> (AstMemo, AstBool)
inlineAstBool memo v0 = case v0 of
  Ast.AstBoolOp opCodeBool args ->
    let (memo2, args2) = mapAccumR inlineAstBool memo args
    in (memo2, Ast.AstBoolOp opCodeBool args2)
  AstBoolConst{} -> (memo, v0)
  Ast.AstRel @n opCodeRel args ->
    let (memo2, args2) =  mapAccumR inlineAstPrimal memo args
    in (memo2, Ast.AstRel opCodeRel args2)
  Ast.AstRelS @n opCodeRel args ->
    let (memo2, args2) =  mapAccumR inlineAstPrimalS memo args
    in (memo2, Ast.AstRelS opCodeRel args2)

inlineAstPrimalS
  :: forall sh r. (GoodScalar r, OS.Shape sh)
  => AstMemo
  -> AstPrimalPartS r sh -> (AstMemo, AstPrimalPartS r sh)
inlineAstPrimalS memo (AstPrimalPartS v1) =
  second astPrimalPartS $ inlineAstS memo v1

inlineAstDualS
  :: forall sh r. (GoodScalar r, OS.Shape sh)
  => AstMemo
  -> AstDualPartS r sh -> (AstMemo, AstDualPartS r sh)
inlineAstDualS memo (AstDualPartS v1) =
  second AstDualPartS $ inlineAstS memo v1

inlineAstS
  :: forall sh r. (GoodScalar r, OS.Shape sh)
  => AstMemo
  -> AstShaped r sh -> (AstMemo, AstShaped r sh)
inlineAstS memo v0 = case v0 of
  Ast.AstVarS var -> let f Nothing = Just 1
                         f (Just count) = Just $ succ count
                     in (EM.alter f var memo, v0)
  Ast.AstLetS var u v ->
    -- We assume there are no nested lets with the same variable.
    let (memo1, v2) = inlineAstS memo v
        memo1NoVar = EM.delete var memo1
        (memo2, u2) = inlineAstS memo1NoVar u
    in case EM.findWithDefault 0 var memo1 of
      0 -> (memo1, v2)
      1 -> (memo2, substitute1AstS (SubstitutionPayloadShaped u2) var v2)
        -- this is the substitution that doesn't simplify, so that
        -- inlining can be applied with and without simplification
      count | astIsSmallS (count < 10) u ->
        let (memoU0, u0) = inlineAstS EM.empty u
            memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1NoVar memoU0
                      -- u is small, so the union is fast
        in (memo3, substitute1AstS (SubstitutionPayloadShaped u0) var v2)
      _ -> (memo2, Ast.AstLetS var u2 v2)
  Ast.AstLetADShareS{} -> error "inlineAstS: AstLetADShareS"
  AstNmS opCode args ->
    let (memo2, args2) = mapAccumR inlineAstS memo args
    in (memo2, AstNmS opCode args2)
  Ast.AstOpS opCode args ->
    let (memo2, args2) = mapAccumR inlineAstS memo args
    in (memo2, Ast.AstOpS opCode args2)
  Ast.AstOpIntegralS opCode args ->
    let (memo2, args2) = mapAccumR inlineAstS memo args
    in (memo2, Ast.AstOpIntegralS opCode args2)
  AstSumOfListS args ->
    let (memo2, args2) = mapAccumR inlineAstS memo args
    in (memo2, AstSumOfListS args2)
  Ast.AstIotaS -> (memo, v0)
  Ast.AstIndexS @sh1 v ix ->
    let (memo1, v2) = inlineAstS memo v
        (memo2, ix2) = mapAccumR inlineAstPrimal EM.empty
                                 (ShapedList.sizedListToList ix)
        count = 10  -- don't inline into integer expressions until we share them
        memo3 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memo2
    in (memo3, Ast.AstIndexS @sh1 v2 (ShapedList.listToSized ix2))
  Ast.AstSumS v -> second Ast.AstSumS (inlineAstS memo v)
  Ast.AstScatterS @sh2 @p v (vars, ix) ->
    let (memo1, v2) = inlineAstS memo v
        (memoI0, ix2) = mapAccumR inlineAstPrimal EM.empty
                                  (ShapedList.sizedListToList ix)
        count = OS.sizeT @sh + 10  -- don't inline into integer expressions
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstScatterS @sh2 @p v2 (vars, ShapedList.listToSized ix2))
  Ast.AstFromListS l ->
    let (memo2, l2) = mapAccumR inlineAstS memo l
    in (memo2, Ast.AstFromListS l2)
  Ast.AstFromVectorS l ->
    let (memo2, l2) = mapAccumR inlineAstS memo (V.toList l)
    in (memo2, Ast.AstFromVectorS $ V.fromList l2)
      -- TODO: emulate mapAccum using mapM?
  Ast.AstReplicateS v -> second Ast.AstReplicateS (inlineAstS memo v)
  Ast.AstAppendS x y ->
    let (memo1, t1) = inlineAstS memo x
        (memo2, t2) = inlineAstS memo1 y
    in (memo2, Ast.AstAppendS t1 t2)
  Ast.AstSliceS @i v -> second (Ast.AstSliceS @i) (inlineAstS memo v)
  Ast.AstReverseS v -> second Ast.AstReverseS (inlineAstS memo v)
  Ast.AstTransposeS @perm v ->
    second (Ast.AstTransposeS @perm) $ inlineAstS memo v
  Ast.AstReshapeS v -> second Ast.AstReshapeS (inlineAstS memo v)
  Ast.AstBuild1S @n (var, v) ->
    let (memoV0, v2) = inlineAstS EM.empty v
        memo1 = EM.unionWith (\c1 c0 -> c1 + valueOf @n * c0) memo memoV0
    in (memo1, Ast.AstBuild1S (var, v2))
  Ast.AstGatherS @sh2 @p v (vars, ix) ->
    let (memo1, v2) = inlineAstS memo v
        (memoI0, ix2) = mapAccumR inlineAstPrimal EM.empty
                                  (ShapedList.sizedListToList ix)
        count = OS.sizeT @sh + 10  -- don't inline into integer expressions
        memo2 = EM.unionWith (\c1 c0 -> c1 + count * c0) memo1 memoI0
    in (memo2, Ast.AstGatherS @sh2 @p v2 (vars, ShapedList.listToSized ix2))
  Ast.AstCastS v -> second Ast.AstCastS $ inlineAstS memo v
  Ast.AstRToS v -> second Ast.AstRToS $ inlineAst memo v
  AstConstS{} -> (memo, v0)
  Ast.AstConstantS a -> second Ast.AstConstantS $ inlineAstPrimalS memo a
  Ast.AstDS u u' ->
    let (memo1, t1) = inlineAstPrimalS memo u
        (memo2, t2) = inlineAstDualS memo1 u'
    in (memo2, Ast.AstDS t1 t2)
  Ast.AstLetDomainsS vars l v ->  -- TODO: actually inline
    let (memo1, l2) = inlineAstDomains memo l
        (memo2, v2) = inlineAstS memo1 v
    in (memo2, Ast.AstLetDomainsS vars l2 v2)
  Ast.AstFloorS a -> second Ast.AstFloorS $ inlineAstPrimalS memo a
  Ast.AstCondS b a2 a3 ->
    -- This is a place where our inlining may increase code size
    -- by enlarging both branches due to not considering number of syntactic
    -- occurences, but only dynamic occurences. Tensor expressions
    -- in conditionals are problematic and special enough
    -- that we can let it be until problems are encountered in the wild.
    -- See https://github.com/VMatthijs/CHAD/blob/main/src/Count.hs#L88-L152.
    let (memo1, b1) = inlineAstBool memo b
        (memoA2, t2) = inlineAstS EM.empty a2
        (memoA3, t3) = inlineAstS EM.empty a3
        memo4 = EM.unionWith max memoA2 memoA3
        memo5 = EM.unionWith (+) memo1 memo4
    in (memo5, Ast.AstCondS b1 t2 t3)
  Ast.AstMinIndexS a -> second Ast.AstMinIndexS $ inlineAstPrimalS memo a
  Ast.AstMaxIndexS a -> second Ast.AstMaxIndexS $ inlineAstPrimalS memo a


-- * The pass eliminating nested lets bottom-up

data UnletEnv = UnletEnv
  { unletSet     :: ES.EnumSet AstVarId
  , unletADShare :: ADShare }

emptyUnletEnv :: ADShare -> UnletEnv
emptyUnletEnv l = UnletEnv ES.empty l

unletAstDomains6
  :: [(AstVarId, DynamicExists AstDynamic)] -> ADShare -> AstDomains
  -> AstDomains
unletAstDomains6 astBindings l t =
  unletAstDomains (emptyUnletEnv l)
  $ bindsToDomainsLet (bindsToDomainsLet t astBindings) (assocsADShare l)

unletAst6
  :: (GoodScalar r, KnownNat n)
  => ADShare -> AstPrimalPart r n -> AstPrimalPart r n
unletAst6 l (AstPrimalPart t) = astPrimalPart $ unletAst (emptyUnletEnv l)
                                $ bindsToLet t (assocsADShare l)

unletAst6S
  :: (GoodScalar r, OS.Shape sh)
  => ADShare -> AstPrimalPartS r sh -> AstPrimalPartS r sh
unletAst6S l (AstPrimalPartS t) = astPrimalPartS $ unletAstS (emptyUnletEnv l)
                                  $ bindsToLetS t (assocsADShare l)

-- TODO: if a nested let is alone, eliminate the nesting let instead;
-- this probably requires many passes though
unletAstPrimal
  :: (GoodScalar r, KnownNat n)
  => UnletEnv -> AstPrimalPart r n -> AstPrimalPart r n
unletAstPrimal env (AstPrimalPart t) = astPrimalPart $ unletAst env t

unletAst
  :: (GoodScalar r, KnownNat n)
  => UnletEnv -> AstRanked r n -> AstRanked r n
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
  AstNm opCode args -> AstNm opCode (map (unletAst env) args)
  Ast.AstOp opCode args -> Ast.AstOp opCode (map (unletAst env) args)
  Ast.AstOpIntegral opCode args ->
    Ast.AstOpIntegral opCode (map (unletAst env) args)
  AstSumOfList args -> AstSumOfList (map (unletAst env) args)
  Ast.AstIota -> t
  Ast.AstIndex v ix ->
    Ast.AstIndex (unletAst env v) (fmap (unletAstPrimal env) ix)
  Ast.AstSum v -> Ast.AstSum (unletAst env v)
  Ast.AstScatter sh v (var, ix) ->
    Ast.AstScatter sh (unletAst env v) (var, fmap (unletAstPrimal env) ix)
  Ast.AstFromList l -> Ast.AstFromList (map (unletAst env) l)
  Ast.AstFromVector l -> Ast.AstFromVector (V.map (unletAst env) l)
  Ast.AstReplicate k v -> Ast.AstReplicate k (unletAst env v)
  Ast.AstAppend x y -> Ast.AstAppend (unletAst env x) (unletAst env y)
  Ast.AstSlice i k v -> Ast.AstSlice i k (unletAst env v)
  Ast.AstReverse v -> Ast.AstReverse (unletAst env v)
  Ast.AstTranspose perm v -> Ast.AstTranspose perm (unletAst env v)
  Ast.AstReshape sh v -> Ast.AstReshape sh (unletAst env v)
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, unletAst env v)
  Ast.AstGather sh v (vars, ix) ->
    Ast.AstGather sh (unletAst env v) (vars, fmap (unletAstPrimal env) ix)
  Ast.AstCast v -> Ast.AstCast (unletAst env v)
  Ast.AstSToR v -> Ast.AstSToR (unletAstS env v)
  AstConst{} -> t
  Ast.AstConstant v -> Ast.AstConstant (unletAstPrimal env v)
  Ast.AstD u (AstDualPart u') -> Ast.AstD (unletAstPrimal env u)
                                  (AstDualPart $ unletAst env u')
  Ast.AstLetDomains vars l v ->
    let env2 = env {unletSet = unletSet env
                               `ES.union` ES.fromList (V.toList vars)}
    in Ast.AstLetDomains vars (unletAstDomains env l) (unletAst env2 v)
  Ast.AstFloor a -> Ast.AstFloor $ unletAstPrimal env a
  Ast.AstCond b a1 a2 ->
    Ast.AstCond
      (unletAstBool env b) (unletAst env a1) (unletAst env a2)
  Ast.AstMinIndex a -> Ast.AstMinIndex $ unletAstPrimal env a
  Ast.AstMaxIndex a -> Ast.AstMaxIndex $ unletAstPrimal env a

unletAstDynamic
  :: UnletEnv -> DynamicExists AstDynamic -> DynamicExists AstDynamic
unletAstDynamic env = \case
  DynamicExists (AstRToD u) -> DynamicExists $ AstRToD $ unletAst env u
  DynamicExists (AstSToD u) -> DynamicExists $ AstSToD $ unletAstS env u

unletAstDomains
  :: UnletEnv -> AstDomains -> AstDomains
unletAstDomains env = \case
  Ast.AstDomains l -> Ast.AstDomains $ V.map (unletAstDynamic env) l
  Ast.AstDomainsLet var u v ->
    if var `ES.member` unletSet env
    then unletAstDomains env v
    else let env2 = env {unletSet = ES.insert var (unletSet env)}
         in Ast.AstDomainsLet var (unletAst env u)
                                  (unletAstDomains env2 v)
  Ast.AstDomainsLetS var u v ->
    if var `ES.member` unletSet env
    then unletAstDomains env v
    else let env2 = env {unletSet = ES.insert var (unletSet env)}
         in Ast.AstDomainsLetS var (unletAstS env u)
                                   (unletAstDomains env2 v)

unletAstBool :: UnletEnv -> AstBool -> AstBool
unletAstBool env t = case t of
  Ast.AstBoolOp opCodeBool args ->
    Ast.AstBoolOp opCodeBool (map (unletAstBool env) args)
  AstBoolConst{} -> t
  Ast.AstRel opCodeRel args ->
    Ast.AstRel opCodeRel (map (unletAstPrimal env) args)
  Ast.AstRelS opCodeRel args ->
    Ast.AstRelS opCodeRel (map (unletAstPrimalS env) args)

unletAstPrimalS
  :: (GoodScalar r, OS.Shape sh)
  => UnletEnv -> AstPrimalPartS r sh -> AstPrimalPartS r sh
unletAstPrimalS env (AstPrimalPartS t) = astPrimalPartS $ unletAstS env t

unletAstS
  :: (GoodScalar r, OS.Shape sh)
  => UnletEnv -> AstShaped r sh -> AstShaped r sh
unletAstS env t = case t of
  Ast.AstVarS{} -> t
  Ast.AstLetS var u v ->
    -- This optimization is sound, because there is no mechanism
    -- that would nest lets with the same variable (e.g., our lets always
    -- bind fresh variables at creation time and we never substitute
    -- a term into the same term). If that changes, let's refresh
    -- let variables whenever substituting into let bodies.
    -- See the same assumption in AstInterpret.
    if var `ES.member` unletSet env
    then unletAstS env v
    else let env2 = env {unletSet = ES.insert var (unletSet env)}
         in Ast.AstLetS var (unletAstS env u) (unletAstS env2 v)
  Ast.AstLetADShareS l v ->
    let lassocs = subtractADShare l $ unletADShare env
          -- potentially prevents quadratic cost induced by tletWrap
          -- duplicating the global ADShare; may induce overhead when
          -- the same lets are verified for removal twice, in subtractADShare
          -- and via unletAst, but if many lets can be eliminated,
          -- subtractADShare does it much faster
    in unletAstS env $ bindsToLetS v lassocs
  AstNmS opCode args -> AstNmS opCode (map (unletAstS env) args)
  Ast.AstOpS opCode args -> Ast.AstOpS opCode (map (unletAstS env) args)
  Ast.AstOpIntegralS opCode args ->
    Ast.AstOpIntegralS opCode (map (unletAstS env) args)
  AstSumOfListS args -> AstSumOfListS (map (unletAstS env) args)
  Ast.AstIotaS -> t
  Ast.AstIndexS v ix ->
    Ast.AstIndexS (unletAstS env v) (fmap (unletAstPrimal env) ix)
  Ast.AstSumS v -> Ast.AstSumS (unletAstS env v)
  Ast.AstScatterS v (var, ix) ->
    Ast.AstScatterS (unletAstS env v) (var, fmap (unletAstPrimal env) ix)
  Ast.AstFromListS l -> Ast.AstFromListS (map (unletAstS env) l)
  Ast.AstFromVectorS l -> Ast.AstFromVectorS (V.map (unletAstS env) l)
  Ast.AstReplicateS v -> Ast.AstReplicateS (unletAstS env v)
  Ast.AstAppendS x y -> Ast.AstAppendS (unletAstS env x) (unletAstS env y)
  Ast.AstSliceS @i v -> Ast.AstSliceS @i (unletAstS env v)
  Ast.AstReverseS v -> Ast.AstReverseS (unletAstS env v)
  Ast.AstTransposeS @perm v -> Ast.AstTransposeS @perm (unletAstS env v)
  Ast.AstReshapeS v -> Ast.AstReshapeS (unletAstS env v)
  Ast.AstBuild1S (var, v) -> Ast.AstBuild1S (var, unletAstS env v)
  Ast.AstGatherS v (vars, ix) ->
    Ast.AstGatherS (unletAstS env v) (vars, fmap (unletAstPrimal env) ix)
  Ast.AstCastS v -> Ast.AstCastS (unletAstS env v)
  Ast.AstRToS v -> Ast.AstRToS (unletAst env v)
  AstConstS{} -> t
  Ast.AstConstantS v -> Ast.AstConstantS (unletAstPrimalS env v)
  Ast.AstDS u (AstDualPartS u') -> Ast.AstDS (unletAstPrimalS env u)
                                     (AstDualPartS $ unletAstS env u')
  Ast.AstLetDomainsS vars l v ->
    let env2 = env {unletSet = unletSet env
                               `ES.union` ES.fromList (V.toList vars)}
    in Ast.AstLetDomainsS vars (unletAstDomains env l) (unletAstS env2 v)
  Ast.AstFloorS a -> Ast.AstFloorS $ unletAstPrimalS env a
  Ast.AstCondS b a1 a2 ->
    Ast.AstCondS
      (unletAstBool env b) (unletAstS env a1) (unletAstS env a2)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS $ unletAstPrimalS env a
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS $ unletAstPrimalS env a


-- * The simplifying bottom-up pass

simplifyAstPrimal
  :: (GoodScalar r, KnownNat n)
  => AstPrimalPart r n -> AstPrimalPart r n
simplifyAstPrimal (AstPrimalPart t) = astPrimalPart $ simplifyAst t

-- This function guarantees full simplification: every redex
-- is visited and each combinator applied. The most exhaustive and costly
-- variants of each combinator are used, e.g., astIndexR.
simplifyAst
  :: forall n r. (GoodScalar r, KnownNat n)
  => AstRanked r n -> AstRanked r n
simplifyAst t = case t of
  Ast.AstVar{} -> t
  Ast.AstLet var u v -> astLet var (simplifyAst u) (simplifyAst v)
  Ast.AstLetADShare{} -> error "simplifyAst: AstLetADShare"
  AstNm opCode args ->
    case testEquality (typeRep @r) (typeRep @Int64) of
      Just Refl -> simplifyAstNumOp opCode (map simplifyAst args)
      _ -> AstNm opCode (map simplifyAst args)
  Ast.AstOp opCode args -> Ast.AstOp opCode (map simplifyAst args)
  Ast.AstOpIntegral opCode args ->
    case testEquality (typeRep @r) (typeRep @Int64) of
      Just Refl -> simplifyAstIntegralOp opCode (map simplifyAst args)
      _ -> Ast.AstOpIntegral opCode (map simplifyAst args)
  AstSumOfList args ->
    case testEquality (typeRep @r) (typeRep @Int64) of
      Just Refl -> foldr1 simplifyAstPlusOp (map simplifyAst args)
      _ -> astSumOfList (map simplifyAst args)
  Ast.AstIota -> t
  Ast.AstIndex v ix -> astIndexR (simplifyAst v) (fmap simplifyAstPrimal ix)
  Ast.AstSum v -> astSum (simplifyAst v)
  Ast.AstScatter sh v (var, ix) ->
    astScatter sh (simplifyAst v) (var, fmap simplifyAstPrimal ix)
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
          u@(Ast.AstTranspose _ (AstNm _ args))
            | length args > 1 || all isVar args -> u  -- normal form
          u@(Ast.AstTranspose _ (Ast.AstOp _ args))
            | length args > 1 || all isVar args -> u
          u@(Ast.AstTranspose _ (AstSumOfList args))
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
          u@(Ast.AstReshape _ (AstNm _ args))
            | length args > 1 || all isVar args -> u
              -- normal form, because gather doesn't go inside AstNm either
          u@(Ast.AstReshape _ (Ast.AstOp _ args))
            | length args > 1 || all isVar args -> u
          u@(Ast.AstReshape _ (AstSumOfList args))
            | length args > 1 || all isVar args -> u  -- normal form
          u@(Ast.AstReshape _ Ast.AstScatter{}) -> u  -- normal form
          -- Not a normal form, because often AstReshape scan be eliminated:
          -- u@(Ast.AstReshape _ Ast.AstReplicate{}) -> u  -- normal form
          Ast.AstReshape sh3 v3 -> astReshapeAsGather sh3 v3
            -- this is terribly expensive, but the only way to fully simplify
          u -> simplifyAst u
      u -> simplifyAst u
  Ast.AstBuild1 k (var, v) -> Ast.AstBuild1 k (var, simplifyAst v)
  Ast.AstGather sh v (vars, ix) ->
    astGatherR sh (simplifyAst v) (vars, fmap simplifyAstPrimal ix)
  Ast.AstCast v -> Ast.AstCast $ simplifyAst v
  Ast.AstSToR v -> Ast.AstSToR $ simplifyAstS v
  AstConst{} -> t
  Ast.AstConstant v -> Ast.AstConstant (simplifyAstPrimal v)
  Ast.AstD u (AstDualPart u') -> Ast.AstD (simplifyAstPrimal u)
                                  (AstDualPart $ simplifyAst u')
  Ast.AstLetDomains vars l v ->
    Ast.AstLetDomains vars (simplifyAstDomains l) (simplifyAst v)
  Ast.AstFloor a -> Ast.AstFloor (simplifyAstPrimal a)
  Ast.AstCond b a2 a3 ->
    astCond (simplifyAstBool b) (simplifyAst a2) (simplifyAst a3)
  Ast.AstMinIndex a -> Ast.AstMinIndex (simplifyAstPrimal a)
  Ast.AstMaxIndex a -> Ast.AstMaxIndex (simplifyAstPrimal a)

simplifyAstDynamic
  :: DynamicExists AstDynamic -> DynamicExists AstDynamic
simplifyAstDynamic (DynamicExists (AstRToD u)) =
  DynamicExists $ AstRToD $ simplifyAst u
simplifyAstDynamic (DynamicExists (AstSToD u)) =
  DynamicExists $ AstSToD $ simplifyAstS u

simplifyAstDomains
  :: AstDomains -> AstDomains
simplifyAstDomains = \case
  Ast.AstDomains l -> Ast.AstDomains $ V.map simplifyAstDynamic l
  Ast.AstDomainsLet var u v ->
    astDomainsLet var (simplifyAst u) (simplifyAstDomains v)
  Ast.AstDomainsLetS var u v ->
    astDomainsLetS var (simplifyAstS u) (simplifyAstDomains v)

simplifyAstBool :: AstBool -> AstBool
simplifyAstBool t = case t of
  Ast.AstBoolOp opCodeBool args ->
    simplifyAstBoolOp opCodeBool (map simplifyAstBool args)
  AstBoolConst{} -> t
  Ast.AstRel opCodeRel args ->
    simplifyRelOp opCodeRel (map simplifyAstPrimal args)
      -- These expressions potentially represent large tensors that are
      -- expensive to compute even when constant so we simplify and ignore them,
      -- because computation should be done on GPU, not on CPU when simplifying;
      -- we'd need a flag to control how much we pre-compute.
      -- Anyway, because these tensors sometimes represent indexes,
      -- we simplify them a bit more than the shaped ones.
  Ast.AstRelS opCodeRel args ->
    Ast.AstRelS opCodeRel (map simplifyAstPrimalS args)

-- TODO: when we have more tests, try to limit this rewrite
-- (or only the first half) to Int64 at rank 0 and see if performance improves
-- even more.
simplifyRelOp :: (KnownNat n, GoodScalar r)
              => OpCodeRel -> [AstPrimalPart r n] -> AstBool
simplifyRelOp EqOp [AstPConst u, AstPConst v] = AstBoolConst $ u == v
simplifyRelOp NeqOp [AstPConst u, AstPConst v] = AstBoolConst $ u /= v
simplifyRelOp LeqOp [AstPConst u, AstPConst v] = AstBoolConst $ u <= v
simplifyRelOp GeqOp [AstPConst u, AstPConst v] = AstBoolConst $ u >= v
simplifyRelOp LsOp [AstPConst u, AstPConst v] = AstBoolConst $ u < v
simplifyRelOp GtOp [AstPConst u, AstPConst v] = AstBoolConst $ u > v
simplifyRelOp EqOp [AstPVar u, AstPVar v] | u == v = AstBoolConst True
simplifyRelOp LeqOp [AstPVar u, AstPVar v] | u == v = AstBoolConst True
simplifyRelOp GeqOp [AstPVar u, AstPVar v] | u == v = AstBoolConst True
simplifyRelOp NeqOp [AstPVar u, AstPVar v] | u == v = AstBoolConst False
simplifyRelOp LsOp [AstPVar u, AstPVar v] | u == v = AstBoolConst False
simplifyRelOp GtOp [AstPVar u, AstPVar v] | u == v = AstBoolConst False
simplifyRelOp opCodeRel arg = Ast.AstRel opCodeRel arg

-- Normally, we wouldn't simplify tensor arithmetic so much, but some
-- of these ranked tensors can represent integers in indexes, so we have to.
-- Integer terms need to be simplified, because large ones they are sometimes
-- created due to vectorization, e.g., via astTransposeAsGather
-- or astReshapeAsGather and can be a deciding factor in whether
-- the other tensor terms can be simplified in turn.
--
-- We mix Num and Integral operations in the code below, so we have
-- to limit out underling scalar to @Int64@, which is very well,
-- because we mutiply by zero and compare (big) tensors there,
-- which are both problematic operations with floats.
-- Another problematic operations is comparing big tensors,
-- but we don't have to limit tensor rank to 0, because we compare
-- only tensors from inside bare AstConst and float tensors are always
-- wrapped in AstConstant, so they can't be involved.
--
-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right
-- and let's push negation down.
-- Not considered are rules that would require comparing non-constant terms
-- or that would duplicate a non-constant term, as well as most rules
-- informed by inequalities, expressed via max or min, such as
-- max n (signum (abs x)) | n <= 0 --> signum (abs x).
--
-- Several first paragraphs are modelled on Num (AstPrimalPart r n)
-- and depend on the normal form where AstConst, if any, is the first element
-- and the list if fully flattened and of length >= 2.
-- Additionally we here ensure the AstConst is never zero.
simplifyAstPlusOp :: KnownNat n
                  => AstRanked Int64 n -> AstRanked Int64 n
                  -> AstRanked Int64 n
simplifyAstPlusOp (AstSumOfList (AstConst u : lu))
                  (AstSumOfList (AstConst v : lv)) =
  addConstToList (u + v) (lu ++ lv)
simplifyAstPlusOp (AstSumOfList lu)
                  (AstSumOfList (AstConst v : lv)) =
  AstSumOfList (AstConst v : lv ++ lu)
simplifyAstPlusOp (AstSumOfList lu)
                  (AstSumOfList lv) =
  AstSumOfList (lu ++ lv)

simplifyAstPlusOp (AstConst u)
                  (AstSumOfList (AstConst v : lv)) =
  addConstToList (u + v) lv
simplifyAstPlusOp u
                  (AstSumOfList (AstConst v : lv)) =
  AstSumOfList (AstConst v : u : lv)
simplifyAstPlusOp u
                  (AstSumOfList lv) =
  AstSumOfList (u : lv)

simplifyAstPlusOp (AstSumOfList (AstConst u : lu))
                  (AstConst v) =
  addConstToList (u + v) lu
simplifyAstPlusOp (AstSumOfList (AstConst u : lu))
                  v =
  AstSumOfList (AstConst u : v : lu)
simplifyAstPlusOp (AstSumOfList lu)
                  v =
  AstSumOfList (v : lu)

simplifyAstPlusOp (AstConst u) (AstConst v) = AstConst $ u + v
simplifyAstPlusOp u (AstConst v) = addConstToList v [u]
simplifyAstPlusOp (AstConst u) v = addConstToList u [v]

-- Unfortunately, these won't fire if the required terms are scattered
-- among elements of the AstSumOfList list. However, in many cases,
-- binary addition is used interspersed with other operations,
-- so longer lists don't form and so these terms have a chance to be adjacent,
-- especially that AstConst is guaranteed not to intervene.
simplifyAstPlusOp (AstNm NegateOp [Ast.AstVar _ var])
                  (Ast.AstVar _ var')
  | var == var' = 0
simplifyAstPlusOp (Ast.AstVar _ var')
                  (AstNm NegateOp [Ast.AstVar _ var])
  | var == var' = 0
simplifyAstPlusOp
  (Ast.AstOpIntegral RemOp [ AstNm NegateOp [Ast.AstVar _ var]
                           , AstConst v ])
  (Ast.AstOpIntegral RemOp [ Ast.AstVar _ var'
                           , AstConst v' ])
  | var == var' && v == v' = 0
simplifyAstPlusOp
  (Ast.AstOpIntegral RemOp [ Ast.AstVar _ var'
                           , AstConst v' ])
  (Ast.AstOpIntegral RemOp [ AstNm NegateOp [Ast.AstVar _ var]
                           , AstConst v ])
  | var == var' && v == v' = 0

simplifyAstPlusOp u v = AstSumOfList [u, v]

addConstToList :: OR.Array n Int64 -> [AstRanked Int64 n] -> AstRanked Int64 n
addConstToList _ [] = error "addConstToList: AstSumOfList list too short"
addConstToList arr [i] =
  if OR.allA (== 0) arr then i else AstSumOfList [AstConst arr, i]
addConstToList arr l =
  if OR.allA (== 0) arr then AstSumOfList l else AstSumOfList (AstConst arr : l)

simplifyAstNumOp :: KnownNat n
                 => OpCodeNum -> [AstRanked Int64 n] -> AstRanked Int64 n
simplifyAstNumOp MinusOp [u, v] =
  simplifyAstPlusOp u (simplifyAstNumOp NegateOp [v])
simplifyAstNumOp TimesOp [AstConst u, AstConst v] = AstConst $ u * v
simplifyAstNumOp TimesOp [AstConst 0, _v] = AstConst 0
  -- this is suspect for floats, but needed for index integers
simplifyAstNumOp TimesOp [_u, AstConst 0] = AstConst 0
simplifyAstNumOp TimesOp [AstConst 1, v] = v
simplifyAstNumOp TimesOp [u, AstConst 1] = u
{- TODO: these break sharing as long as we don't have @let@ for AstInt:
simplifyAstNumOp TimesOp [AstNm PlusOp [u, v], w] =
  simplifyAstPlusOp [ simplifyAstNumOp TimesOp [u, w]
                             , simplifyAstNumOp TimesOp [v, w] ]
simplifyAstNumOp TimesOp [u, AstNm PlusOp [v, w]] =
  simplifyAstPlusOp [ simplifyAstNumOp TimesOp [u, v]
                             , simplifyAstNumOp TimesOp [u, w] ]
-}
simplifyAstNumOp TimesOp [AstSumOfList l, w@AstConst{}] =
  foldl1' simplifyAstPlusOp (map (\u -> simplifyAstNumOp TimesOp [u, w]) l)
simplifyAstNumOp TimesOp [u@AstConst{}, AstSumOfList l] =
  foldl1' simplifyAstPlusOp (map (\w -> simplifyAstNumOp TimesOp [u, w]) l)
-- TODO: perhaps aim for a polynomial normal form? but that requires global
-- inspection of the whole expression
simplifyAstNumOp TimesOp [ AstConst u
                         , AstNm TimesOp [AstConst v, w] ] =
  simplifyAstNumOp TimesOp [AstConst $ u * v, w]
simplifyAstNumOp TimesOp [u, AstConst n] =
  simplifyAstNumOp TimesOp [AstConst n, u]
simplifyAstNumOp TimesOp [AstNm TimesOp [u, v], w] =
  simplifyAstNumOp TimesOp [u, simplifyAstNumOp TimesOp [v, w]]

-- With static shapes, the second argument to QuotOp and RemOp
-- is often a constant, which makes such rules worth including,
-- since they are likely to fire. To help them fire, we avoid changing
-- that constant, if possible, e.g., in rules for NegateOp.
simplifyAstNumOp
  TimesOp [ AstConst v
          , Ast.AstOpIntegral QuotOp
                              [Ast.AstVar sh var, AstConst v'] ] | v == v' =
    simplifyAstNumOp MinusOp
                     [ Ast.AstVar sh var
                     , Ast.AstOpIntegral RemOp [Ast.AstVar sh var, AstConst v] ]

simplifyAstNumOp NegateOp [AstConst u] = AstConst $ negate u
simplifyAstNumOp NegateOp [AstSumOfList l] =
  foldl1' simplifyAstPlusOp (map (simplifyAstNumOp NegateOp . (: [])) l)
simplifyAstNumOp NegateOp [AstNm TimesOp [AstConst u, v]] =
  simplifyAstNumOp TimesOp [AstConst $ negate u, v]
    -- given a choice, prefer to negate a constant
simplifyAstNumOp NegateOp [AstNm TimesOp [u, v]] =
  simplifyAstNumOp TimesOp [u, simplifyAstNumOp NegateOp [v]]
simplifyAstNumOp NegateOp [AstNm NegateOp [u]] = u
simplifyAstNumOp NegateOp [AstNm SignumOp [u]] =
  simplifyAstNumOp SignumOp [simplifyAstNumOp NegateOp [u]]
simplifyAstNumOp NegateOp [AstNm MaxOp [u, v]] =
  simplifyAstNumOp MinOp [ simplifyAstNumOp NegateOp [u]
                         , simplifyAstNumOp NegateOp [v] ]
simplifyAstNumOp NegateOp [AstNm MinOp [u, v]] =
  simplifyAstNumOp MaxOp [ simplifyAstNumOp NegateOp [u]
                         , simplifyAstNumOp NegateOp [v] ]
simplifyAstNumOp NegateOp [Ast.AstOpIntegral QuotOp [AstConst u, v]] =
  simplifyAstIntegralOp QuotOp [AstConst $ negate u, v]
simplifyAstNumOp NegateOp [Ast.AstOpIntegral QuotOp [u, v]] =
  simplifyAstIntegralOp QuotOp [simplifyAstNumOp NegateOp [u], v]
simplifyAstNumOp NegateOp [Ast.AstOpIntegral RemOp [AstConst u, v]] =
  simplifyAstIntegralOp RemOp [AstConst $ negate u, v]
simplifyAstNumOp NegateOp [Ast.AstOpIntegral RemOp [u, v]] =
  simplifyAstIntegralOp RemOp [simplifyAstNumOp NegateOp [u], v]

simplifyAstNumOp AbsOp [AstConst u] = AstConst $ abs u
simplifyAstNumOp AbsOp [AstNm AbsOp [u]] = AstNm AbsOp [u]
simplifyAstNumOp AbsOp [AstNm NegateOp [u]] = simplifyAstNumOp AbsOp [u]
simplifyAstNumOp SignumOp [AstConst u] = AstConst $ signum u
simplifyAstNumOp SignumOp [AstNm SignumOp [u]] = AstNm SignumOp [u]
simplifyAstNumOp SignumOp [AstNm AbsOp [u]] =
  simplifyAstNumOp AbsOp [AstNm SignumOp [u]]
simplifyAstNumOp MaxOp [AstConst u, AstConst v] = AstConst $ max u v
simplifyAstNumOp MaxOp [ AstConst u
                       , AstNm MaxOp [AstConst v, w] ] =
  simplifyAstNumOp MaxOp [AstConst $ max u v, w]
simplifyAstNumOp MaxOp [u, AstConst n] = AstNm MaxOp [AstConst n, u]
simplifyAstNumOp MaxOp [AstNm MaxOp [u, v], w] =
  simplifyAstNumOp MaxOp [u, simplifyAstNumOp MaxOp [v, w]]
simplifyAstNumOp MinOp [AstConst u, AstConst v] = AstConst $ min u v
simplifyAstNumOp MinOp [ AstConst u
                       , AstNm MinOp [AstConst v, w] ] =
  simplifyAstNumOp MinOp [AstConst $ min u v, w]
simplifyAstNumOp MinOp [u, AstConst n] = AstNm MinOp [AstConst n, u]
simplifyAstNumOp MinOp [AstNm MinOp [u, v], w] =
  simplifyAstNumOp MinOp [u, simplifyAstNumOp MinOp [v, w]]

simplifyAstNumOp opCode arg = AstNm opCode arg

simplifyAstIntegralOp :: KnownNat n
                      => OpCodeIntegral -> [AstRanked Int64 n]
                      -> AstRanked Int64 n
simplifyAstIntegralOp QuotOp [AstConst u, AstConst v] = AstConst $ quot u v
simplifyAstIntegralOp QuotOp [AstConst 0, _v] = AstConst 0
simplifyAstIntegralOp QuotOp [u, AstConst 1] = u
simplifyAstIntegralOp QuotOp [ Ast.AstOpIntegral RemOp [_u, AstConst v]
                             , AstConst v' ]
  | v' >= v && v >= 0 = 0
simplifyAstIntegralOp QuotOp [Ast.AstOpIntegral QuotOp [u, v], w] =
  simplifyAstIntegralOp QuotOp [u, simplifyAstNumOp TimesOp [v, w]]
simplifyAstIntegralOp QuotOp [ Ast.AstNm TimesOp [AstConst u, v]
                             , AstConst u' ]
  | u == u' = v

simplifyAstIntegralOp RemOp [AstConst u, AstConst v] = AstConst $ rem u v
simplifyAstIntegralOp RemOp [AstConst 0, _v] = 0
simplifyAstIntegralOp RemOp [_u, AstConst 1] = 0
simplifyAstIntegralOp RemOp [ Ast.AstOpIntegral RemOp [u, AstConst v]
                            , AstConst v']
  | v' >= v && v >= 0 = Ast.AstOpIntegral RemOp [u, AstConst v]
simplifyAstIntegralOp RemOp [ Ast.AstOpIntegral RemOp [u, AstConst v]
                            , AstConst v']
  | rem v v' == 0 && v > 0 = simplifyAstIntegralOp RemOp [u, AstConst v']
simplifyAstIntegralOp RemOp [ AstNm TimesOp [AstConst u, _v]
                            , AstConst u' ]
  | rem u u' == 0 = 0

simplifyAstIntegralOp opCode arg = Ast.AstOpIntegral opCode arg

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right.
simplifyAstBoolOp :: OpCodeBool -> [AstBool] -> AstBool
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

simplifyAstPrimalS
  :: (OS.Shape sh, GoodScalar r)
  => AstPrimalPartS r sh -> AstPrimalPartS r sh
simplifyAstPrimalS (AstPrimalPartS t) = astPrimalPartS $ simplifyAstS t

simplifyAstS
  :: (OS.Shape sh, GoodScalar r)
  => AstShaped r sh -> AstShaped r sh
simplifyAstS t = case t of
  Ast.AstVarS{} -> t
  Ast.AstLetS var u v -> astLetS var (simplifyAstS u) (simplifyAstS v)
  Ast.AstLetADShareS{} -> error "simplifyAstS: AstLetADShareS"
  AstNmS opCode args -> AstNmS opCode (map simplifyAstS args)
  Ast.AstOpS opCode args -> Ast.AstOpS opCode (map simplifyAstS args)
  Ast.AstOpIntegralS opCode args ->
    Ast.AstOpIntegralS opCode (map simplifyAstS args)
  AstSumOfListS args -> AstSumOfListS (map simplifyAstS args)
    -- We do not simplify, e.g., addition or multiplication by zero.
    -- There are too many cases and values are often unknown.
  Ast.AstIotaS -> t
  Ast.AstIndexS v ix ->
    Ast.AstIndexS (simplifyAstS v) (fmap simplifyAstPrimal ix)  -- TODO
  Ast.AstSumS v -> astSumS (simplifyAstS v)
  Ast.AstScatterS v (var, ix) ->
    astScatterS (simplifyAstS v) (var, fmap simplifyAstPrimal ix)
  Ast.AstFromListS l -> astFromListS (map simplifyAstS l)
  Ast.AstFromVectorS l -> astFromVectorS (V.map simplifyAstS l)
  Ast.AstReplicateS v -> astReplicateS (simplifyAstS v)
  Ast.AstAppendS x y -> astAppendS (simplifyAstS x) (simplifyAstS y)
  Ast.AstSliceS @i v -> Ast.AstSliceS @i (simplifyAstS v)  -- TODO
  Ast.AstReverseS v -> astReverseS (simplifyAstS v)
  Ast.AstTransposeS @perm v -> Ast.AstTransposeS @perm $ simplifyAstS v  -- TODO
  Ast.AstReshapeS v -> Ast.AstReshapeS $ simplifyAstS v  -- TODO
  Ast.AstBuild1S (var, v) -> Ast.AstBuild1S (var, simplifyAstS v)
  Ast.AstGatherS v (vars, ix) ->
    astGatherS (simplifyAstS v) (vars, fmap simplifyAstPrimal ix)
  Ast.AstCastS v -> Ast.AstCastS $ simplifyAstS v
  Ast.AstRToS v -> Ast.AstRToS $ simplifyAst v
  AstConstS{} -> t
  Ast.AstConstantS v -> Ast.AstConstantS (simplifyAstPrimalS v)
  Ast.AstDS u (AstDualPartS u') -> Ast.AstDS (simplifyAstPrimalS u)
                                     (AstDualPartS $ simplifyAstS u')
  Ast.AstLetDomainsS vars l v ->
    Ast.AstLetDomainsS vars (simplifyAstDomains l) (simplifyAstS v)
  Ast.AstFloorS a -> Ast.AstFloorS (simplifyAstPrimalS a)
  Ast.AstCondS b a2 a3 ->
    astCondS (simplifyAstBool b) (simplifyAstS a2) (simplifyAstS a3)
  Ast.AstMinIndexS a -> Ast.AstMinIndexS (simplifyAstPrimalS a)
  Ast.AstMaxIndexS a -> Ast.AstMaxIndexS (simplifyAstPrimalS a)

astLetS :: forall sh1 sh2 r r2.
           (OS.Shape sh1, OS.Shape sh2, GoodScalar r, GoodScalar r2)
        => AstVarId -> AstShaped r sh1 -> AstShaped r2 sh2 -> AstShaped r2 sh2
astLetS var u v | astIsSmallS True u =
  substitute1AstS (SubstitutionPayloadShaped u) var v
  -- we use the substitution that does not simplify, which is sad,
  -- because very low hanging fruits may be left hanging, but we
  -- don't want to simplify the whole term; a better alternative
  -- would be a substitution that only simplifies the touched
  -- terms with one step lookahead, as normally when vectorizing
astLetS var u v@(Ast.AstVarS var2) =
  if var2 == var
  then case sameShape @sh1 @sh2 of
    Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> u
      _ -> error "astLetS: type mismatch"
    _ -> error "astLetS: shape mismatch"
  else v
astLetS var u v = Ast.AstLetS var u v

astSumS :: (KnownNat n, OS.Shape sh, GoodScalar r)
        => AstShaped r (n ': sh) -> AstShaped r sh
astSumS (AstConstS t) = AstConstS $ tsumS t
astSumS (Ast.AstConstantS (AstPrimalPartS v)) =
  Ast.AstConstantS $ astPrimalPartS $ astSumS v
astSumS (Ast.AstReverseS v) = Ast.AstSumS v
astSumS v = Ast.AstSumS v

-- TODO: fuse scatters, scatter and sum, perhaps more (fromList?)
astScatterS :: forall sh2 p sh r.
               ( OS.Shape sh2, OS.Shape sh
               , OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh)
               , OS.Shape (sh2 OS.++ OS.Drop p sh), GoodScalar r )
            => AstShaped r (sh2 OS.++ OS.Drop p sh)
            -> (AstVarListS sh2, AstIndexS (OS.Take p sh))
            -> AstShaped r sh
astScatterS v (ZSH, ZSH) =
  gcastWith (unsafeCoerce Refl
             :: OS.Take p sh OS.++ OS.Drop p sh :~: sh)
  v
-- astScatterS v (var :$: vars, ix) | not $ var `intVarInIndexS` ix =
--   astScatterS (astSumS v) (vars, ix)
  -- TODO: ^^^
-- astScatterS v (Z, ix) = update (tzero sh 0) ix v
astScatterS (Ast.AstConstantS (AstPrimalPartS v)) (vars, ix) =
  Ast.AstConstantS $ astPrimalPartS $ astScatterS v (vars, ix)
astScatterS v (vars, ix) = Ast.AstScatterS v (vars, ix)

astFromListS :: (KnownNat n, OS.Shape sh, GoodScalar r)
             => [AstShaped r sh] -> AstShaped r (n ': sh)
astFromListS [a] = astReplicateS a
astFromListS l =
  let unConstant (Ast.AstConstantS (AstPrimalPartS t)) = Just t
      unConstant _ = Nothing
  in case mapM unConstant l of
    Just [] -> Ast.AstFromListS []
    Just l2 -> Ast.AstConstantS $ astPrimalPartS $ astFromListS l2
    Nothing ->
      let unConst (AstConstS t) = Just t
          unConst _ = Nothing
      in case mapM unConst l of
        Just l3 -> AstConstS $ tfromListS l3
        Nothing -> Ast.AstFromListS l

astFromVectorS :: (KnownNat n, OS.Shape sh, GoodScalar r)
               => Data.Vector.Vector (AstShaped r sh) -> AstShaped r (n ': sh)
astFromVectorS v | V.length v == 1 = astReplicateS (v V.! 0)
astFromVectorS l =
  let unConstant (Ast.AstConstantS (AstPrimalPartS t)) = Just t
      unConstant _ = Nothing
  in case V.mapM unConstant l of
    Just l2 | V.null l2 -> Ast.AstFromVectorS l2
    Just l2 -> Ast.AstConstantS $ astPrimalPartS $ astFromVectorS l2
    Nothing ->
      let unConst (AstConstS t) = Just t
          unConst _ = Nothing
      in case V.mapM unConst l of
        Just l3 -> AstConstS $ tfromVectorS l3
        Nothing -> Ast.AstFromVectorS l

astReplicateS :: forall n sh r. (KnownNat n, OS.Shape sh, GoodScalar r)
              => AstShaped r sh -> AstShaped r (n ': sh)
astReplicateS = \case
  Ast.AstConstantS (AstPrimalPartS v) ->
    Ast.AstConstantS $ astPrimalPartS $ astReplicateS v
  Ast.AstTransposeS @perm @sh1 v ->
    let zsuccPerm = 0 : map succ (OS.shapeT @perm)
    in OS.withShapeP zsuccPerm $ \(_proxy :: Proxy zsuccPerm) ->
--      gcastWith (unsafeCoerce Refl :: 0 ': MapSucc perm :~: zsuccPerm) $
      gcastWith (unsafeCoerce Refl
                 :: OS.Permute zsuccPerm (n : sh1) :~: n : sh) $
      gcastWith (unsafeCoerce Refl :: OS.Rank zsuccPerm :~: 1 + OS.Rank perm) $
      trustMeThisIsAPermutation @zsuccPerm
      $ astTransposeS @zsuccPerm $ astReplicateS @n v
  v -> Ast.AstReplicateS v

astAppendS :: (KnownNat m, KnownNat n, OS.Shape sh, GoodScalar r)
           => AstShaped r (m ': sh) -> AstShaped r (n ': sh)
           -> AstShaped r ((m + n) ': sh)
astAppendS (AstConstS u) (AstConstS v) = AstConstS $ tappendS u v
astAppendS (Ast.AstConstantS (AstPrimalPartS u))
           (Ast.AstConstantS (AstPrimalPartS v)) =
  Ast.AstConstantS $ astPrimalPartS $ astAppendS u v
astAppendS (Ast.AstFromListS l1) (Ast.AstFromListS l2) = astFromListS $ l1 ++ l2
astAppendS (Ast.AstFromListS l1) (Ast.AstFromVectorS l2) =
  astFromListS $ l1 ++ V.toList l2
astAppendS (Ast.AstFromVectorS l1) (Ast.AstFromListS l2) =
  astFromListS $ V.toList l1 ++ l2
astAppendS (Ast.AstFromVectorS l1) (Ast.AstFromVectorS l2) =
  astFromVectorS $ l1 V.++ l2
astAppendS u v = Ast.AstAppendS u v

astReverseS :: forall n sh r. (KnownNat n, OS.Shape sh, GoodScalar r)
            => AstShaped r (n ': sh) -> AstShaped r (n ': sh)
astReverseS (AstConstS t) = AstConstS $ treverseS t
astReverseS (Ast.AstConstantS (AstPrimalPartS v)) =
  Ast.AstConstantS $ astPrimalPartS $ astReverseS v
astReverseS (Ast.AstFromListS l) = Ast.AstFromListS $ reverse l
astReverseS (Ast.AstFromVectorS l) = Ast.AstFromVectorS $ V.reverse l
astReverseS (Ast.AstReplicateS v) = Ast.AstReplicateS v
astReverseS (Ast.AstReverseS v) = v
astReverseS (Ast.AstGatherS v ((:$:) @k var vars, ix)) =
  let ivar = astPrimalPart
             $ AstNm Ast.MinusOp [ AstConst
                                   $ OR.scalar (valueOf @k :: Int64)
                                 , Ast.AstVar ZS var ]
      ix2 = fmap (substituteAstPrimal (SubstitutionPayloadInt ivar) var) ix
  in astGatherS v (var :$: vars, ix2)
astReverseS v = Ast.AstReverseS v

astGatherS
  :: forall sh2 p sh r.
     ( OS.Shape sh, OS.Shape sh2
     , OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh) )
  => AstShaped r sh
  -> (AstVarListS sh2, AstIndexS (OS.Take p sh))
  -> AstShaped r (sh2 OS.++ OS.Drop p sh)
astGatherS = Ast.AstGatherS  -- TODO

astDomainsLetS :: forall sh r. (GoodScalar r, OS.Shape sh)
               => AstVarId -> AstShaped r sh -> AstDomains -> AstDomains
astDomainsLetS var u v | astIsSmallS True u =
  substitute1AstDomains (SubstitutionPayloadShaped u) var v
  -- we use the substitution that does not simplify, which is sad,
  -- because very low hanging fruits may be left hanging, but we
  -- don't want to simplify the whole term; a better alternative
  -- would be a substitution that only simplifies the touched
  -- terms with one step lookahead, as normally when vectorizing
astDomainsLetS var u v = Ast.AstDomainsLetS var u v

astCondS :: AstBool -> AstShaped r sh -> AstShaped r sh -> AstShaped r sh
astCondS (AstBoolConst b) v w = if b then v else w
astCondS b (Ast.AstConstantS (AstPrimalPartS v))
           (Ast.AstConstantS (AstPrimalPartS w)) =
  Ast.AstConstantS $ astPrimalPartS $ astCondS b v w
astCondS b v w = Ast.AstCondS b v w

-- We have to simplify after substitution or simplifying is not idempotent.
substituteAstPrimal :: forall n r. (GoodScalar r, KnownNat n)
                    => SubstitutionPayload -> AstVarId
                    -> AstPrimalPart r n
                    -> AstPrimalPart r n
substituteAstPrimal i var v1 = simplifyAstPrimal $ substitute1AstPrimal i var v1

substituteAst :: forall n r. (GoodScalar r, KnownNat n)
              => SubstitutionPayload -> AstVarId -> AstRanked r n
              -> AstRanked r n
substituteAst i var v1 = simplifyAst $ substitute1Ast i var v1

substituteAstDomains
  :: SubstitutionPayload -> AstVarId -> AstDomains
  -> AstDomains
substituteAstDomains i var v1 =
  simplifyAstDomains $ substitute1AstDomains i var v1

substituteAstBool :: SubstitutionPayload -> AstVarId -> AstBool
                  -> AstBool
substituteAstBool i var b1 = simplifyAstBool $ substitute1AstBool i var b1

substituteAstS :: forall sh r. (GoodScalar r, OS.Shape sh)
               => SubstitutionPayload -> AstVarId -> AstShaped r sh
               -> AstShaped r sh
substituteAstS i var v1 = {-simplifyAstS $-} substitute1AstS i var v1
